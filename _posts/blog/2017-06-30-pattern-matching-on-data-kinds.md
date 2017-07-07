---
layout: post
category: reflections
author: gregory malecha
title: "Pattern Matching on Data Kinds"
tags:
- haskell
- data kinds
- GADT
highlight: true
---

In this post I'm going to discuss a problem that I ran into while working with shape indexed types in Haskell and an elgant solution that is inspired by dependent type theory.
The problem is implementing functions that produce values of shape-indexed types *without* accepting a to do case analysis on to refine the index.
A simple example arrises when implementing an `Applicative` instance for length indexed vectors.

```haskell
data Nat = O | S Nat

data Vector (l :: Nat) t where
  Vnil :: Vector O t
  Vcons :: forall l. t -> Vector l t -> Vector ('S l) t
```

Implementing `<*>` is no problem at all because we get to do recursion on the input parameters; in fact, our type nicely guarantees that the two `Vector`s have the same length.

```haskell
apVector :: Vector l (a -> b) -> Vector l a -> Vector l b
apVector Vnil Vnil = Vnil
apVector (Vcons f fs) (Vcons x xs) = Vcons (f x) (apVector fs xs)
```

However, we run into a problem when we try to implement `pure` because we don't have any way to inspect the `l` index of the vector type.

```haskell
pureVector :: a -> Vector l a
pureVector = undefined -- What can we do?
```

In a depenent type theory such as [Coq](https://coq.inria.fr/), [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php), [Idris](https://www.idris-lang.org/), etc. we could simply match on the `l` and determine what to do, but in Haskell, `l` is a at the type level[^fn-not-a-type].
If we don't have a way to pattern match on `l`, then how can we solve this problem?

## Just get the Value! (A Failed Attempt)

The first thing that came to my mind was that we simply needed to be able to pattern match on the value of type `Nat`.
To do that, we can use a type-class (data-kind class?) to get the value.

```haskell
class KnownNat (n :: Nat) where
  natValue :: Nat

instance KnownNat 'O where
  natValue = O
instance KnownNat n => KnownNat ('S n) where
  natValue = S (natValue @n)
```

Unfortunately, this doesn't help us solve our problem because, in Haskell, `l :: Nat` at the value level is really completely different from `l :: Nat` at the type level.
Inspecting the value-level `l :: Nat` doesn't tell us anything about the `l :: Nat` that occurs at the type level.

## Dependent Pattern Matching to the Rescue

In order to solve our problem, we need to express the dependent pattern match in the type-class.
Here's what that looks like:

```haskell
class ElimNat (l :: Nat) where
  elimNat :: f 'O
          -> (forall n. ElimNat n => f ('S n))
          -> f l
```

Note, the function `elimNat` is polymorphic in a type-level function `f`, which describes the result type as a function of the index (`l :: Nat`).
Thus, the caller of the function will simply need to supply two arguments, for the result is `l` is `O` and the result if `l` is `S m` for some `ElimNat m`.

Perhaps surprisingly, it is very easy to provide instances for this version of `ElimNat` because when we declare instances, we use Haskell's type-level unification to selet the appropriate index. 

```haskell
instance ElimNat 'O where
  elimNat f _ = f
instance ElimNat n => ElimNat ('S n) where
  elimNat _ f = f
```

In the first instance, we know that `l` is `'O`, so we need to produce a value of type `f 'O` given a value of type `f 'O` (the first parameter).
Pretty simple.
Similarly, in the `'S` case, we are asked to produce a value of type `f ('S n)` given a value of type `(forall n. ElimNat n => f ('S n))`.
Since GHC resolves the type class instances for us (using the one required by the super-class declaration) the implementation looks similarly trivial.

### Implementing `pure`

If we have an instance of `ElimNat n`, then it is pretty easy to implement `pureVector`.

```haskell
pureVector :: forall a l. ElimNat l => a -> Vector l a
pureVector a = getPureVector $ elimNat (PureVector Vnil) mkCons
  where mkCons :: forall l. ElimNat l => PureVector a ('S l)
        mkCons = PureVector $ Vcons a (pureVector a)

-- Local type necessary to get around GHC's lack of type-level lambdas.
newtype PureVector a l = PureVector
  { getPureVector :: Vector l a }
```

The caveat in the implementation is that GHC doesn't support type-level lambdas, so we need to make a `newtype` to swap the arguments of `Vector` since we need to instantiate `f` with a type function of kind `Nat -> *`.
I'm not sure if there is a cleaner way to achieve this in Haskell, but if you know one, please leave a comment.

## What else is `ElimNat` good for?

One might argue that we could avoid the complexity of `ElimNat` simply by incorporating it into the `Applicative` instances for `Vector l`.
Indeed, this would work, but the generalization allows us to write other sorts of functions.
For example, we can implement `fromList` which allows us to use the `OverloadedLists` extension to have nice syntax for `Vector`s.

```haskell
fromList :: forall l a. ElimNat l => [a] -> Maybe (Vector l a)
fromList = getFromList $ elimNat (FromList $ const $ Just Vnil) mkCons
  where mkCons :: forall l. ElimNat l => FromList a ('S l)
        mkCons = FromList $ \ case
                                [] -> Nothing
                                (x:xs) -> Vcons x <$> fromList xs

newtype FromList a l = FromList
  { getFromList :: [a] -> Maybe (Vector l a) }
```

Similarly, it gives us a convenient way to define the instance for `Monad` simply by adding the `ElimNat` constraint.

```haskell
instance ElimNat l => Monad (Vector l) where
  return = pure
  Vnil >>= _ = Vnil
  (Vcons x xs) >>= f = case f x of
                         Vcons z _ -> Vcons z (xs >>= f)
```

Note that like this `Monad` instance works like the instances for [`Seq`](https://hackage.haskell.org/package/containers-0.5.10.2/docs/Data-Sequence.html) or [`ZipList`](http://hackage.haskell.org/package/base-4.9.1.0/docs/Control-Applicative.html#v:ZipList) by zipping the vectors together rather than taking their cross product (which would have a different length).

# Learning the Structure of a Nat

Unlike the `KnownNat` type class in the standard library, we can actually build instances of `ElimNat` at runtime if we have access to a value that is indexed (in a useful way) on the `Nat`.
For example, if we have a `Vector` of length `l`, we can compute an instance of `ElimNat l` using the definitions in the [constraints library](https://hackage.haskell.org/package/constraints) and the following function:

```haskell
learnLength :: Vector l t -> Dict (ElimNat l)
learnLength Vnil = Dict
learnLength (Vcons _ xs) = case learnLength xs of
                             Dict -> Dict
```

Note that behind the scenes, GHC is handling all of the type-class resolution for us.
It supplies `ElimNat O` for the first instance of `Dict` and `ElimNat n => ElimNat ('S n)` for the second instance (resolving the `ElimNat n` using the instance we get from pattern matching on the `Dict`.

## Conclusions

In this post I demonstrated a technique for "matching" data kinds by encoding their dependent pattern match within a type-class.
This technique allows us to encapsulate the pattern match an use it to implement a variety of functions that produce indexed values without consuming an indexed value.


### Footnotes ###

[^fn-not-a-type]: Note that strictly speaking `l` isn't a type, it is a `Nat`. Haskell, however, treats data kinds as type-like in the sense that they exist only at compile time.

[^fn-strength-of-pattern-match]: Haskell's pattern matching supports Coq-style `in` clauses (through GADTs) but not `as` clauses which makes sense because, in Haskell, `l :: Nat` at the value level is different than `l :: Nat` at the type level.
