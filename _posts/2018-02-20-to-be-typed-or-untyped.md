---
layout: post
category: reflections
author: gregory malecha
title: "To Be Typed and Untyped"
tags:
- haskell
- GADT
- compositional datatypes
highlight: true
links:
- gist: "https://gist.github.com/gmalecha/ceb3778b9fdaa4374976e325ac8feced"
---

There is a tension between being too strongly (statically) typed and too weakly (statically) typed.
In this post, I show how to use existential types to "derive" untyped syntax from typed syntax.
This allows you to use strongly typed syntax and selectively escape to an untyped world, e.g. to do parsing or non-local transformations, without needing to maintain two different syntax definitions.
This solution arose as part of discussions with  [Matthew Farkas-Dyck](https://hackaday.io/Strake), [Daniel Winograd-Cort](http://www.danwc.com/), [Moritz Drexl](https://github.com/themoritz), and the problem was originally posed to me by [Daniel King](https://dekvek.com/).

{% comment %}
The benefit of being strongly (statically) typed comes from the guarantees that you get and (in some circumstances) additional runtime performance due to the ability to eraase tags.
The drawback is that sometimes it is difficult to convince the compiler that what you are doing is well-typed.
The later point is aided greatly by rich type systems, e.g. Haskell and (even more so) Agda, Coq, and Idris.
{% endcomment %}

Recently I have been playing with a deep embedding of a programming language within Haskell and I was immediately forced with the question of whether the syntax of the language should be strongly typed or weakly typed.
Since the whole programming language isn't particularly important, I'll just boil it down to the essential bits.

In the weakly typed variant, there is a single type `Expr` that represents (possibly ill-typed) expressions of any type.

```haskell
data Expr = ILit Int
          | BLit Bool
	  | Plus Expr Expr
	  | If Expr Expr Expr
```

In the strongly-typed variant, the type of expressions is indexed by the type of the expression.

```haskell
data Expr t where
  ILit :: Int -> Expr Int
  BLit :: Bool -> Expr Bool
  Plus :: Expr Int -> Expr Int -> Expr Int
  If   :: Expr Bool -> Expr a -> Expr a
```

In the former of these, the type `Expr` encodes the syntax of the language, in the later, the type `Expr` encodes the typing derivations of the language.
There are pros and cons to each approach.

In the *strong representation*, you get compile-time checking of expressions and transformations, meaning that the Haskell type checker will ensure that you can not build an ill-typed term.
That is we are getting [typed perserving translations](https://www.cs.cmu.edu/~rwh/theses/morrisett.pdf) enforced by the host language's (Haskell in this case) type system.
Another, property that we get out of this stronger representation[^fn-sel-representation] is that it *may* provide a path towards self-representation via [Brown's work from POPL'16](https://dl.acm.org/citation.cfm?id=2837623).

The down-side of strong typing is that you always have to track types around and so transformations that rely on sophisticated invariants might be more difficult to express in Haskell.
Some examples of complex transformations arise in [the dissertation of Tristan](http://tel.archives-ouvertes.fr/tel-00437582/), e.g. loop fusion and loop scheduling in [CompCert](http://compcert.inria.fr/).
Note, however, that this work is based on the weakly typed representation of C in CompCert.
A particularly complex piece often comes when representing open terms (especially in dependent type theories) where "acrobatics" (using telescopes) become necessary to track the interesting interplay between types and terms.

Another, and the motivation for my own experimentation, upside to the weakly-typed representation is that it can be used directly during parsing.
I had a pile of type-class instances that pulled a variety of runtime type checking to parse my strongly-typed representation from JSON, and even with these hacks, I wasn't obvious how to get useful features such as inference and variables to work correctly.

So the question arises, can we write **a single type** and get **both a weakly and a strongly typed representation**?
The answer to this question turns out to be "yes", and in this post I'm going to explain how it works.
As with a lot of questions in logic, in retrospect the answer seems completely obvious, so before proceeding, you might spend a few minutes puzzling through it to satisfy your intellectual curiosity.

# A Functorized Type

It shouldn't be too surprising that our core representation will be a typed representation since it carries *strictly more* information than the untyped reprsentation.
However, I am not going to use the standard encoding in Haskell that I wrote above.
Instead, I am going to do is to factor the type into two pieces: the constructors and the fixpoint using the pattern of [Datatypes *a la* Carte](http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf).

```haskell
-- | The functor.
data ExprF (e :: k -> *) (t :: k) where
  NLit :: Int -> ExprF e Int
  Plus :: e Int -> e Int -> ExprF e Int

  BLit :: Bool -> ExprF e Bool
  If :: e Bool -> e a -> e a -> ExprF e a

-- | The fixpoint combinator.
data Fix1 (e :: (k -> *) -> (k -> *)) (t :: k) where
  Fix1 :: e (Fix1 e) t -> Fix1 e t

-- | The expression type.
-- Note that the kind of this type is `k -> *`
type Expr = Fix1 ExprF
```

While a little bit more verbose than the basic representation, it has a lot of benefits, some of which I will leverage to solve this problem.
Here, I am using the *kind variable* `k` to represent the "type" of types in my language.
One can freely think of `k ~ *` if this makes more sense, but I personally find the distinction useful in tracking the object language (the syntax) from the meta-language (Haskell).

Using this representation is a bit annoying, so we can define some basic combinators.

```haskell
eInt :: Int -> Expr Int
eInt = Fix1 . NLit

eBool :: Bool -> Expr Bool
eBool = Fix1 . BLit
```

Using these combinators, we can write expressions in Haskell and the Haskell type checker will guarantee that they are well-typed.

```haskell
e1 :: Expr Int
e1 = eIf (eBool True) (eInt 0) (eInt 1)

not :: Expr Bool -> Expr Bool
not e = eIf e (eBool False) (eBool True)
```

Note that our simple language does not have lambda abstractions so the second expression is a Haskell function that takes an expression and builds a larger expression using it.


# An Interpreter

Just to give a flavor of how we can program with this representation, let's implement a simple interpreter.
The core of the interpreter is an evaluator for the functor.

```haskell
eval :: ExprF Identity t -> Identity t
eval (NLit n) = pure n
eval (Plus a b) = (+) <$> a <*> b
eval (BLit b) = pure b
eval (If (Identity a) b c) = if a then b else c
```

Note that here we assume that sub-expressions are already evaluated (i.e. their type is `Identity t` for whatever `t` the `Expr` type calls for).
Note in particular that this means that we don't need to do any runtime type checking *and* the evaluation function is **total**, i.e. we do not need to return a `Maybe` in the case that the term is ill-typed because the types of the constructors guarantee that this will not happen.

We then combine this with the recursor for the fixpoint combinator.

```haskell
evaluate :: Fix1 ExprF :-> D
evaluate (Fix1 e) = eval $ hfmap evaluate e
```

Here `hfmap` (code available [in the accompanying gist]() and originally in the [compdata package](https://hackage.haskell.org/package/compdata-0.11/docs/Data-Comp-Multi-HFunctor.html)) is like `fmap` but lifted to natural transformations.

```haskell
-- | Natural transformations.
type (:->) f g = forall a. f a -> g a

-- | Lifting a natural transformation over another natural
-- transformation.
class HFunctor (f :: (k -> *) -> (k -> *)) where
  hfmap :: forall g g'. g :-> g' -> f g :-> f g'
```




# Hiding the Types

So, how can we get untyped expressions on top of this typed representation?
Morally, what we want to do is take this representation and simply forget the index, but naively that would require that we make a new type.
Instead, we can use *existential quantification* to loosen the requirement that the indicies match, i.e. that we can only put an expression of type `Int` in a hole "requiring" an `Int` expression.
It turns out that there are many ways to do this, but at some level they are all the same.
Let's start with a type combinator that takes in a typed algebra, and returns one that doesn't require the types to match.

```haskell
-- | Allow an expression (`e`) of type `t` to fill a whole of any
-- type (`t'`).
data IgnoreT (e :: (k -> *) -> (k -> *)) (u :: k -> *) (t :: k) where
  IgnoreT :: forall t' e u t. e u t' -> IgnoreT e u t

-- | Untyped terms.
type UExpr = Fix1 (IgnoreT ExprF) ()
```

Here, the syntax is the same (i.e. just an `e`) but the type index fed to `e` (i.e. `t'`) and the type index (i.e. `t`) on the resulting type are independent.
This allows us to build ill-typed expressions which we usually can not do in the strongly typed syntax.

```haskell
-- | Ignore types on a term.
untype :: ExprF (Fix1 (IgnoreT ExprF)) t -> UExpr
untype = Fix1 . IgnoreT

-- | Coerce untyped
rewrap :: UExpr -> Fix1 (IgnoreT ExprF) t
rewrap (Fix1 (IgnoreT e)) = Fix1 (IgnoreT e)
 -- NOTE that this is not the identity function because the
 -- types are not the same.

uInt :: Int -> UExpr
uInt n = untype $ NLit n

uBool :: Bool -> UExpr
uBool b = untype $ BLit b

uIf :: UExpr -> UExpr -> UExpr -> UExpr
uIf i t e = untype $ If (rewrap i) t e

-- | Term representing `if 1 then 1 else true`
illTyped :: UExpr
illTyped = uIf (uInt 1) (uInt 1) (uBool True)
```


# Type Checking

Being able to represent ill-typed terms is great for phases such as parsing, but ultimately, we need to be able to converty these `UExpr`s back into regular `Expr`s.
The way we do this is through type-checking.
As with the evaluator, we will break the implementation down into two pieces, the piece that operates on the algebra, and the piece that operates through the fixpoint.

Here is the definition of the type checking functor:

```haskell
-- | A type containing both type checking and type-inference.
-- Note that the `t` parameter is unused, it is needed to match the
-- type of the recursive argument.
data CheckInfer m f t = CheckInfer
  { check :: forall t'. Typeable t' => m (f t')
  , infer :: m (Ex f)
  }

-- | Build a @CheckInfer@ from just an `infer`.
fromInfer :: forall m f t. MonadPlus m => m (Ex f) -> CheckInfer m f t
fromInfer val = CheckInfer
  { check = do
      Ex e <- val
      check e
  , infer = val
  }
  where check :: forall t t'. (Typeable t, Typeable t') => f t' -> m (f t)
        check e = case eqT @t @t' of
                    Just Refl -> return e
                    Nothing -> mzero

-- | Type checking function for the language functor.
checkF :: MonadPlus m
       => IgnoreT ExprF (CheckInfer m e) t
       -> CheckInfer m (ExprF e) t
checkF (IgnoreT (NLit n)) =
  fromInfer $ return (Ex (NLit n))
checkF (IgnoreT (Plus a b)) =
  fromInfer $ (\ a b -> Ex (Plus a b)) <$> check a <*> check b
checkF (IgnoreT (BLit n)) = fromInfer $ return (Ex (BLit n))
checkF (IgnoreT (If i t e)) = CheckInfer
  { check = do
      it <- check i
      If it <$> check t <*> check e
  , infer = do
      it <- check i
      Ex tt <- infer t
      et <- check e
      return $ Ex (If it tt et)
  }
```

As one would expect, with compositional data types the handling of the fixpoint is identical to above since we have only swapped out the functor[^fn-handling-the-fix].

```haskell
checkInfer :: MonadPlus m
           => Fix1 (IgnoreT ExprF) t -> CheckInfer m ExprF t'
checkInfer (Fix1 e) = eval $ hfmap checkInfer e
```

With this code, our type checker actually takes a term where types are ignored and returns a term where they are not.
Wrapping things up, we get:

```haskell
checkType :: forall t m. (Typeable t, MonadPlus m) => UExpr -> m (Expr t)
checkType e = check <$> checkInfer e

inferType :: forall t m. MonadPlus m => UExpr -> m (Ex Expr)
inferType e = infer <$> checkInfer e
```

And `TypeApplications` makes calling this really easy.

```haskell
checkType @Int @Maybe illTyped :: Maybe (Expr Int)
-- == Nothing
```


# Putting it all Together

From here, you can build a very simple program that parses an *untyped expression*, performs type-checking, and then evaluates the typed expression (if type checking succeded).
Here's the code (sans the parser).

```haskell
main :: IO ()
main = do
  source <- readContents
  parse source >>= \case
    Left err -> putStrLn "Failed to parse expression."
    Right uexpr -> inferType uexpr >>= \case
      Nothing -> putStrLn "The expression is ill-typed"
      Just (Ex texpr) -> do
        putStrLn $ "The expression has type `" ++ showType texpr ++ "`"
        let result = evaluate texpr
        putStrLn $ show result
```

There are two nice things about this.

1. The Haskell type tells us whether the term has been type checked. This allows us to avoid the problem of potentially trying to evaluate before we type check.
2. We can write both typed and untyped transformations without needing to duplicate the syntax types (or any functions).

If we choose to use the compositional features of the functorial representation, we note the following isomorphism on `IgnoreT` which allows us to write the type checker in a completely compositional manner.

```haskell
iso :: Iso (IgnoreT (f :+: g) u t) ((IgnoreT f :+: IgnoreT g) u t)
iso = ...
```

{% comment %}
# Alternatives

As I mentioned earlier, there are a few alternatives to the above approach.
As you might expect, however, they all boil down to existential quantification.
One particularly interesting alternative is to use compositional data-types to "mix-in" a coercion operator.
For completeness,

```haskell
data (:+:) (l :: (k -> *) -> (k -> *)) (r :: (k -> *) -> (k -> *)) (u :: k -> *) (t :: k) where
  InL :: l u a -> l :+: r u a
  InR :: r u a -> l :+: r u a

data CoerceF u t where
  CoerceF :: u t -> CoerceF u t'
```

With these definitions we can extend our data type with `CoerceF`, i.e.

```haskell
type UExpr = Fix1 (ExprF :+: CoerceF) ()
```

Note here that combining `ExprF` and `CoerceF` within the argument to `Fix1` is allowing us to freely intermix `ExprF` and `CoerceF` constructors within the term.

Under this formulation, the type checker simply needs to find all occurances of `CoerceF` and remove them (first checking to see if they can be removed).
Morally, it is a (partial) [desugaring]().

```haskell
checkF' :: _
checkF' (CoerceF ci) = CheckInfer
  { check = check ci
  , infer = infer ci
  }
checkF' ...
```

An interesting property of this representation is that if we have a large term that we know is well-typed, we can splice that into an untyped term by wrapping it in a `CoerceF`.
Then, when we type check, we don't necessarily need to type check the entire term.
{% endcomment %}

# Conclusions

In this post, I showed a simple way to convert a typed abstract syntax tree into an untyped abstract syntax tree in a completely modular way.
There is no need to duplicate any type definitions, and the mechanism for achieving this allows for a whole host of other "mix-ins", e.g. decoration with source locations, and even mixing in other syntax fragments to support syntactic sugar.

I have not seen this before, if you're aware of any other places where this is used, please mention them in the comments.


### Attributions & Acknowledgements

This work arose from discussions with my co-workers: [Matthew Farkas-Dyck](https://hackaday.io/Strake), [Daniel Winograd-Cort](http://www.danwc.com/), and [Moritz Drexl](https://github.com/themoritz).
It was originally posed to me by my graduate school lab mate [Daniel King](https://dekvek.com/).


{% comment %}
## An Alternative Formulation

The fact that we are taking a fixpoint actually means that there are actually several other ways to accompish this.
If we unroll the definition of `UExpr` using the fixpoint rules, we see that we end up with the following:

```haskell
  UExpr t
≡ Fix1 (IgnoreT ExprF) t
≡ IgnoreT FExpr (Fix1 (IgnoreT ExprF)) t
≡ IgnoreT FExpr (IgnoreT ExprF (Fix1 (IgnoreT ExprF))) t
```

Note that (ignoring the `Fix1` construtor[^fn-equirecursive]) the argument to `IgnoreT FExpr` is always an `IgnoreT`.
Therefore, it is equivalent to write the following type:

```haskell
-- | Ignore the final argument.
data IgnoreF (u :: k -> *) (t :: k) where
  IgnoreF :: forall t t' u. u t' -> IgnoreF u t

-- | Allow an expression (`e`) of type `t` to fill a whole of any
-- type (`t'`).
data IgnoreT (e :: (k -> *) -> (k -> *)) (u :: k -> *) (t :: k) where
  IgnoreT :: forall e u t. e (IgnoreF u) t -> IgnoreT e u t

-- | Untyped terms.
newtype UExpr' t = UExpr'
  { unUExpr' :: IgnoreF (Fix1 (IgnoreT ExprF)) t }
```

In the definitions above `IgnoreF` does the existential quantification effectively allowing the types of subterms to ignore their types, but the expression itself must carry the type that is expected..


## One Final Representation

One final reprsentation that is worth considering is to allow for both typed and untyped terms
Morally, we can





Note that the kind of `IgnoreT` is `((k -> *) -> (k -> *)) -> (k -> *) -> (k -> *)`.
That is, it takes an indexed functor and returns a new indexed functor that ignores the stated index (the one that occurs in the type) and uses a new one that is existentially quantified.

So, how does it work out?
We can now write ill-typed terms, that are well-typed in Haskell.

```haskell
rewrap :: UExpr a -> UExpr b
rewrap (Fix1 (IgnoreT a)) = Fix1 (IgnoreT a)

uplus :: UExpr a -> UExpr b -> UExpr c
uplus l r = Fix1 (IgnoreT (Plus (rewrap l) (rewrap r)))

uint :: Int -> UExpr a
uint n = Fix1 (IgnoreT (NLit n))

ubool :: Bool -> UExpr a
ubool n = Fix1 (IgnoreT (BLit n))

bad :: UExpr Int
bad = uplus (uint 1) (ubool True)
```
{% endcomment %}

[^fn-sel-representation]: Self-representation is the ability to fully represent the syntax of a programming language within itself *and* write an interpreter the evaluates the syntax into the language itself. This is a very interesting property for topics such as [computational reflection](2015-10-03-computational-reflection-primer) and meta-programming.

[^fn-handling-the-fix]: In reality these types are really particular instantiations of more generic types. See, for example, [the Algebra module in compdata](https://hackage.haskell.org/package/compdata-0.11/docs/Data-Comp-Algebra.html).
