---
layout: post
category: reflections
title: Compositional (Co-inductive) Recursion in Coq
author: gregory malecha
tags:
- coq
- coinduction
- extensible effects
- semantics
- general recursion
mathjax: true
---

There have been several different articles that advocate for the use of **denotational semantics**, where we give a *function* from the syntax to another language that we already understand.  In Coq, the target language is often Gallina.
However, because all Gallina programs terminate, we can't give a direct interpretation of non-terminating programs. 
An alternative is to give a denotation of your source language through a co-inductive definition of traces.
The problem with this is that co-recursion is notoriously non-compositional in Coq.
The [paco](https://plv.mpi-sws.org/paco/) work provides a compositional proof rule for co-inductive types, but the is no similar definition for co-inductive definitions.
In this post I'm going to explain how to build a general recursion combinator in Coq that is completely composable- a surprisingly difficult problem that I pondered for a while in grad school.

The implementation of these ideas can be found in the [coq-interaction-trees](https://github.com/gmalecha/coq-interaction-trees) library.
*EDIT:* Since the original posting, I have started collaborating on these ideas in the [InteractionTrees repository](https://github.com/DeepSpec/InteractionTrees) repository.

## The Co-inductive Definition

One way to represent non-terminating computations is as a co-inductive data type.
Adam Chlipala addresses this [in his book](http://adam.chlipala.net/cpdt/html/Cpdt.GeneralRec.html), but the solution there isn't satisfying because it can't be written in a general way.
Adam gives the following example (notations removed), trying to define the Fibonacci function co-inductively[^fn-fibonacci].

```coq
CoInductive thunk (A : Type) : Type :=
| Answer : A -> thunk A
| Think : thunk A -> thunk A.

CoFixpoint fib (n : nat) : thunk nat :=
  match n with
    | 0 => Answer 1
    | 1 => Answer 1
    | _ =>
	  TBind (fib (pred n)) (fun n1 =>
	  TBind (fib (pred (pred n))) (fun n2 =>
	  Answer (n1 + n2)))
  end.
```

Gallina rejects this definition by saying that the recursive call to `fib` is not "guarded".
Intuitively, this means that Gallina can not guarantee that there is a finite amount of computation between two adjacent constructors.
In the definition of `fib` above, it turns out that there is, but the syntactic check that Coq does is too conservative to prove this.


## Enter Extensible Effects

To get around the guardedness check we are going to generalize the `thunk` type above into a free monad.
Here's the new definition.

```coq
Section Eff.
  Variable eff : Type -> Type.

  CoInductive Eff (T : Type) : Type :=
  | Pure : T -> Eff T
  | Delay : Eff T -> Eff T
  | Interact : forall {U}, eff U -> (U -> Eff T) -> Eff T.
End Eff.
```

Here, the entire `Eff` definition is parameterized over an algebra of effects (`eff`.
The first two constructors are exactly the same as `Answer` and `Think`, and the `Interact` constructor allows us to appeal to `eff`.

On top of this definition, it isn't too difficult to define monadic bind by co-induction.

```coq
Section bind.
  Context {A B} (k : A -> Eff B).
  CoFixpoint bind' (c : Eff a) : Eff B :=
    match c with
	| Pure v => k v
	| Delay d => Delay (bind' d)
	| Interact e k' => Interact e (fun x => bind' (k' x))
	end.
End bind.

Definition bind {A B} c k := @bind' A B k c.
```

It is important, but subtle, that we lift the continuation to not be a parameter to the co-fixpoint due to Coq's rule for reducing co-fixpoints[^fn-reducing-cofixpoint].
In essence, without this lifting, Coq's guardedness check (like its well-founded check) can not infer that the `k` argument is constant across co-recursive calls (similarly for the well-founded check on fixpoints).

### The Problem with mfix

Using this definition (even the previous definition of `thunk`) it is trivial to implement "diverging" computations, i.e. ones that never produce a `Pure` (or `Answer`).
So, one might assume that we could implement a [fix-point combinator](https://en.wikipedia.org/wiki/Fixed-point_combinator) that wraps up this recursion appropriately.
In Gallina, this function would have the following type[^fn-mfix-haskell].

```coq
CoFixpoint mfix_attempt (f : (a -> Eff eff b) -> a -> Eff eff b)
: a -> Eff eff b.
```

Naively, one would expect this function to have a very simple implementation:

```coq
CoFixpoint mfix_attempt (f : (a -> Eff eff b) -> a -> Eff eff b)
: a -> Eff eff b :=
  f (mfix f).
```

However, Coq *rightfully* rejects this definition because it isn't guaranteed to be productive.
To give a simple example for the problem, suppose Coq accepted this definition and we called `mfix` with the identity function.

```coq
mfix_attempt id = id (mfix_attempt id) = id (id (mfix_attempt id)) = ...
```

As Coq tries to reduce this term it never finds a constructor so, by our intuition above, the definition is not guarded.
One might (accurately) say that we shouldn't call `mfix` with `id`, but instead with `Delay`.
Doing this would cause us to have an infinite tower of `Delay`s, which is exactly what we want.  However, it isn't sufficient to show that the function is guarded for some calls, it has to be guarded **for any** `f`.

One might think that we can address this problem by inserting the `Delay` into the definition itself.

```coq
CoFixpoint mfix_attempt2 (f : (a -> Eff eff b) -> a -> Eff eff b)
: a -> Eff eff b :=
  Delay (f (mfix f)).
```

Now, if we instantiate `f` with `id` we get the nice (guarded) tower of `Delay`s that we expect.
However, Coq still *rightfully* rejects this definition because not *all* uses of `mfix` are guarded.
Here's a simple definition that breaks guardedness.

```coq
Definition a_little_faster (rec : a -> Eff eff b) (x : a) : Eff eff b :=
  match rec x with
  | Pure y => Pure y
  | Interact e k => Interact e k
  | Delay y => y
  end.
```

Just to demonstrate the problem, let's look at the unrolling.


```coq
  mfix_attempt2 a_little_faster x
= Delay (a_little_faster (mfix_attempt2 a_little_faster) x)
= Delay (match mfix_attempt2 a_little_faster x with
         | ...
		 | Delay y => y
		 end)
= Delay (match Delay (a_little_faster (mfix_attempt2 a_little_faster) x) with
         | ...
		 | Delay y => y
		 end)
= Delay (a_little_faster (mfix_attempt2 a_little_faster) x) (* cycle *)
```

We do get the head `Delay` like we expect, but after that `a_little_faster` takes a function that appears guarded and makes it unguarded by dropping the head constructor that is actually doing the guarding.

### An Attempt with Parametricity

The problem with `a_little_faster` is that it inspects the `rec` function rather than simply calling it.
The above definition of `mfix` would be great if we could require that `f` uses the recursive call only by calling it and not pattern matching on the result.
If Coq had parametricity built in then we might be able to achieve this by generalizing over the use of `Eff eff` in the body of the fixpoint.
Something like:

```coq
CoFixpoint mfix_param
  (f : forall eff' (inj : forall a, eff a -> Eff eff' a),
                   (a -> Eff eff' b) -> (a -> Eff eff' b))
: a -> Eff eff b :=
  fun x => @f eff (fun _ e => Interact e ret) (mfix f).
```

Here the `f` becomes a little bit more complicated because we parameterize over `m` but we also want a way to do all the effects that we used to be able to do, i.e. those allowed by `Eff eff`, which is what the `inj` argument does.
While we can actually implement this function, the naive definition above does not work.
Coq again rejects it due to guardedness, though one could argue that, assuming parametricity, this definition is guarded, it would be difficult to capture the property algorithmically.
For example, if `f` also takes a function `forall a, m a -> Eff eff a`, then parametricity no longer guarantees the guardedness condition.

## Enforcing Parametricity with Effects

Since Coq doesn't have parametricity built in, we need to enforce it ourselves.
Essentially, we need to build a sub-language of Gallina that represents functions that use their argument in a limited way (essentially it only `bind`s their result).
This may seem like a tall order, but in actuality it isn't as difficult as one might think; essentially the entire problem lies in the use of the "middle" arrow in the type of `f`, i.e.

```coq
CoFixpoint mfix_attempt
  (f : (a -> Eff eff b) -> (* <-- this arrow! *)
        a -> Eff eff b)
: a -> Eff eff b.
```

This arrow says that we can use all of Gallina to implement the body of the recursive function.
If we want to restrict the things that the body can do, we simply need to replace this arrow with a more restricted representation of functions.
For our purposes, one easy thing to do is to represent the idea of making a recursive call as *an effect*.
Here, we could write the following[^fn-generalize-dependent-function]:

```coq
Inductive fixpoint a b : Type -> Type :=
| call (_ : a) : fixpoint a b b.

CoFixpoint mfix
  (f : a -> Eff (bothE eff (fixpoint a b)) b)
: a -> Eff eff b.
```

In this phrasing of the "function," we offer access to the argument (which is the recursive call) only through the effect layer of `Eff` (namely the `fixpoint`/`call` effect).
Thus, if the `f` function can not inspect the body of the recursive call, it only sees the constructor.

The implementation of `mfix` is surprisingly simple.
Essentially, all we need to do is to interpret the added `fixpoint` effect using the usual interpretation mechanism (which I am inling here).

```coq
Section mfix.
  Variable f : forall x : a, Eff (bothE eff fixpoint) (b x).

  CoFixpoint finterp {T : Type}
             (c : Eff (bothE eff fixpoint) T)
  : Eff eff T :=
    match c with
    | Pure x => Pure x
    | Interact (Left e) k =>
      Interact e (fun x => finterp (k x))
    | Interact (Right e) k =>
      match e in fixpoint X return (X -> _) -> _ with
      | call x => fun k =>
        (* interpret the call by running `f` on `x` *)
        Delay (finterp (bind (f x) k))
      end k
    | Delay x => Delay (finterp x)
    end.

  Definition mfix (x : a) : Eff eff b :=
    finterp (f x).
End mfix.
```

Note that we are interpreting `f x` by replacing all occurrences of `Right (call x)` with `finterp (f x)`.
In the code, since `Interact` carries its continuation (`k` which also needs to be interpreted), this is written `finterp (bind (f x) k)`.
The dependent pattern match on `e` is simply necessary to justify the fact that the type of `k` accepts the value returned by the recursive call.

We can actually use this implementation to implement `mfix_param`.

```coq
CoFixpoint mfix_param
  (f : forall eff' (inj : forall a, eff a -> Eff eff' a),
                (a -> Eff eff' b) -> (a -> Eff eff' b))
: a -> Eff eff b :=
  fun x =>
    mfix (f (bothE (Eff eff) (fixpoint a b))
		    (fun _ e => bind (Left e) ret)
			(fun x => Interact (Right (Call x))).
```


## Related Work

Interaction trees provide the underlying semantics for the [new version of Vellvm](https://github.com/vellvm/vellvm), and seem to be a topic of interest in [DeepSpec](https://deepspec.org/main), especially the work being done at UPenn.

Alternative styles of defining semantics can be used to get around this problem.
Classic small-step operational semantics are the swiss-army-knife that solve just about every semantic problem though purely syntactic methods.
Obviously there are huge benefits to this approach in terms of generality, but re-usability seems to be much harder since each semantics is specialized to its own syntax.
Arthur Charguéraud's [Pretty-Big-Step Semantics](https://www.chargueraud.org/research/2012/pretty/pretty.pdf) provides a way to encode the semantics of non-terminating programs using a relational representation.

The standard trick that has been proposed for solving this problem functionally is to use fuel.
However, fuel still only allows us to talk about terminating programs- we need an alternative definition to describe the semantics of non-terminating programs.
Similarly, in the presence of input, fuel breaks down.
Consider, for example, the program that reads an input integer and loops that many times before returning.
There is no finite amount of fuel that you know will be sufficient to run the program to completion *before* you read the input.
Thus, to use fuel you need to give a "fuel until next event" as a *function* from the variable context which requires a resumption monad which seems more complex, though I haven't looked deeply into it.


## Conclusions

I've never seen this encoding of fixpoints through effects before, though I'd be interested if it exists somewhere.
Any pointers in the comments would be greatly appreciated.

Moving forward, I'm interested to understand if I can define a generic logic, such as the step-indexed work of [the Iris project](http://iris-project.org/) on top of this semantic definition.
If so, it might provide a common ground for leveraging Iris (and the sophisticated techniques that it has built) to reason about new programming languages.

{% comment %}
In a similar vein, I, like [others](https://github.com/vellvm/vellvm), am hopeful that this semantic model can be used to define the semantics of many programming languages providing a common semantics that can be used to improve program linking.
{% endcomment %}


#### Footnotes

[^fn-earlier-big-step]: [Pretty-Big-Step Semantics](https://www.chargueraud.org/research/2012/pretty/pretty.pdf).

[^fn-fibonacci]: Note that the Fibonacci function should be defined inductively, and Coq will gladly accept the basic definition.

[^fn-reducing-cofixpoint]: [This gist](https://gist.github.com/gmalecha/09781e107fcac95cac8b74d615a1477e) gives a concrete example where the version using a `Section` (i.e. a regular lambda abstraction) succeeds and the version that simply makes them an argument to the `cofix` fails.

[^fn-mfix-haskell]: Unlike Haskell's [`mfix` from `MonadFix`](http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad-Fix.html), classical recursion combinators expose the functional form. This mimics the fact that Haskell *values* actually include non-termination, as opposed to the Haskell function space (which is total).

[^fn-generalize-dependent-function]: It is easy to generalize this to dependent functions, where the type of `b` is `a -> Type`.

<!--  LocalWords:  Compositional Coq gregory malecha coq coinduction
 -->
<!--  LocalWords:  mathjax denotational Gallina compositional paco fn
 -->
<!--  LocalWords:  combinator composable Chlipala CoInductive nat inj
 -->
<!--  LocalWords:  CoFixpoint TBind pred monadic fibonacci monad mfix
 -->
<!--  LocalWords:  guardedness forall fixpoint Coq's fixpoints bothE
 -->
<!--  LocalWords:  cofixpoint parametricity fixpoint finterp mfix
 -->
<!--  LocalWords:  param ret Vellvm
 -->
