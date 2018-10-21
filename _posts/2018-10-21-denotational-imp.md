---
layout: post
category: reflections
title: A Denotational Semantics for an Imperative Language
author: gregory malecha
tags:
- coq
- interaction trees
- extensible effects
- semantics
- denotational semantics
mathjax: true
---

In [my last post]({% post_url 2018-06-29-compositional-coinductive-recursion-in-coq %}) I presented an implementation of a fixpoint combinator in Coq.
In this post, I'm going to show how that technique can be used to give a compositional denotational semantics to [Imp, a simple imperative programming language](https://mitpress.mit.edu/books/formal-semantics-programming-languages).
I'm not going to pretend to cover all the corner cases of C in this post (perhaps a future post), but rather will focus on the general recipe for defining semantics using co-inductive effects.

[The full definitions described in this post are available as a gist](https://gist.github.com/gmalecha/5d2ed61c5951b9f285d9da29caa4a771).

# C-ish

First, let's start with the syntax of Imp.

```coq
Inductive expr : Set :=
| Evar (_ : var)
| Econst (_ : nat)
| Eplus (_ _ : expr).

Inductive stmt : Set :=
| Sassign (x : var) (e : expr)    (* x = e *)
| Sseq    (a b : stmt)            (* a ; b *)
| Sif     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| Swhile  (t : expr) (b : stmt)   (* while (t) { b } *)
| Sskip.                          (* ; *)
```
The expression language (`expr`) isn't particularly interesting here because, unlike statements, expressions are guaranteed to terminate.
In the statement language (`stmt`) we have the standard definitions for an imperative language, assignment (`Assign`), sequencing (`Seq`), conditionals (`If`), while-loops (`While`), and a no-op (`Skip`).

# A Denotational Semantics

A standard way to define the meaning of this language would be through a small-step operational semantics.
There are plenty of [examples of small-step operational semantics](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html#lab133), so I won't belabor the definition anymore.
Big-step semantics are a bit more subtle because the programs above can diverge and we need to give them a meaning as well.

In this post, however, we're going to ascribe a denotational semantics to our language by translating it into Gallina.
Of course, we would immediately run into a problem if we tried to give a naive definition because Gallina doesn't allow for non-termination, which is required when giving a meaning to `Swhile`.

However, our co-inductive interaction trees do allow non-terminating programs, so instead of denoting into vanilla Gallina, we'll denote into interaction trees.
The first step in doing that is to define the effects that our language uses.
We could thread the local variable state explicitly, but instead, let's use effects for it just so show how they work.
Here's a simple definition for the operations that we need for dealing with local variables:

```coq
Inductive Locals : Type -> Type :=
| GetVar (x : var) : Locals value
| SetVar (x : var) (v : value) : Locals unit.
```

Here's the denotation function for expressions and statements using [ExtLib's monad notation](https://github.com/coq-ext-lib/coq-ext-lib).

```coq
(* Denotation for expressions *)
Fixpoint denoteExpr (e : expr) : itree Locals value :=
  match e with
  | Evar v => do (GetVar v)
  | Econst v => ret v
  | Eplus a b => l <- denoteExpr a ;; r <- denoteExpr b ;; ret (a + b)
  end.

(* A `while` combinator *)
Definition while {eff} (t : itree eff bool) (body : itree eff unit)
: itree eff unit :=
  mfix (fun _ : unit => unit)
       (fun _ _ inj rec _ =>
          continue <- inj _ t ;;
          if continue
          then body ;; rec tt
          else ret tt) tt.

(* Denotation for statements *)
Fixpoint denoteStmt (s : stmt) : itree Locals unit :=
  match s with
  | Sassign x e =>
    v <- denoteExpr e ;;
    Do (SetVar x v)
  | Sseq a b =>
    denoteStmt a ;; denoteStmt b
  | Sif i t e =>
    v <- denoteExpr i ;;
    if is_true v then denoteStmt t else denoteStmt e
  | Swhile t b =>
    while (v <- denoteExpr t ;; ret (is_true v))
          (denoteStmt b)
  | Sskip => ret tt
  end.
```

The cases translate Imp statements into our effectful computation type.
Sequencing is probably the best example of this where `;` denotes directly to `;;` (`ExtLib's` equivalent of `>>`).
`Sassign` and `Sif` are similar, denoting the subterms and composing them appropriately.
The `Swhile` case is the interesting one.
There, we use the `mfix` operator that [we defined previously]({% post_url 2018-06-29-compositional-coinductive-recursion-in-coq %}) to implement a `while` combinator and use it to give the meaning of the loop[^fn-while-combinator].

## Interpreting the Environment

At this point we have have translated Imp into Gallina, giving us a semantics for the language; however, the semantics aren't very specific about the treatment of local variables.
For example, consider the denotation for the program `x = 1; y = x + 1`.

```coq
denoteStmt (Sseq (Sassign "x" (Elit 1))
                 (Sassign "y" (Eplus (Evar "x") (Elit 1))))
== (* after some forcing *)
   Do (SetVar "x" 1) (fun _ : unit =>
   Do (GetVar "x") (fun x : value =>
   Do (SetVar "y" (x + 1))))
```

We would expect that we would know the value of `y` at the end of the program, but instead, the interaction tree says that the value of `y` will be 1 more than whatever value we get when running `GetVar "x"`.
In essence, our semantics is "free" from the interpretation of the local variable environment.
This freedom lets us play with different instantiations of the environment without changing the semantics, but it also prevents use from usefully reasoning about our programs (in Imp, all the reasoning is about the values of variables after all!).

To complete our semantics, we need to give an interpretation of the `Locals` effect.
To do this, we give a stateful homomorphism from `Locals` to a "more primitive" effect.
The type of a stateful effect homomorphism is:

```coq
Definition eff_hom_s (s : Type) (eff eff' : Type -> Type) : Type :=
  forall t, eff t -> stateT s (itree eff') t.
```

Intuitively, we interpret every `eff` effect into a program that has `eff'` effects *using the state `s`* (which is threaded through using a state monad transformer).
What is convenient about this separation of concerns is that we can describe tha handling of effects independently of the programming language and we can reuse their definitions and meta-theory across different languages.

### Total Environments

If we decide that all variables should have default values, then we can pick `s` to be a function from variables to values.
We can write:

```coq
Definition evalLocals : eff_hom_s (var -> value) Locals Error :=
  fun _ e =>
    match e with
    | GetVar x =>
      st <- get ;;
      ret (st v)
    | SetVar x v =>
      modify (update x v) ;;
      ret tt
    end.
```

We can now interpret away the local variable effects to produce the following denotation (after some forcing):

```coq
interp_state evalLocals (denoteStmt (Sseq (Sassign "x" (Elit 1))
                                    (Sassign "y" (Eplus (Evar "x") (Elit 1))))) (fun _ => 0)
== (* after some forcing *)
   Tau (Tau (Tau (Ret (update "y" 2 (update "x" 1 (fun _ => 0)), tt))))
```

#### The Burden of Tau
Here, we get `Tau`s as interpretation artifacts because our interpretation is a cofixpoint over our interaction tree and therefore needs to be productive/guarded.
To see why this is essential, suppose that you started out with a computation that repeatedly added 1 to the variable `x`.
After interpretation, *all* of the effects would be gone, and there would still be no result!
This would be an instance of an infinite amount of computation necessary to observe the head constructor, which is clearly problematic.

To clean up these `Tau` transitions, we almost always reason about our programs up to *finite* stuttering.
In practice this means that every interaction tree is equivalent (up to finite stuttering) to a value of the following type.

```coq
CoInductive pitree (eff : Type -> Type) (t : Type) : Type :=
| Pret (_ : t)
| Pvis {u} (_ : eff u) (_ : u -> pitree eff t)
| Ploop.
```

Of course, only the conversion from `pitree` to `itree` is decidable, going the other way requires solving the [halting problem](https://en.wikipedia.org/wiki/Halting_problem).

While the types are equivalently expressive, it is important to note that `itree` (which uses `Tau`) is **substantially more modular** exactly because the haulting problem is undecidable (especially in constructive logic).
We would not be able to implement `interp` on `pitree` exactly because when an effect was fully interpreted away, we would have to determine whether the rest of the program will immediately enter an infinite loop.


### Partial Environments

If we choose a more C-style semantics where variables must be initialized before they are used, we can use partial functions from variabls to values.
However, in this case we need to add a new effect to track runtime errors that ocur when programs read uninitialized variables.
Here's our error effect:

```coq
Inductive Error : Type -> Type :=
| RuntimeError (msg : string) : Error Empty_set.
```

For convenience, I've added strings to the error effect allowing us to document the reason for the error, but this isn't strictly necessary[^fn-alternate-errors].

```coq
Definition evalLocals : eff_hom_s (var -> option value) Locals Error :=
  fun _ e =>
    match e with
    | GetVar x =>
      st <- get ;;
      match st x with
      | None =>
        x <- do (RuntimeError ("variable `" ++ x ++ "` not defined")) ;;
        match x : Empty_set with end
      | Some v => ret v
      end
    | SetVar x v =>
      modify (update x v) ;;
      ret tt
    end.
```

Note that we can use either of these effect interpreters to "complete" the semantics of `Imp`.
If I recall correctly, the default semantics for Imp is the one with total environments.

# Adding Functions

If we wish to add function calls to our language, things don't get much more complex.
First, we need to add function calls to our syntax tree.
For simplicity, we'll put them in the expression language (therefore making them all return a value).

```coq
Inductive expr : Set :=
| ...
| Ecall (fn : expr) (x : expr).
```

Note that by using `expr` here for the type of `fn` were are making functions first-class values.
Also, purely for simplicity, we are making them take a single parameter, generalizing this to lists just means that we have to map when computing the arguments.

As with the interpretation of variables, we will abstract the definition a little bit by introducing an effect to represent function calls.

```coq
Inductive Calls : Type -> Type :=
| Call (fn : value) (x : value) : Calls value.
```

Given that the effect is essentially identical to the syntax, it isn't too surprising that extending `denoteExpr` to support `Ecall` is fairly trivial.
We use `:+:` (called [`+'` in the interaction trees library](https://github.com/DeepSpec/InteractionTrees/blob/master/theories/OpenSum.v#L30)) to represent the union of two effects, i.e. an `itree (A :+: B) t` can do *both* `A` actions and `B` actions.


```coq
Fixpoint denoteExpr (e : expr) : itree (Locals :+: Calls) value :=
  match e with
  | ...
  | Ecall fn arg =>
    fnValue <- denoteExpr fn ;;
    argValue <- denoteExpr arg ;;
	Do (Call fnValue argValue)
  end.
```

Essentially, we are postponing the implementation of the calling logic to the effect interpreter.
This insulates `denoteExpr` and `denoteStmt` from the implementation of the `value` type, preventing us from having to update these if we add new types, e.g. structures, unions, etc.


## Functions Are IO

The generality of our implementation of functions (and indeed our other effects) means that we can actually use the same technique to model calls to functions defined in other languages and I/O.
Note that when we define our interpreter for an effect, we can tract any information that we might need.
In the case of locals, we tracked the local variable environment, but in the case of external functions or I/O, we can track the trace of all of the (external) function calls that we make.
To see concretely how this would work, we can give a completely generic interpretation of interaction trees into traces[^fn-alternatives].

```coq
CoInductive trace (eff : Type -> Type) (t : Type) : Type :=
| TEnd (_ : t)
| TSend {u} (_ : eff u) (_ : traceK eff t u)
| TNever
with traceK (eff : Type -> Type) (t u : Type) : Type :=
| TKRecv (_ : u) (_ : trace eff t)
| TKNever.

CoInductive is_trace {eff : Type -> Type} {t}
: itree eff t -> trace eff t -> Prop :=
| is_trace_ret {v} : is_trace (Ret v) (TEnd v)
| is_trace_tau {it t} : is_trace it t -> is_trace (Tau it) t
| is_trace_send {u e itk kt} : is_traceK ikt kt -> is_trace (Vis e ikt) (Send e kt)
| is_trace_never {it} : Diverges it -> is_trace it TNever
with is_traceK {eff : Type -> Type} {t}
: forall {u}, (u -> itree eff t) -> traceK eff t u -> Prop :=
| is_traceK_recv {u} {v : u} {it} {t} : is_trace (it v) t -> is_traceK it ((TKRecv v t)
| is_traceK_never {u} {it} : Diverges it ->  @is_trace eff t u it TKNever.
```

This definition is slightly more complex than the standard one where we use lists of pairs of the action taken and the response for two reaons.
First, since interaction trees are co-inductive, we need co-inductive lists (our type also includes the information "returned" by the computation) in order to account for the fact that an infinite number of interactions can occur.
Second, separating `Send` and `Recv` makes it possible to model events that never return, e.g. the return value is `Empty_set`.
Note that here I am collapsing an infinite number of `Tau`s (described by `Diverges`) into `TKNever`.
We need to do something similar in the trace type since this particular trace definition opts to drop consecutive `Tau` constructors.

# Conclusions

In this post I demonatrated how to use interaction trees to give a compositional denotational semantics to imperative programs.
The style leverages two properties of interaction trees.
First, the co-inductive nature of interaction trees allows them to naturally capture non-termination.
Second, algebraic effects (the name for the style used here) are composable allowing me to add additional effects without dramatically changing the underlying effect definition.

I've also done some experiments encoding more interesting control flow such as `break` and `continue` on top of these definitions.
Those results, however, will have to wait for another post (if there is interest).

#### Footnotes

[^fn-while-combinator]: While (no pun intended) this makes our semantics a bit more readable here, if we extend the language with richer control flow, e.g. `try-catch` or `break`, we need to abandon this definition in favor of a richer recursive structure.

[^fn-alternate-errors]: In an alternate implementation, we could different constructors of `Error` to track different error sources, or we could parameterize `Error` by a type of errors.

[^fn-parametricity]: The parametricity that we get is only a first-order sort of parametricity. Unlike the normal shallow encoding with Gallina, if we quantify over an `itree eff t`, we can actually inspect the `itree` to determine when the error occurs.

[^fn-alternatives]: There are several possible ways to define traces depending on whether you want to capture stuttering in the trace, or eliminate it. Different choices here make more sense depending on your particular interpretation of stuttering, i.e. if it is just a compositional representation of divergence, or it has some additional meaning, e.g. for step-indexing.

<!--  LocalWords:  Denotational gregory malecha denotational mathjax
 -->
<!--  LocalWords:  Gallina GetVar SetVar ExtLib's monad denoteExpr
 -->
<!--  LocalWords:  itree homomorphism
 -->
