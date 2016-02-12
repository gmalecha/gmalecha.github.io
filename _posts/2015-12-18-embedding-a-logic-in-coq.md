---
layout: post
category: blog
title: Embedding Logics in Coq
author: gregory malecha
tags:
- coq
- tutorial
highlight: true
---

Coq comes with a powerful, built-in logic (Gallina) with features such as inductive and dependent types, recursion, etc.
However, most uses of Coq don't study its theory, but rather use it as a foundation to reason about something else.
A few examples come to mind:

* The [Verified Software Toolchain](http://vst.cs.princeton.edu/) embeds a program logic for reasoning about C programs.
* [VeriDrone](http://ucsd-pl.github.io/veridrone/) embeds a temporal logic for reasoning about cyber-physical systems
* [Iris](http://plv.mpi-sws.org/iris/), [Charge!](http://www.itu.dk/people/jebe/project/), and others all embed different logics for reasoning about concurrent program.
* [Bedrock](http://plv.csail.mit.edu/bedrock/) embeds a logic for reasoning about low-level imperative programs.

Many of these systems are structured in a similar way, they build their logic on top of Gallina in a *shallow* way.
While shallow encodings are not good for everything, they often allow you to get to the heart of your problem very quickly so that you can think about the problems that you are interested in solving.
In this post, I'll talk about how to use the [Charge!](https://github.com/jesper-bengtson/Charge!) library to quickly embed a custom logic inside of Coq and reason about properties in it.
I'll start with a brief tour of the core piece of the library and then I'll show how to use it to quickly build a shallow embedding of a temporal logic.

The code for this post is available [on github](https://github.com/gmalecha/coq-temporal) and depends on [ExtLib](https://github.com/coq-ext-lib/coq-ext-lib) and [ChargeCore](https://github.com/jesper-bengtson/ChargeCore) [^fn-charge-core].
I will discuss a slightly [simplified version of the definitions](https://github.com/gmalecha/coq-temporal/blob/48755b2b6ea6148f41e02c2bb92d37ba89e857fa/theories/DiscreteLogic.v) which avoids the complexity of quotienting the underlying model.

## Describing Logics with Charge! ##

Charge! is a framework for defining different logical structures and reasoning with them.
Charge! is built using Coq's type class mechanism which makes it easy to build new logics from old ones.
The primary Charge! type class is the one for an intuitionistic logic.

~~~
Class ILogicOps (L : Type) : Type :=
{ lentails : L -> L -> Prop (* P |-- Q *)
; ltrue    : L
; lfalse   : L
; land     : L -> L -> L    (* P //\\ Q *)
; lor      : L -> L -> L    (* P \\// Q *)
; limpl    : L -> L -> L    (* P -->> Q *)
; lforall  : forall (T : Type), (T -> L) -> L (* Forall x : T, ...x... *)
; lexists  : forall (T : Type), (T -> L) -> L (* Exists x : T, ...x... *) }.
~~~

Here, an instance of `ILogicOps T` provides various functions for operations to construct intuitionistic logic formulas.
Just walking through the definitions.

  * `lentails` (written `|--`) states that the first formula entails/implies the second.
  * `ltrue` is the formula that means truth, and `lfalse` is the formula which means falsehood.
  * `land` (written `//\\`), `lor` (written `\\//`), and `limpl` (written `-->>`) are the binary connectives for conjunction, disjunction, and implication.
  * `lforall` and `lexists` are the universal and existential quantifiers of the logic[^fn-shallow-binders].

To show how a type, e.g. `Prop`, is an intuitionistic logic, we can implement an instance of `ILogicOps Prop` (also included in Charge!). Here's the definition.

~~~
Instance ILogicOps_Prop : ILogicOps Prop :=
{ lentails := impl
; ltrue    := True
; lfalse   := False
; land     := and
; lor      := or
; limpl    := impl
; lforall  := fun T P => forall x : T, P x
; lexists  := fun T P => exists x : T, P x }.
~~~

All of the operators for `Prop` come pre-packaged either in the standard library, e.g. `and` and `or` or in the logic itself, e.g. universal quantification.
{% comment %}
Note that the carrier (i.e. `T`) is  `Prop` we can use `impl : Prop -> Prop -> Prop` (which is defined to be `fun x y : Prop => x -> y`) for entailment.
In general, this will not work, but it does hint at the strong connection between implication and entailment.
{% endcomment %}


The `ILogicOps` type class mostly just provides a uniform way to access the combinators of arbitrary intuitionistic logics.
In addition, as we saw above, Charge! defines useful notation (with the correct precedence and associativity) for writing formulas in a fairly readable way.

The benefit of the uniform interface is the ability to state and prove properties about it.
In Charge!, the reasoning principles for `ILogicOps` are defined in the `ILogic` type class[^fn-separate-classes].

~~~
Class ILogic {A : Type} {ILOps: ILogicOps A} : Type :=
{ lentailsPre :> PreOrder lentails
; ltrueR   : forall (C : A), C |-- ltrue
; lfalseL  : forall (C : A), lfalse |-- C
; landR    : forall (P Q C : A), C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q
; landL1   : forall (P Q C : A), P |-- C  ->  P //\\ Q |-- C
; landL2   : forall (P Q C : A), Q |-- C  ->  P //\\ Q |-- C
; lorR1    : forall (P Q C : A), C |-- P  ->  C |-- P \\// Q
; lorR2    : forall (P Q C : A), C |-- Q  ->  C |-- P \\// Q
; lorL     : forall (P Q C : A), P |-- C  ->  Q |-- C  ->  P \\// Q |-- C
; landAdj  : forall (P Q C : A), C |-- (P -->> Q) -> C //\\ P |-- Q
; limplAdj : forall (P Q C : A), C //\\ P |-- Q -> C |-- (P -->> Q)
; lforallL : forall (T : Type) x (P: T -> A) C, P x |-- C -> lforall P |-- C
; lforallR : forall (T : Type) (P: T -> A) C, (forall x, C |-- P x) -> C |-- lforall P
; lexistsL : forall (T : Type) (P: T -> A) C, (forall x, P x |-- C) -> lexists P |-- C
; lexistsR : forall (T : Type) (x : T) (P: T -> A) C, C |-- P x -> C |-- lexists P }.
~~~

The first line states that `lentails` is a pre-order, namely that is reflexive and transitive.
The remaining lines are the standard introduction (post-fixed with an R) and elimation (post-fixed with an L) rules from logic.
For example, the rule `ltrueR` states that `ltrue` is provable under any assumptions (`C`).
`landR` states that a conjunction is provable if each of the conjuncts is provable.
The `limplAdj` and `landAdj` state that conjunction is the adjoint of implication.
Note that the rules governing the quantifiers essentially just lift the quantifier into Coq's logic.
For example, the rule `lforallR` replaces a universal quantifier within the logic in the conclusion with a universal quantifier in Coq's logic.

I won't show the definition of this class; the proofs are all trivially discharged by `firstorder`.
{% comment %}
The interested reader can find the definition in [the source code, look for ILogic_Prop](https://github.com/jesper-bengtson/Charge/).
{% endcomment %}

### Other Logics ###

In addition to `Prop`, the Charge! library contains several other useful instances of logics.
One of the most useful is function spaces into intuitionistic logics.
Formally, the instance is the following:

~~~
Instance ILogicOps_Fun (D : Type) {L : Type} (ILogicOps_L : ILogicOps L)
: ILogicOps (D -> L) :=
{ lentails := fun P Q => forall x : D, P x |-- Q x
; ltrue    := fun _ => ltrue
; lfalse   := fun _ => lfalse
; land     := fun P Q => (fun x => P x //\\ Q x)
; lor      := fun P Q => (fun x => P x \\// Q x)
; ltrue    := fun P Q => (fun x => P x -->> Q x)
; lforall  := fun T P => (fun x => lforall (fun y : T => P y x))
; lexists  := fun T P => (fun x => lexists (fun y : T => P y x)) }.

Instance ILogic_Fun {D L : Type} (ILO : ILogicOps L) (IL : ILogic L)
: ILogic (ILogicOps_Fun D ILO) := ...
~~~

All of the definitions in this class arise directly from point-wise lifting of the individual operators.
For example, `land P Q` is simply `(fun x => P x //\\ Q x)` where the conjunction is the conjunction from the intuitionistic logic on `L`.
In this logic, `P |-- Q` universally quantifies over the domain of the function and requires that `Q x` be provable under the assumptions in `P x`.

Charge! also contains other logics, for example, when `L` is a logic the following are also logics.

  * `option L` is the logic where `None` is interpreted as `lfalse` and `Some P` is interpreted as `P`
  * `D -> L` is a pre-order respecting logic when there is a pre-order on `D`. This is useful when you need built-in weakening properties such as in step indexing.

You can also define your own logics.
For example, VeriDrone defines an inductive data type for temporal logics and defines instances for `ILogicOps` and `ILogic` on it.
The only requirement is that the logic that you define must use a shallow encoding of local quantifiers in order to fit into the `ILogicOps` interface.

### Generic Theorems ###

The real benefit of using Charge! is the wealth of extra definitions and constructions that Charge! provides.
For example, `landC` and `lorC` prove the commutativity of `land` and `lor` respectively.
Charge! also provides generic proofs of the core morphisms used in logic.
For example, instances such as

~~~
Global Instance Proper_land_lentails {T} {ILO : ILogicOps T} {IL : ILogic T}
: Proper (lentails ==> lentails ==> lentails) land.
~~~

allow Coq's setoid rewriting mechanism to transparently rewrite on the left- and right-side of conjunctions within logical formulas.

While none of these pieces are individually very complex, writing them all is quite time consuming.
By re-using the generic proofs in Charge!, we can drastically reduce the amount of boiler-plate that we need before we have a useful logic.

### Custom Tactics & Automation ###

In addition to useful lemmas, using Charge! also gives you access to some generic automation.
At the moment, there is not a lot of it, but I have been extending it since we have been using Charge! in the [VeriDrone](http://ucsd-pl.github.io/veridrone/) project.
At the moment, the automation includes the following basic tactics that mimic their Coq counter-parts.

* `charge_intro` and `charge_intros`
* `charge_left` and `charge_right`
* `charge_split`
* `charge_exists` and `charge_eexists`
* `charge_assumption`
* `charge_revert`
* `charge_apply` (currently not very robust)

In addition, `charge_tauto` combines much of this reasoning into an automated procedure for deciding simple tautologies.
Neither `charge_tauto` or `charge_apply` are as featureful as their primitive Ltac counter-parts, but they do simplify the proving process.

I plan to keep adding to this list as I continue to use Charge!, and hopefully others will do the same.
In addition, Jesper Bengtson and I are currently applying [MirrorCore and Rtac](https://github.com/gmalecha/mirror-core/) to write reflective tactics that reason about generic intuitionistic logics.
This should make reasoning about very large formulas substantially more efficient.


## Example: Defining a Temporal Logic ##

With the preliminaries of Charge! behind us, I'll now describe the process of using Charge! to quickly build an shallow embedding of a linear-time temporal logic.
This logic is quite similar to the logic that we use in the VeriDrone project and in our recent work we have found this approach substantially more expressive than our previous logic.

When building a shallow embedding of a logic, the first step is to define the model that the predicates in the logic are about.
In discrete-time temporal logic, the model is an infinite sequence of states, which we will call a "trace".
In this post, I will cheat and use `nat -> State` to represent traces because it simplifies things.
This choice means that our definitions will depend on functional extensionality, but there are other choices that we could make to remove this dependency.

~~~
Definition trace (T : Type) : Type := nat -> T.
~~~

To separate concerns, traces are parametric in the type of states.
For example, `trace nat` represents traces where the state is a single natural number.
In the first version of the VeriDrone project, we used total functions from `string` to `R`.

Using this model, a discrete-time temporal logic formula is simply a predicate over these traces.
In Coq, this is expressed by the following:

~~~
Definition TraceProp (T : Type) : Type := trace T -> Prop.
~~~

Since `Prop` is an intuitionistic logic, `TraceProp` is an intuitionistic logic by lifting (recall `ILogic_Fun`).
We get this for free from Charge!'s type classes with the following defintions.

~~~
Global Instance ILogicOps_TraceProp (T : Type) : ILogicOps (TraceProp T) := _.
Global Instance ILogic_TraceProp (T : Type) : ILogic (TraceProp T) := _.
~~~

Note that Coq's elaboration mechanism fills in the `_` using the Charge! instance automatically.
These four lines give us the core intuitionistic logic operators, e.g. entailment, conjunction, disjunction, etc, as well as their reasoning principles and the tactics that we discussed above.
That is pretty concise, considering that the original VeriDrone code not using Charge! required several hundred lines to define only a fraction of the reasoning principles that we get for free.

### Logic-specific Definitions ###

The above definition gives us the core intuitionistic logic operators, but it does not give us any structure of a temporal logic.
However, because `TraceProp` is a definition, we can easily write the temporal logic operators as definitions which peek into the implementation.

~~~
Definition next {T} (P : TraceProp T) : TraceProp T :=
  fun tr : trace T => P (fun t => tr (S t)).

Definition Always {T} (P : TraceProp T) : TraceProp T :=
  fun tr : trace T => forall n : nat, P (fun t => tr (n + t)).
Notation "[] P" := (Always P) (...).

Definition Eventually {T} (T : TraceProp T) : TraceProp T :=
  fun tr : stream T => exists n : nat, P (fun t => tr (n + t)).
Notation "<> P" := (Eventually P) (...).
~~~

With these definitions, we can now prove standard reasoning principles from temporal logic such as the distributivity of conjunction over always.

~~~
Theorem Always_distr_and {T} : forall P Q : TraceProp T, [] P //\\ [] Q -|- [] (P //\\ Q).
Proof. compute. firstorder. Qed.
~~~

We can also prove more interesting properties such as temporal induction:

~~~
Theorem temporal_induction {T} : forall P : TraceProp T, |-- P -->> [](P -->> next P) -->> [] P.
Proof. ... Qed.
~~~

Proving properties like these tends to be quite easy for simple definitions.
The general strategy is to break the Charge! abstraction and reason directly about the definitions.
However, once we prove the theorems, we can use them to *reason within the logic* without seeing the underlying model.

{% comment %}
In addition to the normal theorems, it is useful to prove the `Proper`ness of these new operators.
For example, the following theorem states that always respects entailment.

~~~
Gloal Instance Proper_always_lentails : Proper (lentails ==> lentails) always.
Proof. ... Qed.
~~

Proofs of this variety hook into Coq's setoid rewriting mechanism to allow rewriting terms that occur under always.
For example, running `rewrite <- H` on the following goal

~~~
H : P |-- Q
================
|-- always Q
~~~

will result in

~~~
H : P |-- Q
================
|-- always P
~~~
{% endcomment %}

### A Family of Logics ###

Since `TraceProp` is parametric in the state, we actually have a family of temporal logics.
For example, `TraceProp nat` is a logic over natural number states while `TraceProp (R * R)` is a logic over pairs of real numbers.
With this in mind, we can show relationships between these different logics by describing the relationship between the underlying streams.
The following `focusT` operator shows us what this means [^fn-focus].

~~~
Definition focusT {T U : Type} (view : T -> U) (P : TraceProp U) : TraceProp T :=
  fun tr => P (fun t => view (tr t)).
~~~

Focusing provides a convienient framing rule that allows us to build complex formulas from smaller ones in a very modular way.
Take for example a formula that describes two variables that both increase.
If we have `increases : TraceProp nat` that describes when a trace of natural numbers is increasing, then we can compose it with itself by using `focusT` to "focus" it on the individual components.

~~~
Definition both_increase : TraceProp (nat * nat) :=
  focusT fst increases //\\ focusT snd increases.
~~~

We can also use focusing to apply simulations.
For example, suppose that we would like to convert a predicate that deals with polar coordinate into one that deals with rectangular coordinates.
Using focusing, we simply apply the transformation to the trace.

~~~
Record PolarCoord := { r : R ; theta : R }.
Record RectCoord := { x : R ; y : R }.

Definition polar_to_rect (polar : PolarCoord) : RectCoord :=
  {| x := polar.(r) * Rcos polar.(theta)
   ; y := polar.(r) * Rsin polar.(theta) |}.

Definition to_polar (P : TraceProp RectCoord) : TraceProp PolarCoord :=
  focusT polar_to_rect P.
~~~

This is just the tip of the iceberg in terms of temporal logic.
There are a lot more constructions and reasoning principles that we have defined on top of our shallow embedding.


{% comment %}
We can also easily decribe auxiliary state using "temporal existential quantification."
While standard existential quantification introduces a variable that is static across states, temporal existential quantification introduces a variable that can change between the states.
In essence, it existentially quantifies a new trace fragment and combines it with the state that already exists.
The definition is the following:

~~~
Definition Texists {T U : Type} (P : TraceProp (T * U)) : TraceProp U :=
  fun tr : trace U => exists tr' : trace T, P (trace_zip tr' tr).
~~~

The rules that we prove about `Texists` allows us to easily add history variables that expose the previous values of a variable in a list.
{% endcomment %}



## Recap ##

In this post I described the basics of Charge! and gave a simple example of how to use it to define the very core of a temporal logic.
Charge! is a extremely convenient for rapid prototyping of logics because it takes care defining the basic notation, core operators, a wealth of theorems, and even a bit of automation.
In addition, we get to build on top of all of Coq's existing features.
For example, we get strong types when we write formulas and we get Coq's proof language to provide foundational guarantees.

Charge!'s type classes also provide guidance in defining "sensible" logics.
On more than one occasion I have sketched out a logic only to realize that one or two of the axioms is unprovable in the model.
When this happens, it is a good indication that something is not what it seems and it is a good idea to revisit your definitions to see what does not work.

**Aside** Right now, the biggest pain point that I have encountered in using Charge is notation for base assertions.
Everything that I discussed in this post quantified over base assertions such as `increasing` but when we use the logic to reason about real formulas, we wil be reasoning about these definitions.
The lazy-man's solution is to simply break the abstraction and write functions everywhere, but this tends to be quite ugly.
Charge! contains some fancy notation for easily lifting predicates and functions to work within embedded logics, but that will be the topic of another post.

Despite this current shortcoming, I encourage everyone to give Charge! a try for your next project and to contribute any useful definitions or automation back to the Charge! project so that others can make use of your work.


### External Pointers ###

The [ChargeCore](https://github.com/jesper-bengtson/ChargeCore) repository is maintained by [Jesper Bengtson](http://www.itu.dk/people/jebe/) and is a stripped down version of the [Charge!](https://github.com/jesper-bengtson/Charge) library.
The first version of Charge! was described in [this paper](http://www.itu.dk/people/jebe/charge.pdf).
Charge! is quite similar to the logical foundations of the [Verified Software Toolchain](http://vst.cs.princeton.edu/) developed by Andrew Appel and his collaborators for reasoning about C programs.
Lars Birkedal's new [ModuRes framework](http://users-cs.au.dk/birke/modures/) also uses similar definitions though they are architected in a different way.
{% comment %}
In the upcoming [Coq 8.5](https://coq.inria.fr/news/126.html) release, [opam](https://coq.inria.fr/howto-opam) will be the officially sanctioned way to manage Coq libraries, but it can still be useful to minimize dependencies.
{% endcomment %}



[^fn-charge-core]: ChargeCore is a slimmed down version of [Charge!](https://github.com/jesper-bengtson/Charge!). 

[^fn-shallow-binders]: Note `lforall` and `lexists` use the binders of Gallina (Coq's programming language) to represent bound variables. This choice allows us to reuse much of Gallina in writing predicates.

[^fn-separate-classes]: Jesper refers to this as the "Dutch-style" due to its use in the [Math Classes project](https://github.com/math-classes/math-classes). See, for example the [definition of functors](https://github.com/math-classes/math-classes/blob/master/interfaces/functors.v). There are pros and cons to this style, but I'll leave an extensive discussion of that for another post.

[^fn-focus]: Readers familiar with CoFunctors will note that `focusT` is none other than `cofmap`.
LocalWords:  Gallina Coq intuitionistic lentails ltrue lfalse lor
LocalWords:  limpl disjunction lforall lexists ILogicOps impl forall
