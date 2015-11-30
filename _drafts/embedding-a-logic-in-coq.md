---
layout: post
category: blog
title: Embedding Logics in Coq
author: gregory malecha
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
In this post, I'll talk about how to use the [ChargeCore](https://github.com/jesper-bengtson/ChargeCore) library to quickly embed a custom logic inside of Coq and reason about properties in it.
I'll start with a brief tour of the core piece of the library and then I'll show how to use it to quickly build a shallow embedding of a temporal logic.

The code for this post is available [on github](https://github.com/gmalecha/coq-temporal) and depends on [ExtLib](https://github.com/coq-ext-lib/coq-ext-lib) and [ChargeCore](https://github.com/jesper-bengtson/ChargeCore).

## Describing Logics with Charge! ##

ChargeCore is a framework for defining different logical structures and reasoning with them.
It is built using Coq's type-class mechanism which makes it quite easy to leverage it for new logics.
The core ChargeCore type class is the following definition of an intuitionistic logic.

```coq
Class ILogicOps (L : Type) : Type :=
{ lentails : L -> L -> Prop
; ltrue    : L
; lfalse   : L
; land     : L -> L -> L
; lor      : L -> L -> L
; limpl    : L -> L -> L
; lforall  : forall (T : Type), (T -> L) -> L
; lexists  : forall (T : Type), (T -> L) -> L
}.
```

Here, an instance of ```ILogicOps T``` provides various functions for operations to construct intuitionistic logic formulae.

  * ```lentails``` (written ```|--```) states that the first formula entails the second.
  * ```ltrue``` is the formula that means truth, and ```lfalse``` is the formula which means falsehood.
  * ```land``` (written ```//\\```), ```lor``` (written ```\\//```), and ```limpl``` (written ```-->>```) are the binary connectives for conjunction, disjunction, and implication.
  * ```lforall``` and ```lexists``` are the universal and existential quantifiers of the logic[^fn-shallow-binders].

To show how a type, e.g. ```Prop```, is an intuitionistic logic, we can implement an instance of ```ILogicOps Prop``` (also included in ChargeCore). Here's the definition.

```coq
Instance ILogicOps_Prop : ILogicOps Prop :=
{ lentails := impl
; ltrue    := True
; lfalse   := False
; land     := and
; lor      := or
; limpl    := impl
; lforall  := fun T P => forall x : T, P x
; lexists  := fun T P => exists x : T, P x }.
```

We don't need to define any new operators for describing the logical structure, they are all standard from the Coq standard library (or primitive in the system).
For example, we use the standard conjunction, disjunction, and implication from the standard library to represent conjunction, disjunction, and impliciation in the logic.
Note that since ```T``` is  ```Prop``` we can use ```impl``` (which is defined to be ```fun x y : Prop => x -> y```) for entailment.
In general, this will not work, but it does hint at the strong connection between implication and entailment.


The ```ILogicOps``` type class mostly just gives us convenient notation (e.g. ```//\\``` or ```Forall``` defined with correct associativity and precedence levels.
This is convenient because writing those levels correctly is a bit cumbersome.
However, where ChargeCore really becomes useful is in reasoning.

In ChargeCore, the axioms about these operators are defined in the ```ILogic``` type class.

```coq
Class ILogic {A : Type} {ILOps: ILogicOps A} : Type :=
{ lentailsPre :> PreOrder lentails
; ltrueR: forall (C : A), C |-- ltrue
; lfalseL: forall (C : A), lfalse |-- C
; landR:  forall (P Q C : A), C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q
; landL1: forall (P Q C : A), P |-- C  ->  P //\\ Q |-- C
; landL2: forall (P Q C : A), Q |-- C  ->  P //\\ Q |-- C
; lorR1:  forall (P Q C : A), C |-- P  ->  C |-- P \\// Q
; lorR2:  forall (P Q C : A), C |-- Q  ->  C |-- P \\// Q
; lorL:   forall (P Q C : A), P |-- C  ->  Q |-- C  ->  P \\// Q |-- C
; landAdj: forall (P Q C : A), C |-- (P -->> Q) -> C //\\ P |-- Q
; limplAdj: forall (P Q C : A), C //\\ P |-- Q -> C |-- (P -->> Q)
; lforallL: forall (T : Type) x (P: T -> A) C, P x |-- C -> lforall P |-- C
; lforallR: forall (T : Type) (P: T -> A) C, (forall x, C |-- P x) -> C |-- lforall P
; lexistsL: forall (T : Type) (P: T -> A) C, (forall x, P x |-- C) -> lexists P |-- C
; lexistsR: forall (T : Type) (x : T) (P: T -> A) C, C |-- P x -> C |-- lexists P
}.
```

The first line states that ```lentails``` is a pre-order, namely that is reflexive and transitive.
The remaining lines are the standard introduction (post-fixed with an R) and elimation (post-fixed with an L) rules from logic.
For example, the rule ```ltrueR``` states that ```ltrue``` is provable under any assumptions (```C```).
```landR``` states that a conjunction is provable if each of the conjuncts is provable.
The ```limplAdj``` and ```landAdj``` state that conjunction is the adjoint of implication.
Note that the rules governing the quantifiers essentially just lift the quantifier into Coq's logic.
For example, the rule ```lforallR``` replaces a universal quantifier within the logic in the conclusion with a universal quantifier in Coq's logic.

I won't show the instance of this class; like ```ILogicOps_Prop```, this is also included in the ChargeCore library.
Plus, given the definitions above, most of these axioms can be proven by ```tauto``` and so the proovs are quite trivial.

The real benefit of using ChargeCore is what you get from these core definitions.
For example, ChargeCore contains a wealth of theorems about these logic operators that are proven with respect to any ```ILogic```.
For example, ```landC``` and ```lorC``` prove the commutativity of ```land``` and ```lor``` respectively.

In addition, ChargeCore also comes with generic proofs of the core morphisms used in logic.
For example, instances such as

```coq
Global Instance Proper_land_lentails {T} {ILO : ILogicOps T} {IL : ILogic T}
: Proper (lentails ==> lentails ==> lentails) land.
```

allow Coq's setoid rewriting mechanism to transparently rewrite on the left- and right-side of conjunctions within logical formulas.

While none of these pieces are individually extremely complex, writing them all is quite time consuming, and the fact that we can re-use the generic proofs in ChargeCore when we use it can drastically reduce the amount of boiler-plate that we need before we have a useful logic.

## Custom Tactics & Automation ##

In addition to useful lemmas, using ChargeCore also gives you access to some generic automation.
At the moment, there is not a lot of it, but it has been growing due to our use of it in the [VeriDrone](http://ucsd-pl.github.io/veridrone/) project.
At the moment, the automation includes the following basic tactics which mimic their Coq counter-parts.

* ```charge_intro``` and ```charge_intros```
* ```charge_left``` and ```charge_right```
* ```charge_split```
* ```charge_exists``` and ```charge_eexists```
* ```charge_assumption```
* ```charge_revert```
* ```charge_apply``` (currently not very robust)

In addition, ```charge_tauto``` combines much of this reasoning into an automated procedure for deciding simple tautologies.
Neither ```charge_tauto``` or ```charge_apply``` are as featureful as their primitive Ltac counter-parts, but they do simplify the proving process.

I plan to keep adding to this list as I continue to use ChargeCore, and hopefully others will do the same.
In addition, Jesper Bengtson and I are currently applying [MirrorCore and Rtac](https://github.com/gmalecha/mirror-core/) to write reflective tactics that reason about generic intuitionistic logics.
This should make reasoning about very large formulas substantially more efficient.

### Building Logics from Functions ###

In addition to ```Prop```, the ChargeCore library contains several other useful instances of logics.
One of the most useful is function spaces into intuitionistic logics.
Formally, the instance is the following:

```coq
Instance ILogicOps_Fun (D L : Type) (ILogicOps_L : ILogicOps L)
: ILogicOps (D -> L) :=
{ lentails := fun P Q => forall x : D, P x |-- Q x
; ltrue    := fun _ => ltrue
; lfalse   := fun _ => lfalse
; land     := fun P Q => (fun x => P x //\\ Q x)
; lor      := fun P Q => (fun x => P x \\// Q x)
; ltrue    := fun P Q => (fun x => P x -->> Q x)
; lforall  := fun T P => (fun x => lforall (fun y : T => P y x))
; lexists  := fun T P => (fun x => lexists (fun y : T => P y x))
}.
```

All of the definitions in this class arise directly from point-wise lifting of the individual operators.
For example, ```land P Q``` is simply ```(fun x => P x //\\ Q x)``` where the conjunction is the conjunction from the intuitionistic logic on ```L```.
Unlike in the definition of ```Prop```, ```lentails``` and ```limpl``` are no longer the same in this definition.
In particular, entailment universally quantifies over an element of the domain (```D```) element to build a proposition out of a function space.

## A Temporal Logic ##

With the preliminaries of ChargeCore behind us, I'll now describe the process of using ChargeCore to quickly build an shallow embedding of a linear-time temporal logic.
This logic is quite similar to the logic that we use in the VeriDrone project, but the implementation is completely different because it is built using a shallow encoding.

When building a shallow embedding of a logic, the first step is to define the model that the predicates in the logic are about.
In discrete-time temporal logic, the model is an infinite sequence of states.
We can define traces in in Coq using the following co-inductive definition (reference for co-induction?).

```coq
CoInductive trace (T : Type) : Type :=
| Cons : T -> trace T -> trace T.
```

To separate concerns, streams are parametric in the type of states.
That is, ```trace nat``` represents streams where the state is just a single natural number.
However, other choices are possible as well.
For example, in the VeriDrone project, we us total functions from ```string``` to ```R```.

Using this model, a discrete-time temporal logic formula is simply a predicate over these traces so we can write the following:

```coq
Definition TraceProp (T : Type) : Type := trace T -> Prop.
```

Since ```Prop``` is an intuitionistic logic, ```TraceProp``` is an intuitionistic logic by lifting.
We get this for free from Charge's type classes with the following defintions.

```coq
Global Instance ILogicOps_TraceProp (T : Type) : ILogicOps (TraceProp T) := _.
Global Instance ILogic_TraceProp (T : Type) : ILogic (TraceProp T) := _.
```

Note that Coq's elaboration mechanism fills in the ```_``` using the ChargeCore instance for intuitionistic logics over function spaces. This definition gives us the core intuitionistic logic operators.

### Logic-specific Definitions ###

The above definition gives us the core intuitionistic logic operators, but it doesn't give us any structure of a temporal logic. However, because ```TraceProp``` is a definition, we can easily extend it with the temporal logic operators.

```coq
Definition next {T} (P : TraceProp T) : TraceProp T :=
  fun tr : stream T => P (tl tr).

Definition Always {T} (P : TraceProp T) : TraceProp T :=
  fun tr : stream T =>
    forall n : nat, P (skipn st n).
Notation "[] P" := (Always P) (...).

Definition Eventually {T} (T : TraceProp T) : TraceProp T :=
  fun tr : stream T =>
    exists n : nat, P (skipn st n).
Notation "<> P" := (Eventually P) (...).
```

With these definitions, we can now prove standard reasoning principles from temporal logic such as the distributivity of conjunction over always.

```coq
Theorem Always_distr_and {T} : forall P Q : TraceProp T, [] P //\\ [] Q -|- [] (P //\\ Q).
Proof. ... Qed.
```

We can also prove more interesting properties such as temporal induction:

```coq
Theorem temporal_induction {T} : forall P : TraceProp T, |-- P -->> [](P -->> next P) -->> [] P.
Proof. ... Qed.
```

Proving properties like these tends to be quite easy for simple definitions.
You simply need to break the ChargeCore abstraction and reason directly about the definitions.
However, proving these theorems is still quite valuable because it allows you to *not break the abstraction* when you are working in the defined logic.

{% comment %}
In addition to the normal theorems, it is useful to prove the ```Proper```ness of these new operators.
For example, the following theorem states that always respects entailment.

```coq
Gloal Instance Proper_always_lentails : Proper (lentails ==> lentails) always.
Proof. ... Qed.
```

Proofs of this variety hook into Coq's setoid rewriting mechanism to allow rewriting terms that occur under always.
For example, running ```rewrite <- H``` on the following goal

```coq
H : P |-- Q
================
|-- always Q
```

will result in

```coq
H : P |-- Q
================
|-- always P
```
{% endcomment %}

## Logics within Logics ##

So far, we have a shallowly-defined discrete-time temporal logic. To complete our logical system, we'd like to define two more logics. First, predicates over states (called *state formulas*) so that we can easily make statements such as "the value of x in the current state is 1", and second, predicates over pairs of states (called *action formulas*) to represent the evolution of the system, for example "the value of x in the next state is 1 more than the value of x in this state".

{% comment %}
There are two ways to solve this problem. First, we could simply state that these are ```TraceProp```s, they are just special in that they only require a small part of the trace (this is the way that we accomplish this in our current formalism).
An alternative approach is to define two new logics, one for predicates over single states, and one for predicates over pairs of states.
{% endcomment %}
A nice way to solve this problem is using embeddings.
The idea is to define a new logic for each of state predicates and action predicates and provide definitions that embed these definitions into trace predicates.

Building on ChargeCore, it is quite easy to define both of these logics.

```coq
Definition StateProp (St : Type) : Type := St -> Prop.
Instance ILogicOps_StateProp {St : Type} : ILogicOps (StateProp St) := _.
Instance ILogic_StateProp {St : Type} : ILogic (StateProp St) := _.

Definition ActionProp (St : Type) : Type := St -> St -> Prop.
Instance ILogicOps_ActionProp {St : Type} : ILogicOps (ActionProp St) := _.
Instance ILogic_ActionProp {St : Type} : ILogic (ActionProp St) := _.
```

At this point we have three logics: ```StateProp``` is a logic over individual states, ```ActionProp``` is a logic over transitions between states, and ```TraceProp``` is a logic over entire traces.

{% comment %}
For these types to be useful, we need two things: first, a way to embed them inside of a trace, snd second, a way to write them.
{% endcomment %}

The basic way to embed a ```StateProp``` into a ```TraceProp``` is to assert that the state predicate holds on the first state.
This is accomplished using the ```now``` definition, similarly, for ```ActionProp```s we can state that the pair of the first transition (pair of states) satisfies the predicate.

```coq
Definition now {St : Type} (P : StateProp St) : TraceProp St :=
  fun tr : stream St => P (hd tr).

Definition discretely {St : Type} (P : ActionProp St) : TraceProp St :=
  fun tr : stream st => P (hd tr) (hd (tl tr)).
```

At this point, we can very easily write assertions that manipulate abstract predicates in any of these logics.
For example, given a predicate describing an initial state (a ```StateProp```) and a predicate describing the possible transitions of a system (an ```ActionProp```), we can easily construct a temporal logic formula representing the transitions of the entire system:

```coq
now Init //\\ [] (discretely Step)
```





## Recap ##

In this post I described the basics of ChargeCore and gave a simple example of how to use it to define a temporal logic.
ChargeCore is a extremely convenient for rapid prototyping of logics because it takes care defining the basic notation, core operators, a wealth of theorems, and even a bit of automation.
In addition, the type classes provide guidance in defining "sensible" logics.
On more than one occasion I have sketched out a logic only to realize that one or two of the axioms is unprovable in the model.
When this happens, it is a good indication that something is not what it seems and it is a good idea to revisit your definitions to see what does not work.

I encourage everyone to give ChargeCore a try for your next project and to contribute any useful definitions or automation back to the ChargeCore project so that others can make use of your work.

### External Pointers ###

The ChargeCore code is maintained by [Jesper Bengtson](http://www.itu.dk/people/jebe/) and is a stripped down version of the [Charge!](https://github.com/jesper-bengtson/Charge) library.
The first version of Charge! was described in [this paper](http://www.itu.dk/people/jebe/charge.pdf).
Charge! is quite similar to the logical foundations of the [Verified Software Toolchain](http://vst.cs.princeton.edu/) developed by Andrew Appel and his collaborators for reasoning about C programs.
Lars Birkedal's new [ModuRes framework](http://users-cs.au.dk/birke/modures/) also uses similar definitions though they are architected in a different way.
ChargeCore was pulled out to avoid external dependencies in an effort to make it easier to use.
In the upcoming [Coq 8.5](https://coq.inria.fr/news/126.html) release, [opam](https://coq.inria.fr/howto-opam) will be the officially sanctioned way to manage Coq libraries, but it can still be useful to minimize dependencies.

[^fn-shallow-binders]: Note ```lforall``` and ```lexists``` use the binders of Gallina (Coq's programming language) to represent bound variables. This choice allows us to reuse much of Gallina in writing predicates.