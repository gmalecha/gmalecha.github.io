---
layout: post
category: blog
title: Embedding Logics in Coq
---

Coq comes with a powerful, built-in logic (Gallina) with features such as inductive and dependent types, recursion, etc.
However, most uses of Coq don't study its theory, but rather use it as a foundation to reason about something else.
A few examples come to mind due to my experience with program verification:

* The Verified Software Toolchain embeds a program logic for reasoning about C programs.
* Ynot embeds a logic for reasoning about imperative programs.
* Iris, ...,  all embed different logics for reasoning about concurrent program.
* Bedrock embeds a logic for reasoning about low-level imperative programs.

May of these systems are structured in a similar way, they build their logic on top of Gallina in a /shallow/ way.
While shallow encodings are not good for everything, they often allow you to get to the heart of your problem very quickly so that you can think about the problems that you are interested in solving.
In this post, I'll talk about how to use [Charge!]() to quickly embed a custom logic inside of Coq and use it to ????????

Describing Logics with Charge!
------------------------------

Charge! is a framework for defining different logical structures and reasoning with them. It is built using Coq's type-class mechanism which makes it quite easy to leverage it for new logics. The core Charge! type class is the following definition of an intuitionistic logic.

```
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

Here, an instance of ```ILogicOps T``` provides various functions for operations to construt intuitionistic logic formulae.

  * ```lentails``` (written ```|--```) states that the first formula entails the second.
  * ```ltrue``` is the formula that means truth, and ```lfalse``` is the formula which means falsehood.
  * ```land``` (written ```//\\```), ```lor``` (written ```\\//```), and ```limpl``` (written ```-->>```) are the binary connectives for conjunction, disjunction, and implication.
  * ```lforall``` and ```lexists``` are the universal and existential quantifiers of the logic.

To show how a type, e.g. ```Prop```, is an intuitionistic logic, we can implement an instance of ```ILogicOps Prop```. Here's the definition.

```
Instance ILogicOps_Prop : ILogicOps Prop :=
{ lentails := fun P Q => P -> Q
; ltrue    := True
; lfalse   := False
; land     := and
; lor      := or
; limpl    := impl
; lforall  := fun T P => forall x : T, P x
; lexists  := fun T P => exists x : T, P x
}.
```

We don't need to define any new operators for describing the logical structure, they are all standard from the Coq standard library (or primitive in the system).

(What is the story for proving this?)

A Custom Logic
--------------

In addition to ```Prop```, the Charge! library contains several other useful instances of logics. In particular, functions into an intuitionistic logic form an intuitionistic logic by lifting. Formally, the instance is the following:

```
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

With this definition and the soundness proof (both of which are defined in Charge!), we can now use these logical symbols to write formulas.

A Temporal Logic
----------------

To define a logic shallowly, we first need to define the object that the logic is built to reason about. In discrete-time temporal logic, that object is an infinite sequence of states. We can define this in Coq using the following co-inductive definition (reference for co-induction?).

```
CoInductive stream (T : Type) : Type :=
| Cons : T -> stream T -> stream T.
```

To separate concerns, streams are parametric in the type of states, but in our temporal logic, we will fix the type of states to be total functions from ```string``` to ```R```. (this seems less than ideal; it isn't motivated by anything else in this post!)

A discrete-time temporal logic is simply a predicate over these traces so we can write the following:

```
Definition TraceProp (T : Type) : Type := stream T -> Prop.
```

Since ```Prop``` is an intuitionistic logic, ```TraceProp``` is a temporal logic by lifting. We get this for free from Charge's type classes with the following defintions.

```
Instance ILogicOps_TraceProp (T : Type) : ILogicOps (TraceProp T) := _.
Instance ILogic_TraceProp (T : Type) : ILogic (TraceProp T) := _.
```

Note that Coq's elaboration mechanism fills in the ```_``` using the Charge! instance for intuitionistic logics over function spaces. This definition gives us the core intuitionistic logic operators.

Logic-specific Definitions
--------------------------

The above definition gives us the core intuitionistic logic operators, but it doesn't give us any structure of a temporal logic. However, because ```TraceProp``` is a definition, we can easily extend it with the temporal logic operators.

```
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

```
Theorem Always_distr_and : forall P Q, [] P //\\ [] Q -|- [] (P //\\ Q).
Proof. ... Qed.
```

We can also prove more interesting properties such as temporal induction:

```
Theorem temporal_induction : forall G P, G |-- P -->> [](P -->> next P) -->> [] P.
Proof. ... Qed.
```

Logics within Logics
--------------------

So far, we have a shallowly-defined discrete-time temporal logic. To complete our logical system, we'd like to define two more logics. First, predicates over states so that we can easily make statements such as "the value of x in the current state is 1", and second, predicates over pairs of states to represent the evolution of the system, for example "the value of x in the next state is 1 more than the value of x in this state".

There are two ways to solve this problem. First, we could simply state that these are ```TraceProp```s, they are just special in that they only require a small part of the trace (this is the way that we accomplish this in our current formalism). An alternative approach is to define two new logics, one for predicates over single states, and one for predicates over pairs of states. Building on Charge!, both of these are quite simple to define:

```
Definition StateProp (St : Type) : Type := St -> Prop.
Instance ILogicOps_StateProp {St : Type} : ILogicOps (StateProp St) := _.
Instance ILogic_StateProp {St : Type} : ILogic (StateProp St) := _.

Definition ActionProp (St : Type) : Type := St -> St -> Prop.
Instance ILogicOps_ActionProp {St : Type} : ILogicOps (ActionProp St) := _.
Instance ILogic_ActionProp {St : Type} : ILogic (ActionProp St) := _.
```

For these types to be useful, we need two things: first, a way to embed them inside of a trace, snd second, a way to write them.

The first of these is quite easy. The basic way to embed a ```StateProp``` into a ```TraceProp``` is to assert that the state predicate holds on the first state. This is accomplished using the ```now``` definition, similarly, for ```ActionProp```s we can state that the pair of the first two states satisfies the predicate.

```
Definition now {St : Type} (P : StateProp St) : TraceProp St :=
  fun tr : stream St => P (hd tr).

Definition discretely {St : Type} (P : ActionProp St) : TraceProp St :=
  fun tr : stream st => P (hd tr) (hd (tl tr)).
```

Recap
-----

We started out with the goal of defining a temporal logic in Coq that is reminiscent of Lamport's Temporal Logic of Actions. 