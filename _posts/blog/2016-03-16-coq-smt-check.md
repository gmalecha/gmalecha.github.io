---
layout: post
category: reflections
tags:
 - coq plugins
 - SMT
 - coq
author: gregory malecha
title: Using SMT Solvers in Coq 8.5
---

During my post-doc at UCSD I've been working on verifying cyber-physical systems in the [VeriDrone](http://veridrone.ucsd.edu) project.
Cyber-physical systems are just systems that interact with the real world (think quadcopters, cars, planes, hydro-electric dams, and robots).
The interesting thing about verifying cyber-physical systems in Coq is that they require *a lot* of reasoning about continuous mathematics, real numbers, differential equations, and all that.
Coq does a great job at all of the discrete reasoning that we do (see my previous blog post on [embedding logics in Coq]({% post_url 2015-12-18-embedding-a-logic-in-coq %})) but at the end of all the nice theory, problems often boil down to mundane reasoning about real arithmetic.
In this post I'm going to discuss a plugin that I wrote to call SMT solvers from Coq.

**Caveat**: The plugin currently does not import proof objects back into Coq (that is an interesting area of research), so, at least for the time being, you need to ```admit``` the goals that it proves.

## The High Level ##

Let's just take a look at the high level code.
You can install the latest version of the plugin using [opam](http://coq.io/opam) and Coq 8.5 with the following command line:

~~~bash
# opam install coq-smt-check
~~~

This will pull in all the dependencies and install the package.
This *does not* install any SMT solvers, so you'll need to do that manually and ensure that it is on your path.
The current package supports: [Z3](https://github.com/Z3Prover/z3) and [CVC4](http://cvc4.cs.nyu.edu/web/) [^fn-cvc4], [Polya](https://github.com/avigad/polya) support is coming soon via [its SMT2 interface](https://github.com/rlewis1988/smtlib2polya).
At the moment, Z3 is the most tested of these solvers but try other ones and [please submit bug reports if you find issues](https://github.com/gmalecha/coq-smt-check).

To try out the plugin, you can start up coqtop and run the following:

~~~coq
Require Import Coq.Reals.Reals.
Require Import SMTC.Tactic. (** Load the SMT tactic **)

Set SMT Solver "z3". (** Use Z3, also "CVC4" **)

Local Open Scope R_scope. (** Interpret arithmetic notations as reals. **)

(** The axiom that we will use to discharge proof obligations that
 ** the SMT solver "proves". We declare it local so that it doesn't
 ** get picked up in search results.
 **)
Local Axiom by_smt : forall P : Prop, P.

(** A simple goal **)
Lemma simple_goal : forall x y : R, x > 0 -> y > 0 -> x * y > 0.
Proof.
  intros.
  smt solve; apply by_smt.
  (** 'smt solve' will fail if it does not solve the goal
   ** so chaining it with 'apply by_smt' is "safe". We can't use
   ** 'admit' in Coq 8.5 because that would force us to finish
   ** the proof with 'Admitted' and would not do the final proof
   ** checking.
   **)
Qed.

Print Assumptions simple_goal.
(** Axioms:
 ** by_smt : forall P : Prop, P   <--- The SMT axiom
 ** Rmult : R -> R -> R
 ** Rlt : R -> R -> Prop
 ** R0 : R
 ** R : Set
 **)
~~~

## Current Limitations ##

The plugin is currently only concerned with proving theorems about real arithmetic so it is not using much of the power of the underlying solver.
Concretely, the plugin knows how to interpret the following symbols:

   * Real constants (```R0``` and ```R1```)
   * Real-valued addition, subtraction, multiplication, division, negation, and inverse (```Rplus```, ```Rminus```, ```Rmult```, ```Rdiv```, ```Ropp```, ```Rinv```).
   * Equalities between real valued expressions (```@eq R```).
   * Propositional logic constants and connectives: ```True```, ```False```, ```/\```, ```\/```, ```->```.

All other terms of type ```R``` and ```Prop``` are abstracted as opaque symbols meaning that an expression such as:

~~~coq
f x - 3 > 0 -> f x + 3 > 0
~~~

will be passed to the solver as

~~~coq
X - 3 > 0 -> X + 3 > 0
~~~

in this problem this isn't an issue, but it can make some things a little bit confusing.
For example, the solver will fail to prove:

~~~coq
true = true
~~~

because equality between booleans is not supported.

The current justification for such as small subset is that it keeps the translation very simple.
It also keeps us honest and forces us to do all of reasoning that is not about real arithmetic in a foundational way.
In addition, recall that SMT solvers are classical in nature meaning if they say 'UNSAT' (which is what we care about) it does not mean that there is a constructive proof, only a classical proof.
For example, Z3 will happily prove the following:

~~~coq
Goal forall P : Prop, P \/ ~ P.
  intros.
  smt solve; apply by_smt.
~~~

even though this type is clearly not inhabited in Coq without an axiom.

If the SMT solver returns 'SAT' (and produces a model) the model is printed to the console (in addition to the tactic failing).
For example,

~~~coq
Goal forall x : R, x > 0.
  intros.
  smt solve.
(** Error: Tactic failure: solver failed to solve the goal.
 **
 **  x = 0.0
 **)
~~~

## Looking Forward ##

While it is not currently on my radar, extending the translation to reflect more problems would be great.
One could imagine that in some cases, a plugin like this could provide similar functionality to [quick-chick](https://github.com/QuickChick) which does property based testing.

[Jasmin Blanchette](http://people.mpi-inf.mpg.de/~jblanche/) one of the developers of [Isabelle's Sludgehammer tactic](http://people.mpi-inf.mpg.de/~jblanche/#sledgehammer) has started a project on porting some of those ideas into Coq in a principled way.
When he is successful his automation will be able to import proof objects back into Coq providing foundational guarantees rather than relying on the ```by_smt``` axiom that we used above.

[^fn-cvc4]: For CVC4, the executable should be renamed 'cvc4'.