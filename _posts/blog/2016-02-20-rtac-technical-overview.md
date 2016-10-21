---
layout: post
category: reflections
author: gregory malecha
title: "Rtac: Reflective Tactics in Coq"
tags:
- coq
- mirror-core
- rtac
- computational reflection
extra_js_head:
- "https://www.google.com/jsapi?autoload={'modules':[{'name':'visualization','version':'1','packages':['corechart']}]}"
highlight: true
---

In this post I'm going to discuss [Rtac](https://github.com/gmalecha/mirror-core) the reflective tactic language that I developed as a central piece of [my dissertation]({% post_url 2015-02-01-extensible-proof-engineering-in-intensional-type-theory %}).
The results there show how reflective tactics can be a game-changer in the ability to build very efficient automation.
For comparison, the automation that I'm going to write in this post is a monoidal cancellation procedure and at the end of the post we'll see that it scales substantially better than Ltac, e.g. on larger problems it is **almost 2 orders of magnitude faster than Ltac**.

There isn't enough space here to fully discuss the technical details that make Rtac work, so I'll instead focus on using it from the client perspective. More examples can be found in the [MirrorCore repository](https://github.com/gmalecha/mirror-core) and is installable for Coq 8.5 with [opam](http://coq.io/opam/) using:

~~~bash
opam install coq-mirror-core
~~~

## Reflective Tactics ##

I will not go into the details of what computational reflection is in this post, [I've discussed it in the past]({% post_url 2015-10-03-computational-reflection-primer %}). At the high level, we're going to replace a large proof term with a computation and prove that the computation implies the existence of a proof of the property.

Rtac is a reflective tactic language built on top of the [MirrorCore](https://github.com/gmalecha/mirror-core) library for extensible computational reflection.
From the client point of view, ```rtac``` tactics are just elements of a data type and sound tactics are those that satisfy a particular property, namely ```rtac_sound```.
Here is a slightly simplified version [^fn-rtac-simplifications].

~~~
(* The "raw" type of tactics *)
Definition rtac : Type.

(* A predicate stating that the tactic [r] is sound.
 * Rtac establishes this fact separately to avoid the overhead of
 * constructing proofs during computation.
 *)
Definition rtac_sound (r : rtac) : Prop :=
  ... (* interesting *) ...

(* Function to run a tactic on a goal *)
Definition run_rtac (tac : rtac) (g : goal) : option goal := ...

(* Sound tactics result in sound reasoning.
 *)
Definition run_rtac_sound : forall (r : rtac),
   rtac_sound r ->
   forall g g',
     run_rtac r g = Some g' ->
     goalD g' -> goalD g.
~~~

Readers familiar with computational reflection will notice that this type is the prototypical type for computational reflection.
In particular, the function (```run_rtac r```) is applied to a syntactic representation of the current goal (```g```) which produces a new goal (```g'```) and the denotation of ```g'``` implies the denotation of ```g```.

### The Model ###

The programming model of Rtac closely resembles the programming model of Ltac.
As we saw above, tactics operate on goals and produce optional goals.
Intuitively, if the tactic produces a new goal, then the new goal implies the input goal.
Goals in Rtac are just like goals in Ltac, they have a context (the part above the line), and a distinguished "goal" expression (the part below the line).
Rtac reasoning is restricted to only backwards reasoning, i.e. all reasoning performs manipulation of the goal.

### Reasoning Tactics ###

The core Rtac tactics are quite similar to the Ltac ones.

A common tactic is ```ASSUMPTION``` which searches for a hypothesis that unifies with the current goal.
Its definition (and its corresponding soundness proof) is quite simple

~~~
(* Search for an assumption matching the goal in the context *)
Definition ASSUMPTION : rtac := ...

(* The ASSUMPTION tactic is sound *)
Theorem ASSUMPTION_sound : rtac_sound ASSUMPTION.
Proof. ... Qed.
~~~

A few other basic tactics are ```INTRO``` and ```EEXISTS``` which have similar structure and mimic their Ltac counter-parts.


The workhorse of Rtac is the ```EAPPLY``` tactic which applies a syntactic representation of a lemma to the current goal [^fn-syntactic-lemmas].

~~~
Record lemma : Type :=
{ vars := list typ
; prems := list expr
; concl := expr }.

(* The tactic *)
Definition EAPPLY : lemma -> rtac := ...

(* The soundness proof *)
Theorem EAPPLY_sound : forall lem, lemmaD lem -> rtac_sound (EAPPLY lem).
Proof. ... Qed.
~~~

Under the hood, `EAPPLY` essentially does the exact same thing that Ltac does when we apply a lemma.
It unpacks the lemma, constructing unification variables for each of the universally quantified variables (those listed in `vars`).
Then it attempts to unify the conclusion (`concl`) with the current goal.
If that unification succeeds, it produces a new subgoal for each premise in the `prems` list.
While the reasoning that goes into its proof is a bit subtle, from the client point of view, using it is quite simple.
For example,

~~~
EAPPLY plus_comm_lem
~~~

is a tactic that applies the commutativity of addition to the current goal.
Further, the soundness of this tactic is established directly from `EAPPLY_sound`.

Using just `EAPPLY`, we can easily derive Rtac variants of common Ltac tactics such as `left`, `right`, `reflexivity`, and `split`, simply by supplying the appropriate lemma.



### Tactic Combinators ###

Beyond the core reasoning tactics, Rtac has several tactic combinators (in Coq often called tacticals) that allow users to combine these base tactics into more interesting reasoning procedures.
Rtac's tactic combinators are based on the Ltac tactic combinators in Coq 8.4.
They include, for example:

* `tac1 ;; tac2` : run `tac2` on all subgoals produced by `tac1`
* `TRY tac` : if `tac` fails, then do nothing and succeed
* `FIRST [ tac1 | tac2 | .. ]` : try `tac1`, if it fails, try `tac2`, etc. if all fail then the tactic fails.
* `DO n tac` : essentially `tac ;; tac ;; tac ...` n-times.
* `REPEAT n tac` : similar to `DO n tac` except that it stops early if `tac` fails. `REPEAT n tac` never fails.
* `REC n (fun rec => tac)` : Similar to `REPEAT` but gives explicit access to the continuation.
* `SOLVE tac` : fail if `tac` does not completely solve the goal.

Using these combinators, we can write tactics that do backtracking search.
For example, if we want to do a depth-first search for a proof using a few lemmas, we could write the following:

~~~
Definition search n : rtac :=
  REC n (fun rec => FIRST [ SOLVE [ EAPPLY lem1_lem ;; rec ]
                          | SOLVE [ EAPPLY lem2_lem ;; rec ]
			  | SOLVE [ EAPPLY lem3_lem ;; rec ] ]).
~~~

Proving `search` sound is trivial using the soundness of the individual tactics.

~~~
Theorem search_sound : forall n, rtac_sound (search n).
Proof.
  eapply REC_sound; intros.
  eapply FIRST_sound; repeat first [ apply Forall_cons | apply Forall_nil ].
  - eapply SOLVE_sound.
    eapply SEQ_sound.
    - eapply EAPPLY_sound. exact lem1.
    - assumption.
  - eapply SOLVE_sound.
    eapply SEQ_sound.
    - eapply EAPPLY_sound. exact lem2.
    - assumption.
  - eapply SOLVE_sound.
    eapply SEQ_sound.
    - eapply EAPPLY_sound. exact lem3.
    - assumption.
Qed.
~~~

Of course, since the proof is so regular, it is quite easy to automate:

~~~
Theorem search_sound : forall n, rtac_sound (search n).
Proof.
  unfold search; intros.
  rtac_derive_soundness.
  - apply lem1.
  - apply lem2.
  - apply lem3.
Qed.
~~~

### Tactic Continuations ###

The last bit of Rtac is "tactic continuations".
Tactic continuations generalize tactics to be able to inspect multiple parallel goals.
To see how they fit into the landscape of tactics, consider applying a tactic such as `split` (which would be implemented in Rtac using `EAPPLY conj`).
Recall that `conj` is the constructor for `/\` so it has the type:

~~~
Check conj.
(* conj
 *   : forall A B : Prop, A -> B -> A /\ B
 *)
~~~

When we apply `split`, we will get two subgoals.
In Ltac, we could chain this tactic with a single tactic, e.g. `auto`, if we want to run the same tactic on *all* of the new goals, we could sequence it with a sequence of tactics, e.g. `[ tauto | eassumption ]`, if we want to apply a different tactic to each subgoal[^fn-check].
In Rtac, both of these cases arise naturally from tactic continuations.
The `;` operator accepts a tactic and a tactic continuation.
In the case that the second operator is another tactic then we can use the `ON_ALL : rtac -> rtacK` tactic combinator to lift it to a tactic continuation.
In the case that the second operator is a list of tactics, then we can use the `ON_EACH : list rtac -> rtacK` tactic combinator to apply one to each unsolved goal.

**Aside**: While developed independently, tactic continuations are quite similar to focusing tactics in [Coq's new tactic engine](http://coqhott.gforge.inria.fr/blog/coq-tactic-engine/).


## Performance ##

Using just the core tactics and tacticals, it is easy to build a tactic that performs monoidal cancellation.
The code is adapted from the [Ynot cancellation algorithm]({% post_url 2009-08-31-effective-interactive-proofs-for-higher-order-imperative-programs %}).
The code (simplified to be in line with this post) is the following:

~~~
(* The unifier is a parameter. This allows custom cancellation rather than
 * being restricted to syntactic cancellation. For example, cancelling
 * [foo] with [bar] given a premise [foo = bar], or cancelling
 * [f (x + y)] with [f (y + x)] using arithmetic reasoning.
 *)
Variable SOLVER : rtac.

(* Iterate the terms on the right-hand-side.
 * Use [SOLVER] to try to cancel the left-most term.
 *)
Definition iter_right (n : nat) : rtac :=
  REC n (fun rec =>
           FIRST [ EAPPLY lem_plus_unit_c
                 | EAPPLY lem_plus_assoc_c1 ;; ON_ALL rec
                 | EAPPLY lem_plus_assoc_c2 ;; ON_ALL rec
                 | EAPPLY lem_plus_cancel ;;
                   ON_EACH [ SOLVE SOLVER | IDTAC ]
                 ])
      IDTAC.

(* Iterate the terms on the left-hand-side *)
Definition iter_left (k : rtac) (n : nat) : rtac :=
  REC n (fun rec =>
           FIRST [ EAPPLY lem_plus_unit_p
                 | EAPPLY lem_plus_assoc_p1 ;; ON_ALL rec
                 | EAPPLY lem_plus_assoc_p2 ;; ON_ALL rec
                 | k ])
      IDTAC.

(* Iterate the terms on the left, then the terms on the right. *)
Definition cancel' (n m : nat) : rtac :=
  let k :=
      FIRST [ EAPPLY lem_plus_comm_c ;; ON_ALL (iter_right m)
            | iter_right m ]
  in
  FIRST [ iter_left k n
        | EAPPLY lem_plus_comm_p ;; ON_ALL (iter_left k n) ].
~~~

There are two things to note about this code.
First, the similarity between Ltac and Rtac made it possible to port this code directly from the Ltac code in a relatively simple way.
Second, the proof that this tactic is sound arises directly from the soundness of the individual pieces making the entire soundness proof just a few lines long.


To get an idea of the benefit of computational reflection for problems like this, take a look at the performance of this tactic.

<div style="height: 300pt" id="rtac-perf"></div>

The vertical axis is time in seconds (note the logarithmic scale) and the horizontal axis is the number of terms on either side.
For example, `a * b * c = c * b * a` is a problem of size 3.
For low numbers, the difference is negligable (easily within the measurement error of Coq's `Time` command), but as the problem size increases, the Rtac implementation remains fast while the Ltac implementation slows to a crawl.
For example, cancelling 100 terms takes over 12 minutes in Ltac while the same problem takes **less than one second in Rtac**.

The other axis to compare on is development time.
I built this entire benchmark and proved it correct in a few hours.
I started by writing the Ltac code and constructing some problem instances and then I built the reflective automation using it as a guide.
Most of the development time for the reflective automation was spent the syntactic representation that is necessary for computational reflection; writing the actual tactic was relatively easy, and proving it correct was trivial.

## Summary ##

In this post I gave an overview of Rtac, a full-reflective tactic language.
Rtac is modeled on Ltac and drastically simplifies the process of writing reflective automation.
Rtac is *not* meant to replace Ltac, though it is useful as a glue mechanism for other reflective tactics.
For example, in my work on [MirrorShard]({% post_url 2014-07-14-compositional-computational-reflection %}) I describe how gluing reflective procedures together with reflection is *substantially* more efficient than doing it in Ltac.

The code snippets that I presented are slightly simplified for presentation purposes, but the basic mechanism is the same.
In a later post I will go through this example in detail, describing all of the pieces and how we put them together.

**Current Work**
I have been working with [Jesper Bengtson](http://www.itu.dk/people/jebe/) on simplifying the process of using mirorr-core, and we have made progress that has been incorporated back into [mirror-core](https://github.com/gmalecha/mirror-core).
MirrorCore is still under development, so if you're interested in using it for a something please [get in touch with me](mailto:gmalecha at gmail dot com), and please submit [bug reports or feature suggestions](https://github.com/gmalecha/mirror-core/issues). 

### Further Reading ###

The main ideas in this post are covered in [my dissertation]({% post_url 2015-02-01-extensible-proof-engineering-in-intensional-type-theory %}) and [our ESOP'16 paper]({% post_url 2016-01-01-extensible-and-efficient-automation-through-reflective-tactics %}).

<script type="text/javascript">
    function drawChart() {
      var data = google.visualization.arrayToDataTable([
        ['Size',  'Ltac', 'Ltac-Qed', 'Rtac', 'Rtac-Qed'],
        [3,     0.006703,   0.000742, 0.020547, 0.000669],
        [5,     0.017333,   0.009652, 0.027689, 0.001191],
        [10,    0.125059,   0.054242, 0.047115, 0.000889],
        [20,    1.415505,   0.473854, 0.099066, 0.050034],
        [50,   43.206063,   6.420724, 0.317515, 0.145612],
        [75,  229.532949,  26.239868, 0.586712, 0.266718],
        [100, 737.690032,  80.558039, 0.960886, 0.404200]
      ]);

      var options = {
        title: 'Rtac Performance',
        curveType: 'function',
        legend: { position: 'bottom' },
        hAxis: { ticks : [3,5,10,20,50,75,100], logScale: true, title: 'Size' },
        vAxis: { format: '#.####', gridlines: { count: 6}, title: 'Time (sec)', logScale: true }
      };

      var chart = new google.visualization.LineChart(document.getElementById('rtac-perf'));

      chart.draw(data, options);
    }
    google.setOnLoadCallback(drawChart);
</script>

### Footnotes ###

[^fn-rtac-simplifications]: In the code, the representation of types and terms is a parameter of `rtac`. This allows clients to use Rtac with their own custom representations if they do not wish to use MirrorCore.

[^fn-syntactic-lemmas]: Since Rtac is completely reflective, everything must be represented syntactically. However, MirrorCore comes with a helpful plugin to automate the construction of syntactic lemmas.

[^fn-check]: Chaining a tactic with `[ | ]` also asserts the number of new goals. This can be useful for checking whether running a tactic leaves only a single goal.
