---
layout: page
category: blog
author: gregory malecha
title: The Core of Computational Reflection
tags:
 - computational reflection
 - coq
 - tutorial
highlight: true
---

Computational reflection is a technique for extending proof assistants with efficient, domain-specific automation. There are a lot of interesting ideas in computational reflection but in this blog post I'm just going to cover a simple example, proving evenness of large constants. This example is purposefully *extremely* simple, and computational reflection is certainly capable of doing a lot more, but the very key pieces are here.


The source code for this post can be found [here](/assets/blog/computational-reflection-example/even_refl.v) or as a [gist](https://gist.github.com/gmalecha/46542774bfcc722b7c26#file-even_refl-v).

### The Problem ###

Let's consider the problem of proving that large numbers are `Even`, which can be defined inductively as:

~~~
Inductive Even : nat -> Prop :=
| Even_O : Even 0
| Even_SS : forall n, Even n -> Even (S (S n)).
~~~

Proving that constants are `Even` using Ltac is quite easy:

~~~
Goal Even 0.
  apply Even_O.
Qed.

Goal Even 4.
  apply Even_SS; apply Even_SS; apply Even_O.
Qed.
~~~

We can even use `repeat constructor` to prove that large numbers are `Even`.

~~~
Lemma by_constructor_2048 : Even 2048.
  repeat constructor. (* 2.92s *)
Defined. (* 2.71s *)
~~~

The problem with this proof is that it can take quite a bit of time to construct (the time for `repeat constructor`) and to check the proof (the time for `Qed`). While these problems aren't particularly bad, scaling to larger instances is more problemantic, for example, doubling 2048 to 4096 increases the time to 11.98s and 16.01s, respectively. 

A common gut-reaction is to fault Coq for being slow on such a simple problem, but that is not quite fair. Coq is about constructing foundational proofs so there needs to be some representation of the proof, and it turns out that our automation is building a particularly bad one. It gis true that sophisticated features such as bi-directional type checking would allow this proof to be more efficient, but these are not yet "merely implementation issues".

### Applying Computational Reflection ###

The intuition behind computational reflection is to compress this proof using Coq's computation mechanism. The first step is to implement a function that will compute whether a number is `Even` or not.

~~~
Fixpoint is_even (n : nat) {struct n} : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n') => is_even n'
  end.
~~~

In order to use this function to check `Even`ness, we need to show how to construct a proof of `Even n` for any `n` such that `is_even n = true`. This is often called the "soundness theorem", and for our `is_even` example. It turns out that setting up the right induction for this proof is a bit tricky since `is_even` is making the recursive call on `n-2` rather than `n-1`; however, we can avoid the complex induction by implementing the theorem directly in Gallina so that it mirrors the definition of `is_even`.

~~~
Fixpoint is_even_sound (n : nat) {struct n} : is_even n = true -> Even n :=
  match n with
  | 0 => fun _ => Even_O
  | 1 => fun pf : false = true => match pf with eq_refl => tt end
  | S (S n') => fun pf : is_even n' = true => Even_SS (is_even_sound n' pf)
  end.
~~~

This function uses dependent pattern matching (which is hidden since Coq infers the annotation) to refine the type given the value of `n`. I don't want to go into the details of dependent pattern matching here, but there is much more information available.

Using this theorem, we can write a much shorter proof of `Even 2048`:

~~~
Lemma by_reflection_2048 : Even 2048.
Proof.
  apply is_even_sound.
  reflexivity.
Qed.
~~~

After applying `is_even_sound`, we are left to prove `is_even 2048 = true`. However, these two terms are the same after reduction (try running `compute`), so we can appeal directly to `reflexivity`. Note that both the process of constructing the proof (.03s) and the process of checking the proof (.07s) is substantially faster. This is due to the fact that the proof is so much smaller, 1 lemma application and some computation, rather than a chain of 2049 constructors. Printing the proof actually shows something pretty reasonable.

~~~
Print by_reflection_2048.
(* by_reflection = is_even_sound 2048 eq_refl *)
~~~

### What Makes Computational Reflection Possible? ###

One way to view computational reflection is as compression. We take a large proof object comprised of many construtors and summarize it in a small proof by translating pieces into computation which does not require an explicit proof in Coq. If we ever need to decompress the proof, we can simply run the decompression function, i.e. the soundness theorem, which will construct the appropriate proof.

The key feature that makes computational reflection possible in Coq is the fact that Gallina (Coq's logic) internalizes definitional equality, i.e. reduction. This is what allows us to witness the proof `is_even 2048 = true` by `eq_refl`. In Coq, reduction is deterministic (aka confluent) which means that all reductions have a single canonical form. This allows witnesses of reduction to be completely eliminated.

Proof assistants based on rewriting such as HOL can not do this in a foundational way because not all rewriting systems are confluent. To guarantee that any correct implementation of the proof checker arrives at exactly the same result, the trace of the reduction must be explicitly represented within the proof. For example, a proof of `is_even 0 = true` would need to witness the sequence of reduction steps, e.g. "delta-reduction, beta-reduction, iota-reduction", explicilty in the proof term. Theorem provers such as Isabelle and HOL make this efficient by not explicitly constructing proof terms; however, this means that the proof checker has more work to do reconstructing the appropriate reductions. By not constructing proof terms, these systems do not get first-class proof objects that can be manipulated within the language.

### Computational Reflection and Proof Relevence ###

Readers interested in proof objects may wonder if this proof is fundamentally different than the naive proof constructed by Ltac. The answer is no. While not syntactically equal, the two proofs are definitionally equal. We can see this by computing the proof terms.

~~~
Eval compute in @is_even_sound 2048 eq_refl.
(* = Even_SS (Even_SS ....) **)

Theorem by_reflection_is_by_constructor
: by_reflection_2048 = by_constructor_2048.
Proof. reflexivity. Qed.
~~~

This shouldn't be surprising given that we implemented the soundness proof as a function.

### Summary ###

I covered the very core of computational reflection with a *very* simple example. The key insight of computational reflection is to translate proofs into computations which does not need to be witnessed explicitly in proof terms. This drastically reduces the size of the proof term and makes checking it substantially faster. Despite this translation, computation on proof terms allows us to decompress the reflective proof term into one that does not rely on reflection.

The reflective procedure that I implemented in this post does not work when numbers are not constants (try using it to prove `forall n, Even n -> Even (S (S n))` and you'll see why). I'll show more about this in a later post.

### Further Reading ###

 * The first two chapters of [my dissertation]({% post_url 2015-02-01-extensible-proof-engineering-in-intensional-type-theory %}) cover the background of computational reflection. The rest of the dissertation discusses the [MirrorCore](https://github.com/gmalecha/mirror-core) library for extensible computational reflection which itself is based on my work [building automation for Bedrock]({% post_url 2014-07-14-compositional-computational-reflection %}).
 * Computational reflection is also emerging as a reasoning method in Agda. Koke and Swierstra have a [reflective implementation of auto](https://github.com/pepijnkokke/AutoInAgda/), Van der Walt and Swierstra [discuss the implementation of computational reflection in Agda](http://www.staff.science.uu.nl/~swier004/Publications/EngineeringReflection.pdf), and Devriese and Piessens have a paper on [typed syntactic meta-programming](https://lirias.kuleuven.be/bitstream/123456789/404549/1/icfp002-devriese-authorversion.pdf).
