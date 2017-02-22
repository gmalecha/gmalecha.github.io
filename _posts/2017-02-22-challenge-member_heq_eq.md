---
layout: post
category: reflections
author: gregory malecha
title: |
  Challenge: member_heq_eq
tags:
- coq
- challenge
- dependent types
---

Working on a polymorphic version of [MirrorCore](https://github.com/gmalecha/mirror-core) I have been working a lot with [heterogeneous lists](https://github.com/coq-ext-lib/coq-ext-lib/blob/v8.5/theories/Data/HList.v) and [proof-relevant membership](https://github.com/coq-ext-lib/coq-ext-lib/blob/v8.5/theories/Data/Member.v).
The later is the source of this challenge problem.

A shell of the code is [available as a gist](https://gist.github.com/gmalecha/be7b83a23c458fcd5c2ad6eadb0eef61), and [my solution is available as well](https://gist.github.com/gmalecha/75c1577c2bed86e6d126859193909715).

## The Function

Suppose that I want to implement the following version of hetergeneous decideable equality on them:

```coq
Section del_val.
  Context {T : Type}.
  Variable ku : T.

  Fixpoint del_member (ls : list T) (m : member ku ls) : list T :=
    match m with
    | MZ l => l
    | MN ku' m => ku' :: del_member m
    end.
End del_val.

Definition member_heq
: forall (T : Type) (l r : T) (ls : list T) (m : member l ls),
  member r ls -> member r (del_member m) + (l = r)
```

Essntially `del_member` computes the list that is the result of removing the position marked by `m`.
You can see how this might be useful in the context of manipulating syntax because when you replace a unification variable (notated by `m`) with an expression, you will get an expression that has all the same unification variables but without any occurances of `m`.

Given that, what `member_heq` is doing is comparing two `member`s and returning the translation of the second into the `del_member`ed list in the case that they are not the same, or proving that the two types are the same.
Parametricity will guarantee that if we return an `inr pf` for any `pf`, that the two memberes must be equal; however, we'll prove that as the second (more challenging) part of the challenge.

First part of the challenge is to implement `member_heq` **without using any axioms or additional assumptions**.
If you are going to try to do it with tactics, note that tactics such as `dependent induction` and `dependent destruct` can silently introduce axioms, so you should check the proof at the end with `Print Assumptions member_heq.`.
Don't forget to [finish your definition with `Defined`]({% post_url 2017-02-18-qed-considered-harmful   %}) or you won't be able to prove anything about the function!

## The verification

The second step, which is significantly more challenging, is to prove that if `member_heq a b` returns `inr pf` then `a = b`.
Of course, you won't simply be able to simply write `a = b` since the two terms have different types, but the `pf` proof shows that these two types are *provably* equal.

Here's the statement of the second part of the challenge.

```coq
Lemma member_heq_eq : forall {l l' ls} (m1 : member l ls) (m2 : member l' ls) pf,
  member_heq m1 m2 = inr pf ->
  match pf in _ = X return member X ls with
  | eq_refl => m1
  end = m2.
```

As before, no axioms.
The proof needs to reduce completely, i.e.

```coq
member_heq_eq MZ MZ eq_refl eq_refl = eq_refl
```

and

```coq
member_heq_eq (MN MZ) (MN MZ) eq_refl eq_refl = eq_refl
```

## Finished?

If you've found a solution that you'd like to share, leave a link in the comments.