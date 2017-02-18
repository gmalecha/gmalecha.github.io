---
layout: post
category: blog
title: Qed Considered Harmful
author: gregory malecha
tags:
- coq
- dependent types
- qed
mathjax: true
---

Coq provides two ways to finish definitions `Qed` and `Defined`.
The former is meant for "proofs" and makes the definition opaque while the later is meant for "definitions" and leaves the definition transparent.
While the "proof" and "definition" dicotomy initially makes a lot of sense to users, but as users start to use dependent types more and more, they realize that the distinction is quite arbitrary, in which case, should we abandon `Qed`?
In this post, I argue that yes abandoning `Qed` is a perfectly sensible thing to do.

The complete code for this post is available [as a gist](https://gist.github.com/gmalecha/99210fb65b1c65edc087a7636f6bf42e).

## Qed vs. Defined: An Example

One of the first places that I noticed the `Defined` vs `Qed` problem was when writing the following theorem about heterogeneous lists in the [ExtLib]() library (some section variables are ommitted for brevity).

```coq
Theorem hlist_app_assoc : forall ls ls' ls'' (hs : hlist ls) (hs' : hlist ls') (hs'' : hlist ls''),
  hlist_app (hlist_app hs hs') hs'' =
  match eq_sym (app_ass ls ls' ls'') in _ = X return hlist X with
  | eq_refl => hlist_app hs (hlist_app hs' hs'')
  end.
```

If you haven't come across dependent types before, this theorem might look a bit odd.
In essence, what is happening in the above code is the `match` is implementing a "cast" between the type of the left hand side (`hlist F ((ls ++ ls') ++ ls'')`) and the type of the right side (`hlist F (ls ++ (ls' ++ ls''))`).
Obviously the equality of those two types is justified by the associativity of list append which is exactly what the `app_ass` theorem states.

On the surface the proof (as usual) follows the computational structure of the function, in this case `hlist_app` which is defined by structural induction on the first argument[^fn-hlist-definition].
Proceeding by induction on `hs` yields the following:

```coq
ls' , ls'' : list T
===================
forall (hs' : hlist ls') (hs'' : hlist ls''),
  hlist_app (hlist_app Hnil hs') hs'' =
  match eq_sym (app_assoc_reverse nil ls' ls'') in _ = X return hlist X with
  | eq_refl => hlist_app Hnil (hlist_app hs' hs'')
  end
```

Note that `app_ass` is simple a notation for `app_assoc_reverse`.
Simplification of this term yields the following:

```coq
ls' , ls'' : list T
===================
forall (hs' : hlist ls') (hs'' : hlist ls''),
  hlist_app hs' hs'' =
  match eq_sym (app_assoc_reverse nil ls' ls'') in _ = X return hlist X with
  | eq_refl => hlist_app hs' hs''
  end
```

The relevent parts of the conclusion have reduced to the same thing (note the `hlist_app hs' hs''` on both sides), but the cast is preventing us from proving the theorem by `reflexivity`.
Interestingly, if we look at the implementation of `app_assoc_reverse` we find that it too should reduce:

```coq
Print app_assoc_reverse.

Fetching opaque proofs from disk for Coq.Lists.List
(*
app_assoc_reverse =
fun (A : Type) (l m n : list A) => eq_sym (app_assoc l m n)
     : forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n

Argument A is implicit
Argument scopes are [type_scope list_scope list_scope list_scope]
*)
```

However, the opacity of `app_assoc_reverse` gets in the way of the reduction.
Coq even warns us about this when we print the definition.

Finishing the proof while maintaining the opacity of `app_assoc_reverse` requires one of two things:

1. Admit an axiom stating that equality proofs are uninformative (the famous `UIP_refl` or one of its equivalent definitions), or
2. Parameterize the proof by fact that equality proofs at type `T` are uninformative.

The first of these choices is clearly suboptimal becaues we're admitting a global axiom that is inconsistent with many interesting models of Gallina, namely [homotopy type theory](https://homotopytypetheory.org/)[^fn-mere-proposition].
The second allows us to avoid the axiom by punting the proof off to the user; however, it is still suboptimal because it reduces the number of types that `hlist_app_assoc` holds for.
Namely, it only holds for types in which all equalities are trivial.

### Transparency to the Rescue

If we're willing to duplicate the definition of `app_ass`, we can prove `hlist_app_assoc` without appealing to any axioms.
To see how it works out, we first duplicate the definition:

```coq
Fixpoint app_ass_trans ls ls' ls'' : (ls ++ ls') ++ ls'' = ls ++ (ls' ++ ls'') :=
  match ls as ls return (ls ++ ls') ++ ls'' = ls ++ (ls' ++ ls'') with
  | nil => eq_refl
  | l :: ls => f_equal (f:=cons l) (app_ass_trans ls ls' ls'')
  end.
```

Note that you can prove this using tactics if you're more familiar with that approach; however, if you do, you must end the definition with `Defined` so that Coq makes the definition transparent.

With the transparent definition we can re-phrase the theorem.

```coq
Theorem hlist_app_assoc : forall ls ls' ls'' (hs : hlist ls) (hs' : hlist ls') (hs'' : hlist ls''),
  hlist_app (hlist_app hs hs') hs'' =
  match eq_sym (app_ass_trans ls ls' ls'') in _ = X return hlist _ X with
  | eq_refl => hlist_app hs (hlist_app hs' hs'')
  end.
```

Note that this time when we do induction and simplify, the definition of `app_ass_trans` also reduces and we are now left with the simple reflexivity goal, which is easily discharged.

```coq
ls' , ls'' : list T
===================
forall (hs' : hlist ls') (hs'' : hlist ls''),
  hlist_app hs' hs'' = hlist_app hs' hs''.
```

In the inductive case things are a bit more complex:

```coq
ls , ls' , ls'' : list T
l : T
h : F l
hs : hlist ls
==============================
forall (hs' : hlist ls') (hs'' : hlist ls''),
  hlist_app (hlist_app (Hcons f hs) hs') hs'' =
  match eq_sym (app_ass_trans (t :: ts) ls' ls'') in (_ = X) return (hlist X) with
  | eq_refl => hlist_app (Hcons f hs) (hlist_app hs' hs'')
  end
```

Simplification and introduction allows us to rewrite by the inductive hypothesis, which leaes us with the following:

```coq
Hcons f
    match eq_sym (app_ass_trans ts ls' ls'') in (_ = X) return (hlist X) with
    | eq_refl => hlist_app hs (hlist_app hs' hs'')
    end =
  match eq_sym (f_equal (app_ass_trans ts ls' ls'')) in (_ = X) return (hlist X) with
  | eq_refl => Hcons f (hlist_app hs (hlist_app hs' hs''))
  end
```

Here, we note that if we ignore the `match`es, everything matches up (no pun intended).
The naive thing to do is to `destruct (app_ass_trans ts ls' ls'')`, but that doesn't work here.
Coq complains that the *conclusion is not parametric in the index of the inductive type*.
In Ltac, we can get around this problem using the following (quite common) incantation

```coq
clear.
generalize (hlist_app hs (hlist_app hs' hs'')).
destruct (app_ass_trans ts ls' ls'').
```

Which gets us to:

```coq
forall h : hlist ((ts ++ ls') ++ ls''),
  Hcons f match eq_sym eq_refl in (_ = X) return (hlist X) with
          | eq_refl => h
          end =
  match eq_sym (f_equal eq_refl) in (_ = X) return (hlist X) with
  | eq_refl => Hcons f h
  end
```

Since the `match`es are on `eq_refl`, they reduce.
Clearing away the cruft, we find that we're essentially done.

```coq
forall h : hlist ((ts ++ ls') ++ ls''), Hcons f h = Hcons f h
```

Which is completed by `reflexivity`.

## Abstraction and Dependent Let

Above, we saw that completing a proof with `Defined` leaves it transparent, i.e. able to be reduced, while `Qed` seals the definition.
Interestingly, but purhaps unsurprisingly, this same thing plays out in the expression language as well.
Readers familiar with vanilla type theory are used to thinking of `let` as syntactic sugar for function application.
For example,

```coq
let x := e1 in e2   (* = *)   (fun x => e2) e1
```

Where `e2` mentions `x`.
In Gallina, however, this equality does not hold.
We can see that by noting that the following definition type checks:

```coq
let x := 1 in
@eq_refl nat 1 : x = x
```

while the "same" definition using `fun` is rejected.

```coq
(fun x => @eq_refl nat 1 : x = x) 1
```

Knowing the type checking rules, the fact that the latter does not type check shouldn't be too unexpected.
The former works because, in Gallina, `let` (sometimes called "dependent let") introduces a transparent variable in the context.
This allows the type checker to unfold[^fn-zeta] `x` in order to unify it with `1` when type checking the body of the `let`.
In the later formulation, the type checking rules introduce a universal quantifier (for the lambda abstraction) which requires the body to be *parametric* in the argument.

This is exactly what happens with `Qed` and `Defined`.
In Gallina, `let` acts like `Defined` while `Qed` acts like the function encoding of `let`.

## Opacity is Enforced Parametricity

Taking a step back, we see that when we declare a definition to be opaque (using `Qed`) we are enforcing that **all** uses of the definition are parametric with respect to the implementation.
Fundamentally, this limits the places where the definition can be used because it prevents a client from using the term where reduction is necessary.
This sort of opacity makes sense in closed contexts where we know exactly what the body will depend on up front.
But, in the open context of the Coq toplevel, the assertion that "this definition will never need to be reduced" seems a bit extreme.
Library developers rarely forsee all possible use cases of their libraries, and artificially limiting their useability seems like a perfect recipe for crippling their adoption.


The obvious alternative is to make the definition transparent, but, from a conceptual point of view, this might be a bit unsatisfying.
In particular, both type-checking and tactics can be more efficient when they are parameteric because the kernel does not need too (indeed it can not) perform reduction on those terms.

Is there a way to get the best of both worlds?
We can achieve the opaque (parametric) behavior on a case-by-case basis if we parameterize our definition by the proof.
Take proving the commutativity of addition on natural numbers for example.

```coq
Section plus_comm.
  (* Parameterize by the lemmas *)
  Variable plus_unit : forall a : nat, a + 0 = a.
  Variable plus_S_r : forall a b, a + S b = S (a + b).

  Theorem plus_comm : forall a b : nat, a + b = b + a.
  Proof.
    induction a.
    { intros. symmetry. apply plus_unit. }
    { intros.
      rewrite plus_S_r. simpl; rewrite IHa. reflexivity. }
  Defined. (* Make the definition transparent *)

End plus_comm.
```

By making the theorem transparent and parameterizing it over the proof of the lemma we can control its reduction.
For example, if we invoke the lemma on transparent proofs, then the entire theorem reduces.

```coq
Eval compute in plus_comm plus_unit plus_S_r 5 5.
(*   = eq_refl
     : 5 + 5 = 5 + 5 *)
```

Where `plus_unit` and `plus_S_r` are transparent (see [the gist]() for all the details).
And, if we pass an opaque proof (or a parameter), then reduction will be blocked.

```coq
Opaque plus_unit plus_S_r.

Eval compute in plus_comm plus_unit plus_S_r 5 5.
(*   = match
         match plus_S_r 5 4 in (_ = y) return (y = 10) with
         | eq_refl => eq_refl
         end in (_ = y) return (10 = y)
       with
       | eq_refl => ... snip ...
       end
     : 5 + 5 = 5 + 5 *)
```

## Practical Considerations

While conceptually quite elegant, taking this parametrization approach to the extreme in the current version of Coq is a bit problematic.
There are three basic reasons for this:

1. The syntactic overhead to parameterizing definitions can be quite substantial.
You can easily see this in the `plus_comm` definition above where I opened a new section and had to restate the type of the lemma entirely.
2. There is overhead to using parameterized definitions because the type of a parameterized term is larger, and its uses must include the dependencies.
For example, to prove `x + y = y + x` using the `plus_comm` from above, we need a proof term that includes the dependencies, i.e. `plus_comm plus_unit plus_S_r`, rather than the smaller term `plus_comm`.
3. Coq is optimized for opaque proofs.
A good deal of engineering has gone into optimizing opaque proofs, for example, [processing them in parallel](https://hal.inria.fr/hal-01135919) and avoiding loading during proof checking (only query commands can force the definitions to be loaded).

While these problems are not currently solved, I believe that opaque definitions provide onlya short term solution.
A richer treatment of dependency (where we distinguish between depending on a value of the type, an opaque dependency, and depending on a *particular* value, a transparent dependency) could give us all the benefits of above and more.
For example, converting dependent lets into non-dependent lets (using abstraction) would provide more parallelism potential for type checking *within terms*, not just at the top-level.
In addition, computation mechanisms such as `vm_compute` and `native_compute` could erase proof terms when can be statically shown to reduce to `eq_refl`, which is mainly when working with vanilla inductive types and when the terms do not appeal to axioms.

## Conclusions

When I was first working with Coq, I subscribed to the matra that there is an obvious deliniation between what is a proof (and should be `Qed`'d) and what is a program (and should be `Defined`).
However, dependent types rightfully challenge that mantra.
As we saw in the first example, a proof for you might need to be a definition for someone else.

So the next time that you finish a "proof", think about closing it with `Defined` because, indeed, you have just defined a quite interesting *value*.

{% comment %}
Luckily, from what I have seen this is increasingly becoming the norm, with great backing from proof assistants that focus more on "programming" than "proving", e.g. [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php) and [Idris](http://www.idris-lang.org/).
Transparent definitions allows us to avoid the need to duplicate definitions[^fn-duplicate-definitions] and makes reduction clearer and simpler because "everything reduces".
When we don't care about the particular term that we use, we can make this explicit in the definition by quantifying over all possible implementations of that proof. 
{% endcomment %}

#### Footnotes

[^fn-hlist-definition]: Heterogeneous lists in [ExtLib](https://github.com/coq-ext-lib/coq-ext-lib) are defined as an indexed inductive type rather than as a function from lists to types. More details [on using functions to define types can be found here]().

[^fn-mere-proposition]: In homotopy type theory, this could be read as "equality is a *[mere proposition](https://ncatlab.org/nlab/show/mere+proposition)*"; though of course this completely destroys the interesting higher structure is central to homotopy type theory.

[^fn-destruct]: Destruct works quite often, but in this instance there is something in the way.

[^fn-zeta]: Unfolding a `let` is called zeta ($$\zeta$$) reduction.

[^fn-duplicate-definitions]: Lately I have found that as I have been using dependent types more and more for programming, more and more I have been [duplicating definitions from the standard library](https://github.com/coq-ext-lib/coq-ext-lib/??) so that they do not block reduction.
