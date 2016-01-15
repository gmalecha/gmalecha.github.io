---
layout: page
category: blog
author: gregory malecha
title: Approximating Inductive Types in Coq
highlight: true
---

Coq inductive data types are required to be strictly positive. In this article, I'll discuss a bit about what this means, and I'll show a simple technique to approximate an inductive data type. While not the paragon of computational efficiency, the technique that I describe here makes it possible to build inductive data types compositionally (though it only supports data-types with finite branching).

The full source code is available as a [gist](https://gist.github.com/gmalecha/6dd68639da8c18f02753#file-approxnat-v).

### Strict Positivity ###

Beginners in Coq often get messages like this when trying to write more complex inductive data types.

```
Non strictly positive occurrence of "..." in "...".
```

So, what does this mean? And why do types need to be "strictly positive"?
"Strictly positive" means that the type of arguments of a constructor of type ```X``` can only contain ```X``` in the co-domain (range) of function types.
Here are a few examples:

```coq
Inductive A : Type := (* strictly positive *)
| _A1 : (nat -> A) -> A
| _A2 : A.

Inductive A : Type := (* positive, not strictly positive *)
| _A1 : ((A -> nat) -> A) -> A
| _A2 : A.

Inductive B : Type := (* not positive *)
| _B1 : (B -> nat) -> B
| _B2 : B.
```

This restriction is necessary to preserve soundness (see [^fn-strict-positive] for a formal justification of this).
However, there are times when we would like to define types and prove that they are semantically ok even though they do not pass Coq's syntactic check.
In this post, I describe a technique to get around this limitation (though not completely general)and, hopefully in the process, describe a bit about inductive types.
As we will see, the technique will not solve the problem completely, but it will be a useful partial solution.

### Inductive Types as Functors ###

From a purely set-theory point of view, an inductive type is the least fixed-point of a functor, i.e. a function from type to type
Let's take an example with the natural numbers.

```coq
Inductive nat : Type :=
| S : nat -> nat
| O : nat.

Definition natF (T : Type) : Type :=
  T + unit.
```

The definition of ```natF``` describes one level of the ```nat``` type, i.e. each constructor has a corresponding representation in ```natF```.
Here's an example,

```coq
O = inr tt
S n = inl ? (* ? is the representation of n *)
```

*Aside*: 
Here is the encoding of a few other inductive types. For simplicity, I'll stick to monomorphic types in this post.

   * ```natlistF (T : Type) : Type := unit + (nat * T).``` -- lists of natural numbers
   * ```nattreeF (T : Type) : Type := unit + (T * nat * T).``` -- binary trees with natural numbers in the branches.


Now that we've defined the functor, we can construct the least fixed-point by iterating the function starting with the empty set.

```coq
nat_0 = empty_set
nat_1 = natF nat_0
nat_2 = natF nat_1
...
```

Tarski's fixed-point theorem states that a least fixed-point exists and is unique as long as ```natF``` is monotonic, i.e. ```forall X, X < natF X```. The reason that this is necessary is the following: Suppose that you had a functor ```F x = x -> False```. We can think of this functor as the complement of ```X```. Now, if we try to iterate it to a fixed-point we realize that it never converges, it simply oscilates between the empty set and the universal set. Monotonicity solves this problem by ensuring that the set never decreases in size.

### Building an "Inductive" type ###

Now let's see how to use this ```natF``` functor to build ```nat```. We won't be able to get all the way to ```nat```, but we will be able to approximate it. In constructing the fixed-point, we build successive approximations of ```nat``` (```nat_0```, ```nat_1```, etc.) by repeatedly applying the functor. In Coq, we can do the same thing using a ```Fixpoint```.

```coq
Fixpoint approx (F : Type -> Type) (n : nat) : Type :=
  match n with
  | 0 => Empty_set
  | S n => F (approx F n)
  end.
```

Using ```approx```, we get the following:

```coq
approx natF 0 = Empty_set
approx natF 1 = natF Empty_set = nat_1
approx natF 2 = natF (natF Empty_set) = nat_2
...
```

Essentially, ```approx natF n``` represents natural numbers smaller than ```n```. Since all values of inductive type are finite, we can always build an approximation that is large enough to contain the number. Thus, we can pick

```coq
Definition Nat : Type := { n : nat & approx natF n }.

Definition NatO : Nat := { 1 , inr tt }.
Definition Nat1 : Nat := { 2 , inl (inr tt) }.
...
```

Note that the ```nat``` is the size of the number, not the number itself. Now, the type of ```NatO``` and the type of ```Nat1``` are the same. We can also define the successor function for naturals.

```coq
Definition NatS (n : Nat) : Nat :=
  { S (projT1 n) , inl (projT2 n) }.
```

Note that when we add a constructor, we need to increase the size of the approximation.

Next, let's prove that ```Nat``` is indeed a fixed-point, i.e. we want to prove ```natF Nat ~ Nat``` where ```~``` means isomorphic to. Formally, we are obligated to construct two functions ```into : natF Nat -> Nat``` and ```outof : Nat -> natF Nat``` and prove that their composition is the identity.

```coq
Definition into (n : natF Nat) : Nat :=
  match n with
  | inl n' => n'
  | inr tt => NatO
  end.

Definition outof (n : Nat) : natF Nat :=
  let '(a,n) := n in
  match a as a return approx natF a -> natF Nat with
  | 0 => fun x : Empty_set => match x with end
  | S a' => fun x : natF (approx natF a') =>
    fmap (fun n : approx natF a' => { a' , n }) x
  end

Theorem outof_into : forall (n : natF Nat),
  outof (into n) = n.
Proof. ... Qed.

Theorem into_outof : forall (n : Nat),
  into (outof n) = n.
Proof. ... (* stuck *)
```

Unfortunately, our approximation scheme does not quite work with Coq's built-in notion of equality. ```outof_into``` is provable, but we get stuck on ```into_outof```. The issue lies in the base case. There are many representations of 0, e.g. ```existT _ _ (S n) (inr tt)``` is a representation of zero for any number ```n```, and the ```outof``` function does not return this information, for good reason, we don't want to think about the approximation level.

The solution is to define a notion of equality that is independent of the approximation level. The definition of ```approx_Eq``` captures equivalence of approximate elements.

```coq
Variable RF : forall T U, (T -> U -> Prop) -> F T -> F U -> Prop.
Fixpoint approx_Eq {n m} : approx F n -> approx F m -> Prop :=
  match n as n , m as m return approx F n -> approx F m -> Prop with
  | 0 , _ => fun (a : Empty_set) _ => match a with end
  | S _ , 0 => fun _ (b : Empty_set) => match b with end
  | S n' , S m' => @RF _ _ (@approx_Eq n' m')
  end.
```

Note that to make the definition work, we need heterogenous relations, i.e. relations between values of two different types because we need to relate two values of potentially different approximations. Coupling the definition of ```approx_Eq``` with the notion of equality of ```natF``` gives us an appropriate definition of equality for ```Nat```.

```coq
Section natF_eq.
  Variables T U : Type.
  Variable RTU : T -> U -> Prop.
  Inductive NatF_eq : natF T -> natF U -> Prop :=
  | Oinr : NatF_eq (inr tt) (inr tt)
  | Oinl : forall a b, RTU a b -> NatF_eq (inl a) (inl b).
End natF_eq.

Definition Nat_eq (a b : Nat) : Prop :=
  approx_Eq NatF_eq (projT2 a) (projT2 b).
```

In particular, this definition abstracts away the level of the approximation making it possible to prove that the isomorphism is indeed an isomorphism.

```coq
Theorem Nat_eq_outof_into : forall (n : natF Nat),
  NatF_eq _ _ Nat_eq (outof (into n)) n.
Proof.
  destruct n; simpl.
  { constructor. unfold Nat_eq.
    simpl. eapply Refl_approx_Eq.
    clear. intros.
    red. destruct x.
    - constructor. apply H.
    - destruct u. constructor. }
  { destruct u. simpl. constructor. }
Qed.

Theorem Nat_eq_into_outof : forall (n : Nat),
  Nat_eq (into (outof n)) n.
Proof.
  destruct n.
  simpl. destruct x.
  { elimtype Empty_set. assumption. }
  { destruct a.
    { simpl. unfold NatS. simpl.
      unfold Nat_eq. apply Refl_approx_Eq. eapply Refl_NatF_eq. }
    { simpl. destruct u.
      red. simpl.
      unfold approx_Eq. simpl.
      constructor. } }
Qed.
```

### Matching our "Inductive" Type ###

The final piece of inductive types is observation. ```outof``` already encodes the non-recursive, non-dependent elimination principle, i.e. a pattern match, by exposing the top level of the ```Nat```. Wrapping this up in an appropriate definition makes it apparent.

```coq
Definition match_nat (n : Nat) (retT : Type) (case_zero : retT) (case_S : Nat -> retT) : retT :=
  match outof n with
  | inl n => case_S n
  | inr tt => case_zero
  end.
```

The implementation is not terribly interesting.

Of course we can not use this ```match_nat``` inside of a ```Fixpoint``` to do recursion; we need to code a separate recursive eliminator.
There are a variety of interesting fold structures, e.g. Mendler folds and monadic folds, but for simplicity I'll just cover the basic fold.
As one might expect, the justification of the recursion comes from the level of the approximation.
The implementation is generic for any type function as long as it is a ```Functor```.

```coq
Section approx.
  Variable F : Type -> Type.
  Context {FunctorF : Functor F}.
  Variable Ret : Type.

  Variable f : F Ret -> Ret.

  Fixpoint approx_rec (n : nat) : approx F n -> Ret :=
    match n as n return approx F n -> Ret with
    | 0 => fun x : Empty_set => match x with end
    | S n => fun x : F (approx F n) =>
               f (fmap (F:=F) (approx_rec n) x)
    end.
End approx.

Definition Nat_rec {T} (case0 : T) (caseS : T -> T) (n : Nat) : T :=
  @approx_rec natF _ T (fun x => match x with
                                 | inl x => caseS x
                                 | inr _ => case0
                                 end) n.(depth) n.(value).
```

Unwrapping the ```Nat``` and recursing on the approximation level makes it easy to construct the fold for ```Nat```.
Here I am breaking up the two cases so that the function more closely corresponds to Coq's ```nat_rec``` (though of course without dependent types).



Using this definition we can easily implement functions such as addition:

```coq
Definition Nat_plus (a b : Nat) : Nat :=
  fold_Nat (fun x => match x with
                     | inl x => NatS x
                     | inr tt => b
                     end) a.
```

Computation works in the usual way.

```coq
Eval compute in Nat_plus NatO (NatS (NatS NatO)).
```

### Dependent Folds ###

Dependent pattern matching and folds are a bit trickier.
Dependent pattern matches allow us to describe the return type using the value of the term that we are matching on (another post on this).
For natural numbers, our goal is something along these lines:

```coq
Definition case_Nat_dep (F : Nat -> Type) (n : nat)
  (case_zero : F NatO)
  (case_S    : forall n : Nat, F n -> F (NatS n))
: F n.
```

Ideally, we'd be able to simply replace ```nat``` by ```Nat``` and everything would work out, but things are not quite that simple.
The problem is the same as the problem defining the equivalence relation.
Namely, the function ```F``` describing the return type can make observations on the level of the approximation.
The solution is to forbid this by stating that ```F``` respects ```Nat_eq```.
Morally, this is stated using ```Proper``` like this

```coq
Proper (Nat_eq ==> (fun a b => a <-> b)) F
```

which means:

```coq
forall a b : Nat, Nat_eq a b -> ((F a -> F b) * (F b -> F a)).
```

However, these definitions do not quite work out since ```a``` and ```b``` are ```Type``` instead of ```Prop```.
To overcome this, we specify this manually:

```coq
Variable Proper_ResT : forall a b,
      Nat_eq a b ->
      (ResT a -> ResT b) * (ResT b -> ResT a).
```

In reality, we will only need the second component of the pair, but having both around makes it clear that we are really working with an isomorphism.

Augmenting ```case_Nat_dep``` with an additional argument witnessing the properness of ```F``` enable us to complete the implementation.

```coq
Variable case_zero : ResT NatO.
Variable case_S : forall n : Nat, ResT n -> ResT (NatS n).

Fixpoint approx_natF_rec_dep (d : nat)
: forall v : approx natF d, ResT (mkNat d v) :=
  match d as d
        return forall v : approx natF d, ResT (mkNat d v)
  with
  | 0 => fun v : Empty_set => match v with end
  | S d => fun v : natF (approx natF d) =>
             match v with
             | inl v' => case_S (mkNat d v') (approx_natF_rec_dep d v')
             | inr _ =>
               fst (Proper_ResT _ _ (Nat_eq_zero _ _ _ _)) case_zero
             end
  end.

Definition Nat_rec_dep (v : Nat) : ResT v :=
  match v as v return ResT v with
  | mkNat d v => approx_natF_rec_dep d v
  end.
```

Note that we are using ```Proper_ResT``` to convert ```case_zero : ResT Nat0```, which is the same as ```ResT (mkNat 1 (inr tt))```, into a ```ResT (mkNat (S n) (inr u))```.

We can use a similar trick to implement the dependent fold.
The implementation is almost identical the same except now the function is recursive on the depth.

```coq
Fixpoint approx_natF_rec_dep (d : nat)
: forall v : approx natF d, ResT (mkNat d v) :=
  match d as d
        return forall v : approx natF d, ResT (mkNat d v)
  with
  | 0 => fun v : Empty_set => match v with end
  | S d => fun v : natF (approx natF d) =>
             match v with
             | inl v' => case_S (mkNat d v') (approx_natF_rec_dep d v')
             | inr _ =>
               fst (Proper_ResT _ _ (Nat_eq_zero _ _ _ _)) case_zero
             end
  end.

Definition Nat_rec_dep (v : Nat) : ResT v :=
  match v as v return ResT v with
  | mkNat d v => approx_natF_rec_dep d v
  end.
```

Specifying these functions in the generic style (using the type-function F) is a bit more complex since we need a way to rebuild the value of the term given its subterms. 

## Going Further ##

I discussed the idea of expressing inductive data-types by using their functor representations and an approximation function.
This technique works reasonably well for many things, but it isn't perfect.
First, I have not talked at all about polymorphic or depenent inductive types.
This technique can extend to both of those, but it gets a bit more complex so I'll leave it to another post.
The second limitation deals with functions embedded inside of inductive types.
For example, take infinite branching trees.

```coq
Inductive itree : Type :=
| Leaf
| Node : (nat -> itree) -> itree.
```

Following the recipe described in the post we would write ```itree``` as a functor and take its fixpoint by pairing an approximation depth with a value of the approximation.
Concretely,

```coq
Definition itreeF (T : Type) : Type :=
  unit + (nat -> T).
Definition ITree : Type := { n : nat & approx itreeF n }.
```

For infinite branching types such as this one, we can not write an injection, ```into : itreeF ITree -> ITree```.
The reason for this is that we can not *compute* an upper bound on the depth required to approximate all of the subterms in the tree.

While this is a limitation, in practice it often is not a problem.
For example, much of the work on modular data types, e.g. [Deleware's modular meta theory](http://people.csail.mit.edu/bendy/MTC/) and [modular monadic meta theory](http://people.csail.mit.edu/bendy/3MT/), focuses on modular representations of syntax trees.
These trees are naturally finite branching since they correspond to syntax (though it does forbid using higher-order encodings of variables).
In addition, it is not always necessary to define a fully general ```into`` function.
For example, if we construct the value in such a way that we know the upper-bound, the we can easily pick an appropriate approximation level.

### Further Reading ###

I hope that the post gave some insights into inductive types and how they are generated from type functions.
This is really just the tip of the iceberg, and there are a lot of interesting things that you can do from here on.
For example, this view is just about taking the fixpoint in the world of Sets.
Things get a lot more interesting when playing in other spaces, e.g. when defining [higher-inductive types](http://homotopytypetheory.org/2011/04/24/higher-inductive-types-a-tour-of-the-menagerie/), but we'll leave that for another day.

Phil Wadler has an [excellent discussion of these topics](http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt) from a more mathematical point of view.
Since is working at the meta-theory level, he does not need to worry about *computing* approximation depths like we do in this post.



{% comment %}
### Church Encodings to the Rescue ###

There is a way to solve this problem: Church encodings.
The idea behind Church encodings is that instead of excoding the data explicitly as constructors, we encode it implicitly via a fold function.
Essentially, a value of type ```Mu F``` is simply the corresponding fold.
In code:

```coq
Definition Mu (F : Type -> Type) : Type :=
  forall T, (F T -> T) -> T.
```

Continuing here is essentially Ben's papers/dissertation.
{% endcomment %}