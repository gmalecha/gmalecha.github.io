Set Implicit Arguments.
Set Strict Implicit.

Inductive Even : nat -> Prop :=
| Even_O : Even 0
| Even_SS : forall n, Even n -> Even (S (S n)).

Goal Even 0.
  apply Even_O.
Qed.

Goal Even 4.
  apply Even_SS; apply Even_SS; apply Even_O.
Qed.

Lemma by_constructor_2046 : Even 2046.
  Time repeat constructor.
Time Defined.

Fixpoint is_even (n : nat) {struct n} : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n') => is_even n'
  end.

Fixpoint is_even_sound (n : nat) {struct n} : is_even n = true -> Even n :=
  match n (* as n return is_even n = true -> Even n *) with
  | 0 => fun _ => Even_O
  | 1 => fun pf : false = true => match pf with eq_refl => tt end
  | S (S n') => fun pf : is_even n' = true => Even_SS (is_even_sound n' pf)
  end.

Lemma by_reflection_2046 : Even 2046.
  Time (apply is_even_sound;reflexivity).
Time Defined.

Print by_reflection_2046.

Print by_constructor_2046.

Eval compute in @is_even_sound 2046 eq_refl.

Theorem by_reflection_2046_is_by_constructor_2046
: by_reflection_2046 = by_constructor_2046.
Proof. vm_compute. reflexivity. Qed.