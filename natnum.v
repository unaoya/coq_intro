Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (plus p m)
  end.

Fixpoint mult (n m :nat) : nat :=
  match n with
  | O => O
  | S p => (plus m (mult p m))
  end.

Goal forall (n : nat), n = (plus n O).
  intros.induction n.simpl.reflexivity.simpl.f_equal.apply IHn.Qed.
