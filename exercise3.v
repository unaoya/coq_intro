Require Import Arith.

Fixpoint sum_odd (n : nat) : nat :=
  match n with
  | O => O
  | S m => 1 + m + m +sum_odd m
  end.

Goal forall n, sum_odd n = n * n.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  f_equal.
  rewrite IHn.
  ring.
Qed.

Require Import Lists.List.

Fixpoint sum (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | x :: xs => x + sum xs
  end.

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1 < x /\ In x xs).
Proof.
  intros.
  induction xs.
  contradict H.
  simpl.
  apply Lt.lt_irrefl.
  simpl in H.
  
  
  