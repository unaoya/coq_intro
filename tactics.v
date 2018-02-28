Goal forall (P Q R S : Prop), (S /\ P) /\ (Q /\ R) -> (P /\ S) /\ (R /\ Q).
  intros.
  destruct H.
  assert (forall (X Y :Prop), X /\ Y -> Y /\X).
  intros.
  destruct H1.
  split.
  apply H2.
  apply H1.
  split.
  apply (H1 S P H).
  apply (H1 Q R H0).
Qed.

Require Import List.

Theorem app_eq_nil : forall (A : Type)(l l' : list A), l ++ l' = nil -> l = nil /\ l' = nil.
  intros.
  split.
  destruct l.
  reflexivity.
  discriminate.
  destruct l'.
  reflexivity.
  destruct l.
  discriminate.
  discriminate.
  Qed.