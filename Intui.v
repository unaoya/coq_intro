(* http://www.ne.jp/asahi/fmsci/fmmath/coqp/vvof/Intui.v *)

Theorem Syllog : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Theorem Syllogeq : forall A B C:Prop, (A <-> B) -> (B <-> C) -> (A <-> C).
Proof.
  intros.
  elim H.
  elim H0.
  intros.
  split.
  apply (Syllog A B C).
  apply H3.
  apply H1.
  apply (Syllog C B A).
  apply H2.
  apply H4.
Qed.

Theorem InDN : forall A:Prop, A -> ~~A.
Proof.
  intros.
  intro.
  apply H0.
  apply H.
Qed.

Theorem Andell:forall A B:Prop, A /\ B -> A.
Proof.
  intros.
  destruct H.
  apply H.
Qed.

Theorem Andelr:forall A B:Prop, A /\ B -> B.
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

Theorem AndABAB:forall A B:Prop, (A <-> B) -> (A -> B).
Proof.
  intros.
  destruct H.
  apply (H H0).
Qed.

Theorem AndABBA:forall A B:Prop, (A <-> B) -> (B -> A).
Proof.
  intros.
  apply 