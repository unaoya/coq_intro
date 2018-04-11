(* http://qnighy.github.io/coqex2014/ex2.html *)
Require Import Arith.

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.
  intros.
  apply plus_lt_compat_r.
  apply H.
Qed.

Goal forall P Q : nat -> Prop, P 0 -> (forall x, P x -> Q x) -> Q 0.
Proof.
  intros.
  apply H0.
  apply H.
Qed.

Goal forall P : nat -> Prop, P 2 -> (exists y, P (1 + y)).
Proof.
  intros.
  exists 1.
  apply H.
Qed.

Goal forall P : nat -> Prop, (forall n m, P n -> P m) -> (exists p, P p) -> forall q, P q.
Proof.
  intros.
  destruct H0.
  apply (H x q).
  apply H0.
Qed.

Require Import Arith.
Goal forall m n : nat, (n * 10) + m = (10 * n) + m.
Proof.
  intros.
  assert (n * 10 = 10 * n).
  apply Nat.mul_comm.
  rewrite H.
  reflexivity.
Qed.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros.
  apply Nat.add_shuffle1.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros.
  assert ((n + m) * (n + m) = n * (n + m) + m * (n + m)).
  apply (Nat.mul_add_distr_r n m (n + m)).
  rewrite H.
  assert (n * (n + m) = n * n + n * m).
  apply (Nat.mul_add_distr_l n n m).
  assert (m * (n + m) = m * n + m * m).
  apply (Nat.mul_add_distr_l m n m).
  rewrite H0.
  rewrite H1.
  assert (m * n + m * m = m * m + m * n).
  apply Nat.add_comm.
  rewrite H2.
  assert (n * n + n * m + (m * m + m * n) = n * n + m * m + (n * m + m * n)).  
  apply Unnamed_thm4.
  rewrite H3.
  assert (n * m + m * n = n * m + n * m).
  assert (m * n = n * m).
  apply Nat.mul_comm.
  rewrite H4.
  reflexivity.
  rewrite H4.
  assert ((n + n) * m = n * m + n * m).
  apply Nat.mul_add_distr_r.
  rewrite <- H5.
  simpl.
  assert (n + n + 0 = n + (n + 0)).
  apply (plus_assoc_reverse n n 0).
  rewrite <- H6.
  assert (n + n + 0 = n + n).
  apply (Nat.add_0_r (n + n)).
  rewrite H7.
  reflexivity.
Qed.

Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
(* Notation "x / y" := (mult x (inv y)). *) (* 使ってもよい *)

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

Lemma inv_r : forall x, x * / x = 1.
Proof.
  intros.
  assert (//x * /x = 1).
  apply (inv_l (/ x)).
  assert (//x * /x * x = //x * (/x * x)).
  rewrite <- (mult_assoc (//x) (/x) x).
  reflexivity.
  rewrite H in H0.
  rewrite inv_l in H0.
  rewrite one_unit_l in H0.
  assert (//x * (1 * /x) = 1).
  rewrite one_unit_l.
  apply H.
  rewrite mult_assoc in H1.
  rewrite <- H0 in H1.
  apply H1.
Qed.

Lemma one_unit_r : forall x, x * 1 = x.
Proof.
  intros.
  rewrite <- (inv_l x).
  rewrite mult_assoc.
  rewrite inv_r.
  rewrite one_unit_l.
  reflexivity.
Qed.