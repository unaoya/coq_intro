(* http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt4.html *)
Require Import Arith.

Goal forall (n : nat), (exists m : nat, n = m * 4) -> exists k : nat, n = k * 2.
  intros.destruct H.exists (x * 2).rewrite mult_assoc_reverse.simpl.apply H.Qed.

Theorem lt_Snm_nm : forall (n m :nat), S n < m -> n < m.
  intros.apply (lt_trans n (S n) m).apply lt_n_Sn.apply H.Qed.

Inductive InList (A : Type)(a : A) : list A -> Prop :=
| headIL : forall xs, InList A a (a::xs)
| consIL : forall x xs, InList A a xs -> InList A a (x::xs).

Require Import List.

Theorem pigeonhole : forall (xs : list nat),
    length xs < fold_right plus 0 xs -> exists x : nat, InList nat (S (S x)) xs.
  intros.
induction xs.
simpl in H.
apply False_ind.
apply (lt_n_O 0 H).
simpl in H.
destruct a.
apply lt_Snm_nm in H.
apply IHxs in H.
destruct H.
exists x.
constructor.
apply H.
destruct a.
simpl in H.
apply lt_S_n in H.
apply IHxs in H.
destruct H.
exists x.
constructor.
apply H.
exists a.
constructor.
Qed.