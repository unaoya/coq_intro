Definition Subset (X : Set) : Type := X -> Prop.
Definition whole (X : Set) : Subset X := fun (x : X) => x = x.
Definition empty (X : Set) : Subset X := fun (x : X) => x <> x.

Inductive incl {X : Set} : Subset X -> Subset X -> Prop :=
| Incl_intro : forall S1 S2 : Subset X,
    (forall x : X, S1 x -> S2 x) -> incl S1 S2.

Variable X : Set.

Lemma whole_incl_all : forall U : Subset X, incl U (whole X).
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold whole.
  auto.
Qed.

Lemma all_incl_empty : forall U : Subset X, incl (empty X) U.
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold empty in H.
  destruct H.
  auto.
Qed.

Lemma incl_trans : forall U V W : Subset X, incl U V -> incl V W -> incl U W.
Proof.
  intros.
  apply Incl_intro.
  intros.
  destruct H.
  destruct H0.
  apply H0.
  apply H.
  apply H1.
  Qed.