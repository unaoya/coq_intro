Definition Subset (X : Set) : Type := X -> Prop.
Definition whole (X : Set) : Subset X := fun (x : X) => x = x.
Definition empty (X : Set) : Subset X := fun (x : X) => x <> x.
Inductive incl {X : Set} : Subset X -> Subset X -> Prop :=
| Incl_intro : forall S1 S2 : Subset X,
    (forall x : X, S1 x -> S2 x) ->
    incl S1 S2.
Lemma whole_incl_all {X : Set} : forall U : Subset X, incl U (whole X).
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold whole.
  auto.
Qed.
Lemma all_incl_empty {X : Set} : forall U : Subset X, incl (empty X) U.
Proof.
  intros.
  apply Incl_intro.
  intros.
  unfold empty in H.
  destruct H.
  auto.
Qed.
Lemma incl_trans {X : Set} : forall U V W : Subset X, incl U V -> incl V W -> incl U W.
Proof.
  intros.
  destruct H.
  destruct H0.
  apply Incl_intro.
  intros.
  auto.
Qed.  
Definition bigcap {X : Set} (I : Set) (index : I -> Subset X) : Subset X :=
  fun (x : X) => forall i : I, (index i) x.
Definition intsec {X : Set} (S1 S2 : Subset X) :=
  let index (b : bool) := match b with
                          | true => S1
                          | false  => S2
                          end in
  bigcap bool index.
Lemma intsec_in {X : Set} : forall (U V : Subset X) (x : X), (intsec U V) x -> U x.
Proof.
  intros.  
  unfold intsec in H.  
  unfold bigcap in H.
  specialize H with true.
  simpl in H.
  apply H.
Qed.  
Lemma intsec_incl {X : Set} : forall U V : Subset X, incl (intsec U V) U.
Proof.  
  intros.
  split.
  apply intsec_in.
Qed.
Lemma intsec_equle {X : Set} : forall U V : Subset X, incl U V -> (forall x : X, (intsec U V) x <-> U x).
Proof.
  intros.
  split.
  apply intsec_in.
  intros.
  unfold intsec.
  unfold bigcap.
  induction i.
  apply H0.
  destruct H.
  auto.
Qed.