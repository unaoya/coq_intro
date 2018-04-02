Definition Subset (X : Set) : Type := X -> Prop.
Definition empty (X : Set) : Subset X := fun (x : X) => x <> x.
Definition intsec {X : Set} (S1 S2 : Subset X) : Subset X :=
  fun (x : X) => S1 x /\ S2 x.
Inductive incl {X : Set} : Subset X -> Subset X -> Prop :=
| Incl_intro : forall U V : Subset X,
    (forall x : X, U x -> V x) -> incl U V.
Variable X : Set.

Hypothesis subset_equal : forall U V : Subset X, (forall x : X, U x <-> V x) -> U = V.  

Lemma incl_cap : forall {X : Set} (U V : Subset X) (x : X), incl U V -> (intsec U V) x <-> U x.
  Proof.
  intros.
  unfold intsec.
  destruct H.
  split.
intro.
apply H0.
intro.
split.
apply H0.
apply H.
apply H0.
  Qed.
  
Variable A : Set.
Variable E : A -> Subset X.
Variable r : A -> Subset X -> A.

Hypothesis A_eq : forall a b : A,  a = b -> b = a.
Hypothesis A_assoc : forall a b c : A, a = b /\ b = c -> a = c.
Hypothesis subset_eq : forall U V : Subset X, U = V -> forall a : A, r a U = r a V.
Hypothesis ps_empty : forall a b : A, r a (empty X) = r b (empty X).
Hypothesis ps_res_idempotent : forall a : A, r a (E a) = a.

Lemma res : forall a b : A, forall U : Subset X, E a = U -> r b (E a) = r b U.
Proof.
  intros.
  apply subset_eq.
  apply H.
Qed.

Lemma empty_idemp_lem : forall a : A, E a = empty X -> r a (empty X) = a.
  intros.
  apply A_eq.
  rewrite <- H.
  apply A_eq.
  apply ps_res_idempotent.
Qed.

Lemma empty_idemp : forall a b : A, ((E a) = (empty X)) -> ((E b) = (empty X)) -> a = b.
  intros.
apply empty_idemp_lem in H.
apply empty_idemp_lem in H0.
rewrite <- H.
rewrite <- H0.
apply ps_empty.
Qed.  

Hypothesis comm_e_res : forall a : A, forall U : Subset X, E (r a U) = intsec (E a) U.
Hypothesis res_assoc : forall a : A, forall U V : Subset X, r (r a U) V = r a (intsec U V).
Lemma res_id : forall a : A, forall U : Subset X, E a = U -> r a U = a.
  intros.
  rewrite <- H.
  apply ps_res_idempotent.
Qed.

Lemma inclusion : forall x : X, forall U V : Subset X, incl U V -> U x -> V x.
Proof.
  intros.
  destruct H.
apply H.
apply H0.
Qed.

Lemma intsec_and : forall U V : Subset X, forall x : X, (intsec U V) x <-> U x /\ V x.
Proof.
  intros.
  split.
  intros.
  unfold intsec in H.
  apply H.
  split.
  apply H.
  apply H.
Qed.
Lemma incl_intsec : forall U V : Subset X, forall x : X, incl U V -> (intsec U V) x <->  U x.
Proof.
  intros.
  unfold intsec.
  split.
  intro.
  apply H0.
  intro.
  destruct H.
  split.
  apply H0.
  apply H.
  apply H0.
Qed.

Lemma res_incl : forall a : A, forall U V : Subset X, incl U V -> E a = V -> r (r a V) U = r a U.
Proof.
  intros.  
  assert (r (r a V) U = r a (intsec V U)).
  apply res_assoc.
  assert (intsec V U = U).
  apply subset_equal.
  intro.
  destruct H.
  split.
  unfold intsec.
  intro.
  apply H2.
  unfold intsec.
  intro.
  split.
  apply H.
apply H2.
apply H2.
assert (r a (intsec V U) = r a U).
apply subset_eq.
apply H2.
rewrite <- H3.
  apply H1.
Qed.


  

                                                                             
                                                                    