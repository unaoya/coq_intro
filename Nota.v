(* http://www.ne.jp/asahi/fmsci/fmmath/coqp/vvof/Nota.v *)
Parameter Element : forall A:Type, Set -> A -> Prop.
Implicit Arguments Element [A].
Notation "a /e b" := (Element a b) (at level 50).

Axiom IntCl : forall C:Set -> Prop, forall x:Set, (x /e C) <-> (C x).

Definition Subcl (A B:Type) (a:A) (b:B) : Prop:=
  forall x:Set, (Element (A := A) x a) -> (Element (A := B) x b).
Implicit Arguments Subcl [A B].
Notation "C /c= D" := (Subcl C D) (at level 50).

Theorem Subc_refl : forall (T:Type)(A:T), A/c= A.
Proof.
  intros.
  intro.
  intro.
  apply H.
Qed.

Theorem Subc_trans : forall (A B C:Type)(a:A)(b:B)(c:C),
    (a /c= b) -> (b /c= c) -> (a /c= c).
Proof.
  intros.
  intro.
  intro.
  apply H0.
  apply H.
  apply H1.
Qed.

Definition Subcln (A B:Type)(a:A)(b:B):Prop:=
  (Subcl (A:=A)(B:=B) a b) /\ ~(Subcl (A:=B)(B:=A) b a).
Implicit Arguments Subcln [A B].
Notation "a /cc b" := (Subcln a b) (at level 50).

Definition Eqcl (A B:Type)(a:A)(b:B):Prop:=
  (Subcl (A:=A) (B:=B) a b) /\ (Subcl (A:=B)(B:=A) b a).
Implicit Arguments Eqcl [A B].
Notation "C /= D" := (Eqcl C D) (at level 50).

Theorem Eqcl_refl:forall (T:Type)(A:T), A/= A.
Proof.
  intros.
  split.
  apply Subc_refl.
  apply Subc_refl.
Qed.

Definition Set_eq := forall (a b:Set), (a /= b) -> a = b.
Definition ExEmp := exists y:Set, forall x:Set, ~(x /e y).
Definition SPair := forall a b:Set, exists y:Set, forall x:Set,
        (x /e y) <-> ((x = a) \/ (x = b)).
Definition SSum := forall x:Set, exists y:Set, forall z:Set,
        (z /e y) <-> exists u:Set, ((z /e u) /\ (u /e x)).
Definition SPow := forall x:Set, exists y:Set, forall z:Set,
        (z /e y) <-> (z /c= x).
Definition SRepl := forall P:Set -> Set -> Prop,
    (forall x y z:Set, (P x y) -> (P x z) -> y = z) ->
    forall u:Set, exists v:Set, forall y:Set,
          (y /e v) <-> exists x:Set, ((x /e u) /\ (P x y)).
Definition SCom := forall P:Set -> Prop,
    forall u:Set, exists v:Set, forall y:Set,
          (y /e v) <-> ((y /e u) /\ (P y)).

Theorem Ex2uni : Set_eq -> forall P:Set -> Prop,
      (exists y:Set, forall x:Set, (x /e y) <-> (P x)) ->
      (exists! y:Set, forall x:Set, (x/e y) <-> (P x)).
Proof.
  intros Hse P (y,H).
  exists y.
  red.
  split.
  assumption.
  intros.
  apply Hse.
  split.
  intros z Hzy.
  apply H0.
  apply (H z).
  assumption.
  intro.
  intro.
  apply H.
  apply (H0 x).
  assumption.
Qed.

Theorem Empuni : Set_eq -> ExEmp -> exists! y:Set, forall x:Set, ~(x /e y).
Proof.
  intros Hse (y,Hee).
  exists y.
  red.
  split.
  assumption.
  intros.
  apply Hse.
  split.
  intro.
  intro.
  apply False_ind.
  apply (Hee x).
  assumption.
  intro.
  intro.
  apply False_ind.
  apply (H x).
  assumption.
Qed.

