Definition plus (n : nat)(m : nat) : nat := n + m.
Eval compute in plus 3 5.                                                 
Definition id (A : Type)(x : A) : A := x.
Eval compute in id nat 5.

Definition prop0 : forall (A : Prop), A -> A := fun A x => x.
Definition prop1 : forall (A B C : Prop), (B -> C) -> (A -> B) -> (A -> C) :=
  fun A B C f g x => f (g x).
Definition prop2 : forall (A B : Prop), A -> (A -> B) -> B :=
  fun A B x f => f x.
Definition prop3 : forall (A B C : Prop), (A -> B -> C) -> (B -> A -> C) :=
  fun A B C f x y => (f y) x.
Definition prop4 : forall (A : Prop), A -> A.
Proof.
  intros.
  apply H.
Qed.

