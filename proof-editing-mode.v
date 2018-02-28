Goal forall (P Q : Prop), (forall P :Prop, (P -> Q) -> Q) -> ((P -> Q) -> P) -> P.
intros.apply H0.intro.apply (H (P -> Q)).intros.apply H2.apply H1.Qed.
  
Goal forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
intros.apply H0.apply H.apply H1.Qed.

Inductive False : Prop :=.
Definition not (A: Prop) := A -> False.
Goal forall P : Prop, P -> not (not P).
intro.intros.intro.apply H0.apply H.Qed.

Inductive or (A B : Prop) : Prop :=
| or_introl : A -> or A B
| or_intror : B -> or A B.
Goal forall (P Q : Prop), (or P Q) -> (or Q P).
intros.destruct H.apply or_intror.apply H.apply or_introl.apply H.Qed.

Inductive and (A B : Prop) : Prop :=
  conj : A -> B -> and A B.
Goal forall (P Q : Prop), (and P Q) -> (and Q P).
intros.apply conj.destruct H.apply H0.destruct H.apply H.Qed.

Goal forall (P : Prop), not (and P (not P)).
  intros.intro.destruct H.destruct H0.apply H.Qed.

Goal forall (P Q : Prop), (or (not P) (not Q)) -> (not (and P Q)).
intros.intro.destruct H0.destruct H.apply H.apply H0.apply H.apply H1.Qed.

Goal forall (P : Prop), (forall (P : Prop), (not (not P)) -> P) -> (or P (not P)).
intros.apply H.intro.apply H0.right.intro.apply H0.left.apply H1.