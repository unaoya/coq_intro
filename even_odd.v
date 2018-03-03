Inductive even:nat -> Prop :=
| even_0 : even 0
| even_S : forall n, odd n -> even (S n)
with odd:nat -> Prop :=
       | odd_S : forall n, even n -> odd (S n).

Theorem plus_odd : forall n m,
    (even n -> odd m -> odd(n+m)) /\
    (odd n -> odd m -> even(n+m)).
Proof.  
  induction n.
intros.  
split.
intros.
simpl.
auto.
intros.
simpl.
inversion H.
intros.
split.
intros.
destruct (IHn m).
simpl.
apply odd_S.
apply H2.
inversion H.
auto.
auto.
intros.
simpl.
apply even_S.
destruct (IHn m).
apply H1.
inversion H.
auto.
auto.
Qed.

Theorem plus_even_odd_odd : forall n m,
    even n -> odd m -> odd (n+m).
Proof.
  intros.
  destruct (plus_odd n m).
  apply H1.
  auto.
  auto.
Qed.
