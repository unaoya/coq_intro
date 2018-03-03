Section ML.
  Variables A B C : Prop.
  Theorem s : (A -> (B -> C)) -> (A -> B) -> (A -> C).
  Proof.
    intros.
    apply H.
    apply H1.
    apply H0.
    apply H1.
  Qed.
  End ML.