(* http://qnighy.github.io/coqex2014/ex1.html *)
Theorem tautology : forall P : Prop, P -> P.
Proof.
  intros P H.
  assumption.
Qed.
(*
Theorem wrong : forall P : Prop, P.
Proof.
  intros P.
Qed.  
 *)
Theorem Modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q.
  intros H H0.
  apply H0.
  apply H.
Qed.
Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
  intros P Q H.
  destruct H.
  intro.
  assert Q.
  apply H0.
  apply H1.
  apply H.
  apply H2.
Qed.
Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros P Q H.
  destruct H.
  intro.
  contradiction.
  apply H.