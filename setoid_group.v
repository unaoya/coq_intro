(* http://study-func-prog.blogspot.jp/2012/04/coq-group-on-setoid.html *)
Require Import Relation_Definitions Setoid Morphisms.
Require Import Arith Omega.

Inductive Z' : Set :=
| mkZ' : nat -> nat -> Z'.

Definition eq'(z1 z2:Z') : Prop :=
  match z1, z2 with
  | (mkZ' p1 n1), (mkZ' p2 n2) => (p1 + n2 = p2 + n1)
                                    end.

Definition minus'(z:Z') :=
  match z with
  | mkZ' a b => mkZ' b a
                     end.
Definition plus'(z1 z2:Z') :=
  match z1, z2 with
  | (mkZ' a1 b1), (mkZ' a2 b2) => (mkZ' (a1+a2) (b1+b2))
                                    end.

Lemma refl_eq' : reflexive _ eq'.
Proof.
  unfold reflexive.
  intro.
  destruct x as [a b].
  unfold eq'.
  omega.
Qed.

Lemma sym_eq' : symmetric _ eq'.
Proof.
  unfold symmetric.
  intros.
  destruct x.
  destruct y.
  unfold eq'.
  unfold eq' in H.
  omega.
Qed.

Lemma trans_eq' : transitive _ eq'.
Proof.
  unfold transitive.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold eq' in *.
  omega.
Qed.

Add Parametric Relation : Z' eq'
    reflexivity proved by refl_eq'
    symmetry proved by sym_eq'
                         transitivity proved by trans_eq' as Z'_setoid.

Add Parametric Morphism :
  minus' with signature (eq' ==> eq') as minus'_mor.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold minus'.
  unfold eq' in *.
  omega.
Qed.

Add Parametric Morphism :
  plus' with signature (eq' ==> eq' ==> eq') as plus'_mor.
Proof.
  intros.
  destruct x.
  destruct y.
  destruct x0.
  destruct y0.
  unfold plus'.
  unfold eq' in *.
  omega.
Qed.

Class Group {S:Set}(eq:S->S->Prop)
      (e:S)(inv:S->S)(op:S->S->S) := {
                                      equiv : Equivalence eq;
                                      equiv_dec : forall x y:S, {eq x y} + {~(eq x y)};
                                      inv_mor : forall x y:S, eq x y -> eq (inv x) (inv y);
                                      op_mor : forall x1 y1 x2 y2:S, eq x1 y1 -> eq x2 y2 ->
                                                                     eq (op x1 x2) (op y1 y2);
                                      op_assoc : forall x y z:S, eq (op (op x y) z) (op x (op y z));
                                      left_unit : forall x:S, eq (op e x) x;
                                      right_unit : forall x:S, eq (op x e) x;
                                      left_inv : forall x:S, eq (op (inv x) x) e;
                                      right_inv : forall x:S, eq (op x (inv x)) e}.

Instance Z'_group : Group eq' (mkZ' O O) minus' plus'.
Proof.
  apply Build_Group.
  apply Z'_setoid.
  intros.
  destruct x.
  destruct y.
  unfold eq'.
  eapply eq_nat_dec.
  intros.
  destruct x.
  destruct y.
  unfold minus'.
  unfold eq' in *.
  omega.
  intros.
  destruct x1.
  destruct x2.
  destruct y1.
  destruct y2.
  unfold plus'.
  unfold eq' in *.
  omega.
  intros.
  destruct x.
  destruct y.
  destruct z.
  unfold plus'.
  unfold eq'.
  omega.
  intros.
  destruct x.
  unfold plus'.
  unfold eq'.
  omega.
  intros.
  destruct x.
  unfold plus'.
  unfold eq'.
  omega.
  intros.
  destruct x.
  unfold minus'.
  unfold plus'.
  unfold eq'.
  omega.
  intros.
  destruct x.
  unfold minus'.
  unfold plus'.
  unfold eq'.
  omega.
Defined.  