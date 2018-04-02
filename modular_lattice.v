Section ModularLattice.
Require Import Relation_Definitions Setoid Morphisms.

Class POSet
      (S : Type)
      (eq : S -> S -> Prop)
      (le : S -> S -> Prop)
  := {
      POS_equiv :> Equivalence eq;
      POS_le_mor : forall x x' : S, eq x x' -> forall y y' : S, eq y y' -> le x y -> le x' y';
      POS_le_refl : forall x : S, le x x;
      POS_le_trans : forall x y z : S, le x y -> le y z -> le x y;
      POS_le_antisym : forall x y : S, le x y -> le y x -> eq x y
    }.

Require Import Coq.Sets.Powerset.
Parameter S : Set.
Parameter E : Ensemble S.

  