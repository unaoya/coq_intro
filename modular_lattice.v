Class Lattice (L : Type)(eq : L -> L -> Prop)
      (le : L -> L -> Prop)
      (sup : L -> L -> L)(inf : L -> L -> L) := {
                                                 L_POSset :> POSet L eq le;
                                                 L_sup_mor : forall x x' : L, eq x x' ->
                                                                              forall y y' : L, eq y y' ->
                                                                                               eq (sup x y) (sup x' y');
                                                 L_inf_mor : forall x x' : L, eq x x' ->
                                                                              forall y y' : L, eq y y' ->
                                                                                               eq (inf x y) (inf x' y');
                                                 L_sup_l : forall x y : L, le x (sup x y);
                                                 L_sup_r : forall x y : L, le y (sup x y);
                                                 L_sup_min : forall x y z : L, le x z -> le y z -> le (sup x y) z;
                                                 L_inf_l : forall x y : L, le (inf x y) x;
                                                 L_inf_r : forall x y : L,  le (inf x y) y;
                                                 L_inf_max : forall x y z : L, le z x -> le z y -> le z (inf x y)}.
                                                 
                                                         