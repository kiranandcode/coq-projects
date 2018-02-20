
Theorem and_commutative : (forall A B :Prop,  A /\ B -> B /\ A).
Proof.
intros.
elim H.
intros.
split.
auto.
auto.
Qed.


Theorem or_commutative : (forall A B : Prop, A \/ B -> B \/ A).
Proof.
        intros.
        elim H.
        intro HA.
        clear H. (* remove unnecessary proofs *)
        right.
        trivial.
        auto.
Qed.


Section Predicate_calculus.
        Variable D : Set.
        Variable R : D -> D -> Prop.
Section R_sym_trans.
Hypothesis R_symmetric: (forall x y : D, R x y -> R y x).
Hypothesis R_transitive: (forall x y z : D, R x y -> R y z -> R x z).

Lemma refl_if : forall x : D, (exists y , R x y) -> R x x.
Proof.
        intros x x_Rlinked.
        elim x_Rlinked.
        intros y Rxy.
        apply R_transitive with y.
        assumption.
        apply R_symmetric. 
        assumption.
Qed.
End R_sym_trans.

