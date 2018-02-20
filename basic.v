
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


