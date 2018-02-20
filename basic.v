
Theorem and_commutative : (forall A B :Prop,  A /\ B -> B /\ A).
intros.
elim H.
intros.
split.
auto.
auto.
Qed.

