Require Import Bool.

Theorem true_is_True: Is_true true.
Proof.
        simpl.
        exact I.
Qed.

Theorem False_cannot_be_proven : ~False.
Proof.
        unfold not.
        intros proof_of_false.
        exact proof_of_false.
Qed.


Theorem not_eqb_true_false: ~(Is_true (eqb true false)).
Proof.
        simpl.
        exact False_cannot_be_proven.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
        intros a.
        case a.
        simpl.
        exact I.
        simpl.
        exact I.
Qed.

Theorem thm_eqb_a_t: (forall a : bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
        intros a.
        case a.
        simpl.
        intros proof_of_True.
        exact I.
        simpl.
        intros proof_of_False.
        case proof_of_False.
Qed.


Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
        intros A B.
        intros proof_of_A.
        pose(proof_of_A_or_B := or_introl proof_of_A : A \/ B).
        exact proof_of_A_or_B.
Qed.


Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
        intros A B.
        intros proof_of_B.
        pose (proof_of_A_or_B := or_intror proof_of_B : A \/ B).
        exact proof_of_A_or_B.
Qed.

Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
        intros A B.
        intros A_or_B.
        case A_or_B.
        intros proof_of_A.
        pose (proof_of_B_or_A := or_intror proof_of_A : B \/ A).
        exact proof_of_B_or_A.
        intros proof_of_B.
        pose (proof_of_B_or_A := or_introl proof_of_B : B \/ A).
        exact proof_of_B_or_A.
Qed.


Theorem both_and: (forall A B :  Prop, A -> B -> A /\ B).
Proof.
        intros A B.
        intros HA HB.
        refine (conj _ _).
                exact HA.
                exact HB.
Qed.

Theorem and_commutes : (forall A B : Prop, A /\ B -> B /\ A).
Proof.
        intros A B.
        intros A_and_B.
        
        case A_and_B.
        intros HA HB.
        refine (conj _ _).
                exact HB.
                exact HA.
Qed.


Theorem and_commutes_again: (forall A B : Prop, A /\ B -> B /\ A).
Proof.
        intros A B.

        intros A_and_B.

        destruct A_and_B as [ proof_of_A proof_of_B].
        refine (conj _ _).
                exact proof_of_B.
                exact proof_of_A.
Qed.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
        intros a b.
        unfold iff.
        refine (conj _ _).
                intros H.
                case a, b.
                simpl.
                refine (or_introl _).
                        exact I.
                simpl.
                exact (or_introl I).
                exact (or_intror I).
                simpl in H.
                case H.
                intros H.
                case a,b.
                simpl.
                exact I.
                exact I.
                exact I.
                case H.
                intros A.
                simpl in A.
                case A.
                intros B.
                simpl in B.
                case B.
Qed.

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
        intros a b.
        unfold iff.
        refine (conj _ _).
        intros H.
        case a, b.
        exact (conj I I).
        simpl in H.
        case H.
        simpl in H.
        case H.
        simpl in H.
        case H.
        intros H.
        case a, b.
        simpl.
        exact I.
        simpl in H.
        destruct H as [ A B].
        case B.
        simpl in H.
        destruct H as [ A B].
        case A.
        destruct H as [ A B].
        simpl.
        simpl in A.
        exact A.
Qed.

Theorem notb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
        intros a.
        unfold iff.
        refine (conj _ _).
        case a.
        simpl.
        unfold not.
        intro PF.
        intro PT.
        exact PF.
        simpl.
        intros PT.
        unfold not.
        intros PF.
        exact PF.
        case a.
        simpl.
        unfold not.
        intros PTF.
        intros T.
        intros H.
        unfold not.
        case a.
        simpl.
