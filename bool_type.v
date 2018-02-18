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


        
