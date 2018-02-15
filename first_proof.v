Theorem first_proof: (forall A : Prop, A -> A).
Proof.
        intros A.
        intros proof_of_A.
        exact proof_of_A.
Qed.


Theorem forward_small : (forall A B : Prop, A -> (A->B) -> B).
Proof.
        intros A.
        intros B.
        intros proof_of_A.
        intros A_implies_B.
        pose (proof_of_B := A_implies_B proof_of_A).
        exact proof_of_B.
Qed.


Theorem backward_small : (forall A B : Prop, A -> (A->B)->B).
Proof.
        intros A B.
        intros proof_of_A A_implies_B.
       refine (A_implies_B _). 
                exact proof_of_A.
Qed.
