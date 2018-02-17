Inductive False : Prop := .

Inductive True : Prop :=
        | I : True.


Inductive bool : Set :=
        | true : bool
        | false : bool.

Theorem True_can_be_proven : True.
Proof.
        exact I.
Qed.

Definition not (A : Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Theorem False_cannot_be_proven : ~False.
Proof.
        unfold not.
        intros proof_of_false.
        exact proof_of_false.
Qed.

Theorem Fale_cannot_be_proven_again : ~False.
Proof.
        intros proof_of_false.
        case proof_of_false.
Qed.

Theorem thm_true_imp_true : True -> True.
Proof.
        intros proof_of_True.
        exact I.
Qed.


Theorem thm_false_imp_true : False -> True.
Proof.
        intros proof_of_false.
        exact I.
Qed.

Theorem thm_false_imp_false : False -> False.
Proof.
        intros proof_of_false.
        case proof_of_false.
Qed.

Theorem thm_true_imp_false : ~(True -> False).
Proof.
        unfold not.
        intros T_implies_F.
        refine (T_implies_F _).
                exact I.
Qed.


Theorem absurd2 : forall A C : Prop, A -> ~ A -> C.
Proof.
        intros A C.
        intros proof_of_A proof_that_A_cannot_be_proven.
        unfold not in proof_that_A_cannot_be_proven.
        pose(proof_of_false := proof_that_A_cannot_be_proven proof_of_A).
        case proof_of_false.
Qed.
