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


