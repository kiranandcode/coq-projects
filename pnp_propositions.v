From mathcomp.ssreflect
Require Import ssreflect ssrnat seq.


Require Import Classical_Prop.

Definition pierce_law: forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
    move=> P Q.
    move=> H.
    apply: Peirce.
    move=> Hs.
    apply: H.
    move /Hs.
    apply: False_ind.
Qed.


Definition double_neg' : forall P : Prop, (~~P) -> P.
Proof.
    move=> P.
    move=> nnp.
    apply: Peirce.
    move=> H.
    destruct nnp.
    assumption.
Qed.


Definition excluded_middle : forall P : Prop, P \/ ~ P.
Proof.
    move=> P.
    rewrite /conj .
    

