From mathcomp.ssreflect 
Require Import ssreflect.

From mathcomp.ssreflect
Require Import ssrbool.

From mathcomp.ssreflect
Require Import ssrnat.

From mathcomp.ssreflect
Require Import seq.



Theorem imp_trans : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
    move=> P Q R.
    move=> Hpq.
    move=> Hqr.
    move=> p.
    apply: Hqr.
    exact: (Hpq p).
Qed.

Theorem demorgan : forall (P Q : Prop), ~(P \/ Q) -> (~ P) /\ (~ Q).
Proof.
    move=> P Q.
    move=> not_P_or_Q.
    split.
    intros b.
    elim not_P_or_Q.
    left.
    exact: b.
    intros b.
    elim not_P_or_Q.
    right.
    exact: b.
Qed.

