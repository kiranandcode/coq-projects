From mathcomp.ssreflect
Require Import ssreflect.

From mathcomp.ssreflect
Require Import ssrnat seq ssrbool.


Theorem one_eq_two : False -> 1 = 2.
Proof.
    case.
Qed.

Theorem one_eq_two' : False -> 1 = 2.
Proof.
    exact: (False_ind (1 = 2)).
Qed.

Theorem one_eq_two'': False -> 1 = 2.
Proof.
    exact: (fun (f : False) => match f with end).
Qed.

Theorem imp_trans: (forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R).
Proof.
    move=> A B C.
    move=> H2 H1.
    move=> a.
    apply: H1.
    apply: H2.
    assumption.
Qed.


Theorem imp_trans': (forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R).
Proof.
    move=> A B C.
    move=> H1 H2 a.
    exact: (H2 (H1 a)).
Qed.

Theorem forall_distrib: (forall P Q : Prop -> Prop, (forall (x: Prop), (P x) -> (Q x)) -> ((forall (y : Prop), (P y)) -> (forall (z: Prop), (Q z)))).
Proof.
    move=> P Q.
    move=> H1.
    move=> H2.
    move=> z.
    apply: H1.
    apply: H2.
Qed.

Theorem imp_trans'' (P Q R : Prop) : (Q -> R) -> (P -> Q) -> P -> R.
Proof.
    move=> H1 H2.
    move=> p.
    apply: H1.
    apply: H2.
    exact: p.
Qed.

Theorem imp_trans''' (P Q R : Prop) : (Q -> R) -> (P -> Q) -> P -> R.
Proof.
    move=> H1 H2.
    move: (imp_trans P Q R)=> H.
    apply: H.
    exact H2.
    exact H1.
Qed.


Goal forall P R : Prop, P -> R -> P /\ R.
Proof.
    move=> P R.
    move=> p r.
    constructor 1; done.
Qed.


Goal forall P Q : Prop, P /\ Q -> Q.
Proof.
    move=> P Q.
    move=> R.
    destruct R as [ p q ].
    done.
Qed.

Goal forall P Q : Prop, P /\ Q -> Q.
Proof.
    move=> P Q.
    case.
    move=> p q.
    done.
Qed.



Goal forall P Q R : Prop, Q -> P \/ Q \/ R.
Proof.
    move=> P Q R.
    move=> q.
    right.
    left.
    done.
Qed.

Goal forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
    move=> P Q.
    move=> p_or_q.
    case p_or_q.
    move=> p.
    right.
    done.
    move=> q.
    left.
    done.
Qed.


Goal forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
    move=> P Q.
    case=> x.
    right; done.
    left; done.
Qed.


Theorem absurd (P Q : Prop) : P -> ~P -> Q.
Proof.
    move=> p H.
    move : (H p).
    apply: False_ind.
Qed.


Theorem contapos (P Q : Prop) : (P -> Q) -> (~Q -> ~P).
Proof.
    move=> H.
    move=> Hq.
    move /H.
    assumption.
Qed.


Theorem ex_imp_ex A (S T : A -> Prop): (exists a: A, S a) -> (forall x: A, S x -> T x) ->
    exists b: A, T b.
Proof.
    case=> a Hs Hst.  
    exists a.
    apply: Hst.
    done.
Qed.



Inductive my_ex A (S: A -> Prop) : Prop := my_ex_intro x of S x.

Goal forall A (S : A -> Prop), my_ex A S <-> exists y: A, S y.
Proof.
    move=> A s.
    split.
    case.
    move=> H.
    move=> s_H.
    by exists H.
    move=> H; destruct H as [a s_x].
    move: (my_ex_intro A s a)=> H.
    by apply: H.
Qed.



