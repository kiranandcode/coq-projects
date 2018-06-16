From mathcomp.ssreflect
Require Import ssreflect ssrnat seq ssrbool eqtype.


Section HilbertAxiom.
    Variables A B C : Prop.

    Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
    Proof.
        (* assuming the premise is true *)
        move=> H1 H2 a.
        apply: H1.
        done.
        apply: H2.
        done.
    Qed.

    Lemma HilbertS' : (A -> B -> C) -> (A -> B) -> A -> C.
    Proof.
        (* move the top of the proof stack to assumptions *)
        move=> hA1B1C hA1B hA.
        (* push on hA1B1C to the top of the proof stack *)
        move: hA1B1C.
        (* consider the proof stack minus it's top as a consequent of it's top, and ask
        * for a proof of it's arguments *)
        apply.
            (* solve the first subgoal trivially *)
            by [].
        (* generalize the result by hA1B, and then try and consider the proof stack minus
        * it's top as a consequent of it's top *)
        (* then solve trivially *)
        by apply: hA1B.
    Qed.


    Hypotheses (hA1B1C : A -> B -> C) (hA1B : A -> B) (hA : A).

    Lemma HilbertS'' : C.
    Proof.
        apply: hA1B1C; first by apply: hA.
        exact: hA1B.
    Qed.



    Lemma HilbertS''': C.
    Proof.
        exact: (hA1B1C _ (hA1B _)).
    Qed.

    Lemma HilbertS'''': C.
    Proof.
        exact: hA1B1C (hA1B _).
    Qed.


    Lemma HilbertS''''': C.
    Proof.
        exact: HilbertS''''.
    Qed.

End HilbertAxiom.



Section Symmetric_Conjunction_Disjunction.
    Lemma andb_sym : forall A B : bool, A && B -> B && A.
    Proof.
        (* Note: actual statement being proven is (A && B = true) -> (B && A = true). *)
        (* ssrbool uses auto coercion to allow for a natural representation *)
        (* case performs a case splitting on the top of the stack *)
        case.
            (* when a is true, prove by case analysis on b *)
            by case.
        (* solve the alternate case trivially *)
        by [].
    Qed.

    Lemma andb_sym': forall A B : bool, A && B -> B && A.
    Proof.
        by case; case.
    Qed.


    Lemma andb_sym'': forall A B : bool, A && B -> B && A.
    Proof.
        (* equivalent to case; case *)
        (* do 10! case. would be case; case...*)
        by do 2! case.
    Qed.


    Variables (C D : Prop) (hC : C) (hD : D).

    Lemma and_sym : forall A B : Prop, A /\ B -> B /\ A.
    Proof.
        (* note: move=> A1 B [], 
        * is shorthand for move=> A1 B; case. 
        *)
        by move=> A1 B [].
    Qed.

    Lemma or_sym : forall A B : Prop, A \/ B -> B \/ A.
    Proof.
        move=> A B [hA | hB].
        by right.
        by left.
    Qed.

    Lemma or_sym' : forall A B : Prop, A \/ B -> B \/ A.
    Proof.
        by move=> A B [hA | hB]; [by right | by left].
    Qed.


    Lemma or_sym'' : forall A B : bool, A \/ B -> B \/ A.
    Proof.
        by move=> [] [] AorB;
        (*apply/P replaces a goal using a reflection lemma. 
        * a reflection lemma is an eqivalence property *)
        apply/orP;
        (* introduce the AorB assumption *)
        move: AorB;
        (* rephrase the top of the proof stack *)
        move/orP.
    Qed.



End Symmetric_Conjunction_Disjunction.


Section R_sym_trans.
    Variables (D : Type) (R : D -> D -> Prop).

    Hypothesis R_sym : forall x y, R x y -> R y x.
    Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.
    
    Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
    Proof.
        (* assume premise is true, then case destruct the next premise *)
        move=> x [y Rxy].
        (* R x x can be achieved by applying R_trans to two arguments R x y and (R_sym R x y) *)
        by apply: R_trans _ (R_sym _ y _).
    Qed.

End R_sym_trans.




Section Smullyan_drinker.
    Variables (D : Type) (P : D -> Prop).

    Hypothesis  (d : D) (EM : forall A, A \/ ~A).

    Lemma drinker : exists x, P x -> forall y, P y.
    Proof.
        (* generalize by em, then case expand *)
        case: (EM (exists y, ~ P y)).
        (* case expand the top of the proof stack into y and notPy *)
        move=> [y notPy]. 
        (* provide y as a witness and prove *)
        by exists y.
        (* assume premise is true *)
        move=> nonotPy.
        (* provide d as a witness, discard the value, and store the result of the forall
        * *)
        exists d => _ y.
        (* generalize by EM and then case analys *)
        case: (EM (P y))=>// notPy.
        (* case analyse the results, and then use exists y as the witness *)
        by case: nonotPy; exists y.
    Qed.


    Lemma drinker' : exists x, P x -> forall y, P y.
    Proof.
        case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy]; first by exists y.
        exists d => _ y; case: (EM (P y)) =>// notPy.
        by case: nonotPy; exists y.
    Qed.


End Smullyan_drinker.


Section Equality.
    Variable f : nat -> nat.
    Hypothesis f00 : f 0 = 0.

    Lemma fkk : forall k, k = 0 -> f k = k.
    Proof.
        move=> k k0.
        by rewrite k0.
    Qed.


    Lemma fkk2 : forall k, k = 0 -> f k = k.
    Proof.
        by move=> k -> .
    Qed.


    Variable f10 : f 1 = f 0.

    Lemma ff10 : f (f 1) = 0.
    Proof.
        by rewrite f10 f00.
    Qed.


    Variables (D : eqType) (x y : D).

    Lemma eq_prop_bool : x = y -> x == y.
    Proof.
        by move/eqP.
    Qed.


    Lemma eq_bool_prop :x == y -> x = y.
    Proof.
        by move/eqP.
    Qed.


End Equality.


Section Using_Definition.

    Variable U : Type.
    Definition set := U -> Prop.
    Definition subset (A B : set) := forall x, A x -> B x.  

    Definition transitive (T : Type) (R : T -> T -> Prop) := forall x y z, R x y -> R y z -> R x z.


    Lemma subset_trans : transitive set subset.
    Proof.
        rewrite /transitive /subset => x y z subxy subyz t xt.
        by apply: subyz; apply: subxy.
    Qed.


    Lemma subset_trans2 : transitive set subset.
    Proof.
        move=> x y z subxy subyz t.
        (* rewrites can also be done using implications, however these are only one way *)
        by move/subxy; move/subyz.
    Qed.

End Using_Definition.


Lemma three : S (S (S 0)) = 3 /\ 2 = 0.+1.+1.
Proof.
    by [].
Qed.


Lemma concrete_plus : plus 16 64 = 80.
Proof.
    by [].
Qed.


Lemma concrete_plus_bis : 16 + 64 = 80.
Proof.
    by [].
Qed.



Lemma concrete_le : le 1 3.
Proof.
    by apply: (Le.le_trans _ 2 _); apply: Le.le_n_Sn.
Qed.


Lemma concrete_big_le : le 16 64.
Proof.
    by auto 47 with arith.
Qed.


Lemma concrete_big_leq : 0 <= 51.
Proof.
    by [].
Qed.


Lemma semi_concrete_leq : forall n m, n <= m -> 51 + n <= 51 + m.
Proof.
    by [].
Qed.


Lemma concrete_arith : (50 < 100) && (3 + 4 < 3 * 4 <= 17 - 2).
Proof.
    by [].
Qed.



Lemma plus_commute : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
    (* elim case analyses the top of the proof stack *)
    (* alongside this, it also produces an induction hypothesis *)
    (* the first subgoal has no variables moved to stack *)
    elim=> [| n IHn m].
    (* solve the first subgoal by computation *)
    by elim.
    (* rewrite replaces a phrase with an equivalent phrase *)
    (* -/ inverses the rewrite *)
    (* [] allows the user to specify where to rewrite *)
    (* multiple rewrites can be chained - if not preceded by another /, the rewrite is
    * done in the same place.*)
    rewrite -[n.+1 + m]/(n + m).+1 IHn.
    by elim: m.
Qed.


Lemma plus_commute' : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
    by elim=> [| n IHn m]; [elim | rewrite -[n.+1 + m]/(n + m).+1 IHn ].
Qed.



Definition edivn_rec d := fix loop (m q : nat) {struct m} := if m - d is m'.+1 then loop m'
    q.+1 else (q, m).









    



