(* Quick Coq *)

(* Use check to view the types and structures of values *)

(* Use definition to define constants: *)
Definition example1 := fun x : nat => x * x + 2 * x + 1.

(* We can force coq to evaluate an expression,
* and actually do work, to do so, coq must do some symbolic execution.
* multiple strategies are available to do this,
* we will use compute.*)

Definition sum5 := fun (x y z a b : nat) => x + y + z + a + b.


Require Import Bool.

(* while bools are defined as part of the language, much of the functionality of boolean
* values are achieved by drawing from a library Bool. 
* this includes facilities such as if else, 
* conjunctions etc.
*)
Eval compute in if true then 3 else 4.

Require Import Arith.
Require Import Nat.
Require Import List.

Lemma example2 : forall a b : Prop, a /\ b -> b /\ a.
Proof.
    intros.
    destruct H.
    split.
    exact H0.
    exact H.
Qed.

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
    intros.
    destruct H.
    right.
    exact H.
    left.
    exact H.
Qed.

Lemma example : 3 <= 5.
Proof.
    apply le_S.
    apply le_S.
    apply le_n.
Qed.


Lemma example5: forall x y, x <= 10 -> 10 <= y -> x <= y.
    intros.
    apply le_trans with (m := 10).
    assumption.
    assumption.
Qed.

(* Lemma example6: forall x y, (x + y) * (x + y) = x * x + 2 * x * y + y * y.
Proof.
    intros.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_add_distr_r.
    rewrite <- plus_assoc with (n := x * x).
    rewrite mult_comm with (n := y) (m := x).
    pattern (x * y) at 1; rewrite <- mult_1_l.
Exercise for reader.
*)


Fixpoint count n l :=
    match l with
    | nil => 0
    | a ::t1 => 
            let r := count n t1 in
            if beq_nat n a then
                1 + r
            else
                r
    end.


Lemma insert_incr : forall n l, count n (n::l) = 1 + count n l.
Proof.
    intros.
    induction l.
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.



Inductive bin : Type :=
    | L : bin
    | N : bin -> bin -> bin.


Example example7 (t : bin) : bool := 
    match t with N L L => false
    | _ => true
    end.

Fixpoint flatten_aux (t1 t2:bin) : bin :=
    match t1 with
    | L => N L t2
    | N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
    end.

Fixpoint flatten (t : bin) : bin :=
    match t with
    | L => L
    | N t1 t2 => flatten_aux t1 (flatten t2)
    end.

Fixpoint size (t : bin) : nat :=
    match t with
    | L => 1
    | N t1 t2 => 1 + (size t1) + (size t2) 
    end.

Lemma example7_size : 
    forall t : bin, example7 t = false -> size t = 3.
    intro t.
    destruct t.
    simpl.
    intros H.
    discriminate H.
    destruct t1.
    destruct t2.
    simpl.
    auto.
    intros H; discriminate H.
    intros H; discriminate H.
Qed.


Lemma flatten_aux_size :
    forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
    induction t1.
    intros t2.
    simpl.
    ring.
    intros t2.
    simpl.
    rewrite IHt1_1.
    rewrite IHt1_2.
    ring.
Qed.


Lemma flatten_size : forall t, size (flatten t) = size t.
Proof.
    intros.
    induction t.
    simpl.
    ring.
    simpl.
    rewrite  flatten_aux_size.
    rewrite IHt2.
    ring.
Qed.


Lemma not_subterm_self_1 : forall x y, ~ x = N x y.
Proof.
    induction x.
    intros y.
    discriminate.
    intros y.
    intros abs.
    injection abs.
    intros h2 h1.
    assert (IHx1' : x1 <> N x1 x2).
        apply IHx1.
    case  IHx1'.
    exact h1.
Qed.


Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenS : forall x:nat, even x -> even (S (S x)).

Lemma even_mult : forall x, even x -> exists y, x = 2 * y.
Proof.
    intros x.
    intros H.
    elim H.
    exists 0.
    ring.
    intros x0 Hevenx0 IHx.
    destruct IHx as [y Heq].
    exists (y + 1).
    rewrite Nat.mul_add_distr_l.
    rewrite <- Heq.
    ring.
Qed.



Lemma not_even_1 : ~even 1.
Proof.
    intros even1.
    inversion even1.
Qed.


Lemma even_inv : forall x, even (S (S x)) -> even x.
    induction x.
    intros even2.
    exact even0.
    intros even_3.
    inversion even_3.
    exact H0.
Qed.
