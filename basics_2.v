Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday(d: day) : day :=
        match d with
        | monday => tuesday 
        | tuesday => wednesday 
        | wednesday => thursday 
        | thursday => friday 
        | friday => saturday 
        | saturday => sunday 
        | sunday => monday
        end.


(* We can run functions using commands of the form Eval ____ in (expr). *)
(*  other values than simple can be used, but have yet to have been seen *)
Eval simpl in (next_weekday friday).

(* examples act as unit test like constructs - except using proofs rather than testing*)
(* You write a statement about your functions and then you must proove it *)
Example test_next_weekday:
        (next_weekday (next_weekday saturday)) = monday.

Proof.
        simpl.
        reflexivity.
Qed.


(* we can use this adt to describe boolean values *)
Inductive bool : Type :=
| true : bool
| false : bool.


Definition negb (b : bool) : bool := 
        match b with
        | true => false
        | false => true
        end.

Definition andb ( b1 : bool ) ( b2 : bool)  : bool :=
        match b1 with 
        | true => b2
        | false => false
        end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
        match b1 with
        | true => true
        | false => b2
        end.


Example test_orb1: (orb true false) = true.
Proof.  simpl.  reflexivity.  Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.


Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1 : bool) (b2 : bool) : bool :=
        match b1 with
        | false => true
        | true => negb b2
        end.

Example test_nandb1: (nandb true false) = true.
Proof.  simpl.  reflexivity.  Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl.  reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


Definition andb3 (b1 : bool) (b2 : bool) (b3: bool) : bool :=
        match b1 with
        | false => false
        | true => andb b2 b3
        end.


Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.


Module Playground1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.


Definition pred (n : nat) : nat :=
match n with
| O => O
| S n' => n'
end.

Definition minustwo (n : nat) : nat :=
        match n with 
        | O => O
        | S O => O
        | S (S n') => n'
        end.


Fixpoint evenb (n : nat) : bool :=
        match n with
        | O => true
        | S O => false
        | S (S n') => evenb n'
        end.


Fixpoint oddb (n : nat) : bool := 
        match n with
        | O => false
        | S O => true
        | S ( S n') => oddb n'
        end.

Example test_oddb1 : (oddb (S O)) = true.
Proof.  simpl.  reflexivity.  Qed.

Example test_oddb2 : (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.



Fixpoint plus (n : nat) (m : nat) : nat :=
        match n with
        | O => m
        | S n' => plus n' m
        end.

Fixpoint mult (n m : nat) : nat :=
        match n with
        | O => O
        | S n' => plus m (mult n' m)
        end.

Fixpoint minus (n m : nat) : nat :=
        match n, m with
        | O, _ => O
        | S _, O => n
        | S n', S m' => minus n' m'
        end.


Fixpoint exp (n m : nat) : nat :=
        match m with
        | O => S O
        | S m' => mult n (exp n m')
        end.

End Playground1.

Module Playground2.
Fixpoint factorial ( n : nat ) : nat := 
        match n with
        | O => S O
        | S O => S O
        | S n' => mult n (factorial n')
        end.



Example test_factorial1 : ( factorial 3 ) = 6.
Proof.  simpl.  reflexivity.  Qed.

Example test_factorial2 : (factorial 5) = (mult 10 12).
Proof.  simpl.  reflexivity.  Qed.



Notation "x + y" := (plus x y)
        (at level 50, left associativity) : nat_scope.

Notation "x - y" := (minus x y)
        (at level 50, left associativity) : nat_scope.

Notation "x * y" := (mult x y)
        (at level 40, left associativity) : nat_scope.


Fixpoint beq_nat (n m : nat) : bool :=
        match n with
        | O => match m with
                | O => true
                | S m' => false
                end
        | S n' => match m with
                | O => false
                | S m' => beq_nat n' m'
                end
        end.

Fixpoint ble_nat (n m : nat) : bool :=
        match n with
        | O => true
        | S n' =>
                        match m with
                        | O => false
                        | S m' => ble_nat n' m'
                        end
        end.

Example test_ble_nat1 : (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_ble_nat2 : (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.


Example test_ble_nat3 : (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.


Definition blt_nat (n m : nat) : bool :=
        match beq_nat n m with
        | true => false
        | false => ble_nat n m
        end.

Example test_blt_nat1 : (blt_nat 2 2) = false.
Proof.  compute.  reflexivity.  Qed.

Example test_blt_nat2 : (blt_nat 2 4) = true.
Proof.  compute. reflexivity. Qed.

Example test_blt_nat3 : (blt_nat 4 2) = false.
Proof.  compute. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.  intros n.  simpl.  reflexivity.  Qed.


Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.  intros n.  simpl.  reflexivity.  Qed.


Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.  intros n.  unfold plus.  reflexivity.  Qed.


Theorem mult_O_l : forall n : nat, 0 * n = 0.
Proof.  intros n.  unfold mult.  reflexivity.  Qed.  

        
Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.        
Proof.
intros n m.
intros H.
rewrite <- H. (* rewrite takes a equality expression and rewrites a goal using it *)
reflexivity.
Qed.


Theorem plus_id_exercise : forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
        intros n m o.
        intros hypothesis_n_equals_m.
        intros hypothesis_m_equals_o.
        rewrite <- hypothesis_m_equals_o.
        rewrite <- hypothesis_n_equals_m.
        reflexivity.
Qed.


Theorem mult_O_plus : forall n m : nat, (0 + n) * m = n * m.
Proof.
        intros n m.
        rewrite -> plus_O_n.
        reflexivity.
Qed.



Theorem mult_1_plus : forall n m : nat, (1 + n) * m = m + (n * m).
Proof.
        intros n m.
        simpl.
        reflexivity.
Qed.


Theorem plus_1_neq_0_firsttry :forall n : nat, beq_nat (n + 1) 0 = false.
Proof.
        intros n.
        destruct n as [| n']. 
        simpl.
        reflexivity.
        simpl.
        reflexivity.
Qed.


Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
        intros b.
        destruct b.
        simpl.
        reflexivity.
        simpl.
        reflexivity.
Qed.


Theorem zero_nbeq_plus_1 : forall n : nat, beq_nat 0 (n + 1) = false.
Proof.
        intros n.
        destruct n as [| n'].
        simpl.
        reflexivity.
        simpl.
        reflexivity.
Qed.




End Playground2.
