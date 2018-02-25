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


Check ((0 + 1) + 1).
End. Playground2.
