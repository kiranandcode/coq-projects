From mathcomp 
Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit.

(* 
* In Coq the way a lambda is defined is as follows:
* (fun n => n + 1) 2
*
* We can associate names with operations, using a definition:
* Definition f := fun n => n + 1. 
*)

Definition f := fun n => n + 1.


Print f.


(*
* Within coq, well typed expressions can be computed
* this means that they are reduced to a simpler form.
*)


Definition h (n: nat) : nat -> nat := fun m => n + m * 2.


Definition repeat_twice (g : nat -> nat) : nat -> nat := fun x => g (g x).

(* Coq also supports local definitions *)
Definition fun_with_local (g : nat) : nat := let x := g + 2 in x * x.

(* booleans are a definition that are loaded
* into coq upon launch. 
* 
* to use a boolean we can use an if then statement
*)

Definition twoVthree (b : bool) := if b then 2 else 3.

(* We can also do pattern matching with inductive data types *)
Definition prednn n := if n is p.+1 then p else n.

(* for matching with multiple cases, we can use a match *)

Definition three_patterns n :=
    match n with
    | u.+1.+1.+1.+1 => u
    | v.+1 => v
    | 0 => n
    end.


(* also note that n.+1 is equivalent to (S n) *)


(* we can define recursive functions in coq using fixpoint*)
Fixpoint addnn n m := if n is p.+1 then (addn p m).+1 else m.

Fixpoint eqnnn n m :=
    match n, m with
    | 0, 0 => true
    | p.+1, q.+1 => eqn p q
    | _, _ => false
    end.


(* 
* In coq terminology, we call a container a group of datatypes which have been grouped together so that they can be manipulated as a single object.  lists of nats *)
Inductive listn := niln | consn (hd : nat) (t1 : listn).

Inductive cust_list (A : Type) := cust_nil | cust_cons (hd : A) (t1 : cust_list A).

(* Type is the type of all types, seq is Type -> Type - a type constructor*)
(* mathcomp provides a series of definitions of lists
* Check 1 :: 2 :: 3 :: nil.
*)

(* mathcomp also provides a utility tool for the repeated application of right associative
* operations *)
Definition tandb (a b c : bool) := [&& a, b & c].
(* the last element is always seperated by & rather than a comma *)
Eval compute in [seq i.+1 | i <- [:: 2; 3]].


(* coq provides the record syntax for a shorthand equivalent to defining an inductive type
* with a single data constructor.*)

Record making_a_point (A : Type) : Type := myPoint { x : A; y : nat; z : nat }.


Section iterators.
    Variables (T : Type) (A: Type).
    Variables (f : T -> A -> A).

    Fixpoint foldr a s :=
        if s is x ::xs then f x (foldr a xs) else a.


    Variable init : A.
    Variables x1 x2 : T.

    Eval compute in foldr init [:: x1; x2].
End iterators.

Section addition.

    Fixpoint adds n m := if n is p.+1 then adds p m.+1 else m.
    Fixpoint addn n m := if n is p.+1 then (adds p m).+1 else m.

    Variable n : nat.

    Eval simpl in (adds n.+1 7).-1.
    Eval simpl in (addn n.+1 7).-1.




End addition.


Section exercises.

    Inductive triple (A : Type) : Type := mk_triple (x : A) (y: A) (z: A).

    Notation "( a , b , c )" := (mk_triple a b c).

    Definition fst (A : Type) (p : triple A) : A := match p with
    | mk_triple x _ _ => x
    end.

    Definition snd (A : Type) (p : triple A) : A := match p with mk_triple _ y _ => y end.

    Definition thrd (A : Type) (p : triple A) : A := match p with mk_triple _ _ z => z end.


    Notation "p .1" := (fst p). 
    Notation "p .2" := (snd p). 
    Notation "p .3" := (thrd p) (at level 2). 

        Eval compute in (4, 5, 8).1.
        Eval compute in (4, 5, 8).2.
        Eval compute in (4, 5, 8).3.
End  exercises.


(*
* In this section the book describes how to state elementary candidate theorems starting with identities
*
* Coq provides the binary predicate eq with the infix notation =
* this statement is used to state that two objects are equal
*
* we can start with a few of coq's ground equality statements
*
* ground means that the statements do not contain any parameter variables.
*
* The check command can not only be used to verify the type of some expression, but to also check whether a formal statement is well formed or not.
*)


Check 3 = 3.
Check false && true = false.


(*
* much like the type system in coq ensures that function applications are correct, the type system also ensures that theorems are well formed.
*
* Formal statements in coq are themselves terms and have a type.
*
* The equlity statement is obtained by applying eq to two arguments of the same type, and results in a well formed term of type prop for proposition.
*
* While check ensures the formed ness of a formal theorem, it does not check the provability:
*)
Check 3 = 4.




(*
* In order to establish that an equality holds, the user should announce that they are going to prove a lemma.
* This can be done using a special command such as Lemma, Theorem, Remark, Corollary.
*
*
* To begin a Proof of a theroem simply use the Proof command to indicate the start of the proof text.
*
*)

Lemma my_first_lemma : 3 = 3.
Proof.
    (* in the coq system, the user builds a formal proof by providing instructions to the
    * coq system that  describe the construction
    *  of the proof
    * the list of instruction is called a proof script, and the commands are tactics
    *
    * Once a proof is completed the Qed command can be called which verifies that the proof is actually correct.
*)
    (* The statement in question holds by definition as the two sides of the equality are
    *  syntactically the same
    * The by tactical applies a tactic, 
    * and then attempts to solve it by computation
    * in this case as the values are the same by computation, no extra work is necassary.
    *)
    by [].
Qed.
About my_first_lemma.

(* ground identities are a special case of statements called identities.
*
* an identity is an equality relation A = B that holds regardless of the values that are substituted for variables in A and B.
* for example we can state the identity expressing associativity of addition on natural numbers
*
*)
Lemma addnA (m n k : nat) : m + (n + k) = m + n + k.
Admitted.


Lemma dvdn_mul d1 d2 m1 m2 : d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Admitted.

Lemma my_second_lemma : 2 + 1 = 3.
Proof.
    (* shallow embedded, so we can just compute the result to be the same.*)
    by [].
Qed.


Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof.
    by [].
Qed.

Lemma negbK (b : bool) : ~~ (~~ b) = b.
Proof.
    (* can not prove by computation,as b can not be expanded *)
    by case: b.
Qed.


Lemma leqn0 n : (n <= 0) = (n == 0).
Proof.
    by case: n => [| k].
Qed.

Fixpoint muln (m n : nat) : nat :=
    if m is p.+1 then n + muln p n else 0.

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Proof.
    case:  m => [| m] //.
    case: n => [| k] //.
    by rewrite muln0.
Qed.
(* page 56 *)

