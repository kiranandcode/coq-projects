From mathcomp 
Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit.


(* Exercise 1 *)

Inductive Triple A B C := mk_triple (a : A) (b : B) (c : C).

Definition fst A B C (p : Triple A B C) := match p with mk_triple a _ _ => a end.
Definition snd A B C (p : Triple A B C) := match p with mk_triple _ b _ => b end.
Definition thrd A B C (p : Triple A B C) := match p with mk_triple _ _ c => c end.


Notation "( a , b , c )" := (mk_triple a b c).
Notation "p .3" := (thrd p) (at level 2).

Eval compute in fst (4, 5, 8).
Eval compute in snd (true, false, 1).
Eval compute in (2, true, false).3.


(* Exercise 2 *)
Definition sum_with_iter (n m : nat) := iter n S m.

(* Exercise 3 *)
Definition mult_with_iter (n m : nat) := iter n (fun x => x + m) m.


(* Exercise 4 *)
Fixpoint nth_element A (default: A) (list : seq A) (n : nat) := if list is head::tail
        then if n is n'.+1 
                then nth_element default tail n'
                else head
        else default.
                

Eval compute in nth_element 99 [:: 3; 7; 11; 22] 2.
Eval compute in nth_element 99 [:: 3; 7; 11; 22] 7.


(* Exercise 5 *)
Fixpoint rev A (list : seq A) := if list is head::tail
    then (rev tail)  ++ [:: head]
    else nil.

Eval compute in rev [:: 1; 2; 3].


(* Exercise 6 *)
Definition flatten A (list : seq (seq A)) := foldr cat nil list. 




