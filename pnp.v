From mathcomp.ssreflect
Require Import ssreflect ssrbool.
From mathcomp.ssreflect
Require Import ssrnat.


(* Recap: we can define simple inductive types as seen before 
Inductive unit : Set := it. 
*)

(* seemingly, types of symbols are inferred to be elements
* i.e it : unit
*)

(* Inductive types can be empty *)
Inductive empty: Set := .

(* Recap: Types can hold multiple values
    Inductive bool : Set := true : bool | false : bool.
*)


(* Recap: quick example of a simple 
*  non-recursive function 
    Definition negate b :=
        match b with
        | true => false
        | false => true
        end.
*)

(* A simple custom add operation:
*    add n m:
*       if n == 0:
*           return m
*       else:
*           return (add (n-1) m) + 1
*)
Fixpoint custom_plus n m :=
    match n with
    | 0 => m
(* New: we haven't used temporary variables before - looks like they act like haskell. *)
    | n'.+1 => let tmp := custom_plus n' m in tmp.+1
    end.

(* 
* ssreflect provides a couple of utility constructs that can make proofs faster.
* specifically, the if-is notation
* which is exactly rust's if-let construct.
*)
Fixpoint custom_plus' (n m: nat) :=
    if n is n'.+1 then (custom_plus' n' m).+1
                  else m.

(* COOL stuff: now we're cooking with functionals!
* we're going to use the recursion principle 
* to implement custom_plus 
*)
Definition custom_plus'' (n m: nat) :=
    nat_rec (fun _ => nat) m (fun n' m' => m'.+1) n.
(*
* All values of P n are natural numbers
* f (base of the recursion is m)
* f0 n' m' returns m'.+1
* and then is applied to n.
*
* so once executed, it becomes
* f0 (m-1) (f0 (m-2) (f0 (m-3) .... (f0 1 0) ..)
* which evaluates to 
*  0.+1.+1.+1 ... .+1 = result
*)

Example plus_works: custom_plus'' 2 3 = 5.
simpl.
reflexivity.
Qed.

(* Note how Coq's compile time restrictions allows for dependantly typed functions
* to illustrate the point, we'll implement a complex one
*)
Definition sum_no_zero n :=
    let: P := (fun n => if n is 0 then unit else nat) in
    nat_rec P tt (fun n' m =>
        match n' return P n' -> _ with
        | 0 => fun _ => 1
        | n''.+1 => fun m => custom_plus'' m (n'.+1)
        end m) n.

