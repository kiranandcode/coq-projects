From mathcomp.ssreflect
Require Import ssreflect ssrbool.
From mathcomp.ssreflect
Require Import ssrnat.
From mathcomp.ssreflect
Require Import seq.


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
    (* P is a function that return the unit type if input is 0 else the natural type *)
    let: P := (fun n => if n is 0 then unit else nat) in
    (* our type generator function is P, our initial element is the only element in unit
    * tt, our combiner function *)
    nat_rec P tt (fun n' m =>
        match n' return P n' -> _ with (* Note: the return construct is a type annotation *)
        | 0 => fun _ => 1  (* maps from unit to nat - is the first function in the
                sequence  *)
        | n''.+1 => fun m => custom_plus'' m (n'.+1) (* maps from nat to nat *)
        end m) n.

(* Having looked at the definition of empty_rect, we can see that it's type signiture:
* (P: empty -> Type) -> (e: empty) -> P e
* i.e given a mapping from empty to a type, and given an element of empty, we can construct
* a member of any type
* 
* This is a vacuous truth - much like false -> anything, we can never get an element of empty
* so this would never apply.
*)

(*
* However, a type with no elements is not the only way we can construct an 
* un-instantiateable type.
*
* for example:
*)

Inductive strange : Set := cs : strange -> strange.

(*
* The definition of strange_rect is as follows:
*strange_rect
*    : forall P : strange -> Type,
*      (forall s : strange, P s -> P (cs s)) -> forall s : strange, P s
* i.e,  given a mapping from strange to type = P,
*       and a mapping from P s to P (cs s)
*       we can get P s
*)


(*
* Now consider the definition of prod - coq's equivalent of a pair type.
*
* Inductive prod (A B : Type) : Type := A -> B -> A * B
*
*  This becomes clearer when you look at how  a pair is constructed.
* 
*  Check pair 1 tt.
*  
* (1, tt)
*      : nat * unit
*
*  which can be corroborated by considering the type of the type prod
*  
* Check prod. 
*
* prod
*     : Type -> Type -> Type
*
* I.e, like in Haskell, the prod takes in two arguments and produces a type.
*
* We can manually specify the type (rather than allowing it to be inferred) using @:
*
* Check @pair nat unit 1 tt.
*
*)


(*
*
* Now, finally, to include some bread-and-butter functional programming utilities,
*  let's consider the union and list types - sum and seq.
* Sum : (A B : Type) : Type = inl : A -> A + B 
*                           | inr : B -> A + B.
*
* seq : (A : Type) : Type := nil : seq A
*                           | cons: A -> seq A -> seq A
* 
* We can also do nifty typedefs as follows:
*)
Notation seq := list.


(* 
*
* Let's try using this stuff out by implementing an alternate function, which alternates the elements of two lists.
*
*)

(* This is how we'd implement it in Haskell,
*  However, this is not permitted by the coq language
*  as it has no clear recursive variant - no parameter is always decreasing 
Fixpoint alternate (a : seq nat) (b : seq nat) : seq nat :=
    match a return seq nat with
    | nil => b
    | cons head' tail' => cons head' (alternate b tail)
    end.
*  we can implement it as follows:
*)

Fixpoint alternate (a b : seq nat) : seq nat :=
        match a return seq nat with
                | nil => b
                | cons head_a tail_a => match b with
                                    | nil => cons head_a tail_a
                                    | cons head_b tail_b => cons head_a (cons head_b
                                            (alternate
                                            tail_a tail_b))
                                    end
                end.


(*
*
* Now we will consider how we can use ssreflect to speed up our proofs
*  here we'll consider a shorter way to define pairs
*)

Inductive custom_prod (A B : Type) : Type := custom_pair of A & B.

(*
* Here, we will use of & structure to allow A and B to be the parameters of the type as well a the constructor.
*
* However with this format, we need to provide the types explicitly.
* We can work around this using the Implicit arguments of coq.
*)

Implicit Arguments custom_pair [A B].


(* 
*
* Alongside implicit arguments, coq provides additional utilities is the form of
* custom notation to represent our own types for ease of reading.
*)

Notation "X ** Y" := (custom_prod X Y) (at level 2).
Notation "( X ,, Y )" := (custom_pair X Y).

(*
*
* You can see this notation in action by running Check (1 ,, 3).
*)

