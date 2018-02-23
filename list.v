From mathcomp.ssreflect
Require Import seq.

Notation seq := list.

Fixpoint length' A (l : list A) :=
        match l with
        | nil => 0
        | _ :: l' => S ( length' A l')
        end.


(* Merge sort in COQ - 1st split list into two *)
Fixpoint split' A (l : list A) : list A * list A :=
        match l with
        | nil => (nil, nil)
        | a::nil => (a::nil, nil)
        | a :: b :: l' => let (l1, l2) := split' A l' in (a::l1, b::l2)
        end.

(* Merge sort in COQ - merge two lists *)
Definition merge' A (less : A->A->bool) : list A -> list A -> list A :=
        fix merge'' l1 : match l1 with
        | nil => (fun l2 => l2)
        | x1 :: l1' =>
                (fun l2 => match l2 with
                | nil => l1
                | x2 :: l2' =>
                                if less x1 x2 then x1 :: merge'' l1' l2
                                        else x2 :: merge'' l1 l2'
                end)
        end.
