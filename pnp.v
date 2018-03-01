From mathcomp.ssreflect
Require Import ssrnat.
Inductive unit : Set := it.

Check tt.

Definition negate b :=
        match b with
        | true => false
        | false => true
        end.


Fixpoint my_plus n m :=
        match n with
        | 0 => m
        | n'.+1 => let tmp := my_plus n' m in tmp.+1
        end.

Eval compute in my_plus 6 7.

