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

Definition sum_no_zero n := 
        let: P := (fun n => if n is 0 then unit else nat) in
                nat_rec P tt (fun n' m =>
                match n' return P n' -> _ with
                | 0 => fun _ => 1
                | n''.+1 => fun m => my_plus m (n'.+1)
                end m) n.

