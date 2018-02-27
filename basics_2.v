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


Theorem identity_fn_applied_twice : forall (f : bool -> bool), (forall (x : bool), f x = x) -> forall ( b : bool), f (f b) = b.
Proof.
        intros f.
        intros hypothesis_f_is_ident.
        intros b.
        rewrite -> hypothesis_f_is_ident.
        rewrite -> hypothesis_f_is_ident.
        reflexivity.
Qed.


Theorem negation_fn_applied_twice : forall (f : bool -> bool), (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
intros f.
intros hypothesis_f_is_neg.
intros b.
rewrite -> hypothesis_f_is_neg.
rewrite -> hypothesis_f_is_neg.
unfold negb.
destruct b.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.


Theorem andb_eq_orb : forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
intros b c.
unfold andb.
unfold orb. 
destruct b. 
intros hypothesis_c_is_true.
rewrite -> hypothesis_c_is_true. 
reflexivity.
intros hypothesis_c_is_false.
rewrite -> hypothesis_c_is_false.
reflexivity.
Qed.


Inductive bin : Type :=
| O : bin
| Twice : bin -> bin
| Plus1 : bin -> bin.

Fixpoint increment (x : bin) : bin :=
        match x with
        | O => Plus1 O
        | Plus1 O => Twice (Plus1 O)
        | Twice n' => Plus1 (Twice n')
        | Plus1 n' => Plus1 (increment n')
        end.

Fixpoint toNat ( x : bin ) : nat :=
match x with
| O => 0
| Plus1 n' => 1 + (toNat n')
| Twice n' => 2 * (toNat n')
end.


End Playground2.


Theorem andb_true_eliml : forall ( b c : bool ), andb b c = true -> b = true.
Proof.
intros b c H.
destruct b.
reflexivity.
rewrite <- H.
reflexivity.
Qed.


Theorem andb_true_elim2 : forall (b c : bool), andb b c = true -> c = true.
Proof.
intros b c H.
destruct c.
reflexivity.
rewrite <- H.
destruct b.
simpl.
reflexivity.
reflexivity.
Qed.


Theorem plus_0_r_firsttry : forall (n : nat), n + 0 = n.
Proof.
intros n.
induction n as [| n'].
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem minus_diag : forall (n : nat), minus n n = 0.
Proof.
intros n.
induction n as [| n'].
simpl.
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.


Theorem mult_0_r : forall (n : nat), n * 0 = 0.
Proof.
        intros n.
        induction n as [| n'].
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.


Theorem plus_n_Sm : forall (n m : nat), S (n + m) = n + (S m).
Proof.
intros n m.
induction  n.
simpl.
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.


Theorem plus_comm : forall (n m : nat), n + m  = m + n.
Proof.
        intros n m.
        induction n as [|n'].
        rewrite -> plus_0_r_firsttry.
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHn'.
        rewrite -> plus_n_Sm.
        reflexivity.
Qed.


Theorem plus_assoc : forall (n m p : nat), n + (m + p) = (n + m) + p.
Proof.
        intros n m p.
        induction n as [|n'].
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.


Fixpoint double (n : nat) :=
        match n with
        | O => O
        | S n' => S ( S ( double n') )
        end.

Lemma double_plus : forall (n : nat), double n = n + n.
Proof.
        intros n.
        induction n as [|n'].
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHn'.
        rewrite -> plus_n_Sm.
        reflexivity.
Qed.

Theorem mult_0_plus' : forall (n m : nat), (0 + n) * m = n * m.
Proof.
        intros n m.
        assert (H: 0 + n = n).
                simpl.
                reflexivity.
        rewrite -> H.
        reflexivity.
Qed.


Theorem plus_rearrange_firsttry : forall (n m p q : nat), (n + m) + (p + q) = (m + n) + (p + q).
Proof.
        intros n m p q.
        assert (n + m = m + n) as H.
                rewrite -> plus_comm.
                reflexivity.
        rewrite -> H.
        reflexivity.
Qed.


Theorem plus_swap : forall (n m p : nat), n + ( m + p) = m + ( n + p).
Proof.
        intros n m p.
        rewrite -> plus_assoc.
        rewrite -> plus_assoc.
        assert (m + n = n + m) as H.
               rewrite -> plus_comm. 
               reflexivity.
        rewrite -> H.
        reflexivity.
Qed.

Theorem mult_1 : forall (m : nat), m * 1 = m.
Proof.
        intros m.
        induction m as [|m'].
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHm'.
        reflexivity.
Qed.

Theorem mult_2 : forall (m : nat), m * 2 = m + m.
Proof.
        intros m.
        induction m as [|m'].
        simpl.
        reflexivity.
        simpl.
        rewrite <- plus_n_Sm.
        rewrite <- IHm'.
        reflexivity.
Qed.


Theorem plus_sn : forall (n : nat), S n = n + 1.
Proof.
        intros n.
        induction n.
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHn.
        reflexivity.
Qed.


Theorem distrobutivity_l : forall (n a b : nat), n * ( a + b ) = (n * a) + (n * b).
Proof.
        intros n a b.
        induction n.
        simpl.
        reflexivity.
        simpl.
        rewrite -> plus_assoc.
        rewrite -> IHn.
        rewrite -> plus_assoc.
        assert (b + n * a = n * a + b) as H.
                rewrite -> plus_comm. 
                reflexivity.
        assert (a + b + n * a = a + n * a + b) as H'.
                rewrite <- plus_assoc.
                rewrite <- plus_swap.
                rewrite -> plus_assoc.
                rewrite <- plus_assoc.
                rewrite -> plus_comm.
                reflexivity.
        rewrite -> H'.
        reflexivity.
Qed.

Theorem distrobutivity_r : forall (n a b : nat), (a + b) * n = ( n * a) + ( n * b).
Proof.
        intros n a b.
        induction n.
        simpl.
        rewrite -> mult_0_r.
        reflexivity.
        simpl.
        assert (b + n * b = n * b + b) as nb_comm.
                rewrite -> plus_comm.
                reflexivity.
        rewrite -> nb_comm.
        rewrite -> plus_assoc.
        assert (a + n * a + n * b + b = a + ( n * a + n * b ) + b) as simpl_h.
                rewrite -> plus_assoc.
                reflexivity.
        rewrite -> simpl_h.
        rewrite <- IHn.
        assert ((a + b) * n + b = b + (a + b) * n) as rotate_b.
                rewrite -> plus_comm.
                reflexivity.
        assert (a + ((a + b) * n + b) = a + (a + b) * n + b) as even_simpl.
                rewrite -> plus_assoc.
                reflexivity.
        assert (a + b + (a + b) * n = a + (a + b) * n + b) as rotate.
                rewrite <- even_simpl.
                rewrite -> rotate_b.
                rewrite -> plus_assoc.
                reflexivity.
        rewrite <- rotate.
        assert (a + b + (a + b) * n = (a + b) * (1 + n)).
                rewrite -> distrobutivity_l.
                rewrite -> mult_1.
                reflexivity.
        rewrite -> H.
        rewrite -> plus_sn.
        assert (1 + n = n + 1).
               rewrite -> plus_sn.
               reflexivity.
        rewrite -> H0.
        reflexivity.
Qed.       


Theorem mult_comm : forall (m n : nat), m * n = n * m.
Proof.
        intros m n.
        induction n as [|n'].
        rewrite -> mult_0_r.
        simpl.
        reflexivity.
        rewrite -> plus_sn.
        simpl.
        rewrite -> distrobutivity_l.
        rewrite -> plus_comm.
        rewrite <- distrobutivity_l.
        rewrite -> plus_comm.
        rewrite -> distrobutivity_l.
        rewrite -> distrobutivity_r.
        reflexivity.
Qed.


Inductive natprod : Type := 
        pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
        match p with
        | pair x y => x
        end.

Definition snd (p : natprod) : nat :=
        match p with
        | pair x y => y
        end.

Notation "( x , y )" := (pair x y).

Theorem subjective_pairing' : forall (n m : nat), (n,m) = (fst (n,m), snd (n,m)).
Proof.
intros n m.
simpl.
reflexivity.
Qed.

Theorem subjective_pairing : forall (p : natprod), p = (fst p, snd p).
Proof.
        intros p.
        destruct p as (n, m).
        simpl.
        reflexivity.
Qed.

Definition swap_pair (p : natprod) : natprod :=
        match p with
        | (n, m) => (m,n)
        end.

Theorem snd_fst_is_swap : forall ( p : natprod), (snd p, fst p) = swap_pair p.
Proof.
        intros p.
        destruct p as (n, m).
        simpl.
        reflexivity.
Qed.

Theorem fst_swap_is_snd : forall ( p : natprod ), fst ( swap_pair p ) = snd p.
Proof.
        intros p.
        destruct p as (n, m).
        simpl.
        reflexivity.
Qed.


Inductive natlist : Type := 
| nil : natlist
| cons : nat -> natlist -> natlist.


Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat ( n count : nat ) : natlist :=
        match count with
        | O => nil
        | S count' => n :: (repeat n count')
        end.


Fixpoint length (l : natlist) : nat :=
        match l with
        | nil => 0
        | cons head tail => S (length tail)
        end.

Fixpoint app (l1 l2 : natlist) : natlist :=
        match l1 with
        | nil => l2
        | cons head tail => cons head (app tail l2)
        end.

Notation "x ++ y" := (app x y)
                        (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof.
        unfold app.
        reflexivity.
Qed.


Definition head (default : nat) (l : natlist) : nat := 
        match l with
        | nil => default
        | h :: t => h
        end.

Definition tail (l : natlist) : natlist :=
        match l with
        | nil => nil
        | h :: t => t
        end.

Fixpoint nonzeros (l : natlist) : natlist :=
        match l with
        | nil => nil
        | h :: t => match h with
                       | 0 => (nonzeros t) 
                       | S n' => h :: (nonzeros t)
                        end
        end.



Fixpoint alternate (l1 l2 : natlist) : natlist :=
        match l1 with
        | nil => match l2 with
                | nil => nil
                | h :: t => h :: t
                end
        | h1 :: t1 => match l2 with
                | nil => h1 :: t1
                | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
                end
        end.


Theorem app_ass : forall (l1 l2 l3 : natlist), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
        intros l1 l2 l3.
        induction l1 as [| n l1'].
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHl1'.
        reflexivity.
Qed.

Theorem app_length : forall (l1 l2 : natlist), length (l1 ++ l2) = (length l1) + (length l2).
Proof.
        intros l1 l2.
        induction l1 as [| n l1'].
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHl1'.
        reflexivity.
Qed.

Fixpoint snoc (l : natlist) (v : nat) : natlist :=
        match l with
        | nil => [v]
        | h :: t => h :: (snoc t v)
        end.

Fixpoint rev (l : natlist) : natlist :=
        match l with
        | nil => nil
        | h :: t => snoc (rev t) h
        end.


Example test_rev1 : rev [1,2,3] = [3,2,1].
Proof.  simpl.  reflexivity.  Qed.


Theorem length_snoc : forall (n : nat), forall (l : natlist), length (snoc l n) = S (length l).
Proof.
        intros n.
        intros l.
        induction l.
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHl.
        reflexivity.
Qed.


Theorem rev_length_firsttry : forall (l :natlist), length (rev l) = length l.
Proof.
        intros l.
        induction l.
        simpl.
        reflexivity.
        simpl.
        rewrite -> length_snoc.
        simpl.
        rewrite <- IHl.
        reflexivity.
Qed.


Theorem app_nil_end : forall (l : natlist), l ++ [] = l.
Proof.
        intros l.
        induction l.
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHl.
        reflexivity.
Qed.


Theorem snoc_eqiv_app : forall (l : natlist), forall ( n : nat), snoc l n = l ++ [n].
Proof.
        intros l n.
        induction l.
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHl.
        reflexivity.
Qed.

Theorem rev_distrib : forall (l n : natlist), rev (l ++ n) = (rev n) ++ (rev l).
Proof.
        intros n l.
        induction n.
        rewrite -> app_nil_end.
        simpl.
        reflexivity.
        simpl.
        rewrite -> IHn.
        rewrite -> snoc_eqiv_app.
        rewrite -> snoc_eqiv_app.
        rewrite -> app_ass.
        reflexivity.
Qed.



Theorem sub_rev_involutive : forall (l : natlist), forall (n : nat), rev (snoc (rev l) n) = n :: (rev (rev l)).
Proof.
        intros l n.
        induction l.
        simpl.
        reflexivity.
        rewrite -> snoc_eqiv_app.
        simpl.
        rewrite -> snoc_eqiv_app.
        rewrite -> rev_distrib.
        simpl.
        rewrite -> rev_distrib.
        simpl.
        reflexivity.
Qed.
        

Theorem rev_involutive : forall (l : natlist), rev (rev l) = l.
Proof.
        intros l.
        induction l.
        simpl.
        reflexivity.
        simpl.
        rewrite -> sub_rev_involutive.
        rewrite -> IHl.
        reflexivity.
Qed.


Theorem app_app4 : forall (l1 l2 l3 l4 : natlist), l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
        intros l1 l2 l3 l4.
        rewrite -> app_ass.
        rewrite -> app_ass.
        reflexivity.
Qed.


Lemma nonzeros_length : forall (l1 l2 : natlist), nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
        intros l1 l2.
        induction l1.
        simpl.
        reflexivity.
        destruct n.
        simpl.
        rewrite -> IHl1.
        reflexivity.
        simpl.
        rewrite -> IHl1.
        reflexivity.
Qed.



