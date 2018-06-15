From mathcomp.ssreflect
Require Import ssrnat ssreflect seq.

Require Import Classical_Prop.



Definition excluded_middle : forall P : Prop, P \/ ~P.
Proof.
    move=> P.
    apply: Peirce.
    move=> H.
    right.
    move=> p.
    apply: H.
    by left.
Qed.



Definition demorgan_not_and_not : forall P Q : Prop, ~( ~P /\ ~Q ) -> P \/ Q.
Proof.

    (* Asume P and Q are any propositonal statements *)
    move=> P Q.
    (* Assume the premise of the argument is true *)
    move=> H.
    (* From Peirce, we know, forall P, (P -> False) -> P is true *)
    (* So rewrite, the current goal in Peirce's for with P as the goal *)
    apply: Peirce.
    (* Assume that the premise is true *)
    move=> Hs.
    (* Generalize the statement, using the initial assumption H *)
    move: (H).
    (* Consider the possible values of the current premise *)
    (* we can see that this statement 
    *   ((~ P /\ ~ Q) -> False) -> P \/ Q
    *   is dependant only on  ~ P /\ ~ Q *)
    case.
    (* To construct a conjunction, both subclauses must be proven *)
    constructor.
    (* To show something is false, we need to show assuming it, leads to False *)
    (* Assume that it is true *)
    move=> p.
    (* From our assumption P \/ Q -> False *)
    apply: (Hs).
    (* we assumed a proof for P exists, thus P \/ Q is true *)
    by left.
    (* same as above *)
    move=> q.
    apply: Hs.
    by right.
Qed.


Definition implies_to_or: forall P Q : Prop, (P -> Q) -> (~P \/ Q).
Proof.
    (* Assume P and Q are any Propositional variables *)
    move=> P Q.
    (* Asume the premise of the argument is true *)
    move=> H.
    (* Using peirce's law, add a premise to the proposition*)
    (* the premise being, that if P is proven, then P -> False can also be proven *)
    apply: Peirce.
    (* Assume that the new premise (P -> False) is true *)
    move=> Hs.
    (* We will prove ~P \/ Q by proving ~P *)
    left.
    (* By definition of ~P, assuming P is true will lead to a contradiction *)
    move=> p.
    (* Using the premise introduced by Peirce, which is ~ P \/ Q -> False  *)
    (* the only way we could get false, is if ~ P \/ Q is proven*)
    apply: Hs.
    (* if P is true, how can ~P \/ Q be true? *)
    (* Obviously, we need to prove that Q is proven *)
    right.
    (* using our initial hypothesis, if P is proven, then Q can be proven *)
    by apply: H.
Qed.



From mathcomp.ssreflect 
Require Import ssrbool eqtype.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Implicit Arguments.


(* my_eq is an inductive type, parameterized by a type and a value of that type.
* the constructor, my_ex_refl is of type my_eq x x, which means that to construct the 
* type, two elements of the same type must be provided:
*  i.e  my_eq x y => (my_eq  x) y  // note assuming implicit type arguments
*                 : (X -> Prop) X  // let x be the type of x
*  not only does it tell us that y must be of the same type as x,
*  but also, from the only constructor, my_ex_refl : my_eq a a.
*                   x must equal y.
*)
Inductive my_eq (A : Type) (x : A) : A -> Prop := my_ex_refl : my_eq x x.
Notation "x === y" := (my_eq x y) (at level 70).

(* Coq's type resolving technique will identify this fact, adn automatically
* rewrite instances of one side with the other: *)
Lemma my_eq_sym A (x y: A) : x === y -> y === x.
Proof.
    case.
    done.
Qed.


Lemma my_eq_leibniz A (x y: A) (P : A -> Prop) : x === y -> P x -> P y.
Proof.
    case.
    move=> p_x.
    done.
Qed.



Lemma disaster : 2 === 1 -> False.
Proof.
    move=> H.
    pose D  x := if x is 2 then False else True.
    have D1: D 1.
    done.
    move: H D1.
    case.
    done.
Qed.


Lemma disaster2 : 1 === 2 -> False.
Proof.
    (* We are proving that 1 === 2 is false *)
    (* Assume that 1 === 2 is true *)
    move=> H.
    (* Consider the function D, which returns true if x is 1, and false if x is not *)
    pose D x := if x is 1 then False else True.
    (* We shall prove that D 2 is true *)
    have D2: D 2.
    (* By definition, it is true *)
    done.
    (* Now, reintroduce the assumptions into the goal as premises *)
    move: H D2.
    (* Now consider a case analysis of the first premise *)
    (* from the case analysis, we can infer that 2 should be replaceable by 1 in all
    * occurances *)
    case.
    (* We can trivially show that D 1 is false. *)
    done.
Qed.



Lemma disaster3: 2 = 1 -> False.
Proof.
    move=> H.
    pose D x := if x is 2 then False else True.
    have D2 : D 2.
    done.
    move: H D2.
    done.
Qed.

Lemma disaster3': 2 = 1 -> False.
Proof.
    done.
Qed.


Definition double {A} (f: A -> A) (x : A) := f (f x).
Fixpoint nat_iter (n: nat) {A} (f: A -> A) (x: A) : A :=
    if n is S n' then f (nat_iter n' f x) else x.


Lemma double2 A (x: A) f t:
    t = double f x -> double f t = nat_iter 4 f x.
Proof.
    (* Assume that the premise is true *)
    move=> Et.
    (* Using the premise, expand t *)
    rewrite Et.
    (* expand double using it's definition *)
    rewrite /double.
    (* expand nat_iter using it's definition *)
    rewrite /nat_iter.
    (* use reflexivity of eq to conclude the result *)
    reflexivity.
Qed.


Lemma double2' A (x: A) f t:
    t = double f x -> double f t = nat_iter 4 f x.
Proof.
    (* -> is like :, but if the premise is an equality, rewrites all values *)
    move=>->.
    rewrite /double.
    rewrite /nat_iter.
    done.
Qed.



Definition f x y := x + y.
Goal forall x y, x + y + ( y + x ) = f y x + f y x.
Proof.
    move=> x y.
    rewrite /f.
    congr (_ + _).
    rewrite [y + _] addnC.
    done.
Qed.


Goal forall x y z, (x  + ( y + z )) = (z + y + x).
Proof.
    move=> x y z.
    rewrite [x + _] addnC.
    rewrite [y + _] addnC.
    done.
Qed.



Lemma huh n m : (m <= n) /\ (m > n) -> False.
Proof.
    suff X: m <= n -> ~(m > n).
    case.
    done.
    elim: m n => [| m IHm] [| n].
    done.
    done.
    done.
    exact: IHm (n ).
Qed.


Definition maxn m n := if m < n then n else m.

(*Lemma max_is_max m n: n <= maxn m n /\ m <= maxn m n.
Proof.
    elim: n m => [| m IHm] [| n].
    done.
    done.
    done.
    move: (IHm (n + 1))=> IHmn.
    exact: IHm n. 


    Exercise for the reader. 
    *)
