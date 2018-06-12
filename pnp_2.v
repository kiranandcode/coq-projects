From mathcomp.ssreflect
Require Import ssrnat.
From mathcomp.ssreflect
Require Import ssreflect.


(*
*
* Now we will be considering proofs in Coq.
* Much like how all types are elements of the Set kind,
* all proofs have types that are elements of the Prop type.
* 
* We prove that a statement P is true by using them to construct
* an element that has a type of an element in Prop.
*
* For example:
* Print True.
* Inductive True : Prop :=  I : True
*)

Theorem true_is_true: True.

(* Note: at this point we are currently in the middle of a proof.
* the Theorem/Example/Lemma etc. acts as a definition for an entity - 
* *not necassarily a proof.
* 
*)
Proof.
    (* At this point, our Goals look like:
    *  
    *   1 subgoal
    *   ======================== ( 1 / 1 )
    *   True
    *
    * i.e we need to find a way of making our entity
    * true_is_true an element of True
    * 
    * How can we do that?
    *
    *
    * well looking at the definition, the answer becomes clear.
    * we can simply use True's only constructor.
    * I
    *
    * we do this using exact I.
    *)
    exact I.
    (* having proven all requirements, we end the proof. *)
Qed.

(* Infact, this overall proof could have been written into the entity as follows: *)
Definition true_is_true' : True := I.
(* however, through our earlier proof, we were able to split the proof process
*  into several smaller chunks.
*  For a proof of this scale, that is not useful; however when dealing with
*  larger more complex proofs, the theorem method can be invaluable.
*)

(*
*
* While we have suggested that the definition and theorem entities are equivalent,
* they actually have subtle differences.
*
* The definition entity can be executed and a result retrieved from the definition
* i.e definition f (a : ...
* i.e Eval compute in f 3.
*
* the theorem entity can not be executed - it is opaque, encapsulating it's internals.
* one way to interpret this is as though the theorem is a fact, that has been checked
* to be true, and can now be treated as an axiom.
* 
* On the other hand a definition is transparent, allowing access to it's internals.
* 
* we can see this distinction more clearly if we attempt to evaluate the proofs.
*
* Eval compute in true_is_true.
*    = true_is_true
*    : True
*
* Eval compute in true_is_true'.
*    = I
*    : True
*
* So the aim of a proof is to show that the type of the entity is inhabited.
* True_is_true says, don't worry, True contains a value. 
* on the other hand, true_is_true' provides the exact value.
*
*
* infact, we can exactly use Theorem to "prove" the unit type:
*)

Theorem unprovable : unit.
Proof.
    exact tt.
Qed.

(*
* So we can clearly see that Theorems aren't magic to do with props,
* they just demonstrate the existance of a inhabitant of the type.
*
* Notice also, that True's definition is very simmilar to unit's
* infact, there is a theorem called the Curry-Howard-Equivalence
* which states that the True is isomorphic to the unit type.
*
*
* Furthermore, False is represented very simmilarly to the empty type.
*
*
* simmilarly, remember how we noted that the empty-type argument functions could produce
* a value of any type if an element of empty was produced and that this was simmilar to 
* false implying anything in propositional logic?
*
*
* The curry-howard equivalence demonstrates that this is not just a coincidence, but
* must be true, given the definition of logic.
*
* just for fun, let's prove 1 = 2 using False as an assumption.
*)

Theorem obviously_incorrect : False -> 1 = 2.
Proof.
    (*
    * we will now use the fact that the false induction principle is
    * False_ind : forall (P: Prop), False -> P.
    * thus if we pass in 1 = 2 as P, we get
    *
    * False -> 1 = 2.
    *
    * Thereby demonstrating that the type is not empty.
    *)
    exact (False_ind (1 = 2)).
    
Qed.

(* seeing as proofs using False are quite simple, 
* let's use this opportunity to explore the different 
* ways in which proofs can be constructed.
* 
* First let's try proving it using the apply statement.
* The apply statement looks through the head types 
* (a subcomponent of the given type), matches the goal
* 
* in this case, if we supply False_ind, the apply
* tactic can identify that if P := 1 = 2, then the
* whole type matches the goal.
*)

Theorem obv_incorr': False -> 1 = 2.
Proof.
    apply False_ind.
Qed.

(*
* now let's use the case tactic.
* this causes coq to deconstruct the assumptions of the goal.
* in this case the first assumption is False,
*)

Theorem obv_incorr'': False -> 1 = 2.
Proof.
    case.
Qed.


Theorem imp_trans: forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
    move=> P Q R.
    move=> H1 H2 a.
    apply H2.
    apply H1.
    exact a.
Qed.


Theorem forall_dist: forall a, (forall (P Q : a -> Prop), (forall x, P x -> Q x) -> ((forall y, P y) -> (forall z, Q z))).
Proof.
    move=> a P Q.
    move=> H1 H2.
    move=> b.
    apply H1.
    apply H2.
Qed.

Theorem imp_trans' (P Q R: Prop) : (Q -> R) -> (P -> Q) -> P -> R.
Proof.
    move=> H1 H2.
    move: (imp_trans P Q R)=> H.
    apply H.
    done.
    done.
Qed.

Module Connectives.
Variables P Q R: Prop.

Goal P -> R -> P /\ R.
Proof.
    move=> p r.
    constructor 1.
    done.
    done.
Qed.


Goal P /\ Q -> Q.
Proof.
    case.
    intros a b.
    exact b.       (* Done old school style - equiv is just done. *)
Qed.


Goal Q -> P \/ Q \/ R.
Proof.
    move=> q.
    constructor 2.
    constructor 1.
    exact q.            (* Can be done more succintly as by left; right. *)
Qed.


Goal P \/ Q -> Q \/ P.
Proof.
    case.
    move=> x.
    by right.
    by left.
Qed.

Theorem absurd: P -> ~P -> Q.
Proof.
    move=>p H;
    move: (H p).
    case.
Qed.

Theorem contraP: (P -> Q) -> ~Q -> ~P.
Proof.
    move=> H Hq.
    move /H.
    move /Hq. 
    case.
Qed.


Theorem ex_imp_ex A (S T: A -> Prop): (exists a: A, S a) -> (forall (x: A), S x -> T x) -> exists (b: A), T b.
Proof.
    case=> a Hs Hst.
    exists a.
    by apply: Hst.
Qed.


Inductive my_ex A (S: A -> Prop) : Prop := my_ex_intro x of S x.

(* Goal forall A (S: A -> Prop), my_ex A S <-> exists y: A, S y.
Proof.
    split.
    case.
    move=> H.
    move=> c.
    exists H.
    done.
    case.
    move=> H c.*)
