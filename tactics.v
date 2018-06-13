(* From Yale Flint's detailed list of tactics. *)

Inductive Option : Set :=
| Fail : Option
| Ok : bool -> Option.


Definition get : forall x : Option, x <> Fail -> bool.
Proof.
    intros x.
    induction x.
