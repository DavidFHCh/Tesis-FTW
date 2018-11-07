(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.

(* Converted type declarations: *)

Record MonadTrans__Dict t := MonadTrans__Dict_Build {
  lift__ : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> t m a }.

Definition MonadTrans t :=
  forall r, (MonadTrans__Dict t -> r) -> r.

Existing Class MonadTrans.

Definition lift `{g : MonadTrans t}
   : forall {m} {a}, forall `{(GHC.Base.Monad m)}, m a -> t m a :=
  g _ (lift__ t).

(* No value declarations to convert. *)

(* External variables:
     GHC.Base.Monad
*)
