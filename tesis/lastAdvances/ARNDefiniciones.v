(* Default settings (from HsToCoq.Coq.Preamble) *)

(* Archivo con las definiciones de los arboles rojinegros. *)
Generalizable All Variables.

Require Export Utf8_core.
Require Import Coq.Classes.RelationClasses.
Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Program.Equality.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Err.
Require GHC.Types.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Color : Type := R : Color |  B : Color.

Inductive RB a : Type := E : RB a |  T : Color -> (RB a) -> a -> (RB a) -> RB a.

(* Tree for insert*)
Arguments E {_}.
Arguments T {_} _ _ _ _.


Instance Default__Color : GHC.Err.Default Color := GHC.Err.Build_Default _ R.

(* Converted value declarations: *)

Definition member {a} `{GHC.Base.Ord a} : a -> RB a -> bool :=
  fix member arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | x, E => false
           | x, T _ tl y tr =>
               if x GHC.Base.< y : bool then member x tl else
               if x GHC.Base.> y : bool then member x tr else
               true
           end.
Hint Resolve member.
