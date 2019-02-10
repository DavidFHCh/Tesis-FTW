(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Classes.
Require GHC.Err.
Require GHC.Types.
Import GHC.Classes.Notations.

(* Converted type declarations: *)

Inductive Color : Type := R : Color |  B : Color.

Inductive RB a : Type
  := E : RB a
  |  EBB : RB a
  |  T : Color -> (RB a) -> a -> (RB a) -> RB a.

Arguments E {_}.

Arguments EBB {_}.

Arguments T {_} _ _ _ _.

Instance Default__Color : GHC.Err.Default Color := GHC.Err.Build_Default _ R.

(* Converted value declarations: *)

Definition redden {a} : RB a -> RB a :=
  fun arg_0__ =>
    match arg_0__ with
    | T c a x b => T R a x b
    | E => GHC.Err.error (GHC.Base.hs_string__ "invariance violation")
    | EBB => GHC.Err.error (GHC.Base.hs_string__ "nunca se cae en este caso")
    end.

Definition member {a} `{GHC.Classes.Ord a} : a -> RB a -> GHC.Types.Bool :=
  fix member arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | x, E => GHC.Types.False
           | x, T _ tl y tr =>
               if x GHC.Classes.< y : bool then member x tl else
               if x GHC.Classes.> y : bool then member x tr else
               GHC.Types.True
           | _, _ => GHC.Err.patternFailure
           end.

Definition balance {a} : RB a -> a -> RB a -> RB a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | T R a x b, y, T R c z d => T R (T B a x b) y (T B c z d)
    | T R (T R a x b) y c, z, d => T R (T B a x b) y (T B c z d)
    | T R a x (T R b y c), z, d => T R (T B a x b) y (T B c z d)
    | a, x, T R b y (T R c z d) => T R (T B a x b) y (T B c z d)
    | a, x, T R (T R b y c) z d => T R (T B a x b) y (T B c z d)
    | a, x, b => T B a x b
    end.

Definition ins {a} `{GHC.Classes.Ord a} : a -> RB a -> RB a :=
  fix ins arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | x, E => T R E x E
           | x, (T B a y b as s) =>
               if x GHC.Classes.< y : bool then balance (ins x a) y b else
               if x GHC.Classes.> y : bool then balance a y (ins x b) else
               s
           | x, (T R a y b as s) =>
               if x GHC.Classes.< y : bool then T R (ins x a) y b else
               if x GHC.Classes.> y : bool then T R a y (ins x b) else
               s
           | _, _ => GHC.Err.patternFailure
           end.

Definition insert {a} `{GHC.Classes.Ord a} : a -> RB a -> RB a :=
  fun x s =>
    match ins x s with
    | T _ a z b => T B a z b
    | _ => GHC.Err.patternFailure
    end.

(* External variables:
     bool GHC.Classes.Ord GHC.Classes.op_zg__ GHC.Classes.op_zl__
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.error GHC.Err.patternFailure
     GHC.Types.Bool GHC.Types.False GHC.Types.True
*)
