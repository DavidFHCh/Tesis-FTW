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

Inductive RB a : Type := E : RB a |  T : Color -> (RB a) -> a -> (RB a) -> RB a.

Arguments E {_}.

Arguments T {_} _ _ _ _.

Instance Default__Color : GHC.Err.Default Color := GHC.Err.Build_Default _ R.
(* Converted value declarations: *)

Definition member {a} `{GHC.Classes.Ord a} : a -> RB a -> GHC.Types.Bool :=
  fix member arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | x, E => GHC.Types.False
           | x, T _ tl y tr =>
               if x GHC.Classes.< y : bool then member x tl else
               if x GHC.Classes.> y : bool then member x tr else
               GHC.Types.True
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

Definition insert {a} `{GHC.Classes.Ord a} : a -> RB a -> RB a :=
  fun x s =>
    let fix ins arg_0__
              := match arg_0__ with
                 | E => T R E x E
                 | (T B a y b as s) =>
                     if x GHC.Classes.< y : bool then balance (ins a) y b else
                     if x GHC.Classes.> y : bool then balance a y (ins b) else
                     s
                 | (T R a y b as s) =>
                     if x GHC.Classes.< y : bool then T R (ins a) y b else
                     if x GHC.Classes.> y : bool then T R a y (ins b) else
                     s
                 end in
    match ins s with
    | T _ a z b => T B a z b
    | _ => GHC.Err.patternFailure
    end.

(* External variables:
     bool GHC.Classes.Ord GHC.Classes.op_zg__ GHC.Classes.op_zl__
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.patternFailure GHC.Types.Bool
     GHC.Types.False GHC.Types.True
*)
