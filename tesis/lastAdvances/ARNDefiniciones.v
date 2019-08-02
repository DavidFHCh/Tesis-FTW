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

(* Pinta de rojo la raiz de un arbol
 *)
Definition makeBlack {a} `{GHC.Base.Ord a} (t:RB a) :=
 match t with
 | E => E
 | T _ a x b => T B a x b
 end.

Hint Unfold makeBlack.

Definition makeRed {a} `{GHC.Base.Ord a} (t:RB a) :=
 match t with
 | E => E
 | T _ a x b => T R a x b
 end.

Hint Unfold makeRed.

Definition lbal {a} `{GHC.Base.Ord a} (l:RB a) (k:a) (r:RB a) :=
 match l with
 | T R (T R a x b) y c => T R (T B a x b) y (T B c k r)
 | T R a x (T R b y c) => T R (T B a x b) y (T B c k r)
 | _ => T B l k r
 end.

Hint Resolve lbal.

Definition rbal {a} `{GHC.Base.Ord a} (l:RB a) (k:a) (r:RB a) :=
 match r with
 | T R (T R b y c) z d => T R (T B l k b) y (T B c z d)
 | T R b y (T R c z d) => T R (T B l k b) y (T B c z d)
 | _ => T B l k r
 end.

Hint Resolve rbal.