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
Require GHC.Err.
Require GHC.Types.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Color : Type := R : Color |  B : Color.

Inductive RB a : Type := E : RB a |  T : Color -> (RB a) -> a -> (RB a) -> RB a.

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

Definition ins {a} `{GHC.Base.Ord a} : a -> RB a -> RB a :=
  fix ins arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | x, E => T R E x E
           | x, (T B a y b as s) =>
               if x GHC.Base.< y : bool then balance (ins x a) y b else
               if x GHC.Base.> y : bool then balance a y (ins x b) else
               s
           | x, (T R a y b as s) =>
               if x GHC.Base.< y : bool then T R (ins x a) y b else
               if x GHC.Base.> y : bool then T R a y (ins x b) else
               s
           end.


(* cambiar el tipo de regreso a un tipo error/option*)
Definition insert {a} `{GHC.Base.Ord a} : a -> RB a -> option(RB a) :=
  fun x s =>
    match ins x s with
    | T _ a z b => Some(T B a z b)
    | _ => None
    end.



(* proofs *)

Inductive is_redblack {a} `{GHC.Base.Ord a} : option(RB a) -> Color -> nat -> Prop :=
 | IsRB_leaf: forall c, is_redblack (Some(E)) c 0
 | IsRB_r: forall tl x tr n,
          is_redblack (Some(tl)) R n ->
          is_redblack (Some(tr)) R n ->
          is_redblack (Some(T R tl x tr)) B n
 | IsRB_b: forall c tl x tr n,
          is_redblack (Some(tl)) B n ->
          is_redblack (Some(tr)) B n ->
          is_redblack (Some(T B tl x tr)) c (S n).

Lemma insert_is_redblack:
  forall x s n, is_redblack (Some(s)) R n->
                    exists n', is_redblack (insert x s) R n'.
Proof.
Admitted.



(* External variables:
     bool GHC.Classes.Ord GHC.Classes.op_zg__ GHC.Classes.op_zl__
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.error GHC.Err.patternFailure
     GHC.Types.Bool GHC.Types.False GHC.Types.True
*)
