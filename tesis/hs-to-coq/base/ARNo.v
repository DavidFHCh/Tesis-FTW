(* Default settings (from HsToCoq.Coq.Preamble) *)

(* Archivo traducido de ARNo.hs, se intenta hacer la prueba. *)
Generalizable All Variables.

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


(* cambiar el tipo de regreso a un tipo error/option ------2018*)
(* No se eta usando option porque estorba y se esta simulando la funcion total al agregar el ultimo caso*)
Definition insert {a} `{GHC.Base.Ord a} : a -> RB a -> RB a :=
  fun x s =>
    match ins x s with
    | T _ a z b => T B a z b
    | _ => E
    end.


(* proofs *)

Inductive is_redblack {a} `{GHC.Base.Ord a} : RB a -> Color -> nat -> Prop :=
 | IsRB_leaf: forall c, is_redblack E c 0
 | IsRB_r: forall tl x tr n,
          is_redblack tl R n ->
          is_redblack tr R n ->
          is_redblack (T R tl x tr) B n
 | IsRB_b: forall c tl x tr n,
          is_redblack tl B n ->
          is_redblack tr B n ->
          is_redblack (T B tl x tr) c (S n).



Lemma insert_is_redblack:
  forall x s n, is_redblack s R n->
                    exists n', is_redblack (insert x s) R n'.
Proof.
intros.
induction insert.
- exists 0.
  apply IsRB_leaf.
- inversion IHr1; inversion IHr2. (*Necesito que x1 == x0, pero por alguna razon se desligan*)
  exists (S x0).
admit.
  apply IsRB_b.







(* External variables:
     bool GHC.Classes.Ord GHC.Classes.op_zg__ GHC.Classes.op_zl__
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.error GHC.Err.patternFailure
     GHC.Types.Bool GHC.Types.False GHC.Types.True
*)