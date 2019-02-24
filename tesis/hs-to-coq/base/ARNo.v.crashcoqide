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
Hint Resolve member.


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
    
Hint Resolve balance.

Fixpoint ins {a} `{GHC.Base.Ord a} (arg_0__: a) (arg_1__: RB a):RB a :=
   match arg_0__, arg_1__ with
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
           
Hint Unfold ins.

(* cambiar el tipo de regreso a un tipo error/option ------2018*)
(* No se eta usando option porque estorba y se esta simulando la funcion total al agregar el ultimo caso*)
Definition insert {a} `{GHC.Base.Ord a} : a -> RB a -> RB a :=
  fun x s =>
    match ins x s with
    | T _ a z b => T B a z b
    | E => E
    end.

Hint Unfold insert.

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
          is_redblack (T B tl x tr) c (S n)
| error : forall r1 x r2 n, is_redblack (T R r1 x r2) R n.

Hint Constructors is_redblack.

Lemma subtreeEmpty: forall s c,is_redblack s c 0 -> s = E.
Proof.
Admitted.

Lemma subtree0: forall n c, n = 0 -> is_redblack E c n.
Proof.
Admitted.

Inductive nearly_redblack {a} `{GHC.Base.Ord a}: RB a -> nat -> Prop :=
| nrRB_r: forall tl k tr n,
         is_redblack tl B n ->
         is_redblack tr B n ->
         nearly_redblack (T R tl k tr) n
| nrRB_b: forall tl k tr n,
         is_redblack tl B n ->
         is_redblack tr B n ->
         nearly_redblack (T B tl k tr) (S n).

Lemma ins_is_redblack {a} `{GHC.Base.Ord a}:
  forall (x: a) (s:RB a) (n:nat), 
    (is_redblack s B n -> nearly_redblack (ins x s) n) /\
    (is_redblack s R n -> is_redblack (ins x s) B n).
Proof.
dependent induction s;intro n;simpl;split;intros;inversion H1;repeat constructor.
- destruct (IHs1 n); clear IHs1.
  destruct (IHs2 n); clear IHs2.
  case_eq (x GHC.Base.< a0);intros.
  -- apply nrRB_r.
     --- apply H10.
         trivial.
     --- rewrite H2 in H8.
         (* apply H8. *)
          admit.
  -- case_eq (x GHC.Base.> a0);intros.
     apply nrRB_r.
     --- admit.
     --- apply H12.
         trivial.
     --- apply nrRB_r.
         ---- admit.
         ---- admit.
- destruct (IHs1 n); clear IHs1.
  destruct (IHs2 n); clear IHs2.
  case_eq (x GHC.Base.< a0);intros.
  unfold balance.


Lemma insert_is_redblack {a} `{GHC.Base.Ord a}:
  forall (x: a) (s: RB a) (n: nat), is_redblack s R n->
                    exists n', is_redblack (insert x s) R n'.
Proof.
intros.

dependent induction H1.
- exists 1. 
unfold insert.
simpl.
apply IsRB_b; apply IsRB_leaf.
 - exists n.
(* unfold insert. *)
case_eq (x GHC.Base.< x0); intros.
-- unfold insert.
   
   rewrite H1.
   
 eapply IsRB_b.
-- 

simpl; rewrite H1.


(*
destruct s.
induction insert.
exists 0.
apply IsRB_leaf.
destruct c.
exists n.
apply error.
exists (S n).
apply IsRB_b.

*)

(*En esta se toman demasiados casos y la definicion de insert con el retorno de E en caso de error causa ruido.*)
(* intros.
exists n.
induction H.
- induction insert.
  + apply IsRB_leaf.
  + admit.
- induction (insert x (T R tl x0 tr)).
  + admit.
  + destruct c.
    * apply IsRB_r.
     admit.
     admit.
    * admit. (*Tengo la sospecha de que estos casos no se pueden*)
- induction (insert x (T B tl x0 tr)).
  + admit.
  + destruct c0.
    * admit.
    *apply IsRB_b.
      admit.
      admit.
- destruct (insert x (T R r1 x0 r2)).
  + admit.
  + destruct c.
    *apply error.
    *admit. *)

(* intros.
induction insert.
- exists 0.
  apply IsRB_leaf.
- induction c.
  + exists n.
    apply error.
  + exists (S n).
    apply IsRB_b.
    apply sameHeight with x1.
    trivial.
    trivial.
    .
    apply IsRB_b.
    destruct s.
    destruct r1.
   (*Necesito que x1 == x0, pero por alguna razon se desligan*)
  
admit.
  apply IsRB_b. *)







(* External variables:
     bool GHC.Classes.Ord GHC.Classes.op_zg__ GHC.Classes.op_zl__
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.error GHC.Err.patternFailure
     GHC.Types.Bool GHC.Types.False GHC.Types.True
*)