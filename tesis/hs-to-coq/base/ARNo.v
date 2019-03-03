(* Default settings (from HsToCoq.Coq.Preamble) *)

(* Archivo traducido de ARNo.hs, se intenta hacer la prueba. *)
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

Definition makeBlack {a} `{GHC.Base.Ord a} (t: RB a) := 
  match t with 
  | E => E
  | T _ a x b => T B a x b
  end.
Hint Unfold makeBlack.

(* cambiar el tipo de regreso a un tipo error/option ------2018*)
(* No se eta usando option porque estorba y se esta simulando la funcion total al agregar el ultimo caso*)
Definition insert{a} `{GHC.Base.Ord a} (x:a) (s: RB a):= makeBlack (ins x s).

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
          is_redblack (T B tl x tr) c (S n).

Hint Constructors is_redblack.

Inductive nearly_redblack {a} `{GHC.Base.Ord a}: RB a -> nat -> Prop :=
| nrRB_r: forall tl k tr n,
         is_redblack tl B n ->
         is_redblack tr B n ->
         nearly_redblack (T R tl k tr) n
| nrRB_b: forall tl k tr n,
         is_redblack tl B n ->
         is_redblack tr B n ->
         nearly_redblack (T B tl k tr) (S n).

Lemma T_neq_E {a} `{GHC.Base.Ord a}:
  ∀ (c:Color) (l: RB a) (k: a) (r: RB a), T c l k r ≠ E.
Proof.
intros. intro Hx. inversion Hx.
Qed.

Hint Resolve T_neq_E.

Lemma ins_not_E{a} `{GHC.Base.Ord a}: forall (x: a) (s: RB a), ins x s ≠ E.
Proof.
intros.
(* dependent induction s. *)
destruct s.
- simpl.
  apply T_neq_E.
- remember (ins x s1) as a1.
  remember (ins x s2) as a2.
  simpl.
  destruct c;case_eq (x GHC.Base.> a0);case_eq (x GHC.Base.< a0);intros; eauto.
(*   -- rewrite <- Heqa1.
     apply T_neq_E.
  -- rewrite <- Heqa2.
     apply T_neq_E.
  -- apply T_neq_E.
  -- apply T_neq_E.
 *)  -- rewrite <- Heqa1.
     unfold balance.
     destruct a1.
     --- destruct s2; eauto.
(*          ---- apply T_neq_E. *)
         ---- destruct c.
              ----- destruct s2_2; destruct s2_1; eauto.
(*                     ------ apply T_neq_E. *)
                       ------ destruct c;apply T_neq_E.
(*                     ------ destruct s2_1. *)
                           ------ destruct c; apply T_neq_E.
                           ------ destruct c0; destruct c; apply T_neq_E.
              ----- apply T_neq_E.
     --- destruct c.
              ----- destruct a1_1.
                    ------ destruct a1_2.
                           ------- destruct s2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                           ------- destruct c; destruct s2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E. 
                   ------ destruct c; destruct a1_2.
                           ------- destruct s2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E. 
                           ------- destruct c; destruct s2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                           ------- destruct s2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                           ------- destruct c; destruct s2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
              ----- destruct s2.
                    ------ apply T_neq_E.
                    ------ destruct c.
                           ------- destruct s2_1.
                                   -------- destruct s2_2.
                                            --------- apply T_neq_E.
                                            --------- destruct c; apply T_neq_E.
                                   -------- destruct c; destruct s2_2.
                                            --------- apply T_neq_E.
                                            --------- destruct c; apply T_neq_E.
                                            --------- apply T_neq_E.
                                            --------- destruct c; apply T_neq_E.
                          ------- apply T_neq_E.
  -- rewrite <- Heqa2.
     unfold balance.
     destruct s1.
     --- destruct a2; eauto.
(*          ---- apply T_neq_E. *)
         ---- destruct c.
              ----- destruct a2_1.
                    ------ destruct a2_2.
                           ------- apply T_neq_E.
                           ------- destruct c;apply T_neq_E.
                    ------ destruct c.
                           ------- destruct a2_2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                           ------- destruct a2_2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
              ----- apply T_neq_E.
     --- destruct c.
         ---- destruct s1_1.
              ----- destruct s1_2.
                    ------ destruct a2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                    ------ destruct c; destruct a2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
              ----- destruct c; destruct s1_2.
                    ------ destruct a2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E. 
                    ------ destruct c; destruct a2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                    ------ destruct a2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                    ------ destruct c; destruct a2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
         ---- destruct a2.
              ----- apply T_neq_E.
              ----- destruct c.
                    ------ destruct a2_1.
                           ------- destruct a2_2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                           ------- destruct c; destruct a2_2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                    ------ apply T_neq_E.
  -- rewrite <- Heqa1.
     unfold balance.
     destruct a1.
     --- destruct s2.
         ---- apply T_neq_E.
         ---- destruct c.
              ----- destruct s2_2.
                    ------ destruct s2_1.
                           ------- apply T_neq_E.
                           ------- destruct c;apply T_neq_E.
                    ------ destruct s2_1.
                           ------- destruct c; apply T_neq_E.
                           ------- destruct c0; destruct c; apply T_neq_E.
              ----- apply T_neq_E.
     --- destruct c.
         ---- destruct a1_1.
              ----- destruct a1_2.
                    ------ destruct s2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                    ------ destruct c; destruct s2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E. 
              ----- destruct c; destruct a1_2.
                    ------ destruct s2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                    ------ destruct c; destruct s2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                    ------ destruct s2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                    ------ destruct c; destruct s2.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
                           ------- apply T_neq_E.
                           ------- destruct c; apply T_neq_E.
         ---- destruct s2.
              ----- apply T_neq_E.
              ----- destruct c.
                    ------ destruct s2_1.
                           ------- destruct s2_2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                           ------- destruct c; destruct s2_2.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                                   -------- apply T_neq_E.
                                   -------- destruct c; apply T_neq_E.
                   ------ apply T_neq_E.
(*   -- apply T_neq_E. *)
Qed.

Hint Resolve ins_not_E.

Lemma is_redblack_toblack {a} `{GHC.Base.Ord a}:
  ∀ (s:RB a) (n: nat), is_redblack s R n → is_redblack s B n.
Proof.
intros.
destruct H1; auto.
(* - constructor.
- constructor;trivial.
- constructor;trivial.
 *)
Qed.

Hint Resolve is_redblack_toblack.


Lemma makeblack_fiddle {a} `{GHC.Base.Ord a}:
  ∀ (s: RB a)(n : nat), is_redblack s B n → 
            ∃ (n:nat), is_redblack (makeBlack s) R n.
Proof.
intros.
dependent induction H1.
(* destruct H1. *)
- exists 0.
  simpl.
  constructor.
- simpl.
  exists (S n).
  constructor; apply is_redblack_toblack;trivial.
- exists (S n).
  constructor;trivial.
Qed.

Hint Resolve makeblack_fiddle.

Lemma ins_is_redblack {a} `{GHC.Base.Ord a}:
  forall (x: a) (s:RB a) (n:nat), 
    (is_redblack s B n -> nearly_redblack (ins x s) n) /\
    (is_redblack s R n -> is_redblack (ins x s) B n).
Proof.
dependent induction s; intro n; split; intros; inversion H1; repeat constructor; auto.

destruct (IHs1 n); destruct (IHs2 n); case_eq (x GHC.Base.< a0); intro Hltxa0.
simpl; rewrite Hltxa0. 

apply nrRB_r. apply H10; assumption. 
apply is_redblack_toblack in H8; assumption.

simpl. rewrite Hltxa0. 
case_eq (x GHC.Base.> a0); intro Hgtxa0.
apply nrRB_r. apply is_redblack_toblack in H7; assumption.
apply H12; assumption.
apply nrRB_r. apply is_redblack_toblack in H7; assumption. 
apply is_redblack_toblack in H8; assumption.

destruct (IHs1 n0); destruct (IHs2 n0); case_eq (x GHC.Base.< a0); intro Hltxa0.
- simpl; rewrite Hltxa0.
  remember (ins x s1) as a1.
  destruct a1.
-- symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction.
-- specialize (H10 H8).
   destruct c1.
---- destruct a1_1.
----- destruct a1_2.
------ destruct s2.
------- simpl. constructor;trivial.
        inversion H10.
Admitted.
(*   
- simpl;case_eq (x GHC.Base.< a0);intros.
-- remember (ins x s1) as a1.
   unfold balance.
   destruct a1.
--- symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction.
--- admit. (* destruct c1.
---- destruct a1_1.
----- destruct a1_2.
------ destruct s2.
------- repeat constructor. *)
-- case_eq (x GHC.Base.> a0);intros.
   remember (ins x s2) as a2.
   destruct a2.
--- symmetry in Heqa2;apply ins_not_E in Heqa2;contradiction.
--- admit.
--- repeat constructor; eauto.
- simpl.

-- simpl.
--- destruct s2.
    repeat constructor;trivial.

 *)




(* Teorema principal *)

Lemma insert_is_redblack {a} `{GHC.Base.Ord a}:
  forall (x: a) (s: RB a) (n: nat), is_redblack s R n->
                    exists n', is_redblack (insert x s) R n'.
Proof.
intros.
unfold insert.
apply makeblack_fiddle with n.
apply ins_is_redblack.
trivial.
Qed.



(* External variables:
     bool GHC.Classes.Ord GHC.Classes.op_zg__ GHC.Classes.op_zl__
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.error GHC.Err.patternFailure
     GHC.Types.Bool GHC.Types.False GHC.Types.True
*)