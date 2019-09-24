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

Definition isblack {a} `{GHC.Base.Ord a} (t : RB a) :=
 match t with T B _ _ _ => True | _ => False end.

Definition notblack {a} `{GHC.Base.Ord a} (t : RB a) :=
 match t with T B _ _ _ => False | _ => True end.

Definition notred {a} `{GHC.Base.Ord a} (t : RB a) :=
 match t with T R _ _ _ => False | _ => True end.


(* definicion inductiva que ayuda a verificar que un arbol es rojinegro al llevar un contador de la altura
negra del arbol
 *)
(* dos nodos sucesivos NO pueden ser rojos *)
Inductive is_redblack {a} `{GHC.Base.Ord a} : nat -> RB a -> Prop :=
 | RB_Leaf : is_redblack 0 E
 | RB_R n l k r :
   notred l -> notred r -> is_redblack n l -> is_redblack n r -> is_redblack n (T R l k r)
 | RB_B n l k r : is_redblack n l -> is_redblack n r -> is_redblack (S n) (T B l k r).

Hint Constructors is_redblack.

Inductive redred_tree {a} `{GHC.Base.Ord a} (n:nat) : RB a -> Prop :=
 | RR_Rd l k r : is_redblack n l -> is_redblack n r -> redred_tree n (T R l k r).



(* definicion inductiva que sirve como auxiliar al momento de la demostracion, es un poco mas laxa con una invariante
de los arboles rojinegros, ya que permite que la raiz sea roja y que haya dos rojos a lo mas en la raiz del arbol.
 *)
Inductive nearly_redblack {a} `{GHC.Base.Ord a} (n:nat)(t:RB a) : Prop :=
 | ARB_RB : is_redblack n t -> nearly_redblack n t
 | ARB_RR : redred_tree n t -> nearly_redblack n t.

Class redblack {a} `{GHC.Base.Ord a} (t:RB a) := RedBlack : exists d, is_redblack d t.


Lemma lbal_rb {a} `{GHC.Base.Ord a} (n:nat) (l:RB a) (k:a) (r:RB a) :
 nearly_redblack n l -> is_redblack n r -> is_redblack (S n) (lbal l k r).
Proof.
intros.
destruct l.
simpl.
constructor.
inversion H1.
trivial.
inversion H3.
trivial.
simpl.
destruct c.
destruct l1.
destruct l2.
constructor;trivial.
inversion H1.
trivial.
inversion H3.
constructor;simpl;trivial.
destruct c.
constructor;simpl;trivial.
inversion H1.
inversion H3.
subst.
constructor;trivial.
inversion H11.
trivial.
inversion H3.
constructor;trivial.
inversion H8.
trivial.
inversion H1.
inversion H3.
inversion H9.
inversion H3.
inversion H8.
constructor;trivial.
inversion H1.
inversion H3.
constructor;trivial.
constructor;trivial.
inversion H3.
constructor;simpl;trivial.
destruct c.
inversion H1.
inversion H3.
subst.
constructor;simpl;trivial.
inversion H10.
constructor;trivial.
constructor;trivial.
inversion H3.
constructor;simpl;trivial.
inversion H6.
constructor;trivial.
constructor;trivial.
destruct l2.
inversion H1.
inversion H3.
constructor;trivial.
constructor;trivial.
inversion H3.
inversion H6.
constructor;simpl;trivial.
constructor;trivial.
subst;trivial.
destruct c.
inversion H1.
inversion H3.
constructor;simpl;trivial.
constructor;trivial.
inversion H11;trivial.
constructor.
inversion H11;trivial.
trivial.
inversion H3.
constructor;simpl;trivial.
constructor;trivial.
inversion H8;trivial.
constructor.
inversion H8;trivial.
trivial.
inversion H1.
inversion H3.
constructor;simpl;trivial.
constructor;trivial.
inversion H3.
constructor;simpl;trivial.
constructor;trivial.
inversion H1.
trivial.
inversion H3.
Qed.

Lemma rbal_rb {a} `{GHC.Base.Ord a} (n:nat) (l:RB a) (k:a) (r:RB a) :
 is_redblack n l -> nearly_redblack n r -> is_redblack (S n) (rbal l k r).
Proof.
intros.
destruct r.
simpl.
constructor.
trivial.
inversion H2.
trivial.
inversion H3.
simpl.
destruct c.
destruct r1.
destruct r2.
constructor.
exact H1.
inversion H2.
exact H3.
inversion H3.
constructor;simpl;trivial.
destruct c.
constructor;simpl;trivial.
inversion H2.
constructor.
exact H1.
inversion H3.
exact H10.
constructor.
exact H1.
inversion H3.
exact H6.
inversion H2.
inversion H3.
constructor.
inversion H11.
exact H18.
inversion H11.
exact H19.
inversion H3.
constructor.
inversion H8.
exact H15.
inversion H8.
exact H16.
inversion H2.
constructor.
exact H1.
exact H3.
constructor.
exact H1.
inversion H3.
constructor.
simpl;trivial.
simpl;trivial.
exact H6.
exact H8.
destruct c.
inversion H2.
constructor.
simpl;trivial.
simpl;trivial.
inversion H3.
constructor.
exact H1.
inversion H10.
exact H18.
constructor.
inversion H3.
inversion H10.
exact H19.
inversion H3.
exact H11.
inversion H3.
constructor.
simpl;trivial.
simpl;trivial.
constructor.
exact H1.
inversion H6.
exact H15.
constructor.
inversion H6.
exact H16.
exact H8.
destruct r2.
inversion H2.
constructor.
exact H1.
exact H3.
inversion H3.
constructor;simpl;trivial.
constructor;simpl;trivial.
destruct c.
inversion H2.
inversion H3.
constructor;simpl;trivial.
constructor.
exact H1.
exact H10.
constructor.
inversion H11.
exact H18.
inversion H11.
exact H19.
inversion H3.
constructor.
constructor;simpl;trivial.
constructor;simpl;trivial.
constructor.
exact H1.
exact H6.
inversion H8.
constructor.
exact H15.
exact H16.
inversion H2.
inversion H3.
constructor;simpl;trivial.
inversion H3.
constructor.
exact H1.
constructor.
constructor;simpl;trivial.
constructor;simpl;trivial.
exact H6.
exact H8.
inversion H2.
constructor.
exact H1.
exact H3.
inversion H3.
Qed.