(* Este archivo contiene todas las definiciones y teoremas necesarios para probar que la insercion de elementos
a un arbol rojinegro, da como resultado un arbol rojinegro *)

(* Archivo traducido de ARNo.hs, se uso hs-to-coq para traducir pero las definiciones no pasaron inmediatamente despuesdes
de hacer la traduccion, varias se tuvieron que mejorar para hacer la demostracion mas sencilla, otras como balance se reescribieron completamente

Se puede decir que la traduccion que dio la herramienta se uso como guia para poder obtener un script que funcionara medianamente bien para lo que se
busca hacer.

Se entiende que esta es una estrucutura un tanto compleja y que la herramienta todavia esta en su infancia y no genere
codigo 100% proof ready *)
Generalizable All Variables.

Require Export Utf8_core.
Require Import Coq.Classes.RelationClasses.
Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Program.Equality.
Require MSetGenTree.
Require Import Bool List BinPos Pnat Setoid SetoidList PeanoNat.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Import ARNDefiniciones.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Err.
Require GHC.Types.
Import GHC.Base.Notations.

Fixpoint ins {a} `{GHC.Base.Ord a} (x:a) (s:RB a) :=
 match s with
 | E => T R E x E
 | T c l y r =>
    if x GHC.Base.< y : bool then 
      match c with
       | R => T R (ins x l) y r
       | B => lbal (ins x l) y r
      end
    else 
    if x GHC.Base.> y : bool then 
      match c with
       | R => T R l y (ins x r)
       | B => rbal l y (ins x r)
      end
    else s
 end.

Hint Unfold ins.

Definition insert {a} `{GHC.Base.Ord a} (x:a) (s:RB a) := makeBlack (ins x s).

Hint Unfold insert.



(** un fold para arboles rojinegros cuando el arbol tiene raiz roja *)
Definition rcase{a} `{GHC.Base.Ord a} {A} f g (t: RB a) : A :=
 match t with
 | T R a x b => f a x b
 | _ => g t
 end.


(** case analysis si es rojo aplica la primer funcion sino aplica la segunda *)
Definition ifred {a} `{GHC.Base.Ord a} (s : RB a) (A B : Prop) := 
rcase (fun _ _ _ => A) (fun _ => B) s.

(* Proofs!!
 *)
Lemma ifred_notred {a} `{GHC.Base.Ord a} (s : RB a) (A B : Prop) :
 notred s -> (ifred s A B <-> B).
Proof.
induction s;intros;split;intros;trivial;simpl in H1;destruct c.
contradiction H1.
simpl in H2;trivial.
contradiction H1.
simpl in H2;trivial.
Qed.

Lemma ifred_or {a} `{GHC.Base.Ord a} (s : RB a) (A B : Prop) :
ifred s A B -> A \/ B.
Proof.
induction s;simpl.
intro;right;trivial.
destruct c;intro.
left;trivial.
right;trivial.
Qed.


(** insert de un termino en un redblacktree depende del color de la raiz:
si es rojo da un arbol rojo-rojo
sino da uno rojinegro *)
Lemma ins_rr_rb {a} `{GHC.Base.Ord a} (x:a) (s: RB a) (n : nat) :
is_redblack n s -> ifred s (redred_tree n (ins x s)) (is_redblack n (ins x s)).
Proof.
intro.
induction H1.
- simpl.
constructor;simpl;trivial.
- simpl.
destruct (x GHC.Base.< k).
rewrite ifred_notred in IHis_redblack1.
constructor;trivial.
trivial.
destruct (x GHC.Base.> k).
rewrite ifred_notred in IHis_redblack2.
constructor;trivial.
trivial.
constructor;trivial.
(* induction 1. *)
-
rewrite ifred_notred.
simpl.
destruct (x GHC.Base.< k).
3: simpl; trivial.
--
apply ifred_or in IHis_redblack1.
intuition.
apply lbal_rb.
2: assumption.
constructor 2; assumption.
apply lbal_rb; [constructor; assumption | assumption].
--
destruct (x GHC.Base.> k).
apply ifred_or in IHis_redblack2.
intuition.
apply rbal_rb.
assumption.
constructor 2;assumption.
apply rbal_rb; [assumption | constructor; assumption].
constructor;assumption.
Qed.


Lemma makeBlack_rb {a} `{GHC.Base.Ord a} n t : 
nearly_redblack n t -> redblack (makeBlack t).
Proof.
destruct t.
exists 0.
simpl;trivial.
destruct 1.
inversion H1.
exists (S n).
simpl.
constructor.
exact H9.
exact H10.
exists (S n0).
simpl.
constructor.
exact H5.
exact H8.
exists (S n).
simpl.
inversion H1.
constructor.
exact H4.
exact H7.
Qed.

Lemma makeRed_rr {a} `{GHC.Base.Ord a} t n :
 is_redblack (S n) t -> notred t -> redred_tree n (makeRed t).
Proof.
destruct t.
inversion 1.
inversion 1.
simpl;contradiction.
intro.
constructor.
exact H5.
exact H8.
Qed.

Lemma ins_arb {a} `{GHC.Base.Ord a} (x:a) (s:RB a) (n:nat) : 
is_redblack n s -> nearly_redblack n (ins x s).
Proof.
intros.
apply (ins_rr_rb x) in H1.
apply ifred_or in H1.
destruct H1.
constructor 2.
exact H1.
constructor.
exact H1.
Qed.

Instance add_rb {a} `{GHC.Base.Ord a} (x:a) (s: RB a) : redblack s -> redblack (insert x s).
Proof.
intros (n,H1).
unfold insert.
apply (makeBlack_rb n).
apply ins_arb.
exact H1.
Qed.

