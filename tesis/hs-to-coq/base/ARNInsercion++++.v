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

Definition insert x s := makeBlack (ins x s).

Hint Unfold insert.

Definition isblack {a} `{GHC.Base.Ord a} (t : RB a) :=
 match t with T B _ _ _ => True | _ => False end.

Definition notblack {a} `{GHC.Base.Ord a} (t : RB a) :=
 match t with T B _ _ _ => False | _ => True end.

Definition notred {a} `{GHC.Base.Ord a} (t : RB a) :=
 match t with T R _ _ _ => False | _ => True end.



(* proofs *)

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

Lemma makeBlack_rb {a} `{GHC.Base.Ord a} n t : nearly_redblack n t -> redblack (makeBlack t).
Admitted.
Lemma makeRed_rr {a} `{GHC.Base.Ord a} t n :
 is_redblack (S n) t -> notred t -> redred_tree n (makeRed t).
Admitted.




Lemma ins_arb {a} `{GHC.Base.Ord a} (x:a) (s:RB a) (n:nat) : is_redblack n s -> nearly_redblack n (ins x s).
Proof.
induction s;simpl;repeat constructor;trivial.
destruct c.
inversion H1.
specialize (IHs1 H8).
specialize (IHs2 H9).
inversion IHs1.
inversion H10.
destruct (_GHC.Base.<_ x a0).
subst.
constructor.


simpl;trivial.
simpl;trivial.

Instance add_rb x s : redblack s -> redblack (insert x s).