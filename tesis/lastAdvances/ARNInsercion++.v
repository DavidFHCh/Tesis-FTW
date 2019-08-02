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

(* proofs *)

(* definicion inductiva que ayuda a verificar que un arbol es rojinegro al llevar un contador de la altura
negra del arbol
 *)
(* dos nodos sucesivos NO pueden ser rojos *)
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

(* definicion inductiva que sirve como auxiliar al momento de la demostracion, es un poco mas laxa con una invariante
de los arboles rojinegros, ya que permite que la raiz sea roja y que haya dos rojos a lo mas en la raiz del arbol.
 *)
Inductive nearly_redblack {a} `{GHC.Base.Ord a}: RB a -> nat -> Prop :=
| nrRB_r: forall tl k tr n,
         is_redblack tl B n ->
         is_redblack tr B n ->
         nearly_redblack (T R tl k tr) n
| nrRB_b: forall tl k tr n,
         is_redblack tl B n ->
         is_redblack tr B n ->
         nearly_redblack (T B tl k tr) (S n).

(* lema que prueba que un arbol con al menos un elemento no es vacio.
 *)
Lemma T_neq_E {a} `{GHC.Base.Ord a}:
  ∀ (c:Color) (l: RB a) (k: a) (r: RB a), T c l k r ≠ E.
Proof.
intros. intro Hx. inversion Hx.
Qed.

Hint Resolve T_neq_E.

(* Lema que prueba que la insercion en un arbol rojinegro no da como resultado un arbol vacio.
 *)
(* La demostracion es bastante sencilla pero muy repetitiva, consiste en ir destruyendo la estructura hasta caer en los casos bases
de las definiciones antes dadas, de tal manera que se pueda aplicar el lemma T_neq_E, que es a lo que siempre se llega
despues de destruir la insercion.
 *)
Lemma ins_not_E{a} `{GHC.Base.Ord a}: forall (x: a) (s: RB a), ins x s ≠ E.
Proof.
intros.
(* dependent induction s. *)
destruct s.
- simpl.
  apply T_neq_E.
- remember (ins x s1) as a1.
  remember (ins x s2) as a2.
(*   El recordar y sustituir de esta manera es lo que nos hace tener resultados de la forma del lemma T_neq_E.
 *)
  simpl.
  destruct c.
  destruct (x GHC.Base.< a0).
  apply T_neq_E.
  destruct (x GHC.Base.> a0).
  apply T_neq_E.
  apply T_neq_E.
  destruct (x GHC.Base.< a0).
  symmetry in Heqa1.
  rewrite Heqa1.
  unfold lbal;destruct a1.
  apply T_neq_E.
  destruct c.
  destruct a1_1.
  destruct a1_2.
  apply T_neq_E.
  destruct c.
  apply T_neq_E.
  apply T_neq_E.
  destruct c.
  apply T_neq_E.
  destruct a1_2.
  apply T_neq_E.
  destruct c.
  apply T_neq_E.
  apply T_neq_E.
  apply T_neq_E.
  destruct (x GHC.Base.> a0).
  symmetry in Heqa2.
  rewrite Heqa2.
  unfold rbal;destruct a2.
  apply T_neq_E.
  destruct c.
  destruct a2_1.
  destruct a2_2.
  apply T_neq_E.
  destruct c.
  apply T_neq_E.
  apply T_neq_E.
  destruct c.
  apply T_neq_E.
  destruct a2_2.
  apply T_neq_E.
  destruct c.
  apply T_neq_E.
  apply T_neq_E.
  apply T_neq_E.
  apply T_neq_E.
Qed.

Hint Resolve ins_not_E.

(* Este lemma nos dice que si tenemos un arbol _rojo_ (nodo fantasma padre de la raiz) puede ser pintado de negro sin mayor problema
 *)
Lemma is_redblack_toblack {a} `{GHC.Base.Ord a}:
  ∀ (s:RB a) (n: nat), is_redblack s R n → is_redblack s B n.
Proof.
intros.
destruct H1; auto.
Qed.

Hint Resolve is_redblack_toblack.

(* Al hacer makeB puede que la altura del arbol crezca en uno ya que la raiz puede ser roja(nearly_redblack) y
tiene que ser pintada de negro.
 *)
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

(* Intento fallido de la prueba de que la insercion es rojinegra, justo como viene en el libro de Appel.
 *)
(* Lemma ins_is_redblack_2 {a} `{GHC.Base.Ord a}:
  forall (x: a) (s:RB a) (n:nat),
    (is_redblack s B n -> nearly_redblack (ins x s) n) /\
    (is_redblack s R n -> is_redblack (ins x s) B n).
Proof.
induction s; intro n; simpl; split; intros; inversion H1;repeat constructor;auto.
destruct (_GHC.Base.<_ x a0).
destruct (IHs1 n).
destruct (IHs2 n).
unfold balance.
constructor.
eauto.
specialize (H12 H8).
trivial.
auto.
destruct (_GHC.Base.<_ a0 x).
destruct (IHs1 n).
destruct (IHs2 n).
intuition.
apply is_redblack_toblack in H7.
apply is_redblack_toblack in H8.
intuition.
remember (ins x s2) as a1.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction.
unfold balance.
constructor;auto.
constructor;auto.
destruct (IHs1 n0).
destruct (IHs2 n0).
intuition.
subst.
destruct (_GHC.Base.<_ x a0).
remember (ins x s1) as a1.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction.
unfold balance.
destruct c.
destruct a1_1.
destruct a1_2.
destruct s2.
constructor;auto.
inversion H14;subst.
constructor.

Admitted. *)

(* Pruba con una modificacion al color, lo cual solo nos deja con dos casos que son complicados de resolver, a diferencia
de la desmostracion pasada.

El estilo de la demostracion es parecida a la de ins_not_E, con la diferencia de que aqui se utiliza induccion sobre el arbol
mas el truco de recordar la operacion ins x a para poder capturar una absudurdo en el cual se pone que T c l a r = E, hay una contradiccion por cada
caso que genera la induccion sobre el arbol.

Dejando ese absurdo de lado el estilo de la demostracion sigue el camino de utilizar las definiciones inductivas para probar quelos arboles
despues de insertar elementos sigan siendo rojinegros.


 *)
Lemma isEmpty{a} `{GHC.Base.Ord a}:
 forall x s1 a1, T R E a1 E = ins x s1 -> s1 = E.
Admitted.

Lemma isZero {a} `{GHC.Base.Ord a}:
forall n0, is_redblack E B n0 -> n0 = 0.
Admitted.

Lemma ins_is_redblack_1 {a} `{GHC.Base.Ord a}:
  forall (x: a) (s:RB a) (n:nat),
    (is_redblack s B n -> nearly_redblack (ins x s) n) /\
    (is_redblack s R n -> is_redblack (ins x s) B n).
Proof.
induction s; intro n; simpl; split; intros; inversion H1;repeat constructor;auto.
-remember (ins x s1) as a1.
remember (ins x s2) as a2.
destruct (IHs1 n).
destruct (IHs2 n).
specialize (H10 H7).
specialize (H12 H8).
destruct (_GHC.Base.<_ x a0).
constructor.
trivial.
apply is_redblack_toblack.
trivial.
destruct (_GHC.Base.>_ x a0).
constructor.
apply is_redblack_toblack.
trivial.
trivial.
constructor.
apply is_redblack_toblack.
trivial.
apply is_redblack_toblack.
trivial.
-subst.
remember (ins x s1) as a1.
remember (ins x s2) as a2.
destruct (IHs1 n0).
destruct (IHs2 n0).
specialize (H2 H8).
specialize (H4 H9).
destruct (_GHC.Base.<_ x a0).
unfold lbal.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction.
destruct c.
destruct a1_1.
destruct a1_2.
constructor.
inversion H2.
admit.
(* apply isEmpty in Heqa1.
subst.
apply isZero in H8.
subst.
constructor.
trivial.
trivial. *)
trivial.
destruct c.
inversion H2.
constructor.
constructor.
trivial.
inversion H13.

(* 
apply is_redblack_toblack. *)
admit.
trivial.
destruct c.
constructor.
constructor.

3: {
subst.
destruct (IHs1 n0).
destruct (IHs2 n0).
destruct (_GHC.Base.<_ x a0).
- remember (ins x s1) as a1.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction. (* Una contradiccion *)
unfold lbal.
destruct c.
destruct a1_1.
destruct a1_2.
constructor.
constructor.
specialize (H2 H8).
apply H3.
trivial.
trivial.
destruct c.
destruct s2_1.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
apply is_redblack_toblack.
trivial.
constructor.
inversion H9.
inversion H13.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
constructor.
inversion H9.
trivial.
inversion H9.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
inversion H10.
inversion H9.
constructor.
inversion H10.
apply is_redblack_toblack.
trivial.
destruct s2_2.
constructor.
apply H3.
trivial.
inversion H9.
constructor.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
apply is_redblack_toblack.
trivial.
inversion H9.
constructor.
inversion H13.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
constructor.
apply H3.
trivial.
trivial.
destruct c.
specialize (H3 H8).
inversion H3.
constructor.
constructor.
apply is_redblack_toblack.
trivial.
inversion H13.
constructor.
inversion H13.
trivial.
destruct s2.
specialize (H3 H8).
constructor.
trivial.
trivial.
destruct c.
destruct s2_1.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
apply is_redblack_toblack.
trivial.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
inversion H10.
inversion H9.
inversion H10.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
apply is_redblack_toblack.
trivial.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
constructor.
apply H3.
trivial.
trivial.
destruct c.
specialize (H3 H8).
inversion H3.
constructor.
inversion H10.
constructor.
apply is_redblack_toblack.
trivial.
trivial.
destruct a1_2.
destruct s2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
destruct s2_1.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
auto.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
inversion H10.
inversion H9.
inversion H10.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
apply is_redblack_toblack.
trivial.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
constructor.
apply H3.
trivial.
trivial.
destruct c.
specialize (H3 H8).
constructor.
constructor.
inversion H3.
auto.
inversion H3.
inversion H13.
inversion H3.
inversion H13.
destruct s2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
destruct s2_1.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
auto.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
inversion H10.
inversion H9.
inversion H10.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
auto.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
constructor.
apply H3.
trivial.
trivial.
destruct s2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
destruct s2_1.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
auto.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
inversion H10.
inversion H9.
inversion H10.
destruct s2_2.
constructor.
apply H3.
trivial.
trivial.
destruct c.
constructor.
constructor.
apply H3.
trivial.
inversion H9.
auto.
inversion H9.
inversion H13.
constructor.
apply H3.
trivial.
trivial.
constructor.
apply H3.
trivial.
trivial.
-specialize (H5 H9).
destruct (_GHC.Base.<_ a0 x).
unfold balance.
remember (ins x s2) as a1.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction. (* Una contradiccion *)
destruct c.
destruct a1_1.
destruct a1_2.
destruct s1.
constructor.
trivial.
apply H5.
trivial.
destruct c.
destruct s1_1.
destruct s1_2.
constructor.
trivial.
apply H5.
trivial.
destruct c.
constructor.
constructor.
inversion H8.
auto.
inversion H8.
inversion H13.
constructor.
inversion H8.
inversion H13.
apply H5.
trivial.
constructor.
inversion H8.
trivial.
apply H5.
trivial.
destruct c.
constructor.
inversion H8.
inversion H10.
inversion H8.
constructor.
auto.
apply H5.
trivial.
destruct s1_2.
constructor.
inversion H8.
constructor.
trivial.
trivial.
apply H5.
trivial.
destruct c.
constructor.
constructor.
inversion H8.
auto.
inversion H8.
inversion H13.
constructor.
inversion H8.
inversion H13.
apply H5.
trivial.
constructor.
trivial.
apply H5.
trivial.
constructor.
trivial.
apply H5.
trivial.
destruct s1.
destruct c.
constructor.
auto.
inversion H5.
inversion H13.
constructor.
trivial.
trivial.
destruct c0.
destruct s1_1.
destruct s1_2.
destruct c.
constructor.
constructor.
trivial.
inversion H8.
auto.
inversion H5.
inversion H13.
inversion H5.
constructor.
constructor.
trivial.
trivial.
trivial.
destruct c0.
inversion H8.
inversion H13.
destruct c.
inversion H8.
constructor.
constructor.
constructor.
trivial.
trivial.
auto.
inversion H5.
inversion H19.
inversion H8.
constructor.
trivial.
trivial.
destruct c0.
inversion H8.
inversion H5.
constructor.
inversion H10.
constructor.
auto.
constructor;trivial.
inversion H5.
inversion H8.
subst.
destruct s1_2.
destruct c.
constructor.
constructor.
constructor.
trivial.
trivial.
auto.
inversion H13.
constructor.
constructor.
trivial.
trivial.
auto.
destruct c0.
constructor.
constructor.
auto.
inversion H19.
constructor.
inversion H19.
constructor;auto.
destruct c.
constructor.
constructor.
constructor;auto.
auto.
inversion H13.
constructor;auto.
inversion H5.
subst.
destruct c.
constructor;auto.
inversion H13.
constructor;auto.
inversion H5.
subst.
destruct s1.
destruct c.
constructor;auto.
inversion H10.
inversion H10.
destruct a1_2.
constructor;auto.
destruct c.
constructor;auto.
inversion H13.
constructor;auto.
destruct c0.
destruct s1_1.
destruct s1_2.
destruct c.
inversion H10.
destruct a1_2.
constructor;auto.
destruct c.
inversion H13.
constructor;auto.
destruct c0.
inversion H8.
inversion H15.
destruct c.
inversion H8.
inversion H10.
destruct a1_2.
constructor;auto.
destruct c.
inversion H13.
constructor;auto.
destruct c0.
inversion H8.
inversion H11.
destruct s1_2.
destruct c.
inversion H8.
inversion H10.
destruct a1_2.
constructor;auto.
destruct c.
inversion H8.
inversion H13.
constructor;auto.
destruct c0.
inversion H8.
inversion H15.
destruct c.
inversion H8.
inversion H10.
destruct a1_2.
constructor;auto.
destruct c.
inversion H8.
inversion H13.
constructor;auto.
destruct c.
inversion H10.
destruct a1_2.
constructor;auto.
destruct c.
inversion H13.
constructor;auto.
destruct s1.
constructor;auto.
destruct c.
destruct s1_1.
destruct s1_2.
constructor;auto.
destruct c.
inversion H8.
inversion H13.
constructor;auto.
destruct c.
inversion H8.
inversion H10.
destruct s1_2.
constructor;auto.
destruct c.
inversion H8.
inversion H13.
constructor;auto.
constructor;auto.
constructor;auto.
}
1:{subst.
destruct (IHs1 n0).
destruct (IHs2 n0).
destruct (_GHC.Base.<_ x a0).
specialize (H3 H8).
unfold balance.
remember (ins x s1) as a1.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction. (* Una contradiccion *)
inversion H3.
subst.
destruct a1_1.
destruct a1_2.
destruct s2.
constructor;auto.
destruct c.
destruct s2_1.
destruct s2_2.
constructor;auto.
inversion H9.
destruct c.
constructor;auto.
inversion H15.
constructor;auto.
inversion H9;subst.
destruct c.
inversion H10.
destruct s2_2.
constructor;auto.
destruct c.
constructor.
constructor;auto.
inversion H15.
constructor;auto.
constructor;auto.
destruct c.
constructor.
inversion H14.
inversion H14.
destruct s2.
constructor;auto.
destruct c.
destruct s2_1.
destruct s2_2.
constructor;auto.
destruct c.
constructor;auto.
inversion H9.
inversion H15.
inversion H9.
constructor;auto.
inversion H9.
subst.
destruct c.
constructor.
inversion H10.
inversion H10.
destruct s2_2.
constructor;auto.
destruct c.
constructor;auto.
inversion H15.
constructor;auto.
constructor;auto.
destruct c.
constructor;auto.
inversion H13.
destruct a1_2.
destruct s2.
constructor;auto.
destruct c.
destruct s2_1.
destruct s2_2.
constructor;auto.
inversion H9.
subst.
destruct c.
constructor;auto.
inversion H15.
constructor;auto.
inversion H9.
subst.
destruct c.
inversion H10.
destruct s2_2.
constructor;auto.
destruct c.
constructor;auto.
inversion H15.
constructor;auto.
constructor;auto.
destruct c.
inversion H14.
destruct s2.
constructor;auto.
destruct c.
destruct s2_1.
destruct s2_2.
constructor;auto.
inversion H9.
subst.
destruct c.
constructor;auto.
inversion H15.
constructor;auto.
inversion H9.
subst.
destruct c.
constructor.
inversion H10.
inversion H10.
destruct s2_2.
constructor;auto.
destruct c.
constructor;auto.
inversion H15.
constructor;auto.
constructor;auto.
subst.
destruct s2.
constructor;auto.
destruct c.
destruct s2_1.
destruct s2_2.
constructor;auto.
inversion H9.
subst.
destruct c.
constructor;auto.
inversion H13.
constructor;auto.
inversion H9;subst.
destruct c.
inversion H10.
destruct s2_2.
constructor;auto.
destruct c.
constructor;auto.
inversion H13.
constructor;auto.
constructor;auto.


-destruct (_GHC.Base.<_ a0 x).
specialize (H5 H9).
unfold balance.
remember (ins x s2) as a1.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction. (* Una contradiccion *)
inversion H5.
subst.
destruct a1_1.
destruct a1_2.
destruct s1.
constructor;auto.
destruct c.
destruct s1_1.
destruct s1_2.
constructor;auto.
inversion H8.
subst.
destruct c.
inversion H15.
constructor;auto.
inversion H8;subst.
destruct c.
inversion H10.
destruct s1_2.
constructor;auto.
destruct c.
constructor.
constructor;auto.
inversion H15.
inversion H15.
constructor;auto.
constructor;auto.
destruct s1.
destruct c.
inversion H14.
constructor;auto.
destruct c0.
destruct s1_1.
destruct s1_2.
destruct c.
constructor;auto.
inversion H8.
inversion H14.
constructor;auto.
inversion H8.
subst.
destruct c0.
constructor.
inversion H15.
inversion H15.
destruct c.
constructor;auto.
inversion H14.
constructor;auto.
inversion H8.
subst.
destruct c0.
constructor;auto.
inversion H10.
destruct s1_2.
destruct c.
constructor;auto.
inversion H14.
constructor;auto.
destruct c0.
inversion H15.
destruct c.
constructor;auto.
inversion H14.
constructor;auto.
destruct c.
constructor;auto.
inversion H14.
constructor;auto.
destruct s1.
destruct c.
inversion H13.
destruct a1_2.
constructor;auto.
destruct c.
constructor;auto.
inversion H14.
constructor;auto.
destruct c0.
destruct s1_1.
destruct s1_2.
destruct c.
inversion H13.
destruct a1_2.
constructor;auto.
destruct c.
inversion H14.
constructor;auto.
inversion H8.
subst.
destruct c0.
inversion H15.
destruct c.
inversion H13.
destruct a1_2.
constructor;auto.
destruct c.
inversion H14.
constructor;auto.
inversion H8;subst.
destruct c0.
inversion H10.
destruct s1_2.
destruct c.
inversion H13.
destruct a1_2.
constructor;auto.
destruct c.
inversion H14.
constructor;auto.
destruct c0.
inversion H15.
destruct c.
inversion H13.
destruct a1_2.
constructor;auto.
destruct c.
inversion H14.
constructor;auto.
destruct c.
inversion H13.
destruct a1_2.
constructor;auto.
destruct c.
inversion H14.
constructor;auto.
subst.
destruct s1.
constructor;auto.
destruct c.
destruct s1_1.
destruct s1_2.
constructor;auto.
inversion H8;subst.
destruct c.
inversion H13.
constructor;auto.
inversion H8;subst.
destruct c.
inversion H10.
destruct s1_2.
constructor;auto.
destruct c.
inversion H13.
constructor;auto.
constructor;auto.
constructor;auto.
}
1:{
destruct (IHs1 n).
destruct (IHs2 n).
destruct (_GHC.Base.<_ x a0).
subst.
specialize (H9 H7).
apply is_redblack_toblack in H7.
specialize (H10 H7).
unfold balance.
constructor;auto.
remember (ins x s1) as a1.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction. (* Una contradiccion *)
inversion H10;subst.
inversion H9;subst.
intuition.
admit.  (* Caso en que se tiene un arbol rojo y se quiere probar un arbol negro, contrario al lemma make_redblack_toblack.*)
constructor;auto.
destruct (_GHC.Base.<_ a0 x).
unfold balance.
constructor;auto.
remember (ins x s2) as a1.
destruct a1.
symmetry in Heqa1;apply ins_not_E in Heqa1;contradiction. (* Una contradiccion *)
intuition.
apply is_redblack_toblack in H8.
intuition.
inversion H11;subst.
inversion H9;subst.
admit. (* Caso en que se tiene un arbol rojo y se quiere probar un arbol negro, contrario al lemma make_redblack_toblack.*)
constructor;auto.
constructor;auto.
}
Admitted.



(* Teorema principal *)

Lemma insert_is_redblack {a} `{GHC.Base.Ord a}:
  forall (x: a) (s: RB a) (n: nat), is_redblack s R n->
                    exists n', is_redblack (insert x s) R n'.
Proof.
intros.
unfold insert.
apply makeblack_fiddle with n.
apply ins_is_redblack_1.
intuition.
Qed.
