(** * Insercion a arboles rojinegros. 
Este archivo, junto con ARNDefiniciones.v) contiene definiciones, lemas y teoremas necesarios para probar formalmente que la insercion en arboles rojinegros
es correcta.

Se utilizan elementos obtenidos de la traduccion de las bibliotecas de Haskell traducidos con la ayuda de la herramienta _HS-TO-COQ_, en especial los booleanos y
los elementos que se agregaran a los arboles.

Tambien se utilizan lemas y definiciones que ya habian sido previamente demostrados para la biblioteca de teorias de Coq.

En este archivo se presenta la idea de poder usar codigo traducido de Haskell usando la herramienta previamente mencionada y combinandolo con teoremas previamente
demostrados con los tipos booleanos de Coq.
*)
Generalizable All Variables.

Require Export Utf8_core.
Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Bibliotecas traducidas de Haskell a Coq y la biblioteca que contiene lemas y definiciones compartidos entre la insercion y eliminacion de elementos de un arbol rojinegro.*)
Require Import ARNDefiniciones.
Require GHC.Base.
Import GHC.Base.Notations.
(** ** Funciones de insercion.*)
(** *** Funcion ins(a,s)
Donde _a_ es un elemento comparable y _s_ es un arbol rojinegro.
Se hace uso de funciones de balanceo separadas, una para el lado izquierdo y su equivalente para el lado derecho, esto para efectuar los giros necesarios en los subarboles
y de esta manera conservar las invariantes de los arboles rojinegros.

Esta funcion puede regresar arboles _casi_ rojinegros, los cuales pueden tener dos nodos rojos consecutivos pero solamente en la raiz.
*)
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

(** *** Definicion insert(x,s)
Donde _x_ es un elemento comparable y _s_ es un arbol rojinegro.

En esta definicion se arregla el resultado de la funcion anterior al pintar la raiz de negro y de esta manera preservando todas las invariantes de un arbol
rojinegro.
*)
Definition insert {a} `{GHC.Base.Ord a} (x:a) (s:RB a) := makeBlack (ins x s).

Hint Unfold insert.

(** ** Lemas y pruebas
Estos lemas enuncian que la insercion de elementos comparables a un arbol rojinegro, bajo las definiciones antes dadas, dan como resultado un arbol rojinegro.
 *)

(** *** Definiciones auxiliares para las pruebas
Esta definicion es un fold para arboles rojinegros; cuando el arbol tiene raiz roja aplica una funcion _f_ a sus subarboles y nodo, en otro caso aplica
una funcion g al arbol que recibe como argumento. *)
Definition rcase{a} `{GHC.Base.Ord a} {A} f g (t: RB a) : A :=
 match t with
 | T R a x b => f a x b
 | _ => g t
 end.


(**  Esta funcion solo es azucar sintactica para la definicion dada antes. *)
Definition ifred {a} `{GHC.Base.Ord a} (s : RB a) (A B : Prop) := 
rcase (fun _ _ _ => A) (fun _ => B) s.

(** ** Lemas auxiliares para las pruebas.*)
(** *** Lema ifred_notred
Este lema enuncia que si un arbol _no_ tiene la raiz negra la proposicion B se comple.
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
(** *** Lema ifred_or
Este lema enuncia que si un arbol tiene la raiz roja, se cumple la propesicion A o B, de igual manera si la raiz es negra.
*)
Lemma ifred_or {a} `{GHC.Base.Ord a} (s : RB a) (A B : Prop) :
ifred s A B -> A \/ B.
Proof.
induction s;simpl.
intro;right;trivial.
destruct c;intro.
left;trivial.
right;trivial.
Qed.

(** ** Lemas principales
*** Lema ins_rr_rb
Este lema enuncia que si la insercion de un elemento en un arbol rojinegro,usando la funcion _ins_, depende del color de la raiz 
del arbol al cual se le insertara el elemento; si esta es roja, la insercion resultara en un arbol con dos nodos rojos en la raiz del arbol,
en otro caso terminara con un arbol rojinegro.
*)
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


(** *** Lema ins_arb
Este lema enuncia que si se inserta, con la funcion ins, un elemento a un arbol casi rojinegro, el resultado es un arbol rojinegro.
*)
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

(** *** Instancia de un arbol rojinegro.
Esta instancia consolida las pruebas anteriores de coreccion de la insercion de elementos a un arbol rojinegro.
*)
Instance add_rb {a} `{GHC.Base.Ord a} (x:a) (s: RB a) : redblack s -> redblack (insert x s).
Proof.
intros (n,H1).
unfold insert.
apply (makeBlack_rb n).
apply ins_arb.
exact H1.
Qed.

