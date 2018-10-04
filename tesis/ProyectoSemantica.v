(*Autor: David Felipe Hernandez Chiapa
Proyecto Final de Semantica y Verificacion
*)

Require Import Nat.

Require Import List.
Require Import Utf8.

Export ListNotations.

Definition key := nat.

Inductive color := Red | Black.

Section RBTree.
Variable V : Type.
Variable default: V.

 Inductive Tree : Type :=
 | E : Tree 
 | T: color → Tree → key → V → Tree → Tree.




Fixpoint lookup (x: key) (t : Tree) : V :=
  match t with
  | E => default
  | T _ tl k v tr => if x <? k then lookup x tl 
                         else if k <? x then lookup x tr
                         else v
  end.

Definition balance rb t1 k vk t2 :=
 match rb with 
 | Black => match t1 with 
        | T Red (T Red a x vx b) y vy c => T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | T Red a x vx (T Red b y vy c) => T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | _ => match t2 with 
            | T Red (T Red b y vy c) z vz d => T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | T Red b y vy (T Red c z vz d) => T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | _ => T Black t1 k vk t2
            end
        end
 | Red => T Red t1 k vk t2
 end.

Definition makeBlack t := 
  match t with 
  | E => E
  | T _ a x vx b => T Black a x vx b
  end.

Fixpoint ins x vx t :=
 match t with 
 | E => T Red E x vx E
 | T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
                        else if ltb y x then balance c a y vy (ins x vx b)
                        else T c a x vx b
 end.

Definition insert x vx t := makeBlack (ins x vx t).



Inductive SearchTreeAux : nat → Tree → nat → Prop :=
| ST_E : ∀ min max, min ≤ max → SearchTreeAux min E max
| ST_T: ∀ min c l k v r max,
    SearchTreeAux min l k →
    SearchTreeAux (S k)  r max →
    SearchTreeAux min (T c l k v r) max.

Inductive isSearchTree: Tree → Prop :=
| ST_intro: ∀ t min max, SearchTreeAux min t max → isSearchTree t.

Theorem SearchTreeCorrectness: ∀ col lt rt k v min max, 
                                SearchTreeAux min lt k ->
                                SearchTreeAux (S k) rt max ->
                                SearchTreeAux min (balance col lt k v rt) max.
Proof.
intros.
unfold balance.
destruct col.
*
constructor;trivial.
*
destruct lt;destruct rt.
constructor;trivial.
destruct c.
destruct rt1;destruct rt2.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
constructor;trivial.
destruct c.
destruct lt1;destruct lt2.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c0.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
constructor;trivial.
destruct c;destruct lt1;destruct lt2;destruct c0;destruct rt1;destruct rt2.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H;inversion H9;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H;inversion H9;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H;inversion H9;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c2.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H;inversion H9;trivial.
destruct c0.
constructor;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H;inversion H9;trivial.
constructor;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c1.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
constructor;trivial.
destruct c0.
constructor;constructor;inversion H0;inversion H8;trivial.
destruct c2.
constructor;constructor;inversion H0;inversion H9;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
constructor;trivial.
Qed.

Inductive isRB : Tree → color → nat → Prop :=
 | IsRB_leaf: ∀ c, isRB E c 0
 | IsRB_r: ∀ tl k kv tr n,
          isRB tl Red n →
          isRB tr Red n →
          isRB (T Red tl k kv tr) Black n
 | IsRB_b: ∀ c tl k kv tr n,
          isRB tl Black n →
          isRB tr Black n →
          isRB (T Black tl k kv tr) c (S n).


Lemma red_to_black : ∀ t n, isRB t Red n -> isRB t Black n.
Proof.
intros.
destruct H;constructor;trivial.
Qed.
Hint Resolve red_to_black.



Inductive nearRB : Tree → nat → Prop :=
| nrRB_r: ∀ tl k kv tr n,
         isRB tl Black n →
         isRB tr Black n →
         nearRB (T Red tl k kv tr) n
| nrRB_b: ∀ tl k kv tr n,
         isRB tl Black n →
         isRB tr Black n →
         nearRB (T Black tl k kv tr) (S n).

Lemma insAux : ∀ k x t1 n,isRB (ins k x t1) Black n -> isRB (ins k x t1) Red n.
Admitted.

Theorem ins_isRB:
  ∀ k x t n, 
    (isRB t Red n → nearRB (ins k x t) n) ∧
    (isRB t Black n → isRB (ins k x t) Black n).
Proof.
induction t; intro n; simpl; split; intros; inversion H; repeat constructor; auto.
*
destruct (IHt1 n0); clear IHt1.
destruct (IHt2 n0); clear IHt2.
specialize (H10 H7).
specialize (H12 H8).
unfold balance.
destruct (k <? k0).
destruct (ins k x t1).
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18;auto.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
constructor;trivial.
destruct c1.
destruct t3.
destruct t4.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18;auto.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H10;inversion H19;auto.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18;auto.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H10;inversion H18;auto.
destruct t4.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18;auto.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H10;inversion H19;auto.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18;auto.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
constructor;trivial.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18;auto.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19;auto.
constructor;trivial.
constructor;trivial.
destruct (k0 <? k).
destruct t1.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
destruct t1_1.
destruct t1_2.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H7;inversion H19;trivial.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H7;inversion H18;trivial.
destruct t1_2. 
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H7;inversion H19;trivial.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
constructor;trivial.
*
destruct (IHt1 n); clear IHt1.
destruct (IHt2 n); clear IHt2.
assert (A := H6).
assert (B := H7).
apply red_to_black in H6.
apply red_to_black in H7.
specialize (H11 H7).
specialize (H9 H6).
unfold balance.
destruct (k0 <? k);destruct (k <? k0);constructor;trivial.
apply insAux;trivial.
apply insAux;trivial.
apply insAux;trivial.
*
destruct (IHt1 n0); clear IHt1.
destruct (IHt2 n0); clear IHt2.
specialize (H10 H7).
specialize (H12 H8).
unfold balance.
destruct (k <? k0).
destruct (ins k x t1).
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
destruct t3.
destruct t4.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H10;inversion H19.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H10;inversion H18.
destruct t4.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H10;inversion H19.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
constructor;trivial.
destruct t2.
constructor;trivial.
destruct c1.
destruct t2_1.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H18.
destruct t2_2.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H8;inversion H19.
constructor;trivial.
constructor;trivial.
destruct (k0 <? k).
destruct t1.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
destruct t1_1.
destruct t1_2.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H7;inversion H19.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H7;inversion H18.
destruct t1_2.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H7;inversion H19.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
destruct (ins k x t2).
constructor;trivial.
destruct c1.
destruct t1.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H18.
destruct t3.
constructor;trivial.
destruct c1.
constructor;constructor;inversion H12;inversion H19.
constructor;trivial.
constructor;trivial.
constructor;trivial.
Qed.


End RBTree.
































