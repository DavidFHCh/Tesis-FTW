Require Import GHC.Base.
Require Import Data.Foldable.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

From Coq Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

(* -------------------------------------------------------------------- *)

(* Laws *)

Class FoldableLaws {t} `{Foldable t} := {
(*  foldr_foldMap : forall f z t, foldr f z t = appEndo (foldMap (Mk_Endo ∘ f) t ) z;
  foldl_foldMap : forall f z t,
     foldl f z t = appEndo (getDual (foldMap (Mk_Dual ∘ Mk_Endo ∘ flip f) t)) z;
  foldMap_id : forall a `{Monoid a}, @fold t _ a = foldMap id *)
}.

Class FoldableFunctor {t} `{Foldable t} `{Functor t} := {
  foldfmap : forall a b (f : a -> b)`{Monoid b}, foldMap f = fold ∘ fmap f;
}.

(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Theorem hs_coq_length_list {A} (l : list A) :
  length l = Zlength l.
Proof. apply hs_coq_list_length. Qed.

Theorem hs_coq_length_list' {A} (l : list A) :
  Data.Foldable.Foldable__list_length l = Zlength l.
Proof. apply hs_coq_length_list. Qed.

Theorem hs_coq_foldr_list {A B} (f : A -> B -> B) (z : B) (l : list A) :
  foldr f z l = Coq.Lists.List.fold_right f z l.
Proof. by rewrite ->hs_coq_foldr_base. Qed.

Theorem hs_coq_foldr_list' {A B} (f : A -> B -> B) (z : B) (l : list A) :
  Data.Foldable.Foldable__list_foldr f z l = Coq.Lists.List.fold_right f z l.
Proof. apply hs_coq_foldr_list. Qed.

Theorem hs_coq_foldl_list {A B} (f : B -> A -> B) (z : B) (l : list A) :
  foldl f z l = Coq.Lists.List.fold_left f l z.
Proof. apply hs_coq_foldl_base. Qed.

Theorem hs_coq_foldl'_list {A B} (f : B -> A -> B) (z : B) (l : list A) :
  foldl' f z l = Coq.Lists.List.fold_left f l z.
Proof. apply hs_coq_foldl_base. Qed.

Theorem hs_coq_foldl_list' {A B} (f : B -> A -> B) (z : B) (l : list A) :
  Data.Foldable.Foldable__list_foldl f z l = Coq.Lists.List.fold_left f l z.
Proof. apply hs_coq_foldl_list. Qed.


(* -------------------------------------------------------------------- *)
(** ** Theory about foldable for lists *)

Ltac unfold_Foldable_foldr :=
  unfold Foldable.foldr,
  Foldable.foldr__,
  Foldable.Foldable__list,
  Foldable.Foldable__list_foldr.

Ltac unfold_Foldable_foldl' :=
  unfold Foldable.foldl',  Foldable.Foldable__list, 
  Foldable.foldl'__, Foldable.Foldable__list_foldl', Base.foldl'.

Ltac unfold_Foldable_foldl :=
  unfold Foldable.foldl,  Foldable.Foldable__list, 
  Foldable.foldl__, Foldable.Foldable__list_foldl, Base.foldl.


Lemma Foldable_foldr_nil : forall a b (f: a -> b -> b) (s:b), 
    Foldable.foldr f s nil = s.
Proof.  
  unfold_Foldable_foldr.
  simpl.
  auto.
Qed.

Lemma Foldable_foldr_cons : forall a b (f: a -> b -> b) (s:b) x xs, 
    Foldable.foldr f s (x :: xs) = f x (Foldable.foldr f s xs).
Proof.  
  unfold_Foldable_foldr.
  simpl.
  auto.
Qed.

Lemma Foldable_foldr_app : forall a b (f:a -> b -> b) (s:b) 
                              (vs1 : list a) (vs2: list a),
    Foldable.foldr f s (vs1 ++ vs2) =
    Foldable.foldr f (Foldable.foldr f s vs2) vs1.
Proof.
  intros.
  unfold_Foldable_foldr.
  rewrite hs_coq_foldr_base.
  rewrite fold_right_app.
  auto.
Qed.

Lemma Foldable_foldl_nil : forall a b (f: b -> a -> b) (s:b), 
    Foldable.foldl f s nil = s.
Proof.
  unfold_Foldable_foldl.  
  simpl.
  auto.
Qed.

Lemma Foldable_foldl_cons : forall a b (f: b -> a -> b) (s:b) x xs, 
    Foldable.foldl f s (x :: xs) = (Foldable.foldl f (f s x) xs).
Proof.
  intros.
  unfold_Foldable_foldl.
  simpl.
  auto.
Qed.

Lemma Foldable_foldl_app : forall a b (f:b -> a -> b) (s:b) 
                              (vs1 : list a) (vs2: list a),
    Foldable.foldl f s (vs1 ++ vs2) =
    Foldable.foldl f (Foldable.foldl f s vs1) vs2.
Proof.
  unfold_Foldable_foldl.
  intros.
  repeat rewrite <- List_foldl_foldr.
  rewrite fold_left_app.
  auto.
Qed.

Lemma Foldable_foldl'_nil : forall a b (f: b -> a -> b) (s:b), 
    Foldable.foldl' f s nil = s.
Proof.
  unfold_Foldable_foldl'.  
  simpl.
  auto.
Qed.

Lemma Foldable_foldl'_cons : forall a b (f: b -> a -> b) (s:b) x xs, 
    Foldable.foldl' f s (x :: xs) = (Foldable.foldl' f (f s x) xs).
Proof.
  intros.
  unfold_Foldable_foldl'.
  simpl.
  auto.
Qed.

Lemma Foldable_foldl'_app : forall a b (f:b -> a -> b) (s:b) 
                              (vs1 : list a) (vs2: list a),
    Foldable.foldl' f s (vs1 ++ vs2) =
    Foldable.foldl' f (Foldable.foldl' f s vs1) vs2.
Proof.
  unfold_Foldable_foldl'.
  intros.
  repeat rewrite <- List_foldl_foldr.
  rewrite fold_left_app.
  auto.
Qed.



Hint Rewrite
     Foldable_foldl'_nil Foldable_foldr_nil 
     Foldable_foldl_nil

     Foldable_foldl'_cons Foldable_foldr_cons 
     Foldable_foldl_cons

     Foldable_foldl'_app Foldable_foldr_app 
     Foldable_foldl_app : hs_simpl.

Lemma Foldable_any_nil : forall A (f : A -> bool), Foldable.any f nil = false. 
Proof. 
  intros.
  unfold Foldable.any.
  unfold compose, Foldable.foldMap.
  unfold Foldable.Foldable__list,Foldable.foldMap__,
         Foldable.Foldable__list_foldMap,
         Foldable.Foldable__list_foldr. 
  simpl.
  auto.
Qed.

Lemma Foldable_any_cons : forall A x xs (f : A -> bool), 
    Foldable.any f (x :: xs) = f x || Foldable.any f xs.
Proof. 
  intros.
  unfold Foldable.any.
  unfold compose, Foldable.foldMap.
  unfold Foldable.Foldable__list,Foldable.foldMap__,
         Foldable.Foldable__list_foldMap,
         Foldable.Foldable__list_foldr. 
  simpl.
  auto.
Qed.

Lemma Foldable_any_app : forall {A} `{Eq_ A} (v:A) (l1 l2:list A),
      Foldable.any (fun y : A => v == y) (l1 ++ l2) =
      Foldable.any (fun y : A => v == y) l1
      || Foldable.any (fun y : A => v == y) l2.
Proof.
  intros.
  unfold Foldable.any.
  unfold compose, Foldable.foldMap.
  unfold Foldable.Foldable__list,Foldable.foldMap__,
         Foldable.Foldable__list_foldMap,
         Foldable.Foldable__list_foldr. 
  simpl.
  induction l1.
  + simpl. auto.
  + simpl.
    rewrite <- orb_assoc.
    f_equal.
    unfold SemigroupInternal.getAny.
    auto.
Qed.

Hint Rewrite @Foldable_any_nil @Foldable_any_cons @Foldable_any_app : hs_simpl.

Lemma elem_nil : forall {A} `{Eq_ A}  (x:A),  
  Foldable.elem x nil = false.
Proof.
  intros.
  reflexivity.
Qed.

Lemma elem_cons : 
  forall {A} `{Eq_ A} (v:A) (x:A) (l:list A),  
    Foldable.elem v (x :: l) = (v == x) || Foldable.elem v l.
Proof.
  intros.
  apply Foldable_any_cons.
Qed.

Lemma Foldable_elem_app : forall {A}`{Eq_ A} (v:A) (l1 l2:list A),  
    Foldable.elem v (l1 ++ l2) = Foldable.elem v l1 || Foldable.elem v l2.
Proof.
  intros. apply Foldable_any_app.
Qed.

Hint Rewrite @elem_nil @elem_cons @Foldable_elem_app : hs_simpl.



