(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From mathcomp.ssreflect
Require Import ssreflect ssrnat prime ssrbool eqtype.

Require Import Core.
Require Import FV.
Require Import Proofs.ContainerAxioms.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetFSet.
Require Import Proofs.Var.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Import GHC.Base.ManualNotations.



Set Bullet Behavior "Strict Subproofs".


(** * Well-formedness of [FV]s. *)

(* A FV is well formed when it is denoted by some VarSet vs. *)


Reserved Notation "A ⊢ B" (at level 70, no associativity).

Inductive Denotes : VarSet -> FV -> Prop :=
| DenotesVarSet : forall vs fv,
    (forall f in_scope vs' l,
        extendVarSetList emptyVarSet l [=] vs' ->
        extendVarSetList emptyVarSet (fst (fv f in_scope (l, vs'))) [=]
        snd (fv f in_scope (l, vs')) /\
        snd (fv f in_scope (l, vs')) [=]
        unionVarSet (minusVarSet (filterVarSet f vs) in_scope) vs') ->
    vs ⊢ fv
where "A ⊢ B" := (Denotes A B).


Theorem Denotes_fvVarSet : forall m fv f in_scope l vs,
    m ⊢ fv ->
    extendVarSetList emptyVarSet l [=] vs ->
    snd (fv f in_scope (l, vs)) [=]
    unionVarSet (minusVarSet (filterVarSet f m) in_scope) vs.
Proof.
  move => m fv f in_scope l vs [vs' fv' H0] H1.
  specialize (H0 f in_scope vs l ); subst.
  move: (H0 H1) => [h0 h1].
  auto.
Qed.

Definition WF_fv (fv : FV) : Prop := exists vs, vs ⊢ fv.
      
Ltac unfold_WF :=
  repeat match goal with
  | [ H : WF_fv ?fv |- _] =>
    let vs := fresh "vs" in
    let Hd := fresh "Hdenotes" in
    inversion H as [vs Hd]; inversion Hd; subst; clear H
  | [ |- WF_fv ?fv ] =>
    unfold WF_fv
  end.


(* We show that the various operations on FVs produce well-formed FVs. *)

Lemma emptyVarSet_emptyFV : Denotes emptyVarSet emptyFV.
Proof.
  constructor; intros; subst.
  unfold emptyFV.
  unfold fst, snd.
  hs_simpl.
  split; auto.
  reflexivity.
Qed.

Lemma empty_FV_WF :
  WF_fv emptyFV.
Proof.
  unfold WF_fv. exists emptyVarSet. eapply emptyVarSet_emptyFV. 
Qed.


Lemma unitVarSet_unitFV x : Denotes (unitVarSet x) (unitFV x).
Proof.
  constructor; intros; subst. 
  unfold fst, snd.
  unfold unitFV.
  destruct elemVarSet eqn:E1;
  destruct (f x) eqn:FX;
  hs_simpl; split; auto.
  - rewrite -> filterSingletonTrue; try done.
    rewrite elemVarSet_minusVarSetTrue; try done.
    hs_simpl.
    reflexivity.
  - rewrite filterSingletonFalse; try done.
    hs_simpl.
    reflexivity.
  - elim In: (elemVarSet x vs') => //.    
    hs_simpl.
    rewrite <- H.
    rewrite extendVarSetList_extendVarSet_iff.
    reflexivity.
  - rewrite filterSingletonTrue; try done.
    rewrite elemVarSet_minusVarSetFalse; try done.
    elim E2: (elemVarSet x vs').
    hs_simpl.
    set_b_iff.
    rewrite add_equal; try done.
    hs_simpl.
    reflexivity.
  - elim E2: (elemVarSet x vs'); done.
  - rewrite filterSingletonFalse; try done.
    hs_simpl.
    elim E2: (elemVarSet x vs'); done.
Qed.


Lemma unit_FV_WF :
  forall x, WF_fv (unitFV x).
Proof.
  move=>x. unfold WF_fv.
  exists (unitVarSet x).
  eapply unitVarSet_unitFV.
Qed.

Lemma filterVarSet_filterFV f vs x :
  Denotes vs x -> Denotes (filterVarSet f vs) (filterFV f x).
Proof.
  move => D.
  constructor. move=> f0 in_scope vs' l h0.
  inversion D.
  unfold filterFV.
  specialize (H (fun v : Var => f0 v && f v) in_scope vs' l h0).
  destruct H. intuition.
  rewrite H2. rewrite <- filterVarSet_comp. reflexivity.
Qed.

Lemma filter_FV_WF : forall f x,
    WF_fv x -> WF_fv (filterFV f x).
Proof.
  intros. unfold_WF.
  exists (filterVarSet f vs). 
  eapply filterVarSet_filterFV. auto.
Qed.

Lemma delVarSet_delFV vs v fv :
  Denotes vs fv -> Denotes (delVarSet vs v) (delFV v fv).
Proof.
  move=> H. inversion H.
  constructor; intros. unfold delFV.
  specialize (H0 f (extendVarSet in_scope v) vs' l H3).
  destruct H0. intuition. rewrite H4.
  destruct (fv f (extendVarSet in_scope v)) as [l0 h0] eqn:h.
  simpl in *.
  apply union_equal_1.
  move => x. 
  unfold VarSetFSet.In.
  rewrite !elemVarSet_minusVarSet.
  split.
  - move=> /andP [h1 h2].
    apply /andP.
    hs_simpl in h2.
    rewrite negb_or in h2.
    move: h2 => /andP.
    move => [h3 h4].
    intuition.
    erewrite filterVarSet_StrongSubset; eauto.
    apply delVarSet_StrongSubset; auto.
  - move=> /andP [h1 h2].
    apply /andP.

    rewrite elemVarSet_filterVarSet in h1.
    move: h1 => /andP. move => [h3 h4].
    elim hf: (f x); rewrite hf in h3; try done; clear h3.
    rewrite elemVarSet_delVarSet in h4.
    elim ev: (v GHC.Base.== x).
    + rewrite ev in h4. done. 
    + rewrite ev in h4. 
      move: h4 => /andP. move => [h5 h6].
      rewrite elemVarSet_filterVarSet.
      rewrite elemVarSet_extendVarSet.
      rewrite hf.
      rewrite ev.
      rewrite h6.
      done.
Qed.


Lemma del_FV_WF : forall fv v,
    WF_fv fv -> WF_fv (delFV v fv).
Proof.
  intros. unfold_WF.
  exists (delVarSet vs v). 
  eapply delVarSet_delFV. auto.
Qed.

Lemma unionVarSet_unionFV vs vs' fv fv' :
  Denotes vs fv -> Denotes vs' fv' -> Denotes (unionVarSet vs vs') (unionFV fv' fv).
Proof.
  move=> H H1. inversion H. inversion H1. subst.
  constructor.
  move=> f in_scope vs1 l h.
  unfold unionFV.
  specialize (H0 f in_scope vs1 l h).  move: H0 => [h1 h2].
  remember (fv f in_scope (l, vs1)) as vs_mid.
  specialize (H4 f in_scope (snd vs_mid) (fst vs_mid) h1); move: H4 => [h3 h4].
  replace vs_mid with (fst vs_mid, snd vs_mid); [| destruct vs_mid; reflexivity].
  intuition.
  remember (fv' f in_scope (fst vs_mid, snd vs_mid)) as vs_fin.
  rewrite h4.
  rewrite h2.
  rewrite <- union_assoc.
  apply union_equal_1.
  rewrite -> unionVarSet_minusVarSet.
  rewrite unionVarSet_filterVarSet.
  set_b_iff. rewrite union_sym.
  reflexivity. 
Qed.

Lemma union_FV_WF : forall fv fv',
    WF_fv fv -> WF_fv fv' -> WF_fv (unionFV fv fv').
Proof.
  intros. unfold_WF.
  exists (unionVarSet vs vs0). 
  eapply unionVarSet_unionFV; eauto.
Qed.  

Lemma mapUnionFV_nil A f : 
  mapUnionFV f (nil : list A) = emptyFV.
Proof.
  simpl.
  unfold emptyFV.
  reflexivity.
Qed. 
Hint Rewrite mapUnionFV_nil : hs_simpl. 

Lemma mapUnionFV_cons A f (x : A) xs : 
  mapUnionFV f (x :: xs) = unionFV (mapUnionFV f xs) (f x).
Proof.
  simpl.
  unfold unionFV.
  reflexivity.
Qed.
Hint Rewrite mapUnionFV_cons : hs_simpl. 


Lemma map_union_FV_WF : forall A f (ls : list A),
    (forall e, In e ls -> WF_fv (f e)) ->
    WF_fv (mapUnionFV f ls).
Proof.
  induction ls.
  - intros.
    exists emptyVarSet.
    hs_simpl.
    eapply emptyVarSet_emptyFV.
  -  move=> h. simpl in h.
    assert (h0 : forall e : A, In e ls -> WF_fv (f e)). { intros. apply h. tauto. }
    apply IHls in h0.
    assert (WF_fv (f a)). { apply h; tauto. }
    hs_simpl.
    move: h0 => [vs D].
    move: H => [vs' D'].
    eexists.
    eapply unionVarSet_unionFV; eauto.
Qed.

Lemma unions_FV_WF : forall fvs,
    (forall fv, In fv fvs -> WF_fv fv) ->
    WF_fv (unionsFV fvs).
Proof.
  apply map_union_FV_WF.
Qed.

Lemma mkFVs_FV_WF : forall vs,
    WF_fv (mkFVs vs).
Proof.
  intros. apply map_union_FV_WF; intros. apply unit_FV_WF.
Qed.

Hint Resolve unit_FV_WF.
Hint Resolve empty_FV_WF.
Hint Resolve union_FV_WF.
Hint Resolve unions_FV_WF.
Hint Resolve del_FV_WF.
Hint Resolve mkFVs_FV_WF.

(** * Some other theroems about [FV]s. *)

Lemma union_empty_l : forall fv, FV.unionFV FV.emptyFV fv = fv.
Proof. reflexivity. Qed.

Lemma union_empty_r : forall fv, FV.unionFV fv FV.emptyFV = fv.
Proof. reflexivity. Qed.

Lemma DenotesfvVarSet vs fv :
  Denotes vs fv -> fvVarSet fv [=] vs.
Proof.
  move => [vs0 fv0 h1].
  unfold fvVarSet, op_z2218U__, fvVarListVarSet, Tuple.snd.
  specialize (h1 (const true) emptyVarSet emptyVarSet nil).
  destruct h1.
  rewrite extendVarSetList_nil.
  reflexivity.
  remember (fv0 (const true) emptyVarSet (nil, emptyVarSet)) as tup.
   replace tup with (fst tup, snd tup); [| destruct tup; reflexivity].
   rewrite H0.
   hs_simpl.
   reflexivity.
Qed.

Lemma fst_pair A B (x:A) (y:B) : fst (x,y) = x.
Proof. simpl. reflexivity. Qed.
Hint Rewrite fst_pair : hs_simpl.
Lemma snd_pair A B (x:A) (y:B) : snd (x,y) = y.
Proof. simpl. reflexivity. Qed.
Hint Rewrite snd_pair : hs_simpl.


Lemma Denotes_inj1 vs1 vs2 fv : Denotes vs1 fv -> Denotes vs2 fv -> vs1 [=] vs2.
Proof.      
  move => h1. inversion h1.
  move => h2. inversion h2.
  subst.
  set in_scope := emptyVarSet.
  assert (h : extendVarSetList emptyVarSet nil [=] emptyVarSet).
  { rewrite <- mkVarSet_extendVarSetList. reflexivity. }
  specialize (H (const true) in_scope emptyVarSet nil h).
  specialize (H2 (const true) in_scope emptyVarSet nil h).
  move: H => [h3 h4].
  move: H2 => [h5 h6].
  remember (fv (const true) emptyVarSet (nil,emptyVarSet)) as tup1.
  replace tup1 with (fst tup1, snd tup1); [| destruct tup1; reflexivity].
  remember (fv (const true) emptyVarSet (nil,emptyVarSet)) as tup2.
  replace tup2 with (fst tup2, snd tup2); [| destruct tup2; reflexivity].
  hs_simpl in h4.
  hs_simpl in h6.
  rewrite <- h4.
  rewrite <- h6.
  reflexivity.
Qed.

Lemma exists_elems : forall vs, exists l, extendVarSetList emptyVarSet l [=] vs.
Proof.
  move => vs.
  elim: vs => [i].
  elim: i => [m].
  exists (Foldable.toList m).
  unfold Foldable.toList, Foldable.toList__ , Internal.Foldable__IntMap, Internal.Foldable__IntMap_toList. 
  rewrite extendVarSetList_foldl'. 
  unfold add, extendVarSet.
  unfold emptyVarSet.
  unfold UniqSet.addListToUniqSet, UniqSet.emptyUniqSet, UniqFM.emptyUFM.
  unfold UniqSet.addOneToUniqSet.
  unfold UniqFM.addToUFM.
Abort.


Lemma unionVarSet_same vs : unionVarSet vs vs [=] vs.
Proof. set_b_iff. fsetdec. Qed.
Hint Rewrite unionVarSet_same : hs_simpl.

Lemma delVarSet_fvVarSet: forall fv x,
    WF_fv fv ->
    delVarSet (fvVarSet fv) x [=] fvVarSet (delFV x fv).
Proof.
  move => fv x [vs D].
  move: (delVarSet_delFV _ x _ D) => h1.
  move: (DenotesfvVarSet _ _ h1) => h2.
  move: (DenotesfvVarSet _ _ D) => h3.
  rewrite h3.
  rewrite h2.
  reflexivity.
Qed.

Lemma delVarSet_fvVarSet_exact: forall fv x,
    WF_fv fv ->
    delVarSet (fvVarSet fv) x = fvVarSet (delFV x fv).
Proof.
  move=> fv x [vs D].
  unfold FV.delFV, FV.fvVarSet.
  unfold Base.op_z2218U__, FV.fvVarListVarSet.

  inversion D; subst.
  assert (h : extendVarSetList emptyVarSet nil [=] emptyVarSet).
  { rewrite <- mkVarSet_extendVarSetList. reflexivity. }
  move: (H (const true) emptyVarSet emptyVarSet nil h) => [h0 h1].
  remember (fv (const true) emptyVarSet (nil,emptyVarSet)) as tup1.
  replace tup1 with (fst tup1, snd tup1); [| destruct tup1; reflexivity].
  move: (H (const true) (extendVarSet emptyVarSet x) emptyVarSet nil h) => [h2 h3].
  remember (fv (const true) (extendVarSet emptyVarSet x) (nil,emptyVarSet)) as tup2.
  replace tup2 with (fst tup2, snd tup2); [| destruct tup2; reflexivity].
  hs_simpl in h1.
  hs_simpl in h3.
  hs_simpl.
  clear H. clear h.
Admitted.
(*  specialize (H0 (Base.const true) emptyVarSet emptyVarSet [] H2).
  specialize (H1 (Base.const true) (extendVarSet emptyVarSet x) emptyVarSet [] H2).
  destruct H0; destruct H1.
  rewrite hs_coq_tuple_snd. rewrite H3.
  rewrite hs_coq_tuple_snd. rewrite H4.
  unfold_VarSet_to_IntMap.
  (* Seems true. *)
Admitted. *)


(* --------------------------------------- *)