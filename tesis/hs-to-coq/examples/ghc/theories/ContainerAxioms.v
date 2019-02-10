(* When these things get proven, they ought to move to [containers] *)

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import GHC.Base.
Require Import Data.IntMap.Internal.

Axiom member_eq : forall A k k' (i : IntMap.Internal.IntMap A),
    k == k' ->
    IntMap.Internal.member k i = IntMap.Internal.member k' i.

Axiom member_insert : forall A k k' v (i : IntMap.Internal.IntMap A),
IntMap.Internal.member k (IntMap.Internal.insert k' v i) =
  (k == k') || IntMap.Internal.member k i.

Axiom member_union :
   forall (A : Type)
     (key : Internal.Key) 
     (i i0 : Internal.IntMap A),
   (IntMap.Internal.member key (IntMap.Internal.union i i0)) = 
   (IntMap.Internal.member key i0 || IntMap.Internal.member key i).

Axiom union_nil_l : forall A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.union IntMap.Internal.Nil i = i.

Axiom union_nil_r : forall A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.union i IntMap.Internal.Nil = i.

Axiom difference_self : forall A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.difference i i = IntMap.Internal.empty.

Axiom difference_nil_r : forall A B (i : IntMap.Internal.IntMap A),
    IntMap.Internal.difference i (@IntMap.Internal.Nil B) = i.

Axiom difference_nil_l : forall B A (i : IntMap.Internal.IntMap A),
    IntMap.Internal.difference (@IntMap.Internal.Nil B) i = 
    (@IntMap.Internal.Nil B).

Axiom difference_Tip_member:
  forall A (i : Internal.IntMap A) (n : Internal.Key),
    (IntMap.Internal.member n i) ->
    forall x:A, IntMap.Internal.difference
        (IntMap.Internal.Tip n x) i = Internal.Nil.

Axiom difference_Tip_non_member: 
    forall A (i : Internal.IntMap A) (n : Internal.Key),
      (IntMap.Internal.member n i) = false ->
      forall x : A, IntMap.Internal.difference (IntMap.Internal.Tip n x) i =
        IntMap.Internal.Tip n x.

Axiom null_empty : forall A,
    (@IntMap.Internal.null A IntMap.Internal.empty).

Axiom filter_comp : forall A f f' (i : IntMap.Internal.IntMap A),
    IntMap.Internal.filter f (IntMap.Internal.filter f' i) =
    IntMap.Internal.filter (fun v => f v && f' v) i.

Axiom filter_insert: forall A f key (v:A) i,
  IntMap.Internal.filter f (IntMap.Internal.insert key v i) =
  (if (f v)
   then IntMap.Internal.insert key v (IntMap.Internal.filter f i)
   else IntMap.Internal.filter f i).

Axiom filter_true : forall (A:Type) (m:IntMap.Internal.IntMap A), 
   IntMap.Internal.filter (const true) m = m.

Axiom lookup_insert : forall A key (val:A) i, 
    IntMap.Internal.lookup key (IntMap.Internal.insert key val i) = Some val.

Axiom lookup_insert_neq : 
  forall b key1 key2 (val:b) m, 
    key1 <> key2 ->
    Internal.lookup key1 (Internal.insert key2 val m) = Internal.lookup key1 m.

Axiom lookup_filterWithKey : 
  forall b key (val:b) m f, Internal.lookup key (Internal.filterWithKey f m) = Some val ->
                       Internal.lookup key m = Some val.

Axiom lookup_intersection :
  forall a b key (val1:a) m1 m2, 
    Internal.lookup key m1 = Some val1 /\
    (exists (val2:b), Internal.lookup key m2 = Some val2) <-> 
    Internal.lookup key (Internal.intersection m1 m2) = Some val1.

Axiom delete_eq : forall key b (i : IntMap b),
  lookup key (delete key i) = None.

Axiom delete_neq : forall key1 key2 b (i : IntMap b),
    key1 <> key2 ->
    lookup key1 (delete key2 i) = lookup key1 i.

Axiom member_delete_neq : forall k1 k2 b (i: IntMap b), k1 <> k2 ->
  IntMap.Internal.member k2 (IntMap.Internal.delete k1 i) =
  IntMap.Internal.member k2 i.

Axiom lookup_union :
  forall (A:Type) key (val:A) (m1 m2: IntMap A), 
    (lookup key m1 = Some val \/ (lookup key m1 = None /\ lookup key m2 = Some val)) <->
    lookup key (union m1 m2) = Some val.

Axiom lookup_partition :
  forall (A:Type) key (val:A) (m m': IntMap A) (P: A -> bool), 
    ((m' = fst (partition P m) \/
      m' = snd (partition P m)) /\
     lookup key m' = Some val) <->
    lookup key m  = Some val.

(*
Axiom lookup_partition :
  forall (key : Internal.Key) (b : Type) (i left right: IntMap b)(f:b -> bool)(y : b), 
    lookup key i = Some y ->
    (left, right) = partition f i -> 
    lookup key left = Some y \/ lookup key right = Some y.    
*)

Axiom lookup_union_None:
  forall (A : Type)
    (key : Internal.Key)
    (m1 m2 : Internal.IntMap A),
    IntMap.Internal.lookup key m1 = None /\
    IntMap.Internal.lookup key m2 = None <->
    IntMap.Internal.lookup key
             (IntMap.Internal.union m1 m2) = None.

Axiom lookup_difference_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap b) (y:b),
    lookup key i' = Some y -> 
    lookup key (difference i i') = None.

Axiom lookup_difference_not_in_snd:
  forall (key : Internal.Key) (b : Type) (i i': IntMap b)(y:b),
    lookup key i' = None ->
    lookup key (difference i i') = lookup key i.

Axiom member_lookup :
   forall (A : Type)
     (key : Internal.Key) 
     (i : Internal.IntMap A),
   (is_true (IntMap.Internal.member key i)) =
   (exists val, IntMap.Internal.lookup key i = Some val).

Axiom non_member_lookup :
   forall (A : Type)
     (key : Internal.Key) 
     (i : Internal.IntMap A),
   (IntMap.Internal.member key i = false) =
   (IntMap.Internal.lookup key i = None).

(* This is a pretty strong property about the representation of 
   IntMaps. I hope that it is true. *)
Axiom delete_commute :
  forall (A : Type)
    (kx ky : Internal.Key) 
    (i : Internal.IntMap A),
  IntMap.Internal.delete ky (IntMap.Internal.delete kx i) =
  IntMap.Internal.delete kx (IntMap.Internal.delete ky i).

Axiom lookup_eq : forall A k k' (i : IntMap.Internal.IntMap A),
    k == k'->
    IntMap.Internal.lookup k i = IntMap.Internal.lookup k' i.

Axiom intersection_empty :
  forall A B (i : IntMap.Internal.IntMap A) (j : IntMap.Internal.IntMap B),
    (j = IntMap.Internal.empty) ->
    IntMap.Internal.null (IntMap.Internal.intersection i j).


(*
This is a QuickChick setup to test the above axioms
(as bugs easily lurk there).

Unfortunately, we have to wait for 
https://github.com/QuickChick/QuickChick/issues/87
to be fixed, as currently the programs that QuickChick extracts to
test stuff do not compile...

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
From QuickChick Require Import Instances.
Set Warnings "-extraction-opaque-accessed,-extraction".

Global Instance genKey : GenSized Internal.Key := 
  {| arbitrarySized n := fmap N.of_nat (arbitrarySized n) |}.

Global Instance genIntMap {A} `{GenSized A} : GenSized (IntMap A) := 
  {| arbitrarySized n := fmap Internal.fromList (arbitrarySized n) |}.

Global Instance shrinkIntMap {A} : Shrink (IntMap A) := 
  {| shrink := fun _ => nil |}.

Global Instance shrinkKey : Shrink Internal.Key := 
  {| shrink := fun _ => nil |}.

Global Instance showKey : Show Internal.Key :=
  {| show := fun s => show (N.to_nat s) |}.

Global Instance showIntMap {A} `{Show A} : Show (IntMap A) :=
  {| show := fun s => show (Internal.toList s) |}.

QuickCheck delete_eq.
*)
