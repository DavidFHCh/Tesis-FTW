(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.OldList.
Require GHC.Base.
Require Name.
Require OccName.
Require UniqSet.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition NameSet :=
  (UniqSet.UniqSet Name.Name)%type.

Definition Uses :=
  NameSet%type.

Definition FreeVars :=
  NameSet%type.

Definition Defs :=
  NameSet%type.

Definition DefUse :=
  (option Defs * Uses)%type%type.

Definition DefUses :=
  (list DefUse)%type.

(* Converted value declarations: *)

Definition usesOnly : Uses -> DefUses :=
  fun uses => cons (pair None uses) nil.

Definition unitNameSet : Name.Name -> NameSet :=
  UniqSet.unitUniqSet.

Definition unitFV : Name.Name -> FreeVars :=
  unitNameSet.

Definition unionNameSets : list NameSet -> NameSet :=
  UniqSet.unionManyUniqSets.

Definition unionNameSet : NameSet -> NameSet -> NameSet :=
  UniqSet.unionUniqSets.

Definition plusFVs : list FreeVars -> FreeVars :=
  unionNameSets.

Definition plusFV : FreeVars -> FreeVars -> FreeVars :=
  unionNameSet.

Definition plusDU : DefUses -> DefUses -> DefUses :=
  Coq.Init.Datatypes.app.

Definition nameSetElemsStable : NameSet -> list Name.Name :=
  fun ns => Data.OldList.sortBy Name.stableNameCmp (UniqSet.nonDetEltsUniqSet ns).

Definition nameSetAny : (Name.Name -> bool) -> NameSet -> bool :=
  UniqSet.uniqSetAny.

Definition nameSetAll : (Name.Name -> bool) -> NameSet -> bool :=
  UniqSet.uniqSetAll.

Definition mkNameSet : list Name.Name -> NameSet :=
  UniqSet.mkUniqSet.

Definition mkFVs : list Name.Name -> FreeVars :=
  mkNameSet.

Definition mkDUs : list (Defs * Uses)%type -> DefUses :=
  fun pairs =>
    let cont_0__ arg_1__ :=
      let 'pair defs uses := arg_1__ in
      cons (pair (Some defs) uses) nil in
    Coq.Lists.List.flat_map cont_0__ pairs.

Definition minusNameSet : NameSet -> NameSet -> NameSet :=
  UniqSet.minusUniqSet.

Definition isEmptyNameSet : NameSet -> bool :=
  UniqSet.isEmptyUniqSet.

Definition isEmptyFVs : NameSet -> bool :=
  isEmptyNameSet.

Definition intersectNameSet : NameSet -> NameSet -> NameSet :=
  UniqSet.intersectUniqSets.

Definition intersectsNameSet : NameSet -> NameSet -> bool :=
  fun s1 s2 => negb (isEmptyNameSet (intersectNameSet s1 s2)).

Definition intersectFVs : FreeVars -> FreeVars -> FreeVars :=
  intersectNameSet.

Definition findUses : DefUses -> Uses -> Uses :=
  fun dus uses =>
    let get :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair None rhs_uses, uses => unionNameSet rhs_uses uses
        | pair (Some defs) rhs_uses, uses =>
            if orb (intersectsNameSet defs uses) (nameSetAny (OccName.startsWithUnderscore
                                                              GHC.Base.∘
                                                              Name.nameOccName) defs) : bool
            then unionNameSet rhs_uses uses else
            uses
        end in
    Data.Foldable.foldr get uses dus.

Definition filterNameSet : (Name.Name -> bool) -> NameSet -> NameSet :=
  UniqSet.filterUniqSet.

Definition extendNameSetList : NameSet -> list Name.Name -> NameSet :=
  UniqSet.addListToUniqSet.

Definition extendNameSet : NameSet -> Name.Name -> NameSet :=
  UniqSet.addOneToUniqSet.

Definition emptyNameSet : NameSet :=
  UniqSet.emptyUniqSet.

Definition emptyFVs : FreeVars :=
  emptyNameSet.

Definition emptyDUs : DefUses :=
  nil.

Definition elemNameSet : Name.Name -> NameSet -> bool :=
  UniqSet.elementOfUniqSet.

Definition duUses : DefUses -> Uses :=
  fun dus =>
    let get :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair None rhs_uses, uses => unionNameSet rhs_uses uses
        | pair (Some defs) rhs_uses, uses =>
            minusNameSet (unionNameSet rhs_uses uses) defs
        end in
    Data.Foldable.foldr get emptyNameSet dus.

Definition duDefs : DefUses -> Defs :=
  fun dus =>
    let get :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair None _u1, d2 => d2
        | pair (Some d1) _u1, d2 => unionNameSet d1 d2
        end in
    Data.Foldable.foldr get emptyNameSet dus.

Definition delFromNameSet : NameSet -> Name.Name -> NameSet :=
  UniqSet.delOneFromUniqSet.

Definition delListFromNameSet : NameSet -> list Name.Name -> NameSet :=
  fun set ns => Data.Foldable.foldl delFromNameSet set ns.

Definition delFVs : list Name.Name -> FreeVars -> FreeVars :=
  fun ns s => delListFromNameSet s ns.

Definition delFV : Name.Name -> FreeVars -> FreeVars :=
  fun n s => delFromNameSet s n.

Definition allUses : DefUses -> Uses :=
  fun dus =>
    let get :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair _d1 u1, u2 => unionNameSet u1 u2
        end in
    Data.Foldable.foldr get emptyNameSet dus.

Definition addOneFV : FreeVars -> Name.Name -> FreeVars :=
  extendNameSet.

(* External variables:
     None Some bool cons list negb nil op_zt__ option orb pair Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map Data.Foldable.foldl Data.Foldable.foldr
     Data.OldList.sortBy GHC.Base.op_z2218U__ Name.Name Name.nameOccName
     Name.stableNameCmp OccName.startsWithUnderscore UniqSet.UniqSet
     UniqSet.addListToUniqSet UniqSet.addOneToUniqSet UniqSet.delOneFromUniqSet
     UniqSet.elementOfUniqSet UniqSet.emptyUniqSet UniqSet.filterUniqSet
     UniqSet.intersectUniqSets UniqSet.isEmptyUniqSet UniqSet.minusUniqSet
     UniqSet.mkUniqSet UniqSet.nonDetEltsUniqSet UniqSet.unionManyUniqSets
     UniqSet.unionUniqSets UniqSet.uniqSetAll UniqSet.uniqSetAny UniqSet.unitUniqSet
*)
