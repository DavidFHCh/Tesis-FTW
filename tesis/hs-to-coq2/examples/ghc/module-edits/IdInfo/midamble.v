(*  IdInfo: midamble *)

Require GHC.Err.

(* --------------------- *)
(* There are two parts of IdInfo that cause trouble -- Rules & unfolding information. 
   Part of the issue is that types contain embedded CoreExpr's 
*)
(* We break the cyclic structure for the unfolding info here. The type "Unfolding" is parameterized 
   in the midamble. *)


Inductive UnfoldingInfo : Type
  := NoUnfolding : UnfoldingInfo
  |  BootUnfolding : UnfoldingInfo
  |  OtherCon : list AltCon -> UnfoldingInfo
  |  DFunUnfolding (df_bndrs : list Var)
                   (df_con   :  DataCon)
                   (df_args  : list CoreExpr) : UnfoldingInfo
  |  CoreUnfolding (uf_tmpl         : CoreExpr)
                   (uf_src          : UnfoldingSource)
                   (uf_is_top       : bool)
                   (uf_is_value     : bool)
                   (uf_is_conlike   : bool)
                   (uf_is_work_free : bool)
                   (uf_expandable   : bool)
                   (uf_guidance     : UnfoldingGuidance) : UnfoldingInfo.


Parameter getUnfoldingInfo : Unfolding -> UnfoldingInfo.
Parameter getUnfolding     : UnfoldingInfo -> Unfolding.

Parameter getCoreRule : CoreRuleInfo -> CoreRule.
Parameter getCoreRuleInfo : CoreRule -> CoreRuleInfo.

(*****)

Instance Default_RuleInfo : GHC.Err.Default RuleInfo :=
  GHC.Err.Build_Default _ (Mk_RuleInfo nil UniqDSet.emptyUniqDSet).

Instance Default_UnfoldingInfo : GHC.Err.Default UnfoldingInfo :=
  GHC.Err.Build_Default _ NoUnfolding.

Instance Default_Unfolding : GHC.Err.Default Unfolding :=
  GHC.Err.Build_Default _ (getUnfolding GHC.Err.default).


Instance Default_TickBoxOp : GHC.Err.Default TickBoxOp :=
  GHC.Err.Build_Default _ (TickBox GHC.Err.default GHC.Err.default).

Instance Default_CafInfo : GHC.Err.Default CafInfo :=
  GHC.Err.Build_Default _ MayHaveCafRefs.

Instance Default_Termination {r} : GHC.Err.Default (Termination r) :=
  GHC.Err.Build_Default _ Diverges.

Instance Default_DmdType : GHC.Err.Default DmdType :=
  GHC.Err.Build_Default _ (Mk_DmdType GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default_StrictSig : GHC.Err.Default StrictSig :=
  GHC.Err.Build_Default _ (Mk_StrictSig GHC.Err.default).

Instance Default_JointDmd `{GHC.Err.Default a} `{GHC.Err.Default b} : GHC.Err.Default (JointDmd a b) :=
  GHC.Err.Build_Default _ (JD GHC.Err.default GHC.Err.default).

Instance Default_Str {s} : GHC.Err.Default (Str s) :=
  GHC.Err.Build_Default _ Lazy.
Instance Default_Use {s} : GHC.Err.Default (Use s) :=
  GHC.Err.Build_Default _ Abs.

Instance Default_IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ (Mk_IdInfo GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default_TyCon : GHC.Err.Default TyCon :=
  GHC.Err.Build_Default _ (PrimTyCon GHC.Err.default GHC.Err.default nil tt tt GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default ).

Instance Default_RecSelParent : GHC.Err.Default RecSelParent :=
  GHC.Err.Build_Default _ (RecSelData GHC.Err.default).

Instance Default__Var : GHC.Err.Default Var := GHC.Err.Build_Default _ (Mk_Id GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__DataCon : GHC.Err.Default DataCon :=
 Err.Build_Default _ (MkData GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default nil nil nil nil tt tt nil tt nil nil GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default tt GHC.Err.default GHC.Err.default).
