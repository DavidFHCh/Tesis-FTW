(* DEMAND midamble file *)

Require Import GHC.Nat.
Require Import Omega.

Ltac solve_not_zero_N := match goal with 
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] => 
    unfold GHC.Base.op_zeze__ in H;
    unfold GHC.Base.Eq_Char___ in H;
    simpl in H;
    apply N.eqb_neq in H end;
    zify;
    omega.
Ltac simpl_not_zero := match goal with 
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] =>
  unfold GHC.Base.op_zeze__ in H;
    unfold Eq_nat in H;
    simpl in H;
  apply Nat.eqb_neq in H end.
Ltac solve_error_sub :=
  unfold error_sub;
  let Hltb := fresh in
  let HeqHltb := fresh in
  match goal with 
    [ |- context[ Nat.ltb ?x (Pos.to_nat 1) ] ] =>
    remember (Nat.ltb x (Pos.to_nat 1)) as Hltb eqn:HeqHltb; 
      destruct Hltb;
      symmetry in HeqHltb;
      try (rewrite Nat.ltb_lt in HeqHltb);
      try (rewrite Nat.ltb_ge in HeqHltb);
      try solve [zify; omega]
  end.

Ltac distinguish := split; intros; unfold not; intros [? ?]; discriminate.
Ltac solve_mkWorkerDemand := Tactics.program_simpl; simpl_not_zero; solve_error_sub.

Ltac solve_dmdTransform := Tactics.program_simpl; try solve_mkWorkerDemand; try distinguish.


Instance Unpeel_StrictSig : Prim.Unpeel StrictSig DmdType :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_StrictSig y => y end) Mk_StrictSig.

(* Definitions that we cannot process, see edits file for details. *)

Axiom lubUse : UseDmd -> UseDmd -> UseDmd.
Axiom lubArgUse :  Use UseDmd ->  Use UseDmd ->  Use UseDmd.
Axiom bothUse : UseDmd -> UseDmd -> UseDmd.
Axiom bothArgUse :  Use UseDmd ->  Use UseDmd ->  Use UseDmd.

(*
Axiom bothStr : StrDmd -> StrDmd -> StrDmd.
Axiom lubStr : StrDmd -> StrDmd -> StrDmd.
Axiom splitFVs : bool -> DmdEnv -> (DmdEnv * DmdEnv)%type.
Axiom postProcessDmdEnv : DmdShell -> DmdEnv -> DmdEnv.
Axiom peelManyCalls : GHC.Num.Int -> CleanDemand -> DmdShell.
Axiom toCleanDmd : Demand -> unit -> (DmdShell * CleanDemand)%type.
Axiom trimToType : Demand -> TypeShape -> Demand.
Axiom dmdTransformDictSelSig : StrictSig -> CleanDemand -> DmdType.
Axiom strictifyDictDmd : unit -> Demand -> Demand.
Axiom dmdTransformDataConSig  : BasicTypes.Arity -> StrictSig -> CleanDemand -> DmdType.
Axiom addCaseBndrDmd : Demand -> list Demand -> list Demand.
Axiom bothUse : UseDmd -> UseDmd -> UseDmd.
Axiom zap_usg : KillFlags -> UseDmd -> UseDmd.
*)

(* Example of successful mutual recursion. Not sure that we can automate this *)
(*
Definition isUsedMU' isUsedU (au : ArgUse) : bool :=
    match au with
      | Abs => true
      | Mk_Use One _ => false
      | Mk_Use Many u => isUsedU u
    end.

Fixpoint isUsedU (ud : UseDmd) : bool :=
    match ud with
      | Used => true
      | UHead => true
      | UProd us => Data.Foldable.all (isUsedMU' isUsedU) us
      | UCall One _ => false
      | UCall Many _ => true
    end.

Definition isUsedMU := isUsedMU' isUsedU.

Definition markReusedDmd' markReused : ArgUse -> ArgUse :=
  fun arg_258__ =>
    match arg_258__ with
      | Abs => Abs
      | Mk_Use _ a => Mk_Use Many (markReused a)
    end.

Fixpoint markReused (x : UseDmd) : UseDmd :=
    match x with
      | UCall _ u => UCall Many u
      | UProd ux => UProd (GHC.Base.map (markReusedDmd' markReused) ux)
      | u => u
    end.
Definition markReusedDmd := markReusedDmd' markReused.
*)

(* size metric, incase it is useful *)

Definition Str_size {a} (f : a -> nat) (x : Str a) : nat :=
  match x with
  | Lazy => 0
  | Mk_Str _ s => f s
  end.

Fixpoint StrDmd_size (s1 : StrDmd): nat :=
  match s1 with
  | HyperStr => 0
  | SCall s => Nat.add 1 (StrDmd_size s)
  | SProd ss => List.fold_left Nat.add (List.map (Str_size StrDmd_size) ss) 1
  | HeadStr => 0
  end.

Definition ArgStrDmd_size := Str_size StrDmd_size.
