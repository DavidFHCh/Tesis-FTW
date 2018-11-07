(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Classes.
Require GHC.Err.
Require GHC.Types.
Import GHC.Classes.Notations.

(* Converted type declarations: *)

Inductive Color : Type := R : Color |  B : Color.

Inductive RB a : Type := E : RB a |  T : Color -> (RB a) -> a -> (RB a) -> RB a.

Arguments E {_}.

Arguments T {_} _ _ _ _.

Instance Default__Color : GHC.Err.Default Color := GHC.Err.Build_Default _ R.
(* Converted value declarations: *)

Definition red {a} : RB a -> RB a :=
  fun arg_0__ =>
    match arg_0__ with
    | T B a x b => T R a x b
    | _ => GHC.Err.error (GHC.Base.hs_string__ "invariance violation")
    end.

Definition member {a} `{GHC.Classes.Ord a} : a -> RB a -> GHC.Types.Bool :=
  fix member arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | x, E => GHC.Types.False
           | x, T _ tl y tr =>
               if x GHC.Classes.< y : bool then member x tl else
               if x GHC.Classes.> y : bool then member x tr else
               GHC.Types.True
           end.

Definition balance {a} : RB a -> a -> RB a -> RB a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | T R a x b, y, T R c z d => T R (T B a x b) y (T B c z d)
    | T R (T R a x b) y c, z, d => T R (T B a x b) y (T B c z d)
    | T R a x (T R b y c), z, d => T R (T B a x b) y (T B c z d)
    | a, x, T R b y (T R c z d) => T R (T B a x b) y (T B c z d)
    | a, x, T R (T R b y c) z d => T R (T B a x b) y (T B c z d)
    | a, x, b => T B a x b
    end.

Definition balleft {a} : RB a -> a -> RB a -> RB a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | T R a x b, y, c => T R (T B a x b) y c
    | bl, x, T B a y b => balance bl x (T R a y b)
    | bl, x, T R (T B a y b) z c => T R (T B bl x a) y (balance b z (red c))
    | _, _, _ => GHC.Err.patternFailure
    end.

Definition balright {a} : RB a -> a -> RB a -> RB a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | a, x, T R b y c => T R a x (T B b y c)
    | T B a x b, y, bl => balance (T R a x b) y bl
    | T R a x (T B b y c), z, bl => T R (balance (red a) x b) y (T B c z bl)
    | _, _, _ => GHC.Err.patternFailure
    end.

Definition insert {a} `{GHC.Classes.Ord a} : a -> RB a -> RB a :=
  fun x s =>
    let fix ins arg_0__
              := match arg_0__ with
                 | E => T R E x E
                 | (T B a y b as s) =>
                     if x GHC.Classes.< y : bool then balance (ins a) y b else
                     if x GHC.Classes.> y : bool then balance a y (ins b) else
                     s
                 | (T R a y b as s) =>
                     if x GHC.Classes.< y : bool then T R (ins a) y b else
                     if x GHC.Classes.> y : bool then T R a y (ins b) else
                     s
                 end in
    match ins s with
    | T _ a z b => T B a z b
    | _ => GHC.Err.patternFailure
    end.

Definition app {a} : RB a -> RB a -> RB a :=
  fix app arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | E, x => x
           | x, E => x
           | T R a x b, T R c y d =>
               match app b c with
               | T R b' z c' => T R (T R a x b') z (T R c' y d)
               | bc => T R a x (T R bc y d)
               end
           | T B a x b, T B c y d =>
               match app b c with
               | T R b' z c' => T R (T B a x b') z (T B c' y d)
               | bc => balleft a x (T B bc y d)
               end
           | a, T R b x c => T R (app a b) x c
           | T R a x b, c => T R a x (app b c)
           end.

Definition delete {a} `{GHC.Classes.Ord a} : a -> RB a -> RB a :=
  fun x t =>
    let del :=
      fix del arg_0__
            := match arg_0__ with
               | E => E
               | T _ a y b =>
                   if x GHC.Classes.< y : bool then delfromLeft a y b else
                   if x GHC.Classes.> y : bool then delfromRight a y b else
                   app a b
               end with delfromLeft arg_5__ arg_6__ arg_7__
                          := match arg_5__, arg_6__, arg_7__ with
                             | (T B _ _ _ as a), y, b => balleft (del a) y b
                             | a, y, b => T R (del a) y b
                             end with delfromRight arg_11__ arg_12__ arg_13__
                                        := match arg_11__, arg_12__, arg_13__ with
                                           | a, y, (T B _ _ _ as b) => balright a y (del b)
                                           | a, y, b => T R a y (del b)
                                           end for del in
    let delfromLeft :=
      fix del arg_0__
            := match arg_0__ with
               | E => E
               | T _ a y b =>
                   if x GHC.Classes.< y : bool then delfromLeft a y b else
                   if x GHC.Classes.> y : bool then delfromRight a y b else
                   app a b
               end with delfromLeft arg_5__ arg_6__ arg_7__
                          := match arg_5__, arg_6__, arg_7__ with
                             | (T B _ _ _ as a), y, b => balleft (del a) y b
                             | a, y, b => T R (del a) y b
                             end with delfromRight arg_11__ arg_12__ arg_13__
                                        := match arg_11__, arg_12__, arg_13__ with
                                           | a, y, (T B _ _ _ as b) => balright a y (del b)
                                           | a, y, b => T R a y (del b)
                                           end for delfromLeft in
    let delfromRight :=
      fix del arg_0__
            := match arg_0__ with
               | E => E
               | T _ a y b =>
                   if x GHC.Classes.< y : bool then delfromLeft a y b else
                   if x GHC.Classes.> y : bool then delfromRight a y b else
                   app a b
               end with delfromLeft arg_5__ arg_6__ arg_7__
                          := match arg_5__, arg_6__, arg_7__ with
                             | (T B _ _ _ as a), y, b => balleft (del a) y b
                             | a, y, b => T R (del a) y b
                             end with delfromRight arg_11__ arg_12__ arg_13__
                                        := match arg_11__, arg_12__, arg_13__ with
                                           | a, y, (T B _ _ _ as b) => balright a y (del b)
                                           | a, y, b => T R a y (del b)
                                           end for delfromRight in
    match del t with
    | T _ a y b => T B a y b
    | _ => E
    end.

(* External variables:
     bool GHC.Classes.Ord GHC.Classes.op_zg__ GHC.Classes.op_zl__
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.error GHC.Err.patternFailure
     GHC.Types.Bool GHC.Types.False GHC.Types.True
*)
