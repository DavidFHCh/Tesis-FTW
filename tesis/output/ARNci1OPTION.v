(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Coq.Init.Nat.

(* Converted imports: *)

Require GHC.Err.
Require GHC.Types.


(* Converted type declarations: *)

Inductive Color : Type := R : Color |  B : Color.

Inductive RB a : Type := E : RB a |  T : Color -> option(RB a) -> a -> option(RB a) -> RB a.

Arguments E {_}.

Arguments T {_} _ _ _ _.


Fixpoint leb n m : bool :=
  match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
  end.

Definition ltb n m := leb (S n) m.

(* Converted value declarations: *)

Definition red : option(RB nat) -> option(RB nat) :=
  fun arg_0__ =>
    match arg_0__ with
    | Some(T B a x b) => Some(T R a x b)
    | _ => None
    end.
(*
Definition member : nat -> option(RB nat) -> bool :=
  fix member arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | x, Some(E) => false
           | x, Some(T _ tl y tr) =>
               if ltb x y : bool then member x tl else
               if ltb y x : bool then member x tr else
               true
           | _,_ => false
           end.
*)
Definition balance
   : option(RB nat) -> nat -> option(RB nat) -> (RB nat) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Some(T R a x b), y, Some(T R c z d) => T R (Some (T B a x b)) y (Some (T B c z d))
    | Some(T R (Some(T R a x b)) y c), z, d => T R (Some (T B a x b)) y (Some (T B c z d))
    | Some(T R a x (Some(T R b y c))), z, d => T R (Some (T B a x b)) y (Some (T B c z d))
    | a, x, Some(T R b y (Some (T R c z d))) => T R (Some(T B a x b)) y (Some(T B c z d))
    | a, x, Some(T R (Some (T R b y c)) z d) => T R (Some(T B a x b)) y (Some(T B c z d))
    | a, x, b => T B a x b
    end.

Definition balleft
   : option (RB nat) -> nat -> option(RB nat) -> option(RB nat) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Some (T R a x b), y, c => Some(T R (Some(T B a x b)) y c)
    | bl, x, Some(T B a y b) => Some(balance bl x (Some(T R a y b)))
    | bl, x, Some(T R (Some (T B a y b)) z c) => Some(T R (Some(T B bl x a)) y (Some(balance b z (red c))))
    | _, _, _ => None
    end.

Definition balright
   : option(RB nat) -> nat -> option(RB nat) -> option(RB nat) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | a, x, Some(T R b y c) => Some(T R a x (Some(T B b y c)))
    | Some(T B a x b), y, bl => Some(balance (Some(T R a x b)) y bl)
    | Some(T R a x (Some(T B b y c))), z, bl => Some(T R (Some(balance (red a) x b)) y (Some(T B c z bl)))
    | _, _, _ => None
    end.

Definition insert : nat -> option(RB nat) -> option (RB nat) :=
  fun x s =>
    let fix ins arg_0__
              := match arg_0__ with
                 | E => T R (Some E) x (Some E)
                 | (T B a y b as s) =>
                     if ltb x y : bool then balance (ins a) y b else
                     if ltb y x : bool then balance a y (ins b) else
                     s
                 | (T R a y b as s) =>
                     if ltb x y : bool then T R (ins a) y b else
                     if ltb y x : bool then T R a y (ins b) else
                     s
                 end in
    match ins s with
    | T _ a z b => T B a z b
    | _ => GHC.Err.patternFailure
    end.

Definition app : RB nat -> RB nat -> RB nat :=
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

Definition delete : nat -> RB nat -> RB nat :=
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
     bool GHC.Classes.op_zg__ GHC.Classes.op_zl__ GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.error GHC.Err.patternFailure GHC.Types.Bool
     GHC.Types.False nat GHC.Types.True
*)
