(* Default settings (from HsToCoq.Coq.Preamble) *)

(* Archivo que contiene la extension de las definiciones para eliminar elementos de un arbol rojinegro.

En varias funciones se agregaron casos extras para volver a las funciones totales, se cree que en las demostraciones esto
va causar ruido y se tengan que eliminar esos casos haciendo uso de admits, ya que aunque por construccion NO se puede caer
en esos casos, Coq pide que se demuestren, es posible que algo asi pase en el script de insercion con los dos casos que no se han podido demostrar.
 *)

(* 
Se entiende que esta es una estrucutura un tanto compleja y que la herramienta todavia esta en su infancia y no genere
codigo 100% proof ready *)
Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Err.
Require GHC.Types.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Color : Type := R : Color |  B : Color.

Inductive RB a : Type := E : RB a |  T : Color -> (RB a) -> a -> (RB a) -> RB a.

Arguments E {_}.

Arguments T {_} _ _ _ _.

Instance Default__Color : GHC.Err.Default Color := GHC.Err.Build_Default _ R.

(* Converted value declarations: *)

(* Pinta de rojo la raiz de un arbol
 *)
Definition red {a} `{GHC.Base.Ord a}: RB a -> RB a :=
  fun arg_0__ =>
    match arg_0__ with
    | T _ a x b => T R a x b
    | _ => E
    end.

Definition member {a} `{GHC.Base.Ord a}: a -> RB a -> bool :=
  fix member arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | x, E => false
           | x, T _ tl y tr =>
               if x GHC.Base.< y : bool then member x tl else
               if x GHC.Base.> y : bool then member x tr else
               true
           end.

(* balancea un arbol despues de insertar o eliminar, de tal manera que las invariantes no se violen
 *)
Definition balance {a} `{GHC.Base.Ord a}
   : RB a -> a -> RB a -> RB a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | T R a x b, y, T R c z d => T R (T B a x b) y (T B c z d)
    | T R (T R a x b) y c, z, d => T R (T B a x b) y (T B c z d)
    | T R a x (T R b y c), z, d => T R (T B a x b) y (T B c z d)
    | a, x, T R b y (T R c z d) => T R (T B a x b) y (T B c z d)
    | a, x, T R (T R b y c) z d => T R (T B a x b) y (T B c z d)
    | a, x, b => T B a x b
    end.

Definition balleft {a} `{GHC.Base.Ord a}
   : RB a -> a -> RB a -> RB a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | T R a x b, y, c => T R (T B a x b) y c
    | bl, x, T B a y b => balance bl x (T R a y b)
    | bl, x, T R (T B a y b) z c => T R (T B bl x a) y (balance b z (red c))
    | ti, x, tr => T R ti x tr (*caso extra para hacerlo total...*)
    end.

Definition balright {a} `{GHC.Base.Ord a}
   : RB a -> a -> RB a -> RB a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | a, x, T R b y c => T R a x (T B b y c)
    | T B a x b, y, bl => balance (T R a x b) y bl
    | T R a x (T B b y c), z, bl => T R (balance (red a) x b) y (T B c z bl)
    | ti, x, tr => T R ti x tr (*caso extra para hacerlo total...*)
    end.

(* Fixpoint appaux {a} `{GHC.Base.Ord a} (a: RB a) (b: RB a) :=
match a, b with  *)


(* maybe separating this function making an auxiliar fn(?)
 *)
Definition app {a} `{GHC.Base.Ord a}: RB a -> RB a -> RB a :=
  fun arg_0__ arg_1__ =>
         match arg_0__, arg_1__ with
           | E, x => x
           | x, E => x
           | a, b => appaux a b
         end.
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

Definition delete : a -> RB a -> RB a :=
  fun x t =>
    let del :=
      fix del arg_0__
            := match arg_0__ with
               | E => E
               | T _ a y b =>
                   if x GHC.Base.< y : bool then delfromLeft a y b else
                   if x GHC.Base.> y : bool then delfromRight a y b else
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
                   if x GHC.Base.< y : bool then delfromLeft a y b else
                   if x GHC.Base.> y : bool then delfromRight a y b else
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
                   if x GHC.Base.< y : bool then delfromLeft a y b else
                   if x GHC.Base.> y : bool then delfromRight a y b else
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
     bool GHC.Base.op_zg__ GHC.Base.op_zl__ GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.error GHC.Err.patternFailure GHC.Types.Bool
     GHC.Types.False a GHC.Types.True
*)
