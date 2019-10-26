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
Require Import ARNDefiniciones.

Print ARNDefiniciones.
(* Converted imports: *)

Require GHC.Base.
Require GHC.Err.
Require GHC.Types.
Import GHC.Base.Notations.



Definition rbal' {a} `{GHC.Base.Ord a} (l:RB a) (k:a) (r:RB a) :=
 match r with
 | T R b y (T R c z d) => T R (T B l k b) y (T B c z d)
 | T R (T R b y c) z d => T R (T B l k b) y (T B c z d)
 | _ => T B l k r
 end.

Definition lbalS {a} `{GHC.Base.Ord a} (l:RB a) (k:a) (r:RB a) :=
 match l with
 | T R a x b => T R (T B a x b) k r
 | _ =>
   match r with
   | T B a y b => rbal' l k (T R a y b)
   | T R (T B a y b) z c => T R (T B l k a) y (rbal' b z (makeRed c))
   | _ => T R l k r 
   end
 end.

Definition rbalS {a} `{GHC.Base.Ord a} (l:RB a) (k:a) (r:RB a) :=
 match r with
 | T R b y c => T R l k (T B b y c)
 | _ =>
   match l with
   | T B a x b => lbal (T R a x b) k r
   | T R a x (T B b y c) => T R (lbal (makeRed a) x b) y (T B c k r)
   | _ => T R l k r 
   end
 end.


Fixpoint append {a} `{GHC.Base.Ord a} (l:RB a) : RB a -> RB a :=
 match l with
 | E => fun r => r
 | T lc ll lx lr =>
   fix append_l (r:RB a) : RB a :=
   match r with
   | E => l
   | T rc rl rx rr =>
     match lc, rc with
     | R, R =>
       let lrl := append lr rl in
       match lrl with
       | T R lr' x rl' => T R (T R ll lx lr') x (T R rl' rx rr)
       | _ => T R ll lx (T R lrl rx rr)
       end
     | B, B =>
       let lrl := append lr rl in
       match lrl with
       | T R lr' x rl' => T R (T B ll lx lr') x (T B rl' rx rr)
       | _ => lbalS ll lx (T B lrl rx rr)
       end
     | B, R => T R (append_l rl) rx rr
     | R, B => T R ll lx (append lr r)
     end
   end
 end.

(*  x, (T B a y b as s) =>
               if x GHC.Base.< y : bool then balance (ins x a) y b else
               if x GHC.Base.> y : bool then balance a y (ins x b) else
               s
 *)
Fixpoint del {a} `{GHC.Base.Ord a} (x:a) (t:RB a) :=
 match t with
 | E => E
 | T _ a y b =>
    if x GHC.Base.< y : bool then 
      match a with
       | T B _ _ _ => lbalS (del x a) y b
       | _ => T R (del x a) y b
      end
    else 
    if x GHC.Base.> y : bool then 
      match b with
       | T B _ _ _ => rbalS a y (del x b)
       | _ => T R a y (del x b)
      end
    else append a b
 end.

Definition remove x t := makeBlack (del x t).

(* Lemmas a demostrar *)



Lemma append_arb_rb {a} `{GHC.Base.Ord a} (n:nat) (l r: RB a) : is_redblack n l -> is_redblack n r ->
 (nearly_redblack n (append l r)) /\
 (notred l -> notred r -> is_redblack n (append l r)).
Proof.
revert r n.
induction l as [| lc ll _ lx lr IHlr].
-
intros;simpl.
split.
constructor;exact H2.
intros.
exact H2.
-
induction r as [| rc rl IHrl rx rr _].
--
simpl.
intros.
split.
constructor.
exact H1.
destruct lc.
contradiction.
intros;exact H1.
--
destruct lc, rc.
--- (*APPEND RED RED*)
specialize (IHlr rl).
intros.
inversion H1.
inversion H2.
case (IHlr n).
exact H10.
exact H17.
intros.
split.
constructor 2.
simpl.
destruct (append lr rl).
constructor.
exact H9.
constructor.
simpl.
trivial.
exact H16.
inversion H19.
exact H21.
apply H20.
exact H8.
exact H14.
exact H18.
destruct c.
constructor.
inversion H19.
constructor 2.
exact H6.
inversion H21.
exact H25.
exact H9.
inversion H21.
exact H28.
constructor.
exact H6.
inversion H21.
admit.
exact H9.
inversion H21.
exact H24.
inversion H19.
constructor.
inversion H21.
exact H27.
exact H16.
inversion H21.
exact H29.
exact H18.
constructor.
admit.
exact H16.
inversion H21.
exact H26.
exact H18.
constructor.
exact H9.
constructor.
simpl.
trivial.
exact H16.
inversion H19.
exact H21.
inversion H21.
exact H18.
intros.
simpl in H21.
contradiction.
--- (*APPEND RED BLACK*)
admit.
--- (*APPEND BLACK RED*)
admit.
--- (*APPEND BLACK BLACK*)
admit.
Admitted.
destruct (append lr rl).
constructor.
 induction l as [| lc ll _ lx lr IHlr];
 [intro r; simpl
 |induction r as [| rc rl IHrl rx rr _];
   [simpl
   |destruct lc, rc;
     [specialize (IHlr rl); clear IHrl
     |simpl;
      assert (Hr:notred (T B rl rx rr)) by (simpl; trivial);
      set (r:= T B rl rx rr) in *; clearbody r; clear IHrl rl rx rr;
      specialize (IHlr r)
     |change (append _ _) with (T R (append (T B ll lx lr) rl) rx rr);
      assert (Hl:notred (T B ll lx lr)) by (simpl; trivial);
      set (l:=T B ll lx lr) in *; clearbody l; clear IHlr ll lx lr
     |specialize (IHlr rl); clear IHrl]]].



Lemma del_arb {a} `{GHC.Base.Ord a} (s:RB a) (x:a) (n:nat) : is_redblack (S n) s -> isblack s -> nearly_redblack n (del x s)
with del_rb s x n : is_redblack n s -> notblack s -> is_redblack n (del x s).
Admitted.

Instance remove_rb s x : redblack s -> redblack (remove x s).
Admitted.
