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

Lemma foo {a} `{GHC.Base.Ord a} (n : nat) (t : RB a):
nearly_redblack n t -> notred t -> is_redblack n t.
Proof.
intros.
destruct n; destruct t.
- trivial.
- destruct c.
inversion H2.
inversion H1.
assumption.
inversion H3.
- destruct H1.
assumption.
inversion H1.
- destruct c.
inversion H1.
assumption.
inversion H2.
inversion H1.
assumption.
inversion H3.
Qed.

Hint Resolve foo.




Lemma lbalS_rb {a} `{GHC.Base.Ord a} (n : nat) (l : RB a) (x : a ) (r : RB a) :
nearly_redblack n l -> is_redblack (S n) r -> notred r -> is_redblack (S n) (lbalS l x r).
Proof.
intros Hl Hr Hr'.
destruct r.
-
inversion Hr.
-
destruct l.
simpl.
destruct c.
-- 
destruct r1.
---
constructor.
simpl;trivial.
exact Hr'.
inversion Hr.
exact H7.
exact Hr.
---
simpl in Hr'.
contradiction.
-- 
destruct r1.
---
destruct r2.
constructor.
inversion Hr.
exact H4.
inversion Hr.
constructor;simpl;trivial.
destruct c.
constructor;simpl;trivial.
inversion Hr.
constructor.
exact H4.
exact H4.
inversion Hr.
inversion H6.
constructor.
exact H13.
exact H14.
inversion Hr.
constructor.
exact H4.
constructor;simpl;trivial.
---
destruct c.
----
destruct r2.
inversion Hr.
inversion H4.
constructor;simpl;trivial.
constructor.
exact H6.
exact H13.
constructor.
exact H14.
exact H6.
destruct c.
inversion Hr.
constructor;simpl;trivial.
constructor;simpl;trivial.
inversion Hl.
exact H7.
inversion H7.
inversion H6.
constructor;trivial.
inversion Hr.
constructor;simpl;trivial.
constructor;simpl;trivial.
inversion Hl.
exact H7.
inversion H7.
inversion H4;trivial.
constructor.
inversion H4;trivial.
exact H6.
----
destruct r2.
inversion Hr.
constructor.
exact H6.
constructor;simpl;trivial.
destruct c.
inversion Hr.
constructor;simpl;trivial.
constructor.
inversion Hl.
exact H7.
inversion H7.
exact H4.
inversion H6.
constructor.
exact H13.
exact H14.
inversion Hr.
constructor.
inversion Hl.
exact H7.
inversion H7.
constructor;simpl;trivial.
--
simpl.
destruct c0.
---
constructor;simpl;trivial.
inversion Hl.
inversion H1.
constructor.
exact H8.
exact H9.
inversion H1.
constructor.
exact H4.
exact H6.
---
destruct c.
simpl in Hr'.
contradiction.
destruct r1.
----
destruct r2.
-----
inversion Hl;constructor.
exact H1.
inversion Hr.
constructor;simpl;trivial.
inversion H1.
inversion Hr.
constructor;simpl;trivial.
-----
destruct c;constructor;simpl;trivial.
inversion Hl.
constructor.
exact H1.
inversion Hr.
exact H5.
constructor.
inversion H1.
inversion H1.
inversion Hr.
inversion H6.
constructor;trivial.
inversion Hl.
exact H1.
inversion H1.
inversion Hr.
constructor;simpl;trivial.
----
destruct c.
-----
destruct r2.
inversion Hr.
inversion H4.
constructor;simpl;trivial.
constructor.
inversion Hl.
exact H15.
inversion H15.
exact H13.
constructor;trivial.
destruct c.
inversion Hr.
constructor;simpl;trivial.
constructor.
inversion Hl.
exact H7.
inversion H7.
exact H4.
inversion H6.
constructor;trivial.
inversion Hr.
constructor;simpl;trivial.
constructor.
inversion Hl.
exact H7.
inversion H7.
inversion H4.
exact H13.
constructor.
inversion H4.
exact H14.
exact H6.
-----
destruct r2.
inversion Hr.
constructor.
inversion Hl.
exact H7.
inversion H7.
constructor;simpl;trivial.
destruct c.
inversion Hr.
constructor;simpl;trivial.
constructor;simpl;trivial.
inversion Hl.
exact H7.
inversion H7.
inversion H6.
constructor;trivial.
inversion Hr.
constructor.
inversion Hl.
exact H7.
inversion H7.
constructor;simpl;trivial.
Qed.



Lemma append_arb_rb {a} `{GHC.Base.Ord a} (n:nat) (l r: RB a) : 
  is_redblack n l -> is_redblack n r ->
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
specialize (H20 H8).
specialize (H20 H14).
constructor.
exact H6.
inversion H20.
exact H24.
exact H9.
inversion H20.
exact H27.
specialize (H20 H8).
specialize (H20 H14).
inversion H20.
constructor.
exact H26.
exact H16.
exact H28.
exact H18.
constructor;trivial.
constructor;simpl;trivial.
apply H20;trivial.
intros.
simpl in H21.
contradiction.
--- (*APPEND RED BLACK*)
simpl.
set (r:= T B rl rx rr) in *.
specialize (IHlr r).
split.
destruct (IHlr n) as (_,IH).
inversion H1.
exact H10.
exact H2.
inversion H1.
constructor 2.
constructor.
exact H9.
apply IH.
exact H8.
simpl;trivial.
intro;contradiction.
--- (*APPEND BLACK RED*)
change (append _ _) with (T R (append (T B ll lx lr) rl) rx rr).
intros.
set (l:=T B ll lx lr) in *.
destruct (IHrl n) as (_,IH).
exact H1.
inversion H2.
exact H9.
split.
inversion H2.
constructor 2.
constructor.
apply IH.
simpl;trivial.
exact H6.
exact H10.
simpl.
intros.
contradiction.
--- (*APPEND BLACK BLACK*)
specialize (IHlr rl).
destruct n.
split.
inversion H1.
inversion H2.
intros.
destruct (IHlr n) as (IH,_).
inversion H1.
exact H8.
inversion H2.
exact H6.
split.
constructor.
simpl.

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
