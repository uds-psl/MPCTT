(** This file collects definitions of inductive types
    and their eliminators from MPCTT as used in ICL 2026.
    The goal is to bring across the master plan behind inductive types. 
    We forget about implicit arguments and syntactic sugar
    and try to make the definitions look as uniform as possible.
    Two take homes are: 
    - The types of eliminators
      follow from the inductive type definitions.            
    - The defining equations of the eliminators
      follow from the type of the eliminators.
    - The eliminators are best obtained in proof mode
      using discrimination patterns.     
    - There is great beauty.    
*)

Module Box.
Inductive bool : Type :=
| true : bool
| false : bool.

Fixpoint elim_bool (p: bool -> Type) :
  p true ->
  p false ->
  forall b, p b.
Proof.
  intros e1 e2.
  intros [|].
  - exact e1.
  - exact e2.
Defined.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint elim_nat (p: nat -> Type) :
  p O ->
  (forall n, p n -> p (S n)) ->
  forall n, p n.
Proof.
  intros e1 e2.
  intros [|n].
  - exact e1.
  - exact (e2 n (elim_nat p e1 e2 n)).
Defined.

Definition match_nat_simply_typed
  : forall Z:Type, nat -> Z -> (nat -> Z) -> Z
  := fun Z n e1 e2 => elim_nat (fun _ => Z) e1 (fun n _ => e2 n) n.

Compute match_nat_simply_typed nat (S (S O)) O (fun n => n).

Inductive list (X: Type) : Type :=
| Nil : list X
| Cons : X -> list X -> list X.

Fixpoint elim_list (X : Type) (p: list X -> Type) :
  p (Nil X) ->
  (forall x A, p A -> p (Cons X x A)) ->
  forall A, p A.
Proof.
  intros e1 e2.
  intros [|x A].
  - exact e1.
  - exact (e2 x A (elim_list X p e1 e2 A)).
Defined.

Inductive exp : Type :=
| Con : nat -> exp
| Var : nat -> exp
| Sub : exp -> exp -> exp.

Fixpoint elim_exp (p: exp -> Type) :
  (forall x, p (Con x)) ->
  (forall x, p (Var x)) ->
  (forall a1 a2, p a1 -> p a2 -> p (Sub a1 a2)) ->
  forall a, p a.
Proof.
  intros e1 e2 e3.
  intros [x|x|a1 a2].
  - exact (e1 x).
  - exact (e2 x).
  - exact (e3 a1 a2 (elim_exp p e1 e2 e3 a1) (elim_exp p e1 e2 e3 a2)).
Defined.

Inductive pair (X Y : Type) : Type :=
| Pair : X -> Y -> pair X Y.

Definition elim_pair (X Y : Type) (p: pair X Y -> Type) :
  (forall x y, p (Pair X Y x y)) -> forall a, p a.
Proof.
  intros e1.
  intros [x y]. exact (e1 x y).
Defined.

Inductive sig (X: Type) (q: X -> Type) : Type :=
| Sig : forall x, q x -> sig X q.

Definition elim_sig (X: Type) (q: X -> Type) (p: sig X q -> Type) :
  (forall x y, p (Sig X q x y)) -> forall a, p a.
Proof.
  intros e1.
  intros [x y]. exact (e1 x y).
Defined.

Inductive sum (X Y: Type) : Type :=
| L :  X -> sum X Y
| R :  Y -> sum X Y.

Definition elim_sum (X Y : Type) (p: sum X Y -> Type) :
  (forall x, p (L X Y x)) ->
  (forall y, p (R X Y y)) ->
  forall a, p a.
Proof.
  intros e1 e2.
  intros [x|y].
  - exact (e1 x).
  - exact (e2 y).
Defined.

Inductive unit : Type :=
| U : unit.

Definition elim_unit (p: unit -> Type) :
  p U -> forall a, p a.
Proof.
  intros e1.
  intros []. exact e1.
Defined.

Inductive void : Type := .

Definition elim_void (Z: Type) :
  False -> Z.
Proof.
  intros [].
Defined.

Inductive False : Prop := .

Definition elim_False (Z: Type) :
  False -> Z.
Proof.
  intros [].
Defined.

Inductive or (X Y: Prop) : Prop :=
| left :  X -> or X Y
| right :  Y -> or X Y.

Definition elim_or (X Y : Prop) (Z: Prop) :
  (X -> Z) ->
  (Y -> Z) ->
  or X Y -> Z.
Proof.
  intros e1 e2.
  intros [x|y].
  - exact (e1 x).
  - exact (e2 y).
Defined.

Inductive eq (X: Type) (x: X) : X -> Prop :=
| Q : eq X x x.

Definition elim_eq X (x:X) (p: forall y, eq X x y -> Type) :
  p x (Q X x) -> forall y e, p y e.
Proof.
  intros e1.
  intros _ [].
  exact e1.
Defined.

Definition elim_eq' X (x:X) (p: X -> Type) :
  p x -> forall y, eq X x y -> p y.
Proof.
  intros e1.
  intros _ [].
  exact e1.
Defined.

Inductive le (x: nat) : nat -> Prop :=
| leR :   le x x 
| leS y : le x y -> le x (S y).

Fixpoint elim_le (x: nat) (p: nat -> Prop) :
  p x ->
  (forall y, p y -> p (S y)) ->
  forall y, le x y -> p y.
Proof.
  intros e1 e2.
  intros _ [|y a].
  - exact e1.
  - exact (e2 y (elim_le x p e1 e2 y a)).
Defined.

End Box.
(* We will use the predefined [nat] now *)

Inductive G : nat -> nat -> nat -> Prop :=
| G0 z     : G 0 z z
| G1 x y z : G x y z -> G y x z
| G2 x y z : x <= y -> G x (y - x) z -> G x y z.

Fixpoint elim_G (p: nat -> nat -> nat -> Prop) :
  (forall z, p 0 z z) ->
  (forall x y z, p x y z -> p y x z) ->
  (forall x y z, x <= y -> p x (y - x) z -> p x y z) ->
  (forall x y z, G x y z -> p x y z).
Proof.
  intros e1 e2 e3.
  intros _ _ _ [z|x y z a|x y z h a].
  - exact (e1 z).
  - exact (e2 x y z (elim_G p e1 e2 e3 x y z a)).
  - exact (e3 x y z h (elim_G p e1 e2 e3 x (y - x) z a)).
Defined.

(* Linear search types featuring higher order recursion *)

Inductive L (p: nat -> Prop) : nat -> Type :=
| CL n : (~p n -> L p (S n)) -> L p n.

Fixpoint elim_L (p: nat -> Prop) (q: nat -> Type) :
  (forall n, (~p n -> q (S n)) ->  q n) -> (forall n, L p n -> q n).
Proof.
  intros e.
  intros _ [n phi].
  exact (e n (fun h => elim_L p q e (S n) (phi h))).
Defined.

(* Lowering to Prop using a quasi parameter *)

Inductive T (p: nat -> Prop) (n: nat) : Prop :=
| C : (~p n -> T p (S n)) -> T p n.

Fixpoint elim_T (p: nat -> Prop) (q: nat -> Type) :
  (forall n, (~p n -> q (S n)) ->  q n) -> (forall n, T p n -> q n).
Proof.
  intros e.
  intros n [phi].
  exact (e n (fun h => elim_T p q e (S n) (phi h))).
Defined.
