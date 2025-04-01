From Stdlib Require Import Arith Lia.

Definition size_rec {X: Type} (sigma: X -> nat) {p: X -> Type} :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) ->
  (forall x, p x).
Proof.
  intros F.
  enough (forall n x, sigma x < n -> p x) as H.
  { intros x. apply (H (S (sigma x))). lia. }
  induction n as [|n IH]; intros x H.
  - exfalso. lia.
  - apply F. intros y H1. apply IH. lia.
Defined.

Definition size_rec2 {X Y: Type} (sigma: X -> Y -> nat) {p: X -> Y -> Type} :
  (forall x y, (forall x' y', sigma x' y' < sigma x y -> p x' y') -> p x y) ->
  (forall x y, p x y).
Proof.
  intros F.
  pose (p' a := p (fst a) (snd a)).
  pose (sigma' a := sigma (fst a) (snd a)).
  enough (forall a, p' a) as H.
  { intros x y. exact (H (x,y)). } 
  refine (size_rec sigma' _ ).
  intros [x y] IH.
  apply F. intros x' y'. cbn.
  specialize (IH (x',y')). exact IH.
Defined.

Definition gcd_rec (p: nat -> nat -> Type) :
  (forall y, p 0 y) ->
  (forall x, p (S x) 0) ->
  (forall x y, 0 < x <= y -> p x (y - x) -> p x y) ->
  (forall x y, 0 < y < x -> p (x - y) y -> p x y) ->
  forall x y, p x y.
Proof.
  intros e1 e2 e3 e4.
  refine (size_rec2 (fun x y => x + y) _).
  intros [|x] y IH.
  - apply e1.
  -  destruct y as [|y].
     + apply e2.
     + destruct (le_lt_dec x y) as [H|H].
       * apply e3. lia. apply IH. lia.
       * apply e4. lia. apply IH. lia.
Qed.
  
  
