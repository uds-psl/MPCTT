Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
From Coq Require Import Arith Lia Eqdep_dec.
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Fact inr_injective X Y (y y': Y) :
  inr X y = inr y' -> y = y'.
Proof.
  intros H % (f_equal (fun a: X + Y => match a with
                                    | inl x => y
                                    | inr y => y
                                    end)).
  exact H.
Qed.

Inductive L (x: nat) : nat -> Type :=
| L1: L x (S x)
| L2: forall y z, L x y -> L y z -> L x z.

Fact L_complete x y :
  x < y -> L x y.
Proof.
  induction y as [|y IH].
  - lia.
  - intros H.
    destruct (Nat.eq_dec x y) as [<-|H1].
    + constructor.
    + eapply L2. 2:exact (L1 y).
      apply IH. lia.
Qed.

Definition L_elim (p: forall x y, L x y -> Type)
  : (forall x, p x (S x) (L1 x)) ->
    (forall x y z a b, p x y a -> p y z b -> p x z (L2 x y z a b)) ->
    forall x y a, p x y a
  := fun e1 e2 => fix f x _ a :=
       match a with
       | L1 _ => e1 x
       | L2 _ y z a b => e2 x y z a b (f x y a) (f y z b)
       end.

Fact L_sound {x y} :
  L x y -> x < y.
Proof.
  induction 1; lia.
Qed.

Fixpoint depth_left {x y} (a: L x y) : nat :=
  match a with
  | L1 _ => 1
  | L2 _ y z a b => S (depth_left a)
  end.

Goal
  L2 3 4 6 (L1 3) (L2 4 5 6 (L1 4) (L1 5))
<> L2 3 5 6 (L2 3 4 5 (L1 3) (L1 4)) (L1 5) .
Proof.
  intros [=] % (f_equal depth_left).
Qed.
  

Definition L_inv {x y} :
  L x y -> sum (y = S x) (Sigma z, prod (L x z) (L z y)).
Proof.
  destruct 1 as [|z y a b].
  - left; reflexivity.
  - right. exists z. easy.
Defined.

(** Injectivity of L2 *)

(* Cannot write a function L x y -> Sigma z, prod (L x z) (L z y) *)

Section L2_injective.
  Variable DPI_nat: forall (p: nat -> Type) n a b, Sig p n a = Sig p n b -> a = b.

  Fact L2_injective x y z a b a' b':
    L2 x z y a b = L2 x z y a' b' -> (a,b) = (a',b').
  Proof.
    intros H.
    apply (f_equal L_inv) in H. cbn in H.
    apply inr_injective in H.
    apply DPI_nat in H. 
    exact H.
  Qed.
End L2_injective.
