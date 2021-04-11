From Coq Require Import Arith Lia.
Ltac refl := reflexivity.

Definition functional {X Y Z} (p: X -> Y -> Z -> Prop) :=
  forall x y z z', p x y z -> p x y z' -> z = z'.

Inductive G : nat -> nat -> nat -> Prop :=
| G1 y : G 0 y y
| G2 x y z: G x y z -> G y x z
| G3 x y z : x <= y -> G x (y - x) z -> G x y z.

Definition gcd_pred (p: nat -> nat -> nat -> Prop) : Prop :=
  (forall y, p 0 y y) /\
  (forall x y z, p x y z -> p y x z) /\
  (forall x y z, x <= y ->  p x (y - x) z -> p x y z).

Fact gcd_pred_G :
  gcd_pred G.
Proof.
  split. exact G1. split. exact G2. exact G3.
Qed.

Fact G_least p x y z :
  gcd_pred p -> G x y z -> p x y z.
Proof.
  intros (H1&H2&H3). hnf.
  induction 1 as [y|x y z _ IH|x y z H _ IH].
  - apply H1.
  - apply H2, IH.
  - apply H3; easy.
Qed.

Inductive G': nat -> nat -> nat -> Prop :=
| G'1: forall y, G' 0 y y
| G'2: forall x, G' (S x) 0 (S x)
| G'3: forall x y z, x <= y -> G' (S x) (y - x) z -> G' (S x) (S y) z
| G'4: forall x y z, y < x -> G' (x - y) (S y) z -> G' (S x) (S y) z.

Fact G'inv :
  forall x y z, G' x y z ->
           match x, y return Prop with
           | 0, y => z = y
           | S x, 0 => z = S x
           | S x, S y => if le_lt_dec x y
                        then G' (S x) (y - x) z
                        else G' (x - y) (S y) z
           end.
Proof.
  destruct 1 as [y|x|x y z H1 H2|x y z H1 H2].
  - refl.
  - refl.
  - destruct le_lt_dec as [H|H]. easy. exfalso. lia.
  - destruct le_lt_dec as [H|H]. exfalso. lia. easy.
Defined.

Fact G'com x y z :
  G' x y z -> G' y x z.
Proof.
  induction 1 as [y|x|x y z H _ IH|x y z H _ IH].
  - destruct y; constructor.
  - apply G'1.
  - destruct (Nat.eq_dec x y) as [<-|H1].
    + apply G'3. exact H. revert IH.
      replace (x-x) with 0 by lia.
      intros -> % G'inv. apply G'2.
    + apply G'4. lia. exact IH.
  - apply G'3. lia. exact IH. 
Qed.

Fact gcd_pred_G' :
  gcd_pred G'.
Proof.
  split. constructor.
  split. exact G'com.
  intros x y z H.
  destruct x.
  - replace (y-0) with y by lia. easy.
  - destruct y.
    + lia.
    + cbn. apply G'3. lia.
Qed.

Fact G'fun :
  functional G'.
Proof.
  intros x y z z'.
  induction 1 as  [y|x|x y z H _ IH|x y z H _ IH].
  all:intros H1%G'inv; revert H1.
  - easy.
  - easy.
  - destruct le_lt_dec as [H1|H1]. exact IH. lia.
  - destruct le_lt_dec as [H1|H1]. lia. exact IH.
Qed.

Fact G_G' {x y z} :
  G x y z -> G' x y z.
Proof.
  apply G_least, gcd_pred_G'.
Qed.

Fact G_fun :
  functional G.
Proof.
  hnf. intros * H1%G_G' H2%G_G'. revert H1 H2. apply G'fun.
Qed.
