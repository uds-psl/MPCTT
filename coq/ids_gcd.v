From Coq Require Import Arith Lia.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation pi1 := projT1.
Notation pi2 := projT2.

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
  enough (forall '(x,y), p x y) as H.
  { intros x y. apply (H (x,y)). } 
  refine (size_rec (fun '(x,y) => sigma x y) (fun '(x,y) IH => _)). cbn in IH.
  apply F. intros x' y' H. apply (IH (x',y')), H.
Defined.

Notation functional p := (forall x y z z', p x y z -> p x y z' -> z = z').

Definition gcd_rel (p: nat -> nat -> nat -> Prop) : Prop :=
  (forall y, p 0 y y) /\
  (forall x y z, p x y z -> p y x z) /\
  (forall x y z, x <= y ->  p x (y - x) z -> p x y z).

Inductive G : nat -> nat -> nat -> Prop :=
| G1 y : G 0 y y
| G2 x y z: G x y z -> G y x z
| G3 x y z : x <= y -> G x (y - x) z -> G x y z.

Fact G_gcd_rel :
  gcd_rel G.
Proof.
  split. exact G1. split. exact G2. exact G3.
Qed.

Fact G_cont p x y z :
  gcd_rel p -> G x y z -> p x y z.
Proof.
  intros (H1&H2&H3). hnf.
  induction 1 as [y|x y z _ IH|x y z H _ IH].
  - apply H1.
  - apply H2, IH.
  - apply H3; easy.
Qed.

Fact G_total :
  forall x y, Sigma z, G x y z.
Proof.
  refine (size_rec2 (fun x y => x + y) _).
  intros x y IH.
  destruct x.
  - exists y. apply G1.
  - destruct y.
    + exists (S x). apply G2, G1.
    + destruct (le_lt_dec x y) as [H|H].
      * specialize (IH (S x) (y - x)) as [z IH]. lia.
        exists z. apply G3. lia. exact IH.
      * specialize (IH (S y) (x - y)) as [z IH]. lia.
        exists z. apply G2, G3. lia. apply IH. 
Defined.

Definition gcd x y := pi1 (G_total x y).
Compute gcd 63 49.

Fact G_agree x y z p :
  gcd_rel p -> functional p -> (G x y z <-> p x y z).
Proof.
  intros H1 H2. split.
  - apply G_cont, H1.
  - intros H3.
    destruct (G_total x y) as [z' H].
    enough (z = z') as <- by exact H.
    eapply H2. exact H3.
    apply G_cont; assumption.
Qed.

Inductive G': nat -> nat -> nat -> Prop :=
| G'1: forall y, G' 0 y y
| G'2: forall x, G' (S x) 0 (S x)
| G'3: forall x y z, x <= y -> G' (S x) (y - x) z -> G' (S x) (S y) z
| G'4: forall x y z, y < x -> G' (x - y) (S y) z -> G' (S x) (S y) z.

Fact G'_inv :
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
  - reflexivity.
  - reflexivity.
  - destruct le_lt_dec as [H|H]. easy. exfalso. lia.
  - destruct le_lt_dec as [H|H]. exfalso. lia. easy.
Defined.

Fact G'_com x y z :
  G' x y z -> G' y x z.
Proof.
  induction 1 as [y|x|x y z H _ IH|x y z H _ IH].
  - destruct y; constructor.
  - apply G'1.
  - destruct (Nat.eq_dec x y) as [<-|H1].
    + apply G'3. exact H. revert IH.
      replace (x-x) with 0 by lia.
      intros -> % G'_inv. apply G'2.
    + apply G'4. lia. exact IH.
  - apply G'3. lia. exact IH. 
Qed.

Fact G'_gcd_rel :
  gcd_rel G'.
Proof.
  split. constructor.
  split. exact G'_com.
  intros x y z H.
  destruct x.
  - replace (y-0) with y by lia. easy.
  - destruct y.
    + lia.
    + cbn. apply G'3. lia.
Qed.

Fact G'_fun :
  functional G'.
Proof.
  intros x y z z'.
  induction 1 as  [y|x|x y z H _ IH|x y z H _ IH].
  all:intros H1%G'_inv; revert H1.
  - easy.
  - easy.
  - destruct le_lt_dec as [H1|H1]. exact IH. lia.
  - destruct le_lt_dec as [H1|H1]. lia. exact IH.
Qed.

Fact G_G' {x y z} :
  G x y z <-> G' x y z.
Proof.
  apply G_agree.
  - apply G'_gcd_rel.
  - apply G'_fun.
Qed.

Fact G_fun :
  functional G.
Proof.
  hnf. intros * H1%G_G' H2%G_G'.
  eapply G'_fun; eassumption.
Qed.
