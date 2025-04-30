Lemma elim_bool (p: bool -> Prop) :
  p true -> p false -> forall x, p x.
Proof.
  intros H1 H2. destruct x. exact H1. exact H2.
Qed.

Check elim_bool.

Lemma enum_bool :
  forall x:bool, x = true \/ x = false.
Proof.
  apply elim_bool.
  - tauto.
  - tauto.
Qed.

Lemma Kaminski (f: bool -> bool) :
  forall x, f (f (f x )) = f x.
Proof.
  apply elim_bool.
  - destruct (enum_bool (f true)) as [H|H].
    + congruence.
    + destruct (enum_bool (f false)) as [H1|H1].
      * congruence.
      * congruence.
  - destruct (enum_bool (f false)) as [H1|H1].
    + destruct (enum_bool (f true)) as [H|H].
      * congruence.
      * congruence.
    + congruence.
Qed.

Lemma elim_nat (p: nat -> Prop) :
  p 0 -> (forall x, p x -> p (S x)) -> forall x, p x.
Proof.
  intros H F.
  induction x.
  - exact H.
  - exact (F x IHx).
Qed.
Lemma CA_nat (p: nat -> Prop) :
  p 0 -> (forall x, p (S x)) -> forall x, p x.
Proof.
  intros H F.
  apply elim_nat.
  - exact H.
  - intros x _. apply F.
Qed.

Lemma nat_eq :
  forall x y:nat, x = y \/ x <> y.
Proof.
  refine (elim_nat _ _ _).
  - apply CA_nat.
    + tauto.
    + intros x. right. congruence.
  - intros x IHx.
    apply CA_nat.
    + right. congruence.
    + intros y.
      destruct (IHx y) as [H|H].
      * left. congruence.
      * right. contradict H. congruence.
Qed.

Lemma elim_pair X Y (p: X * Y -> Prop) :
  (forall x y, p (x,y)) -> forall a, p a.
Proof.
  intros F.
  destruct a as [x y].
  apply F.
Qed.

Lemma eta_pair X Y :
  forall a: X * Y, a = (fst a, snd a).
Proof.
  apply elim_pair.
  intros x y.
  reflexivity.
Qed.

Definition card_le_two X :=
  forall x y z : X, x = y \/ x = z \/ y = z.

Fact bool_card :
  card_le_two bool.
Proof.
  hnf.
  refine (elim_bool _ _ _).
  - refine (elim_bool _ _ _).
    + auto.
    + refine (elim_bool _ _ _); auto.
  - refine (elim_bool _ _ _).
    + refine (elim_bool _ _ _); auto.
    + auto.
Qed.

Fact nat_card :
  ~ card_le_two nat.
Proof.
  intros F.
  specialize (F 0 1 2).
  destruct F as [H|[H|H]].
  - congruence.
  - congruence.
  - congruence.
Qed.

Goal nat <> bool.
Proof.
  intros H.
  apply nat_card.
  rewrite H.
  apply bool_card.
Qed.

Inductive void: Type := .
Inductive unit: Type := U.

Lemma elim_void (Z: Prop):
  void -> Z.
Proof.
  intros a.
  destruct a.
Qed.

Lemma elim_unit (p: unit -> Prop) :
  p U -> forall x, p x.
Proof.
  intros H.
  destruct x.
  exact H.
Qed.
