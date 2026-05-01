From Stdlib Require Import Lia.

Fixpoint induction_nat (p: nat -> Prop)
  (a: p 0) (f: (forall n, p n -> p (S n)))
  (n : nat) : p n.
Proof.
  destruct n.
  - exact a.
  - exact (f n (induction_nat p a f n)).
Qed.

Fact discriminate_nat (p: nat -> Prop) :
  p 0 -> (forall n, p (S n)) -> forall n, p n.
Proof.
  intros a f [|n].
  - exact a.
  - exact (f n).
Qed.

(** We prove [S n <> n] using the induction rule
    and the  constructor laws for [nat] as lemmas *)

Fact nat_S_O n :
  S n <> 0.
Proof.
  lia.
Qed.

Fact nat_S_injective x y :
  S x = S y -> x = y.
Proof.
  lia.
Qed.

Goal forall n, S n <> n.
Proof.
  refine (induction_nat _ _ _).
  - apply nat_S_O.
  - intros n IH H. apply IH. apply nat_S_injective, H.
Qed.

Goal forall n, S n <> n.
Proof.
  lia.
Qed.

Goal forall n, S n <> n.
Proof.
  induction n; congruence.
  (* congruence knows the constructor laws *)
Qed.

(** Order on numbers *)

Notation "x <= y" := (x - y = 0) : nat_scope.
Arguments Nat.sub : simpl nomatch.

Fact le_refl :
  forall x, x <= x.
Proof.
  induction x; cbn; easy.
Qed.

Goal forall x, x <= x.
Proof.
  refine (induction_nat _ _ _); cbn; easy.
Qed.

Goal forall x y z, x <= y -> y <= z -> x <= z.
Proof.
  induction x; cbn. easy. (* easy knows the first constructor law *)
  destruct y; cbn. easy. (* easy knows the first constructor law *)
  destruct z; cbn. easy. (* easy knows the first constructor law *)
  apply IHx.
Qed.

Goal forall x y z, x <= y -> y <= z -> x <= z.
Proof.
  refine (induction_nat _ _ _); cbn. easy.
  intros x IH.
  refine (discriminate_nat _ _ _); cbn. easy.  (* easy knows the first constructor law *)
  intros y.
  refine (discriminate_nat _ _ _); cbn. easy.
  apply IH.
Qed.

Fact le_antisym :
  forall x y, x <= y -> y <= x -> x = y.
Proof.
  induction x as [|x IH]; cbn.
  - intros [|y]; cbn; easy.
  - intros [|y]; cbn. easy.
    intros H1 H2.
    f_equal.
    apply IH; assumption.
Qed.

Goal forall x y, x <= y \/ S y <= x.
Proof.
  induction x; cbn.
  - auto.
  - destruct y; cbn.
    + auto.
    + exact (IHx y).
Qed.

(** Equality decider for numbers *)

Fact plus_and x y :
  x + y = 0 <-> x = 0 /\ y = 0.
Proof.
  split.
  - destruct x; cbn. easy. easy.
  - intros [-> ->]; cbn. reflexivity.
Qed.

Goal forall x y, x = y <-> (x - y) + (y - x) = 0.
Proof.
  intros x y.
  rewrite plus_and.  (* we rewrite with a propsitional equivalence *)
  split.
  - intros <-. split; apply le_refl.
  - intros [H1 H2]. apply le_antisym; assumption.
Qed.

(** Pairs *)

Fact discriminate_pair {X Y: Type} (p: X * Y -> Prop) :
  (forall x y, p (x,y)) -> forall a, p a.
Proof.
  intros f [x y]. exact (f x y).
Qed.

Fact eta X Y :
  forall a: X * Y, a = (fst a, snd a).
Proof.
   refine (discriminate_pair _ _).
  cbn. reflexivity.
Qed.

Definition M_pair {X Y Z} (f: X -> Y -> Z) (a: X * Y) : Z
  := match a with (x,y) => f x y end.

Fact pair_injective {X Y x y} {x':X} {y':Y} :
  (x,y) = (x',y') -> x = x' /\ y = y'.
Proof.
  intros e.
  change (M_pair (fun x y => x = x' /\ y = y') (x,y)).
  rewrite e. cbn. easy.
Qed.

Goal forall a, a = (0,0) \/ a <> (0,0).
Proof.
  refine (discriminate_pair _ _).
  refine (discriminate_nat _ _ _).
  - refine (discriminate_nat _ _ _).
    + left. reflexivity.
    + right. intros H.
      apply pair_injective in H.
      apply (nat_S_O n).
      apply H.
  - refine (discriminate_nat _ _ _).
    + right. intros H.
      apply pair_injective in H.
      apply (nat_S_O 0).
      apply H.
    + right. intros H.
      apply pair_injective in H.
      eapply (nat_S_O (S n)).
      apply H.
Qed.

Goal forall a, a = (0,0) \/ a <> (0,0).
Proof.
  intros [[|x] [|y]]; cbn.
  - left. reflexivity.
  - right. easy.
  - right. easy.
  - right. easy.
Qed.

Goal forall a, a = (0,0) \/ a <> (0,0).
Proof.
  intros [[|x] [|y]]; intuition easy.
Qed.

Fact nat_eq :
  forall x y : nat, x = y \/ x <> y.
Proof.
  refine (induction_nat _ _ _).
  - refine (discriminate_nat _ _ _).
    + left; reflexivity.
    + right. symmetry. apply nat_S_O.
  - intros x IH.
    refine (discriminate_nat _ _ _).
    + right. apply nat_S_O.
    + intros y. destruct (IH y) as [-> |H].
      * left; reflexivity.
      * right. contradict H. apply nat_S_injective, H.
Qed.

Goal forall a b: nat*nat, a = b \/ a <> b.
Proof.
  intros [x y] [x' y'].
  destruct (nat_eq x x') as [-> |Hx].
  - destruct (nat_eq y y') as [-> |Hy].
    + left. reflexivity.
    + right. contradict Hy.
      apply pair_injective in Hy. apply Hy.
  - right. contradict Hx.
    apply pair_injective in Hx. apply Hx.
Qed.

