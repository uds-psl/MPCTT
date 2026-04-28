From Stdlib Require Import Lia.

Fixpoint ind_nat (p: nat -> Prop)
  (a: p 0) (f: (forall n, p n -> p (S n)))
  (n : nat) : p n.
Proof.
  destruct n.
  - exact a.
  - exact (f n (ind_nat p a f n)).
Qed.

Fact discriminate_nat (p: nat -> Prop) :
  p 0 -> (forall n, p (S n)) -> forall n, p n.
Proof.
  intros a f [|n].
  - exact a.
  - exact (f n).
Qed.

Fact discriminate_pair (X Y: Type) (p: X * Y -> Prop) :
  (forall x y, p (x,y)) -> forall a, p a.
Proof.
  intros f [x y]. exact (f x y).
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
  refine (ind_nat _ _ _).
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

(* Eta law for pairs *)

Goal forall X Y, forall p: X * Y -> Prop,
    (forall x y, p (x,y)) -> forall a, p a.
Proof.
  intros * f.
  refine (discriminate_pair _ _ _ _). exact f.
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
  refine (ind_nat _ _ _); cbn; easy.
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
  refine (ind_nat _ _ _); cbn. easy.
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

Fact plus_and x y :
  x + y = 0 <-> x = 0 /\ y = 0.
Proof.
  split.
  - destruct x. easy. easy.
  - intros [-> ->]. easy.
Qed.

Goal forall x y, x = y <-> (x - y) + (y - x) = 0.
Proof.
  intros x y.
  rewrite plus_and.  (* we rewrite with a propsitional equivalence *)
  split.
  - intros <-. split; apply le_refl.
  - intros [H1 H2]. apply le_antisym; assumption.
Qed.
  
