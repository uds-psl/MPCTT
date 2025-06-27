From Stdlib Require Import Lia.

(** Arithmetic GCD predicate *)

Definition divides n x : Prop := exists k, x = k * n.
Notation "( n | x )" := (divides n x) (at level 0) : nat_scope.

Definition gamma x y z : Prop :=
  forall n, (n | z) <-> (n | x) /\ (n | y).

(** Inductive GCD predicate *)

Inductive G : nat -> nat -> nat -> Prop :=
| G_zero y : G 0 y y
| G_sym x y z : G x y z -> G y x z
| G_sub x y z : x <= y -> G x (y - x) z -> G x y z.

Fact gamma_zero y :
  gamma 0 y y.
Proof.
  intros n.
  enough (n | 0) by tauto.
  exists 0. reflexivity.
Qed.

Fact gamma_sym x y z :
  gamma x y z -> gamma y x z.
Proof.
  unfold gamma. firstorder.
Qed.

Fact divides_sub x y n :
  x <= y -> (n | x) -> (n | y) <->  (n | y - x).
Proof.
  intros H [k ->]. split.
  - intros [l ->]. exists (l-k). nia.
  - intros [l H1]. exists (k + l). nia.
Qed.

Fact gamma_sub x y z :
  x <= y -> gamma x (y - x) z -> gamma x y z.
Proof.
  intros H H1 n.
  specialize (H1 n).
  generalize (divides_sub _ _ n H).
  tauto.
Qed.

Fact G_gamma x y z :
  G x y z -> gamma x y z.
Proof.
  induction 1 as [y|x y z _ IH|x y z H _ IH].
  - apply gamma_zero.
  - revert IH. apply gamma_sym.
  - revert H IH. apply gamma_sub.
Qed.

(*** Procedural Specification *)

Definition Gamma f (x y: nat) : nat :=
  if x then y
  else if y then x
       else  if x - y then f x (y - x)
             else f (x - y) y.

Fixpoint gcd' n x y :=
  match n with
  | 0 => 0
  | S n => Gamma (gcd' n) x y
  end.

Definition gcd x y := gcd' (S x + y) x y.

Compute gcd 16 24.
Compute gcd 60 48.
Compute gcd 175 5.


Definition sat (p: nat -> nat -> nat -> Prop) f := forall x y, p x y (f x y).
Notation "f == f'" := (forall x y, f x y = f' x y) (at level 70).

Fact gcd'_index_independence n1 n2 x y :
  n1 > x + y -> n2 > x + y -> gcd' n1 x y = gcd' n2 x y.
Proof.
  induction n1 as [|n1 IH] in n2, x, y|-*; intros H1 H2.
  - exfalso; lia.
  - destruct n2. exfalso; lia.
    cbn. unfold Gamma.
    destruct x. reflexivity.
    destruct y. reflexivity.
    destruct (S x - S y) as [|d] eqn:H3; apply IH; lia. 
Qed.

Fact gcd_sat_Gamma :
  gcd == Gamma gcd.
Proof.
  cbn. unfold Gamma.
  destruct x. reflexivity.
  destruct y. reflexivity.
  destruct (S x - S y) eqn:H;
    apply gcd'_index_independence; lia.
Qed.

Lemma size_ind2 {X Y} (sigma: X -> Y -> nat) {p: X -> Y -> Type} :
  (forall x y, (forall x' y', sigma x' y' < sigma x y -> p x' y') -> p x y) ->
  forall x y, p x y.
Proof.
  intros H.
  enough (forall n x y, sigma x y < n -> p x y) by eauto.
  induction n as [|n IH]. lia.
  intros x y H1. apply H. intros x' y' H2.
  apply IH. lia.
Qed.

Fact Gamma_unique f f' :
  f == Gamma f -> f' == Gamma f' -> f == f'.
Proof.
  intros H1 H2.
  apply (size_ind2 (fun x y => x + y)).
  intros x y IH.
  rewrite H1, H2. unfold Gamma.
  destruct x. reflexivity.
  destruct y. reflexivity.
  destruct (S x - S y) eqn:H; apply IH; lia.
Qed.

Fact gcd_sat_Gamma_unique f :
  f == Gamma f <-> f == gcd.
Proof.
  split; intros H.
  - apply Gamma_unique. exact H. apply gcd_sat_Gamma.
  - intros x y. unfold Gamma. do 3 rewrite H. apply gcd_sat_Gamma.
Qed.

Fact Gamma_G f :
  f == Gamma f -> sat G f.
Proof.
  intros E. unfold sat.
  apply (size_ind2 (fun x y => x + y)).
  intros x y IH.
  rewrite E. unfold Gamma.
  destruct x. {apply G_zero. }
  destruct y. {apply G_sym, G_zero. }
  destruct (S x - S y) eqn:H.
  - apply G_sub. lia.
    apply IH. lia.
  - apply G_sym, G_sub. lia.
    apply G_sym. rewrite <-H. apply IH. lia.
Qed.

Fact gcd_sat_gamma :
  sat gamma gcd.
Proof.
  intros x y. apply G_gamma, Gamma_G, gcd_sat_Gamma.
Qed.

(*** Uniqueness of gamma *)

Lemma divides_le x y :
  (forall n, (n | x) <-> (n | y)) -> x <= y.
Proof.
  intros H.
  destruct y.
  - specialize (H (S x)).
    assert (S x | x) as [k H1].
    { apply H. exists 0. lia. }
    destruct k; lia.
  - specialize (H x).
    assert (x | S y) as [k H1].
    { apply H. exists 1. lia. }
    destruct k; lia.
Qed.

Fact gamma_unique x y z z' :
  gamma x y z -> gamma x y z' -> z = z'.
Proof.
  unfold gamma. intros H1 H2.
  enough (z <= z' /\ z' <= z) by lia.
  split; apply divides_le.
  - intros n. rewrite H1, H2. easy.
  - intros n. rewrite H1, H2. easy.
Qed.

Fact gcd_sat_gamma_unique f :
  sat gamma f <-> f == gcd.
Proof.
  split; intros H x y.
  - apply (gamma_unique x y). apply H. apply gcd_sat_gamma.
  - rewrite H. apply gcd_sat_gamma.
Qed.

Fact G_gamma_equiv x y z :
  G x y z <-> gamma x y z.
Proof.
  split.
  - apply G_gamma.
  - intros H.
    enough (z = gcd x y) as ->.
    + apply Gamma_G, gcd_sat_Gamma.
    + apply (gamma_unique x y).
      * apply H.
      * apply gcd_sat_gamma.
Qed.

Fact sat_gamma_Gamma f :
  sat gamma f <-> f == Gamma f.
Proof.
  rewrite gcd_sat_gamma_unique.
  symmetry. apply gcd_sat_Gamma_unique.
Qed.


