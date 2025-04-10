Check 3+4.
Compute 3+4.
Check Nat.add.

Goal 3 + 4 = 10 - 3.
Proof.
  cbn. reflexivity.
Qed.

Goal forall y, 0 + y = y.
Proof.
  intros y. cbn. reflexivity.
Qed.

Goal forall x, x + 0 = x.
Proof.
  intros x; cbn.
  easy.
Qed.

Goal forall x, x + 0 = x.
Proof.
  induction x.
  - reflexivity.
  - cbn. rewrite IHx.  reflexivity.
Qed.

Fact add0 x :
  x + 0 = x.
Proof.
  induction x.
  - reflexivity.
  - cbn. rewrite IHx. reflexivity.
Qed.

Fact addS x y:
  x + S y = S (x + y).
Proof.
  induction x.
  - reflexivity.
  - cbn. rewrite IHx. reflexivity.
Qed.

Fact add_comm x y:
  x + y = y + x.
Proof.
  induction x; cbn.
  - rewrite add0. reflexivity.
  - rewrite IHx. rewrite addS. reflexivity.
Qed.

Goal forall x y, x + y = y + x.
Proof.
  intros x. intros y.
  revert x. revert y.
  intros a b. apply add_comm.
Qed.

(** Distance, quantified inductive hypothesis *)

Fixpoint D x y :=
  match x, y with
  | 0, y => y
  | S x, 0 => S x
  | S x, S y => D x y
  end.

Compute D 3 7.
Compute D 7 3.

Arguments D : simpl nomatch.

Fact D_comm x y :
  D x y = D y x.
Proof.
  induction x; cbn.
  - destruct y; cbn; reflexivity.
  - destruct y; cbn.
    + reflexivity.
    +
Abort.

Fact D_comm x y :
  D x y = D y x.
Proof.
  revert y.
  induction x; cbn.
  - destruct y; cbn; reflexivity.
  - destruct y; cbn.
    + reflexivity.
    + apply IHx.
Qed.

Fact D_sub x y :
  D x y = (x - y) + (y - x).
Proof.
  revert y.
  induction x as [|x IH]; intros y.
  - destruct y; reflexivity.
  - destruct y; cbn.
    + rewrite add0. reflexivity.
    + apply IH.
Qed.

(** Automatic prover for linear arithmetic *)

From Stdlib Require Import Lia.

Goal forall x y z, x - (y + z) = x - y - z.
Proof.
  lia.
Qed.

