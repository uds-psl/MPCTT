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


(** Iteration *)

Fixpoint iter (X: Type) (f: X -> X) (n:nat) (x:X) : X :=
  match n with
  | 0 => x
  | S n => f (iter X f n x)
  end.

Fact iter_add n x :
  n + x = iter nat S n x.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact iter_mul n x :
  n * x = iter nat (Nat.add x) n 0.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

(* demo "_" *)

(* goto gs.v for implicit arguments *)

Inductive Pair (X Y: Type) : Type :=
| pair : X -> Y -> Pair X Y.

Check Pair.
Check pair.

Definition swap X Y (a: Pair X Y) :=
  match a with
  | pair _ _ x y => pair _ _ y x
  end.

Goal forall X Y (a: Pair X Y),
    swap _ _ (swap _ _ a) = a.
Proof.
  intros X Y.
  destruct a as [x y].
  reflexivity.
Qed.
