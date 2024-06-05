From Coq Require Import Lia.

Notation "x <= y" := (x - y = 0) : nat_scope.
Notation "x < y" := (S x - y = 0) : nat_scope.

(* Additive characterization *)

Fact add_O x :
  x + 0 = x.
Proof.
  induction x as [|x IH]; cbn; congruence.
Qed.

Fact add_sub x y :
  x + y - x = y.
Proof.
  induction x as [|x IH]; cbn.
  - destruct y; reflexivity.
  - exact IH.
Qed.

Fact sub_xx x :
  x - x = 0.
Proof.
  replace x with (x + 0) at 1.
  - apply add_sub.  
  - apply add_O.
Qed.

Fact sub_add_zero x y :
  x - (x + y) = 0.
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - exact IH.
Qed.

Fact le_add_char x y :
  x <= y  <-> x + (y - x) = y.
Proof.
  induction x as [|x IH] in y |-*; destruct y; cbn.
  1-3:easy.
  rewrite IH. intuition congruence.
Qed.


Fact le_anti x y :
  x <= y -> y <= x -> x = y.
Proof.
  intros H1%le_add_char H2. revert H1.
  rewrite H2. rewrite add_O. easy.
Qed.

(* Decisions *)

Goal forall x y, (x <= y) + (y < x).
Proof.
  induction x as [|x IH]; destruct y; cbn; auto.
Qed.

Goal forall x y, (x <= y) + ~(x <= y).
Proof.
  induction x as [|x IH]; destruct y; cbn; auto.
Qed.

Fact lt_contra x y:
  (x <= y) <-> ~(y < x).
Proof.
  revert y.
  induction x as [|x IH]; destruct y.
  1-3: cbn; intuition congruence.
  rewrite (IH y). reflexivity.
Qed.

Fact le_test x y :
  if x - y then x <= y else ~(x <= y).
Proof.
  destruct (x - y); easy.
Qed.

Fact lt_test x y :
  if S x - y then x < y else ~(x < y).
Proof.
  apply le_test.
Qed.

Fact eq_test x y :
  if (x - y) + (y - x) then x = y else ~(x = y).
Proof.
  destruct (_ + _) eqn:E.
  - apply le_anti;
      destruct (x - y) as [|a] eqn:E1;
      destruct (y - x) as [|b] eqn:E2;
      easy.
  - intros <-. rewrite sub_xx in E. easy.
Qed.

(* Equality by contradiction *)

Fact lt_not_eq x y :
  (x < y -> False) -> (y < x -> False) -> x = y.
Proof.
  intros H1%lt_contra H2%lt_contra.
  apply le_anti; assumption.
Qed.





