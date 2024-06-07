(*** MPCTT, Chapter Linear Arithmetic, brute force proofs *)

Arguments Nat.sub : simpl nomatch.

Notation "x <= y" := (x - y = 0) : nat_scope.
Notation "x < y" := (S x <= y) : nat_scope.

Fact le_refl x :
  x <= x.
Proof.
  induction x as [|x IH]; cbn; easy.
Qed.

Fact le_trans x y z:
  x <= y -> y <= z -> x <= z.
Proof.
  revert y z.
  induction x as [|x IH]; cbn.
  - easy.
  - destruct y, z; cbn. 1-3:easy. apply IH.
Qed.

Fact le_anti x y :
  x <= y -> y <= x -> x = y.
Proof.
  revert y; induction x as [|x IH]; destruct y; cbn; auto.
Qed.

Fact sub_add_zero x y :
  x <= x + y.
Proof.
  induction x as [|x IH]; cbn; auto.
Qed.

Fact le_add_char x y :
  x <= y -> x + (y - x) = y.
Proof.
  revert y.
  induction x as [|x IH]; destruct y; cbn; auto; easy.
Qed.

(* Decisions *)

Goal forall x y, (x <= y) + (y < x).
Proof.
  induction x; destruct y; cbn; auto.
Qed.

Goal forall x y, (x <= y) + ~(x <= y).
Proof.
  induction x; destruct y; cbn; auto.
Qed.

Fact lt_contra x y:
  (x <= y) <-> ~(y < x).
Proof.
  revert y.
  induction x as [|x IH]; destruct y; cbn; easy.
Qed.

Fact le_test x y :
  if x - y then x <= y else ~(x <= y).
Proof.
  destruct (x - y); easy.
Qed.

Fact lt_test x y :
  if S x - y then x < y else ~(x < y).
Proof.
  destruct (S x - y); easy.
Qed.

Fact eq_test x y :
  if (x - y) + (y - x) then x = y else ~(x = y).
Proof.
  revert y.
  induction x as [|x IH]; destruct y; cbn; try easy.
  specialize (IH y). destruct (_ + _); congruence.
Qed.
          
Fact le_zero x :
  x <= 0 -> x = 0.
Proof.
  destruct x; easy.
Qed.

Fact tightness_dec x y :
  x <= y -> y <= S x -> (x=y) + (y = S x).
Proof.
  revert y.
  induction x as [|x IH]; destruct y; cbn; auto.
  - destruct y; cbn. auto. easy.
  - specialize (IH y). intuition congruence.
Qed.

 






