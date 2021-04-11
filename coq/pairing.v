From Coq Require Import PeanoNat.
Import Nat.

Implicit Types (n x y: nat) (c: nat * nat).

Definition next c : nat * nat :=
  match c with
  | (0,y) => (S y, 0)
  | (S x, y) => (x, S y)
  end.

Fixpoint decode n : nat * nat :=
  match n with
  | 0 => (0,0)
  | S n' => next (decode n')
  end.

Fixpoint sum n : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + sum n'
  end.

Definition encode '(x, y) : nat :=
  sum (x + y) + y.

Fact encode_next c :
  encode (next c) = S (encode c).
Proof.
  destruct c as [[|x] y]; cbn -[sum].
  - rewrite !add_0_r. rewrite add_comm. reflexivity.
  - rewrite !add_succ_r. reflexivity.
Qed.

Fact encode_decode n :
  encode (decode n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite encode_next, IH. reflexivity.
Qed.

Fact decode_encode c :
  decode (encode c) = c.
Proof.
  revert c.
  enough (forall n c, encode c = n -> decode n = c) by eauto.
  induction n as [|n IH]; intros [x y]; cbn [decode].
  - destruct x, y.
    1:reflexivity. all:intros [=].
  - destruct y. 1:destruct x.
    + intros [=].
    + change (S x, 0) with (next (0,x)).
      rewrite encode_next. intros H. f_equal.
      apply IH. congruence.
     + change (x, S y) with (next (S x, y)). 
      rewrite encode_next. intros H. f_equal.
      apply IH. congruence.
Qed.
