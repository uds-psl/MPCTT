From Coq Require Import PeanoNat.
Import Nat.

Implicit Types (n x y: nat) (a: nat * nat).

Definition next a : nat * nat :=
  match a with
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

Fact encode_next a :
  encode (next a) = S (encode a).
Proof.
  destruct a as [[|x] y]; cbn -[sum].
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

Opaque encode.

Fact decode_encode a :
  decode (encode a) = a.
Proof.
  revert a.
  enough (forall n a, encode a = n -> decode n = a) by eauto.
  induction n as [|n IH]; intros [x y]; cbn.
  - destruct x, y; cbn [encode]; cbn; easy.
  - destruct y.
    + destruct x.
      * discriminate.
      * change (S x, 0) with (next (0,x)).
        rewrite encode_next.
        intros [= <-].
        f_equal. apply IH. reflexivity.
    + change (x, S y) with (next (S x, y)). 
      rewrite encode_next.
      intros [= <-].
      f_equal. apply IH. reflexivity.
Qed.
