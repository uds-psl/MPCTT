(*** MPCTT, Chapter Arithmetic Pairing *)

From Coq Require Import Lia.

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
  destruct a as [[|x] y]; cbn.
  - replace (y + 0) with y by lia. lia.
  - replace (x + S y) with (S (x +y)) by lia. cbn. lia.
Qed.

Opaque encode. (* Disable simplification of encode *)

Fact encode_decode n :
  encode (decode n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite encode_next, IH. reflexivity.
Qed.

Fact decode_encode a :
  decode (encode a) = a.
Proof.
  revert a.
  enough (forall n a, encode a = n -> decode n = a) by eauto.
  induction n as [|n IH]; intros [x y]; cbn.
  - destruct x, y; easy.
  - destruct y.
    + destruct x. easy.
      change (S x, 0) with (next (0,x)).
      rewrite encode_next.
      specialize (IH (0,x)). 
      intros [= <-]. f_equal. auto.
    + change (x, S y) with (next (S x, y)). 
      rewrite encode_next.
      intros [= <-]. f_equal. auto. 
Qed.
