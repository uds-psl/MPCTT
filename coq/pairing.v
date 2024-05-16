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

Fact encode_zero x y :
  encode (x,y) = 0 -> x = 0 /\ y = 0.
Proof.
  destruct x.
  - destruct y. easy. easy.
  - easy.
Qed.

Fact encode_next a :
  encode (next a) = S (encode a).
Proof.
  destruct a as [[|x] y]; cbn.
  - replace (y + 0) with y by lia. lia.
  - replace (x + S y) with (S (x +y)) by lia. cbn. lia.
Qed.

(* Disable simplification of encode
   without affecting reflexivity and easy. *)
Opaque encode. 

Fact encode_eq_zero x n :
  encode (S x, 0) = S n -> encode (0, x) = n.
Proof.
  change (S x, 0) with (next (0,x)).
  rewrite encode_next. congruence.
Qed.

Fact encode_eq_S x y n :
  encode (x, S y) = S n -> encode (S x, y) = n.
Proof.
  change (x, S y) with (next (S x, y)). 
  rewrite encode_next. congruence.
Qed.

Fact encode_decode n :
  encode (decode n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite encode_next. congruence.
Qed.

Fact decode_encode a :
  decode (encode a) = a.
Proof.
  revert a.
  enough (forall n a, encode a = n -> decode n = a) by eauto.
  induction n as [|n IH]; intros [x y]; cbn.
  - intros [-> ->] %encode_zero. reflexivity.
  - destruct y.
    + destruct x. easy.
      intros <-%encode_eq_zero.
      rewrite (IH (0,x)); reflexivity.
    + intros <-%encode_eq_S.
      rewrite (IH (S x, y)); reflexivity.
Qed.
