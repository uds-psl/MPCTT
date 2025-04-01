(*** MPCTT, Chapter Arithmetic Pairing *)

(* This development is a pearl both mathematically
   and regarding the Rocq mechanization.  We will
   demonstrate several advanced tactic uses.  *)

From Stdlib Require Import Lia.

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
  - replace (y + 0) with y; lia.
  - replace (x + S y) with (S (x + y)); cbn; lia.
Qed.

Opaque encode.
(* Disables simplification of encode;
   doesn't affect reflexivity and easy. *)

Fact encode_decode n :
  encode (decode n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite encode_next. congruence.
Qed.


Fact encode_zero a :
  encode a = 0 -> a = (0,0).
Proof.
  destruct a as [[|x] [|y]]; easy.
Qed.

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

Fact decode_encode a :
  decode (encode a) = a.
Proof.
  revert a.
  enough (forall n a, encode a = n -> decode n = a) by eauto.
  induction n as [|n IH]; cbn.
  - intros a H%encode_zero. easy.
  - destruct a as [x [|y]].
    + destruct x. easy.
      intros <-%encode_eq_zero.
      rewrite (IH (0,x)); reflexivity.
    + intros <-%encode_eq_S.
      rewrite (IH (S x,y)); reflexivity.
Qed.

Fact Gauss n :
  2 * sum n = n * S n.
Proof.
  induction n as [|n IH]; cbn; lia.
Qed.
