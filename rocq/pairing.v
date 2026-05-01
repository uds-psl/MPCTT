(*** MPCTT, Chapter Arithmetic Pairing *)

(* This development is a pearl both mathematically
   and regarding the Rocq mechanization.  We will
   demonstrate several advanced tactic uses.  *)

From Stdlib Require Import Lia.
Implicit Types (n x y: nat) (a: nat * nat).

Definition eta a :=
  match a with
  | (0,y) => (S y, 0)
  | (S x, y) => (x, S y)
  end.

Fixpoint decode n :=
  match n with
  | 0 => (0,0)
  | S n => eta (decode n)
  end.

Fixpoint sigma n :=
  match n with
  | 0 => 0
  | S n => sigma n + S n
  end.

Definition encode '(x, y) :=
  sigma (x + y) + y.

Fact encode_eta a :
  encode (eta a) = S (encode a).
Proof.
  destruct a as [[|x] y]; cbn.
  - replace (y + 0) with y; lia.
  - replace (x + S y) with (S (x + y)); cbn; lia.
Qed.

Fact encode_decode n :
  encode (decode n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite encode_eta. congruence.
Qed.

Definition pi a :=
  match a with
  | (0,0) => (0,0)
  | (S x,0) => (0,x)
  | (x, S y) => (S x, y)
  end.
Arguments pi : simpl nomatch.

Fact eta_pi a :
  a = (0,0) \/ a = eta (pi  a).
Proof.
  destruct a as [[|x] [|y]]; cbn; auto.
Qed.

Fact decode_encode a :
  decode (encode a) = a.
Proof.
  revert a.
  enough (forall n a, encode a = n -> decode n = a) by eauto.
  induction n as [|n IH]; cbn; intros a.
  - destruct a as [[|x] [|y]]; cbn; (lia || easy).
  - destruct (eta_pi a) as [-> | ->]; cbn. easy.
    rewrite encode_eta. intros [= H1%IH]. congruence.
Qed.

Fact Gauss n :
  2 * sigma n = n * S n.
Proof.
  induction n as [|n IH]; cbn; lia.
Qed.

Goal forall a, pi (eta a) = a.
Proof.
  intros [[|[|x]] [|y]]; cbn; easy.
Qed.
