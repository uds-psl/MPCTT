(*** MPCTT, Chapter Arithmetic Pairing *)

(* This development is a pearl both mathematically
   and regarding the Rocq mechanization.  We will
   demonstrate several advanced tactic uses.  *)

From Stdlib Require Import Lia.
Implicit Types (n x y: nat) (a: nat * nat).

Definition sigma a :=
  match a with
  | (0,y) => (S y, 0)
  | (S x, y) => (x, S y)
  end.

Fixpoint D n :=
  match n with
  | 0 => (0,0)
  | S n => sigma (D n)
  end.

Fixpoint gamma n :=
  match n with
  | 0 => 0
  | S n => gamma n + S n
  end.

Definition E '(x, y) :=
  gamma (x + y) + y.

Fact E_sigma a :
  E (sigma a) = S (E a).
Proof.
  destruct a as [[|x] y]; cbn.
  - replace (y + 0) with y; lia.
  - replace (x + S y) with (S (x + y)); cbn; lia.
Qed.

Fact E_D n :
  E (D n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite E_sigma. congruence.
Qed.

Definition pi a :=
  match a with
  | (0,0) => (0,0)
  | (S x,0) => (0,x)
  | (x, S y) => (S x, y)
  end.
Arguments pi : simpl nomatch.

Fact D_E a :
  D (E a) = a.
Proof.
  revert a.
  enough (forall n a, E a = n -> D n = a) by eauto.
  induction n as [|n IH]; cbn; intros a.
  - destruct a as [[|x] [|y]]; cbn; auto; lia.
  - assert (a = (0,0) \/ a = sigma (pi  a)) as [-> | ->]; cbn.
    + destruct a as [[|x] [|y]]; cbn; auto.
    + easy.
    + rewrite E_sigma. intros [= H1%IH]. congruence.
Qed.

Fact Gauss n :
  2 * gamma n = n * S n.
Proof.
  induction n as [|n IH]; cbn; lia.
Qed.

Goal forall a, pi (sigma a) = a.
Proof.
  intros [[|[|x]] [|y]]; cbn; easy.
Qed.
