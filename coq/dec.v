From Coq Require Import Arith.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

(** We choose a less general definition of dec than on paper
    to be compatible with Coq's standard library *)

Definition dec P := { P } + { ~P }.

Fact dec_boolean X (p: X -> Prop) :
  (forall x, dec (p x)) <=> { f & forall x, p x <-> f x = true }.
Proof.
  split.
  - intros F. exists (fun x => if F x then true else false).
    intros x. destruct (F x) as [H|H]; intuition congruence.
  - intros [f H] x. specialize (H x). unfold dec.
    destruct (f x); intuition congruence.
Qed.

Fact dec_prop_impl P Q:
  dec P -> dec Q -> dec (P -> Q).
Proof.
  intros [H1|H1].
  - intros [H2|H2].
    + left. auto.
    + right. auto.
  - intros _. left. intros H. destruct (H1 H).
Qed.

Definition eqdec X := forall x y: X, dec (x = y).

Definition nat_eqdec :
  eqdec nat.
Proof.
  hnf. apply Nat.eq_dec.
Defined.

Definition option_eqdec X : eqdec X -> eqdec (option X).
Proof.
  intros H [x|] [y|].
  - specialize (H x y) as [<-|H].
    + left. reflexivity.
    + right. intros [= <-]. auto.
  - right. intros [=].
  - right. intros [=].
  - left. reflexivity.
Defined.

Compute if option_eqdec nat nat_eqdec (Some 5) (Some 5) then true else false.

