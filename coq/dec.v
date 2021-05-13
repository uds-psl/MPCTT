Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

(** We choose a less general definition of dec than in the text
    to be compatible with Coq's standard library *)

Definition dec (P: Prop) := { P } + { ~P }.

Fact dec_boolean X (p: X -> Prop) :
  (forall x, dec (p x)) <=> Sigma f, forall x, p x <-> f x = true.
Proof.
  split.
  - intros F.
    exists (fun x => if F x then true else false).
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

From Coq Require Import Arith.
Search concl: ({_=_} + {_}).

Definition nat_eqdec :
  eqdec nat.
Proof.
  hnf. unfold dec. decide equality.
  Restart.
  exact Nat.eq_dec.
Defined.

Definition option_eqdec X :
  eqdec X -> eqdec (option X).
Proof.
  intros H [x|] [y|].
  - specialize (H x y) as [<-|H].
    + left. reflexivity.
    + right. intros [= <-]. auto.
  - right. intros [=].
  - right. intros [=].
  - left. reflexivity.
Defined.

Definition dec2bool {P}
  : dec P -> bool
  := fun a => if a then true else false.

Compute dec2bool (option_eqdec nat nat_eqdec (Some 3) (Some 5)).

