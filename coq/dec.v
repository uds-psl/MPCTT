Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition dec (X: Type) := sum X (X -> False).

Fact dec_boolean X (p: X -> Prop) :
  (forall x, dec (p x)) <=> Sigma f, forall x, p x <-> f x = true.
Proof.
  split.
  - intros F.
    exists (fun x => if F x then true else false).
    intros x.
    destruct (F x) as [H|H];
      intuition congruence.
  - intros [f H] x. specialize (H x). unfold dec.
    destruct (f x);
      intuition congruence.
Qed.

Fact dec_prop_impl P Q:
  dec P -> dec Q -> dec (P -> Q).
Proof.
  unfold dec. intuition.
Qed.

Definition dec_iff_invariance {X Y} :
  X <=> Y -> dec X -> dec Y.
Proof.
  intros H [H1|H1].
  - left. apply H, H1.
  - right. intros y. apply H1, H, y.
Defined.

Definition dec2bool {X} : dec X -> bool :=
  fun a => if a then true else false.


(*** Equality Deciders *)

Definition eqdec X := forall x y: X, dec (x = y).

Definition nat_eqdec : eqdec nat.
Proof.
  hnf. induction x as [|x IH]; destruct y.
  - left. reflexivity.
  - right. congruence.
  - right. congruence.
  - destruct (IH y) as [H|H].
    + left. congruence.
    + right. congruence.
Defined.

Compute dec2bool (nat_eqdec 3 5).

Definition option_eqdec {X} :
  eqdec X -> eqdec (option X).
Proof.
  intros H [x|] [y|].
  - specialize (H x y) as [H|H].
    + left. congruence.
    + right. congruence.
  - right. congruence.
  - right. congruence.
  - left. reflexivity.
Defined.

Compute dec2bool (option_eqdec nat_eqdec (Some 3) (Some 5)).


(*** Coq's Decision Format *)

(** Coq offers support for equality decisions 
    but uses a different decision format. *)

Print sumbool.
From Coq Require Import Arith.
Search concl: ({_=_} + {_}).

Definition dec_adapt (P: Prop) :
  { P } + { ~ P} <=> dec P.
Proof.
  split.
  - intros [H|H].
    + left. exact H.
    + right. exact H.
  - intros [H|H].
    + left. exact H.
    + right. exact H.
Defined.

Definition coq_nat_eqdec : eqdec nat.
Proof.
  intros x y. apply dec_adapt. decide equality.
Defined.

Compute dec2bool (coq_nat_eqdec 3 5).

Definition coq_option_eqdec {X} :
  eqdec X -> eqdec (option X).
Proof.
  intros H x y. apply dec_adapt. decide equality.
  apply dec_adapt, H.
Defined.
  
Compute dec2bool (coq_option_eqdec coq_nat_eqdec (Some 5) (Some 5)).

Definition coq_nat_eqdec' : eqdec nat.
Proof.
  intros x y. apply dec_adapt. apply Nat.eq_dec.
Defined.

Compute dec2bool (coq_nat_eqdec' 3 5).



