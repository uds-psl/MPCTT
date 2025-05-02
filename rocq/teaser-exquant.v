Module Demo.
  
  Inductive ex {X: Type} (p: X -> Prop) : Prop := E (x:X) (a: p x).

  (* X implicit for ex and E *)

  Definition match_ex {X: Type} (p: X -> Prop) (Z: Prop)
    : ex p -> (forall x, p x -> Z) -> Z
    := fun a e => match a with E _ x b => e x b end.

  Lemma deMorgan X (p: X -> Prop) :
    ~ ex (fun x => p x) <-> forall x, ~ p x.
  Proof.
    split.
    - intros f x a.
      apply f.
      exact (E p x a).   (* note eta conversion *)
    - intros f a.
      apply (match_ex p False a).
      exact f.
  Qed.
End Demo.

Lemma deMorgan X (p: X -> Prop) :
  ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  split.
  - intros H x H1. apply H. exists x. exact H1.
  - intros H [x Hx]. apply (H x Hx).
Qed.


Fact Barber X (p: X -> X -> Prop) :
  ~ (exists x, forall y, p x y <-> ~ p y y).
Proof.
  intros [x H]. specialize (H x). tauto.
Qed.


(** Lawvere *)

(* Boolean negation has no fixed pont *)

Fact negb_no_fp :
  ~ exists x, negb x = x.
Proof.
  intros [[|] H].
  - cbn in H. congruence.
  - cbn in H. congruence.
Qed.

(* Propositional negation has no fixed pont *)

Fact not_no_fp :
  ~ exists P: Prop, (~P) = P.
Proof.
  intros [P H].
  enough (H1: P <-> ~ P).
  - tauto.
  - rewrite H. tauto.
Qed.

Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Theorem Lawvere X Y (f: X -> X -> Y) (g: Y -> Y) :
  surjective f -> exists y, g y = y.
Proof.
  intros H.
  specialize (H (fun x => g (f x x))) as [x H].
  apply (f_equal (fun f => f x)) in H.
  exists (f x x).
  easy.
Qed.

Corollary Lawvere_bool X :
  ~ exists f: X -> X -> bool, surjective f.
Proof.
  intros [f H].
  apply negb_no_fp.
  revert H. apply Lawvere.
Qed.

Corollary Lawvere_Prop X :
  ~ exists f: X -> X -> Prop, surjective f.
Proof.
  intros [f H].
  apply not_no_fp.
  revert H. apply Lawvere.
Qed.

(** Unit and void *)

Inductive unit : Type := U.
Inductive void : Type := .

Lemma elim_void (Z: Prop) :
  void -> Z.
  intros x. destruct x.
Qed.

Lemma elim_unit (p: unit -> Prop) :
  p U -> forall x, p x.
Proof.
  intros H. destruct x. exact H.
Qed.












Definition void : Type := forall X : Type, X.

Goal void -> False.
Proof.
  intros f. exact (f False).
Qed.

(* Universe inconsistency *)
Fail Check (fun f: void => f void).
