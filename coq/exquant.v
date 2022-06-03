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
    Show Proof.
  Qed.
End Demo.

Locate "exists".
Print ex.

Lemma deMorgan X (p: X -> Prop) :
  ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  split.
  - intros f x a. apply f. exists x. exact a.
  - intros f [x a]. exact (f x a).
    Show Proof.
Qed.

Goal forall X (p: X -> Prop),
    ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  refine (fun X p => conj (fun f x a => _) (fun f b => _)).
  - refine (f (ex_intro p x a)).
  - refine (match b with ex_intro _ x a => f x a end).
  Show Proof.
Qed.

Theorem Barber X (p: X -> X -> Prop) :
  ~ (exists x, forall y, p x y <-> ~ p y y).
Proof.
  intros [x H]. specialize (H x). tauto.
Qed.

(** Lawvere *)

Fact negb_no_fp :
  ~ exists x, negb x = x.
Proof.
  intros [[|] H]; discriminate.  
Qed.

Fact not_no_fp :
  ~ exists P: Prop, (~P) = P.
Proof.
  intros [P H].
  enough (H1: ~(P <-> P)).
  - tauto.
  -  pattern P at 2. rewrite <-H. tauto.
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

(** Exercise: Equational proof of not_no_fp, tricky *)

Corollary not_no_fp' X :
  (~X) <> X.
Proof.
  intros H.
  pose (id:= fun a: False => a).
  enough (exists a, id a = a) as [[] _].
  enough (exists f: X -> X -> False, surjective f) as [f H1].
  - revert H1. apply Lawvere.
  - pattern (X -> False). rewrite H.
    exists (fun x => x). intros x. exists x. reflexivity.
Qed.
