Module Demo.
  Inductive ex (X: Type) (p: X -> Prop) : Prop := E (x:X) (a: p x).

  Definition elim_ex (X: Type) (p: X -> Prop) (Z: Prop) (f: forall x, p x -> Z) (b: ex X p) : Z :=
    match b with E _ _ x a => f x a end.

  Lemma deMorgan X (p: X -> Prop) :
    ~ ex X (fun x => p x) <-> forall x, ~ p x.
  Proof.
    split.
    - intros f x a. apply f.
      apply (E X (fun x => p x) x).
      (* Coq did beta-reduction immediately *)
      exact a.
    - intros f. hnf.
      apply (elim_ex X (fun x => p x)).
      (* Coq did beta-reduction immediately *)
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

Lemma Russell (P: Prop) :
  ~ (P <-> ~ P).
Proof.
  intros [f g].
  assert (a: P).
  { apply g. intros a. exact (f a a). }
  exact (f a a).
Qed.
  
Goal forall X (p: X -> X -> Prop),
    ~ (exists x, forall y, p x y <-> ~ p y y).
Proof.
  intros X p [x H]. exact (Russell _ (H x)).
  Show Proof.
Qed.

Fact negb_fp :
  ~ exists x, negb x = x.
Proof.
  intros [x H]. revert H.
  destruct x; cbn; discriminate.
Qed.

Fact not_fp :
  ~ exists P: Prop, (~P) = P.
Proof.
  intros [P H].
  apply (Russell P).
  replace (~P) with P.
  tauto.
Qed.

Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Theorem Lawvere X Y (f: X -> X -> Y) (g: Y -> Y) :
  surjective f -> exists y, g y = y.
Proof.
  intros H.
  specialize (H (fun x => g (f x x))) as [a H].
  exists (f a a). pattern (f a) at 2. rewrite H.
  reflexivity.
Qed.

Corollary Lawvere_bool X :
  ~ exists f: X -> X -> bool, surjective f.
Proof.
  intros [f H].
  apply negb_fp.
  revert H. apply Lawvere.
Qed.

Corollary Lawvere_Prop X :
  ~ exists f: X -> X -> Prop, surjective f.
Proof.
  intros [f H].
  apply not_fp.
  revert H. apply Lawvere.
Qed.

Definition id X (x:X) := x.

Corollary not_no_fp X :
  (~X) <> X.
Proof.
  intros H.
  enough (exists h, id False h = h) as [[] _].
  enough (exists f: X -> X -> False, surjective f) as [f H1].
  { revert H1. apply Lawvere. }
  pattern (X -> False). rewrite H.
  exists (id X). intros x. exists x. reflexivity.
Qed.
