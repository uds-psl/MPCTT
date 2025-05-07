Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).


Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.

Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  (* congruence. *)
  intros H x x' H1.
  cut (g (f x) = g (f x')).
  -  rewrite H. rewrite H. easy.
  - f_equal. exact H1.
Qed.

Fact inv_surjective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> surjective g.
Proof.
  intros H x. exists (f x). apply H.
Qed.

Fact inv_injective_inv X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective g -> inv f g.
Proof.
  intros H1 H2 y. apply H2. apply H1.
Qed.

Fact inv_surjective_inv X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> surjective f -> inv f g.
Proof.
  intros H1 H2 y.
  specialize (H2 y) as [x H2]. subst y. f_equal. apply H1.
Qed.

Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (H: inv g f).

Fact injection_refl X :
  injection X X.
Proof.
  exists (fun x => x) (fun x => x). hnf. reflexivity.
Qed.

Fact injection_trans X Y Z :
  injection X Y -> injection Y Z -> injection X Z.
Proof.
  intros [f g H] [f' g' H'].
  exists (fun x => f' (f x)) (fun z => g (g' z)).
  intros x. congruence.
Qed.

Fact injection_Cantor X :
  ~ injection (X -> bool) X.
Proof.
  intros [f g H].
  pose (h x := negb (g x x)).
  enough (g (f h) (f h) = h (f h)) as H1.
  { revert H1. unfold h at 3. destruct g; easy. }
  rewrite H. reflexivity.
Qed.

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

Goal bijection bool (unit + unit).
Proof.
  exists (fun b => if b:bool then inl tt else inr tt)
    (fun a => match a with inl _ => true | inr _ => false end).
  - intros b. destruct b; reflexivity.
  - intros a. destruct a; destruct u; reflexivity.
  (* needs reduction for  matches *)
Qed.

Lemma eqdec_nat :
  forall x y : nat, (x = y) + (x <> y).
Proof.
  induction x; destruct y.
  - auto.
  - auto.
  - auto.
  - destruct (IHx y) as [H|H].
    + left.  auto.
    + right. auto.
Qed.

Goal forall X (p: X -> Prop),
    (forall x, p x + ~ p x) -> exists f: X -> bool, forall x, if f x then p x else ~ p x.
Proof.
  intros * D.
  exists (fun x => if D x then true else false).
  intros x.
  destruct (D x) as [H|H]; exact H.
  (* needs reduction for boolean matches *)
Qed.
  
Goal forall X (p: X -> Prop),
    (forall x, p x \/ ~ p x) -> exists f: X -> bool, forall x, if f x then p x else ~ p x.
Proof.
  intros * D.
  Fail exists (fun x => if D x then true else false).
  (* PDR *)
Abort.
