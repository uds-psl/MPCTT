Section ExAbstract.
  Variable ex : forall X:Type, (X -> Prop) -> Prop.
  Variable exI : forall X p, forall x, p x -> ex X p.
  Variable exE : forall X p, ex X p -> forall Z: Prop, (forall x, p x -> Z) -> Z.

  Goal forall X p, ~ex X p <-> forall x, ~p x.
  Proof.
    split.
    - intros H x H1.
      apply H. exact (exI _ _ x H1).
    - intros H H1.
      apply (exE _ _ H1). exact H.
  Qed.

  Goal forall X p, ex X (fun x => ~p x) -> ~forall x, p x.
  Proof.
    intros X p H H1.
    apply (exE _ _ H).
    intros x H2. exact (H2 (H1 x)).
  Qed.

  Goal forall X (p: X -> Prop), ex X (fun x => ~p x) -> ~forall x, p x.
  Proof.
    refine (fun X p a H => exE _ _ a _ (fun x f => f (H x))).
  Qed.
 
  Goal forall X (p: X -> Prop) (Z: Prop),
    (forall x, p x -> Z) <-> (ex X p -> Z).
  Proof.
    split.
    - intros H H1.
      apply (exE _ _ H1). intros x H2. eauto.
    - intros H x H1. apply H. apply (exI _ _ x H1).
  Qed.
 
End ExAbstract.

Module ExDef.
  Definition ex (X:Type) (p: X -> Prop)
    : Prop
    := forall Z: Prop, (forall x, p x -> Z) -> Z.
  Definition exI X (p: X -> Prop)
    : forall x, p x -> ex X p
    := fun x a => fun Z f => f x a.
  Definition exE X (p: X -> Prop)
    : ex X p -> forall Z: Prop, (forall x, p x -> Z) -> Z
    := fun a => a.
End ExDef.

Goal forall X (p: X -> Prop),
    ~(exists x, p x) <-> forall x, ~p x.
Proof.
  split.
  - intros H x H1.
    apply H. exists x. exact H1.
  - intros H [x H2]. exact (H x H2).
Qed.

Goal forall X (p: X -> Prop),
    (exists x, ~p x) -> ~forall x, p x.
Proof.
  intros X p [x H] H1. apply H, H1.
Qed.

Lemma forall_exists X (p: X -> Prop) (Z: Prop) :
  (forall x, p x -> Z) <-> ((exists x, p x) -> Z).
Proof.
  split.
  - intros H [x H1]. eapply H, H1.
  - intros H x H1. apply H. exists x. exact H1.
Qed.

Fact Barber X (p: X -> X -> Prop) :
  ~ (exists x, forall y, p x y <-> ~ p y y).
Proof.
  intros [x H]. specialize (H x). tauto.
Qed.

From Stdlib Require Import Lia.

Lemma eq_fun {X Y} {f g: X -> Y} x :
  f = g -> f x = g x.
Proof.
  congruence.
Qed.

Fact Cantor (f: nat -> nat -> nat) :
  exists g,  forall n, f n <> g.
Proof.
  exists (fun n => S (f n n)).
  intros n H.
  apply (eq_fun n) in H. cbn in H.
  lia.
Qed.

Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Fact Lawvere {X Y} {f: X -> X -> Y} :
  surjective f -> forall g, exists y:Y, g y = y.
Proof.
  intros H g.
  specialize (H (fun x => g (f x x))) as [x H].
  exists (f x x).
  apply (eq_fun x) in H.
  easy.
Qed.

Goal forall f: bool -> bool -> bool, ~surjective f.
Proof.
  intros f H.
  destruct (Lawvere H negb) as [b H1].
  destruct b; easy.
Qed.

Goal forall f: bool -> bool -> Prop, ~surjective f.
Proof.
  intros f H.
  destruct (Lawvere H (fun X:Prop => ~X)) as [X H1].
  enough (X <-> ~X) by tauto.
  rewrite H1; tauto.
Qed.

Definition LDN := forall X:Prop, ~ ~X -> X.

Fact DeMorgan_all_ex (X: Type) (p: X -> Prop) :
  LDN -> ~(forall x, p x) -> exists x, ~p x.
Proof.
  intros H H1. apply H. intros H2.
  apply H1. intros x. apply H. intros H3.
  apply H2. exists x. exact H3.
Qed.

Fact Lawvere' {X Y} {f: X -> X -> Y} :
  surjective f -> forall g, exists y:Y, g y = y.
Proof.
  intros H g.
  assert (H1:= H (fun x => g (f x x))).
  destruct H1 as [x H2].
  exists (f x x).
  assert (H3:= eq_fun x H2). cbn in H3.
  easy.
Qed.
