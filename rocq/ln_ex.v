Definition LDN := forall X: Prop, ~ ~X -> X.

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
    intros x. specialize (H1 x). auto.
  Qed.

  Goal LDN -> forall X p, ~(forall x, p x) -> ex X (fun x => ~p x).
  Proof.
    intros H X p H1.
    apply H. intros H2.
    apply H1. intros x.
    apply H. intros H3.
    apply H2. exact (exI _ _ x H3).
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

Goal LDN -> forall X  (p: X -> Prop),
    ~(forall x, p x) -> (exists x, ~p x).
  Proof.
    intros H X p H1.
    apply H. intros H2.
    apply H1. intros x.
    apply H. intros H3.
    apply H2. exists x. exact H3.
  Qed.
