Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.
Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.
Arguments Bijection {X Y}.
Definition dec (X: Type) := sum X (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).


Definition FE : Prop :=
  forall X (p: X -> Type) (f g: forall x, p x), (forall x, f x = g x) -> f = g.
Definition PE : Prop :=
  forall P Q: Prop, P <-> Q -> P = Q.
Definition unique (X: Type) : Prop :=
  forall a b: X, a = b.
Definition PI : Prop :=
  forall P: Prop, unique P.

Fact unique_bot :
  unique False.
Proof.
  intros [].
Qed.

Fact unique_top :
  unique True.
Proof.
  intros [] []. reflexivity.
Qed.

Fact PE_PI :
  PE -> PI.
Proof.
  intros H P a.
  enough (unique P) as H1.
  { apply H1. }
  enough (P = True) as H1.
  { rewrite H1. apply unique_top. }
  apply H. tauto.
Qed.

Fact bool_bool_enum :
  FE -> forall f,
    f = (fun _ => true) \/
    f = (fun _ => false) \/
    f = (fun b => b) \/
    f = negb.
Proof.
  intros H f.
  assert (forall g, f true = g true -> f false = g false -> f = g).
  - intros g ? ?. apply H. intros []; easy.
  - destruct (f true) eqn:?, (f false) eqn:?; auto.
Qed.

Goal
  FE -> bijection (True -> True) True.
Proof.
  intros H.
  exists (fun _ => I) (fun _ x => x).
  - intros f. apply H. intros x. apply unique_top.
  - intros x. apply unique_top.
Qed.

Goal
  FE -> bijection (True -> bool) bool.
Proof.
  intros H.
  exists (fun f => f I) (fun b x => b).
  - intros f. apply H. intros []. reflexivity.
  - intros b. reflexivity.
Qed.

Definition encode (f: bool -> bool) : bool * bool :=
  (f true, f false).

Definition decode (a: bool * bool) : bool -> bool :=
  match a with
  | (true, true) => fun _ => true
  | (true, false) => fun b => b
  | (false, true) => negb
  | (false, false) => fun _ => false
  end.

Goal
  FE -> bijection (bool -> bool) (bool * bool).
Proof.
  intros H.
  exists encode decode; hnf.
  - intros f. apply H. intros x. unfold encode. 
    destruct x, (f true), (f false); reflexivity.
  - intros [x y]. unfold decode. destruct x, y; reflexivity.
Qed.

Goal forall X, unique X -> eqdec X.
Proof.
  intros X H x y. left. apply H.
Qed.

Goal forall X, bijection X True -> unique X.
Proof.
  intros X [f g H1 H2] x y.
  rewrite <-(H1 x), <-(H1 y). f_equal.
  apply unique_top.
Qed.

Goal forall X, X -> unique X -> bijection X True.
Proof.
  intros X x.
  exists (fun _ => I) (fun _ => x).
  - intros y. apply H.
  - intros a. apply unique_top.
Qed.

Fact unique_Coquand (A: Prop) (E: Prop -> A) (D: A -> Prop) :
  unique A -> (forall P: Prop, D (E P) <-> P) -> False.
Proof.
  intros HA H.
  apply H. rewrite (HA (E False) (E True)). apply H, I.
Qed.

Section Elim_restriction_or.
  Variables (f: True \/ True -> bool)
            (feqT: f (or_introl I) = true)
            (feqF: f (or_intror I) = false).
  Goal PI -> False.
  Proof.
    intros H.
    assert (f (or_introl I) = f (or_intror I))
      as H1 by apply f_equal, H.
    revert H1. rewrite feqT, feqF. discriminate.
  Qed.
End Elim_restriction_or.

Section Elim_restriction_ex.
  Variables (f: @ex bool (fun _ => True) -> bool)
            (feq: forall x, f (ex_intro _ x I) = x).

  Goal PI -> False.
  Proof.
    intros H.
    assert (f (ex_intro _ true I) = f (ex_intro _ false I))
      as H1 by apply f_equal, H.
    revert H1. rewrite !feq. discriminate.
  Qed.
End Elim_restriction_ex.
