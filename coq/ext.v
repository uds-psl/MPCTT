Definition FE : Prop :=
  forall X (p: X -> Type) (f g: forall x, p x), (forall x, f x = g x) -> f = g.
Definition PE : Prop :=
  forall P Q: Prop, P <-> Q -> P = Q.
Definition pure (P: Prop) : Prop :=
  forall a b: P, a = b.
Definition PI : Prop :=
  forall P: Prop, pure P.

Fact pure_False :
  pure False.
Proof.
  intros [].
Qed.
Fact pure_True :
  pure True.
Proof.
  intros [] []. reflexivity.
Qed.

Fact PE_PI :
  PE -> PI.
Proof.
  intros H P a.
  enough (pure P) as H1.
  { apply H1. }
  enough (P = True) as H1.
  { rewrite H1. apply pure_True. }
  apply H. tauto.
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

