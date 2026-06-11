Module AndOrFalse.
  Inductive and (X Y: Prop) : Prop :=
  | C: X -> Y -> and X Y.
  
  Inductive or (X Y: Prop) : Prop :=
  | L: X -> or X Y
  | R: Y -> or X Y.
  
  Inductive False : Prop := .

  Definition E_and (X Y: Prop)
    : and X Y -> forall Z: Prop, (X -> Y -> Z) -> Z
    := fun a Z f => match a with C _ _ x y => f x y end.

  Definition E_or (X Y: Prop)
    : or X Y -> forall Z: Prop, (X -> Z) -> (Y -> Z) -> Z
    := fun a Z f g => match a with L _ _ x => f x | R _ _ y => g y end.
  
  Fail Definition E_or' (X Y: Prop)
    : or X Y -> forall Z: Type, (X -> Z) -> (Y -> Z) -> Z
    := fun a Z f g => match a with L _ _ x => f x | R _ _ y => g y end.

  Definition E_False
    : False -> forall X: Type, X
    := fun a => match a with end.

  Definition CFE := False -> forall X: Type, X.

  Goal CFE.
  Proof.
    exact E_False.
  Qed.

  Goal CFE.
  Proof.
    intros [].
  Qed.
End AndOrFalse.

Abbreviation sig := sigT.
Abbreviation Sig := existT.
Abbreviation pi1 := projT1.
Abbreviation pi2 := projT2.

Module Eq.
  Inductive eq (X: Type) (x: X) : X -> Prop :=
  | Q : eq X x x.

  Definition R {X: Type} {x y: X}
    : eq X x y -> forall p: X -> Type, p x -> p y
    := fun e p a => match e with Q _ _ => a end.

  Arguments Q {X}.
  Notation "x = y" := (eq _ x y) : type_scope.

  Goal forall X (x: X), R (Q x) _ x = x.
  Proof.
    intros X x. cbn. apply Q.
  Qed.

  Lemma J X (x:X) (p: forall y, x = y -> Type) :
    p x (Q x) -> forall y e, p y e.
  Proof.
    exact (fun H y e => match e with Q _ => H end).
  Qed.

  Definition K := forall X (x:X) (p: x = x -> Prop),
      p (Q x) -> forall e, p e.
  
  Definition UIP :=
    forall X (x:X) (e e': x = x), e = e'.

  Fact UIP_K :
    UIP <-> K.
  Proof.
    split; intros H X x.
    - intros p H1 e.
      specialize (H X x (Q x) e).
      apply (R H). exact H1.
    - refine (H X x _ _).
      refine (H X x _ _).
      apply Q.
  Qed.
 
  Definition DPI :=
    forall X (p: X -> Type) x y y',
      Sig p x y = Sig p x y' -> y = y'.

  Goal UIP -> DPI.
  Proof.
    intros H X p.
    enough (forall a b: sig p,
               a = b -> forall e: pi1 a = pi1 b, R e p (pi2 a) = pi2 b) as H1.
    - intros x y y' e.
      specialize (H1 _ _ e). cbn in H1.
      specialize (H1 (Q x)). cbn in H1.
      exact H1.
    - intros a b e. pattern b.
      apply (R e). intros e1.
      assert (e2: Q (pi1 a) = e1) by apply H.
      apply (R e2). apply Q.
  Qed.
  
  Lemma DPI_UIP :
    DPI -> UIP.
  Proof.
    intros H X x.
    enough (forall e: x = x, Q x = e) as H1.
    - intros e e'.
      apply (R (H1 e)).
      apply (R (H1 e')).
      apply Q.
    - enough (forall e: x = x, Sig (eq X x) x (Q x) = Sig (eq X x) x e) as H1.
      + intros e. apply H. apply H1.
      + enough (forall y, forall e: x = y, Sig (eq X x) x (Q x) = Sig (eq X x) y e) as H1.
        * exact (H1 x).
        * apply J. apply Q.
  Qed.
End Eq.

(** Less or Equal *)

From Stdlib Require Import Lia.

Inductive le (x: nat) : nat -> Prop :=
| leE :   le x x 
| leS y : le x y -> le x (S y).

Fixpoint ind_le (x: nat) (p: nat -> Prop) :
  p x ->
  (forall y, p y -> p (S y)) ->
  forall y, le x y -> p y.
Proof.
  intros e1 e2.
  intros _ [|y a].
  - exact e1.
  - exact (e2 y (ind_le x p e1 e2 y a)).
Qed.

Goal le 2 5.
Proof.
  apply leS. 
  apply leS. 
  apply leS. 
  apply leE.
Qed.

Fact le_sound x :
  forall y, le x y -> x <= y.
Proof.
  apply ind_le.
  - lia.
  - lia.
Qed.

Goal forall x y, le x y -> x <= y.
Proof.
  induction 1; lia.
Qed.

Fact le_complete x y :
  x <= y -> le x y.
Proof.
  induction y as [|y IH]; intros H.
  - assert (x = 0) as -> by lia.
    apply leE.
  - assert (x = S y \/ x <= y) as [->|H1] by lia.
    + apply leE.
    + apply leS, IH, H1.
Qed.

Goal forall x, ~le (S x) x.
Proof.
  intros x H%le_sound. lia.
Qed.

(** GCD *)

Definition size_ind2 {X Y} (sigma: X -> Y -> nat) {p: X -> Y -> Type} :
  (forall x y, (forall x' y', sigma x' y' < sigma x y -> p x' y') -> p x y) ->
  forall x y, p x y.
Proof.
  intros H.
  enough (forall n x y, sigma x y < n -> p x y) by eauto.
  induction n as [|n IH]. lia.
  intros x y H1. apply H. intros x' y' H2.
  apply IH. lia.
Qed.

Inductive G : nat -> nat -> nat -> Prop :=
| G0 z     : G 0 z z
| G1 x y z : G x y z -> G y x z
| G2 x y z : x <= y -> G x (y - x) z -> G x y z.

Fixpoint ind_G (p: nat -> nat -> nat -> Prop) :
  (forall z, p 0 z z) ->
  (forall x y z, p x y z -> p y x z) ->
  (forall x y z, x <= y -> p x (y - x) z -> p x y z) ->
  (forall x y z, G x y z -> p x y z).
Proof.
  intros e1 e2 e3.
  intros _ _ _ [z|x y z a|x y z h a].
  - exact (e1 z).
  - exact (e2 x y z (ind_G p e1 e2 e3 x y z a)).
  - exact (e3 x y z h (ind_G p e1 e2 e3 x (y - x) z a)).
Qed.

Goal G 15 25 5.
Proof.
  apply G2. lia. cbn.
  apply G1. apply G2. lia. cbn.
  apply G1. apply G2. lia. cbn.
  apply G2. lia. cbn.
  apply G1. apply G0.
Qed.

Section GCD.
  (* We assume the necessary properties of [gamma].
     Proofs can be found in [ln_sizeind.v].      *)
  Variable gamma : nat -> nat -> nat -> Prop.
  Variable gamma0  : forall y, gamma 0 y y.
  Variable gamma1 : forall x y z, gamma x y z -> gamma y x z.
  Variable gamma2 : forall x y z, x <= y -> gamma x (y - x) z -> gamma x y z.

  Fact soundness :
    forall x y z, G x y z -> gamma x y z.
  Proof.
    induction 1 as [y|x y z _ IH|x y z H _ IH].
    - apply gamma0. 
    - apply gamma1, IH.
    - eapply gamma2. exact H. apply IH.
  Qed.

  Fact totality :
    forall x y, sig (G x y).
  Proof.
    refine (size_ind2 (fun x y => 2*x+y) _).
    intros x y IH.
    destruct x.
    - exists y. apply G0.
    - destruct (S x - y) as [|a] eqn:E.
      + specialize (IH (S x) (y - S x)) as [z IH]. lia.
        exists z. apply G2. lia. exact IH.
      + specialize (IH y (S x)) as [z IH]. lia.
        exists z. apply G1. exact IH.
  Qed.

  Variable gamma3 : forall x y z z', gamma x y z -> gamma x y z' -> z = z'.

  Fact completeness :
    forall x y z, gamma x y z -> G x y z.
  Proof.
    intros x y z H.
    destruct (totality x y) as [z' H1].
    enough (z = z') by congruence.
    eapply gamma3. exact H. apply soundness, H1.
  Qed.

  Variable gamma4 : forall y z, gamma 0 y z -> y = z.
  Variable gamma5 : forall x y z, x <= y -> gamma x y z -> gamma x (y - x) z.

  Fact completeness' :
    forall x y z, gamma x y z -> G x y z.
  Proof.
    intros x y z. revert x y.
    refine (size_ind2 (fun x y => 2*x+y) _).
    intros x y IH H.
    destruct x.
    - apply gamma4 in H as ->. apply G0.
    - destruct (S x - y) as [|a] eqn:E.
      + eapply G2. lia.
        apply IH. lia.
        apply gamma5. lia. exact H.
      + apply G1. apply IH. lia. apply gamma1, H.
  Qed.

End GCD.
  






  

  


  
