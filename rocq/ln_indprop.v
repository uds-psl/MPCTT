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

Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.

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

(** EWO *)

Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition dec (X: Type) : Type := X + ~ X.
Definition decider {X} (p: X -> Type) := forall x, dec (p x).

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.
Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (H: inv g f).

Definition EWO (X: Type) :=
  forall p: X -> Prop, decider p -> ex p -> sig p.

Fact injection_ewo X Y :
  injection X Y -> EWO Y -> EWO X.
Proof.
  intros [f g H] E p p_dec H1.
  destruct (E (fun y => p (g y))) as [a Ha].
  - intros x. destruct (p_dec (g x)); unfold dec; auto.
  - destruct H1 as [x Hx]. exists (f x). congruence.
  - eauto.
Qed.
  
Section EWO_Nat.
  Variable p: nat -> Prop.
  Variable p_dec: decider p.

  Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Fixpoint W n (a: T n) : sig p :=
    match a with C _ phi => match p_dec n with
                       | inl h => (Sig p n h)
                       | inr h => W (S n) (phi h)
                       end
    end.
  
  Lemma T_lower n :
    T n -> T 0.
  Proof.
    induction n as [|n IH]. easy.
    intros H. apply IH. constructor. auto.
  Qed.

  Fact ewo_nat : ex p -> sig p.
  Proof.
    intros H.
    apply (W 0).
    destruct H as [n H].
    apply (T_lower n).
    constructor.
    easy.
  Qed.
End EWO_Nat.

(** Less or Equal *)

From Stdlib Require Import Lia.

Inductive le (x: nat) : nat -> Prop :=
| leR :   le x x 
| leS y : le x y -> le x (S y).

Fact le_complete x y :
  x <= y -> le x y.
Proof.
  induction y as [|y IH]; intros H.
  - assert (x = 0) as -> by lia.
    apply leR.
  - assert (x = S y \/ x <= y) as [->|H1] by lia.
    + apply leR.
    + apply leS, IH, H1.
Qed.

Fixpoint elim_le (x: nat) (p: nat -> Prop)
  : p x -> (forall y, p y -> p (S y)) -> forall y, le x y -> p y
  := fun e1 e2 _ a => match a with
                   | leR _ => e1
                   | leS _ y a => e2 y (elim_le x p e1 e2 y a)
                   end.

Fact le_correct x :
  forall y, le x y -> x <= y.
Proof.
  apply elim_le.
  - lia.
  - lia.
Qed.

Goal forall x y, le x y -> x <= y.
Proof.
  induction 1; lia.
Qed.








  

  


  
