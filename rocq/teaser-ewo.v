From Stdlib Require Import Lia.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decider p := (forall x, dec (p x)).
Notation sig := sigT.
Notation Sig := existT.
Inductive void : Type := .
Inductive unit : Type := U.
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

  Fact ewo_nat' : ex p -> sig p.
  Proof.
    intros H.
    apply W with (n:=0).
    destruct H as [n H].
    apply (T_lower n).
    constructor.
    easy.
  Qed.
End EWO_Nat.

Definition ewo_nat : EWO nat := ewo_nat'.
