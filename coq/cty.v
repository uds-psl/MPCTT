Definition dec (X: Type) : Type := X + (X -> False).
Definition decider {X} (p: X -> Prop) := forall x, dec (p x).
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.
Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (_: inv g f).


(*** Equality deciders *)

Definition eqdec X := forall x y: X, dec (x = y).

Definition eqdec_bot : eqdec False.
Proof.
  intros [].
Qed.

Definition eqdec_nat : eqdec nat.
Proof.
  hnf; induction x as [|x IH]; destruct y as [|y]; unfold dec in *.
  1-3: intuition congruence.
  destruct (IH y); intuition congruence.
Qed.

Definition eqdec_injection X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros [f g H] d x1 x2.
  destruct (d (f x1) (f x2)) as [H1|H1];
    unfold dec; intuition congruence.
Qed.

Definition eqdec_option X :
  eqdec X <=> eqdec (option X).
Proof.
  split; intros d.
  - intros [x1|] [x2|].
    2-4:  unfold dec; intuition congruence.
    specialize (d x1 x2).
    unfold dec in *; intuition congruence.
  - intros x1 x2.
    specialize (d (Some x1) (Some x2)).
    unfold dec in *; intuition congruence.
Qed.

(*** Enumerators *)

Definition enum X := Sigma f: nat -> option X, forall x, exists n, f n = Some x.

Definition enum_bot : enum False.
Proof.
  exists (fun _ => None). intros [].
Qed.

Definition enum_nat : enum nat.
Proof.
  exists Some. eauto.
Qed.

Definition enum_injection X Y :
  injection X Y -> enum Y -> enum X.
Proof.
  intros [f g H] [e H1].
  exists (fun n => match e n with Some x => Some (g x) | None => None end).
  intros x. specialize (H1 (f x)) as [n H1].
  exists n. rewrite H1. congruence.
Qed.

Definition enum_option X :
  enum X <=> enum (option X).
Proof.
  split; intros [e H].
  - exists (fun n => Some match n with 0 => None| S n => e n end).
    intros [x|].
    + specialize (H x) as [n H]. exists (S n). congruence.
    + exists 0. reflexivity.
  - exists (fun n => match e n with Some (Some x) => Some x | _ => None end).
    intros x.
    specialize (H (Some x)) as [n H].
    exists n. rewrite H. reflexivity.
Qed.

(*** EWOs *)

Definition ewo X := forall (p: X -> Prop), decider p -> ex p -> sig p.

Definition ewo_bot : ewo False.
Proof.
  intros p _ [[] _].
Qed.

From Coq Require Import ConstructiveEpsilon.

Definition ewo_nat : ewo nat.
Proof.
  intros p H1 H2.
  apply constructive_indefinite_ground_description_nat in H2.
  - destruct H2; eauto. 
  - intros n. destruct (H1 n); auto.
Qed.

Definition ewo_injection X Y :
  injection X Y -> ewo Y -> ewo X.
Proof.
  intros [f g H] e p d H1.
  destruct (e (fun y => p (g y))) as [y H2].
  - intros y. apply d.
  - destruct H1 as [x H1]. exists (f x). congruence.
  - eauto.
Qed.

Definition ewo_option X :
  ewo X <=> ewo (option X).
Proof.
  split; intros e p d H.
  - destruct (d None) as [H1|H1]. {eauto.}
    destruct (e (fun x => p (Some x))) as [x H2].
    + intros x. apply d.
    + destruct H as [[x|] H].
      * eauto.
      * exfalso. auto.
    + eauto.
  - destruct (e (fun a => match a with Some x => p x | None => False end)) as [[x|] H1].
    + intros [x|]. {apply d.} right. easy.
    + destruct H as [x H]. exists (Some x). easy.
    + eauto.
    + contradict H1.
Qed.

(*** Countable Types *)

Definition cty X := (eqdec X * enum X) %type.

Definition cty_bot : cty False.
Proof.
  split. apply eqdec_bot. apply enum_bot.
Qed.

Definition cty_nat : cty nat.
Proof.
  split. apply eqdec_nat. apply enum_nat.
Qed.

Definition cty_injection X Y :
  injection X Y -> cty Y -> cty X.
Proof.
  intros H [d e]. split.
  - apply eqdec_injection in H; assumption.
  - apply enum_injection in H; assumption.
Qed.

Definition cty_option X :
  cty X <=> cty (option X).
Proof.
  split; intros [d e]; split.
  - revert d. apply eqdec_option.
  - revert e. apply enum_option.
  - revert d. apply eqdec_option.
  - revert e. apply enum_option.
Qed.

Fact cty_enum_sigma {X} :
  cty X -> Sigma f: nat -> option X, forall x, Sigma n, f n = Some x.
Proof.
  intros (d&e&H).
  exists e. intros x. apply ewo_nat.
  - intros n. apply eqdec_option in d. apply d.
  - apply H.
Qed.
 
Fact cty_equiv X :
  cty X <=> injection (option X) nat.
Proof.
  split.
  - intros [h G] %cty_enum_sigma.
    exists (fun a => match a with Some x => S (pi1 (G x)) | None => 0 end)
      (fun n => match n with 0 => None | S n => h n end).
    intros [x|]. apply (pi2 (G x)). reflexivity.
  - intros H. apply cty_injection in H.
    + revert H. apply cty_option.
    + apply cty_nat.
Qed.

Fact cty_ewo X :
  cty X -> ewo X.
Proof.
  intros H %cty_equiv %ewo_injection.
  - revert H. apply ewo_option.
  - apply ewo_nat.
Qed.

Fact injection_nat_option X :
  injection X nat -> injection (option X) nat.
Proof.
  intros [f g H].
  exists (fun a => match a with Some x => S (f x) | None => 0 end)
    (fun n => match n with 0 => None | S n => Some ( g n) end).
  intros [x|]; congruence.
Qed.

Fact cty_injection_nat X :
  injection X nat -> cty X.
Proof.
  intros H. apply cty_equiv, injection_nat_option, H.
Qed.

Fact injection_option X Y :
  injection (option X) Y -> X -> injection X Y.
Proof.
  intros [f g H] x0.
  exists (fun x => f (Some x))
    (fun y => match g y with Some x => x | None => x0 end).
  intros x. rewrite H. reflexivity.
Qed.

Fact cty_flat_injection X :
  cty X -> X -> injection X nat.
Proof.
  intros H %cty_equiv. apply injection_option, H.
Qed.
g
