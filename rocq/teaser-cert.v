Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Inductive void : Type := .
Inductive unit : Type := U.

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
  exists (fun b => if b:bool then inl U else inr U)
    (fun a => match a with inl _ => true | inr _ => false end).
  - intros b. destruct b; reflexivity.
  - intros a. destruct a; destruct u; reflexivity.
  (* needs reduction for  matches *)
Qed.

Goal forall X, bijection (X + void) X.
Proof.
  intros X.
  exists (fun a: X + void => match a with inl x => x | inr v => match v with end end)
    inl.
  - intros [x|[]]. reflexivity.
  - intros x. reflexivity.
Qed.

Goal bijection (nat + nat) nat.
(* Takes too much arithmetic for now, will do later *)
Abort.

Goal bijection (nat + unit) nat.
Proof.
  exists (fun a: nat + unit => match a with inl x => S x | inr _ => 0 end)
    (fun x: nat => match x with 0 => inr U | S x => inl x end).
  - intros [x|[]]; reflexivity.
  - intros [|x]; reflexivity.
Qed.

Goal ~ injection unit void.
Proof.
  intros [f g H].
  destruct (f U).
Qed.

(* All empty types are in bijection *)
Goal forall X Y, ~ X ->  ~ Y -> bijection X Y.
Proof.
  intros * FX FY.
  exists (fun x:X => match FX x with end)
    (fun y:Y => match FY y with end).
  - intros x. destruct (FX x).
  - intros y. destruct (FY y).
  (* Computational falsity elimination *)
Qed.


Definition dec (X: Type) : Type := X + (X -> False).

Goal forall X Y,
    dec X -> dec Y -> dec (X + Y).
Proof.
  unfold dec. tauto.
Qed.

Definition eqdec X := forall x y: X, dec (x = y).

Fact eqdec_void : eqdec void.
Proof.
  intros [].
Qed.

Fact eqdec_bot : eqdec False.
Proof.
  intros [].
  (* Computational falsity elimination *)
Qed.

Fact eqdec_nat : eqdec nat.
Proof.
  hnf.
  induction x; destruct y.
  all: unfold dec.
  1-3: intuition congruence.
  destruct (IHx y) as [H|H]; intuition congruence.
Qed.

Fact eqdec_prod X Y :
  eqdec X -> eqdec Y -> eqdec (X*Y).
Proof.
  intros dX dY [x y] [x' y'].
  destruct (dX x x') as [H1|H1].
  - destruct (dY y y') as [H2|H2].
    + left. congruence.
    + right. congruence.
  - right. congruence.
Qed.
 
Fact eqdec_injective {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H d x x'. specialize (H x x').
  destruct (d (f x) (f x')) as [H1|H1];
    unfold dec in *; intuition congruence.
Qed.

Fact eqdec_injection X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros [f g H] H1.
  apply inv_injective in H.
  revert H H1. apply eqdec_injective.
Qed.
  
  
  



