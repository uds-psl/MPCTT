(** Inverse functions *)

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
  apply (f_equal g) in H1.
  rewrite !H in H1.
  easy.
Qed.

Fact inv_surjective X Y (f: X -> Y) g :
  inv g f -> surjective g.
Proof.
  intros H x. exists (f x). apply H.
Qed.

Fact inv_injective_inv X Y (f: X -> Y) g :
  inv g f -> injective g -> inv f g.
Proof.
  intros H1 H2 y. apply H2. apply H1.
Qed.

Fact inv_surjective_inv X Y (f: X -> Y) g :
  inv g f -> surjective f -> inv f g.
Proof.
  intros H1 H2 y.
  specialize (H2 y) as [x H2]. subst y. f_equal. apply H1.
Qed.

Fact inv_inv_surjective X Y  (f: X -> Y) g g' :
  inv g f -> inv g' f -> surjective f -> forall y, g y = g' y.
Proof.
  intros Hgf hg'f Hf y.
  specialize (Hf y) as [x Hf].
  congruence.
Qed.  

(** Injections and bijections *)

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

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

Fact bijection_refl (X: Type) :
  bijection X X.
Proof.
  exists (fun x => x) (fun x => x); hnf; reflexivity.
Qed.

(** Unit, sums, option types *)

Print unit.
Print sum.
Print option.

(* need reducing simply typed match functions *)

Goal bijection bool (unit + unit).
Proof.
  exists (fun b => if b:bool then inl tt else inr tt)
    (fun a => match a with inl _ => true | inr _ => false end)
    ; hnf.
  - intros [|]; reflexivity.
  - intros [u|u]; destruct u; reflexivity.
Qed.

Goal forall X Y, bijection (X + Y) (Y + X).
Proof.
  intros X Y.
  exists (fun a => match a with inl x => inr x | inr y => inl y end)
    (fun a => match a with inl x => inr x | inr y => inl y end)
    ; hnf.
  - intros [x|y]; reflexivity.
  - intros [y|x]; reflexivity.
Qed.

Goal forall X, bijection (option X) (X + unit).
Proof.
  intros X.
  exists (fun a => match a with Some x => inl x | None => inr tt end)
    (fun a => match a with inl x => Some x | inr _ => None end)
  ; hnf.
  - intros [x|]; reflexivity.
  - intros [x|[]]; reflexivity.
Qed.

(* singleton types are in bijection with unit *)
Goal forall X (x0:X), (forall x, x = x0) -> bijection X unit.
Proof.
  intros X x0 H.
  exists (fun _ => tt) (fun _ => x0); hnf.
  - easy.
  - intros []. reflexivity.
Qed.
  
(** Nonexistence of injections *)

Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.

Fact no_injection_bool_unit :
  ~ injection bool unit.
Proof.
  intros [f g H].  (* Discrimination into [Prop] *)
  enough (true = false) by congruence.
  rewrite <-(H true), <-(H false).
  destruct (f true), (f false).
  reflexivity.
Qed.

Fact no_injection_nat_bool :
  ~ injection nat bool.
Proof.
  intros [f g H].
  enough (forall n, n = g true \/ n = g false) as H1.
  - destruct (H1 0), (H1 1), (H1 2); congruence.
  - intros n. rewrite <-(H n).
    destruct (f n) as [|]; auto.
Qed.

Fact no_injection_Cantor X :
  ~ injection (X -> bool) X.
Proof.
  intros [f g H].
  pose (h x := negb (g x x)). (* must be reducible *)
  enough (g (f h) (f h) = h (f h)) as H1.
  { revert H1. unfold h at 3. destruct g; easy. }
  rewrite H. reflexivity.
Qed.

(** Elimination functions *)

Definition discriminate_bool (p: bool -> Type)
  (H1: p true) (H2: p false) (x: bool) : p x
  :=
  match x return p x with true => H1 | false => H2 end.

Definition match_bool
  : bool -> forall Z: Type, Z -> Z -> Z
  := fun x Z H1 H2 => discriminate_bool (fun _ => Z) H1 H2 x.

Compute match_bool true nat 0 1.

Fact discriminate_bool_prop :
  forall p: bool -> Prop, p true -> p false -> forall x, p x.
Proof.
  intros p. exact (discriminate_bool p).
Qed.

Goal forall x:bool, x = true \/ x = false.
Proof.
  refine (discriminate_bool_prop _ _ _).
  all: auto.
Qed.

Fixpoint recursion_nat (p: nat -> Type)
  (H1: p 0) (H2: forall n, p n -> p (S n)) (x: nat) : p x
  :=
  match x return p x with
  | 0 => H1
  | S n => H2 n (recursion_nat p H1 H2 n)
  end.

Fact induction_nat (p: nat -> Prop) :
  p 0 -> (forall n, p n -> p (S n)) -> forall x, p x.
Proof.
  exact (recursion_nat p).
Qed.

Definition discrimination_nat (p: nat -> Type) :
  p 0 -> (forall n, p (S n)) -> forall x, p x
  := fun H1 H2 => recursion_nat p H1 (fun n _ => H2 n).

Definition match_nat
  : nat -> forall Z, Z -> (nat -> Z) -> Z
  := fun x Z H1 H2 => discrimination_nat (fun _ => Z) H1 H2 x.

Compute match_nat 7 (option nat) None (fun n => Some n).

Fact discrimination_nat_prop (p: nat -> Prop) :
  p 0 -> (forall n, p (S n)) -> forall x, p x.
Proof.
  exact (discrimination_nat p).
Qed.

Definition double: nat -> nat :=
  recursion_nat (fun _ => nat) 0 (fun _ a => S (S a)).

Compute double 5.

(** Void *)

Inductive void : Type := .

Goal forall X, bijection (X + void) X.
Proof.
  intros X.
  exists (fun a: X + void => match a with inl x => x | inr v => match v with end end)
    inl.
  - intros [x|[]]. reflexivity.
  - intros x. reflexivity.
Qed.

Goal bijection (nat + unit) nat.
Proof.
  exists (fun a: nat + unit => match a with inl x => S x | inr _ => 0 end)
    (fun x: nat => match x with 0 => inr tt | S x => inl x end).
  - intros [x|[]]; reflexivity.
  - intros [|x]; reflexivity.
Qed.

Goal ~ injection unit void.
Proof.
  intros [f g H].
  destruct (f tt).
Qed.

Goal bijection void (forall X:Type, X).
Proof.
  exists (fun v:void => match v with end)
    (fun f: forall X, X => match f void with end);
    hnf.
  - intros [].
  - intros f. destruct (f void).
Qed.
                             
(** Decisions and equality deciders *)

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
    all: unfold dec.
    all: intuition congruence.
  - unfold dec; intuition congruence.
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

(** CFE *)

Fact CFE :
  False -> forall X:Type, X.
Proof.
  intros [].
Qed.

Fact eqdec_bot : eqdec False.
Proof.
  intros b. apply (CFE b).
Qed.

(* All empty types are in bijection *)
Goal forall X Y: Type, ~ X ->  ~ Y -> bijection X Y.
Proof.
  intros X Y FX FY.
  exists (fun x => match CFE (FX x) void return Y with end)
    (fun y => match CFE (FY y) void return X with end)
    ; hnf.
  - intros x. exfalso. easy. 
  - intros y. exfalso. easy. 
Qed.

Goal bijection void False.  (* subtyping *)
Proof.
  exists (fun v:void => match v return False with end)
    (fun b => CFE b void)
  ; hnf.
  - intros [].
  - intros x. exfalso. exact x.
Qed.

  



