(*** Inverse functions *)

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

(*** Injections and bijections *)

Inductive injection (X Y: Type) : Type :=
| Injection (f: X -> Y) (g: Y -> X) (H: inv g f).

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
  hnf. congruence.
Qed.

Fact discriminate_injection {X Y} :
  injection X Y -> forall Z:Type, (forall f g, @inv X Y g f -> Z) -> Z.
Proof.
  intros [f g H] Z H1. eapply H1, H.
Qed.

Fact injection_trans' X Y Z :
  injection X Y -> injection Y Z -> injection X Z.
Proof.
  intros H1 H2.
  apply (discriminate_injection H1). intros f g H.
  apply (discriminate_injection H2). intros f' g' H'.
  apply (Injection _ _ (fun x => f' (f x)) (fun z => g (g' z))).
  hnf. congruence.
Qed.

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

Fact bijection_refl (X: Type) :
  bijection X X.
Proof.
  exists (fun x => x) (fun x => x); hnf; reflexivity.
Qed.

(*** Unit, bool, option types,
sum types, product types *)

Print unit.
Print bool.
Print option.
Print sum.
Print prod.

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

Goal bijection (nat + unit) nat.
Proof.
  exists (fun a: nat + unit => match a with inl x => S x | inr _ => 0 end)
    (fun x: nat => match x with 0 => inr tt | S x => inl x end).
  - intros [x|[]]; reflexivity.
  - intros [|x]; reflexivity.
Qed.

(** Discrimination rules *)

Definition discriminate_unit (p: unit -> Prop)
  (e: p tt) a : p a
  :=
  match a return p a with tt => e end.

Definition discriminate_bool (p: bool -> Prop)
  (e1: p true) (e2: p false) a : p a
  :=
  match a return p a with true => e1 | false => e2 end.

Goal forall x:bool, x = true \/ x = false.
Proof.
  refine (discriminate_bool _ _ _).
  all: auto.
Qed.

Definition discriminate_option X (p: option X -> Prop)
  (e1: forall x, p (Some x)) (e2: p None) a : p a
  :=
  match a return p a with Some x => e1 x | None => e2 end.

Definition discriminate_sum X Y (p: X + Y -> Prop)
  (e1: forall x, p (inl x)) (e2: forall y, p (inr y)) a : p a
  :=
  match a return p a with inl x => e1 x | inr y => e2 y end.

Definition discriminate_product X Y (p: X * Y -> Prop)
  (e: forall x y, p (x, y)) a : p a
  :=
  match a return p a with (x,y) => e x y end.

(*** Arithmetic Eliminator *)

Fixpoint elim_nat (p: nat -> Type) (e1: p 0) (e2: forall n, p n -> p (S n)) (n: nat) : p n
  := match n with 0 => e1 | S n => e2 n (elim_nat p e1 e2 n) end.

(* Discrimination rule *)
Check fun p: nat -> Prop => elim_nat p.

(* Simply typed reducing match *)
Definition match_nat n Z e1 e2 := elim_nat (fun _ => Z) e1 (fun n _ => e2 n) n.
Check match_nat.

Goal forall Z e1 e2, match_nat 0 Z e1 e2 = e1.
  reflexivity.
Qed.

Goal forall Z e1 e2 n, match_nat (S n) Z e1 e2 = e2 n.
  reflexivity.
Qed.

(* Addition defined with eliminator *)
Definition plus x y := elim_nat (fun _ => nat) y (fun _ => S) x.
Check plus.

Goal forall y, plus 0 y = y.
  reflexivity.
Qed.

Goal forall x y, plus (S x) y = S (plus x y).
  reflexivity.
Qed.

(*** Nonexistence of Injections *)

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

Lemma eq_fun {X Y} {f g: X -> Y} x :
  f = g -> f x = g x.
Proof.
  congruence.
Qed.

Definition fixed_point {X} f (x:X) := f x = x.

Fact Lawvere {X Y} (f: X -> X -> Y) :
  surjective f -> forall g: Y -> Y, ex (fixed_point g).
Proof.
  intros H g.
  specialize (H (fun x => g (f x x))) as [x H].
  exists (f x x). hnf.
  apply (eq_fun x) in H. cbn in H.
  easy.
Qed.

Fact no_injection_Cantor X :
  ~ injection (X -> bool) X.
Proof.
  intros [f g H].
  enough (ex (fixed_point negb)) as [x Hx].
  - destruct x; easy.
  - apply (Lawvere g).
    eapply inv_surjective, H.
Qed.

(*** Void *)

Inductive void : Type := .

Definition elim_void
  : void -> forall X:Type, X
  := fun v => match v with end.

Goal bijection void (forall X:Type, X).
Proof.
  exists elim_void
    (fun f => f void)
  ; hnf.
  - intros [].
  - intros f. destruct (f void).
Qed.

Goal forall X, bijection (X + void) X.
Proof.
  intros X.
  exists (fun a: X + void => match a with inl x => x | inr v => elim_void v X end)
    inl.
  - intros [x|[]]. reflexivity.
  - intros x. reflexivity.
Qed.

Goal ~ injection unit void.
Proof.
  intros [f g H].
  destruct (f tt).
Qed.

(*** Truncation *)

Definition truncation (X: Type) : Prop := forall Z:Prop, (X -> Z) -> Z.
Notation "□ X" := (truncation X) (at level 30, right associativity).

Goal forall P Q, P /\ Q <-> □ (P * Q).
Proof.
  split.
  - intros [H1 H2] Z. auto.
  - intros H. apply H. tauto.
Qed.

Goal forall P Q, P \/ Q <-> □ (P + Q).
Proof.
  split.
  - intros [H1|H2] Z; auto.
  - intros H. apply H. tauto.
Qed.

Goal False <-> □ void.
Proof.
  split.
  - intros [].
  - intros H. apply H. intros [].
Qed.

Goal forall P: Prop, □ P <-> P.
Proof.
  split.
  - intros H. apply H. auto.
  - intros H Z. auto.
Qed.

Goal □ (forall X:Type, X + ~X) -> (forall X:Prop, X \/ ~X).
Proof.
  intros F X.
  apply F.
  intros G.
  specialize (G X). tauto.
Qed.

(*** CFE *)

Definition CFE := False -> forall X:Type, X.


Fact CFE_bijection_empty :
  CFE -> forall X: Type, ~ X ->  bijection X void.
Proof.
  intros F X f.
  exists (fun x => F (f x) void)
    (fun v => elim_void v X)
    ; hnf.
  - intros x. exfalso. exact (f x).
  - intros [].
Qed.

Goal CFE -> bijection False void.
Proof.
  intros F.
  apply CFE_bijection_empty.
  exact F. auto.
Qed.

(* CFE can be defined in Rocq using discrimination
   on   inductiove definition of [False] *)
Goal CFE.
Proof.
  intros [].
Qed.
