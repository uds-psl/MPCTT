Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

(*** Injections and Bijections *)


Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.
Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Fact injective_eqdec {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H d x x'.
  destruct (d (f x) (f x')) as [H1|H1].
  - left. apply H, H1.
  - right. congruence.
Qed.

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.

Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  intros H x x' H1 %(f_equal g). rewrite !H in H1. exact H1.
Qed.

Fact inv_surjective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> surjective g.
Proof.
  intros H x. exists (f x). apply H.
Qed.

Fact inv_injective_inv X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective g -> inv f g.
Proof.
  intros H1 H2 y. apply H2. rewrite H1. reflexivity.
Qed.

Fact inv_surjective_inv X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> surjective f -> inv f g.
Proof.
  intros H1 H2 y.
  specialize (H2 y) as [x H2]. subst y. rewrite H1. reflexivity.
Qed.

Fact inv_agree X Y (f: X -> Y) (g g': Y -> X) :
  surjective f -> inv g f -> inv g' f -> forall y, g y = g' y.
Proof.
  intros H1 H2 H3 y.
  specialize (H1 y) as [x H1]. subst y. rewrite H2, H3. reflexivity.
Qed.

Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (_: inv g f).

Fact injection_refl X :
  injection X X.
Proof.
  exists (fun x => x) (fun x => x). intros x. reflexivity.
Qed.

Fact injection_trans X Y Z :
  injection X Y -> injection Y Z -> injection X Z.
Proof.
  intros [f g H] [f' g' H'].
  exists (fun x => f' (f x)) (fun z => g (g' z)).
  intros x. congruence.
Qed.

Fact injection_transport X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros [f g H].
  eapply injective_eqdec, inv_injective, H.
Qed.

Fact injection_Cantor X :
  injection (X -> bool) X -> False.
Proof.
  intros [f g H].
  pose (h x := negb (g x x)).
  enough (g (f h) (f h) = h (f h)) as H1.
  { revert H1. unfold h at 3. destruct g; easy. }
  congruence.
Qed.
    
Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

Fact bijection_refl X :
  bijection X X.
Proof.
  exists (fun x => x) (fun x => x); easy.
Qed.

Fact bijection_sym X Y :
  bijection X Y -> bijection Y X.
Proof.
  intros [f g H1 H2]. exists g f; assumption.
Qed.

Fact bijection_trans X Y Z :
  bijection X Y -> bijection Y Z -> bijection X Z.
Proof.
  intros [f g H1 H2] [f' g' H1' H2'].
  exists (fun x => f' (f x)) (fun z => g (g' z)).
  - intros z. rewrite H1'. apply H1.
  - intros x. rewrite H2. apply H2'.
Qed.

Fact bij_empty X Y :
  (X -> False) -> (Y -> False) -> bijection X Y.
Proof.
  intros f g.
  exists (fun x => match f x with end) (fun y => match g y with end).
  - intros x. exfalso. easy.
  - intros y. exfalso. easy.
Qed.

(* Note the use of 'unshelve eexists' *)

Definition bijection_prod X Y :
  bijection (X * Y) (sig (fun _: X => Y)).
Proof.
  unshelve eexists.
  - intros [x y]. exists x. exact y.
  - intros [x y]. exact (x,y).
  - intros [x y]. reflexivity.
  - intros [x y]. reflexivity.
Qed.

Definition bijection_sum X Y :
  bijection (X + Y) (sig (fun b: bool => if b then X else Y)).
Proof.
  unshelve eexists.
  - intros [x|y].
    + exists true. exact x.
    + exists false. exact y.
  - intros [[] z].
    + left. exact z.
    + right. exact z. 
  - intros [x|y]; reflexivity.
  - intros [[] z]; reflexivity.
Qed.

Definition bij_bij_sig X Y:
  bijection (bijection X Y) (Sigma f g, @inv X Y g f /\ inv f g).
Proof.
  unshelve eexists.
  - intros [f g H1 H2]. exists f, g. exact (conj H1 H2).
  - intros (f&g&H1&H2). exists f g; assumption. 
  - intros [f g H1 H2]. reflexivity.
  - intros (f&g&H1&H2). reflexivity.
Qed.

Goal bijection nat bool -> False.
Proof.
  intros [f g H _].
  assert (f 0 = f 1 \/ f 0 = f 2 \/ f 1 = f 2) as [H3| [H3|H3]].
  { destruct (f 0), (f 1), (f 2); auto. }
  all: apply (f_equal g) in H3.
  all: rewrite !H in H3.
  all: easy.
Qed.

Fact exercise_bool1 (f: bool -> bool) :
  injective f <-> surjective f.
Proof.
  destruct (f true) eqn:E1, (f false) eqn:E2; split; intros H.
  - exfalso. enough (true = false) by congruence.
    apply H. congruence.
  - exfalso. specialize (H false) as [x H].
    destruct x; congruence.
  - intros [|]; eauto.
  - intros [|] [|]; congruence.
  - intros [|]; eauto.
  - intros [|] [|]; congruence.
  - exfalso.
    enough (true = false) by congruence.
    apply H. congruence.
  - exfalso. specialize (H true) as [x H].
    destruct x; congruence.
Qed.

Fact exercise_bool2 (f: bool -> bool) :
  injective f ->
  (forall x, f x = x) \/ (forall x, f x = negb x).
Proof.
  intros H.
  destruct (f true) eqn:E1.
  - left. intros [|]. exact E1.
    destruct (f false) eqn:E2. 2:easy.
    apply H. congruence.
  - right. intros [|]. exact E1.
    destruct (f false) eqn:E2; cbn. easy.
    apply H. congruence.
Qed.
    
Definition agree {X Y} (f g: X -> Y) := forall x, f x = g x.

Fact exercise_bool3  (f: bool -> bool) :
  injective f ->
  inv f f *  (forall g, inv g f -> agree g f).
Proof.
  intros [H|] %exercise_bool2; split.
  - congruence.
  - congruence.
  - intros x. rewrite !H. destruct x; easy.
  - intros g H1.
    enough (agree g negb) by congruence.
    assert (H2: inv g negb) by congruence.
    intros x. rewrite <-H2. destruct x; easy.
Qed.

(*** Option Types *)

Definition option_eqdec {X} :
  eqdec X -> eqdec (option X).
Proof.
  intros H [x|] [y|].
  - specialize (H x y) as [H|H].
    + left. congruence.
    + right. congruence.
  - right. congruence.
  - right. congruence.
  - left. reflexivity.
Qed.

Definition option_eqdec_backwards {X} :
  eqdec (option X) -> eqdec X.
Proof.
  intros H x y.
  specialize (H (Some x) (Some y)) as [H|H].
  - left. congruence.
  - right. congruence.
Qed.

Fixpoint Fin n : Type :=
  match n with 0 => False | S n' => option (Fin n') end.

Fact Fin_eqdec n :
  eqdec (Fin n).
Proof.
  induction n as [|n IH]; cbn.
  - intros [].
  - apply option_eqdec, IH.
Qed.


(*** Bijection Theorem *)

Fact R {X Y f g} :
  @inv (option X) (option Y) g f ->
  forall x, Sigma y, match f (Some x) with Some y' => y = y' | None => f None = Some y end.
Proof.
  intros H x.
  destruct (f (Some x)) as [y|] eqn:E1.
  - exists y. reflexivity.
  - destruct (f None) as [y|] eqn:E2.
    + exists y. reflexivity.
    + exfalso. congruence.
Qed.

Fact R_inv {X Y f g} :
  forall (H1: @inv (option X) (option Y) g f)
    (H2: inv f g),
    inv (fun y => pi1 (R H2 y)) (fun x => pi1 (R H1 x)).
Proof.
  intros H1 H2 x.
  destruct (R H1 x) as [y H3]; cbn.
  destruct (R H2 y) as [x' H4]; cbn.
  revert H3 H4.  
  destruct (f (Some x)) as [y1|] eqn:E.
  - intros <-. rewrite <-E, H1. easy.
  - intros <-.  rewrite H1. rewrite <-E, H1. congruence.
Qed.

Theorem bijection_option X Y : 
  bijection (option X) (option Y) -> bijection X Y.
Proof.
  intros [f g H1 H2].
  exists (fun y => pi1 (R H1 y)) (fun x => pi1 (R H2 x)); apply R_inv.
Qed.
