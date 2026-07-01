From Stdlib Require Import Lia.
Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) : Type := X + (~X).
Abbreviation decider p := (forall x, dec (p x)).
Abbreviation sig := sigT.
Abbreviation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Lemma size_ind {X} (sigma: X -> nat) (p: X -> Type) :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H.
  enough (forall n x, sigma x < n -> p x) by eauto.
  induction n as [|n IH]. lia. (* CFE *)
  intros x H1. apply H. intros y H2.
  apply IH. lia.
Qed.

(** Accessibility and well-founded relations*)

Inductive Acc {X: Type} (R: X -> X -> Prop) (x: X) : Prop :=
| Acc_intro : (forall y, R y x -> Acc R y) -> Acc R x.

Fixpoint Acc_elim {X} R (p: X -> Type)
    : (forall x, (forall y, R y x -> p y) -> p x) -> forall x, Acc R x -> p x.
Proof.
  intros F x [f].
  exact (F x (fun y r => Acc_elim X R p F y (f y r))).
Qed.

Check Acc_rect.

Definition W {X: Type} (R: X -> X -> Prop) := forall x, Acc R x.

Fact ACC_impred X (R: X -> X -> Prop) x :
  Acc R x <-> forall p: X -> Prop,
      (forall x, (forall y, R y x -> p y) -> p x) -> p x.
Proof.
  split; intros H.
  - intros p H1. revert H1 x H. apply Acc_elim.
  - apply H. apply Acc_intro.
Qed.

(** Well-founded induction operators *)

Definition omega  {X} (R: X -> X -> Prop) : Type :=
    forall p: X -> Type,
      (forall x, (forall y, R y x -> p y) -> p x) ->
      forall x, p x.

Fact omega_W X (R: X -> X -> Prop) :
  omega R -> W R.
Proof.
  intros H. hnf. apply H. exact (Acc_intro R).
Qed.

Fact W_omega X (R: X -> X -> Prop) :
  W R -> omega R.
Proof.
  intros H p H1.
  intros x. generalize x (H x).
  apply Acc_elim. exact H1.
Qed.

Definition omega' {X} (R: X -> X -> Prop) : Prop :=
    forall p: X -> Prop,
      (forall x, (forall y, R y x -> p y) -> p x) ->
      forall x, p x.

Fact omega_omega'  X (R: X -> X -> Prop) :
  omega R -> omega' R.
Proof.
  intros H p. exact (H p).
Qed.

Fact omega'_W X (R: X -> X -> Prop) :
  omega' R -> W R.
Proof.
  intros H. hnf. apply H. exact (Acc_intro R).
Qed.

Fact omega'_omega  X (R: X -> X -> Prop) :
  omega' R <=> omega R.
Proof.
  split.
  - intros H. apply W_omega, omega'_W, H.
  - apply omega_omega'.
Qed.

Fact W_nat_size {X} (sigma: X -> nat) :
  W (fun x y => sigma x < sigma y).
Proof.
  apply omega_W.
  exact (size_ind sigma).
Qed.

Fact W_nat :
  W (fun x y => x < y).
Proof.
  apply (W_nat_size (fun n => n)).
Qed.

(** EWO *)

Section EWO.
  Variable p: nat -> Prop.

  Let R x y := x = S y /\ ~p y.

  Lemma ewo_Acc_init x :
    p x -> Acc R x.
  Proof.
    intros H.
    constructor. unfold R at 1. easy.
  Qed.
  
  Lemma ewo_Acc_S x :
    Acc R (S x) -> Acc R x.
  Proof.
    intros H.
    constructor. unfold R at 1. intuition congruence.
  Qed.
 
  Lemma ewo_Acc_O x :
    Acc R x -> Acc R 0.
  Proof.
    induction x as [|x IH]. easy. 
    intros H. apply IH, ewo_Acc_S, H.
  Qed.

  Fact ewo_Acc_sig :
    decider p -> forall x, Acc R x -> sig p.
  Proof.
    intros d.
    induction 1 as [x _ IH].
     destruct (d x) as [H|H].
    + eauto.
    + apply (IH (S x)). hnf. easy.
  Qed.

  Fact ewo_nat :
    decider p -> ex p -> sig p.
  Proof.
    intros d H.
    apply (ewo_Acc_sig d 0).
    destruct H as [x H].  (* Acc propositional *)
    apply ewo_Acc_O with x.
    apply ewo_Acc_init. exact H.
  Qed.
End EWO.

Check ewo_nat.

(** CFE with ACC *)

Fact CFE : False -> forall X: Type, X.
Proof.
  enough (omega (fun x y : False => False)) as H.
  - refine (H (fun _ => forall X: Type, X) _). 
    intros h H1. exact (H1 h h).
  - apply W_omega. intros h. destruct h. (* Acc propositional *)
Qed.

(** Lexical product *)

(** Crucial to work with W  *)

Section LexicalProduct.
  Variables
    (X: Type) (R1: X -> X -> Prop) (W1: W R1)
    (Y: Type) (R2: Y -> Y -> Prop) (W2: W R2).

  Definition lex (a b: X * Y) : Prop :=
    let (x,y) := a in
    let (x',y') := b in
    R1 x x' \/ (x = x' /\ R2 y y').

  Fact W_lex :
    W lex.
  Proof.
    intros [x y].
    induction (W1 x) as [x _ IHx] in y |-*.
    induction (W2 y) as [y _ IHy].
    constructor. intros [a b].
    unfold lex at 1. intros [H|[-> H]].  (* Acc propositional *)
    - apply IHx, H.
    - apply IHy, H.
  Qed.
End LexicalProduct.

Arguments lex {X} R1 {Y} R2.
Arguments W_lex {X R1} W1 {Y R2} W2.

Check lex (fun x y => x < y) (fun x y => x < y).

Check W_lex W_nat W_nat.

Goal W (fun p1 p2  =>  match p1, p2 with
                   | (x1,y1), (x2,y2) => x1 < x2 \/ x1 = x2 /\ y1 < y2
                   end).
Proof.
  exact (W_lex W_nat W_nat).
Qed.

(** Size induction *)

Section Morphism.
  Variables (X: Type) (R: X -> X -> Prop)
            (A: Type) (S: A -> A -> Prop)
            (f: X -> A)
            (Hom: forall x y, R x y -> S (f x) (f y)).

  Definition morphism_Acc x:
    Acc S (f x) -> Acc R x.
  Proof.
    revert x.
    enough (forall a, Acc S a -> forall x, a = f x -> Acc R x) by eauto.
    induction 1 as [a _ IH].
    intros x ->.
    constructor. intros y H.
    apply (IH (f y)). apply Hom, H. reflexivity.
  Qed.
  
  Definition morphism_W :
    W S -> W R.
  Proof.
    intros H x. apply morphism_Acc, H.
  Qed.
End Morphism.  

Definition inv_image {X A} (f: X -> A) {R} :
  W R -> W (fun x y => R (f x) (f y)).
Proof.
  apply morphism_W with (f:=f). auto.
Qed.

Fact wf_size_induction {X A} (f: X -> A) {R} :
  @W A R ->
  forall p: X -> Type, (forall x, (forall y, R (f y) (f x) -> p y) -> p x) -> forall x, p x.
Proof.
  intros H. apply W_omega. apply inv_image, H.
Qed.

Definition LEM := forall X: Prop, X \/ ~X.

Section InfiniteDescent.
  Variable X : Type.
  Variable R : X -> X -> Prop.

  Definition progressive (p: X -> Prop) : Prop :=
    forall x, p x -> exists y, R y x /\ p y.
  
  Definition inf_descent (x:X) :=
    exists p: X -> Prop, progressive p /\ p x.

  Fact Acc_inf_descent_disjoint x :
    Acc R x -> ~inf_descent x.
  Proof.
    induction 1 as [x _ IH].
    intros (p&H1&H2).
    destruct (H1 x H2) as (y&H3&H4).
    apply (IH y). easy. exists p. easy.
  Qed.

  Fact W_inf_descent_disjoint :
    W R -> ~ ex inf_descent.
  Proof.
    intros H [x H1].
    revert H1. apply Acc_inf_descent_disjoint, H.
  Qed.

  Fact Acc_inf_descent_XM :
    LEM -> progressive (fun x => ~ Acc R x).
  Proof.
    intros H x H1.
    destruct (H (exists y : X, R y x /\ ~ Acc R y)) as [H2|H2]. easy. 
    exfalso.
    apply H1. constructor. intros y H3.
    destruct (H (Acc R y)) as [H4|H4]. easy.
    exfalso. eauto.
  Qed.
  
  Fact Acc_inf_descent_exhaustive_XM x :
    LEM -> Acc R x \/ inf_descent x.
  Proof.
    intros H.
    destruct (H (Acc R x)) as [H1|H1]. 1:left; easy.
    right. exists (fun x => ~Acc R x). split. 2: easy.
    apply Acc_inf_descent_XM, H.
  Qed.

  Fact inf_descent_W_XM :
    LEM -> ~ ex inf_descent -> W R.
  Proof.
    intros H H1 x.
    destruct (Acc_inf_descent_exhaustive_XM x H) as [H2|H2].
      + exact H2.
      + contradict H1. eauto.
  Qed.

End InfiniteDescent.


