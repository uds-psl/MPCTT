(*** MPCTT, Chapter Sum Types *)

Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.

Module SumTypes.
  Inductive sum (X Y: Type) : Type := L (x : X) | R (y : Y).
  
  Arguments L {X Y}.
  Arguments R {X Y}.
  
  Definition match_sum (X Y Z: Type) 
    : sum X Y -> (X -> Z) -> (Y -> Z) -> Z
    := fun a e1 e2 => match a with L x => e1 x | R y => e2 y end.
 
  Definition elim_sum (X Y: Type) (p: sum X Y -> Type)
    : (forall x, p (L x)) -> (forall y, p (R y)) -> forall a, p a
    := fun e1 e2 a => match a with L x => e1 x | R y => e2 y end.

  Fact L_injective (X Y: Type) (x x': X) :
    @L X Y x = L x' -> x = x'.
  Proof.
    intros H.
    change (match_sum X Y X (L x) (fun x => x) (fun _ => x) = x').
    rewrite H. cbn.
    reflexivity.
  Qed.

  Fact L_R_disjoint X Y (x:X) (y:Y) :
    L x <> R y.
  Proof.
    intros H.
    change (match_sum X Y Prop (L x) (fun x => False) (fun y => True)).
    rewrite H. cbn.
    exact I.
  Qed.
End SumTypes.

(* From now on we use Coq's predefined sum types *)

Locate "+".
Print sum.
Print unit.

Goal forall a : False + unit,
    a = inr tt.
Proof.
  destruct a as [x|y].
  - destruct x.
  - destruct y. reflexivity.
Qed.

Goal forall a : (False + unit) + unit,
    a = inr tt \/ a = inl (inr tt).
Proof.
  destruct a as [x|y].
  - right. destruct x  as [x|y].
    + destruct x.
    + destruct y. reflexivity.
  - left. destruct y. reflexivity.
Qed.

Goal forall a : ((False + unit) + unit) + unit,
    a = inr tt \/ a = inl (inr tt) \/ a = inl (inl (inr tt)).
Proof.
  destruct a as [x|y].
  - right. destruct x as [x|y].
    + right. destruct x as [x|y].
      * destruct x.
      * destruct y. reflexivity.
    + left. destruct y. reflexivity.
  - left. destruct y. reflexivity.
Qed.


Section Exercise.
  Variables X Y : Type.
  Let  T (a: X + Y) := if a then true else false.
  Goal forall a, if T a then exists x, a = inl x else exists y, a = inr y.
  Proof.
    intros [x|y].
    - cbn. exists x. reflexivity.
    - cbn. exists y. reflexivity.
  Qed.
End Exercise.

(*** Proving at Type Level *)

Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Section Exercise.
  Variables X Y Z : Type.
  Goal (X + Y -> Z) <=> (X -> Z) * (Y -> Z).
  Proof.
    unfold iffT. tauto.
  Qed.
  
  Goal (X + Y -> Z) <=> (X -> Z) * (Y -> Z).
  Proof.
    split.
    - intros f. split.
      + intros x. apply f. left. exact x.
      + intros y. apply f. right. exact y.
    - intros [f g]. intros [x|y].
      + apply f,x.
      + apply g,y.
  Qed.
End Exercise.

From Coq Require Import Bool.
Module Exercise.
  Goal forall x y : bool,
      x && y = false <=> (x = false) + (y = false).
  Proof.
    destruct x, y; cbn; unfold iffT; tauto.
  Qed.
End Exercise.

Goal forall X Y,
    X + Y <=> forall Z, (X -> Z) -> (Y -> Z) -> Z.
Proof.
  intros *. split.
  - intros [x|y]; auto.
  - intros F. apply F; auto.
Qed.

(*** Decision Types *)

Definition dec (X: Type) : Type := X + (X -> False).

Goal forall X Y,
    dec X -> dec Y -> dec (X + Y).
Proof.
  unfold dec. tauto.
Qed.

Goal forall X Y,
    (X <=> Y) -> dec X -> dec Y.
Proof.
  unfold dec, iffT. tauto.
Qed.

Goal forall X (f: X -> bool) x,
    dec (f x = true).
Proof.
  intros *. destruct (f x) as [|].
  - left. reflexivity.
  - right. easy.
Qed.

(*** Certifying Equality Deciders *)

Goal forall x y: nat, (x = y) + (x <> y).
Proof.
  induction x as [|x IH]; destruct y.
  - left. reflexivity.
  - right. easy.
  - right. easy.
  - destruct (IH y) as [H|H].
    + left. congruence.
    + right. congruence.
Qed.

Definition eqdec X := forall x y: X, dec (x = y).

Fact eqdec_bot : eqdec False.
Proof.
  intros [].
Qed.

Definition nat_eqdec : eqdec nat.
Proof.
  hnf. induction x as [|x IH]; destruct y.
  - left. reflexivity.
  - right. congruence.
  - right. congruence.
  - destruct (IH y) as [H|H].
    + left. congruence.
    + right. congruence.
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

Fact eqdec_sum X Y :
  eqdec X * eqdec Y <=> eqdec (X + Y).
Proof.
  split.
  - intros [dX dY] [x1|y1] [x2|y2].
    + destruct (dX x1 x2); unfold dec in *; intuition congruence.
    + unfold dec in *; intuition congruence.
    + unfold dec in *; intuition congruence.
    + destruct (dY y1 y2); unfold dec in *; intuition congruence.
  - intros d; split.
    + intros x1 x2.
      destruct (d (inl x1) (inl x2)); unfold dec in *; intuition congruence.
    + intros y1 y2.
      destruct (d (inr y1) (inr y2)); unfold dec in *; intuition congruence.
Qed.

Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Fact eqdec_injective {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H d x x'. specialize (H x x').
  destruct (d (f x) (f x')) as [H1|H1];
    unfold dec in *; intuition congruence.
Qed.

Fixpoint nat_eqb (x y: nat) : bool :=
  match x, y with
  | 0, 0 => true
  | 0, _ => false
  | S x, 0 => false
  | S x, S y => nat_eqb x y
  end.

Fact nat_eqb_correct x y :
  if nat_eqb x y then x = y else x <> y.
Proof.
  revert y.
  induction x as [|x IH]; destruct y; cbn.
  - reflexivity.
  - congruence.
  - congruence.
  - specialize (IH y).
    destruct (nat_eqb x y).
    + congruence.
    + congruence.
Qed.




