(*** MPCTT, Chapter 5 *)

(* We define and apply inductive eliminators *)

(*** Void and Unit *)

Module VoidUnit.
   Inductive bot : Prop := .
   Inductive top : Prop := I.

   Definition elim_bot
     : forall Z: Type, bot -> Z
     := fun Z a => match a with end.

   Definition elim_top
     : forall p: top -> Type, p I -> forall a, p a
     := fun p e a => match a with I => e end.

   Goal bot <-> False.
   Proof.
     split.
     - apply elim_bot.
     - apply False_ind.
       Show Proof.
   Qed.

   Goal forall x: top, x = I.
   Proof.
     apply elim_top.
     reflexivity.
     Show Proof.
   Qed.

   Goal forall x: top, x = I.
   Proof.
     exact (fun x => match x with I => eq_refl I end).
   Qed.

   Inductive F: Prop := C (_: F).

   Definition elim_F
     : forall Z: Type, F -> Z
     := fun Z => fix f a := match a with C a => f a end.

   Goal F <-> bot.
   Proof.
     split.
     - apply elim_F.
     - apply elim_bot.
       Show Proof.
   Qed.
End VoidUnit.

(*** Bool *)

Definition elim_bool
  : forall p: bool -> Type, p true -> p false -> forall x, p x
  := fun p e1 e2 x => match x with true => e1 | false => e2 end.

Print elim_bool.
(* Note: Coq derives the return type function of the match *)

Goal forall x, x = true \/ x = false.
Proof.
  refine (elim_bool _ _ _).
  Show Proof.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Check fun p: bool -> Prop => elim_bool p.
Check fun p: bool -> Type => elim_bool p.
Check fun p: bool -> Prop => p true.
Check fun p: bool -> Type => p true.

Goal forall x, x = true \/ x = false.
Proof.
  intros [|]; auto.
  Show Proof.
Qed.

Goal forall (f: bool -> bool) x, f (f (f x)) = f x.
Proof.
  intros f.
  enough (forall x y z, f true = y -> f false = z -> f (f (f x)) = f x) by eauto.
  refine (elim_bool _ _ _).
  all: refine (elim_bool _ _ _).
  all: refine (elim_bool _ _ _).
  all: congruence.
Qed.

Goal forall (f: bool -> bool) x, f (f (f x)) = f x.
Proof.
  intros f.
  enough (forall x y z, f true = y -> f false = z -> f (f (f x)) = f x) by eauto.
  intros [|] [|] [|]; congruence.
Qed.

Goal forall (f: bool -> bool) x, f (f (f x)) = f x.
Proof.
  destruct x;
    destruct (f true) eqn:H1;
    destruct (f false) eqn:H2.
    all: congruence.
Qed.

(*** Nat *)

Definition elim_nat
  : forall p: nat -> Type, p 0 -> (forall n, p n -> p (S n)) -> forall n, p n
  := fun p e1 e2 => fix F n :=
       match n with 0 => e1 | S n' => e2 n' (F n') end.

Definition match_nat
  : forall p: nat -> Type, p 0 -> (forall n, p (S n)) -> forall n, p n
  := fun p e1 e2 n =>
       match n with 0 => e1 | S n' => e2 n' end.

Goal forall x, x + 0 = x.
Proof.
  refine (elim_nat _ _ _).
  - reflexivity.
  - intros n IH. cbn. rewrite IH. reflexivity.
Qed.

Goal forall x y,
    x + y = elim_nat (fun _ => nat) y (fun _ => S) x.
Proof.
  intros *. 
  induction x as [|x IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Goal forall x y,
    x + y = elim_nat (fun _ => nat -> nat) (fun y => y) (fun _ a y => S (a y)) x y.
Proof.
  intros *.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fixpoint  plus (x: nat) : nat -> nat :=
  match x with
  | 0 => fun y => y
  | S x' => fun y => S (plus x' y)
  end.

Goal plus = elim_nat (fun _ => nat -> nat) (fun y => y) (fun x a y => S (a y)).
Proof.
  cbv. reflexivity.
Qed.

Goal forall x y: nat, x = y \/ x <> y.
Proof.
  refine (elim_nat _ _ _).
  - refine (match_nat _ _ _).
    all: auto.  (* auto includes discriminate *)
  - intros x IH.
    refine (match_nat _ _ _).
    + auto.
    + intros y. specialize (IH y).
      destruct IH; auto.  (* auto includes injectivity *)
Qed.

Goal forall x y: nat, x = y \/ x <> y.
Proof.
  induction x as [|x IH]; destruct y.
  1-3: auto.
  specialize (IH y) as [IH|IH].
  - left. congruence.
  - right. congruence.
Qed.

Fixpoint eq_nat (x y: nat) : bool :=
  match x, y with
  | 0, 0 => true
  | 0, S _ => false
  | S _, 0 => false
  | S x, S y => eq_nat x y
  end.

Fact eq_nat_correct x y :
  eq_nat x y = true <-> x = y.
Proof.
  revert x y.
  refine (elim_nat _ _ _).
  - refine (elim_nat _ _ _).
    + cbn. easy.
    + intros y _. cbn. easy.
  - intros x IH.
    refine (elim_nat _ _ _).
    + cbn. easy.
    + intros y _. cbn. specialize (IH y). split.
      * intros H. f_equal. apply IH, H.
      * intros H. apply IH. congruence.
Qed.

Goal forall x y: nat, x = y \/ x <> y.
Proof.
  intros x y.
  assert (H:= eq_nat_correct x y).
  destruct (eq_nat x y).
  - left. apply H. easy.
  - right. intros H1.
    enough (false = true) by easy.
    apply H, H1.
Qed.
  
Module Exercise.
  Notation "x <= y" := (x - y = 0) : nat_scope.
  Fact antisymmetry x y :
    x <= y -> y <= x -> x = y.
  Proof.
    revert y.
    induction x as [|x IH]; destruct y.
    all:auto.
  Qed.
End Exercise.

(*** Pairs *)

Definition elim_pair
  : forall (X Y: Type) (p: X * Y -> Type), (forall x y, p(x,y)) -> forall a, p a
  := fun X Y p e => fix F a :=
    match a with (x,y) => e x y end.

Definition fst
  : forall X Y, X * Y -> X
  := fun X Y => elim_pair X Y _ (fun x _ => x).

Definition snd
  : forall X Y, X * Y -> Y
  := fun X Y => elim_pair X Y _ (fun _ y => y).

Goal forall X Y (a: X * Y), a = (fst _ _ a, snd _ _ a).
Proof.
  intros X Y.
  apply elim_pair.
  cbn.
  reflexivity.
Qed.

(*** [nat <> bool] *)

Goal nat <> bool.
Proof.
  pose  (p X := forall x y z : X, x = y \/ x = z \/ y = z).
  enough (p bool /\ ~ p nat) as [H1 H2].
  - intros H. apply H2. rewrite H. exact H1.
  - split; unfold p. 
    + intros [|] [|] [|]; auto.
    + intros H. specialize (H 0 1 2) as [H|[H|H]]; congruence.
Qed.

(*** Coq's Set considered harmful *)

(* Coq has a subuniverse Set of Type and type inference uses
    Set rather than type if it can.  In particular, the predefined
    types bool and nat are typed with Set.  This can lead to
    annoying problems.  An example follows. *)

Check nat.
Check bool.
Set Printing All.
Check nat <> bool.

Lemma eq_not (X: Type) (x y : X) (p: X -> Prop) :
  ~ p x -> p y -> x <> y.
Proof.
  intros H H1. contradict H. rewrite H. exact H1.
Qed.

Definition card_le2 (X: Type) :=
  forall x y z : X, x = y \/ x = z \/ y = z.

Goal nat <> bool.
Proof.
  Fail apply (eq_not Type nat bool card_le2).
  enough (not (@eq Type nat bool)) as H.
  - contradict H. rewrite H. reflexivity.
  - apply (eq_not Type _ _ card_le2).
    + intros H. specialize (H 0 1 2) as [H|[H|H]]; congruence.
    + intros [|] [|] [|]; auto.
Qed.
Unset Printing All.

(*** Coq derives eliminators *)
Check bool_rect.
Check nat_rect.
Check prod_rect.
Check False_rect.
Check True_rect.
(* Coq doesn't derive most general eliminator for True by default *)
Check and_ind.
Check and_rect.
Check or_ind.

Check False_rect nat.
Check False_rect (nat -> nat).
Check False_rect (nat -> nat -> nat).

