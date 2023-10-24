(*** Bool *)

Definition elim_bool
  : forall p: bool -> Type, p true -> p false -> forall x, p x
  := fun p e1 e2 x => match x with true => e1 | false => e2 end.

(* Note: Coq derives the return type function of the match automatically *)

Goal forall x, x = true \/ x = false.
Proof.
  refine (elim_bool _ _ _).
  Show Proof.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Goal forall x, x = true \/ x = false.
Proof.
  intros [|]; auto.
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
    destruct (f false) eqn:H2;
    congruence.
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

(*** Void and Unit *)

Definition elim_void
  : forall Z: Type, False -> Z
  := fun Z a => match a with end.

Definition elim_unit
  : forall p: True -> Type, p I -> forall a, p a
  := fun p e a => match a with I => e end.

Goal forall x: True, x = I.
Proof.
  apply elim_unit.
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
    + intros H. specialize (H 0 1 2) as [H|[H|H]]; discriminate.
Qed.

(*** Notes *)

(* Coq derives eliminators *)
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

