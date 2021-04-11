(*** Bool *)

Definition elim_bool
  : forall p: bool -> Type, p true -> p false -> forall x, p x
  := fun p a b x => match x with true => a | false => b end.

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

(*** Nat *)

Definition match_nat
  : forall p: nat -> Type, p 0 -> (forall n, p (S n)) -> forall n, p n
  := fun p h f n =>
       match n with 0 => h | S n' => f n' end.

Definition elim_nat
  : forall p: nat -> Type, p 0 -> (forall n, p n -> p (S n)) -> forall n, p n
  := fun p h f => fix F n :=
       match n with 0 => h | S n' => f n' (F n') end.

Goal forall x, x + 0 = x.
Proof.
  refine (elim_nat _ _ _).
  - reflexivity.
  - intros n IH. cbn. rewrite IH. reflexivity.
Qed.

Goal forall x y: nat, x = y \/ x <> y.
Proof.
  refine (elim_nat _ _ _).
  - refine (match_nat _ _ _).
    all: auto.
  - intros x IH.
    refine (match_nat _ _ _).
    + auto.
    + intros y. specialize (IH y). intuition.
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

Goal forall x y, plus x y = x + y.
Proof.
  refine (elim_nat _ _ _).
  - cbv. reflexivity.
  - intros n IH y. cbn. rewrite IH. reflexivity.
Qed.
  

(*** [nat <> bool] *)

Lemma diseq X (x y: X) :
 (exists p, ~ p x /\ p y) -> x <> y.
Proof.
  intros (p&H1&H2) <-. auto.
Qed.

Goal nat <> bool.
Proof.
  apply diseq.
  exists  (fun X => forall x y z : X, x = y \/ x = z \/ y = z).
  split.
  - intros H.
    specialize (H 0 1 2) as [H|[H|H]]; discriminate.
  - intros [|] [|] [|]; auto.
Qed.

(*** Exercises *)

Module Exercises.
Fixpoint eq_nat x y : bool :=
  match x, y with
  | 0, 0 => true
  | 0, S _ => false
  | S _, 0 => false
  | S x', S y' => eq_nat x' y'
  end.

Goal forall x y, x = y <-> eq_nat x y = true.
Proof.
  refine (elim_nat _ _ _).
  - intros [|y]; cbn.
    + intuition.
    + intuition congruence.
  - intros x IH [|y]; cbn.
    + intuition congruence.
    + specialize (IH y). intuition.
Qed.

Definition plus
  : nat -> nat -> nat
  := fun x y => elim_nat (fun _ => nat) y (fun _ a => S a) x.

Goal forall x y, plus x y = x + y.
Proof.
  refine (elim_nat _ _ _).
  - reflexivity.
  - intros x IH y.
    change (plus (S x) y) with (S (plus x y)).
    rewrite IH. reflexivity.
Qed.

Definition minus : nat -> nat -> nat
  := elim_nat _
              (fun _ => 0)
              (fun x f => match_nat _ (S x) f).

Compute minus 4 2.
Compute minus 4 5.

Goal forall x y, minus x y = x - y.
Proof.
  induction x as [|x IH].
  - reflexivity.
  - intros [|y].
    + reflexivity.
    + cbn. apply IH.
Qed.
End Exercises.
