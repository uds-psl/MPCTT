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

Definition match_nat
  : forall p: nat -> Type, p 0 -> (forall n, p (S n)) -> forall n, p n
  := fun p e1 e2 n =>
       match n with 0 => e1 | S n' => e2 n' end.

Definition elim_nat
  : forall p: nat -> Type, p 0 -> (forall n, p n -> p (S n)) -> forall n, p n
  := fun p e1 e2 => fix F n :=
       match n with 0 => e1 | S n' => e2 n' (F n') end.

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
    all: auto.  (* auto includes discriminate *)
  - intros x IH.
    refine (match_nat _ _ _).
    + auto.
    + intros y. specialize (IH y).
      destruct IH; auto.  (* auto includes injectivity *)
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

Goal nat <> bool.
Proof.
  pose  (p X := forall x y z : X, x = y \/ x = z \/ y = z).
  enough (p bool /\ ~ p nat) as [H1 H2].
  - intros H. apply H2. rewrite H. exact H1.
  - split; unfold p. 
    + intros [|] [|] [|]; auto.
    + intros H. specialize (H 0 1 2) as [H|[H|H]]; discriminate.
Qed.

(*** Procedural Specifications *)

Module Procedural_Specifications.

  Definition Plus f x y :=
    match x with
    | 0 => y
    | S x' => S (f x' y)
    end.
  
  Fact Plus_unique f g :
    (forall x y, f x y = Plus f x y) ->
    (forall x y, g x y = Plus g x y) ->
    forall x y, f x y = g x y.
  Proof.
    intros Hf Hg x y.
    induction x as [|x IH];
      rewrite Hf, Hg; cbn.
    - reflexivity.
    - f_equal. exact IH.
  Qed.
  
  Definition Fib f n :=
    match n with
    | 0 => 0
    | 1 => 1
    | S (S n) => f n + f (S n)
    end.

  Fact Fib_unique f g :
    (forall n, f n = Fib f n) ->
    (forall n, g n = Fib g n) ->
    forall n, f n = g n /\ f (S n) = g (S n).
  Proof.
    intros Hf Hg.
    induction n as [|n [IH1 IH2]].
    - rewrite !Hf, !Hg. easy.
    - split. exact IH2.
      rewrite Hf, Hg; cbn.
      congruence.
  Qed.

  Definition Acker f x y :=
    match x, y with
    | 0, y => S y
    | S x, 0 => f x 1
    | S x, S y => f x (f (S x) y)
    end.

  Fact Acker_unique f g :
    (forall x y, f x y = Acker f x y) ->
    (forall x y, g x y = Acker g x y) ->
    forall x y, f x y = g x y.
  Proof.
    intros Hf Hg.
    induction x as [|x IHx].
    - destruct y;
        rewrite Hf, Hg;
        reflexivity.
    - induction y as [|y IHy];
        rewrite Hf, Hg; cbn.
      + apply IHx.
      + rewrite IHy. apply IHx.
  Qed.
    
End Procedural_Specifications.

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
End Exerci
