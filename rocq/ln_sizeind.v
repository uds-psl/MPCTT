From Stdlib Require Import Lia.
Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) : Type := X + ~ X.
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

(** Size induction *)

Lemma size_ind {X} (sigma: X -> nat) (p: X -> Type) :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H.
  enough (forall n x, sigma x < n -> p x) by eauto.
  induction n as [|n IH]. lia. (* CFE *)
  intros x H1. apply H. intros y H2.
  apply IH. lia.
Qed.

Definition size_ind2 {X Y} (sigma: X -> Y -> nat) {p: X -> Y -> Type} :
  (forall x y, (forall x' y', sigma x' y' < sigma x y -> p x' y') -> p x y) ->
  forall x y, p x y.
Proof.
  intros H.
  enough (forall n x y, sigma x y < n -> p x y) by eauto.
  induction n as [|n IH]. lia.
  intros x y H1. apply H. intros x' y' H2.
  apply IH. lia.
Qed.

(** GCDs *)

Definition divides n x : Prop := exists k, x = k * n.
Notation "( n | x )" := (divides n x) (at level 0) : nat_scope.
Definition gamma x y z : Prop :=
  forall n, (n | z) <-> (n | x) /\ (n | y).

Fact gamma_zero y :
  gamma 0 y y.
Proof.
  intros n.
  enough (n | 0) by tauto.
  exists 0. reflexivity.
Qed.

Fact gamma_sym x y z :
  gamma x y z -> gamma y x z.
Proof.
  unfold gamma. firstorder.
Qed.

Fact divides_sub x y n :
  x <= y -> (n | x) -> (n | y) <->  (n | y - x).
Proof.
  intros H [k ->]. split.
  - intros [l ->]. exists (l-k). nia.
  - intros [l H1]. exists (k + l). nia.
Qed.

Fact gamma_sub x y z :
  x <= y -> gamma x (y - x) z -> gamma x y z.
Proof.
  intros H H1 n.
  specialize (H1 n).
  generalize (divides_sub _ _ n H).
  tauto.
Qed.

Definition GCD f (x y: nat) : nat :=
  if x then y else
    if x - y then f x (y - x) else f y x.

Definition sigma x y := 2*x + y.

Fixpoint gcd_index n x y :=
  match n with
  | 0 => 0
  | S n => GCD (gcd_index n) x y
  end.

Definition gcd x y := gcd_index (S (sigma x y)) x y.

Compute gcd 16 24.
Compute gcd 60 48.
Compute gcd 175 5.

Fact gcd_cert :
  forall x y, Sigma z, gamma x y z.
Proof.
  refine (size_ind2 sigma _).
  intros x y IH.
  destruct x.
  - exists y. apply gamma_zero.
  - destruct (S x - y) as [|a] eqn:E.
    + specialize (IH (S x) (y - S x)) as [z IH].
      * unfold sigma; lia.
      * exists z. apply gamma_sub. lia. exact IH.
    + specialize (IH y (S x)) as [z IH].
      * unfold sigma; lia.
      * exists z. apply gamma_sym. exact IH.
Qed.

Notation "f == f'" := (forall x y, f x y = f' x y) (at level 70).

Fact GCD_correct f :
  f == GCD f -> forall x y, gamma x y (f x y).
Proof.
  (* follows proof of gcd_cert *)
  intros H.
  refine (size_ind2 sigma _).
  intros x y IH.
  rewrite H.
  destruct x.
  - cbn. apply gamma_zero.
  - unfold GCD.
    destruct (S x - y) as [|a] eqn:E.
    + apply gamma_sub. lia.
      apply IH. unfold sigma; lia.
    + apply gamma_sym.
      apply IH. unfold sigma; lia.
Qed.
     
 Fact gcd_index_independence n1 n2 x y :
  n1 > sigma x y -> n2 > sigma x y -> gcd_index n1 x y = gcd_index n2 x y.
Proof.
  induction n1 as [|n1 IH] in n2, x, y|-*; intros H1 H2.
  - exfalso; lia.
  - destruct n2. exfalso; lia.
    cbn. unfold GCD.
    destruct x. reflexivity.
    destruct (S x - y) as [|d] eqn:H3.
    + apply IH; unfold sigma in *; lia. 
    + apply IH; unfold sigma in *; lia. 
Qed.

Fact gcd_GCD_correct :
  gcd == GCD gcd.
Proof.
  intros x y. cbn. unfold GCD.
  destruct x. reflexivity.
  destruct (S x - y) eqn:?.
  - apply gcd_index_independence; unfold sigma; lia.
  - apply gcd_index_independence; unfold sigma; lia.
Qed.

Fact gcd_correct :
  forall x y, gamma x y (gcd x y).
Proof.
  apply GCD_correct, gcd_GCD_correct.
Qed.
 

Fact GCD_unique f f' :
  f == GCD f -> f' == GCD f' -> f == f'.
Proof.
  intros H1 H2.
  apply (size_ind2 sigma).
  intros x y IH.
  rewrite H1, H2. unfold GCD.
  destruct x. reflexivity.
  destruct (S x - y) as [|d] eqn:H3.
  - apply IH. unfold sigma; lia.  
  - apply IH. unfold sigma; lia.
Qed.

(** Ackermann *)

Definition A f x y :=
  match x, y with
  | 0, y => S y
  | S x, 0 => f x 1
  | S x, S y => f x (f (S x) y)
  end.

Fact A_unique f g :
  f == A f -> g == A g -> f == g.
Proof.
  intros Ef Eg.
  induction x as [|x IHx].
  - destruct y; rewrite Ef, Eg; reflexivity.
  - induction y as [|y IHy]; rewrite Ef, Eg; cbn; congruence.
Qed.

Fixpoint beta f y :=
  match y with
  | 0 => f 1
  | S y => f (beta f y)
  end.

Fixpoint alpha x :=
  match x with
  | 0 => S
  |S x => beta (alpha x)
  end.

Fact alpha_sat_A :
  alpha == A alpha.
Proof.
  destruct x, y; reflexivity.
Qed.

(** Divisibility *)

Theorem divide n :
  forall x, (Sigma k, x = k * S n) + (forall k, x <> k * S n).
Proof.
  apply (size_ind (fun n => n)). intros x IH.
  destruct x. left. exists 0. lia.
  destruct (n - x) as [|a] eqn:E.
  - specialize (IH (x - n)) as [IH|IH]. lia.
    + left. destruct IH as [k IH]. exists (S k). lia.
    + right. intros k H. specialize (IH (k-1)). nia.
  - right. intros [|k]; lia.
Qed.

Fixpoint W (n x i : nat) : option nat :=
  match i with
  | 0 => None
  | S i => match x with
          | 0 => Some 0
          |S x => match n - x with
                 | 0 => match W n (x - n) i with
                       | Some k => Some (S k)
                       | None => None
                       end
                 | S _ => None
                 end
          end
  end.

Definition D n x := W n x (S x).

Compute D 4 25.

Lemma W_independence {n} :
  forall i i' x, i > x -> i' > x -> W n x i = W n x i'.
Proof.
  induction i as [|i IH]. lia.
  destruct i'. lia.
  intros x H1 H2.
  destruct x. reflexivity.
  cbn. destruct (n - x) as [|a]. 2:reflexivity.
  rewrite (IH i'). reflexivity. lia. lia.
Qed.

Fact D_correct n :
  forall x, match D n x with
       | Some k => x = k * S n
       | None => forall k, x <> k * S n
       end.
Proof.
  unfold D.
  apply (size_ind (fun n => n)). intros x IH.
  destruct x; cbn.
  - reflexivity.
  - destruct (n - x) as [|a] eqn:E.
    + assert (x - n < S x) as H by lia.
      specialize (IH (x - n) H).
      rewrite (W_independence _ (S (x - n))). 2,3:lia.
      destruct W as [k|]. lia.
      intros k H1. specialize (IH (k - 1)). nia.
    + intros [|k]; lia.
Qed.

  
