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

Fact GCD_certifying :
  forall x y, sig (gamma x y).
Admitted.

Fact GCD_simply_typed :
  Sigma G, forall x y, gamma x y (G x y).
Admitted.

        
(** Step functions *)

Definition sat2 {X Y Z} (f: X -> Y -> Z) F := forall x y, f x y = F f x y.

Definition A f x y :=
  match x, y with
  | 0, y => S y
  | S x, 0 => f x 1
  | S x, S y => f x (f (S x) y)
  end.

Fact A_unique f g :
  sat2 f A -> sat2 g A -> forall x y, f x y = g x y.
Proof.
  intros Ef Eg.
  induction x as [|x IHx].
  - destruct y; rewrite Ef, Eg; reflexivity.
  - induction y as [|y IHy]; rewrite Ef, Eg; cbn; congruence.
Qed.

Fixpoint h g y :=
  match y with
  | 0 => g 1
  | S y => g (h g y)
  end.

Fixpoint f x :=
  match x with
  | 0 => S
  |S x => h (f x)
  end.

Fact f_sat_A :
  sat2 f A.
Proof.
  hnf.
  destruct x, y; reflexivity.
Qed.

(** Left over *)

Module Div.
Definition Div f (x n : nat) : option nat :=
  if x then Some 0 else
    if x - n  (* x < S n *)
    then  None
    else match f (x - S n) n with Some k => Some (S k) | None => None end.

Fixpoint DIV k : nat -> nat -> option nat :=
  match k with
  | 0 => fun _ _ => None
  | S k => Div (DIV k)
  end.

Definition D x n := DIV (S x) x n.

Compute D 48 3.
End Div.
 

  
