(*** Arithmetic Recursion *)

From Coq Require Import Lia.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).

(*** Complete induction *)

Definition complete_ind {p: nat -> Type} :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H x. apply H.
  induction x as [|x IH]. lia.
  intros y H1. apply H. intros z H3.
  apply IH. lia.
Qed.

Definition Fib f n :=
  if n - 1 then n else f (n - 2) + f (n - 1).

Fact Fib_unique f f' :
  (forall n, f n = Fib f n) -> 
  (forall n, f' n = Fib f' n) -> 
  forall n, f n = f' n.
Proof.
  intros H1 H2. 
  refine (complete_ind _). intros n IH.
  rewrite H1, H2.
  destruct n. reflexivity.
  destruct n. reflexivity.
  cbn. rewrite IH. rewrite IH.
  reflexivity. lia. lia.
Qed.

(*** Size Induction *)

Definition size_ind {X} (sigma: X -> nat) {p: X -> Type} :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) ->
  forall x, p x.
Proof.
  intros H.
  enough (forall n x, sigma x < n -> p x) by eauto.
  induction n as [|n IH]. lia.
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

(*** Euclidean Quotient *)

Definition DIV f x y :=
  if x - y then 0 else S (f (x - S y) y).

Notation "f == f'" := (forall x y, f x y = f' x y) (at level 70).

Fact DIV_unique f f' :
  f == DIV f -> f' == DIV f' -> f == f'.
Proof.
  intros H1 H2 x y.
  revert x. apply complete_ind. intros x IH.
  rewrite H1, H2. unfold DIV.
  destruct (x - y) eqn:?. reflexivity.
  f_equal. apply IH. lia.
Qed.

Fact DIV_unique' f f' :
  f == DIV f -> f' == DIV f' -> f == f'.
Proof.
  intros H1 H2 x y. revert x.
  enough (forall n x, x < n -> f x y = f' x y) by eauto.
  induction n as [|n IH]; intros x H.
  - exfalso; lia.
  - rewrite H1, H2. unfold DIV.
    destruct (x - y) eqn:?.
    + reflexivity.
    + f_equal. apply IH. lia.
Qed.

(*** Step-Indexed Construction *)

Fixpoint Div n x y :=
  match n with
  | 0 => 0
  | S n => DIV (Div n) x y
  end.

Fact Div_index_independence n1 n2 x y :
  n1 > x -> n2 > x -> Div n1 x y = Div n2 x y.
Proof.
  induction n1 as [|n1 IH] in n2, x|-*; intros H1 H2.
  - exfalso; lia.
  - destruct n2. exfalso; lia.
    cbn. unfold DIV.
    destruct (x - y) eqn:?. reflexivity.
    f_equal. apply IH; lia.
Qed.

Definition D x := Div (S x) x.

Fact D_correct :
  D == DIV D.
Proof.
  intros x y. cbn. unfold DIV.
  destruct (x - y) eqn:?. reflexivity.
  f_equal. apply Div_index_independence; lia.
Qed.

Compute D 33 4.

(*** GCD *)

Definition GCD f (x y: nat) : nat :=
  if x then y else
    if x - y then f x (y - x) else f y x.

Definition sigma x y := 2*x + y.

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

Fixpoint gcd_index n x y :=
  match n with
  | 0 => 0
  | S n => GCD (gcd_index n) x y
  end.

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

Definition gcd x y := gcd_index (S (sigma x y)) x y.

Compute gcd 16 24.
Compute gcd 60 48.
Compute gcd 175 5.

Fact gcd_correct :
  gcd == GCD gcd.
Proof.
  intros x y. cbn. unfold GCD.
  destruct x. reflexivity.
  destruct (S x - y) eqn:?.
  - apply gcd_index_independence; unfold sigma; lia.
  - apply gcd_index_independence; unfold sigma; lia.
Qed.

Fact GCD_unique' f f' :
  f == GCD f -> f' == GCD f' -> f == f'.
Proof.
  intros H1 H2.
  enough (forall n x y, sigma x y < n -> f x y = f' x y) by eauto.
  induction n as [|n IH]; intros x y H.
  - exfalso; lia.
  - rewrite H1, H2. unfold GCD.
    destruct x. reflexivity.
    destruct (S x - y) eqn:?.
    + apply IH. unfold sigma in * ; lia.  
    + apply IH. unfold sigma in * ; lia.  
Qed.

Fact gcd_rec (p: nat -> nat -> Type) :
  (forall y, p 0 y) ->
  (forall x y, x <= y -> p x (y - x) -> p x y) ->
  (forall x y, p x y -> p y x) ->
  forall x y, p x y.
Proof.
  intros H1 H2 H3.
  apply (size_ind2 sigma).
  intros x y IH.
  destruct x. {apply H1.}
  destruct (S x - y) eqn:?.
  - apply H2. lia. apply IH. unfold sigma; lia.
  - apply H3, IH. unfold sigma; lia.
Qed.

(*** Vector Types and Course-of-values Recursion *)

Fixpoint vec n X : Type :=
  match n with
  | 0 => unit
  | S n => X * vec n X
  end.

Compute vec 3 nat.
Check (1,(2,(3,tt))) : vec 3 nat.

Fixpoint vecrec {X} (f: forall n, vec n X -> X) n : vec n X :=
  match n with
  | 0 => tt
  | S n => let v := vecrec f n in (f n v, v)
  end.

Definition covrec {X} f n : X := fst (vecrec f (S n)).

Definition vecnat : forall n, vec n nat := vecrec (fun n _ => n).

Compute vecnat 5.
Compute covrec (fun n _ => n*n) 5.

Definition facstep n : vec n nat -> nat :=
  match n with
  | 0 => fun _ => 1
  | S _ => fun v => n * fst v
  end.

Compute covrec facstep 5.

Goal let fac := covrec facstep in
     forall n, fac n = if n then 1 else n * fac (n - 1).
Proof.
  intros fac n.
  destruct n. reflexivity.
  replace (S n - 1) with n by lia.
  reflexivity.
Qed.

Definition fibstep n : vec n nat -> nat :=
  match n with
  | 0 => fun _ => 0
  | 1 => fun _ => 1
  | S (S _) => fun v => fst (snd v) + fst v
  end.

Definition fib := covrec fibstep.

Compute fib 5.

Fact fib_correct n :
  fib n = if n - 1 then n else  fib (n - 2) + fib (n - 1).
Proof.
  destruct n. reflexivity.
  destruct n. reflexivity.
  replace (S (S n) - 2) with n by lia.
  reflexivity.
Qed.

(** Equality decider *)

Definition vec_eqdec X n :
  eqdec X -> eqdec (vec n X).
Proof.
  unfold eqdec, dec. intros d.
  induction n as [|n IH]. 
  - intros [] []. auto.
  - intros [x v] [x' v'].
    specialize (d x x'). specialize (IH v v').
    intuition congruence.
Qed.

(** Tuple Types *)

Fixpoint tup n (p: nat -> Type) : Type :=
  match n with
  | 0 => unit
  | S n => p n * tup n p
  end.

Compute tup 3 (fun n => n = n).

Fixpoint tuprec {p: nat -> Type} (e: forall n, tup n p -> p n) n : tup n p :=
  match n with
  | 0 => tt
  | S n => let t := tuprec e n in (e n t, t)
  end.

Definition tupcov {p} e n : p n := fst (tuprec e (S n)).

Check @tupcov.

(** Vector operations *)

(* Coq's type inference needs a little help *)
Definition cons {X n}
  : X -> vec n X -> vec (S n) X
  := @pair X (vec n X).

Definition evec {X} : vec 0 X := tt.

Fact vec_eta {X n} (v: vec (S n) X) :
  v = cons (fst v) (snd v).
Proof.
  destruct v. reflexivity.
Qed.

Fixpoint snoc {X n}
  : vec n X -> X -> vec (S n) X 
  := match n with
     | 0 => fun _ x => cons x evec
     | S n => fun v x => cons (fst v) (snoc (snd v) x)
     end.

Fixpoint rev {X n}
  : vec n X -> vec n X 
  := match n with
     | 0 => fun v => v
     | S n => fun v => snoc (rev (snd v)) (fst v)
     end.

Compute rev (vecnat 5).
Compute rev (rev (vecnat 5)).

Fact rev_cons X n (v: vec n X) (x: X) :
  rev (cons x v) = snoc (rev v) x.
Proof.
  reflexivity.
Qed.

Fact rev_snoc_cons X n (v: vec n X) (x y: X) :
  rev (snoc (cons x v) y) = snoc (rev (snoc v y)) x.
Proof.
  reflexivity.
Qed.
  
Fact rev_snoc X x n (v: vec n X) :
  rev (snoc v x) = cons x (rev v).
Proof.
  induction n as [|n IH] in v|-*.
  - destruct v. reflexivity.
  - destruct v as [y v]. change (y,v) with (cons y v).
    rewrite rev_snoc_cons. rewrite IH. reflexivity.
Qed.

Fact rev_rev X n (v: vec n X) :
  rev (rev v) = v.
Proof.
  induction n as [|n IH]. reflexivity.
  destruct v as [x v]. change (x,v) with (cons x v).
  rewrite rev_cons. rewrite rev_snoc. f_equal. apply IH.
Qed.
  
Fixpoint last {X n}
  : vec (S n) X -> X :=
  match n with
  | 0 => fun v => fst v
  | S n => fun v => last (snd v)
  end.

Fact last_snoc X n x (v: vec n X) :
  last (snoc v x) = x.
Proof.
  induction n as [|n IH]. reflexivity.
  destruct v as [y v]. change (y,v) with (cons y v).
  cbn. apply IH.
Qed.

Fixpoint sub {X} k {n}
  : vec (S n) X -> X
  := match k with
     | 0 => fun v => fst v
     | S k => match n with
             | 0 => fun v => fst v
             | S n => fun v => sub k (snd v)
             end
     end.

Fact sub0 X n (v: vec (S n) X) :
    sub 0 v = fst v.
Proof.
  reflexivity.
Qed.

Fact sub1 X n (v: vec (S (S n)) X) :
  sub 1 v = fst (snd v).
Proof.
  destruct v. reflexivity.
Qed.

Fact sub_last X n (v: vec (S n) X) :
  sub n v = last v.
Proof.
  induction n as [|n IH]. reflexivity.
  cbn. apply IH.
Qed.

Fixpoint concat {X m n}
  : vec m X -> vec n X -> vec (m + n) X
  := match m with
     | 0 => fun v w => w
     | S m => fun v w => cons (fst v) (concat (snd v) w)
     end.

Compute concat (vecnat 5) (vecnat 3).

(** Type conversion weakness *)

Fact conversion_weakness X n :
  vec (n + 0) X = vec n X.
Proof.
  replace (n + 0) with n by lia.
  reflexivity.
Qed.

Fixpoint transport {X n} : vec n X -> vec (n + 0) X :=
  match n with
  | 0 => fun v => v
  | S _ => fun v => cons (fst v) (transport (snd v))
  end.

Compute transport  (vecnat 10).
