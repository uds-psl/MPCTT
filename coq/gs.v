(** We first give some basic definitions.  We do this in a module
    so that afrewards we can use the respective definitions 
    from the standard libraries.  *)

Module Definitions.
 
  Inductive bool : Type :=
  | true : bool
  | false : bool.
 
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Inductive prod (X Y: Type) : Type :=
  | pair : X -> Y -> prod X Y.

  Definition negb (x: bool) : bool :=
    match x with
    | true => false
    | false => true
    end.

  Definition andb (x y: bool) : bool :=
    match x with
    | true => y
    | false => false
    end.

  Definition orb (x y: bool) : bool :=
    match x with
    | true => true
    | false => y end.
  
  Fixpoint add (x y: nat) : nat :=
    match x with
    | O => y
    | S x' => S (add x' y)
    end.
  
  Fixpoint mul (x y: nat) : nat :=
    match x with
    | O => O
    | S x' => add y (mul x' y)
    end.

  Fixpoint sub (x y: nat) : nat :=
    match x, y with
    | O, _  => O
    | S x', O => x
    | S x', S y' => sub x' y'
    end.

  Check pair.
  Check pair nat.
  Check pair nat bool.
  Check pair nat bool (S O).
  Check pair nat bool (S O) false.
  Check pair _ _ (S O) false.
  
  Arguments pair {X Y}.
  Check pair (S O) false.
  Check pair.
  Check @pair.
  Check @pair nat.
  Check @pair nat bool.
  Check @pair nat bool (S O).
  
  Definition swap {X Y: Type} (a: prod X Y) : prod Y X := 
    match a with
    |  pair x y => pair y x
    end.

  Definition fst {X Y: Type} (a: prod X Y) : X :=
    match a with
    |  pair x _ => x
    end.

  Definition snd {X Y: Type} (a: prod X Y) : Y :=
    match a with
    |  pair _ y => y
    end.

  Check negb.
  Compute negb (negb (negb true)).
  Check orb.
  Compute orb false true.
  Check mul.
  Compute mul (S (S O)) (S (S (S O))).
  Compute sub (S (S (S O))) (S (S O)).
  Check swap.
  Check swap (pair O true).
  Compute swap (pair O true).
End Definitions.

Check Definitions.orb.
Check Definitions.swap.

(** We now switch to the definitions from the library.  
    They come with convenient notations.        *)

Locate "+".
Check Nat.add.
Check Nat.sub.
Check Nat.mul.
Print Nat.mul.

Check nat.
Check bool.
(** Read "Set" as "Type" *)
Print nat.
Print bool.

From Coq Require Import Bool.

Lemma L11 x :
  negb (negb x) = x.
Proof.
  destruct x.
  - cbn. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma L12 x y :
  x && y = y && x.
Proof.
  destruct x.
  - cbn. destruct y.
    + cbn. reflexivity.
    + cbn. reflexivity.
  - cbn. destruct y.
    + cbn. reflexivity.
    + cbn. reflexivity.
Qed.

Lemma L12' x y :
  x && y = y && x.
Proof.
  destruct x, y; reflexivity.
Qed.

Lemma L13 x y z :
  x && (y || z) = x && y || x &&z.
Proof.
  destruct x.
  - cbn. reflexivity.
  - cbn. reflexivity.
Qed.

(** if-then-else notation *)

Lemma L14 (x: bool) :
  (if x then false else true) = match x with true => false | false => true end.
Proof.
  reflexivity.
Qed.

Print nat.

Compute 2 + 7.
Check S (S O).

Lemma add0 x :
  x + 0 = x.
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma addS x y:
  x + S y = S (x + y).
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma add_comm x y:
  x + y = y + x.
Proof.
  induction x as [|x IH]; cbn.
  - rewrite add0. reflexivity.
  - rewrite IH, addS. reflexivity.
Qed.

Lemma add_sub x y :
  (x + y) - y = x.
Proof.
  induction y as [|y IH].
  - rewrite add0. destruct x; reflexivity.
  - rewrite addS. cbn. exact IH.
Qed.

(** Ackermann function *) 

Fixpoint acker' (f: nat -> nat) (x:nat) : nat :=
  match x with
  | 0 => f 1
  | S x' => f (acker' f x')
  end.

Fixpoint acker (x:nat) : nat -> nat :=
  match x with
  | 0 => S
  | S x' => acker' (acker x')
  end.

Lemma Ackermann x y :
  acker (S x) (S y) = acker x (acker (S x) y).
Proof.
  cbn [acker]. cbn [acker']. reflexivity.
Qed.

(** We now use the predefined pairs. *)

Locate "*".
Print prod.

(** We define a polymorphic swap function with
    implicit arguments. *)

Definition swap {X Y: Type} (a: X * Y) : Y * X := 
  match a with (x,y) => (y,x) end.

Lemma swap_swap X Y (a: X * Y) :
  swap (swap a) = a.
Proof.
  destruct a as [x y]. cbn. reflexivity.
Qed.

Lemma eta_law X Y (a: X * Y) :
  (fst a, snd a) = a.
Proof.
  destruct a as [x y]. cbn. reflexivity.
Qed.

(** Syntactic sugar and type inference *)

Definition swap' {X Y} '(x,y) : Y * X := (y,x).

Goal @swap' = @swap.
Proof.
  reflexivity.
Qed.

(** We make the objects of the predefined module Nat available
    without the module prefix, for instance, add rather than Nat.add. *) 

Print Nat.
Import Nat.
Check add.
Check sub.

(** We redefine the polymorphic iteration function. *)

Fixpoint iter {X: Type} (f: X -> X) (n:nat) (x:X) : X :=
  match n with
  | 0 => x
  | S n' => f (iter f n' x)
  end.

Lemma iter_add n x :
  n + x = iter S n x.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma iter_mul n x :
  n * x = iter (add x) n 0.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma iter_pow n x :
  x^n = iter (mul x) n 1.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma iter_shift X (f: X -> X) n x :
  iter f (S n) x = iter f n (f x).
Proof.
  induction n as [|n IH].
  - cbn. reflexivity.
  - cbn. f_equal. exact IH.
Qed.

Fixpoint fac (n :nat) : nat :=
  match n with
  | 0 => 1
  | S n' => S n' * fac n'
  end.

Definition step '(n, a) := (S n, S n * a).

Lemma iter_fact n :
  (n, fac n) = iter step n (0,1).
Proof.
  induction n as [|n IH].
  - cbn. reflexivity.
  - cbn [iter step fac]. rewrite <-IH. reflexivity.
Qed.

Compute fac 5.
Compute iter step 5 (0,1).

Lemma iter_even n b :
  iter negb (n*2) b = b.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite L11. exact IH.
Qed.

(** There is automation available for arithmetic proofs. *)

From Coq Require Import Lia.

Goal forall x y, x + y - y = x.
Proof.
  lia.
Qed.

Goal forall x y, x * y  = y * x.
Proof.
  lia.
Qed.

Goal forall x y z, x * y * z = (x * y) * z.
Proof.
  lia.
Qed.

Goal forall x y z, x*(y + z) = x*y + x*z.
Proof.
  lia.
Qed.

Goal forall x y, (x + y)^2 = x^2 + 2*x*y + y^2.
Proof.
  cbn. lia.
Qed.

(** ADVICE: Coq comes with lots of involved natatotional conveniences,
    including infix notations, type inference, and implicit arguments.
    This can be confusing.  It is important to understand 
    what a phrase elaborates to once all notational conveniences are removed. *)

Set Printing All.
Print swap.
Print swap'.
Check 6.
Check 2+3.
Unset Printing All.
Check 2 + 3.

(** There is a command that prints all defined constants *)

Print All.


(** Comands used:
    Print, Check, Compute, 
    Definition, Fixpoint, Arguments,
    Lemma, Proof, Qed, Goal,
    Import Nat, 
    From Coq Require Import Lia
    Set Printing All.
    Unset Printing All. 
    Print All.
 *)
(** Tactics used:
    cbn, reflexivity, destruct, induction, rewrite, exact, f_equal,
    lia
 *)
