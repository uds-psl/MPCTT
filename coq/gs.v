(** We use the predefined type of booleans and
    define boolean negation and boolean conjunction *)

Print bool.
(** Read "Set" as "Type" *)
Check bool.
Check true.
Check false.

Definition negb (x: bool) : bool :=
  match x with true => false | false => true end.

Compute negb (negb (negb true)).

Lemma L11 x :
  negb (negb x) = x.
Proof.
  destruct x.
  - reflexivity.
  - reflexivity.
Qed.

Definition andb (x y: bool) : bool :=
  match x with true => y | false => false end.

Definition orb (x y: bool) : bool :=
  match x with true => true | false => y end.

Lemma L12 x y z :
  andb x (orb y z) = orb (andb x y) (andb x z).
Proof.
  destruct x.
  - cbn. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma L13 x y :
  andb x y = andb y x.
Proof.
  destruct x, y; reflexivity.
Qed.

(* Syntactic sugar *)

Definition negb' (x: bool) := if x then false else true.
Check negb'.

Goal negb = negb'.
Proof.
  reflexivity.
Qed.

Definition andb' (x y: bool) := if x then y else false.
Check andb'.

Goal andb = andb'.
Proof.
  reflexivity.
Qed.

(** We use the predefined type of numbers. *)

Print nat.

Fixpoint add (x y: nat) : nat :=
  match x with 0 => y | S x' => S (add x' y) end.

Compute add 2 7.
  
Lemma add0 x :
  add x 0 = x.
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma addS x y:
  add x (S y) = S (add x y).
Proof.
  induction x as [|x IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma add_comm x y:
  add x y = add y x.
Proof.
  induction x as [|x IH]; cbn.
  - rewrite add0. reflexivity.
  - rewrite IH, addS. reflexivity.
Qed.

Fixpoint sub (x y: nat) : nat :=
  match x, y with
    0, _  => 0
  | S x', 0 => x
  | S x', S y' => sub x' y'
  end.

Lemma add_sub x y :
  sub (add x y) y = x.
Proof.
  induction y as [|y IH].
  - rewrite add0. destruct x; reflexivity.
  - rewrite addS. cbn. exact IH.
Qed.

(** Ackermann function. *) 

Fixpoint acker' (f: nat -> nat) (x:nat) : nat :=
  match x with 0 => f 1 | S x' => f (acker' f x') end.

Fixpoint acker (x:nat) : nat -> nat :=
  match x with 0 => S | S x' => acker' (acker x') end.

Lemma Ackermann x y :
  acker (S x) (S y) = acker x (acker (S x) y).
Proof.
  cbn [acker]. cbn [acker']. reflexivity.
Qed.

(** We now use the predefined pairs. *)

Print prod.

(** We define a polymorphic swap function with
    implicit arguments. *)

Definition swap (X Y: Type) (a: X * Y) : Y * X := 
  match a with (x,y) => (y,x) end.

Arguments swap [X Y].

Lemma L_swap X Y (p: X*Y) :
  swap (swap p) = p.
Proof.
  destruct p as [x y]. reflexivity.
Qed.

Print fst.

Lemma eta_law X Y (p: X*Y) :
  (fst p, snd p) = p.
Proof.
  destruct p as [x y]. reflexivity.
Qed.

(* Syntactic sugar and type inference *)

Definition swap' X Y '(x,y) : Y * X := (y,x).
Check swap'.

(** We make the objects of the predefined module Nat available
    without the module prefix, for instance, add rather than Nat.add.
    This shadows our previous definitions of add and sub.  *) 

Print Nat.
Import Nat.
Check add.
Check iter.

(** We redefine the polymorphic iteration function. *)

Fixpoint iter (X: Type) (f: X -> X) (n:nat) (x:X) : X :=
  match n with 0 => x | S n' => f (iter X f n' x) end.

Arguments iter [X].

Lemma iter_add n x :
  n + x = iter S n x.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - now rewrite IH. 
Qed.

Lemma iter_mul n x :
  n * x = iter (add x) n 0.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma iter_pow n x :
  x^n = iter (mul x) n 1.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma iter_shift X (f: X -> X) n x :
  iter f (S n) x = iter f n (f x).
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - now rewrite <-IH.
Qed.

Definition step '(n, a) := (S n, S n*a).

Fixpoint fac (n:nat) : nat :=
  match n with 0 => 1 | S n' => S n' * fac n' end.

Lemma iter_fact n :
  (n, fac n) = iter step n (0,1).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [iter fac]. rewrite <-IH. reflexivity.
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

Lemma iter_even' n b :
  iter negb (S(n*2)) b = negb b.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn. rewrite L11. exact IH.
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
  intros. lia.
Qed.

Goal forall x y z, x*(y + z) = x*y + x*z.
Proof.
  lia.
Qed.

Goal forall x y, (x + y)^2 = x^2 + 2*x*y + y^2.
Proof.
  cbn. lia.
Qed.

(** We have been using the inductive types of booleans,
    numbers, and pairs as defined in the library.  
    Equivalent definitions are given below.  *)

Module TypeDefinitions.
  Inductive bool : Type := true | false.
  Inductive nat : Type := O | S (_:nat).
  Inductive prod (X Y: Type) : Type := pair (_:X) (_:Y).
End TypeDefinitions.


(** Comands used:
    Print, Check, Compute, 
    Definition, Fixpoint, Arguments,
    Lemma, Proof, Qed, Goal,
    Import Nat, 
    From Coq Require Import Lia 
 *)
(** Tactics used:
    cbn, reflexivity, destruct, induction, rewrite, exact,
    lia
 *)
