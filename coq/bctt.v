Definition T : nat -> nat :=
  fun x => S (S x).

Lemma demo :
  T 1 = 3.
Proof.
  cbv delta [T].
  cbv beta.
  reflexivity.
Abort.

(** We abort the proof so we can reuse the name [demo]. **)

Definition P : nat -> nat :=
  fun x => match x with 0 => 0 | S x' => x' end.

Lemma demo :
  P 2 = 1.
Proof.
  cbv delta [P].
  cbv beta.
  cbv match. cbv beta.
  reflexivity.
Abort.

Definition D: nat -> nat :=
  fix f x := match x with 0 => 0 | S x' => S (S (f x')) end.

Lemma demo :
  D 1 = 2.
Proof.
  cbv delta [D].
  cbv fix. fold D.
  cbv beta.
  cbv match. cbv beta.
  cbv delta [D].
  cbv fix. fold D.
  cbv beta.
  cbv match.
  reflexivity.
Abort.

Lemma demo :
  D 1 = 2.
Proof.
  cbv delta [D].
  cbv fix. cbv beta.
  cbv match. cbv beta.
  cbv fix. cbv beta.
  cbv match.
  reflexivity.
Abort.

Lemma demo n :
  D (S n) = S (S (D n)).
Proof.
  set (a:= S (S (D n))).
  cbv delta [D]. cbv fix. fold D. cbv beta.
  cbv match. cbv beta.
  subst a.
  reflexivity.
Abort.

Locate "+".
Import Nat. (* Write add for Nat.add *)
Print add.


Lemma demo x :
  2 + x = S (S x).
Proof.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match.
  reflexivity.
Abort.
 
Lemma demo x y :
  S (S x) + y = S (S (x + y)).
Proof.
  set (a:= x+y).
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  reflexivity.
Abort.

(** We compute normal forms of terms describing functions *)

Compute add 0.
Compute add 1.
Compute add 2.
Compute fun x => 3 + x - 2.

(** Alpha conversion *)

Lemma demo :
  (fun n: nat => n) = (fun x => x).
Proof.
  reflexivity.
Abort.

(** Eta conversion *)

Lemma demo :
  add 1 = S.
Proof.
  cbv. reflexivity.
Abort.

Lemma demo :
  (fun x => 3 + x - 2) = S.
Proof.
  cbv. reflexivity.
Abort.

(* We use the predefined iter, which has arguments swapped *)

Check iter.
Compute iter.
Compute iter 2 S.
Compute add 2 = iter 2 S.

Inductive Pair X Y : Type :=
  pair: X -> Y -> Pair X Y.
Check Pair.
Check pair.

Definition swap :=
  fun X Y p => match p with pair _ _ x y => pair Y X y x end.

Lemma demo X Y x y :
  swap X Y (pair X Y x y) = pair Y X y x.
Proof.
  cbv delta. cbv beta. cbv match. cbv beta.
Abort.

(** If-then-else and let notations *)

Set Printing All.

Check fun b: bool => if b then false else true.

(** We define our own product types to demonstrate
    the let notation.  *)     

Inductive prod (X Y: Type) : Type :=
| pair : X -> Y -> prod X Y.

Check fun a: prod nat nat => let (x,y) := a in pair nat nat y x.

(** Matches are equipped with return types,
    simple function types are printed as dependent function types,
    a generalization of both polymorphic function types and simple function types
    that will be explained later. *)

Unset Printing All.

Check fun b: bool => if b then false else true.
Check fun a: prod nat nat => let (x,y) := a in pair nat nat y x.

(** Commands used:
    Abort, Inductive,
    Definition, Lemma, Proof, Compute, Check
    Set Printing All   
 *)
(** Tactics used:
    cbv, fold, set, subst, reflexivity
 *)
