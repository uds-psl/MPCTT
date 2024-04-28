(*** MPCTT, Chapter 2 *)

(* We show how Coq realizes basic CTT *)

(* We start with the definitions of the inductive types 
   for booleans, numbers, and pairs.  We also define 
   some inductive functions for these types.        
   We enclose the definitions in a module so that 
   the predefined definitions can be used afterwards. *)        

Module Definitions.
 
  Inductive bool : Type :=
  | true : bool
  | false : bool.
 
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Inductive Pair (X Y: Type) : Type :=
  | pair : X -> Y -> Pair X Y.

  Definition negb (x: bool) : bool :=
    match x with
    | true => false
    | false => true
    end.
  
  Fixpoint add (x y: nat) : nat :=
    match x with
    | O => y
    | S x => S (add x y)
    end.
  
  Fixpoint mul (x y: nat) : nat :=
    match x with
    | O => O
    | S x => add y (mul x y)
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

  (* declare implicit arguments *)
  Arguments pair {X Y}. 
  Check pair (S O) false.
  Check @pair nat bool (S O).
  Check @pair.
  Check @pair nat.
  Check @pair nat bool.
  Check pair.
  
  Definition swap {X Y: Type} (a: Pair X Y) : Pair Y X := 
    match a with
    |  pair x y => pair y x
    end.

  Definition fst {X Y: Type} (a: Pair X Y) : X :=
    match a with
    |  pair x _ => x
    end.
  
  Check negb.
  Compute negb (negb (negb true)).
  Check mul.
  Compute mul (S (S O)) (S (S (S O))).
  Compute sub (S (S (S O))) (S (S O)).
  Check swap.
  Check swap (pair O true).
  Compute swap (pair O true).
End Definitions.

(** We now look at predefined inductive types and inductive functions *)

Print bool.
(** Read "Set" as "Type" *)
Print nat.
Locate "*".
Print prod.
Check S (S O).
Compute 2 + 7.
Locate "+".
Check Nat.add.
Check Nat.sub.

(** Beta and zeta reduction *)

Eval cbv beta in
(fun x => x + x) (2 * 3).

Eval cbv zeta in
let x := 2 * 5 in x + x.

(** Match reduction *)

Eval cbv match in
fun x:nat => match 0 with 0 => x | S y => x + y end.
            
Eval cbv match in
fun x:nat => match S (2 * x) with 0 => x | S y => x + y end.
            
Eval cbv match in
fun x:nat => match x with 0 => x | S y => x + y end.
   
(** Delta reduction *)

Definition T : nat -> nat :=
  fun x => S (S x).

Eval cbv delta in
T 1 = 3.

(* We switch to proof mode so that we can do reduction chains *)

Goal
  T 1 = 3.
Proof.
  cbv delta [T].
  cbv beta.
Abort.
                             
Definition P : nat -> nat :=
  fun x => match x with 0 => 0 | S x' => x' end.

Goal
  P 2 = 1.
Proof.
  cbv delta [P].
  cbv beta.
  cbv match.
Abort.

(** Fix reduction *)

Definition D: nat -> nat :=
  fix f x := match x with 0 => 0 | S x' => S (S (f x')) end.

Goal
  D 1 = 2.
Proof.
  cbv delta [D].
  cbv fix. cbv beta.
  cbv match.
  cbv fix. cbv beta.
  cbv match.
Abort.

(** Readability can be improved by folding in the constant $D$
    again after reduction of the recursive abstraction. 
    This is routinely done by Coq's simplification tactics. *)          

Goal
  D 1 = 2.
Proof.
  cbv delta [D].
  cbv fix. fold D. cbv beta.
  cbv match.
  cbv delta [D].
  cbv fix. fold D. cbv beta.
  cbv match.
Abort.

Example demo n :
  D (S n) = S (S (D n)).
Proof.
  (* We use set/subst so that delta affects only the left occurrence od D *)
  set (a:= S (S (D n))).
  cbv delta [D]. cbv fix. fold D. cbv beta.
  cbv match. cbv beta.
  subst a.
Abort.

Locate "+".
Import Nat. (* Write add for Nat.add *)
Print add.

Example demo x :
  2 + x = S (S x).
Proof.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match.
Abort.
 
Example demo x y :
  S (S x) + y = S (S (x + y)).
Proof.
  set (a:= x+y).
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  cbv delta [add]. cbv fix. fold add. cbv beta.
  cbv match. cbv beta.
  subst a.
Abort.

(** We compute normal forms of terms describing functions *)

Compute add 0.
Compute add 1.
Compute add 2.
Compute fun x => 3 + x - 2.

(** Alpha renaming *)

Goal
  (fun n: nat => n) = (fun x => x).
Proof.
  reflexivity.
Abort.

(** Coq has also eta conversion, explained in Chapter 4 of MPCTT. *)

Goal forall X Y (f: X -> Y),
    (fun x => f x) = f.
Proof.
  intros X Y f.
  cbv.
  reflexivity.
Abort.

Goal
  (fun x => 3 + x - 2) = S.
Proof.
  cbv.
  reflexivity.
Abort.
