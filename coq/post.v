(** Post Correspondence Problem *)

From Coq Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).

Inductive char := a | b.
Definition string : Type := list char.
Definition card : Type := string * string.
Definition deck : Type := list card.

Inductive post (D: deck) : string -> string -> Prop :=
| post1 : forall A B, (A,B) el D -> post D A B
| post2 : forall A B A' B', (A,B) el D -> post D A' B' -> post D (A ++ A') (B ++ B').

Definition D : deck := [([a], []); ([b],[a]); ([], [b;b])].

Goal post D [b;b;a;a] [b;b;a;a].
Proof.
  refine (post2 _ [] [b;b] [b;b;a;a] [a;a] _ _).
  { cbn; auto. }
  refine (post2 _ [b] [a] [b;a;a] [a] _ _).
  { cbn; auto. }
  refine (post2 _ [b] [a] [a;a] [] _ _).
  { cbn; auto. }
  refine (post2 _ [a] [] [a] [] _ _).
  { cbn; auto. }
  refine (post1 _ [a] [] _).
  { cbn; auto. }
Qed.

