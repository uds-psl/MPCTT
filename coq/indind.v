(*** MPCTT, Chapter Indexed Inductives *)
From Coq Require Import Lia.

(*** Inductive Equality *)
Module IndEquality.
  
  Inductive eq X (x: X) : X -> Prop :=
  | Q : eq X x x.

  Check eq.
  Check Q.

  
  Definition E 
    : forall X  (x: X) (p: X -> Type),  p x -> forall y, eq X x y -> p y
    := fun X x p a _ e =>
         match e with
         | Q _ _ => a
         end.


  Definition R 
    : forall X  (x y: X) (p: X -> Type),  eq X x y -> p x -> p y
    := fun X x _ p e => match e with
                     | Q _ _ => fun a => a
                     end.
End IndEquality.

(*** Reflexive Transitive Closure *)

Module Star.
Section Star.
  Variable X : Type.
  Implicit Type R: X -> X -> Prop.

  Inductive star (R: X -> X -> Prop) (x: X) : X -> Prop :=
  | Nil : star R x x
  | Cons y z : R x y -> star R y z -> star R x z.

  Definition elim R (p: X -> X -> Prop)
    : (forall x, p x x) ->
      (forall x y z, R x y -> p y z -> p x z) -> 
      forall x y, star R x y -> p x y
    := fun f1 f2 => fix f x _ a :=
      match a with
      | Nil _ _ => f1 x
      | Cons _ _ x' z r a => f2 x x' z r (f x' z a)
      end.
 
  Implicit Type p: X -> X -> Prop.
  Definition reflexive p := forall x, p x x.
  Definition transitive p := forall x y z, p x y -> p y z -> p x z.
  Definition incl p p' := forall x y, p x y -> p' x y.

  Fact star_incl R :
    incl R (star R).
  Proof.
    intros x y r. eapply Cons. exact r. apply Nil.
  Qed.
  
  Fact star_trans R :
    transitive (star R).
  Proof.
    intros x y z.
    revert x y.
    refine (elim _ _ _ _).
    - easy.
    - intros x x' y r IH.
      intros H%IH. revert r H. apply Cons.
  Qed.

  (** We may also use the automatically generated eliminator for star. *)

  Check star_ind.
  
  Goal 
    forall R, transitive (star R).
  Proof.
    induction 1 as [|x x' y r _ IH].
    - easy.
    - intros H%IH. econstructor. exact r. exact H.
  Qed.

  Fact least R p :
    reflexive p ->
    transitive p ->
    incl R p ->
    incl (star R) p.
  Proof.
    intros H1 H2 H3. hnf.
    apply elim.
    - exact H1.
    - intros x y z H%H3. apply H2, H.
  Qed.

  Goal forall R, incl (star (star R)) (star R).
  Proof.
    intros R. apply least.
    - hnf. apply Nil.
    - apply star_trans.
    - easy.
  Qed.

  Fixpoint path R n x y : Prop :=
    match n with
    | 0 => x = y
    | S n => exists x', R x x' /\ path R n x' y
    end.

  Goal forall R x y,
      star R x y <-> exists n, path R n x y.
  Proof.
    split.
    - induction 1 as [|x x' y r _ IH].
      + exists 0. easy.
      + destruct IH as [n IH].
        exists (S n). exists x'. easy.
    - intros [n H]. revert x H.
      induction n as [|n IH]; cbn.
      + intros x <-. apply Nil.
      + intros x (x'&H1&H2).
        eapply Cons. exact H1.
        apply IH, H2.
  Qed.

  (*** Index Elimination *)

  (** We can define R* as an inductive predicate without indices. **)

  Inductive star' (R: X -> X -> Prop) (x: X) (y:X) : Prop :=
  | Nil' : x = y -> star' R x y
  | Cons' x' : R x x' -> star' R x' y -> star' R x y.

  Definition elim' R (p: X -> Prop) (y: X)
    : (forall x, x = y -> p x) ->
      (forall x x', R x x' -> p x' -> p x) -> 
      forall x, star' R x y -> p x
    := fun f1 f2 => fix f x a :=
      match a with
      | Nil' _ _ _ e => f1 x e
      | Cons' _ _ _ x' r a => f2 x x' r (f x' a)
      end.

  Goal forall R x y, star' R x y <-> star R x y.
    Proof.
      intros *; split.
      - revert x. apply elim'.
        + intros x <-. apply Nil.
        + intros * r IH. eapply Cons; eassumption.
      - revert x y. apply elim.
        + intros *. apply Nil'. reflexivity.
        + intros * r IH. eapply Cons'; eassumption.
    Qed.
End Star.
End Star.

 (** Index eliminatiom will not work for equality
      since Leibniz equality doesnt give us rewriting at type. *)

Module Eq_without_index.
    
  Inductive eq' X (x: X) (y: X) : Prop :=
  | L : (forall p: X -> Type, p x -> p y) -> eq' X x y.
    
  Inductive eq'' X (x: X) (y: X) : Prop :=
  | L' : (forall p: X -> Prop, p x -> p y) -> eq'' X x y.

  Goal forall X x y, eq' X x y <-> x = y.
  Proof.
    intros *; split.
    - intros [H]. pattern y. apply H. reflexivity.
    - intros <-. apply L. auto. 
  Qed.

  Goal forall X (x y: X) (p: X -> Type),
      eq' X x y -> p x -> p y.
  Proof.
    Fail intros * [H]. (* PDR kills it *)
  Abort.
  
  Goal forall X x y, eq' X x y <-> eq'' X x y.
  Proof.
    intros *; split.
    - intros [H]. pattern y. apply H. apply L'. auto.
    - intros [H]. pattern y. apply H. apply L. auto.
  Qed.

End Eq_without_index.

(*** Inductive Comparisons *)

Module LE.
  Inductive le (x: nat) : nat -> Prop :=
  | leE : le x x 
  | leS y : le x y -> le x (S y).

  Definition elim (x: nat) (p: nat -> Prop)
    : p x ->
      (forall y, p y -> p (S y)) -> 
      forall y, le x y -> p y
    := fun e1 e2 => fix f _ a :=
      match a with
      | leE _ => e1
      | leS _ y a => e2 y (f y a)
      end.

  Fact le_correct x y :
    le x y <-> x <= y.
  Proof.
    split.
    - revert y. apply elim.
      + lia.
      + lia.
    - induction y as [|y IH]; intros H.
      + assert (x = 0) as -> by lia. apply leE.
      + assert (x = S y \/ x <= y) as [->|H1] by lia.
        * apply leE.
        * apply leS, IH. lia.
  Qed.
End LE.

(*** Inductive Numeral Types *)

Module Fin.
Fixpoint num n : Type :=
  match n with
  | 0 => False
  | S n => option (num n)
  end.

Inductive fin : nat -> Type :=
| Old: forall n, fin n -> fin (S n)
| New: forall n, fin (S n).

Definition fin_num 
  : forall n, fin n -> num n
  := fix f n a :=
    match a with
    | Old n a => Some (f n a)
    | New n => None
                  end.

Definition num_fin 
  : forall n, num n -> fin n
  := fix f n :=
    match n with
    | 0 => fun a => match a with end
    | S n => fun a => match a with
                  | Some a => Old n (f n a)
                  | None => New n
                  end
    end.

Fact num_fin_inv n a :
  num_fin n (fin_num n a) = a.
Proof.
  induction a as [n a IH | n]; cbn.
  - f_equal. apply IH.
  - reflexivity.
Qed.

Definition elim (p: forall n, fin n -> Type)
  : (forall n a, p n a -> p (S n) (Old n a)) ->
    (forall n, p (S n) (New n)) ->
    forall n a, p n a
  := fun e1 e2 => fix f n a :=
    match a with
    | Old n a => e1 n a (f n a)
    | New n => e2 n
    end.

Fact num_fin_inv' n a :
  num_fin n (fin_num n a) = a.
Proof.
  revert n a. apply elim; cbn.
  - intros n a IH. f_equal. exact IH.
  - reflexivity.
Qed.

Fact fin_num_inv n a :
  fin_num n (num_fin n a) = a.
Proof.
  induction n as [|n IH].
  - destruct a.
  - destruct a as [a|]; cbn.
    + f_equal. apply IH.
    + reflexivity.
Qed.

Goal fin 0 -> False.
Proof.
  enough (forall n, fin n -> n = 0 -> False) by eauto.
  refine (elim _ _ _).
  - lia.
  - lia.
Qed.

Goal fin 0 -> False.
Proof.
  intros a. apply (fin_num 0 a).
Qed.
End Fin.

(*** Inductive Vector Types *)

Module Vector.
Section Vector.
Variable X: Type.
    
Fixpoint vec n : Type :=
  match n with
  | 0 => unit
  | S n => X * vec n
  end.

Inductive V : nat -> Type :=
| Nil : V 0
| Cons n : X -> V n -> V (S n).

Definition V_vec
  : forall n, V n -> vec n
  := fix f n a :=
    match a with
    | Nil => tt
    | Cons n x a => (x, f n a)
    end.

Definition vec_V
  : forall n, vec n -> V n
  := fix f n :=
    match n with
    | 0  => fun _ => Nil
    | S n => fun v => let (x,v) := v in Cons n x (f n v)
    end.

Fact vec_V_inv n v :
  vec_V n (V_vec n v) = v.
Proof.
  induction v as [|n x v IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Definition elim (p: forall n, V n -> Type) 
  : p 0 Nil ->
    (forall n x v, p n v -> p (S n) (Cons n x v)) ->
    forall n v, p n v
  := fun e1 e2 => fix f n v :=
    match v with
    | Nil => e1
    | Cons n x v => e2 n x v (f n v)
    end.

Fact vec_V_inv' n v :
  vec_V n (V_vec n v) = v.
Proof.
  revert n v. apply elim; cbn.
  - reflexivity.
  - intros n x v IH. f_equal. exact IH.
Qed.

Fact V_vec_inv n v :
  V_vec n (vec_V n v) = v.
Proof.
  induction n as [|n IH]; cbn.
  - destruct v. reflexivity.
  - destruct v as [x v]; cbn. f_equal. apply IH.
Qed.
End Vector.
End Vector.

(*** Post Correspondence Problem *)

From Coq Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).

Module Post.
  Inductive char := a | b.
  Definition string : Type := list char.
  Definition card : Type := string * string.
  Definition deck : Type := list card.

  Inductive post (D: deck) | : string -> string -> Prop :=
  | post1 : forall A B, (A,B) el D -> post A B
  | post2 : forall A B A' B', (A,B) el D -> post A' B' -> post (A ++ A') (B ++ B').

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
End Post.






