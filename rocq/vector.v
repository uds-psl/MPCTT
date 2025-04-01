From Stdlib Require Import Arith Lia List.
Import ListNotations.
From Equations Require Import Equations.
Ltac refl := reflexivity.
Definition dec (P: Prop) : Type := P + ~P.
Definition eqdec X : Type := forall x x': X, dec (x = x').
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Inductive num : nat -> Type :=
| Zero: forall n, num (S n)
| Next: forall {n}, num n -> num (S n).

Section Vector.
  Variable X : Type.

  Inductive vector : nat -> Type :=
  | Nil : vector O
  | Cons : forall {n}, X -> vector n -> vector (S n).

  Definition vector_elim (p: forall n, vector n -> Type)
    : p 0 Nil ->
      (forall n x v, p n v -> p (S n) (Cons x v)) ->
      forall n v, p n v
    := fun e1 e2 => fix f n v := match v with
                              | Nil => e1
                              | @Cons n' x v' => e2 n' x v' (f n' v')
                              end.

  Definition vec_inv :
    forall {n} (v: vector n),
      match n return vector n -> Type with
      | 0 => fun v => v = Nil
      | S n' => fun v => Sigma x v', v = Cons x v'
      end v.
  Proof.
    intros n v.
    destruct v as [|n x v].
    - refl.
    - exists x, v. refl.
  Defined.
  
  Goal forall v: vector 0,
      v = Nil.
  Proof.
    intros v. apply (vec_inv v).
  Qed.
  
  Goal forall n (v: vector (S n)),
      Sigma x v', v = Cons x v'.
  Proof.
    intros n v. apply (vec_inv v).
  Qed.

  (** Head, tail, last, sub *)

  Definition hd {n} (v: vector (S n)) : X :=
    pi1 (vec_inv v).

  Definition tl {n} (v: vector (S n)) : vector n :=
    pi1 (pi2 (vec_inv v)).

  Fact eta_law n (v:vector (S n)) :
    v = Cons (hd v) (tl v).
  Proof.
    destruct (vec_inv v) as (x&v'&->).
    refl.
  Qed.

  Fixpoint last {n} : vector (S n) -> X :=
    match n with
    | 0 => hd
    | S n' => fun v => @last n' (@tl (S n') v)
    end.

  Fixpoint trunc {n} : vector (S n) -> vector n :=
    match n with
    | 0 => fun _ => Nil
    | S n' => fun v => Cons (hd v) (trunc (tl v))
    end.

  Fixpoint sub {n} (a: num n) : vector n -> X :=
    match a with
    | Zero n' => @hd n'
    | @Next n' a' => fun v => @sub n' a' (@tl n' v)
    end.

  (** Constructor injectivity *)

  Fact Cons_inj1 n x x' (v v': vector n) :
    Cons x v = Cons x' v' -> x = x'.
  Proof.
    intros H % (f_equal hd). exact H.
  Qed.
    
  Fact Cons_inj2 n x x' (v v': vector n) :
    Cons x v = Cons x' v' -> v = v'.
  Proof.
    intros H % (f_equal tl).
    exact H.
  Qed.

  (** Equality Decider *)

  Definition vector_eq n :
    eqdec X -> forall v1 v2: vector n, dec (v1 = v2).
  Proof.
    intros H.
    induction v1 as [|n x1 v1 IH];
      intros v2;
      generalize (vec_inv v2).
    - intros ->. left. refl.
    - intros (x2&v2'&->).
      specialize (H x1 x2) as [<-|H].
      + destruct (IH v2') as [<-|H1].
        * left. refl.
        * right. contradict H1. exact (f_equal tl H1).
      + right. contradict H. exact (f_equal hd H).
  Defined.

  (** Generalized head and tail *)
  
  Definition Hd  {n} (v: vector n)
    : match n return Type with 0 => True | S n' => X end
    := match v with Nil => I | Cons x _ => x end.
  
  Definition Tl  {n} (v: vector n)
    : match n return Type with 0 => True | S n' => vector n' end
    := match v with Nil => I | Cons _ v' => v' end.

  Fact Cons_inj n x x' (v v': vector n) :
    Cons x v = Cons x' v' -> x = x' /\ v = v'.
  Proof.
    intros H. split.
    - exact (f_equal Hd H).
    - exact (f_equal Tl H).
  Qed.

  (** Snoc, reverse *)
  
  Fixpoint snoc {n} (v: vector n) (x: X) : vector (S n) :=
    match v with
    | Nil => Cons x Nil
    | Cons x' v' => Cons x' (snoc v' x)
    end.
  
  Fixpoint rev {n} (v: vector n) : vector n :=
    match v with
    | Nil => Nil
    | Cons x v' => snoc (rev v') x
    end.

  Goal forall x n (v: vector n),
      last (snoc v x) = x.
  Proof.
    induction v as [|n y v IH]; cbn.
    - refl.
    - exact IH.
  Qed.

  Goal forall n (v: vector (S n)),
      v = snoc (trunc v) (last v).
  Proof.
    induction n as [|n IH];
      intros v;
      destruct (vec_inv v) as (x&v'&->);
      cbn; f_equal.
    - destruct (vec_inv v'); refl.
    - apply IH.
  Qed.
  
  Fact rev_snoc x n (v: vector n) :
    rev (snoc v x) = Cons x (rev v).
  Proof.
    induction v as [|n y v IH]; cbn.
    - refl.
    - rewrite IH. refl.
  Qed.

  Goal forall n (v: vector n),
      rev (rev v) = v.
  Proof.
    induction v as [|n x v IH]; cbn.
    - refl.
    - rewrite rev_snoc, IH. refl.
  Qed.
  

  (** Converting between vectors and lists *)

  Fixpoint vec_list {n} (v: vector n) : list X :=
    match v with
    | Nil => nil
    | Cons x v' => cons x (vec_list v')
    end.

  Fact vec_list_length n :
    forall v: vector n, length (vec_list v) = n.
  Proof.
    induction v as [|n x v IH]; cbn.
    - refl.
    - f_equal.  exact IH.
  Qed.
  
  Fact vec_list_injective n (v1 v2: vector n) :
    vec_list v1 = vec_list v2 -> v1 = v2.
  Proof.
    revert n v1 v2.
    induction v1 as [|n x1 v1 IH];
      intros v2;
      generalize (vec_inv v2).
    - intros ->. easy. 
    - intros (x2&v2'&->); cbn.
      intros [= <- H].
      f_equal. apply IH, H.
  Qed.

  Definition guarded_list_vec :
    forall A, Sigma v: vector (length A), vec_list v = A.
  Proof.
    induction A as [|x A IH]; cbn.
    - exists Nil. refl.
    - specialize IH as [v IH].
      exists (Cons x v). cbn. f_equal. exact IH.
  Defined.

  Definition list_vec (A: list X) : vector (length A) :=
    pi1 (guarded_list_vec A).

  Fact vec_list_eq :
    forall A, vec_list (list_vec A) = A.
  Proof.
    intros A.
    apply (pi2 (guarded_list_vec A)).
  Qed.

  Fail Check forall n (v: vector n),
      list_vec (vec_list v) = v.

  Fact vec_cast {n} {v: vector n} :
    vector (length (vec_list v)) -> vector n.
  Proof.
    rewrite vec_list_length. easy.
  Qed.

  Check forall n (v: vector n),
      vec_cast (list_vec (vec_list v)) = v.
       

  (** Smart matches *)
  
  Definition hd' {n} (v: vector (S n)) : X :=
    match v with Cons x _ => x end.

  Definition tl' {n} (v: vector (S n)) : vector n :=
    match v with Cons _ v' => v' end.

  Fact eta_law' n (v: vector (S n)) :
    v = Cons (hd' v) (tl' v).
  Proof.
    refine (match v with Cons x v' => eq_refl end).
  Qed.

  Definition hd'' {n} (v: vector (S n)) : X :=
    match v
          in vector n return match n with 0 => True | S _ => X end
    with
    | Nil => I
    | Cons x _ => x
    end.
 
  Goal forall v: vector 0,
      v = Nil.
  Proof.
    refine (fun v => match v with Nil => eq_refl end).
  Qed.
  
  Goal forall n (v: vector (S n)),
      Sigma x v', v = Cons x v'.
  Proof.
    refine (fun n v => match v with Cons x v' => _ end).
    exists x, v'. refl.
  Qed.
              
  (** Experiments *)

  Fixpoint revapp {m} (v: vector m) :
    forall {n} (w: vector n), vector (tail_plus m n) :=
    match v with
    | Nil => fun n w => w
    | Cons x v => fun n w => revapp v (Cons x w)
    end.

  Fail Goal forall n (v: vector n),
      rev v = revapp v Nil.
 
  Fixpoint app {m n} (v: vector m) (w: vector n) : vector (m + n) :=
    match v with
    | Nil => w
    | Cons x v' => Cons x (app v' w)
    end.

  Fixpoint cast {m n} (v: vector (m + S n)) : vector (S (m + n)).
  Proof.
    rewrite plus_n_Sm. exact v. 
  Defined.

  Fact snoc_app m n (v: vector m) (w: vector n) x :
    snoc (app v w) x = cast (app v (snoc w x)).
  Proof.
    induction v as [|n' x' v' IH] in n,w |-*.
    - cbn.
  Abort.
  
End Vector.

Arguments Nil {X}.
Arguments Cons {X n}.
Arguments hd {X n}.
Arguments hd'' {X n}.
Arguments tl {X n}.
Arguments last {X n}.
Arguments rev {X n}.
Arguments sub {X n}.
Arguments vec_list {X n}.
Arguments list_vec {X}.
Arguments vec_list {X n}.

Compute rev (Cons 5 (Cons 2 Nil)).
Compute hd (tl (Cons 5 (Cons 2 Nil))).
Compute hd'' (tl (Cons 5 (Cons 2 Nil))).
Compute last (Cons 5 (Cons 2 Nil)).

Compute sub (Zero 1) (Cons 5 (Cons 2 Nil)).
Compute sub (Next (Zero 0)) (Cons 5 (Cons 2 Nil)).
Compute vec_list (Cons 5 (Cons 2 Nil)).

Compute list_vec [5;3;7].
Compute vec_list (list_vec [5;3;7]).

Goal vec_list (list_vec [5;3;7]) = [5;3;7].
Proof.
  refl.
Qed.

(** Exercises *)

Fixpoint map {X Y} (f: X -> Y) {n} (v: vector X n) : vector Y n :=
  match v with
  | Nil => Nil
  | Cons x v' => Cons (f x) (map f v')
  end.

Fixpoint tab n : vector (num n) n :=
  match n with
  | 0 => Nil
  | S n' => Cons (Zero n') (map Next (tab n'))
  end.

Compute tab 7.
Compute rev (tab 7).
Compute sub (Zero 6) (rev (tab 7)).
