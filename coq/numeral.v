From Coq Require Import Arith Lia List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Ltac refl := reflexivity.
Definition dec (P: Prop) : Type := P + ~P.
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

Check Zero 5.
Check Next (Zero 4).
Check Next (Next (Zero 3)).

Definition num_elim (p: forall n, num n -> Type)
  : (forall n, p (S n) (Zero n)) ->
    (forall n a, p n a -> p (S n) (Next a)) -> 
    forall n a, p n a
  := fun e1 e2 => fix f n a :=
       match a with
       | Zero n => e1 n
       | @Next n a => e2 n a (f n a)
       end.

(** Constructor laws *)

Definition f_disjoint n (c: num n) : Prop :=
  match c with Zero _ => False | Next _ => True end.

Fact num_disjoint n a :
  Zero n = Next a -> False.
Proof.
  intros H.
  discriminate (f_equal (fun c => match c with
                             | Zero _ => true
                             | Next _ => false
                             end) H).
Qed.

Definition f_Next_inj n (c: num n)
  : match n return Type with 0 => False | S n' => option (num n') end
  := match c with Zero _ => None | Next c' => Some c' end.

Fact Next_injective n (a b: num n) :
  Next a = Next b -> a = b.
Proof.
  intros H % (f_equal (f_Next_inj (S n))).
  revert H. cbn. intros [= H]. exact H.
Qed.

(** Listing *)

Fixpoint num_listing n : list (num n) :=
  match n with
  | 0 => []
  | S n' => Zero n' :: map Next (num_listing n')
  end.

Compute num_listing 0.
Compute num_listing 1.
Compute num_listing 2.

Goal forall n (a: num n), a el num_listing n.
Proof.
  induction a as [n|n a IH]; cbn.
  - left. refl.
  - right. apply in_map, IH.
Qed.
 
Goal forall n, length (num_listing n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - refl.
  - f_equal. rewrite map_length. exact IH.
Qed.

Fixpoint nrep {X} (A: list X) : Prop :=
  match A with
  | [] => True
  | x::A => x nel A /\ nrep A
  end.

Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Fact nrep_map X Y (f: X -> Y) A :
  injective f -> nrep A -> nrep (map f A).
Proof.
  intros H1.
  induction A as [|x A IH]; cbn.
  - auto.
  - intros [H2 H3].
    split. 2:{ apply IH, H3. }
    intros (x'&H4&H5)%in_map_iff.
    apply H1 in H4 as ->.
    auto.
Qed.

Goal forall n, nrep (num_listing n).
Proof.
  induction n as [|n IH]; cbn.
  - exact I.
  - split.
    + intros (a&H&_) % in_map_iff.
      symmetry in H. apply num_disjoint in H. easy.
    + apply nrep_map. 2:exact IH. exact (Next_injective n).
Qed.

(** Inversion *)
   
Definition num_inv 
  : forall {n} (a: num n),
    match n return num n -> Type with
    | 0 => fun a =>  False
    | S n' => fun a => sum (a = Zero n') (Sigma a', a = Next a')
    end a.
Proof.
  destruct a as [n|n a].
  - left. refl.
  - right. exists a. refl.
Defined.

Goal num 0 -> False.
Proof.
  intros a.
  contradict (num_inv a).
Qed.

Goal forall a: num 1,  a = Zero 0.
Proof.
  intros a.
  destruct (num_inv a) as [->|[a' ->]].
  - refl.
  - contradict (num_inv a').
Qed.

(** Smart matches are compiled to plain matches
    but introduce new problems. *)

Goal num 0 -> False.
Proof.
  exact (fun a => match a with end).
Qed.

Goal forall a: num 1, a = Zero 0.
Proof.
  refine (fun a => match a with
                | Zero n => _
                | Next a => _
                end).
  - destruct n; easy.
  - destruct n; easy.
Qed.


(** Equality decider *)

Definition num_eqdec :
  forall n (a1 a2: num n), dec (a1 = a2).
Proof.
  induction a1 as [n|n a1 IH]; intros a2.
  all: destruct (num_inv a2) as [->|[a2' ->]].
  - left. refl.
  - right. intros [] % num_disjoint.
  - right. intros H. symmetry in H. eapply num_disjoint, H.
  - specialize (IH a2') as [[]|H].
    + left. refl.
    + right. contradict H. apply Next_injective, H.
Defined.

(** Lift *)

Fixpoint lift {n} (a: num n) : num (S n) :=
  match a with
  | Zero n => Zero (S n)
  | Next a => Next (lift a)
  end.

Fact lift_injective n (a b: num n) :
  lift a = lift b -> a = b.
Proof.
  revert n a b.
  induction a as [|n a IH];
    intros b;
    destruct (num_inv b) as [->|[a' ->]];
    cbn.
  - easy.
  - intros [] % num_disjoint.
  - intros H. exfalso. symmetry in H. eapply num_disjoint, H.
  - intros H % Next_injective. f_equal. apply IH, H.
Qed.

(** Predecessor *)

Definition pre {n} (a: num (S (S n))) : num (S n).
Proof.
  destruct (num_inv a) as [H|[a' H]].
  - exact (Zero n).
  - exact a'.
Defined.

Goal forall n (a: num (S n)),
    pre (Next a) = a.
Proof.
  refl.
Qed.
    
(** Embedding into numbers *)

Fixpoint N {n} (a: num n) : nat :=
  match a with
  | Zero n => 0
  | Next a => S (N a)
  end.

Compute N (Zero 3).
Compute N (Next (Next (Zero 3))).

Fact N_lt {n} (a: num n) :
  N a < n.
Proof.
  induction a as [n|n a IH]; cbn.
  - lia.
  - lia.
Qed.

Fixpoint B k n : num (S n) :=
  match k, n with
  | 0, n => Zero n
  | S k, 0 => Zero 0
  | S k, S n => Next (B k n)
  end.

Compute B 3 3.
Compute B 4 3.
Compute B 2 3.
Compute N (B 2 3).
Compute B (N (Zero 5)) 5.
Compute B (N (B 3 5)) 5.

Fact NB_eq k n :
  k <= n -> N (B k n) = k.
Proof.
  induction k as [|k IH] in n |-*; cbn.
  - easy.
  - destruct n as [|n]; cbn.
    + intros H. exfalso. lia.
    + intros H. f_equal. apply IH. lia.
Qed.

Fact BN_eq {n} (a: num (S n)) :
  B (N a) n = a.
Proof.
  induction n as [|n IH];
    destruct (num_inv a) as [->|[a' ->]];
    cbn.
  - refl.
  - exfalso. contradict (num_inv a').
  - refl.
  - f_equal. apply IH.
Qed.

Fact N_injective n (a b: num n) :
  N a = N b -> a = b.
Proof.
  destruct n as [|n].
  - contradict (num_inv a).
  - intros H % (f_equal (fun k => B k n)).
    revert H. rewrite !BN_eq. easy.
Qed.

Fact N_injective' n (a b: num n) :
  N a = N b -> a = b.
Proof.
  revert n a b.
  induction a as [|n a IH];
    intros b;
    destruct (num_inv b) as [->|[a' ->]];
    cbn.
  - easy.
  - intros [=].
  - intros [=].
  - intros [= H]. f_equal. apply IH, H.
Qed.

(** Recursive numeral types *)

Fixpoint fin (n: nat) : Type :=
  match n with
  | 0 => False
  | S n' => option (fin n')
  end.

Fixpoint num_fin {n} (a: num n) : fin n :=
  match a with
  | Zero _ => None
  | Next a => Some (num_fin a)
  end.

Fixpoint fin_num {n} (c: fin n) : num n :=
  match n, c with
  | 0, c => match c with end
  | S n', None => Zero n'
  | S n', Some c => Next (fin_num c)
  end.

Goal forall n (a: num n),
    fin_num (num_fin a) = a.
Proof.
  induction a as [n|n a IH]; cbn.
  - refl.
  - f_equal. exact IH.
Qed.

Goal forall n (c: fin n),
    num_fin (fin_num c) = c.
Proof.
  induction n as [|n IH].
  - intros [].
  - intros [c|]; cbn.
    + f_equal. apply IH.
    + refl.
Qed.
 
Compute num_fin (Next (Next (Zero 5))).
Compute fin_num (num_fin (Next (Next (Zero 5)))).

Module Embedding.
Fixpoint N n (c: fin n): nat :=
  match n, c with
  | 0, c => match c with end
  | S n, None => 0
  | S n, Some c => S (N n c)
  end.

Fixpoint B k n : fin (S n) :=
  match k, n with
  | 0, _ => None
  | S _, 0 => None
  | S k, S n => Some (B k n)
  end.

Fact N_lt n (c: fin n) :
  N n c < n.
Proof.
  induction n as [|n IH].
  - destruct c.
  - destruct c as [c|]; cbn.
    + specialize (IH c). lia.
    + lia.
Qed.

Compute N 4 None.
Compute N 6 (Some (Some None)).
Compute B 3 3.
Compute B 2 3.
Compute N 4 (B 2 3).
Compute B (N 6 None) 5.
Compute B (N 6 (B 3 5)) 5.

Fact NB_eq k n :
  k <= n -> N (S n) (B k n) = k.
Proof.
  induction k as [|k IH] in n |-*; cbn.
  - easy.
  - destruct n as [|n]; cbn.
    + intros H. exfalso. lia.
    + intros H. f_equal. apply IH. lia.
Qed.

Fact BN_eq n (c: fin (S n)) :
  B (N (S n) c) n = c.
Proof.
  induction n as [|n IH].
  - destruct c as [c|]; cbn.
    + contradict c.
    + refl.
  - destruct c as [c|].
    + cbn . f_equal. apply IH.
    + refl.
Qed.
End Embedding.
