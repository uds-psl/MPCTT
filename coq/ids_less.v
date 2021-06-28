Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
From Coq Require Import Arith Lia Eqdep_dec.
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Fact inr_injective X Y (y y': Y) :
  inr X y = inr y' -> y = y'.
Proof.
  intros H % (f_equal (fun a: X + Y => match a with
                                    | inl x => y
                                    | inr y => y
                                    end)).
  exact H.
Qed.

Definition cast {X} {x y: X} {p: X -> Type}
  : x = y -> p x -> p y
  := fun e a => match e with eq_refl => a end.

Fact  UIP_nat :
  forall {x: nat} (e: x = x), e = eq_refl.
Proof.
  exact UIP_refl_nat.
Qed.
Fact cast_nat {p: nat -> Type} {x: nat} {y: p x} :
  forall e: x = x, cast (p:= p) e y = y.
Proof.
  intros e. rewrite (UIP_nat e). reflexivity.
Qed.
Fact DPI_nat :
  forall (p: nat -> Type) n a b, Sig p n a = Sig p n b -> a = b.
Proof.
  intros p.
  enough (forall a b: sig p, a = b -> forall e: pi1 a = pi1 b, cast e (pi2 a) = pi2 b) as H.
  { intros x u v H1. refine (H _ _ H1 eq_refl). }
  intros a b []. apply cast_nat.
Qed.

(*** Binary Variant *)
Module Binary.
Inductive L (x: nat) : nat -> Type :=
| L1: L x (S x)
| L2: forall y z, L x y -> L y z -> L x z.

Fact L_complete x y :
  x < y -> L x y.
Proof.
  induction y as [|y IH].
  - lia.
  - intros H.
    destruct (Nat.eq_dec x y) as [<-|H1].
    + constructor.
    + eapply L2. 2:exact (L1 y).
      apply IH. lia.
Qed.

Definition L_elim (p: forall x y, L x y -> Type)
  : (forall x, p x (S x) (L1 x)) ->
    (forall x y z a b, p x y a -> p y z b -> p x z (L2 x y z a b)) ->
    forall x y a, p x y a
  := fun e1 e2 => fix f x _ a :=
       match a with
       | L1 _ => e1 x
       | L2 _ y z a b => e2 x y z a b (f x y a) (f y z b)
       end.

Fact L_sound {x y} :
  L x y -> x < y.
Proof.
  induction 1; lia.
Qed.

Fixpoint depth_left {x y} (a: L x y) : nat :=
  match a with
  | L1 _ => 1
  | L2 _ y z a b => S (depth_left a)
  end.

Goal
  L2 3 4 6 (L1 3) (L2 4 5 6 (L1 4) (L1 5))
<> L2 3 5 6 (L2 3 4 5 (L1 3) (L1 4)) (L1 5) .
Proof.
  intros [=] % (f_equal depth_left).
Qed.
  

Definition L_inv {x y} :
  L x y -> sum (y = S x) (Sigma z, prod (L x z) (L z y)).
Proof.
  destruct 1 as [|z y a b].
  - left; reflexivity.
  - right. exists z. easy.
Defined.

Compute fun x => L_inv (L1 x).
Compute fun x y z a b => L_inv (L2 x y z a b).

Fact L2_injective x y z a b a' b':
  L2 x z y a b = L2 x z y a' b' -> (a,b) = (a',b').
Proof.
  intros H.
  apply (f_equal L_inv) in H. cbn in H.
  apply inr_injective in H.
  apply DPI_nat in H. 
  exact H.
Qed.
  
Fact L_inv_full {x y} :
  forall a: L x y,
    match y return L x y -> Type with
    | 0 => fun _ => False
    | S y => fun a => sum
                    (Sigma e: y = x, cast (p:= fun z => L x (S z)) e a = L1 x)
                    (Sigma z a1 a2, a = L2 x z (S y) a1 a2)
    end a.
Proof.
  destruct a as [|y z a1 a2].
  - left. exists eq_refl. reflexivity.
  - destruct z.
    + generalize (L_sound a2). lia.
    + right. exists y, a1, a2. reflexivity.
Qed.
End Binary.

(*** Linear Indexed-Determined Variant *)
Module Linear.
Inductive L : nat -> nat -> Type :=
| L1 : forall y, L 0 (S y)
| L2 : forall x y, L x y -> L (S x) (S y).

Definition L_elim (p: forall x y, L x y -> Type)
  : (forall y, p 0 (S y) (L1 y)) ->
    (forall x y a, p x y a -> p (S x) (S y) (L2 x y a)) ->
    forall x y a, p x y a
  := fun e1 e2 => fix f x y a := match a with
                              | L1 y => e1 y
                              | L2 x y a => e2 x y a (f x y a)
                              end.

Goal forall x y,
    L x y <=> x < y.
Proof.
  split.
  - induction 1 as [y|x y a IH]; lia.
  - induction x as [|x IH] in y |-*.
    all: (destruct y; try lia).
    all: intros H; constructor.
    apply IH. lia.
Qed.

Definition L_inv {x y} (a: L x y) :
  match x, y return L x y -> Type with
  | 0, S y => fun a => a = L1 y
  | S x, S y =>  fun a => Sigma a', a = L2 x y a'
  | _, _ =>  fun a => False
  end a.
Proof.
  destruct a as [y|x y a].
  - reflexivity.
  - exists a. reflexivity.
Defined.

Compute fun x => L_inv (L1 x).
Compute fun x y a => L_inv (L2 x y a).

Fact L_unique x y :
  forall a b: L x y, a = b.
Proof.
  induction a as [y|x y a IH];
    intros b; generalize (L_inv b).
  - easy.
  - intros [a' ->]. f_equal. apply IH.
Qed.

Goal forall x, L x 0 -> False.
Proof.
  intros [|x] a; generalize (L_inv a); easy.
Qed.
    
Goal forall x, L x x -> False.
Proof.
  induction x as [|x IH].
  - intros a. contradict (L_inv a).
  - intros a. destruct (L_inv a) as [a' ->]. easy.
Qed.

End Linear.

(*** Linear Left-Anchored Variant *)
Module Linear_Anchored.
Inductive L (x: nat) : nat -> Type :=
| L1 : L x (S x)
| L2 : forall y, L x y -> L x (S y).

Goal forall x y,
    L x y <=> x < y.
Proof.
  split.
  - induction 1 as [|y a IH]; lia.
  - induction y as [|y IH].
    + lia.
    + destruct (Nat.eq_dec x y) as [<-|H].
      * intros _. constructor.
      * intros H1. constructor. apply IH. lia.
Qed.

Definition L_inv {x y} :
  L x y -> sum (y = S x) (Sigma y', prod (y = S y') (L x y')).
Proof.
  destruct 1 as [|y a].
  - left. reflexivity.
  - right. exists y. easy.
Defined.

Compute fun x => L_inv (L1 x).
Compute fun x y a => L_inv (L2 x y a).

Fact L2_injective x y a b :
  L2 x y a = L2 x y b -> a = b.
Proof.
  intros H % (f_equal L_inv)
         % inr_injective
         % DPI_nat
         % (f_equal snd).
  exact H.
Qed.

Fact L_inv_full {x y} :
  forall a: L x y,
    match y return L x y -> Type with
    | 0 => fun _ => False : Type
    | S y => fun a => sum
                    (Sigma e: y = x, cast (p:= fun z => L x (S z)) e a = L1 x)
                    (Sigma a', a = L2 x y a')
    end a.
Proof.
  destruct a as [|y a].
  - left. exists eq_refl. reflexivity.
  - right. exists a. reflexivity.
Defined.

Fact L_lt {x y} :
  L x y -> x < y.
Proof.
  induction 1 as [|y a IH]; lia.
Qed.

Fact L_unique x :
  forall y (a b: L x y), a = b.
Proof.
  induction a as [|y a IH];
    intros b; destruct (L_inv_full b) as [[e H]|[b' H]].
  - rewrite <-H. refine (cast_nat _).
  - exfalso. specialize (L_lt b'). lia.
  - exfalso.  specialize (L_lt a). lia.
  - rewrite H. f_equal. apply IH.
Qed.
End Linear_Anchored.
