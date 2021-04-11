From Coq Require Import Lia.

Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Print sum.
Print sigT.

Definition match_sum
  : forall X Y Z: Type, X + Y -> (X -> Z) -> (Y -> Z) -> Z
  := fun X Y Z a f g => match a with inl x => f x | inr y => g y end.
Arguments match_sum {X Y Z}.

Definition match_sigT
  : forall (X: Type) (p: X -> Type) (Z: Type), sigT p -> (forall x, p x -> Z) -> Z
  := fun X p Z a f => match a with existT _ x c => f x c end.
Arguments match_sigT {X p Z}.

Definition nat_eqdec :
  forall x y: nat, (x = y) + (x <> y).
Proof.
  induction x as [|x IH]; destruct y.
  - left. reflexivity.
  - right. intros [=].
  - right. intros [=].
  - apply (match_sum (IH y)); intros H.
    (* destruct (IH y) as [H|H]. *)
    + left. f_equal. exact H.
    + right. intros [= H1]. apply H, H1.
Defined.

Definition distance :
  forall x y: nat, { z & sum (x + z = y) (y + z = x) }.
Proof.
  induction x as [|x IH]. 2:destruct y.
  - intros y. exists y. left. reflexivity.
  - exists (S x). right. reflexivity.
  - apply (match_sigT (IH y)). intros z a.
    apply (match_sum a); intros H.
    (* apply (IH y) as [z [H|H]]. *)
    + exists z. left. cbn. f_equal. exact H.
    + exists z. right. cbn. f_equal. exact H.
Defined.

Fact sumAsSigma X Y:
  X + Y <=> {b: bool & if b then X else Y}.
Proof.
  split.
  - intros [x|y].
      + exists true. exact x.
      + exists false. exact y.
  - intros a. apply (match_sigT a). intros [|]; auto.
Qed.

(*** Projections and Skolem equivalence *)

Definition pi1
  : forall (X: Type) (p: X -> Type), sigT p -> X
  := fun X p a => match a with existT _ x _ => x end.
Arguments pi1 {X p}.
Definition pi2
  : forall (X: Type) (p: X -> Type) (a: sigT p),  p (pi1 a)
  := fun X p a => match a with existT _ x c => c end.
Arguments pi2 {X p}.

Compute pi1 (distance 3 7).

Fact pi1_eq X (p: X -> Type) x c :
  pi1 (existT p x c) = x.
Proof.
  reflexivity.
Qed.

Fact pi2_eq X (p: X -> Type) x c :
  pi2 (existT p x c) = c.
Proof.
  reflexivity.
Qed.

Fact Skolem X Y (p: X -> Y -> Type) :
  {f & forall x, p x (f x)} <=> forall x, {y & p x y}.
Proof.
  split.
  - intros a x. exists (pi1 a x). exact (pi2 a x).
    (* intros [f H] x. exists (f x). exact (H x). *)
  - intros F. exists (fun x => pi1 (F x)). intros x. exact (pi2 (F x)).
Qed.

Goal forall (X: Type) (p: X -> Type) (Z: Type),
    sigT p -> (forall x, p x -> Z) -> Z.
Proof.
  intros X p Z a f. exact (f (pi1 a) (pi2 a)).
Qed.

Fact pi1_injective X (p: X -> Type) x c x' c' :
  existT p x c = existT p x' c' -> x = x'.
Proof.
  intros H.
  change x with (pi1 (existT p x c)).
  rewrite H. reflexivity.
Qed.

Fail
  Fact pi2_injective X (p: X -> Type) x c x' c' :
  existT p x c = existT p x' c' -> c = c'.

Fact pi2_injective X (p: X -> Type) x c c' :
  existT p x c = existT p x c' -> c = c'.
Proof.
  intros H.
  change c with (pi2 (existT p x c)).
  Fail pattern (existT p x c).
  Fail rewrite H. 
Abort.

Fact SkolemE X Y (p: X -> Y -> Prop) :
  (exists f, forall x, p x (f x)) <=> forall x, exists y, p x y.
Proof.
  split.
  - intros [f H] x. exists (f x). exact (H x).
  - intros F.
Abort.

(*** Full eliminator *)

Definition elim_sigT 
  : forall (X: Type) (p: X -> Type) (q: sigT p -> Type),
    (forall x c, q (existT _ x c)) -> forall a, q a
  := fun X p q f a => match a with existT _ x c => f x c end.
Arguments elim_sigT {X p q}.

Fact sigT_eta X (p: X -> Type) :
  forall a, a = existT p (pi1 a) (pi2 a).
Proof.
  apply elim_sigT. cbn. reflexivity.
Qed.

Fact pi1_elim X (p: X -> Type) :
  pi1 (p:=p) = elim_sigT (q:= fun _ => X) (fun x c => x).
Proof.
  reflexivity.
Qed.

Fact pi2_elim X (p: X -> Type) (a: sigT p) :
  pi2 (p:=p) = elim_sigT (q:= fun a => p (pi1 a)) (fun x c => c).
Proof.
  reflexivity.
Qed.

Goal forall x y, x - y = if pi2 (distance x y) then 0 else pi1 (distance x y).
Proof.
  intros x y.
  destruct (distance x y) as [z [H|H]]; cbn.
  - subst y. lia.
  - subst x. lia.
Qed.

Goal forall x y, (x - y) + (y - x) = pi1 (distance x y).
Proof.
  intros x y.
  destruct (distance x y) as [z [H|H]]; cbn.
  - subst y. lia.
  - subst x. lia.
Qed.

Module ProductAsSigma.
Section ProductAsSigma.
  Variables X Y: Type.
  Definition p (_:X) := Y.
  Definition f
    : X * Y -> sigT p
    := fun z => existT  p (fst z) (snd z).
  Definition g
    : sigT p -> X * Y
    := fun a => (pi1 a, pi2 a).

  Fact gf_eq z :
    g (f z) = z.
  Proof.
    destruct z as [x y]. cbv. reflexivity.
  Qed.

  Fact fg_eq a :
    f (g a) = a.
  Proof.
    revert a. apply elim_sigT. cbv. reflexivity.
    (* destruct a as [x y]. reflexivity. *)
  Qed.
End ProductAsSigma.
End ProductAsSigma.

Module SumAsSigma.
Section SumAsSigma.
  Variables X Y: Type.
  Definition p (b: bool) := if b then X else Y.
  Definition f
    : X + Y -> sigT p
    := fun t => match_sum t (existT p true) (existT p false).

  Definition g
    : sigT p -> X + Y
    := fun a => match a with
               existT _ true x => inl x
             | existT _ false y => inr y
             end.

  Fact gf_eq t :
    g (f t) = t.
  Proof.
    destruct t as [x|y]; cbn. all:reflexivity.
  Qed.

  Fact fg_eq a :
    f (g a) = a.
  Proof.
    destruct a as [[|] z]; cbn. all:reflexivity.
  Qed.
End SumAsSigma.
End SumAsSigma.

(*** Truncation *)

Inductive trunc (X: Type) : Prop := T (x:X).

Goal forall P Q, P \/ Q <-> trunc (P + Q).
Proof.
  split.
  - intros [a|b]; constructor; auto.
  - intros [[a|b]]; auto.
Qed.

Goal forall X (p: X -> Prop), ex p <-> trunc (sig p).
Proof.
  split.
  - intros [x H]. constructor. eauto.
  - intros [[x H]]. eauto.
Qed.

Fact trunc_equi X :
  trunc X <=> exists x:X, True.
Proof.
  split.
  - intros [x]. exists x. exact I.
  - intros [x _]. constructor. exact x.
Qed.

Goal forall X (p: X -> Prop), ~ ~ex p <-> ~(sig p -> False).
Proof.
  split.
  - intros H. contradict H. intros [x H1]. eauto.
  - intros H. contradict H. intros [x H1]. eauto.
Qed.

Goal forall P Q, ~ ~(P \/ Q) <-> ~(P + Q -> False).
Proof.
  split.
  - intros H. contradict H. intros [a|a]; eauto.
  - intros H. contradict H.intros [a|a]; eauto.
Qed.

Check (True * True) <-> (True /\ True).
