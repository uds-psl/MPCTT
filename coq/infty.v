Unset Elimination Schemes.

Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Module Definitions.
  Inductive sum (X Y: Type) : Type :=
  | L: X -> sum X Y
  | R: Y -> sum X Y.
  Arguments L {X Y}.
  Arguments R {X Y}.
  
  Definition match_sum {X Y Z: Type} 
    : sum X Y -> (X -> Z) -> (Y -> Z) -> Z
    := fun a e1 e2 => match a with L x => e1 x | R y => e2 y end.
 
  Inductive sig {X: Type} (p: X -> Type) : Type :=
  | E : forall x: X, p x -> sig p.
  Arguments E {X p}.
 
  Definition match_sig {X: Type} {p: X -> Type} {Z: Type}
    : sig p -> (forall x, p x -> Z) -> Z
    := fun a e => match a with E x c => e x c end.

  Definition pi1 {X: Type} {p: X -> Type}
    : sig p -> X
    := fun a => match a with E x _ => x end.

  Definition pi2 {X: Type} {p: X -> Type}
    : forall a: sig p,  p (pi1 a)
    := fun a => match a with E x c => c end.

  Definition skolem X Y (p: X -> Y -> Type) :
    sig (fun f => forall x, p x (f x)) <=> forall x, sig (p x).
  Proof.
    split.
    - intros a.
      apply (match_sig a). intros f H x.
      exists (f x). apply H.
    - intros H. exists (fun x => pi1 (H x)). intros x.
      exact (pi2 (H x)).
  Defined.
    
  Definition skolem' X Y (p: X -> Y -> Type) :
    sig (fun f => forall x, p x (f x)) <=> forall x, sig (p x).
  Proof.
    split.
    - intros [f H] x. exists (f x). apply H.
    - intros H. exists (fun x => pi1 (H x)). intros x.
      destruct (H x) as [y H1]. exact H1.
  Defined.
    
  Definition elim_sig {X: Type} {p: X -> Type} (q: sig p -> Type)
    : (forall x c, q (E x c)) -> forall a, q a
    := fun e a => match a with E x c => e x c end.

  Goal forall X (p: X -> Type),
      @pi1 X p = elim_sig (fun _ => X) (fun x c => x).
  Proof.
    cbv. reflexivity.
  Qed.

  Goal forall X (p: X -> Type),
      @pi2 X p = elim_sig (fun a => p (pi1 a)) (fun x c => c).
  Proof.
    reflexivity.
  Qed.

  Fact eta X (p: X -> Type) :
    forall a: sig p, E (pi1 a) (pi2 a) = a.
  Proof.
    (* cannot be shown with match_sig *)
    refine (elim_sig _ _).
    cbn. reflexivity.
  Qed.

  Fact pi1_injective X (p: X -> Type) x (c: p x) x' (c': p x') :
    E x c = E x' c' -> x = x'.
  Proof.
  intros H.
  change x with (pi1 (E x c)).
  rewrite H. reflexivity.
  Qed.

  Fail
    Fact pi2_injective X (p: X -> Type) x (c: p x) x' (c': p x') :
    E x c = E x' c' -> c = c'.
  
  Fact pi2_injective X (p: X -> Type) x (c c': p x) :
    E x c = E x c' -> c = c'.
  Proof.
    intros H.
    change c with (pi2 (E x c)).
    Fail pattern (E x c).
    Fail rewrite H. 
  Abort.

End Definitions.

Locate "+".
Print sum.

Definition nat_eqdec :
  forall x y: nat, (x = y) + (x <> y).
Proof.
  induction x as [|x IH]; destruct y.
  - left. reflexivity.
  - right. intros [=].
  - right. intros [=].
  - destruct (IH y) as [H|H].
    + left. f_equal. exact H.
    + right. intros [= <-]. easy.
Defined.

(** We use the predefined sigma types with customized notation *)

Print sigT.
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition distance :
  forall x y: nat, Sigma z, sum (x + z = y) (y + z = x).
Proof.
  induction x as [|x IH]; cbn. 
  - intros y. exists y. auto.
  - destruct y; cbn.
    + exists (S x). auto.
    + specialize (IH y) as [z IH].
      exists z. intuition.
Defined.

Fact sumAsSigma X Y:
  X + Y <=> Sigma b: bool, if b then X else Y.
Proof.
  split.
  - intros [x|y].
      + exists true. exact x.
      + exists false. exact y.
  - intros [[|] z]; auto.
Defined.

Module ProductAsSigma.
Section ProductAsSigma.
  Variables X Y: Type.
  Definition p (_:X) := Y.
  Definition f
    : X * Y -> sig p
    := fun z => Sig p (fst z) (snd z).
  Definition g
    : sigT p -> X * Y
    := fun a => (pi1 a, pi2 a).

  Fact gf_eq z :
    g (f z) = z.
  Proof.
    destruct z as [x y]. reflexivity.
  Qed.

  Fact fg_eq a :
    f (g a) = a.
  Proof.
    destruct a as [x y]. reflexivity.
  Qed.
End ProductAsSigma.
End ProductAsSigma.

Module SumAsSigma.
Section SumAsSigma.
  Variables X Y: Type.
  Definition p (b: bool) := if b then X else Y.
  Definition f
    : X + Y -> sig p
    := fun a => match a with
             | inl x => Sig p true x
             | inr y => Sig p false y
             end.
  
  Definition g
    : sigT p -> X + Y
    := fun a => match a with
             | Sig _ true x => inl x
             | Sig _ false y => inr y
             end.

  Fact gf_eq a :
    g (f a) = a.
  Proof.
    destruct a as [x|y]; reflexivity.
  Qed.

  Fact fg_eq a :
    f (g a) = a.
  Proof.
    destruct a as [[|] z]; reflexivity.
  Qed.
End SumAsSigma.
End SumAsSigma.

(*** Full eliminator needed *)

Fact sig_eta X (p: X -> Type) :
  forall a, a = Sig p (pi1 a) (pi2 a).
Proof.
  intros [x H]. cbn. reflexivity.
Qed.

From Coq Require Import Lia.

Goal forall x y, x - y = if pi2 (distance x y) then 0 else pi1 (distance x y).
Proof.
  intros x y.
  destruct (distance x y) as [z [<-|<-]]; cbn; lia.
Qed.

Goal forall x y, (x - y) + (y - x) = pi1 (distance x y).
Proof.
  intros x y.
  destruct (distance x y) as [z [<-|<-]]; cbn; lia.
Qed.

Module Ex_eta.
Section Ex_eta.
  Variables (P: Prop) (p: P -> Prop).
  Definition pi1 (a: ex p) : P :=
    match a with ex_intro _ x c => x end.
  Definition pi2 (a: ex p) : p (pi1 a) :=
    match a with ex_intro _ x c => c end.
  Goal forall a, a = ex_intro p (pi1 a) (pi2 a).
  Proof.
    intros [x a]. reflexivity.
  Qed.
End Ex_eta.
End Ex_eta.

(*** Truncation *)

Inductive trunc (X: Type) : Prop :=
| T: X -> trunc X.

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
  - intros H. contradict H. intros [a|a]; eauto.
Qed.

Check (True * True) <-> (True /\ True).
