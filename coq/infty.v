Unset Elimination Schemes.
(* Switches off automatic generation of eliminators *)

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
 
  Definition elim_sum {X Y: Type} (p: sum X Y -> Type)
    : (forall x, p (L x)) -> (forall y, p (R y)) -> forall a, p a
    := fun e1 e2 a => match a with L x => e1 x | R y => e2 y end.

  Fact L_injective (X Y: Type) (x x': X) :
    L (Y:= Y) x = L x' -> x = x'.
  Proof.
    intros H.
    change (match_sum (Y:= Y) (L x) (fun x => x) (fun _ => x) = x').
    rewrite H.
    reflexivity.
  Qed.    
 
  Inductive sig {X: Type} (p: X -> Type) : Type :=
  | E : forall x: X, p x -> sig p.
  Arguments E {X p}.
 
  Definition match_sig {X: Type} {p: X -> Type} {Z: Type}
    : sig p -> (forall x, p x -> Z) -> Z
    := fun a e => match a with E x c => e x c end.
    
  Definition elim_sig {X: Type} {p: X -> Type} (q: sig p -> Type)
    : (forall x c, q (E x c)) -> forall a, q a
    := fun e a => match a with E x c => e x c end.

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

  Fact match_sum' X Y :
    forall a: sum X Y, sig (fun x => a = L x) + sig (fun y => a = R y).
  Proof.
    apply elim_sum.
    - intros x. left. exists x. reflexivity.
    - intros y. right. exists y. reflexivity.
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

(*** Predefined Sum and Sigma Types *)

Locate "+".
Print sum.

(** We use customized notation for the predefined sigma types *)
Print sigT.
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Module ProductAsSigma.
Section M.
  Variables X Y: Type.
  Definition p: X -> Type := fun _=>  Y.
  Definition f
    : X * Y -> sig p
    := fun a => Sig p (fst a) (snd a).
  Definition g
    : sig p -> X * Y
    := fun a => match a with Sig _ x c => (x, c) end.

  Fact gf_eq a :
    g (f a) = a.
  Proof.
    destruct a as [x y]. reflexivity.
  Qed.
  Fact fg_eq a :
    f (g a) = a.
  Proof.
    destruct a as [x y]. reflexivity.
  Qed.
End M.
End ProductAsSigma.

Module SumAsSigma.
Section M.
  Variables X Y: Type.
  Definition p: bool -> Type := fun b => if b then X else Y.
  Definition f
    : X + Y -> sig p
    := fun a => match a with
             | inl x => Sig p true x
             | inr y => Sig p false y
             end.  
  Definition g
    : sig p -> X + Y
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
End M.
End SumAsSigma.

(*** Projections *)

Definition skolem X Y (p: X -> Y -> Type) :
  (forall x, Sigma y, p x y) <=> (Sigma f, forall x, p x (f x)).
Proof.
  split.
  - intros F.
    exists (fun x => pi1 (F x)).
    intros x. exact (pi2 (F x)).
  - intros [f F] x.
    exists (f x). exact (F x).
Defined. 

Fact sig_eta X (p: X -> Type) :
  forall a, a = Sig p (pi1 a) (pi2 a).
Proof.
  intros [x H]. cbn. reflexivity.
Qed.

Module Ex_eta.
Section M.
  Variables (P: Prop) (p: P -> Prop).
  Definition pi1 (a: ex p) : P :=
    match a with ex_intro _ x c => x end.
  Definition pi2 (a: ex p) : p (pi1 a) :=
    match a with ex_intro _ x c => c end.
  Goal forall a, a = ex_intro p (pi1 a) (pi2 a).
  Proof.
    intros [x a]. reflexivity.
  Qed.
End M.
End Ex_eta.

(*** Equality Decider *)

Definition eqdec :
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

Definition eqb (x y: nat) : bool :=
  if eqdec x y then true else false.

(* sum_rect is the predefined eliminator for sums *)

Fact eqb_correct x y :
    eqb x y = true <-> x = y.
Proof.
  unfold eqb.
  pattern (eqdec x y).
  apply sum_rect.
  - tauto.
  - intuition congruence.
Qed.

Fact eqb_correct' x y :
    eqb x y = true <-> x = y.
Proof.
  apply (sum_rect (fun a => (if a then true else false) = true <-> x = y)).
  - tauto.
  - intuition congruence.
Qed.

(* using destruct is more convenient *)

Fact eqb_correct'' x y :
    eqb x y = true <-> x = y.
Proof.
  unfold eqb.
  destruct eqdec as [H|H].
  - tauto.
  - intuition congruence.
Qed.


(*** Distance *)

Definition distance :
  forall x y: nat, Sigma z, sum (x + z = y) (y + z = x).
Proof.
  induction x as [|x IH]; cbn. 
  - intros y. exists y. auto.
  - destruct y; cbn.
    + exists (S x). auto.
    + specialize (IH y) as [z [<-|<-]];
        exists z; auto.
Defined.

Compute
  let d := distance 17 4 in
  (pi1 d, if pi2 d then true else false).

From Coq Require Import Lia.

Section Distance.
  Variable D: forall x y: nat, Sigma z, sum (x + z = y) (y + z = x).
  
  Fact D_sub x y :
      x - y = if pi2 (D x y) then 0 else pi1 (D x y).
  Proof.
    destruct (D x y) as [z [<-|<-]]; cbn; lia.
  Qed.

  Fact D_pi1 x y :
      pi1 (D x y) = (x - y) + (y - x).
  Proof.
    destruct (D x y) as [z [<-|<-]]; cbn; lia.
  Qed.

  Goal pi1 (D 3 7) = 4.
  Proof.
    rewrite D_pi1. reflexivity.
  Qed.
End Distance.

(*** Division by 2 *)

Definition Div_two :
  forall x, Sigma n, sum (x = n * 2) (x = S ( n * 2)).
Proof.
  induction x as [|x IH]; cbn.
  - exists 0. left. reflexivity.
  - destruct IH as [n [-> | ->]]; cbn.
    + exists n; cbn. right. reflexivity.
    + exists (S n); cbn. left. reflexivity.
Defined.

Definition div_two (x: nat) : nat * nat :=
  let (n,a) := Div_two x in (n, if a then 0 else 1).

Compute div_two 15.

Section Div_two.
  Variable D: forall x, Sigma n, sum (x = n * 2) (x = S ( n * 2)).
  Definition d (x: nat) : nat * nat :=
    let (n,a) := D x in (n, if a then 0 else 1).

  Fact d_correct x :
    let  (n,k) := d x in
    x = k + n*2 /\ (k = 0 \/ k = 1).
  Proof.
    unfold d.
    destruct (D x) as [n [-> | ->]]; cbn; auto.
  Qed.
End Div_two.

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

(*** Coq specialiaties *)

(* Products are universe polymorpihic *)
Check (True * True) <-> (True /\ True).
