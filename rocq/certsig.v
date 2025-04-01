(*** MPCTT, Chapter Sigma Types *)

From Stdlib Require Import Lia.

Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) : Type := X + ~ X.
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).

(*** Sigma types *)

Module SigmaTypes.
  Inductive sig (X: Type) (p: X -> Type) : Type :=
  | Sig : forall x, p x -> sig X p.

  Arguments sig {X}.
  Arguments Sig {X}.

  Definition elim_sig {X: Type} {p: X -> Type} (q: sig p -> Type)
    : (forall x y, q (Sig p x y)) -> forall a, q a
    := fun f a => match a with Sig _ x y => f x y end.

  Definition pi1 {X: Type} {p: X -> Type}
    : sig p -> X
    := fun a => match a with Sig _ x _ => x end.

  Definition pi2 {X: Type} {p: X -> Type}
    : forall a: sig p, p (pi1 a)
    := fun a => match a with Sig _ _ y => y end.

  Fact eta_law X (p: X -> Type) :
    forall a, a = Sig p (pi1 a) (pi2 a).
  Proof.
    apply elim_sig. cbn. reflexivity.
  Qed.

  Fact pi1_injective X (p: X -> Type) x y x' y' :
    Sig p x y = Sig p x' y' -> x = x'.
  Proof.
    intros H.
    change x with (pi1 (Sig p x y)).
    rewrite H. reflexivity.
  Qed.

  Fact pi2_injective_nondep X Y x y x' y' :
  Sig (fun _: X => Y) x y = Sig _ x' y' -> y = y'.
  Proof.
    intros H.
    change y with (pi2 (Sig _ x y)).
    rewrite H. reflexivity.
  Qed.

  (* Injectivity in the second component cannot be shown in general *)

  Fail
    Fact pi2_injective X (p: X -> Type) x y x' y' :
    Sig p x y = Sig p x' y' -> y = y'.

  Fact pi2_injective X (p: X -> Type) x y y' :
    Sig p x y = Sig p x y' -> y = y'.
  Proof.
    (* cannot be shown without assumptions *)
    intros H.
    change y with (pi2 (Sig p x y)).
    Fail pattern (Sig p x y).
    Fail rewrite H. 
  Abort.

  Goal forall X (p: X -> Type),
      @pi1 X p = @elim_sig X p (fun _ => X) (fun x _ => x).
  Proof.
    reflexivity.
  Qed.

  Goal forall X (p: X -> Type),
      @pi2 X p = @elim_sig X p (fun a => p (pi1 a)) (fun _ y => y).
  Proof.
    reflexivity.
  Qed.

End SigmaTypes.

(* We shall use Rocq's predefined sigma types from now on.
   We rename the constructors and projections to better fit MPCTT.  
   We also define the big sigma notation 
   (replacing Rocq's curly braces notation *)

Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

(*** Certifying Division *)

Goal
  forall x, Sigma y, (x = 2*y)%nat + (x = S (2*y)).
Proof.
  induction x as [|x [y [IH|IH]]].
  - exists 0. auto. 
  - exists y. right. congruence.
  - exists (S y). left. lia. 
Qed.

(* Note the "%nat" annotation in the statement of div2.  It is
   needed to help with the overloading of "+" and "*" 
   for numbers and types. *)

Goal (forall x, Sigma y, (x = 2*y)%nat + (x = S (2*y))) <=>
  (Sigma D M, (forall x, x = 2 * D x + M x /\ M x < 2) %nat).
Proof.
  split.
  - intros F.
    exists (fun x => pi1 (F x)).
    exists (fun x => if pi2 (F x) then 0 else 1).
    intros x.
    destruct (F x) as [y [H|H]]; cbn; lia.
  - intros (D&M&H) x.
    specialize (H x).
    exists (D x).     
    destruct (M x) as [|b].
    + left. lia.
    + right. lia.
Qed.

(*** Translation Theorems *)

Fact trans_eqdec X :
  eqdec X <=> Sigma f: X -> X -> bool, forall x y, x = y <-> f x y = true.
Proof.
  split.
  - intros d.
    exists (fun x y => if d x y then true else false).
    intros x y.
    destruct (d x y) as [H|H]; intuition congruence.
  - intros [f H] x y. specialize (H x y).
    destruct (f x y); unfold dec; intuition easy.
Qed.

Fact trans_eqdec' X :
  eqdec X <=> Sigma f: X -> X -> bool, forall x y, if f x y then x = y else x <> y.
Proof.
  split.
  - intros d.
    exists (fun x y => if d x y then true else false).
    intros x y.
    destruct (d x y) as [H|H]; easy.
  - intros [f H] x y. specialize (H x y).
    destruct (f x y); unfold dec; intuition.
Qed.

Fact trans_p_dec X (p: X -> Type) :
  decider p <=> Sigma f: X -> bool, forall x, p x <=> f x = true.
Proof.
  split.
  - intros d.
    exists (fun x => if d x then true else false).
    intros x.
    destruct (d x) as [H|H]; unfold iffT; intuition easy.
  - intros [f H] x. specialize (H x).
    destruct (f x); unfold dec, iffT in *; intuition easy.
Qed.

Fact trans_p_dec' X (p: X -> Type) :
  decider p <=> Sigma f: X -> bool, forall x, if f x then p x else ~ p x.
Proof.
  split.
  - intros d.
    exists (fun x => if d x then true else false).
    intros x.
    destruct (d x) as [H|H]; unfold iffT; easy.
  - intros [f H] x. specialize (H x).
    destruct (f x); unfold dec, iffT in *; auto. 
Qed.

Fact trans_skolem X Y (p: X -> Y -> Type) :
  (forall x, Sigma y, p x y) <=> Sigma f: X -> Y, forall x, p x (f x).
Proof.
  split.
  - intros F.
    exists (fun x => pi1 (F x)).
    intros x. destruct (F x) as [y H]. cbn. exact H.
  - intros [f H] x. exists (f x). apply H.
Qed.

(*** Truncation *)

Definition trunc X := forall Z:Prop, (X -> Z) -> Z.
Notation "□ X" := (trunc X) (at level 30, right associativity).

Goal forall P Q, P /\ Q <-> □ (P * Q).
Proof.
  intros *; split.
  - intros H Z H1. tauto.
  - intros H. apply H. tauto.
Qed.

Goal forall P Q, P \/ Q <-> □ (P + Q).
Proof.
  intros *; split.
  - intros H Z. tauto.
  - intros H. apply H. tauto.
Qed.


Goal forall X p, @ex X p <-> □ @sig X p.
Proof.
  intros *; split.
  - intros [x H] Z H1. apply H1. eauto.
  - intros H. apply H. intros [x Hx]. eauto.
Qed.

Goal forall X, ~X <-> ~ □ X.
Proof.
  intros *; split; intros H.
  - intros H2. apply H2. easy.
  - intros x. apply H. intros Z. auto.
Qed.

Inductive truncation X : Prop := Truncation (_: X).

Goal forall X, truncation X <-> □ X.
Proof.
  intros X. split.
  - intros [x] Z. auto.
  - intros H. apply H. intros x. constructor. exact x.
Qed.

(*** Exercises *)

(** Certifying Distance *)
Fact distance :
  forall x y, Sigma z, (x + z = y)%nat + (y + z = x)%nat.
Proof.
  induction x as [|x IH]; cbn. 
  - intros y. exists y. auto.
  - destruct y; cbn.
    + exists (S x). auto.
    + specialize (IH y) as [z [<-|<-]]; exists z; auto.
Qed.

Section Distance.
  Variable D: forall x y: nat, Sigma z, (x + z = y)%nat + (y + z = x)%nat.
  
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

Fact skolem_prop_bool Y (p: bool -> Y -> Prop) :
  (forall x, exists y, p x y) <=> (exists f, forall x, p x (f x)).
Proof.
  split.
  - intros F.
    destruct (F true) as [y1 H1].
    destruct (F false) as [y2 H2].
    exists (fun x: bool => if x then y1 else y2).
    destruct x; assumption.
  - intros [f H] x. exists (f x). apply H.
Qed.

Fact skolem_prop_prop X (Y: Prop) (p: X -> Y -> Prop) :
  (forall x, exists y, p x y) <=> (exists f, forall x, p x (f x)).
Proof.
  split.
  - intros F.
    exists (fun x => let (y,_) := F x in y).
    intros x. destruct (F x) as [y H]. exact H.
  - intros [f H] x. exists (f x). apply H.
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

Goal forall x, Sigma a b, (x = 2 * a + b /\ b < 2)%nat.
Proof.
  induction x as [|x (a&b&H)].
  - exists 0, 0. lia.
  - destruct b.
    + exists a, 1. lia.
    + exists (S a), 0. lia.
Qed.

Goal
  (forall x, Sigma a b, (x = 2 * a + b /\ b < 2)%nat) <=>
    (forall x, Sigma a, (x = 2 * a)%nat + (x = S (2 * a))).
Proof.
  split; intros F x.
  - specialize (F x) as (a&b&H).
    exists a. destruct b; intuition lia.
  - specialize (F x) as [a [H|H]]; exists a.
    + exists 0. lia.
    + exists 1. lia.
Qed.

Goal
  (forall x, exists a b, x = 2 * a + b /\ b < 2) <->
    (forall x, exists a, x = 2 * a \/ x = S (2 * a)).
Proof.
  split; intros F x.
  - specialize (F x) as (a&b&H).
    exists a. destruct b; intuition lia.
  - specialize (F x) as [a [H|H]]; exists a.
    + exists 0. lia.
    + exists 1. lia.
Qed.

