(*** MPCTT, Chapter Sigma Types *)

From Coq Require Import Lia.

Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) : Type := X + ~ X.
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).

(* We shall use Coq's predefined sigma types but rename the constructors
   and projections.  We also define the big sigma notation to replace
   Coq's curly braces notation *)

Print sigT.
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

(*** Eliminator *)

Definition sig_elim X  (p: X -> Type) (q: sig p -> Type)
  : (forall x y, q (Sig p x y)) -> forall a, q a
  := fun e a => match a with Sig _ x y => e x y end.

(* Our eliminator is computationally equal with 
   Coq's predefined eliminator. *)         

Goal sig_elim = sigT_rect.
Proof.
  reflexivity.
Qed.

(*** Certifying Division *)

Definition div2 :
  forall x, Sigma y, (x = 2*y) %nat + (x = S (2*y)).
Proof.
  induction x as [|x [y [IH|IH]]].
  - exists 0. left. reflexivity.
  - exists y. right. f_equal. exact IH.
  - exists (S y). left. lia. 
Qed.

(* Note the %nat annotation in the statement of div2.  It is
   needed to help with the overloading of "+" and "*" for numbers
   and types. *)

Section Div2.
  Variable F : forall x, Sigma y, (x = 2*y) %nat + (x = S (2*y)).
  Definition D x := let (n,_) := F x in n.
  Definition M x := let (_,a) := F x in if a then 0 else 1.
  Fact Div2 x : x = 2 * D x + M x /\ M x <= 1.
  Proof.
    unfold D, M. destruct (F x) as [n [H|H]]; lia.
  Qed.
  (* Note the use of the let and if-then-else notations sugaring matches. *)
End Div2.

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

Fact trans_skolem X Y (p: X -> Y -> Type) :
  (forall x, Sigma y, p x y) <=> Sigma f: X -> Y, forall x, p x (f x).
Proof.
  split.
  - intros F.
    exists (fun x => let (y,_) := F x in y).
    intros x. destruct (F x) as [y H]. exact H.
  - intros [f H] x. exists (f x). apply H.
Qed.

(*** Projections *)

Check pi1.
Check pi2.

Fact eta_law X (p: X -> Type) :
  forall a, a = Sig p (pi1 a) (pi2 a).
Proof.
  destruct a as [x y]. cbn. reflexivity.
Qed.

Fact sig_elim' X  (p: X -> Type) (q: sig p -> Type)
  : (forall x y, q (Sig p x y)) -> forall a, q a.
Proof.
  intros e a. rewrite eta_law. apply e.
Qed.

Section Translation.
  Variables X Y : Type.
  Variable p: X -> Y -> Type.

  Goal (forall x, Sigma y, p x y) -> Sigma f, forall x, p x (f x).
  Proof.
    exact (fun F => Sig (fun f => forall x, p x (f x))
                   (fun x => pi1 (F x))
                   (fun x => (pi2 (F x)))).
  Qed.

  Goal (Sigma f, forall x, p x (f x)) -> forall x, Sigma y, p x y.
  Proof.
    exact (fun a x => Sig (p x) (pi1 a x) (pi2 a x)).
  Qed.
End Translation.

Goal forall X (p: X -> Type),
    @pi1 X p = sig_elim X p (fun _ => X) (fun x _ => x).
Proof.
  reflexivity.
Qed.

Goal forall X (p: X -> Type),
    @pi2 X p = sig_elim X p (fun a => p (pi1 a)) (fun _ y => y).
Proof.
  reflexivity.
Qed.

Fact pi1_injective X (p: X -> Type) x y x' y' :
  Sig p x y = Sig p x' y' -> x = x'.
Proof.
  intros H.
  change x with (pi1 (Sig p x y)).
  rewrite H. reflexivity.
Qed.

Fact pi1_injective_nondep X Y x y x' y' :
  Sig (fun _: X => Y) x y = Sig _ x' y' -> y = y'.
Proof.
  intros H.
  change y with (pi2 (Sig _ x y)).
  rewrite H. reflexivity.
Qed.

Fail
  Fact pi2_injective X (p: X -> Type) x y x' y' :
  Sig p x y = Sig p x' y' -> y = y'.

Fact pi2_injective X (p: X -> Type) x y y' :
  Sig p x y = Sig p x y' -> y = y'.
Proof.
  (* cannot be shown without assumptions *)
  intros H.
  change y with (pi2 (Sig p x y)).
  change (let z := Sig p x y in pi2 z = y').
  Fail pattern (Sig p x y).
  Fail rewrite H. 
Abort.


(*** Dependent Pair Types *)

Module SigmaTypes.
 
  Inductive sig {X: Type} (p: X -> Type) : Type :=
  | E : forall x, p x -> sig p.
  
  Arguments E {X p}.
   
  Definition elim_sig {X: Type} {p: X -> Type} (q: sig p -> Type)
    : (forall x y, q (E x y)) -> forall a, q a
    := fun e a => match a with E x y => e x y end.

  Definition pi1 {X: Type} {p: X -> Type}
    : sig p -> X
    := fun a => match a with E x _ => x end.

  Definition pi2 {X: Type} {p: X -> Type}
    : forall a: sig p,  p (pi1 a)
    := fun a => match a with E x y => y end.

  Goal forall X (p: X -> Type),
      @pi1 X p = elim_sig (fun _ => X) (fun x y => x).
  Proof.
    cbv. reflexivity.
  Qed.

  Goal forall X (p: X -> Type),
      @pi2 X p = elim_sig (fun a => p (pi1 a)) (fun x y => y).
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

  Definition skolem X Y (p: X -> Y -> Type) :
    (forall x, sig (p x)) <=> sig (fun f => forall x, p x (f x)).
  Proof.
    split.
    - intros F.
      refine (E (fun x => pi1 (F x)) _).
      intros x. exact (pi2 (F x)).
    - intros a.
      refine (elim_sig _ _ a).
      intros f H x. apply (E (f x)). apply H.
  Qed.

  (* Proof much easier with destruct and exists tactic.
     Destruct uses automatically derived eliminator *)          

  Definition skolem' X Y (p: X -> Y -> Type) :
    (forall x, sig (p x)) <=> sig (fun f => forall x, p x (f x)).
  Proof.
    split.
    - intros F. exists (fun x => pi1 (F x)). intros x. exact (pi2 (F x)).
    - intros [f H] x. exists (f x). apply H.
  Qed.

  Fact match_sum X Y :
    forall a: sum X Y, sig (fun x => a = inl x) + sig (fun y => a = inr y).
  Proof.
    apply sum_rect.
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
    (* cannot be shown without assumptions *)
    intros H.
    change c with (pi2 (E x c)).
    Fail pattern (E x c).
    Fail rewrite H. 
  Abort.

End SigmaTypes.

(*** Truncations *)

Inductive trunc (X: Type) : Prop := Trunc (_ : X).
Notation "□ X" := (trunc X) (at level 75, right associativity).

(*** Exercises *)


(** Certifying Distance *)
Definition distance :
  forall x y: nat, Sigma z:nat, (x + z = y)%nat + (y + z = x)%nat.
Proof.
  induction x as [|x IH]; cbn. 
  - intros y. exists y. auto.
  - destruct y; cbn.
    + exists (S x). auto.
    + specialize (IH y) as [z [<-|<-]];
        exists z; auto.
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


