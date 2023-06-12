(*** Sum types *)

Module SumTypes.
  Inductive sum (X Y: Type) : Type := L (x : X) | R (y : Y).
  
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
End SumTypes.

(** Predefined Sum Types *)
Locate "+".
Print sum.

Definition dec (X: Type) := sum X (X -> False).

Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Fact dec_prop_impl P Q:
  dec P -> dec Q -> dec (P -> Q).
Proof.
  unfold dec. intuition.
Qed.

Definition dec_iff_invariance {X Y} :
  (X <=> Y) -> dec X -> dec Y.
Proof.
  intros H [H1|H1].
  - left. apply H, H1.
  - right. intros y. apply H1, H, y.
Defined.

Definition dec2bool {X} : dec X -> bool :=
  fun a => if a then true else false.

(** Products and sums are universe polymorphic *)

Check prod True True.
Check prod bool bool.
Check prod Prop Prop.
Check sum True True.
Check sum bool bool.
Check sum Prop Prop.

(*** Equality Deciders *)

Definition nat_eqdec' :
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

Compute dec2bool (nat_eqdec' 3 5).

Definition eqdec X := forall x y: X, dec (x = y).

Definition nat_eqdec : eqdec nat.
Proof.
  hnf. induction x as [|x IH]; destruct y.
  - left. reflexivity.
  - right. congruence.
  - right. congruence.
  - destruct (IH y) as [H|H].
    + left. congruence.
    + right. congruence.
Defined.

Compute dec2bool (nat_eqdec 3 5).

Fact eqdec_prod X Y :
  eqdec X -> eqdec Y -> eqdec (X*Y).
Proof.
  intros dX dY [x y] [x' y'].
  destruct (dX x x') as [H1|H1].
  - destruct (dY y y') as [H2|H2].
    + left. congruence.
    + right. congruence.
  - right. congruence.
Qed.

Definition nat_eqb (x y: nat) : bool :=
  if nat_eqdec x y then true else false.

(* sum_rect is the predefined eliminator for sums *)

Fact nat_eqb_correct x y :
    nat_eqb x y = true <-> x = y.
Proof.
  unfold nat_eqb.
  pattern (nat_eqdec x y).
  apply sum_rect.
  - tauto.
  - intuition congruence.
Qed.

Fact nat_eqb_correct' x y :
    nat_eqb x y = true <-> x = y.
Proof.
  apply (sum_rect (fun a => (if a then true else false) = true <-> x = y)).
  - tauto.
  - intuition congruence.
Qed.

(* using destruct is more convenient *)

Fact nat_eqb_correct'' x y :
    nat_eqb x y = true <-> x = y.
Proof.
  unfold nat_eqb.
  destruct nat_eqdec as [H|H].
  - tauto.
  - intuition congruence.
Qed.

Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Fact injective_eqdec {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H F x x'.
  destruct (F (f x) (f x')) as [H1|H1].
  - left. apply H, H1.
  - right. congruence.
Qed.

(*** Dependent Pair Types *)

Module SigmaTypes.
 
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
    (forall x, sig (p x)) <=> sig (fun f => forall x, p x (f x)).
  Proof.
    split.
    - intros F.
      exists (fun x => pi1 (F x)).
      intros x. exact (pi2 (F x)).
    - intros a.
      apply (match_sig a).
      intros f H x.
      exists (f x). apply H.
  Defined.

  (* Construction done at term level *)
  Definition skolem' X Y (p: X -> Y -> Type) :
    (forall x, sig (p x)) <=> sig (fun f => forall x, p x (f x)).
  Proof.
    refine (_,_).
    - unshelve refine (fun F => E _ _).
      + exact (fun x => pi1 (F x)).
      + exact (fun x => pi2 (F x)).
    - refine (fun a => (match_sig a (fun f h x => _))).
      cbn in h.
      exact (E (f x) (h x)).
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

(** Predefined Sigma Types *)

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

(** Certifying Distance *)

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

Fact dec_boolean_dec X (p: X -> Prop) :
  (forall x, dec (p x)) <=> Sigma f, forall x, p x <-> f x = true.
Proof.
  split.
  - intros F.
    exists (fun x => if F x then true else false).
    intros x.
    destruct (F x) as [H|H].
    + tauto.
    + intuition congruence.
  - intros [f H] x. specialize (H x). unfold dec.
    destruct (f x).
    + tauto.
    + right.
      intuition congruence.
Qed.

Fact eqdec_boolean_dec X :
  eqdec X <=> Sigma f, forall (x y: X), x = y <-> f x y = true.
Proof.
  split.
  - intros F.
    exists (fun x y => if F x y then true else false).
    intros x y.
    destruct (F x) as [H|H].
    + tauto.
    + intuition congruence.
  - intros [f H] x y. specialize (H x y). unfold dec.
    destruct (f x).
    + tauto.
    + right.
      intuition congruence.
Qed.

(*** Skolem Theorem *)

Definition skolem X Y (p: X -> Y -> Type) :
  (forall x, Sigma y, p x y) <=> (Sigma f, forall x, p x (f x)).
Proof.
  split.
  - intros F.
    exists (fun x => pi1 (F x)).
    intros x.  exact (pi2 (F x)).
  - intros [f F] x.
    exists (f x). exact (F x).
Defined. 

Fact sig_eta X (p: X -> Type) :
  forall a, a = Sig p (pi1 a) (pi2 a).
Proof.
  intros [x H]. cbn. reflexivity.
Qed.

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

(*** Bijection Types *)

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.
Arguments Bijection {X Y}.

Fact bijection_refl X :
  bijection X X.
Proof.
  exists (fun x => x) (fun x => x); easy.
Qed.

Fact bijection_sym X Y :
  bijection X Y -> bijection Y X.
Proof.
  intros [f g H1 H2]. exists g f; assumption.
Qed.

Fact bijection_trans X Y Z :
  bijection X Y -> bijection Y Z -> bijection X Z.
Proof.
  intros [f g H1 H2] [f' g' H1' H2'].
  exists (fun x => f' (f x)) (fun z => g (g' z)).
  - intros z. rewrite H1'. apply H1.
  - intros x. rewrite H2. apply H2'.
Qed.

Definition bijection_prod X Y :
  bijection (X * Y) (sig (fun x: X => Y)).
Proof.
  unshelve eexists.
  - intros [x y]. exists x. exact y.
  - intros [x y]. exact (x,y).
  - intros [x y]. reflexivity.
  - intros [x y]. reflexivity.
Defined.

Definition bijection_sum X Y :
  bijection (X + Y) (sig (fun b: bool => if b then X else Y)).
Proof.
  unshelve eexists.
  - intros [x|y].
    + exists true. exact x.
    + exists false. exact y.
  - intros [[] z].
    + left. exact z.
    + right. exact z. 
  - intros [x|y]; reflexivity.
  - intros [[] z]; reflexivity.
Defined.

Definition bij_bij_sig X Y:
  bijection (bijection X Y) (Sigma f g, @inv X Y g f /\ inv f g).
Proof.
  unshelve eexists.
  - intros [f g H1 H2]. exists f, g. exact (conj H1 H2).
  - intros (f&g&H1&H2). exact (Bijection f g H1 H2). 
  - intros [f g H1 H2]. reflexivity.
  - intros (f&g&H1&H2). reflexivity.
Defined.

Fact bij_empty X Y :
  (X -> False) -> (Y -> False) -> bijection X Y.
Proof.
  intros f g.
  exists (fun x => match f x with end) (fun y => match g y with end).
  - intros x. exfalso. easy.
  - intros y. exfalso. easy.
Qed.

Goal bijection nat bool -> False.
Proof.
  intros [f g H _].
  assert (f 0 = f 1 \/ f 0 = f 2 \/ f 1 = f 2) as [H3| [H3|H3]].
  { destruct (f 0), (f 1), (f 2); auto. }
  all: apply (f_equal g) in H3.
  all: rewrite !H in H3.
  all: easy.
Qed.

(*** Option Types *)

Definition option_eqdec {X} :
  eqdec X -> eqdec (option X).
Proof.
  intros H [x|] [y|].
  - specialize (H x y) as [H|H].
    + left. congruence.
    + right. congruence.
  - right. congruence.
  - right. congruence.
  - left. reflexivity.
Defined.

Definition option_eqdec_backwards {X} :
  eqdec (option X) -> eqdec X.
Proof.
  intros H x y.
  specialize (H (Some x) (Some y)) as [H|H].
  - left. congruence.
  - right. congruence.
Defined.

Compute dec2bool (option_eqdec nat_eqdec (Some 3) (Some 5)).

(** Bijection Theorem *)

Fact R {X Y f g} :
  @inv (option X) (option Y) g f ->
  forall x, Sigma y, match f (Some x) with Some y' => y = y' | None => f None = Some y end.
Proof.
  intros H x.
  destruct (f (Some x)) as [y|] eqn:E1.
  - exists y. reflexivity.
  - destruct (f None) as [y|] eqn:E2.
    + exists y. reflexivity.
    + exfalso. congruence.
Qed.

Fact R_inv {X Y f g} :
  forall (H1: @inv (option X) (option Y) g f)
    (H2: inv f g),
    inv (fun y => pi1 (R H2 y)) (fun x => pi1 (R H1 x)).
Proof.
  intros H1 H2 x.
  destruct (R H1 x) as [y H3]; cbn.
  destruct (R H2 y) as [x' H4]; cbn.
  revert H3 H4.  
  destruct (f (Some x)) as [y1|] eqn:E.
  - intros <-. rewrite <-E, H1. easy.
  - intros <-.  rewrite H1. rewrite <-E, H1. congruence.
Qed.

Theorem bijection_option X Y : 
  bijection (option X) (option Y) -> bijection X Y.
Proof.
  intros [f g H1 H2].
  exists (fun y => pi1 (R H1 y)) (fun x => pi1 (R H2 x)); apply R_inv.
Qed.

(*** Truncation *)

Inductive box (X: Type) : Prop := T (x:X).

Goal forall P Q, P \/ Q <-> box (P + Q).
Proof.
  split.
  - intros [a|b]; constructor; auto.
  - intros [[a|b]]; auto.
Qed.

Goal forall X (p: X -> Prop), ex p <-> box (sig p).
Proof.
  split.
  - intros [x H]. constructor. eauto.
  - intros [[x H]]. eauto.
Qed.

Fact box_equi X :
  box X <=> exists x:X, True.
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

Module Choice.
  Arguments existT {A P}.
  Implicit Types X Y: Type.
  Implicit Type P: Sigma X, X -> Prop.

  Definition choice X Y :=
    forall p: X -> Y -> Prop, (forall x, ex (p x)) -> exists f, forall x, p x (f x).
  Definition wo X :=
    forall p: X -> Prop, ex p -> sig p.

  Fact wo2choice :
    box (forall X, wo X) -> forall X Y, choice X Y.
  Proof.
    intros [W] X Y p F.
    exists (fun x => pi1 (W Y (p x) (F x))).
    intros x.
    destruct (W Y (p x) (F x)) as [y pxy].
    exact pxy.
  Qed.

  Fact choice2wo :
    (forall X Y, choice X Y) -> box (forall X, wo X).
  Proof.
    intros C.
    destruct (C (Sigma P, ex (pi2 P))
                (Sigma P, sig (pi2 P))
                (fun a b => pi1 a = pi1 b))
      as [f H].
    - intros [[X p] [x px]]. cbn in *.
      exists (Sig (Sig X p) (Sig x px)). reflexivity.
    - constructor. intros X p exp.
      generalize (H (Sig (Sig X p) exp)). cbn.
      destruct f as [P sigP]. cbn. intros <-. exact sigP.
  Qed.

  Goal (forall X Y, choice X Y) <-> box (forall X, wo X).
  Proof.
    split.
    - apply choice2wo.
    - Fail apply wo2choice.
      (* There is a universe conflict *)
  Abort.
End Choice.


(*** Coq's Decision Format *)

(** Coq offers support for equality decisions 
    but uses a different decision format. *)

Print sumbool.
From Coq Require Import Arith.
Search concl: ({_=_} + {_}).

Definition dec_adapt (P: Prop) :
  { P } + { ~ P} <=> dec P.
Proof.
  split.
  - intros [H|H].
    + left. exact H.
    + right. exact H.
  - intros [H|H].
    + left. exact H.
    + right. exact H.
Defined.

Definition coq_nat_eqdec : eqdec nat.
Proof.
  intros x y. apply dec_adapt. decide equality.
Defined.

Compute dec2bool (coq_nat_eqdec 3 5).

Definition coq_nat_eqdec' : eqdec nat.
Proof.
  intros x y. apply dec_adapt. apply Nat.eq_dec.
Defined.

Compute dec2bool (coq_nat_eqdec' 3 5).

Definition coq_option_eqdec {X} :
  eqdec X -> eqdec (option X).
Proof.
  intros H x y. apply dec_adapt. decide equality.
  apply dec_adapt, H.
Defined.
  
Compute dec2bool (coq_option_eqdec coq_nat_eqdec (Some 5) (Some 5)).
