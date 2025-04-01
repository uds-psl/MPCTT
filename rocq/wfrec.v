From Stdlib Require Import Arith Lia.
Unset Elimination Schemes. 

Section Acc.
  Variables (X: Type) (R: X -> X -> Prop).
  Inductive Acc (x: X) : Prop := AccC (h: forall y, R y x -> Acc y).
  Fact Acc_iff x :
    Acc x <-> forall y, R y x -> Acc y.
  Proof.
    split.
    - intros [h]. exact h.
    - apply AccC.
  Qed.
  Variable p: X -> Type.
  Variable F: (forall x, (forall y, R y x -> p y) -> p x).
  Definition W'
    : forall x, Acc x -> p x
    := fix f x a :=
         match a with AccC _ h => F x (fun y r => f y (h y r)) end.
  Definition wf := forall x, Acc x.
End Acc.
Arguments Acc {X}.
Arguments AccC {X R}.
Arguments W' {X R p}.
Arguments wf {X}.
Definition W {X R p} H F x := @W' X R p F x (H x).

Fact Acc_ext {X} {R R': X -> X -> Prop} :
  (forall x y, R' x y -> R x y) -> forall x, Acc R x -> Acc R' x.
Proof.
  intros H.
  apply W'. intros x IH.
  constructor. intros y H1%H.
  apply IH, H1.
Qed.

Fact lt_wf :
  wf lt.
Proof.
  hnf.
  enough (forall n x, x < n -> Acc lt x) by eauto.
  induction n as [|n IH].
  - easy.
  - intros x H. constructor. intros y H1. apply IH. lia.
Defined.
 
Section Lexical_product.
  Variables (X: Type) (R: X -> X -> Prop).
  Variables (Y: Type) (S: Y -> Y -> Prop).
  Definition lex (a b: X * Y) : Prop :=
    R (fst a) (fst b) \/ fst a = fst b /\ S (snd a) (snd b).
  Fact lex_wf :
    wf R -> wf S -> wf lex.
  Proof.
    intros H1 H2 [x y]. revert x y.
    refine (W H1 _). intros x IH1.
    refine (W H2 _). intros y IH2.
    constructor. intros [x' y']. unfold lex at 1. cbn. intros [H|[-> H]].
    - apply IH1, H.
    - apply IH2, H.
  Defined.
End Lexical_product.
Arguments lex {X} R {Y}.
Arguments lex_wf {X R Y S}.
  
Section Retract.
  Variables (X Y: Type) (R: Y -> Y -> Prop) (sigma: X -> Y).
  Definition retract (x x': X) := R (sigma x) (sigma x').
  Fact retract_wf :
    wf R -> wf retract.
  Proof.
    intros H.
    enough (forall y x,  sigma x = y -> Acc retract x) by (hnf;eauto).
    refine (W H _). intros y IH x H1.
    constructor. intros x' H2.
    apply (IH (sigma x')). 2:reflexivity.
    destruct H1. exact H2.
  Defined.
  Definition size_rec :
    wf(R) -> forall p: X -> Type,
      (forall x, (forall x', R (sigma x') (sigma x) -> p x') -> p x) ->
      forall x, p x.
  Proof.
    intros R_wf p. apply (W (retract_wf R_wf)).
  Defined.
End Retract.
Arguments retract_wf {X Y R}.

From Stdlib Require Import FunctionalExtensionality.

Fact Acc_unique X (R: X -> X -> Prop) :
  forall x (a a': Acc R x), a = a'.
Proof.
  enough (forall x (a: Acc R x) (a a': Acc R x), a = a') by eauto.
  refine (W' _). intros x IH [h] [h']. f_equal.
  extensionality y. extensionality r. apply IH, r.
Qed.

Print Assumptions Acc_unique.

Fact W_eq
     {X} {R: X -> X -> Prop} {R_wf: wf R}
     {p: X -> Type}
     {F: forall x, (forall y, R y x -> p y) -> p x}
     (x: X)
  : W R_wf F x = F x (fun y _ => W R_wf F y).
Proof.
  unfold W. destruct (R_wf x) as [h]. cbn.
  f_equal. extensionality y. extensionality r.
  f_equal. apply Acc_unique.
Qed.

Fact W_unique 
     {X} {R: X -> X -> Prop} {R_wf: wf R}
     {p: X -> Type}
     {F: forall x, (forall y, R y x -> p y) -> p x}
     (f f': forall x, p x)
  : (forall x, f x = F x (fun y r => f y)) ->
    (forall x, f' x = F x (fun y r => f' y)) ->
    forall x, f x = f' x.
Proof.
  intros H1 H2.
  apply (W R_wf). intros x IH.
  rewrite H1, H2.
  f_equal. extensionality y. extensionality r.
  apply IH,r.
Qed.

(* A function useed for hiding lia-generated termination proofs *)
Definition tau {X x} : X := x.

(** Euclidean division with W *)

(* Guarded step function, y pulled out as parameter *)
Definition Div (y x : nat) (h: forall x', x' < x -> nat) : nat.
Proof.
  refine (if le_lt_dec x y then 0 else S (h (x - S y) tau)).
  lia. 
Defined.

Definition div x y : nat := W lt_wf (Div y) x.
Compute div 16 3.
Fact div_eq x y :
  div x y = if le_lt_dec x y then 0 else S (div (x - S y) y).
Proof.
  exact (W_eq x).
Qed.

Print Assumptions div_eq.

(** GCDs with W *)
(* Note: Pairing introduces considerable bureaucratic pain *)

Module GCD.
Implicit Types (x y: nat) (a b: nat * nat).
Definition sigma a := fst a + snd a.

Definition GCD a : (forall b, sigma b < sigma a -> nat) -> nat.
Proof.
  (* must take h late because of dependency on a *)
  refine (match a with
          | (0, y) => fun _ => y
          | (S x, 0) => fun _ => S x
          | (S x, S y) => fun h => match (le_lt_dec x y) with
                               | left H => h (S x, y - x) tau
                               | right H => h (x - y, S y) tau
                               end
          end).
  all: cbn; lia.
Defined.

Definition gcd x y : nat := W (retract_wf sigma lt_wf) GCD (x,y).

Compute gcd 49 63.
     
Fact gcd_eq3 x y :
  gcd (S x) (S y) = if le_lt_dec x y
                    then gcd (S x) (y - x)
                    else gcd (x - y) (S y).
Proof.
  refine (W_eq _).
Qed.
 
Fact gcd_eq x y :
  gcd x y = match x, y with
            | 0, y => y
            | S x, 0 => S x
            | S x, S y => if le_lt_dec x y
                         then gcd (S x) (y - x)
                         else gcd (x - y) (S y)
            end.
Proof.
  unfold gcd. rewrite W_eq.
  destruct x. reflexivity.
  destruct y; reflexivity.
Qed.

End GCD.

(** Ackermann with W *)

Definition ACK a : (forall b, lex lt lt b a -> nat) -> nat.
Proof.
  (* must take h late because of dependency on a *)
  (* tuned so that computation works, 
     "_" in place of tau, auto instead of lia.
     Fragile, I don't understand it *)
  refine (match a with
          | (0, y) => fun _ => S y
          | (S x, 0) => fun h => h (x, 1) tau
          | (S x, S y) => fun h => h (x, h (S x, y) tau) _
          end).
  Unshelve.
  all: unfold lex; cbn; auto.
Defined.

Definition ack x y : nat := W (lex_wf lt_wf lt_wf) ACK (x,y).

Compute ack 3 3. 
 
Fact ack_eq x y :
  ack x y = match x, y with
            | 0, y => S y
            | S x, 0 => ack x 1
            | S x, S y => ack x (ack (S x) y)
            end.
Proof.
  unfold ack. rewrite W_eq.
  destruct x. reflexivity.
  destruct y; reflexivity.
Qed.

(** Unfolding equation without FE *)

Section Unfolding.
  Variables
    (X: Type) (R: X -> X -> Prop)
    (p: X -> Type)
    (F: forall x, (forall y, R y x -> p y) -> p x).

  Implicit Types (x y : X) (f: forall x, p x).
  
  Definition Ext := 
    forall x h h', (forall y r, h y r = h' y r) -> F x h = F x h'.

  Variable F_ext: Ext.

  Lemma W'_ext x a a' :
    W' F x a = W' F x a'.
  Proof.
    revert x a a'.
    enough (forall x (a: Acc R x), forall a a', W' F x a = W' F x a') by eauto.
    refine (W' (fun x IH => _)).
    intros [phi] [phi']. cbn.
    apply F_ext. intros y r.
    apply IH, r.
  Qed.

  Definition sat f :=
    forall x, f x = F x (fun y _ => f y).

  Variable R_wf: wf R.
 
  Fact W_eq' :
    sat (W R_wf F).
  Proof.
    intros x. unfold W. destruct (R_wf x) as [phi]. cbn.
    apply F_ext. intros y r. apply W'_ext.
  Qed.

  Fact unique f f' :
    sat f -> sat f' -> forall x, f x = f' x.
  Proof.
    intros H1 H2.
    apply (W R_wf). intros x IH.
    rewrite H1, H2. apply F_ext. exact IH.
  Qed.
End Unfolding.
Arguments Ext {X R p} F.
Arguments W_eq' {X R p F} F_ext R_wf.

Fact Div_ext y :
  Ext (Div y).
Proof.
  intros x h h' H. unfold Div.
  destruct le_lt_dec as [H1|H1].
  - reflexivity.
  - f_equal. apply H.
Qed.

Fact GCD_ext :
  Ext GCD.GCD.
Proof.
  intros [x y] h h' H.
  destruct x. reflexivity.
  destruct y. reflexivity.
  unfold GCD.GCD.
  destruct le_lt_dec as [H1|H1]; apply H.
Qed.

Fact ACK_ext :
  Ext ACK.
Proof.
  intros [x y] h h' H.
  destruct x. reflexivity.
  destruct y; cbn.
  - apply H.
  - rewrite H. unfold tau. rewrite H. reflexivity.
Qed.

(** Padding *)

Section Padding.
  Variables (X: Type) (R: X -> X -> Prop).
  Definition des x (a: Acc R x) : forall y, R y x -> Acc R y :=
    match a with AccC _ phi => phi end.
  Fixpoint pad n x (a: Acc R x) : Acc R x :=
    match n with
    | 0 => a
    | S n' => AccC x (fun y r => pad n' y (des x a y r))
    end.
  Variables (x: X) (a: Acc R x) (n:nat).
  Eval cbn in pad (4 + n) x a.
End Padding.

(** Classical Characterization *)

From Stdlib Require Import Classical_Prop.

Section Classical.
  Variables (X: Type) (R: X -> X -> Prop).
  Implicit Types (x y: X) (p: X -> Prop).
  
  Fact char_wf_ind :
    wf R <-> forall p: X -> Prop, (forall x, (forall y, R y x -> p y) -> p x) -> forall x, p x.
  Proof.
    split; intros H.
    - intros p. apply W. exact H.
    - refine (H (Acc R) _). apply AccC.
  Qed.

  Definition pro_pred p := forall x, p x -> exists y, p y /\ R y x.
  Definition pro x := exists p, p x /\ pro_pred p.

  Fact pro_disjoint x :
    Acc R x -> pro x -> False.
  Proof.
    revert x. refine (W' _). intros x IH.
    intros (p&H1&H2). apply H2 in H1 as (y&H1&H3).
    eapply IH. exact H3. exists p. easy.
  Qed.
  
  Fact pro_exhaustive_xm x :
    Acc R x \/ pro x.
  Proof.
    classical_right.
    exists (fun x => ~Acc R x). split. exact H.
    clear. intros x H.
    apply NNPP. contradict H. constructor. intros y H1.
    apply NNPP. contradict H. exists y; easy.
  Qed.
  
  Fact char_wf_pro_xm :
    wf R <-> ~ex pro.
  Proof.
    split.
    - intros H (x&H1). specialize (H x).
      eapply pro_disjoint; eassumption.
    - intros H x.
      destruct (pro_exhaustive_xm x) as [H1|H1]. exact H1.
      contradict H. exists x. exact H1.
  Qed.

  Definition min p x := p x /\ forall y, p y -> ~R y x.
 
  Fact pro_min_xm p :
    pro_pred p <-> ~ ex (min p).
  Proof.
    split; intros H.
    - intros (x&H2&H3).
      apply H in H2 as (y&H2&H4). eapply H3; eassumption.
    - intros x H2. apply NNPP. contradict H.
      exists x. split. exact H2.
      intros y H4 H5. apply H. exists y; easy.
  Qed.

  Fact pro_min_pred_xm :
    ~ex pro <-> forall p, ex p -> ex (min p).
  Proof.
    split; intros H.
    - intros p [x H1].
      apply NNPP. intros H2%pro_min_xm.
      apply H. exists x,p; easy.
    - intros (y&p&H1&H2%pro_min_xm).
      apply H2, H. exists y. exact H1.
  Qed.
  
  Fact char_wf_min_xm :
    wf R <-> forall p, ex p -> ex (min p).
  Proof.
    rewrite char_wf_pro_xm. apply pro_min_pred_xm.
  Qed.
End Classical.
Print Assumptions char_wf_min_xm.

(** Transitive closure *)

Section Transitive_closure.
  Variables (X: Type) (R: X -> X -> Prop).
  Inductive TC (x y: X) : Prop :=
  | TC1 : R x y -> TC x y
  | TC2 y' : TC x y' -> R y' y -> TC x y.
  Fact TC_wf :
    wf R -> wf TC.
  Proof.
    intros H. hnf.
    refine (W H _). intros y IH.
    constructor. intros x H1.
    destruct H1 as [H1|y' H1 H2].
    - apply IH, H1.
    - apply IH in H2. destruct H2 as [H2].
      apply H2, H1.
  Qed.
  Fact TC_ind x (p: X -> Prop) :
    (forall y, R x y -> p y) ->
    (forall y' y, p y' -> R y' y -> p y) ->
    forall y, TC x y -> p y.
  Proof.
    intros e1 e2.
    refine (fix f y a := match a with
                         | TC1 _ _ r => e1 y r
                         | TC2 _ _ y' a r => e2 y' y _ r
                         end).
    refine (f y' a).
  Qed.
  Fact TC_trans x y z :
    TC x y -> TC y z -> TC x z.
  Proof.
    intros H. revert z. apply TC_ind.
    - intros z. apply TC2, H.
    - intros y' z. apply TC2.
  Qed.
End Transitive_closure.

Section Successor_relation.
  Definition R_S (x y: nat) := S x = y.
  Fact R_S_wf :
    wf R_S.
  Proof.
    hnf. induction x as [|x IH].
    - constructor. unfold R_S at 1. easy.
    - constructor. unfold R_S at 1. intros y [= ->]. exact IH.
  Qed.
End Successor_relation.

(** Void *)

Goal Acc eq I -> forall X, X.
Proof.
  generalize I.
  refine (W' _).
  intros x IH.
  apply (IH x).
  reflexivity.
Qed.

(** Existential Witness Operator *)

Module EWO.
Section EWO.
  Variable p: nat -> Prop.
  Variable p_dec: forall n, p n + ~p n.
  Implicit Types x y: nat.

  Let R x y := (x = S y) /\ ~p y.

  Fact R_Acc x y :
    p (x + y) -> Acc R y.
  Proof.
    induction x as [|x IH] in y |-*;
      intros H; constructor; intros ? [-> H1].
    - exfalso. easy.
    - apply IH. rewrite <-plus_n_Sm. easy.
  Qed.

  Fact R_Acc_Sigma :
    forall x, Acc R x -> sigT p.
    refine (W' _). intros x IH.
    destruct (p_dec x) as [H1|H1].
    - exists x. exact H1.
    - apply (IH (S x)). easy.
  Qed.

  Fact EWO :
    ex p -> sigT p.
  Proof.
    intros H.
    apply (R_Acc_Sigma 0).
    destruct H as [x H].
    apply (R_Acc x 0).
    rewrite plus_0_r. exact H.
  Qed.
End EWO.
End EWO.
  
(** Exercise: Prove that (TC R_S) is < on numbers *)

Fact exercise_loop (X: Type) (R: X -> X -> Prop) :
  forall x y, R x y -> R y x -> ~Acc R x.
Proof.
  intros x y H1 H2 H3. revert x H3 y H1 H2.
  refine (W' _). intros x IH y H1 H2.
  eapply IH; eassumption.
Qed.

(** Extraction *)

Require Import Extraction.
Recursive Extraction GCD.gcd.

