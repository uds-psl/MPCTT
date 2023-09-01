From Coq Require Import Lia List.
Definition dec (X: Type) : Type := X + (X -> False).
Definition decider {X} (p: X -> Type) : Type := forall x, dec (p x).
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
Definition eqdec X := forall x y: X, dec (x = y).
Fact eqdec_nat : eqdec nat.
Proof.
  hnf; induction x as [|x IH]; destruct y as [|y]; unfold dec in *.
  1-3: intuition congruence.
  destruct (IH y); intuition congruence.
Qed.
Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.
Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.
Definition bijective {X Y} (f: X -> Y) :=
  injective f /\ surjective f.

Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).

Fixpoint nrep {X} (A: list X) : Prop :=
  match A with
  | [] => True
  | x::A => x nel A /\ nrep A
  end.
Definition covering {X} (A: list X) :=
  forall x, x el A.
Definition listing {X} (A: list X) :=
  covering A /\ nrep A.
Definition fin n X : Type :=
  eqdec X * Sigma A,  @listing X A /\ length A = n.
Fact fin_zero X :
  fin 0 X <=> (X -> False).
Proof.
  split.
  - intros [D (A&[H1 _]&H2)] x.
    specialize (H1 x). destruct A; easy.
  - intros H. split.
    + intros x. easy.
    + exists nil. easy.
Qed.

Definition segment A := forall k, k el A <-> k < length A.
Definition serial (A: list nat) := forall n k, n el A -> k <= n -> k el A.
Fact map_injective {X Y f x A} :
  @injective X Y f -> f x el map f A -> x el A.
Proof.
  intros H (?&->%H&H2) %in_map_iff. exact H2.
Qed.
Fact nrep_map X Y f A :
  @injective X Y f -> nrep A -> nrep (map f A).
Proof.
  intros H.
  induction A as [|x A IH]; cbn.
  - auto.
  - intros [H2 H3]. split. 
    + contradict H2. eapply map_injective; eassumption.
    + auto.
Qed.
Fact nrep_nat_large_el (A: list nat) n :
  nrep A -> length A = S n -> Sigma k, k el A /\ k >= n.
Admitted. (* Proof is in file list.v *)
Fact serial_segment A :
  serial A -> nrep A -> segment A.
Admitted. (* Proof is in file list.v *)

(*** Injections *)

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.
Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (_: inv g f).
Inductive bijection (X Y: Type) : Type :=
| Bijection {f: X -> Y} {g: Y -> X} (_: inv g f) (_: inv f g).
Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  intros H x x' H1 %(f_equal g). rewrite !H in H1. exact H1.
Qed.

Fact injection_nat_x_nat : injection (nat * nat) nat.
Proof.
  From Coq Require Import Arith.Cantor.
  exists to_nat of_nat. exact cancel_of_to.
Qed.

Fact injection_nat_option X :
  injection X nat -> injection (option X) nat.
Proof.
  intros [f g H].
  exists (fun a => match a with Some x => S (f x) | None => 0 end)
    (fun n => match n with 0 => None | S n => Some ( g n) end).
  intros [x|]; congruence.
Qed.

Fact injection_option X Y :
  injection (option X) Y -> X -> injection X Y.
Proof.
  intros [f g H] x0.
  exists (fun x => f (Some x))
    (fun y => match g y with Some x => x | None => x0 end).
  intros x. rewrite H. reflexivity.
Qed.

Fact fin_injection_nat X n :
  fin (S n) X -> injection X nat.
Admitted. (* Proof is in file finty.v *)

(*** Least *)

Definition safe (p: nat -> Prop) n := forall k, p k -> k >= n.
Definition least (p: nat -> Prop) n := p n /\ safe p n.
Notation unique p := (forall x x', p x -> p x' -> x = x').

Fact least_unique (p: nat -> Prop) :
  unique (least p).
Proof.
  intros x y [H1 H2] [H3 H4].
  enough (x <= y /\ y <= x) by lia. split.
  - apply H2, H3.
  - apply H4, H1.
Qed.

Fact safe_S p n :
  safe p n -> ~p n -> safe p (S n).
Proof.
  intros H1 H2 k H3. specialize (H1 k H3).
  enough (k <> n) by lia. congruence.
Qed.

Fact least_sigma (p: nat -> Prop) :
  decider p -> sig p -> sig (least p).
Proof.
  intros d.
  enough (forall n, sig (least p) + safe p n) as F.
  { intros [n Hn]. destruct (F n) as [H|H]. easy. exists n. easy. }
  induction n as [|n [IH|IH]].
  - right. hnf; lia.
  - eauto.
  - destruct (d n) as [H|H].
    + left. exists n. easy.
    + right. apply safe_S; easy.
Qed.

Fact least_exists (p: nat -> Prop) :
  decider p -> ex p -> ex (least p).
Proof.
  intros d [n Hn].
  destruct (least_sigma p d) as [x H]; eauto.
Qed.

Definition XM : Prop := forall X: Prop, X \/ ~X.

Fact least_xm_exists (p: nat -> Prop) :
  XM -> ex p -> ex (least p).
Proof.
  intros xm.
  enough (forall n, ex (least p) \/ safe p n) as H1.
  { intros [n H]. specialize (H1 n) as [H1|H1]. easy. exists n; easy. }
  induction n as [|n [IH|IH]].
  - right. hnf; lia.
  - left. exact IH.
  - destruct (xm (p n)) as [H|H].
    + left. exists n. easy.
    + right. apply safe_S; easy.
Qed.

(*** Equality deciders *)

Fact eqdec_bot : eqdec False.
Proof.
  intros [].
Qed.

Fact eqdec_injective {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H d x x'. specialize (H x x').
  destruct (d (f x) (f x')) as [H1|H1];
    unfold dec in *; intuition congruence.
Qed.

Fact eqdec_injection X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros [f g H] d x1 x2.
  destruct (d (f x1) (f x2)) as [H1|H1];
    unfold dec; intuition congruence.
Qed.

Fact eqdec_option X :
  eqdec X <=> eqdec (option X).
Proof.
  split; intros d.
  - intros [x1|] [x2|].
    2-4:  unfold dec; intuition congruence.
    specialize (d x1 x2).
    unfold dec in *; intuition congruence.
  - intros x1 x2.
    specialize (d (Some x1) (Some x2)).
    unfold dec in *; intuition congruence.
Qed.

Fact eqdec_sum X Y :
  eqdec X * eqdec Y <=> eqdec (X + Y).
Proof.
  split.
  - intros [dX dY] [x1|y1] [x2|y2].
    + destruct (dX x1 x2); unfold dec in *; intuition congruence.
    + unfold dec in *; intuition congruence.
    + unfold dec in *; intuition congruence.
    + destruct (dY y1 y2); unfold dec in *; intuition congruence.
  - intros d; split.
    + intros x1 x2.
      destruct (d (inl x1) (inl x2)); unfold dec in *; intuition congruence.
    + intros y1 y2.
      destruct (d (inr y1) (inr y2)); unfold dec in *; intuition congruence.
Qed.

Fact eqdec_prod X Y :
  eqdec X -> eqdec Y -> eqdec (X * Y).
Proof.
  intros dX dY [x1 y1] [x2 y2].
  destruct (dX x1 x2), (dY y1 y2);
    unfold dec in *; intuition congruence.
Qed.

(*** Enumerators *)

Definition enum' X (f: nat -> option X) := forall x, exists n, f n = Some x.

Definition enum X := sig (enum' X).

Fact enum_bot : enum False.
Proof.
  exists (fun _ => None). intros [].
Qed.

Fact enum_nat : enum nat.
Proof.
  exists Some. hnf; eauto.
Qed.

Fact enum_injection X Y :
  injection X Y -> enum Y -> enum X.
Proof.
  intros [f g H] [e H1].
  exists (fun n => match e n with Some x => Some (g x) | None => None end).
  intros x. specialize (H1 (f x)) as [n H1].
  exists n. rewrite H1. congruence.
Qed.

Fact enum_option X :
  enum X <=> enum (option X).
Proof.
  split; intros [e H].
  - exists (fun n => Some match n with 0 => None| S n => e n end).
    intros [x|].
    + specialize (H x) as [n H]. exists (S n). congruence.
    + exists 0. reflexivity.
  - exists (fun n => match e n with Some (Some x) => Some x | _ => None end).
    intros x.
    specialize (H (Some x)) as [n H].
    exists n. rewrite H. reflexivity.
Qed.

Fact enum_sum X Y :
  enum X * enum Y <=> enum (X + Y).
Proof.
  split.
  - intros [[eX HX] [eY HY]].
    destruct injection_nat_x_nat as [f g H].
    exists (fun n => match g n with
             | (0,n) => match eX n with
                       | Some x => Some (inl x)
                       | None => None
                       end
             | (1,n) => match eY n with
                       | Some y => Some (inr y)
                       | None => None
                       end
             | _ => None
             end).
    intros [x|y].
    + specialize (HX x) as [n HX].
      exists (f (0,n)). rewrite H, HX. reflexivity.
    + specialize (HY y) as [n HY].
      exists (f (1,n)). rewrite H, HY. reflexivity.
  - intros [e He]. split.
    + exists (fun n => match e n with Some (inl x) => Some x | _ => None end).
      intros x. specialize (He (inl x)) as [n He].
      exists n. rewrite He. reflexivity.
    + exists (fun n => match e n with Some (inr y) => Some y | _ => None end).
      intros y. specialize (He (inr y)) as [n He].
      exists n. rewrite He. reflexivity.
Qed.

Fact enum_prod X Y :
  enum X -> enum Y -> enum (X * Y).
Proof.
  intros [eX HX] [eY HY].
  destruct injection_nat_x_nat as [f g H].
  exists (fun n => let (nx,ny) := g n in
           match eX nx, eY ny with
           | Some x, Some y => Some (x,y)
           | _, _ => None
           end).
  intros (x,y).
  destruct (HX x) as [nx Hx].
  destruct (HY y) as [ny Hy].
  exists (f (nx,ny)).
  rewrite H, Hx, Hy.
  reflexivity.
Qed.

(*** Co_Enumerators *)

Definition co_enum {X} (g: X -> nat) f :=
  forall x, f (g x) = Some x.

Fact co_enum_enum X f g :
  co_enum g f -> enum' X f.
Proof.
  intros H x. exists (g x). congruence.
Qed.

Fact co_enum_injective X f g :
  @co_enum X g f -> injective g.
Proof.
  intros H x y H1 %(f_equal f). congruence.
Qed.

Fact co_enum_eqdec X f g :
  @co_enum X g f -> eqdec X.
Proof.
  intros H %co_enum_injective.
  generalize H eqdec_nat. apply eqdec_injective.
Qed.

(*** EWOs *)

Definition ewo X := forall (p: X -> Prop), decider p -> ex p -> sig p.

Fact ewo_bot : ewo False.
Proof.
  intros p _ [[] _].
Qed.

Fact ewo_nat : ewo nat.
Proof.
  (* Proof is in file ewo.v *)
  intros p H1 H2.
  From Coq Require Import ConstructiveEpsilon.
  apply constructive_indefinite_ground_description_nat in H2.
  - destruct H2; eauto. 
  - intros n. destruct (H1 n); auto.
Qed.

Fact ewo_injection X Y :
  injection X Y -> ewo Y -> ewo X.
Proof.
  intros [f g H] e p d H1.
  destruct (e (fun y => p (g y))) as [y H2].
  - intros y. apply d.
  - destruct H1 as [x H1]. exists (f x). congruence.
  - eauto.
Qed.

Fact ewo_option X :
  ewo X <=> ewo (option X).
Proof.
  split; intros e p d H.
  - destruct (d None) as [H1|H1]. {eauto.}
    destruct (e (fun x => p (Some x))) as [x H2].
    + intros x. apply d.
    + destruct H as [[x|] H].
      * eauto.
      * exfalso. auto.
    + eauto.
  - destruct (e (fun a => match a with Some x => p x | None => False end)) as [[x|] H1].
    + intros [x|]. {apply d.} right. easy.
    + destruct H as [x H]. exists (Some x). easy.
    + eauto.
    + contradict H1.
Qed.

Fact least_dec (p: nat -> Prop) :
  decider p -> decider (least p).
Proof.
  intros d n.
  destruct (d n) as [H|H].
  2:{ right. intros [H2 _]. easy. }
  destruct (least_sigma p d) as [x Hx]. {eauto.}
  destruct (eqdec_nat x n) as [->|H1]. {left. exact Hx.}
  right. intros H2. contradict H1.
  eapply least_unique; eassumption.
Qed.

Fact least_ewo (p: nat -> Prop) :
  decider p -> ex p -> sig (least p).
Proof.
  intros d H. apply least_sigma. exact d.
  apply ewo_nat; assumption.
Qed.

(*** Inverse functions via EWOs *)

Fact co_inv_ex {X Y f} :
  @surjective X Y f -> ewo X -> eqdec Y -> Sigma g, inv f g.
Proof.
  intros H e d.
  enough (G: forall y, Sigma x, f x = y).
  { exists (fun y => pi1 (G y)). intros y. apply (pi2 (G y)). }
  intros y. apply e.
  - intros x. apply d.
  - apply H. 
Qed.

Fact bijection_ex X Y f :
  @bijective X Y f -> ewo X -> eqdec Y -> Sigma g, inv g f /\ inv f g.
Proof.
  intros [H1 H2] e d.
  destruct (co_inv_ex H2 e d) as [g H3].
  exists g. split. 2:exact H3.
  intros x. apply H1. congruence.
Qed.

Fact co_enum_ex {X f} :
  eqdec X -> enum' X f -> Sigma g, co_enum g f.
Proof.
  intros d H.
  assert (F: forall x, Sigma n, f n = Some x).
  { intros x. apply ewo_nat.
    - intros n. apply eqdec_option in d. apply d.
    - apply H. }
  exists (fun x => pi1 (F x)). intros x. apply (pi2 (F x)).
Qed.

(*** Countable Types *)

Definition cty X := (eqdec X * enum X) %type.

Fact cty_bot : cty False.
Proof.
  split. apply eqdec_bot. apply enum_bot.
Qed.

Fact cty_nat : cty nat.
Proof.
  split. apply eqdec_nat. apply enum_nat.
Qed.

Fact cty_injection X Y :
  injection X Y -> cty Y -> cty X.
Proof.
  intros H [d e]. split.
  - apply eqdec_injection in H; assumption.
  - apply enum_injection in H; assumption.
Qed.

Fact cty_sum X Y :
  cty X -> cty Y -> cty (X + Y).
Proof.
  intros [dX eX] [dY eY]. split.
  - apply eqdec_sum. split; assumption.
  - apply enum_sum. split; assumption.
Qed.

Fact cty_prod X Y :
  cty X -> cty Y -> cty (X * Y).
Proof.
  intros [dX eX] [dY eY]. split.
  - apply eqdec_prod; assumption.
  - apply enum_prod; assumption.
Qed.

Fact cty_nat_x_nat : cty (nat * nat).
Proof.
  apply cty_prod; apply cty_nat.
Qed.

Fact cty_option X :
  cty X <=> cty (option X).
Proof.
  split; intros [d e]; split.
  - revert d. apply eqdec_option.
  - revert e. apply enum_option.
  - revert d. apply eqdec_option.
  - revert e. apply enum_option.
Qed.

Fact cty_char_co_enum X :
  cty X <=> Sigma g f, @co_enum X g f.
Proof.
  split.
  - intros (d&f&H).
    destruct (co_enum_ex d H) as [g Hg]. exists g, f. exact Hg.
  - intros (g&f&H). split.
    + eapply co_enum_eqdec, H.
    + exists f. eapply co_enum_enum, H.
Qed.

Fact cty_char_retract X :
  cty X <=> injection (option X) nat.
Proof.
  split.
  - intros (g&f&H) %cty_char_co_enum.
    exists (fun a => match a with Some x => S (g x) | None => 0 end)
      (fun n => match n with 0 => None | S n => f n end).
    intros [x|]; easy.
  - intros H. apply cty_injection in H.
    + revert H. apply cty_option.
    + apply cty_nat.
Qed.

Fact cty_ewo {X} :
  cty X -> ewo X.
Proof.
  intros H %cty_char_retract %ewo_injection.
  - revert H. apply ewo_option.
  - apply ewo_nat.
Qed.

Fact cty_injection_nat X :
  injection X nat -> cty X.
Proof.
  intros H. apply cty_char_retract, injection_nat_option, H.
Qed.

Fact cty_inhabited_injection X :
  cty X -> X -> injection X nat.
Proof.
  intros H %cty_char_retract. apply injection_option, H.
Qed.

Fact Cantor X :
  ~ex (@surjective X (X -> bool)).
Proof.
  intros [f H].
  specialize (H (fun x => negb (f x x))) as [x H].
  enough (f x x = negb (f x x)) by (destruct (f x x); easy).
  pattern (f x) at 1. now rewrite H.
Qed.

Fact uncountable :
  cty (nat -> bool) -> False.
Proof.
  intros [f g H] %(cty_inhabited_injection (nat -> bool)).
  2: exact (fun _ => true).
  apply (Cantor nat). exists g. intros h. exists (f h). apply H.
Qed.

(*** Injections into nat *)

Definition prefix {X} (A B: list X) := exists A', A ++ A' = B.

Fact prefix_refl {X} (A: list X) :
  prefix A A.
Proof.
  exists nil. apply app_nil_r.
Qed.

Fact prefix_trans {X} (A B C: list X) :
  prefix A B -> prefix B C -> prefix A C.
Proof.
  intros [D1 H1] [D2 H2]. exists (D1 ++ D2).
  rewrite app_assoc, H1. exact H2.
Qed.

Section SubPos.
  Variable X : Type.
  Variable X_escape: X.
  Variable X_eqdec : eqdec X.
    
  Implicit Types (x : X) (A : list X).
 
  Fixpoint sub A n : X :=
    match A, n with
      [], _ => X_escape
    | x::A', 0 => x
    | x::A', S n' => sub A' n'
    end.

  Fixpoint pos A x : nat :=
    match A with
      [] => 0
    | y::A' => if X_eqdec y x then 0 else S (pos A' x)
    end.
   
  Fact sub_pos x A :
    x el A -> sub A (pos A x) = x.
  Proof.
    induction A as [|y A IH]; cbn.
    - intros [].
    - destruct X_eqdec as [<-|H]. easy.
      intros [->|H1]. easy. auto.
  Qed.

  Fact pos_bnd A x :
    x el A -> pos A x < length A.
  Proof.
    induction A as [|y A IH]; cbn.
    - intros [].
    - destruct X_eqdec as [->|H].
      + lia.
      + intros [->|H1].
        * easy.
        * apply IH in H1; lia.
  Qed.

  Fact sub_prefix k A B :
    k < length A -> prefix A B -> sub A k = sub B k.
  Proof.
    intros H [C <-]. revert k H.
    induction A as [|y A IH]; cbn.
    - easy.
    - destruct k. easy.
      intros H. apply IH. lia.
  Qed.
End SubPos.

Section Enumeration.
  Variable X: Type.
  Variable L: nat -> list X.
  Variable beta: X -> nat.
  Variable X_eqdec : eqdec X.
  Variable HL_cum : forall n, prefix (L n) (L (S n)).
  Variable HL_len : forall n, length (L n) < length (L (S n)).
  Variable HL_beta  :  forall x, x el L (beta x).

  Let L_prefix m n :
    m <= n -> prefix (L m) (L n).
  Proof.
    induction n as [|n IH]; intros H.
    - assert (m=0) as -> by lia. apply prefix_refl.
    - assert (m = S n \/ m <= n) as [->|H1] by lia. {apply prefix_refl.}
      generalize (HL_cum n). apply prefix_trans, IH, H1.
  Qed.
  
  Let L_prefix_either m n :
    prefix (L m) (L n) \/ prefix (L n) (L m).
  Proof using L_prefix.
    assert (m <= n \/ n <= m) as [H|H] by lia.
    - left. apply L_prefix, H.
    - right. apply L_prefix, H.
  Qed.

  Let x0 : X.
  Proof.
    destruct (L 1) as [|x A] eqn:E.
    - exfalso. generalize (HL_len 0).
      rewrite E. cbn. lia.
    - exact x. 
  Qed.

  Let Pos:= pos X X_eqdec.
  Let Sub:= sub X x0.
  
  Let L_sub k m n :
    k < length (L m) -> k < length (L n) -> Sub (L m) k = Sub (L n) k.
  Proof.
    intros H1 H2.
    destruct (L_prefix_either m n) as [H|H].
    - now apply sub_prefix.
    - symmetry. now apply sub_prefix.
  Qed.

  Let L_length : forall n, n <= length (L n).
  Proof.
    induction n as [|n IH]. lia.
    specialize (HL_len n). lia.
  Qed.

  Fact list_enumeration :
    injection X nat.
  Proof.
    exists (fun x => Pos (L (beta x)) x)
      (fun n => Sub (L (S n)) n).
    intros x.
    set (k:= Pos (L (beta x)) x).
    enough (Sub (L (S k)) k = Sub (L (beta x)) k) as ->.
    { apply sub_pos, HL_beta. }
    apply L_sub.
    - generalize (L_length (S k)). lia.
    - apply pos_bnd, HL_beta.
  Qed.
End Enumeration.

Check list_enumeration.

(*** More Countable Types *)

Inductive tree := TL (x: nat) | TN (t1 t2: tree).

Fact eqdec_tree :
  eqdec tree.
Proof.
  intros s t. revert t. unfold dec.
  induction s as [x|s1 IH1 s2 IH2]; destruct t as [y|t1 t2].
  - destruct (eqdec_nat x y) as [<- |H1]; intuition congruence.
  - intuition congruence.
  - intuition congruence.
  - specialize (IH1 t1). specialize (IH2 t2). intuition congruence.
Qed.

Fact tree_list_product :
  forall A B, Sigma C, forall s, s el C <-> exists t1 t2, s = TN t1 t2 /\ t1 el A /\ t2 el B.
Proof.
  intros A B. induction A as [|t A [C IH]].
  - exists nil. cbn. firstorder.
  - exists (map (TN t) B ++ C). intros s. split.
    + intros [H|H] %in_app_iff.
      * apply in_map_iff in H as (t'&<-&H). exists t, t'; cbn; auto.
      * apply IH in H as (t1&t2&->&H1&H2). firstorder.
   + intros (t1&t2&->&[->|H1]&H2); apply in_app_iff.
     * left. apply in_map_iff. eauto.
     * right. apply IH. eauto.
Qed.

Fact injection_tree_nat :
  injection tree nat.
Proof.
  pose (L:= fix L n :=
          match n with
          | 0 => []
          | S n => L n ++ TL n :: pi1 (tree_list_product (L n) (L n))
          end).
  pose (beta:= fix beta t :=
          match t with
          | TL n => S n
          | TN t1 t2 => S (beta t1 + beta t2)
          end).

  assert (L_cum: forall m n, m <= n -> L m <<= L n).
  { intros m n H.
    induction n as [|n IH].
    - assert (m = 0) as -> by lia. easy.
    - assert (m = S n \/ m <= n) as [->|H1] by lia. easy.
      cbn. intros t H2. apply in_app_iff. left. apply IH; easy. }

  apply (list_enumeration tree L beta).
  - apply eqdec_tree.
  - intros n. exists ([TL n] ++ pi1 (tree_list_product (L n) (L n))). easy.
  - intros n. cbn. rewrite app_length. cbn. lia.
  - intros t.
    induction t as [x|t1 IH1 t2 IH2]; cbn; apply in_app_iff.
    + cbn; auto.
    + right. right. destruct tree_list_product as [C H]; cbn.
      apply H. exists t1,t2. repeat split.
      * apply L_cum with (m:= beta t1). lia. easy.
      * apply L_cum  with (m:= beta t2). lia. easy.
Qed.

Fact cty_tree :
  cty tree.
Proof.
  apply cty_injection_nat, injection_tree_nat.
Qed.

Fact cty_nat_nat :
  cty (nat * nat).
Proof.
  apply cty_injection with (Y:= tree). 2:exact cty_tree.
  exists (fun a => TN (TL (fst a)) (TL (snd a)))
    (fun t => match t with
           | TN (TL x) (TL y) => (x,y)
           | _ => (0,0)
           end).
  intros [x y]. reflexivity.
Qed.
  
Fact cty_list_nat:
  cty (list nat).
Proof.
  apply cty_injection with (Y:= tree). 2:exact cty_tree.
  pose (f:= fix f A := match A with
                       | [] => TL 0
                       | x::A => TN (TL x) (f A)
                       end).
  pose (g:= fix g t := match t with
                       | TN (TL x) t => x :: g t
                       | _ => []
                       end).
  exists f g. intros A.
  induction A as [|x A IH]; cbn; congruence.
Qed.

Fact cty_list X:
  cty X -> cty (list X).
Proof.
  intros [f g H] %cty_char_retract.
  apply cty_injection with (Y:= list nat). 2:exact cty_list_nat.
  pose (F:= map (fun x => f (Some x))).
  pose (G:= fix G A := match A with
                       | [] => []
                       | n::A => match g n with
                                | Some x => x :: G A
                                | None => []
                                end
                       end).
  exists F G. intros A.
  induction A as [|x A IH]; cbn. easy.
  destruct (g (f (Some x))) as [y|] eqn:E; congruence.
Qed.

Fact injection_list X:
  injection X nat -> injection (list X) (list nat).
Proof.
  intros [f g H].
  exists (map f) (map g). intros A.
  induction A as [|x A IH]; cbn; congruence.
Qed.

(*** Alignments *)

Definition hit {X} (f: X -> nat) n := exists x, f x = n.
Definition serial' {X} (f: X -> nat) := forall n k, hit f n -> k <= n -> hit f k.
Definition alignment {X} (f: X -> nat) := serial' f /\ injective f.
Definition cutoff {X} (f: X -> nat) n :=  forall k, hit f k <-> k < n.

Fact cutoff_unique X (f: X -> nat) n1 n2 :
  cutoff f n1 -> cutoff f n2 -> n1 = n2.
Proof.
  intros H1 H2.
  destruct n1, n2.
  - easy.
  - exfalso.
    enough (hit f n2) by firstorder lia. apply H2. lia.
  - exfalso.
    enough (hit f n1) by firstorder lia. apply H1. lia.
  - enough (~(n1 < n2) /\ ~(n2 < n1)) by lia.
    split; intros H3.
    + enough (hit f (S n1)) by firstorder lia. apply H2. lia.
    + enough (hit f (S n2)) by firstorder lia. apply H1. lia.
Qed.

Fact alignment_bijective_function X (f: X -> nat) :
  alignment f /\ surjective f <-> bijective f.
Proof.
  split.
  - intros [[_ H1] H2]. easy.
  - intros [H1 H2]. split. 2:exact H2. split. 2:exact H1.
    intros n k _ _. apply H2.
Qed.

Fact cty_alignment_bijection X g :
  cty X -> @alignment X g -> surjective g -> bijection X nat.
Proof.
  intros H1 [Hg1 Hg2] H2.
  enough (Sigma f : nat -> X, inv f g /\ inv g f) as (f&H3&H4).
  { exists g f; easy. }
  apply bijection_ex. easy. apply cty_ewo. exact H1. apply eqdec_nat.
Qed.

Fact hit_self X f x :
  @hit X f (f x).
Proof.
  exists x. reflexivity.
Qed.

Fact cty_hit_witness {X f n} :
  cty X -> @hit X f n -> Sigma x, f x = n.
Proof.
  intros H1 H2. apply (cty_ewo H1). 2:exact H2.
  intros x. apply eqdec_nat.
Qed.

Fact cty_alignment_segment {X f} n :
  cty X -> @alignment X f -> hit f n ->
  Sigma A, nrep A /\ length A = S n /\ segment (map f A).
Proof.
  intros H1 [H2 _] H3. (*injevtivity of f not needed *)
  induction n as [|n IH].
  - destruct (cty_hit_witness H1 H3) as [x H4].
    exists [x]. split; cbn. easy. split. easy. hnf; cbn; intuition lia.
  - destruct (cty_hit_witness H1 H3) as [x H4].
    destruct IH as (A&IH1&IH2&IH3).
    { eapply H2. exact H3. lia. }
    exists (x::A). cbn. split. 1:split. 2:exact IH1. 2:split. 2:congruence.
    + intros H5. enough (f x < S n) by lia.
      specialize (IH3 (f x)).
      rewrite map_length, IH2 in IH3.
      apply IH3, in_map, H5.
    + intros k. cbn. specialize (IH3 k). rewrite H4.
      rewrite map_length, IH2. rewrite map_length, IH2 in IH3.
      split.
      * intros [<-|H5]; intuition lia.
      * intros H5.
        assert (k = S n \/ k <= n) as [->|H6] by lia.
        now auto. right. apply IH3. lia.
Qed.

(*** Alignment Construction *)

Definition enum_nrep {X} (f: nat -> option X) : Prop :=
  forall m n, f m = f n -> f m <> None -> m = n.

Fact cty_enum_nrep {X} :
  cty X -> Sigma f, enum' X f /\ enum_nrep f.
Proof.
  intros (d&f&Hf).
  assert (D: forall x, decider (fun n => f n = Some x)).
  { intros x n. apply (eqdec_option X). exact d. }
  exists (fun n => match f n with
           | None => None
           | Some x => if least_dec (fun n => f n = Some x) (D x) n
                      then Some x
                      else None
           end).
  split.
  - intros x.
    destruct (least_exists _ (D x) (Hf x)) as (k&Hk).
    assert (Hx: f k = Some x). {apply Hk.}
    exists k. destruct (f k) as [y|]. 2:easy.
    assert (x=y) as <- by congruence.
    destruct least_dec as [H|H]; easy.
  - intros m n.
    destruct (f m) as [xm|] eqn:Em. 2:easy.
    destruct (f n) as [xn|] eqn:En. 2:easy.
    destruct (least_dec _ _ m) as [H1|H1]. 2:easy.
    destruct (least_dec _ _ n) as [H2|H2]. 2:easy.
    intros [= ->] _. eapply least_unique; eassumption.
Qed.

Lemma serial'' X (f: X -> nat) :
  (forall n, hit f (S n) -> hit f n) -> serial' f.
Proof.
  intros H. hnf. induction n as [|n IH]; intros k H1 H2.
  - assert (k = 0) as -> by lia. exact H1.
  - assert (k = S n \/ k <= n) as [->|H3] by lia; auto.
Qed.

Theorem cty_alignment {X} :
  cty X -> sig (@alignment X).
Proof.
  intros H.
  destruct (cty_enum_nrep H) as (f&H1&H2).
  destruct H as [d _].
  destruct (co_enum_ex d H1) as [g Hg].
  (* hn = # hits f has below n *)
  pose (h := fix h n := match n with
                        | 0 => 0
                        | S n => if f n then S (h n) else h n
                        end).
  assert (h_serial: forall k n, h n = S k -> Sigma m y, m < n /\ f m = Some y /\ h m = k).
  { intros k; induction n as [|n IH]; cbn. lia.
    destruct (f n) as [y|] eqn:E.
    - intros [= <-]. exists n, y. intuition lia.
    - intros (m&y&H)%IH. exists m, y. intuition lia. }
  assert (h_increasing: forall m x n, f m = Some x -> m < n -> h m < h n).
  { intros m x. induction n as [|n IH].
    - lia.
    - intros H3 H4. cbn.
      assert (m = n \/ m < n) as [->|H5] by lia.
      + rewrite H3. lia.
      + destruct (f n) as [y|].
        * specialize (IH H3 H5). lia.
        * auto. }
  exists (fun x => h (g x)). split.
  - apply serial''.
    intros n [x (m&y&H3&H4&<-)%h_serial].
    exists y. enough (g y = m) by congruence.
    apply H2; congruence.
  - intros x y H.
    eapply co_enum_injective. exact Hg.
    enough (g x < g y \/ g y < g x -> False) by lia. 
    intros [H3|H3]; eapply h_increasing in H3; try lia;  apply Hg.
Qed.

(*** Bijection Theorem *)

Lemma cty_injection_hit_transport {X Y f g} :
  cty X -> cty Y -> @alignment X f -> @alignment Y g  ->
  injection X Y -> forall x, Sigma y, g y = f x.
Proof.
  intros H1 H2 H3 H4 [F G H5] x.
  apply (cty_hit_witness H2).
  destruct (cty_alignment_segment (f x) H1 H3) as (A&H7&H8&_).
  {apply hit_self.}
  destruct H3 as [H31 H32], H4 as [H41 H42].
  destruct (nrep_nat_large_el (map g (map F A)) (f x)) as (k&H10&H11).
  { apply nrep_map. exact H42. apply nrep_map.
    eapply inv_injective. exact H5. exact H7. }
  { rewrite !map_length. exact H8. }
  eapply H41. 2:exact H11.
  apply in_map_iff in H10 as (y&<-&H10).
  apply hit_self.
Qed.

Theorem cty_bijection X Y  :
  cty X -> cty Y -> injection X Y -> injection Y X -> bijection X Y.
Proof.
  intros H1 H2 H3 H4.
  destruct (cty_alignment H1) as [f Hf].
  destruct (cty_alignment H2) as [g Hg].
  assert (F:= cty_injection_hit_transport H1 H2 Hf Hg H3).
  assert (G:= cty_injection_hit_transport H2 H1 Hg Hf H4).
  exists (fun x => pi1 (F x)) (fun y => pi1 (G y)).
  - intros x. destruct (F x) as [y HF]. cbn.
    destruct (G y) as [x' HG]. cbn. apply Hf. congruence.
  - intros y. destruct (G y) as [x HG]. cbn.
    destruct (F x) as [y' HF]. cbn. apply Hg. congruence.
Qed.

Fact cty_infinite X :
  injection nat X -> cty X -> bijection X nat.
Proof.
  intros H1 H2. apply cty_bijection.
  exact H2. exact cty_nat. 2: exact H1.
  apply cty_inhabited_injection. exact H2.
  destruct H1 as [f _ _]. exact (f 0).
Qed.

(*** Finite Types and Cutoffs *)

Fact alignment_cutoff_fin X f n :
  cty X -> @alignment X f -> cutoff f n -> fin n X.
Proof.
  intros H1 H2 H3. split. {apply H1.}
  destruct n.
  - exists []. split. 2:easy. split. 2:easy.
    intros x. enough (f x < 0) by lia. apply H3,hit_self.
  - destruct (cty_alignment_segment n H1 H2) as (A&H7&H8&H9).
    {apply H3. lia.} 
    exists A. split. 2:easy. split. 2:easy.
    intros x. eapply map_injective. {apply H2.}
    apply H9. rewrite map_length, H8.
    apply H3, hit_self.
Qed.

Fact fin_alignment_cutoff {X f n} :
  fin n X -> @alignment X f -> cutoff f n.
Proof.
  intros (H1&A&[H2 H3]&<-) [H51 H52]. hnf.
  assert(H6: forall k, hit f k <-> k el map f A).
  { intros k. split; intros H7.
    - apply in_map_iff. destruct H7 as [x H7].
      exists x. split. exact H7. apply H2.
    - apply in_map_iff in H7 as (x&<-&H8). apply hit_self. }
  enough(forall k, k el map f A <-> k < length A). {firstorder.}
  rewrite <- map_length with (f:=f).
  apply serial_segment.
  + intros n k (x&H7&H8) %in_map_iff H9.
    apply H6. revert H9. apply H51. exists x; easy.
  + apply nrep_map. apply H52. exact H3.
Qed.

Fact alignment_fin_not_surjective n X f :
  fin n X -> @alignment X f -> ~surjective f.
Proof.
  intros H1 H2.
  enough (~hit f n) as H. { contradict H. apply H. }
  intros H % (fin_alignment_cutoff H1 H2). lia.
Qed.

(*** Finite or Infinite *)

Fact XM_cutoff_or_surjective X f :
  XM -> @serial' X f -> ex (cutoff f) \/ surjective f.
Proof.
  intros xm H.
  destruct (xm (surjective f)) as [H1|H1]. {auto.} left.
  pose (miss n := ~hit f n).
  enough (ex (least miss)) as [n H2].
  - exists n. intros k. split; intros H3.
    + enough (~ n <= k) by lia. intros H4.
      destruct H2 as [H2 _]. enough (hit f n) by easy.
      revert H3 H4. apply H.
    + destruct (xm (hit f k)) as [H4|H4]. {auto.} exfalso.
      apply H2 in H4. lia.
  - apply least_xm_exists. exact xm.
    destruct (xm (ex miss)) as [H2|H2]. {auto.} exfalso.
    apply H1. intros n.
    destruct (xm (hit f n)) as [H3|H3]. {auto.} exfalso.
    eauto.
Qed.

Inductive box (X: Type) : Prop := T (x:X).

Fact cty_finite_or_infinite {X} :
  XM -> cty X -> box ((Sigma n, fin n X) + bijection X nat).
Proof.
  intros xm H.
  destruct (cty_alignment H) as [f H1].
  edestruct XM_cutoff_or_surjective as [H2|H2]. exact xm. now apply H1.
  - destruct H2 as [n H2]. constructor. left. exists n.
    eapply alignment_cutoff_fin; eassumption.
  - constructor. right.
    eapply cty_alignment_bijection; eassumption.
Qed.

Fact cty_retract_or_empty {X} :
  XM -> cty X -> box (injection X nat) \/ (X -> False).
Proof.
  intros xm H.
  destruct (cty_finite_or_infinite xm H) as [[[n H1]|[f g H1 _]]].
  - destruct n. 
    + right. apply fin_zero, H1.
    + left. constructor. eapply fin_injection_nat, H1.
  - left. constructor. exists f g. exact H1.
Qed.
