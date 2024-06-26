(*** MPCTT, Chapter More Computational Types *)

From Coq Require Import Lia.
Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Fact skolem_trans {X Y} (p: X -> Y -> Prop) :
  (forall x, Sigma y, p x y) -> Sigma f, forall x, p x (f x).
Proof.
  intros F.
  exists (fun x => pi1 (F x)). intros x. exact (pi2 (F x)).
Qed.

(*** Injections and Bijections *)


Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.
Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Fact injective_eqdec {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H d x x'.
  destruct (d (f x) (f x')) as [H1|H1].
  - left. apply H, H1.
  - right. contradict H1.  congruence.
Qed.

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.

Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  intros H x x' H1 %(f_equal g). rewrite !H in H1. exact H1.
Qed.

Fact inv_surjective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> surjective g.
Proof.
  intros H x. exists (f x). apply H.
Qed.

Fact inv_injective_inv X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective g -> inv f g.
Proof.
  intros H1 H2 y. apply H2. rewrite H1. reflexivity.
Qed.

Fact inv_surjective_inv X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> surjective f -> inv f g.
Proof.
  intros H1 H2 y.
  specialize (H2 y) as [x H2]. subst y. rewrite H1. reflexivity.
Qed.

Fact inv_agree X Y (f: X -> Y) (g g': Y -> X) :
  surjective f -> inv g f -> inv g' f -> forall y, g y = g' y.
Proof.
  intros H1 H2 H3 y.
  specialize (H1 y) as [x H1]. subst y. rewrite H2, H3. reflexivity.
Qed.

Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (H: inv g f).

Fact injection_refl X :
  injection X X.
Proof.
  exists (fun x => x) (fun x => x). intros x. reflexivity.
Qed.

Fact injection_trans X Y Z :
  injection X Y -> injection Y Z -> injection X Z.
Proof.
  intros [f g H] [f' g' H'].
  exists (fun x => f' (f x)) (fun z => g (g' z)).
  intros x. congruence.
Qed.

Fact injection_transport X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros [f g H].
  eapply injective_eqdec, inv_injective, H.
Qed.

Fact injection_Cantor X :
  ~ injection (X -> bool) X.
Proof.
  intros [f g H].
  pose (h x := negb (g x x)).
  enough (g (f h) (f h) = h (f h)) as H1.
  { revert H1. unfold h at 3. destruct g; easy. }
  rewrite H. reflexivity.
Qed.
    
Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

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

Fact bij_empty X Y :
  (X -> False) -> (Y -> False) -> bijection X Y.
Proof.
  intros f g.
  exists (fun x => match f x with end) (fun y => match g y with end).
  - intros x. exfalso. easy.
  - intros y. exfalso. easy.
Qed.

(* Note the use of 'unshelve eexists' *)

Definition bijection_prod X Y :
  bijection (X * Y) (sig (fun _: X => Y)).
Proof.
  unshelve eexists.
  - intros [x y]. exists x. exact y.
  - intros [x y]. exact (x,y).
  - intros [x y]. reflexivity.
  - intros [x y]. reflexivity.
Qed.

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
Qed.

Definition bij_bij_sig X Y:
  bijection (bijection X Y) (Sigma f g, @inv X Y g f /\ inv f g).
Proof.
  unshelve eexists.
  - intros [f g H1 H2]. exists f, g. exact (conj H1 H2).
  - intros (f&g&H1&H2). exists f g; assumption. 
  - intros [f g H1 H2]. reflexivity.
  - intros (f&g&H1&H2). reflexivity.
Qed.

Goal injection nat bool -> False.
Proof.
  intros [f g H].
  assert (f 0 = f 1 \/ f 0 = f 2 \/ f 1 = f 2) as [H3|[H3|H3]].
  { destruct (f 0), (f 1), (f 2); auto. }
  all: apply (f_equal g) in H3.
  all: rewrite !H in H3.
  all: easy.
Qed.

Fact exercise_bool1 (f: bool -> bool) :
  injective f <-> surjective f.
Proof.
  destruct (f true) eqn:E1, (f false) eqn:E2; split; intros H.
  - exfalso. enough (true = false) by congruence.
    apply H. congruence.
  - exfalso. specialize (H false) as [x H].
    destruct x; congruence.
  - intros [|]; eauto.
  - intros [|] [|]; congruence.
  - intros [|]; eauto.
  - intros [|] [|]; congruence.
  - exfalso.
    enough (true = false) by congruence.
    apply H. congruence.
  - exfalso. specialize (H true) as [x H].
    destruct x; congruence.
Qed.

Fact exercise_bool2 (f: bool -> bool) :
  injective f ->
  (forall x, f x = x) \/ (forall x, f x = negb x).
Proof.
  intros H.
  destruct (f true) eqn:E1.
  - left. intros [|]. exact E1.
    destruct (f false) eqn:E2. 2:easy.
    apply H. congruence.
  - right. intros [|]. exact E1.
    destruct (f false) eqn:E2; cbn. easy.
    apply H. congruence.
Qed.
    
Definition agree {X Y} (f g: X -> Y) := forall x, f x = g x.

Fact exercise_bool3  (f: bool -> bool) :
  injective f ->
  inv f f *  (forall g, inv g f -> agree g f).
Proof.
  intros [H|] %exercise_bool2; split.
  - congruence.
  - congruence.
  - intros x. rewrite !H. destruct x; easy.
  - intros g H1.
    enough (agree g negb) by congruence.
    assert (H2: inv g negb) by congruence.
    intros x. rewrite <-H2. destruct x; easy.
Qed.

(*** Option Types *)

Print option.

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
Qed.

Definition option_eqdec_backwards {X} :
  eqdec (option X) -> eqdec X.
Proof.
  intros H x y.
  specialize (H (Some x) (Some y)) as [H|H].
  - left. congruence.
  - right. congruence.
Qed.

Goal forall X Y, bijection X Y -> bijection (option X) (option Y).
Proof.
  intros X Y [f g H1 H2].
  exists (fun a => match a with Some x => Some (f x) | None => None end)
    (fun b => match b with Some y => Some (g y) | None => None end).
  - hnf. intros [x|]; congruence.
  - hnf. intros [y|]; congruence.
Qed.

Definition lower' X Y (f: option X -> option Y) x z :=
  match f (Some x) with
  | Some y => z = y
  | None => match f None with
           | Some y => z = y
           | None => False
           end
  end.

Definition lower X Y (f: option X -> option Y) f' :=
  forall x, lower' X Y f x (f' x).
  
Fact lower_sig {X Y} f :
  injective f -> sig (lower X Y f).
Proof.
  intros H.
  apply skolem_trans.
  intros x. unfold lower'.
  destruct (f (Some x)) as [y|] eqn:E1.
  - eauto.
  - destruct (f None) as [y|] eqn:E2.
    + eauto.
    + enough (Some x = None) by easy.
      apply H. congruence.
Qed.
  
Fact lem_lower X Y f g f' g'  :
  inv g f -> inv f g ->
  lower X Y f f' -> lower Y X g g' -> inv g' f'.
Proof.
  intros H1 H2 H3 H4 x.
  specialize (H3 x). unfold lower' in H3.
  destruct (f (Some x)) as [y|] eqn:E1.
  - specialize (H4 y). unfold lower' in H4.
    destruct (g (Some y)) as [x'|] eqn:E2; congruence.
  - destruct (f None) as [y|] eqn:E2. 2:easy.
    specialize (H4 y). unfold lower' in H4.
    assert (E3: g (Some y) = None) by congruence.
    rewrite E3 in H4.  
    destruct (g None) as [x'|] eqn:E4; congruence.
Qed.

Theorem bijection_option X Y : 
  bijection (option X) (option Y) -> bijection X Y.
Proof.
  intros [f g H1 H2].
  destruct (lower_sig f) as [f' H3].
  { eapply inv_injective, H1. }
  destruct (lower_sig g) as [g' H4].
  { eapply inv_injective, H2. }
  exists f' g'; eapply lem_lower; eassumption.
Qed.

(*** Numeral Types *)

Fixpoint num n : Type :=
  match n with
  | 0 => False
  | S n' => option (num n')
  end.

Fact num_eqdec n :
  eqdec (num n).
Proof.
  induction n as [|n IH]; cbn.
  - intros [].
  - apply option_eqdec, IH.
Qed.

Fact bijection_eq m n :
  bijection (num m) (num n) -> m = n.
Proof.
  revert m n.
  induction m as [|m IH]; destruct n; intros H.
  - reflexivity.
  - exfalso. apply H. exact None.
  - exfalso. apply H. exact None.
  -  f_equal. apply IH. apply bijection_option. exact H.
Qed.

(*** Vector Types *)

Fixpoint vec X n : Type :=
  match n with
  | 0 => unit
  | S n => X * vec X n
  end.

Compute vec nat 3.
Check (1,(2,(3,tt))) : vec nat 3.

Definition vec_eqdec X n :
  eqdec X -> eqdec (vec X n).
Proof.
  unfold eqdec, dec. intros d.
  induction n as [|n IH]. 
  - intros [] []. auto.
  - intros [x v] [x' v'].
    specialize (d x x'). specialize (IH v v').
    intuition congruence.
Qed.

(** List operations *)

Definition nil {X} : vec X 0 := tt.

Definition cons {X n}
  : X -> vec X n -> vec X (S n)
  := @pair X (vec X n).

Definition hd {X n}
  : vec X (S n) -> X
  := fst.

Arguments hd :simpl never.

Definition tl {X n}
  : vec X (S n) -> vec X n
  := snd.

Fact vec_eta {X n} (v: vec X (S n)) :
  v = cons (hd v) (tl v).
Proof.
  destruct v as [x v]. cbn. reflexivity.
Qed.

(** Enumeration *)

Fixpoint enum k n : vec nat n :=
  match n with
  | 0 => nil
  | S n => cons k (enum (S k) n)
  end.

Eval cbn in enum 1 3.

(** Tuple Types *)

Fixpoint tup (p: nat -> Type) n : Type :=
  match n with
  | 0 => unit
  | S n => p n * tup p n
  end.

Compute tup (fun n => n = n) 3.

Definition tuprec {p: nat -> Type}
  : (forall n, tup p n -> p n) -> forall n, tup p n
  := fun e => fix f n :=
       match n with
       | 0 => tt
       | S n => let t := f n in (e n t, t)
       end.

Definition tupcov {p} e n : p n := fst (tuprec e (S n)).

Check @tupcov.

(** Position element maps *)

Fixpoint sub {X n}
  : vec X (S n) -> nat -> X
  := match n with
     | 0 => fun v k => hd v
     | S n => fun v k => match k with
                     | 0 => hd v
                     | S k => sub (tl v) k
             end
     end.

Fixpoint sub' {X n}
  : vec X n -> num n -> X
  := match n with
     | 0 => fun v a => match a with end
     | S n => fun v a => match a with 
                     | Some a => sub' (tl v) a
                     | None => hd v
                     end
     end.

Fact sub0 X n (v: vec X (S n)) :
  sub v 0 = hd v.
Proof.
  destruct n; reflexivity.
Qed.

Fact sub1 X n (v: vec X (S (S n))) :
  sub v 1 = hd (tl v).
Proof.
  destruct n; reflexivity.
Qed.

Fact sub'0 X n (v: vec X (S n)) :
  sub' v None = hd v.
Proof.
  destruct n; reflexivity.
Qed.

Fact sub'1 X n (v: vec X (S (S n))) :
  sub' v (Some None) = hd (tl v).
Proof.
  destruct n; reflexivity.
Qed.

(** last, snoc, reversion *)

Fixpoint last {X n}
  : vec X (S n) -> X :=
  match n with
  | 0 => hd
  | S n => fun v => last (tl v)
  end.

Compute last (enum 1 5).

Fact sub_last X n (v: vec X (S n)) :
  sub v n = last v.
Proof.
  induction n as [|n IH]. reflexivity.
  cbn. apply IH.
Qed.

Fixpoint snoc {X n}
  : vec X n -> X -> vec X (S n)
  := match n with
     | 0 => fun _ x => cons x nil
     | S n => fun v x => cons (hd v) (snoc (tl v) x)
     end.

Compute snoc (enum 1 5) 6.

Fact last_snoc X n x (v: vec X n) :
  last (snoc v x) = x.
Proof.
  induction n as [|n IH]. reflexivity.
  destruct v as [y v]. change (y,v) with (cons y v).
  cbn. apply IH.
Qed.
  
(** Reversion *)

Fixpoint rev {X n}
  : vec X n -> vec X n 
  := match n with
     | 0 => fun v => v
     | S n => fun v => snoc (rev (tl v)) (hd v)
     end.

Compute rev (enum 0 5).
Compute rev (rev (enum 0 5)).

Fact rev_cons X n (v: vec X n) (x: X) :
  rev (cons x v) = snoc (rev v) x.
Proof.
  reflexivity.
Qed.

Fact rev_snoc_cons X n (v: vec X n) (x y: X) :
  rev (snoc (cons x v) y) = snoc (rev (snoc v y)) x.
Proof.
  reflexivity.
Qed.
  
Fact rev_snoc X x n (v: vec X n) :
  rev (snoc v x) = cons x (rev v).
Proof.
  induction n as [|n IH] in v|-*.
  - destruct v. reflexivity.
  - destruct v as [y v]. change (y,v) with (cons y v).
    rewrite rev_snoc_cons. rewrite IH. reflexivity.
Qed.

Fact rev_rev X n (v: vec X n) :
  rev (rev v) = v.
Proof.
  induction n as [|n IH]. reflexivity.
  destruct v as [x v]. change (x,v) with (cons x v).
  rewrite rev_cons. rewrite rev_snoc. f_equal. apply IH.
Qed.

(** Concatenation *)

Fixpoint con {X m n}
  : vec X m -> vec X n -> vec X (m + n)
  := match m with
     | 0 => fun v w => w
     | S m => fun v w => cons (hd v) (con (tl v) w)
     end.
  
Fail Check
  forall X m n k (u: vec X m) (v: vec X n) (w: vec X k),
    con (con u v) w = con u (con v w).

Fixpoint cast {X m n k}
  : vec X ((m + n) + k) -> vec X (m + (n + k))
  := match m with
     | 0 => fun v => v
     | S m => fun v => cons (hd v) (cast (tl v))
     end.

Fact con_assoc X m n k (u: vec X m) (v: vec X n) (w: vec X k) :
  cast (con (con u v) w) = con u (con v w).
Proof.
  revert m u.
  induction m as [|m IH]; intros u.
  - simpl cast. simpl con. reflexivity.
  - simpl con. simpl cast. f_equal. apply IH.
Qed.

Module GroundExample.
  Definition u := enum 0 3.
  Definition v := enum 3 3.
  Definition w := enum 6 3.
  Goal con (con u v) w = con u (con v w).
  Proof.
    cbn. reflexivity.
  Qed.
  Eval cbn in cast (con (con u v) w).
End GroundExample.

Goal forall X m n k,
    vec X ((m + n) + k) = vec X (m + (n + k)).
Proof.
  intros *. f_equal. lia.
Qed.
