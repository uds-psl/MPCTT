From Coq Require Import Lia.
From Coq Require ConstructiveEpsilon Cantor.
(** We use an EWO for nat and Cantor pairing from the library *)

Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

(*
Notation "X <-> Y" := (prod (X -> Y) (Y -> X)) 
(at level 95, no associativity) : type_scope.
(* symmetry tactic doesn't work for prod *)
*)

Definition dec (X: Type) : Type := X + (X -> False).
Notation Dec p := (forall x, dec (p x)).
Notation eqdec X := (forall x y: X, dec (x = y)).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
Fact sig_ex {X} {p: X -> Prop} :
  sig p -> ex p.
Proof.
  intros [? ?]; eauto.
Qed.

Inductive trunc (X: Type) : Prop := Trunc (_ : X).
Notation "□ X" := (trunc X) (at level 75, right associativity) : type_scope.

Definition surjective {X Y} (f: X -> Y) := forall y, exists x, f x = y.
Notation Rel X Y :=  (X -> Y -> Prop).
Fact skolem_trans {X Y} (R: Rel X Y) :
  (forall x, Sigma y, R x y) -> Sigma f, forall x, R x (f x).
Proof.
  intros F. exists (fun x => pi1 (F x)). intros x. exact (pi2 (F x)).
Qed.

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.

Definition XM := forall P, P \/ ~ P.
Definition FE : Prop :=
  forall X (p: X -> Type) (f g: forall x, p x), (forall x, f x = g x) -> f = g.

Implicit Type n k : nat.
Implicit Type b: bool.

Fact bool_eqdec :
  eqdec bool.
Proof.
  intros [|] [|]; unfold dec; intuition easy.
Qed.
Fact nat_eqdec : eqdec nat.
Proof.
  intros x y. unfold dec.
  destruct ((x - y) + (y - x)) eqn:?; intuition lia.
Qed.

Fact ewo_nat (p: nat -> Prop) :
  Dec p -> ex p -> sig p.
Proof.
  (* See file ewo.v for a proof *)
  intros d H.
  apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat in H.
  - destruct H; eauto. 
  - intros n. destruct (d n); auto.
Qed.

(** Arithmetic Pairing *)
Definition arp n k := (Cantor.to_nat (n,k)).
Definition arp1 n := fst (Cantor.of_nat n).
Definition arp2 n := snd (Cantor.of_nat n).
Fact arp1_eq n k :
  arp1 (arp n k) = n.
Proof.
  unfold arp, arp1. rewrite Cantor.cancel_of_to. easy.
Qed.
Fact arp2_eq n k :
  arp2 (arp n k) = k.
Proof.
  unfold arp, arp2. rewrite Cantor.cancel_of_to. easy.
Qed.
Fact arp_eq n :
  arp (arp1 n) (arp2 n) = n.
Proof.
  unfold arp, arp1, arp2.
  destruct (Cantor.of_nat n) as [n1 n2] eqn:E.
  cbn [fst snd].
  assert (E1:=Cantor.cancel_to_of n).
  congruence.
Qed.

(** Least Witnesses *)

Definition safe p n := forall k, k < n -> ~p k.
Definition least p n := p n /\ safe p n.
Notation unique p := (forall x x', p x -> p x' -> x = x').

Fact least_unique p : unique (least p).
Proof.
  intros n n' [H1 H2] [H1' H2'].
  enough (~(n < n') /\ ~(n' < n)) by lia.
  split; intros H.
  - eapply H2'; eassumption.
  - eapply H2; eassumption.
Qed.

Fact safe_S p n :
  safe p n -> ~p n -> safe p (S n).
Proof.
  intros H1 H2 k H3. unfold safe in *.
  assert (k < n \/ k = n) as [H|H] by lia.
  - eauto.
  - congruence.
Qed.

Section LWO.
Variable p : nat -> Prop.
Variable p_dec : Dec p.

Definition lwo :
  forall n, (Sigma k, k < n /\ least p k) + safe p n.
Proof.
  induction n as [|n IH].
  - right. easy. 
  - destruct IH as [(k&H1&H2)|H1].
    + left. exists k. split. lia. exact H2.
    + destruct (p_dec n).
      * left. exists n. split. lia. easy.
      * right. apply safe_S; assumption.
Qed.

Definition least_ex :
  ex p -> ex (least p).
Proof.
  intros [n H].
  destruct (lwo (S n)) as [(k&H1&H2)|H1].
  - exists k. exact H2.
  - exfalso. apply (H1 n). lia. exact H.
Qed.

Definition safe_dec n :
  dec (safe p n).
Proof.
  destruct (lwo n) as [(k&H1&H2)|H1].
  - right. intros H. apply (H k). exact H1. apply H2.
  - left. exact H1.
Qed.

Definition least_dec :
  Dec (least p).
Proof.
  intros n. unfold least.
  destruct (p_dec n) as [H|H].
  2:{ right. tauto. }
  destruct (safe_dec n) as [H1|H1].
  - left. easy.
  - right. tauto.
Qed.

Fact least_ewo :
  ex p -> sig (least p).
Proof.
  intros H. apply ewo_nat.
  exact least_dec.
  apply least_ex, H.
Qed.

End LWO.

(*** Tests and Basic Predicates *)

Notation "p ≡ q" := (forall x, p x <-> q x) (at level 70).
Definition compl {X} : (X -> Prop) -> (X -> Prop) := fun p x => ~ p x.
Notation "'co' p" := (compl p)
                       (at level 69, right associativity) : type_scope.

Notation test  := (nat -> bool).
Notation test2 := (nat -> nat -> bool).
Definition K : test -> Prop := fun f => exists n, f n = true.
Definition dom (f: test2) := (fun n => K (f n)).
Definition basic (p: nat -> Prop) := exists f, p ≡ dom f.

Fact dom_basic f :
  basic (dom f).
Proof.
  exists f. easy.
Qed.

Fact dec_basic (p: nat -> Prop) :
  Dec p -> basic p.
Proof.
  intros d.
  exists (fun n k => if d n then true else false).
  intros n. unfold dom.
  destruct (d n) as [H|H]; split.
  - intros H1. exists 0. easy.
  - easy.
  - easy.
  - intros [_ H1]. easy.
Qed.

Fact K_sig f :
  K f -> Sigma n, f n = true.
Proof.
  intros [n H]%(ewo_nat (fun n => f n = true)).
  - eauto.
  - intros n. apply bool_eqdec.
Qed.

Fact dec_test (P: Prop) :
  dec P -> Sigma f, P <-> K f.
Proof.
  intros d.
  exists (fun n => if d then true else false).
  destruct d as [H|H].
  - split. 2:easy. intros _. exists 0. easy.
  - split. 1:easy. intros [_ H1]. easy.
Qed.

Fact Dec_test (p: nat -> Prop) :
  Dec p -> Sigma f, ex p <-> K f.
Proof.
  intros d.
  exists (fun n => if d n then true else false).
  split;
    intros [n H]; exists n; destruct (d n) as [H1|H1]; easy.
Qed.

Fact coK f :
  ~ K f <-> forall n, f n = false.
Proof.
  split.
  - intros H n. destruct (f n) eqn:E. 2:easy.
    contradict H. exists n; easy.
  - intros H [n H1]. congruence.
Qed.

(*** Axiom UT *)

Definition UT := Sigma U: nat -> test2, forall f: test2, exists c, dom f ≡ dom (U c).

Fact UT_codom_not_basic :
  UT -> Sigma f, ~basic (co (dom f)).
Proof.
  intros [U HU].
  exists (fun n => U n n). intros [f Hf]. hnf in Hf.
  specialize (HU f) as [c HU].
  specialize (HU c).
  specialize (Hf c).
  unfold dom, compl in *. tauto.
Qed.

Fact UT_basic_co_not_basic :
  UT -> Sigma p, basic p /\ ~basic (co p).
Proof.
  intros [f H] %UT_codom_not_basic.
  exists (dom f). split. 2:exact H.
  apply dom_basic.
Qed.

Fact dec_co_dec X (p: X -> Prop) :
  Dec p -> Dec (co p).
Proof.
  intros d. unfold dec, compl in *. firstorder.
Qed.

Fact UT_basic_undec :
  UT -> Sigma p, basic p /\ ~Dec p.
Proof.
  intros (p&H1&H2) %UT_basic_co_not_basic.
  exists p.  split. exact H1.
  contradict H2. apply dec_basic.
  apply dec_co_dec, H2.
Qed.

Fact UT_undec_coK :
  UT -> ~ Dec (co K).
Proof.
  intros [U F] d.
  pose (f n := if d (U n n) then fun _:nat => true else fun _ => false).
  specialize (F f) as [c Hc].
  specialize (Hc c). unfold dom, compl, f in *.
   destruct (d (U c c)) as [H|H].
  - apply H, Hc. exists 0. easy.
  - contradict H. intros [k H] % Hc. easy.
Qed.

Fact UT_undec_K :
  UT -> ~ Dec K.
Proof.
  intros H d.
  apply (UT_undec_coK H).
  apply dec_co_dec, d.
Qed.

Fact UT_undec_in_dom n :
  UT -> ~ Dec (fun f => dom f n).
Proof.
  intros ut d.
  apply (UT_undec_K ut).
  intros f. exact (d (fun _ => f)).
Qed.

Fact UT_undec_ex_dom :
  UT -> ~ Dec (fun f => ex (dom f)).
Proof.
  intros ut d.
  apply (UT_undec_K ut).
  intros f.
  destruct (d (fun _ => f)) as [H|H].
  - left. destruct H as [n H]. exact H.
  - right. contradict H. exists 0.  exact H.
Qed.

Fact UT_disjoint :
  UT -> exists f, forall g,
      (forall n, dom f n -> dom g n -> False) ->
      exists n, ~ K (f n) /\ ~ K (g n).
Proof.
  intros [U HU]. exists (fun n => U n n). intros g H.
  specialize (HU g) as [c HU].
  exists c. specialize (HU c). specialize (H c).
  unfold dom in *.
  tauto.
Qed.

Fact UT_UT2 :
  UT <=> Sigma g, forall f, exists c, dom f  ≡ dom (fun n => g (arp c n)).
Proof.
  split.
  - intros [U H].
    exists (fun n => U (arp1 n) (arp2 n)).
    intros f. specialize (H f) as [c Hc].
    exists c. intros n. unfold dom in *.
    rewrite arp1_eq, arp2_eq. apply Hc.
  - intros [g H].
    exists (fun c n => g (arp c n)).
    intros f. specialize (H f) as [c Hc].
    exists c. intros n. unfold dom in *. apply Hc.
Qed.

(*** Diophantine Expressions *)

Inductive exp :=
| Var: nat -> exp
| Zero
| One
| Add: exp -> exp -> exp
| Sub: exp -> exp -> exp
| Mul: exp -> exp -> exp.
  
Fixpoint get n k : nat :=
  match n with
  | 0 => 0
  | S n => match k with
          | 0 => arp1 n
          | S k => get (arp2 n) k
          end
  end.
  
Definition cons n k := S (arp n k).

Compute get 0 7.
Compute get (cons 5 (cons 6 (cons 7 0))) 2.
Compute get (cons 5 (cons 6 (cons 7 0))) 3.

Implicit Type e : exp.

Fixpoint eva n e : nat :=
  match e with
  | Var k => get n k
  | Zero => 0
  | One => 1         
  | Add e1 e2 => eva n e1 + eva n e2
  | Sub e1 e2 => eva n e1 - eva n e2
  | Mul e1 e2 => eva n e1 * eva n e2
  end.

Definition pred e n := exists k, eva (cons n k) e = 0.

Definition tau e : nat -> nat -> bool :=
  fun n k => if eva (cons n k) e then true else false.

Fact pred_tau e :
  pred e ≡ dom (tau e).
Proof.
  unfold tau.
  intros n; split; intros [k H]; exists k.
  - rewrite H. easy.
  - destruct eva; easy.
Qed.

Fact exp_basic e :
  basic (pred e).
Proof.
  exists (tau e). apply pred_tau.
Qed.

Fact exp_test :
  forall e, exists f, dom f ≡ pred e.
Proof.
  intros e. exists (tau e). intros n. symmetry. apply pred_tau.
Qed.

Fact enum_exp :
  Sigma delta, forall e, exists n, delta n = e.
Admitted.

(*** Axiom CT *)

Definition CT := forall f, exists e, dom f ≡ pred e.

Fact CT_UT:
  CT -> UT.
Proof.
  intros H.
  destruct enum_exp as [delta H_delta].
  exists (fun c => tau (delta c)). intros f.
  specialize (H f) as [e He].
  specialize (H_delta e) as [c Hc].
  exists c. intros n. rewrite Hc, He. apply pred_tau. 
Qed.

Fact CT_exp_not_basic :
  CT -> exists e, ~ basic (co (pred e)).
Proof.
  intros ct.
  destruct (UT_codom_not_basic (CT_UT ct)) as [f Hf].
  specialize (ct f) as [e He].
  exists e.  contradict Hf. destruct Hf as [g Hg].
  exists g. intros n. specialize (He n). specialize (Hg n).
  unfold compl in *. tauto.
Qed.

Fact CT_exp_undec :
  CT -> exists e, ~Dec (pred e).
Proof.
  intros [e H] %CT_exp_not_basic.
  exists e. contradict H.
  apply dec_basic, dec_co_dec, H.
Qed.

Fact CT_exp_undec' :
  CT -> ~ forall e n, dec (pred e n).
Proof.
  intros [e He] %CT_exp_undec. contradict He. apply He.
Qed.

Definition diophantine p := exists e, p ≡ pred e.

Fact CT_equiv p :
  CT -> basic p <-> diophantine p.
Proof.
  intros H. split.
  - intros [f Hf]. destruct (H f) as [e He].
    exists e. intros n. rewrite Hf. apply He.    
  - intros [e He]. exists (tau e).
    intros n. rewrite He, <-pred_tau. easy.
Qed.

Lemma eva_cons :
  forall e, Sigma e', forall k, eva (cons 0 k) e = eva k e'.
Admitted.

Fact CT_eva_zero :
  CT -> forall f: test, exists e, K f <-> exists n, eva n e = 0.
Proof.
  intros H f.
  specialize (H (fun _ => f)) as [e He]. unfold dom in He.
  destruct (eva_cons e) as [e' He'].
  exists e'. rewrite (He 0). split; intros [n Hn]; exists n; congruence.
Qed.

(* Challenges *)
Goal CT -> ~ Dec (fun e => ex (pred e)).
Abort.
Goal CT -> ~ Dec (fun e => exists n, eva n e = 0).
Abort.

Definition ACT A (tau: A -> test2) (delta: nat -> A) : Prop := 
  (forall f, exists a, dom f ≡ dom (tau a)) /\ (forall a, exists n, delta n = a).
 
 
Fact ACT_exp :
  CT -> sig (ACT exp tau).
Proof.
  intros H.
  destruct enum_exp as [delta H_delta].
  exists delta. split.
  - intros f. destruct (H f) as [e He].
    exists e. intros n. rewrite He. apply pred_tau.
  - exact H_delta.
Qed.

Fact ACT_UT A tau delta :
  ACT A tau delta -> UT.
Proof.
  intros [H1 H2].
  exists (fun n => tau (delta n)). intros f.
  specialize (H1 f) as [a Hf].
  specialize (H2 a) as [c <-].
  eauto.
Qed.

Fact ACT_basic A tau delta :
  ACT A tau delta -> forall p, basic p <-> exists a, p ≡ dom (tau a).
Proof.
  intros [H1 _] p. split.
  - intros [f Hf].
    specialize (H1 f) as [a Ha].
    exists a. intros n.
    specialize (Hf n). specialize (Ha n). tauto.
  - intros [a Ha]. exists (tau a). exact Ha.
Qed.

(*** Recusant Relations *)

Definition functional {X Y} (R: Rel X Y) :=
  forall x y y', R x y -> R x y' -> y = y'.
Definition total {X Y} (R: Rel X Y) :=
  forall x, exists y, R x y.
Definition Dom {X Y} (R: Rel X Y) := fun x => ex (R x).

(** Characteristic relation *)

Definition rho {X} (p: X -> Prop) : X -> bool -> Prop :=
  fun x b => if b then p x else ~ p x.

Fact rho_functional {X} (p: X -> Prop) :
  functional (rho p).
Proof.
  intros x b b'. unfold rho. destruct b, b'; easy.
Qed.

Fact rho_total {X} (p: X -> Prop) :
  XM -> total (rho p).
Proof.
  intros xm n. unfold rho.
  destruct (xm (p n)) as [H|H].
  - exists true. easy.
  - exists false. easy.
Qed.

Fact rho_dec_skolem {X} (p: X -> Prop) :
  Dec p <=> Sigma f, forall x, rho p x (f x).
Proof.
  split.
  - intros d.
    exists (fun x => if d x then true else false).
    intros x. destruct (d x); easy.
  - intros [f Hf] x. specialize (Hf x). revert Hf.
    unfold rho, dec. destruct (f x); auto.
Qed.

Fact UT_XM_recusant_rel :
  UT -> XM -> Sigma R: nat -> bool -> Prop,
      functional R /\ total R /\
      ~ exists f, forall n, R n (f n).
Proof.
  intros (p&_&Hp)%UT_basic_undec xm.
  exists (rho p). repeat split.
  - apply rho_functional.
  - apply rho_total, xm.
  - intros [f Hf]. apply Hp.
    apply rho_dec_skolem. eauto.
Qed.

(*** UT_Sigma *)

Definition UT_Sigma :=
  Sigma U: nat -> test2, forall f, Sigma c, dom f ≡ dom (U c).

Fact UT_Sigma_UT :
  UT_Sigma -> UT.
Proof.
  intros [U F]. exists U. intros f.
  destruct (F f) as [c Hc]. eauto.
Qed.

Definition TE := forall f g : test, (forall n, f n = g n) -> f = g.

Fact UT_Sigma_TE_dec_coK :
  UT_Sigma -> TE -> Dec (co K).
Proof.
  intros [U F] te.
  pose (gamma (f:test) := pi1 (F (fun _ => f))).
  assert (Hgamma: forall f, K f <-> K (U (gamma f) 0)).
  { intros f. unfold gamma. destruct F as [c Hc]. apply Hc. }
  intros f. unfold compl.
  destruct (nat_eqdec (gamma f) (gamma (fun _ => false))) as [H1|H1].
  - left. intros H2. apply Hgamma in H2.
    rewrite H1 in H2. apply Hgamma in H2 as [n H2]. easy.
  - right. contradict H1.
    f_equal. apply te.
    apply coK, H1.
Qed.

Fact UT_Sigma_TE_False :
  UT_Sigma -> TE -> False.
Proof.
  intros H1 H2. apply UT_undec_coK.
  - apply UT_Sigma_UT, H1.
  - apply UT_Sigma_TE_dec_coK; easy.
Qed.

(*** Post Hierarchy *)

Definition red {X Y} (p: X -> Prop) (q: Y -> Prop) (f: X -> Y) :=
  forall x, p x <-> q (f x).

Notation "p ⪯ q" := (sig (red p q)) (at level 70).
Notation "p ≈ q" := (((p ⪯ q) * (q ⪯ p)) %type) (at level 70).
Notation "p ≡ q" := (forall x, p x <-> q x) (at level 70).


Fact red_refl X (p: X -> Prop) :
  p ⪯ p.
Proof.
  exists (fun x => x). easy.
Qed.

Fact red_trans X Y Z (p: X -> Prop) (q: Y -> Prop) (r: Z -> Prop)  :
  p ⪯ q -> q ⪯ r -> p ⪯ r.
Proof.
  intros [f Hf] [g Hg]. exists (fun x => g (f x)).
  unfold red in *. firstorder.
Qed.

Fact red_co X Y (p: X -> Prop) (q: Y -> Prop) :
  p ⪯ q -> co p ⪯ co q.
Proof.
  intros [f Hf]. exists f. unfold red in *. firstorder.
Qed.

Fact red_equiv X (p q: X -> Prop) :
  p ≡ q -> p ⪯ q.
Proof.
  intros H. exists (fun x => x). exact H.
Qed.

Fact red_Dec X Y (p: X -> Prop) (q: Y -> Prop) :
  p ⪯ q -> Dec q -> Dec p.
Proof.
  intros [f H] d x.
  specialize (H x).
  specialize (d (f x)).
  unfold dec in *; tauto.
Qed.

Fact red_skolem X Y (p: X -> Prop) (q: Y -> Prop) :
  (forall x, Sigma y, p x <-> q y) -> p ⪯ q.
Proof.
  apply skolem_trans.
Qed.

Fact ired_refl X (p: X -> Prop) :
  p ≈ p.
Proof.
  split; apply red_refl.
Qed.

Fact ired_sym X Y (p: X -> Prop) (q: Y -> Prop) :
  p ≈ q -> q ≈ p.
Proof.
  tauto.
 Qed.

Fact ired_trans X Y Z (p: X -> Prop) (q: Y -> Prop) (r: Z -> Prop)  :
  p ≈ q -> q ≈ r -> p ≈ r.
Proof.
  intros [? ?] [? ?]. split; eapply red_trans; eassumption.
Qed.

Fact ired_co X Y (p: X -> Prop) (q: Y -> Prop) :
  p ≈ q -> co p ≈ co q.
Proof.
  intros [? ?]. split; apply red_co; assumption.
Qed.

Fact ired_equiv X (p q: X -> Prop) :
  p ≡ q -> p ≈ q.
Proof.
  intros H. split; apply red_equiv; firstorder.
Qed.

Definition stable {X} (p: X -> Prop) := forall x, ~ ~ p x -> p x.

Fact stable_equiv X (p: X -> Prop) :
  stable p <-> co co p ≡ p.
Proof.
  unfold stable. firstorder easy.
Qed.

Fact stable_co X (p: X -> Prop) :
  stable (co p).
Proof.
  unfold stable. firstorder easy.
Qed.

Fact Dec_stable X (p: X -> Prop) :
  Dec p -> stable p.
Proof.
  unfold dec, stable. firstorder easy.
Qed.

Fact red_stable X Y (p: X -> Prop) (q: Y -> Prop) :
  p ⪯ q -> stable q -> stable p.
Proof.
  unfold stable. firstorder easy.
Qed.

Fact red_stable_right_co_shift X Y (p: X -> Prop) (q: Y -> Prop) :
  stable p -> co p  ⪯ q -> p ⪯ co q.
Proof.
  unfold stable. firstorder easy.
Qed.

Fact red_stable_left_co_shift X Y (p: X -> Prop) (q: Y -> Prop) :
  stable q -> p ⪯ co q -> co p  ⪯ q.
Proof.
  unfold stable. firstorder easy.
Qed.

(* Constancy of tests *)

Notation ct_false := (fun g => forall n, g n = false).
Notation ct_true  := (fun g => forall n, g n = true).
Notation ct       := (fun g => exists b, forall n, g n = b).

Fact ct_false_coK_equiv :
  ct_false ≡ co K.
Proof.
  intros g; cbn. split.
  - intros H [n H1]. congruence.
  - unfold compl. intros H n. destruct (g n) eqn:E. 2:easy.
    contradict H. exists n. easy.
Qed.

Fact ired_ct_false_coK :
  ct_false ≈ co K.
Proof.
  apply ired_equiv, ct_false_coK_equiv.
Qed.

Fact ired_ct_coK :
  ct ≈ co K.
Proof.
  eapply ired_trans. 2:exact ired_ct_false_coK.
  split; apply red_skolem; intros f.
  - exists (if f 0 then fun n =>negb (f n) else f).
    destruct (f 0) eqn:E; split.
    + intros [[|] H] n; rewrite H. easy. congruence.
    + intros H. exists true. intros n. specialize (H n). destruct (f n); easy.
    + intros [[|] H] n; congruence.
    + eauto.
  - exists (if f 0 then fun n => if n then true else false else f).
    destruct (f 0) eqn:E; split.
    + congruence.
    + intros [[|] H] n. 
    * specialize (H 1). easy.
    * specialize (H 0). easy.
    + intros H. exists false. easy.
    + intros [[|] H] n; congruence. 
Qed.

Fact ired_K_dom_membership n :
  (fun f => dom f n) ≈ K.
Proof.
  split; apply red_skolem; intros f.
  - exists (f n). easy.
  - exists (fun _ => f). easy.
Qed.

Fact ired_K_dom_satisfiability :
  (fun f => ex (dom f)) ≈ K.
Proof.
  split; apply red_skolem; intros f.
  - exists (fun n => f (arp1 n) (arp2 n)). split.
    + intros (n&k&H). exists (arp n k). rewrite arp1_eq, arp2_eq. exact H.
    + intros [n H]. unfold dom, K. eauto.
  - exists (fun n k => f (arp n k)). split.
    + intros [n H]. exists (arp1 n), (arp2 n). rewrite arp_eq. exact H.
    + intros (n&k&H). unfold K. eauto.
Qed.

Module General_Tests.
  (** Great demo of the expressiveness of dependent types *) 

  Fixpoint test n : Type :=
    match n with
    | 0 => bool
    | S n => nat -> test n
    end.
  
  Fixpoint sat {n} : test n -> Prop :=
    match n with
    | 0 => fun f => (f = true)
    | S n => fun f => exists k, @sat n (f k)
    end.

  Eval cbn in @sat 2.
  
  Set Printing Implicit.
  
  Fact ired_sat_SS n :
    @sat (S (S n)) ≈ @sat (S n).
  Proof.
    split; apply red_skolem; intros f; cbn.
    - exists (fun n => f (arp1 n) (arp2 n)). split.
      + intros (k1&k2&H). exists (arp k1 k2). rewrite arp1_eq, arp2_eq. exact H.
      + intros [k H]. eauto. 
    - exists (fun n k => f (arp n k)). split.
      + intros [k H]. exists (arp1 k), (arp2 k). rewrite arp_eq. exact H.
      + intros (k1&k2&H). eauto.
  Qed.
  
  Fact ired_sat_K n :
    @sat (S n) ≈ K.
  Proof.
    induction n as [|n IH].
    - apply ired_refl.
    - eapply ired_trans. 2:exact IH.
      apply ired_sat_SS.
  Qed.
End General_Tests.

(*** Decidable Predicates *)

Definition D : bool -> Prop := fun b => b = true.

Fact D_Dec :
  Dec D.
Proof.
  intros n. apply bool_eqdec.
Qed.

Fact D_stable :
  stable D.
Proof.
  apply Dec_stable, D_Dec.
Qed.

Fact Dec_coDec  X (p: X -> Prop) :
  Dec p -> Dec (co p).
Proof.
  intros d x. specialize (d x).
  unfold dec, compl in *; tauto.
Qed.

Fact red_D_Dec X (p: X -> Prop) :
  p ⪯ D <=> Dec p.
Proof.
  split.
  - intros [f Hf] x. specialize (Hf x).
    unfold dec, D in *. destruct (f x); intuition easy.
  - intros H. apply red_skolem; intros x.
    specialize (H  x) as [H|H]; unfold D.
    + exists true. easy.
    + exists false. easy.
Qed.

Fact red_D_co {X} (p: X -> Prop) :
  p ⪯ D -> co p ⪯ D.
Proof.
  intros H.
  apply red_D_Dec, Dec_coDec, red_D_Dec, H.
Qed.

Fact ired_beq_co :
  D ≈ co D.
Proof.
  assert (H: co D ⪯ D) by apply red_D_co, red_refl.
  split. 2:exact H.
  eapply red_stable_right_co_shift. exact D_stable. exact H.
Qed.

(*** Semidecidable Predicates *)

Fact red_dom_K f :
  dom f ⪯ K.
Proof.
  exists f. hnf. intros n. unfold dom. easy.
Qed.

Fact red_D_K :
  D ⪯ K.
Proof.
  apply red_skolem; intros b.
  exists (fun _ => b). unfold D, K.
  split.
  - intros ->. exists 0; easy.
  - intros [_ H]; easy.
Qed.

Fact red_D_coK :
  D ⪯ co K.
Proof.
  apply red_trans with (q:= co co D).
  - apply red_equiv. symmetry. revert x.
    apply stable_equiv, D_stable.
  - apply red_co.
    apply red_trans with (q:= D). 2:exact red_D_K.
    apply red_D_co, red_refl.
Qed.

Fact red_K_D_coK_K :
  K ⪯ D -> co K ⪯ K.
Proof.
  intros H.
  eapply red_trans. 2:exact red_D_K. apply red_D_co, H.
Qed.

Definition sdec {X} (p: X -> Prop) := (p ⪯ K).

Fact basic_sdec p :
  basic p <-> □ sdec p.
Proof.
  split.
  - intros [f H]. constructor. exists f. exact H.
  - intros [[f H]]. exists f. exact H.
Qed.

Fact not_basic_not_sdec p :
  ~ basic p <-> ~ sdec p.
Proof.
  rewrite basic_sdec.
  split; intros H. 
  - contradict H. constructor. exact H.
  - intros [H1]. easy.
Qed.

Fact red_sdec {X Y} (p: X -> Prop) (q: Y -> Prop) :
  p ⪯ q -> sdec q -> sdec p.
Proof.
  intros H H1.
  apply red_trans with (q:= q); easy.
Qed.

Fact dec_sdec  {X} (p: X -> Prop) :
  Dec p -> sdec p.
Proof.
  intros H.
  apply red_trans with (q:= D). 2:exact red_D_K.
  apply red_D_Dec, H.
Qed.

Fact dec_cosdec  {X} (p: X -> Prop) :
  Dec p -> sdec (co p).
Proof.
  intros H.
  apply red_trans with (q:= D). 2:exact red_D_K.
  apply red_D_Dec, dec_co_dec, H.
Qed.

Fact dom_sdec f :
  sdec (dom f).
Proof.
  exists f. easy.
Qed.

Fact UT_unsdec_coK :
  UT -> ~ sdec (co K).
Proof.
  intros [f H] %UT_codom_not_basic.
  contradict H. apply basic_sdec. constructor.
  apply red_trans with (q:= co K). 2:exact H.
  apply red_co, dom_sdec.
Qed.

(*
Fact UT_undec_K :
  UT -> ~ Dec K.
Proof.
  intros H H1 %red_D_Dec.
  apply (UT_unsdec_coK H).
  apply red_K_D_coK_K, H1.
Qed.
*)

Fact NT_ct_unsdec :
  UT -> ~sdec ct.
Proof.
  intros H H1. apply (UT_unsdec_coK H).
  eapply red_sdec. 2:exact H1. apply ired_ct_coK.
Qed.

(*** Semidecidable predicates continued *)

Fact sdec_arith_projection {X} (p: X * nat -> Prop) :
  sdec p -> sdec (fun x => exists n, p(x,n)).
Proof.
  intros [f Hf]. hnf in Hf.
  pose (g x n := if f (x, arp1 n) (arp2 n) then true else false).
  exists g. hnf. intros x. split.
  - intros [n Hn]. apply Hf in Hn as [k Hk].
    exists (arp n k). unfold g. rewrite arp1_eq, arp2_eq, Hk. easy.
  - intros [k Hk]. exists (arp1 k). apply Hf. exists (arp2 k).
    unfold g in Hk. destruct f; easy.
Qed.

Corollary sdec_arith_projection2 {X} (p: X * nat * nat -> Prop) :
  sdec p -> sdec (fun x => exists n k, p (x,n,k)).
Proof.
  intros H % sdec_arith_projection %sdec_arith_projection.
  exact H.
Qed.

Definition ewo_nat_sdec (p: nat -> Prop) :
  sdec p -> ex p -> sig p.
Proof.
  intros [f H] H1.
  pose (q n := f (arp1 n) (arp2 n) = true).
  assert (sig q) as [n H2].
  - apply ewo_nat.
    + intros n. apply bool_eqdec.
    + destruct H1 as [n H1].
      apply H in H1 as [k H1].
      exists (arp n k). unfold q.
      rewrite arp1_eq, arp2_eq. exact H1.
  - hnf in H2.  exists (arp1 n). apply H. exists (arp2 n). exact H2.
Qed.

Fact sdec_eqdec X :
  eqdec X <=> Sigma f, forall x y: X, x = y <-> K (f x y).
Proof.
  split.
  - intros d.
    exists (fun x y _ => if d x y then true else false).
    intros x y. split.
    + intros <-. exists 0. destruct (d x x); easy.
    + intros [_ H].  destruct (d x y); easy.
  - intros [f H] x y.
    assert (Sigma k, f x x k = true) as [k E].
    { apply ewo_nat.
      - intros n. apply bool_eqdec.
      - apply H. easy. }
    destruct (f x y k) eqn:E1.
    + left. apply H. exists k. exact E1.
    + right. intros <-. congruence.
Qed.

(** Exercises *)

Fact sdec_arith_projection' {X} (p: X -> nat -> Prop) :
  (forall x n, dec (p x n)) -> sdec (fun x => exists n, p x n).
Proof.
  intros d.
  assert (F:= sdec_arith_projection (fun a => p (fst a) (snd a))).
  destruct F as [f Hf].
  - apply dec_sdec. intros [x n]. cbn. apply d.
  - exists f.  exact Hf.
Qed.

(*** Markov's Principle *)

Definition MP := stable K.

Fact MP_eq :
  MP = forall f, ~ ~ K f -> K f.
Proof.
  reflexivity.
Qed.

Fact MP_equiv :
  MP <-> co co K ≡ K.
Proof.
  apply stable_equiv.
Qed.

Fact MP_coK X (p: X -> Prop) :
  MP -> p ⪯ co K -> co p ⪯ K.
Proof.
  intros mp H%red_co.
  eapply red_trans. exact H.
  apply red_equiv, MP_equiv, mp.
Qed.

Fact test_disjunction :
  forall f g, Sigma h, K h <=> K f + K g.
Proof.
  intros f g.
  exists (fun n => if f n then f n else g n). split.
  - intros [n H]%K_sig.
    destruct (f n) eqn:E; unfold K; eauto.
  - intros [[n H]|[n H]]; exists n.
    + rewrite H. easy.
    + destruct (f n); easy.
Qed.

Definition MP_test_partition :
  MP <=> forall f g, (~K f <-> K g) -> K f + K g.
Proof.
  split.
  - intros H f g H1.
    destruct (test_disjunction f g) as [h Hh].
    apply Hh. apply H. intros H2.
    enough (~K f /\ ~ ~K f) by easy.
    split; contradict H2; apply Hh; tauto.
  - intros H f H1.
    specialize (H f (fun _ => false)) as [H|H].
    + split. tauto. intros [n H]. easy.
    + easy.
    + destruct H as [n H]. easy.
Qed.


Fact MP_bitest :
  MP <=> forall P f g, (P <-> K f) -> (~P <-> K g) -> dec P.
Proof.
  rewrite MP_test_partition. split; unfold dec.
  - intros H P f g H1 H2. specialize (H f g). tauto.
  - intros H f g H1. specialize (H (K f) f g). tauto.
Qed.


Fact MP_bisdec_dec {X} {p: X -> Prop} :
  MP -> sdec p -> sdec (co p) -> Dec p.
Proof.
  intros mp [f Hf] [g Hg] x.
  eapply MP_bitest. exact mp. apply Hf. apply Hg.
Qed.

(* Exercises *)

Fact MP_sdec_dec_iff X (p: X -> Prop) :
  MP -> Dec p <=> sdec p * sdec (co p).
Proof.
  intros mp. split.
  - intros d. split.
    + apply dec_sdec, d.
    + apply dec_cosdec, d.
  - intros [H1 H2]. apply MP_bisdec_dec; easy.
Qed.

Fact MP_dec_K_sdec_coK :
  MP -> Dec K <=> sdec (co K).
Proof.
  intros mp. split.
  - apply dec_cosdec.
  - intros H.  apply (MP_bisdec_dec mp).
    + apply red_refl.
    + exact H.
Qed.

Definition lift (P: Prop) X : X -> Prop := fun _ => P.

Fact lift_dec_Dec {P: Prop} {X} (x:X) :
  dec P <=> Dec (lift P X).
Proof.
  split; unfold dec, lift; tauto.
Qed.

Fact MP_sdec_dec_necessary X :
  X -> (forall p: X -> Prop, sdec p -> sdec (co p) -> Dec p) -> MP.
Proof.
  intros x H. apply MP_bitest. intros P f g H1 H2.
  specialize (H (lift P X)).
  apply (lift_dec_Dec x), H.
  - exists (fun _ => f); easy.
  - exists (fun _ => g); easy.
Qed.

Fact MP_ct_cosdec :
  MP -> sdec (co ct).
Proof.
  intros mp. apply MP_coK. exact mp.
  apply ired_ct_coK.
Qed.

(*** Promises *)

Notation Prom Y := (nat -> option Y).
Definition del {Y} (f: Prom Y) n := f n <> None.
Definition span {Y} (f: Prom Y) n := least (del f) n.
Definition delta {Y} (f: Prom Y) y n := span f n /\ f n = Some y.
Notation "f ⇓" := (exists n, del f n) (at level 20).
Notation "f ↓ y" := (exists n, delta f y n) (at level 20).

Section Promises.
  Variable Y: Type.
  Implicit Type y : Y.
  Implicit Type f : Prom Y.
  Implicit Type g : test.

  Fact delta_del f y :
    f ↓ y -> f ⇓.
  Proof.
    intros (n&_&H). exists n. hnf. congruence.
  Qed.
  
  Fact span_unique f n n' :
    span f n -> span f n' -> n = n'.
  Proof.
    unfold span. intros ? ?. eapply least_unique; eassumption.
  Qed.
  
  Fact delta_unique f y y' :
    f ↓ y -> f ↓ y' -> y = y'.
  Proof.
    intros (n&H1&H2) (n'&H1'&H2').
    enough (n = n') as <- by congruence.
    eapply span_unique; eassumption.
  Qed.

  Fact del_dec f :
    Dec (del f).
  Proof.
    intros n. unfold dec, del. destruct (f n); intuition easy.
  Qed.
 
  Fact span_dec f :
    Dec (span f).
  Proof.
    intros n. apply least_dec, del_dec.
  Qed.
 
  Fact delta_dec f y:
    eqdec Y -> Dec (delta f y).
  Proof.
    intros d n. unfold delta.
    destruct (span_dec f n) as [H|H].
    - destruct (f n) as [y'|] eqn:E.
      + destruct (d y' y) as [->|H1]; unfold dec; intuition congruence.
      + right. intuition easy.
    - right; easy.
  Qed.
  
  Fact del_span f :
    f ⇓ -> Sigma n, span f n.
  Proof.
    intros H.
    apply least_ewo. apply del_dec. exact H.
  Qed.
  
  Fact del_delta f :
    f ⇓ -> Sigma y, f ↓ y.
  Proof.
    intros [n H]%del_span.
    destruct (f n) as [y|] eqn:E.
    - exists y, n. easy.
    - exfalso. apply H, E.
  Qed.

  Fact sdec_del :
    sdec (fun f => f ⇓).
  Proof.
    exists (fun f n => if f n then true else false). hnf.
    intros f. split; intros [n H]; exists n.
    - hnf in H. destruct (f n); easy.
    - hnf. destruct (f n); easy.
  Qed.
   
  Fact sdec_delta y :
    eqdec Y -> sdec (fun f => f ↓ y).
  Proof.
    intros d.
    exists (fun f n => if delta_dec f y d n then true else false).
    intros f. split;
      intros [n H]; exists n; destruct delta_dec as [H1|H1]; easy.
  Qed.

  Fact red_K_del :
    Y -> K  ⪯ (fun f => f ⇓).
  Proof.
    intros y.
    exists (fun g n => if g n then Some y else None). hnf.
    intros g. split; intros [n H]; exists n.
    - hnf. destruct (g n); easy.
    - hnf in H. destruct (g n); easy.
  Qed.

  Fact red_del_delta y :
    (fun f => f ⇓) ⪯ (fun f => f ↓ y).
  Proof.
    exists (fun f n => if f n then Some y else None). hnf.
    intros f. split.
    - intros (y'&n&H1&H2) %del_delta.
      exists n. hnf. rewrite H2. split. 2:easy.
      split; unfold del.
      + rewrite H2. easy.
      + intros k H3.
        destruct H1 as [_ H1]. specialize (H1 k H3). unfold del in H1.
        destruct (f k) as [y''|]; intuition easy.
    - intros (n&_&H). exists n. unfold del. destruct (f n); easy.
  Qed.

  Fact ired_del_K :
    Y -> (fun f => f ⇓) ≈ K.
  Proof.
    intros y. split.
    - apply sdec_del.
    - apply red_K_del, y.
  Qed.

  Fact ired_delta_K y :
    eqdec Y -> (fun f => f ↓ y) ≈ K.
  Proof.
    intros d. split.
    - apply sdec_delta, d.
    - eapply red_trans.
      + apply red_K_del, y.
      + apply red_del_delta.
  Qed.

  Fact pruning :
    forall f, Sigma f', (forall y, f ↓ y <-> f' ↓ y) /\
                 (forall n y, f' n = Some y -> delta f y n).
  Proof.
    intros f.
    exists (fun n => if span_dec f n then f n else None); unfold delta. split.
    - intros y. split; intros (n&H1&H2); exists n.
      + unfold span, least, del.
        destruct (span_dec f n) as [H3|H3]. 2:easy.
        split. 2:easy. split. congruence.
        intros k H4. destruct (span_dec f k) as [H5|H5]. 2:easy.
        exfalso. enough (k = n) by lia.
        eapply span_unique; eassumption.
      + destruct (span_dec f n); easy.
    - intros n y. destruct (span_dec f n); easy.
  Qed.

End Promises.
Arguments delta_unique {Y f y y'}.
Arguments delta_dec {Y}.
Arguments span_dec {Y}.

(*** Promising functions *)

Notation SD X := (X -> nat -> bool).
Notation PF X Y := (X -> nat -> option Y).

Section PFun.
  Variable X Y : Type.
  Implicit Type x : X.
  Implicit Type y : Y.
  Implicit Type f : PF X Y.
  Implicit Type g : SD X.

  Fact PF_functional f x y y' :
    f x ↓ y -> f x ↓ y' -> y = y'.
  Proof.
    apply delta_unique.
  Qed.

  Fact PF_EWO f x :
    f x ⇓ -> Sigma y, f x ↓ y.
  Proof.
    apply del_delta.
  Qed.
  
  Fact PF_total f :
    (forall x, f x ⇓) -> Sigma h, forall x, f x ↓ h x.
  Proof.
    intros H.
    apply (skolem_trans (fun x y => f x ↓ y)).
    intros x. apply PF_EWO, H.
  Qed.

  Fact PF_translation_from_sdec :
    Y -> forall g: X -> test, Sigma f: PF X Y, forall x, K (g x) <-> f x ⇓.
  Proof.
    intros y g.
    exists (fun x n => if g x n then Some y else None).
    intros x; split; intros [n H].
    - exists n. hnf. rewrite H. easy.
    - hnf in H. exists n. destruct g; congruence.
  Qed.
  
  Fact PF_translation_to_sdec :
    forall f: PF X Y, Sigma g: X -> test, forall x, K (g x) <-> f x ⇓.
  Proof.
    intros f.
    exists (fun x n => if f x n then true else false).
    intros x; split; intros [n H].
     - exists n. hnf. destruct f; congruence.
    - hnf in H. exists n. destruct f; congruence.
  Qed.

  Fact PF_sdec :
    forall f: PF X Y, sdec (fun x => f x ⇓).
  Proof.
    intros f.
    destruct (PF_translation_to_sdec f) as [g Hg].
    exists g. intros x. symmetry. apply Hg.
  Qed.

  Fact PF_sdec_iff (p: X -> Prop) :
    Y -> sdec p <=> Sigma f: PF X Y, forall x, p x <-> f x ⇓.
  Proof.
    intros y. split.
    - intros [g Hg]. hnf in Hg.
      destruct (PF_translation_from_sdec y g) as [f Hf].
      exists f. intros x. specialize (Hg x). specialize (Hf x). tauto.
    - intros [f Hf]. destruct (PF_sdec f) as [g Hg].
      exists g. intros x. specialize (Hg x). specialize (Hf x).
      cbn in Hg. tauto.
  Qed.
  
  Fact PF_sdec_delta y :
    eqdec Y -> forall f: PF X Y, sdec (fun x => f x ↓ y).
  Proof.
    intros d f. apply red_skolem. intros x.
    exists (fun n => if delta_dec (f x) y d n then true else false).
    split;
      intros [n H]; exists n; destruct delta_dec as [H1|H1]; easy.
  Qed.

End PFun.
Arguments PF_sdec_delta {X Y}.

Fact UT_PF_del_unsdec Y :
  UT -> Y -> exists f: PF nat Y, ~ sdec (co (fun n => f n ⇓)).
Proof.
  intros [g Hg] %UT_codom_not_basic y.
  destruct (PF_translation_from_sdec nat Y y g) as [f Hf].
  exists f. contradict Hg. destruct Hg as [r Hr]. hnf in Hr.
  exists r. unfold compl, dom. intros n. unfold compl in Hr.
  specialize (Hr n). specialize (Hf n). tauto.
Qed.

Fact composition {X Y Z} :
  forall (f: PF X Y) (g: PF Y Z), Sigma h: PF X Z,
  forall x z, h x ↓ z <-> (exists y, f x ↓ y /\ g y ↓ z).
Proof.
  intros f g.
  pose (h x n := match f x (arp1 n)  with
                 | None => None
                 | Some y => if span_dec (f x) (arp1 n)
                            then if span_dec (g y) (arp2 n)
                                 then g y (arp2 n)
                                 else None
                            else None
                 end).
  exists h. intros x z. split.
  - intros (n&H1&H2). revert H2. unfold h.
    destruct (f x (arp1 n)) as [y|] eqn:E1. 2:easy.
    destruct (span_dec (f x) (arp1 n)) as [H2|H2]. 2:easy.
    destruct (span_dec (g y) (arp2 n)) as [H3|H3]. 2:easy.
    intros H4. exists y. unfold delta. eauto 6. 
  - intros (y&(n1&H11&H12)&(n2&H21&H22)).
    exists (arp n1 n2). split.
    + unfold span, del, h. split.
      * rewrite arp1_eq, arp2_eq, H12.
        destruct (span_dec (f x) n1) as [H3|H3]. 2:easy.
        rewrite H22. destruct (span_dec (g y) n2); easy.
      * intros k H.
        destruct (f x (arp1 k)) as [y'|] eqn:E1. 2:easy.
        destruct (span_dec (f x) _) as [H3|H3]. 2:easy.
        assert (E2: arp1 k = n1).
        { eapply span_unique; eassumption. }
        assert (y' = y) as -> by congruence.
        destruct (span_dec (g y) _) as [H4|H4]. 2:easy.
        exfalso.
        assert (E4: arp2 k = n2).
        { eapply span_unique; eassumption. }
        enough (arp n1 n2 = k) by lia.
        rewrite <-E2, <-E4. apply arp_eq.
    + unfold h. rewrite arp1_eq, arp2_eq, H12.
      destruct (span_dec (f x) n1) as [H3|H3]. 2:easy.
      rewrite H22. destruct (span_dec (g y) n2); easy. 
Qed.

(*** Recusant Partial Decider *)

Section PartialDec.
  Variable X : Type.
  Implicit Type x : X.
  Implicit Type f g : PF X bool.
  Implicit Type p : X -> Prop.    

  Definition pdec p f :=
    forall x b, f x ↓ b -> if b then p x else ~p x.

  Fact pdec_trivial p :
    pdec p (fun _ _ => None).
  Proof.
    intros x [|]; intros (n&_&H); easy.
  Qed.

  Fact pdec_total_dec p f :
    pdec p f -> (forall x, f x ⇓) -> Dec p.
  Proof.
    intros H1 H2 x.
    specialize (H2 x).
    apply del_delta in H2 as (b&H3).
    specialize (H1 x b).
    destruct b; unfold dec; tauto.
  Qed.

  Fact dec_pdec_total p :
    Dec p -> Sigma f, pdec p f /\ (forall x, f x ⇓).
  Proof.
    intros d.
    exists (fun x _ => if d x then Some true else Some false).
    split.
    - intros x b.
      destruct (d x) as [H|H], b.
      + easy.
      + intros (n&_&H1). easy.
      + intros (n&_&H1). easy.
      + easy.
    - intros x. exists 0.
      destruct (d x) as [H|H]; easy. 
  Qed.
         
  Definition recusant f :=
    forall g, (forall x b, f x ↓ b -> g x ↓ b) -> exists x, ~ g x ⇓.

  Fact recusant_total f :
    (forall x, Sigma b, (forall b' , f x ↓ b' -> b' = b)) -> ~ recusant f.
  Proof.
    intros F H.
    specialize (H (fun x _ => Some (pi1 (F x)))) as [x H].
    - intros x b' H. exists 0. unfold delta, least, del.
      repeat split. easy. hnf; lia. f_equal.
      destruct (F x) as [b'' H1]. cbn. symmetry. auto.
    - apply H. exists 0. easy.
  Qed.

  Fact recusant_delta_undec f b :
    Dec (fun x => f x ↓ b) -> ~recusant f.
  Proof.
    intros d H. revert H. apply recusant_total.
    intros x. destruct (d x) as [H1|H1].
    - exists b. intros b' H2. eapply delta_unique; eassumption.
    - exists (negb b). intros b' H2. destruct b, b'; easy.
  Qed.

  Fact recusant_del_undec f :
    Dec (fun x => f x ⇓) -> ~recusant f.
  Proof. 
    intros d. apply recusant_total.
    intros x. destruct (d x) as [H1|H1].
    - apply del_delta in H1 as [b H1].
      exists b. intros b' H2. eapply delta_unique; eassumption.
    - exists true. intros b' H2. contradict H1. eapply delta_del, H2.
  Qed.
  
  Fact recusant_recusant f g :
    recusant f -> (forall x b, f x ↓ b -> g x ↓ b) -> recusant g.
  Proof.
  intros Hf Hg h Hh. apply Hf. auto.
  Qed.
End PartialDec.

Arguments recusant {X}.

Fact compose_right {X Y Z} (f: PF X Y) (h: Y -> Z) :
  Sigma g, forall x y, f x ↓ y -> g x ↓ h y.
Proof.
  exists (fun x k => match f x k with
             | Some y => Some (h y)
             | None => None
             end).
  intros x y (k&H1&H2). exists k. split.
  - split; unfold del.
    + rewrite H2. easy.
    + intros k' H3.
      destruct H1 as [_ H1].
      specialize (H1 k' H3).
      unfold del in H1.
      destruct (f x k') as [z|] eqn:E. 2:easy.
      exfalso. apply H1. easy. 
  - rewrite H2. easy.
Qed.

Definition UPD :=  Sigma U: nat -> PF nat bool, forall f, exists c, forall n b, f n ↓ b <-> U c n ↓ b.

Fact UPD_recusant :
  UPD -> Sigma f: PF nat bool, recusant f.
Proof.
  intros [U HU].
  exists (fun  n => U n n). intros f Hf.
  destruct (compose_right f negb) as [g Hg].
  destruct (HU g) as [c Hc].
  exists c. intros (b&H)%del_delta.
  enough (f c ↓ negb b) as H'.
  { generalize (delta_unique H H').  destruct b; easy. }
  apply Hf, Hc, Hg, H.
Qed.

(*** Universal Partial Decider *)

Definition gamma (g1 g2: nat -> bool) : Prom  bool :=
  fun k => if g1 k then Some true
        else if g2 k then Some false else None.

Lemma gamma_correct1 {f g b} :
  gamma f g ↓ b -> (if b then K f else K g).
Proof.
  intros (n&_&H2). revert H2; unfold gamma.
  destruct (f n) eqn:Ef.
  - intros [= <-]. exists n; easy.
  - destruct (g n) eqn:Eg.
    + intros [= <-]. exists n; easy.
    + easy.
Qed.

Notation "f || g" := (K f -> K g -> False).

(* gamma constant if g1 || g2 *)

Fact gamma_correct (f g: nat -> bool) b :
  f || g -> 
  gamma f g ↓ b <-> (if b then K f else K g).
Proof.
  intros H. split.
  - apply gamma_correct1.
  - destruct b; intros H1.
    + assert (gamma f g ⇓) as [b H2] %del_delta.
      { destruct H1 as [n H1]. exists n. unfold del, gamma. rewrite H1. easy. }
      destruct b. easy.
      exfalso. apply gamma_correct1 in H2. cbn in H2. apply H; easy.
    + assert (gamma f g ⇓) as [b H2] %del_delta.
      { destruct H1 as [n H1]. exists n.
        unfold del, gamma. rewrite H1. destruct (f n); easy. }
      destruct b. 2:easy.
      exfalso. apply gamma_correct1 in H2. cbn in H2. apply H; easy.
Qed.

Fact UT_UPD :
  UT -> UPD.
Proof.
  intros [U HU].
  pose (V c n := gamma (U (arp1 c) n) (U (arp2 c) n)).
  exists V. intros f.
  destruct (PF_sdec_delta true bool_eqdec f) as [g1 H1].
  destruct (PF_sdec_delta false bool_eqdec f) as [g2 H2].
  unfold red in *.
  destruct (HU g1) as [c1 Hc1].
  destruct (HU g2) as [c2 Hc2].
  unfold dom in *.
  exists (arp c1 c2). intros n b.
  unfold V. rewrite arp1_eq, arp2_eq.
  specialize (H1 n). specialize (H2 n).
  specialize (Hc1 n). specialize (Hc2 n).
  rewrite gamma_correct.
  - destruct b; tauto.
  - assert (f n ↓ true -> f n ↓ false -> False).
    { intros H3 H4. generalize (delta_unique H3 H4). easy. }
    tauto.
Qed.

Fact UT_recusant :
  UT -> Sigma f: PF nat bool, recusant f.
Proof.
  intros H. apply UPD_recusant, UT_UPD, H.
Qed.
