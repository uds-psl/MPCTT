(*** MPCTT, Chapter 4 *)

(* We study conversion and propositonal equality. *)

Definition id X : X -> X := fun x => x.

Section Conversion.
  Variable p: nat -> Prop.

  Check fun a : p 4 => a.
  Check fun a : p (2 + 2) => a.
  Check fun a : p 4 => id (p (2 + 2)) a.

  (* Coq uses the notation $s:t$ for applications "id t s" 
     of the polymorphic identity function *)      
  Check fun a : p 4 => a : p (2 + 2).
  Check id (p 4 -> p (2 + 2)) (fun a : p 4 => a).
  Check (fun a : p 4 => a) : p 4 -> p (2 + 2).

  (* One can force cenversions with the change tactic *)
  Goal p 4 -> p (2 + 2).
  Proof.
    intros a.
    change (p 4).
    exact a.
    Show Proof.
  Qed.

  Goal p 4 -> p (2 + 2).
  Proof.
    intros a. exact a.
    Show Proof.
  Qed.
  
  Goal p 4 -> p (2 + 2).
  Proof.
    intros a.
    apply (id (p 4)).
    exact a.
    Show Proof.
  Qed.

End Conversion.

(** Coq implements propositional negation 
    and propositional equivalence with
    predicates "not" and "iff". *)  

Locate "~".
Print not.
Locate "<->".
Print iff.

Goal forall X, ~X -> X -> False.
  intros X a.
  change (~X).
  exact a.
  Show Proof.
Qed.

Goal forall X, ~X -> X -> False.
  intros X a. exact a.
  Show Proof.
Qed.

Goal forall X Y, (X <-> Y) -> (X -> Y) /\ (Y -> X).
Proof.
  intros * a.
  change (X <-> Y).
  Show Proof. (* not visible in partial proof term *)
  exact a.
  Show Proof.
Qed.

(* The pattern tactic does beta expansions *)

(** Exercise Leibniz symmetry *)

Fact Leibniz_symmetry X (x y: X) :
  (forall p: X -> Prop, p x -> p y) -> (forall p: X -> Prop, p y -> p x).
Proof.
  intros F p.
  pattern y.
  Show Proof.  (* pattern puts in a type ascription *)
  apply F.
  intros a. exact a.
  Show Proof.
Qed.

Check fun X (x y: X) (F: forall p: X -> Prop, p x -> p y) (p: X -> Prop) =>
        F (fun y => p y -> p x) (fun a => a).

(*** Abstract Equality *)
        
Section AbstractEquality.
  Variable eq : forall X, X -> X -> Prop.
  Variable Q  : forall X x, eq X x x.
  Variable R  : forall X x y (p: X -> Prop), eq X x y -> p x -> p y.

  Arguments eq {X}.
  Arguments Q {X}.
  Arguments R {X x y}.
  Notation "s = t" := (eq s t) : type_scope.
  Notation "s <> t" := (~ s = t) : type_scope.

  Goal 2 + 3 = 9 - 4.
  Proof.
    apply (Q 5).
    Show Proof.
  Qed.

  Goal forall X (x y z: X),
      x = y -> y = z -> x = z.
  Proof.
    intros * e.
    pattern y.
    apply (R _ e).
    (* beta reduction was done tacitly *)
    exact (fun e => e).
    Show Proof.
  Qed.

  Check fun X (x y z : X) (e : x = y) =>
          R (fun y => y = z -> x = z) e (fun e => e).

(*** Basic Equational Facts *)
    
  Goal True <> False.
  Proof.
    intros e.
    pattern False.
    apply (R _ e).
    exact I.
    Show Proof.
  Qed.

  Check fun e : True = False => R (fun X => X) e I.

  Goal true <> false.
  Proof.
    intros e.
    change ((fun x:bool => if x then True else False) false).
    apply (R _ e).
    exact I.
    Show Proof.
  Qed.

  Check (fun e : true = false =>
           R (fun x : bool => if x then True else False) e I).

  Goal forall x y, S x = S y -> x = y.
  Proof.
    intros x y e.
    change ((fun z => x = match z with 0 => 0 | S z' => z' end) (S y)).
    apply (R _ e).
    exact (Q x).
    Show Proof.
  Qed.

  Check fun (x y : nat) (e : S x = S y) =>
          R (fun z => x = match z with
                       | 0 => 0
                       | S z' => z'
                       end) e (Q x).

  Goal forall X (x y: X),
      x = y -> y = x.
  Proof.
    intros * e.
    pattern y.
    apply (R _ e).
    exact (Q x).
    Show Proof.
  Qed.

  Check  fun X (x y : X) (e : x = y) =>
           R (fun y => y = x) e (Q x).

  Goal forall X (x y z: X),
      x = y -> y = z -> x = z.
  Proof.
    intros * e.
    pattern y.
    apply (R _ e).
    exact (fun e => e).
    Show Proof.
  Qed.

  Check fun X (x y z : X) (e : x = y) =>
          R (fun y => y = z -> x = z) e (fun e => e).

  Goal forall X (x y z: X),
      x = y -> y = z -> x = z.
  Proof.
    intros * e1 e2.
    (* claim is "(eq x) z" up to notation *)
    exact (R _ e2 e1).
    Show Proof.
  Qed.

  Check fun X (x y z : X) (e1 : x = y) (e2 : y = z) =>
          R (eq x) e2 e1.

  (** Applicative closure laws *)

  Goal forall X Y (f: X -> Y) x x',
      x = x' -> f x = f x'.
  Proof.
    intros * e.
    pattern x'.
    apply (R _ e).
    apply Q.
    Show Proof.     
  Qed.

  Goal forall X Y (f g: X -> Y) x,
      f = g -> f x = g x.
  Proof.
    intros * e.
    pattern g.
    apply (R _ e).
    apply Q.
    Show Proof.     
  Qed. 

  (** Leibniz characterization *)
  
  Goal forall X x y,
      x = y <-> forall p: X -> Prop, p x -> p y.
  Proof.
    intros *. split.
    - intros e p H.
      apply (R _ e H).
    - intros H.
      change ((fun z => x = z) y).
      apply H.
      apply Q.
    Show Proof.
  Qed.

  Goal (forall X:Prop, X -> X) <> (forall X:Prop, X).
  Proof.
    intros e.
    enough (forall X:Prop, X) as H.
    - apply H.
    - apply (R (fun X:Prop => X) e).
      exact (fun X x => x).
  Qed.

End AbstractEquality.

(*** Definition of Leibniz Equality *)

Module Type EQ.
  Parameter eq : forall X, X -> X -> Prop.
  Parameter Q : forall X x, eq X x x.
  Parameter R : forall X x y (p: X -> Prop), eq X x y -> p x -> p y.
End EQ.

Module EqLeibniz : EQ.
  Definition eq X x y := forall p: X -> Prop, p x -> p y.
  Definition Q X x : eq X x x := fun p a => a.
  Definition R X x y p (f: eq X x y) := f p.
End EqLeibniz.

Print EqLeibniz.R.

(* We sandbox the import of EqLeibniz
   since we will use Coq's predefined equality afterwards.
 *)

Module Sandbox.
  Import EqLeibniz.
  Print R.
  Print eq.
End Sandbox.

(*** Coq's Predefined Equality *)

(* From now on we use Coq's predefined equality 
   with the tactics "reflexivity" and "rewrite". *)

Locate "=".
Check @eq.
Check @eq_refl.    (* Q, used by reflexivity tactic*)
Check @eq_ind.     (* R *)
Check @eq_ind_r.   (* used by rewrite tactic *)

Fact feq {X Y} (f: X -> Y) {x x'} :
    x = x' -> f x = f x'.
Proof.
  intros e. rewrite e. reflexivity.
  Show Proof.     
Qed.

Check @feq.
Print feq.
Compute @feq.  (* No delta reduction *)

(* The Fact-Proof-Qed format defines an abstract constant (above "feq"). 
   The command "Print" still shows the definition of abstract constants
   introduced with "Qed".
 *)

(* The "Fact" keyword is synonnymous with the keywords
   "Theorem",  "Lemma", "Corollary", "Example". 
 *)

Definition pred (x: nat) : nat :=
  match x with 0 => 0 | S x' => x' end.

Goal forall x y, S x = S y -> x = y.
Proof.
  intros * e.
  exact (feq pred e).
  Show Proof.
Qed.

Definition zero (x:nat) : Prop :=
  if x then True else False.

Goal forall x, S x <> 0.
Proof.
  intros x e.
  assert (H: False = True) by exact (feq zero e).
  rewrite H. exact I.
  Show Proof.
Qed.

Goal true <> false.
Proof.
  intros e.
  rewrite (feq (fun b: bool => if b then False else True) e).
  exact I.
  Show Proof.
Qed.

(*** Automation tactic "congruence" *)

Goal true <> false.
Proof.
  congruence.
Qed.

Goal forall x, S x <> 0.
Proof.
  congruence.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
  congruence.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
  intros * [= e]. exact e. 
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
  intros * [= <-]. reflexivity. 
Qed.

Goal forall X Y (f: X -> Y) x x',
    x = x' -> f x = f x'.
Proof.
  congruence.
Qed.

Goal forall X Y (f g: X -> Y) x,
    f = g -> f x = g x.
Proof.
  congruence.     
Qed.

Goal forall X Y (x x': X) (y y': Y),
    (x,y) = (x',y') -> x = x' /\ y = y'.
Proof.
  intros * e. split; congruence.     
Qed.

(*** Abstract Presentation of Propositional Connectives *)

Section Abstract_Prop_Connectives.
  Variable bot : Prop.
  Variable elim_bot : bot -> forall X: Prop, X.

  Fact bot_char :
    bot <-> forall Z, Z.
  Proof.
    split.
    - exact elim_bot.
    - intros H. apply H.
  Qed.

  Variable and : Prop -> Prop -> Prop.
  Variable intro_and : forall X Y, X -> Y -> and X Y.
  Variable elim_and : forall X Y Z , and X Y -> (X -> Y -> Z) -> Z.

  Fact and_char X Y :
    and X Y <-> forall Z, (X -> Y -> Z) -> Z.
  Proof.
    split.
    - intros H Z. apply elim_and, H.
    - intros H. apply H. apply intro_and.
  Qed.

  Variable or : Prop -> Prop -> Prop.
  Variable intro_or_l : forall X Y, X -> or X Y.
  Variable intro_or_r : forall X Y, Y -> or X Y.
  Variable elim_or : forall X Y Z , or X Y -> (X -> Z) -> (Y -> Z) -> Z.

  Fact or_char X Y :
    or X Y <-> forall Z, (X -> Z) -> (Y -> Z) -> Z.
  Proof.
    split.
    - intros H Z. apply elim_or, H.
    - intros H. apply H. apply intro_or_l. apply intro_or_r.
  Qed.
  
End Abstract_Prop_Connectives.

(*** Eta Conversion *)

Goal forall X Y (f: X -> Y),
    (fun x => f x) = f.
Proof.
  intros X Y f.
  cbv.
  reflexivity.
Abort.


Goal
  (fun x => 3 + x - 2) = S.
Proof.
  cbv.
  reflexivity.
Abort.

Section Currying.
  Variables X Y Z : Type.
  Definition C : (X * Y -> Z) -> X -> Y -> Z
    := fun f x y => f (x,y).
  Definition U : (X -> Y -> Z) -> X * Y -> Z
    := fun f '(x,y) => f x y.
  Goal forall f x y, U (C f) (x,y) = f (x,y).
  Proof.
    cbv.
    reflexivity.
  Qed.
  Goal forall f x y, C (U f) x y = f x y.
  Proof.
    cbv. reflexivity.
  Qed.
  Goal forall f, C (U f) = f.
  Proof.
    cbv. reflexivity.
    (* Note the use of eta equivalence *)
  Qed.
  Goal forall f, U (C f) = f.
  Proof.
    cbv.
    Fail reflexivity.
  Abort.
End Currying.
