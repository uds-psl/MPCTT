(*** MPCTT, Chapter 3 *)

(* We show how Coq accommodates propositions and proofs. *)

Print False.
Definition exfalso : forall X: Prop, False -> X :=
  fun X a => match a with end.
Check exfalso.
Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.

Section Demo.
  Variables X Y Z: Prop.

  Goal X -> ~X -> False.
  Proof.
    exact (fun x f => f x).
    Show Proof.
  Qed.
 
  Goal X -> ~X -> False.
  Proof.
    refine (fun x f => _).
    exact (f x).
    Show Proof.
  Qed.
 
  Goal X -> ~X -> False.
  Proof.
    intros x f. apply f. exact x.
    Show Proof.
  Qed.
  
  Goal X -> ~X -> False.
  Proof.
    auto.
    Show Proof.
  Qed.
  
  Goal X -> ~X -> Y.
  Proof.
    intros x f.
    apply exfalso.
    exact (f x).    
    Show Proof.
  Qed.
  
  Goal X -> ~X -> Y.
  Proof.
    intros x f.
    exfalso.  (* Coq's exfalso tactic *)
    exact (f x).
    Show Proof.
  Qed.
    
  Goal (X -> ~X) -> (~X -> X) -> False.
  Proof.
    refine (fun f g => _).
    refine (f _ _).
    - refine (g (fun x => _)). exact (f x x).
    - refine (g (fun x => _)). exact (f x x).
    Show Proof.
  Qed.
 
  Goal (X -> ~X) -> (~X -> X) -> False.
  Proof.
    refine (fun f g => _).
    unshelve refine (let x:X := _ in _).
    - refine (g (fun x => _)). exact (f x x).
    - exact (f x x).
    Show Proof.
  Qed.
  
  Goal (X -> ~X) -> (~X -> X) -> False.
  Proof.
    intros f g.
    assert (x: X).
    - apply g. intros x. exact (f x x).
    - exact (f x x).
      Show Proof.
  Qed.

  Goal X -> ~ ~ X.
  Proof.
    intros x f. exact (f x).
  Qed.
  
  Goal ~ ~X -> (X -> ~X) -> False.
  Proof.
    intros f g.
    apply f. intros x.
    exact (g x x).
    Show Proof.
  Qed.

  Goal ~ ~ (~ ~ X -> X).
  Proof.
    intros f. apply f. intros g.
    exfalso. apply g. intros x.
    apply f. intros _. exact x.
    Show Proof.
  Qed.

  Goal ~ ~ (~ ~ X -> X).
  Proof.
    tauto.
  Qed.

End Demo.

Fact mobility1 X (P: Prop) (p: X -> Prop) :
  (forall x, P -> p x) -> (P -> forall x, p x).
Proof.
  intros f H x. apply f. apply H.
  Show Proof.
Qed.

Fact mobility2 X (P: Prop) (p: X -> Prop) :
  (P -> forall x, p x) -> (forall x, P -> p x).
Proof.
  intros f x H. apply f. apply H.
  Show Proof.
Qed.

Fact exchange X Y (p: X -> Y -> Prop) :
  (forall x y, p x y) -> (forall y x, p x y).
Proof.
  intros f y x. exact (f x y).
Qed.

Fact exchange_alpha X Y (p: X -> Y -> Prop) :
  (forall x y, p x y) -> (forall x' y', p x' y').
Proof.
  exact (fun a => a).
Qed.

(** We use Coq's conjunctions, and disjunctions. *)

Locate "/\".
Print and.
Locate "\/".
Print or.
(* proof constructors of or have overloaded implicit arguments *)

Definition match_and {X Y Z: Prop} 
  : X /\ Y -> (X -> Y -> Z) -> Z
  := fun a e => match a with conj x y => e x y end.

Definition match_or {X Y Z: Prop}
  : X \/ Y -> (X -> Z) -> (Y -> Z) -> Z
  := fun a e1 e2 => match a with or_introl x => e1 x | or_intror y => e2 y end.

Section Demo.
  Variables X Y Z: Prop.

  Goal X /\ Y -> Y /\ X.
  Proof.
    intros H.
    apply (match_and H).
    intros x y. exact (conj y x).
    Show Proof.
  Qed.

  Goal X /\ Y -> Y /\ X.
  Proof.
    intros [x y].
    split. exact y. exact x.
    Show Proof.
  Qed.

  Goal X \/ Y -> Y \/ X.
  Proof.
    intros H.
    apply (match_or H).
    - intros x. exact (or_intror x).
    - intros y. exact (or_introl y).
      Show Proof.
  Qed.
  
  Goal X \/ Y -> Y \/ X.
  Proof.
    intros [x|y].
    - right. exact x.
    - left. exact y.
      Show Proof.
  Qed.

  Goal X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
  Proof.
    intros H.
    apply (match_or H).
    - intros x. apply conj.
      + exact (or_introl x).
      + exact (or_introl x).
    - intros H1.
      apply (match_and H1).
      intros y z. apply conj.
      + exact (or_intror y).
      + exact (or_intror z).
  Qed.

  Goal X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
  Proof.
    intros [x | [y z]].
    - split.
      + left. exact x.
      + left. exact x.
    - split.
      + right. exact y.
      + right. exact z.
  Qed.
  
  Goal X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
  Proof.
    tauto.
  Qed.
End Demo.

Notation "A <-> B" := ((A -> B) /\ (B -> A))
                      (at level 95, no associativity) : type_scope.

Section Demo.
  Variables X Y Z: Prop.

  Goal ~(X <-> ~X).
  Proof.
    intros H. apply (match_and H).
    intros f g.
    assert (x: X).
    - apply g. intros x. exact (f x x).
    - exact (f x x).
      Show Proof.
  Qed.
 
  Goal ~(X <-> ~X).
  Proof.
    intros [f g].
    Show Proof. (* unnecessary beta redex *)
    assert (x:X).
    - apply g. intros x. exact (f x x).
    - exact (f x x).
  Qed.

  Fact Russell :
    ~(X <-> ~X).
  Proof.
    tauto.
  Qed.

  Fact deMorgan_or :
    ~ (X \/ Y) <-> ~ X /\ ~ Y.
  Proof.
    split.
    - intros f. split.
      + contradict f. left. exact f.
      + contradict f. right. exact f.
    - intros [f g] [x|y].
      + auto.
      + auto.
  Qed.
 
  Goal ~ ~(X -> Y) <-> (~ ~X -> ~ ~Y).
  Proof.
    split.
    - intros f g h.
      apply g. intros x. apply f. intros f'.
      exact (h (f' x)).
    - intros f g. apply g. intros x. exfalso.
      apply f.
      + intros h. auto.
      + intros y. apply g. auto.
  Qed.
End Demo.

(** Assumed variables now appear as leading arguments *)

Check Russell.
Check deMorgan_or.

Goal forall X (p q: X -> Prop),
    (forall x, p x <-> q x) -> (forall x, q x) -> forall x, p x.
Proof.
  intros X p q f g x.
  destruct (f x) as [_ h].
  exact (h (g x)).
Qed.

Goal forall X (p q: X -> Prop),
    (forall x, p x <-> q x) -> (forall x, q x) -> forall x, p x.
Proof.
  intros X p q f g x.
  apply f.  (* matchin direction is applied *)
  exact (g x).
Qed.

Goal forall X (p q: X -> Prop),
    (forall x, p x <-> q x) -> (forall x, q x) -> forall x, p x.
Proof.
  intros X p q f g x.
  refine (match f x with conj _ h => _ end).
  exact (h (g x)).
  Show Proof.
Qed.

(** Impredicative characterizations *)

Goal False <-> forall Z: Prop, Z.
Proof.
  split.
  - intros [].
  - intros f. exact (f False).
  Show Proof.
Qed.

Goal forall X Y: Prop,
    X /\ Y <-> forall Z: Prop, (X -> Y -> Z) -> Z.
Proof.
  intros X Y.
  split.
  - intros [x y] Z f. exact (f x y).
  - intros f. eapply f. apply conj.
    (* eapply is smarter than apply *)
    Show Proof.
Qed.

Goal forall X Y: Prop,
    X \/ Y <-> forall Z: Prop, (X -> Z) -> (Y -> Z) -> Z.
Proof.
  intros X Y.
  split.
  - intros [x|y] Z f g.
    + exact (f x).
    + exact (g y).
  - intros f. eapply f.
    + eapply or_introl.
    + eapply or_intror.
      Show Proof.
Qed.

(** Excluded Middle *)

Fact XM_DN :
  (forall X: Prop, X \/ ~X) <-> (forall X: Prop, ~ ~X -> X).
Proof.
  split; intros H X.
  - destruct (H X) as [x|H1].
    + auto.
    + intros H2. exfalso. apply H2. exact H1.
  - apply H. intros H1. apply H1.
    right. contradict H1. auto.
Qed.
  
