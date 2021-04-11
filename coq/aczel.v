Unset Elimination Schemes.

Module Aczel.
  Set Printing Universes.
  Inductive tree : Type := T (X: Type) (f: X -> tree).
  Implicit Types s t: tree.

  Fail Check T tree (fun s => s).
  
  Lemma tree_ind (p: tree -> Type) :
    (forall X f, (forall x, p (f x)) -> p (T X f)) -> forall s, p s.
  Proof.
    intros F.
    refine (fix G s := match s with T X f => _ end).
    exact (F X f (fun x => (G (f x)))).
  Qed.

  Definition sub s t : Prop := match t with T X f => exists x, f x = s end.
  
  Lemma sub_irrefl :
    forall s, ~sub s s.
  Proof.
    apply tree_ind. intros X f IH [x H].
    apply (IH x).
    replace (sub (f x) (f x)) with (sub (f x) (T X f)) by congruence.
    unfold sub. eauto.
  Qed.
  
End Aczel.

Module Demo.
  Set Printing Universes.
  Definition Type_i := Type.
  Fail Inductive tree : Type_i := T (X: Type_i) (f: X -> tree).
  Inductive tree : Prop := T (X: Type_i) (f: X -> tree).
  Module T.
    Inductive tree : Type_i := T_i (X: Prop) (f: X -> tree).
  End T.
  Fail Inductive L (X: Type_i) : Set := C (_: X).
  Inductive L (X: Type_i) : Set := N | C (_: L (prod nat X)).
End Demo.

Module XM_PI.
  Inductive tree: Prop := T (X: Prop) (f: X -> tree).
  Implicit Types s t: tree.

  Definition u: tree := T tree (fun s => s).

  Lemma tree_ind (p: tree -> Prop) :
    (forall X f, (forall x, p (f x)) -> p (T X f)) -> forall s, p s.
  Proof.
    intros F.
    refine (fix G s := match s with T X f => _ end).
    exact (F X f (fun x => (G (f x)))).
  Qed.

  Lemma sub_contra (R: tree -> tree -> Prop) :
    ~ (forall s X f, R s (T X f) <-> exists x, f x = s).
  Proof.
    intros H.
    assert (H_irrefl: forall s, ~R s s).
    { apply tree_ind. intros X f IH [x H1]%H.
      apply (IH x).
      replace (R (f x) (f x)) with (R (f x) (T X f)) by congruence.
      apply H. eauto. }
    apply (H_irrefl u), H. eauto.
  Qed.

  Theorem Coquand (A: Prop) (E: Prop -> A) (D: A -> Prop) :
    ~ forall P, D (E P) <-> P.
  Proof.
    intros H.
    apply (sub_contra (fun s t => D (match t with T X f => E (exists x, f x = s) end))).
    intros s X f. apply H.
  Qed.

  Lemma elim_or (X Y: Prop) (p: X \/ Y -> Prop) :
    (forall x, p (or_introl x)) ->
    (forall y, p (or_intror y)) -> 
    forall a, p a.
  Proof.
    exact (fun f g a => match a with or_introl x => f x | or_intror y => g y end).
  Qed.

  Theorem xm_pi :
    (forall P: Prop, P \/ ~P) -> forall (P: Prop) (a b: P), a = b.
  Proof.
    intros H A a b.
    destruct (H (a=b)) as [H1|H1]. exact H1. exfalso.
    apply (Coquand A (fun P => if H P then a else b) (fun c => a = c)).
    intros P.
    (* destruct (H P) as [H2|H2]; tauto. *)
    pattern (H P). apply elim_or; tauto.
  Qed.
End XM_PI.

Module Hierarchy.
  Definition embeds X Y := 
    exists (E: X -> Y) (D: Y -> X), forall x, D (E x) = x.

  Fact embeds_refl X :
    embeds X X.
  Proof.
    exists (fun x => x), (fun x => x). reflexivity.
  Qed.

  Definition Tyi := Type.
  
  Section Hier.
    Variables (A: Tyi) (D: A -> Tyi).
    
    Inductive tree: Tyi:= T (a: A) (f: D a -> tree).

    Implicit Types s t : tree.

    Lemma tree_ind (p: tree -> Type) :
      (forall a f, (forall x, p (f x)) -> p (T a f)) -> forall s, p s.
    Proof.
      intros F.
      refine (fix G s := match s with T a f => _ end).
      exact (F a f (fun x => (G (f x)))).
    Qed.
    
    Definition sub s t : Prop :=
      match t with T a f => exists x, f x = s end.
    
    Fact sub_irrefl :
      forall s, ~ sub s s.
    Proof.
      apply tree_ind. intros a f IH [x H].
      apply (IH x).
      replace (sub (f x) (f x)) with (sub (f x) (T a f)) by congruence.
      unfold sub. eauto.
    Qed.
   
    Lemma hier (E: Tyi -> A) :
      ~ embeds tree (D (E tree)).
    Proof.
      intros (F&G&H).
      apply (sub_irrefl (T (E tree) G)).
      cbn. exists (F (T (E tree) G)). apply H.
    Qed.
  End Hier.

  Theorem hierarchy :
    forall X:Tyi, ~embeds Tyi X.
  Proof.
    intros X (E&D&H).
    apply (hier X D E). rewrite H. apply embeds_refl.
  Qed.
    
  Goal forall X:Tyi, Tyi <> X.
  Proof.
    intros X H. apply (hierarchy X). rewrite H. apply embeds_refl.
  Qed.
  
End Hierarchy.




