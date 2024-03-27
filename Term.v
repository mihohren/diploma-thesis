Require Import Base.
Require Import Signature.

Section term.
  Variable Σ : signature.
  Definition var := nat.

  (* Definition 2.1.2 *)
  Inductive term : Type :=
  | TVar : var -> term
  (* constant symbols are function symbols with arity 0 *)
  | TFunc : forall f : FuncS Σ, vec term (FuncArr f) -> term.

  Section term_better_ind.
    Variable P : term -> Prop.
    
    Hypothesis Pbase : forall v, P (TVar v).
    Hypothesis Pind : forall (f : FuncS Σ) (args : vec term (FuncArr f)),
        V.Forall (fun st => P st) args -> P (TFunc f args).
    
    Definition term_better_ind : forall t : term, P t.
      fix IND_PRINCIPLE 1; intros [v | f args].
      - apply Pbase.
      - apply Pind. induction args; constructor.
        + apply IND_PRINCIPLE.
        + assumption.
    Defined.
  End term_better_ind.

  Section term_better_ind2.
    Variable P : term -> Prop.
    Hypothesis Pbase : forall v, P (TVar v).
    Hypothesis Pind : forall (f : FuncS Σ) (args : vec term (FuncArr f)),
        (forall st : term, V.In st args -> P st) -> P (TFunc f args).

    Definition term_better_ind2 : forall t : term, P t.
      induction t as [v | f args IH] using term_better_ind.
      - apply Pbase.
      - apply Pind. intros st Hin. rewrite V.Forall_forall in IH.
        apply IH. apply Hin.
    Defined.
  End term_better_ind2.    
          
  (* In term [t], substitutes all occurrences
     of the variable [x] with the term [u] *)
  Fixpoint term_var_subst (t : term) (u : term) (x : var) : term :=
    match t with
    | TVar v => if v =? x then u else t
    | TFunc f args => TFunc f (V.map (fun st => term_var_subst st u x) args)
    end.

  (* The set of all variables of a given term. *)
  Inductive Var : term -> E.Ensemble var :=
  | VarVar : forall (v : var), Var (TVar v) v
  | VarFunc : forall (f : FuncS Σ) (args : vec term (FuncArr f)) (v : var),
      V.Exists (fun t => Var t v) args -> Var (TFunc f args) v.
End term.

Arguments TVar {Σ} _.
Arguments TFunc {Σ} _.
Arguments term_better_ind {Σ} _ _ _ _.
Arguments term_var_subst {Σ} _ _ _.
Arguments Var {Σ} _.

Declare Scope term_scope.
Delimit Scope term_scope with term.
Notation " t '[' x '=>' u ']' " :=
  (term_var_subst t u x) (at level 100) : term_scope.

Section term_facts.
  Open Scope term_scope.
  Variable Σ : signature.

  Lemma var_not_in_Var_not_eq : forall v x, ~ E.In (@Var Σ (TVar v)) x -> v <> x.
  Proof.
    intros v x H. intros eq. apply H. subst; constructor.
  Qed.
  
  Lemma var_not_in_Func_not_in_args :
    forall (f : FuncS Σ) (args : vec (term Σ) (FuncArr f)) (x : var),
      ~ E.In (Var (TFunc f args)) x -> V.Forall (fun st => ~ E.In (Var st) x) args.
  Proof.
    intros f args x Hnotin; rewrite V.Forall_forall; unfold E.In in *.
    intros t Hin Hvar. apply Hnotin. constructor.
    apply Exists_exists.
    exists t; intuition.
  Qed.
    
  Lemma term_var_subst_id : forall (t : term Σ) (x : var),
      t [x => TVar x] = t.
  Proof.
    induction t as [v | f args IH] using term_better_ind; intros x.
    - simpl. destruct (v =? x) eqn:E.
      + f_equal. symmetry. apply Nat.eqb_eq. apply E.
      + reflexivity.
    - cbn. f_equal. induction IH.
      + reflexivity.
      + simpl; f_equal.
        * apply H.
        * apply IHIH.
  Qed.
    
  Lemma term_var_subst_no_occ : forall (t u : term Σ) (x : var),
      ~ E.In (Var t) x -> t [x => u] = t.
  Proof.
    intros t; induction t as [v | f args IH] using term_better_ind2;
      intros u x Hnotin; cbn.
    - destruct (v =? x) eqn:E.
      + exfalso; apply Hnotin; rewrite Nat.eqb_eq in E; subst; constructor.
      + reflexivity.
    - f_equal. rewrite <- V.map_id. apply V.map_ext_in.
      intros st Hstin. apply IH.
      + assumption.
      + intros Hinvar. apply Hnotin. constructor.
        apply Exists_exists. exists st; intuition.
  Qed.
End term_facts.
