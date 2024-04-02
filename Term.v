Require Import Base.
Require Import Signature.

Notation var := nat.

Section term.
  Context {Σ : signature}.

  Unset Elimination Schemes.
  
  (* Definition 2.1.2 *)
  Inductive term : Type :=
  | TVar : var -> term
  (* constant symbols are function symbols with arity 0 *)
  | TFunc : forall f : FuncS Σ, vec term (fun_ar f) -> term.

  Set Elimination Schemes.

  Fixpoint term_subst (s : var -> term) (t : term) : term :=
    match t with
    | TVar v => s v
    | TFunc f args => TFunc f (V.map (term_subst s) args)
    end.
  
  (* In term [t], substitutes all occurrences
     of the variable [x] with the term [u] *)
  Definition term_var_subst (t : term) (x : var) (u : term) : term :=
    term_subst (fun v => if v =? x then u else TVar v) t.

  (* The set of all used variables of a given term. *)
  Inductive Var : term -> E.Ensemble var :=
  | VarVar : forall v, Var (TVar v) v
  | VarFunc : forall f args v, V.Exists (fun t => Var t v) args -> Var (TFunc f args) v.
End term.

Arguments term Σ : clear implicits.

Module TermNotations.
  Declare Scope term_scope.
  Delimit Scope term_scope with term.
  Notation " t [ f ] " := (term_subst f t)
                            (at level 100) : term_scope.
  Open Scope term_scope.
End TermNotations.

Section term_ind1.
  Context {Σ : signature} (P : term Σ -> Prop).
  
  Hypothesis Pbase : forall v, P (TVar v).
  Hypothesis Pind : forall (f : FuncS Σ) args,
      V.Forall (fun st => P st) args -> P (TFunc f args).
  
  Definition term_ind1 : forall t, P t.
    fix IND_PRINCIPLE 1; intros [v | f args].
    - apply Pbase.
    - apply Pind. induction args; constructor.
      + apply IND_PRINCIPLE.
      + assumption.
  Defined.
End term_ind1.

Require Import Coq.Program.Equality.

Section term_ind2.
  Context {Σ : signature} (P : term Σ -> Prop).
  
  Hypothesis Pbase : forall v, P (TVar v).
  Hypothesis Pind : forall (f : FuncS Σ) args,
      (forall st, V.In st args -> P st) -> P (TFunc f args).

  Definition term_ind2 : forall t, P t.
    induction t as [v | f args IH] using term_ind1.
    - apply Pbase.
    - apply Pind. intros st Hin. rewrite V.Forall_forall in IH.
      apply IH. apply Hin.
  Defined.
End term_ind2.

Section term_facts.
  Import TermNotations.
  Context {Σ : signature}.

  Lemma var_not_in_Var_not_eq : forall v x, ~ @Var Σ (TVar v) x -> v <> x.
  Proof.
    intros v x H. intros eq. apply H. subst; constructor.
  Qed.
  
  Lemma var_not_in_Func_not_in_args : forall (f : FuncS Σ) args x,
      ~ Var (TFunc f args) x -> forall st, V.In st args -> ~ Var st x.
  Proof.
    intros f args x Hnotin; unfold E.In in *.
    intros t Hin Hvar. apply Hnotin. constructor.
    apply Exists_exists.
    exists t; intuition.
  Qed.
    
  Lemma term_subst_id : forall (t : term Σ) (x : var),
      t [fun x => TVar x] = t.
  Proof.
    induction t as [v | f args IH] using term_ind2; intros x.
    - reflexivity.
    - simpl. f_equal. rewrite <- V.map_id; apply V.map_ext_in.
      intuition.
  Qed.
    
  Lemma term_var_subst_no_occ : forall (t u : term Σ) (x : var),
      ~ Var t x -> term_var_subst t x u = t.
  Proof.
    intros t; induction t as [v | f args IH] using term_ind2;
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
