Require Import Coq.Unicode.Utf8.
Require Import Coq.Vectors.Vector.
Require Import Coq.Sets.Ensembles.
Require Import CFOLID.Signature.
Require Import Arith.

Definition vec := Vector.t.

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
        Vector.Forall (fun st => P st) args -> P (TFunc f args).
    
    Definition term_better_ind : forall t : term, P t.
      fix IND_PRINCIPLE 1. intros t. induction t.
      - apply Pbase.
      - apply Pind. induction v; constructor.
        + apply IND_PRINCIPLE.
        + assumption.
    Defined.
  End term_better_ind.

  (* In term [t], substitutes all occurrences
     of the variable [x] with the term [u] *)
  Fixpoint term_var_subst (t : term) (u : term) (x : var) : term :=
    match t with
    | TVar v => if v =? x then u else t
    | TFunc f args => TFunc f (map (fun st => term_var_subst st u x) args)
    end.

  (* The set of all variables of a given term. *)
  Inductive Var : term -> Ensemble var :=
  | VarVar : forall (v : var), Var (TVar v) v
  | VarFunc : forall (f : FuncS Σ) (args : vec term (FuncArr f)) (v : var),
      Exists (fun t => Var t v) args -> Var (TFunc f args) v.
End term.

Arguments TVar {Σ} _.
Arguments TFunc {Σ} _.
Arguments term_better_ind {Σ} _ _ _ _.
Arguments term_var_subst {Σ} _ _ _.
Arguments Var {Σ} _.

Notation " t '[' x '=>' u ']' " := (term_var_subst t u x) (at level 100).

Section term_facts.
  Variable Σ : signature.

  Lemma var_not_in_Var_not_eq : forall v x, ~ In _ (@Var Σ( TVar v)) x -> v <> x.
  Proof.
    intros v x H. intros eq. apply H. subst; constructor.
  Qed.

  Lemma var_not_in_Func_not_in_sub :
    forall (f : FuncS Σ) (args : vec (term Σ) (FuncArr f)) (x : var),
      ~ In _ (Var (TFunc f args)) x -> Vector.Forall (fun st => ~ In _ (Var st) x) args.
  Proof.
    intros f args x H.
    unfold In in *.
    generalize dependent args.
    Fail induction args.
  Admitted.
    
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
      ~ In _ (Var t) x -> t [x => u] = t.
  Proof.
    intros t; induction t as [v | f args IH] using term_better_ind;
      intros u x x_not_in_t.
    - simpl; destruct (v =? x) eqn:Eqvx.
      + exfalso; apply x_not_in_t.
        rewrite Nat.eqb_eq in Eqvx. subst; constructor.
      + reflexivity.
  Admitted.
End term_facts.
