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

  Notation "t [ u / x ]" := (term_var_subst t u x)
                              (no associativity, at level 150).

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
