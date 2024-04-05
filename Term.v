Require Import Base.
Require Import Signature.
Require Program.

Section variables.
  Record Vars := mkVars {
    typ :> Type;
    eq_dec: ∀ (x y : typ), {x = y} + {x ≠ y}
  }.

  Program Definition NoVars := {| typ := Empty_set |}.
  Next Obligation.
    destruct x.
  Defined.
  
  Program Definition Extend (X : Vars) := {| typ := option (typ X) |}.
  Next Obligation.
    destruct x as [x|]; destruct y as [y|]; 
      try solve [right; discriminate | left; reflexivity].
    destruct (eq_dec _ x y).
    * left; f_equal; assumption.
    * right; intro.
      inversion H; subst.
      apply n; reflexivity.
  Defined.  
End variables.


Module VarNotations.
  Declare Scope var_scope.
  Delimit Scope var_scope with var.
  Notation "∅" := NoVars : var_scope.
  Notation "X ⁺" := (Extend X) (at level 1, format "X ⁺") : var_scope.
  Notation "x == y" := (eq_dec _ x y) (at level 50) : var_scope.
  Open Scope var_scope.
End VarNotations.



Section term.
  Context {Σ : signature}.

  Unset Elimination Schemes.
  
  (* Term over a set of (possible) free variables X. *)
  Inductive term (X : Vars): Type :=
  | TVar : X -> term X
  (* constant symbols are function symbols with arity 0 *)
  | TFunc : forall f : FuncS Σ, vec (term X) (fun_ar f) -> (term X).

  Arguments TVar [X] _.
  Arguments TFunc [X] _.

  Set Elimination Schemes.

  Fixpoint term_subst [X Y : Vars] (s : X -> term Y) (t : term X) : term Y :=
    match t with
    | TVar v => s v
    | TFunc f args => TFunc f (V.map (term_subst s) args)
    end.
  
  Import VarNotations.
  
  (* In term [t], substitutes all occurrences
     of the variable [x] with the term [u] *)
  Definition term_var_subst [X : Vars] (t : term X) (x : X) (u : term X) : term X :=
    term_subst (fun v => if v == x then u else TVar v) t.


End term.

Arguments term : clear implicits.
Arguments TVar [Σ X].
Arguments TFunc [Σ X].

Module TermNotations.
  Declare Scope term_scope.
  Delimit Scope term_scope with term.
  Notation " t [ f ] " := (term_subst f t)
                            (at level 100) : term_scope.
  Open Scope term_scope.
End TermNotations.



Section term_ind.
  Context {Σ : signature} {X : Vars} (P : term Σ X -> Prop).
  
  Hypothesis Pbase : forall (v : X), P (TVar v).
  Hypothesis Pind : forall (f : FuncS Σ) args,
      (forall st, V.In st args -> P st) -> P (TFunc f args).

  Definition term_ind : forall t, P t.
    fix IND_PRINCIPLE 1; intros [v | f args].
    - apply Pbase.
    - apply Pind. apply V.Forall_forall.         
      induction args; constructor.
      + apply IND_PRINCIPLE.
      + assumption.
  Defined.
End term_ind.

Section term_facts.
  Import TermNotations.
  Context {Σ : signature}.
  
    
  Lemma term_subst_id [X] : forall (t : term Σ X) (x : X),
      t [fun x => TVar x] = t.
  Proof.
    induction t as [v | f args IH]; intros x.
    - reflexivity.
    - simpl. f_equal. rewrite <- V.map_id; apply V.map_ext_in.
      intuition.
  Qed.
    
End term_facts.
