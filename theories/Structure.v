Require Import Base Syntax.

Section structure.
  Context {Σ : signature}.

  Structure structure := {
      domain : Type;
      interpF (f : FuncS Σ) : vec domain (fun_ar f) -> domain;
      interpP (P : PredS Σ) : vec domain (pred_ar P) -> Prop;
      interpIP (P : IndPredS Σ) : vec domain (indpred_ar P) -> Prop;
    }.
End structure.

Arguments structure : clear implicits.
Arguments interpF {Σ M} _ _ : rename.
Arguments interpP {Σ M} _ _ : rename.
Arguments interpIP {Σ M} _ _ : rename.
Notation "| M |" := (domain M) (no associativity, at level 150).

Section environment.
  Context {Σ : signature} {M : structure Σ}.

  Definition env := var -> |M|.

  Definition env_subst (ρ : env) (x : var) (d : |M|) : var -> |M| :=
    fun (y : var) => if y =? x then d else ρ y.

  Fixpoint eval (ρ : env) (t : term Σ) : |M| :=
    match t with
    | var_term x => ρ x
    | TFunc f args => interpF f (V.map (eval ρ) args)
    end.

  Definition eval_vec (ρ : env) {n} (v : vec (term Σ) n) : vec (|M|) n :=
    V.map (eval ρ) v.

  Fixpoint eval_subst (ρ : env) (t : term Σ) (x : var) (d : |M|) : |M| :=
    match t with
    | var_term y => env_subst ρ x d y
    | TFunc f args => interpF f (V.map (fun st => eval_subst ρ st x d) args)
    end.
End environment.

Arguments env {Σ} M.

Section lemma_2_1_5.
  Context {Σ : signature} {M : structure Σ}.
  Variable ρ : env M.
  Variable t : term Σ.
  Variable x : var.

  Lemma eval_subst_sanity1 : forall (d : |M|),
      ~ TV t x -> eval_subst ρ t x d = eval ρ t.
  Proof.
    induction t as [v | f args IH];
      intros d x_not_in_t.
    - simpl; unfold env_subst; destruct (v =? x) eqn:eq_vx.
      + exfalso. apply x_not_in_t. rewrite Nat.eqb_eq in eq_vx; subst.
        constructor.
      + reflexivity.
    - simpl. f_equal. apply V.map_ext_in.
      intros st Hin. apply IH.
      + assumption.
      + intros x_in_var_st. apply x_not_in_t.
        constructor. exists st; intuition.
  Qed.

  Lemma eval_subst_sanity2 : forall (u : term Σ),
      eval_subst ρ t x (eval ρ u) = eval ρ (term_var_subst t x u).
  Proof.
    intros u. induction t as [v | f args IH].
    - cbn. unfold env_subst. destruct (v =? x) eqn:E;
        reflexivity.
    - simpl. f_equal. rewrite V.map_map.
      apply V.map_ext_in. intros st Hst.
      apply IH. assumption.
  Qed.
End lemma_2_1_5.
