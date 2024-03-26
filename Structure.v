Require Coq.Unicode.Utf8.
Require Coq.Vectors.Vector.
Require Import Arith Bool.
Require Import FunctionalExtensionality.
Require Import Sets.Ensembles.
Require Import CFOLID.Signature.
Require Import CFOLID.Term.

Section structure.
  Variable Σ : signature.

  Structure structure := {
      domain : Type;
      interpF : forall f : FuncS Σ, vec domain (FuncArr f) -> domain;
      interpP : forall P : PredS Σ, vec domain (PredArr P) -> Prop;
      interpIP : forall P : IndPredS Σ, vec domain (IndPredArr P) -> Prop;
    }.
End structure.

Arguments domain {Σ}.
Arguments interpF {Σ}.
Arguments interpP {Σ}.
Arguments interpIP {Σ}.
Notation "| M |" := (domain M) (no associativity, at level 150).

Section environment.
  Variable Σ : signature.
  Variable M : structure Σ.

  Definition env_var := var -> |M|.

  Definition env_var_subst (ρ : env_var) (x : var) (d : |M|)
    : var -> |M| :=
    fun (y : var) => if y =? x then d else ρ y.

  Section extended_environment.
    Variable ρvar : env_var.
              
    Fixpoint env (t : term Σ) : |M| :=
      match t with
      | TVar x => ρvar x
      | TFunc f args => interpF M f (Vector.map env args)
      end.

    Definition env_vec n (v : vec (term Σ) n) : vec (|M|) n :=
      Vector.map env v.

    Fixpoint env_subst (t : term Σ) (x : var) (d : |M|) : |M| :=
      match t with
      | TVar y => env_var_subst ρvar x d y
      | TFunc f args => interpF M f (Vector.map (fun st => env_subst st x d) args)
      end.
  End extended_environment.

  Section lemma_2_1_5.
    Variable ρvar : env_var.
    Definition ρ := env ρvar.

    Lemma env_subst_sanity1 : forall (t : term Σ) (x : var) (d : |M|),
        ~ In _ (Var t) x -> env_subst ρvar t x d = env ρvar t.
    Proof.
      intros t; induction t as [v | f args IH] using term_better_ind;
        intros x d x_not_in_t.
      - simpl; unfold env_var_subst; destruct (v =? x) eqn:eq_vx.
        + exfalso. apply x_not_in_t. rewrite Nat.eqb_eq in eq_vx; subst.
          constructor.
        + reflexivity.
      - simpl. f_equal. inversion IH; subst.
        + reflexivity.
        + admit.
          (* TODO this is a big mess because of Vector  *)
    Admitted.
                      
  End lemma_2_1_5.
End environment.
