Require Import Base Signature Term.
Require Import Formula.

Section structure.
  Context {Σ : signature}.

  Structure structure := {
      domain : Type;
      interpF : forall f : FuncS Σ, vec domain (fun_ar f) -> domain;
      interpP : forall P : PredS Σ, vec domain (pred_ar P) -> Prop;
      interpIP : forall P : IndPredS Σ, vec domain (indpred_ar P) -> Prop;
    }.
End structure.

Arguments structure : clear implicits.
Arguments interpF {Σ M} _ _ : rename.
Arguments interpP {Σ M} _ _ : rename.
Arguments interpIP {Σ M} _ _ : rename.
Notation "| M |" := (domain M) (no associativity, at level 150).




Section environment.
  Context {Σ : signature} {X : Vars} {M : structure Σ}.

  Import VarNotations.
  
  Definition env := X -> |M|.
  
  Definition ExtendEnv (ρ : env) (b : |M|) (x : X⁺) :=
    match x with
    | Some a => ρ a
    | None   => b
    end.
  

  Import VarNotations.
  
  Definition env_subst (ρ : env) (x : X) (d : |M|) : X -> |M| :=
    fun (y : X) => if y == x then d else ρ y.
  
  
  Fixpoint eval (ρ : env) (t : term Σ X) : |M| :=
    match t with
    | TVar x => ρ x
    | TFunc f args => interpF f (V.map (eval ρ) args)
    end.

  Definition eval_vec (ρ : env) {n} (v : vec (term Σ X) n) : vec (|M|) n :=
    V.map (eval ρ) v.

  Fixpoint eval_subst (ρ : env) (t : term Σ X) (x : X) (d : |M|) : |M| :=
    match t with
    | TVar y => env_subst ρ x d y
    | TFunc f args => interpF f (V.map (fun st => eval_subst ρ st x d) args)
    end.
    
End environment.

Arguments env {Σ} X M.

Fixpoint interpForm [Σ X] M (ρ : env X M) (φ : formula Σ X) : Prop :=
    match φ with
    | FPred R args    => interpP R (V.map (eval ρ) args)
    | FIndPred R args => interpIP R (V.map (eval ρ) args)
    | FImp φ₁ φ₂      => interpForm M ρ φ₁ → interpForm M ρ φ₂
    | FNeg ψ          => ¬ interpForm M ρ ψ
    | FAll ψ          => ∀ v, interpForm M (ExtendEnv ρ v) ψ
    end.

Definition models [Σ X] M (φ : formula Σ X) : Prop :=
  ∀ ρ, interpForm M ρ φ.
  
Notation "M , ρ ⊧ φ" := (interpForm M ρ φ) (at level 100, format "M ,  ρ  ⊧  φ").
Notation "M ⊧ φ" := (models M φ) (at level 101).
