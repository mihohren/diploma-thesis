Require Import Base Syntax InductiveDefinitions.
Require Import Relations.
Import ListNotations.

Section lkid.
  Context {Σ : signature} {Φ : @IndDefSet Σ}.

  Inductive sequent : Type :=
  | mkSeq (left : list (formula Σ)) (right : list (formula Σ)).

  Notation "Γ ⊢ Δ" := (mkSeq Γ Δ) (no associativity, at level 61).

  Definition Prem (Pi Pj : IndPredS Σ) :=
    exists pr, Φ pr /\ indcons pr = Pi /\ exists ts, List.In (existT _ Pj ts) (indpreds pr).

  Definition Prem_star := clos_refl_trans (IndPredS Σ) Prem.

  Lemma Prem_star_refl : forall P, Prem_star P P.
  Proof.
    intros P; apply rt_refl.
  Qed.

  Lemma Prem_star_trans : forall P Q R, Prem_star P Q -> Prem_star Q R -> Prem_star P R.
  Proof.
    intros P Q R HPQ HQR; induction HQR.
    - apply rt_trans with x; auto using rt_step.
    - assumption.
    - auto.
  Qed.
      
  Definition mutually_dependent (P Q : IndPredS Σ) :=
    Prem_star P Q /\ Prem_star Q P.

  Lemma mutually_dependent_refl : forall P, mutually_dependent P P.
  Proof.
    intros P; split; apply rt_refl.
  Qed.

  Lemma mutually_dependent_symm : forall P Q, mutually_dependent P Q -> mutually_dependent Q P.
  Proof.
    intros P Q [HPQ HQP]; split; intuition.
  Qed.

  Lemma mutually_dependent_trans : forall P Q R,
      mutually_dependent P Q -> mutually_dependent Q R -> mutually_dependent P R.
  Proof.
    Hint Constructors clos_refl_trans.
    intros P Q R [HPQ HQP] [HQR HRQ]; unfold Prem_star in *; split.
    - induction HPQ; eauto 10. apply rt_trans with y; auto.
    - induction HQP; eauto 10. apply rt_trans with x; auto.
  Qed.

  Inductive LKID : sequent -> Prop :=
  (* Structural rules. *)
  | Ax : forall Γ Δ, (exists φ, In φ Γ /\ In φ Δ) -> LKID (Γ ⊢ Δ)
  | Wk : forall Γ' Δ' Γ Δ,
      (forall φ, In φ Γ' -> In φ Γ) ->
      (forall φ, In φ Δ' -> In φ Δ) ->
      LKID (Γ' ⊢ Δ') -> LKID (Γ ⊢ Δ)
  | ContrL : forall Γ Δ φ, LKID (Γ ++ [φ; φ] ⊢ Δ) -> LKID (Γ ++ [φ] ⊢ Δ)
  | ContrR : forall Γ Δ φ, LKID (Γ ⊢ φ :: φ :: Δ) -> LKID (Γ ⊢ φ :: Δ)
  | Cut : forall Γ Δ φ,
      LKID (Γ ⊢ φ :: Δ) -> LKID (Γ ++ [φ] ⊢ Δ) ->
      LKID (Γ ⊢ Δ)
  | Subst : forall Γ Δ, LKID (Γ ⊢ Δ) -> forall σ, LKID (map (subst_formula σ) Γ ⊢ map (subst_formula σ) Δ)
  (* Propositional rules. *)
  | NegL : forall Γ Δ φ, LKID (Γ ⊢ φ :: Δ) -> LKID (Γ ++ [FNeg φ] ⊢ Δ)
  | NegR : forall Γ Δ φ, LKID (Γ ++ [φ] ⊢ Δ) -> LKID (Γ ⊢ FNeg φ :: Δ)
  | ImpL : forall Γ Δ φ ψ,
      LKID (Γ ⊢ φ :: Δ) -> LKID (Γ ++ [ψ] ⊢ Δ) ->
      LKID (Γ ++ [FImp φ ψ] ⊢ Δ)
  | ImpR : forall Γ Δ φ ψ,
      LKID (Γ ++ [φ] ⊢ ψ :: Δ) -> LKID (Γ ⊢ (FImp φ ψ) :: Δ)
  (* Quantifier rules. *)
  (* TODO *).
