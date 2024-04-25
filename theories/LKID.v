Require Import Base Syntax InductiveDefinitions.
Require Import Relations.
Require Import Sorting.Permutation.
Import ListNotations.

Section lkid.
  Context {Σ : signature} {Φ : @IndDefSet Σ}.

  Inductive sequent : Type :=
  | mkSeq (left : list (formula Σ)) (right : list (formula Σ)).

  Notation "Γ ⊢ Δ" := (mkSeq Γ Δ) (no associativity, at level 61).
  (* Γ izvodi Δ *)

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
  
  Definition shift_formula := @subst_formula Σ (funcomp var_term ↑).
  Definition shift_formulas := map shift_formula.
  
  Inductive LKID : sequent -> Prop := 
  (* Structural rules. *)
  | Ax : forall Γ Δ φ, In φ Γ -> In φ Δ -> LKID (Γ ⊢ Δ)
  | Wk : forall Γ' Δ' Γ Δ,
      Γ' ⊆ Γ ->
      Δ' ⊆ Δ ->
      LKID (Γ' ⊢ Δ') ->
      LKID (Γ ⊢ Δ)
  | Cut : forall Γ Δ φ,
      LKID (Γ ⊢ φ :: Δ) ->
      LKID (φ :: Γ ⊢ Δ) ->
      LKID (Γ ⊢ Δ)
  | Subst : forall Γ Δ,
      LKID (Γ ⊢ Δ) ->
      forall σ, LKID (map (subst_formula σ) Γ ⊢ map (subst_formula σ) Δ)
  (* Propositional rules. *)
  | NegL : forall Γ Δ φ, LKID (Γ ⊢ φ :: Δ) -> LKID (FNeg φ :: Γ ⊢ Δ)
  | NegR : forall Γ Δ φ, LKID (φ :: Γ ⊢ Δ) -> LKID (Γ ⊢ FNeg φ :: Δ)
  | ImpL : forall Γ Δ φ ψ,
      LKID (Γ ⊢ φ :: Δ) -> LKID (ψ :: Γ ⊢ Δ) ->
      LKID (FImp φ ψ :: Γ ⊢ Δ)
  | ImpR : forall Γ Δ φ ψ,
      LKID (φ :: Γ ⊢ ψ :: Δ) -> LKID (Γ ⊢ (FImp φ ψ) :: Δ)
  (* Quantifier rules. *)
  | AllL : forall Γ Δ φ t,
      LKID (subst_formula (t .: ids) φ :: Γ ⊢ Δ) -> 
      LKID (FAll φ :: Γ ⊢ Δ)
  | AllR : forall Γ Δ φ,
      LKID (shift_formulas Γ ⊢ φ :: shift_formulas Δ) ->
      LKID (Γ ⊢ (FAll φ) :: Δ)
  (* TODO *).

  

  Lemma NegL_inversion : forall Γ Δ φ,
      LKID (FNeg φ :: Γ ⊢ Δ) -> LKID (Γ ⊢ φ :: Δ).
  Proof.
    intros Γ Δ φ H.
    apply Cut with (FNeg φ).
    - apply NegR. apply Ax with φ; intuition.
    - eapply Wk; eauto; intuition.
  Qed.

  Lemma NegR_inversion : forall Γ Δ φ,
      LKID (Γ ⊢ FNeg φ :: Δ) -> LKID (φ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ H.
    apply Cut with (FNeg φ).
    - eapply Wk; eauto; intuition.
    - apply NegL. apply Ax with φ; intuition.
  Qed.
                                      
  Lemma ImpL_inversion : forall Γ Δ φ ψ,
      LKID (FImp φ ψ :: Γ ⊢ Δ) -> LKID (Γ ⊢ φ :: Δ) /\ LKID (ψ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ ψ H; split.
    - apply Cut with (FImp φ ψ).
      + apply ImpR. apply Ax with φ; intuition.
      + eapply Wk; eauto; intuition.
    - apply Cut with (FImp φ ψ).
      + apply ImpR. apply Ax with ψ; intuition.
      + eapply Wk; eauto; intuition.
  Qed.
  
  Lemma AxExtended : forall Γ Δ φ, LKID (φ :: Γ ⊢ φ :: Δ).
  Proof.
    intros Γ Δ φ. apply Wk with ([φ]) ([φ]).
    - intros ψ Hin; inversion Hin; subst; intuition.
    - intros ψ Hin; inversion Hin; subst; intuition.
    - apply Ax with φ; intuition.
  Qed.

  Lemma ContrL : forall Γ Δ φ, LKID (φ :: φ :: Γ ⊢ Δ) -> LKID (φ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ; apply Wk.
    - intros ψ Hin; inversion Hin.
      + subst; now left.
      + assumption.
    - intuition.
  Qed.
  
  Lemma ContrR : forall Γ Δ φ, LKID (Γ ⊢ φ :: φ :: Δ) -> LKID (Γ ⊢ φ :: Δ).
  Proof.
    intros Γ Δ φ; apply Wk.
    - intuition.
    - intros ψ Hin; inversion Hin.
      + subst; now left.
      + assumption.
  Qed.

  Lemma Perm : forall Γ Δ Γ' Δ',
      Permutation Γ Γ' ->
      Permutation Δ Δ' ->
      LKID (Γ ⊢ Δ) ->
      LKID (Γ' ⊢ Δ').
  Proof.
    intros Γ Δ Γ' Δ' HpermΓ HpermΔ Hlkid.
    apply Wk with Γ Δ.
    - intros φ Hin. apply Permutation_in with Γ; assumption.
    - intros φ Hin. apply Permutation_in with Δ; assumption.
    - assumption.
  Qed.
  
  Lemma AndL1 : forall Γ Δ φ ψ,
      LKID (φ :: Γ ⊢ Δ) ->
      LKID (FAnd φ ψ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ ψ H; unfold FAnd.
    apply NegL. apply ImpR. apply NegR.
    apply Wk with (φ :: Γ) Δ; intuition.
  Qed.

  Lemma AndL2 : forall Γ Δ φ ψ,
      LKID (ψ :: Γ ⊢ Δ) ->
      LKID (FAnd φ ψ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ ψ H; unfold FAnd.
    apply NegL. apply ImpR. apply NegR.
    apply Wk with (ψ :: Γ) Δ; intuition.
  Qed.

  Lemma AndR : forall Γ Δ φ ψ,
      LKID (Γ ⊢ φ :: Δ) -> LKID (Γ ⊢ ψ :: Δ) ->
      LKID (Γ ⊢ FAnd φ ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ Hφ Hψ; unfold FAnd.
    apply NegR. apply ImpL.
    - apply Hφ.
    - apply NegL. apply Hψ.
  Qed.

  Lemma OrL : forall Γ Δ φ ψ,
      LKID (φ :: Γ ⊢ Δ) -> LKID (ψ :: Γ ⊢ Δ) ->
      LKID (FOr φ ψ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ ψ Hφ Hψ; unfold FOr.
    apply ImpL.
    - apply NegR. apply Hφ.
    - apply Hψ.
  Qed.

  Lemma OrR1 : forall Γ Δ φ ψ,
      LKID (Γ ⊢ φ :: Δ) ->
      LKID (Γ ⊢ FOr φ ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ H; unfold FOr.
    apply ImpR. apply NegL. eapply Wk; eauto; intuition.
  Qed.

  Lemma OrR2 : forall Γ Δ φ ψ,
      LKID (Γ ⊢ ψ :: Δ) ->
      LKID (Γ ⊢ FOr φ ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ H; unfold FOr.
    apply ImpR. apply NegL. eapply Wk; eauto; intuition.
  Qed.

  Lemma OrL_inversion : forall Γ Δ φ ψ, LKID (FOr φ ψ :: Γ ⊢ Δ) -> LKID (φ :: Γ ⊢ Δ) /\ LKID (ψ :: Γ ⊢ Δ).
  Proof.
    intros.
    unfold FOr in *.
    split.
    - eapply Cut with (FOr φ ψ); unfold FOr.
      + apply ImpR. apply NegL. apply Ax with φ; intuition.
      + eapply Wk; eauto; intuition.
    - eapply Cut with (FOr φ ψ); unfold FOr.
      + apply ImpR. apply NegL. apply Ax with ψ; intuition.
      + eapply Wk; eauto; intuition.
  Qed.
  
  Lemma OrR_inversion : forall Γ Δ φ ψ, LKID (Γ ⊢ FOr φ ψ :: Δ) -> LKID (Γ ⊢ φ :: ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ H.
    apply Cut with (FOr φ ψ).
    - apply Wk with Γ (FOr φ ψ :: Δ); intuition.
    - unfold FOr in *. apply ImpL.
      + apply NegR. apply AxExtended.
      + apply Ax with ψ; intuition.
  Qed.

  Lemma ExistL : forall Γ Δ φ,
      LKID (φ :: shift_formulas Γ ⊢ shift_formulas Δ) ->
      LKID (FExist φ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ H; unfold FExist.
    apply NegL. apply AllR. apply NegR. apply H.
  Qed.

  Lemma ExistR : forall Γ Δ φ t,
      LKID (Γ ⊢ subst_formula (t .: ids) φ :: Δ) ->
      LKID (Γ ⊢ FExist φ :: Δ).
  Proof.
    intros Γ Δ φ t H; unfold FExist.
    apply NegR. apply AllL with t; cbn. apply NegL. apply H.
  Qed.

  
  Section proof_examples.
    Lemma LKID_XM : forall Γ Δ φ, LKID (Γ ⊢ FOr φ (FNeg φ) :: Δ).
    Proof.
      intros Γ Δ φ; unfold FOr.
      apply ImpR. apply AxExtended.
    Qed.

    Lemma LKID_ID : forall Γ Δ φ, LKID (Γ ⊢ FImp φ φ :: Δ).
    Proof.
      intros Γ Δ φ.
      apply ImpR. apply AxExtended.
    Qed.

    Lemma LKID_EXPLOSION : forall Γ Δ φ, LKID (FAnd φ (FNeg φ) :: Γ ⊢ Δ).
    Proof.
      intros Γ Δ φ; unfold FAnd.
      apply NegL. apply ImpR. apply NegR. apply NegL. apply AxExtended.
    Qed.
  End proof_examples.
End lkid.
