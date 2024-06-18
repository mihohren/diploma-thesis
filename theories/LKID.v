Require Import Base Syntax InductiveDefinitions.
Require Import Relations RelationClasses.
Require Import Sorting.Permutation.
Import ListNotations.

Section lkid.
  Context {Σ : signature}.
  Context (Φ : IndDefSet Σ).

  Inductive sequent : Set :=
  | mkSeq (Γ Δ : list (formula Σ)).
  Notation "Γ ⊢ Δ" := (mkSeq Γ Δ) (no associativity, at level 61).

  Definition provable (proofsystem : sequent -> Prop) (φ : formula Σ) :=
    proofsystem ([] ⊢ [φ]).

  Definition Prem (Pi Pj : IndPredS Σ) :=
    exists pr, Φ pr /\ indcons pr = Pi /\ exists ts, List.In (Pj; ts) (indpreds pr).

  Definition Prem_star := clos_refl_trans (IndPredS Σ) Prem.

  Lemma Prem_star_refl : Reflexive Prem_star.
  Proof.
    intros P; apply rt_refl.
  Qed.

  Lemma Prem_star_trans : Transitive Prem_star.
  Proof.
    intros P Q R HPQ HQR; induction HQR.
    - apply rt_trans with x; auto using rt_step.
    - assumption.
    - auto.
  Qed.
      
  Definition mutually_dependent (P Q : IndPredS Σ) :=
    Prem_star P Q /\ Prem_star Q P.

  Lemma mutually_dependent_refl : Reflexive mutually_dependent.
  Proof.
    intros P; split; apply rt_refl.
  Qed.

  Lemma mutually_dependent_symm : Symmetric mutually_dependent. 
  Proof.
    intros P Q [HPQ HQP]; split; auto.
  Qed.

  Lemma mutually_dependent_trans : Transitive mutually_dependent. 
  Proof.
    intros P Q R [HPQ HQP] [HQr HRQ]; split; now apply rt_trans with Q.
  Qed.

  Lemma mutually_dependent_equiv : Equivalence mutually_dependent.
  Proof.
    constructor.
    - apply mutually_dependent_refl.
    - apply mutually_dependent_symm.
    - apply mutually_dependent_trans.              
  Qed.
  
  Definition FPreds_from_preds (ps : list {P : PredS Σ & vec (term Σ) (pred_ar P)})
    : list (formula Σ) :=
    map (fun '(Q; us) => FPred Q us) ps.
  
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
  (* Induction rules. *)
  | IndL : forall Γ Δ
             (Pj : IndPredS Σ) (u : vec _ (indpred_ar Pj))
             (z_i : forall P, vec var (indpred_ar P))
             (z_i_nodup : forall P, VecNoDup (z_i P))
             (G_i : IndPredS Σ -> formula Σ)
             (HG2 : forall Pi, ~mutually_dependent Pi Pj ->
                          G_i Pi = FIndPred
                                     Pi
                                     (V.map var_term (z_i Pi))),
      let maxΓ := max_fold (map some_var_not_in_formula Γ) in
      let maxΔ := max_fold (map some_var_not_in_formula Δ) in
      let maxP := some_var_not_in_formula (FIndPred Pj u) in
      let shift_factor := max maxP (max maxΓ maxΔ) in
      let Fj := subst_formula
                  (finite_subst (z_i Pj) u)
                  (G_i Pj) in
      let minor_premises :=
        (forall pr (HΦ : Φ pr) (Hdep : mutually_dependent (indcons pr) Pj),
            let Qs := shift_formulas_by
                        shift_factor
                        (FPreds_from_preds (preds pr)) in
            let Gs := map (fun '(P; args) =>
                             let shifted_args :=
                               V.map
                                 (shift_term_by shift_factor)
                                 args in
                             let σ :=
                               finite_subst
                                 (z_i P)
                                 (shifted_args) in
                             let G := G_i P in
                             subst_formula σ G)
                        (indpreds pr) in
            let Pi := indcons pr in
            let ty := V.map
                        (shift_term_by shift_factor)
                        (indargs pr) in
            let Fi := subst_formula
                        (finite_subst (z_i Pi) ty)
                        (G_i Pi) in
            LKID (Qs ++ Gs ++ Γ ⊢ Fi :: Δ))
      in
      minor_premises ->
      LKID (Fj :: Γ ⊢ Δ) ->
      LKID (FIndPred Pj u :: Γ ⊢ Δ)
  | IndR : forall Γ Δ pr σ,
      Φ pr ->
      (forall Q us,
          In (Q; us) (preds pr) ->
          LKID (Γ ⊢ (FPred Q (V.map (subst_term σ) us) :: Δ))) ->
      (forall P ts,
          In (P; ts) (indpreds pr) ->
          LKID (Γ ⊢ (FIndPred P (V.map (subst_term σ) ts) :: Δ))) ->
      LKID ( Γ ⊢ FIndPred
               (indcons pr)
               (V.map (subst_term σ) (indargs pr))
               :: Δ).

  Ltac lkid_intros :=
    repeat match goal with
      | [|- forall _ : @formula _, _] =>
          let φ := fresh "φ" in
          intros φ
      | [|- forall _ : list (@formula _), _] =>
          let Γ := fresh "Γ" in
          intros Γ
      | [|- forall _ : LKID _, _] =>
          let H := fresh "Hlkid" in
          intros H
      | _ => intros
      end.

  Ltac lkid_propositional :=
    unfold FOr, FAnd, FExist in *;
    repeat match goal with
      | [ |- LKID (FNeg _ :: _ ⊢ _) ] => apply NegL
      | [ |- LKID (_ ⊢ FNeg _ :: _) ] => apply NegR
      | [ |- LKID (FImp _ _ :: _ ⊢ _) ] => apply ImpL
      | [ |- LKID (_ ⊢ FImp _ _ :: _) ] => apply ImpR
      end; try auto.

  Ltac lkid_trysolve :=
    lkid_intros; lkid_propositional.
  
  Lemma AxExtended : forall Γ Δ φ, LKID (φ :: Γ ⊢ φ :: Δ).
  Proof.
    intros Γ Δ φ. apply Ax with φ; now left.
  Qed.

  Lemma ContrL : forall Γ Δ φ, LKID (φ :: φ :: Γ ⊢ Δ) -> LKID (φ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ; apply Wk.
    - intros ψ Hin; inversion Hin.
      + subst; now left.
      + assumption.
    - apply incl_refl.
  Qed.
  
  Lemma ContrR : forall Γ Δ φ, LKID (Γ ⊢ φ :: φ :: Δ) -> LKID (Γ ⊢ φ :: Δ).
  Proof.
    intros Γ Δ φ; apply Wk.
    - apply incl_refl.
    - intros ψ Hin; inversion Hin.
      + subst; now left.
      + assumption.
  Qed.

  Lemma Perm : forall Γ' Δ' Γ Δ,
      Permutation Γ' Γ ->
      Permutation Δ' Δ ->
      LKID (Γ' ⊢ Δ') ->
      LKID (Γ ⊢ Δ).
  Proof.
    intros Γ' Δ' Γ Δ HpermΓ HpermΔ Hlkid.
    apply Wk with Γ' Δ'.
    - intros φ Hin. apply Permutation_in with Γ'; assumption.
    - intros φ Hin. apply Permutation_in with Δ'; assumption.
    - assumption.
  Qed.

  Lemma AndL : forall Γ Δ φ ψ,
      LKID (φ :: ψ :: Γ ⊢ Δ) ->
      LKID (FAnd φ ψ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ ψ H; unfold FAnd.
    apply NegL. apply ImpR. apply NegR.
    apply Perm with (φ :: ψ :: Γ) Δ.
    - repeat constructor.
    - apply Permutation_refl.
    - assumption.
  Qed.
    
  Lemma AndR : forall Γ Δ φ ψ,
      LKID (Γ ⊢ φ :: Δ) -> LKID (Γ ⊢ ψ :: Δ) ->
      LKID (Γ ⊢ FAnd φ ψ :: Δ).
  Proof. lkid_trysolve. Qed.

  Lemma OrL : forall Γ Δ φ ψ,
      LKID (φ :: Γ ⊢ Δ) -> LKID (ψ :: Γ ⊢ Δ) ->
      LKID (FOr φ ψ :: Γ ⊢ Δ).
  Proof. lkid_trysolve. Qed.
    
  Lemma OrR : forall Γ Δ φ ψ,
      LKID (Γ ⊢ φ :: ψ :: Δ) ->
      LKID (Γ ⊢ FOr φ ψ :: Δ).
  Proof. lkid_trysolve. Qed.

  Lemma OrR1 : forall Γ Δ φ ψ,
      LKID (Γ ⊢ φ :: Δ) ->
      LKID (Γ ⊢ FOr φ ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ H.
    apply OrR. eapply Wk; eauto.
    - apply incl_refl.
    - intros ε Hin; inversion Hin; subst; [ left | do 2 right ]; auto.
  Qed.

  Lemma OrR2 : forall Γ Δ φ ψ,
      LKID (Γ ⊢ ψ :: Δ) ->
      LKID (Γ ⊢ FOr φ ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ H.
    apply OrR. eapply Wk; eauto.
    - apply incl_refl.
    - intros ε Hin; inversion Hin; subst; [ right; left | do 2 right ]; auto.
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

  Ltac incl_auto :=
    auto using incl_refl, incl_tl, in_eq, in_cons;
    match goal with
    | [ |- incl _ _ ] => solve [let φ := fresh "φ" in
                              let Hin := fresh "Hin" in
                              (intros φ Hin;
                              inversion Hin;
                              subst;
                              auto using incl_refl, incl_tl, in_eq, in_cons)]
    | _ => idtac
    end.
  
  Lemma NegL_inversion : forall Γ Δ φ,
      LKID (FNeg φ :: Γ ⊢ Δ) -> LKID (Γ ⊢ φ :: Δ).
  Proof.
    intros Γ Δ φ H.
    apply Cut with (FNeg φ).
    - apply NegR. apply Ax with φ; incl_auto.
    - eapply Wk; eauto; incl_auto.
  Qed.

  Lemma NegR_inversion : forall Γ Δ φ,
      LKID (Γ ⊢ FNeg φ :: Δ) -> LKID (φ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ H.
    apply Cut with (FNeg φ).
    - eapply Wk; eauto; incl_auto.
    - apply NegL. apply Ax with φ; incl_auto.
  Qed.
                                      
  Lemma ImpL_inversion : forall Γ Δ φ ψ,
      LKID (FImp φ ψ :: Γ ⊢ Δ) -> LKID (Γ ⊢ φ :: Δ) /\ LKID (ψ :: Γ ⊢ Δ).
  Proof.
    intros Γ Δ φ ψ H; split.
    - apply Cut with (FImp φ ψ).
      + apply ImpR. apply Ax with φ; incl_auto.
      + eapply Wk; eauto; incl_auto.
    - apply Cut with (FImp φ ψ).
      + apply ImpR. apply Ax with ψ; incl_auto.
      + eapply Wk; eauto; incl_auto.
  Qed.
  
  Lemma OrL_inversion : forall Γ Δ φ ψ, LKID (FOr φ ψ :: Γ ⊢ Δ) -> LKID (φ :: Γ ⊢ Δ) /\ LKID (ψ :: Γ ⊢ Δ).
  Proof.
    intros.
    unfold FOr in *.
    split.
    - eapply Cut with (FOr φ ψ); unfold FOr.
      + apply ImpR. apply NegL. apply Ax with φ; incl_auto.
      + eapply Wk; eauto; incl_auto.
    - eapply Cut with (FOr φ ψ); unfold FOr.
      + apply ImpR. apply NegL. apply Ax with ψ; incl_auto.
      + eapply Wk; eauto; incl_auto.
  Qed.
  
  Lemma OrR_inversion : forall Γ Δ φ ψ, LKID (Γ ⊢ FOr φ ψ :: Δ) -> LKID (Γ ⊢ φ :: ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ H.
    apply Cut with (FOr φ ψ).
    - apply Wk with Γ (FOr φ ψ :: Δ); incl_auto.
    - unfold FOr in *. apply ImpL.
      + apply NegR. apply AxExtended.
      + apply Ax with ψ; incl_auto.
  Qed.
  
  Section proof_examples.
    Lemma LKID_XM : forall φ, provable LKID (FOr φ (FNeg φ)).
    Proof.
      intros φ.
      apply OrR.
      apply Perm with [] [FNeg φ; φ]; auto using perm_nil, perm_swap.
      apply NegR. apply AxExtended.
    Qed.

    Lemma LKID_ID : forall φ, provable LKID (FImp φ φ).
    Proof.
      intros φ.
      apply ImpR. apply AxExtended.
    Qed.

    Lemma LKID_EXPLOSION : forall φ Δ, LKID ([FAnd φ (FNeg φ)] ⊢ Δ).
    Proof.
      intros φ Δ. apply AndL.
      apply Perm with [FNeg φ; φ] Δ; auto using perm_swap.
      apply NegL. apply AxExtended.
    Qed.

    Lemma LKID_DN : forall φ, provable LKID (FImp (FNeg (FNeg φ)) φ).
    Proof.
      intros φ.
      apply ImpR. apply NegL. apply NegR. apply AxExtended.
    Qed.
  End proof_examples.
End lkid.
