Require Import Base Syntax Semantics InductiveDefinitions LKID.
From Coq Require Import Logic.Classical.

Notation "Γ ⊢ Δ" := (mkSeq Γ Δ) (at level 61).

Definition Sat_sequent 
  {Σ} (M : structure Σ) (ρ : env M)
  (s : sequent)
  : Prop :=
  match s with
  | mkSeq Γ Δ => (forall φ, In φ Γ -> Sat ρ φ) -> exists ψ, In ψ Δ /\ Sat ρ ψ
  end.
  
Section soundness.
  Variable Σ : signature.
  Variable Φ : @IndDefSet Σ.

  Notation "Γ '⊫' Δ" := (forall (M : structure Σ) (ρ : env M), @Sat_sequent _ M ρ (mkSeq Γ Δ))
                            (no associativity, at level 10).

  Lemma LS_Ax : forall Γ Δ φ, In φ Γ -> In φ Δ -> Γ ⊫ Δ.
  Proof.
    intros Γ Δ φ Hin1 Hin2 M ρ Hsat.
    exists φ; intuition.
  Qed.

  Lemma LS_Wk : forall Γ' Δ' Γ Δ, Γ' ⊆ Γ -> Δ' ⊆ Δ ->
                             Γ' ⊫ Δ' -> Γ ⊫ Δ.
  Proof.
    intros Γ' Δ' Γ Δ HsubsΓ HsubsΔ Hsat M ρ HsatΓ.
    assert (HsatΓ' : forall φ, In φ Γ' -> Sat ρ φ) by intuition.
    apply Hsat in HsatΓ' as [ψ [HinΔ' Hsatψ]].
    exists ψ; auto.
  Qed.

  Lemma LS_Cut : forall Γ Δ φ, Γ ⊫ (φ :: Δ) -> (φ :: Γ) ⊫ Δ -> Γ ⊫ Δ.
  Proof.
    intros Γ Δ φ Hsat1 Hsat2 M ρ HsatΓ.
    pose proof (Hsat1 M ρ HsatΓ) as [ψ [Hin Hsatψ]].
    inversion Hin; subst; clear Hin.
    - apply Hsat2. intros φ Hin'. inversion Hin'; subst; intuition.
    - exists ψ; intuition.
  Qed.

  Lemma LS_Subst : forall Γ Δ, Γ ⊫ Δ -> forall σ, map (subst_formula σ) Γ ⊫ (map (subst_formula σ) Δ).
  Proof.
    intros Γ Δ Hsat σ M ρ HsatΓ.
    unfold Sat_sequent in Hsat.
    assert (H : forall φ, In φ Γ -> (funcomp (eval ρ) σ) ⊨ φ).
    { intros φ Hin. apply strong_form_subst_sanity2.
      apply HsatΓ. apply in_map. apply Hin. }
    apply (Hsat M (funcomp (eval ρ) σ)) in H as [ψ [Hinψ Hsatψ]].
    apply strong_form_subst_sanity2 in Hsatψ.
    exists (subst_formula σ ψ); auto using in_map.
  Qed.

  Lemma LS_NegL : forall Γ Δ φ,
      Γ ⊫ (φ :: Δ) -> (FNeg φ :: Γ) ⊫ Δ.
  Proof.
    intros Γ Δ φ Hsat M ρ HsatΓ.
    assert (HΓ : forall φ, In φ Γ -> ρ ⊨ φ) by intuition.
    apply Hsat in HΓ as [ψ [Hinψ Hsatψ]].
    inversion Hinψ; subst; clear Hinψ.
    - assert (Hsatnψ : ρ ⊨ (FNeg ψ)) by intuition. contradiction.
    - exists ψ; auto.
  Qed.

  Lemma LS_NegR : forall Γ Δ φ,      (* NOTE: uses excluded middle *)
      (φ :: Γ) ⊫ Δ -> Γ ⊫ (FNeg φ :: Δ).
  Proof.
    intros Γ Δ φ Hsatseq M ρ HsatΓ.
    pose proof (classic (ρ ⊨ φ)) as [Hsatφ | Hnsatφ].
    - assert (forall ψ, In ψ (φ :: Γ) -> ρ ⊨ ψ).
      { intros ψ Hin; inversion Hin; subst; intuition. }
      apply Hsatseq in H as [ψ [Hinψ Hsatψ]].
      exists ψ; intuition.
    - exists (FNeg φ); intuition.
  Qed.

  Lemma LS_ImpL : forall Γ Δ φ ψ,    (* NOTE: uses excluded middle *)
      Γ ⊫ (φ :: Δ) -> (ψ :: Γ) ⊫ Δ -> (FImp φ ψ :: Γ) ⊫ Δ.
  Proof.
    intros Γ Δ φ ψ Hsatseq1 Hsatseq2 M ρ HsatΓ.
    assert (HΓ : forall ξ, In ξ Γ -> ρ ⊨ ξ) by intuition;
      apply Hsatseq1 in HΓ as [ξ [Hinξ Hsatξ]].
    inversion Hinξ; subst; clear Hinξ.
    - pose proof (classic (ρ ⊨ ψ)) as [Hsatψ | Hnsatψ].
      + assert (HΓ : forall γ, In γ (ψ :: Γ) -> ρ ⊨ γ) by (intros γ Hinγ; inversion Hinγ; subst; intuition);
          apply Hsatseq2 in HΓ. exact HΓ.
      + assert (Himp : ρ ⊨ (FImp ξ ψ)) by intuition. cbn in Himp.
        apply Himp in Hsatξ; contradiction.
    - exists ξ; auto.
  Qed.

  Lemma LS_ImpR : forall Γ Δ φ ψ,    (* NOTE: uses excluded middle *)
      (φ :: Γ) ⊫ (ψ :: Δ) -> Γ ⊫ (FImp φ ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ Hsatseq M ρ HsatΓ.
    pose proof (classic (ρ ⊨ φ)) as [Hsatφ | Hnsatφ].
    - assert (H: forall ξ, In ξ (φ :: Γ) -> ρ ⊨ ξ) by (intros ξ Hinξ; inversion Hinξ; subst; intuition);
        apply Hsatseq in H as [ξ [Hinξ Hsatξ]].
      inversion Hinξ; subst; clear Hinξ.
      + exists (FImp φ ξ); cbn; intuition.
      + exists ξ; intuition.
    - exists (FImp φ ψ); cbn; intuition.
  Qed.
    
  Lemma LS_AllL : forall Γ Δ φ t,
      (subst_formula (t .: ids) φ :: Γ) ⊫ Δ ->
      (FAll φ :: Γ) ⊫ Δ.
  Proof.
    intros Γ Δ φ t Hsatprem M ρ HsatΓ.    
  Admitted.
    
  Lemma LS_AllR : forall Γ Δ φ,
      (shift_formulas Γ) ⊫ (φ :: shift_formulas Δ) ->
      Γ ⊫ (FAll φ :: Δ).
  Proof.
    intros Γ Δ φ Hsat M ρ HsatΓ.
    unfold Sat_sequent in Hsat.
  Admitted.

  
  Lemma soundness : forall Γ Δ, LKID (Γ ⊢ Δ) -> Γ ⊫ Δ.
  Proof.
    intros Γ Δ Hlkid.
    induction Hlkid; intros M ρ Hsat.
    - apply LS_Ax with Γ0 φ; auto.
    - apply LS_Wk with Γ' Δ' Γ0; auto.
    - apply LS_Cut with Γ0 φ; auto.
    - eapply LS_Subst; eauto.
    - eapply LS_NegL; eauto.
    - eapply LS_NegR; eauto.
    - eapply LS_ImpL; eauto.
    - eapply LS_ImpR; eauto.
    - eapply LS_AllL; eauto.
    - eapply LS_AllR; eauto.
  Admitted.

  
End soundness.


