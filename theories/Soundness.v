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

  Notation "Γ '⊫S' Δ" := (forall (M : structure Σ), standard_model Σ Φ M -> forall (ρ : env M), @Sat_sequent _ M ρ (mkSeq Γ Δ))
                           (no associativity, at level 10).

  Lemma Tarski_implies_Standard : forall Γ Δ, Γ ⊫ Δ -> Γ ⊫S Δ.
  Proof.
    intuition.
  Qed.

  Lemma LS_Ax : forall Γ Δ φ, In φ Γ -> In φ Δ -> Γ ⊫S Δ.
  Proof.
    intros Γ Δ φ Hin1 Hin2 M Hstandard ρ Hsat.
    exists φ; intuition.
  Qed.

  Lemma LS_Wk : forall Γ' Δ' Γ Δ, Γ' ⊆ Γ -> Δ' ⊆ Δ ->
                             Γ' ⊫S Δ' -> Γ ⊫S Δ.
  Proof.
    intros Γ' Δ' Γ Δ HsubsΓ HsubsΔ Hsat M Hstandard ρ HsatΓ.
    assert (HsatΓ' : forall φ, In φ Γ' -> Sat ρ φ) by intuition.
    apply Hsat in HsatΓ' as [ψ [HinΔ' Hsatψ]].
    exists ψ; auto. auto.
  Qed.

  Lemma LS_Cut : forall Γ Δ φ, Γ ⊫S (φ :: Δ) -> (φ :: Γ) ⊫S Δ -> Γ ⊫S Δ.
  Proof.
    intros Γ Δ φ Hsat1 Hsat2 M Hstandard ρ HsatΓ.
    pose proof (Hsat1 M Hstandard ρ HsatΓ) as [ψ [Hin Hsatψ]].
    inversion Hin; subst; clear Hin.
    - apply Hsat2; auto. intros φ Hin'. inversion Hin'; subst; intuition.
    - exists ψ; intuition.
  Qed.

  Lemma LS_Subst : forall Γ Δ, Γ ⊫S Δ -> forall σ, map (subst_formula σ) Γ ⊫S (map (subst_formula σ) Δ).
  Proof.
    intros Γ Δ Hsat σ M Hstandard ρ HsatΓ.
    unfold Sat_sequent in Hsat.
    assert (H : forall φ, In φ Γ -> (funcomp (eval ρ) σ) ⊨ φ).
    { intros φ Hin. apply strong_form_subst_sanity2.
      apply HsatΓ. apply in_map. apply Hin. }
    apply (Hsat M Hstandard (funcomp (eval ρ) σ)) in H as [ψ [Hinψ Hsatψ]].
    apply strong_form_subst_sanity2 in Hsatψ.
    exists (subst_formula σ ψ); auto using in_map.
  Qed.

  Lemma LS_NegL : forall Γ Δ φ,
      Γ ⊫S (φ :: Δ) -> (FNeg φ :: Γ) ⊫S Δ.
  Proof.
    intros Γ Δ φ Hsat M Hstandard ρ HsatΓ.
    assert (HΓ : forall φ, In φ Γ -> ρ ⊨ φ) by intuition.
    apply Hsat in HΓ as [ψ [Hinψ Hsatψ]].
    inversion Hinψ; subst; clear Hinψ.
    - assert (Hsatnψ : ρ ⊨ (FNeg ψ)) by intuition. contradiction.
    - exists ψ; auto.
    - auto.
  Qed.

  Lemma LS_NegR : forall Γ Δ φ,      (* NOTE: uses excluded middle *)
      (φ :: Γ) ⊫S Δ -> Γ ⊫S (FNeg φ :: Δ).
  Proof.
    intros Γ Δ φ Hsatseq M Hstandard ρ HsatΓ.
    pose proof (classic (ρ ⊨ φ)) as [Hsatφ | Hnsatφ].
    - assert (forall ψ, In ψ (φ :: Γ) -> ρ ⊨ ψ).
      { intros ψ Hin; inversion Hin; subst; intuition. }
      apply Hsatseq in H as [ψ [Hinψ Hsatψ]]; auto.
      exists ψ; intuition.
    - exists (FNeg φ); intuition.
  Qed.

  Lemma LS_ImpL : forall Γ Δ φ ψ,
      Γ ⊫S (φ :: Δ) -> (ψ :: Γ) ⊫S Δ -> (FImp φ ψ :: Γ) ⊫S Δ.
  Proof.
    intros Γ Δ φ ψ Hsatseq1 Hsatseq2 M Hstandard ρ HsatΓ.
    assert (Himpsat : ρ ⊨ (FImp φ ψ)) by intuition.
    cbn in Himpsat.
    assert (HΓ : forall ξ, In ξ Γ -> ρ ⊨ ξ) by intuition;
      apply Hsatseq1 in HΓ as [ξ [Hinξ Hsatξ]].
    inversion Hinξ; subst; clear Hinξ; auto.
    - apply Himpsat in Hsatξ.
      assert (H : forall γ, In γ (ψ :: Γ) -> ρ ⊨ γ) by
        (intros γ Hin; inversion Hin; subst; intuition);
        apply Hsatseq2 in H; auto.
    - exists ξ; auto.
    - auto.
  Qed.

  Lemma LS_ImpR : forall Γ Δ φ ψ,    (* NOTE: uses excluded middle *)
      (φ :: Γ) ⊫S (ψ :: Δ) -> Γ ⊫S (FImp φ ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ Hsatseq M Hstandard ρ HsatΓ.
    pose proof (classic (ρ ⊨ φ)) as [Hsatφ | Hnsatφ].
    - assert (H: forall ξ, In ξ (φ :: Γ) -> ρ ⊨ ξ) by (intros ξ Hinξ; inversion Hinξ; subst; intuition);
        apply Hsatseq in H as [ξ [Hinξ Hsatξ]].
      inversion Hinξ; subst; clear Hinξ.
      + exists (FImp φ ξ); cbn; intuition.
      + exists ξ; intuition.
      + auto.
    - exists (FImp φ ψ); cbn; intuition.
  Qed.
    
  Lemma LS_AllL : forall Γ Δ φ t,    (* NOTE: uses excluded middle *)
      (subst_formula (t .: ids) φ :: Γ) ⊫S Δ ->
      (FAll φ :: Γ) ⊫S Δ.
  Proof.
    intros Γ Δ φ t Hsatprem M Hstandard ρ HsatΓ.
    assert (Hφ : ρ ⊨ (FAll φ)) by intuition. cbn in Hφ.
    pose proof (classic (ρ ⊨ (subst_formula (t .: ids) φ))) as [H | H].
    - assert (HΓ : forall ψ, In ψ (subst_formula (t .: ids) φ :: Γ) -> ρ ⊨ ψ) by (intros ψ Hin; inversion Hin; subst; intuition);
        apply Hsatprem in HΓ as [ψ [Hinψ Hsatψ]]. exists ψ; intuition. auto.
    - rewrite strong_form_subst_sanity2 in H. Search funcomp eval. specialize Hφ with (eval ρ t).
      asimpl in *. contradiction.
  Qed.

  Lemma LS_ExL : forall Γ Δ φ,       (* NOTE: uses excluded middle and dependent functional extensionality *)
      (φ :: shift_formulas Γ) ⊫S (shift_formulas Δ) ->
      (FExist φ :: Γ) ⊫S Δ.
  Proof.
    intros Γ Δ φ Hsat M Hstandard ρ Hsat1.
    assert (Hexφ : ρ ⊨ (FExist φ)) by intuition.
    cbn in Hexφ. apply not_all_not_ex in Hexφ.
    destruct Hexφ as [d Hd].
    assert (HΓ : forall ψ, In ψ (shift_formulas Γ) -> (d .: ρ) ⊨ ψ).
    { intros ψ Hin. apply in_map_iff in Hin as [ξ [Heq Hinξ]]; subst.
      unfold shift_formula. rewrite strong_form_subst_sanity2.
      apply Hsat1. now right. }
    assert (H : forall ψ, In ψ (φ :: shift_formulas Γ) -> (d .: ρ) ⊨ ψ) by (intros ψ Hin; inversion Hin; subst; intuition).
    apply Hsat in H; auto.
    destruct H as [ψ [Hinψ Hsatψ]].
    apply in_map_iff in Hinψ as [ξ [Heq Hinξ]]; subst. exists ξ; split. assumption.
    unfold shift_formula in Hsatψ. rewrite strong_form_subst_sanity2 in Hsatψ. assumption.
  Qed.

  Lemma LS_ExR : forall Γ Δ φ t,
      Γ ⊫S (subst_formula (t .: ids) φ :: Δ) ->
      Γ ⊫S (FExist φ :: Δ).
  Proof.
    intros Γ Δ φ t Hsatseq M Hstandard ρ HsatΓ.
    apply Hsatseq in HsatΓ as [ψ [Hinψ Hsatψ]]; auto.
    inversion Hinψ; subst; clear Hinψ.
    - exists (FExist φ); split. now left. cbn.
      rewrite strong_form_subst_sanity2 in Hsatψ.
      intros H. specialize H with (eval ρ t).
      apply H. rewrite scons_comp in Hsatψ. auto.
    - exists ψ; intuition.
  Qed.

  Lemma Semantic_NegAllNegAll : forall Γ Δ φ,
      Γ ⊫S (FNeg (FExist (FNeg φ)) :: Δ) ->
      Γ ⊫S (FAll φ :: Δ).
  Proof.
    unfold FExist. intros Γ Δ φ Hsatseq M Hstandard ρ HsatΓ.
    apply Hsatseq in HsatΓ; auto.
    destruct HsatΓ as [ψ [Hinψ Hsatψ]].
    inversion Hinψ; subst; clear Hinψ.
    - exists (FAll φ); split. now left. cbn in Hsatψ. apply NNPP in Hsatψ.
      intros d; specialize Hsatψ with d. now apply NNPP in Hsatψ.
    - exists ψ; split. now right. assumption.
  Qed.
  
  Lemma LS_AllR : forall Γ Δ φ,
      (shift_formulas Γ) ⊫S (φ :: shift_formulas Δ) ->
      Γ ⊫S (FAll φ :: Δ).
  Proof.
    intros Γ Δ φ Hsatseq.
    apply Semantic_NegAllNegAll. apply LS_NegR. apply LS_ExL. apply LS_NegL.
    apply Hsatseq.
  Qed.

  Notation "'{' x ',' y '}'" := (existT _ x y) (only printing).
  Lemma LS_IndL : forall Γ Δ pr σ,   (* NOTE: uses excluded middle *)
      Φ pr ->
      (forall Q us, In (existT _ Q us) (preds pr) ->
               Γ ⊫S (FPred Q (V.map (subst_term σ) us) :: Δ)) ->
      (forall P ts, In (existT _ P ts) (indpreds pr) ->
               Γ ⊫S (FIndPred P (V.map (subst_term σ) ts) :: Δ)) ->
      Γ ⊫S (FIndPred (indcons pr) (V.map (subst_term σ) (indargs pr)) :: Δ).
  Proof.
    intros Γ Δ pr σ HΦ Hpreds Hindpreds M Hstandard ρ HsatΓ.
    cbn beta in Hpreds, Hindpreds.
    pose proof (classic (exists ψ, In ψ Δ /\ ρ ⊨ ψ)) as [HΔ | HΔ].
    - destruct HΔ as [ψ [Hinψ Hsatψ]]; exists ψ; intuition.
    - assert (Hpreds' : forall Q us, In (existT _ Q us) (preds pr) -> ρ ⊨ (FPred Q (V.map (subst_term σ) us))).
      { intros Q us Hin. pose proof (Hpreds Q us Hin M Hstandard ρ HsatΓ) as [ξ [Hinξ Hsatξ]].
        inversion Hinξ; subst; clear Hinξ.
        - assumption.
        - exfalso; apply HΔ; exists ξ; auto. }
      assert (Hindpreds' : forall P ts, In (existT _ P ts) (indpreds pr) -> ρ ⊨ (FIndPred P (V.map (subst_term σ) ts))).
      { intros P ts Hin. pose proof (Hindpreds P ts Hin M Hstandard ρ HsatΓ) as [ξ [Hinξ Hsatξ]].
        inversion Hinξ; subst; clear Hinξ.
        - assumption.
        - exfalso; apply HΔ; exists ξ; auto. }
      cbn in Hpreds', Hindpreds'. exists (FIndPred (indcons pr) (V.map (subst_term σ) (indargs pr))); split. now left.
      apply Hstandard. apply ω_prefixed.
      unfold φ_Φ. unfold φ_P. exists pr. exists (conj eq_refl HΦ). cbn. unfold φ_pr.
      assert (Heq : eval (funcomp (eval ρ) σ) = fun t => eval ρ (subst_term σ t)) by (fext; apply eval_comp).
      exists (funcomp (eval ρ) σ); repeat split.
      + intros Q us Hin. rewrite Heq. rewrite <- V.map_map. apply Hpreds'. assumption.
      + intros P ts Hin. rewrite Heq. apply Hstandard. rewrite <- V.map_map. apply Hindpreds'. assumption.
      + rewrite V.map_map. f_equal. rewrite Heq. reflexivity.
  Qed.
  
  Lemma soundness : forall Γ Δ, @LKID Σ Φ (Γ ⊢ Δ) -> Γ ⊫S Δ.
  Proof.
    intros Γ Δ Hlkid.
    induction Hlkid; intros M Hstandard ρ Hsat.
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
    - eapply LS_IndL; eauto.
  Qed.
End soundness.
