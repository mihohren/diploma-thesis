Require Import Base Syntax Semantics InductiveDefinitions LKID.
From Coq Require Import Logic.Classical.

Notation "Γ ⊢ Δ" := (mkSeq Γ Δ) (at level 61).

Section soundness.
  Context {Σ : signature}.
  Context (Φ : IndDefSet Σ).

  Definition Sat_sequent (s : sequent) : Prop :=
    let '(Γ ⊢ Δ) := s in            
    forall (M : structure Σ), standard_model Φ M -> forall (ρ : env M),
        (forall φ, In φ Γ -> ρ ⊨ φ) -> exists ψ, In ψ Δ /\ ρ ⊨ ψ.

  Notation "Γ '⊫' Δ" := (Sat_sequent (mkSeq Γ Δ))
                           (no associativity, at level 10).

  Lemma LS_Ax : forall Γ Δ φ, In φ Γ -> In φ Δ -> Γ ⊫ Δ.
  Proof.
    intros Γ Δ φ Hin1 Hin2 M Hstandard ρ Hsat.
    exists φ; split; auto.
  Qed.

  Lemma LS_Wk : forall Γ' Δ' Γ Δ, Γ' ⊆ Γ -> Δ' ⊆ Δ ->
                             Γ' ⊫ Δ' -> Γ ⊫ Δ.
  Proof.
    intros Γ' Δ' Γ Δ HsubsΓ HsubsΔ Hsat M Hstandard ρ HsatΓ.
    assert (HsatΓ' : forall φ, In φ Γ' -> Sat ρ φ) by auto.
    apply Hsat in HsatΓ' as [ψ [HinΔ' Hsatψ]]; [ exists ψ | ]; auto.
  Qed.

  Lemma LS_Cut : forall Γ Δ φ, Γ ⊫ (φ :: Δ) -> (φ :: Γ) ⊫ Δ -> Γ ⊫ Δ.
  Proof.
    intros Γ Δ φ Hsat1 Hsat2 M Hstandard ρ HsatΓ.
    pose proof (Hsat1 M Hstandard ρ HsatΓ) as [ψ [Hin Hsatψ]].
    inversion Hin; subst; clear Hin.
    - apply Hsat2; auto. intros φ Hin'. inversion Hin'; subst; auto.
    - exists ψ; auto.
  Qed.

  Lemma LS_Subst : forall Γ Δ, Γ ⊫ Δ -> forall σ, map (subst_formula σ) Γ ⊫ (map (subst_formula σ) Δ).
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
      Γ ⊫ (φ :: Δ) -> (FNeg φ :: Γ) ⊫ Δ.
  Proof.
    intros Γ Δ φ Hsat M Hstandard ρ HsatΓ.
    assert (HΓ : forall φ, In φ Γ -> ρ ⊨ φ) by (intros ε Hin; apply HsatΓ; now right).
    apply Hsat in HΓ as [ψ [Hinψ Hsatψ]].
    inversion Hinψ; subst; clear Hinψ.
    - assert (Hsatnψ : ρ ⊨ (FNeg ψ)) by (apply HsatΓ; now left); contradiction.
    - exists ψ; auto.
    - auto.
  Qed.

  Lemma LS_NegR : forall Γ Δ φ,
      (φ :: Γ) ⊫ Δ -> Γ ⊫ (FNeg φ :: Δ).
  Proof.
    intros Γ Δ φ Hsatseq M Hstandard ρ HsatΓ.
    pose proof (classic (ρ ⊨ φ)) as [Hsatφ | Hnsatφ].
    - assert (forall ψ, In ψ (φ :: Γ) -> ρ ⊨ ψ).
      { intros ψ Hin; inversion Hin; subst; auto. }
      apply Hsatseq in H as [ψ [Hinψ Hsatψ]]; auto.
      exists ψ; split; auto. now right.
    - exists (FNeg φ); split; auto. now left.
  Qed.

  Lemma LS_ImpL : forall Γ Δ φ ψ,
      Γ ⊫ (φ :: Δ) -> (ψ :: Γ) ⊫ Δ -> (FImp φ ψ :: Γ) ⊫ Δ.
  Proof.
    intros Γ Δ φ ψ Hsatseq1 Hsatseq2 M Hstandard ρ HsatΓ.
    assert (Himpsat : ρ ⊨ (FImp φ ψ)) by (apply HsatΓ; now left).
    cbn in Himpsat.
    assert (HΓ : forall ξ, In ξ Γ -> ρ ⊨ ξ) by (intros ξ Hin; apply HsatΓ; now right).
    apply Hsatseq1 in HΓ as [ξ [Hinξ Hsatξ]]; auto.
    inversion Hinξ; subst; clear Hinξ; auto.
    - apply Himpsat in Hsatξ.
      assert (H : forall γ, In γ (ψ :: Γ) -> ρ ⊨ γ).
      { intros γ Hin; destruct Hin; subst; auto. apply HsatΓ; now right. }
        apply Hsatseq2 in H; auto.
    - exists ξ; auto.
  Qed.

  Lemma LS_ImpR : forall Γ Δ φ ψ,
      (φ :: Γ) ⊫ (ψ :: Δ) -> Γ ⊫ (FImp φ ψ :: Δ).
  Proof.
    intros Γ Δ φ ψ Hsatseq M Hstandard ρ HsatΓ.
    pose proof (classic (ρ ⊨ φ)) as [Hsatφ | Hnsatφ].
    - assert (H: forall ξ, In ξ (φ :: Γ) -> ρ ⊨ ξ) by (intros ξ Hinξ; inversion Hinξ; subst; auto);
        apply Hsatseq in H as [ξ [Hinξ Hsatξ]].
      inversion Hinξ; subst; clear Hinξ.
      + exists (FImp φ ξ); cbn; auto.
      + exists ξ; split; auto. now right.
      + auto.
    - exists (FImp φ ψ); cbn; split; auto; intros contra; contradiction.
  Qed.
    
  Lemma LS_AllL : forall Γ Δ φ t,
      (subst_formula (t .: ids) φ :: Γ) ⊫ Δ ->
      (FAll φ :: Γ) ⊫ Δ.
  Proof.
    intros Γ Δ φ t Hsatprem M Hstandard ρ HsatΓ.
    assert (Hφ : ρ ⊨ (FAll φ)) by (apply HsatΓ; now left).
    pose proof (classic (ρ ⊨ (subst_formula (t .: ids) φ))) as [H | H].
    - assert (HΓ : forall ψ, In ψ (subst_formula (t .: ids) φ :: Γ) -> ρ ⊨ ψ).
      { intros ψ Hin; inversion Hin; subst; auto. apply HsatΓ; now right. }
      apply Hsatprem in HΓ as [ψ [Hinψ Hsatψ]]; auto. exists ψ; split; auto.
    - rewrite strong_form_subst_sanity2 in H.
      asimpl in *; cbn in Hφ; specialize Hφ with (eval ρ t).
      contradiction.
  Qed.

  Lemma LS_ExL : forall Γ Δ φ,
      (φ :: shift_formulas Γ) ⊫ (shift_formulas Δ) ->
      (FExist φ :: Γ) ⊫ Δ.
  Proof.
    intros Γ Δ φ Hsat M Hstandard ρ Hsat1.
    assert (Hexφ : ρ ⊨ (FExist φ)) by (apply Hsat1; now left).
    cbn in Hexφ. apply not_all_not_ex in Hexφ.
    destruct Hexφ as [d Hd].
    assert (HΓ : forall ψ, In ψ (shift_formulas Γ) -> (d .: ρ) ⊨ ψ).
    { intros ψ Hin. apply in_map_iff in Hin as [ξ [Heq Hinξ]]; subst.
      unfold shift_formula_by. rewrite strong_form_subst_sanity2.
      apply Hsat1. now right. }
    assert (H : forall ψ, In ψ (φ :: shift_formulas Γ) -> (d .: ρ) ⊨ ψ) by (intros ψ Hin; inversion Hin; subst; intuition).
    apply Hsat in H; auto.
    destruct H as [ψ [Hinψ Hsatψ]].
    apply in_map_iff in Hinψ as [ξ [Heq Hinξ]]; subst. exists ξ; split. assumption.
    unfold shift_formula_by in Hsatψ.
    rewrite strong_form_subst_sanity2 in Hsatψ. assumption.
  Qed.

  Lemma LS_ExR : forall Γ Δ φ t,
      Γ ⊫ (subst_formula (t .: ids) φ :: Δ) ->
      Γ ⊫ (FExist φ :: Δ).
  Proof.
    intros Γ Δ φ t Hsatseq M Hstandard ρ HsatΓ.
    apply Hsatseq in HsatΓ as [ψ [Hinψ Hsatψ]]; auto.
    inversion Hinψ; subst; clear Hinψ.
    - exists (FExist φ); split. now left. cbn.
      rewrite strong_form_subst_sanity2 in Hsatψ.
      intros H. specialize H with (eval ρ t).
      apply H. rewrite scons_comp in Hsatψ. auto.
    - exists ψ; split; auto. now right.
  Qed.

  Lemma Semantic_NegExistNegAll : forall Γ Δ φ,
      Γ ⊫ (FNeg (FExist (FNeg φ)) :: Δ) ->
      Γ ⊫ (FAll φ :: Δ).
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
      (shift_formulas Γ) ⊫ (φ :: shift_formulas Δ) ->
      Γ ⊫ (FAll φ :: Δ).
  Proof.
    intros Γ Δ φ Hsatseq.
    apply Semantic_NegExistNegAll. apply LS_NegR. apply LS_ExL. apply LS_NegL.
    apply Hsatseq.
  Qed.
  Import SigTNotations. 

  Lemma LS_IndR : forall Γ Δ pr σ,   (* NOTE: uses excluded middle *)
      Φ pr ->
      (forall Q us, In (Q; us) (preds pr) ->
               Γ ⊫ (FPred Q (V.map (subst_term σ) us) :: Δ)) ->
      (forall P ts, In (P; ts) (indpreds pr) ->
               Γ ⊫ (FIndPred P (V.map (subst_term σ) ts) :: Δ)) ->
      Γ ⊫ (FIndPred (indcons pr) (V.map (subst_term σ) (indargs pr)) :: Δ).
  Proof.
    intros Γ Δ pr σ HΦ Hpreds Hindpreds M Hstandard ρ HsatΓ.
    cbn beta in Hpreds, Hindpreds.
    pose proof (classic (exists ψ, In ψ Δ /\ ρ ⊨ ψ)) as [HΔ | HΔ].
    - destruct HΔ as [ψ [Hinψ Hsatψ]]; exists ψ; split; auto. now right.
    - assert (Hpreds' : forall Q us, In (Q; us) (preds pr) -> ρ ⊨ (FPred Q (V.map (subst_term σ) us))).
      { intros Q us Hin. pose proof (Hpreds Q us Hin M Hstandard ρ HsatΓ) as [ξ [Hinξ Hsatξ]].
        inversion Hinξ; subst; clear Hinξ.
        - assumption.
        - exfalso; apply HΔ; exists ξ; auto. }
      assert (Hindpreds' : forall P ts, In (P; ts) (indpreds pr) -> ρ ⊨ (FIndPred P (V.map (subst_term σ) ts))).
      { intros P ts Hin. pose proof (Hindpreds P ts Hin M Hstandard ρ HsatΓ) as [ξ [Hinξ Hsatξ]].
        inversion Hinξ; subst; clear Hinξ.
        - assumption.
        - exfalso; apply HΔ; exists ξ; auto. }
      cbn in Hpreds', Hindpreds'. exists (FIndPred (indcons pr) (V.map (subst_term σ) (indargs pr))); split. now left.
      apply Hstandard. apply φ_Φ_ω_least_prefixed.
      exists pr, (conj eq_refl HΦ); cbn.
      assert (Heq : eval (funcomp (eval ρ) σ) = fun t => eval ρ (subst_term σ t)) by (fext; apply eval_comp).
      exists (funcomp (eval ρ) σ); repeat split.
      + intros Q us Hin. rewrite Heq. rewrite <- V.map_map. apply Hpreds'. assumption.
      + intros P ts Hin. rewrite Heq. apply Hstandard. rewrite <- V.map_map. apply Hindpreds'. assumption.
      + rewrite V.map_map. f_equal. rewrite Heq. reflexivity.
  Qed.


  Axiom Φfin : exists prods : list (production Σ), forall pr, Φ pr <-> In pr prods.
  Axiom mutdepdec : forall Pi Pj, {mutually_dependent Φ Pi Pj} + {~mutually_dependent Φ Pi Pj}.
  Axiom e : forall (M : structure Σ) n, vec M n.
  Axiom premstardec : forall Pi Pj, {Prem_star Φ Pi Pj} + {~Prem_star Φ Pi Pj}.
  
  Lemma LS_IndL : forall Γ Δ
                    (Pj : IndPredS Σ) (u : vec _ (indpred_ar Pj))
                    (z_i : forall P, vec var (indpred_ar P))
                    (z_i_nodup : forall P, VecNoDup (z_i P))
                    (G_i : IndPredS Σ -> formula Σ)
                    (HG : forall Pi, ~@mutually_dependent Σ Φ Pi Pj ->
                                G_i Pi = FIndPred Pi (V.map var_term (z_i Pi))),
      let maxΓ := max_fold (map some_var_not_in_formula Γ) in
      let maxΔ := max_fold (map some_var_not_in_formula Δ) in
      let maxP := some_var_not_in_formula (FIndPred Pj u) in
      let shift_factor := max maxP (max maxΓ maxΔ) in
      let Fj := subst_formula (finite_subst (z_i Pj) u) (G_i Pj) in
      let minor_premises :=
        (forall pr (HΦ : Φ pr) (Hdep : mutually_dependent Φ (indcons pr) Pj),
            let Qs := shift_formulas_by shift_factor (FPreds_from_preds (preds pr)) in
            let Gs := map (fun '(P; args) =>
                             let shifted_args := V.map (shift_term_by shift_factor) args in
                             let σ := finite_subst (z_i P) (shifted_args) in
                             let G := G_i P in
                             subst_formula σ G)
                        (indpreds pr) in
            let Pi := indcons pr in
            let ty := V.map (shift_term_by shift_factor) (indargs pr) in
            let Fi := subst_formula (finite_subst (z_i Pi) ty) (G_i Pi) in
            (Qs ++ Gs ++ Γ) ⊫ (Fi :: Δ))
      in
      minor_premises ->
      (Fj :: Γ) ⊫ Δ ->
      (FIndPred Pj u :: Γ) ⊫ Δ.
  Proof.
    intros Γ Δ Pj u z_i z_i_nodup G_i HmutdepG.
    intros maxΓ maxΔ maxP shift_factor Fj minor_premises.
    intros Hminor Hindhyp M Hstandard ρ Hpremises.
    assert (Hsat1 : forall ψ, In ψ Γ -> ρ ⊨ ψ).
    { intros ψ Hin; apply Hpremises; now right. }
    assert (Hsat2: ρ ⊨ (FIndPred Pj u)).
    { apply Hpremises; now left. }
    destruct (classic (exists ψ, In ψ Δ /\ ρ ⊨ ψ)) as [Hyes | Hno].
    { assumption. }
    assert (HΔunsat : forall ψ, In ψ Δ -> ~ ρ ⊨ ψ).
    { intros ψ Hin Hsat. apply Hno; now exists ψ. } clear Hno.    
    destruct Φfin as [prods Hprods].
    set (xlist := map (fun v => v + shift_factor) (nodup Nat.eq_dec (concat (map (fun pr =>
                     if mutdepdec (indcons pr) Pj then vars_of_production pr else nil
                                          ) prods)))).
    set (evec := e M (length xlist)).
    set (xvec := V.of_list xlist).
    assert (Hxvar : forall xvar, In xvar xlist -> xvar >= shift_factor).
    { intros xvar Hinx. subst xlist; apply in_map_iff in Hinx as [xvar' [Heq Hin]]. lia. }
    assert (Γfvx : forall ψ xvar, In ψ Γ -> In xvar xlist -> ~ FV ψ xvar).
    { intros ψ xvar Hinψ Hinx Hfv.
      assert (Hge : xvar >= shift_factor) by auto.
      assert (Hge1: xvar >= maxΓ) by lia.
      assert (xvar >= some_var_not_in_formula ψ).
      { unfold ">=" in *. transitivity maxΓ; auto. subst maxΓ; apply max_fold_ge; auto using in_map. }
      apply lt_some_var_not_in_term_not_FV in H.
      contradiction. }
    assert (Δfvx : forall ψ xvar, In ψ Δ -> In xvar xlist -> ~ FV ψ xvar).
    { intros ψ xvar Hinψ Hinx Hfv.
      assert (Hge : xvar >= shift_factor) by auto.
      assert (Hge1: xvar >= maxΔ) by lia.
      assert (xvar >= some_var_not_in_formula ψ).
      { unfold ">=" in *. transitivity maxΔ; auto. subst maxΔ; apply max_fold_ge; auto using in_map. }
      apply lt_some_var_not_in_term_not_FV in H.
      contradiction. }
    set (ρ' := env_finite_subst ρ xvec evec).
    assert (HsatΓ' : forall ψ, In ψ Γ -> ρ' ⊨ ψ).
    { intros ψ Hin. apply form_subst_sanity1_vec; auto.
      intros x Hinx. apply Γfvx; auto. now apply vec_In_of_list. }
    assert (HunsatΔ' : forall ψ, In ψ Δ -> ~ ρ' ⊨ ψ).
    { intros ψ Hin Hsat'. apply form_subst_sanity1_vec in Hsat'.
      - specialize (HΔunsat ψ Hin); contradiction.
      - intros x Hinx. apply Δfvx; auto. now apply vec_In_of_list. }
    set (Y := fun P v =>
                if premstardec Pj P
                then env_finite_subst ρ' (z_i P) v ⊨ (G_i P)
                else True).
    enough (HYpref : prefixed Φ M Y).
    { assert (Hωsubinterp : forall P v, φ_Φ_ω Φ M P v -> Y P v).
      { intros P v Hω. now apply (proj2 (φ_Φ_ω_least_prefixed Φ M) ). }
      destruct (classic (ρ' ⊨ Fj)) as [HsatFj | HunsatFj].
      { assert (forall ψ, In ψ (Fj :: Γ) -> ρ' ⊨ ψ).
        { intros ψ; inversion 1; subst; auto. }
        apply (Hindhyp M Hstandard ρ') in H as [ψ [Hin HsatΔ']].
        exists ψ; split; auto. apply form_subst_sanity1_vec in HsatΔ'; auto.
        intros x Hinx; apply Δfvx; auto. now apply vec_In_of_list. }
      subst Fj. rewrite form_subst_sanity2_vec in HunsatFj.
      assert (HnotYju : ~ Y Pj (V.map (eval ρ') u)).
      { intros HYju. subst Y. cbn in HYju.
        destruct (premstardec Pj Pj). contradiction. apply n. apply Prem_star_refl. }
      assert (Hnotωju : ~ φ_Φ_ω Φ M Pj (V.map (eval ρ') u)).
      { intros Hω. apply HnotYju. now apply (proj2 (φ_Φ_ω_least_prefixed Φ M)). }
      assert (forall xvar, In xvar xlist -> xvar >= maxP).
      { intros xvar Hinx. unfold ge. transitivity shift_factor. lia.
        unfold ">=" in *. auto. }
      assert (forall xvar uu, In xvar xlist -> V.In uu u -> ~ TV uu xvar).
      { intros xvar uu Hinx Hinu Htv.
        assert (xvar >= maxP) by auto; unfold ">=" in *. subst maxP.
        cbn in H0. admit. }
      assert (Hevaleq: V.map (eval ρ') u = V.map (eval ρ) u).
      { admit. }
      rewrite Hevaleq in Hnotωju. cbn in Hsat2. apply Hstandard in Hsat2. contradiction.
    }
    intros P v Hω. unfold Y.
    destruct (premstardec Pj P) as [HpremstarPjP | HnotpremstarPjP].
    2: { constructor. }
    destruct (premstardec P Pj) as [HpremstarPPj | HnotpremstarPPj].
    2: { assert (Hnotmutdep : ~ mutually_dependent Φ Pj P).
         { intros [H1 H2]; contradiction. }
         rewrite HmutdepG.
         2: { intros H. apply mutually_dependent_symm in H; contradiction. }  
  Admitted.    
    
  Theorem soundness : forall Γ Δ, LKID Φ (Γ ⊢ Δ) -> Γ ⊫ Δ.
  Proof.
    intros Γ Δ Hlkid.
    induction Hlkid; intros M Hstandard ρ Hsat.
    - apply LS_Ax with Γ0 φ; auto.
    - apply LS_Wk with Γ' Δ' Γ0; auto.
    - apply LS_Cut with Γ0 φ; auto.
    - now apply (LS_Subst Γ0 Δ0 IHHlkid σ M Hstandard ρ).
    - eapply LS_NegL; eauto.
    - eapply LS_NegR; eauto.
    - eapply LS_ImpL; eauto.
    - eapply LS_ImpR; eauto.
    - eapply LS_AllL; eauto.
    - eapply LS_AllR; eauto.
    - eapply LS_IndL; eauto.
    - eapply LS_IndR; eauto.
  Admitted.
End soundness.
