From CFOLID Require Import Base Syntax Semantics InductiveDefinitions LKID.

(* Note: some LS lemmas rely on axioms. *)

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

  Lemma LS_IndR : forall Γ Δ pr σ,
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
  Axiom Minhab : forall M, {e : M | True}.
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
    enough (He : (forall {n}, vec M n) -> exists ψ, In ψ Δ /\ ρ ⊨ ψ).
    { apply He. induction n. apply V.nil. destruct (Minhab M) as [eM _].
      apply V.cons. apply eM. apply IHn. }
    intros e.
                
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
    set (evec := e (length xlist)).
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
      { intros xvar uu Hinx Hinu.
        assert (xvar >= maxP) by auto; unfold ">=" in *. subst maxP.
        cbn in H0.
        apply lt_some_var_not_in_term_not_TV.
        pose proof (vec_max_fold_ge (V.map some_var_not_in_term u)).
        assert (vec_max_fold (V.map some_var_not_in_term u) <= xvar) by lia.
        transitivity (vec_max_fold (V.map some_var_not_in_term u)); auto.
        apply H1. now apply vec_in_map.
      }
      assert (Hevaleq: V.map (eval ρ') u = V.map (eval ρ) u).
      { apply V.map_ext_in. intros st Hinst. subst ρ'.
        symmetry. apply eval_env_subst_unused_vec.
        intros xvar Hinxvar; apply H0; auto. now rewrite vec_In_of_list. }
      rewrite Hevaleq in Hnotωju. cbn in Hsat2. apply Hstandard in Hsat2. contradiction.
    }
    unfold prefixed, subinterp. intros P v HY. unfold Y.
    destruct (premstardec Pj P) as [HpremstarPjP | HnotpremstarPjP].
    2: { constructor. }
    destruct (premstardec P Pj) as [HpremstarPPj | HnotpremstarPPj].
    2: { assert (Hnotmutdep : ~ mutually_dependent Φ Pj P).
         { intros [H1 H2]; contradiction. }
         rewrite HmutdepG.
         2: { intros H. apply mutually_dependent_symm in H; contradiction. }
         assert (Yω : forall v, Y P v <-> φ_Φ_ω Φ M P v).
         { intros v'. unfold Y. destruct (premstardec Pj P); try contradiction.
           rewrite HmutdepG; try (intros Hmutdep;
                                  apply mutually_dependent_symm in Hmutdep; contradiction).
           cbn. rewrite eval_finite_subst_on_args; auto. }
         
         cbn. rewrite eval_finite_subst_on_args; auto. apply Hstandard.
         destruct HY as (pr & [Heq HΦ] & ρ'' & Hpreds & Hindpreds & Heval).
         subst; cbn in Heval; subst.
         assert (Hpremindpreds : forall Pk,
                    In Pk (map (fun p => p.1) (indpreds pr)) ->
                    Prem_star Φ Pj Pk /\ ~Prem_star Φ Pk Pj).
         { intros Pk HinPk; split.
           - apply Prem_star_trans with (indcons pr); auto. apply Relation_Operators.rt_step.
             unfold Prem. exists pr; repeat split; auto.
             apply in_map_iff in HinPk as ([Pkk ts] & Heq & Hin).
             cbn in Heq; subst. now (exists ts).
           - intros HpremstarPkPj. apply HnotpremstarPPj. constructor 3 with Pk.
             + constructor. exists pr; repeat split. auto.
               apply in_map_iff in HinPk as ([Pkk ts] & Heq & Hin).
               cbn in Heq; subst. now (exists ts).
             + assumption. }
         
         assert (Hindpredsω : forall Pk,
                    In Pk (map (fun p => p.1) (indpreds pr)) ->
                    forall v, Y Pk v <-> φ_Φ_ω Φ M Pk v).
         { intros Pk Hin v. pose proof Hin as Hin1.
           apply in_map_iff in Hin as ([Pkk ts] & Heq & Hin).
           cbn in Heq; subst. unfold Y.
           rewrite HmutdepG.
           2: { intros [H1 H2]. specialize (Hpremindpreds Pk). apply Hpremindpreds; auto. }
           destruct (premstardec Pj Pk).
           - cbn. rewrite eval_finite_subst_on_args; auto.
           - specialize (Hpremindpreds Pk). exfalso. now apply n, Hpremindpreds. }
         apply φ_Φ_ω_least_prefixed.
         exists pr, (conj eq_refl HΦ), ρ''; intuition.
         apply Hindpredsω. { apply in_map_iff. exists (P; ts); split; auto. }
         apply Hindpreds. assumption. }
    
    assert (HmutdepPPj : mutually_dependent Φ P Pj).
    { now split. }
    
    destruct HY as (pr & [Heq HΦ] & ρ'' & Hpreds & Hindpreds & Heval).
    subst P; cbn in Heval.
    unfold Y in Hindpreds. subst v.
    
    specialize (Hminor pr HΦ HmutdepPPj).
    remember (shift_formulas_by shift_factor (FPreds_from_preds (preds pr))) as Qs.
    remember (list_map
                (λ '(P; args),
                  let shifted_args := V.map (shift_term_by shift_factor) args in
                  let σ := finite_subst (z_i P) shifted_args in let G := G_i P in subst_formula σ G)
                (indpreds pr)) as Gs.
    remember (V.map (shift_term_by shift_factor) (indargs pr)) as ty.
    remember (subst_formula (finite_subst (z_i (indcons pr)) ty) (G_i (indcons pr))) as Fi.
    cbn zeta in Hminor.
    rewrite <- HeqFi in Hminor.

    assert (Hρ'e : V.map (eval ρ') (V.map var_term xvec) = evec).
    { unfold ρ'. rewrite eval_finite_subst_on_args; auto. subst xvec.
      rewrite <- ListNoDup_iff_VecNoDup. unfold xlist. apply NoDup_injective_map.
      - intros x y _ _ Heq. lia.
      - apply NoDup_nodup. }

    assert (Himplies : (forall Q, In Q Qs -> ρ' ⊨ Q) ->
                       (forall G, In G Gs -> ρ' ⊨ G) ->
                       ρ' ⊨ Fi).
    { intros HQ HG. destruct (classic (ρ' ⊨ Fi)) as [HsatFi | HunsatFi]; auto.
      exfalso. specialize (Hminor M Hstandard ρ').
      assert (H1 : forall φ, In φ (Qs ++ Gs ++ Γ) -> ρ' ⊨ φ).
      { intros φ Hin. apply in_app_or in Hin as [HinQ | Hinrest]; auto.
        apply in_app_or in Hinrest as [HinG | HinΓ]; auto. }
      apply Hminor in H1 as [ψ [[HF | HinΔ] Hsat]].
      - subst; contradiction.
      - apply HunsatΔ' in HinΔ. contradiction. }
    subst Qs; subst Gs; subst Fi; subst ty.
    unfold shift_formulas_by in Himplies.
    rewrite form_subst_sanity2_vec in Himplies.
    assert (Himplies1 : (forall Q ts, In (Q; ts) (preds pr) ->
                                 funcomp (eval ρ') (funcomp var_term (fun x => shift_factor + x))
                                   ⊨ (FPred Q ts))
                        -> (forall P us, In (P; us) (indpreds pr) ->
                                   env_finite_subst ρ'
                                     (z_i P)
                                     (V.map (eval ρ') (V.map (shift_term_by shift_factor) us))
                                     ⊨ (G_i P))
                        -> env_finite_subst ρ' (z_i (indcons pr))
                            (V.map (eval ρ') (V.map (shift_term_by shift_factor) (indargs pr)))
                            ⊨ (G_i (indcons pr))).
    { intros Qs Gs.
      apply Himplies.
      - intros Q Hin. apply in_map_iff in Hin as [φ [Heq Hin]].
        subst. apply in_map_iff in Hin as [[Q ts] [Heq1 Hin1]]. subst.
        unfold shift_formula_by. rewrite strong_form_subst_sanity2.
        now apply Qs.
      - intros G Hin. apply in_map_iff in Hin as [[P us] [Heq Hin]].
        subst. rewrite form_subst_sanity2_vec. now apply Gs. }
    assert (Hpremindpreds : forall Pk,
               In Pk (map (fun p => p.1) (indpreds pr)) ->
               Prem_star Φ Pj Pk).
    { intros Pk Hin. apply in_map_iff in Hin as [[P ts] [Heq Hin]]; subst; cbn.
      assert (Hprem: Prem Φ (indcons pr) P).
      { exists pr; split; auto; split; auto. now (exists ts). }
      constructor 3 with (indcons pr).
      - apply HpremstarPjP.
      - constructor. apply Hprem. }

    assert (Hindpreds1 : forall Pk ts, In (Pk; ts) (indpreds pr) ->
                                  env_finite_subst ρ' (z_i Pk) (V.map (eval ρ'') ts) ⊨ (G_i Pk)).
    { intros Pk ts Hin. specialize (Hpremindpreds Pk).
      assert (In Pk (map (fun p => p.1) (indpreds pr))).
      { apply in_map_iff; exists (Pk; ts); split; auto. }
      specialize (Hpremindpreds H); clear H.
      specialize (Hindpreds Pk ts Hin). destruct (premstardec Pj Pk); intuition auto. }
    clear Y.
      
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
  Qed.
End soundness.
