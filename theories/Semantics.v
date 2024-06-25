From CFOLID Require Import Base Syntax.

Section structure.
  Context {Σ : signature}.

  Structure structure := {
      domain :> Set;
      interpF (f : FuncS Σ) : vec domain (fun_ar f) -> domain;
      interpP (P : PredS Σ) : vec domain (pred_ar P) -> Prop;
      interpIP (P : IndPredS Σ) : vec domain (indpred_ar P) -> Prop;
    }.
End structure.

Arguments structure : clear implicits.
Arguments interpF {Σ M} _ _ : rename.
Arguments interpP {Σ M} _ _ : rename.
Arguments interpIP {Σ M} _ _ : rename.

Section environment.
  Context {Σ : signature} {M : structure Σ}.

  Definition env := var -> M.

  Definition env_subst (ρ : env) (x : var) (d : M) : var -> M :=
    fun (y : var) => if y =? x then d else ρ y.
  
  Fixpoint env_finite_subst (ρ : env) {n} (xvec : vec var n) (dvec : vec M n) : var -> M :=
    match xvec in vec _ n return vec M n -> var -> M with
    | V.cons xh xt => fun dvec => env_subst (env_finite_subst ρ xt (V.tl dvec)) xh (V.hd dvec)
    | V.nil => fun _ => ρ
    end dvec.

  Fixpoint eval (ρ : env) (t : term Σ) : M :=
    match t with
    | var_term x => ρ x
    | TFunc f args => interpF f (V.map (eval ρ) args)
    end.

  Fixpoint eval_subst (ρ : env) (t : term Σ) (x : var) (d : M) : M :=
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
  
  Lemma eval_subst_sanity1 : forall (d : M),
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
        apply TVFunc with st; auto.
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

Section eval_facts.
  Context {Σ : signature}.
  Context {M: structure Σ}.

  Lemma env_subst_scons : forall (ρ : env M) b x d,
    b .: env_subst ρ x d = env_subst (b .: ρ) (S x) d.
  Proof.
    intros ρ b x d. fext; intros [|y]; reflexivity.
  Qed.

  Lemma eval_ext : forall (ρ ξ : env M) t,
      (forall x, ρ x = ξ x) -> eval ρ t = eval ξ t.
  Proof.
    intros ρ ξ t Eq; induction t as [v | f args IH]; simpl.
    - apply Eq.
    - f_equal. apply V.map_ext_in; apply IH.
  Qed.

  Lemma eval_ext_scons : forall (ρ ξ : env M) t,
      (forall x, ρ x = ξ x) -> forall d, eval (d .: ρ) t = eval (d .: ξ) t.
  Proof.
    intros ρ ξ t Eq d. induction t as [v | f args IH].
    - simpl; destruct v; simpl; auto.
    - simpl; f_equal; apply V.map_ext_in; apply IH.
  Qed.

  Lemma eval_scons : forall (ρ ξ : env M),
      (forall t, eval ρ t = eval ξ t) ->
      forall d t, eval (d .: ρ) t = eval (d .: ξ) t.
  Proof.
    intros ρ ξ Eq d t. induction t as [v | f args IH].
    - simpl. destruct v.
      + reflexivity.
      + simpl. pose proof (Eq (var_term v)) as Eq'. simpl in Eq'.
        assumption.
    - simpl. f_equal. apply V.map_ext_in; apply IH.
  Qed.
    
  Open Scope subst_scope.

  (* strong version of eval_subst_sanity2 *)
  Lemma eval_comp :
    forall (σ : var -> term Σ) (ρ : env M) t,
      eval (σ >> eval ρ) t = eval ρ (subst_term σ t).
  Proof.
    intros σ; induction t as [v | f args IH].
    - reflexivity.
    - simpl. f_equal. rewrite V.map_map.
      apply V.map_ext_in. intuition.
  Qed.
  
  Lemma eval_scons0 : forall (ρ : env M) d,
      eval (d .: ρ) (var_term 0) = d.
  Proof.
    intros d; reflexivity.
  Qed.

  Lemma eval_shift : forall (ρ : env M) d,
      subst_term (↑ >> var_term) >> eval (d .: ρ) = eval ρ.
  Proof.
    intros; asimpl.
    fext. intros u.
    asimpl. induction u; asimpl; simpl.
    - reflexivity.
    - f_equal. rewrite V.map_map. apply V.map_ext_in.
      intros a Hin. apply H. assumption.
  Qed.
  
  Lemma eval_env_subst_unused :
    forall (ρ : env M) x t d,
      ~ TV t x -> eval ρ t = eval (env_subst ρ x d) t.
  Proof.
    intros ρ x t d HnotTV; induction t as [v | f args IH].
    - unfold env_subst; simpl. destruct (v =? x) eqn:E.
      + apply var_not_in_TV_not_eq in HnotTV. exfalso.
        rewrite Nat.eqb_eq in E. auto.
      + reflexivity.
    - simpl. f_equal. erewrite V.map_ext_in.
      + reflexivity.
      + intros st Hin. apply IH.
        * assumption.
        * eapply var_not_in_Func_not_in_args in HnotTV; eauto.
  Qed.

  Lemma eval_env_subst_unused_vec :
    forall (ρ : env M) {n} (xvec : vec var n) (dvec : vec M n) u,
      (forall xvar, V.In xvar xvec -> ~ TV u xvar) ->
      eval ρ u = eval (env_finite_subst ρ xvec dvec) u.
  Proof.
    intros ρ n xvec. induction xvec as [| h m t IH]; intros dvec u Hin; auto.
    cbn.
    assert (Hin' : forall xvar, V.In xvar t -> ~ TV u xvar).
    { intros xvar Hin'; apply Hin; now right. }
    specialize (IH (V.tl dvec) u Hin').
    rewrite IH.
    apply eval_env_subst_unused. apply Hin; now left.
  Qed.

  Lemma env_finite_subst_not_in : forall ρ xvar {n} (xvec : vec var n) (dvec : vec M n),
      ~V.In xvar xvec -> env_finite_subst ρ xvec dvec xvar = ρ xvar.
  Proof.
    intros ρ xvar n xvec; revert ρ; induction xvec as [| h n t IH]; intros ρ dvec Hnotin; auto.
    cbn. unfold env_subst.
    destruct (xvar =? h) eqn:E.
    - apply Nat.eqb_eq in E; subst. exfalso; apply Hnotin; now left.
    - apply IH. intros Hin; apply Hnotin; now right.
  Qed.
  
  
  Lemma env_subst_env_finite_subst_commute :
    forall (ρ : env M) xvar dvar {n} (xvec : vec var n) (dvec : vec M n),
      VecNoDup (V.cons xvar xvec) ->
      env_subst (env_finite_subst ρ xvec dvec) xvar dvar =
        env_finite_subst (env_subst ρ xvar dvar) xvec dvec.
  Proof.
    intros ρ xvar dvar n xvec dvec Hnodup. fext.
    revert dvec ρ Hnodup. induction xvec as [| h n t IH]; intros dvec ρ Hnodup v; auto.
    inversion Hnodup; subst; apply Eqdep_dec.inj_pair2_eq_dec in H1; auto using Nat.eq_dec; subst.
    inversion H3; subst; apply Eqdep_dec.inj_pair2_eq_dec in H1; auto using Nat.eq_dec; subst.
    assert (VecNoDup (V.cons xvar t)).
    { constructor; auto. intros Hin; apply H2; now right. }
    cbn. unfold env_subst at 1 3.
    destruct (v =? xvar) eqn:E1, (v =? h) eqn:E2.
    - exfalso. rewrite Nat.eqb_eq in *; subst. apply H2; now left.
    - rewrite Nat.eqb_eq in *; subst. rewrite env_finite_subst_not_in.
      + unfold env_subst; now rewrite Nat.eqb_refl.
      + intros Hin; apply H2; now right.
    - rewrite Nat.eqb_eq in *; subst. unfold env_subst; now rewrite Nat.eqb_refl.
    - specialize (IH (V.tl dvec) ρ).
      rewrite <- IH; auto.
      unfold env_subst; now rewrite E1, E2.
  Qed.
  
  Lemma eval_finite_subst_on_args : forall (ρ : env M) {n} (xvec : vec var n) (dvec : vec M n),
      VecNoDup xvec -> V.map (eval (env_finite_subst ρ xvec dvec)) (V.map var_term xvec) = dvec.
  Proof.
    intros ρ n xvec; revert ρ.
    induction xvec as [| h n t IH]; intros ρ dvec Hnodup; auto using (V.nil_spec dvec).
    rewrite (V.eta dvec); cbn; f_equal.
    - unfold env_subst; now rewrite Nat.eqb_refl.
    - inversion Hnodup; subst. apply Eqdep_dec.inj_pair2_eq_dec in H1; auto using Nat.eq_dec; subst.
      rewrite env_subst_env_finite_subst_commute; auto; now rewrite IH.
  Qed.

  Lemma eval_subst_env_subst :
    forall (ρ : env M) x t d,
      eval_subst ρ t x d = eval (env_subst ρ x d) t.
  Proof.
    intros ρ x t d. induction t as [v | f args IH].
    - reflexivity.
    - cbn; f_equal; apply V.map_ext_in; apply IH.
  Qed.
End eval_facts.

Section kripke_semantics.
  Context {Σ : signature}.
  Context {M : structure Σ}.

  Fixpoint Sat (ρ : env M) (F : formula Σ) : Prop :=
    match F with
    | FPred P args => interpP P (V.map (eval ρ) args)
    | FIndPred P args => interpIP P (V.map (eval ρ) args)
    | FNeg G => ~ Sat ρ G
    | FImp F G => Sat ρ F -> Sat ρ G
    | FAll G => forall d, Sat (d .: ρ) G
    end.
  
  Example sat_imp :
    forall ρ F G, Sat ρ G -> Sat ρ (FImp F G).
  Proof.
    intros ρ F G satG. simpl.
    intros _; apply satG.
  Qed.
End kripke_semantics.
  
Notation "ρ ⊨ F" := (Sat ρ F) (at level 10).

Section Sat_facts.
  Context {Σ : signature}.
  Context {M : structure Σ}.

  Lemma Sat_ext : forall (ρ ξ : env M),
      (forall t, eval ρ t = eval ξ t) ->
      forall F, ρ ⊨ F <-> ξ ⊨ F.
  Proof.
    intros ρ ξ Eq F; generalize dependent ξ; generalize dependent ρ.
    induction F; intros ρ ξ Eq;  split; intros Hsat; simpl in *;
      try (erewrite V.map_ext; [eassumption | congruence]);
      try intuition;
      try (apply Hsat; erewrite IHF; eauto).
    - erewrite IHF2.
      + eapply Hsat; erewrite IHF1; eauto.
      + intuition.
    - erewrite IHF2.
      + eapply Hsat; erewrite IHF1; eauto.
      + intuition.
    - apply IHF with (d .: ρ).
      + intros u; apply eval_scons; intuition.
      + apply Hsat.
    - apply IHF with (d .: ξ).
      + intros u; apply eval_scons; intuition.
      + apply Hsat.
  Qed.
End Sat_facts.

Section lemma_2_1_9.
  Lemma form_subst_sanity1 :
    forall (Σ : signature) (F : formula Σ) (M : structure Σ)
      (ρ : env M) (d : M) (x : var),
    ~ FV F x -> (ρ ⊨ F <-> (env_subst ρ x d) ⊨ F).
  Proof.
    intros Σ; induction F; intros M ρ d x Hfv;
      split; intros Hsat; simpl in *;
      try (erewrite V.map_ext_in;
           [ apply Hsat
           | intros st Hin; rewrite <- eval_env_subst_unused;
             [ reflexivity
             | intros Htv; apply Hfv; try (apply FV_Pred with st);
               try (apply FV_IndPred with st); intuition]]).
    - intros Hsats; apply Hsat; rewrite IHF.
      + apply Hsats.
      + intros Hfv'; apply Hfv; constructor; assumption.
    - intros Hsats; apply Hsat; rewrite <- IHF.
      + assumption.
      + intros Hfs'; apply Hfv; constructor; assumption.
    - intros Hsat1; rewrite <- IHF2.
      + apply Hsat; rewrite IHF1.
        * apply Hsat1.
        * intros Hfv1; apply Hfv; apply FV_Imp_l; auto.
      + intros Hfv2; apply Hfv; apply FV_Imp_r; auto.
    - intros Hsat1; rewrite IHF2.
      + apply Hsat; rewrite <- IHF1; auto; intros Hfv1.
        apply Hfv; apply FV_Imp_l; auto.
      + intros Hfv2; apply Hfv; apply FV_Imp_r; auto.
    - intros b; specialize Hsat with b. rewrite env_subst_scons;
        rewrite <- IHF.
      + apply Hsat.
      + intros Hfv'; apply Hfv.
        constructor; assumption.
    - intros b; specialize Hsat with b; rewrite IHF.
      + rewrite <- env_subst_scons. apply Hsat.
      + contradict Hfv.
        replace x with (pred (S x)) by easy. 
        constructor; assumption.
  Qed.

  Lemma form_subst_sanity1_vec :
    forall (Σ : signature) (F : formula Σ) (M : structure Σ)
      (ρ : env M) {n} (xvec : vec var n) (dvec : vec M n),
      (forall x, V.In x xvec -> ~ FV F x) -> (ρ ⊨ F <-> (env_finite_subst ρ xvec dvec) ⊨ F).
  Proof.
    intros Σ F M ρ n xvec. revert ρ. induction xvec as [| h n t IH].
    - tauto.
    - intros ρ dvec Hfv. cbn; split; intros Hsat.
      + apply form_subst_sanity1.
        * apply Hfv; now left.
        * apply IH; auto. intros x Hin. apply Hfv; now right.
      + apply form_subst_sanity1 in Hsat.
        * apply IH in Hsat; auto. intros x Hin. apply Hfv; now right.
        * apply Hfv; now left.
  Qed.

  Open Scope subst_scope.
  
  Lemma strong_form_subst_sanity2 :
    forall (Σ : signature) (φ : formula Σ) (σ : var -> term Σ)
      (M : structure Σ) (ρ : env M),
      ρ ⊨ (subst_formula σ φ) <-> (σ >> eval ρ) ⊨ φ.
  Proof.
    intros Σ φ; induction φ; intros σ M ρ; cbn; intuition.
    - erewrite <- vec_comp.
      + eauto.
      + intros u; asimpl; now rewrite eval_comp.
    - erewrite vec_comp.
      + eapply H.
      + intros u; asimpl; now rewrite eval_comp.
    - erewrite <- vec_comp.
      + eapply H.
      + intros u; asimpl; now rewrite eval_comp.
    - erewrite vec_comp.
      + eapply H.
      + intros u; asimpl; now rewrite eval_comp.
    - now apply H, IHφ.
    - now apply H, IHφ. 
    - apply IHφ2; apply H; apply IHφ1; auto.
    - apply IHφ2; apply H; apply IHφ1; auto.
    - asimpl in H. specialize H with d.
      apply IHφ in H. asimpl in H. simpl in H.
      rewrite eval_shift in H. apply H.
    - rewrite IHφ. asimpl. simpl.
      rewrite eval_shift.
      apply H.
  Qed.

  Lemma form_subst_sanity2 :
    forall (Σ : signature) (φ : formula Σ) (x : var) (t : term Σ)
      (M : structure Σ) (ρ : env M),
      ρ ⊨ (subst_formula (single_subst x t) φ) <-> (env_subst ρ x (eval ρ t)) ⊨ φ.
  Proof.
    intros Σ φ x t M ρ; rewrite strong_form_subst_sanity2.
    enough (single_subst x t >> eval ρ = env_subst ρ x (eval ρ t)).
    { rewrite H; tauto. }
    fext; intros v. unfold ">>", funcomp; cbn.
    unfold single_subst, env_subst.
    destruct (v =? x); auto.
  Qed.

  Lemma form_subst_sanity2_vec :
    forall (Σ : signature) (φ : formula Σ) {n} (xvec : vec var n ) (tvec : vec (term Σ) n)
      (M : structure Σ) (ρ : env M),
      ρ ⊨ (subst_formula (finite_subst xvec tvec) φ) <->
        (env_finite_subst ρ xvec (V.map (eval ρ) tvec)) ⊨ φ.
  Proof.
    intros Σ φ n xvec tvec M ρ. rewrite strong_form_subst_sanity2.
    enough (Heq : (finite_subst xvec tvec >> eval ρ) = (env_finite_subst ρ xvec (V.map (eval ρ) tvec))).
    { rewrite Heq; tauto. }
    fext; unfold ">>", funcomp; cbn. revert ρ tvec.
    induction xvec as [| hxvec nx txvec IH]; intros ρ tvec v; auto.
    rewrite (V.eta tvec); cbn.
    unfold env_subst.
    destruct (v =? hxvec) eqn:E.
    - reflexivity.
    - apply IH.
  Qed.
End lemma_2_1_9.
