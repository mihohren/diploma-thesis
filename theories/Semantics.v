Require Import Base Syntax.

Section structure.
  Context {Σ : signature}.

  Structure structure := {
      domain : Type;
      interpF (f : FuncS Σ) : vec domain (fun_ar f) -> domain;
      interpP (P : PredS Σ) : vec domain (pred_ar P) -> Prop;
      interpIP (P : IndPredS Σ) : vec domain (indpred_ar P) -> Prop;
    }.
End structure.

Arguments structure : clear implicits.
Arguments interpF {Σ M} _ _ : rename.
Arguments interpP {Σ M} _ _ : rename.
Arguments interpIP {Σ M} _ _ : rename.
Notation "| M |" := (domain M) (no associativity, at level 150).

Section environment.
  Context {Σ : signature} {M : structure Σ}.

  Definition env := var -> |M|.

  Definition env_subst (ρ : env) (x : var) (d : |M|) : var -> |M| :=
    fun (y : var) => if y =? x then d else ρ y.

  Fixpoint eval (ρ : env) (t : term Σ) : |M| :=
    match t with
    | var_term x => ρ x
    | TFunc f args => interpF f (V.map (eval ρ) args)
    end.

  Fixpoint eval_subst (ρ : env) (t : term Σ) (x : var) (d : |M|) : |M| :=
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
  
  Lemma eval_subst_sanity1 : forall (d : |M|),
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
        constructor. exists st; intuition.
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

Section Sat_ind.
  Context {Σ : signature}.
  Context {M : structure Σ}.
  Context {ρ : env M}.
  Context {Q : formula Σ -> Prop}.

  Hypothesis HP : forall P args,
      interpP P (V.map (eval ρ) args) -> Q (FPred P args).

  Hypothesis HIP : forall P args,
      interpIP P (V.map (eval ρ) args) -> Q (FIndPred P args).

  Hypothesis Hneg : forall F,
      ~ Sat ρ F -> Q F -> Q (FNeg F).

  Hypothesis Himp : forall F G,
      (Sat ρ F -> Sat ρ G) -> Q G -> Q G -> Q (FImp F G).

  Hypothesis Hall : forall F,
      (forall d, Sat (d .: ρ) F) -> Q F -> Q (FAll F).

  Definition Sat_ind : forall F, Sat ρ F -> Q F.
    fix IND_PRINCIPLE 1; intros F Hsat.
    destruct F eqn:E.
    - apply HP, Hsat.
    - apply HIP, Hsat.
    - apply Hneg; [apply Hsat | apply IND_PRINCIPLE]. admit.
  Abort.
  (* Je li moguce / ima li smisla definirati Sat_ind? *)
End Sat_ind.

  
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
      (ρ : env M) (d : |M|) (x : var),
    ~ FV F x -> (ρ ⊨ F <-> (env_subst ρ x d) ⊨ F).
  Proof.
    intros Σ; induction F; intros M ρ d x Hfv;
      split; intros Hsat; simpl in *;
      try (erewrite V.map_ext_in;
           [ apply Hsat
           | intros st Hin; rewrite <- eval_env_subst_unused;
             [ reflexivity
             | intros Htv; apply Hfv; constructor; exists st; intuition]]).
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
      + intros Hfv'; apply Hfv. admit.
    - intros b; specialize Hsat with b; rewrite IHF.
      + rewrite <- env_subst_scons. apply Hsat.
      + admit.
  Admitted.

  Open Scope subst_scope.

  Lemma strong_form_subst_sanity2 :
    forall (Σ : signature) (F : formula Σ)
      (M : structure Σ) (ρ : env M)
      (σ : var -> term Σ),
      ρ ⊨ (subst_formula σ F) <-> (σ >> eval ρ) ⊨ F.
  Proof.
    intros Σ F; induction F; intros M ρ σ; cbn; intuition.
    - erewrite <- vec_comp.
      + eapply H.
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
    - now apply H, IHF.
    - now apply H, IHF. 
    - apply IHF2; apply H; apply IHF1; auto.
    - apply IHF2; apply H; apply IHF1; auto.
    - asimpl in H. specialize H with d.
      apply IHF in H. asimpl in H. simpl in H.
      rewrite eval_shift in H. apply H.
    - rewrite IHF. asimpl. simpl.
      rewrite eval_shift.
      apply H.
  Qed.  
  
End lemma_2_1_9.
