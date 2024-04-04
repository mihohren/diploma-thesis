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

  Open Scope subst_scope.
  Lemma strong_eval_subst_sanity2 :
    forall (σ : var -> term Σ),
      eval (σ >> eval ρ) t = eval ρ (subst_term σ t).
  Proof.
    intros σ; induction t as [v | f args IH].
    - reflexivity.
    - simpl. f_equal. rewrite V.map_map.
      apply V.map_ext_in. intuition.
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

Section lemma_2_1_9.
  Context {x : var}.
  Context {Σ : signature}.
  Context {M : structure Σ}.
  Context {ρ : env M}.             
  Context {t : term Σ}.
  Context {F : formula Σ}.

  Lemma form_subst_sanity1 :
    forall (d : |M|), ~ FV F x -> (ρ ⊨ F <-> (env_subst ρ x d) ⊨ F).
  Proof.
    intros d Hfv; split; intros Hsat.
    - induction F.
      + simpl in *.
  Admitted.

  Open Scope subst_scope.

  Lemma eval_scons0 : forall d,
      eval (d .: ρ) (var_term 0) = d.
  Proof.
    intros d; reflexivity.
  Qed.

  Lemma eval_shift : forall d,
      (funcomp
         (eval (scons d ρ))
         (subst_term (funcomp var_term shift))) = eval ρ.
  Proof.
    intros; asimpl.
    fext. intros u.
    asimpl. induction u; asimpl; simpl.
    - reflexivity.
    - f_equal. rewrite V.map_map. apply V.map_ext_in.
      intros a Hin. apply H. assumption.
  Qed.
  
  Lemma strong_form_subst_sanity2 :
    forall (σ : var -> term Σ),
    ρ ⊨ (subst_formula σ F) <-> (σ >> eval ρ) ⊨ F.
  Proof.
    revert ρ; induction F; cbn; intuition.
    - erewrite <- vec_comp.
      + eapply H.
      + intros u. asimpl. rewrite strong_eval_subst_sanity2.
        reflexivity.
    - erewrite vec_comp.
      + eapply H.
      + intros u; asimpl; rewrite strong_eval_subst_sanity2.
        reflexivity.
    - erewrite <- vec_comp.
      + eassumption.
      + intuition. rewrite strong_eval_subst_sanity2.
        asimpl. reflexivity.
    - erewrite vec_comp.
      + eassumption.
      + intuition. asimpl. rewrite strong_eval_subst_sanity2.
        reflexivity.
    - apply H. apply IHf. assumption.
    - apply H; apply IHf; assumption.
    - apply IHf2. apply H. apply IHf1. assumption.
    - apply IHf2; apply H; apply IHf1; auto.
    - asimpl in H. specialize H with d.
      apply IHf in H. asimpl in H. simpl in H. rewrite eval_shift in H.
      assumption.
    - rewrite IHf. asimpl. simpl.
      rewrite eval_shift.
      apply H.
  Abort.                        (* an ugly (dependent?) type error *)
    
End lemma_2_1_9.
