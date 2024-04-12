Require Import Base.

Structure signature := {
    FuncS : Type;
    fun_ar : FuncS -> nat;
    PredS : Type;
    pred_ar : PredS -> nat;
    IndPredS : Type;
    indpred_ar : IndPredS -> nat
  }.

Arguments fun_ar {Σ} f : rename.
Arguments pred_ar {Σ} P : rename.
Arguments indpred_ar {Σ} P : rename.

Notation var := nat.

Section term.
  Context {Σ : signature}.

  Unset Elimination Schemes.
  
  Inductive term  : Type :=
  | var_term : var -> term 
  | TFunc : forall (f : FuncS Σ), vec term (fun_ar f) -> term .
  
  Set Elimination Schemes.

  Inductive TV : term -> E.Ensemble var :=
  | TVVar : forall v, TV (var_term v) v
  | TVFunc : forall f args v,
      (exists st, V.In st args /\ TV st v) -> TV (TFunc f args) v.
  
  Lemma congr_TFunc
    {f : FuncS Σ}
    {s0 : vec term (fun_ar f)}
    {t0 : vec term (fun_ar f)}
    (H1 : s0 = t0)
    : TFunc  f s0 = TFunc  f t0 .
  Proof. congruence. Qed.
  
  Fixpoint subst_term  (σ : var -> term) (t : term) : term :=
    match t with
    | var_term v => σ v
    | TFunc f args => TFunc f (V.map (subst_term σ) args)
    end.

  Definition term_var_subst (t : term) (x : var) (u : term) : term :=
    subst_term (fun v => if v =? x then u else var_term v) t.
  
  Definition up_term_term  (σ : var -> term) : var -> term  :=    
    scons
      (var_term var_zero)
      (funcomp (subst_term (funcomp var_term shift)) σ).

  Definition upId_term_term
    (σ : var -> term) (Eq : forall x, σ x = var_term x)
    : forall x, (up_term_term σ) x = var_term x :=
    fun n => match n with
          | S var_n => (ap) (subst_term ((funcomp) (var_term ) (shift))) (Eq var_n)
          | 0  => eq_refl
          end.
  
  Fixpoint idSubst_term
    (σ : var -> term) (Eq : forall x, σ x = var_term x) (s : term)
    : subst_term σ s = s :=
    match s return subst_term σ s = s with
    | var_term  s => Eq s
    | TFunc  f s0 => congr_TFunc ((vec_id (idSubst_term σ Eq)) s0)
    end.
 
  Definition upExt_term_term
    (σ : var -> term) (τ : var -> term) (Eq : forall x, σ x = τ x)
    : forall x, (up_term_term σ) x = (up_term_term τ) x :=
    fun n => match n with
             | S var_n => (ap) (subst_term ((funcomp) (var_term ) (shift))) (Eq var_n)
             | 0  => eq_refl
             end.

  
  Fixpoint ext_term
    (σ : var -> term ) (τ : var -> term ) (Eq : forall x, σ x = τ x) (s : term)
    : subst_term σ s = subst_term τ s :=
    match s return subst_term σ s = subst_term τ s with
    | var_term  s => Eq s
    | TFunc  f s0 => congr_TFunc ((vec_ext (ext_term σ τ Eq)) s0)
    end.

  Fixpoint compSubstSubst_term
    (σ : var -> term ) (τ : var -> term ) (θ : var -> term ) (Eq : forall x, (funcomp (subst_term τ) σ) x = θ x) (s : term )
    : subst_term τ (subst_term σ s) = subst_term θ s :=
    match s return subst_term τ (subst_term σ s) = subst_term θ s with
    | var_term  s => Eq s
    | TFunc  f s0 => congr_TFunc ((vec_comp (compSubstSubst_term σ τ θ Eq)) s0)
    end.

  Definition up_subst_subst_term_term
    (σ : var -> term ) (τ : var -> term ) (θ : var -> term ) (Eq : forall x, ((funcomp) (subst_term τ) σ) x = θ x)
    : forall x, ((funcomp) (subst_term (up_term_term τ)) (up_term_term σ)) x = (up_term_term θ) x :=
    fun n => match n with
             | S var_n => (eq_trans) (compSubstSubst_term ((funcomp) (var_term ) (shift)) (up_term_term τ) ((funcomp) (up_term_term τ) (shift)) (fun x => eq_refl) (σ var_n)) ((eq_trans) ((eq_sym) (compSubstSubst_term τ ((funcomp) (var_term ) (shift)) ((funcomp) (subst_term ((funcomp) (var_term ) (shift))) τ) (fun x => eq_refl) (σ var_n))) ((ap) (subst_term ((funcomp) (var_term ) (shift))) (Eq var_n)))
             | 0  => eq_refl
             end.

  Lemma instId_term : subst_term var_term = id.
  Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_term ) (fun n => eq_refl) ((id) x))). Qed.

  Lemma varL_term (σ : var -> term) : funcomp (subst_term σ) var_term = σ.
  Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

  Lemma compComp_term (σ : var -> term) (τ : var -> term) (s : term)
    : subst_term τ (subst_term σ s) = subst_term ((funcomp) (subst_term τ) σ) s .
  Proof. exact (compSubstSubst_term σ τ (_) (fun n => eq_refl) s). Qed.

  Lemma compComp'_term (σ : var -> term) (τ : var -> term)
    : funcomp (subst_term τ) (subst_term σ) = subst_term (funcomp (subst_term τ) σ).
  Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term σ τ n)). Qed.

End term.

Arguments term Σ : clear implicits.

Section term_ind.
  Context {Σ : signature} (P : term Σ -> Prop).
  
  Hypothesis Pbase : forall v, P (var_term v).
  Hypothesis Pind : forall (f : FuncS Σ) args,
      (forall st, V.In st args -> P st) -> P (TFunc f args).

  Definition term_ind : forall t, P t.
    fix IND_PRINCIPLE 1; intros [v | f args].
    - apply Pbase.
    - apply Pind. apply V.Forall_forall.         
      induction args; constructor.
      + apply IND_PRINCIPLE.
      + assumption.
  Defined.
End term_ind.

Section term_facts.
  Context {Σ : signature}.

  Lemma var_not_in_TV_not_eq : forall v x, ~ @TV Σ (var_term v) x -> v <> x.
  Proof.
    intros v x H. intros eq. apply H. subst; constructor.
  Qed.
  
  Lemma var_not_in_Func_not_in_args : forall (f : FuncS Σ) args x,
      ~ TV (TFunc f args) x -> forall st, V.In st args -> ~ TV st x.
  Proof.
    intros f args x Hnotin; unfold E.In in *.
    intros t Hin Hvar. apply Hnotin.
    apply TVFunc.
    exists t; intuition.
  Qed.
    
  Lemma term_subst_id : forall (t : term Σ) (x : var),
      subst_term (fun x => var_term x) t = t.
  Proof.
    pose proof (@idSubst_term Σ) as idsubst.
    intros t v. apply idsubst. intuition.
  Qed.
    
  Lemma term_var_subst_no_occ : forall (t u : term Σ) (x : var),
      ~ TV t x -> term_var_subst t x u = t.
  Proof.
    intros t; induction t as [v | f args IH];
      intros u x Hnotin; cbn.
    - destruct (v =? x) eqn:E.
      + exfalso; apply Hnotin; rewrite Nat.eqb_eq in E; subst; constructor.
      + reflexivity.
    - f_equal. rewrite <- V.map_id. apply V.map_ext_in.
      intros st Hstin. apply IH.
      + assumption.
      + intros Hinvar. apply Hnotin. constructor.
        exists st; intuition.
  Qed.                                             
End term_facts.

Section formula.
  Context {Σ : signature}.
  
  Inductive formula  : Type :=
  | FPred (P : PredS Σ) : vec (term Σ) (pred_ar P) -> formula 
  | FIndPred (P : IndPredS Σ) : vec (term Σ) (indpred_ar P) -> formula 
  | FNeg : formula -> formula 
  | FImp : formula -> formula -> formula 
  | FAll : formula -> formula.

  Inductive FV : formula -> E.Ensemble var :=
  | FV_Pred : forall R args v,
      (exists st, V.In st args /\ TV st v) -> FV (FPred R args) v
  | FV_IndPred : forall R args v,
      (exists st, V.In st args /\ TV st v) -> FV (FIndPred R args) v
  | FV_Imp_l : forall F G v, FV F v -> FV (FImp F G) v
  | FV_Imp_r : forall F G v, FV G v -> FV (FImp F G) v
  | FV_Neg : forall F v, FV F v -> FV (FNeg F) v
  | FV_All : forall F v, FV F (S v) -> FV (FAll F) v.
  
  Lemma congr_FPred
    {P : PredS Σ}
    {s0 : vec (term Σ) (pred_ar P)}
    {t0 : vec (term Σ) (pred_ar P)}
    (H1 : s0 = t0)
    : FPred  P s0 = FPred  P t0 .
  Proof. congruence. Qed.

  Lemma congr_FIndPred
    {P : IndPredS Σ}
    {s0 : vec (term Σ) (indpred_ar P)}
    {t0 : vec (term Σ) (indpred_ar P)}
    (H1 : s0 = t0)
    : FIndPred  P s0 = FIndPred  P t0 .
  Proof. congruence. Qed.

  Lemma congr_FNeg
    {s0 : formula}
    {t0 : formula}
    (H1 : s0 = t0)
    : FNeg s0 = FNeg t0.
  Proof. congruence. Qed.

  Lemma congr_FImp
    {s0 : formula}
    {s1 : formula}
    {t0 : formula}
    {t1 : formula}
    (H1 : s0 = t0)
    (H2 : s1 = t1)
    : FImp  s0 s1 = FImp  t0 t1.
  Proof. congruence. Qed.

  Lemma congr_FAll
    {s0 : formula}
    {t0 : formula}
    (H1 : s0 = t0)
    : FAll s0 = FAll t0.
  Proof. congruence. Qed.

  Fixpoint subst_formula
    (σ : var -> term Σ) (s : formula )
    : formula  :=
    match s return formula  with
    | FPred  P s0 => FPred  P ((V.map (subst_term σ)) s0)
    | FIndPred  P s0 => FIndPred  P ((V.map (subst_term σ)) s0)
    | FNeg  s0 => FNeg  ((subst_formula σ) s0)
    | FImp  s0 s1 => FImp  ((subst_formula σ) s0) ((subst_formula σ) s1)
    | FAll  s0 => FAll  ((subst_formula (up_term_term σ)) s0)
    end.

  Fixpoint idSubst_formula
    (σ : var -> term Σ) (Eq : forall x, σ x = var_term x) (s : formula )
    : subst_formula σ s = s :=
    match s return subst_formula σ s = s with
    | FPred  P s0 => congr_FPred ((vec_id (idSubst_term σ Eq)) s0)
    | FIndPred  P s0 => congr_FIndPred ((vec_id (idSubst_term σ Eq)) s0)
    | FNeg  s0 => congr_FNeg ((idSubst_formula σ Eq) s0)
    | FImp  s0 s1 => congr_FImp ((idSubst_formula σ Eq) s0) ((idSubst_formula σ Eq) s1)
    | FAll  s0 => congr_FAll ((idSubst_formula (up_term_term σ) (upId_term_term (_) Eq)) s0)
    end.

  Fixpoint ext_formula
    (σ : var -> term Σ) (τ : var -> term Σ) (Eq : forall x, σ x = τ x) (s : formula )
    : subst_formula σ s = subst_formula τ s :=
    match s return subst_formula σ s = subst_formula τ s with
    | FPred  P s0 => congr_FPred ((vec_ext (ext_term σ τ Eq)) s0)
    | FIndPred  P s0 => congr_FIndPred ((vec_ext (ext_term σ τ Eq)) s0)
    | FNeg  s0 => congr_FNeg ((ext_formula σ τ Eq) s0)
    | FImp  s0 s1 => congr_FImp ((ext_formula σ τ Eq) s0) ((ext_formula σ τ Eq) s1)
    | FAll  s0 => congr_FAll ((ext_formula (up_term_term σ) (up_term_term τ) (upExt_term_term (_) (_) Eq)) s0)
    end.
  
  Fixpoint compSubstSubst_formula
    (σ : var -> term Σ) (τ : var -> term Σ) (θ : var -> term Σ) (Eq : forall x, ((funcomp) (subst_term τ) σ) x = θ x) (s : formula )
    : subst_formula τ (subst_formula σ s) = subst_formula θ s :=
    match s return subst_formula τ (subst_formula σ s) = subst_formula θ s with
    | FPred  P s0 => congr_FPred ((vec_comp (compSubstSubst_term σ τ θ Eq)) s0)
    | FIndPred  P s0 => congr_FIndPred ((vec_comp (compSubstSubst_term σ τ θ Eq)) s0)
    | FNeg  s0 => congr_FNeg ((compSubstSubst_formula σ τ θ Eq) s0)
    | FImp  s0 s1 => congr_FImp ((compSubstSubst_formula σ τ θ Eq) s0) ((compSubstSubst_formula σ τ θ Eq) s1)
    | FAll  s0 => congr_FAll ((compSubstSubst_formula (up_term_term σ) (up_term_term τ) (up_term_term θ) (up_subst_subst_term_term (_) (_) (_) Eq)) s0)
    end.

  Lemma instId_formula  : subst_formula var_term = id .
  Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_formula (var_term ) (fun n => eq_refl) ((id) x))). Qed.

  Lemma compComp_formula
    (σ : var -> term Σ) (τ : var -> term Σ) (s : formula )
    : subst_formula τ (subst_formula σ s) = subst_formula ((funcomp) (subst_term τ) σ) s .
  Proof. exact (compSubstSubst_formula σ τ (_) (fun n => eq_refl) s). Qed.

  Lemma compComp'_formula
    (σ : var -> term Σ) (τ : var -> term Σ )
    : (funcomp) (subst_formula τ) (subst_formula σ) = subst_formula ((funcomp) (subst_term τ) σ) .
  Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_formula σ τ n)). Qed.

End formula.

Arguments formula Σ : clear implicits.
                            


Instance Subst_term (Σ : signature)  : Subst1 (var -> term Σ) (term Σ) (term Σ) := @subst_term Σ   .

Instance Subst_formula (Σ : signature)  : Subst1 (var -> term Σ) (formula Σ ) (formula Σ) := @subst_formula Σ  .

Instance VarInstance_term (Σ : signature) : Var (var) (term Σ) := @var_term Σ .

Notation "x '__term'" := (var_term x) (at level 5, format "x __term") : subst_scope.

Notation "x '__term'" := (@ids (_) (_) VarInstance_term x) (at level 5, only printing, format "x __term") : subst_scope.

Notation "'var'" := (var_term) (only printing, at level 1) : subst_scope.

Class Up_term X Y := up_term : ( X ) -> Y.

Notation "↑__term" := (up_term) (only printing) : subst_scope.

Notation "↑__term" := (up_term_term) (only printing) : subst_scope.

Instance Up_term_term (Σ : signature)  : Up_term (_) (_) := @up_term_term Σ  .

Notation "s [ σ ]" := (subst_term σ s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ σ ]" := (subst_term σ) (at level 1, left associativity, only printing) : fscope.

Notation "s [ σ ]" := (subst_formula σ s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ σ ]" := (subst_formula σ) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_formula,  VarInstance_term.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_formula,  VarInstance_term in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?instId_formula| progress rewrite ?compComp_formula| progress rewrite ?compComp'_formula| progress rewrite ?varL_term| progress (unfold up_ren, up_term_term)| progress (cbn [subst_term subst_formula])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?instId_formula in *| progress rewrite ?compComp_formula in *| progress rewrite ?compComp'_formula in *| progress rewrite ?varL_term in *| progress (unfold up_ren, up_term_term in *)| progress (cbn [subst_term subst_formula] in *)| fsimpl in *].

Ltac substify := auto_unfold.
Ltac renamify := auto_unfold.
