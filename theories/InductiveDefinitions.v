From CFOLID Require Import Base Syntax Semantics.

Section inductive_definition_set.
  Context (Σ : signature).
  
  Record production :=
    mkProd {
        preds : list { P : PredS Σ & vec (term Σ) (pred_ar P) };
        indpreds : list { P : IndPredS Σ & vec (term Σ) (indpred_ar P) };
        indcons : IndPredS Σ;
        indargs : vec (term Σ) (indpred_ar indcons);
      }.
  
  Definition IndDefSet := production -> Prop.

  Definition vars_of_production (pr : production) : list var :=
    nodup Nat.eq_dec
      (concat (
           map (fun p => vars_of_formula (FPred p.1 p.2)) (preds pr) ++
             map (fun p => vars_of_formula (FIndPred p.1 p.2)) (indpreds pr) ++
             V.to_list (V.map vars_of_term (indargs pr)))).
End inductive_definition_set.

Arguments mkProd {Σ}.
Arguments preds {Σ}.
Arguments indpreds {Σ}.
Arguments indcons {Σ}.
Arguments indargs {Σ}.
Arguments vars_of_production {Σ}.

Section definition_set_operator.
  Context {Σ : signature}.
  Context (Φ : IndDefSet Σ).
  Context (M : structure Σ).

  Definition InterpInd := forall P : IndPredS Σ, vec M (indpred_ar P) -> Prop.

  Definition subinterp (U V : InterpInd) := forall P v, U P v -> V P v.
  Notation "U ⊑ V" := (subinterp U V) (at level 11).
  
  Definition φ_pr
    (pr : production Σ)
    (interp : InterpInd)
    (ds : vec M (indpred_ar (indcons pr)))
    : Prop :=
        exists (ρ : env M),
        (forall Q us, List.In (Q; us) (preds pr) ->
                 interpP Q (V.map (eval ρ) us)) /\
          (forall P ts, List.In (P; ts) (indpreds pr) ->
                    interp P (V.map (eval ρ) ts)) /\
          ds = V.map (eval ρ) (indargs pr).

  Definition φ_P
    (P : IndPredS Σ)
    (interp : InterpInd)
    : vec M (indpred_ar P) -> Prop.
    refine (fun ds => _).
    refine (@ex (production Σ) (fun pr => _)).
    refine (@ex (P = indcons pr /\ Φ pr) (fun '(conj Heq HΦ) => _)).
    rewrite Heq in ds.
    exact (φ_pr pr interp ds).
  Defined.
  
  Definition φ_Φ (interp : InterpInd) : InterpInd :=
    fun P => φ_P P interp.

  Definition monotone (F : InterpInd -> InterpInd) :=
    forall U V : InterpInd, U ⊑ V -> F U ⊑ F V.
  
  Proposition φ_Φ_monotone : monotone φ_Φ.
  Proof.
    intros U V Hle P v Hφ.
    unfold φ_Φ, φ_P in *.
    destruct Hφ as (pr & (Heq & HΦ) & ρ & Hpreds & Hindpreds & Heval).
    exists pr, (conj Heq HΦ), ρ; auto.
  Qed.

  Fixpoint φ_Φ_n (α : nat) : InterpInd :=
    match α with
    | 0 => fun _ _ => False
    | S α => φ_Φ (φ_Φ_n α)
    end.

  Lemma φ_Φ_n_succ : forall α : nat, φ_Φ_n α ⊑ φ_Φ_n (S α).
  Proof.
    induction α as [| α IH].
    - inversion 1.
    - apply φ_Φ_monotone, IH.
  Qed.
      
  Lemma φ_Φ_n_monotone : forall α β : nat, α <= β -> φ_Φ_n α ⊑ φ_Φ_n β.
  Proof.
    intros α β Hle; induction Hle as [| β _ IH].
    - red; auto.
    - pose proof (φ_Φ_n_succ β); red; auto.
  Qed.
      
  Lemma φ_Φ_n_characterization : forall α P v,
      φ_Φ_n α P v <-> exists β, β < α /\ φ_Φ (φ_Φ_n β) P v.
  Proof.
    intros α P v; split; intros H.
    - induction α.
      + inversion H.
      + exists α; split; [apply le_n | apply H].
    - destruct H as [β [Hle Hφ]]; induction Hle.
      + apply Hφ.
      + now apply φ_Φ_n_succ.
  Qed.

  Definition φ_Φ_ω : InterpInd := fun P v => exists α, φ_Φ_n α P v.
  
  Definition prefixed (U : InterpInd) := φ_Φ U ⊑ U.
  Definition least (P : InterpInd -> Prop) (U : InterpInd) :=
    P U /\ (forall V, P V -> U ⊑ V).
  
  Lemma φ_Φ_ω_least_prefixed : least prefixed φ_Φ_ω.
  Proof.
    split.
    - intros P v H.
      unfold φ_Φ, φ_P, φ_pr in H;
        destruct H as (pr & [Heq Hpr] & (ρ & Hpreds & Hindpreds & Heval)). 
      unfold eq_rect in Heval; subst P; subst v.
      enough (Hsup : exists α, forall P ts, In (P; ts) (indpreds pr) -> φ_Φ_n α P (V.map (eval ρ) ts)).
      + destruct Hsup as [κ Hsup].
        exists (S κ), pr, (conj eq_refl Hpr), ρ; split; auto.
      + induction (indpreds pr) as [| [P' v'] indpreds' IH].
        * exists 0; inversion 1.
        * pose proof (Hindpreds P' v').
          assert (Hin: In (P'; v') ((P'; v') :: indpreds')) by now left.
          apply H in Hin as [α Hα].
          assert (IH_help : forall P ts, In (P; ts) indpreds' -> φ_Φ_ω P (V.map (eval ρ) ts)).
          { intros P ts Hin. apply Hindpreds. now right. }
          apply IH in IH_help as [β Hβ].
          exists (S (max α β)).
          intros P ts Hin; inversion Hin.
          -- apply φ_Φ_n_monotone with α; auto with arith.
             inversion H0; subst P.
             apply inj_pair2 in H0; now subst.
          -- apply φ_Φ_n_monotone with β; auto with arith.
    - intros interp Hprefixed P v Hω.
      destruct Hω as [α Hφ].
      enough (H: forall β, φ_Φ (φ_Φ_n β) P v -> φ_Φ interp P v).
      + now apply Hprefixed, (H α), φ_Φ_n_succ.
      + intros β; apply φ_Φ_monotone. induction β as [| β IH].
        * inversion 1.
        * cbn; unfold prefixed in Hprefixed.
          apply φ_Φ_monotone in IH. red; auto.
  Qed.
End definition_set_operator.

Section standard_model.
  Context {Σ : signature}.
  
  Definition standard_model (Φ: IndDefSet Σ) (M : structure Σ) : Prop :=
    forall (P : IndPredS Σ) ts, interpIP P ts <-> φ_Φ_ω Φ M P ts.
End standard_model.
