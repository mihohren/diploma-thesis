Require Import Base Syntax Semantics.

Section inductive_definition_set.
  Context {Σ : signature}.
  
  Record production := mkProd {
      preds : list ({ P : PredS Σ & vec (term Σ) (pred_ar P) });
      indpreds : list ({ P : IndPredS Σ & vec (term Σ) (indpred_ar P) });
      indcons : IndPredS Σ;
      indargs : vec (term Σ) (indpred_ar indcons);
    }.

  Definition IndDefSet := production -> Prop .
End inductive_definition_set.

Section definition_set_operator.
  Context {Σ : signature}.
  Context {M : structure Σ}.
  Context {Φ : @IndDefSet Σ}.
  Let D := domain M.             
  (*
    D^k ≡ vec D k
    Pow(D^k) ≡ vec D k -> Prop
    Pow(D^1) × ... × Pow(D^k) ≡ ∀ P, vec D (indpred_ar P) -> Prop
   *)

  (* Definition Φ_P (* Φ_i *) (P : IndPredS Σ): production -> Prop := *)
  (*   fun pr => Φ pr /\ indcons pr = P. *)
  
  Definition φ_pr (* φ_{i, r} *)
    (pr : production)
    (args : forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop)
    (ds : vec D (indpred_ar (indcons pr)))
    : Prop :=
        exists (ρ : env M),
        (forall Q us, List.In (existT _ Q us) (preds pr) ->
                 interpP Q (V.map (fun u => eval ρ u) us))
        /\
          ( forall P ts, List.In (existT _ P ts) (indpreds pr) ->
                    args P (V.map (eval ρ) ts))
        /\
          ds = V.map (fun v => eval ρ v) (indargs pr).

  Definition φ_P (* φ_i *)
    (P : IndPredS Σ)
    (args : forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop)
    : vec D (indpred_ar P) -> Prop.
    refine (fun ds => _).
    refine (@ex production (fun pr => _)).
    refine (@ex (P = indcons pr /\ Φ pr) (fun H => _)).
    destruct H as [Heq HΦ].
    rewrite Heq in ds.
    exact (φ_pr pr args ds).
  Defined.
  
  Print φ_P.
  
  Definition φ_Φ (args : forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop)
    : forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop :=
    fun P => φ_P P args.

  Proposition φ_Φ_monotone : forall (x y : forall P, vec D (indpred_ar P) -> Prop),
      (forall P v, x P v -> y P v) ->
      (forall P v, φ_Φ x P v -> φ_Φ y P v).
  Proof.
    intros x y Hle P v Hφ.
    unfold φ_Φ, φ_P in *.
    destruct Hφ as (pr & (Heq & HΦ) & Hφ_P_pr).
    destruct Hφ_P_pr as (ρ & Hpreds & Hindpreds & Hcons).
    exists pr, (conj Heq HΦ).
    unfold φ_pr in *.
    exists ρ; repeat split.
    - apply Hpreds.
    - intros PP ts HIn. apply Hle. apply Hindpreds; auto.
    - apply Hcons.
  Qed.
  (* OK, dokaz prolazi, ali ovo je unreadable... *)
  
End definition_set_operator.

Section approximants.
  Context {Σ : signature} {M : structure Σ}.
  Context {Φ : @IndDefSet Σ}.
  Let D := domain M.

  Fixpoint φ_Φ_n (α : nat) P (v : vec D (indpred_ar P)) : Prop :=
    match α with
    | 0 => False
    | S α => @φ_Φ Σ M Φ (φ_Φ_n α) P v
    end.

  Definition approximant_of (P : IndPredS Σ) (α : nat)
    : vec D (indpred_ar P) -> Prop :=
    φ_Φ_n α P.
End approximants.

Definition standard_model
  (Σ : signature) (Φ: @IndDefSet Σ)
  : structure Σ -> Prop :=
  fun M =>
    forall (P : IndPredS Σ) ts, interpIP P ts <-> exists α, @φ_Φ_n Σ M Φ α P ts.
