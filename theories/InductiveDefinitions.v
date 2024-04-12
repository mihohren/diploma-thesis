Require Import Base Syntax Semantics.

Section inductive_definition_set.
  Context {Σ : signature}.
  
  Inductive production :=
  | mkProd
      (preds : list ({ P : PredS Σ & vec (term Σ) (pred_ar P) }))
      (indpreds : list ({ P : IndPredS Σ & vec (term Σ) (indpred_ar P) }))
      (P : IndPredS Σ)
      (v : vec (term Σ) (indpred_ar P)).

  Definition IndDefSet := production -> Prop .
End inductive_definition_set.

Section definition_set_operator.
  Context {Σ : signature}.
  Context {M : structure Σ}.
  Context {Φ : @IndDefSet Σ}.
  Let D := domain M.

  (*
    For a given inductive definition set Φ,
    the inductive definition set Φ_P is defined as
    all the productions in Φ which contain P as their
    conclusion.
   *)
  Definition Φ_P (* Φ_i *) (P : IndPredS Σ) (pr : production) : Prop :=
    match pr with
    | mkProd _ _ Q _ => Φ pr /\ P = Q
    end.

  (*
    Now we define a corresponding function
    ϕi,r : (Pow(Dk1 ) × . . . × Pow (Dkn )) → Pow(Dki ) by:       
    ϕi,r (X1 , . . . , Xn ) =
    {tM (x) |
        QM1 u1 (x), . . . , Qh uh (x),
        t1 (x) ∈ X j1 , . . . , tm (x) ∈ X jm
    }
    
    i je indeks predikata P
    ki je mjesnost induktivnog predikata s indeksom i
    n je broj induktivnih predikata u Σ
   *)
  
  Definition φ_P_prod (* φ_i,r *) (P : IndPredS Σ) (pr : production) :
    Φ_P P pr ->
    (forall P : IndPredS Σ, vec D (indpred_ar P) -> Prop) ->
    (vec D (indpred_ar P) -> Prop).
    intros P_in_pr argvec; destruct pr;
      inversion P_in_pr; subst; clear P_in_pr.
    intros t.
    (* TODO *) exact False.
  Defined.
End definition_set_operator.
