Require Import Base.
Require Import Signature Term Formula Structure.

Section Peano.
  Inductive PeanoFuncT := o | s | plus | mult.
  Definition PeanoFuncArr (f : PeanoFuncT) : nat :=
    match f with
    | o => 0
    | s => 1
    | plus => 2
    | mult => 2
    end.

  Inductive PeanoPredT := eq.
  Definition PeanoPredArr (f : PeanoPredT) : nat :=
    match f with
    | eq => 2
    end.

  Definition Σ_PA : signature :=
    {|
      FuncS := PeanoFuncT;
      fun_ar := PeanoFuncArr;
      PredS := PeanoPredT;
      pred_ar := PeanoPredArr;
      IndPredS := Empty_set;
      indpred_ar := fun e => match e with end
    |}.

  Coercion PeanoFuncT_FuncS (f : PeanoFuncT) : FuncS Σ_PA := f.
  Coercion PeanoPredT_PredS (R : PeanoPredT) : PredS Σ_PA := R.
End Peano.

Import V.VectorNotations.

Section term_examples.
  Open Scope term_scope.
  Example peano_zero {X : Vars} : term Σ_PA X := TFunc o [].
  Example peano_one  {X : Vars} : term Σ_PA X := TFunc s [peano_zero].
  Example peano_plus {X : Vars} : term Σ_PA X := TFunc plus [peano_zero; peano_one].

  Definition var := {| typ := nat; eq_dec := Nat.eq_dec |}.
  Definition x : var := 1.
  Example x_plus_one := TFunc plus [TVar x; peano_one].
  Example substitution_ex :
    term_var_subst x_plus_one x peano_zero = peano_plus.
  Proof. reflexivity. Qed.
End term_examples.







Section Peano.
  Arguments nil {A}.
  Arguments cons {A}.

  Import V.VectorNotations.
  
  Definition lift_vec1 (f : nat -> nat) : vec nat 1 -> nat :=
    fun v => match v with
          | [h] => f h
          | _ => 0
          end.

  Definition a := [3].
  Compute lift_vec1 S a.        (* = 4 : nat *)

  Definition lift_vec2 (f : nat -> nat -> nat) : vec nat 2 -> nat :=
    fun v => match v with
          | [x; y] => f x y
          | _ => 0
          end.

  Definition b := [3; 4].
  Compute lift_vec2 Nat.add b.  (* = 7 : nat *)
  
  Definition M_PA : structure Σ_PA :=
    {|
      domain := nat;
      interpF := fun (f : FuncS Σ_PA) =>
                  match f with
                  | o => fun _ => 0
                  | s => lift_vec1 S
                  | plus => lift_vec2 Nat.add
                  | mult => lift_vec2 Nat.mul
                  end;
      interpP := fun (P : PredS Σ_PA) =>
                   match P with
                   | eq => fun v =>
                            match v with
                            | [x; y] => x = y
                            | _ => False
                            end
                   end;
      interpIP := fun (IP : IndPredS Σ_PA) =>
                    match IP with end;
      |}.

  Compute @interpF Σ_PA M_PA o _ : nat.
  (* = 0 : nat *)
  Compute @interpF Σ_PA M_PA plus b : nat.
  (* = 7 : nat *)
  Compute |M_PA|.
  (* = nat : Type *)
  (* if only we could have notation for interpretation... *)
End Peano.

Section quantifiers_examples.
  Import VarNotations.
  
  Example equality_example := (* ∀ x, x = x *)
    let x := @None ∅ : ∅⁺ in
    FAll (*x*) (FPred eq [TVar x; TVar x]).
    
  Example equality_true_example : 
    M_PA ⊧ equality_example.
  Proof.
    intro.
    simpl.
    intro; reflexivity.
  Qed.
  
  Example existence_of_successor_example := (* ∀ x, ∃ y, y = x + 1 *)
    let x := Some (@None ∅) : ∅⁺⁺ in
    let y := @None ∅⁺ : ∅⁺⁺ in
    FAll (*x*) (FExists (*y*)  (FPred eq [TVar y; TFunc plus [TVar x; peano_one]])).
     
  Example existence_of_successor_is_true_example : 
    M_PA ⊧ existence_of_successor_example.
  Proof.
    intro.
    simpl.
    intros a H. 
    apply (H (a + 1)).
    reflexivity.
  Qed.
    

End quantifiers_examples.
