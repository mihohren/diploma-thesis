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
      FuncArr := PeanoFuncArr;
      PredS := PeanoPredT;
      PredArr := PeanoPredArr;
      IndPredS := Empty_set;
      IndPredArr := fun e => match e with end
    |}.

  Coercion PeanoFuncT_FuncS (f : PeanoFuncT) : FuncS Σ_PA := f.
  Coercion PeanoPredT_PredS (R : PeanoPredT) : PredS Σ_PA := R.
End Peano.

Import V.VectorNotations.

Section term_examples.
  Open Scope term_scope.
  Example peano_zero := TFunc o [].
  Example peano_one := TFunc s [peano_zero].
  Example peano_plus := TFunc plus [peano_zero; peano_one].

  Definition x : var := 1.
  Example x_plus_one := TFunc plus [TVar x; peano_one].
  Example substitution_ex :
    term_var_subst x_plus_one peano_zero x = peano_plus.
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

  Compute interpF M_PA o _ : nat.
  (* = 0 : nat *)
  Compute interpF M_PA plus b : nat.
  (* = 7 : nat *)
  Compute |M_PA|.
  (* = nat : Type *)
  (* if only we could have notation for interpretation... *)
End Peano.
