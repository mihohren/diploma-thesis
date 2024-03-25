Require Import Coq.Vectors.Vector.
Require Import CFOLID.Signature CFOLID.Term CFOLID.Formula CFOLID.Structure.

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

Arguments nil {A}.
Arguments cons {A} _ {n}.

Section term_examples.
  Example peano_zero :=
    TFunc o nil.

  Example peano_one :=
    TFunc s (cons peano_zero nil).

  Example peano_plus :=
    TFunc plus (cons peano_zero (cons peano_one nil)).
End term_examples.
(* As we can see, manually defining terms is a bit clunky.
   The problem is, if we define a signature to be implicit for
   [var] and [func], Coq can not deduce that [o] is of type
   [FuncS PeanoSig] - it thinks that [o] is of type [PeanoFuncT]
   (and indeed it is).

   By adding [Coercion]s, readability has improved a bit.
 *)

Section Peano.
  Arguments nil {A}.
  Arguments cons {A}.

  Definition lift_vec1 (f : nat -> nat) : vec nat 1 -> nat :=
    fun v => match v with
          | cons h 0 nil => f h
          | _ => 0
          end.

  Definition a := cons 3 _ nil.
  Compute lift_vec1 S a.        (* = 4 : nat *)

  Definition lift_vec2 (f : nat -> nat -> nat) : vec nat 2 -> nat :=
    fun v => match v with
          | cons x 1 (cons y 0 nil) => f x y
          | _ => 0
          end.

  Definition b := cons 3 _ (cons 4 _ nil).
  Compute lift_vec2 Nat.add b.  (* = 7 : nat *)
  
  Definition M_PA : structure :=
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
                            | cons x _ (cons y _ nil) => x = y
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
