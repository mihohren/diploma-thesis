vec : Functor

term : Type
formula : Type

TFunc (f : FuncS) : "vec (fun_arr f)" (term)  -> term

FPred (P : PredS) : "vec (pred_arr P)" (term) -> formula
FIndPred (P : IndPredS) : "vec (indpred_arr P)" (term) -> formula
FNeg : formula -> formula
FImp : formula -> formula -> formula
FAll : (term -> formula) -> formula