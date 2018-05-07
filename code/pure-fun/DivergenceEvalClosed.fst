module DivergenceEvalClosed

open FStar.StrongExcludedMiddle

type var = nat

type exp =
| App : exp -> exp -> exp
| Lam : exp -> exp
| Var : var -> exp

type sub = var -> Tot exp

type renaming (s:sub) = (forall (x:var). Var? (s x))

val is_renaming : s:sub -> GTot (n:int{  (renaming s  ==> n=0) /\
                                       (~(renaming s) ==> n=1)})
let is_renaming s = (if strong_excluded_middle (renaming s) then 0 else 1)


val sub_inc : var -> Tot exp
let sub_inc y = Var (y+1)

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if Var? e then 0 else 1

val subst : s:sub -> e:exp -> Pure exp (requires True)
     (ensures (fun e' -> (renaming s /\ Var? e) ==> Var? e'))
     (decreases %[is_var e; is_renaming s; e])
let rec subst s e =
  match e with
  | Var x -> s x
  | Lam e1 ->
     let sub_elam : y:var -> Tot (e:exp{renaming s ==> Var? e}) =
       fun y -> if y=0 then Var y
                       else subst sub_inc (s (y-1))            (* shift +1 *)
     in Lam (subst sub_elam e1)
  | App e1 e2 -> App (subst s e1) (subst s e2)

val sub_elam: s:sub -> Tot sub
let sub_elam s y = if y=0 then Var y
                   else subst sub_inc (s (y-1))

val sub_beta : exp -> Tot sub
let sub_beta v = fun y -> if y = 0 then v      (* substitute *)
                          else (Var (y-1))     (* shift -1 *)

val eval : exp -> Dv exp
let rec eval e =
  match e with
  | App (Lam e1) e2 -> eval (subst (sub_beta e2) e1)
  | App e1 e2 -> eval (App (eval e1) e2)
  | Lam e1 -> Lam (eval e1)
  | _ -> e

val below : n:var -> e:exp -> Tot bool (decreases e)
let rec below n e =
  match e with
  | Var x -> x < n
  | App e1 e2 -> below n e1 && below n e2
  | Lam e1 -> below (n+1) e1

val closed : exp -> bool
let closed = below 0

let rec below_subst_beta (n:var) (e1 e2:exp) : Lemma
          (requires (below (n+1) e1 /\ below n e2))
          (ensures (below n (subst (sub_beta e2) e1))) =
  match e1 with
  | Var x -> ()
  | App e11 e12 -> (below_subst_beta n e11 e2;
                    below_subst_beta n e12 e2)
  | Lam e11 -> admit() (* below_subst_beta (n+1) e11 e2 *)

val eval_closed : e:exp -> Div exp (requires (closed e))
                                   (ensures (fun e' -> Lam? e' /\ closed e'))
let rec eval_closed e =
  match e with
  | App e1 e2 -> let Lam e1' = eval_closed e1 in
                 below_subst_beta 0 e1' e2;
                 eval_closed (subst (sub_beta e2) e1')
  | Lam e1 -> Lam e1
