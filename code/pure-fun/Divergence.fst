module Divergence

type exp =
| App : exp -> exp -> exp
| Lam : nat -> exp -> exp
| Var : nat -> exp

val subst : x:nat -> e1:exp -> e2:exp -> Tot exp (decreases e2)
let rec subst x e1 e2 =
  match e2 with 
  | Var x' -> if x = x' then e1 else Var x'
  | App e21 e22 -> App (subst x e1 e21) (subst x e1 e22)
  | Lam x' e2' -> Lam x (subst x e1 e2') (* naive implementation *)

val eval : exp -> Dv exp
let rec eval e =
  match e with
  | App (Lam x e1) e2 -> eval (subst x e2 e1)
  | App e1 e2 -> eval (App (eval e1) e2)
  | Lam x e1 -> Lam x (eval e1)
  | _ -> e

assume val factorial : int -> Dv int

(* type tau = x:int{x = factorial (-1)} *)

val bar : unit -> Dv int
let bar () = (1+2) + factorial (-1)

(* this loops forever *)
let main = eval (App (Lam 0 (App (Var 0) (Var 0)))
                     (Lam 0 (App (Var 0) (Var 0))))
