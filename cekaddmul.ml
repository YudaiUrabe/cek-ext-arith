
module StringMap = Map.Make(String)

(* Object Langugae -untyped lambda calculus(CbV)- *)
type var = string
and lambda = var * term
and num = int
and add = term * term
and term = 
  | TmVar of var
  | TmAbs of lambda
  | TmApp of term * term
  | TmNum of num
  | TmAdd of term * term
  | TmMul of term * term


(* CEK Machine *)
(* SYNTAX of CEK machine *)

(* state
 triple of an expression, an environment and continuation
*)
type state = term * env * cont

(* value *)
and value = 
  | lambda
  | num


(* storable *)
and storable = 
  | Clo of value * env

(* env *)
and env = storable StringMap.t

(* cont *)
and cont = 
  | Done
  | Ar of term * env * cont
  | Fn of storable * cont
  | Addsnd of temr * env * cont 
  | Addfst of num * cont
  | Mulsnd of term * env * cont
  | Mulfst of num * cont




(* syntactic sugar *)
let (==>) x y = (x, y)  (* tuple *)
let (//) map entries = List.fold_left(fun acc(key, value) -> StringMap.add key value acc) map entries





(* SEMANTICS of CEK machine *)

(* injection function  *)
let inject (e:term) : state = (e, StringMap.empty, Done)


(* (one-step) transition function *)
let step (sigma: state): state = 
  match sigma with
  | (TmVar x, rho, kappa) ->
      let Clo(value, rho') = StringMap.find x rho in (value, rho', kappa)

  | (TmApp (e,f), rho, kappa) ->
      (e, rho, Ar(f, rho, kappa))
  | (value, rho, Ar(e, rho', kappa)) ->
      (e, rho', Fn((value, rho), kappa)) 
  | (value, rho, Fn((lam, rho'), kappa)) ->
      (e,rho'//[x ==> Clo(value, rho)], kappa)

  | (TmAdd (e0,e1), rho, kappa) ->
      (e0, rho, Addsnd(e1, rho, kappa))
  | (num, rho, Addsnd(e, rho', kappa)) ->
      (e, rho', Addfst(num, kappa))
  | (num n1, rho, Addfst(n0, kappa)) ->
      (n0 + n1, rho, kappa)(* temp. need to fix delta function *)

  | (TmMul (e0,e1), rho, kappa) ->
     (e0, rho, Mulsnd(e1, rho, kappa))
  | (num, rho, Mulsnd(e, rho', kappa)) ->
     (e, rho', Mulfst(num, kappa))
  | (num n1, rho, Mulfst(n0, kappa)) ->
     (n0 * n1, rho, kappa)(* temp. need to fix delta function *)

  | _ ->
      failwith "Invalid configuration"



(* auxiliary functions for evaluation function *)

(* isFinal *)
let isFinal (state: state) : bool =
  match state with
    |(value, rho, Done) -> true
    | _ -> false

(* evaluation function *)
let evaluate (e: term): state =
   step isFinal(inject e)



(* test *)
 let term_test = 

  (* test1 (λx.x+1)(2*3) -> 7*)

  (* test2 ((λx.x+1)3)+(2*3) -> 10 *)

let result = evaluate term_test

