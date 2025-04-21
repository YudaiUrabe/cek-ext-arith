
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
  | ValAbs of lambda
  | ValNum of num

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
  | Addsnd of term * env * cont 
  | Addfst of num * cont
  | Mulsnd of term * env * cont
  | Mulfst of num * cont



(* syntactic sugar *)
let (==>) x y = (x, y)  (* tuple *)
let (//) map entries = List.fold_left(fun acc(k, v) -> StringMap.add k v acc) map entries



(* SEMANTICS of CEK machine *)

(* injection function  *)
let inject (e:term) : state = (e, StringMap.empty, Done)

(* (one-step) transition function *)
let step (sigma: state): state = 
  match sigma with
  | (TmVar x, rho, kappa) ->
      let Clo(v, rho') = StringMap.find x rho in (ValNum v, rho', kappa)

  | (TmApp (e,f), rho, kappa) ->
      (e, rho, Ar(f, rho, kappa))
  | (ValAbs lam, rho, Ar(e, rho', kappa)) ->
      (e, rho', Fn((lam, rho), kappa)) 
  | (ValNum _, rho, Ar(_, _, _)) ->
  failwith "Cannot apply a number as a function"
  | (v, rho, Fn((ValAbs(x, e), rho'), kappa)) ->
      (e,rho'//[x ==> Clo(v, rho)], kappa)

  | (TmAdd (e0,e1), rho, kappa) ->
      (e0, rho, Addsnd(e1, rho, kappa))
  | (TmNum n0, rho, Addsnd(e, rho', kappa)) ->
      (e, rho', Addfst(n0, kappa))
  | (TmNum n1, rho, Addfst(n0, kappa)) ->
      (n0 + n1, rho, kappa)

  | (TmMul (e0,e1), rho, kappa) ->
     (e0, rho, Mulsnd(e1, rho, kappa))
  | (TmNum n0, rho, Mulsnd(e, rho', kappa)) ->
     (e, rho', Mulfst(n0, kappa))
  | (TmNum n1, rho, Mulfst(n0, kappa)) ->
     (n0 * n1, rho, kappa)

  | _ ->
      failwith "Invalid configuration"



(* auxiliary functions for evaluation function *)
(* isFinal *)
let isFinal (state: state) : bool =
  match state with
    |(TmAbs _, _, Done) -> true  
    |(TmNum _, _, Done) -> true
    | _ -> false

let rec run (s:state): state =
  if isFinal s then s
  else run (step s)

(* evaluation function *)
let evaluate (e: term): state =
  run(inject e)




(* test *)
  (* test1 (λx.x+1)(2*3) -> 7*)
   let term_test1 = TmApp(TmAbs("x", TmAdd(TmVar "x",TmNum 1)),TmMul(TmNum 2,TmNum 3))

  (* test2 ((λx.x+1)3)+(2*3) -> 10 *)
  let term_test2 = TmAdd(TmApp(TmAbs("x",TmAdd(TmVar "x",TmNum 1)),TmNum 3),TmMul(TmNum 2,TmNum 3))

(* to string *)
let rec string_of_term t =
  match t with
  | TmVar x -> x
  | TmNum n -> string_of_int n
  | TmAbs(x, body) -> "(λ" ^ x ^ "." ^ string_of_term body ^ ")"
  | TmApp(e1, e2) -> "(" ^ string_of_term e1 ^ " " ^ string_of_term e2 ^ ")"
  | TmAdd(e1, e2) -> "(" ^ string_of_term e1 ^ " + " ^ string_of_term e2 ^ ")"
  | TmMul(e1, e2) -> "(" ^ string_of_term e1 ^ " * " ^ string_of_term e2 ^ ")"

  let string_of_state (s: state) : string =
    match s with
    | (TmNum n, _, Done) -> string_of_int n
    | (TmAbs(_, _) as abs, _, Done) -> string_of_term abs
    | _ -> "<non-final state>"
  

  (* output *)
  let () =
  let result1 = evaluate term_test1 in
  let result2 = evaluate term_test2 in
  print_endline ("test1 result: " ^ string_of_state result1);
  print_endline ("test2 result: " ^ string_of_state result2)

