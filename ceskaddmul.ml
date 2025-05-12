
module StringMap = Map.Make(String)
module AddrMap = Map.Make (Int)

(* Object Langugae *)
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

(* CESK Machine *)
(* SYNTAX of CESK machine *)

(* state *)
type state = term * env * store * cont

(* value *)
and value = 
  | ValAbs of lambda
  | ValNum of num

(* storable *)
and storable = 
  | Clo of value * env



(* env *)
and env = storable StringMap.t

(* store *)
and store = storable AddrMap.t

(* cont *)
and cont = 
  | Done
  | Ar of term * env * cont
  | Fn of storable * cont
  | Addsnd of term * env * cont 
  | Addfst of num * cont
  | Mulsnd of term * env * cont
  | Mulfst of num * cont

(* Address *)
and addr = int

(* syntactic sugar *)
let (==>) x y = (x, y)  (* tuple *)
let (//) map entries = List.fold_left(fun acc(k, v) -> StringMap.add k v acc) map entries
(* /// operator for AddrMap *)
let ( /// ) map entries =
  List.fold_left (fun acc (key, value) -> AddrMap.add key value acc) map entries



(* SEMANTICS of CESK machine *)

(* injection function  *)
let inject (e:term) : state = (e, StringMap.empty, AddrMap.empty, Done)

let to_term(v:value):term =

let to_value(t:term):value =

let isAtomic(t:term):bool =


(* alloc function *)
let alloc (s : store) : addr =



(* (one-step) transition function *)
let step (sigma: state): state = 
  match sigma with
  | (TmVar x, rho, kappa) ->


  | (TmApp (e,f), rho, kappa) ->

  | (TmAbs lam, rho, Ar(e, rho', kappa)) ->    

  | (TmNum _, rho, Ar(_, _, _)) ->
  failwith "Cannot apply a number as a function"

  | (v, rho, Fn(Clo(ValAbs(x, e), rho'), kappa)) when isAtomic(v) ->  


  | (TmAdd (e0,e1), rho, kappa) ->

  | (TmNum n0, rho, Addsnd(e, rho', kappa)) ->

  | (TmNum n1, rho, Addfst(n0, kappa)) ->

  

  | (TmMul (e0,e1), rho, kappa) ->

  | (TmNum n0, rho, Mulsnd(e, rho', kappa)) ->

  | (TmNum n1, rho, Mulfst(n0, kappa)) ->


  | _ ->
      failwith "Invalid configuration"




(* auxiliary functions for evaluation function *)
(* isFinal *)
let isFinal (state: state) : bool =
  match state with
    |(TmAbs _, _, _, Done) -> true  
    |(TmNum _, _, _, Done) -> true
    | _ -> false

let rec run (s:state): state =
      if isFinal s then s
      else run (step s)

(* evaluation function *)
let evaluate (e: term): state =
  run(inject e)





(* tests *)
  (* test1 (λx.x+1)(2*3) -> 7*)
  let term_test1 = TmApp(TmAbs("x", TmAdd(TmVar "x",TmNum 1)),TmMul(TmNum 2,TmNum 3))

  (* test2 *)

(* test3 *)


(* Converts a Church numeral into a TmNum 
*)
let convert_to_TmNum (t:term) :term =


(* to string *)
let rec string_of_term t =

let string_of_state (s: state) : string =



(* output *)
  let () =
  let result1 = evaluate term_test1 in
  let result2 = evaluate term_test2 in
  let result3 = evaluate(convert_to_TmNum(term_test3)) in
  print_endline ("test1 result: " ^ string_of_state result1);
  print_endline ("test2 result: " ^ string_of_state result2);
  print_endline ("test3 result: " ^ string_of_state result3);
  
  (* check the correctness *)
