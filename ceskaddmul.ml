
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

(* env
<changed to addr, not storable>
*)
and env = addr StringMap.t

(* store <added>*)
and store = storable AddrMap.t

(* storable *)
and storable = 
  | Clo of value * env

(* cont *)
and cont = 
  | Done
  | Ar of term * env * cont
  | Fn of storable * cont
  | Addsnd of term * env * cont 
  | Addfst of num * cont
  | Mulsnd of term * env * cont
  | Mulfst of num * cont

(* Address <added> *)
and addr = int


(* syntactic sugar *)
let (==>) x y = (x, y)  (* tuple *)
let (//) map entries = List.fold_left(fun acc(k, v) -> StringMap.add k v acc) map entries
(* /// operator for AddrMap <added> *)
let ( /// ) map entries =
  List.fold_left (fun acc (key, value) -> AddrMap.add key value acc) map entries



(* SEMANTICS of CESK machine *)

(* injection function  *)
let inject (e:term) : state = (e, StringMap.empty, AddrMap.empty, Done)

let to_term(v:value):term =
  match v with 
  | ValAbs(x,t) -> TmAbs(x,t)
  | ValNum n -> TmNum n


let to_value(t:term):value =
  match t with 
  | TmAbs(x,t) -> ValAbs(x,t)
  | TmNum n -> ValNum n


let isAtomic(t:term):bool =
  match t with 
  | TmAbs(x,t) -> true
  | TmNum n -> true
  | _ -> false




(* alloc function *)
let alloc (s : store) : addr =
  let keys = List.map fst (AddrMap.bindings s) in    (* Extract all keys from s, *)
    (* If you want a more functional style, use fold to gather keys:
         let keys = AddrMap.fold (fun key _ acc -> key :: acc) s [] in *)
  let max_key = List.fold_left max 0 keys in         (* find the maximum key in the list, *)
  max_key + 1                                        (* and return the maximum key plus one as the new address. *)


(* (one-step) transition function *)
let step (sigma: state): state = 
  match sigma with
  | (TmVar x, rho, s, kappa) ->
      let addr = StringMap.find x rho in                (* ρ(x) *)
      let Clo (v, rho') = AddrMap.find addr s in    (* σ(ρ(x)) *)
      (to_term(v), rho', s, kappa)

  | (TmApp (e, f), rho, s, kappa) ->
       (e, rho, s, Ar (f, rho, kappa))
  | (TmAbs lam, rho, s, Ar (e, rho', kappa)) ->
       (e, rho', s,  Fn(Clo(ValAbs(lam), rho), kappa))
  | (TmNum _, rho, s, Ar(_, _, _)) ->
       failwith "Cannot apply a number as a function"
  | (v, rho, s, Fn(Clo(ValAbs(x, e), rho'), kappa)) when isAtomic(v) ->  
    let a' = alloc s in
    (e, rho' // [x ==> a'], s /// [a' ==> Clo(to_value(v), rho)], kappa)
  

(* Addition
need refinement!
*)
  | (TmAdd (e0,e1), rho, s, kappa) ->
      (e0, rho, s, Addsnd(e1, rho, kappa))
  | (TmNum n0, rho, s, Addsnd(e, rho', kappa)) ->
      (e, rho', s, Addfst(n0, kappa))
  | (TmNum n1, rho, s, Addfst(n0, kappa)) ->
      (TmNum (n0 + n1), rho, s, kappa)

(* Multiplication
need refinement!
*)
  | (TmMul (e0,e1), rho, s, kappa) ->
      (e0, rho, s, Mulsnd(e1, rho, kappa))
  | (TmNum n0, rho, s, Mulsnd(e, rho', kappa)) ->
      (e, rho', s, Mulfst(n0, kappa))
  | (TmNum n1, rho, s, Mulfst(n0, kappa)) ->
      (TmNum(n0 * n1), rho, s, kappa)

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

(* test3
suc = λnsz.s(nsz)
1 = λsz.sz
suc 1 ->* λsz.s(sz) = 2
 *)
 (* let term_test3 = TmApp(
                    TmAbs("n", TmAbs ("s",TmAbs ("z", TmApp (TmVar "s", TmApp(TmApp(TmVar "n", TmVar "s"), TmVar "z"))))),
                    TmAbs ("s", TmAbs ("z", TmApp (TmVar "s", TmVar "z")))) *)


(* Converts a Church numeral into a TmNum 
i.e. Convert lambad term "\f.\z.f^n z" into "(t (\x. x + 1)) 0"
*)
(* let convert_to_TmNum (t:term) :term = *)



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
    | (TmNum n, _, _, Done) -> string_of_int n
    | (TmAbs(_, _) as abs, _, _, Done) -> string_of_term abs
    | _ -> "<non-final state>"




(* output *)
  let () =
  let result1 = evaluate term_test1 in
  (* let result2 = evaluate term_test2 in
  let result3 = evaluate(convert_to_TmNum(term_test3)) in *)
  print_endline ("test1 result: " ^ string_of_state result1);
  (* print_endline ("test2 result: " ^ string_of_state result2);
  print_endline ("test3 result: " ^ string_of_state result3); *)
  


  (* check the correctness *)
  