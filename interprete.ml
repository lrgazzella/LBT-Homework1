type ide = string;;
type 't env = ide -> 't;; (* Definizione ambiente polimorfo *)

type permissions = 
  | PRead  (* posso leggere il contenuto di variabili *)
  | PWrite (* posso modificare il contenuto di variabili *)
  | PFun   (* posso chiamare funzioni locali *)
  | PAll   (* posso chiamare funzioni locali *)

type exp =  
  | Eint of int
  | Ebool of bool
  | Var of ide
  | BinOp of string * exp * exp
  | UnOp of string * exp
  | If of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide * exp
  | FunCall of exp * arg
  | Letrec of ide * exp * exp
  | Execute of exp * permissions list
  | Send of string * int (* invia all'indirizzo un intero *)
  | Receive of string * int (* riceve dall'indirizzo un intero *)
    and evT = 
      | Int of int
      | Bool of bool
      | Unbound
      | FunVal of ide * exp * evT env
      | RecFunVal of ide * (ide * exp * evT env)
    and arg = Exp of exp | EvT of evT;; (* Tipo utilizzato nella FunCall per distinguere il caso di chiamata di funzione con valore o con espresione *)

       
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(* Definizione type checker *)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*Definizione funzioni primitive*)
let prod_ x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;
let sum_ x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;
let diff_ x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;
let eq_ x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;
let or_ x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;
let and_ x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;
let not_ x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;


let rec exists v xs = match xs with
 | [] -> false 
 | x::xs -> if x=v then true else exists v xs;;

 
let can_all p = exists PAll p;;
let can_read p = exists PRead p || can_all p;;
let can_write p = exists PWrite p || can_all p;;
let can_fun p = exists PFun p || can_all p;;

  (* Definzione interprete *)
let rec eval (e : exp) (r : evT env) : evT = 
  match e with
	| Eint n -> Int n
	| Ebool b -> Bool b
  | UnOp(op, e) -> (match op with
    | "!" -> not_ (eval e r)
    | _ -> failwith ("unknown operator"))
	| BinOp(op, e1, e2) -> (match op with 
    | "*" -> prod_ (eval e1 r) (eval e2 r)
    | "+" -> sum_ (eval e1 r) (eval e2 r)
    | "-" -> diff_ (eval e1 r) (eval e2 r) 
    | "=" -> eq_ (eval e1 r) (eval e2 r)
    | "||" -> or_ (eval e1 r) (eval e2 r)
    | "&&" -> and_ (eval e1 r) (eval e2 r)
    | _ -> failwith ("unknown operator"))
	| If(a, b, c) ->
		let g = (eval a r) in
			if (typecheck "bool" g)
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard")
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r))
	| Fun(i, a) -> FunVal(i, a, r)
	| FunCall(f, arg) ->
      let v = match arg with (* Si distingue il caso in cui arg sia un'espressione o un valore. Se è un espressione si valuta*)
        | Exp(e1) -> eval e1 r
        | EvT(v1) -> v1
      in let fClosure = (eval f r) in
        (match fClosure with
          | FunVal(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg v)
          | RecFunVal(g, (arg, fBody, fDecEnv)) ->
              let rEnv = (bind fDecEnv g fClosure) in
                let aEnv = (bind rEnv arg v) in
                  eval fBody aEnv
          |	_ -> failwith("non functional value"))
  | Letrec(f, funDef, letBody) ->
    (match funDef with
      | Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in eval letBody r1 
      | _ -> failwith("non functional def"))
  | Execute(e, permissions) -> ;;