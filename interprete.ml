open Printf;;
open Bool;;

type ide = string;;
type 't env = ide -> 't;; (* Definizione ambiente polimorfo *)

type permission = (* La execution corrente può: *)
  | PRead  (* leggere il contenuto di variabili di tutte le execution precedenti *)
  | PWrite (* modificare il contenuto di variabili di tutte le executuon precedenti *)
  | PFun   (* chiamare funzioni locali di tutte le execution precedenti *)
  | PAll   (* fare tutto *)

type exp =  
  | Eint of int
  | Ebool of bool
  | Var of ide (* Fa una lookup tra tutte le variabili nell'ambiente. Nota che le variabili sono state aggiunte dal let *)
  | BinOp of string * exp * exp
  | UnOp of string * exp
  | If of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide * exp
  | FunCall of exp * arg
  | Letrec of ide * exp * exp
  | Seq of exp * exp (* todo *)
  | Execute of exp * permission list (* todo: ha senso permettere una execute dentro un'altra execute? *)
  | Send of string * int (* invia all'indirizzo un intero *)
  | Receive of string * int (* riceve dall'indirizzo un intero *)
    and evT = 
      | Int of int
      | Bool of bool
      | Unbound
      | FunVal of ide * exp * evT env * bool
      | RecFunVal of ide * (ide * exp * evT env) * bool
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

let counter = ref 0;;
let next() = incr counter; !counter;;

(* Definzione interprete *)
let rec eval (e : exp) (r : evT env) (p: permission list) (sandbox: bool): evT = 
  match e with
	| Eint n -> Int n
	| Ebool b -> Bool b
  | Var i -> applyenv r i
  | UnOp(op, e) -> (match op with
    | "!" -> not_ (eval e r p sandbox)
    | _ -> failwith ("unknown operator"))
  | BinOp(op, e1, e2) -> (match op with 
    | "*" -> prod_ (eval e1 r p sandbox) (eval e2 r p sandbox)
    | "+" -> sum_ (eval e1 r p sandbox) (eval e2 r p sandbox)
    | "-" -> diff_ (eval e1 r p sandbox) (eval e2 r p sandbox) 
    | "=" -> eq_ (eval e1 r p sandbox) (eval e2 r p sandbox)
    | "||" -> or_ (eval e1 r p sandbox) (eval e2 r p sandbox)
    | "&&" -> and_ (eval e1 r p sandbox) (eval e2 r p sandbox)
    | _ -> failwith ("unknown operator"))
	| If(a, b, c) ->
		let g = (eval a r p sandbox) in
			if (typecheck "bool" g)
				then (if g = Bool(true) then (eval b r p sandbox) else (eval c r p sandbox))
				else failwith ("nonboolean guard")
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r p sandbox)) p sandbox
	| Fun(i, a) -> FunVal(i, a, r, sandbox)
	| FunCall(f, arg) ->
      let v = match arg with (* Si distingue il caso in cui arg sia un'espressione o un valore. Se è un espressione si valuta*)
        | Exp(e1) -> eval e1 r p sandbox
        | EvT(v1) -> v1
      in let fClosure = (eval f r p sandbox) in
        (match fClosure with
          | FunVal(arg, fBody, fDecEnv, s) -> 
            if s = true || can_fun(p) (* Se è true vuol dire che è una funzione che è stata creata all'interno della execution, allora può di sicuro essere usata*)
              then eval fBody (bind fDecEnv arg v) p sandbox
            else failwith("permission violation")
          | RecFunVal(g, (arg, fBody, fDecEnv), s) ->
            if s=true || can_fun(p)
              then let rEnv = (bind fDecEnv g fClosure) in
                let aEnv = (bind rEnv arg v) in
                  eval fBody aEnv p sandbox
              else failwith("permission violation")
          |	_ -> failwith("non functional value"))
  | Letrec(f, funDef, letBody) ->
    (match funDef with
      | Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r), sandbox))) in eval letBody r1 p sandbox
      | _ -> failwith("non functional def"))
  | Seq(e1, e2) -> eval e1 r; eval e2 r p sandbox
  | Execute(e, permissions) -> eval e r permissions true;;


(* =============================  TESTS  ============================= *)


let rec printConvert (v: evT) = match v with (* Funzione di supporto per la stampa di evT *)
    | Int(i) -> printf "%d" i
    | Bool(b) -> printf "%b" b
    | Unbound -> printf "Unbound"
    | FunVal(a,b,c, _) -> printf "FunVal"
    | RecFunVal(a, (b, c, d), _) -> printf "RecFunVal %s" a;;

let env0 = emptyenv Unbound;;

printf "Test 1\n";;
let e1 = Execute(FunCall(Fun("x", BinOp("+", Var("x"), Eint 1)), EvT(Int(7))), [PFun]);;
let e2 = Let("Sum", Fun("x", BinOp("+", Var("x"), Eint 1)), Execute(FunCall(Var("Sum"), EvT(Int(7))), []));;
printConvert (eval e2 env0 [] false);;
printf "\n";;