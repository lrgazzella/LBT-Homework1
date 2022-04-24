open Printf;;
open Bool;;

type ide = string;;

(* Definition of polymorphic env *)
type 't env = ide -> 't;; 
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

type permission = (* The current execution can: *)
  | PMemory    (* Use the memory of the parent execution *)
  | PWrite     (* Write on a file *)
  | PRead      (* Read from a file *)
  | PSend      (* Send the result of an expression to an address *)
  | PReceive;; (* Receive a value from an address *)

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
  | Execute of exp * permission list
  | Send of string * exp (* the string represents an address *)
  | Receive of string * int (* the string represents an address *)
  | Write of string * exp (* the string represents a path *)
  | Read of string * int (* the string represents a path *)
    and evT = 
      | Unbound
      | Int of int
      | Bool of bool
      | FunVal of ide * exp * evT env
      | RecFunVal of ide * (ide * exp * evT env)
    and arg = Exp of exp | EvT of evT;; 

(* type checker *)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("Not a valid type");;

(* primitive functions *)
let prod_ x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with 
    | (Int(n),Int(u)) -> Int(n*u)
    | _ -> failwith("error"))
	else failwith("Type error");;
let sum_ x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with 
    | (Int(n),Int(u)) -> Int(n+u)
    | _ -> failwith("error"))
	else failwith("Type error");;
let diff_ x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with 
    | (Int(n),Int(u)) -> Int(n-u)
    | _ -> failwith("error"))
	else failwith("Type error");;
let eq_ x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with 
    | (Int(n),Int(u)) -> Bool(n=u)
    | _ -> failwith("error"))
	else failwith("Type error");;
let or_ x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with 
    | (Bool(b),Bool(e)) -> (Bool(b||e))
    | _ -> failwith("error"))
	else failwith("Type error");;
let and_ x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		| (Bool(b),Bool(e)) -> Bool(b&&e)
    | _ -> failwith("error"))
	else failwith("Type error");;
let gt_ x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with 
    | (Int(u), Int(v)) -> Bool(u > v)
    | _ -> failwith("error"))
  else failwith("Type error");;
let lt_ x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x,y) with 
    | (Int(u), Int(v)) -> Bool(u < v)
    | _ -> failwith("error"))
  else failwith("Type error");;
let not_ x = if (typecheck "bool" x)
	then (match x with
		| Bool(true) -> Bool(false) 
    | Bool(false) -> Bool(true)
    | _ -> failwith("error"))
	else failwith("Type error");;


(* ys is included in xs *)
let rec includes xs ys = match ys with
  | [] -> true
  | y::yss -> (List.mem y xs) && includes xs yss 

let can_read p = List.mem PRead p;;
let can_write p = List.mem PWrite p;;
let can_send p = List.mem PSend p;;
let can_receive p = List.mem PReceive p;;
let can_memory p = List.mem PMemory p;;


let rec eval (e : exp) (r : evT env) (p: permission list): evT = 
  match e with
	| Eint n -> Int n
	| Ebool b -> Bool b
  | Var i -> let v = applyenv r i in (match v with
    | Unbound -> failwith("No variable " ^ i ^ " found")
    | _ -> v)
  | UnOp(op, e) -> (match op with
    | "!" -> not_ (eval e r p)
    | _ -> failwith ("Unknown operator"))
  | BinOp(op, e1, e2) -> (match op with 
    | "*" -> prod_ (eval e1 r p) (eval e2 r p)
    | "+" -> sum_ (eval e1 r p) (eval e2 r p)
    | "-" -> diff_ (eval e1 r p) (eval e2 r p) 
    | "=" -> eq_ (eval e1 r p) (eval e2 r p)
    | "||" -> or_ (eval e1 r p) (eval e2 r p)
    | "&&" -> and_ (eval e1 r p) (eval e2 r p)
    | ">" -> gt_ (eval e1 r p) (eval e2 r p)
    | "<" -> lt_ (eval e1 r p) (eval e2 r p)
    | _ -> failwith ("Unknown operator"))
	| If(a, b, c) ->
		let g = (eval a r p) in
			if (typecheck "bool" g)
				then (if g = Bool(true) then (eval b r p) else (eval c r p))
				else failwith ("Non boolean guard")
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r p)) p
	| Fun(i, a) -> FunVal(i, a, r)
	| FunCall(f, arg) ->
      let v = match arg with (* Si distingue il caso in cui arg sia un'espressione o un valore. Se è un espressione si valuta *)
        | Exp(e1) -> eval e1 r p
        | EvT(v1) -> v1
      in let fClosure = (eval f r p) in
        (match fClosure with
          | FunVal(arg, fBody, fDecEnv) ->  eval fBody (bind fDecEnv arg v) p
          | RecFunVal(g, (arg, fBody, fDecEnv)) ->
              let rEnv = (bind fDecEnv g fClosure) in
                let aEnv = (bind rEnv arg v) in
                  eval fBody aEnv p
          | _ -> failwith("Non functional value found")) (* todo: stampare il nome della funzione *)
  | Letrec(f, funDef, letBody) ->
    (match funDef with
      | Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in eval letBody r1 p
      | _ -> failwith("Non functional def"))
  | Send(socket, e) -> 
    if can_send(p) 
      then eval e r p
      else failwith("Permission denied -> You cannot use operation Send")
  | Receive(socket, v) -> 
    if can_receive(p)
      then Int(v) (* è una receive fittizia, valuta solamente l'espressione *)
      else failwith("Permission denied -> You cannot use operation Receive")
  | Write(path, e) ->
    if can_write(p)
      then eval e r p
      else failwith("Permission denied -> You cannot use operation Write")
  | Read(path, v) ->
    if can_read(p)
      then Int(v)
      else failwith("Permission denied -> You cannot use operation Read")
  | Execute(e, permissions) -> 
    if includes (List.filter (fun x -> x <> PMemory) p) (List.filter (fun x -> x <> PMemory) permissions)
      then 
        let env = if can_memory(permissions) then r else emptyenv Unbound in
          eval e env permissions 
      else
        failwith("The inner execution cannot have more permission than the outer");;

        
(* =============================  TESTS  ============================= *)
let rec printConvert (v: evT) = match v with (* Support function to print evT *)
  | Int(i) -> printf "%d" i
  | Bool(b) -> printf "%b" b
  | Unbound -> printf "Unbound"
  | FunVal(a,b,c) -> printf "FunVal"
  | RecFunVal(a, (b, c, d)) -> printf "RecFunVal %s" a;;

let env0 = emptyenv Unbound;;
let all_permission = [PMemory; PSend; PReceive; PRead; PWrite];;

printf "---------- Test 1 ----------\n";;
let e1 = Execute(FunCall(Fun("x", BinOp("+", Var("x"), Eint(1))), Exp(Eint(5))), []);;
try printConvert (eval e1 env0 all_permission) with
  Failure e -> printf "%s" e;;
printf "\n";;

printf "---------- Test 2 ----------\n";;
let e2 = Let("mysum", Fun("x", Fun("y", BinOp("+", Var("x"), Var("y")))), Execute(FunCall(FunCall(Var("mysum"), Exp(Eint(5))), Exp(Eint(5))), [PMemory]));;
try printConvert (eval e2 env0 all_permission) with
  Failure e -> printf "%s" e;;
printf "\n";;

printf "---------- Test 3 ----------\n";;
let e3 = Let("mypin", Eint(12345), Execute(Let("result", Var("mypin"), Send("www.unipi.it", Var("result"))), [PSend; PMemory]));;
try printConvert (eval e3 env0 all_permission) with
  Failure e -> printf "%s" e;;
printf "\n";;

printf "---------- Test 4 ----------\n";;
let e4 = Let("x", Eint(1), Execute(Let("y", Eint(5), Execute(Write("./file.txt", BinOp("-", Var("x"), Var("y"))), [PWrite; PMemory])), [PWrite; PMemory]));;
try printConvert (eval e4 env0 all_permission) with
  Failure e -> printf "%s" e;;
printf "\n";;
