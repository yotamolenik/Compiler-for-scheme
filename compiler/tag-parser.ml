(* /////////////////////////// TAG PARSER ////////////////////////// *)
#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_reserve_error of string;;
exception X_sexpr of sexpr;;
exception X_expr of expr;;
exception X_expr_list of expr list;;
exception XX_syntax_error;;
exception X_not_a_pair;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let car = (fun (a,b) -> a );;
let cdr = (fun (a,b) -> b);;

let inList a l = List.mem a l;;

let reserve str = if inList str reserved_word_list then raise (X_reserve_error str) else Var(str);;
  (* Garbage collector *)
  (* אני יכול לכתוב בעברית!!!!! *)
  let rec list_of_pair (rands) = match rands with 
  (* Pair(Pair(....)) => list *)
    | Pair(a,b) -> [a] @ list_of_pair b
    | _ -> []

let rec for_func_whatever list_ length =  match length with
    | 0 -> list_
    | _ -> [Const(Sexpr(Symbol("w")))] @  (for_func_whatever list_ (length-1));;

let make_pair (argsvs) = match argsvs with
  | Pair(args,vs) -> Pair(args,vs)
  | _ -> raise X_not_a_pair
  ;;
let rec cdr_dotted_pair (argsvs) = match argsvs with
  | Pair(a,Pair(b,c)) -> cdr_dotted_pair (Pair(b,c))
  | Pair(a,b) -> b               
  | _ -> raise X_not_a_pair                             
  ;;

let rec car_dotted_pair (argsvs) = match argsvs with
  | Pair(a,Pair(b,c)) -> a :: car_dotted_pair (Pair(b,c))
  | Pair(a,b) -> [a]               
  | _ -> raise X_not_a_pair                             
  ;;
   
let make_str = function
  | Symbol(x) -> x
  | a -> raise (X_sexpr a)
  ;;

  
let rec is_prop_lst = function
  | Pair(a,b) -> is_prop_lst b
  | Nil -> true
  | _ -> false;;

let not_equal_to_begin x =
     (x <> Symbol "begin");;

let rec list_to_pair list_ = match list_ with
  | a :: b -> Pair(a, (list_to_pair b))
  | [] -> Nil
  ;;

let seconds_in_pair s = List.map (function
				   | (Pair(_, Pair(b, Nil))) -> b
				   | _ -> raise X_not_a_pair
				 )
         s;;


let firsts s = List.map (fun (a, b) -> a) s;;
let seconds s = List.map (fun (a, b) -> b) s;;

let wrap_with_quote sexpr = Pair(Symbol "quote",Pair(sexpr,Nil));;


let rec make_sequence rands = 
    let converted_list = clean_begin rands in
    let seq = List.map match_expr converted_list in
    match seq with
  | []  -> Const(Void)
  | [a] ->  a
  | _   -> Seq(seq)
(* Begin *)
and 
clean_begin rands = match rands with
| Symbol ("begin") :: b -> clean_begin b
| a :: [] -> [a]
| a :: b -> a :: clean_begin b
| [] -> []
(* Lambda *)
and 
  make_simple_lambda args body = 
  LambdaSimple(List.map make_str (list_of_pair args), make_sequence body)
and
  make_opt_lambda args body = match args with
  | Symbol(a) -> LambdaOpt([],a,make_sequence body)
  | _ -> LambdaOpt(List.map make_str (car_dotted_pair args), make_str (cdr_dotted_pair args),make_sequence body)
and
  make_lambda args body = 
  if is_prop_lst args then make_simple_lambda args body else make_opt_lambda args body
  (*And*)
  and
  macro_and args =
  let tt = Const(Sexpr(Bool(true))) in
  let ff = Const(Sexpr(Bool(false))) in
  match args with
  | [] -> tt
  | a :: [] -> match_expr a
  | a :: rest ->  If(match_expr a, macro_and rest, ff)
(* Let *)
  and
    macro_let args body =
    Applic( LambdaSimple(extract_vars args, make_sequence body) , extract_vals args )
and 
  extract_vars args = match args with
  | Pair(Pair(Symbol(a) , b),Nil) -> [a]
  | Pair(Pair(Symbol(a) , b), rest) -> [a] @ extract_vars rest
  | _ -> raise (X_sexpr args)
and
  extract_vals args = match args with 
  | Pair(Pair(Symbol(a),Pair(b, Nil)),Nil) -> [match_expr b]
  | Pair(Pair(Symbol(a),Pair(b, Nil)),rest) -> [match_expr b] @ extract_vals rest
  | _ -> raise XX_syntax_error
and
(* Letrec *)
 macro_letrec args body = 
    let vars_ = extract_vars args in
    let vals_ = extract_vals args in
    let set_list_ = List.map2 (fun a b -> Set(Var(a),b)) vars_ vals_ in
    let set_body = set_list_ @ List.map match_expr body in
    let lambda_body = Seq(set_body) in
    let whatever_list = for_func_whatever [] (List.length vars_) in
    Applic(LambdaSimple(vars_,lambda_body), whatever_list) 

  
(* Let_Star *)
and 
  macro_pre_let_star args body =
    macro_let_star (extract_vars args) (extract_vals args) body
and
  macro_let_star vars_ vals_ body = 
  match List.length vars_ with
  | 0 -> Applic(LambdaSimple([],make_sequence body),[])
  | 1 -> Applic(LambdaSimple(vars_,make_sequence body), vals_)
  | _ -> Applic(LambdaSimple([List.hd vars_], (macro_let_star (List.tl vars_) (List.tl vals_) body)),[List.hd vals_])   
    (* Cond  *)
and 
    macro_cond condim = match condim with
    | Nil -> Const(Void)
    | Pair(Pair(test, Pair(Symbol("=>"), then_)),rest) -> arrow_cond test then_ rest
    | Pair(Pair(Symbol("else"),then_),rest) -> make_sequence (list_of_pair then_)
    | Pair(Pair(test,then_),rest) -> If(match_expr test,make_sequence (list_of_pair then_),macro_cond rest) 
    | _ -> Const(Void)

and
    arrow_cond test then_ rest = 
    Applic(
    (*operator*)  LambdaSimple(["value"; "f"; "rest"], If(Var("value"),Applic(Var("f"),[Var("value")]),Var("rest") )),
    (*operands*)  [match_expr test; LambdaSimple([], make_sequence (list_of_pair then_)); LambdaSimple([], macro_cond rest)] )
    
(* MIT style define *)
and
  macro_MIT_define name args body =
  Def(Var(name), make_lambda args body)

(* quasiquote *)
and
  macro_quasiquote sexpr = match sexpr with
  | Pair(Symbol("unquote"),s) -> match_expr s
  (* | Pair(Symbol("unquote-splicing"),s) ->  Applic(Var("quote"),Applic(Var("unquote-splicing"), match_expr s),[]) *)
  | Pair(Pair(Symbol("unquote"),s), rest) -> Applic(Var("cons"),[match_expr s ; macro_quasiquote rest])
  | Pair(Pair(Symbol("unquote-splicing"),s), rest) ->  Applic(Var("append"),[match_expr s; (macro_quasiquote rest)]) 
  | Pair(Pair(a,b),rest) -> Applic(Var("cons"), [macro_quasiquote (Pair(a,b)); macro_quasiquote rest])      
  | Symbol(a) -> Const(Sexpr(String(a)))  
  | Nil ->  Const(Sexpr(Nil))
  | Pair(a,b) -> Applic(Var("cons"),[match_expr (wrap_with_quote a) ; macro_quasiquote b]) 
  |_ -> Const(Void)
  and
  macro_pset args = 
  let vars = extract_vars args in
  let vals = extract_vals args in
  let underscore_ = List.map (fun (str)->  str ^ "fff_bvcfdre" ) vars in
  let sets = List.map2 (fun a b -> Set(Var(a) , Var(b))) vars underscore_ in
  Applic(LambdaSimple(underscore_, Seq(sets)), vals)
and match_expr = function
                                                                              (* Const((Symbol("x")))
                                                                              Const(Sexpr(String("x"))) *)
| Pair(Symbol("quote"), Pair(x, Nil))                                      -> Const(Sexpr(x))
| Number(x)                                                                -> Const(Sexpr(Number(x)))
| Bool(x)                                                                  -> Const(Sexpr(Bool(x)))
| String(x)                                                                -> Const(Sexpr(String(x)))
| Char(x)                                                                  -> Const(Sexpr(Char(x)))
| Symbol(x)                                                                -> reserve(x)
(* | Pair(Symbol(x),Nil)                                                      -> reserve(x)  for the case of pair(symbol,nil) in a body of a lambda *)
| Pair(Symbol("if"), Pair(test, Pair(then_, Pair(else_, Nil))))            -> If(match_expr test, match_expr then_, match_expr else_)
| Pair(Symbol("if"), Pair(test, Pair(then_, Nil)))                         -> If(match_expr test, match_expr then_, Const(Void))
| Pair(Symbol("or"), rands)                                                -> Or(List.map match_expr (list_of_pair (rands)))
| Pair(Symbol("set!"), Pair(var_,Pair(val_,_)))                            -> Set(match_expr var_, match_expr val_)
| Pair(Symbol("lambda"), Pair(args,body))                                  -> make_lambda args (list_of_pair body)
| Pair(Symbol("begin"), rands)                                             -> make_sequence (list_of_pair rands)
(* macros *)
| Pair(Symbol("let"), Pair(Nil, body))                                     -> Applic(LambdaSimple([], make_sequence (list_of_pair body)),[])
| Pair(Symbol("let"), Pair(args,body))                                     -> macro_let args (list_of_pair body)
| Pair(Symbol("and"),args)                                                 -> macro_and (list_of_pair args)
| Pair(Symbol("letrec"),Pair(Nil,body))                                    -> Applic(LambdaSimple([], make_sequence (list_of_pair body)),[])
| Pair(Symbol("letrec"), Pair(args,body))                                  -> macro_letrec args (list_of_pair body)
| Pair(Symbol("let*"), Pair(Nil,body))                                     -> Applic(LambdaSimple([], make_sequence (list_of_pair body)),[])
| Pair(Symbol("let*"), Pair(args,body))                                    -> macro_pre_let_star args (list_of_pair body)
| Pair(Symbol("cond"),condim)                                              -> macro_cond condim
| Pair(Symbol ("define"), Pair(Pair(name, args), body))                    -> macro_MIT_define (make_str name) args (list_of_pair body)
| Pair(Symbol("define"), Pair(var_, Pair(val_, Nil)))                      -> Def(match_expr var_, match_expr val_)
| Pair(Symbol("quasiquote"), Pair(sexpr,Nil))                              -> macro_quasiquote sexpr
| Pair(Symbol("pset!"),args)                                               -> macro_pset args
| Pair(operator, rands)                                                    -> Applic(match_expr operator, List.map match_expr (list_of_pair (rands)))
| Nil -> Const(Void)
;;


let rec the_big_match sexpr = match sexpr with
| [] -> []
| head:: rest ->
  [(match_expr head)] @ the_big_match rest
;;



let tag_parse_expressions sexpr = the_big_match sexpr;;

  
end;; (* struct Tag_Parser *)

(* 
1. some tests are working exactly as expected, but we fail them. why? the only difference is 1 space inside Fraction:
  2, 4, 43,  
2. cond => doesnt work with nested applications
3. we didnt check pset! with the tests
*)

