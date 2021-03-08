(* pc.ml
 * A parsing-combinators package for ocaml
 *
 * Prorammer: Mayer Goldberg, 2018
 *)
(* general list-processing procedures *)
let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;
let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  
let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;
let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;
let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;
module PC = struct
(* the parsing combinators defined here *)
exception X_not_yet_implemented;;
exception X_no_match;;
let const pred =
  function 
  | [] -> raise X_no_match
  | e :: s ->
     if (pred e) then (e, s)
     else raise X_no_match;;

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

let nt_epsilon s = ([], s);;
let caten_list nts =
  List.fold_right
    (fun nt1 nt2 ->
     pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
    nts
    nt_epsilon;;

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_no_match -> (nt2 s);;

let nt_none _ = raise X_no_match;;
let disj_list nts = List.fold_right disj nts nt_none;;
let delayed thunk s =
  thunk() s;;

let nt_end_of_input = function
  | []  -> ([], [])
  | _ -> raise X_no_match;;

let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with X_no_match -> ([], s);;

let plus nt =
  pack (caten nt (star nt))
       (fun (e, es) -> (e :: es));;

let guard nt pred s =
  let ((e, _) as result) = (nt s) in
  if (pred e) then result
  else raise X_no_match;;
  
let diff nt1 nt2 s =
  match (let result = nt1 s in
	 try let _ = nt2 s in
	     None
	 with X_no_match -> Some(result)) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let not_followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     None
	 with X_no_match -> (Some(result))) with
  | None -> raise X_no_match
  | Some(result) -> result;;
	  
let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

(* useful general parsers for working with text *)
let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;
let char = make_char (fun ch1 ch2 -> ch1 = ch2);;
let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
	       (lowercase_ascii ch2));;

let make_word char str = 
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))
    nt_epsilon;;

let word = make_word char;;
let word_ci = make_word char_ci;;
let make_one_of char str =
  List.fold_right
    disj
    (List.map char (string_to_list str))
    nt_none;;

let one_of = make_one_of char;;
let one_of_ci = make_one_of char_ci;;
let nt_whitespace = const (fun ch -> ch <= ' ');;
let make_range leq ch1 ch2 (s : char list) =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2)) s;;

let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;
let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

let nt_any (s : char list) = const (fun ch -> true) s;;
let trace_pc desc nt s =
  try let ((e, s') as args) = (nt s)
      in
      (Printf.printf ";;; %s matched the head of \"%s\", and the remaining string is \"%s\"\n"
		     desc
		     (list_to_string s)
		     (list_to_string s') ;
       args)
  with X_no_match ->
    (Printf.printf ";;; %s failed on \"%s\"\n"
		   desc
		   (list_to_string s) ;
     raise X_no_match);;

(* testing the parsers *)
let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

end;; (* end of struct PC *)
(* end-of-input *)
(* ////////////////////////////////////////////////// READER /////////////////////////////////////////// *)
#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Fraction of int * int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

  let inc num = (num + 1);;

  let rec our_star c nt s =
    try let (e, s) = (nt s) in
        let c = (inc c) in                       
         our_star c nt s 
    with X_no_match -> ((c,s), []);;

  let sexp_pre_comment = (word "#;");;
  let car = (fun (e,s) -> e );;
  let cdr = (fun (e,s) -> s);;
  let cut num rest nt =(
    let a = nt rest in             
    cdr a);;

  let empty_group = (word "()");;
  let newline_char = (char '\n');;

  let end_comment =(disj  (plus newline_char) nt_end_of_input);;
  let semicolon = (char ';');;           
  let nt_line_comment = (caten semicolon (caten (star (diff nt_any end_comment)) end_comment));;
  let packed_line_comment = pack nt_line_comment (fun (ds) -> 'c');;
  let dot = (char '.');;
  let quote = (char '\'');;
  let quasiQuote = (char '`');;
  let unQuote = (char ',');;
  let unquoteAndSplice = (word ",@");;
  (* bool parser *)
  let hashtag = (char '#');;
  let true_ = (caten hashtag (char_ci 't'));;
  let false_ = (caten hashtag (char_ci 'f'));;
  let bool_no_spaces = ( disj true_ false_ );;
  let bool_transform t = (if (t = "#t" || t = "#T") then "true" else "false");;
  let makelist = ( fun (l, e) -> [l;e] );;
  (* number parser *)
  let digit = (range '0' '9');;
  let slashParser = (char '/');;
  let zero = (char '0');;
  let zeros = (star zero);;
  let natural = (plus digit) ;;
  let plus_ = (char '+');;
  let minus_ = (char '-');;
  let signParser = (disj plus_ minus_);;                 
  let sign = (maybe signParser);;
  let pre siman = (match siman with
  |None -> 1
  |Some('+') -> 1
  |Some('-') -> -1
  |Some(a) -> 1) ;;
  let integer = (caten sign natural);;
  let frac = (caten integer (caten slashParser natural));;
  let rec gcd a b =
    if b = 0 then a else gcd b (a mod b);;
  let lo_shever = pack integer (fun (ls) ->
    let optional = car ls in
    let siman = pre optional in
    let mone = cdr ls in
    Number(Fraction(int_of_string(list_to_string(mone)) * siman,1)));;
  let nt_frac =
    pack frac (fun (frc) -> (let first = int_of_string (list_to_string(cdr(car frc))) in
                             let second = int_of_string (list_to_string(cdr(cdr frc))) in
                             let optional = car(car frc) in
                             let siman = pre optional in
                             let gcd_number = gcd first second in
                             let mone = (first / gcd_number) * siman in
                             let mechane = second / gcd_number in
                             Number(Fraction(mone,mechane))));;

  let rec lessThenOne num =
    if num < 1.0 then
    num
    else lessThenOne(num/.10.0);;
  let float_ = (caten integer (caten dot (plus digit)));;
  let nt_float =
    (* get all the float sub strings *)
    pack float_ (fun (ds) ->
     let ff =  [cdr(car ds) ; string_to_list(String.make 1 (car(cdr ds))) ; cdr(cdr ds)] in
     let optional = car(car ds) in
     let siman = pre optional in
      Number(Float(float_of_string (list_to_string (List.flatten(ff))) *. float_of_int(siman) )));;
    let e = (char_ci 'e');;
    let sctific_int = pack (caten (caten integer e) integer) (fun (num) ->
      let first = int_of_string (list_to_string (cdr  (car (car num)))) in
      let second = int_of_string (list_to_string (cdr (cdr num))) in
      let optional =  (car(car(car num)))   in
      let siman = pre optional in
      let exp_optional = car(cdr num) in
      let exp_siman = pre exp_optional in
      let exp = 10.0 ** ((float_of_int(second) *. float_of_int(exp_siman)))  in
        Number(Float(float_of_int(siman) *. (float_of_int(first) *. exp)))) ;;

    let sctific_float = pack (caten (caten float_ e) integer) (fun (num) ->
      let ff = [ 
                 cdr(car(car(car(num))))
              ; string_to_list(String.make 1 (car(cdr(car(car(num))))))
              ; cdr(cdr(car(car(num))))] in
      let first = float_of_string (list_to_string  (List.flatten(ff))) in
      let second = int_of_string (list_to_string (cdr (cdr num))) in
      let optional =  car(car(car(car num))) in
      let siman = pre optional in
      let exp_optional = car(cdr num) in
      let exp_siman = pre exp_optional in
      let exp = 10.0 ** ((float_of_int(second) *. float_of_int(exp_siman)))  in
        Number(Float(float_of_int(siman) *. (first *. exp)))) ;;

    let number_disj = (disj_list [ sctific_float; sctific_int; nt_float ; nt_frac; lo_shever ;]);;

  let upperCase = (range 'A' 'Z');;
  let packed_upperCase = pack upperCase (fun (c) -> char_of_int(int_of_char(c) + 32));;
  let alphabet = (disj (range 'a' 'z') packed_upperCase);;
  let power = (char '^');;
  let dollar = (char '$');;
  let kria = (char '!');;
  (* minus_ and plus_ is in number *)
  let questionMark = (char '?');;
  let underscore = (char '_');;
  let equal = (char '=');;
  let se = (char '<');;
  let ge = (char '>');;
  let mul = (char '*');;
  (* slash in slashparser *)
  let dots = (char ':');;
  let symbolCharNoDot = (disj_list [dots; mul; alphabet; power; dollar; kria; questionMark; mul; minus_; plus_; underscore; equal; se; ge; slashParser; digit]);;
  let symbolChar = (disj symbolCharNoDot dot);;
  let symbolCharPlus = (plus symbolChar);;
  let symbol_ =  (disj (caten symbolChar symbolCharPlus) (caten symbolCharNoDot nt_epsilon) );;
  (* string *)
  let merchaot = (char '\"');;
  let backslashParser = pack (char '\\') (fun (c) -> c);;
  let stringLiteralChar = (diff (diff nt_any merchaot) backslashParser);;
  let page = (char '\012');;
  let newline = (char '\n');;
  let return = (char '\r');;
  let tab = (char '\t');;
  let stringMetaChar = (disj_list [ tab; page; newline; return ; backslashParser]);;
  let stringMetaChar_ = pack (caten backslashParser stringMetaChar) (fun (c) -> (cdr c));;
  let stringChar = (disj stringMetaChar stringLiteralChar);;
  let string_no_spaces = (caten merchaot (caten (star stringChar) merchaot));;
  (* char *)
  let char_prefix = (caten hashtag backslashParser);;
    (* meta chars *)
  let newline_ = (word_ci "newline");;
  let return_ = (word_ci "return");;
  let page_ = (word_ci "page");;
  let nul_ = (word_ci "nul");;
  let space = (char ' ');;
  let space_ = (word_ci "space");;
  let tab_ = (word_ci "tab");;
  let packedline   = pack newline_ (fun (ds) -> '\n');;
  let packedret    = pack return_  (fun ds -> '\r');;
  let packed_page  = pack page_    (fun ds -> '\012');;
  let packed_nul   = pack nul_     (fun ds -> '\000');;
  let packed_space = pack space_   (fun ds -> ' ');;
  let packed_tab   = pack tab_     (fun ds -> '\t');;
  let namedChar = (disj_list [packed_nul; packedline; packedret; packed_tab; packed_page; packed_space]);;
  (* comments *)
  let num_and_rest = (our_star 0 sexp_pre_comment);;
  let make_paired nt_left nt_right nt =
    let nt = caten nt_left nt in
    let nt = pack nt (function (_, e) -> e) in
    let nt = caten nt nt_right in
    let nt = pack nt (function (e, _) -> e) in
    nt;;

  let make_quasi ch = (match ch with
  | '\'' -> "quote"
  | '`' -> "quasiquote,"
  | ',' -> "unquote"
  | _ -> "");;

  let rec nt_sexp_comm s = let nt = pack (caten sexp_pre_comment nt_sexp) (fun (p, s) -> 'c') in
    nt s
    and nt_white s = star (disj_list [nt_sexp_comm; packed_line_comment; nt_whitespace]) s
    and make_spaced nt s =
      make_paired nt_white nt_white nt s

    and lparen s =  char '(' s

    and rparen s =  char ')' s
    (* lists *)
    and quote_disj s = (disj quote (disj quasiQuote unQuote)) s
    and quote_no_spaces s =   quote_disj s
    and packed_sexp_comment s = pack sexp_comment (fun (ds) -> ';') s
    and build_pair list_ =
    match list_ with
    | [] -> Nil
    | [hd] -> Pair(hd,Nil)
    | hd :: tl -> Pair(hd,(build_pair tl))

    and  nt_list s =
    let nested = (caten (caten lparen (star nt_sexp)) rparen) in
    let packed = pack nested
    (fun (l) -> build_pair (cdr (car l))
    ) in
    packed s
    and nt_dotted_list s =
    let head = pack (caten (plus nt_sexp) dot ) (fun (p, o) -> p) in
    let tail = nt_sexp in
    let chain = (caten (caten lparen (caten head tail)) rparen) in
    let packed = pack chain
    (fun (hd, tl) ->
    List.fold_right (fun e aggr -> Pair (e, aggr)) (car (cdr hd)) (cdr (cdr hd))) in
    packed s
  (*fold gets a func, a list and a starting value *)
    and nt_quote s =
    let packed = pack (caten quote_no_spaces nt_sexp)
    (fun (ds) -> Pair(Symbol(make_quasi (car ds)), (Pair((cdr ds),Nil)))) in
    packed s
    and unquoteAndSplice_no_spaces s =  unquoteAndSplice  s
    and nt_unquoteAndSplice s =
    let packed = pack (caten unquoteAndSplice_no_spaces nt_sexp)
    (fun (ds) -> Pair(Symbol("unquote-splicing"), (Pair((cdr ds),Nil)))) in
    packed s
    and visibleSimpleChar s = (diff nt_any nt_whitespace) s
    and char_ s = (caten char_prefix (disj namedChar visibleSimpleChar)) s
    and nt_char s = pack  char_ (fun (p,c) -> Char(c)) s
    and string_ s = pack string_no_spaces (fun (_,(ds,_)) -> ds) s
    and nt_string s = pack string_ (fun (ds) -> String(list_to_string(ds))) s
    and nt_symbol s = pack  symbol_ (fun (c,ds) -> Symbol(list_to_string(c:: ds))) s
    and symbol_no_number s = (diff symbol_ number_disj) s
    and nt_symbol_no_number s =  pack  symbol_no_number (fun (c, ds) ->  Symbol(list_to_string(c:: ds))) s
    and nt_number s =  number_disj s
(* symbol_no_number cuz number is stupid with symbol *)
    and nt_number_not_followed s = not_followed_by nt_number nt_symbol_no_number s
    and bool_ s = pack  bool_no_spaces (fun (p,ds) -> ds) s
    and nt_bool s =
      pack bool_ (fun (ds) -> match ds with
      | 'f' -> Bool(false)
      | 'F' -> Bool(false)
      | _ -> Bool(true)
      )
       s
    and sexp_comment s = pack num_and_rest
    (* for now sexp_comment gives us an infinite loop *)
    (fun (ds) ->
    let num = car ds in
    let rest = cdr ds in
    (* (Printf.printf "%s\n" (list_to_string rest)); *)

    if (num == 0) then
    rest
    else
    cut num rest nt_sexp) s

    and nt_sexp s = make_spaced (disj_list [nt_string; nt_list; nt_number_not_followed; nt_bool; nt_char;
                                nt_symbol; nt_dotted_list; nt_quote;
                                nt_unquoteAndSplice ]) s;;

let read_sexprs string =
  let tokens = string_to_list string in
  let ast, rem = (star nt_sexp) tokens in
  (* (Printf.printf "%s\n" (list_to_string rem)); *)
    ast;;


end;; (* struct Reader *)
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
    | _ -> [Const(Sexpr(Symbol("whatever")))] @  (for_func_whatever list_ (length-1));;
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
and 
match_expr = function
| Pair(Symbol("quote"), Pair(x, Nil))                                      -> Const(Sexpr(x))
| Number(x)                                                                -> Const(Sexpr(Number(x)))
| Bool(x)                                                                  -> Const(Sexpr(Bool(x)))
| String(x)                                                                -> Const(Sexpr(String(x)))
| Char(x)                                                                  -> Const(Sexpr(Char(x)))
| Symbol(x)                                                                -> reserve(x)
| Pair(Symbol(x),Nil)                                                      -> reserve(x)  (* for the case of pair(symbol,nil) in a body of a lambda*)
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

(* /////////////////////////////////////////////// SEMANTIC ANALYZER/////////////////////////////////////////////////////// *)
#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;	
                      
exception X_syntax_error;;
exception X_hara of string list;;
exception X_annotate_is_tp;; 
exception X_box_set;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct
let rec is_bound x bounds  = match bounds with
    | [] -> false  
    | [a] -> if (List.mem x a)
             then true
             else false   
    | hd :: tl -> if (List.mem x hd)
                  then true
                  else is_bound x tl
    ;;  
let rec get_major x bounds index len = 
    match bounds with
    | [] -> -1
    | [a] -> if (List.mem x a)
             then index
             else -1 
    | hd :: tl -> if (List.mem x hd)
                  then index                            
                  else get_major x tl (index+1) len
    ;; 
  let rec get_num_param x param_list index =
      if x = (List.hd param_list) then index                
      else get_num_param x (List.tl param_list) (index + 1) ;;
  let make_var_bound x bounds = 
    let index_in_bounds_list = (get_major x bounds 0 (List.length bounds) ) in
    let pahot_ehad = index_in_bounds_list - 1 in
    let params_list = List.nth bounds index_in_bounds_list in
    Var'(VarBound(x, pahot_ehad , (get_num_param x params_list 0) ))
    ;;
  let check_var x params bounds =
      if List.mem x params then Var'(VarParam(x, get_num_param x params 0))
      else if (is_bound x bounds) then make_var_bound x bounds
      else Var'(VarFree(x));;
  let extract_string expr = match expr with
  | Var(x) -> x
  | _ -> raise X_no_match
  let ret_var_type expr = match expr with
  | Var'(x) -> x
  | _ ->raise X_no_match ;;
  let rec handle_define var_ val_ params bounds =
  let var_type = check_var (extract_string var_) params bounds in
  let var_v2 = ret_var_type var_type in
  Def'(var_v2,build_lexical params bounds val_) 
  and handle_set var_ val_ params bounds =
  let var_type = check_var (extract_string var_) params bounds in
  let var_v2 = ret_var_type var_type in
  Set'(var_v2,build_lexical params bounds val_) 
  and build_lexical params bounds e = match e with
  | Const(x) -> Const'(x)
  | Var(x) -> check_var x params bounds
  | If(test,then_,else_) -> If'(build_lexical  params bounds test
                                ,build_lexical  params bounds then_
                                , build_lexical params bounds else_)
  | Seq(exprs) -> Seq'(List.map (build_lexical params bounds) exprs)      (* i dont know why it's working *)
  | Applic(op,rands) -> Applic'(build_lexical params bounds op, List.map (build_lexical params bounds) rands)
  | Or(exprs) -> Or'(List.map (build_lexical params bounds) exprs)
  | Def(var_,val_) -> handle_define var_ val_ params bounds
  | Set(var_,val_) -> handle_set var_ val_ params bounds
  | LambdaSimple(args,body) -> LambdaSimple'(args, build_lexical args (args :: bounds) body)            
  | LambdaOpt(args,args_vs,body) ->  LambdaOpt'(args,args_vs, build_lexical (args @ [args_vs]) ((args @ [args_vs]) :: bounds) body  ) 
  ;;
let annotate_lexical_addresses e = 
  build_lexical [] [] e
  ;;   
let rec or_seq_tp is_tp exprs = match exprs with
    | [hd] -> [annotate_is_tp is_tp hd]
    | hd :: tl -> [annotate_is_tp false hd] @ or_seq_tp is_tp tl
    | _ -> raise X_no_match
and make_applic operator operands is_tp = 
  if is_tp = true then
  ApplicTP'(annotate_is_tp false operator , List.map (annotate_is_tp false) operands)
  else
  Applic'(annotate_is_tp false operator, List.map (annotate_is_tp false) operands)
and annotate_is_tp is_tp e = match e with
 | Var'(expr')                     -> Var'(expr')
 | Const'(expr')                   -> Const'(expr')
 | Applic'(operator, operands)     -> make_applic operator operands is_tp
 | LambdaSimple'(args,body)        -> LambdaSimple'(args, annotate_is_tp true body)
 | LambdaOpt'(args,args_vs,body)   -> LambdaOpt'(args ,args_vs, annotate_is_tp true body)
 | Seq'(exprs)                     -> Seq'(or_seq_tp is_tp exprs)
 | If'(test,then_,else_)           -> If'(annotate_is_tp false test, annotate_is_tp is_tp then_ , annotate_is_tp is_tp else_)
 | Set'(var_,expr')                -> Set'(var_, annotate_is_tp false expr')
 | Def'(var_,val_)                 -> Def'(var_, annotate_is_tp false val_)
 | Or'(exprs)                      -> Or'(or_seq_tp is_tp exprs)
 | _                               -> raise X_annotate_is_tp
  ;;
let annotate_tail_calls e =
  annotate_is_tp false e
  ;;
(* let rec find_get_and_set e pairs = 
  match e with
  | Var'(expr')                     -> if (List.mem expr' pairs) then 
  | Const'(expr')                   -> 
  | Applic'(operator, operands)     -> List.append pairs (find_get_and_set operator) 
  | LambdaSimple'(args,body)        -> find_get_and_set body) 
  | LambdaOpt'(args,args_vs,body)   -> LambdaOpt'(args ,args_vs, find_get_and_set body)
  | Seq'(exprs)                     -> Seq'(List.map find_get_and_set exprs)
  | If'(test,then_,else_)           -> If'(find_get_and_set test, find_get_and_set then_ , find_get_and_set else_)
  | Set'(var_,expr')                -> 
  | Def'(var_,val_)                 -> Def'(var_, find_get_and_set val_)
  | Or'(exprs)                      -> Or'(List.map find_get_and_set exprs)
  | _                               -> raise X_box_set
  ;; *)
(* 
find_get_and_set returns a list of (get,set) pairs
father is a list of booleans, for each pair in get_and_set, do they share a father?
check_lists does box if e is a var that has a pair && they dont have the same father
*)
let rec do_box_args args body = 
let set_list = List.map (fun (v) -> Set'(VarParam(v, (get_num_param v args 0)), Box'(VarParam(v,get_num_param v args 0)))) args in
Seq'(set_list @ [box_set body])

(* 
and args_loop args index = match args with
    | [a] ->  [Set'(VarParam(a, index), Box'(VarParam(a,index)))]
    | hd::tl ->  [Set'(VarParam(hd, index), Box'(VarParam(hd,index)))] @ args_loop tl (index+1) *)

and box_set e  =  
  (* let get_and_set_of_e = find_get_and_set e [] in
  let father = List.map no_father get_and_set_of_e in *)
  match e with
  | BoxSet'(var, expr')             -> BoxSet'(var, expr')
  | BoxGet'(expr')                  -> BoxGet'(expr')
  | Var'(VarFree(expr'))            -> Var'(VarFree(expr'))        (* check_lists get_and_set_of_e father *)
  | Var'(expr')                     -> BoxGet'(expr')      (* check_lists get_and_set_of_e father *)
  | Const'(expr')                   -> Const'(expr')
  | Applic'(operator, operands)     -> Applic'(box_set operator, List.map box_set operands)
  | ApplicTP'(operator, operands)   -> ApplicTP'(box_set operator, List.map box_set operands)
  | LambdaSimple'(args,body)        -> LambdaSimple'(args, do_box_args args body) 
  | LambdaOpt'(args,args_vs,body)   -> LambdaOpt'(args ,args_vs, do_box_args (args @ [args_vs]) body)
  | Seq'(exprs)                     -> Seq'(List.map box_set exprs)
  | If'(test,then_,else_)           -> If'(box_set test, box_set then_ , box_set else_)
  | Set'(VarFree(var_),expr')       -> Set'(VarFree(var_), box_set expr')   (* check_lists get_and_set_of_e father *)
  | Set'(var_,expr')                -> BoxSet'(var_,box_set expr')  (* check_lists get_and_set_of_e father *)
  | Def'(var_,val_)                 -> Def'(var_, box_set val_)
  | Or'(exprs)                      -> Or'(List.map box_set exprs)
  | _                               -> raise X_box_set
   ;;
let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
end;; (* struct Semantics *)
(* 
why is this function returning expr' -> expr' and not just expr'?
List.map (fun (e) ->


                                          match e with
                                          | hd :: [] -> annotate_is_tp is_tp
                                          | _        -> annotate_is_tp false   
                                          )                                     
                                          exprs
 *)

(* //////////////////////////////////// CODE GENERATOR ///////////////////////////// *)
#use "semantic-analyser.ml";;
(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
(* that code is weired *)
  let primitive_names = 
    ["boolean?"; "flonum?"; "rational?"; "pair?"; "null?"; "char?"; "string?";
 "procedure?"; "symbol?"; "string-length"; "string-ref"; "string-set!";
 "make-string"; "symbol->string"; "char->integer"; "integer->char";
 "exact->inexact"; "eq?"; "+"; "*"; "/"; "="; "<"; "numerator"; "denominator";
 "gcd";"car";"cdr";"set-car!";"set-cdr!";"cons";"apply"];;

 let rec ast_to_consts list_ expr  = match expr with
 | Const'(x)                       -> List.append [x] list_
 | BoxSet'(var, expr')             -> ast_to_consts list_ expr'  
 | Applic'(operator, operands)     -> List.flatten ( [ast_to_consts list_ operator] @ (List.map (ast_to_consts list_) operands) )
 | BoxGet'(x)                      -> []                           
 | Var'(x)                         -> []
 | Box'(x)                         -> []
 | ApplicTP'(operator, operands)   -> List.flatten ( [ast_to_consts list_ operator] @ (List.map (ast_to_consts list_) operands) )
 | LambdaSimple'(args,body)        -> ast_to_consts list_ body
 | LambdaOpt'(args,args_vs,body)   -> ast_to_consts list_ body
 | Seq'(exprs)                     -> List.flatten (List.map (ast_to_consts list_) exprs)
 | If'(test,then_,else_)           -> (ast_to_consts list_ test) @  (ast_to_consts list_ then_) @ (ast_to_consts list_ else_)
 | Set'(var_,expr')                -> ast_to_consts list_ expr'
 | Def'(var_,val_)                 -> ast_to_consts list_ val_
 | Or'(exprs)                      -> (List.flatten (List.map (ast_to_consts list_) exprs)) 
 
 
 
 let rec remove_dupes sexprs members_list = 
   match sexprs with
   | [] -> members_list
   | a :: b ->  if (List.mem a members_list) 
                 then remove_dupes b members_list 
                 else remove_dupes b (List.append members_list [a])
   ;;
 
 let rec check_constant_type  expr_ = match expr_ with
 | Void ->  []
 | Sexpr(x) -> check_nested_sexpr  x
 
 and check_nested_sexpr  sexpr_ = match sexpr_ with
  | Symbol(x) -> [Sexpr(String(x))] @ [Sexpr(Symbol(x))]
  | Pair(a,b) -> (check_nested_sexpr a) @ [Sexpr(a)]   @ (check_nested_sexpr  b) @ [Sexpr(b)] (* change**)
  | _ -> []
 
 
 and order_list list_ = match list_ with
   | [] -> list_
   | hd :: tl -> check_constant_type hd @ [hd] @ order_list tl
 ;;
 
 let find_size sexpr = match sexpr with
 | Void                         -> 1
 | Sexpr(Number(Fraction(a,b))) -> 17
 | Sexpr(Number(Float(a)))      -> 9
 | Sexpr(Bool(x))               -> 2
 | Sexpr(Char(x))               -> 2
 | Sexpr(String(x))             -> 9 + String.length x
 | Sexpr(Symbol(x))             -> 9
 | Sexpr(Pair(a,b))             -> 17
 | Sexpr(Nil)                   -> 1
 ;;
 
 let check_type_bool bool_ = if bool_ then "db T_BOOL, 1" else "db T_BOOL, 0" ;;

 let str_to_asciis str = 
  if String.length str = 0 then "\"\"" else
  let ascii_chars = List.map Char.code (string_to_list str) in
  let asciis = List.map (Printf.sprintf "%d") ascii_chars in
  String.concat ", " asciis;;

  let make_string_lit_string s = 
  let s = str_to_asciis s in
  "MAKE_LITERAL_STRING "^s;;
 
 let rec find_offset expr current_const_table =  match current_const_table with
 (*  *)
 | [] -> string_of_int (0)
 | (Sexpr(const),(off,str)) :: tl ->  if sexpr_eq expr const then string_of_int (off) else  find_offset expr tl
 | (Void, (off,str)) :: tl        ->  find_offset expr tl

 and find_offset_string str current_const_table = match current_const_table with
 | [] -> string_of_int (0)
 | (Sexpr(String(x)),(off,str_)) :: tl -> if  str = x  then string_of_int (off) else  find_offset_string str tl
 | hd :: tl -> find_offset_string str tl
 
 and check_type_sexpr offset expr current_const_table = match expr with
 | Void                         -> current_const_table @ [(expr, (offset, "db T_VOID"))] 
 | Sexpr(Number(Fraction(a,b))) -> current_const_table @ [(expr, (offset, "MAKE_LITERAL_RATIONAL("^string_of_int(a)^","^string_of_int(b)^")"))] 
 | Sexpr(Number(Float(a)))      -> current_const_table @ [(expr, (offset, "MAKE_LITERAL_FLOAT("^string_of_float(a)^")"))] 
 | Sexpr(Bool(x))               -> current_const_table @ [(expr, (offset, check_type_bool x))] 
 | Sexpr(String(x))             -> current_const_table @ [(expr, (offset, make_string_lit_string x))]
 | Sexpr(Char(x))               -> current_const_table @ [(expr, (offset, "MAKE_LITERAL_CHAR("^string_of_int(int_of_char(x))^")"))]
 | Sexpr(Symbol(x))             -> current_const_table @ [(expr, (offset, "MAKE_LITERAL_SYMBOL(const_tbl+"^find_offset_string x current_const_table^")"))] 
 | Sexpr(Pair (a,b))            -> current_const_table @ [(expr, (offset, "MAKE_LITERAL_PAIR(const_tbl+"^(find_offset a current_const_table)^",const_tbl+"^(find_offset b current_const_table)^")"))] 
 | Sexpr(Nil)                   -> current_const_table @ [(expr, (offset, "db T_NIL"))] 
 
 
 and build_const_table offset sexprs current_const_table  =
   match sexprs with 
   | [] -> current_const_table
   | hd :: tl ->  let shlomo = check_type_sexpr offset hd current_const_table in 
                   (build_const_table (offset + (find_size hd ) ) tl shlomo)
   ;;
 
 let make_consts asts = 
   let constants_list = [Void] @ [Sexpr(Nil)] @ [Sexpr(Bool(false))] @ [Sexpr(Bool(true))] @ List.flatten (List.map (ast_to_consts []) asts) in
   let constants_set = remove_dupes constants_list [] in
   let expanded_set =  (order_list constants_set )  in
   let expanded_set_no_dups = remove_dupes expanded_set [] in
   let const_table = build_const_table 0 expanded_set_no_dups [] in 
   const_table
   ;;
 
   let make_consts_tbl asts = make_consts asts;;


   let check_var_type var list_ = match var with
   | VarFree(x)       ->  List.append [x] list_
   | _                ->  list_
   
   let rec ast_to_fvars list_ expr  = match expr with
   | Const'(x)                       -> []
   | BoxSet'(var, expr')             -> check_var_type var list_  @ ast_to_fvars list_ expr'  
   | Applic'(operator, operands)     -> List.flatten ( [ast_to_fvars list_ operator] @ (List.map (ast_to_fvars list_) operands) )
   | BoxGet'(x)                      -> check_var_type x list_                           
   | Var'(x)                         -> check_var_type x list_
   | Box'(x)                         -> check_var_type x list_
   | ApplicTP'(operator, operands)   -> List.flatten ( [ast_to_fvars list_ operator] @ (List.map (ast_to_fvars list_) operands) )
   | LambdaSimple'(args,body)        -> ast_to_fvars list_ body
   | LambdaOpt'(args,args_vs,body)   -> ast_to_fvars list_ body
   | Seq'(exprs)                     -> List.flatten (List.map (ast_to_fvars list_) exprs)
   | If'(test,then_,else_)           -> (ast_to_fvars list_ test) @  (ast_to_fvars list_ then_) @ (ast_to_fvars list_ else_)
   | Set'(var_,expr')                -> check_var_type var_ list_ @ ast_to_fvars list_ expr'
   | Def'(var_,val_)                 -> check_var_type var_ list_ @ ast_to_fvars list_ val_
   | Or'(exprs)                      -> (List.flatten (List.map (ast_to_fvars list_) exprs)) 



   and build_fvar_table offset vars_set  =
     match vars_set with 
     | [] -> []
     | hd :: tl -> [(hd,offset)] @  (build_fvar_table (offset + 1 ) tl)
     ;;

   let make_fvars asts = 
   let vars_list = primitive_names @ List.flatten (List.map (ast_to_fvars []) asts) in
   let vars_set = remove_dupes vars_list [] in
   let fvars_table = build_fvar_table 0 vars_set in 
   fvars_table
    ;;
  let make_fvars_tbl asts = make_fvars asts;;

  let rec get_search_var fvars var_ = match fvars with
   | [] -> "\n"
   | (str,addr) :: tl -> if str = var_ then "mov rax, qword [fvar_tbl + "^string_of_int(addr)^"* WORD_SIZE]\n" else get_search_var tl var_
  ;;

  let rec set_search_var fvars var_ = match fvars with
  | [] -> "\n"
  | (str,addr) :: tl -> if str = var_ then "mov qword [fvar_tbl + "^string_of_int(addr)^"* WORD_SIZE], rax\n" else set_search_var tl var_
 ;;


  let const_string e consts  = 
    let address = find_offset e consts in
      "mov rax, const_tbl + "^address^"\n"

    let uniqe = -1;;

    let inc_uniqe =  uniqe + 1;;

    let get_handle_by_var_type consts fvars v = match v with
      | VarFree(v)              ->  get_search_var fvars v
      | VarBound(_,major,minor) ->  let major_ = string_of_int(major) in
                                    let minor_ = string_of_int(minor) in
                                   "mov rax, qword [rbp + 2 * WORD_SIZE]\n
                                    mov rax, qword [rax + " ^ major_ ^ " * WORD_SIZE ]\n
                                    mov rax, qword [rax + "^ minor_^"* WORD_SIZE ]\n"

      | VarParam(_,minor)       -> "mov rax, qword [rbp + (4 + "^string_of_int(minor)^") * WORD_SIZE]\n"

    let set_handle_by_var_type fvars v = match v with 
    | VarFree(v)              ->  set_search_var fvars v
    | VarBound(_,major,minor) ->  let major_ = string_of_int(major) in
                                  let minor_ = string_of_int(minor) in
                                 "mov rbx, qword [rbp + 2* WORD_SIZE]\n
                                  mov rbx, qword [rbx + " ^ major_ ^ "*WORD_SIZE ]\n
                                  mov qword [rbx + "^ minor_^" * WORD_SIZE], rax\n"

    | VarParam(_,minor)       -> "mov qword [rbp +  (4 + "^string_of_int(minor)^") * WORD_SIZE], rax\n"

  let if_unique  = ref 0;;
  let or_unique  = ref 0;;
  let lambda_unique  = ref 0;;


  let rec generate consts fvars expr' =  our_generate consts fvars expr' 0
(* 
pointers in ocaml:
:= is set
! is get
*)
  and our_generate consts fvars expr' env_deep = 
    match expr' with
    | Const'(Sexpr(e))         ->  const_string e consts
    | Const'(Void)             ->  "mov rax, const_tbl + 0\n" (*Garbage Collector*)
    | Var'(v)                  ->  get_handle_by_var_type consts fvars v  
    | Box'(v)                  ->  allocate_box consts fvars v env_deep
    | BoxSet'(v,expr)          ->  set_box v expr consts fvars env_deep
    | BoxGet'(v)               ->  (our_generate consts fvars (Var'(v)) env_deep) ^ "mov rax, qword[rax]\n"    
    | If'(test,then_,else_)    ->  if_to_string test then_ else_ consts fvars env_deep
    | Seq'(exprs)              ->  seq_to_string consts fvars exprs env_deep
    | Or'(exprs)               ->     or_unique := !or_unique + 1 ; or_to_string consts fvars exprs env_deep
    | Def'(var_,val_)          ->  set_define_to_string consts fvars val_ var_ env_deep
    | Set'(var_,val_)          ->  set_define_to_string consts fvars val_ var_ env_deep
    | Applic'(proc,args)       ->  (* "push SOB_NIL_ADDRESS\n" ^ *) applic_to_string consts fvars proc (List.rev args) (List.length args)  env_deep               
    | LambdaSimple'(args,body) ->  lambda_to_string consts fvars body (env_deep + 1)
    | ApplicTP'(proc,args)     -> (* "push SOB_NIL_ADDRESS\n" ^ *) applicTP_to_string consts fvars proc (List.rev args) (List.length args)  env_deep
    | LambdaOpt'(args,vs,body) ->  lambdaOPT_to_string consts fvars (List.length args) body (env_deep + 1)

and lambdaOPT_to_string consts fvars n body env_deep = 
lambda_unique := !lambda_unique + 1 ;
let unique_ = string_of_int(!lambda_unique) in
let env_deep_str = string_of_int(env_deep * 8) in
 "MALLOC rbx, "^ env_deep_str ^"\n
 ;; first loop for old env \n
 mov rcx, 0 \n
 mov rdx, 1 \n
 loop_1_" ^ unique_ ^ ":\n
 cmp rcx, "^ string_of_int(env_deep -1)^ "\n" ^
 "je " ^ "end_loop1_" ^ unique_^ "\n

;; mov rdi, qword [rbp + (rcx + 2*WORD_SIZE)]
;; mov qword [rbx + rdx * WORD_SIZE], rdi

  mov rax, qword[rbp + 2 * WORD_SIZE]   ;; pointer to env in 0 position
  mov rax, qword[rax + rcx * WORD_SIZE] ;; pointer to env in i position
  mov qword[rbx + rdx * WORD_SIZE], rax

  inc rcx \n
  inc rdx \n
  jmp loop_1_" ^ unique_ ^ "\n
 end_loop1_" ^ unique_^ ":\n" ^

 ";; second loop for new params \n
 mov rdx, qword[rbp + 3*WORD_SIZE] ;; number of params \n
 ;;cmp rdx, 0 \n
 ;;je end_loop2_" ^ unique_^ "\n
 shl rdx,3
 MALLOC rcx, rdx  \n 
 mov rdx, 0 \n
 loop_2_" ^ unique_^ ":\n
 cmp rdx, qword[rbp + 3*WORD_SIZE] \n ;; number of params(not args...)
 je end_loop2_" ^ unique_^ "\n
 
 mov rdi, PVAR(rdx) \n
 mov qword[rcx + rdx * WORD_SIZE],rdi \n

 inc rdx \n
 jmp loop_2_" ^ unique_ ^ "\n
 end_loop2_" ^ unique_ ^":\n" ^  
 "mov qword[rbx], rcx" ^

 ";; allocate the closure \n
 
 MAKE_CLOSURE(rax, rbx, Lcode_" ^ unique_ ^ ")\n" 
 ^ "jmp Lcont_" ^ unique_ ^ "\n
 Lcode_" ^ unique_ ^ ":\n" ^


 "\tpush rbp\n
 \tmov rbp, rsp \n" ^


 ";;adjust the stack
 mov rbx, qword[rbp + 3*WORD_SIZE]          ;; number of params on the stack. while i > n do the loop
 mov rcx, " ^ string_of_int(n) ^"           ;; args.length
 mov rdi, SOB_NIL_ADDRESS
 mov r9, SOB_NIL_ADDRESS                    ;; if we need 'magic' we push only magic
 ;; if args.length == [rbp+3] only push nil
 cmp rcx, qword[rbp + 3*WORD_SIZE]
  je end_adjust_" ^ unique_ ^ "
 mov rsi, qword [rbp + (3+rbx) * WORD_SIZE] ;; last element in the list
 MAKE_PAIR(r9, rsi , rdi)                   ;; always do 1 iteration
 dec rbx
 mov r12, 1                                 ;; list.length
 adjust_" ^ unique_ ^ ":
   cmp rbx, rcx
   je end_adjust_" ^ unique_ ^"
   mov r10, r9
   mov rsi, qword [rbp + (3+rbx) * WORD_SIZE]
   MAKE_PAIR(r9, rsi , r10)             
   dec rbx
   inc r12
   jmp adjust_" ^ unique_ ^ "
 end_adjust_" ^ unique_ ^ ": ;; list in r9
 ;; push list, push args 1-n, push frame stuff, shift frame, make rsp good
 push r9
 mov r10,rcx                  ;; do loop from n-1 to 0
 dec r10
 push_args_" ^ unique_ ^ ":
  cmp r10, -1
  je end_push_args_" ^ unique_ ^ "
  push PVAR(r10) 
  dec r10
  jmp push_args_" ^ unique_ ^ "
  end_push_args_" ^ unique_ ^ ":
inc rcx  
push rcx                           ;; new number of params
push qword [rbp+2*WORD_SIZE]       ;; env pointer
push qword [rbp+1*WORD_SIZE]       ;; ret address
push qword [rbp]                   ;; old rbp



;;mov rsi, qword [rbp+3*WORD_SIZE]
;;mov r8, qword [rbp]
;;mov rdi, "^ string_of_int(n) ^"

dec r12                            ;; length-1
SHIFT_FRAME ("^ string_of_int(n+5) ^") ;; size of old frame (including ret, env, old rbp, list and numParam)
;;sub rdi, rsi
;;dec rdi
;;shl rdi, 3
mov rsp, rbp                          ;; all the math relative to rbp!
;;sub rsp, rdi
shl r12, 3
cmp r9, SOB_NIL_ADDRESS
je do_magic_" ^ unique_ ^ "
add rsp, r12
mov rbp, rsp
jmp exit_opt_" ^ unique_ ^ "
;;mov rbp, r8

do_magic_" ^ unique_ ^ ":
sub rsp, 8
mov rbp, rsp

exit_opt_" ^ unique_ ^ ":

  \t" ^ our_generate consts fvars body env_deep  ^ 
 "\t mov rsp, rbp\n
  \t pop rbp\n
  \t ret \n" ^
 
 "Lcont_" ^ unique_ ^ ":\n"

and applicTP_to_string consts fvars proc args_rev n env_deep = 
match args_rev with 
| [] -> "push "^string_of_int(n)^"\n"^(cont_applicTP consts fvars proc n env_deep) 
| hd :: tl -> (our_generate consts fvars hd env_deep ) ^"push rax\n"^ (applicTP_to_string consts fvars proc tl n env_deep)

and cont_applicTP consts fvars proc n env_deep = 
(our_generate consts fvars proc env_deep )^
"CAR rbx, rax\n CDR rcx, rax\n push rbx\n push qword [rbp + 8 * 1] ; old ret addr
mov rsi, qword [rbp+3*WORD_SIZE]
mov r8, qword [rbp]
mov rdi, "^ string_of_int(n) ^ "
SHIFT_FRAME ("^ string_of_int(n+3) ^ ") ;;size of frame (including ret, env and numParam)
sub rdi, rsi
dec rdi
shl rdi, 3
mov rsp, rbp  ;; all the math relative to rbp!
sub rsp, rdi
mov rbp, r8
jmp rcx\n"

and allocate_box consts fvars v env_deep = 
our_generate consts fvars (Var'(v)) env_deep ^
"MALLOC rcx, 8\n" ^
"mov qword[rcx],rax\n" ^
" mov rax,rcx\n"^
";;mov rax, SOB_VOID_ADDRESS\n"

and set_box v expr consts fvars env_deep = 
our_generate consts fvars expr env_deep ^ "push rax \n"
^ our_generate consts fvars (Var'(v)) env_deep ^
"pop qword [rax] \n mov rax, SOB_VOID_ADDRESS\n"
(* 
nasm -f elf64 -o test/foo.o test/foo.s && gcc -static -m64 -o test/foo test/foo.o && mv test/foo /home/comp211/Desktop/compi/compiler
 *)


 and lambda_to_string consts fvars body env_deep = 
 lambda_unique := !lambda_unique + 1 ;
 let unique_ = string_of_int(!lambda_unique) in
 let env_deep_str = string_of_int(env_deep * 8) in
  "MALLOC rbx, "^ env_deep_str ^"\n
  ;; first loop for old env \n
  mov rcx, 0 \n
  mov rdx, 1 \n
  loop_1_" ^ unique_ ^ ":\n
  cmp rcx, "^ string_of_int(env_deep -1)^ "\n" ^
  "je " ^ "end_loop1_" ^ unique_^ "\n

 ;; mov rdi, qword [rbp + (rcx + 2*WORD_SIZE)]
 ;; mov qword [rbx + rdx * WORD_SIZE], rdi

   mov rax, qword[rbp + 2 * WORD_SIZE]   ;; pointer to env in 0 position
   mov rax, qword[rax + rcx * WORD_SIZE] ;; pointer to env in i position
   mov qword[rbx + rdx * WORD_SIZE], rax

   inc rcx \n
   inc rdx \n
   jmp loop_1_" ^ unique_ ^ "\n
  end_loop1_" ^ unique_^ ":\n" ^

  ";; second loop for new params \n
  mov rdx, qword[rbp + 3*WORD_SIZE] ;; number of params \n
  ;;cmp rdx, 0 \n
  ;;je end_loop2_" ^ unique_^ "\n
  shl rdx,3
  MALLOC rcx, rdx  \n 
  mov rdx, 0 \n
  loop_2_" ^ unique_^ ":\n
  cmp rdx, qword[rbp + 3*WORD_SIZE] \n ;; number of params(not args...)
  je end_loop2_" ^ unique_^ "\n
  
  mov rdi, PVAR(rdx) \n
  mov qword[rcx + rdx * WORD_SIZE],rdi \n

  inc rdx \n
  jmp loop_2_" ^ unique_ ^ "\n
  end_loop2_" ^ unique_ ^":\n" ^  
  "mov qword[rbx], rcx" ^

  ";; allocate the closure \n
  
  MAKE_CLOSURE(rax, rbx, Lcode_" ^ unique_ ^ ")\n" 
  ^ "jmp Lcont_" ^ unique_ ^ "\n
  Lcode_" ^ unique_ ^ ":\n" ^
  "\t push rbp\n
   \t mov rbp, rsp \n" ^
  "\t" ^ our_generate consts fvars body env_deep  ^ 
  "\t mov rsp, rbp\n
   \t pop rbp\n
   \t ret \n" ^
  
  "Lcont_" ^ unique_ ^ ":\n"

 and applic_to_string consts fvars proc args_rev n env_deep =
      match args_rev with 
    | [] -> "push "^string_of_int(n)^"\n"^(cont_applic consts fvars proc env_deep) 
    | hd :: tl -> (our_generate consts fvars hd env_deep ) ^"push rax\n"^ (applic_to_string consts fvars proc tl n env_deep)

  and cont_applic consts fvars proc env_deep = 
  (our_generate consts fvars proc env_deep )^
  "CAR rbx, rax\n push rbx\n CDR rcx, rax\n  call rcx\n"^                                          (*we need to check type closure?*)
  "add rsp, 8*1\n pop rbx\n shl rbx, 3\n add rsp, rbx\n "
 
 
 and set_define_to_string consts fvars expr' var_ env_deep=
    our_generate consts fvars expr' env_deep ^ 
    set_handle_by_var_type fvars var_ ^ "mov rax, SOB_VOID_ADDRESS\n"

  and or_to_string consts fvars exprs env_deep =
  let unique_ = string_of_int(!or_unique) in
  let exi = "Lexit_Or_"^unique_ in                       
   match exprs with
  | [] -> exi^":\n"
  | hd :: tl -> 
      (our_generate consts fvars hd env_deep) ^ "cmp rax, SOB_FALSE_ADDRESS\n" ^"jne "^exi^"\n"^ (or_to_string consts fvars tl env_deep) ^ "\n"


  and seq_to_string consts fvars exprs env_deep = match exprs with
    | [] -> "\n"
    | hd :: tl -> (our_generate consts fvars hd env_deep) ^ (seq_to_string consts fvars tl env_deep) 

  and if_to_string test then_ else_ consts fvars env_deep =
  let unique_ = string_of_int(!if_unique) in
  let les = "Lelse_"^unique_ in
  let exi = "Lexit_If_"^unique_ in
    if_unique := !if_unique + 1 ;
    (our_generate consts fvars test env_deep)^
    "cmp rax, SOB_FALSE_ADDRESS\n"^"je "^les^"\n"^
    (our_generate consts fvars then_ env_deep)^"jmp "^exi^"\n"^
     les ^ ":\n\t"^
    (our_generate consts fvars else_ env_deep)^exi^":\n\t"
  ;;


end;;
(* //////////////////////// end of CODE-GEN, start of runner ////////////////////////// *)


 let fvars s = 
    let sexprs = Reader.read_sexprs s in
    let expr_list = Tag_Parser.tag_parse_expressions sexprs in
    let expr'_list = List.map (Semantics.run_semantics) expr_list in
    Code_Gen.make_fvars_tbl expr'_list
      ;;

let consts s = 
  let sexprs = Reader.read_sexprs s in
  let expr_list = Tag_Parser.tag_parse_expressions sexprs in
  let expr'_list = List.map (Semantics.run_semantics) expr_list in
  Code_Gen.make_consts_tbl expr'_list
    ;;

let semantics s = 
  let sexprs = Reader.read_sexprs s in
  let expr_list = Tag_Parser.tag_parse_expressions sexprs in
  let expr'_list = List.map (Semantics.run_semantics) expr_list in
    expr'_list
    ;;

let read s = 
  let sexprs = Reader.read_sexprs s in
    sexprs
    ;;
    
let tag_parser s = 
  let sexprs = Reader.read_sexprs s in
  let expr_list = Tag_Parser.tag_parse_expressions sexprs in
    expr_list
        ;;

       (* [("boolean?",0); ("flonum?",8); ("rational?",16); ("pair?",24); ("null?",32); ("char?",40); ("string?",48);
  ("procedure?",56); ("symbol?",64); ("string-length",72); ("string-ref",80); ("string-set!",88);
  ("make-string",96); ("symbol->string",104); ("char->integer",112); ("integer->char",120);
  ("exact->inexact",128); ("eq?",136); ("+",144); ("*",152); ("/",160); ("=",168); ("<",176); ("numerator",184); ("denominator",192);
  ("gcd",200)] @  *)