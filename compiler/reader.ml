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
