
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
  | Var'(expr')                     -> BoxGet'(expr')       (* check_lists get_and_set_of_e father *)
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