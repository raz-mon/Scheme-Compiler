#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> 
  if (List.length sexprs1) = (List.length sexprs2) 
    then List.for_all2 sexpr_eq sexprs1 sexprs2
    else false
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let is_reserved_word_sexpr s = match s with
  | ScmSymbol(sym) -> (List.mem sym reserved_word_list)
  | _ -> raise (X_syntax_error(s, "Problem occured while checking for if a symbol is a resereved word."))

let is_reserved_word_sexpr_no_exception s = match s with
  | ScmSymbol(sym) -> (List.mem sym reserved_word_list)
  | _ -> false

let is_reserved s = (List.length (List.filter (fun str -> (String.equal str s) ) reserved_word_list ) > 0 )

let no_resereved_in_scm_list scm_list_ = 
  let li = scm_list_to_list scm_list_ in
  List.length (List.filter (fun sexpr_ -> is_reserved_word_sexpr sexpr_ ) li ) = 0 


let rec improper_to_string_list = (fun l -> match l with
  | ScmPair(ScmSymbol(x),ScmSymbol(y))  when not (is_reserved x) &&  not (is_reserved y)-> x::y::[]
  | ScmPair(ScmSymbol(x),rest) when not (is_reserved x) -> x::(improper_to_string_list rest)
  | _ -> raise (X_syntax_error (l, "Sexpr structure not recognized")))

let rec get_proper_args= (fun l -> match l with
            | [] -> []
            | head::tail::[] -> head::[]
            | head::tail -> head::(get_proper_args tail))

let scm_list_no_name_twice scm_list_ = 
  let li = scm_list_to_list scm_list_ in
  if List.for_all (fun name -> (List.length (List.filter (fun s -> sexpr_eq name s) li) ) = 1 ) li then true else
    raise (X_syntax_error(scm_list_, "List of arguments containes duplicates!"))


let rec expand_quasi sexpr = 
  
  match sexpr with
  | ScmPair(ScmSymbol("unquote"), ScmPair(sexpr_, ScmNil) ) -> sexpr_
  | ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexpr_, ScmNil) ) -> 
      ScmPair(ScmSymbol("quote"), ScmPair(sexpr, ScmNil) )
  | ScmSymbol(sym) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol(sym), ScmNil) ) 
  | ScmNil -> ScmPair(ScmSymbol("quote"), ScmPair(ScmNil, ScmNil) )
  | ScmPair(sexpr1, sexpr2 ) -> 
      begin
        match sexpr1 with
        | ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexpr_, ScmNil) ) -> 
            ScmPair(ScmSymbol("append"), ScmPair(sexpr_, ScmPair( (expand_quasi sexpr2), ScmNil) ) )
        | _ -> ScmPair(ScmSymbol("cons"), ScmPair(expand_quasi sexpr1, ScmPair(expand_quasi sexpr2, ScmNil) ) )
      end
  
  | ScmVector(slist) -> 
      let expanded_list = expand_quasi (list_to_proper_list slist) in
      ScmPair(ScmSymbol("list->vector"), ScmPair(expanded_list, ScmNil) )

  | _ -> sexpr
  

  


(* Implement tag parsing here *)
let rec tag_parse_expression sexpr =
  let sexpr = macro_expand sexpr in
  match sexpr with 
  (* Implement tag parsing here *)
  | ScmNil -> (ScmConst sexpr)
  | ScmBoolean(x) -> ScmConst (sexpr)
  | ScmChar(x) -> ScmConst (sexpr)
  | ScmNumber(ScmReal x) -> ScmConst (sexpr)
  | ScmNumber(ScmRational (x,y)) -> ScmConst (sexpr)
  | ScmString(x) -> ScmConst(sexpr)
  
  | ScmSymbol(s) ->
    if (is_reserved s) then (raise (X_reserved_word s)) else ScmVar(s)
  
  | ScmPair(ScmSymbol "quote", ScmPair(next_sexper, ScmNil) ) -> ScmConst(next_sexper)

  | ScmPair(ScmSymbol "if", ScmPair(test, ScmPair(dit, ScmNil) ) ) ->
    ScmIf((tag_parse_expression test), (tag_parse_expression dit), ScmConst ScmVoid)

  | ScmPair(ScmSymbol "if", ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil) ) ) ) -> 
      ScmIf((tag_parse_expression test),(tag_parse_expression dit),(tag_parse_expression dif))
(*
  | ScmPair(ScmSymbol "if", ScmPair(test, ScmPair(dit, dif ) ) ) -> 
    ScmIf((tag_parse_expression test),(tag_parse_expression dit),(tag_parse_expression dif))
*)
      
  | ScmPair(ScmSymbol "or", ScmNil) -> ScmConst(ScmBoolean false)
  | ScmPair(ScmSymbol "or", ScmPair(a, ScmNil)) -> tag_parse_expression a
  | ScmPair(ScmSymbol "or", sexpr) -> 
      let expr_list = scm_list_to_list sexpr in
      let expr_list = List.map (fun sexpr -> (tag_parse_expression sexpr)) expr_list in
      ScmOr expr_list

  | ScmPair(ScmSymbol "define", ScmPair(ScmSymbol(var), ScmPair(val_, ScmNil) ) ) when not (is_reserved var) -> 
      ScmDef(ScmVar(var), (tag_parse_expression val_))

  | ScmPair(ScmSymbol "set!", ScmPair(var, ScmPair(val_, ScmNil) ) ) -> 
    let var_expr = try (tag_parse_expression var)
      with X_reserved_word(s) -> raise (X_syntax_error (sexpr, "Expected variable on LHS of set!")) in
    let res = match var_expr with
    | ScmVar(x) -> ScmSet(var_expr, (tag_parse_expression val_))
    | _ -> raise (X_syntax_error(sexpr, "Expected variable on LHS of set!")) in
    res

    | ScmPair(ScmSymbol "begin", ScmPair(rest, ScmNil)) -> tag_parse_expression rest
    | ScmPair(ScmSymbol "begin", rest) when scm_is_list rest -> ScmSeq (List.map tag_parse_expression (scm_list_to_list rest))
  
    | ScmPair(ScmSymbol "define", ScmPair(ScmPair(var, rest), body) ) ->
    let newSexpr = 
      ScmPair
      (ScmSymbol "define",
      ScmPair(var, 
              ScmPair(ScmPair(ScmSymbol "lambda", 
                              ScmPair(rest, body)), 
                      ScmNil) ) ) in
      tag_parse_expression newSexpr

        (* Variadic lambda *)
  | ScmPair(ScmSymbol "lambda", ScmPair(ScmSymbol(var), body ) ) when not (is_reserved var) ->
      begin match body with 
        | ScmPair(body1, ScmNil) -> ScmLambdaOpt([], var, (tag_parse_expression body1) )
        | _ -> 
          let body_list = (scm_list_to_list body) in
          let body_list_exprs = List.map (fun s -> (tag_parse_expression s) ) body_list in
          ScmLambdaOpt([], var, ScmSeq(body_list_exprs))
      end

        (* Lambda simple *)
  | ScmPair(ScmSymbol "lambda", ScmPair(args, body )) when (scm_is_list args) &&
                                                           (no_resereved_in_scm_list args) && 
                                                           (scm_list_no_name_twice args) ->
    let args_list = (scm_list_to_list args) in
    let args_string_list = (List.map (fun var -> 
                                          match var with
                                          | ScmSymbol(s) -> s
                                          | _ -> raise (X_syntax_error(sexpr, "One of the vars in not a symbol!")) ) args_list) in
      (begin match body with 
        | ScmPair(body1, ScmNil) -> ScmLambdaSimple(args_string_list, tag_parse_expression body1 )
        | _ -> 
          let body_list = (scm_list_to_list body) in
          let body_list_exprs = (List.map (fun s -> (tag_parse_expression s) ) body_list ) in
          ScmLambdaSimple(args_string_list, ScmSeq(body_list_exprs) )
      end)

        (* LambdaOpt, with improper list as arguments *)
  | ScmPair(ScmSymbol "lambda", ScmPair(args, body) ) when 
      (List.for_all (fun s -> not (is_reserved s) ) (improper_to_string_list args)) &&
      (List.for_all (fun name -> 
        (List.length (List.filter (fun s -> 
          String.equal name s) (improper_to_string_list args)) ) = 1 ) (improper_to_string_list args))
                      -> 
    (*improper_to_string_list takes all symbols in the improper list to a string list, and checks reserved words
    Replace with two function later if have the time.*)
    let args_string_list = (improper_to_string_list args) in
    (* The two rows below are in comment since they raise an 'unused var' exception. They where lifted to the 
    'when' position on top. *)
    (*let no_reserved = (List.for_all (fun s -> not (is_reserved s) ) args_string_list) in
    let no_name_twice = List.for_all (fun name -> 
      (List.length (List.filter (fun s -> 
        String.equal name s) args_string_list) ) = 1 ) args_string_list in*)
    let all_args_but_last = (get_proper_args args_string_list) in
    let last_arg = (List.nth args_string_list ((List.length args_string_list) - 1) ) in  
      (begin match body with 
        | ScmPair(body1, ScmNil) -> ScmLambdaOpt(all_args_but_last, last_arg, (tag_parse_expression body1) )
        | _ -> 
          let body_list = (scm_list_to_list body) in
          let body_list_exprs = (List.map (fun s -> (tag_parse_expression s) ) body_list ) in
          ScmLambdaOpt(all_args_but_last, last_arg, ScmSeq(body_list_exprs) )
      end)

  | ScmPair(sexpr1, ScmNil) when not (is_reserved_word_sexpr_no_exception sexpr1)->
      ScmApplic(tag_parse_expression sexpr1, []) 
  | ScmPair(sexpr1, rest ) when not (is_reserved_word_sexpr_no_exception sexpr1)->
      let rest_list = List.map tag_parse_expression (scm_list_to_list rest) in
      ScmApplic(tag_parse_expression sexpr1, rest_list)

  | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and macro_expand sexpr =
match sexpr with


    (*  let  *)
| ScmPair(ScmSymbol("let"), ScmPair(ribs, body)) -> 
  let make_applic lambda_ args_ = ScmPair(lambda_, args_ ) in
  let make_lambda params_ body_ = ScmPair(ScmSymbol("lambda"), ScmPair(params_, body)) in
  
  let ribs_list = scm_list_to_list ribs in
  let params = (List.map (fun li -> macro_expand (List.nth (scm_list_to_list li) 0) ) ribs_list) in
  let params = (List.fold_right (fun s1 s2 -> ScmPair(s1, s2)) params ScmNil) in
  let args = (List.map (fun li -> macro_expand (List.nth (scm_list_to_list li) 1) ) ribs_list) in
  let args = (List.fold_right (fun exp_ acc -> ScmPair(exp_, acc) ) args ScmNil) in

  let lam = (make_lambda params body) in
  (make_applic lam args)

| ScmPair(ScmSymbol("let*"),  ScmPair(ScmNil, body) ) ->
    macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body) ) )

| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(ScmPair(ScmSymbol(var), ScmPair(expr_, ScmNil) ), ScmNil), body ) ) ->
  macro_expand (ScmPair(ScmSymbol("let"), 
  ScmPair(
    ScmPair(
      ScmPair(ScmSymbol(var), ScmPair(expr_, ScmNil) ), ScmNil), body ) ))

| ScmPair(ScmSymbol("let*"), ScmPair(ribs, body) ) ->
  let ribs_list = scm_list_to_list ribs in
  let rest_ribs = list_to_proper_list (List.tl ribs_list) in
  let ribs_list_of_lists = List.map (fun rib -> scm_list_to_list rib) ribs_list in
  let first_rib = (List.hd ribs_list_of_lists) in
  let first_rib = list_to_proper_list first_rib in
  let new_first_rib = ScmPair(first_rib, ScmNil) in
  let new_body = ScmPair(ScmSymbol("let*"), ScmPair(rest_ribs, body) ) in

  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(new_first_rib, ScmPair(new_body, ScmNil) ) ) )

| ScmPair(ScmSymbol("letrec"), ScmPair(ribs, body) ) -> 
  let ribs_list = scm_list_to_list ribs in
  let ribs_list_of_lists = List.map (fun rib -> scm_list_to_list rib) ribs_list in

  (*let make_new_rib var = ScmPair(var, ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("whatever"), ScmNil ) ), ScmNil) ) in *)
  let make_set_exp var sexpr_ = ScmPair(ScmSymbol("set!"), ScmPair(var, ScmPair(sexpr_, ScmNil) ) ) in

  let new_body_set_part_list = List.map (fun rib -> 
                    make_set_exp (List.hd rib ) 
                                 (List.hd (List.tl rib)) ) ribs_list_of_lists in

  let new_body_set_part = list_to_proper_list new_body_set_part_list in

  let new_body = scm_append new_body_set_part body in

  let new_ribs_list = List.map (fun rib_list_ -> [List.hd rib_list_; 
          ScmPair (ScmSymbol "quote", ScmPair (ScmSymbol "whatever", ScmNil)) ]) ribs_list_of_lists in
  let new_ribs = List.map list_to_proper_list new_ribs_list in
  let new_ribs = list_to_proper_list new_ribs in

  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(new_ribs, new_body) ) )

| ScmPair(ScmSymbol "and", ScmNil) -> macro_expand (ScmBoolean(true))
| ScmPair(ScmSymbol("and"), ScmPair(sexpr_, ScmNil) ) -> macro_expand sexpr_
| ScmPair(ScmSymbol("and"), ScmPair(test1, rest) ) ->
    ScmPair(ScmSymbol("if"), ScmPair(macro_expand test1, ScmPair(macro_expand (ScmPair(ScmSymbol("and"), 
      rest )), ScmPair( 
macro_expand (ScmBoolean(false) ), ScmNil ) ) ) )


| ScmPair(ScmSymbol "cond", rest) ->  
  let make_simple_ribs test body rest = ScmPair(ScmSymbol "if", ScmPair(test, ScmPair
    (ScmPair(ScmSymbol "begin", body), rest))) in

  let make_lambda_empty body = ScmPair(ScmSymbol "lambda",ScmPair (ScmNil, ScmPair (body, ScmNil))) in
  let make_let_value value = ScmPair (ScmSymbol "value", ScmPair (macro_expand value, ScmNil)) in
  let make_let_f f = ScmPair(ScmSymbol "f", ScmPair(make_lambda_empty (macro_expand f), ScmNil)) in
  let make_let_rest rest = ScmPair(ScmSymbol "rest", ScmPair(make_lambda_empty rest, ScmNil)) in

  let constract_let_ribs value f rest = ScmPair(make_let_value value, ScmPair(make_let_f f, ScmPair(make_let_rest rest, ScmNil))) in
  let constract_let_body = ScmPair
  (ScmSymbol "if",
   ScmPair
    (ScmSymbol "value",
     ScmPair
      (ScmPair
        (ScmPair (ScmSymbol "f", ScmNil),
         ScmPair (ScmSymbol "value", ScmNil)),
       ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))) in
  let constract_let value f rest = ScmPair(ScmSymbol "let", ScmPair(constract_let_ribs value f rest, ScmPair(constract_let_body, ScmNil))) in

  let make_else_rib body = ScmPair(ScmSymbol "begin", macro_expand body) in
  let rec expand_cond rest = begin match rest with
                        | ScmPair(ScmPair(ScmSymbol "else", rest), _)  when scm_is_list rest -> make_else_rib rest
                        | ScmPair(ScmPair(test, ScmPair(ScmSymbol "=>", ScmPair(f, ScmNil))), rest) -> macro_expand (constract_let test f (expand_cond rest))
                        | ScmPair(ScmPair(test, body), ScmNil) -> make_simple_ribs test body ScmNil
                        | ScmPair(ScmPair(test, body), rest) -> make_simple_ribs test body (ScmPair((expand_cond rest), ScmNil))
                        | _ -> rest end in
                        (*| _ -> raise (X_syntax_error (rest, "Cond - Sexpr structure not recognized")) end in*)
    expand_cond rest
 
| ScmPair(ScmSymbol("quasiquote"), ScmPair(sexpr_, ScmNil ) ) ->  expand_quasi sexpr_

      (*  Vector  *)
| ScmVector(slist) -> ScmVector(List.map (fun s -> (macro_expand s) ) slist)

       (*  Pair  *)
  | ScmPair(s1, s2) -> ScmPair(macro_expand s1, macro_expand s2)

  | _ -> sexpr


  

(* ScmPair() *)

end;; 
