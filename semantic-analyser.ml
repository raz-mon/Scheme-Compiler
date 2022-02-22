(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
  match v1, v2 with
    | VarFree (name1), VarFree (name2) -> String.equal name1 name2
    | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
      major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
    | VarParam (name1, index1), VarParam (name2, index2) ->
          index1 = index2 && (String.equal name1 name2)
    | _ -> false
  
  let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;

  let unannotate_lexical_address = function
| (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name





let rec unanalyze expr' =
match expr' with
  | ScmConst' s -> ScmConst(s)
  | ScmVar' var -> unannotate_lexical_address var
  | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
  | ScmBoxGet' var -> unannotate_lexical_address var
  | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
  | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
  | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
  | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
  | ScmLambdaSimple' (params, expr') ->
        ScmLambdaSimple (params, unanalyze expr')
  | ScmLambdaOpt'(params, param, expr') ->
        ScmLambdaOpt (params, param, unanalyze expr')
  | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
        ScmApplic (unanalyze expr', List.map unanalyze expr's)

let string_of_expr' expr' =
    string_of_expr (unanalyze expr')



    
let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        list_eq expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
      (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
  (* THOSE FUNCTIONS SHOULD BE DELITED *)
  (* val find_reads : string -> expr' -> expr' -> expr' list 
  val find_writes : string -> expr' -> expr' -> expr' list
  val box_var : string -> expr' -> expr' *)
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  let extend_env env params = 
    params :: env;;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
      | ScmConst(sexpr_) -> ScmConst'(sexpr_)
      | ScmVar(s) -> ScmVar'(tag_lexical_address_for_var s params env)
      | ScmIf(expr1, expr2, expr3) -> 
        ScmIf'(run expr1 params env, run expr2 params env, run expr3 params env)
      | ScmSeq(expr_list) -> ScmSeq'(List.map (fun expr_ -> run expr_ params env) expr_list)
      | ScmSet(expr1, expr2) -> 
        (match expr1 with 
        | ScmVar(s) -> ScmSet'(tag_lexical_address_for_var s params env, 
                                      run expr2 params env)
        | _ -> raise X_this_should_not_happen)

      | ScmDef(expr1, expr2) -> 
        (match expr1 with 
        | ScmVar(s) -> ScmDef'(tag_lexical_address_for_var s params env, 
                                      run expr2 params env)
        | _ -> raise X_this_should_not_happen)

      | ScmOr(expr_list) -> ScmOr'(List.map (fun expr_ -> run expr_ params env) expr_list)
      | ScmLambdaSimple(s_list, expr_) -> ScmLambdaSimple'(s_list, run expr_ s_list (extend_env env params) )
      | ScmLambdaOpt(s_list, s, expr_) -> ScmLambdaOpt'(s_list, s, run expr_ (List.append s_list [s]) (extend_env env params))
      | ScmApplic(expr_, expr_list) -> ScmApplic'(run expr_ params env, List.map (fun expr_ -> run expr_ params env) expr_list )
   in 
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail = 
      match pe with
        | ScmSeq'(expr_list) -> 
          if (not in_tail) 
            then ScmSeq' (List.map (fun b -> run b in_tail) expr_list)
            else 
              let pair = rdc_rac expr_list in
              let app p = (match p with
                | (a,b) -> List.append (List.map (fun b -> run b false) a) [run b true]) in
              let new_expr_list = app pair in
              ScmSeq'(new_expr_list)
        | ScmOr'(expr_list) -> if (not in_tail) 
            then ScmOr' (List.map (fun b -> run b in_tail) expr_list)
            else 
              let pair = rdc_rac expr_list in
              let app p = (match p with
                | (a,b) -> List.append (List.map (fun b -> run b false) a) [run b true]) in
              let new_expr_list = app pair in
              ScmOr'(new_expr_list)
        | ScmSet' (v,e) -> ScmSet'(v, run e false)
        | ScmApplic'(s, args) -> 
          if in_tail 
            then ScmApplicTP'(run s false, List.map (fun b -> run b false) args) 
            else ScmApplic'(run s false, List.map (fun b -> run b in_tail) args)
          
        | ScmIf'(test, dit, dif) -> ScmIf'(test, run dit in_tail, run dif in_tail)
        | ScmLambdaSimple'(s, body) -> ScmLambdaSimple'(s, run body true)
        | ScmLambdaOpt'(l,s,e) -> ScmLambdaOpt'(l,s,run e true)
        | ScmDef'(var', expr') -> ScmDef'(var', run expr' false)
        | _ -> pe in 
   run pe false;;

  (* boxing *)

  let appears_in_args name s_list = not (List.for_all (fun s -> not (String.equal s name)) s_list);;

  (* remove duplicates in a list (from the right, keeping order). *)  
  let uniq_cons x xs = if List.mem x xs then xs else x :: xs;;
  let remove_from_right xs = List.fold_right uniq_cons xs [];;

  
  let rec find_second_reads name enclosing_lambda expr = 
    match expr with

    (* if expr is a single expression: *)
    | ScmLambdaSimple'(s_list, body) ->
        if not (appears_in_args name s_list) then find_second_reads name enclosing_lambda body else []
    
    | ScmLambdaOpt'(s_list, s, body) -> 
        if not (appears_in_args name (s :: s_list) ) then find_second_reads name enclosing_lambda body else []        
      
    | ScmApplic'(func, expr_list) -> 
      let li_args = List.map (find_second_reads name enclosing_lambda) expr_list in
      let li_args = List.flatten li_args in
      let li_func = find_second_reads name enclosing_lambda func in
      List.append li_args li_func

    | ScmApplicTP'(func, expr_list) -> 
      let li_args = List.map (find_second_reads name enclosing_lambda) expr_list in
      let li_args = List.flatten li_args in
      let li_func = find_second_reads name enclosing_lambda func in
      List.append li_args li_func

    | ScmIf'(test, dit, dif) ->
      List.append (find_second_reads name enclosing_lambda test) 
                  (List.append 
                  (find_second_reads name enclosing_lambda dit) 
                      (find_second_reads name enclosing_lambda dif) ) 
                
    | ScmOr'(expr_list) -> 
      let li = List.map (find_second_reads name enclosing_lambda) expr_list in
      List.flatten li
      
    | ScmSet'(var', expr_) -> find_second_reads name enclosing_lambda expr_

    (* if expr (the body) is a sequence: *)
    | ScmSeq'(expr_list) -> 
      let li = List.map (find_second_reads name enclosing_lambda) expr_list in
      List.flatten li

    | ScmVar'(v) -> 
      (match v with
      | VarFree(s) when s = name -> [enclosing_lambda]
      | VarParam(s, minor) when s = name -> [enclosing_lambda]
      | VarBound(s, minor, major) when s = name -> [enclosing_lambda]
      | _ -> [])

    | ScmBoxSet'(v, expr_) -> find_second_reads name enclosing_lambda expr_

    (* All other cases (ScmConst', ScmBoxGet') cannot contain name --> We don't look in them. *)
    | _ -> [];;


  let rec find_first_reads name enclosing_lambda expr = 
    match expr with

    (* if expr is a single expression: *)
    | ScmLambdaSimple'(s_list, body) ->
        if not (appears_in_args name s_list) then find_second_reads name expr body else []
    
    | ScmLambdaOpt'(s_list, s, body) -> 
        if not (appears_in_args name (s :: s_list) ) then find_second_reads name expr body else []        
       
    | ScmApplic'(func, expr_list) -> 
      let li_args = List.map (find_first_reads name enclosing_lambda) expr_list in
      let li_args = List.flatten li_args in
      let li_func = find_first_reads name enclosing_lambda func in
      List.append li_args li_func

    | ScmApplicTP'(func, expr_list) -> 
      let li_args = List.map (find_first_reads name enclosing_lambda) expr_list in
      let li_args = List.flatten li_args in
      let li_func = find_first_reads name enclosing_lambda func in
      List.append li_args li_func

    | ScmIf'(test, dit, dif) ->
      List.append (find_first_reads name enclosing_lambda test) 
                  (List.append 
                      (find_first_reads name enclosing_lambda dit)
                      (find_first_reads name enclosing_lambda dif) )
                
    | ScmOr'(expr_list) -> 
      let li = List.map (find_first_reads name enclosing_lambda) expr_list in
      List.flatten li
      
    | ScmSet'(var', expr_) -> find_first_reads name enclosing_lambda expr_

    (* if expr (the body) is a sequence: *)
    | ScmSeq'(expr_list) -> 
      let li = List.map (find_first_reads name enclosing_lambda) expr_list in
      List.flatten li

    | ScmVar'(var') -> 
      (match var' with
      | VarFree(s) when s = name -> [enclosing_lambda]
      | VarParam(s, minor) when s = name -> [enclosing_lambda]
      | VarBound(s, minor, major) when s = name -> [enclosing_lambda]
      | _ -> [])

    | ScmBoxSet'(v, expr_) -> find_first_reads name enclosing_lambda expr_

    (* All other cases (ScmConst', ScmBoxGet') cannot contain name --> We don't look in them. *)
    | _ -> [];;

    
  let find_reads name enclosing_lambda expr = 
    (* Return a list of lambdas in which there is a read to variable name.
        Practically, we will return a list of lambdas that read name only from the first (enclosing lambda) and second level. *)
    let li = find_first_reads name enclosing_lambda expr in 
    (* clean all of the duplicates from the list, return the cleaned list. (Replace next line..) *)
    remove_from_right li;;



  let rec find_second_writes name enclosing_lambda expr = 
    match expr with

    (* if expr is a single expression: *)
    | ScmLambdaSimple'(s_list, body) ->
        if not (appears_in_args name s_list) then find_second_writes name enclosing_lambda body else []
    
    | ScmLambdaOpt'(s_list, s, body) -> 
        if not (appears_in_args name (s :: s_list) ) then find_second_writes name enclosing_lambda body else []        
    
    | ScmApplic'(func, expr_list) -> 
      let li_args = List.map (find_second_writes name enclosing_lambda) expr_list in
      let li_args = List.flatten li_args in
      let li_func = find_second_writes name enclosing_lambda func in
      List.append li_args li_func

    | ScmApplicTP'(func, expr_list) -> 
      let li_args = List.map (find_second_writes name enclosing_lambda) expr_list in
      let li_args = List.flatten li_args in
      let li_func = find_second_writes name enclosing_lambda func in
      List.append li_args li_func

    | ScmIf'(test, dit, dif) ->
      List.append (find_second_writes name enclosing_lambda test) 
                  (List.append 
                      (find_second_writes name enclosing_lambda dit)
                      (find_second_writes name enclosing_lambda dif) )
                
    | ScmOr'(expr_list) -> 
      let li = List.map (find_second_writes name enclosing_lambda) expr_list in
      List.flatten li
      
    | ScmSet'(v, expr_) ->
      let li_v = (match v with 
        | VarFree(s) when s = name -> [enclosing_lambda]
        | VarParam(s, minor) when s = name -> [enclosing_lambda] 
        | VarBound(s, minor, major) when s = name -> [enclosing_lambda]
        | _ -> []) in
      
      let li_expr = find_second_writes name enclosing_lambda expr_ in
      List.append li_v li_expr

    (* if expr (the body) is a sequence: *)
    | ScmSeq'(expr_list) -> 
      let li = List.map (find_second_writes name enclosing_lambda) expr_list in
      List.flatten li

    | ScmBoxSet'(var', expr_) -> find_second_writes name enclosing_lambda expr_

    (* All other cases (ScmConst', ScmBoxGet') cannot contain name --> We don't look in them. *)
    | _ -> [];;


  let rec find_first_writes name enclosing_lambda expr = 
    match expr with

    (* if expr is a single expression: *)
    | ScmLambdaSimple'(s_list, body) ->
        if not (appears_in_args name s_list) then find_second_writes name expr body else []
    
    | ScmLambdaOpt'(s_list, s, body) -> 
        if not (appears_in_args name (s :: s_list) ) then find_second_writes name expr body else []        
     
    | ScmApplic'(func, expr_list) -> 
      let li_args = List.map (find_first_writes name enclosing_lambda) expr_list in
      let li_args = List.flatten li_args in
      let li_func = find_first_writes name enclosing_lambda func in
      List.append li_args li_func

    | ScmApplicTP'(func, expr_list) -> 
      let li_args = List.map (find_first_writes name enclosing_lambda) expr_list in
      let li_args = List.flatten li_args in
      let li_func = find_first_writes name enclosing_lambda func in
      List.append li_args li_func

    | ScmIf'(test, dit, dif) ->
      List.append (find_first_writes name enclosing_lambda test) 
                  (List.append 
                      (find_first_writes name enclosing_lambda dit)
                      (find_first_writes name enclosing_lambda dif) )
                
    | ScmOr'(expr_list) -> 
      let li = List.map (find_first_writes name enclosing_lambda) expr_list in
      List.flatten li
      
    | ScmSet'(v, expr) ->
      let li_v = (match v with 
        | VarFree(s) when s = name -> [enclosing_lambda]
        | VarParam(s, minor) when s = name -> [enclosing_lambda] 
        | VarBound(s, minor, major) when s = name -> [enclosing_lambda]
        | _ -> []) in
      
      let li_expr = find_first_writes name enclosing_lambda expr in
      List.append li_v li_expr

    (* if expr (the body) is a sequence: *)
    | ScmSeq'(expr_list) -> 
      let li = List.map (find_first_writes name enclosing_lambda) expr_list in
      List.flatten li

    | ScmBoxSet'(var', expr_) -> find_first_writes name enclosing_lambda expr_

    (* All other cases (ScmConst', ScmBoxGet') cannot contain name --> We don't look in them. *)
    | _ -> [];;


  let find_writes name enclosing_lambda expr = 
    let li = find_first_writes name enclosing_lambda expr in
    remove_from_right li;;
  
  let rec box_var name expr = 
    match expr with
    | ScmVar'(v) -> 
      (match v with 
        (* | VarParam(s, minor) when s = name -> ScmBoxGet'(v)
        | VarBound(s, minor, major) when s = name -> ScmBoxGet'(v) *)
        | VarParam(s, minor) when (String.equal s name) -> ScmBoxGet'(v)
        | VarBound(s, minor, major) when (String.equal s name) -> ScmBoxGet'(v)
        | _ -> expr)
      
    | ScmIf'(test, dit, dif) -> ScmIf'(box_var name test, box_var name dit, box_var name dif)
    | ScmSeq'(expr_list) -> ScmSeq'(List.map (box_var name) expr_list)
    | ScmSet'(v, expr_) -> 
      (match v with 
        (* | VarParam(s, minor) when s = name -> ScmBoxSet'(v, box_var name expr_) 
        | VarBound(s, minor, major) when s = name -> ScmBoxSet'(v, box_var name expr_) *)
        | VarParam(s, minor) when (String.equal s name) -> ScmBoxSet'(v, box_var name expr_) 
        | VarBound(s, minor, major) when (String.equal s name) -> ScmBoxSet'(v, box_var name expr_)
        | _ -> expr)

    | ScmOr'(expr_list) -> ScmOr'(List.map (box_var name) expr_list)
    | ScmLambdaSimple'(s_list, body) -> 
        if not (appears_in_args name s_list) 
          then ScmLambdaSimple'(s_list, box_var name body)
          else expr

    | ScmLambdaOpt'(s_list, s, body) -> 
        if not (appears_in_args name (s :: s_list)) 
          then ScmLambdaOpt'(s_list, s, box_var name body)
          else expr 

    | ScmApplic'(func, args) -> ScmApplic'(box_var name func, List.map (box_var name) args)
    | ScmApplicTP'(func, args) -> ScmApplicTP'(box_var name func, List.map (box_var name) args)

    | ScmBoxSet'(var', expr') -> ScmBoxSet'(var', box_var name expr')

    (* Cases we don't check: ScmConst'(sexpr), ScmBox'(var'), ScmBoxGet'(var'), ScmDef'(var', expr'). *)
    | _ -> expr;;


    let rec find_in_list x lst =
      match lst with
      | [] -> -1
      | h :: t -> if x = h then 0 else 1 + find_in_list x t;;


    let rec box_set expr = 
      match expr with
      | ScmIf'(expr'1, expr'2, expr'3) -> ScmIf'(box_set expr'1, box_set expr'2, box_set expr'3)
      | ScmSeq'(expr_list) -> ScmSeq'(List.map box_set expr_list)
      | ScmSet'(var', expr') -> ScmSet'(var', box_set expr')
      | ScmDef'(var', expr') -> ScmDef'(var', box_set expr')
      | ScmOr'(expr_list) -> ScmOr'(List.map box_set expr_list)

      (* New addition *)
      | ScmBoxSet'(var', expr') -> ScmBoxSet'(var', box_set expr')
      
      | ScmApplic'(expr', expr'_list) -> ScmApplic'(box_set expr', List.map box_set expr'_list)
      | ScmApplicTP'(expr', expr'_list) -> ScmApplicTP'(box_set expr', List.map box_set expr'_list)
      | ScmLambdaSimple'(s_list, body) -> 

            let pred = (fun name -> 
              let reads = find_reads name expr body in
              let writes = find_writes name expr body in
              if (List.length reads) = 0 || (List.length writes) = 0 then false 
              else
              let expr_in_list li expr_ = List.mem expr_ li in
              not ((List.for_all (expr_in_list reads) writes) && (List.for_all (expr_in_list writes) reads)) ) in

            let rec box_params b_names = 
              match b_names with
                              | [] -> []
                              | name::[] -> let ind = find_in_list name s_list in 
                                [ScmSet' (VarParam (name, ind), ScmBox' (VarParam (name, ind)))]
                              | name::names -> let ind = find_in_list name s_list in
                                ScmSet' (VarParam (name, ind), ScmBox' (VarParam (name, ind))) :: box_params names in

            let names_to_box = List.filter pred s_list in
            let box_params_expr = box_params names_to_box in
            let boxed_body = box_set (List.fold_left (fun a c -> box_var c a) body names_to_box) in
            let combine = (fun b_p_e -> 
              if b_p_e = [] 
                then (ScmLambdaSimple'(s_list, box_set body))
                else
                  match boxed_body with 
                  | ScmSeq'(expr_list) -> 
                      let new_body = ScmSeq'(List.append b_p_e expr_list) in
                      ScmLambdaSimple'(s_list, new_body)
                  | _ -> ScmLambdaSimple'(s_list, ScmSeq' (List.append b_p_e [boxed_body] ) ) ) in              
                     combine box_params_expr

      | ScmLambdaOpt'(s_list, s, body) -> 
        let pred = (fun name -> 
          let reads = find_reads name expr body in
          let writes = find_writes name expr body in
          if (List.length reads) = 0 || (List.length writes) = 0 then false 
          else
          let expr_in_list li expr_ = List.mem expr_ li in
          not ((List.for_all (expr_in_list reads) writes) && (List.for_all (expr_in_list writes) reads)) ) in
          let rec box_params b_names = 
            match b_names with
                            | [] -> []
                            | name::[] -> let ind = find_in_list name (List.append s_list [s]) in 
                              [ScmSet' (VarParam (name, ind), ScmBox' (VarParam (name, ind)))]                            
                            | name::names -> let ind = find_in_list name (List.append s_list [s]) in
                              ScmSet' (VarParam (name, ind), ScmBox' (VarParam (name, ind))) :: box_params names in
        (* let names_to_box = List.filter pred (s :: s_list) in *)
        let names_to_box = List.filter pred (List.append s_list [s]) in
        let box_params_expr = box_params names_to_box in
        let boxed_body = box_set (List.fold_left (fun a c -> box_var c a) body names_to_box) in
        let combine = (fun b_p_e -> 
          if b_p_e = [] 
            then (ScmLambdaOpt'(s_list, s, box_set body)) 
            else
              match boxed_body with 
              | ScmSeq'(expr_list) -> 
                  let new_body = ScmSeq'(List.append b_p_e expr_list) in
                  ScmLambdaOpt'(s_list, s, new_body)
              | _ -> ScmLambdaOpt'(s_list, s, ScmSeq' (List.append b_p_e [boxed_body] ) ) ) in              
                  combine box_params_expr
      | _ -> expr;;

  (* 
  box_var generates a new body, in which the parameter needed to be boxed is boxed. 
     i.e. every get -> ScmBoxGet'(var')
  *)


  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
