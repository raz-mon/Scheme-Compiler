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
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

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
  val generate : (sexpr * (int * string)) list -> (string * int) list -> int -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let rec consts_of_ast expr' = 
    match expr' with
    | ScmConst'(sexpr) -> [sexpr]
    | ScmVar'(var') -> []
    | ScmBox'(var') -> []
    | ScmBoxGet'(var') -> []
    | ScmBoxSet'(var', expr') -> consts_of_ast expr'
    | ScmIf'(test, dit, dif) -> List.concat [consts_of_ast test; consts_of_ast dit; consts_of_ast dif]
    | ScmSeq'(expr'_list) -> List.concat (List.map (fun expr' -> consts_of_ast expr') expr'_list)
    | ScmSet'(var', expr') -> consts_of_ast expr'
    | ScmDef'(var', expr') -> consts_of_ast expr'
    | ScmOr'(expr'_list) -> List.concat (List.map (fun expr' -> consts_of_ast expr') expr'_list)
    | ScmLambdaSimple'(s_list, body) -> consts_of_ast body
    | ScmLambdaOpt'(s_list, s, body) -> consts_of_ast body
    | ScmApplic'(expr', expr'_list) -> List.concat [consts_of_ast expr'; List.concat (List.map consts_of_ast expr'_list)]
    | ScmApplicTP'(expr', expr'_list) -> List.concat [consts_of_ast expr'; List.concat (List.map consts_of_ast expr'_list)];;

  let uniq_cons x xs = if List.mem x xs then xs else x :: xs;;
  let remove_from_right xs = List.fold_right uniq_cons xs [];;

  let uniq_cons2 xs x = if List.mem x xs then xs else x :: xs;;
  let rev_list l =
    let rec rev_acc acc = function
    | [] -> acc
    | hd::tl -> rev_acc (hd::acc) tl
  in
  rev_acc [] l;;
  let remove_from_left xs = rev_list (List.fold_left uniq_cons2 [] xs);;

  let rec take_appart sexpr = 
    match sexpr with
    | ScmPair(sexpr1, sexpr2) -> List.concat [take_appart sexpr1; take_appart sexpr2; [sexpr]]
    | ScmVector(sexpr_list) -> List.concat [List.concat (List.map take_appart sexpr_list); [sexpr]]
    | ScmSymbol(s) -> [ScmString(s); sexpr]
    | _ -> [sexpr];;

  let find_const_offset sexpr table = 
    let entry = List.find (fun entry -> (match entry with
                            | (a, (b, c) ) -> sexpr_eq sexpr a)           
                          ) table in
    (match entry with
    | (a, (b, c) ) -> b);;
    
  (*
  Comparator interface:
  If sexpr2 is in sexpr1 --> return 1
  If sexpr1 is in sexpr2 --> return -1
  If sexpr1 = sexpr2 --> return 0
  *)
  let rec compare_sexprs sexpr1 sexpr2 = 
    if (sexpr_eq sexpr1 sexpr2) then 0 else 
      (let s2_in_s1 = 
        (match sexpr1 with
        | ScmVector(sexpr1_list) -> List.for_all (fun sexpr11 -> (sexpr_eq sexpr2 sexpr11) || (compare_sexprs sexpr11 sexpr2) > 0 ) sexpr1_list
        | ScmPair(sexpr11, sexpr12) -> (sexpr_eq sexpr11 sexpr2) || (sexpr_eq sexpr12 sexpr2) || (compare_sexprs sexpr11 sexpr2) > 0 ||
                                                                              (compare_sexprs sexpr12 sexpr2) > 0
        | ScmSymbol(s1) -> sexpr2 = ScmString(s1)
        | _ -> false) in
      
      if s2_in_s1 then 1 else
        (let s1_in_s2 = 
          (match sexpr2 with
          | ScmVector(sexpr2_list) -> List.for_all (fun sexpr21 -> (sexpr_eq sexpr21 sexpr1) || (compare_sexprs sexpr21 sexpr1) > 0 ) sexpr2_list
          | ScmPair(sexpr21, sexpr22) -> (sexpr_eq sexpr21 sexpr1) || (sexpr_eq sexpr22 sexpr1) || (compare_sexprs sexpr21 sexpr1) > 0 ||
                                                                                  (compare_sexprs sexpr22 sexpr1) > 0
          | ScmSymbol(s2) -> sexpr1 = ScmString(s2)
          | _ -> false
          ) in
        if s1_in_s2 then -1 else 0
        )
      );;

  let char_list_of_string s =
    let rec exp i l =
      if i < 0 then l else exp (i - 1) (s.[i] :: l) in 
      exp (String.length s - 1) [];;

  let make_consts_tbl asts = 

    let gen_final_tuple entry table = 
    (match entry with
    | (ScmVoid, (ind, s) ) -> (ScmVoid, (ind, Printf.sprintf "db T_VOID"))
    | (ScmNil, (ind, s) ) -> (ScmNil, (ind, Printf.sprintf "db T_NIL"))
    | (ScmBoolean(b), (ind, s) ) -> if b 
            then (ScmBoolean(b), (ind, Printf.sprintf "MAKE_BOOL(1)") ) 
            else (ScmBoolean(b), (ind, Printf.sprintf "MAKE_BOOL(0)") )
    | (ScmChar(c), (ind, s) ) -> (ScmChar(c), (ind, Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (int_of_char c) ) )
    (* | (ScmString(s), (ind, s1) ) -> (ScmString(s), (ind, Printf.sprintf "MAKE_LITERAL_STRING(\"%s\")" s) ) *)
    (* Convert all chars to int_of_char and then concat with String.concat, with ',' in between. *)
    | (ScmString(s), (ind, s1) ) -> 
        let new_str_list = List.map string_of_int (List.map int_of_char (char_list_of_string s)) in
      (ScmString(s), (ind, 
    (Printf.sprintf "db T_STRING
        dq %d
        db %s" (String.length s) ((String.concat "," new_str_list) ) ) ) )
    | (ScmSymbol(s), (ind, s1)) -> (ScmSymbol(s), (ind, Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" (find_const_offset (ScmString(s)) table) ) )
    | (ScmNumber(num), (ind, s) ) -> 
        (match num with 
        | ScmRational(n1, n2) -> (ScmNumber(num), (ind, Printf.sprintf "MAKE_LITERAL_RATIONAL(%d, %d)" n1 n2) )
        | ScmReal(fl) -> (ScmNumber(num), (ind, Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" fl) ) 
        )
    | (ScmVector(sexpr_list), (ind, s) ) -> 
      let sexpr_inds = List.map (fun sexpr -> find_const_offset sexpr table) sexpr_list in
      let sexpr_entries = List.map (fun ind -> Printf.sprintf "const_tbl+%d" ind) sexpr_inds in
      let args = if ((List.length sexpr_entries) != 0) 
        then (String.concat ", " sexpr_entries) 
        else "" in
      let final_string = if ((List.length sexpr_entries) != 0) 
        then Printf.sprintf "MAKE_LITERAL_VECTOR %s" args 
        else Printf.sprintf "MAKE_LITERAL_VECTOR" in
        
        
        (* Printf.sprintf "MAKE_LITERAL_VECTOR %s" args in *)
      (ScmVector(sexpr_list), (ind, final_string))
    | (ScmPair(sexpr1, sexpr2), (ind, s) ) -> (ScmPair(sexpr1, sexpr2), (ind, Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)" 
                                                            (find_const_offset sexpr1 table) (find_const_offset sexpr2 table) ) ) ) in

    let make_entry sexpr = (sexpr, (0, "") ) in
    
    let add_ind ind sexpr = 
      match sexpr with 
      | ScmVoid -> (ind + 1)
      | ScmNil -> (ind + 1)
      | ScmBoolean(b) -> (ind + 2)
      | ScmChar(c) -> (ind + 2)
      | ScmString(s) -> (ind + 1 + 8 + (String.length s) )
      | ScmSymbol(s) -> (ind + 1 + 8)
      | ScmNumber(num) -> 
        (match num with 
        | ScmRational(r) -> (ind + 1 + 16)
        | ScmReal(f) -> (ind + 1 + 8) )
      | ScmVector(sexpr_list) -> (ind + 1 + 8 + ((List.length sexpr_list) * 8) )
      | ScmPair(sexpr1, sexpr2) -> (ind + 17) in

    let rec add_index_consts table ind = 
      match table with
      | [] -> []
      | (sexpr, (0, x)) :: [] -> [(sexpr, (ind, x) ) ]
      | (sexpr, (0, x)) :: tail -> (sexpr, (ind, x) ) :: (add_index_consts tail (add_ind ind sexpr) )
      | _ -> raise(X_this_should_not_happen) in

    let init_sexprs = [ScmVoid; ScmNil; ScmBoolean(true); ScmBoolean(false)] in
    let sexprs = init_sexprs @ List.concat (List.map consts_of_ast asts) in
    let sexprs = remove_from_left sexprs in
    let sexprs = List.concat (List.map take_appart sexprs) in
    let sexprs = remove_from_left sexprs in
    let sexprs = List.sort (fun a b -> compare_sexprs a b) sexprs in
    let table = List.map make_entry sexprs in
    let table = add_index_consts table 0 in
    let table = List.map (fun entry -> gen_final_tuple entry table) table in
    table;;

  let primitives_fvars =
    [
      (* Type queries  *)
      "boolean?"; "flonum?"; "rational?";
      "pair?"; "null?";"char?"; "string?";
      "procedure?"; "symbol?";
      (* String procedures *)
      "string-length"; "string-ref"; "string-set!";
      "make-string";"symbol->string";
      (* Type conversions *)
      "char->integer"; "integer->char"; "exact->inexact";
      (* Identity test *)
      "eq?";
      (* Arithmetic ops *)
      "+"; "*"; "/"; "="; "<";
      (* Additional rational numebr ops *)
      "numerator"; "denominator"; "gcd";
      (* you can add yours here *)
      "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; "apply";
    ]
  let rec add_index fvars ind = match fvars with
                                | [] -> []
                                | head::[] -> [(head, ind)]
                                | head::tail -> (head, ind)::(add_index tail (ind + 8));;

  let var_is_free var' = match var' with
                          | VarFree(x) -> [x]
                          | VarParam(_) -> []
                          | VarBound(_) -> [];;

  let rec make_fvar_ast_2_table ast = 
    match ast with
    | ScmConst'(x) -> []
    | ScmVar'(x) -> var_is_free x
    | ScmBox'(x) -> []
    | ScmBoxGet'(x) -> []
    | ScmBoxSet'(var', expr') -> List.append (var_is_free var') (make_fvar_ast_2_table expr')
    | ScmIf'(test, dit, dif) -> List.append (make_fvar_ast_2_table test) 
                                (List.append (make_fvar_ast_2_table dit) (make_fvar_ast_2_table dif))
    | ScmSeq'(list_exprs) -> List.fold_left (List.append) [] (List.map make_fvar_ast_2_table list_exprs)
    | ScmSet'(var' , expr') -> List.append (var_is_free var') (make_fvar_ast_2_table expr')
    | ScmDef'(var', expr') -> List.append (var_is_free var') (make_fvar_ast_2_table expr')
    | ScmOr'(list_exprs) -> List.fold_left (List.append) [] (List.map make_fvar_ast_2_table list_exprs)
    | ScmLambdaSimple' (_, expr') -> make_fvar_ast_2_table expr'
    | ScmLambdaOpt' (_, _, expr') -> make_fvar_ast_2_table expr'
    | ScmApplic'(expr', list_exprs) -> List.append (make_fvar_ast_2_table expr') 
                                        (List.fold_left (List.append) [] (List.map make_fvar_ast_2_table list_exprs))
    | ScmApplicTP'(expr', list_exprs) -> List.append (make_fvar_ast_2_table expr') 
                                        (List.fold_left (List.append) [] (List.map make_fvar_ast_2_table list_exprs));;
  
  let make_fvars_tbl asts = 
  let list_list_fvars = List.map make_fvar_ast_2_table asts in
  let list_fvars = List.append primitives_fvars (List.fold_left (List.append) [] list_list_fvars) in
  add_index (remove_from_left list_fvars) 0;;

(*
Generate Scm Exprs' to ASM code
*)

  let make_counter () =
    let x = ref 0 in
    let get () = !x in
    let inc () = x := !x + 1 in
    (get,inc);;

  let (get,inc) = make_counter();;

  let rec find_fvar_ind fvars v = 
    match fvars with
    | [] -> raise X_this_should_not_happen
    | (s, i)::tail -> if s = v then i else find_fvar_ind tail v;;

  let asm_const consts c = Printf.sprintf 
    ";;; ----- CONST ASM CODE -----
    mov rax, const_tbl+%d
      ; Getting const from const table\n" (find_const_offset c consts);;

  let asm_var fvars x = 
    (match x with
    | VarFree(v) -> Printf.sprintf "mov rax, qword [fvar_tbl+%d]
      ; Getting free-var %s\n" (find_fvar_ind fvars v) v
    | VarParam(_, minor) -> Printf.sprintf "mov rax, qword [rbp + 8 * (4 + %d)]
      ; Getting param with minor: %d\n" minor minor
    | VarBound(_,major,minor) -> Printf.sprintf "mov rax, qword [rbp + 8 * 2]
    mov rax, qword [rax + 8 * %d]
    mov rax, qword [rax + 8 * %d]
      ; Getting bound-variable in major: %d, minor: %d\n" major minor major minor);;

  let asm_set_var fvars var = 
    match var with
    | VarFree(v) -> Printf.sprintf "mov qword [fvar_tbl+%d], rax
    mov rax, SOB_VOID_ADDRESS
    ; Setting free-var %s\n" (find_fvar_ind fvars v) v
    | VarParam(_, minor) -> Printf.sprintf "mov qword [rbp + 8 * (4 + %d)], rax
    mov rax, SOB_VOID_ADDRESS
    ; Setting parameter at minor: %d\n" minor minor
    | VarBound(_,major,minor) -> Printf.sprintf "mov rbx, qword [rbp + 8 * 2]
    mov rbx, qword [rbx + 8 * %d]
    mov qword [rbx + 8 * %d], rax
    mov rax, SOB_VOID_ADDRESS
    ; Setting bound-var at major: %d, minor: %d\n" major minor major minor;;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
    let (rdc, rac) = rdc_rac s
    in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;

  let asm_or list_asm = 
    let ind = get() in
    let split = rdc_rac list_asm in
    let label = 
      Printf.sprintf
      "cmp rax, SOB_FALSE_ADDRESS
jne Lexit%d\n" ind in
    let last_label = Printf.sprintf "Lexit%d:\n" ind in
    let () = inc() in
    let concat_or label last_l split = 
      match split with
      | (head, last) -> (List.fold_left (^) "" (List.map (fun s -> s ^ label) head)) ^ last ^ last_l in
    ";;; ----- OR ASM CODE ----- \n" ^ concat_or label last_label split;;

  let asm_if test_asm dit_asm dif_asm = 
    let ind = get() in
    let () = inc() in
    Printf.sprintf "
%s
cmp rax, SOB_FALSE_ADDRESS
je Lelse%d
%s
jmp Lexit%d
Lelse%d:
  %s
Lexit%d:
" test_asm ind dit_asm ind ind dif_asm ind;;

  let asm_box_var asm_v =
    Printf.sprintf "; Boxing a variable!
%s
mov rsi, rax
MALLOC rax, WORD_SIZE
mov qword [rax], rsi\n" asm_v


  let asm_box_get asm_v = 
    Printf.sprintf "  ; Getting boxed Variable
%s
mov rax, qword [rax]\n" asm_v;;

  let asm_box_set asm_v asm_exp = 
    Printf.sprintf "; Setting a boxed var
%s
push rax
%s
pop qword [rax]
mov rax, SOB_VOID_ADDRESS\n" asm_exp asm_v;;

  let asm_lambda_simple lambda_ind asm_body = 

    (* 

    lambda_ind - the size of the current environment! We need one of size (lambda_ind+1)!

    1. Extend the current environment:
      - Allocate space in memory for (n+1) ribs.
      - copy ribs from old environment to new one in indexes 1-n.
      - Generate new env:
        - Copy Copy parameters from stack to an array (vector).
        - Put the address of this array in index 0 of new env.
        - 
      - call (generate fvars consts body) [Done in 'generate']--> Put it inside template as in slide 93
        with label Lcode%d.
      - Generate Closure by using MAKE_NEW_CLOSURE(rax, env, Lcode%d)
      *)

    let curr_env_size = lambda_ind + 1 in
    
    let ind = get() in
    let () = inc() in
    let code = Printf.sprintf "Lcode%d:
  push rbp
  mov rbp, rsp
  %s
  leave
  ret
Lcont%d:" ind asm_body ind in

    Printf.sprintf "
      ;;; ----- LAMBDA SIMPLE ASM CODE -----
    mov rdx, [rbp + 8*2]
lea r10, [rbp + 8*3]
CREATE_NEW_RIB r9, r10
  ; Creating new env of size %d
CREATE_NEW_ENV rsi, rdx, %d, r9
MAKE_CLOSURE (rax, rsi, Lcode%d)
jmp Lcont%d
%s\n" curr_env_size curr_env_size ind ind code;;


let asm_lambda_opt lambda_ind asm_body non_opt_num = 
  let curr_env_size = lambda_ind + 1 in
  
  let ind = get() in
  let () = inc() in
  let opt_params_2_list = Printf.sprintf "
;;; r13 <- |opt args|
;;;	r14 <- last opt arg
;;; r15 <- num of params on stack + 2

mov rdi, qword [rsp + WORD_SIZE*2]      ; rdi <- n

INITIATE_OPT_VALUES r13,r14,r15,%d
cmp r13, 0                              ; check if there are optional arguments
je shift_down%d
MAKE_PAIR(r10, r14, SOB_NIL_ADDRESS)    ; r10 <- PAIR(opt[k], NILL), k is the number of optional arguments
mov rcx, 1
loop_l%d:
    cmp r13, rcx                      
    je end_loop%d                       ; no more optional argumetns
    dec r15                             ; r15 <- n + 3 - i
    mov r14, qword [rsp+r15*WORD_SIZE]  ; r10 <- opt[k - rcx] (the current optional argument)
    mov rdx, r10
    MAKE_PAIR(r10, r14, rdx)
    add rcx, 1                          ; increase rcx
    jmp loop_l%d
end_loop%d:
mov qword [rsp+r15*WORD_SIZE], r10  ; move to the first optional argument cell an array (pointer) of arguments.
    
    dec r13
    SHIFT_UP_OPT r13
    lea r8, [%d + 1]
    mov qword [rsp + WORD_SIZE*2], r8                  ; New param count: %d
jmp end%d

shift_down%d:
  SHIFT_DOWN_1
  inc rdi 
  lea r8, [rsp + WORD_SIZE*(2 + rdi)]   ; r8 <- points to the adress of the new point we create in the top of stack
  mov qword [r8], SOB_NIL_ADDRESS       ; no opt args -> new cell gets a nil
  mov [rsp + 2 * WORD_SIZE], rdi

end%d:\n" non_opt_num ind ind ind ind ind non_opt_num (non_opt_num + 1) ind ind ind in

  let code = Printf.sprintf "
Lcode%d:
;;; Adjust stack for opt args
%s
;;; Lambda OPT body
push rbp
mov rbp, rsp
%s
leave
ret
Lcont%d:\n" ind opt_params_2_list asm_body ind in

  Printf.sprintf "
;;; ----- LAMBDA OPT ASM CODE -----
mov rdx, [rbp + 8*2]
lea r10, [rbp + 8*3]
CREATE_NEW_RIB r9, r10
; Creating new env of size %d
CREATE_NEW_ENV rsi, rdx, %d, r9
MAKE_CLOSURE (rax, rsi, Lcode%d)
jmp Lcont%d
%s\n" curr_env_size curr_env_size ind ind code;;

  let asm_applic asm_proc asm_args = 
    (* let ind = get() in
    let () = inc() in *)
    let args = List.fold_right (fun curr acc -> acc ^ curr) (List.map (fun s -> s ^ "push rax\n") asm_args) "" in
    let n = Printf.sprintf "push %d\n" (List.length asm_args) in
    let check_if_closure = Printf.sprintf 
"CHECK_IF_CLOSURE rax
CLOSURE_ENV r11, rax
CLOSURE_CODE r12, rax
push r11
call r12
add rsp , 8*1 ; pop env
pop rbx ; pop arg count
lea rsp , [rsp + 8*rbx]\n" in
      ";;; ----- APPLIC ASM CODE ----- \n" ^ args ^ n ^ asm_proc ^ check_if_closure;;

  let get_fvar_offset fvars var = 
      (match var with
      | VarFree(v) -> Printf.sprintf "lea rax, [fvar_tbl+%d]
        ; Getting address of free-var %s" (find_fvar_ind fvars v) v
      | _ -> raise X_this_should_not_happen );;

  let asm_def fvars var' = 
    match var' with
    | VarFree(v) -> 
      let v_offset = get_fvar_offset fvars var' in
      Printf.sprintf
      (* mov qword [fvar_tbl+%d], rax *)
      "\n ; Define instruction:
push rax
%s
pop qword [rax]
mov rax, SOB_VOID_ADDRESS
" v_offset
    | _ -> raise X_this_should_not_happen;;


 let asm_TPApplic asm_proc asm_args = 
    let args_count = List.length asm_args in
    let args_part = List.fold_right (fun curr acc -> acc ^ curr) (List.map (fun s -> s ^ "\npush rax\n") asm_args) "" in
    (* let ind = get() in
    let () = inc() in *)

(* 
; ----Fix the stack----
      ; 1. shift the frame UP, (new stack-size) times. new stack-size = param-count + 3*8.
      ; 2. mov rsp and rbp to point at the right place.
      ; ** Notice that we DON'T push rbp, cause this happens in the function body. (Ain't part of a call procedure..)
      ; Signature of SHIFT_UP_TP: %1: The step, i.e. the amount of cells each cell must jump up
      ;                           Here: This is the size of the current stack-frame (of the function being executed).
      ;                           ** We assume that the stack is 'clean' other than: n, env, ret, old rbp.
      ;                             IS THIS CORRECT?

      ; ------Calculating the 'step' = the current stack-size (which we override)------
*)

    Printf.sprintf "
 ;;; ----- TP APLIC ASM CODE-----
    %s
      push %d
      %s
      CHECK_IF_CLOSURE rax
      CLOSURE_ENV r8, rax
      push r8
      push qword [rbp + 8*1]
      
      lea r8, [rbp + 8*3]     ; r8 points at the old param-count.
      mov r8, [r8]            ; r8 = (old) n.

      lea r9, [4]           ; The size of the cells that hold: n, env, ret-addr, old-rbp.
      add r8, r9              ; r8 holds the old stack-size.

      SHIFT_UP_TP r8
      
      CLOSURE_CODE rsi, rax
      jmp rsi\n" args_part args_count asm_proc;;




  let rec generate consts fvars lambda_ind e = 
    match e with
    | ScmConst'(c) -> asm_const consts c
    | ScmVar'(x) -> asm_var fvars x
    | ScmBox'(x) -> asm_box_var (asm_var fvars x)
    | ScmBoxGet'(x) -> asm_box_get (asm_var fvars x)
    | ScmBoxSet'(var', expr') -> asm_box_set (asm_var fvars var') (generate consts fvars lambda_ind expr')
    | ScmIf'(test, dit, dif) -> ";;; ----- IF ASM CODE ----- \n" ^ asm_if (generate consts fvars lambda_ind test) 
                                      (generate consts fvars lambda_ind dit) (generate consts fvars lambda_ind dif)

    | ScmSeq'(list_exprs) -> List.fold_left (^) "" 
                            (List.map (fun e' -> (generate consts fvars lambda_ind e') ^ "\n") list_exprs)
    
    | ScmSet'(var' , expr') -> (generate consts fvars lambda_ind expr') ^ "\n" ^  (asm_set_var fvars var') 
    
    | ScmOr'(list_exprs) -> asm_or (List.map (fun e' -> (generate consts fvars lambda_ind e') ^ "\n") list_exprs)

    | ScmDef'(var', expr') -> ";;; ----- Define ASM CODE ----- \n" ^ (generate consts fvars lambda_ind expr') ^ (asm_def fvars var')
    
    | ScmLambdaSimple' (_, body) -> (asm_lambda_simple lambda_ind (generate consts fvars (lambda_ind+1) body) )
    
    | ScmLambdaOpt' (list_args, _, body) -> (asm_lambda_opt lambda_ind (generate consts fvars (lambda_ind+1) body) (List.length list_args))
    
    | ScmApplic'(proc', list_args) -> asm_applic (generate consts fvars lambda_ind proc')  
                                      (List.map (fun e' -> (generate consts fvars lambda_ind e') ^ "\n") list_args)
    
    | ScmApplicTP'(expr', list_exprs) -> asm_TPApplic (generate consts fvars lambda_ind expr') 
                    (List.map (generate consts fvars lambda_ind) list_exprs)  ;;
end;;



