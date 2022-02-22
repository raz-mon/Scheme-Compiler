(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;

 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 
 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)

 module Reader : READER = struct
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str

 and nt_line_comment str =
  let nt1 = 
      pack
        (caten
          (pack
            (caten
              (char ';')
              (star (const (fun ch -> (ch != (char_of_int 10) && ch != (char_of_int 4) && ch != (char_of_int 3) ) ) ) )
            )
            (fun (a, b) -> ()
            )
          )
          (nt_end_of_line_or_file)  
        )
        (fun (a, b) -> ()
        ) in
    nt1 str

 and nt_paired_comment str = 
  let nt1 = 
    pack
      (caten        
        (char '{')
        (caten
          (star 
            (disj_list
              [
                (pack 
                  (const 
                    (fun ch -> (ch != '}' && ch != '{' && ch != '\"' && ch != '#') )
                  )
                  (fun ch -> ())
                );
                (pack nt_char (fun ch -> () ) );
                (pack nt_string (fun s -> () ) );
                nt_paired_comment
              ]
            )
          )
          (char '}')
        )
      )
      (fun (a, (b, c)) -> ()) in
  nt1 str

 and nt_sexpr_comment str = 
  let nt1 = 
    pack
      (caten
        (word "#;")
        nt_sexpr
      )
      (fun (a, b) -> ()) in
  nt1 str
  
 and nt_comment str =
   disj_list
     [nt_line_comment;
      nt_paired_comment;
      nt_sexpr_comment] str

 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str

 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1

 and nt_int str = 
   (pack (caten 
           (maybe 
             (one_of 
               "+-"
             )
           )
           (plus
             (range '0' '9')
           )
         )
         (fun (a, b) ->
           let n = List.fold_left (fun acc curr -> acc*10 + ((int_of_char curr) - (int_of_char '0'))) 0 b in
           match a with 
           | Some a -> if a = '-' then -n else n
           | None -> n
         )
     ) str
 
 and nt_frac str = 
 (pack
   (caten
     nt_int
     (pack
       (caten
         (char '/')
         (plus
           (range '0' '9')
         )
       )
       (fun (a, b) ->
         if b = ['0'] then raise X_no_match    (* In this case, the symbol parser will take care of it.*) 
         else
         let n = List.fold_left (fun acc curr -> acc*10 + ((int_of_char curr) - (int_of_char '0'))) 0 b in
         n     (* Don't need the '/'.. only the number*)
       )
     )
   )
   (fun (a, b) ->
     let g = (gcd a b) in
     ScmRational ((a / g), (b / g))
   )) str
 
 and nt_integer_part str = plus (range '0' '9') str

 and nt_mantissa str = plus (range '0' '9') str

 and nt_exponent str =
     let nt1 = pack (char 'e') (fun c -> [c]) in
     let nt2 = pack (char 'E') (fun c -> [c]) in
     let nt3 = word "*10^" in
     let nt4 = word "*10**" in
     (caten (disj_list [nt1;nt2;nt3;nt4]) nt_int) str

 and nt_float str = 
     let nt1 = pack (maybe (one_of "-+"))
                    (fun c -> match c with
                              | Some s -> [s]
                              | None -> ['+']) in
     let nt_floatA = 
       pack (caten_list [
         nt_integer_part;
         word ".";
         pack 
           (maybe nt_mantissa)
             (fun a -> 
               match a with
                 | Some a -> a
                 | None -> ['0']
             );
         pack
           (maybe nt_exponent)
             (fun a -> 
               match a with
                 | Some (a,b) -> List.append ['e'] (string_to_list (string_of_int b))
                 | _ -> ['e';'0']
             )  
         ])
       (fun l -> List.flatten l) in
     let nt_floatB = 
       pack (caten_list [
         word ".";
         nt_mantissa;
         pack
           (maybe nt_exponent)
             (fun a -> 
               match a with
                 | Some (a,b) -> List.append ['e'] (string_to_list (string_of_int b))
                 | _ -> ['e';'0']
             )
       ])
       (fun l -> List.flatten l) in
     let nt_floatC = 
        pack (caten_list[
         nt_integer_part;
         pack nt_exponent (fun (a,b) -> List.append ['e'] (string_to_list (string_of_int b)))
       ])
        (fun l -> List.flatten l) in
       (pack (caten nt1 (disj_list [nt_floatA;nt_floatB;nt_floatC]))
                (fun (a,b) -> ScmReal (float_of_string (list_to_string (List.append a b))))) str
 
 and nt_number str =
   let nt1 = nt_float in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 (disj nt2 nt3) in
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 and nt_boolean str = (pack
 (caten (char '#') (one_of_ci "tf")) (fun (a, b) -> if (b = 't' || b = 'T') then (ScmBoolean true) else (ScmBoolean false))) str
 
 and nt_char_simple str = (pack (range '!' '~') (fun a -> [a])) str
      
 and make_named_char char_name ch = pack (word_ci char_name) (fun w -> [ch])

 and nt_hexadecimal_char str = 
  let nt1 = caten (char_ci 'x') (plus nt_char_hex) in
  let nt1 = pack nt1 (fun (a, li) -> [(char_of_int (hex_list_to_int li))]) in 
  nt1 str

 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t');
                (make_named_char "nul" '\000')
                ] in
   nt1 str

 and nt_char_hex str = 
    let nt1 = disj_list [(range '0' '9');(range_ci 'a' 'f')] in
    nt1 str

 and nt_char str = 
    let nt_char_prefix = caten_list [(char '#');(char '\\')] in
    let nt1 = disj_list [nt_hexadecimal_char; nt_char_named; nt_char_simple ] in
    (pack 
      (caten nt_char_prefix nt1)
       (fun l -> 
          match l with
            | ( _ , [b]) -> ScmChar b
            | _ -> raise X_no_match)) str

 and nt_symbol_char str = (disj_list [(range '0' '9'); (range 'a' 'z'); (range 'A' 'Z'); (char '!'); (char '$'); (char '<'); (char '>');
       (char '='); (char '-'); (char '_'); (char '^'); (char ':'); (char '+'); (char '?'); (char '/'); (char '*')]) str
 
 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str

 and nt_string_char str = 
   let nt_str_lit_chr = pack (only_if (range (char_of_int 0) '}') 
                             (fun c -> c != '\\' && c != '\"' && c != '~'))
                             (fun c -> [c]) in
   let nt_str_meta_chr = disj
                           (pack (word "~~") 
                               (fun l -> ['~']))
                           (disj_list [pack (word "\\\\") (fun s -> ['\\']);
                           pack (word_ci "\\n") (fun s -> ['\n']);
                           pack (word_ci "\\t") (fun s -> ['\t']);
                           pack (word_ci "\\r") (fun s -> ['\r']);
                           pack (word_ci "\\f") (fun s -> ['\012']);
                           (word "\\\"")])  in
    
   let nt_str_hex_chr = 
    pack
      (disj
        (caten (word "\\x") (caten (plus nt_char_hex) (char ';')) )
        (caten (word "\\X") (caten (plus nt_char_hex) (char ';')) ) ) 
       (fun (a,(b, c) ) -> [(char_of_int (hex_list_to_int b) )] ) in

   pack (plus (disj_list [nt_str_lit_chr;nt_str_meta_chr;nt_str_hex_chr]))
        (fun l -> ScmString (list_to_string(List.fold_left (List.append) [] l)))  str

 and hex_list_to_int li = 
     match li with
     | [] -> 0
     | a::b -> begin
                match a with 
                  | char when ((int_of_char a) >= 48 && (int_of_char a) <= 57) -> 
                    ((int_of_float (16. ** (float_of_int ((List.length li) - 1)))) * ((int_of_char a) - (int_of_char '0'))) + 
                      (hex_list_to_int b)
                  | char when ((int_of_char a) >= 65 && (int_of_char a) <= 70) -> 
                    ((int_of_float (16. ** (float_of_int ((List.length li) - 1)))) * ((int_of_char a) - 55)) + 
                      (hex_list_to_int b)
                  | char when ((int_of_char a) >= 97 && (int_of_char a) <= 102) -> 
                    ((int_of_float (16. ** (float_of_int ((List.length li) - 1)))) * ((int_of_char a) - 87)) + 
                      (hex_list_to_int b)
                  | _ -> raise X_no_match
               end
      
 and nt_str_interp str = 
   let nt1 = pack (caten (word "~{") (caten nt_skip_star (char '}')))
                   (fun _ -> ScmPair (ScmSymbol "format", ScmPair (ScmString "~a", ScmNil))) in
   let nt2 = pack (caten (word "~{")
                         (caten (plus (make_skipped_star nt_sexpr))
                         (word "}")))
             (fun (a,(b,c)) -> ScmPair (ScmSymbol "format" , 
                               (ScmPair (ScmString "~a" , List.fold_right (fun curr acc -> ScmPair (curr, acc)) b ScmNil)))) in
  (disj nt1 nt2) str

 and nt_string str = 
   let nt1 = disj nt_string_char nt_str_interp in
   let nt2 = pack (word "\"") (fun _ -> [ScmVoid]) in
   (pack (caten_list [nt2;(star nt1);nt2])                    
     (fun l -> match l with
               | _::l_2::_ -> begin
                            match l_2 with
                            | [] -> ScmString ""
                            | a::[] -> a
                            | l_2 -> ScmPair (ScmSymbol "string-append", List.fold_right (fun curr acc -> ScmPair (curr, acc)) l_2 ScmNil)
                            end
               | _ -> raise X_no_match)) str

 and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str

 and nt_proper_list str = 
   let nt1 = caten (char '(') (caten nt_skip_star (char ')') ) in 
   let nt1 = pack nt1 (fun _ -> ScmNil) in
   let nt2 = caten (char '(') (caten (plus (make_skipped_star nt_sexpr) ) (char ')') ) in
   let nt2 = pack nt2 (fun (a, (b, c)) -> List.fold_right (fun curr acc -> ScmPair (curr, acc)) b ScmNil) in
   let nt1 = disj nt1 nt2 in
   nt1 str   
   
 and nt_improper_list str = 
   let nt1 = char '(' in 
   let nt1 = caten nt1 (plus (make_skipped_star nt_sexpr)) in
   let nt1 = pack nt1 (fun (a, b) -> b) in
   let nt1 = caten nt1 (char '.') in
   let nt1 = pack nt1 (fun (a, b) -> a) in
   let nt1 = caten nt1 (make_skipped_star nt_sexpr) in
   let nt1 = pack nt1 (fun (a, b) -> List.fold_right (fun curr acc -> ScmPair (curr, acc) ) a b ) in
   let nt1 = caten nt1 (char ')') in
   let nt1 = pack nt1 (fun (a, b) -> a) in
   nt1 str

 and nt_list str = 
  let nt1 = disj nt_proper_list nt_improper_list in
  nt1 str

 and nt_Quoted str = 
  let nt1 = pack (caten nt_skip_star (char '\'')) (fun (a, b) -> ScmSymbol ("quote") ) in
  let nt1 = pack (caten nt1 (make_skipped_star nt_sexpr) ) (fun (a, b) -> ScmPair (a, ScmPair (b, ScmNil))) in
  nt1 str

 and nt_Quasi_Quoted str = 
  let nt1 = pack (caten nt_skip_star (char '`')) (fun (a, b) -> ScmSymbol ("quasiquote") ) in
  let nt1 = pack (caten nt1 (make_skipped_star nt_sexpr) ) (fun (a, b) -> ScmPair (a, ScmPair (b, ScmNil))) in
  nt1 str

 and nt_Unquoted str = 
  let nt1 = pack (caten nt_skip_star (char ',')) (fun (a, b) -> ScmSymbol ("unquote") ) in
  let nt1 = pack (caten nt1 (make_skipped_star nt_sexpr) ) (fun (a, b) -> ScmPair (a, ScmPair (b, ScmNil))) in
  nt1 str

 and nt_Unquoted_And_Spliced str = 
  let nt1 = pack (caten nt_skip_star (word ",@")) (fun (a, b) -> ScmSymbol ("unquote-splicing") ) in
  let nt1 = pack (caten nt1 (make_skipped_star nt_sexpr) ) (fun (a, b) -> ScmPair (a, ScmPair (b, ScmNil))) in
  nt1 str

 and nt_quoted_forms str = 
  let nt1 = disj_list [nt_Quoted; nt_Quasi_Quoted; nt_Unquoted; nt_Unquoted_And_Spliced] in 
  nt1 str

 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 
 end;; (* end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;
