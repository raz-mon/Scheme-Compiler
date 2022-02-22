%define T_UNDEFINED 0
%define T_VOID 1
%define T_NIL 2
%define T_RATIONAL 3
%define T_FLOAT 4
%define T_BOOL 5
%define T_CHAR 6
%define T_STRING 7
%define T_SYMBOL 8
%define T_CLOSURE 9
%define T_PAIR 10
%define T_VECTOR 11

%define TYPE_SIZE 1
%define WORD_SIZE 8
	
%define KB(n) n*1024
%define MB(n) 1024*KB(n)
%define GB(n) 1024*MB(n)


%macro SKIP_TYPE_TAG 2
	mov %1, qword [%2+TYPE_SIZE]	
%endmacro	

%define NUMERATOR SKIP_TYPE_TAG

%macro DENOMINATOR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%macro CHAR_VAL 2
	movzx %1, byte [%2+TYPE_SIZE]
%endmacro

%define FLOAT_VAL SKIP_TYPE_TAG

%define STRING_LENGTH SKIP_TYPE_TAG
%define VECTOR_LENGTH SKIP_TYPE_TAG

%define SYMBOL_VAL SKIP_TYPE_TAG

%macro STRING_ELEMENTS 2
	lea %1, [%2+TYPE_SIZE+WORD_SIZE]
%endmacro
%define VECTOR_ELEMENTS STRING_ELEMENTS

%define CAR SKIP_TYPE_TAG

%macro CDR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define CLOSURE_ENV CAR

%define CLOSURE_CODE CDR

%define PVAR(n) qword [rbp+(4+n)*WORD_SIZE]

; returns %2 allocated bytes in register %1
; Supports using with %1 = %2
%macro MALLOC 2
	add qword [malloc_pointer], %2
	push %2
	mov %1, qword [malloc_pointer]
	sub %1, [rsp]
	add rsp, 8
%endmacro
	
; Creates a short SOB with the
; value %2
; Returns the result in register %1
%macro MAKE_CHAR_VALUE 2
	MALLOC %1, 1+TYPE_SIZE
	mov byte [%1], T_CHAR
	mov byte [%1+TYPE_SIZE], %2
%endmacro

; Creates a long SOB with the
; value %2 and type %3.
; Returns the result in register %1
%macro MAKE_LONG_VALUE 3
	MALLOC %1, TYPE_SIZE+WORD_SIZE
	mov byte [%1], %3
	mov qword [%1+TYPE_SIZE], %2
%endmacro

%define MAKE_FLOAT(r,val) MAKE_LONG_VALUE r, val, T_FLOAT
%define MAKE_CHAR(r,val) MAKE_CHAR_VALUE r, val

; Create a string of length %2
; from char %3.
; Stores result in register %1
%macro MAKE_STRING 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_STRING
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1,WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%str_loop:
	jz %%str_loop_end
	dec rcx
	mov byte [%1+rcx], %3
	jmp %%str_loop
%%str_loop_end:
	pop rcx
	sub %1, WORD_SIZE+TYPE_SIZE
%endmacro

; Create a vector of length %2
; from array of elements in register %3
; Store result in register %1
%macro MAKE_VECTOR 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_VECTOR
	mov qword [%1+TYPE_SIZE], %2

    push rbx
    push rcx
    push %1
    add %1,WORD_SIZE+TYPE_SIZE
    mov rcx, %2
%%vector_loop:
    cmp rcx, 0
    js %%vector_loop_end
    mov rbx, [%3]
    mov [%1], rbx
    add %1, WORD_SIZE
    add %3, WORD_SIZE
    dec rcx
    jmp %%vector_loop
%%vector_loop_end:
    pop %1
    pop rcx
    pop rbx
%endmacro

;;; Creates a SOB with tag %2 
;;; from two pointers %3 and %4
;;; Stores result in register %1
%macro MAKE_TWO_WORDS 4 
        MALLOC %1, TYPE_SIZE+WORD_SIZE*2
        mov byte [%1], %2
        mov qword [%1+TYPE_SIZE], %3
        mov qword [%1+TYPE_SIZE+WORD_SIZE], %4
%endmacro

%macro MAKE_WORDS_LIT 3
	db %1
        dq %2
        dq %3
%endmacro

%define MAKE_RATIONAL(r, num, den) \
	MAKE_TWO_WORDS r, T_RATIONAL, num, den

%define MAKE_LITERAL_RATIONAL(num, den) \
	MAKE_WORDS_LIT T_RATIONAL, num, den
	
%define MAKE_PAIR(r, car, cdr) \
        MAKE_TWO_WORDS r, T_PAIR, car, cdr

%define MAKE_LITERAL_PAIR(car, cdr) \
        MAKE_WORDS_LIT T_PAIR, car, cdr

%define MAKE_CLOSURE(r, env, body) \
        MAKE_TWO_WORDS r, T_CLOSURE, env, body

;;; OUR ADDITIONS (ends with an empty commend: ;;;)

%macro MAKE_LITERAL 2 		
							; Make a literal of type %1
							; followed by the definition %2
		db %1
		%2
%endmacro

%define MAKE_LITERAL_CHAR(val) MAKE_LITERAL T_CHAR, db val

%define MAKE_BOOL(val) MAKE_LITERAL T_BOOL, db val

%define MAKE_LITERAL_FLOAT(val) MAKE_LITERAL T_FLOAT, dq val

%define MAKE_LITERAL_SYMBOL(val) MAKE_LITERAL T_SYMBOL, dq val

%macro MAKE_LITERAL_VECTOR 0-*
		db T_VECTOR
		dq %0
		%rep %0
			dq %1
			%rotate 1
		%endrep
%endmacro

%macro MAKE_LITERAL_STRING 1
	db T_STRING
	dq (%%end_str - %%str)
	%%str:
	db %1
	%%end_str:
%endmacro

;;; Create a new rib, from current parameters.
;;; Parameters:
;;;				%1: Pointer to result.
;;;				%2: Pointer to n (param-count) in the current stack (on which the current paremeters live).
%macro CREATE_NEW_RIB 2

	mov rcx, qword [%2]		; rcx = n (param-count)
	cmp rcx, 0
	je %%no_parameters

	lea r8, [rcx*WORD_SIZE]			; r8 is just a number holder here (for 1 row...).
	MALLOC %1, r8			; %1 holds a pointer to an array of size n
	mov r8, %1				; Create a copy of %1, which we will mutate in the loop.
	cmp rcx, 0
	je %%bye
	%%copy:
		add %2, WORD_SIZE	; %2 points to the next parameter.
		mov r11, [%2]		; Get parameter value.
		mov qword [r8], r11	; Assign that parameter value to the current cell in the array.
		add r8, WORD_SIZE	; r8 points to the next cell in the array.
		dec rcx
		jnz %%copy				; dec rcx --> jnz %%copy
	jmp %%bye

	%%no_parameters:
		mov %1, SOB_NIL_ADDRESS

	%%bye:

%endmacro

;;; Create new environment.
;;; Parameters: %1: pointer to hold result.
;;;				%2: Old environment pointer.
;;; 			%3: Amount of ribs needed in new env.
;;;				%4: The new rib (to be places in index 0).
%macro CREATE_NEW_ENV 4

	mov rcx, %3

	cmp rcx, 0
	je %%top_level

	lea r8, [rcx*WORD_SIZE]
	MALLOC %1, r8				; Allocate memory for the new env.
	mov qword [%1], %4			; Put the new rib in index 0. 
	dec rcx

	cmp rcx, 0
	je %%end

	lea r8, [%1 + 1*WORD_SIZE]			; r8 - pointer to index 1 of the new env

	%%copy: 
		mov r15, qword [%2]
		mov qword [r8], r15			; Put index i of the old env in index (i+1) of the new env.
		add %2, WORD_SIZE
		add r8, WORD_SIZE	
		dec rcx
		jnz %%copy
	jmp %%end

	%%top_level:
		mov %1, SOB_NIL_ADDRESS

	%%end:	

%endmacro

;;; Initiate values before creating opt list.
;;; Parameters: %1: register which will get number of optional arguments.
;;;				%2: register which will get the last optional value.
;;; 			%3: register which will get number of arguments + 2.
;;;             %4: number of non optional args got from generarte
%macro INITIATE_OPT_VALUES 4
mov %1, [rsp+2*WORD_SIZE]         ; number of arguments in r1 , r1 <- n
mov %3, %1                        ; r3 <- n
add %3, 2                         ; r3 <- n + 2
mov %2, [rsp+%3*WORD_SIZE]        ; r2 <- last optional value
sub %1, %4			              ; r1 <- number of optional arguments
%endmacro


;;; Shift the stack UP %1 times, from rsp (the lower limit).
;;; Notice we assume the stack has nothing under rsp (should be the case)!
;;; Here we rearrange the stack ABOVE the current frame (args, n, env, ret, old_rbp).
%macro SHIFT_UP_OPT 1
	lea r11, [rsp + WORD_SIZE*2]							; r11 holds the address of n (param-count) on the stack.
	mov r11, [r11]											; r11 holds n (old param-count).

	lea rcx, [r11 + 3]								
	sub rcx, %1												; rcx holds the overall amount of elements we will displace (copy).

	lea r8, [rsp + 2*WORD_SIZE]								
	lea r8, [r8 + r11*WORD_SIZE]							; r8 points to the upper-most element in the stack-frame.
	    ;4*8 + 8*%2 - 8*1 = 3*8 + 8*%2.

	lea r9, [rsp + 2*WORD_SIZE]								
	lea r9, [r9 + r11*WORD_SIZE]							; r9 points at the upper-most element to be copied (copied) up in the stack-frame.
	lea r10, [%1*WORD_SIZE]
	sub r9, r10
	; lea r9, [rsp + 4*8 + 8*%2 - 8*1 - 8*%1]

	%%loop:
		mov r10, [r9]
		mov [r8], r10
		sub r8, WORD_SIZE
		sub r9, WORD_SIZE
		
		dec rcx
		jnz %%loop

	lea r10, [WORD_SIZE*%1]
	add rsp, r10
%endmacro


;;; Shift the stack UP %1 times, from rsp (the lower limit).
;;; Notice we assume the stack has only the new stack-frame under rsp (should be the case)!
;;; This macro is different from "SHIFT_UP" in that we assume there are 3 cells (n, env, ret-addr) under the parameters
;;; rather than 4 (n, env, ret-addr, old-rbp).
%macro SHIFT_UP_TP 1
	; first element to be copied - (rbp - 8), which is the first cell of the new stack (should be copied to the first 
	; element of the old stack)
	; How much 'steps' is its ascent? 3 + n (brings us to the first of the old frame).
	; How many times do we perform this copy? 2 + (new)n (The amount of cells in the new frame).

	; Save the current rbp, so that the rbp pushed in the body of the closure will push it correctly.
	mov rdx, qword [rbp]

	; r8: Pointer to the first cell to be copied.
	lea r10, [rbp-WORD_SIZE]
	; r9: Pointer to the first cell to copy TO.
	lea r11, [rbp + 3*WORD_SIZE]
	mov r11, [r11]									; r11 holds n (the OLD param-count).

	lea r9, [rbp + 3*WORD_SIZE]
	lea r15, [WORD_SIZE*r11]								; Just a number holder..
	add r9, r15

	; rcx: holds the size of the NEW frame.
	lea r14, [rsp + 2*8]
	mov r14, [r14]								; r14 now holds the NEW param-count.
	lea r14, [r14 + 3]							; num_of_arguments + (m, env, ret) = num_of_arguments + 3
	mov rcx, r14

	%%loop:
		mov r13, qword [r10]
		mov qword [r9], r13
		sub r9, WORD_SIZE
		sub r10, WORD_SIZE

		dec rcx
		jnz %%loop
	
	mov rbp, rdx						; rbp holds the value it had before the shift, so the next body can push the correct rbp.

	; mov rsp to new address.
	lea r15, [%1*WORD_SIZE]
	add rsp, r15	
%endmacro


;;; Shift the stack DOWN %1 times, from rsp (the lower limit - inclusive) to (rbp-8).
;;; Notice we assume the stack has nothing under rbp! (We use this macro in this case only)
%macro SHIFT_DOWN_1 0

	lea r11, [rsp + WORD_SIZE*2]
	mov r11, [r11]							; r11 holds n (old param-count).

	lea rcx, [r11 + 3]						; rcx holds the amount of elements to push (copy) downwords.
	mov r8, rsp								; r8 holds the address of rsp, the first cell to be copied.
	
	mov r9, rsp
	sub r9, WORD_SIZE						; r9 points to the cell under rsp, the first cell to be copied to.

	%%loop:
		mov r10, [r8]						; r10 holds the value to be copied.
		mov [r9], r10						; Assign to the value of r9.
		add r8, WORD_SIZE
		add r9, WORD_SIZE

		dec rcx
		jnz %%loop
	; Stack shifted down by 1.

	sub rsp, WORD_SIZE
%endmacro


;;; Check if %1 points to an SOB of type Closure.
%macro CHECK_IF_CLOSURE 1
	push r8

	mov r8, 0
	mov r8b, byte [rax]
	cmp r8b, 9
	je %%end
	mov %1, 0
	idiv %1

	%%end:

	pop r8
%endmacro

; %1 is the list we want to count
; %2 is a register which will hold list size
%macro LIST_LENGTH 2
mov r10,  %1
mov %2, 0							; counter for list size
%%loop:			
	cmp r10, SOB_NIL_ADDRESS		; empty list
	je %%end	
	CDR r10, r10					; next value in list
	inc %2							; increase counter
	jmp %%loop
%%end:
%endmacro


; %1 is the list we want to count
; %2 list size
; at the end of this macro the list will be inserted to stack in reverse order
%macro PUSH_LIST_TO_STACK 2
mov r10, %2					; r10 <- counter
%%loop1:
	push r10				; save the last counter state
	cmp r10, 0				; check if current list size is empty
	je %%end				; end if empty list
	push %1					; save current list state
	%%loop2:
		dec r10				; decrease counter
		cmp r10, 0			; we got to the last
		je %%end_loop_2		; we got to |r10| deep in list
		CDR %1, %1			; list <- (cdr list)
		jmp %%loop2
	%%end_loop_2:
	CAR r15, %1				; r15 <- desirable value
	pop %1					; restore list
	pop r10					; restore current counter
	dec r10					; decrease counter
	push r15				; push current value to stack
	jmp %%loop1
%%end:
pop r10						; get rid of counter from stack
%endmacro

; push n - 2 arguments to stack, from arg_1 to arg_n-2 (without arg_0 and arg_n-1 which they are proc and list)
%macro PUSH_ARGS_TO_STACK 0
mov r10, [rbp + WORD_SIZE*3]				; r10 <- n
sub r10, 2									; subtract proc and list from arguments
cmp r10, 0									; no args to push
je %%end
%%loop:
	lea r11, [rbp + WORD_SIZE*(4 + r10)]	; r11 <- current arg pointer to push
	mov r11, qword [r11]							
	push r11								; push the current arg to stack
	dec r10
	cmp r10, 0								; no args to push
	je %%end
	jmp %%loop
%%end:
%endmacro







; Not in use:

; %1 new list pointer
; %2 number of arguments
; put a list of stack argument in %1 register
%macro CONSTRACT_ARGS_LIST 2
mov r10, %2									   ; r10 <- n
mov %1, SOB_NIL_ADDRESS					   	   ; %1 <- ()
dec r10										   ; |n| = r10 <- r10 - 1
%%test_currect_input:
	cmp r10, 0
	jne %%loop
	mov rax, 0
    idiv rax                				   ; num of arg is wrong so we terminate the program
%%loop:
	cmp r10, 1								   ; the first arg is proc so we shall finish                      
	je %%end_loop               			   ; no more argumetns
	lea r11, [rbp + WORD_SIZE*(r10 + 3)]       ; r11 <- last argument index (which is not list)
	mov r11, qword [r11]					   ; r11 <- last ragument (not list)
	mov r12, %1
	MAKE_PAIR(%1, r11, r12)      			   ; construct a new pair and put in %1
	dec r10
	jmp %%loop
%%end_loop:
%endmacro

; %1 is the list we want to count
; %2 list size
; at the end of this macro the list will be inserted to stack in reverse order
%macro PUSH_LIST_TO_STACK_TEST 2
mov r10, %1			; r10 <- list
mov r11, %2			; r11 <- |list|
cmp r11, 0			; no args to push
je %%end
dec r11				; r11 <- |list| - 1
mov r15, 0			; r15 <- counter initialize to zero

%%loop1:			; push args from list to stack in opposite direction (need to switch)
	cmp r10, SOB_NIL_ADDRESS			
	je %%loop2
	CAR r12, r10
	push r12
	CDR r10, r10
	jmp %%loop1

%%loop2:
	cmp r11, r15
	jle %%end										; jump if bellow or equal i.e r11 <= r15
	mov r12, qword [rsp + WORD_SIZE*r15]			; pointer from bellow
	mov r13, qword [rsp + WORD_SIZE*r11]			; pointer from above
	mov qword [rsp + WORD_SIZE*r15] , r13
	mov qword [rsp + WORD_SIZE*r11] , r12
	dec r11
	inc r15
	jmp %%loop2
%%end:
%endmacro

; %1 is the list we want to insert
; at the end of this macro the list was inserted to stack
%macro PUSH_ARGS_LIST_TO_STACK 1
push r10
%%loop:
	cmp %1, SOB_NIL_ADDRESS
	je %%end
	mov r10, %1
	CAR r10, r10
	push r10
	CDR %1, %1
	jmp %%loop
%%end:
pop r10
%endmacro


;;;

	
;;; Macros and routines for printing Scheme OBjects to STDOUT
%define CHAR_NUL 0
%define CHAR_TAB 9
%define CHAR_NEWLINE 10
%define CHAR_PAGE 12
%define CHAR_RETURN 13
%define CHAR_SPACE 32
%define CHAR_DOUBLEQUOTE 34
%define CHAR_BACKSLASH 92
	
extern printf, malloc
global write_sob, write_sob_if_not_void
	
write_sob_undefined:
	push rbp
	mov rbp, rsp

	mov rax, qword 0
	mov rdi, .undefined
	call printf

	pop rbp
	ret

section .data
.undefined:
fmt     db "%u  %s",10,0
	db "#<undefined>", 0

section .text
write_sob_rational:
	push rbp
	mov rbp, rsp

	mov rdx, rsi
	NUMERATOR rsi, rdx
	DENOMINATOR rdx, rdx
	
	cmp rdx, 1
	jne .print_fraction

	mov rdi, .int_format_string
	jmp .print

.print_fraction:
	mov rdi, .frac_format_string

.print:	
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.int_format_string:
	db "%ld", 0
.frac_format_string:
	db "%ld/%ld", 0

section .text
write_sob_float:
	push rbp
	mov rbp, rsp

	FLOAT_VAL rsi, rsi
	movq xmm0, rsi
	mov rdi, .float_format_string
	mov rax, 1

	;; printf-ing floats (among other things) requires the stack be 16-byte aligned
	;; so align the stack *downwards* (take up some extra space) if needed before
	;; calling printf for floats
	and rsp, -16 
	call printf

	;; move the stack back to the way it was, cause we messed it up in order to
	;; call printf.
	;; Note that the `leave` instruction does exactly this (reset the stack and pop
	;; rbp). The instructions are explicitly layed out here for clarity.
	mov rsp, rbp
	pop rbp
	ret
	
section .data
.float_format_string:
	db "%f", 0		

section .text
write_sob_char:
	push rbp
	mov rbp, rsp

	CHAR_VAL rsi, rsi

	cmp rsi, CHAR_NUL
	je .Lnul

	cmp rsi, CHAR_TAB
	je .Ltab

	cmp rsi, CHAR_NEWLINE
	je .Lnewline

	cmp rsi, CHAR_PAGE
	je .Lpage

	cmp rsi, CHAR_RETURN
	je .Lreturn

	cmp rsi, CHAR_SPACE
	je .Lspace
	jg .Lregular

	mov rdi, .special
	jmp .done	

.Lnul:
	mov rdi, .nul
	jmp .done

.Ltab:
	mov rdi, .tab
	jmp .done

.Lnewline:
	mov rdi, .newline
	jmp .done

.Lpage:
	mov rdi, .page
	jmp .done

.Lreturn:
	mov rdi, .return
	jmp .done

.Lspace:
	mov rdi, .space
	jmp .done

.Lregular:
	mov rdi, .regular
	jmp .done

.done:
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.space:
	db "#\space", 0
.newline:
	db "#\newline", 0
.return:
	db "#\return", 0
.tab:
	db "#\tab", 0
.page:
	db "#\page", 0
.nul:
	db "#\nul", 0
.special:
	db "#\x%02x", 0
.regular:
	db "#\%c", 0

section .text
write_sob_void:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .void
	call printf

	pop rbp
	ret

section .data
.void:
	db "#<void>", 0
	
section .text
write_sob_bool:
	push rbp
	mov rbp, rsp

	cmp word [rsi], word T_BOOL
	je .sobFalse
	
	mov rdi, .true
	jmp .continue

.sobFalse:
	mov rdi, .false

.continue:
	mov rax, 0
	call printf	

	pop rbp
	ret

section .data			
.false:
	db "#f", 0
.true:
	db "#t", 0

section .text
write_sob_nil:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .nil
	call printf

	pop rbp
	ret

section .data
.nil:
	db "()", 0

section .text
write_sob_string:
	push rbp
	mov rbp, rsp

	push rsi

	mov rax, 0
	mov rdi, .double_quote
	call printf
	
	pop rsi

	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rbx, CHAR_TAB
	je .ch_tab
	cmp rbx, CHAR_NEWLINE
	je .ch_newline
	cmp rbx, CHAR_PAGE
	je .ch_page
	cmp rbx, CHAR_RETURN
	je .ch_return
	cmp rbx, CHAR_DOUBLEQUOTE
	je .ch_doublequote
	cmp rbx, CHAR_BACKSLASH
	je .ch_backslash
	cmp rbx, CHAR_SPACE
	jl .ch_hex
	
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx
	jmp .printf
	
.ch_tab:
	mov rdi, .fs_tab
	mov rsi, rbx
	jmp .printf
	
.ch_page:
	mov rdi, .fs_page
	mov rsi, rbx
	jmp .printf
	
.ch_return:
	mov rdi, .fs_return
	mov rsi, rbx
	jmp .printf

.ch_newline:
	mov rdi, .fs_newline
	mov rsi, rbx
	jmp .printf

.ch_doublequote:
	mov rdi, .fs_doublequote
	mov rsi, rbx
	jmp .printf

.ch_backslash:
	mov rdi, .fs_backslash
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .double_quote
	call printf

	pop rbp
	ret
section .data
.double_quote:
	db CHAR_DOUBLEQUOTE, 0
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	
.fs_tab:
	db "\t", 0
.fs_page:
	db "\f", 0
.fs_return:
	db "\r", 0
.fs_newline:
	db "\n", 0
.fs_doublequote:
	db CHAR_BACKSLASH, CHAR_DOUBLEQUOTE, 0
.fs_backslash:
	db CHAR_BACKSLASH, CHAR_BACKSLASH, 0

section .text
write_sob_pair:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .open_paren
	call printf

	mov rsi, [rsp]

	CAR rsi, rsi
	call write_sob

	mov rsi, [rsp]
	CDR rsi, rsi
	call write_sob_pair_on_cdr
	
	add rsp, 1*8
	
	mov rdi, .close_paren
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.open_paren:
	db "(", 0
.close_paren:
	db ")", 0

section .text
write_sob_pair_on_cdr:
	push rbp
	mov rbp, rsp

	mov bl, byte [rsi]
	cmp bl, T_NIL
	je .done
	
	cmp bl, T_PAIR
	je .cdrIsPair
	
	push rsi
	
	mov rax, 0
	mov rdi, .dot
	call printf
	
	pop rsi

	call write_sob
	jmp .done

.cdrIsPair:
	CDR rbx, rsi
	push rbx
	CAR rsi, rsi
	push rsi
	
	mov rax, 0
	mov rdi, .space
	call printf
	
	pop rsi
	call write_sob

	pop rsi
	call write_sob_pair_on_cdr

.done:
	pop rbp
	ret

section .data
.space:
	db " ", 0
.dot:
	db " . ", 0

section .text
write_sob_symbol:
	push rbp
	mov rbp, rsp

	SYMBOL_VAL rsi, rsi
	
	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

	mov rdx, rcx

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rcx, rdx
	jne .ch_simple
	cmp rbx, '+'
	je .ch_hex
	cmp rbx, '-'
	je .ch_hex
	cmp rbx, 'A'
	jl .ch_hex

.ch_simple:
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	pop rbp
	ret
	
section .data
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	

section .text
write_sob_closure:
	push rbp
	mov rbp, rsp

	CLOSURE_CODE rdx, rsi
	CLOSURE_ENV rsi, rsi

	mov rdi, .closure
	mov rax, 0
	call printf

	pop rbp
	ret
section .data
.closure:
	db "#<closure [env:%p, code:%p]>", 0

section .text
write_sob_vector:
    push rbp
    mov rbp, rsp

    push rsi

    mov rax, 0
    mov rdi, .vector_open_paren
    call printf

    mov rsi, [rsp]

    SKIP_TYPE_TAG rcx, rsi
    VECTOR_ELEMENTS rax, rsi

.loop:
    cmp rcx, 0
    je .done

    mov rsi, [rax]
    push rax
    push rcx
    call write_sob
    pop rcx
    pop rax

    dec rcx
    jz .done

    push rax
    push rcx
    mov rax, 0
    mov rdi, .vector_space
    call printf
    pop rcx
    pop rax

    add rax, WORD_SIZE
    jmp .loop

.done:
    mov rax, 0
    mov rdi, .vector_close_paren
    call printf

    pop rsi

    pop rbp
    ret

section .data
.vector_open_paren:
    db "#(", 0

.vector_space:
    db " ", 0

.vector_close_paren:
    db ")", 0

section .text
write_sob:
	mov rbx, 0
	mov bl, byte [rsi]	
	jmp qword [.jmp_table + rbx * 8]

section .data
.jmp_table:
	dq write_sob_undefined, write_sob_void, write_sob_nil
	dq write_sob_rational, write_sob_float, write_sob_bool
	dq write_sob_char, write_sob_string, write_sob_symbol
	dq write_sob_closure, write_sob_pair, write_sob_vector

section .text
write_sob_if_not_void:
	mov rsi, rax
	mov bl, byte [rsi]
	cmp bl, T_VOID
	je .continue

	call write_sob
	
	mov rax, 0
	mov rdi, .newline
	call printf
	
.continue:
	ret
section .data
.newline:
	db CHAR_NEWLINE, 0
