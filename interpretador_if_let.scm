#lang eopl
;******************************************************************************************
;;;;; Interpretador para lenguaje con condicionales y ligadura local

;; La definición BNF para las expresiones del lenguaje:
;;
;;  <program>       ::= <expression>
;;                      <a-program (exp)>
;;  <expression>    ::= <number>
;;                      <lit-exp (datum)>
;;                  ::= <identifier>
;;                      <var-exp (id)>
;;                  ::= <primitive> ({<expression>} *( , ))
;;                      <primapp-exp (prim rands)>
;;                  ::= if <expression> then <expression> else <expression>
;;                  ::= let (<identifier> = <expression>)∗ in <expression>
;;                  ::= <circuit>
;; <primitive>      ::= + | - | ∗ | add1 | sub1
;;                  ::= eval-circuit | connect-circuits | merge-circuits
;; <circuit>        ::= <gate_list>
;; <gate_list>      ::= empty | <gate> <gate_list>
;; <gate>           ::= <identifier> <type> <input_list>
;; <type>           ::= and | or | not | xor
;; <input_list>     ::= empty | <bool> <input_list>
;;                      | <identifier> <input_list>
;; <bool>           ::= True | False

;******************************************************************************************

;******************************************************************************************
;Especificación Léxica

(define scanner-spec-simple-interpreter
'((white-sp
   (whitespace) skip)
  (comment
   ("%" (arbno (not #\newline))) skip)
  (identifier
   (letter (arbno (or letter digit "?"))) symbol)
  (number
   (digit (arbno digit)) number)
  (number
   ("-" digit (arbno digit)) number)))

;Especificación Sintáctica (gramática)

(define grammar-simple-interpreter
  '((program (expression) a-program)
    (expression (number) lit-exp)
    (expression (identifier) var-exp)
    (expression
     (primitive "(" (separated-list expression ",")")")
     primapp-exp)
    ; características adicionales
    (expression ("if" expression "then" expression "else" expression)
                if-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression)
                let-exp)
    ;Caracteristicas especiales para el tercer taller
    (expression (circuit) circuit-exp)
    (bool ("True") bool-exp-true)
    (bool ("False") bool-exp-false)
    (input (bool) bool-input)
    (input (identifier) ref-input)
    (input-list ("(" "input-list" (arbno input) ")") input-list-id)
    (type ("xor") xor-type)
    (type ("and") and-type)
    (type ("or") or-type)
    (type ("not") not-type)
    (gate ("(" "gate" identifier type input-list  ")") gate-exp)
    (gate-list ( "(" "gate-list" (arbno gate) ")") gate-list-exp)
    (circuit ("(" "circuit" gate-list ")") circuit-case)
    ;;;;;;
    (primitive ("+") add-prim)
    (primitive ("eval-circuit") eval-circuit)
    (primitive ("connect-circuits") connect-circuits)
    (primitive ("merge-circuit") merge-circuit)
    (primitive ("-") substract-prim)
    (primitive ("*") mult-prim)
    (primitive ("add1") incr-prim)
    (primitive ("sub1") decr-prim)))

;(define-datatype program program?
;  (a-program
;   (exp expression?)))
;
;(define-datatype expression expression?
;  (lit-exp
;   (datum number?))
;  (var-exp
;   (id symbol?))
;  (primapp-exp
;   (prim primitive?)
;   (rands (list-of expression?)))
;  (if-exp
;   (test-exp expression?)
;   (true-exp expression?)
;   (false-exp expression?))
;  (let-exp
;   (ids (list-of symbol?))
;   (rans (list-of expression?))
;   (body expression?)))
;
;(define-datatype primitive primitive?
;  (add-prim)
;  (substract-prim)
;  (mult-prim)
;  (incr-prim)
;  (decr-prim))

;Construidos automáticamente:

(sllgen:make-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec-simple-interpreter grammar-simple-interpreter)))

;*******************************************************************************************
;Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Analizador Léxico (Scanner)

(define just-scan
  (sllgen:make-string-scanner scanner-spec-simple-interpreter grammar-simple-interpreter))

;El Interpretador (FrontEnd + Evaluación + señal para lectura )

(define interpretador
  (sllgen:make-rep-loop  "--> "
    (lambda (pgm) (eval-program  pgm)) 
    (sllgen:make-stream-parser 
      scanner-spec-simple-interpreter
      grammar-simple-interpreter)))

;*******************************************************************************************
;El Interprete

;eval-program: <programa> -> numero
; función que evalúa un programa teniendo en cuenta un ambiente dado (se inicializa dentro del programa)

(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (eval-expression body (init-env))))))

(define init-env
  (lambda ()
    (extend-env
     '(A B)
     '(True False)
     (empty-env))))

;eval-expression: <expression> <enviroment> -> numero
; evalua la expresión en el ambiente de entrada

(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (lit-exp (datum) datum)
      (var-exp (id) (apply-env env id))
      (primapp-exp (prim rands)
                   (let ((args (eval-rands rands env)))
                     (apply-primitive prim args env)))
      (if-exp (test-exp true-exp false-exp)
              (if (true-value? (eval-expression test-exp env))
                  (eval-expression true-exp env)
                  (eval-expression false-exp env)))
      (let-exp (ids rands body)
               (let ((args (eval-rands rands env)))
                 (eval-expression body
                                  (extend-env ids args env))))
      (circuit-exp (circ)
                   circ)

      )))

; funciones auxiliares para aplicar eval-expression a cada elemento de una 
; lista de operandos (expresiones)
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))

;apply-primitive: <primitiva> <list-of-expression> -> numero
(define apply-primitive
  (lambda (prim args env)
    (cases primitive prim
      (add-prim () (+ (car args) (cadr args)))
      (substract-prim () (- (car args) (cadr args)))
      (mult-prim () (* (car args) (cadr args)))
      (incr-prim () (+ (car args) 1))
      (decr-prim () (- (car args) 1))
      (eval-circuit () (eval-circuit-aux (car args) env))
      (else 'FALTACONNECTCIRCUITS))
    ))

;true-value?: determina si un valor dado corresponde a un valor booleano falso o verdadero
(define true-value?
  (lambda (x)
    (eq? x 'True)))

;(eval-circuit-exp circ env)
(define eval-bool
  (lambda (exp env)
    (cases bool exp
      (bool-exp-true () #t)    ; Si la expresión es bool-exp-true, devolvemos #t
      (bool-exp-false () #f)   ; Si la expresión es bool-exp-false, devolvemos #f
      )))

;eval-gates (car args) env)
  


(define eval-circuit-aux
  (lambda (el-circuit env)
    (cases circuit el-circuit
      (circuit-case (el-gate-list)
        (cases gate-list el-gate-list
          (gate-list-exp (el-gates)
            (eval-gate-inicial el-gates env))))))) ; se evalua un get se obtiene su valor y se almacena en el ambiente

; eval-gate-inicial: Evalúa todos los gates en la lista y almacena los resultados en el ambiente
(define eval-gate-inicial
  (lambda (gates env)
    (if (null? (cdr gates)) 
        (let ((gate (car gates))) 
          (extend-env (list (gate-id gate)) ; Agregar el identificador del gate al ambiente
                      (list (eval-gate gate env gates)) ; Evaluamos el gate y obtenemos su valor
                      env)) ; Devolvemos el nuevo ambiente extendido
        (eval-gate-inicial (cdr gates) env)))) ; Recursión para evaluar el resto de los gates

; eval-gate: Evalúa una sola puerta y almacena su resultado en el ambiente
(define eval-gate
  (lambda (el-gate env gates)
    (cases gate el-gate
      (gate-exp (id typ inputs)
        (let ((args (eval-inputs inputs env gates)))
          (eval-type typ args))))))

; Suponiendo que gate-id es el accesor para obtener el identificador del gate
(define gate-id
  (lambda (el-gate)
    (cases gate el-gate
      (gate-exp (id type inputs) id))))


; eval-inputs: Evalúa los inputs de un gate (pueden ser referencias o booleanos)
(define eval-inputs
  (lambda (inputs env gates)
    (cases input-list inputs
      (input-list-id (lst)
        (eval-inputs-list lst env gates)))))

; eval-inputs-list: Evalúa una lista de inputs
(define eval-inputs-list
  (lambda (inputs env gates)
    (if (null? inputs)
        '()  ; Caso base: lista vacía
        (cons (eval-input (car inputs) env gates)  ; Evalúa el primer input
              (eval-inputs-list (cdr inputs) env gates)))))  ; Llamada recursiva para el resto de la lista

; eval-input: Evalúa un solo input (puede ser un ref-input o un bool-input)
(define eval-input
  (lambda (in env gates)
    (cases input in
      (ref-input (id)
        (apply-env env id))  ; Si es un ref-input, busca el valor en el ambiente
      (bool-input (exp)
        (cases bool exp
          (bool-exp-true () #t)  ; Si es un bool-exp-true, devuelve #t
          (bool-exp-false () #f))))))  ; Si es un bool-exp-false, devuelve #f

; eval-gate-store-result: Almacena el resultado en el ambiente sin usar let
(define eval-gate-store-result
  (lambda (id result env)
    (extend-env (list id) (list result) env)))

(define eval-type
  (lambda (typ inputs)
    (cases type typ
      (and-type ()
        (if (null? inputs)
            #t
            (and (car inputs) (eval-type typ (cdr inputs)))))
      (or-type ()
        (if (null? inputs)
            #f
            (or (car inputs) (eval-type typ (cdr inputs)))))
      (not-type ()
        (if (null? inputs)
            ('not-gate-needs-one-input)
            (not (car inputs))))
      (xor-type ()
        (xor-list inputs)))))

(define xor-list
  (lambda (lst)
    (if (null? lst)
        #f
        (xor (car lst) (xor-list (cdr lst))))))

(define xor
  (lambda (a b)
    (or (and a (not b)) (and (not a) b))))

;*******************************************************************************************
;Ambientes

;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record (syms (list-of symbol?))
                       (vals (list-of scheme-value?))

                       (env environment?)))

(define scheme-value? (lambda (v) #t))

;empty-env:      -> enviroment
;función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (empty-env-record)))       ;llamado al constructor de ambiente vacío 

;extend-env: <list-of symbols> <list-of numbers> enviroment -> enviroment
;función que crea un ambiente extendido
(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env))) 

;función que busca un símbolo en un ambiente
(define apply-env
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
                        (eopl:error 'apply-env "No binding for ~s" sym))
      (extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))))))

;****************************************************************************************
;Funciones Auxiliares

; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de unambiente

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))


;******************************************************************************************
;Pruebas


(show-the-datatypes)
just-scan
scan&parse
(just-scan "add1(x)")
(just-scan "add1(   x   )%cccc")
(just-scan "add1(  +(5, x)   )%cccc")
(just-scan "add1(  +(5, %ccccc x) ")
(scan&parse "add1(x)")
(scan&parse "add1(   x   )%cccc")
(scan&parse "add1(  +(5, x)   )%cccc")
(scan&parse "add1(  +(5, %cccc
x)) ")
(scan&parse "if -(x,4) then +(y,11) else *(y,10)")
(scan&parse "let
x = -(y,1)
in
let
x = +(x,2)
in
add1(x)")

(define caso1 (primapp-exp (incr-prim) (list (lit-exp 5))))
(define exp-numero (lit-exp 8))
(define exp-ident (var-exp 'c))
(define exp-app (primapp-exp (add-prim) (list exp-numero exp-ident)))
(define programa (a-program exp-app))
(define una-expresion-dificil (primapp-exp (mult-prim)
                                           (list (primapp-exp (incr-prim)
                                                              (list (var-exp 'v)
                                                                    (var-exp 'y)))
                                                 (var-exp 'x)
                                                 (lit-exp 200))))
(define un-programa-dificil
    (a-program una-expresion-dificil))

#|

(scan&parse "eval-circuit((circuit (gate-list (gate G1 or (input-list True False))
                                               (gate G2 and (input-list True True))
                                               (gate G3 not (input-list G2))
                                               (gate G4 and (input-list G1 G3)))))")

(scan&parse "
(circuit
(gate-list
(gate G1 or (input-list A B))
(gate G2 and (input-list A B))
(gate G3 not (input-list G2))
(gate G4 and (input-list G1 G3))))")

#--------------------
let
 c1 = (circuit (gate-list (gate G1 or (input-list A B))
                          (gate G2 and (input-list A B))
                          (gate G3 not (input-list A))
                          (gate G4 and (input-list G1 G3))))
in
 eval-circuit(c1)


#--------------------
let
 c1 = (circuit (gate-list (gate G1 or (input-list A B))
                          (gate G2 and (input-list A B))
                          (gate G3 not (input-list G2))
                          (gate G4 and (input-list G1 G3))))
in
 c1

#--------------------
let
 c1 = (circuit (gate-list (gate G1 or (input-list A B))))                          
in
 eval-circuit(c1)

#--------------------
let
 c1 = (circuit (gate-list (gate G1 or (input-list A B))))                          
in
 c1
|#

(interpretador)
