#lang eopl

;;-----------------------------------------
;; Jhonier Mendez Bravo 202372226
;; David Santiago Guerrero Delgado 202324594
;; Juan Pablo Robayo Maestre 202156743
;;-----------------------------------------

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
    (expression (primitive "(" (separated-list expression ",")")")
                primapp-exp)
    (expression ("if" expression "then" expression "else" expression)
                if-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression)
                let-exp)
    
    ;-------Caracteristicas especiales para el tercer taller-------
    (expression ("(" "circuit" gate-list ")") circuit-exp)
    (expression (circuit-primitive "(" (separated-list expression ",")")")
                cirapp-exp)
    
    (bool ("True") bool-exp-true)
    (bool ("False") bool-exp-false)
    
    (type ("xor") xor-type)
    (type ("and") and-type)
    (type ("or") or-type)
    (type ("not") not-type)
    
    (input (bool) bool-input)
    (input (identifier) ref-input)
    (input-list ("(" "input-list" (arbno input) ")") input-list-id)
    
    (gate ("(" "gate" identifier type input-list  ")") gate-exp)
    (gate-list ( "(" "gate-list" (arbno gate) ")") gate-list-exp)
    
    ;-----------------Primitivas-----------------
    (primitive ("+") add-prim)
    (primitive ("-") substract-prim)
    (primitive ("*") mult-prim)
    (primitive ("add1") incr-prim)
    (primitive ("sub1") decr-prim)
    (primitive ("eval-circuit") eval-circuit)
    (circuit-primitive ("connect-circuits") connect-circuits)
    (circuit-primitive ("merge-circuit") merge-circuit)
  )
)

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
     '(A B C D)
     '(True False False True)
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
      (circuit-exp (circ) circ)
      (cirapp-exp (prim rands)
  (let ((evaluated-args (eval-all-but-last rands env))
        (symbol-arg (get-symbol-from-last rands)))
    (apply-circuit-primitive prim (append evaluated-args (list symbol-arg)) env)))

    )
  )
)

(define eval-all-but-last
  (lambda (rands env)
    (cond
      [(null? rands) '()]
      [(null? (cdr rands)) '()] ; último, no se evalúa
      [else
       (cons (eval-expression (car rands) env)
             (eval-all-but-last (cdr rands) env))])))

(define get-symbol-from-last
  (lambda (rands)
    (let ((last-exp (car (reverse rands))))
      (cases expression last-exp
        (var-exp (id) id)
        (else (eopl:error 'get-symbol-from-last "Último argumento no es un símbolo válido"))))))


; funciones auxiliares para aplicar eval-expression a cada elemento de una 
; lista de operandos (expresiones)
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-rand x env)) rands)))

(define eval-rand
  (lambda (rand env)
    (eval-expression rand env)))

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

(define search-env
  (lambda (env val)
    (cases environment env
      (empty-env-record ()
        #f)
      (extended-env-record (syms vals rest-env)
        (let ((pos (list-find-position val vals)))
          (if (number? pos)
              (list-ref syms pos)
              (search-env rest-env val)))))))

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
    )
  )
)

(define apply-circuit-primitive
  (lambda (prim args env)
    (cases circuit-primitive prim
      (connect-circuits () (connect-circuits-aux (car args) (cadr args) (caddr args) env))
      (else 'FALTAMERGECIRCUITS)
    )
  )
)
  
;true-value?: determina si un valor dado corresponde a un valor booleano falso o verdadero
(define true-value?
  (lambda (x)
    (eq? x 'True)))

;;Pruebas
(true-value? 'True)
(true-value? 'False)

; funcion que retorna el ultimo gate de un arbol de sintaxis abstracta
(define ultimo-gate
  (lambda (gl)
        (ultimo-de-la-lista gl)))

; funcion recursiva que busca el ultimo elemento de la lista
(define ultimo-de-la-lista
  (lambda (lst)
    (if (null? (cdr lst))
        (car lst)
        (ultimo-de-la-lista (cdr lst)))))

; funcion auxiliar para calcular el resultado de cada gate en el arbol de sintaxis abstracta
(define eval-circuit-aux
  (lambda (el-gate-list env)
    (cases gate-list el-gate-list
      (gate-list-exp (el-gate-list)
         (eval-gate-final el-gate-list (ultimo-gate el-gate-list) env)
      )
    )
  )
)

; funcion que manda a evaluar y retorna el valor del ultimo gate
(define eval-gate-final
  (lambda (gates final-gate env)
    (if (null? gates)
      (apply-env env (get-id final-gate)) ;; retorna el valor del gate final
      (eval-gate-final (cdr gates) final-gate (eval-gate (car gates) env))   
      )
    )
  )

; funcion que retorna el id de un gate
(define get-id
  (lambda (g)
    (cases gate g
      (gate-exp (id type inputs) id))))

; funcion que evalua un gate
(define eval-gate
  (lambda (el-gate env)
    (cases gate el-gate
      (gate-exp (id typ inputs)
        (let ((args (eval-inputs inputs env)))
          (extend-env (list id) (list (eval-type typ args)) env)
        )
      )
    )
  )
)

; funcion que evalua el tipo de circuito
(define eval-type
  (lambda (typ inputs) ; typ type, 
    (cases type typ
      (and-type ()
        (eval-and inputs))  ; Caso AND
      (or-type ()
        (eval-or inputs))   ; Caso OR
      (not-type ()
        (eval-not inputs))  ; Caso NOT
      (xor-type ()
        (eval-xor inputs))  ; Caso XOR
    )))

; funcion que evalua el tipo and
(define eval-and
  (lambda (inputs)
    (if (null? inputs)
        'True
        (if (eq? (car inputs) 'True)
            (eval-and (cdr inputs))
            'False
            )
    )
  )
)

; funcion que evalua el tipo or
(define eval-or
  (lambda (inputs)
    (if (null? inputs)
        'False
        (if (eqv? (car inputs) 'True)
            'True
            (eval-or (cdr inputs))))))

; funcion que evalua el tipo not
(define eval-not
  (lambda (inputs)
    (if (eqv? (car inputs) 'True)
        'False
        'True))) ; Solo se usa el primero, como unario

; funcion que evalua el tipo xor
(define eval-xor
  (lambda (list-inputs)
    (if (null? list-inputs)
        'False
        (cond
          [(eqv? (car list-inputs) 'False) (eval-xor (cdr list-inputs))]
          [(eqv? (car list-inputs) 'True) (if (eqv? (eval-or(cdr list-inputs)) 'True)  'False 'True)]))))

(define connect-circuits-aux
  (lambda (F-Circuit S-Circuit Entry env)
    (cases gate-list F-Circuit
      (gate-list-exp (el1-gate-list)
        (let ((new-id (get-id (ultimo-gate el1-gate-list))))
          (cases gate-list S-Circuit
            (gate-list-exp (el2-gate-list)
              (let ((new-second (change-gate-list-entry el2-gate-list Entry new-id)))
                (append-gate-lists el1-gate-list new-second)
              )
            )
          )
        )
      )
    )
  )
)

;; Reemplaza las entradas igual a old-id por new-id en cada gate
(define change-gate-list-entry
  (lambda (gate-list old-id new-id)
    (if (null? gate-list)
      '()
      (cons (change-gate-entry (car gate-list) old-id new-id)
            (change-gate-list-entry (cdr gate-list) old-id new-id))
    )
  )
)

(define change-gate-entry
  (lambda (g old-id new-id)
    (cases gate g
      (gate-exp (id type inputs)
        (gate-exp id type (change-input-list-entry inputs old-id new-id))
      )
    )
  )
)

(define change-input-list-entry
  (lambda (inputs old-id new-id)
    (cases input-list inputs
      (input-list-id (ids)
        (input-list-id (change-id-list-entry ids old-id new-id))
      )
    )
  )
)

(define change-id-list-entry
  (lambda (ids old-id new-id)
    (if (null? ids)
      '()
      (let ((curr-id (ref-id (car ids))))
        (if (eq? curr-id old-id)
           (cons (ref-input new-id)
                 (change-id-list-entry (cdr ids) old-id new-id))
           (cons (car ids)
                 (change-id-list-entry (cdr ids) old-id new-id))
        )
      )
    )
  )
)

(define ref-id
  (lambda (in)
    (cases input in
      (ref-input (in) in)
      (else in)
    )
  )
)

;; Une dos listas de gates (sin usar append)
(define append-gate-lists
  (lambda (l1 l2)
    (if (null? l1)
        l2
        (cons (car l1) (append-gate-lists (cdr l1) l2))
    )
  )
)

;(change-entry '(G D W A) 'A 'B)

; funcion que manda a evaluar una lista de inputs perteneciente a un gate
(define eval-inputs
  (lambda (inputs env)
    (cases input-list inputs
      (input-list-id (lst)
        (eval-inputs-list lst env)))))

; funcion que manda a evaluar inidividualmente cada input perteneciente a un gate
(define eval-inputs-list
  (lambda (inputs env)
    (if (null? inputs)
        '()
        (cons (eval-input (car inputs) env)
              (eval-inputs-list (cdr inputs) env)))))

; funcion que evalua un input
(define eval-input
  (lambda (in env)
    (cases input in
      (ref-input (id)
        (apply-env env id))  ; asumimos que el id ya está en el ambiente
      (bool-input (exp)
        (cases bool exp
          (bool-exp-true () 'True)
          (bool-exp-false () 'False))))))


;###########################################################
; Implementacion
;###########################################################


;******************************************************************************************
;Pruebas

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

(scan&parse "
let
 c1 = (circuit (gate-list (gate G1 or (input-list A B))
                          (gate G2 and (input-list A B))
                          (gate G3 not (input-list G2))
                          (gate G4 and (input-list G1 G3))))
in
 eval-circuit(c1)")

;; AND
(eval-program (scan&parse "
let
 c1 = (circuit (gate-list (gate G1 and (input-list A B))))
in
 eval-circuit(c1)"))

;; OR
(eval-program (scan&parse "
let
 c1 = (circuit (gate-list (gate G1 or (input-list A B))))
in
 eval-circuit(c1)"))

;; NOT
(eval-program (scan&parse "
let
 c1 = (circuit (gate-list (gate G1 not (input-list A))))
in
 eval-circuit(c1)"))

;; XOR
(eval-program (scan&parse "
let
 c1 = (circuit (gate-list (gate G1 xor (input-list A A))))
in
 eval-circuit(c1)")
)

(eval-program (scan&parse "
let
 c1 = (circuit (gate-list (gate G1 xor (input-list A A))))
in
 eval-circuit(c1)"))

#|
let
c1 = (circuit (gate-list (gate G1 or (input-list A B))
                         (gate G2 and (input-list A B))
                         (gate G3 not (input-list G2))
                         (gate G4 and (input-list G1 G3))
))

c2 = (circuit (gate-list (gate G5 or (input-list C D))
                         (gate G6 and (input-list C D))
                         (gate G7 and (input-list G5 G6))
))
in
connect-circuits(c1, c2, C)
|#

(interpretador)
