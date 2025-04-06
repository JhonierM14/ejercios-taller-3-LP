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
    (expression ("(" "circuit" gate-list ")") circuit-exp)
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
    ;(circuit ("(" "circuit" gate-list ")") cirtuit-case)
    ;;;;;;
    (primitive ("+") add-prim)
    (primitive ("eval-circuit") eval-circuit)
    (primitive ("connect-circuits") connect-circuits)
    (primitive ("merge-circuit") merge-circuit)
    (primitive ("-") substract-prim)
    (primitive ("*") mult-prim)
    (primitive ("add1") incr-prim)
    (primitive ("sub1") decr-prim)))

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

;definición del tipo de dato ambiente
(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record (syms (list-of symbol?))
                       (vals (list-of scheme-value?))
                       (env environment?)))

(define scheme-value? (lambda (v) #t))

;extend-env: <list-of symbols> <list-of numbers> enviroment -> enviroment
;función que crea un ambiente extendido
(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env))) 

;empty-env:      -> enviroment
;función que crea un ambiente vacío
(define empty-env  
  (lambda ()
    (empty-env-record)))       ;llamado al constructor de ambiente vacío 

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

(define init-env
  (lambda ()
    (extend-env
     '(A B)
     '(True False)
     (empty-env))))

(define eval-program
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
                 (eval-expression body (init-env))))))

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

;eval-gates (car args) env)
  
;true-value?: determina si un valor dado corresponde a un valor booleano falso o verdadero
(define true-value?
  (lambda (x)
    (eq? x 'True)))

(define ultimo-gate
  (lambda (gl)
        (ultimo-de-la-lista gl)))

(define ultimo-de-la-lista
  (lambda (lst)
    (if (null? (cdr lst))
        (car lst)
        (ultimo-de-la-lista (cdr lst)))))

(define eval-circuit-aux
  (lambda (el-gate-list env)
    (cases gate-list el-gate-list
      (gate-list-exp (el-gate-list)
         ;(display "-----") (display (ultimo-gate el-gate-list))
         (eval-gate-final el-gate-list (ultimo-gate el-gate-list) env)
        ;(display (display (eval-gate-final el-gate-list (ultimo-gate el-gate-list) env)) (display "-----------------"))
      )
    )
  )
)

(define eval-gate-final
  (lambda (gates final-gate env)
    (if (null? gates)
      (apply-env env (get-id final-gate)) ;; retorna el valor del gate final
      (eval-gate-final (cdr gates) final-gate (eval-gate (car gates) env))   
      )
    ;(display env)
    )
  )


;(define eval-gate-final
;  (lambda (gates env)
;    (if (null? (cdr gates))
;        (if (eval-gate (car gates) env gates)
;            'True
;            'False)
;        (eval-gate-final (cdr gates) env))))

(define get-id
  (lambda (g)
    (cases gate g
      (gate-exp (id type inputs) id))))

;; (define eval-gate-final-helper
;;   (lambda (gates env last-id)
;;     (if (null? gates)
;;         (apply-env env last-id)
;;         (eval-gate-final-helper
;;          (cdr gates)
;;          (extend-env
;;           (list (gate-id (car gates)))
;;           (list (display-and-eval-gate (car gates) env gates))
;;           env)
;;          last-id))))

;; (define eval-gate-final-recur
;;   (lambda (rest-gates env all-gates)
;;     (if (null? rest-gates)
;;         (apply-env env (gate-id (car (reverse all-gates))))
;;         (eval-gate-final-helper (car rest-gates)
;;                                 (cdr rest-gates)
;;                                 env
;;                                 all-gates))))

(define gate-id
  (lambda (g)
    (cases gate g
      (gate-exp (id typ inputs) id))))

(define eval-gate
  (lambda (el-gate env)
    (cases gate el-gate
      (gate-exp (id typ inputs)
        (let ((args (eval-inputs inputs env)))
          ;(eval-type typ args)
          (extend-env (list id) (list (eval-type typ args)) env)
          ;(display "Success")
          ;(display args)
          ;(display typ)
          ;(display (extend-env (list id) (list (eval-type typ args)) env))
        )
      )
    )
  )
)

;; ;(eval-circuit-exp circ env)
;; (define eval-bool
;;   (lambda (exp env)
;;     (cases bool exp
;;       (bool-exp-true () 'True)    ; Si la expresión es bool-exp-true, devolvemos #t
;;       (bool-exp-false () 'False)   ; Si la expresión es bool-exp-false, devolvemos #f
;;       )))

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

(define eval-or
  (lambda (inputs)
    (if (null? inputs)
        'False
        (if (eqv? (car inputs) 'True)
            'True
            (eval-or (cdr inputs))))))

(define eval-not
  (lambda (inputs)
    (if (eqv? (car inputs) 'True)
        'False
        'True))) ; Solo se usa el primero, como unario

;evaluar un gate con type xor
(define eval-xor
  (lambda (list-inputs)
    (if (null? list-inputs)
        'False
        (cond
          [(eqv? (car list-inputs) 'False) (eval-xor (cdr list-inputs))]
          [(eqv? (car list-inputs) 'True) (if (eqv? (eval-or(cdr list-inputs)) 'True)  'False 'True)]))))

(define eval-inputs
  (lambda (inputs env)
    (cases input-list inputs
      (input-list-id (lst)
        (eval-inputs-list lst env)))))


(define eval-inputs-list
  (lambda (inputs env)
    (if (null? inputs)
        '()
        (cons (eval-input (car inputs) env)
              (eval-inputs-list (cdr inputs) env)))))

;(define eval-input
;  (lambda (in env gates)
;    (cases input in
;      (ref-input (id) (apply-env env id))
;      (bool-input (exp)
;        (cases bool exp
;          (bool-exp-true () #t)
;          (bool-exp-false () #f))))))

(define eval-input
  (lambda (in env)
    (cases input in
      (ref-input (id)
        (apply-env env id))  ; asumimos que el id ya está en el ambiente
      (bool-input (exp)
        (cases bool exp
          (bool-exp-true () 'True)
          (bool-exp-false () 'False))))))



(define bound-id?
  (lambda (id env)
    (cases environment env
      (empty-env-record () (bool-exp-false))
      (extended-env-record (vars vals old-env)
        (if (null? vars)
            (bound-id? id old-env)
            (if (eq? (car vars) id)
                (bool-exp-true)
                (bound-id? id old-env)))))))


;###########################################################
; Implementacion
;###########################################################



;*******************************************************************************************
;Ambientes



;****************************************************************************************
;Funciones Auxiliares

; funciones auxiliares para encontrar la posición de un símbolo
; en la lista de símbolos de unambiente



;******************************************************************************************
;Pruebas

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


let
 c1 = (circuit (gate-list (gate G1 or (input-list A B))
                          (gate G2 and (input-list A B))
                          (gate G3 not (input-list G2))
                          (gate G4 and (input-list G1 G3))
))

in
 eval-circuit(c1)

;; AND

let
 c1 = (circuit (gate-list (gate G1 and (input-list A B))
))

in
 eval-circuit(c1)

;; OR

let
 c1 = (circuit (gate-list (gate G1 or (input-list A B))
))

in
 eval-circuit(c1)

;; NOT

let
 c1 = (circuit (gate-list (gate G1 not (input-list A))
))

in
 eval-circuit(c1)

;; XOR

let
 c1 = (circuit (gate-list (gate G1 xor (input-list A A))
))

in
 eval-circuit(c1)

|#


(interpretador)
