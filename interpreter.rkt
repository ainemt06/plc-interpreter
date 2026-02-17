#lang racket

;;;; =======================================================================
;;;; Aine Thomas (amt267) Daniel Borhegyi (dmb236)
;;;; =======================================================================

(require "simpleParser.rkt")


;; Possible steps:
; 1. Write M_state, M_bool, M_int, m_name
; 2. Write AddBinding, LookupBinding, RemoveBinding
;    2b. go back and make error messages more detailed
; 3. Do denotational semantics for anything we haven't done
; 4. Implement with the mappings/bindings we've done

;;;; ---------------------------------------------------------
;;;; CONSTANTS/ERRORS/SIMPLE ABSTRACTIONS
;;;; ---------------------------------------------------------

(define first-index 0)
(define value-of-binding car)
(define index-of-binding cdr)
(define operator car)
(define operand1 cadr)
(define operand2 caddr)

(define initial-state (cons '() '()))
(define acc 0)
(define get-state-names (lambda (state) (car state)))
(define get-state-values (lambda (state) (cdr state)))
(define return-state (lambda (names vals) (cons names vals)))
(define return-val (lambda (v) v))

(define (type-err) (error 'type "Parameter type mismatch"))
(define (missing-err) (error 'missing "Var not found in state"))
(define (unbound-err) (error 'unbound "List position out of bounds"))

;;;; ---------------------------------------------------------
;;;; LIST MANIPULATION HELPERS
;;;; ---------------------------------------------------------

(define len
(lambda (lis acc)
(if (null? lis) 
    acc
    (len (cdr lis) (+ acc 1)))))

(define return-pos-of-item
    (lambda (item lis acc)
        (cond
            ((null? item) type-err)
            ((null? lis) missing-err)
            ((eq? item (car lis)) acc)
            (else (return-pos-of-item item (cdr lis) (+ acc 1))))))

(define return-item-at-pos
    (lambda (pos lis)
        (cond
            ((not (number? pos)) type-err)
            ((null? lis) unbound-err)
            ((zero? pos) (car lis))
            (else (return-item-at-pos (- pos 1) (cdr lis))))))

;; check/debug
(define remove-item-at-pos
    (lambda (pos lis return)
        (cond
            ((not (number? pos)) type-err)
            ((null? lis) unbound-err)
            ((zero? pos) (return (cdr lis)))
            (else (remove-item-at-pos (- pos 1) (cdr lis) (lambda (v) (return (cons (car lis)) v)))))))

;;;; ---------------------------------------------------------
;;;; MAPPINGS
;;;; ---------------------------------------------------------


;; may be too nested
(define m-int
    (lambda (atom state)
        (if (number? atom) 
            atom
            (let ([val (value-of-binding (lookup-binding atom state))])
                  (if (number? val)
                      val
                      type-err)))))    

(define m-bool
    (lambda (atom state)
        (if (boolean? atom)
            atom
            (let ([val (value-of-binding (lookup-binding atom state))])
                 (if (boolean? val)
                     val
                     type-err)))))    


(define m-name
    (lambda (atom state)
        (let ([n (lookup-binding atom state)])
              (if (or (eq? n type-err) (eq? n missing-err) (eq? n unbound-err))
                  n
                  atom))))


; (define m-state
;     (lambda (construct state)
;     ; insert giant cond of everything we can handle atm
;     ))

;;;; ---------------------------------------------------------
;;;; BINDING OPERATIONS
;;;; ---------------------------------------------------------

;; in newest -> oldest order
(define add-binding 
    (lambda (name value state)
        (return-state (cons name (get-state-names state))
                      (cons value (get-state-values state)))))

(define lookup-binding
    (lambda (name state)
        (let* ([index (return-pos-of-item name (get-state-names state) first-index)]
               [value (return-item-at-pos index (get-state-values state))])
               (cons value index))))

(define remove-binding
    (lambda (name state)
        (let* ([binding (lookup-binding name state)]
               [index (index-of-binding binding)])
             (return-state (remove-item-at-pos index (get-state-names state))
                           (remove-item-at-pos index (get-state-values state))))))

;;;; ---------------------------------------------------------
;;;; DENOTATIONAL SEMANTICS
;;;; ---------------------------------------------------------

(define statement
    (lambda (expr state)
    (let ([op (operator expr)])
        (cond
            ((eq? op 'if) (if-statement expr state))
            ((eq? op 'while) (while expr state))
            ((eq? op 'var) (declare expr state))
            ((eq? op '=) (assign expr state))
            ((eq? op 'return) (return expr state))
            (else type-err)))))


(define expression
(lambda (expr state)
    (let ([int-binding (int-value expr state)]
          [bool-binding (condition expr state)])
          ((cond
            ((not (eq? type-err int-binding)) int-binding)
            ((not (eq? type-err bool-binding)) bool-binding)
            (else parse-err))))))


(define int-value
  (lambda (expr state)
    (cond
      ((number? expr) expr)
      ((symbol? expr) (m-int expr state))
      ((list? expr)
       (let ((op (operator expr)))
         (cond
           ((eq? op '+)
            (+ (int-value (operand1 expr) state)
               (int-value (operand2 expr) state)))
           ((eq? op '-)
            (if (= (length expr) 2)
                (- (int-value (operand1 expr) state)) 
                (- (int-value (operand1 expr) state)
                   (int-value (operand2 expr) state)))) 
           ((eq? op '*)
            (* (int-value (operand1 expr) state)
               (int-value (operand2 expr) state)))
           ((eq? op '/)
            (quotient (int-value (operand1 expr) state)
                      (int-value (operand2 expr) state)))
           ((eq? op '%)
            (remainder (int-value (operand1 expr) state)
                       (int-value (operand2 expr) state)))
           (else type-err))))
      (else type-err))))
;; what
; statement list 	<statementlist> ::= <statement> <statementlist> | nothing
; (statement1 statement2 ...)
; statement 	<statement> ::= <declare> | <assign> | <return> | <if> | <while>

;; nontrivial
; variable declaration 	<declare> ::= var <name>; | var <assign>;
; (var variable optional-value)
; assignment 	<assign> ::=  <name> = <expresson>;
; (= variable expression)
; return 	<return> ::= return <expression>;
; (return expression)

;; hard
; if statement 	<if> ::= if (<condition>) <statement> | if (<condition>) <statement> else <statement>
; (if condition then-statement optional-else-statement)
; while statement 	<while> ::= while (<condition>) <statement>
; (while condition body-statement)

;; ez
; expression 	<expression> ::= <condition> | <int value>
; condition 	<condition> ::= true | false | <name> | <condition> && <condition> | <condition> || <condition> | !<condition> | <int value> < <int value> | <int value> <= <int value> | <int value> > <int value> | <int value> >= <int value> | <expression> == <expression> | <expression> != <expression> 
; (&& condition condition)
; int value 	<int value> ::= <number> | <name> | <int value> + <int value> | <int value> - <int value> | <int value> * <int value> | <int value> / <int value> | <int value> % <int value> | - <int value>
; (+ intvalue intvalue)