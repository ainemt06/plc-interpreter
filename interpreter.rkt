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
;;;; CONSTANTS/SIMPLE ABSTRACTIONS
;;;; ---------------------------------------------------------

(define first-index 0)
(define initial-state (cons '() '()))
(define get-state-names (lambda (state) (car state)))
(define get-state-values (lambda (state) (cdr state)))
(define return-state (lambda (names vals) (cons names vals)))
(define value-of-binding car)
(define index-of-binding cdr)


;;;; ---------------------------------------------------------
;;;; LIST MANIPULATION HELPERS
;;;; ---------------------------------------------------------

(define return-pos-of-item
    (lambda (item lis acc)
        (cond
            ((or (null? lis) (null? item)) error)
            ((eq? item (car lis)) acc)
            (else (return-pos-of-item item (cdr lis) (+ acc 1))))))

(define return-item-at-pos
    (lambda (pos lis)
        (cond
            ((or (null? lis) (not (number? pos))) error)
            ((zero? pos) (car lis))
            (else (return-item-at-pos (- pos 1) (cdr lis))))))

;; make tail recursive
(define remove-item-at-pos
    (lambda (pos lis)
    (cond
    ((or (null? lis) (not (number? pos))) error)
    ((zero? pos) (cdr lis))
    (else (cons (car lis) (remove-item-at-pos (- pos 1) (cdr lis)))))))

;;;; ---------------------------------------------------------
;;;; MAPPINGS
;;;; ---------------------------------------------------------

(define m-int
(lambda (atom state)
    (if
      ((number? atom) atom)
      (else
        (let ([val (value-of-binding (lookup-binding atom state))])
              (if (number? val)
                  val
                  error))))))    

(define m-bool
(lambda (atom state)
    (if
      ((boolean? atom) atom)
      (else
        (let ([val (value-of-binding (lookup-binding atom state))])
              (if (boolean? val)
                  val
                  error))))))    


;; COME BACK TO THIS WHEN WE CUSTOMIZE ERROR MESSAGES - EQ WON'T WORK
(define m-name
    (lambda (atom state)
        (let ([n (lookup-binding atom state)])
              (if (eq? n error)
                  error
                  atom))))


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
               (cons value . index))))

(define remove-binding
(lambda (name state)
    (let ([binding (lookup-binding name state)])
         (return-state (remove-item-at-pos (index-of-binding binding) (get-state-names state))
                       (remove-item-at-pos (index-of-binding binding) (get-state-values state))))))


; statement list 	<statementlist> ::= <statement> <statementlist> | nothing
; (statement1 statement2 ...)
; statement 	<statement> ::= <declare> | <assign> | <return> | <if> | <while>
; variable declaration 	<declare> ::= var <name>; | var <name> = <expression>;
; (var variable optional-value)
; assignment 	<assign> ::=  <name> = <expresson>;
; (= variable expression)
; return 	<return> ::= return <expression>;
; (return expression)
; if statement 	<if> ::= if (<condition>) <statement> | if (<condition>) <statement> else <statement>
; (if condition then-statement optional-else-statement)
; while statement 	<while> ::= while (<condition>) <statement>
; (while condition body-statement)
; expression 	<expression> ::= <condition> | <int value>
; condition 	<condition> ::= true | false | <name> | <condition> && <condition> | <condition> || <condition> | !<condition> | <int value> < <int value> | <int value> <= <int value> | <int value> > <int value> | <int value> >= <int value> | <expression> == <expression> | <expression> != <expression> 
; (&& condition condition)
; int value 	<int value> ::= <number> | <name> | <int value> + <int value> | <int value> - <int value> | <int value> * <int value> | <int value> / <int value> | <int value> % <int value> | - <int value>
; (+ intvalue intvalue)