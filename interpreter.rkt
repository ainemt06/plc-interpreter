#lang racket
(require "simpleParser.rkt")


;;;; =======================================================================
;;;; Aine Thomas (amt267) Daniel Borhegyi (dmb236)
;;;; =======================================================================

;;;; ---------------------------------------------------------
;;;; INTERPRET
;;;; ---------------------------------------------------------

; parse a file, then interpret it with the initial state
(define interpret
  (lambda (filename)
    (statement-list (parser filename) initial-state)))

;;;; ---------------------------------------------------------
;;;; CONSTANTS/ERRORS/SIMPLE ABSTRACTIONS
;;;; ---------------------------------------------------------

(define first-index 0)
(define value-of-binding car)
(define index-of-binding cdr)
(define operator car)
(define operand1 cadr)
(define operand2 caddr)
(define operand3 cadddr)

(define initial-state (cons '() '()))
(define acc 0)
(define get-state-names (lambda (state) (car state)))
(define get-state-values (lambda (state) (cdr state)))
(define return-state (lambda (names vals) (cons names vals)))
(define return-val (lambda (v) v))

(define (type-err) (error 'type "Parameter type mismatch"))
(define (missing-err) (error 'missing "Var not found in state"))
(define (unbound-err) (error 'unbound "List position out of bounds"))
(define (redefine-err) (error) 'redefine "Attempted to redefine a variable")
(define (parse-err) (error 'parse "Parsing error"))

; turn #t & #f into 'true and 'false
(define parse-bool
  (lambda (bool)
    (if bool
      'true
      'false)))

;;;; ---------------------------------------------------------
;;;; DENOTATIONAL SEMANTICS/M_STATE FUNCTIONS
;;;; ---------------------------------------------------------

; recurse through a list of statements and update the state with each one
(define statement-list
    (lambda (lis state)
        (if (null? lis) 
            state ; return the final state
            (statement-list (cdr lis) (statement (car lis) state)))))

; parse out the type of a statement and evaluate it (basically our M_state)
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


; declare and optionally initialize a variable
(define declare
    (lambda (expr state) 
        (if (not (eq? (lookup-binding (operand1 expr) state) missing-err)) ;prevent variables from being redeclared
            redefine-err
            (if (= (length expr) 2)
              (add-binding (operand1 expr) '() state) ; unassigned variables default to the empty list
              (add-binding (operand1 expr) (expression (operand2 expr) state) state)))))

;; set a variable to a value
(define assign 
    (lambda (expr state)
      (if (eq? (lookup-binding (operand1 expr) state) missing-err)  ; if this variable has not been bound to anything, throw an error
          missing-err 
          (let* ([state1 (remove-binding (operand1 expr) state)] ; remove the old binding and add the new one
                 [state2 (add-binding (operand1 expr) (expression (operand2 expr) state) state1)])
                 state2))))

; return/print the value of this statement
(define return 
    (lambda (expr state)
       (let ([val (expression (operand1 expr) state)])
         (if (boolean? val) ; if the value is a boolean, prettify it with parse-bool
             (parse-bool val)
             val))))

; evaluate one of two statements based on a condition
(define if-statement
  (lambda (expr state)
    (let ([condition-result (condition (operand1 expr) state)])
      (if condition-result
          (statement (operand2 expr) state) ; then branch
          (if (= (length expr) 4)
              (statement (operand3 expr) state) ; else branch
              state))))) 

; while a condition is true, iterate through a code block
(define while
  (lambda (expr state)
    (if (condition (operand1 expr) state) ; check the condition
        (let ([new-state (statement-list (list (operand2 expr)) state)]) ; run body of the statement
         (while expr new-state)) ; recursively iterate through the body again
        state))) ; otherwise return the state


; evaluate a statement
(define expression
    (lambda (expr state) ; evaluate the expression as a condition and an int value
        (let ([int-binding (int-value expr state)]
            [bool-binding (condition expr state)])
            (if (eq? int-binding type-err) ; return the binding that is valid
                (if (eq? bool-binding type-err)
                    parse-err
                    (return-val bool-binding))
                (return-val int-binding)))))

; evaluate an arithmetic expression
(define int-value
  (lambda (expr state)
    (cond 
      ((number? expr) expr) ; return a number
      ((symbol? expr) (m-int expr state)) ; return a variable representing a number
      ((list? expr) ; evaluate an operation
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
  
; evaluate a boolean condition
(define condition
  (lambda (expr state)
    (cond
      ((boolean? expr) (parse-bool expr)) ; return a boolean
      ((symbol? expr) (m-bool expr state)) ; return a variable representing a boolean
      ((list? expr)
       (let ([op (operator expr)]) ; evaluate a condition
             (cond
               ((eq? op '!) (not (condition (operand1 expr) state)))
               ((eq? op '&&)  (and (condition (operand1 expr) state) (condition (operand2 expr) state)))
               ((eq? op '||)  (or (condition (operand1 expr) state) (condition (operand2 expr) state)))
               ((eq? op '==)  (eq? (expression (operand1 expr) state) (expression (operand2 expr) state)))
               ((eq? op '!=)  (not (eq? (expression (operand1 expr) state) (expression (operand2 expr) state))))
               ((eq? op '<) (< (int-value (operand1 expr) state) (int-value (operand2 expr) state)))
               ((eq? op '>) (> (int-value (operand1 expr) state) (int-value (operand2 expr) state)))
               ((eq? op '>=) (>= (int-value (operand1 expr) state) (int-value (operand2 expr) state)))
               ((eq? op '<=) (<= (int-value (operand1 expr) state) (int-value (operand2 expr) state)))
               (else type-err))))
      (else type-err))))

;;;; ---------------------------------------------------------
;;;; MAPPINGS
;;;; ---------------------------------------------------------

; evaluates the integer value of a mapping
(define m-int
    (lambda (atom state)
        (if (number? atom) 
            atom ; return a literal number
            (let ([val (value-of-binding (lookup-binding atom state))]) 
                  (if (number? val) ; check if this var is mapped to an int
                      val 
                      type-err)))))   

; evaluates the boolean value of a mapping
(define m-bool
    (lambda (atom state)
        (cond
          ((boolean? atom) atom)
          ((eq? 'false atom) #f)
          ((eq? 'true atom) #t) ; return a literal boolean
          (else (let ([val (value-of-binding (lookup-binding atom state))])
                 (if (boolean? val) ; check if this var is mapped to a boolean
                     val
                     type-err))))))   

; check if this symbol is mapped to a value
(define m-name
    (lambda (atom state)
        (let ([n (lookup-binding atom state)])
              (if (or (eq? n type-err) (eq? n missing-err) (eq? n unbound-err)) ; check if it returns an error
                  n
                  atom))))

;;;; ---------------------------------------------------------
;;;; BINDING OPERATIONS
;;;; ---------------------------------------------------------

;; add a binding to the state in newest -> oldest order
(define add-binding 
    (lambda (name value state)
        (return-state (cons name (get-state-names state))
                      (cons value (get-state-values state)))))

; find the value of a binding by name
(define lookup-binding
    (lambda (name state)
        (let* ([index (return-pos-of-item name (get-state-names state) first-index)]
               [value (return-item-at-pos index (get-state-values state))])
               (if (eq? missing-err index)
                 missing-err
                (cons value index)))))

; delete a binding
(define remove-binding
    (lambda (name state)
        (let* ([binding (lookup-binding name state)]
               [index (index-of-binding binding)])
             (return-state (remove-item-at-pos index (get-state-names state))
                           (remove-item-at-pos index (get-state-values state))))))

;;;; ---------------------------------------------------------
;;;; LIST MANIPULATION HELPERS
;;;; ---------------------------------------------------------

; return the index of an item in a list
(define return-pos-of-item
    (lambda (item lis acc)
        (cond
            ((null? item) type-err)
            ((null? lis) missing-err)
            ((eq? item (car lis)) acc)
            (else (return-pos-of-item item (cdr lis) (+ acc 1))))))

; return the item at a given index in a list
(define return-item-at-pos
    (lambda (pos lis)
        (cond
            ((not (number? pos)) type-err)
            ((null? lis) unbound-err)
            ((zero? pos) (car lis))
            (else (return-item-at-pos (- pos 1) (cdr lis))))))

; remove the item at a given index in a list (return the list)
(define remove-item-at-pos
  (lambda (pos lis)
    (cond
      ((not (number? pos)) type-err)
      ((null? lis) unbound-err)
      ((zero? pos) (cdr lis))
      (else
        (cons (car lis)
              (remove-item-at-pos (- pos 1) (cdr lis)))))))
