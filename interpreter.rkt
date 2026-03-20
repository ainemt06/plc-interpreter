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
    (statement-list (parser filename) initial-state (lambda (value state) value))))

;;;; ---------------------------------------------------------
;;;; CONSTANTS/ERRORS/SIMPLE ABSTRACTIONS
;;;; ---------------------------------------------------------

(define first-index 0)
(define value-of-binding car)
(define index-of-binding cdr)
(define operator car)
(define operand1 cadr)
(define block cdr)
(define operand2 caddr)
(define operand3 cadddr)

(define initial-state (list (cons '() '())))
(define acc 0)
(define get-state-names (lambda (state) (car state)))
(define get-state-values (lambda (state) (cdr state)))
(define add-state-layer (lambda (state) (cons '() state)))
(define remove-state-layer (lambda (state) (cdr state)))
(define return-state (lambda (names vals) (cons names vals)))
(define return-val (lambda (v) v))

(define (type-err) (error 'type "Parameter type mismatch"))
(define (missing-err) (error 'missing "Var not found in state"))
(define (unbound-err) (error 'unbound "List position out of bounds"))
(define (redefine-err) (error) 'redefine "Attempted to redefine a variable")
(define (parse-err) (error 'parse "Parsing error"))
(define (loop-err) (error 'loop "Break or continue used outside of loop"))

; turn #t & #f into 'true and 'false
(define parse-bool
  (lambda (bool)
    (if bool
      'true
      'false)))

;;;; ---------------------------------------------------------
;;;; DENOTATIONAL SEMANTICS/M_STATE FUNCTIONS
;;;; ---------------------------------------------------------

; set up return through block and try and whatever

; brackets
(define block-of-code
  (lambda (block state next return break continue throw)
    (statement-list block (add-state-layer state) next return break continue throw)))


; recurse through a list of statements and update the state with each one
(define statement-list
    (lambda (lis state next return break continue throw)
        (if (null? lis) 
            (return state) ; return the final state
            (statement (operator lis) state (lambda (new-state) (statement-list (cdr lis) new-state)) return break continue throw))))

; parse out the type of a statement and evaluate it (basically our M_state)
(define statement
    (lambda (expr state next return break continue throw)
    (let ([op (operator expr)])
        (cond
            ((eq? op 'if) (if-statement expr state next return break continue throw))
            ((eq? op 'while) (while expr state next return break continue throw))
            ((eq? op 'var) (declare expr state next return break continue throw))
            ((eq? op '=) (assign expr state next return break continue throw))
            ((eq? op 'return) (return-statement expr state next return break continue throw))
            ((eq? op 'begin) (block-of-code (block expr) state next return break continue throw))
            ((eq? op 'try) (try expr state next return break continue throw))
            ((eq? op 'throw) (throw-excep expr state next return break continue throw))
            (else type-err)))))

(define try
  (lambda (expr state next return break continue throw)
    (let* ([tryblock (operand1 expr)]
          [catchblock (operand2 expr)]
          [exceptvar (car (operand1 catchblock))]
          [finallyblock (operand3 expr)]) 
          ((next (block-of-code tryblock state newnext newreturn newbreak continue newthrow))))))

(define newnext
  (lambda (finallyblock s next return break continue throw)
    (block-of-code finallyblock s next return break continue throw)))

(define newreturn
  (lambda (finallyblock v s next return break continue throw)
    (block-of-code finallyblock s next (lambda s2 (return v s2)) break continue throw)))

(define newbreak
  (lambda (finallyblock s next return break continue throw)
    (block-of-code finallyblock s break return break continue throw)))

(define newthrow
  (lambda (catchblock exceptvar finallyblock e s next return break continue throw)
    (block-of-code catchblock 
           (add-binding exceptvar e s)
           (lambda (s2) (block-of-code finallyblock s2 next return break continue throw))
           (lambda (v s2) (block-of-code finallyblock s2 next (lambda (s3) (return v s3)) break continue throw))
           (lambda (s2) (block-of-code finallyblock s2 break return break continue throw))
           continue 
           (lambda (e2 s2) (block-of-code finallyblock s2 next (lambda (s3) (throw e2 s3)) break continue throw)))))

(define catchthrow
  (lambda (finallyblock v s next return break continue throw)
    (block-of-code finallyblock s next (lambda (s2) (return v s2)) break continue throw)))

; throw an expression
(define throw-excep
  (lambda (expr state next return break continue throw)
    (throw (expression (operand1 expr) state) state)))

; declare and optionally initialize a variable
(define declare
    (lambda (expr state next) 
        (if (not (eq? (lookup-binding (operand1 expr) state) missing-err)) ;prevent variables from being redeclared
            redefine-err
            (if (= (length expr) 2)
              (next (add-binding (operand1 expr) '() state)) ; unassigned variables default to the empty list
              (next (add-binding (operand1 expr) (expression (operand2 expr) state) state))))))

;; set a variable to a value
(define assign
  (lambda (expr state next)
    (next (update-binding (operand1 expr) (expression (operand2 expr) state) state))))

; return/print the value of this statement
(define return-statement
    (lambda (expr state next return)
       (let ([val (expression (operand1 expr) state)])
         (if (boolean? val) ; if the value is a boolean, prettify it with parse-bool
             (return (parse-bool val))
             (return val)))))

; evaluate one of two statements based on a condition
(define if-statement
  (lambda (expr state next)
    (let ([condition-result (condition (operand1 expr) state)])
      (if condition-result
          (next (statement (operand2 expr) state)) ; then branch
          (if (= (length expr) 4)
              (next (statement (operand3 expr) state)) ; else branch
              (next state)))))) 

; while a condition is true, iterate through a code block
(define while
  (lambda (expr state next)
    (if (condition (operand1 expr) state) ; check the condition
        (let ([new-state (statement-list (list (operand2 expr)) state)]) ; run body of the statement
         (while expr new-state)) ; recursively iterate through the body again
        (next state)))) ; otherwise return the state


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

;; add a binding to a layer of the state
(define add-binding
  (lambda (name value state)
    (let* ([names (cons (cons name (car (get-state-names state))) (cdr (get-state-names state)))]
           [vals (cons (cons value (car (get-state-values state))) (cdr (get-state-names state)))])
           (return-state names vals))))

; find the value of a binding by name
(define lookup-binding
    (lambda (name state)
        (let* ([index (return-pos-of-item name (get-state-names state))]
               [value (return-item-at-pos index (get-state-values state))])
               (if (eq? missing-err index)
                 missing-err
                (cons value index)))))

(define update-binding
  (lambda (name newval state)
    (let ([index (return-pos-of-item name (get-state-names state))])
         (replace-item-at-pos index newval (get-state-values state)))))

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

(define return-pos-of-item-cps
  (lambda (item lis return)
    (cond
      ((null? item) type-err)
      ((null? lis) missing-err)
      ((eq? item (car lis)) (return 0))
      ((list? (car lis)) (return-pos-of-item-cps item (car lis) 
                           (lambda (v1) (return-pos-of-item-cps item (cdr lis) 
                           (lambda (v2) (return (+ v1 v2)))))))
      (else (return-pos-of-item-cps item (cdr lis) (lambda (v) (return (+ v 1))))))))

(define return-pos-of-item
  (lambda (item lis)
    (return-pos-of-item-cps item lis (lambda (v) v))))

(define return-item-at-pos-cps
  (lambda (pos lis return)
    (cond
      ((not (number? pos)) type-err)
      ((null? lis) (return #f pos))
      ((zero? pos) (return (car lis) 0)) 
      ((list? (car lis))
       (return-item-at-pos-cps pos (car lis)
         (lambda (v1 pos1)
           (if (zero? pos1)
               (return v1 0)      
               (return-item-at-pos-cps pos1 (cdr lis) return)))))
      (else
       (return-item-at-pos-cps (- pos 1) (cdr lis) return)))))

(define return-item-at-pos
  (lambda (pos lis)
    (return-item-at-pos-cps pos lis (lambda (v pos) v))))

(define remove-item-at-pos-cps
  (lambda (pos lis return)
    (cond
      ((not (number? pos)) type-err)
      ((null? lis) (return '() pos))          
      ((zero? pos) (return (cdr lis) 0))     
      ((list? (car lis))
       (remove-item-at-pos-cps pos (car lis)
         (lambda (v1 pos1)
           (if (zero? pos1)
               (return (cons v1 (cdr lis)) 0)       
               (remove-item-at-pos-cps pos1 (cdr lis)   
                 (lambda (v2 pos2)
                   (return (cons (car lis) v2) pos2)))))))
      (else
       (remove-item-at-pos-cps (- pos 1) (cdr lis)
         (lambda (v pos)
           (return (cons (car lis) v) pos)))))))   

(define remove-item-at-pos
  (lambda (pos lis)
    (remove-item-at-pos-cps pos lis (lambda (state pos) state))))

(define replace-item-at-pos-cps
  (lambda (pos item lis return)
    (cond
      ((not (number? pos)) type-err)
      ((null? lis) (return '() pos))          
      ((zero? pos) (return (cons item (cdr lis)) 0))     
      ((list? (car lis))
       (replace-item-at-pos-cps pos item (car lis)
         (lambda (v1 pos1)
           (if (zero? pos1)
               (return (cons v1 (cdr lis)) 0)       
               (replace-item-at-pos-cps pos1 item (cdr lis)   
                 (lambda (v2 pos2)
                   (return (cons (car lis) v2) pos2)))))))
      (else
       (replace-item-at-pos-cps (- pos 1) item (cdr lis)
         (lambda (v pos)
           (return (cons (car lis) v) pos)))))))   

(define replace-item-at-pos
  (lambda (pos item lis)
    (remove-item-at-pos-cps pos item lis (lambda (state pos) state))))
