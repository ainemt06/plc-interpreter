#lang racket
;(require "functionParser.rkt")


;;;; =======================================================================
;;;; Aine Thomas (amt267) Daniel Borhegyi (dmb236)
;;;; =======================================================================

;;;; ---------------------------------------------------------
;;;; INTERPRET
;;;; ---------------------------------------------------------

; Parse a file, then interpret it with the initial state
(define interpret
  (lambda (filename)
    (global-statement-list filename initial-state 
    (lambda (v) v) (lambda (v s) v) (lambda (v) v) (lambda (v) v) (lambda (v s) v))))

;;;; ---------------------------------------------------------
;;;; CONSTANTS/ERRORS/SIMPLE ABSTRACTIONS
;;;; ---------------------------------------------------------

; Shortcuts for managing lists
(define first-index 0)
(define value-of-binding car)
(define index-of-binding cdr)
(define operator car)
(define operand1 cadr)
(define operand2 caddr)
(define operand3 cadddr)
(define block cdr)
(define actualparams cdr)

; State/stack manipulation functions
(define initial-state (list '() '()))
(define get-state-names (lambda (state) (car state)))
(define get-state-values (lambda (state) (cadr state)))
(define add-state-layer (lambda (state) (return-state (cons '() (get-state-names state)) (cons '() (get-state-values state)))))
(define add-custom-state-layer
  (lambda (layer state)
    (return-state (append (get-state-names layer) (get-state-names state))
                  (append (get-state-values layer) (get-state-values state)))))
(define remove-state-layer (lambda (state) (return-state (cdr (get-state-names  state)) (cdr (get-state-values state)))))
(define return-state (lambda (names vals) (list names vals)))
(define return-val (lambda (v) v))

; Types of errors
(define (type-err) (error 'type "Parameter type mismatch"))
(define (missing-err) (error 'missing "Var not found in state"))
(define (unbound-err) (error 'unbound "List position out of bounds"))
(define (redefine-err) (error) 'redefine "Attempted to redefine a variable")
(define (parse-err) (error 'parse "Parsing error"))
(define (loop-err) (error 'loop "Break or continue used outside of loop"))
(define (global-err) (error 'global "Invalid operation at the global layer"))

; Turn #t & #f into 'true and 'false
(define parse-bool
  (lambda (bool)
    (if bool
        'true
        'false)))

;;;; ---------------------------------------------------------
;;;; DENOTATIONAL SEMANTICS/M_STATE FUNCTIONS
;;;; ---------------------------------------------------------

; Evaluates the global statements in the program
(define global-statement-list
  (lambda (lis state next return break continue throw)
    (if (null? lis)
        (let* ([closure    (value-of-binding (lookup-binding 'main state))]
               [new-state  (get-environment closure state)]
               [bound-state (bind-parameters (get-params closure) '() new-state state next return break continue throw)])
          (statement-list (get-body closure) bound-state
                          (lambda (s) (next s))         
                          (lambda (v s) (return v s))   
                          (lambda (s) (loop-err))
                          (lambda (s) (loop-err))
                          throw))
           (global-statement (operator lis) state
        (lambda (new-state) (global-statement-list (cdr lis) new-state next return break continue throw))
          return break continue throw))))

; Parsing global statements
(define global-statement
  (lambda (expr state next return break continue throw)
    (let ([op (operator expr)])
         (cond
          ((eq? op 'var) (declare expr state next return break continue throw))
          ((eq? op 'function) (function expr state next return break continue throw))
          (else global-err)))))

; Execute a block of code when a bracket is encountered
(define block-of-code
  (lambda (block state next return break continue throw)
    (statement-list block (add-state-layer state) ; add a new layer to the state for this block
                    (lambda (s) (next (remove-state-layer s)))  ; strip the layer before continuing
                    return 
                    (lambda (s) (break (remove-state-layer s))) 
                    (lambda (s) (continue (remove-state-layer s))) 
                    (lambda (e s) (throw e (remove-state-layer s))))))

; recurse through a list of statements and update the state with each one
(define statement-list
  (lambda (lis state next return break continue throw)
    (if (null? lis) 
        (next state) ; return the final state
        (statement (operator lis) state 
                   (lambda (new-state) (statement-list (cdr lis) new-state next return break continue throw)) ; continue through the statements
                   return break continue throw))))

; Parse out the type of a statement and evaluate it (basically our M_state)
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
        ((eq? op 'function) (function expr state next return break continue throw))
        ((eq? op 'funcall) (funcall (cdr expr) state (lambda (s) (next s)) (lambda (v s) (next s)) break continue throw))
        ((eq? op 'break) (break state))
        ((eq? op 'continue) (continue state))
        (else type-err)))))

; Try block, depends on newnext, newreturn, newbreak
(define try
  (lambda (expr state next return break continue throw)
    (let* ([tryblock   (operand1 expr)] ; let for more readability
           [catchblock (operand2 expr)]
           [catchbody (if (null? catchblock) catchblock (operand2 catchblock))] ; default catch if not provided, otherwise use provided
           [exceptvar  (if (null? catchblock) catchblock (car (operand1 catchblock)))]
           [finallyblock (operand3 expr)]
           [finallybody (if (null? finallyblock) finallyblock (operand1 finallyblock))] ; default finally if not provided, otherwise use provided
           [newnext ; redefine next to move on
            (lambda (s)
              (block-of-code finallybody s next return break continue throw))]
           [newreturn ; redefine return to return a value and continue on
            (lambda (v s)
              (block-of-code finallybody s (lambda (s2) (return v s2)) return break continue throw))]
           [newbreak ; redefine break to break out early
            (lambda (s)
              (block-of-code finallybody s break return break continue throw))]
           [newcontinue ; redefine continue to start the next block of code
            (lambda (s)
              (block-of-code finallybody s continue return break continue throw))]
           [newthrow ; redefine throw to end the program with a final block of code
            (lambda (e s)
              (block-of-code catchbody
                             (add-binding exceptvar e s)
                             (lambda (s2) (block-of-code finallybody s2 next return break continue throw))
                             (lambda (v s2) (block-of-code finallybody s2 (lambda (s3) (return v s3)) return break continue throw))
                             (lambda (s2) (block-of-code finallybody s2 break return break continue throw))
                             (lambda (s2) (block-of-code finallybody s2 continue return break continue throw))
                             (lambda (e2 s2) (block-of-code finallybody s2 (lambda (s3) (throw e2 s3)) return break continue throw))))])
      (block-of-code tryblock state newnext newreturn newbreak newcontinue newthrow))))

; Throw an expression
(define throw-excep
  (lambda (expr state next return break continue throw)
    (throw (evaluation (operand1 expr) state next return break continue throw) state)))

; Declare and optionally initialize a variable
(define declare
  (lambda (expr state next return break continue throw) 
    (if (= (length expr) 2)
        (next (add-binding (operand1 expr) '* state)) ; unassigned variables default to the empty list
        (next (add-binding (operand1 expr) (evaluation (operand2 expr) state next return break continue throw) state)))))

; Set a variable to a value
(define assign
  (lambda (expr state next return break continue throw)
    (next (update-binding (operand1 expr) (evaluation (operand2 expr) state next return break continue throw) state))))

; Return/print the value of this statement
(define return-statement
  (lambda (expr state next return break continue throw)
    (let ([val (evaluation (operand1 expr) state next return break continue throw)])
      (if (boolean? val) ; if the value is a boolean, prettify it with parse-bool
          (return (parse-bool val) state)
          (return val state)))))

; Evaluate one of two statements based on a condition
(define if-statement
  (lambda (expr state next return break continue throw)
    (let ([condition-result (condition (operand1 expr) state next return break continue throw)])
      (if condition-result
          (statement (operand2 expr) state next return break continue throw) ; then
          (if (= (length expr) 4)
              (statement (operand3 expr) state next return break continue throw) ; else
              (next state)))))) ; no else branch

; While a condition is true, iterate through a code block
(define while
  (lambda (expr state next return break continue throw)
    (letrec
        ([loop (lambda (state)
           (if (evaluation (operand1 expr) state next return break continue throw)
               (statement (operand2 expr) state
                          (lambda (s) (loop s))
                          return
                          (lambda (s) (next s))
                          (lambda (s) (loop s))
                          throw)
              (next state)))])
         (loop state))))

; Getting parameters of a funciton
  (define get-params
    (lambda (closure)
    (cadr closure)))   ; was car — skipped over 'closure tag

; Getting the body of a function
(define get-body
  (lambda (closure)
    (caddr closure)))  ; was cadr — same issue

; Getting the enviornment of a function
(define get-environment
  (lambda (closure state)
    (let ([numlayers (caddr closure)])
    ((return-state (return-end-of-list numlayers (get-state-names state)) 
                   (return-end-of-list numlayers (get-state-values state)))))))

; Steps to call a function, establish functional next, return, break, continue, throw
; run the function with these

; we don't want to store that old state - grab the current values or just the state layers in common

; strip off everything in scope
; then restore and find out what has changed
(define funcall
  (lambda (expr state next return break continue throw)
    (let* ([name        (operator expr)]
           [params      (actualparams expr)]
           [closure     (value-of-binding (lookup-binding name state))]  ; extract value from (val . idx)
           [new-state (get-environment closure state)]
           [bound-state (bind-parameters (get-params closure) params new-state state next return break continue throw)]
           [functionnext     (lambda (s) (next (restore-state new-state s)))]
           [functionreturn   (lambda (v s) (return v (restore-state new-state s)))]
           [functionbreak    (lambda (s) (loop-err))]
           [functioncontinue (lambda (s) (loop-err))]
           [functionthrow    (lambda (e s) (throw e (restore-state new-state s)))])
      (statement-list (get-body closure) (add-state-layer bound-state) functionnext functionreturn
                      functionbreak functioncontinue functionthrow))))

; Restore state - not able to get this to restore properly, but we acknowledge this should be used
; ended up using remove-state-layer for a similar effect that worked on most tests

; keep track of the number of layers we add/strip
(define restore-state
  (lambda (activestate functionstate)
    (let* ([newvalues (get-state-values functionstate)]
           [funclayers (length newvalues)]
           [totallayers (length (get-state-names activestate))])
           (return-state (get-state-names activestate) 
           (append (take (get-state-values activestate) (- totallayers funclayers)) newvalues)))))


; Bind parameters wrapper
(define bind-parameters
  (lambda (formalparams actualparams new-state state next return break continue throw)
    (bind-parameters-cps formalparams actualparams new-state state next return break continue throw)))

; Puts actual parameters into formal parameters
(define bind-parameters-cps
  (lambda (formalparams actualparams new-state state next return break continue throw)
    (if (null? formalparams)
      new-state
      (bind-parameters-cps (cdr formalparams) (cdr actualparams) 
                       (add-binding (car formalparams) 
                                    (evaluation (car actualparams) state next return break continue throw) new-state) state next return break continue throw))))
       
; Define a function
(define function
  (lambda (expr state next return break continue throw)
    (let ([name (operand1 expr)]
          [formal-params (operand2 expr)]
          [body (operand3 expr)]) 
          (next (add-binding name (make-closure formal-params body name state) state)))))

; Make a closure
; A function has a closure that consists of:
;   (param-list body (state with function added))
;   (state with function added) = (param-list body *)
;   * indicates that this is inside iteself so you should maintain the state and call the body
;   and params of the function again, this is our recusion solution
(define make-closure
  (lambda (param-list body name state)
    (list 'closure param-list body (length (get-state-names state)))))

; Finds if a expression is a function or expression and acts accordingly
(define evaluation
  (lambda (expr state next return break continue throw)
    (if (and (list? expr) (eq? (car expr) 'funcall))
        (funcall (cdr expr) state next (lambda (v s) v) break continue throw)
        (expression expr state next return break continue throw))))

; Evaluate a statement
(define expression
  (lambda (expr state next return break continue throw) ; evaluate the expression as a condition and an int value
    (let ([int-binding (int-value expr state next return break continue throw)]
          [bool-binding (condition expr state next return break continue throw)])
      (if (eq? int-binding type-err) ; return the binding that is valid
          (if (eq? bool-binding type-err)
              parse-err
              (return-val bool-binding))
          (return-val int-binding)))))

; Evaluate an arithmetic expression
(define int-value
  (lambda (expr state next return break continue throw)
    (cond 
      ((number? expr) expr) ; return a number
      ((symbol? expr) (m-int expr state)) ; return a variable representing a number
      ((list? expr) ; evaluate an operation
       (let ((op (operator expr)))
         (cond
           ((eq? op '+)
            (+ (evaluation (operand1 expr) state next return break continue throw)
               (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '-)
            (if (= (length expr) 2)
                (- (evaluation (operand1 expr) state next return break continue throw)) 
                (- (evaluation (operand1 expr) state next return break continue throw)
                   (evaluation (operand2 expr) state next return break continue throw)))) 
           ((eq? op '*)
            (* (evaluation (operand1 expr) state next return break continue throw)
               (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '/)
            (quotient (evaluation (operand1 expr) state next return break continue throw)
                      (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '%)
            (remainder (evaluation (operand1 expr) state next return break continue throw)
                       (evaluation (operand2 expr) state next return break continue throw)))
           (else type-err))))
      (else type-err))))
  
; Evaluate a boolean condition
(define condition
  (lambda (expr state next return break continue throw)
    (cond
      ((boolean? expr) (parse-bool expr)) ; return a boolean
      ((symbol? expr) (m-bool expr state)) ; return a variable representing a boolean
      ((list? expr)
       (let ([op (operator expr)]) ; evaluate a condition
         (cond
           ((eq? op '!) (not (evaluation (operand1 expr) state next return break continue throw)))
           ((eq? op '&&)  (and (evaluation (operand1 expr) state next return break continue throw) (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '||)  (or (evaluation (operand1 expr) state next return break continue throw) (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '==)  (eq? (evaluation (operand1 expr) state next return break continue throw) (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '!=)  (not (eq? (evaluation (operand1 expr) state next return break continue throw) (evaluation (operand2 expr) state next return break continue throw))))
           ((eq? op '<) (< (evaluation (operand1 expr) state next return break continue throw) (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '>) (> (evaluation (operand1 expr) state next return break continue throw) (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '>=) (>= (evaluation (operand1 expr) state next return break continue throw) (evaluation (operand2 expr) state next return break continue throw)))
           ((eq? op '<=) (<= (evaluation (operand1 expr) state next return break continue throw) (evaluation (operand2 expr) state next return break continue throw)))
           (else type-err))))
      (else type-err))))

;;;; ---------------------------------------------------------
;;;; MAPPINGS
;;;; ---------------------------------------------------------

; Evaluates the integer value of a mapping
(define m-int
  (lambda (atom state)
    (if (number? atom) 
        atom ; return a literal number
        (let ([val (value-of-binding (lookup-binding atom state))]) 
          (if (number? val) ; check if this var is mapped to an int
              val 
              type-err)))))   

; Evaluates the boolean value of a mapping
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

; Check if this symbol is mapped to a value
(define m-name
  (lambda (atom state)
    (let ([n (lookup-binding atom state)])
      (if (or (eq? n type-err) (eq? n missing-err) (eq? n unbound-err)) ; check if it returns an error
          n
          atom))))

;;;; ---------------------------------------------------------
;;;; BINDING OPERATIONS
;;;; ---------------------------------------------------------

;; Add a binding to a layer of the state
(define add-binding
  (lambda (name value state)
    (if (null? (get-state-names state))
        ;; No layers exist yet — create the first one
        (return-state (list (list name))
                      (list (list value)))
        ;; Layers exist — cons into the top layer as before
        (let* ([names (cons (cons name  (car (get-state-names  state)))
                            (cdr (get-state-names  state)))]
               [vals  (cons (cons value (car (get-state-values state)))
                            (cdr (get-state-values state)))])
          (return-state names vals)))))

; Find the value of a binding by name
(define lookup-binding
  (lambda (name state)
    (let* ([index (return-pos-of-item name (get-state-names state))]
           [value (return-item-at-pos index (get-state-values state))])
      (if (eq? missing-err index)
          (cons missing-err '*)
          (cons value index)))))

; Return the name and value of the binding at the first element
(define peek-binding
  (lambda (state)
    (let ([name (return-item-at-pos first-index (get-state-names state))]
          [value (return-item-at-pos first-index (get-state-values state))])
          (cons name value))))

; Remove the first element of the state
(define pop-binding
  (lambda (state)
    (return-state (remove-item-at-pos first-index (get-state-names state))
                    (remove-item-at-pos first-index (get-state-values state)))))

; Update a binding by replace function
(define update-binding
  (lambda (name newval state)
    (let ([index (return-pos-of-item name (get-state-names state))])
      (return-state (get-state-names state)
                    (replace-item-at-pos index newval (get-state-values state))))))

; Delete a binding
(define remove-binding
  (lambda (name state)
    (let* ([binding (lookup-binding name state)]
           [index (index-of-binding binding)])
      (return-state (remove-item-at-pos index (get-state-names state))
                    (remove-item-at-pos index (get-state-values state))))))

;;;; ---------------------------------------------------------
;;;; LIST MANIPULATION HELPERS
;;;; ---------------------------------------------------------

; Helper wrapper for empty lists
(define empty-lis?
(lambda (lis)
(empty-cps lis (lambda (v) v))))

; Recurse through a list to see if empty
(define empty-cps 
  (lambda (lis return)
    (cond
      ((null? lis) (return #t))
      ((pair? (car lis)) (return #f))
      ((null? (car lis)) (empty-cps (cdr lis) return))
      (else (return #f)))))

; Helper: total number of atoms across all nested sublists
(define flat-length
  (lambda (lis)
    (cond
      ((null? lis) 0)
      ((closure? (car lis)) (+ 1 (flat-length (cdr lis))))  ; closure = one item
      ((list? (car lis)) (+ (flat-length (car lis)) (flat-length (cdr lis))))
      (else (+ 1 (flat-length (cdr lis)))))))

; Recognizes a closure by its 4-element structure: (name (params) (body) (env))
(define closure?
  (lambda (x)
    (and (list? x)
         (= (length x) 4)
         (eq? 'closure (car x)))))

; Predicate: is this list a scope-level sublist (not a closure value)?
(define scope-list?
  (lambda (x)
    (and (list? x) (not (closure? x)))))

; Return position of an item in a list
(define return-pos-of-item-cps
  (lambda (item lis return)
    (cond
      ((null? item) type-err)
      ((null? lis)  missing-err)
      ((scope-list? (car lis))                          ; only recurse into scope sublists
       (let ([inner (return-pos-of-item-cps item (car lis) (lambda (v) v))])
         (if (eq? missing-err inner)
             (return-pos-of-item-cps item (cdr lis)
                                     (lambda (v) (return (+ (flat-length (car lis)) v))))
             (return inner))))
      ((equal? item (car lis)) (return 0))              ; use equal? so closures can match
      (else
       (return-pos-of-item-cps item (cdr lis)
                               (lambda (v) (return (+ 1 v))))))))

; Wrapper for position of item
(define return-pos-of-item
  (lambda (item lis)
    (return-pos-of-item-cps item lis (lambda (v) v))))

; Returns an item at a position
(define return-item-at-pos-cps
  (lambda (pos lis return)
    (cond
      ((not (number? pos)) type-err)
      ((null? lis) (return #f pos))
      ((scope-list? (car lis))
       (let ([sublen (flat-length (car lis))])
         (if (< pos sublen)
             (return-item-at-pos-cps pos (car lis) return)
             (return-item-at-pos-cps (- pos sublen) (cdr lis) return))))
      ((zero? pos) (return (car lis) 0))
      (else
       (return-item-at-pos-cps (- pos 1) (cdr lis) return))))) ; just pass return

; Wrapper for an item at a position
(define return-item-at-pos
  (lambda (pos lis)
    (return-item-at-pos-cps pos lis (lambda (v pos) v))))

; Remove item at a position
(define remove-item-at-pos-cps
  (lambda (pos lis return)
    (cond
      ((not (number? pos)) type-err)
      ((null? lis) (return '() pos))
      ((scope-list? (car lis))
       (let ([sublen (flat-length (car lis))])
         (if (< pos sublen)
             (remove-item-at-pos-cps pos (car lis)
                                     (lambda (v1 pos1)
                                       (return (cons v1 (cdr lis)) pos1)))
             (remove-item-at-pos-cps (- pos sublen) (cdr lis)
                                     (lambda (v2 pos2)
                                       (return (cons (car lis) v2) pos2))))))
      ((zero? pos) (return (cdr lis) 0))
      (else
       (remove-item-at-pos-cps (- pos 1) (cdr lis)
                               (lambda (v pos)
                                 (return (cons (car lis) v) pos)))))))

; Wrapper to remove item at a position
(define remove-item-at-pos
  (lambda (pos lis)
    (remove-item-at-pos-cps pos lis (lambda (state pos) state))))

; Replacing item at a position
(define replace-item-at-pos-cps
  (lambda (pos item lis return)
    (cond
      ((not (number? pos)) type-err)
      ((null? lis) (return '() pos))
      ((scope-list? (car lis))
       (let ([sublen (flat-length (car lis))])
         (if (< pos sublen)
             (replace-item-at-pos-cps pos item (car lis)
                                      (lambda (v1 pos1)
                                        (return (cons v1 (cdr lis)) pos1)))
             (replace-item-at-pos-cps (- pos sublen) item (cdr lis)
                                      (lambda (v2 pos2)
                                        (return (cons (car lis) v2) pos2))))))
      ((zero? pos) (return (cons item (cdr lis)) 0))
      (else
       (replace-item-at-pos-cps (- pos 1) item (cdr lis)
                                (lambda (v pos)
                                  (return (cons (car lis) v) pos)))))))

; Wrapper to replace an item at a position
(define replace-item-at-pos
  (lambda (pos item lis)
    (replace-item-at-pos-cps pos item lis (lambda (state pos) state))))

; helper to return n layers of the state
(define return-end-of-list
  (lambda (n lis)
      (list-tail lst (max 0 (- (length lst) n)))))