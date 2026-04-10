#lang racket
(require "functionParser.rkt")


;;;; =======================================================================
;;;; Aine Thomas (amt267) Daniel Borhegyi (dmb236)
;;;; =======================================================================

;;;; ---------------------------------------------------------
;;;; INTERPRET
;;;; ---------------------------------------------------------

; parse a file, then interpret it with the initial state
(define interpret
  (lambda (filename)
    (global-statement-list (parser filename) initial-state 
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
(define actualparams cddr)

; State/stack manipulation functions
(define initial-state (list '() '()))
(define get-state-names (lambda (state) (car state)))
(define get-state-values (lambda (state) (cadr state)))
(define add-state-layer (lambda (state) (return-state (cons '() (get-state-names state)) (cons '() (get-state-values state)))))
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

; turn #t & #f into 'true and 'false
(define parse-bool
  (lambda (bool)
    (if bool
        'true
        'false)))

;;;; ---------------------------------------------------------
;;;; DENOTATIONAL SEMANTICS/M_STATE FUNCTIONS
;;;; ---------------------------------------------------------

(define global-statement-list
  (lambda (lis state next return break continue throw)
    (if (null? lis)
      (funcall 'main state next (lambda (v s) v) break continue throw) ; c=eck on this when funcall is set up
      (global-statement (operator lis) state
        (lambda (new-state) (global-statement-list (cdr lis) new-state next return break continue throw)
          return break continue throw)))))

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
                    throw)))

; recurse through a list of statements and update the state with each one
(define statement-list
  (lambda (lis state next return break continue throw)
    (if (null? lis) 
        (next state) ; return the final state
        (statement (operator lis) state 
                   (lambda (new-state) (statement-list (cdr lis) new-state next return break continue throw)) ; continue through the statements
                   return break continue throw))))

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
        ((eq? op 'function) (function expr state next return break continue throw))
        ((eq? op 'funcall) (funcall expr state next return break continue throw))
        ((eq? op 'break) (break state))
        ((eq? op 'continue) (continue state))
        (else type-err)))))

; try block, depends on newnext, newreturn, newbreak
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

; throw an expression
(define throw-excep
  (lambda (expr state next return break continue throw)
    (throw (expression (operand1 expr) state) state return)))

; declare and optionally initialize a variable
(define declare
  (lambda (expr state next return break continue throw) 
    (if (= (length expr) 2)
        (next (add-binding (operand1 expr) '* state)) ; unassigned variables default to the empty list
        (next (add-binding (operand1 expr) (expression (operand2 expr) state return) state)))))

;; set a variable to a value
(define assign
  (lambda (expr state next return break continue throw)
    (next (update-binding (operand1 expr) (expression (operand2 expr) state return) state))))

; return/print the value of this statement
(define return-statement
  (lambda (expr state next return break continue throw)
    (let ([val (expression (operand1 expr) state return)])
      (if (boolean? val) ; if the value is a boolean, prettify it with parse-bool
          (return (parse-bool val))
          (return val state)))))

; evaluate one of two statements based on a condition
(define if-statement
  (lambda (expr state next return break continue throw)
    (let ([condition-result (condition (operand1 expr) state)])
      (if condition-result
          (statement (operand2 expr) state next return break continue throw) ; then
          (if (= (length expr) 4)
              (statement (operand3 expr) state next return break continue throw) ; else
              (next state)))))) ; no else branch

; while a condition is true, iterate through a code block
(define while
  (lambda (expr state next return break continue throw)
    (letrec
        ([loop (lambda (state)
           (if (condition (operand1 expr) state)
               (statement (operand2 expr) state
                          (lambda (s) (loop s))
                          return
                          (lambda (s) (next s))
                          (lambda (s) (loop s))
                          throw)
              (next state)))])
         (loop state))))

; call a function
(define funcall
  (lambda (expr state next return break continue throw)
    (let* ([name (operand1 expr)]
          [params (actualparams expr)]
          [closure (lookup-binding name state)]
          [environment (get-environment closure)] ; if closure = *, then skip this step and run the body in the same enviornment
          [new-state (add-state-layer environment state)] ; have to add a custom layer
          [bound-state (bind-parameters (get-params closure) params new-state state return)]
          [functionnext (lambda (s) (next (restore-state state s)))]
          [functionreturn (lambda (v, s) (return v (restore-state state s)))]
          [functionbreak (lambda (s) loop-err)]
          [functioncontinue (lambda (s) loop-err)]
          [functionthrow (lambda (e, s) (throw e (restore-state state s)))])
         ((statement-list (get-body closure) bound-state functionnext functionreturn functionbreak functioncontinue functionthrow)))))

;; restore state 
(define restore-state
  (lambda (activestate functionstate)
    (restore-state-cps activestate functionstate (lambda (v) v))))

(define restore-state-cps
  (lambda (activestate functionstate return)
      (let ([binding (peek-binding functionstate)])
           (if (empty-lis? functionstate)
               activestate
               (restore-state-cps activestate 
                  (pop-binding functionstate) 
                  (lambda (v) (return 
                      (update-binding (car binding) (cadr binding) activestate))))))))

;; bind parameters
(define bind-parameters
  (lambda (formalparams actualparams new-state state)
    (bind-parameters-cps formalparams actualparams new-state state (lambda (v) v))))

(define bind-parameters-cps
  (lambda (formalparams actualparams new-state state return)
    (if (null? formalparams)
      new-state
      (bind-parameters-cps (cdr formalparams) (cdr actualparams) 
                       (add-binding (car formalparams) 
                                    (expression (car actualparams) state return) new-state) state return))))
       

; define a function
(define function
  (lambda (name formal-params body state)
    (add-binding name (make-closure formal-params body name state) state)))

; make a closure
; a function has a closure that consists of:
;   (param-list body (state with function added))
;   (state with function added) = (param-list body *)
;   * indicates that this is inside iteself so you should maintain the state and call the body
;   and params of the function again
(define make-closure
  (lambda (param-list body name state)
    (list param-list body (add-binding name (list param-list body '*) state))))

(define get-params
  (lambda (closure)
    (car closure)))

(define get-body
  (lambda (closure)
    (cadr closure)))

(define get-environment
  (lambda (closure)
    (caddr closure)))

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

; find the value of a binding by name
(define lookup-binding
  (lambda (name state)
    (let* ([index (return-pos-of-item name (get-state-names state))]
           [value (return-item-at-pos index (get-state-values state))])
      (if (eq? missing-err index)
          missing-err
          (cons value index)))))

; return the name and value of the binding at the first element
(define peek-binding
  (lambda (state)
    (let ([name (return-item-at-pos first-index (get-state-names state))]
          [value (return-item-at-pos first-index (get-state-values state))])
          (cons name value))))

; remove the first element of the state
(define pop-binding
  (lambda (state)
    (return-state (remove-item-at-pos first-index (get-state-names state))
                    (remove-item-at-pos first-index (get-state-values state)))))

; update a binding by replace function
(define update-binding
  (lambda (name newval state)
    (let ([index (return-pos-of-item name (get-state-names state))])
      (return-state (get-state-names state)
                    (replace-item-at-pos index newval (get-state-values state))))))

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

(define empty-lis?
(lambda (lis)
(empty-cps lis (lambda (v) v))))

(define empty-cps 
  (lambda (lis return)
    (cond
      ((null? lis) (return #t))
      ((pair? (car lis)) (return #f))
      ((null? (car lis)) (empty-cps (cdr lis) return))
      (else (return #f)))))

;; Helper: total number of atoms across all nested sublists
(define flat-length
  (lambda (lis)
    (cond
      ((null? lis) 0)
      ((list? (car lis)) (+ (flat-length (car lis)) (flat-length (cdr lis))))
      (else (+ 1 (flat-length (cdr lis)))))))

(define return-pos-of-item-cps
  (lambda (item lis return)
    (cond
      ((null? item) type-err)
      ((null? lis)  missing-err)
      ((list? (car lis)) ; search each sublist
       (let ([inner (return-pos-of-item-cps item (car lis) (lambda (v) v))])
         (if (eq? missing-err inner)
             (return-pos-of-item-cps item (cdr lis)
                                     (lambda (v) (return (+ (flat-length (car lis)) v))))
             (return inner))))
      ((eq? item (car lis)) (return 0))
      (else
       (return-pos-of-item-cps item (cdr lis)
                               (lambda (v) (return (+ 1 v))))))))

(define return-pos-of-item
  (lambda (item lis)
    (return-pos-of-item-cps item lis (lambda (v) v))))

(define return-item-at-pos-cps
  (lambda (pos lis return)
    (cond
      ((not (number? pos)) type-err)
      ((null? lis) (return #f pos))
      ((list? (car lis))
       (let ([sublen (flat-length (car lis))])
         (if (< pos sublen) ; target is inside this sublist
             (return-item-at-pos-cps pos (car lis) return)
             (return-item-at-pos-cps (- pos sublen) (cdr lis) return)))) ; target is beyond this sublist
      ((zero? pos) (return (car lis) 0))
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
      ((list? (car lis))
       (let ([sublen (flat-length (car lis))])
         (if (< pos sublen) ; target is inside this sublist
             (remove-item-at-pos-cps pos (car lis)
                                     (lambda (v1 pos1)
                                       (return (cons v1 (cdr lis)) pos1)))
             (remove-item-at-pos-cps (- pos sublen) (cdr lis) ; target is beyond this sublist
                                     (lambda (v2 pos2)
                                       (return (cons (car lis) v2) pos2))))))
      ((zero? pos) (return (cdr lis) 0))
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
      ((list? (car lis))
       (let ([sublen (flat-length (car lis))])
         (if (< pos sublen)
             (replace-item-at-pos-cps pos item (car lis) ; target within this sublist
                                      (lambda (v1 pos1)
                                        (return (cons v1 (cdr lis)) pos1)))
             (replace-item-at-pos-cps (- pos sublen) item (cdr lis) ; target beyond this sublist
                                      (lambda (v2 pos2)
                                        (return (cons (car lis) v2) pos2))))))
      ((zero? pos) (return (cons item (cdr lis)) 0))
      (else
       (replace-item-at-pos-cps (- pos 1) item (cdr lis)
                                (lambda (v pos)
                                  (return (cons (car lis) v) pos)))))))

(define replace-item-at-pos
  (lambda (pos item lis)
    (replace-item-at-pos-cps pos item lis (lambda (state pos) state))))