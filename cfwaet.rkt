#lang plai

; Deferred Substitution Definition
( define-type DefrdSub
   ( emptySub )
   ( aSub (name symbol?) (value CFAE-Value?) (ds DefrdSub?) ) )

; Function to lookup values of identifiers in the 
; Substitution list
( define lookup
   ( lambda (name ds)
      ( type-case DefrdSub ds
         ( emptySub () (error 'lookup "identifier not found") )
         ( aSub (bound-name bound-value rest-ds)
                ( if (symbol=? name bound-name)
                     bound-value
                     (lookup name rest-ds) ) ) ) ) )   

; Values for CFAE
( define-type CFAE-Value
   ( numV (n number?) )
   ( closureV (param symbol?)
              (body CFAE?)
              (ds DefrdSub?) ) )
   
; CFAE Abstract Syntax Tree constructs
( define-type CFAE
   ( num (n number?) )
   ( id  (name symbol?) )
   ( op  (operator symbol?) (lhs CFAE?) (rhs CFAE?) )
   ( if0 (cond CFAE?) (tbr CFAE?) (fbr CFAE?) )
   ( fun (param symbol?) (fbody CFAE?) )
   ( app (fun-expr CFAE?) (arg CFAE?) ) )

; Define a list of operators. These will be used to lookup
; the function we wish to perform
( define binops (list (list `add +)(list `sub -)(list `mul *)(list `div /)) ) 
   
; Looks up an operator from the operator table
( define oplookup
   ( lambda ( op-name op-table )
      ( cond ( (empty? op-table) (error 'oplookup "Operator not found.") )
             ( else( if (symbol=? (first (car op-table)) op-name)
                        (second (car op-table))
                        (oplookup op-name (cdr op-table)) ) ) ) ) )

; Interprets a CFAE expression by evaluating it
( define interp-cfae
   ( lambda (expr ds ) 
      ( type-case CFAE expr
         ( num (n) (numV n) )
         ( id  (name) (lookup name ds) )
         ( op  (operator lhs rhs) (numV((oplookup operator binops) (numV-n(interp-cfae lhs ds)) (numV-n(interp-cfae rhs ds)))) )
         ( if0 (c t e) (if (= (numV-n (interp-cfae c ds)) 0)
                                 (interp-cfae t ds)
                                 (interp-cfae e ds)) )
         ( fun (param body) (closureV param body ds) )
         ( app (fun-expr arg-expr)
               (local ((define the-fun (interp-cfae fun-expr ds)))
                 (interp-cfae (closureV-body the-fun)
                              (aSub (closureV-param the-fun)
                                    (interp-cfae arg-expr ds)
                                    (closureV-ds the-fun)))) ) ) ) )

; Parses an expression and returns a CFAE expression
( define parse-cfae
   ( lambda (expr)
      ( cond
         ( (number? expr) (num expr) )
         ( (symbol? expr) (id expr ) )
         ( (list? expr)
          ( case (first expr)
             ( (+)    (op `add (parse-cfae (second expr)) (parse-cfae (third expr))) ) 
             ( (-)    (op `sub (parse-cfae (second expr)) (parse-cfae (third expr))) ) 
             ( (*)    (op `mul (parse-cfae (second expr)) (parse-cfae (third expr))) ) 
             ( (/)    (op `div (parse-cfae (second expr)) (parse-cfae (third expr))) ) 
             ( (if0)  (if0 (parse-cfae (second expr))
                           (parse-cfae (third  expr))
                           (parse-cfae (fourth expr))) )
             ( (fun)  (fun (second expr) (parse-cfae (third expr))) )
             ( else   (app (parse-cfae (first expr)) (parse-cfae (second expr))) )             
         ) )
         ( else (error 'parse-cfae "Parsing Error!" ) ) ) ) )
   
; Function to both parse and evaluate an expression
( define eval-cfae
   ( lambda (expr)
      ( interp-cfae (parse-cfae expr) (emptySub) ) ) )
   
; CFWAE Abstract Syntax Tree constructs
( define-type CFWAE
   ( numw  (n number?) )
   ( idw   (name symbol?) )
   ( addw  (lhs CFWAE?) (rhs CFWAE?) )
   ( subw  (lhs CFWAE?) (rhs CFWAE?) )
   ( mulw  (lhs CFWAE?) (rhs CFWAE?) )
   ( divw  (lhs CFWAE?) (rhs CFWAE?) )   
   ( withw (name symbol?) (named-expr CFWAE?) (body CFWAE?) )
   ( condw (branches list?) (base CFWAE?) )
   ( if0w  (cond CFWAE?) (tbr CFWAE?) (fbr CFWAE?) )
   ( funw  (param symbol?) (paramT CFWAETY?) (fbody CFWAE?) )
   ( appw  (fun-expr CFWAE?) (arg CFWAE?) ) )

( define-type CFWAETY
   ( numT )
   ( funT (dom CFWAETY?)
          (ran CFWAETY?) ) )

; Context for types
( define-type con
   ( mtCon )
   ( aCon (x symbol?)
          (t CFWAETY?)
          con ) )
   
; Create a small prelude for the CFWAE language
( define prelude
   ( aSub 'pi (numV 3.141592653589793 )
     ( aSub 'inc (closureV 'x (op 'add (id 'x) (num 1)) (emptySub))
       ( aSub 'square (closureV 'x (op 'mul (id 'x) (id 'x)) (emptySub))
          ( aSub 'area (closureV 'r (op 'mul (num pi) (op 'mul (id 'r) (id 'r))) (emptySub))
             (emptySub) ) ) ) ) )

; Determines the type of a CFWAE data structure
( define typeof 
   ( lambda (expr con)
      ( type-case CFWAE expr
         ( num (n) numT )
         ( addw (l r) (let (( lt (typeof l con))
                            ( rt (typeof r con)))
                        ( if ( and (equal lt rt)
                                   (equal lt numT))
                             numT
                             (error 'typeof "addw types are not valid!" ) ) ) )
         ( subw (l r) (let (( lt (typeof l con))
                            ( rt (typeof r con)))
                        ( if ( and (equal lt rt)
                                   (equal lt numT))
                             numT
                             (error 'typeof "subw types are not valid!" ) ) ) )
         ( mulw (l r) (let (( lt (typeof l con))
                            ( rt (typeof r con)))
                        ( if ( and (equal lt rt)
                                   (equal lt numT))
                             numT
                             (error 'typeof "mulw types are not valid!" ) ) ) )
         ( divw (l r) (let (( lt (typeof l con))
                            ( rt (typeof r con)))
                        ( if ( and (equal lt rt)
                                   (equal lt numT))
                             numT
                             (error 'typeof "divw types are not valid!" ) ) ) )
         ( if0w (c t e) 
               (if (eq (typeof c con) numT)
                   ( let ((tt (typeof t con))
                          (te (typeof e con)))
                      (if (equal tt te) tt (error 'typeof "if0 true and else branch types are not the same!")) )
                   ( error 'typeof "condition type is not a number!" )) )
                           

; Parses an expression and returns a CFWAE expression
( define parse-cfwae
   ( lambda (expr)
      ( cond         
         ( (number? expr) (numw expr) )
         ( (symbol? expr) (idw expr ) )
         ( (list? expr)
          ( case (first expr) 
             ( (+)   (addw (parse-cfwae (second expr)) (parse-cfwae (third expr))) )
             ( (-)   (subw (parse-cfwae (second expr)) (parse-cfwae (third expr))) )
             ( (*)   (mulw (parse-cfwae (second expr)) (parse-cfwae (third expr))) )
             ( (/)   (divw (parse-cfwae (second expr)) (parse-cfwae (third expr))) )
             ( (if0) (if0w (parse-cfwae (second expr))
                           (parse-cfwae (third  expr))
                           (parse-cfwae (fourth expr))) )
             ( (fun) (funw (second expr) (parse-cfwae (third expr))) )
             ( (with) (withw (first (second expr))
                             (parse-cfwae (second (second expr)))
                             (parse-cfwae (third expr))) )
             ; We need to call parse-branches on all but the last item in the list
             ; of branches. The last item serves as the base case so to speak.
             ( (cond0) (condw (parse-branches (drop-right (cdr expr) 1)) (parse-cfwae (last expr))) )
             ( else (appw (parse-cfwae (first expr)) (parse-cfwae (second expr))) )))
         ( else 'parse-cfwae "parsing failed!" ) ) ) )
                               
; Helper function to parse the branches of a cond0 expression
( define parse-branches
   ( lambda (branches)
      ( cond ((empty? branches) '())
             ; First parse the condition in the first branch
             ; then parse the expression in the first branch
             ; Finally recurse on the rest of the branches
             (else (cons (list (parse-cfwae (first  (first branches)))
                               (parse-cfwae (second (first branches))))
                         (parse-branches (cdr branches)))) ) ) )     

; Function to elaborate from CFWAE to CFAE
( define elab-cfwae
   ( lambda (expr)
      ( type-case CFWAE expr
         ( numw  (n) (num n) )
         ( idw   (n) (id  n) )
         ( addw  (lhs rhs) (op 'add (elab-cfwae lhs) (elab-cfwae rhs)) )
         ( subw  (lhs rhs) (op 'sub (elab-cfwae lhs) (elab-cfwae rhs)) )
         ( mulw  (lhs rhs) (op 'mul (elab-cfwae lhs) (elab-cfwae rhs)) )
         ( divw  (lhs rhs) (op 'div (elab-cfwae lhs) (elab-cfwae rhs)) )
         ( withw (name named-expr body) (app (fun name (elab-cfwae body)) (elab-cfwae named-expr)) )
         ( condw (brchs base) (elab-cond brchs (elab-cfwae base)) )
         ( if0w  (c t e) (if0 (elab-cfwae c) (elab-cfwae t) (elab-cfwae e)) )
         ( funw  (param body) (fun param (elab-cfwae body)) )
         ( appw  (fun param) (app (elab-cfwae fun) (elab-cfwae param)) ) ) ) )

; Helper function to handle elab-cfwaeorating cond statements
( define elab-cond
   ( lambda (branches base)
      (cond ((empty? branches) base)
            (else (if0 (elab-cfwae (first  (first branches)))
                       (elab-cfwae (second (first branches)))
                       (elab-cond  (cdr branches) base)))) ) )
             
; Combine the elab-cfwae and parse-cfwae functions into an eval function
; Calls the CFAE interp function
( define eval-cfwae
   ( lambda (expr)
     ( interp-cfae (elab-cfwae (parse-cfwae expr)) prelude ) ) ) 
  