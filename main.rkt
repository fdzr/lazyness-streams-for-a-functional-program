#lang play

#|
<expr> ::= <num>
         | <bool>
         | <id>
         | <string>
         | {if <expr> <expr> <expr>}
         | {fun {<id>*}}  <expr>}
         | {<expr> <expr>*}
         | {local {<def>*} <expr>}
         | {match <expr> <case>+}

<case> ::= {'case <pattern> '=> <expr>}
<pattern> ::= <num>
         | <bool>
         | <string>
         | <id>
         | (<constr-id> <attr-id>*)

<def>  ::= {define <id> <expr>}
         | {datatype <typename> <type-constructor>*}}


<type-constructor> ::= {<id> <member>*}
<constr-id> :: = <id>
<attr-id> :: = <id>
<typename> :: = <id>
<member>   :: = <id>

|#
; expresiones
(deftype Expr
  (num n)
  (bool b)
  (str s)
  (ifc c t f)
  (id s)
  (app fun-expr arg-expr-list)
  (prim-app name args)   ; aplicación de primitivas
  (fun id body)
  (lcal defs body)
  (mtch val cases))

; definiciones
(deftype Def
  (dfine name val-expr) ; define
  (datatype name variants)) ; datatype

; variantes
(deftype Variant
  (variant name params))

; estructuras de datos
(deftype Struct
  (structV name variant values))

; caso en pattern matching
(deftype Case
  (cse pattern body))

; patrón
(deftype Pattern
  (idP id) ; identificador
  (litP l) ; valor literal 
  (constrP ctr patterns)) ; constructor y sub-patrones

;; parse :: s-expr -> Expr
(define(parse s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? boolean?) (bool s-expr)]
    [(? string?) (str s-expr)]
    [(? symbol?) (id s-expr)]    
    [(list 'if c t f) (ifc (parse c) (parse t) (parse f))]
    [(list 'fun xs b) (fun xs (parse b))]
    [(list 'with (list (list x e) ...) b)
     (app (fun x (parse b)) (map parse e))]
    [(list 'local defs body)
     (lcal (map parse-def defs) (parse body))] 
    [(list 'match val-expr cases ...) ; note the elipsis to match n elements
     (mtch (parse val-expr) (map parse-case cases))] ; cases is a list
    [(list 'list args ...) (parse(rec args))] ; solución para que el lenguaje acepte notación (list e1 e2 ... en)
    [(list f args ...) ; same here
     (if (assq f *primitives*)
         (prim-app f (map parse args)) ; args is a list
         (app (parse f) (map parse args)))]
    ))

; parse-def :: s-expr -> Def
(define(parse-def s-expr)  
  (match s-expr
    [(list 'define id val-expr) (dfine id (parse val-expr))]
    [(list 'datatype name variants ...) (datatype name (map parse-variant variants))]))

; parse-variant :: sexpr -> Variant
(define(parse-variant v)
  (match v
    [(list name params ...) (variant name params)]))

; parse-case :: sexpr -> Case
(define(parse-case c)
  (match c
    [(list 'case pattern => body) (cse (parse-pattern pattern) (parse body))]))

; parse-pattern :: sexpr -> Pattern
(define(parse-pattern p)  
  (match p
    [(? symbol?)  (idP p)]
    [(? number?)  (litP (num p))]
    [(? boolean?) (litP (bool p))]
    [(? string?)  (litP (str p))]
    [(list 'list patterns ...) (constrP 'Cons (map parse-pattern (cdr (rec patterns))))]; solucion al ejercicio 3 
    [(list ctr patterns ...) (constrP (first p) (map parse-pattern patterns))]))

;; interp :: Expr Env -> number/boolean/procedure/Struct
(define(interp expr env)
  (match expr 
    ; literals
    [(num n) n]
    [(bool b) b]
    [(str s) s]
    ; conditional
    [(ifc c t f)
     (if (interp c env)
         (interp t env)
         (interp f env))]
    ; identifier
    [(id x) (interp-id(env-lookup x env))]
    ; function (notice the meta interpretation)
    [(fun ids body)
     (λ (arg-vals)
       (printf "arg-values ~v~n" arg-vals)
       (def arg_vals (proc-args (zip ids (strict-function arg-vals)) (strict-cache arg-vals)))
       ;(printf "extend environment ~v~n" (extend-env (map remove-lazy ids) arg_vals env))
       (interp body (extend-env (map remove-lazy ids) arg_vals env)))]
    ; application
    [(app fun-expr arg-expr-list)
     ((interp fun-expr env)
       ;(map (λ (a) (interp a env)) arg-expr-list)
       ;arg-expr-list  ; pasar los argumentos con valores sin interpretar para en el nodo fun preguntar que argumento es lazy y no procesarlo
      (strict arg-expr-list env) ; pasar una promesa de los argumentos de función y el ambiente en el cual debe ser interpretado
      )]
    ; primitive application
    [(prim-app prim arg-expr-list)
     (apply (cadr (assq prim *primitives*))
            (map (λ (a) (interp a env)) arg-expr-list))]
    ; local definitions
    [(lcal defs body)
     (def new-env (extend-env '() '() env))            
     (for-each (λ (d) (interp-def d new-env)) defs)
     (interp body new-env)]
    ; pattern matching
    [(mtch expr cases)
     (def value-matched (interp expr env))
     (def (cons alist body) (find-first-matching-case value-matched cases))
     (interp body (extend-env (map car alist) (map cdr alist) env))]))

; interp-def :: Def Env -> Void
(define(interp-def d env)
  (match d
    [(dfine id val-expr)
     (update-env! id (interp val-expr env) env)]
    [(datatype name variants)
     ;; extend environment with new definitions corresponding to the datatype
     (interp-datatype name env)
     (for-each (λ (v)(interp-variant name v env)) variants)]))

; interp-datatype :: String Env -> Void
(define(interp-datatype name env)
  ; datatype predicate, eg. Nat?
  (update-env! (string->symbol (string-append (symbol->string name) "?"))
               ;(λ (v) (symbol=? (structV-name (first v)) name)); solución original
               ;(λ (v)(printf "datatype interp ~v~n" v) (symbol=? (structV-name (first v)) name)) ; solucion para ver para parametros
               (λ (v) (symbol=? (structV-name (interp(first(strict-function v)) (strict-cache v))) name)) ; solucion del ejercicio para lazy en los datatypes
               env))

; interp-variant :: String String Env -> Void
(define(interp-variant name var env)  
  ;; name of the variant or dataconstructor
  (def varname (variant-name var))
  ;(printf "~v type of arguments " (variant-params var))  ;para ver los parametros
  ;; variant data constructor, eg. Zero, Succ
  (update-env! varname
               ;(λ (args)(structV name varname args)) ;solución original
               (λ (args)(printf "interp-variant ~v~n~a" args (variant-params var))(structV name varname (proc-args (zip (variant-params var) (strict-function args)) (strict-cache args)))); posible solucion a datatypes con parametros lazy
               
               env)
  ;; variant predicate, eg. Zero?, Succ?
  (update-env! (string->symbol (string-append (symbol->string varname) "?")); predicados (constructores) de las estructuras
               (λ (v) (symbol=? (structV-variant (interp (first(strict-function v)) (strict-cache v))) varname))
               env))

;;;;
; pattern matcher
(define(find-first-matching-case value cases)
  (match cases
    [(list) #f]
    [(cons (cse pattern body) cs)
     (match (match-pattern-with-value pattern value)
       [#f (find-first-matching-case value cs)]
       [alist (cons alist body)])]))

(define(match-pattern-with-value pattern value)
  (match/values (values pattern value)
                [((idP i) v) (list (cons i v))]
                [((litP (bool v)) b)
                 (if (equal? v b) (list) #f)]
                [((litP (num v)) n)
                 (if (equal? v n) (list) #f)]
                [((constrP ctr patterns) (structV _ ctr-name str-values))
                 (if (symbol=? ctr ctr-name)
                     (apply append (map match-pattern-with-value
                                        patterns str-values))
                     #f)]
                [(x y) (error "Match failure")]))

;; run :: s-expr -> number/boolean/procedura/struct
(define(run prog)
  (define s-expr-build (append initial_s-expr (list prog)))
  (pretty-printing(interp (parse s-expr-build) empty-env))
  )


#|-----------------------------
Environment abstract data type
empty-env   :: Env
env-lookup  :: Sym Env -> Val 
extend-env  :: List[Sym] List[Val] Env -> Env
update-env! :: Sym Val Env -> Void
|#
(deftype Env
  (mtEnv)
  (aEnv bindings rest)) ; bindings is a list of pairs (id . val)

(def empty-env  (mtEnv))

(define(env-lookup id env)
  (printf "environment actual ~v~n" env)
  (printf "lookup id ~v~n" id)
  (match env
    [(mtEnv) (error 'env-lookup "no binding for identifier: ~a" id)]
    [(aEnv bindings rest)
     (def binding (assoc id bindings))
     (if binding
         (cdr binding)
         (env-lookup id rest))]))

(define (extend-env ids vals env)
  (aEnv (map cons ids vals) ; zip to get list of pairs (id . val)
        env))

;; imperative update of env, adding/overring the binding for id.
(define(update-env! id val env)
  (set-aEnv-bindings! env (cons (cons id val) (aEnv-bindings env))))

;;;;;;;

;;; primitives
; http://pleiad.cl/teaching/primitivas
(define *primitives*
  `((+       ,(lambda args (apply + args)))
    (-       ,(lambda args (apply - args)))
    (*       ,(lambda args (apply * args)))
    (%       ,(lambda args (apply modulo args)))             
    (odd?    ,(lambda args (apply odd? args)))
    (even?   ,(lambda args (apply even? args)))
    (/       ,(lambda args (apply / args)))
    (=       ,(lambda args (apply = args)))
    (<       ,(lambda args (apply < args)))
    (<=      ,(lambda args (apply <= args)))
    (>       ,(lambda args (apply > args)))
    (>=      ,(lambda args (apply >= args)))
    (zero?   ,(lambda args (apply zero? args)))
    (not     ,(lambda args (apply not args)))
    (and     ,(lambda args (apply (lambda (x y) (and x y)) args)))
    (or      ,(lambda args (apply (lambda (x y) (or x y)) args)))))


;Warm-up
;pretty-printing: Struct -> String
;función que recibe una estructura y devuelve un String representado la variante de la estructura y se devuelve si tiene valores la variante
(define (pretty-printing expr)
  (match expr
    ['() ""]
    [(? number?) expr]
    [(? boolean?) expr]
    [(? string?) expr]
    [(? list?)(~a (pretty-printing(car expr))(pretty-printing(cdr expr)))]
    #|[(structV name type-variant values) (~a "{" type-variant (if (equal? values empty)
                                                                 "{ }"
                                                                 (pretty-printing values)) "}")]|#
    [(structV name type-variant values)
     (if (equal? name 'List)
         (aux expr)
         (if (equal? empty values)
             (~a "{" type-variant "}")
             (~a "{" type-variant " " (pretty-printing values) "}")))
     ]
    )
  )

(define (aux expr)
  (match expr
    ['() ""]
    [(? number?) (number->string expr)]
    [(? boolean?) expr]
    [(? string?) expr]
    [(? list?)(if(structV? (car expr))
                 (~a " {list" (temp (car expr)) "}" " " (temp (cdr expr)))
                 (~a " " (aux (car expr)) (temp (cdr expr))))]
    [(structV name type-variant values)(~a (string-append "{list" (aux values)) "}")]
    )
  )

(define (temp expr)
  (match expr
    ['() ""]
    [(? number?)(number->string expr)]
    [(? list?)(temp(car expr))]
    [(structV name type-variant values)(aux values)]
    )
  )

; Listas

(define initial_s-expr '{local {{datatype List
                          {Empty}
                          {Cons a b}}
                {define length {fun {n}
                                {match n
                                   {case {Empty} => 0}
                                   {case {Cons a b} => {+ 1 {length b}}}}}}}})


;rec: Expr -> Expr
; función que recibe el cuerpo(notación de lista (list e1 e2 ... en)) de un match y devuelve la representación en Pares(Cons a (Cons b (Empty)))
(define (rec expr)
  (if(empty? expr)
     '(Empty)
     (append (list 'Cons (if(list? (car expr))
                            (if(equal? (car(car expr)) 'list)
                               (rec(cdr(car expr)))
                               (car expr))
                            (car expr))) (list (rec (cdr expr)))))
  )

;zip: List[x] List[y] -> List[(x, y)]
; función que recibe dos listas y devuelve una lista de pares de los elementos de las listas
(define (zip list-1 list-2)
  (map list list-1 list-2))


;

(define (proc-args args env)
  (if(equal? empty args)
     '()
     (cons (proc-args-aux(car args) env) (proc-args(cdr args) env)))
  )

(define (proc-args-aux arg env)
  (match arg
    [(list id val)(if(symbol? id)
                     (interp val env)
                     ;val
                     (strict (lambda()(interp val env)) (box #f))
                     )]
    )
  )

(define (map-customize function list)
  (if (equal? empty list)
      '()
      (cons (function(car list)) (map-customize function (cdr list))))
  )

(define (remove-lazy id)
  (match id
    [(? symbol?) id]
    [(? list?)(cadr id)]
    )
  )

; Estructura para guardar los datos que no van a ser interpretado cuando el id de los parámetros es lazy, se almacena la función de interpretacion con sus argumentos
; y el campo cache para almacenar el valor de una expresión y así no calcular más de una vez.
(deftype Val
  (strict function cache))

(define (interp-id expr)
  (match expr
    [(strict fun cache)(if(unbox cache)
                        (begin
                          (unbox cache))
                        (let ([value fun])
                          (set-box! cache (value)) (value)))]
    [x x]
    )
  )


; Ejercicio 2 (Evaluación Perezoza)
(def stream-data '{datatype Stream
                              {stream hd {lazy tl}}
                              })

(def make-stream '{define make-stream {fun {hd {lazy tl}}
                                              {stream hd tl}}})



; Trabajando con Streams

(def stream-hd '{define stream-hd {fun {streams}
                                          {match streams
                                            {case {stream hd tl} => hd}}
                                          }})

(def stream-tl '{define stream-tl {fun {streams}
                                          {match streams
                                            {case {stream hd tl} => tl}}
                                          }})

(def ones '{define ones {make-stream 1 ones}})




; Ejercicio 2 Streams

#|(define stream-take '{define stream-take {fun {n streams}
                                              {if {= n 0}
                                                  {Empty}
                                                  {stream {stream-hd streams} {stream-take {- n 1} 2}}}}
                       })

(def stream-lib (list stream-data
                      make-stream
                      stream-hd
                      stream-tl
                      stream-take))|#

(define stream-take '{define stream-take {fun {n streams}
                                               {if {= n 0}
                                                   {Empty}
                                                   {Cons {stream-hd
streams} {stream-take {- n 1} {stream-tl streams}}}}}
                        })

(def stream-zipWith '{define stream-zipWith {fun {f l1 l2}
                                                  {stream {f {stream-hd l1}{stream-hd l2}} {stream-zipWith f {stream-tl l1}{stream-tl l2}} }
                                                  }
                        })

(def fibs '{define fibs {stream 1 {stream 1 {stream-zipWith {fun {n m}
                                                                 {+ n m}} {stream-tl fibs} fibs}}}})

(def merge-sort '{define merge-sort {fun {stream1 stream2}
                                         {if{< {stream-hd stream1} {stream-hd stream2}}
                                            {stream {stream-hd stream1}{stream {stream-hd stream2} {merge-sort {stream-tl stream1}{stream-tl stream2}}}}
                                            {stream {stream-hd stream2}{stream {stream-hd stream1} {merge-sort {stream-tl stream1}{stream-tl stream2}}}}}}})

(def stream-lib (list stream-data
                       make-stream
                       stream-hd
                       stream-tl
                       stream-take
                       stream-zipWith))

;(def stream-take '{define stream-take {fun {n list}
 ;                                          })


#|(run '{local {{datatype List
                          {Empty}
                          {Cons a b}}
                {define length {fun {n}
                                {match n
                                   {case {Empty} => 0}
                                   {case {Cons a b} => {+ 1 {length b}}}}}}}
                                   {length {Cons 1 {Cons 2 {Cons 3 {Empty}}}}}})|#


                                   
                                   




































