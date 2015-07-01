#lang racket
; MESS
; Martin-Löf Extensible Specification and Simulator
; (c) Gershom Bazerman, 2015
; BSD(3) Licensed

(require racket/match)

; value formers
(struct lam-pi (var vt body) #:transparent)
(struct app (fun arg) #:transparent)
; primitives
(struct closure (typ body) #:transparent)
(struct trustme (typ body) #:transparent)

; type formers
(struct type-fun (dom codom) #:transparent)
; one basic type
(define type-unit 'type-unit)
; dependency
(struct type-pi (var dom codom) #:transparent)
(define type-type 'type) ; inconsistent!

; contexts
(define (find-cxt nm cxt)
  (match (assoc nm cxt) [(cons a b) b] [_ #f]))

(define (fresh-var nm cxt)
  (if (assoc nm cxt) (fresh-var (string->symbol (string-append (symbol->string nm) "'")) cxt) nm))

(define-syntax-rule (extend-cxt var vt cxt (newvar newcxt) body)
  (let* ([newvar (fresh-var var cxt)]
         [newcxt (cons (cons newvar vt) cxt)])
    body))

(struct stuck-app (fun arg) #:transparent)

; a reduction of a value in a context creates a term where "app" is not in the head position.
; this is "weak head normal form" call-by-name reduction
; we call a term in such a form "reduced" or simply a "value"
(define/match (reduce cxt body)
  ; To reduce an application of a function to an argument
  ; we confirm that the argument is compatible with the function
  ; and we produce the application of the function to the argument
  ; (if we omit the type check, we get nuprl semantics) 
  [(_ (app (lam-pi var vt  b) arg))   
   (if (hasType? cxt arg vt) (reduce cxt (b arg)) 
       (raise-arguments-error 'bad-type "bad type"
                              "cxt" cxt "arg" arg "vt" vt "app" (lam-pi var vt b)))]
  ; To reduce an application of a closure to an argument, we produce a closure
  ; whose type is the application of the closure type to the argument type
  ; and whose body is the application of the closure body to the argument
  [(_ (app (closure ty b) arg))
   (closure (app-type cxt (red-eval cxt ty) arg) (lambda (cxt) (app (b cxt) arg)))] 
  ; To reduce an application of anything else to an argument, we first reduce the thing itself
  ; and then attempt to again reduce the application of the result
  [(_ (app fun arg)) (if (or (not fun) (symbol? fun))
                         (stuck-app fun arg)
                         (reduce cxt (app (reduce cxt fun) arg)))]
  [(_ _) body])

; A red-eval of a term in a context creates a term where neither "app" nor "closure" are in the head position
; we call a term in such a form "evaluated" (or also, where evident, a "value").
(define (red-eval cxt x)
  (match (reduce cxt x)
    ; To red-eval a closure, we red-eval the application of the body of the closure to the context
    [(closure typ b) (red-eval cxt (b cxt))]
    [v v]))

; An application of a type to a term confirms the term is compatible with the type
; and if so, removes provides the new type that is the result of applying a term
; with the type to a term with the type of the argument
(define/match (app-type cxt fun arg)
  [(_ (type-fun a b) _)
   (if (hasType? cxt arg a) b
       (raise-arguments-error 'bad-type "bad type applying in closure" "cxt" cxt "fun" fun "arg" arg))]
  [(_ (type-pi a at b) _)
   (if (hasType? cxt arg a) (b arg)
       (raise-arguments-error 'bad-type "bad pi type applying in closure" "cxt" cxt "fun" fun "arg" arg))]
  [(_ _ _) (raise-arguments-error 'bad-type "can't apply non-function type in closure" "cxt" cxt "fun" fun "arg" arg)])

(define/match (head-type t)
  [((type-fun a b)) a]
  [((type-pi av a b)) a]
  [(_) (raise-arguments-error 'bad-type "can't take head of non-function-type")]) ; TODO what if it is a symbol?


; In all the following, judgment may be read as "verification"
; and "to judge" may be read as "to verify," "to know" or "to confirm"

; We may judge that an evaluated term is a type by the following rules
(define (type? cxt t) 
  (match (red-eval cxt t)
    ; We know a value is a type if we know that it is tagged type-fun
    ; and furthermore we know that its domain is a type and its codomain is a type
    [(type-fun a b) (and (type? cxt a) (type? cxt b))]
    ; We know a value is a type if it has the symbol 'type-unit
    ['type-unit #t]
    ; We know a value is a type in a context if it is a symbol and that context assigns it a type of type
    [(? symbol? vname) #:when (eq? type-type (find-cxt vname cxt)) #t]
    ; We know a value is a type if we know that it is tagged type-pi
    ; and furthermore we know that its domain is a type and in a context where
    ; its domain is assigned the proper type, its body can send the domain to a type.
    [(type-pi var a b)
     (and (type? cxt a) (extend-cxt var a cxt (newvar newcxt) (type? newcxt (b newvar))))]
    ; We know a value is a type if it has the symbol 'type
    ['type #t]
    ; Or, we know a value is a type if any other rules let us make such a judgment
    [t1 (type?-additional cxt t1)]
    ))

; We may judge that a reduced value has an evaluated type by the following rules
(define (hasType? cxt x1 t1)
  (match* ((reduce cxt x1) (red-eval cxt t1))
    ; To know a closure is of a type is to know that the type of the closure is equal to the desired type
    [((closure typ b) t) (eqType? cxt typ t)]
    ; To know a primitive is of a type is to know the type claimed by the primitive is equal to the desired type
    [((trustme typ b) t) (eqType? cxt typ t)]
    ; To know that a symbol has a type in a context is to know that the context assigns the symbol a type equal to the desired type
    [((? symbol? x) t) #:when (eqType? cxt t (find-cxt x cxt)) #t]
    ; To know that a lambda has type function is to know that
    ; the domain of the function type is equal to the input type of the body and to know that
    ; in a context where the argument is assigned the proper domain type
    ; the body in turn has a type of the codomain of the function type
    [((lam-pi vn vt body) (type-fun a b))
     (and (eqType? cxt vt a)
          (extend-cxt vn vt cxt (newvar newcxt) (hasType? newcxt (body newvar) b)))]
    ; To know that a term has type unit is to know that it is the unit value
    [(x 'type-unit) (null? x)]
    ; To know that a lambda has type pi is to know that
    ; the domain of the function type is equal to the input type of the body and to know that
    ; in a context where the argument is assigned the proper domain type
    ; the body in turn has a type of the codomain of the function type, as viewed in the same context
    [((lam-pi vn vt body) (type-pi _ a b))
     (and (eqType? cxt vt a)
          (extend-cxt vn vt cxt (newvar newcxt) 
                      (hasType? newcxt (body newvar) (reduce newcxt (b newvar)))))]
    ; To know that a term has type type is to know that the term may be judged a type
    [(x 'type) (type? cxt x)]
    ; Or, to know that a term has any other type is to follow any additional rules
    ; on how we may judge the types of terms
    [(x t) (hasType?-additional cxt x t)]))

; We may judge that two evaluated values are equal as types by the following rules
(define (eqType? cxt t1 t2)
  (match* ((red-eval cxt t1) (red-eval cxt t2))
    ; To know two types tagged type-fun are equal is to know that
    ; they have terms equal as types in their domains and
    ; they have terms equal as types in their codomains
    [((type-fun a b) (type-fun a1 b1))
     (and (eqType? cxt a a1) (eqType? cxt b b1))]
    ; To know two types tagged type-pi are equal is to know that
    ; they have terms equal as types in their domains and
    ; in a context where their arguments are assigned the proper domain type
    ; then their codomains also equal as types
    [((type-pi v a b) (type-pi v1 a1 b1))
     (and (eqType? cxt a a1)
          (extend-cxt v a cxt (newvar newcxt) 
                      (eqType? newcxt (b newvar) (b1 newvar))))]
    ; To know two symbols are equal as types is to know that they are the same symbol
    [((? symbol? vname) (? symbol? vname1)) (eq? vname vname1)]
    ; To know two stuck applications are equal as types is to know that their functions have equal types, and are equal as values.
    ; And additionally, to know that their arguments have equal values at the type of the function argument.
    [((stuck-app fun arg) (stuck-app fun1 arg1))
     (and
      (eqType? cxt (find-cxt fun cxt) (find-cxt fun1 cxt))
      (eqVal? cxt (find-cxt fun cxt) fun fun1)
      (eqVal? cxt (head-type (find-cxt fun cxt)) arg arg1))]
    ; Or to know any other two values are equal as types is to follow any
    ; additional rules on how we may judge the equality of terms as types
    [(a b) (and a b (or (eqType?-additional cxt a b)
                        (begin (printf "not equal\n ~a\n ~a\n cxt: ~a\n" a b cxt) #f)))]))

; We may judge that two evaluated values are equal at an evaluated type types by the following rules
(define (eqVal? cxt typ v1 v2)
  (match* ((red-eval cxt typ) (red-eval cxt v1) (red-eval cxt v2))
    ; To know two lambda terms are equal at a function type is to know that
    ; their domains are equal as types to the domain of the function type and
    ; in a context where their domains are assigned the proper input type
    ; then their bodies are equal at the type of the codomain
    [((type-fun a b) (lam-pi x xt body) (lam-pi y yt body2))
     (and (eqType? cxt a xt) (eqType? cxt a yt)
          (extend-cxt x xt cxt (newv newcxt)
                      (eqVal? newcxt b (body newv) (body2 newv))))]
    ; To know two lambda terms are equal at a pi type is to know that
    ; their domains are equal as types to the domain of the function type and
    ; in a context where their domains are assigned the proper input type
    ; then their bodies are equal at the type of the codomain, as viewed in the same context
    [((type-pi v a b) (lam-pi x xt body) (lam-pi y yt body2))
     (and (eqType? cxt a xt) (eqType? cxt a yt)
          (extend-cxt x xt cxt (newv newcxt)
                      (eqVal? newcxt (b newv) (body newv) (body2 newv))))]
    ; To know two values are equal at unit type
    ; requires knowing nothing else -- it is always known
    [('type-unit _ _) #t]
    ; To know two values are equal at type type is to know that they are equal as types
    [('type a b) (eqType? cxt a b)]
    ; To know two symbols are equal at any type is to know that they are equal as symbols
    [(_ (? symbol? x) (? symbol? y)) #:when (eq? x y) #t]
    ; To know two primitives are equal at any type is to know their types are equal and know that
    ; their bodies are equal by primitive recursive comparison
    [(_ (trustme t v) (trustme t1 v1)) (and (eqType? cxt t t1) (equal? v v1))] ;if all else fails use primitive equality
    ; Or to know any other two values are equal at any other type is to follow any
    ; additional rules on how we may judge the equality of terms at types
;    [(rtyp x y) (eqVal?-additional cxt rtyp x y)]))
    [(rtyp x y) (and rtyp (or (eqVal?-additional cxt rtyp x y)
                          (begin (printf "not equal\n typ: ~a\n ~a\n ~a\n cxt: ~a\n" rtyp x y cxt) #f)))]))

; TODO try to add just syntactic equality for stuck terms at a type

(define type-judgments '())
(define (type?-additional cxt t)
  (for/or ([p type-judgments]) (p cxt t)))

(define hasType-judgments '())
(define (hasType?-additional cxt x t)
  (for/or ([p hasType-judgments]) (p cxt x t)))

(define eqType-judgments '())
(define (eqType?-additional cxt t1 t2)
  (for/or ([p eqType-judgments]) (p cxt t1 t2)))

(define eqVal-judgments '())
(define (eqVal?-additional cxt typ v1 v2)
  (for/or ([p eqVal-judgments]) (p cxt typ v1 v2)))

(define apps
  (lambda (fun . args)
    (foldl (lambda (arg acc) (app acc arg)) fun args)))

(define-syntax-rule (lam   (x t) body) (lam-pi  (quote x) t (lambda (x) body)))
(define-syntax-rule (pi    (x t) body) (lam-pi  (quote x) t (lambda (x) body)))
(define-syntax-rule (pi-ty (x t) body) (type-pi (quote x) t (lambda (x) body)))
(define-syntax-rule (close    t  body) (closure t body))

(displayln "id-unit: is type, has type")
(define id-unit (lam (x type-unit) x))
(define id-unit-type (type-fun type-unit type-unit))
(type?    '() id-unit-type)
(hasType? '() id-unit  id-unit-type)

(displayln "id-forall: is type, has type")
(define id-forall (pi (t type-type) (lam (x t) x)))
(define id-forall-type (pi-ty (tau type-type) (type-fun tau tau)))
(type?    '() id-forall-type)
(hasType? '() id-forall id-forall-type)

(displayln "id-forall: application typechecks")
(hasType? '() (app id-forall type-unit) id-unit-type)
(hasType? '() (apps id-forall type-unit '()) type-unit)

(displayln "k-comb: is type, has type")
(define k-comb 
  (pi (a type-type) (lam (x a) (pi (b type-type) (lam (y b) x)))))
(define k-comb-type
  (pi-ty (a type-type) (type-fun a (pi-ty (b type-type) (type-fun b a)))))

(type?    '() k-comb-type)
(hasType? '() k-comb k-comb-type)

(displayln "checking rejection of bad signatures")
(hasType? '() k-comb id-forall-type)
(hasType? '() id-forall id-unit-type)

; To introduce a new type is to
; extend the ways to know a value is a type
; give a way to know a value has that type
; extend the ways to know two values are equal as types
; give a way to know two values are equal at that type

(define (new-form type-judgment hasType-judgment eqType-judgment eqVal-judgment)
  (cond [type-judgment    (set! type-judgments    (cons type-judgment    type-judgments))])
  (cond [hasType-judgment (set! hasType-judgments (cons hasType-judgment hasType-judgments))])
  (cond [eqType-judgment  (set! eqType-judgments  (cons eqType-judgment  eqType-judgments))])
  (cond [eqVal-judgment   (set! eqVal-judgments   (cons eqVal-judgment   eqVal-judgments))])
  )

; adding bool
(define type-bool 'type-bool)
(new-form 
 ; To know a value is a type may be to know that it is the symbol 'type-bool
 (lambda (cxt t) (eq? t 'type-bool))
 ; To know a value is of type bool is to know that it is #t or #f
 (lambda (cxt x t) (and (eq? t 'type-bool) (boolean? x)))
 ; to know a two values are equal as types when the symbol 'type-bool corresponds to a type
 ; is to compare the symbols, which is already known
 #f
 ; To know two values are equal at type bool is to know that they are equal as scheme values
 (lambda (cxt t x y) (and (eq? t 'type-bool) (eq? x y))))

; If we are given two terms at a type,
; then we may produce a term that sends bools to either the first or second of those given terms.
(define bool-elim
  (pi (a type-type) (lam (x a) (lam (y a) (lam (b type-bool) (close a (lambda (cxt) (if (red-eval cxt b) x y))))))))

; If we know a mapping from bools to types
; and we know a term of the type that is the image of that function on true
; and we know a term of the type that is the image of that function on false
; then we may produce a term that sends bools to either the first or second of those terms
; at either the first or second of those types
(define bool-induct
  (pi (p (type-fun type-bool type-type))
  (lam (x (app p #t))
  (lam (y (app p #f))
  (pi (bl type-bool)
  (close (app p bl) (lambda (cxt) (if (red-eval cxt bl) x y))))))))

(displayln "functions on bool")
(define not-bool (apps bool-elim type-bool #f #t))
(red-eval '() (app not-bool #t))
(red-eval '() (app not-bool #f))

; adding equality types
(struct type-eq (type v1 v2) #:transparent)
(struct val-eq (v1 v2))

(new-form
 ; To know a value is a type may be to know that
 ; it is tagged with type-eq and a given type
 ; to know that its first term is of the appropriate type and
 ; to know that its second term is of the appropriate type
 (match-lambda**
  [(cxt (type-eq type v1 v2))
   (and (hasType? cxt v1 type)
        (hasType? cxt v2 type))]
  [(_ _) #f])
 ; To know a value has an equality type is to know that
 ; the values of equality type can be known equal at the appropriate type
 (match-lambda**
  [(cxt 'refl (type-eq type v1 v2)) ;note we ignore the refl
   (eqVal? cxt type v1 v2)]
  [(_ _ _) #f])
 ; To know a two types are equal may be to know that
 ; they are of type-eq and
 ; they are equalities at the same type and
 ; their first values are equal at that type
 ; their second values are equal at that type
 (match-lambda**
  [(cxt (type-eq t1t t1a t1b) (type-eq t2t t2a t2b))
   (and (eqType? cxt t1t t2t) (eqVal? cxt t1t t1a t2a) (eqVal? cxt t1t t1b t2b))]
  [(_ _ _) #f])
 ; To know if two values are equal at any given equality type
 ; requires knowing nothing else -- it is always known
 (match-lambda**
  [(cxt (type-eq t a b) _ _) #t]
  [(_ _ _ _) #f])
 )

; equality intro
; if we know a term at a type, we know that the term, at that type, is equal to itself
(define refl (pi (a type-type) (pi (x a) (close (type-eq a x x) (lambda (cxt) 'refl)))))

; equality elim

; if we know a type
; and we know a family C which can send two terms at that type and an equality between them to types
; and know how to produce from a term at a type a value of C as decided by the identity path on our term
; then we may produce a term that
; sends two values at a type and an equality between them to the value of C as decided by that path between them
(define equal-induct
  (pi (a type-type)
  (pi (c (pi-ty (x a) (pi-ty (y a) (type-fun (type-eq a x y) type-type))))
  (lam (f (pi-ty (z a) (apps c z z 'refl)))
  (pi (m a)
  (pi (n a)
  (pi (p (type-eq a m n))
  (close (apps c m n p) (lambda (cxt) (app f m))))))))))

;todo prove transitivity

(displayln "proving that for all bool, not (not x) = x")

(define not-not-bool (lam (x type-bool) (app not-bool (app not-bool x))))
(define id-bool (lam (x type-bool) x))

; not-not-is-id
(define nnii-fam (lam (x type-bool) (type-eq type-bool (app id-bool x) (app not-not-bool x))))
(hasType? '() nnii-fam (type-fun type-bool type-type))
(hasType? '() 'refl (app nnii-fam #t))

(define nnii-type (pi-ty (x type-bool) (app nnii-fam x)))
(define nnii (pi (x type-bool) (apps bool-induct nnii-fam (apps refl type-bool #t) (apps refl type-bool #f) x)))
(type? '() nnii-type)
(hasType? '() nnii nnii-type)

(displayln "but we don't have extensional function equality")
(define nnii-extensional (type-eq (type-fun type-bool type-bool) id-bool not-not-bool))
(type? '() nnii-extensional)
(hasType? '() (apps refl (type-fun type-bool type-bool) id-bool) nnii-extensional)

(displayln "although we do have intensional equality")
(hasType? '() (apps refl (type-fun type-bool type-bool) not-not-bool) (type-eq (type-fun type-bool type-bool) not-not-bool not-not-bool))

(displayln "and we can add eta as an axiom")
(define eta-axiom
  (pi (a type-type)
  (pi (b type-type)
  (pi (f (type-fun a b))
  (pi (g (type-fun a b))
  (pi (prf (pi-ty (x a) (type-eq a (app f x) (app g x))))
  (trustme (type-eq (type-fun a b) f g) 'eta-axiom)))))))

(define nnii-extensional-term (apps eta-axiom type-bool type-bool id-bool not-not-bool nnii))
(hasType? '() nnii-extensional-term nnii-extensional)
(hasType? '() (red-eval '() nnii-extensional-term) nnii-extensional)
(red-eval '() nnii-extensional-term)

(displayln "naturals are easy")
(define type-nat 'type-nat)
(new-form 
 (lambda (cxt t) (eq? t 'type-nat))
 (lambda (cxt x t) (and (eq? t 'type-nat) (exact-integer? x) (>= x 0)))
 #f
 (lambda (cxt t x y) (and (eq? t 'type-nat) (eq? x y))))

(define z 0)
(define succ (lam (x type-nat)
             (close type-nat (lambda (cxt)
               (let ([x1 (red-eval cxt x)])
                 (if (number? x1)
                     (+ x1 1)
                     (trustme type-nat (cons 'succ x1))))))))

(define nat-induct
  (pi (c (type-fun type-nat type-type))
  (lam (base (app c z))
  (lam (induct (pi-ty (n2 type-nat)
                      (type-fun (app c n2) (app c (app succ n2)))))
  (pi (n1 type-nat)
  (close (app c n1) (lambda (cxt) (for/fold ([acc base])
                                           ([x (in-range (red-eval cxt n1))])
                                   (apps induct x acc)))))))))

(define double (apps nat-induct (lam (x type-nat) type-nat) z (pi (x type-nat) (lam (n type-nat) (app succ (app succ n))))))
(red-eval '() (app double (app double (app succ z))))

(define plus (lam (a type-nat)
             (apps nat-induct (lam (x type-nat) type-nat) a (pi (n type-nat) (lam (n type-nat) (app succ n))))))

(red-eval '() (apps plus 5 5))


(displayln "we can use sigma types, for existential proofs")
(struct type-sig (a b) #:transparent)
(define-syntax-rule (sig-ty (x t) body) (type-sig t (lambda (x) body)))
(new-form 
 ; To know a value is a type may be to know that it is tagged type-sig
 ; and to know that its first element is a type
 ; and to know that the second element can send terms of the first element to types.
 (match-lambda**
  [(cxt (type-sig a b))
   (and (type? cxt a)
        (extend-cxt 'fst a cxt (newv newcxt)
                    (type? newcxt (b newv))))]
  [(_ _) #f])
 ; To know a value is of type sigma is to know that it is a pair
 ; and to know that its first element has the type of the first element of the type
 ; and to know that its second element has the type that the second element of the type
 ; sends the first element of the value to.
 (match-lambda**
  [(cxt (cons x y) (type-sig a b))
      (and (hasType? cxt x a)
           (hasType? cxt y (b x)))]
  [(_ _ _) #f])
 ; To know two values are equal as types may be to know that they are both tagged type-sig
 ; and that their first elements are equal as types
 ; and that their second elements send values of the first element to terms that are equal as types
 (match-lambda**
  [(cxt (type-sig a b) (type-sig a1 b1))
   (and (eqType? cxt a a1)
        (extend-cxt 'fst a cxt (newv newcxt)
                    (eqType? newcxt (b newv) (b1 newv))))]
  [(_ _ _) #f])
 ; To know two values are equal at a sigma type is to know that
 ; their first elements are equal at the first component of the sigma type
 ; and their second elements are equal at the type produced by the application of the
 ; second component of the sigma type to either of their first elements.
 (match-lambda** 
  [(cxt (type-sig a b) (cons x y) (cons x1 y1))
   (and (eqVal? cxt a x x1)
        (eqVal? cxt (b x) y y1))]
  [(_ _ _ _) #f]))

(define sig-induct-type
  (pi-ty (a type-type)
  (pi-ty (b (type-fun a type-type))
  (pi-ty (c (type-fun (sig-ty (x a) (app b x)) type-type))
  (type-fun
   (pi-ty (x a)
   (pi-ty (y (app b x))
   (app c (cons x y))))
  (pi-ty (p (sig-ty (x a) (app b x)))
  (app c p)))))))

(define sig-induct
  (pi (a type-type)
  (pi (b (type-fun a type-type))
  (pi (c (type-fun (sig-ty (x a) (app b x)) type-type))
  (lam (g (pi-ty (x a)
          (pi-ty (y (app b x))
          (app c (cons x y)))))
  (pi (p (sig-ty (x a) (app b x)))
  (close (app c p) (lambda (env) (apps g (car (red-eval env p)) (cdr (red-eval env p)))))))))))

(displayln "Sigma induction can be defined.")
(hasType? '() sig-induct sig-induct-type)

;; Forall A, B over A, app fst Sig(a A,B a) : A
(define fst-sig-type
  (pi-ty (a type-type)
  (pi-ty (b (type-fun a type-type))
  (type-fun (sig-ty (x a) (app b x)) a)
  )))

(define fst-sig
  (pi (a type-type)
  (pi (b (type-fun a type-type))
  (lam (sg (sig-ty (x a) (app b x)))
  (apps sig-induct a b
        (lam (s (sig-ty (x a) (app b x))) a)
        (pi (x a) (pi (y (app b x)) x))
        sg)))))

(displayln "We can use sigma induction to properly eliminate out of sigma, with the type we would expect")
(red-eval '() (apps fst-sig type-nat (lam (x type-nat) type-bool) (cons 25 #t)))

; every number has a successor
(define has-succ (pi (n type-nat) (cons (app succ n) (apps refl type-nat (app succ n)))))
(define has-succ-type (pi-ty (n type-nat) (sig-ty (x type-nat) (type-eq type-nat x (app succ n)))))
(hasType? '() has-succ has-succ-type)

; every inhabitant of unit is equal to '()
(define unit-induct
  (pi  (c (type-fun type-unit type-type))
  (lam (v (app c '()))
  (pi  (u type-unit)
  (close (app c u) (lambda (env) v))))))
(define is-unit (pi (u type-unit) (cons u (apps unit-induct
                                                (lam (x type-unit) (type-eq type-unit x '()))
                                                (apps refl type-unit '())
                                                u))))
(define is-unit-type (pi-ty (u type-unit) (sig-ty (x type-unit) (type-eq type-unit x '()))))
(hasType? '() is-unit is-unit-type)

(displayln "we have partial type inference")
(define (inferType cxt x1)
  (match (reduce cxt x1)
    [(closure typ b) typ]
    [(trustme typ b) typ]
    [(? symbol? x) #:when (find-cxt x cxt) (find-cxt x cxt)]
    [(lam-pi vn vt body) 
     (extend-cxt vn vt cxt (newvar newcxt)
                 (type-pi newvar vt (lambda (y) (subst y newvar (reduce newcxt (inferType newcxt (body newvar)))))))]
    ['() type-unit]
    [(? number? x) type-nat]
    [(? boolean? x) type-bool]
    [(cons a b) (type-sig (inferType cxt a) (lambda (arg) (inferType cxt b)))] ; can't infer sigmas in general
   ; ['refl ...] -- given a plain refl what is its type?
    ; in both cases, more data in terms can help clean this up...
    [(? (lambda (x) (type? cxt x))) type-type]
    ))

(define/match (subst y v x)
  [(_ _ (? symbol? x)) #:when (eq? x y) y]
  [(_ _ (closure typ b)) (closure (abs y v typ) (lambda (cxt) (subst y v (b cxt))))]
  [(_ _ (trustme typ b)) (closure (subst y v typ) (subst y v b))]
  [(_ _ (lam-pi vn vt body)) (lam-pi vn (subst y v vt) (lambda (arg) (subst y v (body arg))))]
  [(_ _ (cons a b))       (cons     (subst y v a) (subst y v b))]
  [(_ _ (type-fun  a b))  (type-fun (subst y v a) (subst y v b))]
  [(_ _ (type-eq t a b))  (type-eq  (subst y v t) (subst y v a) (subst y v b))]
  [(_ _ (type-pi av a b)) (type-pi av (subst y v a) (lambda (arg) (subst y v (b arg))))]
  [(_ _ (type-sig   a b)) (type-sig (subst y v a) (lambda (arg) (subst y v (b arg))))]
  [(_ _ _) x]
  )

(define (saturate cxt x)
  (match (reduce cxt x) 
    [(closure typ b) (closure (saturate cxt typ) (saturate cxt (red-eval cxt (b cxt))))]
    [(trustme typ b) (trustme (saturate cxt typ) b)]
    [(lam-pi vn vt body)
     (extend-cxt vn vt cxt (newvar newcxt)
                 (lam-pi vn vt (saturate newcxt (body newvar))))]
    [(cons a b)       (cons     (saturate cxt a) (saturate cxt b))]
    [(type-fun   a b) (type-fun (saturate cxt a) (saturate cxt b))]
    [(type-eq  t a b) (type-eq  (saturate cxt t) (saturate cxt a) (saturate cxt b))]
    [(type-pi av a b) 
     (extend-cxt av a cxt (newvar newcxt)
                 (type-pi newvar (saturate newcxt a) (saturate newcxt (b newvar))))]
    [(type-sig a b)
     (extend-cxt 'fst a cxt (newvar newcxt)
                 (type-sig (saturate newcxt a) (saturate newcxt (b newvar))))]
    [v v]
    ))

(saturate '() (inferType '() id-bool))
(saturate '() (inferType '() not-not-bool))
(saturate '() (inferType '() nnii))
(saturate '() (inferType '() (cons #t '())))

(displayln "we can build either from sigma")
(define (either-type a b) (sig-ty (bl type-bool)
                                  (apps bool-elim type-type a b bl)))
(define left  (pi (t type-type) (lam (a t) (cons #t a))))
(define right (pi (t type-type) (lam (a t) (cons #f a))))

(hasType? '() (apps left type-nat 5) (either-type type-nat type-nat))

(define maybe-zero (pi (n type-nat) (either-type (type-eq type-nat n z) type-bool)))
(define zero-or-not (apps nat-induct 
                              (lam (x type-nat) (app maybe-zero x))
                              (apps left (type-eq type-nat z z) (apps refl type-nat z))
                              (pi (x type-nat) (lam (y (app maybe-zero x)) (apps right type-bool #f)))))

(hasType? '() (pi (x type-nat) (app zero-or-not x)) (pi-ty (x type-nat) (app maybe-zero x)))

(displayln "we can introduce a type for falsehood, and use it to show contradiction.")
(define type-false 'false)
(new-form 
 (lambda (cxt t) (eq? t 'false))
 #f
 #f
 (lambda (cxt t x y) (eq? t 'false)))

(define transport
  (pi (a type-type)
  (pi (p (type-fun a type-type))
  (apps equal-induct
        a
        (pi (x a) (pi (y a) (lam (q (type-eq a x y)) (type-fun (app p x) (app p y)))))
        (pi (z a) (lam (v (app p z)) v))))))

(define trivial-transport (apps transport type-bool (lam (x type-bool) type-nat) #t #t (apps refl type-bool #t)))
(red-eval '() (app trivial-transport 4))

(define true-is-false (type-eq type-bool #t #f))
(define bool-to-type (apps bool-elim type-type type-unit type-false))

(define contradiction-implies-false
  (lam (absurd true-is-false)
  (apps transport type-bool bool-to-type #t #f absurd '())))

(hasType? '() contradiction-implies-false (type-fun true-is-false type-false))
(hasType? '() (app contradiction-implies-false (trustme true-is-false 'haha)) type-false)
(displayln "although if we posit a falsehood we still can't generate an actual inhabitant of type false.")
(red-eval '() (app contradiction-implies-false (trustme true-is-false 'haha)))

; And finally we can give an axiom for univalence.

(struct pair-ty (fst snd) #:transparent)

(define (fun-compose a f g)
  (lam (x a) (app f (app g a))))

(define (type-homotopy a p f g)
  (pi (x a) (type-eq (app p x) (app f x) (app g x))))

(define (type-isequiv a b f)
  (pair-ty 
   (sig-ty (g (type-fun b a)) (type-homotopy b (lam (x a) b) (fun-compose b f g) (lam (x b) x)))
   (sig-ty (h (type-fun b a)) (type-homotopy a (lam (x b) a) (fun-compose a h f) (lam (x a) x)))))
  
(define (type-equiv a b)
  (sig-ty (f (type-fun a b)) (type-isequiv a b f)))

(define univalence-axiom (pi (a type-type) (pi (b type-type)
  (trustme (type-equiv (type-equiv a b) (type-eq type-type a b)) 'ua))))

; references
; Simply Easy: http://strictlypositive.org/Easy.pdf
; Simpler, Easier: http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html
; PTS: http://hub.darcs.net/dolio/pts
; Pi-Forall: https://github.com/sweirich/pi-forall
