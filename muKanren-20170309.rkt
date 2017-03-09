#lang racket/base

; a racket implementation of muKanren.

; a state in muKanren consists of a list of variable binding/substitutions
; and a counter for fresh variables. a result/solution is expressed in the
; form of binding/substitution, and a muKanren goal transfer a state to
; another state, may or maynot have a solution; that is, the result of a
; muKanren program may or maynot consists a list which is not null and
; consists such bindings.
; for example, the following muKanren program:
;   (call/fresh (λ (q) (=== q 5)))
; (the === here is usually written as == in other implementations)
; will transfer a state to another state which extends the original binding
; list with a new binding, namely the binding between the variable q and the
; constant 5; the representation of this and any other binding is determined
; by the representation chosen when implementing the language itself.
; in some kind of notation the ``types'' for muKanren's primitives and some
; notions can be written as follows:
;    goal       = state -> state
;    ===        : any * any -> goal
;    call/fresh : goal -> goal
;    conj       : goal * goal -> goal
;    disj       : goal * goal -> goal

(define (var x) (vector x))
(define (var? x) (vector? x))
(define (ext-s x v s) `((,x . ,v) . ,s))
(define (walk u s)
  ; walk u in s.
  (let ((walkres (assoc u s)))
    (if walkres (walk (cdr walkres) s) u)))
; if a goal succeeds it returns a list of solutions.
; if it fails then it returns no solution, which is a list with nothing
; inside.
(define (=== u v)
  (λ (s/c)
    (let ((s (unify u v (car s/c))))
      (if s (ext `(,s . ,(cdr s/c))) mzero))))
(define (ext x) (cons x mzero))
(define mzero '())

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (var? u) (var? v) (equal? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else (and (eqv? u v) s)))))
(define (call/fresh f)
  ; the binding of variable is done _at a higher level_.
  (λ (s/c)
    ; remember that a goal is a state -> state.
    ; the car of a state is the bindings
    ; and the cdr of a state is the fresh var counter.
    (let ((c (cdr s/c)))
      ((f (var c)) `(,(car s/c) . ,(+ c 1))))))

(define (disj g1 g2) (λ (s/c) (mplus (g1 s/c) (g2 s/c))))
(define (conj g1 g2) (λ (s/c) (bind (g1 s/c) g2)))

; the mplus & bind determines the searching method used by muKanren.
(define (mplus s1 s2)
  (cond
    ((null? s1) s2) ; if s1 has no result...
    ; we suspend the computation of appending the result of s1 to s2 by
    ; using a lambda...
    ((procedure? s1) (λ () (mplus s2 (s1))))
    ; with the switch between s2 and s1 the search will try every part
    ; of the disjunction for a limited amount of time.
    ; when the result is required we retrieve it:
    (#T (cons (car s1) (mplus (cdr s1) s2)))))
(define (bind s g)
  (cond
    ((null? s) mzero)
    ((procedure? s) (λ () (bind (s) g)))
    (else (mplus (g (car s)) (bind (cdr s) g)))))
; what bind basically does is that it runs the goal g on every single
; result in the previous result stream s and sum up all the possibilities.

; inverse-eta-delay. required for doing infinite stream related stuff.
(define-syntax invdelay
  (syntax-rules ()
    ((_ g) (λ (s/c) (λ () (g s/c))))))
; multi-conj & multi-disj.
(define-syntax conj+
  (syntax-rules ()
    ((_ g) (invdelay g))
    ((_ g1 g2 ...) (conj (invdelay g1) (conj+ g2 ...)))))
(define-syntax disj+
  (syntax-rules ()
    ((_ g) (invdelay g))
    ((_ g1 g2 ...) (disj (invdelay g1) (disj+ g2 ...)))))

; conde.
(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) ...)
     (disj+ (conj+ g0 g ...) ...))))

; fresh.
(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g ...) (conj+ g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/fresh (λ (x0) (fresh (x ...) g0 g ...))))))

(define (pull s) (if (procedure? s) (pull (s)) s))
(define (pull* s n)
  (cond ((= n 0) '())
        ((procedure? s) (pull* (s) n))
        (#T (cons (car s) (pull* (cdr s) (- n 1))))))
(define (pull! s)
  (cond ((procedure? s) (pull! (s)))
        ((null? (cdr s)) s)
        (#T (cons (car s) (pull! (cdr s))))))

; a reifier...
#|
Reification is the process by which an abstract idea about a computer program
is turned into an explicit data model or other object created in a programming language.
-- from Wikipedia
|#
(define (mK-reify s/c*)
  (map reify-state/1st-var s/c*))
(define (reify-state/1st-var s/c)
  (let ((v (walk* (var 0) (car s/c))))
    (walk* v (reify-s v '()))))
(define (reify-s v s) ; for every unbound logic var we give it a new name.
  (let ((v (walk v s)))
    (cond
      ((var? v)
       (let ((n (reify-name (length s))))
         (cons `(,v . ,n) s)))
      ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
      (else s))))
(define (reify-name n)
  (string->symbol
   (string-append "_" "." (number->string n))))
(define (walk* v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) v)
      ((pair? v) (cons (walk* (car v) s)
                       (walk* (cdr v) s)))
      (else v))))

(define empty-state '(() . 0))
(define (call/empty-state g) (g empty-state))

#|
Here, mK-reify is encoded into the run and
run* macros; this could be replaced by a different reier,
or the denitions of run and run* could instead be paramaterized
over the reier and the choice left up to the ultimate
user.
-- from the original muKanren paper
|#
(define-syntax run
  (syntax-rules ()
    ((_ n (x ...) g0 g ...)
     (mK-reify (pull* (call/empty-state (fresh (x ...) g0 g ...)) n)))))
(define-syntax run*
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (mK-reify (pull! (call/empty-state (fresh (x ...) g0 g ...)))))))

; some other possible extensions...
(define (failed? g) (null? (call/empty-state g)))
(define (succeeded? g) (not (failed? g)))
