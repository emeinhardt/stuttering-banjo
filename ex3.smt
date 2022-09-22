;; Here we will 
;;  1. see the *stack* structure of assertions in the solver state
;;  2. get a first taste of uninterpreted functions (technically not a feature
;;     of SAT solvers): we will get z3 to infer a definition for uninterpreted
;;     Boolean functions.

;; These two lines are necessary for `(get-assertions)` down below but may
;; need to be commented out on the z3 Guide "Playground" codeboxes.
(set-option :produce-assertions true)
(set-option :interactive-mode true)


;; -------------------------------------------------------------------------------
(declare-fun f (Bool) Bool) ;; "f is a unary function mapping Booleans to Booleans"

;; multiple assertions in a row...
(assert (not (f true))) ;; " f(true) = false"
(assert (f false))      ;; "f(false) = true"
;; equivalent to:
;; (assert (and (not (f true))
;;              (f false)))

;; Per earlier comment, this might need to be commented out if used in z3 Guide
;; Playground.
(get-assertions) 
;; =>  ((not (f true))
;;      (f false))

(check-sat) ;; => sat
(get-model) ;; The output should include a definition for f consistent
            ;; with all assertions - the negation function! (NB that 
            ;; `ite` is "if-then-else".)
(echo "============")

;; -------------------------------------------------------------------------------
;; A `stack` is a basic data structure - a "first in, last out" list.
;; Every time we use the `(push)` command, we 'chunk' all assertions/constraints 
;; since the last such command as essentially a single conjunct on the solver's 
;; assertion stack.
;; `(pop)` removes the topmost (most recent) chunk.

(declare-fun g (Bool Bool) Bool)

(assert (g true true))       ;; "g(T,T) = T"
(check-sat)                  ;; => sat
(push)                       ;; All assertions up to this point are now in one "chunk"
(get-assertions)             ;; See earlier comment about disabling in the z3 Guide Playground
(echo "----")
(echo "Now we add a constraint that contradicts previous ones...")
(assert (not (g true true))) ;; "g(T,T) = F"
(check-sat)                  ;; => unsat
(get-assertions)             ;; See earlier comment about disabling in the z3 Guide Playground
(echo "----")
(echo "Pop the topmost ('working') chunk of assertions...")
(pop)                        ;; Remove all assertions (there's just one) since the last `(push)`
(get-assertions)             ;; See earlier comment about disabling in the z3 Guide Playground
(check-sat)                  ;; => sat
(echo ":)")

