;; Here we will essentially label a formula - i.e. define a constant function
;; that returns a constraint.
;; We will also illustrate a simple way that z3 can be used as an automated
;; theorem prover.

(declare-const p Bool)
(declare-const q Bool)

;; NB "=>" is implication
(define-fun modus-ponens () Bool
	(=> (and p
                 (=> p q))
		q))

;; NB A formula is valid (true in all possible interpretations) 
;; iff its negation is unsatisfiable.
;; Hence, if we add the negation of our formula above to the assertion stack...
(assert (not modus-ponens))
;; ...and z3 tells us that the assertion is unsatisfiable
(check-sat) ;; => unsat
;; ...then z3 has proved (by contradiction) that our formula is valid.
