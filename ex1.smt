;; Basic example checking satisfiability of 
;;   (p ∨ q) ∧ (p ∨ ¬q)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (and (or p q)
             (or p (not r))))
(check-sat)
(get-model)
