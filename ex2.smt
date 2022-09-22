;; Introducing z3's notation for function definitions...
(declare-const p Bool)
(declare-const q Bool)
(assert (and p q))
(check-sat) ;; => sat
(get-model) ;; The output should introduce a model where 
            ;; p and q are defined as *constant functions*
            ;; of zero arguments that return a single truth
            ;; value.

