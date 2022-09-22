import z3
p, q, r = z3.Bools('p q r')
s = z3.Solver()
s.add(z3.Or(p, q), z3.Or(p, z3.Not(r)))
print(s.check()) # => sat
print(s.model()) # => (probably) [p = True, q = False, r = False]

