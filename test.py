from z3 import *
constraint = ForAll(z, z>3)
s = solver()
print s.check(constraint)

