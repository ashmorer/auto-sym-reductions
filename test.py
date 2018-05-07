from z3 import *


def inv(i,j,k):
	return inv2(i);

def inv2(i):
	return i>0;

n = z3.Int('n')
j = z3.Int('j')
#X = Array('x', IntSort(), IntSort())
p = Array('p', IntSort(), IntSort())
f = Array('f', IntSort(), IntSort())

s = Solver()
#s.add(n>2)
s.add(ForAll(j, Implies(And(0<=j, j<n-1), inv(p[j], f[j+1], f[j]))))

s.add(Exists(j, And(0<=j, j<n-1, Not(inv2(p[j])))))


print s.check()
if s.check()==sat:
	m = s.model()
	print m
else:
	print "Verified assert that wasn't verifying"
