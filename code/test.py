from z3 import *


idArr = z3.Array('idArr', z3.IntSort(), z3.IntSort())
compArr= z3.Array('compArr',z3.IntSort(), z3.IntSort())
compP = z3.Array('compP', z3.IntSort(), z3.IntSort())
idd, comp, compNext, n = z3.Ints('idd comp compNext n')
j, k, l, m, b = z3.Ints('j k l m b')

def mkExtra(idd, comp, compNext):
	return Or(	And(idd==comp, comp==compNext),
				And(idd==compNext, compNext!=comp, comp!=0),
				And(comp==compNext, compNext!=idd, idd!=0))

def obvious(idd, comp, compNext):
	return And(idd>0, comp>=0, compNext>=0, Or(compNext==0, compNext>=idd))

def good(idArr, idd, comp, compNext, n):
    return And(obvious(idd, comp, compNext), 
			Or(	mkExtra(idd, comp, compNext), 
				And(0==comp, comp==compNext),
				And(compNext==0, Exists(j, And(0<=j, j<n, idArr[j]==comp, idArr[j]!=idd))),
	  			And(comp==0, compNext==idd),
	  			Exists([m,k,l], And(Or(And(0<=m, m<k, k<l, l<n),  And(0<=k, k<l, l<m, m<n),  And(0<=l, l<m, m<k, k<n)), 
				  					idArr[m]==idd, idArr[k]==comp,  idArr[l]==compNext))))

def maxFunc(idd, comp, compNext):
	return If(idd>comp, If(idd>compNext, idd, compNext), If(comp>compNext, comp, compNext))

print "defined good"

s = z3.Solver()
s.add(And(2<n, n<4))
s.add(ForAll(j, Implies(And(0<=j, j<n), good(idArr, idArr[j], compArr[j], compArr[(j+1)], n))))
#define compP, where process k moves
s.add(And(idArr[0]==idArr[n], compArr[0]==compArr[n], compP[0]==compP[n]))
s.add(And(0<=k, k<n, k!=n-1))
s.add(ForAll(j, Implies(And(0<=j, j<=n, j!=(k+1)), compP[j]==compArr[j])))
s.add(compP[(k+1)]==maxFunc(idArr[k], compArr[k], compArr[(k+1)]))
s.add(ForAll([j,k], Implies(And(0<=j, j<k, k<n), idArr[j]!=idArr[k])))
s.add(ForAll(j, Implies(And(0<=j, j<n), And(idArr[j]>0, compArr[j]>=0, compP[j]>=0, idArr[j]<=n, compArr[j]<=n))))

s.add(And(0<=b, b<n, Not(good(idArr, idArr[b], compP[b], compP[(b+1)], n))))
print "checking"
result = str(s.check())
print "done checking:"
print result
if result=="sat":
	print s.model()

s.reset()

s.add(And(2<n, n<16))
s.add(ForAll(j, Implies(And(0<=j, j<n), good(idArr, idArr[j], compArr[j], compArr[j+1], n))))
s.add(And(idArr[0]==idArr[n], compArr[0]==compArr[n]))
s.add(ForAll([j,k], Implies(And(0<=j, j<k, k<n), idArr[j]!=idArr[k])))
s.add(ForAll(j, Implies(And(0<=j, j<n), And(idArr[j]>0, compArr[j]>=0, idArr[j]<=n+n, compArr[j]<=n+n))))

s.add(Exists([j,k], And(0<=j, j<k, k<n, compArr[j]==idArr[j], compArr[k]==idArr[k])))

print "checking inv -> safety"
result = str(s.check())
print result
if result=="sat":
	print s.model()
