from z3 import *

import smtplib
from email.mime.text import MIMEText

#some vars
n, i, j = z3.Ints('n i j')
idd, compId, compId_next = z3.Ints('idd compId compId_next')

#mkInv()
def mkInv(idd, compId, compId_next, big):
	return And(Or(compId_next <= compId, compId < idd), Or(compId_next <= idd, And(idd <= compId, compId <= compId_next)))
#Assume non-trivial system
size = n>2

#Define full system
idArr = z3.Array('idArr', z3.IntSort(), z3.IntSort())
compIdArr = z3.Array('compIdArr', z3.IntSort(), z3.IntSort())
bigArr = z3.Array('bigArr', z3.IntSort(), z3.IntSort())

#Provide boundary considerations
topol = And(idArr[0]==idArr[n], compIdArr[0]==compIdArr[n], bigArr[0]==bigArr[n])

#Assume for all i, process i satisfies local inv()
setup = ForAll(i, Implies(And(0<=i, i<n),mkInv(idArr[i], compIdArr[i], compIdArr[i+1], bigArr[i])))

#Assume there are two leaders
bad = Exists([i,j], And(0<=i, i<j, j<n, idArr[i]==compIdArr[i], idArr[j]==compIdArr[j]))

#Added info (seemingly) inexpressible locally
added = ForAll([i,j], Implies(And(0<=i, i<j, j<n), idArr[i]!=idArr[j]))
nonneg = ForAll(i, Implies(And(0<=i, i<n), And(idArr[i]>0, compIdArr[i]>=0, bigArr[i]>=0)))#in particular, ids are positive

s = z3.Solver()
s.add(size)		#non-trivial size
s.add(topol)	#Rings loop around
s.add(setup)	#Everybody satisfies local properties
s.add(bad)		#Assume for counter-example bad state reached
s.add(added)	#Add assumption that everybody's id is distinct
s.add(nonneg)	#All values are non-negatives

print "constraints added"

result =  s.check()
print result
print "done checking!"
output = ""
output += result + "\n"



if str(result)=="unsat":
	print "Local implies global, no counterexample found"
else:
	print "modelling"
	print s.model()
	print "Local does not imply global, counterexample given above"

print "goodbye"