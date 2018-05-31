from z3 import *

#set_param(proof=True)

#Define which terms are of which sorts
idd, compId, compId_next, idd_p, compId_p, compId_next_p, idd_int, compId_int, compId_next_int, idd_int_p, compId_int_p, compId_next_int_p = z3.Ints('idd compId compId_next idd_p compId_p compId_next_p idd_int compId_int compId_next_int idd_int_p compId_int_p compId_next_int_p')
big, big_p, big_int, big_int_p = z3.Ints('big big_p big_int big_int_p')

#Define predicates to be used
def mkInit(idd, compId, compId_next, big):
        return And(compId==0, compId_next==0, idd>0, big==0)

def mkBad1(idd, compId, compId_next, big):    #not veriifed...
	return Or(And(compId_next!=0, compId_next<idd), And(compId==0, compId_next>0, compId_next>idd)) 

def mkBad2(idd, compId, compId_next, big):
  return And(compId_next!=0, compId_next<idd) #verified...

#It's bad if I've ever passed on not the biggest thing
#It's bad if I've made a transition and big<my id
def mkBad3(idd, compId, compId_next, big):    #verified...
  return Or(compId_next!=big, And(0<compId_next, compId_next<idd), And(idd==compId, compId_next>compId), And(idd<compId, compId<compId_next), And(compId==0, compId_next>0, compId_next!=idd), And(compId<idd, idd<compId_next), And(idd<compId_next, compId_next<compId))

def mkBad(idd, compId, compId_next, big):
  return mkBad3(idd, compId, compId_next, big)

def max(idd, compId, big):
  return If(And(idd>compId, idd>big), idd, If(compId>big, compId, big))

def mkT(idd,compId,compId_next,big,idd_p,compId_p,compId_next_p,big_p):
	return And(idd==idd_p, compId==compId_p, big_p==max(idd, compId, big), compId_next_p==big_p)

def Inv(idd, compId, compId_next, big):
  return Not(mkBad(idd, compId, compId_next, big))

#Init -> Inv
cons1 = ForAll([idd, compId, compId_next, big],
               Implies(mkInit(idd, compId, compId_next, big), Inv(idd, compId, compId_next, big)))

vars = [idd,compId,compId_next,big,idd_p,compId_p,compId_next_p,big_p]
transLoc = ForAll(vars,
                   Implies(And(Inv(idd,compId,compId_next, big),
                               mkT(idd,compId,compId_next, big, idd_p,compId_p,compId_next_p, big_p)),
                           Inv(idd_p,compId_p,compId_next_p, big_p)))

#(Inv and Trans) -> Inv
cons2 = transLoc


vars2 = [idd,compId,compId_next,idd_p,compId_p,compId_next_p, idd_int, compId_int, compId_next_int, idd_int_p, compId_int_p, compId_next_int_p, big, big_p, big_int, big_int_p]
#"""
trans1Int = ForAll(vars2,
                   Implies(And(Inv(idd, compId, compId_next, big),
                               Inv(idd_int, compId_int, compId_next_int, big_int),
                               mkT(idd_int, compId_int, compId_next_int, big_int, idd_int_p, compId_int_p, compId_next_int_p, big_int_p),
                               And(compId_next_int==compId, compId_next_int_p==compId_p),
                               And(idd==idd_p, compId_next==compId_next_p, big==big_p, big_int==big_int_p)),
                           Inv(idd_p, compId_p, compId_next_p, big_p)))


#(Inv_i and Inv_j and T_j and local connection appropriate) -> Inv_i
cons3 = trans1Int

#Inv -> not Bad
cons4 = ForAll([idd, compId, compId_next, big], Implies(Inv(idd, compId, compId_next, big), Not(mkBad(idd, compId, compId_next, big))))

#t() does not mention compId_next

s = Solver()
#s.add(SystemCons)
#Add all the restrictions on the Invariant we seek.
s.add(cons1)
s.add(cons2)
s.add(cons3)
s.add(cons4)

print "before s.check()"

result = s.check()
print result

print "after s.check()"


if str(result)=="sat":
  print "Invariant satisfies constraints:"
  m = s.model()
  print m
else:
  #f= open("leaderProof.txt", "w")	
  #print s.proof()
  #f.close()   
  print "The proposed invariant doesn't work!"