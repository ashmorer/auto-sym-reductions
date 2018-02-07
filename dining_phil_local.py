from z3 import *

#Define the two sorts
State = Datatype('State')
State.declare('T')
State.declare('H')
State.declare('E')
State = State.create()

Fork = Datatype('Fork')
Fork.declare("unowned")
Fork.declare("cw")
Fork.declare("ccw")
Fork = Fork.create()

#Define which terms are of which sorts
pc, pc_p, pc_int, pc_int_p = Consts('pc pc_p pc_int pc_int_p', State)
lfork, lfork_p, lfork_int, lfork_int_p = Consts('lfork lfork_p lfork_int lfork_int_p', Fork)
rfork, rfork_p, rfork_int, rfork_int_p = Consts('rfork rfork_p rfork_int rfork_int_p', Fork)

#Define predicates to be used
def mkInit(pc, lfork, rfork):
	return And(pc==State.T, lfork==Fork.unowned, rfork==Fork.unowned)

#Init(pc, lfork, rfork) iff pc==T, lfork==rfork==unowned
'''
Init = Function('Init', State, Fork, Fork, BoolSort())
InitCons1 = ForAll([pc, lfork, rfork], Implies(Init(pc, lfork, rfork), And(pc==State.T, lfork==Fork.unowned, rfork==Fork.unowned)))
InitCons2 = ForAll([pc, lfork, rfork], Implies(And(pc==State.T, lfork==Fork.unowned, rfork==Fork.unowned), Init(pc, lfork, rfork)))
InitCons = And(InitCons1, InitCons2)
#'''

def mkBad(pc, lfork, rfork):
	return And(pc==State.E, Or(lfork!=Fork.ccw, rfork!=Fork.cw))
#Bad(pc, lfork, rfork) iff pc==E and (lfork!=ccw or rfork!=cw)
'''
Bad = Function('Bad', State, Fork, Fork, BoolSort())
BadCons1 = ForAll([pc, lfork, rfork], Implies(Bad(pc, lfork, rfork), And(pc==State.E, Or(lfork!=Fork.ccw, rfork!=Fork.cw))))
BadCons2 = ForAll([pc, lfork, rfork], Implies(And(pc==State.E, Or(lfork!=Fork.ccw, rfork!=Fork.cw)), Bad(pc, lfork, rfork)))
BadCons = And(BadCons1, BadCons2)
#'''


def mkT1(pc,lfork,rfork,pc_p,lfork_p,rfork_p):
	return And(pc==State.T, pc_p==State.H, lfork==lfork_p, rfork==rfork_p)
def mkT2(pc,lfork,rfork,pc_p,lfork_p,rfork_p):
	return And(pc==State.H, pc_p==State.H, lfork==Fork.unowned, lfork_p==Fork.ccw, rfork==rfork_p)
def mkT3(pc,lfork,rfork,pc_p,lfork_p,rfork_p):
	return And(pc==State.H, pc_p==State.H, rfork==Fork.unowned, rfork_p==Fork.cw, lfork==lfork_p)
def mkT4(pc,lfork,rfork,pc_p,lfork_p,rfork_p):
	return And(pc==State.H, pc_p==State.E, lfork==Fork.ccw, lfork_p==Fork.ccw, rfork==Fork.cw, rfork_p==Fork.cw)
def mkT5(pc,lfork,rfork,pc_p,lfork_p,rfork_p):
	return And(pc==State.E, pc_p==State.T, lfork_p==Fork.unowned, rfork_p==Fork.unowned)
def mkT(pc,lfork,rfork,pc_p,lfork_p,rfork_p):
	return And(mkT1(pc,lfork,rfork,pc_p,lfork_p,rfork_p), mkT2(pc,lfork,rfork,pc_p,lfork_p,rfork_p), mkT3(pc,lfork,rfork,pc_p,lfork_p,rfork_p), mkT4(pc,lfork,rfork,pc_p,lfork_p,rfork_p), mkT5(pc,lfork,rfork,pc_p,lfork_p,rfork_p))

#T(pc, lfork, rfork, pc_p, lfork_p, rfork_p) should be defined by ANDing each transition.
'''
T = Function('T', State, Fork, Fork, State, Fork, Fork, BoolSort())
t1 = And(pc==State.T, pc_p==State.H, lfork==lfork_p, rfork==rfork_p)
t2 = And(pc==State.H, pc_p==State.H, lfork==Fork.unowned, lfork==Fork.ccw, rfork==rfork_p)
t3 = And(pc==State.H, pc_p==State.H, rfork==Fork.unowned, rfork==Fork.cw, lfork==lfork_p)
t4 = And(pc==State.H, pc_p==State.E, lfork==Fork.ccw, lfork_p==Fork.ccw, rfork==Fork.cw, rfork_p==Fork.ccw)
t5 = And(pc==State.E, pc_p==State.T, lfork_p==Fork.unowned, rfork_p==Fork.unowned)
t = Or(t1, t2, t3, t4, t5)
tCons1 = ForAll([pc, lfork, rfork, pc_p, lfork_p, rfork_p], Implies(t, T(pc, lfork, rfork, pc_p, lfork_p, rfork_p)))
tCons2 = ForAll([pc, lfork, rfork, pc_p, lfork_p, rfork_p], Implies(T(pc, lfork, rfork, pc_p, lfork_p, rfork_p), t))
tCons = And(tCons1, tCons2)
#'''

#SystemCons = [InitCons, BadCons, tCons]

Inv = Function('Inv', State, Fork, Fork, BoolSort())

#Init -> Inv
cons1 = ForAll([pc, lfork, rfork], Implies(mkInit(pc, lfork, rfork), Inv(pc, lfork, rfork)))


trans1Loc = ForAll([pc, lfork, rfork, pc_p, lfork_p, rfork_p], Implies(And(Inv(pc, lfork, rfork), mkT1(pc, lfork, rfork, pc_p, lfork_p, rfork_p)), Inv(pc_p, lfork_p, rfork_p)))

trans2Loc = ForAll([pc, lfork, rfork, pc_p, lfork_p, rfork_p], Implies(And(Inv(pc, lfork, rfork), mkT2(pc, lfork, rfork, pc_p, lfork_p, rfork_p)), Inv(pc_p, lfork_p, rfork_p)))

trans3Loc = ForAll([pc, lfork, rfork, pc_p, lfork_p, rfork_p], Implies(And(Inv(pc, lfork, rfork), mkT3(pc, lfork, rfork, pc_p, lfork_p, rfork_p)), Inv(pc_p, lfork_p, rfork_p)))

trans4Loc = ForAll([pc, lfork, rfork, pc_p, lfork_p, rfork_p], Implies(And(Inv(pc, lfork, rfork), mkT4(pc, lfork, rfork, pc_p, lfork_p, rfork_p)), Inv(pc_p, lfork_p, rfork_p)))

trans5Loc = ForAll([pc, lfork, rfork, pc_p, lfork_p, rfork_p], Implies(And(Inv(pc, lfork, rfork), mkT5(pc, lfork, rfork, pc_p, lfork_p, rfork_p)), Inv(pc_p, lfork_p, rfork_p)))

#(Inv and Trans) -> Inv
cons2 = And(trans1Loc, trans2Loc, trans3Loc, trans4Loc, trans5Loc)


#"""
trans1Int = ForAll([pc, lfork, rfork, lfork_p, rfork_p, pc_int, lfork_int, rfork_int, pc_int_p, lfork_int_p, rfork_int_p], Implies( \
And( \
Inv(pc, lfork, rfork), \
Inv(pc_int, lfork_int, rfork_int), \
mkT1(pc_int,lfork_int,rfork_int, pc_int_p, lfork_int_p, rfork_int_p), \
Or( \
And(lfork==rfork_int, lfork_p==rfork_int_p, rfork==rfork_p), \
And(rfork==lfork_int, rfork_p==lfork_int_p, lfork==lfork_p) \
) \
) \
, \
Inv(pc, lfork_p, rfork_p) \
) \
)
#"""
#"""
trans2Int = ForAll([pc, lfork, rfork, lfork_p, rfork_p, pc_int, lfork_int, rfork_int, pc_int_p, lfork_int_p, rfork_int_p], Implies( \
And( \
Inv(pc, lfork, rfork), \
Inv(pc_int, lfork_int, rfork_int), \
mkT2(pc_int,lfork_int,rfork_int, pc_int_p, lfork_int_p, rfork_int_p), \
Or( \
And(lfork==rfork_int, lfork_p==rfork_int_p, rfork==rfork_p), \
And(rfork==lfork_int, rfork_p==lfork_int_p, lfork==lfork_p) \
) \
) \
, \
Inv(pc, lfork_p, rfork_p) \
) \
)
#"""

#"""
trans3Int = ForAll([pc, lfork, rfork, lfork_p, rfork_p, pc_int, lfork_int, rfork_int, pc_int_p, lfork_int_p, rfork_int_p], Implies( \
And( \
Inv(pc, lfork, rfork), \
Inv(pc_int, lfork_int, rfork_int), \
mkT3(pc_int,lfork_int,rfork_int, pc_int_p, lfork_int_p, rfork_int_p), \
Or( \
And(lfork==rfork_int, lfork_p==rfork_int_p, rfork==rfork_p), \
And(rfork==lfork_int, rfork_p==lfork_int_p, lfork==lfork_p) \
) \
) \
, \
Inv(pc, lfork_p, rfork_p) \
) \
)
#"""

#"""
trans4Int = ForAll([pc, lfork, rfork, lfork_p, rfork_p, pc_int, lfork_int, rfork_int, pc_int_p, lfork_int_p, rfork_int_p], Implies( \
And( \
Inv(pc, lfork, rfork), \
Inv(pc_int, lfork_int, rfork_int), \
mkT4(pc_int,lfork_int,rfork_int, pc_int_p, lfork_int_p, rfork_int_p), \
Or( \
And(lfork==rfork_int, lfork_p==rfork_int_p, rfork==rfork_p), \
And(rfork==lfork_int, rfork_p==lfork_int_p, lfork==lfork_p) \
) \
) \
, \
Inv(pc, lfork_p, rfork_p) \
) \
)
#"""

#"""
trans5Int = ForAll([pc, lfork, rfork, lfork_p, rfork_p, pc_int, lfork_int, rfork_int, pc_int_p, lfork_int_p, rfork_int_p], Implies( \
And( \
Inv(pc, lfork, rfork), \
Inv(pc_int, lfork_int, rfork_int), \
mkT5(pc_int,lfork_int,rfork_int, pc_int_p, lfork_int_p, rfork_int_p), \
Or( \
And(lfork==rfork_int, lfork_p==rfork_int_p, rfork==rfork_p), \
And(rfork==lfork_int, rfork_p==lfork_int_p, lfork==lfork_p) \
) \
) \
, \
Inv(pc, lfork_p, rfork_p) \
) \
)
#"""

#(Inv_i and Inv_j and T_j and local connection appropriate) -> Inv_i
cons3 = And(trans1Int, trans2Int, trans3Int, trans4Int, trans5Int)

#Inv -> not(Bad)
cons4 = ForAll([pc, lfork, rfork], Implies(Inv(pc, lfork, rfork), Not(mkBad(pc, lfork, rfork))))


s = Solver()
#s.add(SystemCons)
#Add all the restrictions on the Invariant we seek.
s.add(cons1)
s.add(cons2)
s.add(cons3)
s.add(cons4)
print s.check()
if s.check()==sat:
	m = s.model()
	print m


