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

#Init(pc, lfork, rfork) iff pc==T, lfork==rfork==unowned
Init = Function('Init', State, Fork, Fork, BoolSort())
InitCons1 = ForAll([pc, lfork, rfork], Implies(Init(pc, lfork, rfork), And(pc==State.T, lfork==Fork.unowned, rfork==Fork.unowned)))
InitCons2 = ForAll([pc, lfork, rfork], Implies(And(pc==State.T, lfork==Fork.unowned, rfork==Fork.unowned), Init(pc, lfork, rfork)))
InitCons = And(InitCons1, InitCons2)

#Bad(pc, lfork, rfork) iff pc==E and (lfork!=ccw or rfork!=cw)
Bad = Function('Bad', State, Fork, Fork, BoolSort())
BadCons1 = ForAll([pc, lfork, rfork], Implies(Bad(pc, lfork, rfork), And(pc==State.E, Or(lfork!=Fork.ccw, rfork!=Fork.cw))))
BadCons2 = ForAll([pc, lfork, rfork], Implies(And(pc==State.E, Or(lfork!=Fork.ccw, rfork!=Fork.cw)), Bad(pc, lfork, rfork)))
BadCons = And(BadCons1, BadCons2)

#T(pc, lfork, rfork, pc_p, lfork_p, rfork_p) defined by OR'ing each transition, then saying T(stuff) iff t, the large or
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

SystemCons = [InitCons, BadCons, tCons]



Inv = Function('Inv', State, Fork, Fork, BoolSort())
cons1 = ForAll([pc, lfork, rfork], Implies(Init(pc, lfork, rfork), Inv(pc, lfork, rfork)))
cons2 = ForAll([pc, lfork, rfork, pc_p, lfork_p, rfork_p], Implies(And(Inv(pc, lfork, rfork), T(pc, lfork, rfork, pc_p, lfork_p, rfork_p)), Inv(pc_p, lfork_p, rfork_p)))
cons3 = ForAll([pc, lfork, rfork, lfork_p, rfork_p, pc_int, lfork_int, rfork_int, pc_int_p, lfork_int_p, rfork_int_p], Implies( \
And( \
Inv(pc, lfork, rfork), \
Inv(pc_int, lfork_int, rfork_int), \
T(pc_int,lfork_int,rfork_int, pc_int_p, lfork_int_p, rfork_int_p), \
Or( \
And(lfork==rfork_int, lfork_p==rfork_int_p, rfork==rfork_p), \
And(rfork==rfork_int, rfork_p==rfork_int_p, lfork==lfork_p) \
) \
) \
, \
Inv(pc, lfork_p, rfork_p \
)) \
)
#this last paren is unexplained, debug later
cons4 = ForAll([pc, lfork, rfork], Implies(Inv(pc, lfork, rfork), Not(Bad(pc, lfork, rfork))))


s = Solver()
s.add(SystemCons)
s.add(cons1)
s.add(cons2)
s.add(cons3)
s.add(cons4)
m = s.model()
print "x = %s" % m[x]



