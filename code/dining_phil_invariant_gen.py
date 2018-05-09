from z3 import *
print "Generating global constraints..."

n = 3

fork = [Int("fork%s" % i) for i in range(n)]
fork_p = [Int("fork%s" % i) for i in range(n)]
phil = [Int("phil%s" % i) for i in range(n)]
phil_p = [Int("phil%s" % i ) for i in range(n)]
Init = simplify(And([And(fork[i]==0, phil[i]==0) for i in range(n)]))
print "Init = ", Init

#ring topology implicitly encoded here
trans1 = Or([And(phil[i]=='T', phil_p[i]=='H', fork[i]==fork_p[i]) for i in range(n)])
trans2 = Or([And(phil[i]=='H', fork[i]==0, phil_p[i]=='H', fork_p[i]==1, fork[(i+1)%n]==fork_p[(i+1)%n]) for i in range(n)])
trans3 = Or([And(phil[i]=='H', fork[(i+1)%n]==0, phil_p[i]=='H', fork_p[(i+1)%n]==2, fork[i]==fork_p[i]) for i in range(n)])
trans4 = Or([And(phil[i]=='H', fork[i]==1, fork[(i+1)%n]==2, phil_p[i]=='E', fork_p[i]==1, fork_p[(i+1)%n]==2) for i in range(n)])
trans5 = Or([And(phil[i]=='E', fork_p[i]==0, fork_p[(i+1)%n]==0, phil_p[i]=='T') for i in range(n)])

trans = simplify(Or(trans1, trans2, trans3, trans4, trans5))
print "trans = ", trans
