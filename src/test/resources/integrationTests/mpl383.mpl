with(ArrayTools):
# The row vector v denotes the indicator vector of the (singleton)
# set of initial states.
v := Vector[row]([1,0,0,0,0]);

# In what follows, the M_i_x, for a free variable i and a value x, denotes
# an incidence matrix of the underlying graph of (the automaton of)
# the predicate in the query.
# For every pair of states p and q, the entry M_i_x[p][q] denotes the number of
# transitions with i=x from p to q.

M_n23_0 := Matrix([[1,0,0,0,0],
[0,0,1,0,0],
[0,0,0,0,0],
[0,0,0,0,1],
[0,0,0,0,0]]);

M_n23_1 := Matrix([[0,1,0,0,0],
[0,0,0,0,0],
[0,0,0,1,0],
[0,0,0,0,0],
[0,0,0,0,0]]);

# The column vector w denotes the indicator vector of the
# set of final states.
w := Vector[column]([0,0,0,0,1]);

for i from 1 to Size(v)[2] do v := v.M_n23_0; od; #fix up v by multiplying
