from sys import argv
from math import sqrt
from pysat.solvers import Solver

""" Pythagorean triples

In this assignment, you will be using a SAT solver to find partial
solutions to the Boolean Pythagorean Triples Problem.

A PYTHAGOREAN TRIPLE is a group of three positive integers (i, j, k)
such that

  i * i + j * j = k * k.

The BOOLEAN PYTHAGOREAN TRIPLES PROBLEM is the following: is it
possible to color every positive integer so that no Pythagorean triple
is colored the same color? For example, if 3 is colored red and 4 is
red, then 5 must be colored blue.

This problem was solved in 2016 by a massively parallel SAT solver
running on a super computer: there is no coloring for the first 7825
positive integers.  We can get surprisingly close to this value
with a run-of-the-mill solver.

Tasks
-----

1. Install pysat.

2. Fill in the following code so that it constructs a formula which
represents: there is a coloring of 1 through n, such that no
Pythagorean triple is monochromatic.

3. Write a simple function that verifies the coloring given by a
satisfying assignment does not color any Pythagorean triples the same
color.

4. Solve the case of n = 6000 and report how long it took.  (Try
experimenting with larger values to get a sense of how the running
time scales after this.)

"""

try:
    n = int(argv[1])
    assert(n > 0)
except:
    print("USAGE: python trip.py pos_int")
    exit(1)

s = Solver(use_timer=True)

print("Building formula...")
# TODO: add clauses to s using s.add_clause([...])

print("Solving formula...")
sat = s.solve()
print("Satisfiable: " + str(sat))
print('Solving time: {0:.2f}s'.format(s.time()))
a = s.get_model()

def check_assignment(m):
    # TODO: fill in this function
    return True

if sat:
    print("Verifying satisfying assignment...")
    assert(check_assignment(a))

# Running time (n = 6000): TODO: fill in this value
