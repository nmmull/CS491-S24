from  pysat.solvers import Minisat22
from itertools import combinations, product, chain

var = lambda val, x_pos, y_pos: 81 * val + 9 * y_pos + x_pos + 1

pos_vars = lambda row, col: [var(val, row, col) for val in range(9)]
row_vars = lambda val, row: [var(val, x_pos, row) for x_pos in range(9)]
col_vars = lambda val, col: [var(val, col, y_pos) for y_pos in range(9)]
box_vars = lambda val, x, y: [var(val, x * 3 + i, y * 3 + j) for (i, j) in product(range(3), range(3))]

at_least = lambda var_list: [var_list]
at_most = lambda var_list: [[-var_list[i], -var_list[j]] for (i, j) in combinations(range(9), 2)]
exactly = lambda var_list: at_least(var_list) + at_most(var_list)

sudoku_form = list(chain.from_iterable( \
    [exactly(pos_vars(i, j)) for (i, j) in product(range(9), range(9))] + \
    [exactly(row_vars(i, j)) for (i, j) in product(range(9), range(9))] + \
    [exactly(col_vars(i, j)) for (i, j) in product(range(9), range(9))] + \
    [exactly(box_vars(i, j, k)) for (i, j, k) in product(range(9), range(3), range(3))]))

def board_form(b):
    clauses = []
    for (i, j) in product(range(9), range(9)):
        if b[i][j] != 0:
            clauses.append([var(b[i][j] - 1, i, j)])
    return clauses

board = \
    [[0, 0, 1, 0, 0, 0, 0, 0, 8], \
     [0, 0, 0, 0, 6, 0, 0, 5, 0], \
     [0, 6, 0, 0, 0, 0, 0, 1, 3], \
     [0, 2, 0, 0, 0, 3, 0, 0, 0], \
     [8, 1, 0, 4, 0, 0, 0, 0, 9], \
     [0, 0, 0, 7, 0, 0, 5, 4, 0], \
     [0, 0, 0, 0, 0, 0, 3, 0, 0], \
     [0, 9, 0, 0, 4, 0, 0, 0, 0], \
     [0, 0, 0, 9, 7, 1, 0, 6, 0]]

solver = Minisat22()
solver.append_formula(sudoku_form)
solver.append_formula(board_form(board))
solver.solve()
model = solver.get_model()

def from_assignment(a):
    out = [[0 for _ in range(9)] for _ in range(9)]
    for (i, j) in product(range(9), range(9)):
        for val in range(9):
            if a[var(val, i, j) - 1] > 0:
                out[i][j] = val + 1
                break
    return out

def print_board(b):
    for row in b:
        for elem in row:
            if elem != 0:
                print(str(elem) + " ", end="")
            else:
                print("_" + " ", end="")
        print()

print()
print("starting board")
print("==============")

print_board(board)
print()

if model:
    print("solved board")
    print("============")
    print_board(from_assignment(model))
else:
    print("NO SOLUTION")
