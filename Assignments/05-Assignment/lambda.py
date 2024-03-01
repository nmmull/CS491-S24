"""Assignment 5

In this assignment you will be encoding data in the lambda calculus.
The top of the file contains some encodings we saw in lecture.

Your task is to fill in the TODO items below for encoding lists.

"""

# we encode booleans as functions which "choose" one of two values
tru = lambda x: lambda y: x
fls = lambda x: lambda y: y

# this recovers a Python Bool from our lambda calculus boolean
def to_bool(b):
    return lambda b: b(True)(False)

# a small collection of functions on booleans
notb = lambda b: lambda x: lambda y: b(y)(x)
orb = lambda p: lambda q: lambda x: lambda y: p(x)(q(x)(y))
andb = lambda p: lambda q: notb(orb(notb(p))(notb(q)))
impliesb = lambda p: lambda q: orb(notb(p))(q)

# we encode natural numbers as "iterators", where the number `n` is
# represented by the function which applies a function `s` a total of
# `n` times on a given value `z`
zero = lambda s: lambda z: z
one = lambda s: lambda z: s(z)
two = lambda s: lambda z: s(s(z))
suc = lambda n: lambda s: lambda z: s(n(s)(z))

example = lambda s: lambda z: s(s(s(s(s(z)))))
                            # 1+1+1+1+1+0

# The add function uses the "iterator" for `m` to apply the `s` a total of `m` times to the value `n(s)(z)`,
add = lambda m: lambda n: lambda s: lambda z: m(s)(n(s)(z))

# conversion functions to and from Python Ints
def to_int(n):
    def plus_one(x):
        return 1 + x
    return n(plus_one)(0)

def of_int(n):
    assert(n >= 0)
    if n == 0: return zero
    return suc(of_int(n - 1))


assert(to_int(example) == 5)
assert(to_int(add(of_int(2))(of_int(3))) == 5)

# we also represent lists as iterators, but with an additional
# argument to the function `f` which represents the value at the given
# index.  Note that `cons` is just a FOLD.
nil = lambda f: lambda x: x
single = lambda y: lambda f: lambda x: f(y)(x)
cons = lambda y: lambda ys: lambda f: lambda x: f(y)(ys(f)(x))

example = lambda f: lambda x: f(zero)(f(one)(f(two)(x)))
                              # 0 ::    1 ::   2 :: []

# This function repeats an element by using the "iterator" represnted
# by `n`.
repeat = lambda m: lambda n: n(lambda l: cons(m)(l))(nil)

# conversion functions to and from Python Arrays.  Note that we have
# to encode and decode the value in a list
def of_list(l, encode):
    if len(l) == 0:
        return nil
    return cons(encode(l[0]))(of_list(l[1:], encode))

def to_list(l, decode):
    app = lambda x: lambda xs: [decode(x)] + xs
    return l(app)([])

def of_int_list(l):
    return of_list(l, of_int)

def to_int_list(l):
    return to_list(l, to_int)

# TODO: Fill in the lambda term for appending two lists. Take `add`
# above as inspiration.  Think about how to use the "iterator" for `l`
# to construct `l + r`.
app = lambda l: lambda r: None

# TODO: Fill in the lambda term for reversing a list.
rev = lambda l: None

# TODO: Fill in the lambda term for getting the head of a list
hd = lambda l: None

down = lambda n: n(lambda l: cons(suc(hd(l)))(l))(single(zero))
upto = lambda n: rev(down(n))

# Tests
seven = of_int(7)
l1 = of_int_list([0,1,2,3])
l2 = of_int_list([4,5,6,7])
l3 = upto(seven)
l4 = down(seven)

# UNCOMMENT THESE TESTS AS YOU COMPLETE THE ABOVE TODO ITEMS
# assert(to_int_list(example) == [0,1,2])
# assert(to_int_list(app(l1)(l2)) == [0,1,2,3,4,5,6,7])
# assert(to_int_list(rev(l1)) == [3,2,1,0])
# assert(to_int(hd(l1)) == 0)
# assert(to_int(hd(l2)) == 4)
# assert(to_int_list(l3) == to_int_list(app(l1)(l2)))
# assert(to_int_list(l4) == to_int_list(rev(app(l1)(l2))))
# assert(to_int_list(rev(l3)) == to_int_list(l4))
