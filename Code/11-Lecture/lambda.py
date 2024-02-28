
tru = lambda x: lambda y: x
fls = lambda x: lambda y: y

def to_bool(b):
    return lambda b: b(True)(False)

notb = lambda b: lambda x: lambda y: b(y)(x)
orb = lambda p: lambda q: lambda x: lambda y: p(x)(q(x)(y))
andb = lambda p: lambda q: notb(orb(notb(p))(notb(q)))
impliesb = lambda p: lambda q: orb(notb(p))(q)

zero = lambda s: lambda z: z
one = lambda s: lambda z: s(z)
two = lambda s: lambda z: s(s(z))
suc = lambda n: lambda s: lambda z: n(s)(s(z))

add = lambda m: lambda n: lambda s: lambda z: m(s)(n(s)(z))

plus_one = lambda x: 1 + x
to_int = lambda n: n(plus_one)(0)

def from_int(n):
    assert(n >= 0)
    if n == 0: return zero
    return suc (to_nat(n - 1))
