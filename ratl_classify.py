from sage.all import *

from collections import defaultdict
from copy import deepcopy
from pprint import pprint

PGL_elems = []

def initialize_PGL(R):
    global PGL_elems
    x = R.gen()
    F = R.base_ring()
    PGL_elems = [(x + b)/(c*x + d) for b in F for c in F for d in F if d - b*c != F(0)] + [F(1) / (c*x + d) for c in F for d in F if c != F(0)]

deg3ratls = set()

def initialize_deg3ratls(R, deg3only=False):
    def check(s, t):
        poly = x**Integer(4) - Integer(2)*x**Integer(3) - s*x**Integer(2) - Integer(2)*t*x + t
        return not any(root[Integer(0)]**Integer(3) != -t for root in poly.roots())

    global deg3ratls
    x = R.gen()
    F = R.base_ring()
    
    if deg3only:
        deg3ratls = set((x**Integer(3) + s*x + t) / (x * (x - Integer(1))) for s in F for t in F if t != Integer(0) and Integer(1) + s + t != Integer(0) and check(s, t))
    else:
        deg3ratls = set(f / (x**Integer(3) + g) for f in R.polynomials(max_degree=Integer(2)) for g in R.polynomials(max_degree=Integer(2)) if gcd(f, x**Integer(3) + g) == Integer(1))

def num_ratl_equiv_classes(p, q, n): 
    def A(q, n): 
        a = sum([euler_phi(d) * (q**(Integer(2)*n/d-Integer(2)) + (d-Integer(1))*(q**(Integer(2)*n/d)-Integer(1))/(q+Integer(1))) for d in divisors(gcd(q-Integer(1), n)) if d > Integer(1)])
        b = sum([euler_phi(d) * (q**(Integer(2)*floor(n/d)+Integer(1)) + Integer(1))/(q+Integer(1)) for d in divisors(q-Integer(1)) if (d not in divisors(n))])
        return a + b 

    def B(q, n):
        a = sum([euler_phi(d) * (q**(Integer(2)*n/d-Integer(2)) + (q+Integer(1)) * (q**(Integer(2)*n/d) - (-Integer(1))**(n/d))/(q**Integer(2) + Integer(1))) for d in divisors(gcd((q+Integer(1)), n)) if d % Integer(2) == Integer(0)])
        b = sum([euler_phi(d) * q**(Integer(2)*n/d-Integer(2)) for d in divisors(gcd((q+Integer(1)), n)) if (d % Integer(2) == Integer(1) and d > Integer(1))])
        #  c = Integer(1)/((q+Integer(1))*(q**Integer(2)+Integer(1))) * sum([euler_phi(d) * ((Integer(1)+(-Integer(1))**(n//d))/Integer(2) * (Integer(1)+q)**Integer(2) + q*(q**(Integer(2) * n//d + Integer(2)) -Integer(1))) for d in divisors(q+Integer(1)) if d not in divisors(n)])
        d = Integer(1)/(q**Integer(2) + Integer(1)) * sum([euler_phi(d) * ((-Integer(1))**(n//d) * (Integer(1)+q) + q**(Integer(2) * (n//d) + Integer(1)) * (q-Integer(1))) for d in divisors(q+Integer(1)) if d in divisors(q+Integer(1)) if d not in divisors(n)])
        # print("B terms are", a, b, c, d)
        return a + b + d

    def C(q, n):
        if n % p == Integer(0):
            return q**(Integer(2)*n/p-Integer(1)) 
        elif n == Integer(1): 
            return Integer(1) 
        elif n % p == Integer(1): 
            return q**(Integer(2)*(n-Integer(1))/p-Integer(1)) * (q-Integer(1)) 
        else: 
            return Integer(0)

    # print("Each components is", A(q, n), B(q, n), C(q, n))
    
    return (q**(Integer(2)*n-Integer(3)))/(q**Integer(2)-Integer(1)) + Integer(1)/(Integer(2)*(q-Integer(1))) * A(q, n) + Integer(1)/(Integer(2)*(q+Integer(1))) * B(q, n) + Integer(1)/q * C(q,n)

def value_frequency(f, print_preimages=False):
    R = f.numerator().parent()
    F = f.base_ring()

    preimages = defaultdict(set)
    for a in F:
        try:
            preimages[f(a)].add(a)
        except ZeroDivisionError:
            preimages["infinity"].add(a)

    # handle f(infinity)
    P = R(f.numerator())
    Q = R(f.denominator())
    if P.degree() > Q.degree():
        preimages["infinity"].add("infinity")
    elif P.degree() < Q.degree():
        preimages[Integer(0)].add("infinity")
    else:
        c = P.leading_coefficient() / Q.leading_coefficient()
        preimages[c].add("infinity")

    if print_preimages:
        pprint(preimages)
    return sorted([len(preimage) for preimage in preimages.values()])

def ratl_equiv(f, g):
    """returns whether or not f is PGL-equiv to g""" 
    if value_frequency(f) != value_frequency(g): 
        return (False,) 

    if not PGL_elems:
        initialize_PGL(f.parent())

    for alpha in PGL_elems:
        for beta in PGL_elems: 
            try:
                if alpha(f(beta)) == g: 
                    return (True, alpha, beta)
            except ZeroDivisionError: 
                continue
    return (False,)

def get_orbit_case3(f):
    F = f.base_ring()
    x = f.parent().gen()

    s = f.numerator()[Integer(1)]
    t = f.numerator()[Integer(0)]

    preimages = defaultdict(set)
    for a in F:
        if a != Integer(0) and a != Integer(1):
            preimages[f(a)].add(a)
    
    pairs = { (s, t) }
    for preimage in preimages.values():
        if len(preimage) == Integer(3):
            u, v, w = preimage
            s_prime = (u**Integer(2)*(-Integer(1) + v)*v*(u - w) - u*(-Integer(1) + v)*v**Integer(2)*(u - w) + u*(u - v)*v**Integer(2)*(-Integer(1) + w) + (Integer(1) - v)*v**Integer(2)*(u - w)*w + (-Integer(1) + v)*v**Integer(2)*(u - w)*w - u**Integer(2)*(u - v)*(-Integer(1) + w)*w + v**Integer(2)*(-u + v)*(-Integer(1) + w)*w - u*(-Integer(1) + v)*(u - w)*w**Integer(2) + (-Integer(1) + v)*v*(u - w)*w**Integer(2) + u*(u - v)*(-Integer(1) + w)*w**Integer(2) + (u - v)*v*(-Integer(1) + w)*w**Integer(2) + v*(-u + v)*(-Integer(1) + w)*w**Integer(2)) / (u**Integer(2)*(u - v)*(-Integer(1) + w)*w - Integer(2)*u*(u - v)*v*(-Integer(1) + w)*w + (u - v)*v**Integer(2)*(-Integer(1) + w)*w)
            t_prime = (-(u**Integer(2)*(-Integer(1) + v)*v*(u - w)) + Integer(2)*u*(-Integer(1) + v)*v*(u - w)*w - (-Integer(1) + v)*v*(u - w)*w**Integer(2))/(u**Integer(2)*(u - v)*(-Integer(1) + w)*w - Integer(2)*u*(u - v)*v*(-Integer(1) + w)*w + (u - v)*v**Integer(2)*(-Integer(1) + w)*w)
            pairs.add((s_prime, t_prime))

    # print(pairs)
    
    def get(s, t):
        return {
            (s, t),
            (s / t, Integer(1) / t),
            (s, -Integer(1) - s - t),
            (s / t, -(Integer(1) + s + t) / t),
            (-s / (Integer(1) + s + t), -Integer(1) / (Integer(1) + s + t)),
            (-s / (Integer(1) + s + t), -t / (Integer(1) + s + t))
        }
    
    pairs = set.union(*(get(s, t) for s, t in pairs))
    return set((x**Integer(3) + s*x + t) / (x**Integer(2) - x) for s, t in pairs)

def ratl_equiv_classes_case3(R, print_progress=False):
    if not deg3ratls:
        initialize_deg3ratls(R, deg3only=True)

    classes = defaultdict(set)
    total = len(deg3ratls)
    candidates = deepcopy(deg3ratls)

    if print_progress:
        print(f"{total - len(candidates)} out of {total} done", end="\r")

    while candidates:
        f = candidates.pop()
        orbit = get_orbit_case3(f)
        classes[f] = orbit
        candidates -= orbit
        
        if print_progress:
            print(f"{total - len(candidates)} out of {total} done", end="\r")

    if print_progress:
        print()
    return classes

def qnr(F): 
    return (set(F) - { b**2 for b in F }).pop()

def ratl_equiv_classes_case1(R):
    F = R.base_ring()
    q = len(F)
    x = R.gen()

    if q % Integer(6) == Integer(1): 
        b = -qnr(F) 
        a = F(Integer(9))/F(b) 
        return {(x**Integer(3) + a*x)/(b*x**Integer(2)+Integer(1))}
    elif q % Integer(6) == Integer(3): 
        a = -qnr(F) 
        return {x**Integer(3), x**Integer(3) + a*x}
    elif q % Integer(6) == Integer(4): 
        raise NotImplementedError
    else: 
        return {x**Integer(3)}

def ratl_equiv_classes_case2(R):
    F = R.base_ring()
    q = len(F)
    x = R.gen()

    out = set() 
    if q % Integer(3) == Integer(1): 
        gamma = F.primitive_element()
        C = [gamma**i for i in range(Integer(3))]
    else: 
        C = [Integer(1)]
    for t in C: 
        out.add((x**Integer(3) + t)/x)
    
    for t in F: 
        if t != Integer(0): 
            out.add((x**Integer(3) + x**Integer(2) + t)/x)
    
    return out 

def ratl_equiv_classes(R):
    case1 = ratl_equiv_classes_case1(R)
    case2 = ratl_equiv_classes_case2(R) 
    case3 = ratl_equiv_classes_case3(R).keys()
    return case1 | case2 | case3

def small_ramifications(R): 
    x = R.gen()
    sigma = qnr(R.base_ring())
    return {x**Integer(3), x**Integer(3) - Integer(3)*x, (x**Integer(3) + Integer(3)*sigma*x)/(Integer(3)*x**Integer(2)+sigma), x**Integer(3) - Integer(3)*sigma*x}

def ram_case(f): 
    df = derivative(f).numerator()

    F = f.parent().base_ring()
    if df.discriminant() == F(0):
        return Integer(0)

    deg2termcounter = Integer(0) 
    for term in list(factor(df)): 
        deg = term[Integer(0)].degree()
        if deg == Integer(3): 
            return Integer(3)
        elif deg == Integer(4): 
            return Integer(5) 
        elif deg == Integer(2): 
            deg2termcounter += term[Integer(1)]
    if deg2termcounter == Integer(1): 
        return Integer(2) 
    elif deg2termcounter == Integer(2): 
        return Integer(4) 
    else: 
        return Integer(1) 

def ram4Classes(R): 
    cases = {Integer(1): Integer(0), Integer(2): Integer(0), Integer(3): Integer(0), Integer(4): Integer(0), Integer(5): Integer(0)}
    equivs = ratl_equiv_classes(R) 
    for f in equivs: 
        cases[ram_case(f)] += Integer(1) 

    for f in small_ramifications(R): 
        cases[ram_case(f)] -= Integer(1)
    return cases
