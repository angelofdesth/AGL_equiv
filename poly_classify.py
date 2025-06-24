from sage.all import *
from collections import defaultdict
# from itertools import groupby
from functools import cache

def gen_polys(R, deg):
    """
    Generates all monic polynomials in R with no constant term of degree deg.

    Arguments:
        R (PolynomialRing): A polynomial ring over a finite field.
        deg (Integer): The degree of the polynomials to generate.

    Returns:
        Generator[Polynomial]: Polynomials of the form x^deg + ... + cx.
    """
    x = R.gen()
    return (x**deg + x * poly for poly in R.polynomials(max_degree=deg-2))

def num_equiv_classes(p, r, n): 
    """
    Calculate the number of AGL-equivalence classes of polynomials of degree r
    over the finite field with p^r elements.

    Arguments:
        p (Integer): The characteristic of the finite field.
        r (Integer): The degree of the finite field over Z/pZ.
        n (Integer): The degree of polynomials to consider.

    Returns:
        Integer: The number of equivalence classes.
    """
    q = p**r

    if n % p == 0:
        c = 1 - q**(n-2) + q**(n//p - 1)
    elif n == 1:
        c = 1
    else:
        c = 1 - q**(n-2)
    
    return sum(euler_phi(d)*(q**(ceil(n/d)-1)-1) for d in divisors(q-1) if d < n) // (q-1) + c

def weight(n, p):
    """
    Calculate the p-weight of an integer n.

    Arguments:
        n (Integer): An integer to compute the p-weight of.
        p (Integer): A prime number.

    Returns:
        Integer: The p-weight of n.
    """
    w = 0
    while n > 0:
        w += n % p
        n //= p
    return w

def wpart(f, w, p):
    """
    Extracts the terms in f of p-weight w.

    Arguments:
        f (Polynomial): The polynomial to extract terms from.
        w (Integer): The specified p-weight.
        p (Integer): A prime number.

    Returns:
        Polynomial: The part of f with p-weight w.
    """
    x = f.variables()[0]
    return sum(c * x**i for i, c in enumerate(f) if weight(i, p) == w)

def wpart_ge(f, w, p):
    """
    Extracts the terms in f of p-weight >= w.

    Arguments:
        f (Polynomial): The polynomial to extract terms from.
        w (Integer): The specified p-weight.
        p (Integer): A prime number.

    Returns:
        Polynomial: The part of f with p-weight >= w.
    """
    x = f.variables()[0]
    return sum(c * x**i for i, c in enumerate(f) if weight(i, p) >= w)

def dpart(f, d):
    x = f.variables()[0]
    return f[d] * x**d

def dpart_ge(f, d):
    x = f.variables()[0]
    R = f.parent()
    return R(f[d:]) * x**d

def pdeg(f, p):
    """
    Computes the p-weight degree of a polynomial f.

    Arguments:
        f (Polynomial): The polynomial to compute the p-weight degree of.
        p (Integer): A prime number.

    Returns:
        Polynomial: The part of f with p-weight >= w.
    """
    return max((i for (i, c) in enumerate(f) if c != Integer(0)), key=lambda x: (weight(x, p), x))

AGL = []

def initialize_AGL(R):
    """
    Initializes the global AGL variable to AGL(1, F), where F is the base
    field of the polynomial ring R. Equivalently, initializes AGL to a list
    containing the polynomials in R of degree 1.

    The AGL list is stored globally for efficiency across multiple calls
    to the function canonical_form().

    Arguments:
        R (PolynomialRing): A polynomial ring over a field.

    Returns:
        None (but modifies the global AGL variable).
    """
    global AGL
    x = R.gen()
    F = R.base_ring()
    AGL = [a*x + b for a in F if a != F(0) for b in F]

def canonical_form(f, return_elements=False):
    """
    Computes the canonical form of a polynomial f under AGL-equivalence.

    Arguments:
        f (Polynomial): A polynomial over a finite field.

    Returns:
        Polynomial: The canonical form of f.
        Set[Polynomial]: AGL elements to bring f to its canonical form.
    """
    p = f.base_ring().characteristic()
    d = pdeg(f, p)
    f /= f[d]
    f -= f[0]
    K = weight(d, p)

    form = Integer(0)
    f_partial = Integer(0)
    f_parts = [wpart(f, i, p) for i in range(K + 1)]

    candidates = AGL
    for k in range(K, 0, -1):
        f_partial += f_parts[k]
        g_options = defaultdict(list)
        for poly in candidates:
            g_options[wpart(poly[1]**(-d) * f_partial(poly), k, p)].append(poly)
        maximal = min(g_options)
        form += maximal
        candidates = g_options[maximal]
        print(candidates)
    return form if not return_elements else (form, candidates)

@cache
def coset_representatives(l, prim):
    return set(prim**i for i in range(l))

def continue_form(f, n, i, prim):
    if i == 0:
        return

    d = f.degree()
    x = f.parent().gen()
    q = len(f.base_ring())

    if n is None:
        n = gcd([d - j for j, c in enumerate(f) if c != Integer(0)] + [q - 1])

    l = gcd((q - 1) // n * (d - i), q - 1)
    reps = coset_representatives(l, prim)
    forms = set((f + c * x**i, gcd(n, d - i)) for c in reps) | { (f, n) }

    global canonical_forms, should_print_progress
    canonical_forms |= set(form[0] for form in forms)
    if should_print_progress:
        print(f"number of canonical forms found: {len(canonical_forms)}", end="\r")
    
    for form in forms:
        continue_form(form[0], form[1], i - 1, prim)

def start_form(f, n, i, fixer, prim):
    if i == 0:
        return
    elif set(a[0] for a in fixer) == { 0 }:
        continue_form(f, None, i, prim)
    else:
        x = f.parent().gen()
        F = f.base_ring()
        d = f.degree()

        polys = set(a*(x**i) for a in F)
        reps = set()
        while len(polys) > 0:
            g = polys.pop()
            orbit = set(dpart(alpha[1]**(-d) * f(alpha), i) + alpha[1]**(-d) * g(alpha[1]*x) for alpha in fixer)
            rep = min(orbit)
            reps.add(rep)
            polys -= orbit

        global canonical_forms, should_print_progress
        canonical_forms |= set(f + rep for rep in reps)
        if should_print_progress:
            print(f"number of canonical forms found: {len(canonical_forms)}", end="\r")

        for rep in reps:
            start_form(f + rep, n, i - 1, set(alpha for alpha in fixer if dpart(alpha[1]**(-d) * (f + rep)(alpha), i) == rep), prim)

canonical_forms = set()
should_print_progress = False

def enumerate_canonical_forms(deg, R, print_progress=False):
    x = R.gen()
    F = R.base_ring()
    prim = F.primitive_element()
    q = len(F)

    global canonical_forms, should_print_progress
    canonical_forms = { x**deg }
    should_print_progress = print_progress
    if should_print_progress:
        print(f"number of canonical forms found: {len(canonical_forms)}", end="\r")

    start_form(x**deg, q - 1, deg - 1, AGL, prim)
    if should_print_progress:
        print()  # move past carriage return
    return canonical_forms

def differential_uniformity(f, upper_bound=Infinity):
    """
    Computes the differential uniformity of a polynomial f.

    Arguments:
        f (Polynomial): A polynomial over a finite field.

    Returns:
        int: The differential uniformity of f.
    """
    F = f.base_ring()
    maximum = Integer(0)
    for a in F:
        if a != 0:
            counts = defaultdict(Integer)
            for x in F:
                b = f(x + a) - f(x)
                counts[b] += 1
            maximum = max(maximum, max(counts.values()))
            if maximum > upper_bound:
                return maximum
    return maximum
