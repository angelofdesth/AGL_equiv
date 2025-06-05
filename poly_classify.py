from sage.all import *
from collections import defaultdict

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
    return (x**deg + x * poly for poly in R.polynomials(max_degree=deg-Integer(2)))

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

    if p % n == Integer(0):
        c = Integer(1) - q**(n-Integer(2)) + q**(n/p - Integer(1))
    elif n == Integer(1):
        c = Integer(1)
    else:
        c = Integer(1) - q**(n-Integer(2))
    
    return Integer(1)/(q-Integer(1)) * sum(euler_phi(d)*(q**(ceil(n/d)-Integer(1))-Integer(1)) for d in divisors(q-Integer(1)) if d < n) + c

def weight(n, p):
    """
    Calculate the p-weight of an integer n.

    Arguments:
        n (Integer): An integer to compute the p-weight of.
        p (Integer): A prime number.

    Returns:
        Integer: The p-weight of n.
    """
    w = Integer(0)
    while n > Integer(0):
        w += n % p
        n //= p
    return w

def part(f, w, p):
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

def part_ge(f, w, p):
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

AGL = None

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

def canonical_form(f):
    """
    Computes the canonical form of a polynomial f under AGL-equivalence.

    Arguments:
        f (Polynomial): A polynomial over a finite field.

    Returns:
        Polynomial: The canonical form of f.
    """
    p = f.base_ring().characteristic()
    d = pdeg(f, p)
    f /= f[d]
    f -= f[Integer(0)]
    K = weight(d, p)

    form = Integer(0)
    f_partial = Integer(0)
    f_parts = [part(f, i, p) for i in range(K + Integer(1))]

    candidates = AGL
    for k in range(K, Integer(0), -Integer(1)):
        f_partial += f_parts[k]
        g_options = defaultdict(list)
        for poly in candidates:
            g_options[part(poly[Integer(1)]**(-d) * f_partial(poly), k, p)].append(poly)
        maximal = min(g_options)
        form += maximal
        candidates = g_options[maximal]
    return form
