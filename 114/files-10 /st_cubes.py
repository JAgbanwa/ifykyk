#!/usr/bin/env python3
"""
st_cubes.py -- dictionary between

    solutions of  x^3 + y^3 + z^3 = 114
and
    rational non-integer (s,t) with  y  a nonzero integer  in

    y^2 = (A s + B t + C)^2 + N(s)/(B t + beta)

No dependencies beyond the standard library.

  ./st_cubes.py from-cubes  X Y Z          -> prints s, t, y and verifies exactly
  ./st_cubes.py to-cubes    as/bs ct/dt yy -> prints the cube triple
  ./st_cubes.py selftest
  ./st_cubes.py scan FILE                  -> reads "SOLUTION k=114 x=.. y=.. z=.. d=.."
                                              lines from search_cubes and converts them
"""
import sys
from fractions import Fraction as F
from math import gcd

A    = 3185268667669143471416768059029076281260064403298624835146634
B    = 353918740852127052379640895447675142362229378144291648349626
C    = 1519831401667421687829458991789157445364256221653691853090595
beta = 176959370426063526189820447723837571181114689072145824174813
nu   = 74604001735631008979979919114739993010174529587863668273099
n3 = 5386255598429912910239991074883103648061323608347515713067104506907275944285878462789841452986266125005845596825628779494465555970916820770687828281560445713580845857529504520594684
n2 = 6812347168386504364564397888712133441306659545486542739467076752649122734543687696820388736586306024705642039157739295712828518798880977420816988175841637415790459974110929417082796
n1 = 2872005922887105612204712888576895642803577224840059660525955764481773178812678494861246411912387442454262975294561586568820236883258414904154274451272523530538639364401666520125108
n0 = 403601373467692408273995159382149494499487848483215368650586145686569090715672337841415767442159797280078496814999716951880794271356612614897783688494744701337220471456567329598609
K  = 114


def rhs(s, t):
    """Exact right-hand side of the posed equation."""
    P = A * s + B * t + C
    return P * P + F(n3 * s**3 + n2 * s**2 + n1 * s + n0, 1) / (B * t + beta)


def to_cubes(s, t, y):
    """(s,t,y) -> (p,q,r).  p^3+q^3+r^3 == 114 iff y^2 == rhs(s,t)."""
    P, D = A * s + B * t + C, B * t + beta
    p, q, r = P + D, -(D + y), y - D
    assert all(v.denominator == 1 for v in (F(p), F(q), F(r))), "non-integral triple"
    return int(p), int(q), int(r)


def from_cubes(x, y_, z):
    """
    (x,y,z) with x^3+y^3+z^3=114 -> (s, t, y).

    Exactly one of the three is even (all-even is impossible since 8 does not
    divide 114); that one plays the role of p, the two odd ones are q and r.
    Swapping q,r only flips the sign of y.
    """
    trip = [x, y_, z]
    ev = [v for v in trip if v % 2 == 0]
    od = [v for v in trip if v % 2 != 0]
    if len(ev) != 1:
        raise ValueError(f"expected exactly one even coordinate, got {trip}")
    p, (q, r) = ev[0], od
    if (q + r) % 2 or (p + q + r) % 6:
        raise ValueError("parity/divisibility failure -- not a valid 114 triple")
    U = -(q + r) // 2
    yv = (r - q) // 2
    X = (p + q + r) // 6
    if U == 0:
        raise ValueError("U = 0: zero denominator (this is the x = -y family)")
    s = F(X - 3 * nu, 3 * beta)
    t = F(U - beta, 2 * beta)
    return s, t, yv


def report(x, y_, z, out=sys.stdout):
    ok_cube = (x**3 + y_**3 + z**3 == K)
    print(f"triple            : ({x}, {y_}, {z})", file=out)
    print(f"x^3+y^3+z^3 == 114: {ok_cube}", file=out)
    if not ok_cube:
        return False
    s, t, yv = from_cubes(x, y_, z)
    a, b = s.numerator, s.denominator
    c, d = t.numerator, t.denominator
    conds = [
        ("y^2 == RHS(s,t) exactly",     rhs(s, t) == F(yv) ** 2),
        ("y is a nonzero integer",      yv != 0),
        ("s is NOT an integer",         b != 1),
        ("t is NOT an integer",         d != 1),
        ("b | 3*beta",                  (3 * beta) % b == 0),
        ("d | 2*beta",                  (2 * beta) % d == 0),
        ("gcd(a,b) == 1",               gcd(a, b) == 1),
        ("gcd(c,d) == 1",               gcd(c, d) == 1),
        ("(a,b) != (c,d)",              (a, b) != (c, d)),
        ("denominator B*t+beta != 0",   B * t + beta != 0),
    ]
    print(f"s = {a}/{b}", file=out)
    print(f"t = {c}/{d}", file=out)
    print(f"y = {yv}", file=out)
    for name, ok in conds:
        print(f"  [{'OK ' if ok else 'FAIL'}] {name}", file=out)
    return all(ok for _, ok in conds)


def selftest():
    import random
    random.seed(1)
    ok = True
    # identity holds for arbitrary (s,t,y): residual is exactly m - 114
    for _ in range(300):
        s = F(random.randint(-10**6, 10**6), random.choice([1, 3, beta, 3 * beta]))
        t = F(random.randint(-10**6, 10**6), random.choice([1, 2, beta, 2 * beta]))
        if 2 * t + 1 == 0:
            continue
        y = F(random.randint(-10**6, 10**6))
        p, q, r = to_cubes(s, t, y)
        D = B * t + beta
        ok &= (p**3 + q**3 + r**3 - K == 6 * D * (rhs(s, t) - y * y))
    print(f"  [{'OK ' if ok else 'BAD'}] forward map residual identity (300 samples)")

    # round trip on synthetic triples (they need not sum to 114)
    ok2 = True
    for _ in range(300):
        p = 2 * random.randint(-10**5, 10**5)
        q = 2 * random.randint(-10**5, 10**5) + 1
        r = 2 * random.randint(-10**5, 10**5) + 1
        if (p + q + r) % 6 or (q + r) == 0:
            continue
        m = p**3 + q**3 + r**3
        U = -(q + r) // 2
        y = (r - q) // 2
        X = (p + q + r) // 6
        s, t = F(X - 3 * nu, 3 * beta), F(U - beta, 2 * beta)
        ok2 &= (6 * (B * t + beta) * (rhs(s, t) - F(y) ** 2) == m - K)
        ok2 &= (sorted(to_cubes(s, t, F(y))) == sorted((p, q, r)))
    print(f"  [{'OK ' if ok2 else 'BAD'}] inverse map + round trip (300 samples)")
    print("  note: no (x,y,z) with x^3+y^3+z^3=114 is known, so the end-to-end")
    print("        path can only be exercised on synthetic triples until one is found.")
    return ok and ok2


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    cmd = sys.argv[1]
    if cmd == 'selftest':
        sys.exit(0 if selftest() else 1)
    elif cmd == 'from-cubes':
        x, y_, z = (int(v) for v in sys.argv[2:5])
        sys.exit(0 if report(x, y_, z) else 1)
    elif cmd == 'to-cubes':
        s, t, y = F(sys.argv[2]), F(sys.argv[3]), F(sys.argv[4])
        print(to_cubes(s, t, y))
    elif cmd == 'scan':
        good = 0
        for line in open(sys.argv[2]):
            if not line.startswith('SOLUTION'):
                continue
            f = dict(w.split('=') for w in line.split()[1:])
            if int(f['k']) != K:
                continue
            print('-' * 70)
            if report(int(f['x']), int(f['y']), int(f['z'])):
                good += 1
        print(f"\n{good} verified (s,t) solution(s)")
    else:
        print(__doc__)
        sys.exit(1)
