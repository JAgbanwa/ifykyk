#!/usr/bin/env python3
"""
reduction.py -- proves that the posed equation

    y^2 = (A s + B t + C)^2 + N(s)/D(t),      N(s) = n3 s^3 + n2 s^2 + n1 s + n0
                                              D(t) = B t + beta

is a disguise for the sum of three cubes  x^3 + y^3 + z^3 = 114.

Run:  python3 reduction.py          (needs sympy for the symbolic identities)
"""
from fractions import Fraction as F

# ------------------------------------------------------------------ constants
A    = 3185268667669143471416768059029076281260064403298624835146634
B    = 353918740852127052379640895447675142362229378144291648349626
C    = 1519831401667421687829458991789157445364256221653691853090595
beta = 176959370426063526189820447723837571181114689072145824174813   # = B/2, prime
nu   = 74604001735631008979979919114739993010174529587863668273099

n3 = 5386255598429912910239991074883103648061323608347515713067104506907275944285878462789841452986266125005845596825628779494465555970916820770687828281560445713580845857529504520594684
n2 = 6812347168386504364564397888712133441306659545486542739467076752649122734543687696820388736586306024705642039157739295712828518798880977420816988175841637415790459974110929417082796
n1 = 2872005922887105612204712888576895642803577224840059660525955764481773178812678494861246411912387442454262975294561586568820236883258414904154274451272523530538639364401666520125108
n0 = 403601373467692408273995159382149494499487848483215368650586145686569090715672337841415767442159797280078496814999716951880794271356612614897783688494744701337220471456567329598609

Ms = 530878111278190578569461343171512713543344067216437472524439   # = 3*beta
Mt = B                                                              # = 2*beta

K = 114


def y2(s, t):
    """The right-hand side of the posed equation, exactly, as a Fraction."""
    P = A * s + B * t + C
    return P * P + F(n3 * s**3 + n2 * s**2 + n1 * s + n0, 1) / (B * t + beta)


def main():
    from sympy import symbols, expand, isprime, Rational

    print("=" * 74)
    print("STRUCTURE OF THE CONSTANTS")
    print("=" * 74)
    checks = [
        ("beta is prime",                      isprime(beta)),
        ("B  == 2*beta",                       B == 2 * beta),
        ("A  == 18*beta",                      A == 18 * beta),
        ("Ms == 3*beta  (bound on denom of s)", Ms == 3 * beta),
        ("Mt == 2*beta  (bound on denom of t)", Mt == 2 * beta),
        ("C - beta == 18*nu",                  C - beta == 18 * nu),
        ("n3 == 972*beta^3 == 3*A^2*beta",     n3 == 972 * beta**3 == 3 * A * A * beta),
    ]
    for name, ok in checks:
        print(f"  [{'OK ' if ok else 'BAD'}] {name}")

    print()
    print("  => the constraints  b | 3*beta  and  d | 2*beta  say exactly:")
    print("       X := 3*beta*s + 3*nu   is an integer")
    print("       U := beta*(2t+1)       is an integer")
    print("     Since beta is prime the only denominators available are")
    print("       b in {1,3,beta,3*beta},  d in {1,2,beta,2*beta}.")

    print()
    print("=" * 74)
    print("SYMBOLIC IDENTITIES")
    print("=" * 74)
    s, t, yv = symbols('s t y')

    Nx = n3 * s**3 + n2 * s**2 + n1 * s + n0
    id1 = expand(6 * Nx - ((A * s + C - beta)**3 - K))
    print(f"  [{'OK ' if id1 == 0 else 'BAD'}] N(s) == ((A*s + C - beta)^3 - 114)/6")

    P = A * s + B * t + C
    D = B * t + beta
    p, q, r = P + D, -(D + yv), yv - D
    id2 = expand(p**3 + q**3 + r**3 - K - 6 * (D * P**2 + Nx - D * yv**2))
    print(f"  [{'OK ' if id2 == 0 else 'BAD'}] (P+D)^3 + (-(D+y))^3 + (y-D)^3 - 114"
          " == 6*D*(P^2 + N/D - y^2)")

    X, U = symbols('X U')
    lhs = expand(((6 * X + U)**2) * U + 36 * X**3 - K // 6 * 0 - 19)     # y^2*U form
    rhs = expand(36 * X**3 + 36 * U * X**2 + 12 * U**2 * X + U**3 - 19)
    print(f"  [{'OK ' if expand(lhs - rhs) == 0 else 'BAD'}] "
          "(6X+U)^2*U + 36X^3 - 19 == 36X^3+36UX^2+12U^2X+U^3-19")

    print()
    print("  Therefore, with  X = 3*beta*s + 3*nu  and  U = beta*(2t+1):")
    print("      y^2 = (6X + U)^2 + (36 X^3 - 19)/U")
    print("  and equivalently, with  p = P+D,  q = -(D+y),  r = y-D:")
    print("      y^2 = P^2 + N(s)/D   <=>   p^3 + q^3 + r^3 = 114")

    print()
    print("=" * 74)
    print("NUMERIC SPOT CHECKS")
    print("=" * 74)
    import random
    random.seed(7)
    ok = True
    for _ in range(200):
        sv = F(random.randint(-500, 500), random.choice([1, 3, beta, 3 * beta]))
        tv = F(random.randint(-500, 500), random.choice([1, 2, beta, 2 * beta]))
        if 2 * tv + 1 == 0:
            continue
        yq = F(random.randint(-500, 500))
        Pv, Dv = A * sv + B * tv + C, B * tv + beta
        pv, qv, rv = Pv + Dv, -(Dv + yq), yq - Dv
        # residual identity must hold for ARBITRARY y, not just solutions
        ok &= (pv**3 + qv**3 + rv**3 - K == 6 * Dv * (y2(sv, tv) - yq**2))
        # clean (X,U) form
        Xv, Uv = 3 * beta * sv + 3 * nu, beta * (2 * tv + 1)
        ok &= (y2(sv, tv) == (6 * Xv + Uv)**2 + F(36 * Xv**3 - 19, 1) / Uv)
    print(f"  [{'OK ' if ok else 'BAD'}] 200 random (s,t,y) satisfy both identities exactly")


if __name__ == '__main__':
    main()
