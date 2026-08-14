#!/usr/bin/env python3
"""
degenerate.py -- the cases the divisor search in search_cubes.c does NOT cover.

search_cubes.c enumerates solutions of x^3+y^3+z^3 = k with |x| > |y| > |z| and
|z| > k^(1/3).  Three families sit outside that:

  (1) |z| <= k^(1/3)          -- finitely many z, each a plain x^3+y^3 = m solve
  (2) x = -y                  -- then z^3 = k
  (3) y = z                   -- then x^3 + 2y^3 = k, a Thue equation

For the posed (s,t) problem, (2) is exactly U = 0 (zero denominator B t + beta)
and (3) is exactly y = 0, both of which the problem statement already excludes.
They are checked here only so the enumeration is provably complete.
"""
from math import isqrt

K = 114


def divisors(n):
    n = abs(n)
    ds = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            ds += [i, n // i]
        i += 1
    return sorted(set(ds))


def solve_sum_two_cubes(m):
    """all (x,y) in Z^2 with x^3 + y^3 = m,  m != 0"""
    out = set()
    for e in divisors(m):
        for e_ in (e, -e):
            # x+y = e_, x^2-xy+y^2 = m/e_  =>  e_^2 - 3xy = m/e_
            if m % e_:
                continue
            q = m // e_
            if (e_ * e_ - q) % 3:
                continue
            xy = (e_ * e_ - q) // 3
            disc = e_ * e_ - 4 * xy
            if disc < 0:
                continue
            r = isqrt(disc)
            if r * r != disc or (e_ + r) % 2:
                continue
            x, y = (e_ + r) // 2, (e_ - r) // 2
            if x**3 + y**3 == m:
                out.add((x, y))
                out.add((y, x))
    return sorted(out)


def main():
    eps = 1 if K % 9 == 3 else -1
    print(f"k = {K},  k = 3*({eps}) mod 9,  so x = y = z = {eps} (mod 3)\n")

    print("(1) |z| <= k^(1/3):")
    bound = round(K ** (1 / 3)) + 1
    total = 0
    for z in range(-bound, bound + 1):
        if (z - eps) % 3:
            continue
        m = K - z**3
        if m == 0:
            print(f"    z={z}: k = z^3, x = -y arbitrary  (family 2)")
            continue
        sols = solve_sum_two_cubes(m)
        for x, y in sols:
            print(f"    SOLUTION ({x}, {y}, {z})")
            total += 1
    print(f"    -> {total} solution(s)\n")

    print("(2) x = -y  =>  z^3 = k:")
    c = round(K ** (1 / 3))
    hit = [v for v in (c - 1, c, c + 1) if v**3 == K]
    print(f"    {K} is a perfect cube: {bool(hit)}  ->"
          f" {'solutions exist' if hit else 'no solutions'}\n")

    print("(3) y = z  =>  x^3 + 2y^3 = k   (Thue):")
    found = []
    LIM = 2 * 10**6
    for y in range(-LIM, LIM + 1):
        r = K - 2 * y**3
        s = 1 if r >= 0 else -1
        a = abs(r)
        c = round(a ** (1 / 3))
        for cc in (c - 1, c, c + 1):
            if cc >= 0 and cc**3 == a:
                found.append((s * cc, y, y))
                break
    print(f"    brute force |y| <= {LIM}: {found if found else 'no solutions'}")
    print("    For a rigorous certificate use PARI/GP:")
    print("        ? thue(thueinit(x^3+2,1), 114)")
    print("    (This family is excluded from the (s,t) problem anyway: y = z <=> y = 0.)")


if __name__ == '__main__':
    main()
