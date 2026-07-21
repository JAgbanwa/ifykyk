#!/usr/bin/env sage
"""Rank-guided search for the CRT-specialized 114 elliptic curves.

For a modulus M and residue A satisfying M | 36*A^3 - 19, set

    x = M,  n = A + M*t.

The square condition is y^2 = P(t), where P is an integral cubic.  If
P(t) = a*t^3 + b*t^2 + c*t + d, the substitution X=a*t, Y=a*y gives

    Y^2 = X^3 + b*X^2 + a*c*X + a^2*d.

This script constructs those curves, ranks candidates by arithmetic data,
and recovers only points that pass all original integer identities exactly.
"""

import argparse
import itertools

from sage.all import (
    CRT_list,
    EllipticCurve,
    Integer,
    PolynomialRing,
    ZZ,
    inverse_mod,
    power_mod,
    prod,
    srange,
)


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--primes",
        default="17,23,29,41,47,53,59,71,83,89",
        help="comma-separated primes congruent to 2 modulo 3",
    )
    parser.add_argument(
        "--max-product-size",
        type=int,
        default=1,
        help="also test CRT products of up to this many supplied primes",
    )
    parser.add_argument(
        "--compute-rank",
        action="store_true",
        help="compute PARI algebraic-rank bounds (can be expensive for large M)",
    )
    parser.add_argument(
        "--analytic-rank",
        action="store_true",
        help="compute an analytic rank (can be expensive for large M)",
    )
    parser.add_argument(
        "--integral-points",
        action="store_true",
        help="ask Sage for integral points on each Weierstrass model",
    )
    parser.add_argument(
        "--t-bound",
        type=int,
        default=0,
        help="also test every integer t with |t| at most this bound",
    )
    return parser.parse_args()


def cube_root_residue(p):
    p = ZZ(p)
    if not p.is_prime() or p == 2 or p % 3 != 2:
        raise ValueError(f"{p} must be an odd prime congruent to 2 modulo 3")
    e = inverse_mod(ZZ(3), p - 1)
    c = (ZZ(19) * inverse_mod(ZZ(36), p)) % p
    A = power_mod(c, e, p)
    assert (36 * A**3 - 19) % p == 0
    return ZZ(A)


def crt_candidate(primes):
    residues = [cube_root_residue(p) for p in primes]
    M = prod(primes)
    A = ZZ(CRT_list(residues, list(primes))) % M
    assert (36 * A**3 - 19) % M == 0
    return ZZ(M), A


def curve_data(M, A):
    Q = (36 * A**3 - 19) // M
    a = 36 * M**2
    b = 36 * M * (3 * A + M)
    c = 12 * (3 * A + M)**2
    d = (6 * A + M)**2 + Q
    R = PolynomialRing(ZZ, "t")
    t = R.gen()
    P = a * t**3 + b * t**2 + c * t + d
    n = A + M * t
    numerator = 36 * n**3 - 19
    quotient, remainder = numerator.quo_rem(M)
    assert remainder == 0
    assert P == (6 * n + M) ** 2 + quotient
    E = EllipticCurve([0, b, 0, a * c, a**2 * d])
    assert E.discriminant() != 0
    return {
        "M": M,
        "A": A,
        "Q": Q,
        "a": a,
        "P": P,
        "E": E,
    }


def verify_and_format(data, t, y):
    M, A = data["M"], data["A"]
    t, y = ZZ(t), ZZ(y)
    n, x = A + M * t, M
    if x == 0 or (36 * n**3 - 19) % x != 0:
        return None
    rhs = (6 * n + x)**2 + (36 * n**3 - 19) // x
    if y**2 != rhs:
        return None
    u, v, w = y - x, 2 * x + 6 * n, -x - y
    if u**3 + v**3 + w**3 != 114:
        return None
    return {
        "t": t,
        "n": n,
        "x": x,
        "y": y,
        "u": u,
        "v": v,
        "w": w,
    }


def bounded_t_search(data, bound):
    hits = []
    P = data["P"]
    for t in srange(-bound, bound + 1):
        rhs = ZZ(P(t))
        if rhs < 0 or not rhs.is_square():
            continue
        y = rhs.sqrt()
        hit = verify_and_format(data, t, y)
        if hit is not None:
            hits.append(hit)
    return hits


def recover_integral_points(data, points):
    hits = []
    a = data["a"]
    for point in points:
        X, Y = point[0], point[1]
        if X not in ZZ or Y not in ZZ:
            continue
        X, Y = ZZ(X), ZZ(Y)
        if X % a != 0 or Y % a != 0:
            continue
        hit = verify_and_format(data, X // a, abs(Y // a))
        if hit is not None:
            hits.append(hit)
    return hits


def safe_value(label, function):
    try:
        return function()
    except KeyboardInterrupt:
        raise
    except BaseException as exc:
        return f"unavailable ({label}: {type(exc).__name__}: {exc})"


def pari_rank_bounds(E):
    result = E.minimal_model().pari_curve().ellrank()
    return (ZZ(result[0]), ZZ(result[1]))


def pari_analytic_rank(E):
    result = E.minimal_model().pari_curve().ellanalyticrank()
    return ZZ(result[0])


def main():
    args = parse_args()
    primes = tuple(ZZ(part.strip()) for part in args.primes.split(",") if part.strip())
    if not primes:
        raise ValueError("supply at least one prime")
    if len(set(primes)) != len(primes):
        raise ValueError("the supplied primes must be distinct")
    max_size = min(max(1, args.max_product_size), len(primes))

    reports = []
    for size in range(1, max_size + 1):
        for subset in itertools.combinations(primes, size):
            M, A = crt_candidate(subset)
            data = curve_data(M, A)
            E = data["E"]
            report = {
                "primes": subset,
                "data": data,
                "root_number": safe_value("root number", E.root_number),
                "rank_bounds": None,
                "analytic_rank": None,
                "hits": [],
            }
            if args.compute_rank:
                report["rank_bounds"] = safe_value(
                    "PARI rank bounds", lambda: pari_rank_bounds(E)
                )
            if args.analytic_rank:
                report["analytic_rank"] = safe_value(
                    "PARI analytic rank", lambda: pari_analytic_rank(E)
                )
            if args.t_bound > 0:
                report["hits"].extend(bounded_t_search(data, args.t_bound))
            if args.integral_points:
                points = safe_value(
                    "integral points", lambda: E.integral_points(both_signs=True)
                )
                if isinstance(points, list):
                    report["hits"].extend(recover_integral_points(data, points))
                else:
                    report["integral_points_error"] = points
            reports.append(report)

    def priority(report):
        # Root number -1 is the first heuristic filter: the parity conjecture
        # predicts odd rank.  Proven/computed positive ranks then take priority.
        bounds = report["rank_bounds"]
        rank_lower = bounds[0] if isinstance(bounds, tuple) else -1
        rank_upper = bounds[1] if isinstance(bounds, tuple) else -1
        analytic = (
            report["analytic_rank"]
            if isinstance(report["analytic_rank"], Integer)
            else -1
        )
        root_score = 1 if report["root_number"] == -1 else 0
        return (
            len(report["hits"]) > 0,
            rank_lower,
            analytic,
            rank_upper,
            root_score,
        )

    reports.sort(key=priority, reverse=True)
    for report in reports:
        data = report["data"]
        print("=" * 72)
        print(f"primes       = {report['primes']}")
        print(f"M            = {data['M']}")
        print(f"A            = {data['A']}")
        print(f"root number  = {report['root_number']}")
        if args.compute_rank:
            print(f"rank bounds  = {report['rank_bounds']}")
        if args.analytic_rank:
            print(f"analytic rank= {report['analytic_rank']}")
        print(f"curve        = {data['E']}")
        print(f"square cubic = {data['P']}")
        if "integral_points_error" in report:
            print(report["integral_points_error"])
        for hit in report["hits"]:
            print(f"VERIFIED HIT = {hit}")


if __name__ == "__main__":
    main()
