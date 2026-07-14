#!/usr/bin/env python3
import argparse
import math
from fractions import Fraction

D1 = 7729484335457653901640057298531371241781
D2 = 2486598372481845396683104279916570951657
A = 46376906012745923409840343791188227450686
B = D2
C = 46620984167454969979069506324857826890656
E = 609530524018264138310326718615033307496

N3 = 16624709489189407440388643213728981685328681791089732876601710038587810847889998299944067715532425036389785803066750571476
N2 = 49481117808109917372654153079508763668111544754357197384070641920072789816863012403689690888343605217704925500637542381680
N1 = 49091204092562086792376670895376907696653809047079935546700717754945371359211889852498465756993689409319452027811965860800
N0 = 16234787638949931054338904909272730014525041302296577490759268200927073136776735826378161845204226655836573767036816415981


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k1-num", required=True, type=int)
    parser.add_argument("--k1-den", required=True, type=int)
    parser.add_argument("--k2-num", required=True, type=int)
    parser.add_argument("--k2-den", required=True, type=int)
    args = parser.parse_args()

    k1 = Fraction(args.k1_num, args.k1_den)
    k2 = Fraction(args.k2_num, args.k2_den)

    linear = A * k1 + B * k2 + C
    denom = B * k2 + E
    cubic = N3 * k1**3 + N2 * k1**2 + N1 * k1 + N0

    if denom == 0:
        print("denominator is zero")
        return 2

    rhs = linear * linear + cubic / denom
    print(f"linear = {linear}")
    print(f"denominator = {denom}")
    print(f"cubic = {cubic}")
    print(f"rhs = {rhs}")

    if rhs.denominator != 1:
        print("rhs is not an integer")
        return 1

    if rhs.numerator < 0:
        print("rhs is a negative integer")
        return 1

    y = math.isqrt(rhs.numerator)
    if y * y != rhs.numerator:
        print("rhs is an integer but not a square")
        return 1

    print(f"integer y exists: y = +/-{y}" if y else "integer y exists: y = 0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
