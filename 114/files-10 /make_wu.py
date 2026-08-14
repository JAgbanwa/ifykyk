#!/usr/bin/env python3
"""
make_wu.py -- work-unit generator / aggregator for a distributed (Charity Engine,
BOINC, SLURM array, whatever) run of search_cubes.

Cost model.  For a fixed d the searcher walks arithmetic progressions of z in
[d/alpha, zmax], so the work for one d is proportional to zmax/d (times the
sieve density, which is roughly d-independent).  Total work over d in [D0,D1] is
therefore proportional to log(D1/D0), NOT to D1-D0.

  => split the d range GEOMETRICALLY.  A uniform split gives you one work unit
     that runs for a year and a million that finish instantly.

Usage:
  ./make_wu.py plan   --d0 1 --d1 1e12 --z 1e15 --units 4096   > wu.txt
  ./make_wu.py verify --dir results/ --plan wu.txt
"""
import argparse
import math
import os
import sys
import re

ALPHA = 2 ** (1 / 3) - 1


def plan(d0, d1, zmax, units, k, extra):
    d0 = max(d0, 1)
    lo = math.log(d0 if d0 > 1 else 1.5)
    hi = math.log(d1)
    edges = [math.exp(lo + (hi - lo) * i / units) for i in range(units + 1)]
    edges[0], edges[-1] = d0, d1
    out = []
    prev = int(edges[0])
    for i in range(units):
        a = prev
        b = int(edges[i + 1])
        if b < a:
            b = a
        out.append((i, a, b))
        prev = b + 1
        if prev > d1:
            break
    w = f"{sys.executable}"
    print(f"# k={k} zmax={zmax:g} units={len(out)} "
          f"(geometric split; relative cost per unit is ~constant)", file=sys.stderr)
    for i, a, b in out:
        print(f"{i}\t./search_cubes -k {k} -d0 {a} -d1 {b} -z {zmax:g} "
              f"-o results/wu_{i:06d}.out {extra}".strip())
    _ = w


def verify(resdir, planfile):
    """Confirm every planned unit produced an output file, and collect hits."""
    want = {}
    for line in open(planfile):
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        idx, cmd = line.split('\t', 1)
        m = re.search(r'-o\s+(\S+)', cmd)
        want[int(idx)] = os.path.basename(m.group(1)) if m else f"wu_{int(idx):06d}.out"
    missing, hits = [], []
    for idx, fn in sorted(want.items()):
        p = os.path.join(resdir, fn)
        if not os.path.exists(p):
            missing.append(idx)
            continue
        for line in open(p):
            if line.startswith('SOLUTION'):
                hits.append(line.strip())
    print(f"units planned : {len(want)}")
    print(f"units missing : {len(missing)}"
          + (f"  -> {missing[:20]}{'...' if len(missing) > 20 else ''}" if missing else ""))
    print(f"raw hits      : {len(hits)}")
    for h in hits:
        print("  " + h)
    if hits:
        print("\nnow run:  ./st_cubes.py scan <concatenated results>")
    return 1 if missing else 0


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p1 = sub.add_parser('plan')
    p1.add_argument('--d0', type=float, default=1)
    p1.add_argument('--d1', type=float, required=True)
    p1.add_argument('--z', type=float, required=True)
    p1.add_argument('--units', type=int, default=1024)
    p1.add_argument('--k', type=int, default=114)
    p1.add_argument('--extra', default='')
    p2 = sub.add_parser('verify')
    p2.add_argument('--dir', required=True)
    p2.add_argument('--plan', required=True)
    a = ap.parse_args()
    if a.cmd == 'plan':
        if a.z / a.d1 < 1 / ALPHA:
            print(f"# WARNING: zmax/dmax = {a.z/a.d1:.2f} < 1/alpha = {1/ALPHA:.2f}; "
                  "you are wasting d values that can never yield a hit", file=sys.stderr)
        plan(int(a.d0), int(a.d1), a.z, a.units, a.k, a.extra)
    else:
        sys.exit(verify(a.dir, a.plan))
