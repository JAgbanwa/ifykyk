#!/bin/sh
# run_mac.sh -- build and run the k=114 search across all cores of a Mac.
#
#   ./run_mac.sh selftest              # ~1 min: prove the toolchain + code are sane
#   ./run_mac.sh bench                 # ~2 min: measure YOUR throughput
#   ./run_mac.sh run K DMAX ZMAX JOBS  # the real sweep
#
# Examples
#   ./run_mac.sh run 114 1e10 5.4e11 8
#   caffeinate -i ./run_mac.sh run 114 1e11 5.4e12 6     # keeps the Mac awake
#
# Notes for Apple Silicon:
#   * -march=native is a GCC-ism and will fail on Apple clang. We use -mcpu=native
#     when it is accepted and fall back to plain -O3.
#   * An 8-core M1 Pro is 6 performance + 2 efficiency cores. The E-cores are
#     roughly 3x slower, so work is handed out from a queue (xargs -P) rather
#     than statically split; make sure UNITS >> JOBS so the queue can rebalance.
#   * Progress = completed unit files in results/. Nothing else prints until a
#     unit finishes.

set -e
BIN=./search_cubes
SRC=search_cubes.c
PY=${PY:-python3}

build() {
    [ -f "$SRC" ] || { echo "run this from the cubes114 directory"; exit 1; }
    if [ "$SRC" -nt "$BIN" ] 2>/dev/null || [ ! -x "$BIN" ]; then
        echo "building..."
        if cc -O3 -mcpu=native -o "$BIN" "$SRC" -lm 2>/dev/null; then :
        else cc -O3 -o "$BIN" "$SRC" -lm; fi
        echo "built $BIN"
    fi
}

case "$1" in
selftest)
    build
    echo "--- reduction ---";  $PY reduction.py | tail -5
    echo "--- dictionary ---"; $PY st_cubes.py selftest
    echo "--- degenerate families ---"; $PY degenerate.py | grep -E 'solution|cube:|brute'
    echo "--- searcher must rediscover two known solutions ---"
    $BIN -k 39 -d0 1 -d1 30000   -z 2e5
    $BIN -k 30 -d0 1 -d1 2000000 -z 3e8
    echo "if you saw a SOLUTION line for k=39 and k=30, everything works."
    ;;
bench)
    build
    echo "single-core throughput, k=114, ratio zmax/dmax = 54:"
    for D in 1000000 4000000; do
        Z=$($PY -c "print(f'{$D*54:g}')")
        S=$(date +%s)
        $BIN -k 114 -d0 1 -d1 $D -z $Z >/dev/null 2>/tmp/cubes_bench.err
        E=$(date +%s)
        T=$((E-S)); [ $T -eq 0 ] && T=1
        echo "  dmax=$D  ${T}s  -> $($PY -c "print(f'{$T/$D*1e6:.2f}')") us per unit of dmax"
    done
    echo
    echo "multiply by (seconds you are willing to spend * JOBS) to get the dmax you can reach."
    ;;
run)
    build
    K=${2:-114}; DMAX=${3:-1e9}; ZMAX=${4:-5.4e10}; JOBS=${5:-$(sysctl -n hw.perflevel0.logicalcpu 2>/dev/null || sysctl -n hw.ncpu)}
    UNITS=$(( JOBS * 64 ))
    mkdir -p results
    echo "k=$K dmax=$DMAX zmax=$ZMAX jobs=$JOBS units=$UNITS"
    $PY make_wu.py plan --k "$K" --d0 1 --d1 "$DMAX" --z "$ZMAX" --units "$UNITS" > wu.txt
    START=$(date +%s)
    cut -f2 wu.txt | xargs -P "$JOBS" -I CMD sh -c 'CMD' 2>/dev/null
    END=$(date +%s)
    echo "wall clock: $((END-START))s"
    $PY make_wu.py verify --dir results --plan wu.txt
    cat results/*.out > results/all.out 2>/dev/null || true
    if [ -s results/all.out ]; then
        echo; echo "converting hits to (s,t):"
        $PY st_cubes.py scan results/all.out
    else
        echo "no solutions in this range (expected)."
    fi
    ;;
*)
    sed -n '2,25p' "$0"
    ;;
esac
