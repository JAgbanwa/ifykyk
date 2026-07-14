# Rational `k1, k2` Search

This is an exact C++/GMP searcher for the equation in the prompt. It avoids
floating point arithmetic completely.

## Reduction Used

Let

```text
D1 = 7729484335457653901640057298531371241781
D2 = 2486598372481845396683104279916570951657
```

Because `A = 6*D1` and `B = D2`, every rational satisfying `q1 | D1` and
`q2 | D2` can be written as

```text
k1 = m / D1
k2 = n / D2
```

with `m,n` integers. More generally, the searcher supports

```text
k2 = n / (scale*D2)
```

via `--q2-scale scale`; the stated problem is `--q2-scale 1`.

For `k1 = m/D1`, the cubic numerator becomes the integer

```text
P(m) =
  36*m^3
  + 828206165581860705133665232912370284496880*m^2
  + 6351161599146374737633882130250167287933965064228967875255393268381831015506756800*m
  + 16234787638949931054338904909272730014525041302296577490759268200927073136776735826378161845204226655836573767036816415981
```

For a general `scale`, define

```text
X    = scale*E + n
Lnum = scale*(6*m + C) + n
```

Then the right hand side is

```text
(Lnum/scale)^2 + P(m)/(X/scale)
```

The program checks exactly whether this rational number is a non-negative
integer square.

## Build

Install GMP development headers/libraries, then:

```bash
cd rational_search
make -j
```

On clusters, override compiler flags as needed:

```bash
make CXX=g++ CXXFLAGS="-O3 -std=c++17 -pthread -march=native"
```

## Modes

### `box`

Brute force a bounded rectangle in `(m,n)`:

```bash
./build/ksearch \
  --mode box \
  --m-start -1000000 --m-count 2000001 \
  --n-start -1000000 --n-count 2000001 \
  --threads 16 \
  --out hits.box.jsonl
```

### `x`

Search by the shifted denominator numerator `X = scale*E + n`. For
`--q2-scale 1`, this is just `X = D2*k2 + E`. This is the useful mode for
near-pole searches where `X` is small:

```bash
./build/ksearch \
  --mode x \
  --m-start -5000000000 --m-count 10000000001 \
  --x-start -1000000 --x-count 2000001 \
  --root-limit 200000 \
  --threads 16 \
  --out hits.x.jsonl
```

For small `|X/gcd(X,scale^3)|`, this mode enumerates roots of `P(m) = 0`
modulo that value and only tests those `m` residues.

### `divisors`

For each `m`, factor `|scale^3*P(m)|`, enumerate every divisor candidate for
`X`, and verify the full equation exactly. This is complete in `k2` for each
`m` when factorization succeeds:

```bash
./build/ksearch \
  --mode divisors \
  --m-start -10000 --m-count 20001 \
  --factor-trial-limit 1000000 \
  --rho-attempts 64 \
  --rho-iters 200000 \
  --threads 8 \
  --out hits.divisors.jsonl
```

The built-in Pollard-rho factorer is intentionally dependency-light. For very
large hard cofactors, use smaller work units or wire unresolved cofactors from
the JSONL output into ECM/YAFU/CADO-NFS.

## Sharding

All modes support deterministic sharding over the outer range:

```bash
./build/ksearch ... --shard-index 17 --shard-count 1000 --out shard-17.jsonl
```

For SLURM arrays:

```bash
./build/ksearch ... \
  --shard-index "${SLURM_ARRAY_TASK_ID}" \
  --shard-count "${SLURM_ARRAY_TASK_COUNT}" \
  --out "hits.${SLURM_ARRAY_TASK_ID}.jsonl"
```

For volunteer/distributed systems, make each work unit a command line with a
different shard index. Output is append-only JSONL so reducers can concatenate
and deduplicate by `(m,n,y_abs)`.

## Output

Hits are emitted as JSON lines. `y_abs` means both signs are valid unless it is
zero.

```json
{"type":"hit","mode":"box","m":"...","n":"...","k1_num":"...","k1_den":"...","k2_num":"...","k2_den":"...","x_num":"...","x_den":"1","y_abs":"..."}
```

Diagnostic lines such as unresolved factorization are also JSONL records with
`"type":"unfactored"`.

## Verifying One Pair

Use the Python verifier for arbitrary rational pairs:

```bash
python3 tools/verify_pair.py \
  --k1-num -38342878036197254867299316338535661320806 \
  --k1-den 7729484335457653901640057298531371241781 \
  --k2-num -3047652620091320691551633593075166537541 \
  --k2-den 12432991862409226983415521399582854758285
```
