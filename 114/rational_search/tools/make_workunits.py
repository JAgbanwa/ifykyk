#!/usr/bin/env python3
import argparse


def main() -> int:
    parser = argparse.ArgumentParser(description="Emit sharded ksearch command lines.")
    parser.add_argument("--binary", default="./build/ksearch")
    parser.add_argument("--base-args", required=True, help="Arguments shared by every work unit, quoted as one string.")
    parser.add_argument("--shards", required=True, type=int)
    parser.add_argument("--out-prefix", default="hits")
    args = parser.parse_args()

    for i in range(args.shards):
        print(
            f"{args.binary} {args.base_args} "
            f"--shard-index {i} --shard-count {args.shards} "
            f"--out {args.out_prefix}.{i}.jsonl"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
