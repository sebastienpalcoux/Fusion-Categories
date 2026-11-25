"""Reproduce the census and optionally export the surviving rank-15 types."""
import argparse
from pathlib import Path

from criterion import passes, read_types


HERE = Path(__file__).resolve().parent
MODES = ("single", "cover", "gcd", "blocks")


def write_types(types, path):
    with Path(path).open("w", encoding="ascii", newline="\n") as stream:
        for row in types:
            stream.write(" ".join(map(str, row)) + "\n")


def check_dataset(filename, expected_rank):
    types = read_types(HERE / "data" / filename)
    if len(set(types)) != len(types) or any(
        len(row) != expected_rank or tuple(sorted(row)) != row for row in types
    ):
        raise ValueError(f"duplicate, unsorted or wrong-rank row in {filename}")
    return types


def census():
    rank14 = check_dataset("rank14.txt", 14)
    rank15 = check_dataset("rank15.txt", 15)
    examples = check_dataset("rank15-examples.txt", 15)
    rank25 = check_dataset("rank25-odd.txt", 25)
    earlier = check_dataset("rank25-odd-91.txt", 25)
    datasets = {
        "rank 14, residual": rank14,
        "rank 15, non-perfect": [t for t in rank15 if t.count(1) > 1],
        "rank 15, perfect": [t for t in rank15 if t.count(1) == 1],
        "rank 15, examples": examples,
        "odd rank 25, residual": rank25,
        "odd rank 25, initial": earlier,
    }
    expected = [
        (34, 2, 2, 2, 2), (399, 140, 132, 110, 47), (8628, 2341, 1861, 1861, 311),
        (18, 18, 14, 14, 3), (3, 0, 0, 0, 0), (91, 3, 3, 3, 0),
    ]
    print(f"{'dataset':24} {'input':>6} {'single':>6} {'cover':>6} {'gcd':>6} {'blocks':>6}")
    results = {}
    for (name, types), counts in zip(datasets.items(), expected):
        previous = types
        actual = [len(types)]
        for mode in MODES:
            kept = [t for t in types if passes(t, mode)]
            if not set(kept).issubset(previous):
                raise AssertionError(f"{name}: survivor sets are not nested")
            if name == "rank 15, examples" and mode in ("cover", "gcd"):
                removed = set(types) - set(kept)
                if removed != {examples[i-1] for i in (3, 5, 6, 10)}:
                    raise AssertionError("unexpected simultaneous-prime exclusions")
            if name == "odd rank 25, initial" and mode != "blocks":
                if kept != [earlier[i-1] for i in (8, 26, 37)]:
                    raise AssertionError("unexpected rank-25 support-test survivors")
            previous = kept
            actual.append(len(kept))
        print(f"{name:24}" + "".join(f"{a:7}" for a in actual))
        if tuple(actual) != counts:
            raise AssertionError(f"{name}: expected {counts}, obtained {actual}")
        results[name] = previous
    if results["rank 14, residual"] != rank14[:2]:
        raise AssertionError("unexpected rank-14 survivors")
    if results["rank 15, examples"] != [examples[i-1] for i in (1, 2, 4)]:
        raise AssertionError("unexpected rank-15 example survivors")
    return sorted(results["rank 15, non-perfect"] + results["rank 15, perfect"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-survivors", metavar="PATH",
                        help="export all rank-15 types passing the block test")
    args = parser.parse_args()
    survivors = census()
    if survivors != read_types(HERE / "data" / "rank15-survivors.txt"):
        raise AssertionError("rank-15 result differs from the supplied survivor list")
    if args.write_survivors:
        write_types(survivors, args.write_survivors)
    print(f"rank 15, all: {len(survivors)} types pass the block test")
