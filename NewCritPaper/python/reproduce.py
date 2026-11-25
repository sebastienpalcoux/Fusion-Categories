"""Reproduce the census and optionally export the surviving rank-15 types."""
import argparse
from pathlib import Path

from criterion import passes, read_types


HERE = Path(__file__).resolve().parent
MODES = ("single", "cover", "gcd", "blocks", "symmetric", "combined")
PREREQUISITES = {
    "single": (), "cover": ("single",), "gcd": ("cover",), "blocks": ("gcd",),
    "symmetric": ("gcd",), "combined": ("blocks", "symmetric"),
}


def write_types(types, path):
    with Path(path).open("w", encoding="ascii", newline="\n") as stream:
        for row in types:
            stream.write(" ".join(map(str, row)) + "\n")


def check_dataset(filename, expected_rank, odd_perfect=False):
    types = read_types(HERE / "data" / filename)
    if len(set(types)) != len(types):
        raise ValueError(f"duplicate row in {filename}")
    for number, row in enumerate(types, 1):
        if (len(row) != expected_rank or tuple(sorted(row)) != row
                or row[0] != 1 or row[-1] == 1):
            raise ValueError(f"{filename} row {number}: expected a sorted non-pointed type of rank {expected_rank}")
        if odd_perfect and (row.count(1) != 1 or any(d % 2 == 0 for d in row)):
            raise ValueError(f"{filename} row {number}: expected a perfect odd-dimensional type")
    return types


def census(show_stages=False):
    rank14 = check_dataset("rank14.txt", 14)
    rank15 = check_dataset("rank15.txt", 15)
    examples = check_dataset("rank15-examples.txt", 15)
    rank25 = check_dataset("rank25-odd.txt", 25, odd_perfect=True)
    earlier = check_dataset("rank25-odd-91.txt", 25, odd_perfect=True)
    if not set(examples).issubset(rank15):
        raise ValueError("rank-15 example missing from the input census")
    if not set(rank25).issubset(earlier):
        raise ValueError("residual odd rank-25 type missing from the initial list")
    datasets = {
        "rank 14, residual": rank14,
        "rank 15, non-perfect": [t for t in rank15 if t.count(1) > 1],
        "rank 15, perfect": [t for t in rank15 if t.count(1) == 1],
        "rank 15, examples": examples,
        "odd rank 25, residual": rank25,
        "odd rank 25, initial": earlier,
    }
    expected = [
        (34, 2, 2, 2, 2, 2, 2), (399, 140, 132, 110, 47, 74, 41),
        (8628, 2341, 1861, 1861, 311, 1077, 250), (18, 18, 14, 14, 3, 11, 3),
        (3, 0, 0, 0, 0, 0, 0), (91, 3, 3, 3, 0, 0, 0),
    ]
    if show_stages:
        print(f"{'dataset':24} {'input':>6}" + "".join(f"{mode:>10}" for mode in MODES))
    else:
        print(f"{'dataset':24} {'input':>9} {'excluded':>9} {'remaining':>9}")
    results = {}
    for (name, types), counts in zip(datasets.items(), expected):
        by_mode = {}
        actual = [len(types)]
        for mode in MODES:
            kept = [t for t in types if passes(t, mode)]
            for prerequisite in PREREQUISITES[mode]:
                if not set(kept).issubset(by_mode[prerequisite]):
                    raise AssertionError(f"{name}: {mode} passes a row excluded by {prerequisite}")
            if name == "rank 15, examples" and mode in ("cover", "gcd"):
                removed = set(types) - set(kept)
                if removed != {examples[i-1] for i in (3, 5, 6, 10)}:
                    raise AssertionError("unexpected simultaneous-prime exclusions")
            if name == "odd rank 25, initial" and mode in ("single", "cover", "gcd"):
                if kept != [earlier[i-1] for i in (8, 26, 37)]:
                    raise AssertionError("unexpected rank-25 support-test survivors")
            by_mode[mode] = kept
            actual.append(len(kept))
        final = by_mode["combined"]
        if show_stages:
            print(f"{name:24} {actual[0]:6}" + "".join(f"{count:10}" for count in actual[1:]))
        else:
            print(f"{name:24} {len(types):9} {len(types) - len(final):9} {len(final):9}")
        if tuple(actual) != counts:
            raise AssertionError(f"{name}: expected {counts}, obtained {actual}")
        results[name] = final
    if results["rank 14, residual"] != rank14[:2]:
        raise AssertionError("unexpected rank-14 survivors")
    if results["rank 15, examples"] != [examples[i-1] for i in (1, 2, 4)]:
        raise AssertionError("unexpected rank-15 example survivors")
    return sorted(results["rank 15, non-perfect"] + results["rank 15, perfect"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-survivors", metavar="PATH",
                        help="export all rank-15 types passing the combined tests")
    parser.add_argument("--stages", action="store_true",
                        help="show counts for each arithmetic test")
    args = parser.parse_args()
    survivors = census(show_stages=args.stages)
    if survivors != read_types(HERE / "data" / "rank15-survivors.txt"):
        raise AssertionError("rank-15 result differs from the supplied survivor list")
    if args.write_survivors:
        write_types(survivors, args.write_survivors)
    print(f"rank 15, all: {len(survivors)} types pass the combined tests")
