"""Reproduce the census and optionally export the surviving rank-15 types."""
import argparse
from pathlib import Path

from criterion import passes, read_types


HERE = Path(__file__).resolve().parent
MODES = ("single", "cover", "gcd", "blocks", "symmetric", "manuscript", "combined")
PREREQUISITES = {
    "single": (), "cover": ("single",), "gcd": ("cover",), "blocks": ("gcd",),
    "symmetric": ("gcd",), "manuscript": ("blocks",), "combined": ("manuscript", "symmetric"),
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


def census(show_stages=False, manuscript=False):
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
        (34, 2, 2, 2, 2, 2, 2, 2), (399, 140, 132, 110, 47, 74, 45, 41),
        (8628, 2341, 1861, 1861, 311, 1077, 250, 250), (18, 18, 14, 14, 3, 11, 3, 3),
        (3, 0, 0, 0, 0, 0, 0, 0), (91, 3, 3, 3, 0, 0, 0, 0),
    ]
    if show_stages:
        print(f"{'dataset':24} {'input':>6}" + "".join(f"{mode:>10}" for mode in MODES))
    else:
        print(f"{'dataset':24} {'input':>9} {'excluded':>9} {'remaining':>9}")
    # A manuscript run requires only the tests used in the paper. Requesting
    # the full stage table explicitly adds the repository's optional tests.
    modes = MODES if show_stages or not manuscript else ("single", "cover", "gcd", "blocks", "manuscript")
    results = {}
    for (name, types), counts in zip(datasets.items(), expected):
        by_mode = {}
        actual = [len(types)]
        for mode in modes:
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
        final = by_mode["manuscript" if manuscript else "combined"]
        if show_stages:
            print(f"{name:24} {actual[0]:6}" + "".join(f"{count:10}" for count in actual[1:]))
        else:
            print(f"{name:24} {len(types):9} {len(types) - len(final):9} {len(final):9}")
        expected_by_mode = dict(zip(MODES, counts[1:]))
        selected_counts = [counts[0], *(expected_by_mode[mode] for mode in modes)]
        if actual != selected_counts:
            raise AssertionError(f"{name}: expected {selected_counts}, obtained {actual}")
        results[name] = final
    if results["rank 14, residual"] != rank14[:2]:
        raise AssertionError("unexpected rank-14 survivors")
    if results["rank 15, examples"] != [examples[i-1] for i in (1, 2, 4)]:
        raise AssertionError("unexpected rank-15 example survivors")
    return sorted(results["rank 15, non-perfect"] + results["rank 15, perfect"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-survivors", metavar="PATH",
                        help="export the surviving rank-15 types for the selected tests")
    parser.add_argument("--stages", action="store_true",
                        help="show counts for each arithmetic test")
    parser.add_argument("--manuscript", action="store_true",
                        help="report the tests in the paper, before the optional orbit and grading refinements")
    args = parser.parse_args()
    survivors = census(show_stages=args.stages, manuscript=args.manuscript)
    filename = "rank15-manuscript-survivors.txt" if args.manuscript else "rank15-survivors.txt"
    if survivors != read_types(HERE / "data" / filename):
        raise AssertionError("rank-15 result differs from the supplied survivor list")
    if args.write_survivors:
        write_types(survivors, args.write_survivors)
    scope = "manuscript" if args.manuscript else "combined"
    print(f"rank 15, all: {len(survivors)} types pass the {scope} tests")
