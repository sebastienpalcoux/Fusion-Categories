"""Cross-check the column algorithm and the census against independent data."""
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
from math import gcd, lcm

from blocks import block_column_passes
from criterion import column_passes, grading_partitions, passes, read_types
from reproduce import HERE


def check(actual, expected, message):
    if actual != expected:
        raise AssertionError(f"{message}: obtained {actual!r}, expected {expected!r}")


def reference_column(x, sizes, g, total, test):
    """Enumerate every witness subset directly, without state compression."""
    budget = total - g * x * x
    primes = {p for p in range(2, x + 1)
              if x % p == 0 and g % p and all(p % k for k in range(2, p))}
    if test == "single":
        return all(any(y % p and lcm(x, y)**2 <= budget for y in sizes)
                   for p in primes)
    for length in range(len(sizes) + 1):
        for subset in combinations(sizes, length):
            if sum(lcm(x, y)**2 for y in subset) > budget:
                continue
            if test == "cover" and all(any(y % p for y in subset) for p in primes):
                return True
            if test == "gcd" and subset and g % gcd(*(y*y // gcd(x, y) for y in subset)) == 0:
                return True
    return False


def check_columns():
    # Budgets just below, at and above the costs of affordable sets exercise
    # repeated witnesses, exact equality and prime-power contributions.
    for x in (4, 6, 12, 18, 30):
        for sizes in combinations((2, 3, 4, 5, 6, 9), 3):
            costs = {0}
            for y in sizes:
                costs |= {subtotal + lcm(x, y)**2 for subtotal in costs}
            budgets = {max(0, cost + offset) for cost in costs for offset in (-1, 0, 1)}
            for g in (1, 2, 4, 6):
                for budget in budgets:
                    total = budget + g * x * x
                    for test in ("single", "cover", "gcd"):
                        check(column_passes(x, sizes, g, total, test),
                              reference_column(x, sizes, g, total, test),
                              (x, sizes, g, budget, test))


def binary_partitions(dimensions):
    """All equal-weight bipartitions by allocating labeled objects to subsets."""
    total = sum(x*x for x in dimensions)
    expected = set()
    for size in range(1, len(dimensions)):
        for subset in combinations(range(len(dimensions)), size):
            if 2 * sum(dimensions[i]**2 for i in subset) == total:
                left = tuple(dimensions[i] for i in subset)
                right = tuple(x for i, x in enumerate(dimensions) if i not in subset)
                expected.add(tuple(sorted((left, right))))
    return expected


def check_gradings():
    for tail in combinations_with_replacement(range(2, 6), 5):
        row = (1, 1) + tail
        check(set(grading_partitions(row, 2)), binary_partitions(row), row)
    # A four-block partition with repeated blocks and a unique neutral type.
    row = (1,)*4 + (4,)*2 + (12,)*2 + (18,)*7
    expected = (row[:-6], (18, 18), (18, 18), (18, 18))
    check(list(grading_partitions(row, 4)), [expected], "four-block partition")
    check(passes(row, "cover"), True, "cover example")
    check(passes(row, "gcd"), False, "gcd example")


def check_block_search():
    # Enumerate the possible traces first. For each trace, determine the
    # possible energies directly and enumerate all tuples across the blocks.
    for x in (2, 3, 4, 6):
        multiplicities = {2: 2, 3: 1}
        for g in (1, 2):
            rank = g + sum(multiplicities.values())
            for codegree in range(g, rank + 2):
                total = codegree * x*x
                if codegree > rank:
                    expected = True
                else:
                    budget = codegree - g
                    choices = []
                    for y, n in multiplicities.items():
                        weight = (lcm(x, y) // x)**2
                        pairs = []
                        for b in range(-budget, budget+1):
                            lower, r = divmod(b, n)
                            least = (n-r)*lower**2 + r*(lower+1)**2
                            for e in range(least, budget // weight + 1):
                                if (n > 1 or e == b*b) and (e != 1 or abs(b) == 1):
                                    pairs.append((weight*e, b*y*y//gcd(x,y)))
                        choices.append(pairs)
                    expected = any(sum(e for e, _ in pair) == budget
                                   and sum(b for _, b in pair) == -g
                                   for pair in product(*choices))
                check(block_column_passes(x, multiplicities, g, total, rank),
                      expected, ("block", x, g, codegree))


def check_published_list():
    rows = read_types(HERE / "data" / "rank15.txt")
    kept = sorted(row for row in rows if passes(row, "single"))
    normalized = "".join(" ".join(map(str, row)) + "\n" for row in kept).encode("ascii")
    # SHA-256 of the sorted NP and P arrays in the cited RemainingTypes.txt,
    # expanded and written as space-separated decimal integers with Unix LF.
    check(sha256(normalized).hexdigest(),
          "0d72a296856820d1ce469f368bde19dab3a0adbeb2947e995ee423d31d5f5914",
          "published rank-15 list")


def check_centers():
    # Untwisted doubles of S3, A4, A5, and the nonabelian group of order 21.
    centers = {
        "S3": (1,)*2 + (2,)*4 + (3,)*2,
        "A4": (1,)*3 + (3,)*5 + (4,)*6,
        "A5": (1, 3, 3, 4, 5) + (12,)*10 + (15,)*4 + (20,)*3,
        "C7:C3": (1,)*3 + (3,)*16 + (7,)*6,
    }
    for group, row in centers.items():
        for mode in ("single", "cover", "gcd", "blocks"):
            check(passes(row, mode), True, (group, mode))


if __name__ == "__main__":
    check_columns()
    check_gradings()
    check_block_search()
    check_published_list()
    check_centers()
    print("Column and block tests, grading partitions, the published list and four group centers agree.")
