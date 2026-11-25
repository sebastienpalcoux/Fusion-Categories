"""Cross-check the column tests and independently reconstruct the final census."""
from collections import Counter, defaultdict
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
from math import gcd, isqrt, lcm

from blocks import block_column_passes
from criterion import column_passes, grading_partitions, passes, read_types
from reproduce import HERE


def check(actual, expected, message):
    if actual != expected:
        raise AssertionError(f"{message}: obtained {actual!r}, expected {expected!r}")


def reference_column(x, sizes, g, total, test):
    """Enumerate every witness subset directly, without state compression."""
    budget = total - g * x * x
    if budget < 0:
        return False
    affordable = [(y, lcm(x, y)**2) for y in sizes if lcm(x, y)**2 <= budget]
    if test in ("single", "cover"):
        primes = {p for p in range(2, x + 1)
                  if x % p == 0 and g % p and all(p % k for k in range(2, p))}
        if test == "single":
            return all(any(y % p for y, _ in affordable) for p in primes)
    for length in range(len(affordable) + 1):
        for subset in combinations(affordable, length):
            if sum(cost for _, cost in subset) > budget:
                continue
            if test == "cover" and all(any(y % p for y, _ in subset) for p in primes):
                return True
            if test == "gcd" and subset and g % gcd(*(y*y // gcd(x, y) for y, _ in subset)) == 0:
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
            budgets = {cost + offset for cost in costs for offset in (-1, 0, 1)}
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


def check_component_types():
    rows = read_types(HERE / "data" / "rank15.txt")
    for index in (17, 18):
        row = rows[index - 1]
        candidates = reference_gradings(row)
        check(len(candidates), 2, ("rank 15", index, "equal-weight partitions"))
        check(any(parts[1] == parts[2] for parts in candidates), False,
              ("rank 15", index, "no dual nonneutral components"))
        check(passes(row, "blocks"), True, ("rank 15", index, "earlier block test"))
        check(passes(row, "symmetric"), False, ("rank 15", index, "grading obstruction"))
    row = rows[8]
    check((row.count(1), row.count(3), row.count(4), sum(x*x for x in row)),
          (4, 4, 2, 576), "rank-15 row 9: four-element orbit")
    check({y for y in row if y > 1 and y % 3}, {4},
          "rank-15 row 9: forced neighbor")
    check(4*lcm(3, 4)**2, sum(x*x for x in row), "rank-15 row 9: exhausted norm")
    row = rows[9]
    check((row.count(1), row.count(3), gcd(3**2, row.count(1))), (4, 2, 1),
          "rank-15 row 10: impossible orbit size")
    check(sum(sum(x*x for x in row) % 2 for row in rows), 0,
          "all rank-15 inputs have even dimension")


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


def row_digest(rows):
    normalized = "".join(" ".join(map(str, row)) + "\n" for row in rows)
    return sha256(normalized.encode("ascii")).hexdigest()


def check_source_lists():
    # Digests of the ordered, expanded tables in the archived data revision
    # identified in README.md. White space is normalized by row_digest.
    expected = {
        "rank14.txt": "ff69d07733bfbe367eb553f391ef0e4d42feb188d9fd7f2902dd3207ff6a7567",
        "rank15.txt": "932a209b9127d845653e7ab0876c1a48532451ec3ad051cc5c9db7caed3b70e5",
        "rank15-examples.txt": "6882621a302b67956d86d4dff62aeb8fed33baede34a8f93821d2047e0213301",
        "rank25-odd-91.txt": "27736f632d3b7d3e427231d505a0485e787056f04f9549430820c4ac668df1f5",
        "rank25-odd.txt": "f8a5425cba6805a518ad31c680265b69652e717e4fc24b387002695701b9c7ee",
    }
    for filename, digest in expected.items():
        check(row_digest(read_types(HERE / "data" / filename)), digest, filename)


def check_rank14_certificates():
    rows = read_types(HERE / "data" / "rank14.txt")
    # Give the actual symmetric support used in the guide for rows 1 and 2.
    for index, row in enumerate(rows[:2], 1):
        d = row[2:]
        check((row[:2], d[0], d.count(3), d[-2:]), ((1, 1), 2, 2, (max(d),)*2),
              ("rank 14", index, "support witness labels"))
        total = sum(x*x for x in row)
        neutral = range(len(d)-2)
        entries = {(0, j) for j in neutral} | {(j, 0) for j in neutral}
        entries |= {(i, j) for i, x in enumerate(d) for j, y in enumerate(d) if x == y == 3}
        entries |= {(j, j) for j in (len(d)-2, len(d)-1)}
        check(sum(x*x for x in row[:-2]), total // 2,
              ("rank 14", index, "support witness neutral component"))
        for i, x in enumerate(d):
            neighbors = [d[j] for j in range(len(d)) if (i, j) in entries]
            check(2*x*x + sum(lcm(x,y)**2 for y in neighbors) <= total, True,
                  ("rank 14", index, "witness norm", i))
            if i in neutral:
                check(2 % gcd(*(y*y // gcd(x,y) for y in neighbors)), 0,
                      ("rank 14", index, "witness gcd", i))
    # In the worked example the neutral component contains every dimension
    # smaller than 180 and one of the three simples of dimension 180.
    example = rows[2]
    check((example.count(1), example.count(180), sum(y*y for y in example if y < 180)),
          (2, 3, 180**2), "rank-14 hand example: grading")
    check(36 in example and {y for y in example if y > 1 and y % 3} == {40},
          True, "rank-14 hand example: column and witness")
    check(lcm(36, 40)**2 + 2*36**2 > sum(y*y for y in example),
          True, "rank-14 hand example: norm inequality")
    # Each triple gives q, the prime p and the row numbers; the column
    # dimension is twice the largest simple dimension divided by q.
    groups = (
        (2, 3, (3, 4, 6, 7)),
        (2, 5, (5, 9, 11, 13, 15, 16, 19, 20, 21, 22, 23, 24, 27, 28, 30, 31, 34)),
        (3, 7, (10, 12, 25, 26, 29, 32, 33)),
        (5, 3, (8, 18)),
        (7, 3, (14, 17)),
    )
    covered = []
    for q, p, indices in groups:
        for i in indices:
            row = rows[i - 1]
            largest = max(row)
            root = 2 * largest
            g = row.count(1)
            check(sum(y*y for y in row), root*root, ("rank 14", i, "dimension"))
            if g != 1:
                # The part containing the unit must have one largest label
                # and all the smaller labels.
                check((g, row.count(largest)), (2, 3), ("rank 14", i, "grading"))
            x, remainder = divmod(root, q)
            check(remainder == 0 and x in row and x % p == 0 and g % p != 0,
                  True, ("rank 14", i, "column and prime"))
            check(all(lcm(x, y) == root for y in row if y > 1 and y % p),
                  True, ("rank 14", i, "all witnesses exhaust the norm"))
        covered.extend(indices)
    check(sorted(covered), list(range(3, len(rows) + 1)), "rank-14 certificate coverage")


def check_rank15_block_example():
    row = read_types(HERE / "data" / "rank15-examples.txt")[12]
    x, y = 3780, 70
    total = sum(d*d for d in row)
    check((row.count(1), row.count(y), max(row), x % y, total),
          (1, 2, x, 0, 4*x*x), "rank-15 row 13: type and normalized norm")
    check(all(d % 9 == 0 for d in row if d not in (1, y)),
          True, "rank-15 row 13: other blocks vanish modulo nine")
    bound = isqrt(row.count(y) * (total // (x*x) - 1))
    check(any((y*b + 1) % 9 == 0 for b in range(-bound, bound + 1)),
          False, "rank-15 row 13: no integer block sum satisfies orthogonality")


def check_rank25_certificates():
    residual = read_types(HERE / "data" / "rank25-odd.txt")
    choices = [(4095, 13, {75, 175}), (2925, 5, {91}), (135, 3, {385})]
    check(len(residual), len(choices), "odd rank 25: residual row count")
    for row, (x, p, dimensions) in zip(residual, choices):
        check(row.count(1) == 1 and x in row and x % p == 0,
              True, ("residual odd rank 25", x, "adjoint column and prime"))
        check({y for y in row if y > 1 and y % p}, dimensions, (x, "witness dimensions"))
        check(all(lcm(x, y)**2 == sum(v*v for v in row) for y in dimensions),
              True, ("residual odd rank 25", x, "exhausted norm"))
    rows = read_types(HERE / "data" / "rank25-odd-91.txt")
    # The primes in the manuscript's multiplicity obstruction (ABPP, Thm. 8.5).
    primes = {8: 23, 26: 19, 37: 37}
    # Additional centered-residue certificates, explained in the README.
    # (largest dimension, modulus, multiplier, weighted residue square sum)
    exceptions = {
        8: (36225, 289, 78, 760),
        26: (55575, 329, 101, 1036),
        37: (2594625, 17, 7, 2),
    }
    for i, row in enumerate(rows, 1):
        dims = set(row) - {1}
        total = sum(y*y for y in row)
        root = isqrt(total)
        check(root*root == total and row.count(1) == 1 and all(y % 2 for y in row),
              True, ("odd rank 25", i, "dimension and perfection"))
        check(all(root % y == 0 for y in dims), True, ("odd rank 25", i, "divisibility"))
        # A common prime factor of x and every y with lcm(x,y) < root
        # forces every prime-free witness to exhaust the norm.
        excluded = any(gcd(x, *(y for y in dims if lcm(x, y) < root)) > 1 for x in dims)
        check(excluded, i not in exceptions, ("odd rank 25", i, "single prime"))
        if i in exceptions:
            # A unique dual pair coprime to p forces an everywhere nonzero
            # column, contradicting (1.1). See the repository guide.
            p, y = {8: (3, 115), 26: (3, 65), 37: (11, 51)}[i]
            check([d for d in row if d > 1 and d % p], [y, y],
                  ("odd rank 25", i, "unique prime-free dual pair"))
            check(y*y + sum(lcm(x, y)**2 for x in row if x > 1) > total,
                  True, ("odd rank 25", i, "full-support column exceeds norm"))
            prime = primes[i]
            largest_multiplicity = max(Counter(row).values())
            check(largest_multiplicity, 8, ("odd rank 25", i, "maximum multiplicity"))
            check(total % prime == 0 and prime > 2*largest_multiplicity+1,
                  True, ("odd rank 25", i, "prime and multiplicity bound"))
            x, modulus, multiplier, expected = exceptions[i]
            check((max(row), root), (x, 3*x), ("odd rank 25", i, "largest column"))
            # The budget is eight. If y does not divide x, the odd norm
            # weight (lcm(x,y)/x)^2 is at least nine.
            residues = [(multiplier*y + modulus//2) % modulus - modulus//2
                        for y in row if y > 1 and x % y == 0]
            mass = sum(r*r for r in residues)
            check(mass, expected, ("odd rank 25", i, "residue mass"))
            check(0 < 2*multiplier < modulus and 8*mass < multiplier**2,
                  True, ("odd rank 25", i, "strict Cauchy–Schwarz contradiction"))


def check_published_list():
    rows = read_types(HERE / "data" / "rank15.txt")
    kept = sorted(row for row in rows if passes(row, "single"))
    # SHA-256 of the sorted NP and P arrays in the cited RemainingTypes.txt,
    # expanded and written as space-separated decimal integers with Unix LF.
    check(row_digest(kept),
          "0d72a296856820d1ce469f368bde19dab3a0adbeb2947e995ee423d31d5f5914",
          "published rank-15 list")


def reference_gradings(row):
    """Place individual objects in equal-weight components, largest first."""
    g = row.count(1)
    if g == 1:
        return {(row,)}
    target, remainder = divmod(sum(y*y for y in row), g)
    if remainder:
        return set()
    partitions = {((),) * g}
    for y in reversed(row):
        updated = set()
        for parts in partitions:
            for i, part in enumerate(parts):
                if i and part == parts[i-1]:
                    continue
                if y*y + sum(z*z for z in part) <= target:
                    placed = parts[:i] + ((y,) + part,) + parts[i+1:]
                    updated.add(tuple(sorted(placed)))
        partitions = updated
    return partitions


def reference_blocks(x, sizes, g, total, rank):
    """Multiply the feasible trace/energy sets for the dimension blocks."""
    if total > rank * x*x:
        return True
    codegree, remainder = divmod(total, x*x)
    if remainder or codegree < g:
        return False
    budget = codegree - g
    totals = {(0, 0)}
    for y, n in sizes.items():
        weight = (y // gcd(x, y))**2
        limit = budget // weight
        choices = set()
        # The least energy at trace b is at least |b|, since k² >= |k|
        # for each of the n rational integers attaining that minimum.
        for b in range(-limit, limit + 1):
            q, r = divmod(b, n)
            least = (n-r)*q*q + r*(q+1)**2
            for e in range(least, limit + 1):
                if (n == 1 and e != b*b) or (e == 1 and abs(b) != 1):
                    continue
                choices.add((e*weight, b*(y*y // gcd(x, y))))
        totals = {(a+e, c+t) for a, c in totals for e, t in choices if a+e <= budget}
    return (budget, -g) in totals


def reference_symmetric(neutral, row, g, total):
    """Choose a whole minimal witness set at a time, keeping labeled edges."""
    dims = tuple(sorted(y for y in row if y > 1))
    neutral_slots = [y for y in sorted(neutral) if y > 1]
    copies = 1
    if total % 2:
        # Consecutive labels of each dimension form dual pairs. Their
        # multiplicities in the neutral part must separately be even.
        if (row.count(1) % 2 != 1 or neutral.count(1) % 2 != 1
                or dims[::2] != dims[1::2] or neutral_slots[::2] != neutral_slots[1::2]):
            return False
        copies = 2
        dims = dims[::2]
        neutral_slots = neutral_slots[::2]
    labels = defaultdict(list)
    for i, y in enumerate(dims):
        labels[y].append(i)
    adjoint = []
    for y, slots in labels.items():
        adjoint.extend(slots[:neutral_slots.count(y)])
    adjoint.sort(key=dims.__getitem__, reverse=True)
    is_adjoint = set(adjoint)
    cost = {(x, y): copies * lcm(x, y)**2 for x in labels for y in labels}
    budget = {x: total - g*x*x for x in labels}
    if any(b < 0 for b in budget.values()):
        return False
    basis = {}
    for x in set(neutral) - {1}:
        affordable = [y for y in labels if cost[x,y] <= min(budget[x], budget[y])]
        admissible = []
        for number in range(1, len(affordable) + 1):
            for subset in combinations(affordable, number):
                if (sum(cost[x,y] for y in subset) > budget[x]
                        or g % gcd(*(y*y // gcd(x,y) for y in subset))):
                    continue
                support = frozenset(subset)
                if not any(other <= support for other in admissible):
                    admissible.append(support)
        basis[x] = admissible

    @lru_cache(maxsize=8192)
    def search(supports, slack):
        choices = []
        forced = defaultdict(int)
        for i in adjoint:
            x = dims[i]
            present = supports[i]
            if any(support <= present for support in basis[x]):
                continue
            choices_at_i = []
            for support in basis[x]:
                needed = support - present
                if sum(cost[x,y] for y in needed) > slack[i]:
                    continue
                targets = []
                for y in sorted(needed):
                    unique = {}
                    for j in labels[y]:
                        if cost[x,y] <= slack[j]:
                            unique.setdefault((j == i, slack[j], j in is_adjoint, supports[j]), j)
                    targets.append(tuple(unique.values()))
                choices_at_i.extend(product(*targets))
            if not choices_at_i:
                return False
            required = set(dims[j] for j in choices_at_i[0])
            for option in choices_at_i[1:]:
                required.intersection_update(dims[j] for j in option)
            # Count terms already forced at the other ends of these edges.
            for y in required:
                forced[y] += cost[x, y]
                if forced[y] > sum(slack[j] for j in labels[y]):
                    return False
            choices.append((len(choices_at_i), i, choices_at_i))
        if not choices:
            return True
        _, i, options = min(choices)
        x = dims[i]
        for option in options:
            new_slack = list(slack)
            new_supports = list(supports)
            for j in option:
                y = dims[j]
                amount = cost[x,y]
                new_slack[i] -= amount
                new_supports[i] |= {y}
                if i != j:
                    new_slack[j] -= amount
                    new_supports[j] |= {x}
            if search(tuple(new_supports), tuple(new_slack)):
                return True
        return False

    return search((frozenset(),) * len(dims), tuple(budget[x] for x in dims))


def reference_grading_types(parts, g):
    # The kernel of the map from invertibles to grades consists exactly
    # of the invertibles in the neutral component.
    kernel = parts[0].count(1)
    image, remainder = divmod(g, kernel)
    if remainder or sum(part == parts[0] for part in parts) != image:
        return False
    counts = Counter(parts)
    del counts[parts[0]]
    # Nonneutral cosets occur in dual pairs when the quotient is odd.
    multiple = image * (2 if (g // image) % 2 else 1)
    return all(n % multiple == 0 for n in counts.values())


def reference_orbit_columns(parts, g, total):
    """Count kernel orbits and enumerate affordable dimension subsets."""
    k = parts[0].count(1)
    sizes = {x for part in parts for x in part if x > 1}
    # The largest possible stabilizer order divides both k and x squared.
    max_stabilizer = {x: gcd(k, x*x) for x in sizes}
    for part in parts:
        for x, n in Counter(part).items():
            if x > 1 and n*max_stabilizer[x] % k:
                return False
    for x in set(parts[0]) - {1}:
        candidates = [y for y in sizes
                      if g*lcm(x,y)**2 <= (total-g*y*y)*max_stabilizer[x]]
        feasible = False
        for n in range(1, len(candidates)+1):
            for subset in combinations(candidates, n):
                if g % gcd(*(y*y // gcd(x,y) for y in subset)):
                    continue
                cost = sum((g // max_stabilizer[y])*lcm(x,y)**2 for y in subset)
                if cost <= total-g*x*x:
                    feasible = True
                    break
            if feasible:
                break
        if not feasible:
            return False
    return True


def reference_passes(row):
    g = row.count(1)
    sizes = Counter(row)
    del sizes[1]
    total = sum(y*y for y in row)
    for parts in reference_gradings(row):
        if not reference_grading_types(parts, g):
            continue
        if g > 1 and not reference_orbit_columns(parts, g, total):
            continue
        neutral = sorted(set(parts[0]) - {1}, reverse=True)
        if (all(reference_column(x, sizes, g, total, "gcd")
                and reference_blocks(x, sizes, g, total, len(row)) for x in neutral)
                and reference_symmetric(parts[0], row, g, total)):
            return True
    return False


def check_full_lists():
    data = HERE / "data"
    examples = read_types(data / "rank15-examples.txt")
    for name, expected in (
        ("rank14.txt", read_types(data / "rank14.txt")[:2]),
        ("rank15.txt", read_types(data / "rank15-survivors.txt")),
        ("rank15-examples.txt", [examples[i-1] for i in (1, 2, 4)]),
        ("rank25-odd.txt", []),
        ("rank25-odd-91.txt", []),
    ):
        rows = read_types(data / name)
        kept = sorted(row for row in rows if reference_passes(row))
        check(kept, sorted(expected), f"independent final list from {name}")


def check_symmetric_support():
    data = HERE / "data"
    for filename, survivors in (
        ("rank14.txt", [1, 2]),
        ("rank25-odd.txt", []),
        ("rank25-odd-91.txt", []),
        ("rank15-examples.txt", [1, 2, 4, 7, 8, 9, 11, 12, 13, 14, 16]),
    ):
        rows = read_types(data / filename)
        actual = [i for i, row in enumerate(rows, 1) if passes(row, "symmetric")]
        check(actual, survivors, (filename, "symmetric supports"))

    # Rank-15 row 17: four entries in the column of dimension 175 each
    # contribute 12600 squared, before the unit is counted.
    row = read_types(data / "rank15-examples.txt")[16]
    total = sum(y*y for y in row)
    check((row.count(1), row.count(175), row.count(12600), row.count(2520), total),
          (1, 1, 3, 1, 4*12600**2), "rank-15 row 17: multiplicities and global dimension")
    for x in (12600, 2520):
        possible = {y for y in row if y > 1 and y % 3 and lcm(x, y)**2 + x*x <= total}
        check(possible, {175}, ("rank-15 row 17: forced dimension", x))
        check(lcm(x, 175), 12600, ("rank-15 row 17: required cost", x))


def check_centers():
    # Untwisted doubles of S3, A4, A5, and the nonabelian group of order 21.
    centers = {
        "S3": (1,)*2 + (2,)*4 + (3,)*2,
        "A4": (1,)*3 + (3,)*5 + (4,)*6,
        "A5": (1, 3, 3, 4, 5) + (12,)*10 + (15,)*4 + (20,)*3,
        "C7:C3": (1,)*3 + (3,)*16 + (7,)*6,
    }
    for group, row in centers.items():
        for mode in ("single", "cover", "gcd", "blocks", "symmetric", "combined"):
            check(passes(row, mode), True, (group, mode))


if __name__ == "__main__":
    check_source_lists()
    check_rank14_certificates()
    check_rank15_block_example()
    check_rank25_certificates()
    check_columns()
    check_gradings()
    check_component_types()
    check_block_search()
    check_published_list()
    check_symmetric_support()
    check_full_lists()
    check_centers()
    print("All five input digests and the rank-14 and odd rank-25 certificates agree.")
    print("Independent full-list checks agree for ranks 14 and 15 and odd rank 25.")
    print("Column, block, and symmetry tests, grading partitions, the published list and four group centers agree.")
