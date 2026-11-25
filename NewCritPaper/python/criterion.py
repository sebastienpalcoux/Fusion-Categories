"""Exact dimension-type tests for integral modular categories. Python 3.9+."""
from collections import Counter
from functools import lru_cache
from math import gcd, lcm
from pathlib import Path

from blocks import block_column_passes


@lru_cache(maxsize=8192)
def prime_divisors(number):
    """Return the distinct rational prime divisors of a positive integer."""
    factors = []
    divisor = 2
    while divisor * divisor <= number:
        if number % divisor == 0:
            factors.append(divisor)
            while number % divisor == 0:
                number //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if number > 1:
        factors.append(number)
    return tuple(factors)


def grading_partitions(dimensions, number_of_parts):
    """Unordered partitions into nonempty equal-square-sum multisets."""
    total = sum(d * d for d in dimensions)
    if total % number_of_parts:
        return
    weight = total // number_of_parts
    counts = Counter(dimensions)
    sizes = tuple(sorted(counts, reverse=True))
    initial = tuple(counts[d] for d in sizes)
    weights = tuple(d * d for d in sizes)

    def parts(available, residual, index=0):
        if residual == 0:
            yield (0,) * (len(sizes) - index)
            return
        if index == len(sizes):
            return
        for copies in range(min(available[index], residual // weights[index]) + 1):
            for tail in parts(available, residual - copies * weights[index], index + 1):
                yield (copies,) + tail

    # Every block in a partition is one of these vectors. Ordering their
    # indices lets a vector occur more than once without permuting blocks.
    vectors = tuple(parts(initial, weight))

    def partitions(available, remaining, start):
        if remaining == 1:
            if available in vectors[start:]:
                yield (available,)
            return
        for index in range(start, len(vectors)):
            vector = vectors[index]
            if all(a >= b for a, b in zip(available, vector)):
                leftover = tuple(a - b for a, b in zip(available, vector))
                for tail in partitions(leftover, remaining - 1, index):
                    yield (vector,) + tail

    for partition in partitions(initial, number_of_parts, 0):
        yield tuple(sorted(
            tuple(sorted(d for d, count in zip(sizes, vector) for _ in range(count)))
            for vector in partition
        ))


def grading_types_compatible(partition):
    """Test translation by invertibles and duality on the component types."""
    neutral = partition[0]
    multiplicities = Counter(partition)
    image_order = sum(1 for part in partition if 1 in part)
    if multiplicities[neutral] != image_order:
        return False
    # Translation by the image of the invertibles acts freely on grades.
    # Each of its cosets therefore consists of components of a single type.
    if any(count % image_order for count in multiplicities.values()):
        return False
    quotient_order = len(partition) // image_order
    if quotient_order % 2:
        # In an odd-order quotient every nonidentity coset has a distinct
        # inverse. Duality identifies their component types.
        return all((count // image_order) % 2 == 0
                   for part, count in multiplicities.items() if part != neutral)
    return True


def orbit_columns_fit(partition, sizes, invertibles, total):
    """Test pointed-orbit multiplicities and their costs in adjoint columns."""
    kernel = partition[0].count(1)
    orbit_size = {x: invertibles // gcd(kernel, x*x) for x in sizes}
    for part in partition:
        for x, count in Counter(part).items():
            if x > 1 and count % (kernel // gcd(kernel, x*x)):
                return False
    # A nonzero entry brings the full orbit in each index into the support.
    # Each orbit length is a multiple of orbit_size[x]. We use only
    # this lower bound, without reconstructing the orbits themselves.
    for x in set(partition[0]) - {1}:
        budget = total - invertibles*x*x
        options = []
        for y in sizes:
            weight = lcm(x, y)**2
            if orbit_size[x]*weight <= total - invertibles*y*y:
                options.append((y*y // gcd(x,y), orbit_size[y]*weight))
        if not support_within_budget(options, budget, 0, gcd,
                                     lambda common: common > 0 and invertibles % common == 0):
            return False
    return True


def column_passes(x, noninvertible, invertibles, total, test):
    """Apply one of the three bounds to a hypothetical adjoint column x."""
    if test not in ("single", "cover", "gcd"):
        raise ValueError(f"unknown test: {test!r}")
    budget = total - invertibles * x * x
    if budget < 0:
        return False
    candidates = [(y, lcm(x, y) ** 2) for y in noninvertible]
    candidates = [(y, cost) for y, cost in candidates if cost <= budget]
    if test in ("single", "cover"):
        primes = [p for p in prime_divisors(x) if invertibles % p]
        masks = [(sum(1 << i for i, p in enumerate(primes) if y % p), cost)
                 for y, cost in candidates]
        target = (1 << len(primes)) - 1
        if test == "single":
            covered = 0
            for mask, _ in masks:
                covered |= mask
            return covered == target
        if target == 0:
            return True
        # A dimension can cover several primes with its cost paid once.
        options = masks
        join = int.__or__

        def accepts(state):
            return state == target
    else:
        options = [(y * y // gcd(x, y), cost) for y, cost in candidates]
        join = gcd

        def accepts(state):
            return state > 0 and invertibles % state == 0

    return support_within_budget(options, budget, 0, join, accepts)


def support_within_budget(options, budget, start, join, accepts):
    """Find an affordable support by keeping the cheapest subset for each state."""
    # Repeating a dimension cannot improve a union or a gcd.
    costs = {start: 0}
    for item, cost in options:
        for old, subtotal in tuple(costs.items()):
            new = join(old, item)
            price = subtotal + cost
            if price <= budget and price < costs.get(new, budget + 1):
                if accepts(new):
                    return True
                costs[new] = price
    return False


def symmetric_support_passes(neutral, dimensions, invertibles, total):
    """Test (1.1)–(1.2) for one common, symmetric support of all columns."""
    neutral_counts = Counter(neutral)
    dims = tuple(x for x in dimensions if x > 1)
    copies = 1
    if total % 2:
        # Only the unit is self-dual in odd dimension. The neutral component
        # is closed under duals, and columns have the same support at Y and Y*.
        counts = Counter(dims)
        if (invertibles % 2 == 0 or neutral_counts[1] % 2 == 0
                or any(n % 2 for n in counts.values())
                or any(n % 2 for x, n in neutral_counts.items() if x > 1)):
            return False
        copies = 2
        dims = tuple(x for x, n in counts.items() for _ in range(n // 2))
        neutral_counts = {x: neutral_counts[x] // 2 for x in counts}
    adjoint = []
    for i, x in enumerate(dims):
        if neutral_counts[x]:
            adjoint.append(i)
            neutral_counts[x] -= 1
    adjoint.sort(key=dims.__getitem__, reverse=True)
    adjoint_ids = set(adjoint)

    weights = [[copies * lcm(x, y)**2 for y in dims] for x in dims]
    coefficients = [[y*y // gcd(x, y) for y in dims] for x in dims]
    budget = tuple(total - invertibles*x*x for x in dims)
    if min(budget, default=0) < 0:
        return False
    affordable = {
        i: tuple(j for j, weight in enumerate(weights[i])
                 if weight <= min(budget[i], budget[j]))
        for i in adjoint
    }
    # The first requirement is nonempty support. For each prime p, the
    # first power of p not dividing the number of invertibles must fail
    # to divide at least one coefficient in the support.
    requirements = {}
    for i in adjoint:
        primes = {p for j in affordable[i] for p in prime_divisors(dims[j])}
        requirements[i] = [(0, affordable[i])]
        for p in sorted(primes):
            threshold = p
            while invertibles % threshold == 0:
                threshold *= p
            witnesses = tuple(j for j in affordable[i] if coefficients[i][j] % threshold)
            if witnesses != affordable[i]:
                requirements[i].append((threshold, witnesses))

    def gcd_fits(common):
        return common > 0 and invertibles % common == 0

    @lru_cache(maxsize=8192)
    def column_can_finish(x, sizes, slack, common):
        options = [(y*y // gcd(x,y), copies * lcm(x,y)**2) for y in sizes]
        return support_within_budget(options, slack, common, gcd, gcd_fits)

    @lru_cache(maxsize=8192)
    def search(slack, common):
        fewest_witnesses = None
        source = None
        for i in adjoint:
            if gcd_fits(common[i]):
                continue
            available = {j for j in affordable[i] if weights[i][j] <= min(slack[i], slack[j])}
            sizes = tuple(sorted({dims[j] for j in available}))
            if not column_can_finish(dims[i], sizes, slack[i], common[i]):
                return False
            for modulus, candidates in requirements[i]:
                if (common[i] % modulus if modulus else common[i]):
                    continue
                witnesses = [j for j in candidates if j in available]
                if fewest_witnesses is None or len(witnesses) < len(fewest_witnesses):
                    source, fewest_witnesses = i, witnesses
        if fewest_witnesses is None:
            return True

        # No chosen edge can witness a still-unsatisfied requirement, so
        # the residual budgets and column gcds suffice as the search state.
        i = source
        seen = set()
        for j in fewest_witnesses:
            state = (i == j, j in adjoint_ids, dims[j], slack[j], common[j])
            if state in seen:
                continue
            seen.add(state)
            weight = weights[i][j]
            next_slack = list(slack)
            next_common = list(common)
            next_slack[i] -= weight
            next_common[i] = gcd(common[i], coefficients[i][j])
            if i != j:
                next_slack[j] -= weight
                next_common[j] = gcd(common[j], coefficients[j][i])
            if search(tuple(next_slack), tuple(next_common)):
                return True
        return False

    return search(budget, (0,) * len(dims))


def passes(dimensions, test="combined"):
    """Return whether some potential grading passes the selected tests."""
    if test not in ("single", "cover", "gcd", "blocks", "symmetric", "combined"):
        raise ValueError(f"unknown test: {test!r}")
    dimensions = tuple(dimensions)
    if not dimensions or any(type(d) is not int or d <= 0 for d in dimensions):
        raise ValueError("expected a nonempty list of positive integers")
    invertibles = dimensions.count(1)
    if not invertibles:
        raise ValueError("a dimension type must contain the tensor unit")
    if invertibles == len(dimensions):
        return True
    total = sum(d * d for d in dimensions)
    multiplicities = Counter(dimensions)
    del multiplicities[1]
    noninvertible = tuple(sorted(multiplicities))
    support_test = test if test in ("single", "cover") else "gcd"
    use_blocks = test in ("blocks", "combined")
    use_symmetry = test in ("symmetric", "combined")

    @lru_cache(maxsize=None)
    def passes_column(x):
        return column_passes(x, noninvertible, invertibles, total, support_test)

    @lru_cache(maxsize=None)
    def passes_blocks(x):
        return block_column_passes(x, multiplicities, invertibles, total, len(dimensions))

    def passes_neutral(neutral):
        sizes = set(neutral) - {1}
        if not all(passes_column(x) for x in sizes):
            return False
        if use_blocks and not all(passes_blocks(x) for x in sizes):
            return False
        return not use_symmetry or symmetric_support_passes(neutral, dimensions, invertibles, total)

    if invertibles == 1:
        return passes_neutral(dimensions)
    for partition in grading_partitions(dimensions, invertibles):
        # In an actual grading, every block containing an invertible is
        # obtained from the neutral block by tensoring with that object.
        # Thus its dimension multiset is the neutral type. The first
        # block contains 1 since the expanded blocks are sorted.
        if use_symmetry and (not grading_types_compatible(partition)
                             or not orbit_columns_fit(partition, noninvertible, invertibles, total)):
            continue
        if passes_neutral(partition[0]):
            return True
    return False


def read_types(path):
    """Read a whitespace-separated list of integer dimensions on each line."""
    with Path(path).open(encoding="ascii") as stream:
        return [tuple(map(int, line.split())) for line in stream if line.strip()]
