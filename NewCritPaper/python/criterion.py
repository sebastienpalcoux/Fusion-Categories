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


def column_passes(x, noninvertible, invertibles, total, test):
    """Apply one of the three bounds to a hypothetical adjoint column x."""
    budget = total - invertibles * x * x
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
    elif test == "gcd":
        options = [(y * y // gcd(x, y), cost) for y, cost in candidates]
        join = gcd

        def accepts(state):
            return state > 0 and invertibles % state == 0
    else:
        raise ValueError(f"unknown test: {test!r}")

    # For each state keep the cheapest subset of dimensions producing it.
    # Repeating a dimension cannot improve a union or a gcd.
    costs = {0: 0}
    for item, cost in options:
        for old, subtotal in tuple(costs.items()):
            new = join(old, item)
            price = subtotal + cost
            if price <= budget and price < costs.get(new, budget + 1):
                if accepts(new):
                    return True
                costs[new] = price
    return False


def passes(dimensions, test="blocks"):
    """Return whether some potential grading passes every adjoint-column test."""
    if test not in ("single", "cover", "gcd", "blocks"):
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
    support_test = "gcd" if test == "blocks" else test

    @lru_cache(maxsize=None)
    def passes_column(x):
        return column_passes(x, noninvertible, invertibles, total, support_test)

    @lru_cache(maxsize=None)
    def passes_blocks(x):
        return block_column_passes(x, multiplicities, invertibles, total, len(dimensions))

    def passes_neutral(sizes):
        if not all(passes_column(x) for x in sizes):
            return False
        return test != "blocks" or all(passes_blocks(x) for x in sizes)

    if invertibles == 1:
        return passes_neutral(noninvertible)
    for partition in grading_partitions(dimensions, invertibles):
        # In an actual grading, every block containing an invertible is
        # obtained from the neutral block by tensoring with that object.
        # Thus its dimension multiset is the neutral type. The first
        # block contains 1 since the expanded blocks are sorted.
        neutral = set(partition[0]) - {1}
        if passes_neutral(neutral):
            return True
    return False


def read_types(path):
    """Read a whitespace-separated list of integer dimensions on each line."""
    with Path(path).open(encoding="ascii") as stream:
        return [tuple(map(int, line.split())) for line in stream if line.strip()]
