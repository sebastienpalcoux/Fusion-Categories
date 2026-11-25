"""Dimension-block trace and norm tests for a single adjoint column."""
from functools import lru_cache
from math import gcd, isqrt, lcm


def trace_norm_options(multiplicity, energy_limit):
    """Admissible (energy, trace) pairs for one dimension block."""
    yield 0, 0
    for energy in range(1, energy_limit + 1):
        max_trace = isqrt(multiplicity * energy)
        for trace in range(-max_trace, max_trace + 1):
            if multiplicity == 1 and energy != trace * trace:
                continue
            if energy == 1 and abs(trace) != 1:
                continue
            lower, remainder = divmod(trace, multiplicity)
            minimum_energy = ((multiplicity - remainder) * lower**2
                              + remainder * (lower + 1)**2)
            if minimum_energy <= energy:
                yield energy, trace


def block_column_passes(x, multiplicities, invertibles, total, rank):
    """Check a column if x is at least the root-mean-square dimension."""
    if total > rank * x * x:
        return True
    codegree, remainder = divmod(total, x * x)
    if remainder or codegree < invertibles:
        return False
    budget = codegree - invertibles
    blocks = []
    for y, multiplicity in multiplicities.items():
        energy_weight = (lcm(x, y) // x)**2
        if energy_weight > budget:
            continue
        trace_weight = y * y // gcd(x, y)
        choices = tuple((energy_weight * e, trace_weight * b)
                        for e, b in trace_norm_options(multiplicity, budget // energy_weight))
        blocks.append(choices)

    # The target is (budget, -invertibles). Search for one choice in each
    # dimension block. Few-choice blocks first shorten the recursion.
    blocks.sort(key=len)

    @lru_cache(maxsize=None)
    def achievable(index, energy, trace):
        if index == len(blocks):
            return energy == 0 and trace == 0
        return any(achievable(index + 1, energy - e, trace - b)
                   for e, b in blocks[index] if e <= energy)

    return achievable(0, budget, -invertibles)
