# Dimension-type tests for integral modular categories

This directory accompanies the paper by Jingcheng Dong and Sébastien Palcoux. A type lists the Frobenius–Perron dimensions of the simple objects, with repetitions. All calculations use exact integers and the Python 3.9+ standard library.

From this directory run

```sh
python3 reproduce.py
python3 verify.py
```

To export the final rank-15 list to another file, run `python3 reproduce.py --write-survivors remaining.txt`. The program compares the entire computed list with the supplied [rank15-survivors.txt](data/rank15-survivors.txt).

| Candidate list | Input | Single prime | Simultaneous primes | GCD | Dimension blocks |
|---|---:|---:|---:|---:|---:|
| Rank 14, residual | 34 | 2 | 2 | 2 | 2 |
| Rank 15, non-perfect | 399 | 140 | 132 | 110 | 47 |
| Rank 15, perfect | 8,628 | 2,341 | 1,861 | 1,861 | 311 |
| Rank 15, all non-pointed candidates | 9,027 | 2,481 | 1,993 | 1,971 | 358 |
| Rank 15, examples from the first version | 18 | 18 | 14 | 14 | 3 |
| Odd rank 25, residual | 3 | 0 | 0 | 0 | 0 |
| Odd rank 25, earlier list | 91 | 3 | 3 | 3 | 0 |

## Algorithm

Given a type, `passes(dimensions, test="blocks")` in [criterion.py](criterion.py) returns whether it survives the selected necessary condition. Let `D` be the sum of squared dimensions and `g` the number of entries equal to 1. The program enumerates all unordered partitions into `g` parts of square sum `D/g`. These include every universal grading and can also include partitions which no category realizes. In a realizable partition, each component containing an invertible is a translate of the neutral component and has the same type. The lexicographically first part contains a 1, so it has the neutral type in any actual grading. The candidate survives if some partition passes the column test for every noninvertible dimension `x` of its first part.

For each such `x`, a distinct noninvertible dimension `y` costs `lcm(x,y)**2` against the budget `D - g*x*x`.

- `single` checks separately for each prime dividing `x` but not `g` that at least one affordable `y` is prime to it.
- `cover` requires one subset of dimensions within budget that covers all these primes. Each selected dimension can cover several primes.
- `gcd` requires a nonempty subset within budget for which the gcd of the integers `y*y // gcd(x,y)` divides `g`.

For the cover and gcd tests the program retains the cheapest subset producing each prime mask or gcd. Each dimension is processed once because repetitions have no effect on either state and have positive cost.

The final `blocks` test imposes the gcd condition for every adjoint dimension and also checks the signed trace and exact norm equations when `D/x² ≤ rank`. For each dimension `y` of multiplicity `n`, let `b` and `e` be its integral trace and energy. Write `b = nq + r` with `0 ≤ r < n`. The program requires

- `e ≥ (n-r)q² + r(q+1)²`
- `e = b²` when `n = 1`
- `|b| = 1` when `e = 1`.

[blocks.py](blocks.py) looks for one pair per noninvertible dimension, with total weighted trace `−g` and total weighted energy `D/x² − g`. The weights are respectively `y²/gcd(x,y)` and `(lcm(x,y)/x)²`. The cutoff is equivalent to choosing `x` at least as large as the root-mean-square simple dimension. Passing the computation is a necessary condition for categorification.

[verify.py](verify.py) independently recomputes the final survivor lists from all supplied inputs. It places the objects in components one at a time, enumerates witness subsets directly, and accumulates attainable pairs of weighted energy and trace one dimension at a time. It compares the full rank-15 result with all 358 rows of the supplied list. It also checks the individual algorithms on small inputs, compares the original single-prime survivors with the digest of the published list, and tests the untwisted centers for `S3`, `A4`, `A5`, and the nonabelian group of order 21.

The verifier also checks the arithmetic certificates in the paper directly against the input rows. At rank 14 it checks the stated column and prime for each of the 32 exclusions. On the initial odd rank-25 list it checks the single-prime obstruction in 88 rows and the three centered-residue inequalities in rows 8, 26 and 37.

## Three arithmetic exclusions at rank 25

Rows 8, 26 and 37 of the initial list each have one invertible and total dimension $9x^2$, where $x$ is the largest simple dimension. Fix a simple $X$ of dimension $x$. The unit uses one of the nine units in the normalized column norm. If a dimension $y$ fails to divide $x$, the odd integer $y/\gcd(x,y)$ is at least three. A nonzero entry of this dimension would use at least nine units in the averaged norm, so all such entries vanish.

For each remaining non-unit simple $Y$, write $y=\mathrm{FPdim}(Y)$ and $z_Y=s_{X,Y}/x$. Then $\sum_Y |z_Y|^2=8$ and $\sum_Y y z_Y=-1$. For each dimension $y$, the sum of the $z_Y$ with that dimension is an integer by §3.1 of the paper. Choose integers $m,a$ with $0<2a<m$ and take the centered residue $r_y$ of $ay$ modulo $m$. It follows that $\sum_Y r_y z_Y$ is an integer congruent to $-a$ modulo $m$. Its absolute value is at least $a$. Cauchy–Schwarz therefore requires $a^2\leq 8\sum_Y r_y^2$, counting repeated dimensions separately. Each row violates the inequality.

| Row | $x$ | $m$ | $a$ | $a^2$ | $8\sum_Y r_y^2$ |
|---:|---:|---:|---:|---:|---:|
| 8 | 36,225 | 289 | 78 | 6,084 | 6,080 |
| 26 | 55,575 | 329 | 101 | 10,201 | 8,288 |
| 37 | 2,594,625 | 17 | 7 | 49 | 16 |

## Data sources

Each file in [data](data) has one type per line, with dimensions in nondecreasing order. Row numbers start at 1. The following links identify a fixed upstream revision.

`reproduce.py` validates every input row before grouping by the number of invertibles. It checks that the 18 rank-15 examples belong to the full rank-15 list and that the three residual odd rank-25 types belong to the original 91. `verify.py` checks all five ordered input lists against SHA-256 digests of the archived tables, using decimal integers separated by one space and one newline per row. This check includes rows eliminated by the first test. [Archived tables](https://github.com/sebastienpalcoux/Fusion-Categories/tree/f095dd0b5484d1903572a12abda275ab76ab4097/NewCritPaper/python/data)

- [rank14.txt](data/rank14.txt) contains the seven non-perfect and 27 perfect residual types. It has the same rows as the upstream list `Lin`, with the seven non-perfect types in their original order. [Rank-14 investigation](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestRank14.txt)
- [rank15.txt](data/rank15.txt) is the sorted union of the 262 entries in the displayed `Lout` and the 8,765 entries in the displayed `L2` of the rank-15 investigation. The old surviving arrays are `NP` and `P`. The lists here use an expanded, whitespace-separated format. [Input](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestRank15.txt) · [Original 2,481 survivors](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/NewCritPaper/Rank15/RemainingTypes.txt)
- [rank15-examples.txt](data/rank15-examples.txt) preserves the order of the 18 examples in §4.3 of both the first arXiv version and the submitted manuscript. The simultaneous-prime test excludes rows 3, 5, 6 and 10. The remaining fourteen pass the gcd test. The dimension-block test leaves rows 1, 2 and 4. [First arXiv version](https://arxiv.org/html/2510.10311v1#S4.SS3) · [Submitted manuscript](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/NewCritPaper/Version20260715.pdf)
- [rank25-odd-91.txt](data/rank25-odd-91.txt) is the expanded initial list `L` in the odd rank-25 investigation. [rank25-odd.txt](data/rank25-odd.txt) contains the three final unresolved types in that file. The first three tests leave rows 8, 26 and 37 of the initial list and exclude all three residual types. The dimension-block test excludes the entire initial list. [Odd rank-25 investigation](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestMNSDPerfectR25.txt)
