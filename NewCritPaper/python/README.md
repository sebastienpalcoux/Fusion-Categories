# Dimension-type tests for integral modular categories

This directory accompanies [*A new criterion for integral modular categorification*](../README.md) by Jingcheng Dong and Sébastien Palcoux. A type lists the Frobenius–Perron dimensions of the simple objects, with repetitions. All calculations use exact integers and the Python 3.9+ standard library.

Run [reproduce.py](reproduce.py) and [verify.py](verify.py) from this directory

```sh
python3 reproduce.py
python3 verify.py
```

The [rank-15 census](data/rank15.txt) gives the following counts.

| Candidate types | Input | Excluded | Remaining |
|---|---:|---:|---:|
| Non-perfect | 399 | 352 | 47 |
| Perfect | 8,628 | 8,317 | 311 |
| Total | 9,027 | 8,669 | 358 |

To export the 358 types, run [`python3 reproduce.py --write-survivors remaining.txt`](reproduce.py). The program compares every computed row with the [published list](data/rank15-survivors.txt). For intermediate arithmetic checks on all datasets, use [`python3 reproduce.py --stages`](reproduce.py).

## Algorithm

Given a type, `passes(dimensions, test="blocks")` in [criterion.py](criterion.py) returns whether it survives the selected necessary condition. Let `D` be the sum of squared dimensions and `g` the number of entries equal to 1. The program enumerates all unordered partitions into `g` parts of square sum `D/g`. These include every universal grading and can also include partitions which no category realizes. In a realizable partition, each component containing an invertible is a translate of the neutral component and has the same type. The lexicographically first part contains a 1, so it has the neutral type in any actual grading. The candidate survives if some partition passes the column test for every noninvertible dimension `x` of its first part.

For each possible adjoint dimension `x`, (1.1) of Theorem 1.1 allows a total of `D - g*x*x` for the non-invertible terms in the column. Every supported simple of dimension `y` contributes at least `lcm(x,y)**2`. By (1.2), the gcd of `y*y // gcd(x,y)` over this support divides `g`. Each coefficient is a multiple of `y` and divides `y*y`. In a perfect type (`g = 1`), this is exactly (1.3): the supported non-unit dimensions have gcd one. The [support test](criterion.py) searches for a nonempty subset of dimensions satisfying the bound and divisibility, retaining the least cost for each gcd. Repeated dimensions do not affect a gcd and are counted only once in this necessary test.

## Equal-dimension bounds

The census imposes the support conditions on each non-invertible adjoint dimension $x$. When $D/x^2$ is at most the rank, it also uses the two column identities grouped by simple dimension. For the $n$ entries in a block of dimension $y$, write $z_i=s_{X,Y_i}/\mathrm{lcm}(x,y)$, including zero entries. Put $b=\sum_i z_i$ and $e=\sum_i |z_i|^2$. Galois conjugation permutes this list: it permutes characters and preserves simple dimensions because their formal codegrees $D/y^2$ are rational. Since each $z_i$ is a cyclotomic integer, both $b$ and $e$ are rational integers.

The [block test](blocks.py) uses the following necessary conditions for $(e,b)$.

- A nonzero cyclotomic integer has Galois mean square at least one by the arithmetic–geometric mean inequality applied to its norm. Thus each nonzero orbit in a block contributes at least its size to $e$. If $e=1$, there is exactly one nonzero entry. It is Galois-fixed, hence a rational integer, and equals $1$ or $-1$. Consequently $|b|=1$. For a singleton block the entry is always a rational integer, so $e=b^2$.
- Write $b=nq+r$, with $0\le r<n$. None of the cyclotomic integers $2z_i-2q-1$ vanishes, since the half-integer $q+1/2$ is not an algebraic integer. The transformed list is still Galois-stable, so $\sum_i|2z_i-2q-1|^2\ge n$. Expansion gives $e\ge(2q+1)b-nq(q+1)=(n-r)q^2+r(q+1)^2$.

The code looks for one such pair per non-invertible dimension. The weighted sum of the $b$'s must equal $-g$, with weights $y^2/\gcd(x,y)$. The weighted sum of the $e$'s must equal $D/x^2-g$, with weights $(\mathrm{lcm}(x,y)/x)^2$. The cutoff restricts this extra computation to $x$ at least as large as the root-mean-square simple dimension.

For example, [row 13 of the eighteen rank-15 types](data/rank15-examples.txt#L13) is perfect. For $x=3780$, the normalized column norm leaves $D/x^2-1=3$ after the unit is counted. There are two simples of dimension $70$, and $70$ divides $x$. Their block sum $b$ is an integer and Cauchy–Schwarz gives $b^2\le 2\cdot 3$. All other non-unit dimensions are divisible by $9$. Orthogonality with the unit column therefore gives $70b\equiv-1\pmod 9$, or $b\equiv-4\pmod 9$, which is impossible. The [verifier](verify.py) checks the arithmetic for this row.

## Verification

[verify.py](verify.py) independently recomputes the final survivor lists from all supplied inputs. It places the objects in components one at a time, enumerates witness subsets directly, and accumulates attainable pairs of weighted energy and trace one dimension at a time. It compares the full rank-15 result with all 358 rows of the [supplied list](data/rank15-survivors.txt). It also checks the individual algorithms on small inputs, compares the original single-prime survivors with the digest of the published list, and tests the untwisted centers for `S3`, `A4`, `A5`, and the nonabelian group of order 21.

The [verifier](verify.py) also checks the paper’s rank-14 hand example, column and prime certificates for all 32 rank-14 exclusions, and the three dimension and prime choices for the [residual odd rank-25 types](data/rank25-odd.txt). On the [initial list of 91 odd rank-25 types](data/rank25-odd-91.txt), it checks the single-prime obstruction in 88 rows. In the remaining rows 8, 26 and 37, the largest multiplicity is eight and the dimension is divisible by 23, 19 and 37, respectively. Each prime exceeds twice the largest multiplicity plus one, contrary to [Alekseyev–Bruns–Palcoux–Petrov, Theorem 8.5](https://arxiv.org/abs/2302.01613). The following calculation gives a second exclusion of the same three rows.

## An independent calculation for the three odd rank-25 rows

Rows 8, 26 and 37 of the initial list each have one invertible and total dimension $9x^2$, where $x$ is the largest simple dimension. Fix a simple $X$ of dimension $x$. The unit uses one of the nine units in the normalized column norm. If a dimension $y$ fails to divide $x$, the odd integer $y/\gcd(x,y)$ is at least three. A nonzero entry of this dimension would use at least nine units in the averaged norm, so all such entries vanish.

For each remaining non-unit simple $Y$, write $y=\mathrm{FPdim}(Y)$ and $z_Y=s_{X,Y}/x$. Then $\sum_Y |z_Y|^2=8$ and $\sum_Y y z_Y=-1$. For each dimension $y$, the sum of the $z_Y$ with that dimension is an integer by Section 3 of the paper. Choose integers $m,a$ with $0<2a<m$ and take the centered residue $r_y$ of $ay$ modulo $m$. It follows that $\sum_Y r_y z_Y$ is an integer congruent to $-a$ modulo $m$. Its absolute value is at least $a$. Cauchy–Schwarz therefore requires $a^2\leq 8\sum_Y r_y^2$, counting repeated dimensions separately. Each row violates the inequality.

| Row | $x$ | $m$ | $a$ | $a^2$ | $8\sum_Y r_y^2$ |
|---:|---:|---:|---:|---:|---:|
| 8 | 36,225 | 289 | 78 | 6,084 | 6,080 |
| 26 | 55,575 | 329 | 101 | 10,201 | 8,288 |
| 37 | 2,594,625 | 17 | 7 | 49 | 16 |

## Data sources

Each file in [data](data) has one type per line, with dimensions in nondecreasing order. Row numbers start at 1. The following links identify a fixed upstream revision.

[reproduce.py](reproduce.py) validates every input row before grouping by the number of invertibles. It checks that the 18 rank-15 examples belong to the full rank-15 list and that the three residual odd rank-25 types belong to the original 91. [verify.py](verify.py) checks all five ordered input lists against SHA-256 digests of the archived tables, using decimal integers separated by one space and one newline per row. This check includes rows eliminated by the first test. [Archived tables](https://github.com/sebastienpalcoux/Fusion-Categories/tree/f095dd0b5484d1903572a12abda275ab76ab4097/NewCritPaper/python/data)

- [rank14.txt](data/rank14.txt) contains the seven non-perfect and 27 perfect residual types. It has the same rows as the upstream list `Lin`, with the seven non-perfect types in their original order. [Rank-14 investigation](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestRank14.txt)
- [rank15.txt](data/rank15.txt) is the sorted union of the 262 entries in the displayed `Lout` and the 8,765 entries in the displayed `L2` of the rank-15 investigation. The old surviving arrays are `NP` and `P`. The lists here use an expanded, whitespace-separated format. [Input](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestRank15.txt) · [Original 2,481 survivors](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/NewCritPaper/Rank15/RemainingTypes.txt)
- [rank15-examples.txt](data/rank15-examples.txt) preserves the order of the 18 examples in §4.3 of both the first arXiv version and the submitted manuscript. The simultaneous-prime test excludes rows 3, 5, 6 and 10. The remaining fourteen pass the gcd test. The dimension-block test leaves rows 1, 2 and 4. [First arXiv version](https://arxiv.org/html/2510.10311v1#S4.SS3) · [Submitted manuscript](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/NewCritPaper/Version20260715.pdf)
- [rank25-odd-91.txt](data/rank25-odd-91.txt) is the expanded initial list `L` in the odd rank-25 investigation. [rank25-odd.txt](data/rank25-odd.txt) contains the three final unresolved types in that file. The first three tests leave rows 8, 26 and 37 of the initial list and exclude all three residual types. The dimension-block test excludes the entire initial list. [Odd rank-25 investigation](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestMNSDPerfectR25.txt)
