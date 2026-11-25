# Dimension-type tests for integral modular categories

This directory accompanies [*A new criterion for integral modular categorification*](../README.md) by Jingcheng Dong and Sébastien Palcoux. A type lists the Frobenius–Perron dimensions of the simple objects, with repetitions. All calculations use exact integers and the Python 3.9+ standard library.

To reproduce the manuscript and independently verify its results, run these commands from this directory.

```sh
python3 reproduce.py --manuscript
python3 verify.py
```

The manuscript tests the [rank-15 census](data/rank15.txt) with Theorem 1.1, using a common symmetric support and the bounds for equal dimensions described below.

| Candidate types | Input | Excluded | Remaining |
|---|---:|---:|---:|
| Non-perfect | 399 | 354 | 45 |
| Perfect | 8,628 | 8,378 | 250 |
| Total | 9,027 | 8,732 | 295 |

The [manuscript list](data/rank15-manuscript-survivors.txt) contains all 295 types, one per line. To export it from the census, run `python3 reproduce.py --manuscript --write-survivors remaining.txt`. For intermediate counts on all datasets, use `python3 reproduce.py --stages`. [Reproduction script](reproduce.py)

## Algorithm

Given a type, `passes(dimensions, test="manuscript")` in [criterion.py](criterion.py) applies the manuscript tests. Let `D` be the sum of squared dimensions and `g` the number of entries equal to 1. The program enumerates all unordered partitions into `g` parts of square sum `D/g`. These include every universal grading and can also include partitions which no category realizes. In a realizable partition, each component containing an invertible is a translate of the neutral component and has the same type. The lexicographically first part contains a 1, so it has the neutral type in any actual grading. All conditions must hold for the same proposed grading.

For each possible adjoint dimension `x`, (1.1) of Theorem 1.1 allows a total of `D - g*x*x` for the non-invertible terms in the column. Every supported simple of dimension `y` contributes at least `lcm(x,y)**2`. By (1.2), the gcd of `y*y // gcd(x,y)` over this support divides `g`. Each coefficient is a multiple of `y` and divides `y*y`. In a perfect type (`g = 1`), this is exactly (1.3): the supported non-unit dimensions have gcd one. The [support test](criterion.py) searches for a nonempty subset of dimensions satisfying the bound and divisibility, retaining the least cost for each gcd. Repeated dimensions do not affect a gcd and are counted only once in this necessary test.

## Symmetric supports

The two sides of a nonzero entry $s_{X,Y}=s_{Y,X}$ must fit in both column budgets. The [symmetric support test](criterion.py) therefore searches for a single pattern of nonzero entries satisfying (1.1) in every column and (1.2) in every non-invertible adjoint column. Each simple gets its own row and column, even when dimensions coincide. An edge between distinct simples contributes in both columns; a diagonal entry contributes once. In odd dimension the unit is the only self-dual simple. For the non-unit dimensions we can therefore search on dual pairs: $s_{X,Y^*}=\overline{s_{X,Y}}$ implies that an entry is nonzero for both members or for neither. The neutral component is closed under duals. A supported pair of simples of dimension $y$ uses twice the usual weight in a column of dimension $x$, including when the two dual pairs coincide. [Odd-dimensional categories, §12](https://arxiv.org/abs/2302.01613)

In a column of dimension $x$, put $a=y^2/\gcd(x,y)$ for a possible neighbor of dimension $y$. For every prime $p$, some chosen coefficient must avoid divisibility by the smallest power of $p$ which fails to divide $g$. We also require at least one neighbor in each non-invertible adjoint column. The search starts with zero gcds and full budgets. At each step it chooses an unsatisfied requirement and tries every entry that could fulfill it, charging the corresponding column budgets and updating their gcds. Such an entry is always new: an entry already chosen would have fulfilled that requirement. The search can discard a state if even the currently affordable terms of a single column cannot complete its gcd within its budget. [The verifier](verify.py) gives an independent enumeration by choosing entire minimal witness subsets.

The two exceptional [rank-14 types](data/rank14.txt#L1-L2) pass this test. In both, the neutral component consists of all but the two largest simples. Take the unique dimension-two simple to meet every non-invertible adjoint simple, including itself. Take all four entries between the two dimension-three simples, and add diagonal entries for the two largest simples. This gives a symmetric support satisfying the inequalities and divisibility. The paper excludes the two types using a centralizer.

In contrast, [rank-15 example 17](data/rank15-examples.txt#L17) fails by symmetry. Its global dimension is $4\cdot12600^2$. The three columns of dimension $12600$ and the column of dimension $2520$ each need an entry of dimension prime to $3$ by (1.3). In these columns the only affordable choice is the unique dimension $175$. Symmetry forces all four entries into its column, each costing $12600^2$ in (1.1). They already account for the global dimension, and there is still the contribution from the unit.

## Equal-dimension bounds

The census imposes the support conditions on each non-invertible adjoint dimension $x$. When $D/x^2$ is at most the rank, it also uses the two column identities grouped by simple dimension. For the $n$ entries in a block of dimension $y$, write $z_i=s_{X,Y_i}/\mathrm{lcm}(x,y)$, including zero entries. Put $b=\sum_i z_i$ and $e=\sum_i |z_i|^2$. Galois conjugation permutes this list: it permutes characters and preserves simple dimensions because their formal codegrees $D/y^2$ are rational. Since each $z_i$ is a cyclotomic integer, both $b$ and $e$ are rational integers.

The [block test](blocks.py) uses the following necessary conditions for $(e,b)$.

- A nonzero cyclotomic integer has Galois mean square at least one by the arithmetic–geometric mean inequality applied to its norm. Thus each nonzero orbit in a block contributes at least its size to $e$. If $e=1$, there is exactly one nonzero entry. It is Galois-fixed, hence a rational integer, and equals $1$ or $-1$. Consequently $|b|=1$. For a singleton block the entry is always a rational integer, so $e=b^2$.
- Write $b=nq+r$, with $0\le r<n$. None of the cyclotomic integers $2z_i-2q-1$ vanishes, since the half-integer $q+1/2$ is not an algebraic integer. The transformed list is still Galois-stable, so $\sum_i|2z_i-2q-1|^2\ge n$. Expansion gives $e\ge(2q+1)b-nq(q+1)=(n-r)q^2+r(q+1)^2$.

The code looks for one such pair per non-invertible dimension. The weighted sum of the $b$'s must equal $-g$, with weights $y^2/\gcd(x,y)$. The weighted sum of the $e$'s must equal $D/x^2-g$, with weights $(\mathrm{lcm}(x,y)/x)^2$. The cutoff restricts this extra computation to $x$ at least as large as the root-mean-square simple dimension.

For example, [row 13 of the eighteen rank-15 types](data/rank15-examples.txt#L13) is perfect. For $x=3780$, the normalized column norm leaves $D/x^2-1=3$ after the unit is counted. There are two simples of dimension $70$, and $70$ divides $x$. Their block sum $b$ is an integer and Cauchy–Schwarz gives $b^2\le 2\cdot 3$. All other non-unit dimensions are divisible by $9$. Orthogonality with the unit column therefore gives $70b\equiv-1\pmod 9$, or $b\equiv-4\pmod 9$, which is impossible. The [verifier](verify.py) checks the arithmetic for this row.

## Verification

[verify.py](verify.py) independently recomputes the final survivor lists from all supplied inputs. It places the objects in components one at a time, enumerates witness subsets directly, and accumulates attainable pairs of weighted energy and trace one dimension at a time. It also searches symmetric supports by choosing whole minimal witness sets. It checks the [manuscript list](data/rank15-manuscript-survivors.txt) and the list from the optional calculation below row by row. It also checks the individual algorithms on small inputs, compares the original single-prime survivors with the digest of the published list, and tests the untwisted centers for `S3`, `A4`, `A5`, and the nonabelian group of order 21.

The [verifier](verify.py) also checks the paper’s rank-14 hand example, column and prime certificates for all 32 rank-14 exclusions, and the three dimension and prime choices for the [residual odd rank-25 types](data/rank25-odd.txt). On the [initial list of 91 odd rank-25 types](data/rank25-odd-91.txt), it checks the single-prime obstruction in 88 rows. In the remaining rows 8, 26 and 37, the largest multiplicity is eight and the dimension is divisible by 23, 19 and 37, respectively. Each prime exceeds twice the largest multiplicity plus one, contrary to [Alekseyev–Bruns–Palcoux–Petrov, Theorem 8.5](https://arxiv.org/abs/2302.01613). Theorem 1.1 gives a separate proof for these three rows using duality.

## The three odd rank-25 rows

In [rows 8, 26 and 37](data/rank25-odd-91.txt) take respectively $(p,y)=(3,115),(3,65),(11,51)$. Only the two simples of dimension $y$ have non-unit dimension coprime to $p$. They form a dual pair. By (1.3) each non-unit column is nonzero at one member of the pair and hence at both. Symmetry now gives an everywhere nonzero column of dimension $y$. Its left side in (1.1) is at least $y^2+\sum_{X\ne\mathbf1}\mathrm{FPdim}(X)^2=D+y^2-1>D$, a contradiction. Thus (1.1) and (1.3), together with symmetry and duality, exclude all 91 types. [Arithmetic certificates](verify.py)

### An independent calculation with equal dimensions

Rows 8, 26 and 37 of the initial list each have one invertible and total dimension $9x^2$, where $x$ is the largest simple dimension. Fix a simple $X$ of dimension $x$. The unit uses one of the nine units in the normalized column norm. If a dimension $y$ fails to divide $x$, the odd integer $y/\gcd(x,y)$ is at least three. A nonzero entry of this dimension would use at least nine units in the averaged norm, so all such entries vanish.

For each remaining non-unit simple $Y$, write $y=\mathrm{FPdim}(Y)$ and $z_Y=s_{X,Y}/x$. Then $\sum_Y |z_Y|^2=8$ and $\sum_Y y z_Y=-1$. For each dimension $y$, the sum of the $z_Y$ with that dimension is an integer by Section 3 of the paper. Choose integers $m,a$ with $0<2a<m$ and take the centered residue $r_y$ of $ay$ modulo $m$. It follows that $\sum_Y r_y z_Y$ is an integer congruent to $-a$ modulo $m$. Its absolute value is at least $a$. Cauchy–Schwarz therefore requires $a^2\leq 8\sum_Y r_y^2$, counting repeated dimensions separately. Each row violates the inequality.

| Row | $x$ | $m$ | $a$ | $a^2$ | $8\sum_Y r_y^2$ |
|---:|---:|---:|---:|---:|---:|
| 8 | 36,225 | 289 | 78 | 6,084 | 6,080 |
| 26 | 55,575 | 329 | 101 | 10,201 | 8,288 |
| 37 | 2,594,625 | 17 | 7 | 49 | 16 |

## Optional rank-15 refinement

Running `python3 reproduce.py` without `--manuscript` applies two further checks. They exclude four rows of the full census and leave [291 types](data/rank15-survivors.txt), including 41 non-perfect and 250 perfect types. The option `--write-survivors remaining.txt` exports this list.

- **Graded components.** If the image of the invertibles in the grading group has order $h$, its cosets consist of $h$ components of the same type. In a quotient of odd order, every nonidentity coset and its inverse are distinct and have the same component type. With three invertibles the two non-neutral components must have the same type, so every dimension of odd multiplicity must occur in the neutral component. In census row 17, the unique simple of dimension 6 alone fills its dimension $36$, leaving no room for the unit. In row 18, the required dimensions $1,2,3,4,6$ contribute $66>48$. [Census rows 17 and 18](data/rank15.txt#L17-L18)
- **Orbits of invertibles.** Tensoring by an invertible preserves column support. If $k$ invertibles belong to the neutral component, the stabilizer of a simple of dimension $x$ has order dividing both $k$ and $x^2$. Thus the multiplicity of $x$ in each component is divisible by $k/\gcd(k,x^2)$, and a supported witness of that dimension contributes at least $g/\gcd(k,x^2)$ entries. In census row 9, the four adjoint dimension-three simples form one orbit. By (1.2) all four must meet the same dimension-four column. Its four contributions of $12^2$ already exhaust the global dimension. In row 10, a dimension-three simple must have orbit size four, but the type contains only two such simples. [Census rows 9 and 10](data/rank15.txt#L9-L10) · [Dong–Natale–Vendramin, Lemma 2.2](https://doi.org/10.1142/S0219498815500115)

## Data sources

Each file in [data](data) has one type per line, with dimensions in nondecreasing order. Row numbers start at 1. The following links identify a fixed upstream revision.

[reproduce.py](reproduce.py) validates every input row before grouping by the number of invertibles. It checks that the 18 rank-15 examples belong to the full rank-15 list and that the three residual odd rank-25 types belong to the original 91. [verify.py](verify.py) checks all five ordered input lists against SHA-256 digests of the archived tables, using decimal integers separated by one space and one newline per row. This check includes rows eliminated by the first test. [Archived tables](https://github.com/sebastienpalcoux/Fusion-Categories/tree/f095dd0b5484d1903572a12abda275ab76ab4097/NewCritPaper/python/data)

- [rank14.txt](data/rank14.txt) contains the seven non-perfect and 27 perfect residual types. It has the same rows as the upstream list `Lin`, with the seven non-perfect types in their original order. [Rank-14 investigation](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestRank14.txt)
- [rank15.txt](data/rank15.txt) is the sorted union of the 262 entries in the displayed `Lout` and the 8,765 entries in the displayed `L2` of the rank-15 investigation. The old surviving arrays are `NP` and `P`. The lists here use an expanded, whitespace-separated format. [Input](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestRank15.txt) · [Original 2,481 survivors](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/NewCritPaper/Rank15/RemainingTypes.txt)
- [rank15-examples.txt](data/rank15-examples.txt) preserves the order of the 18 examples in §4.3 of both the first arXiv version and the submitted manuscript. The simultaneous-prime test excludes rows 3, 5, 6 and 10. The remaining fourteen pass the gcd test. The test using symmetry also excludes rows 15, 17 and 18. With the equal-dimension bounds, rows 1, 2 and 4 pass all the tests. [First arXiv version](https://arxiv.org/html/2510.10311v1#S4.SS3) · [Submitted manuscript](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/NewCritPaper/Version20260715.pdf)
- [rank25-odd-91.txt](data/rank25-odd-91.txt) is the expanded initial list `L` in the odd rank-25 investigation. [rank25-odd.txt](data/rank25-odd.txt) contains the three final unresolved types in that file. Theorem 1.1 excludes all three residual types. Rows 8, 26 and 37 of the initial list pass the single-column test. The symmetry and duality of the support exclude these three as well. The equal-dimension test gives an independent exclusion of the entire initial list. [Odd rank-25 investigation](https://github.com/sebastienpalcoux/Fusion-Categories/blob/06f3a37b086c0591e086a3aed9a9458f4270165f/ModularPaper/Data/InvestMNSDPerfectR25.txt)
