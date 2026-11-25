# A new criterion for integral modular categorification

Jingcheng Dong and Sébastien Palcoux

Theorem 1.1 bounds the nonzero entries of a column of the modular $S$-matrix and gives a divisibility condition for a non-invertible simple object in the adjoint subcategory. In a perfect category, (1.3) says that the non-unit dimensions in the support of each non-unit column have gcd one. The [Python implementation and reproduction instructions](python/README.md) explain how these two conditions are used to test candidate types.

- [Input lists and their sources](python/README.md#data-sources)
- [The 295 rank-15 types reported in the manuscript](python/data/rank15-manuscript-survivors.txt) comprise 45 non-perfect and 250 perfect types.
- [Reproduce the counts](python/reproduce.py) and [verify them independently](python/verify.py) with the Python 3.9+ standard library.

The [submitted manuscript](Version20260715.pdf) and its [rank-15 list](Rank15/RemainingTypes.txt) document the earlier computation. The [arXiv record](https://arxiv.org/abs/2510.10311) gives the preprint versions.
