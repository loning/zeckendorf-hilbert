# Matrix Generating Functions (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/matrix_foundations_en.md
- L00 · ../L00/hilbert_foundations_en.md

## Canonical Generating Functions
Given a sequence $(f_i(n))_{n\ge 0}$, define
$$
\Omega_{i}(z) = \sum_{n=0}^{\infty} f_{i}(n)\,z^{n}.
$$
Normalized vector correspondence (canonical usage):
$$
\mathbf{e}_{i} = \sum_{n=0}^{\infty} c_{i,n}\,\mathbf{e}_{n},\qquad c_{i,n} = \frac{f_{i}(n)}{\sqrt{\sum_{m=0}^{\infty} \left|f_{i}(m)\right|^{2} + \varepsilon}},\ \ \left\|\mathbf{e}_{i}\right\|=1.
$$

## Dense Summary (non‑canonical)
- This page records canonical forms for generating‑function usage and their Hilbert‑space normalization; it underpins M2‑style mappings.

## Proof chain bullets (from original sources; upward only)
- Cite `docs/the-matrix/01-foundations/1.1-zkt-tensor-representation.md` for sequence/representation conventions.
- Cite `docs/the-matrix/01-foundations/1.2-infinite-matrix-definition.md` for infinite‑matrix and vector conventions.
- Cite `docs/the-matrix/01-foundations/1.3-evolution-operators.md` for operator‑level semantics.
