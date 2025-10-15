# Euler–Maclaurin Summation (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md

## Canonical Statement (schematic)
For suitable $f$ and integer $N\ge 1$,
$$
\sum_{n=1}^{N} f(n) = \int_{1}^{N} f(x)\,dx + \frac{f(N)+f(1)}{2} + \sum_{k=1}^{m} \frac{B_{2k}}{(2k)!}\,\Big( f^{(2k-1)}(N) - f^{(2k-1)}(1) \Big) + R_{m},
$$
with Bernoulli numbers $B_{2k}$ and remainder $R_{m}$ as specified in the admitted sources.

## Dense Summary (non‑canonical)
- Canonical Euler–Maclaurin is recorded for analytic approximations; Bernoulli terms match those recorded under L01/Bernoulli Values.

## Proof chain bullets (from original sources; upward only)
- Cite `docs/zeta/zeta-analytic-continuation-chaos.md` for the project‑admitted Euler–Maclaurin usage and remainder forms.
