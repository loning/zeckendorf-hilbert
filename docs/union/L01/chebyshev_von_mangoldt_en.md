# Chebyshev & von Mangoldt (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md

## Canonical Definitions
Chebyshev theta function:
$$
\theta(x) = \sum_{p \le x} \log p\,,
$$
Chebyshev psi function:
$$
\psi(x) = \sum_{n \le x} \Lambda(n)\,,\qquad \Lambda(n) = \begin{cases}
 \log p, & n=p^{k}\ (p\ \text{prime},\ k\ge 1),\\
 0, & \text{otherwise.}
\end{cases}
$$

## Canonical Asymptotics (recorded in the union)
Prime number theorem (equivalent canonical forms):
$$
\pi(x) \sim \frac{x}{\log x},\qquad \psi(x) \sim x,\qquad (x\to\infty).
$$

## Dense Summary (non‑canonical)
- These canonical definitions underpin explicit‑formula usage and oscillation analyses; upper layers must keep them in full and cite the precise sources.

## Proof chain bullets (from original sources; upward only)
- Cite `docs/zeta/zeta-series-product-analysis.md` for definitions of $\theta(x),\ \psi(x),\ \Lambda(n)$ and their roles in explicit‑formula contexts.
- For asymptotics (PNT equivalences), cite the canonical statements stored in the admitted analytic‑number‑theory references indexed by the project.
