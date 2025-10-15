# Approximate Functional Equation for $\zeta(s)$ (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md

## Canonical Form (recorded in the union)
For $s=\sigma+it$ with $0\le \sigma \le 1$ and $t\in\mathbb{R}$, an approximate functional equation for $\zeta(s)$ can be written in canonical form (parameters chosen as admitted by the project’s sources):
$$
\zeta(s) = \sum_{n\leq N} \frac{1}{n^{s}} + \chi(s)\,\sum_{n\leq M} \frac{1}{n^{1-s}} + R(s;N,M),
$$
where $\chi(s) = 2^{s}\,\pi^{s-1}\,\sin\!\left(\tfrac{\pi s}{2}\right)\,\Gamma(1-s)$ and the remainder $R(s;N,M)$ is controlled by canonical bounds stated in the admitted sources.

## Dense Summary (non‑canonical)
- This canonical‑form record allows upper layers to refer to analytic expansions of $\zeta(s)$ without altering the source expression; bounds on $R(s;N,M)$ are cited as given in the original sources.

## Proof chain bullets (from original sources; upward only)
- Cite non‑summary entries where the AFE is used in the project: `docs/pure-zeta/zeta-universe-complete-framework.md` (critical‑line oscillatory sums via AFE) and `docs/zeta/zeta-holographic-hilbert-completeness.md` (AFE mention); pair with the completed/non‑completed functional equations recorded in L01/functional_equation_derivation_en.md.
