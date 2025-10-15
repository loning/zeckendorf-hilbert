# Dirichlet Eta Function (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md

## Canonical Definitions
Alternating Dirichlet series (for $\operatorname{Re}(s)>0$):
$$
\eta(s) = \sum_{n=1}^{\infty} \frac{(-1)^{n-1}}{n^{s}},\qquad \operatorname{Re}(s) > 0.
$$
Relation to $\zeta(s)$ (canonical):
$$
\eta(s) = \big(1 - 2^{1-s}\big)\,\zeta(s),\qquad s\in\mathbb{C},
$$
which provides analytic continuation of $\zeta(s)$ away from $s=1$.

## Dense Summary (non‑canonical)
- The canonical identity $\eta(s)=(1-2^{1-s})\zeta(s)$ is recorded to support analytic‑continuation arguments without altering source formulas.

## Proof chain bullets (from original sources; upward only)
- Cite `docs/pure-zeta/zeta-analytic-continuation-chaos.md` for the alternating series and its relation to $\zeta(s)$; keep the $(1-2^{1-s})$ factor explicit.
- Any use in functional‑equation derivations should cite `docs/pure-zeta/zeta-analytic-continuation-chaos.md` (functional‑equation context) and the completed function in L00; avoid same‑layer cross‑links.
