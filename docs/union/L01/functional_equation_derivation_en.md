# Functional Equation Derivation (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md

## Canonical Forms (recorded in the union)
Completed function and reflection symmetry:
$$
\xi(s) = \xi(1-s),\qquad \xi(s) = \frac{1}{2}\,s\,(s-1)\,\pi^{-s/2}\,\Gamma\!\left(\frac{s}{2}\right)\,\zeta(s),
$$
Dirichlet‑series and product/series identities (for $\operatorname{Re}(s)>1$):
$$
\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^{s}} = \prod_{p\ \text{prime}} \frac{1}{1 - p^{-s}}.
$$
The canonical functional equation (non‑completed form) is recorded as
$$
\zeta(s) = 2^{s}\,\pi^{s-1}\,\sin\!\left(\frac{\pi s}{2}\right)\,\Gamma(1-s)\,\zeta(1-s)\,=\,\chi(s)\,\zeta(1-s),
$$
with
$$
\chi(s) = 2^{s}\,\pi^{s-1}\,\sin\!\left(\frac{\pi s}{2}\right)\,\Gamma(1-s).
$$

## Dense Summary (non‑canonical)
- This page records the canonical completed and non‑completed functional equations and the supporting identities; they are to be used as anchors for RH‑related derivations.

## Proof chain bullets (from original sources; upward only)
- 引用 `docs/zeta/zeta-analytic-continuation-chaos.md`：函数方程与完备化（及构造所需的积分/变换框架）。
- 引用 `docs/zeta/zeta-series-product-analysis.md`：Dirichlet 级数、欧拉乘积与相应的等价关系（$\operatorname{Re}(s)>1$）。
