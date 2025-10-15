# Consolidated RH Equivalences and Chains (Canonical; Full Forms)

## Dependencies (Upward)
- L01 · ../L01/functional_equation_derivation_en.md
- L01 · ../L01/explicit_formula_variants_en.md
- L01 · ../L01/pair_correlation_en.md
- L01 · ../L01/zero_free_region_en.md
- L01 · ../L01/convexity_bound_en.md
- L01 · ../L01/hardy_z_en.md
- L00 · ../L00/zeta_foundations_en.md

## Canonical Entries Used (recorded in full)
Functional equation (completed and non‑completed):
$$
\xi(s) = \xi(1-s),\qquad \xi(s) = \frac{1}{2}\,s\,(s-1)\,\pi^{-s/2}\,\Gamma\!\left(\frac{s}{2}\right)\,\zeta(s),\qquad \zeta(s) = \chi(s)\,\zeta(1-s).
$$
Explicit formula (one canonical variant):
$$
\psi(x) = x - \sum_{\rho} \frac{x^{\rho}}{\rho} - \log(2\pi) - \frac{1}{2}\,\log\!\left(1 - x^{-2}\right).
$$
GUE spacing and pair correlation (canonical forms used here):
$$
P(s) = \frac{32}{\pi^{2}}\, s^{2}\, \exp\!\left(-\frac{4}{\pi}\,s^{2}\right),\qquad R_{2}(x) = 1 - \left( \frac{\sin(\pi x)}{\pi x} \right)^{2}.
$$
Zero‑free region and convexity bound (canonical statements admitted by the project):
$$
\zeta(\sigma+it) \ne 0\ \text{ if }\ \sigma \ge 1 - \frac{c}{\log\!\left( |t| + 3 \right)};\qquad \zeta(\sigma+it) \ll_{\varepsilon} (|t|+3)^{\,\frac{1-\sigma}{2}+\varepsilon}.
$$

## Dense Summary (non‑canonical)
- This page consolidates canonical chains employed in RH contexts: functional equation \(+\) explicit formulas \(+\) zero‑locations and spacing models. All expressions are recorded canonically and unabridged; proof chains below cite original `/docs/zeta/` files.

## Proof chain bullets (from original sources; upward only)
- Functional‑equation and completion: cite `docs/pure-zeta/zeta-analytic-continuation-chaos.md` (derivation and required transforms); do not abbreviate.
- Explicit‑formula terms and Chebyshev/von‑Mangoldt functions: cite `docs/zeta/zeta-series-product-analysis.md` (with $\theta(x),\ \psi(x),\ \Lambda(n)$ fully defined).
- GUE spacing and pair correlation: cite `docs/zeta-publish/zeta-quantum-classical-phase-transition.md` and `docs/zeta/zeta-prime-distribution-random-matrix.md` (normalized spacing models and correlation forms).
- Zero‑free region and convexity bounds: cite canonical entries as indexed in `docs/zeta/` (non‑summary files carrying the explicit statements), and keep $c>0$ and $\varepsilon>0$ conditions explicit.
- Hardy $Z$‑function and Riemann–Siegel usage: cite `docs/zeta-publish/zeta-critical-line-appendix.md` for $\theta(t)$, $Z(t)$ and the Riemann–Siegel formula.
