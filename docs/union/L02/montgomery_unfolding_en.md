# Montgomery Unfolding (Canonical; Full Forms)

## Dependencies (Upward)
- L01 · ../L01/pair_correlation_en.md
- L01 · ../L01/riemann_von_mangoldt_en.md
- L00 · ../L00/zeta_foundations_en.md

## Canonical Unfolding Setup
Let $\{\gamma_n\}$ denote ordinates of non‑trivial zeros $\rho_n=\tfrac{1}{2}+i\gamma_n$ (ordering by height). Define the counting function in its canonical form
$$
N(T) = \frac{T}{2\,\pi}\,\log\!\left(\frac{T}{2\,\pi e}\right) + O\!\left(\log T\right),
$$
and use the unfolded variable $u= N(t)$. Local spacings are then recorded canonically as
$$
s_n = u(\gamma_{n+1}) - u(\gamma_n),\qquad \text{with unit mean after unfolding}.
$$
The pair correlation (in unfolded units) recorded in the union is
$$
R_{2}(x) = 1 - \left( \frac{\sin(\pi x)}{\pi x} \right)^{2}.
$$

## Dense Summary (non‑canonical)
- Canonical unfolding uses $N(T)$ to normalize zero spacings to unit mean; the union records the standard pair‑correlation form and uses it alongside GUE spacing for statistical comparisons.

## Proof chain bullets (from original sources; upward only)
- Zero counting $N(T)$ — cite `docs/zeta/zeta-series-product-analysis.md` (canonical Riemann–von Mangoldt forms).
- Unfolding and pair‑correlation usage — cite `docs/zeta/zeta-prime-distribution-random-matrix.md` (normalizations and correlation functions).
