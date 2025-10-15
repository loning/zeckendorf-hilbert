# RH Equivalences (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md
- L00 · ../L00/hilbert_foundations_en.md
- L00 · ../L00/matrix_foundations_en.md

## Functional Equation and Completion
$$
\xi(s) = \xi(1-s),\qquad \xi(s) = \frac{1}{2}\,s\,(s-1)\,\pi^{-s/2}\,\Gamma\!\left(\frac{s}{2}\right)\,\zeta(s)
$$

## Explicit Formula
$$
\psi(x) = x - \sum_{\rho} \frac{x^{\rho}}{\rho} - \log(2\pi) - \frac{1}{2}\,\log\!\left(1 - x^{-2}\right)
$$

## GUE Spacing
$$
P(s) = \frac{32}{\pi^{2}}\, s^{2}\, \exp\!\left(-\frac{4}{\pi}\,s^{2}\right)
$$

## Zero Counting (Riemann–von Mangoldt)
$$
N(T) = \frac{T}{2\,\pi}\,\log\!\left(\frac{T}{2\,\pi}\right) - \frac{T}{2\,\pi} + O\!\left(\log T\right)
$$
$$
N(T) = \frac{T}{2\,\pi}\,\log\!\left(\frac{T}{2\,\pi e}\right) + O\!\left(\log T\right)
$$

## Triadic Information (canonical)
$$
\mathcal{I}_{\text{total}}(s) = \left|\zeta(s)\right|^2 + \left|\zeta(1-s)\right|^2 + \left|\operatorname{Re}\!\left(\zeta(s)\,\overline{\zeta(1-s)}\right)\right| + \left|\operatorname{Im}\!\left(\zeta(s)\,\overline{\zeta(1-s)}\right)\right|
$$
$$
\mathcal{I}_{+}(s) = \frac{1}{2}\left(\left|\zeta(s)\right|^2 + \left|\zeta(1-s)\right|^2\right) + \left[\operatorname{Re}\!\left(\zeta(s)\,\overline{\zeta(1-s)}\right)\right]^+,
$$
$$
\mathcal{I}_{0}(s) = \left|\operatorname{Im}\!\left(\zeta(s)\,\overline{\zeta(1-s)}\right)\right|,
$$
$$
\mathcal{I}_{-}(s) = \frac{1}{2}\left(\left|\zeta(s)\right|^2 + \left|\zeta(1-s)\right|^2\right) + \left[\operatorname{Re}\!\left(\zeta(s)\,\overline{\zeta(1-s)}\right)\right]^-
$$
$$
i_{\alpha}(s) = \frac{\mathcal{I}_{\alpha}(s)}{\mathcal{I}_{+}(s) + \mathcal{I}_{0}(s) + \mathcal{I}_{-}(s)}.
$$

## Dense Summary (non‑canonical)
- This page accumulates canonical RH‑related statements tied to L00 forms; same‑layer references are forbidden.

## Pair-correlation derivations context (reference note)
This page uses the canonical pair‑correlation form alongside GUE spacing. For derivation contexts and normalization choices, see the original non‑summary files under `docs/zeta/zeta-prime-distribution-random-matrix.md` and the project’s admitted physics bridge `docs/zeta-publish/zeta-quantum-classical-phase-transition.md`.

## Proof chain bullets (from original sources; upward only)
- Completed functional equation $\xi(s)=\xi(1-s)$ — cite `docs/pure-zeta/zeta-analytic-continuation-chaos.md` (derivation and completion details).
- Explicit formula for $\psi(x)$ — cite `docs/zeta/zeta-series-product-analysis.md` (canonical grouping) together with `docs/pure-zeta/zeta-analytic-continuation-chaos.md`.
- GUE spacing $P(s)=\tfrac{32}{\pi^2}s^{2}\exp(-\tfrac{4}{\pi}s^{2})$ and pair correlation $R_2(x)=1-(\sin \pi x/\pi x)^2$ — cite `docs/zeta/zeta-prime-distribution-random-matrix.md` and `docs/zeta-publish/zeta-quantum-classical-phase-transition.md`.
- Zero counting $N(T)$ (both canonical forms recorded) — cite `docs/zeta/zeta-series-product-analysis.md`.
- Triadic information $\mathcal{I}_{\text{total}},\ \mathcal{I}_{\pm,0},\ i_{\alpha}$ — cite `docs/pure-zeta/zeta-analytic-continuation-chaos.md` and `docs/zeta/zeta-series-product-analysis.md` (exact definitions).
