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

## Proof chain bullets (from original sources; upward only)
- From the completed functional equation $\xi(s)=\xi(1-s)$ (L00; source: `docs/zeta_theorems.md`), symmetry claims on the critical line are anchored.
- From the explicit formula $\psi(x)=x-\sum_{\rho}x^{\rho}/\rho-\log(2\pi)-\tfrac{1}{2}\log(1-x^{-2})$ (L00 dependency; source: `docs/zeta_theorems.md`), prime‑zero correspondences are derived.
- GUE spacing $P(s)=\tfrac{32}{\pi^2}s^{2}\exp\!(-\tfrac{4}{\pi}s^{2})$ (source: `docs/zeta_theorems.md`) is the canonical spacing model referenced here; pair correlation $R_{2}(x)=1-(\sin \pi x / \pi x)^{2}$ is used accordingly.
- Zero‑counting formulas $N(T)$ (two canonical forms) are imported from `docs/zeta_theorems.md` and must not be abbreviated.
- Triadic information $\mathcal{I}_{\text{total}}(s),\ \mathcal{I}_{\pm,0}(s)$ and normalized $i_{\alpha}(s)$ (L00; sources: `docs/zeta_theorems.md`, `docs/zeta_rh_equivalences.md`) provide the quantitative basis for information‑balance statements cited in RH contexts.
