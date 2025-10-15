# Zeta Foundations (Canonical; Full Formulas)

## Triadic Information and Conservation
$$
i_+(s) + i_0(s) + i_-(s) = 1, \quad s \in \mathbb{C}
$$
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
i_{\alpha}(s) = \frac{\mathcal{I}_{\alpha}(s)}{\mathcal{I}_{+}(s) + \mathcal{I}_{0}(s) + \mathcal{I}_{-}(s)}\quad (\alpha \in \{+,0,-\}).
$$

## Functional Equation and Completion
$$
\xi(s) = \xi(1-s),\qquad \xi(s) = \frac{1}{2}\,s\,(s-1)\,\pi^{-s/2}\,\Gamma\!\left(\frac{s}{2}\right)\,\zeta(s)
$$

## Euler Product (canonical; $\operatorname{Re}(s)>1$)
$$
\zeta(s) = \prod_{p\ \text{prime}} \frac{1}{1 - p^{-s}},\qquad \operatorname{Re}(s) > 1.
$$

## Dense Summary (non‑canonical)
- Canonical triadic definitions and the completed functional equation anchor the Zeta view.
- All higher‑layer equivalences and statistics must reference these forms.

## Proof chain bullets (from original sources)
- Canonical total information and components $\mathcal{I}_{\text{total}}(s),\ \mathcal{I}_{\pm,0}(s)$ and normalization $i_+(s)+i_0(s)+i_-(s)=1$ — cite:
  - `docs/pure-zeta/zeta-analytic-continuation-chaos.md` (definitions and dual structure)
  - `docs/zeta/zeta-series-product-analysis.md` (component grouping conventions)
- Completed functional equation $\xi(s)=\xi(1-s)$ — cite `docs/pure-zeta/zeta-analytic-continuation-chaos.md` (derivation and completion).
- Explicit‑formula usage — cite `docs/zeta/zeta-series-product-analysis.md` and `docs/pure-zeta/zeta-analytic-continuation-chaos.md`.
- GUE/statistics usage — cite `docs/zeta-publish/zeta-quantum-classical-phase-transition.md` and `docs/zeta/zeta-prime-distribution-random-matrix.md`.
- Euler product — cite `docs/zeta/zeta-series-product-analysis.md`.
