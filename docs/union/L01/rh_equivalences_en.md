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
- Completed functional equation $\xi(s)=\xi(1-s)$（L00）— 引用 `docs/zeta/zeta-analytic-continuation-chaos.md` 的具体小节。
- 显式公式 $\psi(x)=x-\sum_{\rho}x^{\rho}/\rho-\log(2\pi)-\tfrac{1}{2}\log(1-x^{-2})$（L00 依赖）— 引用 `docs/zeta/zeta-series-product-analysis.md` 与 `docs/zeta/zeta-analytic-continuation-chaos.md`。
- GUE 间距 $P(s)=\tfrac{32}{\pi^2}s^{2}\exp\!(-\tfrac{4}{\pi}s^{2})$ 与配对相关 $R_{2}(x)=1-(\sin \pi x / \pi x)^{2}$ — 引用 `docs/zeta/zeta-quantum-classical-phase-transition.md`, `docs/zeta/zeta-prime-distribution-random-matrix.md` 的相应章节。
- 零点计数 $N(T)$ 两种规范形式 — 引用 `docs/zeta/zeta-series-product-analysis.md`（或项目认可的专门计数条目）。
- 三分信息 $\mathcal{I}_{\text{total}}(s),\ \mathcal{I}_{\pm,0}(s)$ 与 $i_{\alpha}(s)$（L00）— 引用 `docs/zeta/zeta-analytic-continuation-chaos.md`, `docs/zeta/zeta-series-product-analysis.md` 的相关定义小节。
