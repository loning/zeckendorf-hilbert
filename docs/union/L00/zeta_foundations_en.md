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
- Canonical total information and components $\mathcal{I}_{\text{total}}(s),\ \mathcal{I}_{\pm,0}(s)$ and normalization $i_+(s)+i_0(s)+i_-(s)=1$ — cite concrete files:
  - `docs/zeta/zeta-analytic-continuation-chaos.md`（定义与对偶结构）
  - `docs/zeta/zeta-series-product-analysis.md`（分量与总信息的分解习惯式）
- Completed functional equation $\xi(s)=\xi(1-s)$ — cite `docs/zeta/zeta-analytic-continuation-chaos.md`（函数方程与完备化的推导）
- Explicit‑formula usage — cite `docs/zeta/zeta-series-product-analysis.md` 与 `docs/zeta/zeta-analytic-continuation-chaos.md`（显式公式与相关项的整理）
- GUE/statistics usage — cite concrete files `docs/zeta/zeta-quantum-classical-phase-transition.md`, `docs/zeta/zeta-prime-distribution-random-matrix.md`
- Euler product — cite `docs/zeta/zeta-series-product-analysis.md`（欧拉乘积与乘法编码）
