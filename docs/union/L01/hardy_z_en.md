# Hardy Z-function & Riemann–Siegel (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md

## Hardy Z-function (canonical definition)
For $t\in\mathbb{R}$, define
$$
Z(t) = e^{\,i\,\theta(t)}\,\zeta\!\left(\tfrac{1}{2}+i\,t\right),
$$
where the Riemann–Siegel theta function is
$$
\theta(t) = \operatorname{Im}\,\log\!\Gamma\!\left( \frac{1}{4} + i\,\frac{t}{2} \right) - \frac{t}{2}\,\log\!\pi.
$$
This ensures $Z(t)\in\mathbb{R}$ for real $t$, and zeros of $Z(t)$ correspond to zeros of $\zeta(\tfrac{1}{2}+it)$.

## Riemann–Siegel Formula (canonical schematic)
There exists a canonical expansion
$$
Z(t) = 2\,\sum_{n\le N} n^{-1/2}\,\cos\!\big( \theta(t) - t\,\log n \big) + R(t;N),
$$
with $N$ chosen around $\sqrt{t/(2\pi)}$ and remainder $R(t;N)$ bounded as in the admitted sources.

## Dense Summary (non‑canonical)
- $Z(t)$ and the Riemann–Siegel formula are recorded canonically to analyze critical‑line values; they will be referenced in zero‑spacing and counting contexts.

## Proof chain bullets (from original sources; upward only)
- $Z(t)$ 与 $\theta(t)$ 的定义、Riemann–Siegel 公式与余项界：引用 `docs/zeta/zeta-critical-line-appendix.md` 的相应章节；若需要更细界，请引用项目认可的解析数论参考。
