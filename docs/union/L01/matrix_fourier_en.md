# Matrix Fourier Duality (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/matrix_foundations_en.md
- L00 · ../L00/hilbert_foundations_en.md

## Canonical Fourier Transform
$$
\mathcal{F}[f](\omega) = \hat{f}(\omega) = \frac{1}{\sqrt{2\,\pi}}\,\int_{-\infty}^{\infty} f(t)\,e^{-\,i\,\omega\,t}\,dt,
$$
$$
\mathcal{F}^{-1}[\hat{f}](t) = f(t) = \frac{1}{\sqrt{2\,\pi}}\,\int_{-\infty}^{\infty} \hat{f}(\omega)\,e^{\,i\,\omega\,t}\,d\omega.
$$
Parseval/Plancherel:
$$
\int_{-\infty}^{\infty} \left|f(t)\right|^{2}\,dt = \int_{-\infty}^{\infty} \left|\hat{f}(\omega)\right|^{2}\,d\omega.
$$

## Dense Summary (non‑canonical)
- Canonical Fourier duality is recorded here for Matrix usage, with norms and orthogonality aligned to L00 Hilbert foundations; further operator‑level details cite evolution pages.

## Proof chain bullets (from original sources; upward only)
- 引用 `docs/the-matrix/01-foundations/1.24-fourier-transform-as-duality-unification.md`：Fourier 对偶、Parseval 规范式。
- 引用 `docs/the-matrix/01-foundations/1.26-fourier-hilbert-space-complete-correspondence.md`：Fourier 与 Hilbert 的对应关系（规范形式）。
