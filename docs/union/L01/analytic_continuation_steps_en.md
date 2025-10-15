# Analytic Continuation Steps (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md

## Canonical Building Blocks
Reflection for $\Gamma$:
$$
\Gamma(s)\,\Gamma(1-s) = \frac{\pi}{\sin(\pi s)}.
$$
Functional equation (non‑completed):
$$
\zeta(s) = 2^{s}\,\pi^{s-1}\,\sin\!\left(\frac{\pi s}{2}\right)\,\Gamma(1-s)\,\zeta(1-s).
$$
Mellin integral (for $\operatorname{Re}(s)>1$):
$$
\zeta(s) = \frac{1}{\Gamma(s)}\,\int_{0}^{\infty} \frac{t^{s-1}}{e^{t}-1}\,dt.
$$

## Dense Summary (non‑canonical)
- Canonical steps are collected here to reference analytic continuation without changing source expressions; all uses must cite original files.

## Proof chain bullets (from original sources; upward only)
- Cite `docs/zeta/zeta-analytic-continuation-chaos.md` for the derivations involving $\Gamma$ reflection and the functional equation.
- Cite the Mellin representation and its conditions from `docs/zeta/zeta-analytic-continuation-chaos.md`.
