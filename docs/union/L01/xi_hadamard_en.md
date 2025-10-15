# Hadamard Product for $\xi(s)$ (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/zeta_foundations_en.md
- L00 · ../L00/hilbert_foundations_en.md

## Canonical Hadamard Product
The completed $\xi$ function admits an entire product expansion of Hadamard type. A canonical form recorded in the union is
$$
\xi(s) = \xi(0)\,\prod_{\rho}\,\left(1 - \frac{s}{\rho}\right)\,\exp\!\left(\frac{s}{\rho}\right),
$$
where the product ranges over all non‑trivial zeros $\rho$ of $\zeta(s)$, taken with appropriate pairing to ensure convergence.

## Logarithmic Derivative (canonical usage)
Formally,
$$
\frac{\xi'(s)}{\xi(s)} = -\sum_{\rho} \left( \frac{1}{s-\rho} + \frac{1}{\rho} \right),
$$
with convergence understood in the canonical sense by zero pairing; this is used to connect zero distributions to explicit‑formula terms.

## Dense Summary (non‑canonical)
- The Hadamard product encodes the zeros of $\xi(s)$ as an entire function; the union records it canonically for use in zero‑counting and explicit‑formula arguments.

## Proof chain bullets (from original sources; upward only)
- The product and its convergence scheme must cite the canonical Hadamard factorization entries admitted in `docs/zeta_theorems.md`.
- Any use of the logarithmic derivative for zero statistics must explicitly reference this canonical product and the explicit formula recorded in L00/L01 pages.
