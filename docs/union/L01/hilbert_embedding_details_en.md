# Hilbert Embedding Details (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/hilbert_foundations_en.md

## Canonical Embedding and Orthogonalization
$$
\Omega_{i} \longleftrightarrow \mathbf{e}_{i} \in \ell^{2},\quad \left\|\mathbf{e}_{i}\right\| = 1
$$
Gram–Schmidt (explicit):
$$
\mathbf{e}'_{1} = \mathbf{e}_{1},\qquad \mathbf{e}'_{k} = \frac{\mathbf{e}_{k} - \sum_{j=1}^{k-1} \langle \mathbf{e}_{k}, \mathbf{e}'_{j} \rangle \, \mathbf{e}'_{j}}{\left\|\mathbf{e}_{k} - \sum_{j=1}^{k-1} \langle \mathbf{e}_{k}, \mathbf{e}'_{j} \rangle \, \mathbf{e}'_{j}\right\|}.
$$

## Dense Summary (non‑canonical)
- This page codifies the canonical embedding forms to be cited by Matrix–Hilbert equivalence pages and spectral arguments.

## Proof chain bullets (from original sources; upward only)
- 引用 `docs/chapter04_hilbert.md` 的对应小节（嵌入与 Gram–Schmidt）。
