# Hilbert Foundations (Canonical; Full Forms)

## Recursive Embedding and Orthogonalization
$$
\Omega_{i} \longleftrightarrow \mathbf{e}_{i} \in \ell^{2},\quad \left\|\mathbf{e}_{i}\right\| = 1
$$
Gram–Schmidt explicit form:
$$
\mathbf{e}'_{1} = \mathbf{e}_{1},\qquad \mathbf{e}'_{k} = \frac{\mathbf{e}_{k} - \sum_{j=1}^{k-1} \langle \mathbf{e}_{k}, \mathbf{e}'_{j} \rangle \, \mathbf{e}'_{j}}{\left\|\mathbf{e}_{k} - \sum_{j=1}^{k-1} \langle \mathbf{e}_{k}, \mathbf{e}'_{j} \rangle \, \mathbf{e}'_{j}\right\|}
$$

## Spectral Theorem (self‑adjoint; canonical statement)
$$
\mathsf{H} = \int_{\mathbb{R}} \lambda \, dE_{\lambda},\qquad \phi(\mathsf{H}) = \int_{\mathbb{R}} \phi(\lambda) \, dE_{\lambda}.
$$

## Dense Summary (non‑canonical)
- Embedding and spectral forms are the geometric backbone referenced by higher layers.

## Proof chain bullets (from original sources)
- Recursive embedding $\Omega_i \longleftrightarrow \mathbf{e}_i \in \ell^2$ and Gram–Schmidt orthogonalization must cite `docs/chapter04_hilbert.md`.
- Spectral‑theorem usage (self‑adjoint $\mathsf{H}$ with $\mathsf{H}=\int \lambda\,dE_{\lambda}$) must appear with clear operator domains and cite the canonical source used in `docs/chapter04_hilbert.md` (or the designated operator‑theory reference admitted by the project).
