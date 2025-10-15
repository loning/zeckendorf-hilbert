# Matrix Evolution Operators (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/matrix_foundations_en.md
- L00 · ../L00/hilbert_foundations_en.md

## Canonical Forms
Linear operator on $\ell^{2}$ (infinite matrix):
$$
(\mathsf{U}\,\mathbf{x})_{n} = \sum_{m=0}^{\infty} u_{n,m}\,x_{m},\qquad \mathbf{x}=(x_0,x_1,\dots)\in\ell^2.
$$
Unilateral shift $\mathsf{S}$:
$$
(\mathsf{S}\,\mathbf{x})_{n} = x_{n-1}\ (n\ge 1),\qquad (\mathsf{S}\,\mathbf{x})_{0}=0.
$$
Companion operator for a $k$‑step recurrence:
$$
\mathbf{v}_{n+1} = \begin{pmatrix}
 a_{1} & a_{2} & a_{3} & \cdots & a_{k} \\
 1 & 0 & 0 & \cdots & 0 \\
 0 & 1 & 0 & \cdots & 0 \\
 \vdots & & \ddots & \ddots & \vdots \\
 0 & 0 & \cdots & 1 & 0
\end{pmatrix}\,\mathbf{v}_{n} = \mathsf{C}\,\mathbf{v}_{n}.
$$
Semigroup/Generator (formal):
$$
\mathsf{U}(t+s)=\mathsf{U}(t)\,\mathsf{U}(s),\quad \mathsf{U}(0)=\mathsf{I},\quad \mathsf{U}(t)=e^{\,t\,\mathsf{A}},\ \ \mathsf{A}\,\mathbf{x}=\lim_{t\downarrow 0}\frac{\mathsf{U}(t)\,\mathbf{x}-\mathbf{x}}{t}.
$$

## Dense Summary (non‑canonical)
- These canonical forms fix the operator‑level semantics for Matrix evolution and link to Hilbert embeddings via norms and orthogonality.

## Proof chain bullets (from original sources; upward only)
- 引用 `docs/the-matrix/01-foundations/1.3-evolution-operators.md`：演化算子与半群/生成元的规范陈述。
- 引用 `docs/the-matrix/01-foundations/1.2-infinite-matrix-definition.md`：无限矩阵与线性算子的域/有界性惯例。
