# Matrix Foundations (Canonical; Full Forms)

## Row–Algorithm Identity
$$
\text{row}_{i} \equiv \text{recursive algorithm}_{i}
$$

## k‑bonacci Recurrence and Entropy Rate
$$
 p_{n} = \sum_{m=1}^{k} p_{n-m},\quad n \ge k
$$
Let $r_{k}$ be the dominant root of the characteristic equation
$$
 r^{k} = r^{k-1} + r^{k-2} + \cdots + r + 1 = \frac{r^{k}-1}{r-1},\quad r\ne 1,
$$
which is equivalently 
$$
 r^{k+1} - 2\,r^{k} + 1 = 0.
$$
Then
$$
 N_{k}(n) = \Theta\!\left(r_{k}^{\,n}\right),\qquad \frac{dS}{dt} = \log_{2}(r_{k}),\qquad r_{1}=1,\ r_{2}=\varphi>1,\ r_{k}\nearrow 2.
$$

## Dense Summary (non‑canonical)
- This fixes growth and entropy‑rate baselines for Matrix constructs used by higher layers.

## Proof chain bullets (from original sources)
- Row–algorithm identity $\text{row}_{i} \equiv \text{recursive algorithm}_{i}$ must cite `docs/the-matrix/01-foundations/1.7-row-algorithm-identity.md`.
- The $k$‑bonacci recurrence $p_{n}=\sum_{m=1}^{k}p_{n-m}$, characteristic equation and dominant root $r_k$ with $\frac{dS}{dt}=\log_2(r_k)$ must cite `docs/the-matrix/01-foundations/1.4-k-bonacci-recursion.md`.
- Any Fourier/duality or evolution‑operator usage in upper layers must cite the corresponding canonical pages under `docs/the-matrix/01-foundations/` without abbreviation.
