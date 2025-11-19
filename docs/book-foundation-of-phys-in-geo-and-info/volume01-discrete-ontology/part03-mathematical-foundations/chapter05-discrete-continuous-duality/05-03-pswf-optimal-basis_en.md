**5.3 Prolate Spheroidal Wave Functions (PSWF): Optimal Basis and Information Truncation under Finite Observation Windows**

In Section 5.1, we proved that on infinite intervals, Physical Sampling Theorem guarantees perfect equivalence between discrete lattices and continuous band-limited fields. In Section 5.2, we introduced Discrete-Continuous Error Control (DCEC) to handle boundary terms. However, any real physical observation or numerical simulation must be performed within **finite time or space windows**.

When we restrict a band-limited signal (continuous limit of QCA) to a finite interval $[-T, T]$, Heisenberg uncertainty principle tells us that signal's frequency band will no longer be strictly limited, but undergo diffusion (spectral leakage). This leads to famous paradox in information theory: a function cannot be both time-limited and band-limited.

This section will introduce **Prolate Spheroidal Wave Functions (PSWF)** and their discrete counterparts **DPSS (Discrete Prolate Spheroidal Sequences)**, proving they constitute **optimal orthogonal bases** for capturing physical information under finite observation windows. This not only solves errors caused by Gibbs phenomenon, but more profoundly reveals: for a finite spacetime region, the number of effective physical degrees of freedom is not only finite, but precisely bounded by **Shannon Number**.

### 5.3.1 Operator Formulation of Finite Observation and Uncertainty Dilemma

Let physical state space of full space be $L^2(\mathbb{R})$. We need to examine two non-commuting projection operators:

1. **Band-limiting Operator** $B_\Omega$: Restricts physical fields to momentum cutoff $[-\Omega, \Omega]$.

    $$
    (B_\Omega f)(t) = \int_{-\infty}^\infty \frac{\sin \Omega(t-s)}{\pi(t-s)} f(s) \, \mathrm{d}s
    $$

    This corresponds to UV cutoff $\Omega = \pi/a$ of QCA.

2. **Time-limiting Operator** $D_T$: Restricts observation to time window $[-T, T]$.

    $$
    (D_T f)(t) = \begin{cases} f(t) & |t| \le T \\ 0 & |t| > T \end{cases}
    $$

**Lemma 5.3.1 (Corollary of Paley-Wiener Theorem)**

Operators $B_\Omega$ and $D_T$ have no common non-zero eigenfunctions. That is, there exists no non-zero function $f$ simultaneously satisfying $\text{supp}(f) \subset [-T, T]$ and $\text{supp}(\hat{f}) \subset [-\Omega, \Omega]$.

This means any attempt to perfectly reconstruct original physical fields within this finite window is mathematically doomed to have errors. Our goal shifts to finding bases with "minimal loss."

### 5.3.2 Slepian-Landau-Pollak (SLP) Problem

To quantify degree of information retention, we seek a set of band-limited functions $f \in B_\Omega L^2(\mathbb{R})$ that maximize energy proportion (energy concentration) within observation window $[-T, T]$.

**Definition 5.3.2 (Energy Concentration Functional)**

Define energy concentration ratio $\lambda$ as:

$$
\lambda = \frac{\| D_T f \|_2^2}{\| f \|_2^2} = \frac{\int_{-T}^T |f(t)|^2 \, \mathrm{d}t}{\int_{-\infty}^\infty |f(t)|^2 \, \mathrm{d}t}
$$

Finding function $f$ that maximizes $\lambda$ is equivalent to solving the following variational problem:

$$
\delta \left( \| D_T f \|_2^2 - \lambda \| f \|_2^2 \right) = 0, \quad f \in B_\Omega L^2(\mathbb{R})
$$

Using $f = B_\Omega f$, variational equation leads to the following integral equation:

$$
B_\Omega D_T B_\Omega f = \lambda f
$$

Or in time domain, this corresponds to eigenvalue problem:

$$
\int_{-T}^T \frac{\sin \Omega(t-s)}{\pi(t-s)} f(s) \, \mathrm{d}s = \lambda f(t)
$$

### 5.3.3 Prolate Spheroidal Wave Functions (PSWF) as Optimal Basis

Kernel function $K(t, s) = \frac{\sin \Omega(t-s)}{\pi(t-s)}$ of the above integral operator $K_c = B_\Omega D_T B_\Omega$ is real symmetric and positive definite. According to Hilbert-Schmidt operator theory, it has discrete spectrum.

**Theorem 5.3.3 (Spectral Properties of PSWF)**

Integral operator $K_c$ has countably infinite real eigenvalues $\lambda_n$ and corresponding eigenfunctions $\psi_n(t)$ (namely prolate spheroidal wave functions), satisfying:

1. **Ordering of Spectrum**: $1 > \lambda_0 > \lambda_1 > \dots > 0$.

2. **Double Orthogonality**: $\{\psi_n(t)\}$ are orthogonal on finite interval $[-T, T]$, and also orthogonal on entire real axis $(-\infty, \infty)$.

    $$
    \int_{-T}^T \psi_n(t) \psi_m(t) \, \mathrm{d}t = \lambda_n \delta_{nm}, \quad \int_{-\infty}^\infty \psi_n(t) \psi_m(t) \, \mathrm{d}t = \delta_{nm}
    $$

3. **Completeness**: $\{\psi_n\}$ constitutes complete basis of band-limited function space $B_\Omega L^2(\mathbb{R})$.

**Physical Meaning**:

PSWF $\{\psi_n(t)\}$ are **natural modes** of information. $\lambda_n$ represents "visibility" of $n$-th mode within observation window. $\lambda_n \approx 1$ means information of this mode almost completely falls within observation window; $\lambda_n \approx 0$ means although this mode physically exists, it is almost completely outside observation horizon, cannot be acquired through finite window.

### 5.3.4 Shannon Number and Phase Transition of Information Truncation

Distribution of eigenvalues $\lambda_n$ exhibits extremely significant phase transition behavior, which is direct manifestation of finiteness of physical information.

**Definition 5.3.4 (Shannon Number)**

Define dimensionless parameter $c = \Omega T$ (time-bandwidth product). Shannon number $N_{DoF}$ is defined as:

$$
N_{DoF} = \frac{2\Omega T}{\pi} = \frac{2c}{\pi}
$$

This corresponds to number of lattice sites $N_{sites} \approx 2W \cdot N_{steps}$ within observation window in discrete QCA.

**Theorem 5.3.5 (Step Distribution of Spectrum)**

For large $c$, distribution of eigenvalues $\lambda_n$ exhibits step-like behavior:

* **Passband Region** ($n < N_{DoF}$): $\lambda_n \approx 1$. These modes are fully observable "information channels."

* **Transition Region** ($n \approx N_{DoF}$): $\lambda_n$ drops sharply from 1 to 0 within narrow band of width $O(\ln c)$.

* **Stopband Region** ($n > N_{DoF}$): $\lambda_n \approx 0$ (exponential decay). These modes are degrees of freedom "shielded" by observation horizon.

**Physical Corollary (Legitimacy of Information Truncation)**:

When we observe QCA universe with finite windows, we don't need (nor can) acquire all information of infinite-dimensional Hilbert space. We only need to retain first $N_{DoF}$ PSWF modes.

Truncation error $E_{trunc}$ is controlled by sum of discarded eigenvalues:

$$
E_{trunc} \le \sum_{n > N_{DoF}} \lambda_n
$$

Since $\lambda_n$ decays exponentially after $N_{DoF}$, this truncation is **physically safe**. This explains why finite experimental data can precisely verify continuous physical laws: because whether discrete ontology or continuous models, effective degrees of freedom under finite windows are both $N_{DoF}$.

### 5.3.5 Discrete Counterpart: DPSS and Numerical Implementation

For actual computation of QCA, we need discrete versions of PSWF. Suppose we observe on lattice chain of length $N$, physical bandwidth is $W$ (normalized frequency $0 < W < 1/2$).

**Definition 5.3.6 (DPSS Sequences)**

Discrete Prolate Spheroidal Sequences (DPSS) are eigenvectors $v^{(k)}$ of the following $N \times N$ Toeplitz matrix:

$$
[T_{N,W}]_{mn} = \frac{\sin 2\pi W(m-n)}{\pi(m-n)}, \quad 0 \le m, n \le N-1
$$

Their eigenvalues $\lambda_k(N,W)$ also exhibit Shannon phase transition, with critical dimension $K \approx 2NW$.

**DCEC Algorithm Application**:

In DCEC framework of Section 5.2, if we choose first $K$ vectors of DPSS as basis to expand discrete physical fields, we can minimize Gibbs oscillations caused by boundary truncation. At this point, Euler-Maclaurin remainder $R_k$ is naturally suppressed by extremely high energy concentration of DPSS.

**Summary**

This section provides optimal mathematical tools for "finite observation."

1. **PSWF/DPSS** are bridges connecting infinite ontology with finite observation.

2. **Shannon Number** $2\Omega T/\pi$ gives hard upper bound (degree of freedom count) of physical information contained in any finite spacetime region.

3. **Spectral Leakage** is not uncontrollable noise, but analytic tail terms that can be exponentially suppressed by choosing optimal bases.

At this point, we have completed all mathematical preparation for Volume I. We have proved: discrete, finite, band-limited QCA models can not only derive continuous field theory in long-wavelength limit (Chapter 4), but also have strict error control systems in mathematical structure (Chapter 5). This lays an unshakeable foundation for exploring deeper physical problems in subsequent volumes—the nature of time.

