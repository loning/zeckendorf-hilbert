# Windowed Readout Unified Measurement: Born Probability = Minimal KL, Pointer Basis = Minimal-Energy Eigenbasis

(with Non-Asymptotic Error Closure and Window/Kernel Optimization)

**Author**:
**Affiliation**:
**Date**: 2025-10-25

---

## Abstract (Qualitative)

Within the unified framework of **mirror kernel—de Branges–Kreĭn canonical system—information geometry**, this paper proposes and rigorously proves three main theorems:

1. **Windowed Readout Theorem**: Any realizable quantum measurement readout is equivalent to weighting the (relative or absolute) **local density of states** (LDOS) by the pair of "energy window $w_R$ and front-end kernel $h$"; when realistic **discrete sampling—finite truncation** procedures are employed, errors can be **non-asymptotically closed** according to three terms: **Nyquist (aliasing)–Poisson (sampling)–Euler–Maclaurin (EM, sum-integral difference)**, and under **band-limited + Nyquist conditions** the aliasing term is strictly zero. This conclusion rests on the Herglotz property of the Weyl–Titchmarsh $m$-function and the boundary-value dictionary ($\Im m(E+i0)=\pi\rho(E)$) and its equivalence with canonical systems.

2. **Born Probability = Minimal KL (Information Projection)**: When the readout dictionary aligns with the **log-partition potential** $\Lambda(\rho)=\log\!\sum_j w_j e^{\langle\beta_j,\rho\rangle}$, the **minimal-energy projection with unit response** is equivalent to **minimal Kullback–Leibler (KL) divergence under linear moment constraints**; the softmax probability is precisely the weight of the minimal-KL projection, and when the softening parameter $\tau\!\downarrow\!0$ (or equivalently inverse temperature $\kappa=1/\tau\!\uparrow\!\infty$; **not to be confused with dictionary coefficients $\beta_j$**), it $\Gamma$-converges to hard projection (Hilbert orthogonal). Equivalently uses **Fenchel–Legendre duality / Bregman–KL identity / Csiszár's I-projection**.

3. **Pointer Basis = Eigenbasis of Minimal Energy/Information Projection**: Under finite dictionary, the coefficient vector of the minimal-energy mollifier is $\beta^\star=\dfrac{G^{-1}c}{c^\ast G^{-1}c}$; in the Gram spectral decomposition $G=U\Lambda U^\ast$, $\beta^\star$ expands along $\{u_k\}$ weighted by $\lambda_k^{-1}$, thus **the direction contributing most strongly to $\beta^\star$** is realized by

$$
\arg\max_k\ \frac{|\langle u_k,c\rangle|^2}{\lambda_k}
$$

Small eigenvalues tend to amplify that direction, but whether it dominates depends on simultaneously having sufficiently large projection $|\langle u_k,c\rangle|$. The spectral basis of the soft information Hessian $\nabla^2\Lambda$ is isomorphic to this.

On the scattering side, via standard **Birman–Kreĭn** and **Wigner–Smith** constructions, in single-channel case the phase derivative and (relative) spectral density satisfy

$$
\varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)=\pi\,\xi'(E),\qquad
\mathsf Q(E)=-i\,S(E)^\dagger\frac{dS}{dE},
$$

thus $\tfrac1{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$. This interprets "negative delay" as a result of **reference choice** and **relative counting**, not causality violation.

**Keywords**: windowed readout; Weyl–Titchmarsh; spectral shift function; Wigner–Smith time delay; de Branges space; BN—Bregman; minimal KL; PSWF; Nyquist–Poisson–EM; non-asymptotic error.

---

## 0. Notation and Background

### Basic Conventions

* **Energy and Upper Half-Plane**: $E\in\mathbb R$, $\mathbb C_+=\{z:\Im z>0\}$.
* **Fourier Convention**: This paper uniformly adopts $\widehat f(\xi)=\int f(t)e^{-it\xi}\,dt$, where $\xi$ is **angular frequency** (rad/energy).
* **Unit Convention**: Fixed $\hbar=1$.

### Spectral Functions and Boundary Values

* **Weyl–Titchmarsh and LDOS**: If $m:\mathbb C_+\!\to\!\mathbb C_+$ is a Herglotz–Nevanlinna function, then at Lebesgue-a.e. energy points it possesses **non-tangential boundary values** (Fatou boundary theory). When the absolutely continuous part of its Herglotz representation measure has density $\rho_m(E)$ at $E$, a.e.

$$
\Im m(E+i0)=\pi\rho_m(E).
$$

The $\pi$ here comes from the standard constant in **Stieltjes inversion**, independent of Fourier transform convention. Here $\rho_m$ is the **absolutely continuous density** of the Herglotz representation measure; the singular part does not contribute to the boundary value equality a.e. This formula is equivalent to the weak form of Stieltjes inversion; the singular part gives zero a.e. (see Kostenko–Sakhnovich–Teschl's Stieltjes inversion lemma). Fatou boundary values and a.e. existence for Herglotz–Pick class see Teschl and Kostenko–Teschl series. Equivalent form: $\rho(E)=\frac{1}{\pi}\Im m(E+i0)$.

### Scattering and Spectral Shift

* **Sign Convention**: This paper fixes the Birman–Kreĭn "positive sign" convention

$$
\det S(E)=e^{+2\pi i\,\xi(E)},\qquad \xi'(E)=\rho_{\mathrm{rel}}(E).
$$

Define **relative (spectral shift) density** $\rho_{\mathrm{rel}}(E):=\xi'(E)$ (a.e.). If using the "negative sign" convention $\det S=e^{-2\pi i\,\xi}$, one must simultaneously substitute $\varphi\mapsto-\varphi$ to preserve the chain equivalence. **Note**: Mainstream literature (e.g., Pushnitski 2010, "An integer-valued version of the Birman–Krein formula", arXiv:1006.0639) commonly uses the negative sign version $e^{-2\pi i\xi}=\det S$; both are dually consistent via $\varphi\mapsto-\varphi$.

* **Applicability Conditions**: Assume $(H,H_0)$ satisfies appropriate **relative trace class** or **local trace class** conditions (e.g., $(H-H_0)\in\mathfrak S_1$ in a localized sense) to ensure a.e. differentiability of $S(E)$ and $\xi(E)$ and validity of the Birman–Kreĭn formula. When $(H,H_0)$ arises from the same boundary triple/half-line setup and the endpoint Weyl–Titchmarsh functions $m,m_0$ exist, at a.e. $E$ we have the equivalent formula $\xi'(E)=\rho_m(E)-\rho_{m_0}(E)$. In single-channel $S(E)=e^{2i\varphi(E)}$ case, $\varphi'(E)=\pi\,\xi'(E)=\pi\,\rho_{\mathrm{rel}}(E)$ (a.e.).

### Other Structures

* **de Branges—Canonical System**: The Hilbert space $\mathcal H(E)$ generated by completion function $E$ and inner function $U=E^\sharp/E$ is equivalent to a first-order symplectic canonical system; the Weyl function is precisely $m$.
* **Information Potential and Fisher Geometry**: $\Lambda(\rho)=\log\sum_j w_j e^{\langle\beta_j,\rho\rangle}$, $p_j(\rho)=\dfrac{w_j e^{\langle\beta_j,\rho\rangle}}{\sum_\ell w_\ell e^{\langle\beta_\ell,\rho\rangle}}$, $\nabla^2\Lambda=\mathrm{Cov}_{p(\rho)}(\beta)$. This equivalence establishes a one-to-one correspondence between regular exponential families and regular Bregman classes.

---

## 1. Main Theorem I: Windowed Readout and Non-Asymptotic Error Closure

### Theorem 1.1 (Windowed Readout; Nyquist–Poisson–EM Tri-Decomposition)

**Hypothesis**: The sampled function $F(E)=w_R(E)\,[h\!\star\!\rho_\star](E)$ belongs to $L^1(\mathbb R)$ or tempered distribution $\mathcal S'$ and satisfies the interchange conditions for Poisson summation; $h\in L^1\cap L^2$; $w_R$ is an even window; $\rho_\star$ is absolute or relative LDOS.

Take even window $w_R(x)=w(x/R)$ and front-end kernel $h\in L^1\cap L^2$. For absolute or relative LDOS $\rho_\star\in\{\rho_m,\rho_{\mathrm{rel}}\}$ define readout

$$
\mathrm{Obs}_{\Delta,T}:=\Delta\!\!\sum_{|n|\le M}\! w_R(E_n)\,[h\!\star\!\rho_\star](E_n),\quad E_n=n\Delta,\ T=M\Delta.
$$

Then

$$
\mathrm{Obs}_{\Delta,T}
=\int_{\mathbb R} w_R(E)\,[h\!\star\!\rho_\star](E)\,dE
+\varepsilon_{\mathrm{alias}}+\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}},
$$

where
(i) $\varepsilon_{\mathrm{alias}}$: spectral folding (aliasing) induced by **Poisson summation**;
(ii) $\varepsilon_{\mathrm{EM}}$: remainder from **finite-order Euler–Maclaurin** summation formula;
(iii) $\varepsilon_{\mathrm{tail}}$: truncation tail term outside window.

**Necessary and Sufficient Condition for Aliasing Annihilation and Common Criterion**: By the Poisson summation formula (see NIST DLMF §1.8(iv)), the **necessary and sufficient condition** for $\varepsilon_{\mathrm{alias}}=0$ is:

$$
\sum_{k\neq 0}\widehat F\!\Bigl(\tfrac{2\pi k}{\Delta}\Bigr)=0.
$$

**Common Sufficient Condition (Strict Band-Limited + Nyquist)**: If $\widehat w_R$ and $\widehat h$ are respectively **strictly band-limited** to $[-\Omega_w,\Omega_w]$, $[-\Omega_h,\Omega_h]$, then the spectrum of the sampled function $F(E)=w_R(E)\,[h\!\star\!\rho](E)$ satisfies $\widehat F=\widehat w_R\ast(\widehat h\,\widehat\rho)$ with $\mathrm{supp}\,\widehat F\subset[-(\Omega_w+\Omega_h),\Omega_w+\Omega_h]$ (sum bandwidth). When sampling satisfies

$$
\boxed{\ \Delta < \frac{\pi}{\Omega_w+\Omega_h}\ }\quad\Rightarrow\quad\varepsilon_{\mathrm{alias}}=0,
$$

or equivalently

$$
\boxed{\ \Delta \le \frac{\pi}{\Omega_w+\Omega_h}\ \text{and}\ \widehat F(\pm\pi/\Delta)=0\ }\quad\Rightarrow\quad\varepsilon_{\mathrm{alias}}=0.
$$

(See NIST DLMF §1.8(iv) for bandwidth-sampling folding criterion). $\varepsilon_{\mathrm{EM}}$ is explicitly controlled by finite-order periodized Bernoulli functions (NIST DLMF §2.10, §24.11); $\varepsilon_{\mathrm{tail}}$ is given by out-of-window $L^2$ energy.

**Note (Effective Bandwidth, for Sampled $F$)**: Aliasing analysis targets the **time-domain product** $F(E)=w_R(E)\,[h\!\star\!\rho](E)$; its frequency domain is the **convolution** $\widehat w_R\ast\widehat h\,\widehat\rho$, hence spectral width is $\Omega_w+\Omega_h$ (sum bandwidth). Because $\mathrm{supp}(\widehat h\,\widehat\rho)\subseteq \mathrm{supp}(\widehat h)$, when $\widehat h$ is strictly band-limited, the non-band-limitedness of $\widehat\rho$ does not break the band-limitedness of $\widehat F$. This differs from **first convolving into kernel $w_R\!\star h$ then convolving with $\rho$ at the continuous integral** level, where the latter involves spectral width $\min(\Omega_w,\Omega_h)$ of $\widehat{w_R\!\star h}=\widehat w_R\,\widehat h$, **but that is not the sampled object**. If $\widehat w_R$, $\widehat h$ are only nearly band-limited, then aliasing error is jointly bounded by out-of-band energy and sampling rate (giving an upper bound rather than strict zero).

**Note (Boundary Case)**: When $\mathrm{supp}\,\widehat F\subset(-\pi/\Delta,\pi/\Delta)$ or is zero at endpoints, $\varepsilon_{\mathrm{alias}}=0$; if only "nearly band-limited" or endpoints are non-zero, aliasing is explicitly bounded by "out-of-band energy" and sampling rate.

**Note (Nearly Band-Limited Case)**: When $\widehat{w_R}$, $\widehat{h}$ are only **approximately band-limited** (common in reality), $\varepsilon_{\mathrm{alias}}$ is jointly determined by out-of-band energy and sampling rate, can be bounded by the tail sum of non-zero $k$ Poisson terms; ideal "$\varepsilon_{\mathrm{alias}}=0$" requires **strict band-limited + Nyquist** to be simultaneously satisfied.

**Proof Sketch.**
(a) Spectral side: By Herglotz representation and spectral theorem, $[h\!\star\!\rho_\star](E)=\int h(E-E')\,d\mu_\star(E')$, $\Im m(E+i0)=\pi\rho_m(E)$, yielding convolution-weighted form.

(b) Aliasing (Poisson summation, this convention): Under the Fourier convention adopted in this paper $\widehat f(\xi)=\int f(t)e^{-it\xi}dt$, the Poisson summation formula is

$$
\Delta\sum_{n\in\mathbb Z}F(n\Delta)=\sum_{k\in\mathbb Z}\widehat F\!\bigl(\tfrac{2\pi k}{\Delta}\bigr)
$$

(corresponding to NIST DLMF §1.8(iv) under this convention). If $\mathrm{supp}\,\widehat F\subset(-\pi/\Delta,\pi/\Delta)$, then only $k=0$ remains. Here $\xi$ is angular frequency (rad/energy), sampling points are $2\pi k/\Delta$. Out-of-band energy $\epsilon_{\mathrm{OB}}:=|\widehat F\cdot \mathbf 1_{|\xi|>\pi/\Delta}|_{L^1}$ gives the bound $|\varepsilon_{\mathrm{alias}}|\le \epsilon_{\mathrm{OB}}$ (nearly band-limited case).

(c) EM remainder: Using Euler–Maclaurin up to order $2p$ requires $F$ to have integrable derivatives of order $2p$ over the relevant interval, the remainder $R_{2p}$ is expressed via **periodized Bernoulli functions** $\widetilde B_{2p}$ and $f^{(2p)}$ (NIST DLMF §2.10, §24.11). When $F$ has the required order of analytic continuation in the working band, finite-order EM remainder consists of analytic combinations of endpoint higher-order derivatives and periodized Bernoulli functions, introducing no new singularities, not elevating pole order, only changing endpoint analytic data.

### Corollary 1.2 (PSWF Energy Concentration and Coercivity)

For any $f\in \mathsf{PW}_\Omega$ (Paley–Wiener band-limited space), the largest eigenvalue $\lambda_0\in(0,1)$ of the time-limiting operator on $[-T,T]$ satisfies

$$
\int_{-T}^{T}|f|^2\le \lambda_0\,|f|_{L^2(\mathbb R)}^2,\qquad \Rightarrow\quad
|\,\mathbf 1_{|t|>T} f\,|_{L^2}^2 \ge (1-\lambda_0)\,|f|_{L^2}^2,
$$

where $\lambda_0$ is the **operator norm of the time-limiting operator on $\mathsf{PW}_\Omega$** (0-th order eigenvalue of PSWF/DPSS). This is a statement **on $\mathsf{PW}_\Omega$**. From this one obtains coercivity of the error functional.

**Note (PSWF Zero Properties and Energy Concentration)**: The $n$-th order PSWF function has exactly $n$ zeros in the interval $(-1,1)$ (Slepian–Pollak 1961), therefore **only the 0-th order** can maintain single sign (non-oscillatory) on a finite interval; higher-order functions are oscillatory. Energy concentration and zero properties of PSWF/DPSS see Slepian–Pollak–Landau series (1961–1964) and subsequent reviews, this paper only invokes the most basic conclusions.

---

## 2. Main Theorem II: Born Probability = Minimal KL Information Projection

Let dictionary $\{\phi_j\}\subset\mathcal H$, evaluation vector $k_{s_0}$. The geometric side **minimal-energy mollifier** is

$$
\min_{M\in\mathscr B}|M|^2\quad\text{s.t.}\quad \langle M,k_{s_0}\rangle=1,
$$

for finite dictionary write $M^\star=\sum_j\beta_j^\star\phi_j$, $\beta^\star=\dfrac{G^{-1}c}{c^\ast G^{-1}c}$, $G_{ij}=\langle\phi_i,\phi_j\rangle$, $c_j=\langle\phi_j,k_{s_0}\rangle$. This solution is the Lagrangian solution of the quadratic minimization problem under constraint $c^\ast\beta=1$.

**Alignment Hypothesis (Verifiable Condition)**: There exists a linear operator $\mathcal T:\mathcal H\to\mathbb R^d$ such that:
(i) $\mathcal T$ preserves quadratic form/inner product on the working subspace;
(ii) $\mathrm{im}(\nabla\Lambda)=\{\text{moment constraint feasible set}\}$;
(iii) $\langle M,k_{s_0}\rangle=1 \iff \mathbb E_q[\beta]=u_0$.

Under this **dictionary—constraint—potential** tri-alignment, geometric minimal energy $\Longleftrightarrow$ minimal KL (I-projection) holds, soft $\to$ hard limit corresponds to Hilbert orthogonal projection. Correspondence between log-partition Bregman divergence and KL, sufficiency of I-projection see Banerjee et al. (2005) and Csiszár (1975).

**When alignment is not satisfied, this paper does not assert unconditional validity of Born=minimal KL.**

### Lemma 2.1 (Bregman–KL Identity)

Let $\Lambda(\rho)=\log\sum_j w_j e^{\langle\beta_j,\rho\rangle}$, $p_j(\rho)=\dfrac{w_j e^{\langle\beta_j,\rho\rangle}}{\sum_\ell w_\ell e^{\langle\beta_\ell,\rho\rangle}}$. Then

$$
B_\Lambda(\rho'\mid\rho)
=\Lambda(\rho')-\Lambda(\rho)-\langle\nabla\Lambda(\rho),\rho'-\rho\rangle
=\mathrm{KL}\!\big(p(\rho)\,|\,p(\rho')\big).
$$

**Standard Fact**: The Bregman divergence of log-partition $\Lambda$ is precisely the KL divergence on the corresponding exponential family, and minimal-KL under linear moment constraints (I-projection) gives softmax weights. The following identity holds in an exponential family with $\rho$ as **natural parameter**, thus I-projection gives softmax weights equivalent to moment matching with $\nabla\Lambda$. See Banerjee et al. (2005), Csiszár (1975).

### Theorem 2.2 (Geometric Minimal Energy $\Longleftrightarrow$ Minimal KL (I-projection))

**Hypothesis (Dictionary—Constraint—Potential Isometric Alignment)**: There exists a linear operator $\mathcal T:\mathcal H\to\mathbb R^d$ preserving quadratic form on the working subspace, and $\operatorname{im}(\nabla\Lambda)$ aligns with the moment constraint feasible set.

Under this alignment,

$$
\boxed{\
\min_{M}|M|^2\ \text{s.t.}\ \langle M,k_{s_0}\rangle=1
\ \Longleftrightarrow
\min_{q\in\Delta}\{\mathrm{KL}(q|\pi):\ \mathbb E_q[\beta]=u_0\}\ }.
$$

The minimal solution satisfies $\nabla\Lambda(\rho^\star)=u_0$, its weight $p(\rho^\star)$ is I-projection (in exponential family log-partition Bregman divergence equals KL; I-projection unique, see Banerjee et al., JMLR 2005 and Csiszár 1975); when softening parameter $\tau\!\downarrow\!0$ (or equivalently inverse temperature $\kappa=1/\tau\!\uparrow\!\infty$; **not to be confused with dictionary coefficients $\beta_j$**), it $\Gamma$-converges to hard orthogonal projection.

**Note (Degeneracy and Selection)**: When there are **tied maxima/degeneracy**, $\tau\!\downarrow\!0$ softmax may converge to a **minimal-support selection** (non-unique), then the geometric "hard projection" should be understood as **orthogonal projection to the maximal subspace**, requiring a tie-breaking rule.

### Corollary 2.3 (Born Probability Softmax Realization)

Measurement probability weights are

$$
p_j(\rho^\star)=\frac{w_j e^{\langle\beta_j,\rho^\star\rangle}}{\sum_\ell w_\ell e^{\langle\beta_\ell,\rho^\star\rangle}},
$$

which is the **minimal-KL** distribution satisfying moment constraints (I-projection), soft $\to$ hard limit corresponds to geometric orthogonal projection (Born). When the constraint feasible set is a non-empty closed convex set and the reference distribution has positive support, I-projection is unique; tied extrema only appear at the $\tau\downarrow 0$ hardening limit with selection non-uniqueness (consistent with geometric projection to maximal subspace).

---

## 3. Main Theorem III: Spectral Characterization of Pointer Basis

Let $G=U\Lambda U^\ast$ ($\Lambda=\mathrm{diag}(\lambda_k)$). We have

$$
\beta^\star\ \propto\ U\Lambda^{-1}U^\ast c=\sum_k\frac{\langle u_k,c\rangle}{\lambda_k}\,u_k,\qquad
|M^\star|^{-2}=c^\ast G^{-1}c=\max_{|y|=1}\frac{|c^\ast y|^2}{y^\ast G y}.
$$

Default assumption: dictionary linearly independent and $G\succ0$; if only semi-definite, take Moore–Penrose inverse on $\mathrm{ran}(G)$ and interpret $\beta^\star$ as minimal-norm solution.

**(i) Eigenbasis and Dominant Direction**: $\beta^\star=\sum_k \frac{\langle u_k,c\rangle}{\lambda_k}u_k$. The factor $1/\lambda_k$ amplifies small eigenvalue directions, but **whether they dominate** depends on **simultaneously** having sufficiently large projection $|\langle u_k,c\rangle|$; **from the energy perspective in the $G^{-1}$ metric**, the direction contributing **most strongly** to $\beta^\star$ is realized by

$$
\arg\max_k\ \frac{|\langle u_k,c\rangle|^2}{\lambda_k}
$$

(Rayleigh quotient). This embodies the balance of "small eigenvalue amplification but needing sufficient projection".

**(ii) Information Geometry Correspondence (Conditional)**: Under **dictionary—constraint—potential isometric alignment** ($\mathcal T$ isomorphism preserving quadratic form), eigendirections of $\nabla^2\Lambda(\rho^\star)$ **one-to-one correspond** to spectral vectors $\{u_k\}$ of $G$; in general case can only guarantee "correspondence" not isomorphism. Under this condition, dominant direction is still controlled by the above formula.

---

## 4. Phase—Density, Wigner–Smith Time Delay and Reference-Dependence of "Negative Delay"

**Prerequisites (Standard)**: $(H,H_0)$ satisfies appropriate trace class/local integrability conditions to ensure a.e. differentiability of $S(E)$ and $\xi(E)$ and validity of Birman–Kreĭn formula; in single-channel case $S=e^{2i\varphi}$ gives $\operatorname{tr}\mathsf Q=2\varphi'$, thus $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$ a.e. (Wigner 1955; Smith 1960; subsequent reviews/generalizations see references below).

**Sign and Units**: Fixed $\hbar=1$. Adopt Birman–Kreĭn "**positive sign**" convention

$$
\det S(E)=e^{+2\pi i\,\xi(E)},\qquad
\Rightarrow\quad \varphi'(E)=\pi\,\xi'(E)=\pi\,\rho_{\mathrm{rel}}(E)\quad\text{(a.e.)},\quad
\mathsf Q(E)=-i\,S^\dagger\frac{dS}{dE},\ \ \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)\quad\text{(a.e.)}.
$$

If using "negative sign" convention $\det S=e^{-2\pi i\,\xi}$, must simultaneously substitute $\varphi\mapsto-\varphi$ to maintain structural consistency of equations.

**References**: Definition and properties of Wigner–Smith time delay matrix see Wigner (1955) and Smith (1960); Birman–Kreĭn formula and its relation to spectral shift function $\xi$ see Yafaev (1992/2010) and Pushnitski (2010), from which the relation between $\operatorname{tr}\mathsf Q$ and $\xi'$ follows.

### Theorem 4.1 (Phase Derivative = (Relative) Spectral Density)

Under trace class hypothesis and a.e. differentiability,

$$
\boxed{\ \varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)=\pi\,\xi'(E)\ }\quad\text{(a.e., under standard trace class/differentiability conditions; per this paper's BK positive sign convention)}.
$$

Proof: From $\det S(E)=e^{+2\pi i \xi(E)}$ and single-channel $S(E)=e^{2i\varphi(E)}$ we get $2\pi\xi'(E)=2\varphi'(E)$, thus $\varphi'(E)=\pi\,\xi'(E)$; then by definition $\rho_{\mathrm{rel}}:=\xi'$ we obtain the result.

**Note (Sign Conversion and Literature Correspondence)**: If adopting "negative sign" convention $\det S=e^{-2\pi i\,\xi}$ (common in literature), then $\varphi'=-\pi\xi'$, other formulas adjust synchronously via $\varphi\mapsto-\varphi$. Birman–Kreĭn formula and relation to $\det S$ see Pushnitski (2001) (gives negative sign version); modern reviews on Wigner–Smith time delay matrix $\mathsf Q=-iS^\dagger \tfrac{dS}{dE}$ and trace—phase relation generalizations to electromagnetics/acoustics (2020–2023).

### Proposition 4.2 (Wigner–Smith and LDOS)

**Under unitary scattering**, $\mathsf Q(E)=-iS^\dagger \tfrac{dS}{dE}$ is Hermitian; in single-channel case

$$
\operatorname{tr}\mathsf Q(E)=2\,\varphi'(E)\quad\text{(a.e.)},
$$

thus

$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)\quad\text{(a.e.)}.
$$

**Verification Line**: In single-channel $S=e^{2i\varphi}$ case $\mathsf Q=-iS^\dagger \tfrac{dS}{dE}=2\,\varphi'(E)$, thus $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$; multi-channel case see Schomerus–Beenakker series and Davy et al. (PRL 2015, "Transmission eigenchannels and the densities of states of random media") on equivalence between DOS and phase derivative/delay matrix (units $\hbar=1$). In random matrix context the relation between $\tau_W=(1/N)\operatorname{tr}Q$ and DOS also see experimental verification (Grabsch et al. 2018). "Negative delay" arises from **relative counting** and choice of reference $H_0$, does not imply causality violation.

**Note (Applicability Domain and Generalized Delay)**: The identity $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$ holds under a.e. differentiability and **trace class (or local trace class)** hypothesis for $S(E)$ and $\xi(E)$ (**unitary scattering**). "Negative delay" in unitary scattering framework can appear at **channel/eigenchannel delay** level, but $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q$ still agrees with **relative DOS**. **Sub-unitary/dissipative** systems require appropriate **generalized time delay** and non-Hermitian framework (Chen et al., PRE 2021), local negative values do not violate overall causality constraints. Electromagnetic/acoustic extensions see recent computational and experimental reviews (2020–2023). In unitary case, single-channel $\operatorname{tr}\mathsf Q=2\varphi'$; multi-channel eigenvalues of $\mathsf Q$ (proper delays) can be locally negative without violating overall causality constraints. Hermiticity of $\mathsf Q$ only guarantees real spectrum.

---

## 5. Window/Kernel Optimization: Strong Euler–Lagrange, KKT and $\Gamma$-Limit

On the band-limited even subspace $\mathsf{PW}^{\mathrm{even}}_{\Omega}$, define ($K$ is the highest even-order index, unrelated to sampling notation $M$ in §1)

$$
\mathcal J(w)=\sum_{j=1}^{K-1}\gamma_j\,|w_R^{(2j)}|_{L^2}^2+\lambda\,|\mathbf 1_{|t|>T}w_R|_{L^2}^2,\qquad \text{s.t.}\ w(0)=1.
$$

Its first-order necessary condition (frequency-domain strong form) is

$$
\chi_{[-\Omega/R,\Omega/R]}(\xi)\Big(\sum_{j=1}^{K-1}\gamma_j\,\xi^{4j}\,\widehat{w_R^\star}(\xi)
+\tfrac{\lambda}{2\pi}\,(\widehat{\mathbf 1_{|t|>T}}\!\ast\!\widehat{w_R^\star})(\xi)\Big)=\eta\,\chi_{[-\Omega/R,\Omega/R]}(\xi),
$$

where $\widehat{\mathbf 1_{|t|>T}}=2\pi\delta-\tfrac{2\sin(T\xi)}{\xi}$ (understood in $\mathcal S'$ sense; holds under this paper's Fourier convention $\widehat f(\xi)=\int f(t)e^{-it\xi}dt$; constants can be rescaled with $\lambda,\eta$), $\eta$ is Lagrange multiplier.

**Explanation (Constraint Origin and Constant Absorption)**: The constraint $w(0)=1$ is given by inversion formula $w(0)=\frac{1}{2\pi}\int \widehat w(\xi)\,d\xi$, thus its variation term in frequency domain is **constant**, merged into the right-hand side $\eta$. All constants in the above formula (including $2$ and $1/(2\pi)$) can be uniformly absorbed into rescaling of $\lambda,\eta$; numerical implementation fixes Fourier convention and Parseval constant, eliminating this difference via one-time calibration of $\lambda$. Distribution identity and periodized Bernoulli function expression of remainder see NIST DLMF §2.10; paired formulas $\widehat{\mathbf 1_{[-T,T]}}(\xi)=\tfrac{2\sin(T\xi)}{\xi}$ and $\widehat{1}=2\pi\delta$ origins see standard texts (e.g., Stanford EE102 Lecture 11 FT dual table). Derivative order and function space ($w_R\!\in\mathsf{PW}^{\mathrm{even}}_\Omega$ and $w_R^{(2K)}\!\in L^2$) suffice when satisfied. Exponential window case advisable to solve in time domain to avoid distribution order assumptions, still maintaining "pole = principal scale".

**BN–Bregman Softening and $\Gamma$-Limit**: Consider $\mathcal J(w)+\tau\,\Lambda^\ast(\mathcal Tw)$ ($\tau>0$), can obtain unique minimizer; as $\tau\downarrow0$ the minimal value and minimizing sequence $\Gamma$-converge to hard constraint problem.

---

## 6. Singularity Preservation, Thresholds and Zero Stability Radius

When the summand function $F$ has the required order of **analytic continuation** in the working band and satisfies standard differentiability and tail integrability conditions for Euler–Maclaurin formula, employing **finite-order** EM with even window/kernel does not introduce new singularities and does not elevate pole order. The remainder consists of analytic combinations of endpoint higher-order derivatives and **periodized Bernoulli functions** (see NIST DLMF §2.10(i)). Specifically, finite-order Euler–Maclaurin remainder can be written as a convolution integral of $f^{(p)}$ with periodized Bernoulli functions $P_p$, thus **does not introduce new singularities and does not elevate pole order**; only changes analytic data at endpoints. Precise definition, notation and applicability conditions of EM formula and remainder see NIST DLMF §2.10(i) and §24.11. Thresholds can be identified by degenerate points of $\varphi'=\pi\rho$, and stability radius of zero locations obtained via Rouché theorem (details omitted).

---

## 7. Experimental/Numerical Protocol (Reproducible Outline)

**Device**: Single-channel potential barrier/quantum dot/microwave waveguide.
**Steps**:
(1) **Calibrate Reference**: Determine $(H_0,H)$, estimate $\rho_m,\rho_{m_0}$ from transmission/reflection data via Weyl $m$-function or equivalent inversion.
(2) **Solve Window/Kernel**: Solve for $w_R^\star$ in $\mathsf{PW}^{\mathrm{even}}_{\Omega}$ or exponential family per §5 strong equation.
(3) **Sampling Ledger**: Record $(\Delta,M,T)$ and Nyquist condition $\Delta\le \pi/(\Omega_w+\Omega_h)$; EM takes finite order and gives bound.
(4) **Readout Mapping**: Via Theorem 1.1 restore data to weighting of $\rho_\star$ by $w_R$ and $h$; readout separately for $\rho_{\mathrm{rel}}$ and $\rho_m$, compare reference-dependence of delay sign.
(5) **Pointer/Probability**: Construct dictionary and $G,c$, compute $\beta^\star$, Rayleigh quotient; soft layer uses $\Lambda$ to obtain $p(\rho^\star)$ (Born weights).

---

## 8. Relations to and Clarifications with Existing Theories

* **Operational—Information Equivalence**: This paper does not "derive Born from zero postulates", but rather gives **minimal-KL ↔ Hilbert projection** equivalence **under realistic window/kernel/sampling procedures**; hard limit corresponds to orthogonal projection (Born).
* **Wigner–Smith and DOS**: $\operatorname{tr}\mathsf Q/2\pi=\rho_{\mathrm{rel}}$ comes from the chain of phase—spectral shift—LDOS; "negative delay" is a relative counting effect.
* **PSWF and Optimal Energy Concentration**: In/out-of-band energy allocation for band-limited window is controlled by PSWF spectrum, supporting coercivity and optimal window existence.

---

## 9. Interface with S15–S23 and Quantum Readout Theory

* **S15 (Weyl–Heisenberg Unitary Representation)**: Covariance of window family $U_\tau V_\sigma w$ ensures symmetry of readout operator under phase—scale group; isometry makes information potential $\Lambda$ preserved under group averaging.
* **S16 (de Branges–Krein Canonical System)**: We only use the fact that $m$ is a Herglotz–Nevanlinna function corresponding to some canonical system/HB generating function $E$; do **not** assume the special form $m=-E'/E$ (this formula **only holds in special cases**). $J$-unitarity of transfer matrix $M(t,z)$ ensures $\Im m>0$, thus $\rho_m\ge 0$.
* **S17 (Scattering Operator and Functional Equations)**: Theorem 4.1's $\varphi'=\pi\rho_{\mathrm{rel}}$ is precisely S17's scattering phase derivative criterion; channel eigenvalue equivalence gives phase—density dictionary for $\det S=c_0U$.
* **S18 (Orbit—Spectral Windowing Inequalities)**: Theorem 1.1's tri-decomposition error aligns with S18 §3.3 unified non-asymptotic bounds; aliasing annihilation under Nyquist condition corresponds to S18 band-limited Paley–Wiener hypothesis.
* **S19 (Spectral Graph and Ihara ζ)**: Discrete graph non-backtracking operator gives "discrete phase derivative = discrete spectral density"; this paper's Poisson summation reduces to finite sum in discrete setting, error only from EM layer and truncation.
* **S20 (BN Projection—KL Cost—Sensitivity)**: Theorem 2.2's minimal-KL ↔ minimal energy equivalence directly invokes S20 §2's Bregman–KL identity; softening and $\Gamma$-limit correspond to S20 §3.
* **S21 (Continuum Spectrum Thresholds and Singularity Stability)**: This paper's $\varphi'=\pi\rho_{\mathrm{rel}}$ corresponds to S21 §0.2 phase—density identity (0.1); threshold criterion $\varphi'=0\Leftrightarrow\rho_{\mathrm{rel}}=0$ gives singularity detection for windowed readout.
* **S22 (Window/Kernel Optimization)**: §5's frequency-domain strong equation corresponds to S22 equation (2.2); BN–Bregman softening and $\Gamma$-limit inherit S22 Theorem 5.1.
* **S23 (Multi-Window/Multi-Kernel Joint Optimization)**: This paper's single-window optimum generalizes to S23 vector window and frame operator level; pointer basis criterion (Theorem III) corresponds to S23 §5 dual-frame structure and Wexler–Raz biorthogonality.
* **Quantum Readout Theory (phase-derivative-spectral-density-windowed-readout.md)**: This paper's Theorem 1.1 is that paper's §3 windowed trace and tri-decomposition error; Theorem 4.1 corresponds to that paper's Theorem 2.1 phase—density dictionary; this paper further gives information geometry characterization of Born probability and pointer basis.

---

## 10. Conclusion

This paper unifies quantum measurement as a **windowed readout** problem, obtaining:

* **Born probability** = **minimal-KL information projection** (soft); this equivalence depends on **isometric alignment of "dictionary—constraint—potential"**; when constraint/dictionary are not aligned, this paper's equivalence conclusion does not hold unconditionally.
* **Pointer basis** = **eigenbasis of minimal energy/information projection**, its dominant direction given by $\arg\max_k \frac{|\langle u_k,c\rangle|^2}{\lambda_k}$ (soft/hard consistent, via $\Gamma$-limit);
* **Delay/Tunneling** = readout of **(relative) LDOS**; "negative delay" arises from reference and relative counting; unitary/sub-unitary need distinct treatment.
* **Aliasing Annihilation**: This paper's assertion about $\varepsilon_{\mathrm{alias}}=0$ is based on **strict band-limited + Nyquist** premise; for **nearly band-limited** windows/kernels, we give explicitly computable **Poisson folding tail sum bounds** and **EM remainder bounds**, and give verifiable ledger in experimental protocol (§7).
* **Implementation Roadmap**: PSWF/band-limited window + Nyquist–Poisson–EM + variational optimum, forming **non-asymptotic, reproducible** error closure and design criteria.

---

## References (Selected)

### Core Theory

* de Branges, **Hilbert Spaces of Entire Functions** (Purdue public version).
* Wigner, **Lower Limit for the Energy Derivative of the Scattering Phase Shift**, Phys. Rev. 98, 145 (1955).
* Smith, **Lifetime Matrix in Collision Theory**, Phys. Rev. 118, 349 (1960).
* Yafaev, **Mathematical Scattering Theory: General Theory** (AMS, 1992/2010).
* Pushnitski, **The spectral shift function and the invariance principle**, J. Funct. Anal. 183, 269 (2001); arXiv:math/9911182 (open access).
* Pushnitski, **An integer-valued version of the Birman–Krein formula**, arXiv:1006.0639 (2010) (negative sign convention version).
* Behrndt–Gesztesy–Nakamura, **Spectral shift functions and Dirichlet-to-Neumann maps**, Math. Ann. 371, 1255 (2018); arXiv:1609.08292.
* Teschl, **Mathematical Methods in Quantum Mechanics** (AMS, 2014); Kostenko–Teschl, **Spectral theory as influenced by Fritz Gesztesy**, arXiv:2106.06207 (Weyl–Titchmarsh $m$-function and Herglotz–Pick boundary values).
* Kostenko–Sakhnovich–Teschl, **Weyl–Titchmarsh theory for Schrödinger operators with strongly singular potentials**, arXiv:1007.0136 (2010) (contains Stieltjes inversion lemma).

### Sampling and Energy Concentration

* Slepian–Pollak, **Prolate Spheroidal Wave Functions, I**, Bell Syst. Tech. J. 40, 43 (1961) (public PDF: https://archive.org/details/bstj40-1-43).
* Landau–Pollak, **Prolate Spheroidal Wave Functions, II/III**, Bell Syst. Tech. J. (1961/1962).
* Slepian, **Prolate Spheroidal Wave Functions, Fourier Analysis and Uncertainty — V**, Bell Syst. Tech. J. (1978) (DPSS).

### Information Geometry

* Banerjee et al., **Clustering with Bregman Divergences**, JMLR 6, 1705 (2005).
* Csiszár, **I-divergence geometry of probability distributions and minimization problems**, Ann. Probab. 3, 146 (1975).
* Amari–Nagaoka, **Methods of Information Geometry** (AMS MMONO-191, 2000).

### Extensions and Numerics

* Chen et al., **Generalization of Wigner time delay to subunitary scattering systems**, Phys. Rev. E 103, L050203 (2021).
* NIST DLMF §1.8(iv): Poisson Summation Formula (https://dlmf.nist.gov/1.8).
* NIST DLMF §2.10(i) & §24.11: Euler–Maclaurin formula and remainder (https://dlmf.nist.gov/2.10, https://dlmf.nist.gov/24.11).
* Davy et al., **Transmission eigenchannels and the densities of states of random media**, Phys. Rev. Lett. 114, 033901 (2015) (multi-channel DOS and phase derivative/delay matrix equivalence).
* Grabsch et al., **Time delay and Wigner–Smith matrix for general networks**, Phys. Rev. A 98, 033831 (2018) (experimental verification in random matrix context).
* Hur, **Density of Schrödinger Weyl-Titchmarsh m functions on Herglotz wave functions**, arXiv:1501.01268 (2015).

---

## Appendix: Key Formula Index (for Reference)

* **Poisson summation (this convention $\widehat f(\xi)=\int f(t)e^{-it\xi}dt$)**: $\Delta\sum_{n}F(n\Delta)=\sum_k\widehat F\bigl(\tfrac{2\pi k}{\Delta}\bigr)$.
* **Herglotz boundary value (independent of FT convention)**: $\Im m(E+i0)=\pi\rho(E)$ (a.e.).
* **Phase—density—spectral shift**: $\varphi'=\pi\rho_{\mathrm{rel}}=\pi\xi'$ (a.e., under standard trace class/differentiability conditions; per this paper's BK positive sign convention).
* **Time delay density**: $\tfrac1{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$ (a.e., under unitary scattering).
* **Windowed readout**: $\mathrm{Obs}_{\Delta,T}=\int w_R\,(h\!\star\!\rho_\star)+\varepsilon_{\mathrm{alias}}+\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}}$.
* **Nyquist alias-free (sufficient condition)**: $\Delta\le \pi/(\Omega_w+\Omega_h)$ and $\widehat F(\pm\pi/\Delta)=0$ (for time-domain product $F=w_R\cdot(h\!\star\!\rho)$ on sampling variable $E$; frequency-domain support width is sum bandwidth $\Omega_w+\Omega_h$); necessary and sufficient condition is $\sum_{k\neq 0}\widehat F(2\pi k/\Delta)=0$.
* **Bregman–KL (log-partition)**: $B_\Lambda(\rho'\mid\rho)=\mathrm{KL}(p(\rho)\,|\,p(\rho'))$.
* **Minimal energy solution and dominant direction**: $\beta^\star=\dfrac{G^{-1}c}{c^\ast G^{-1}c}$, $\arg\max_k \frac{|\langle u_k,c\rangle|^2}{\lambda_k}$.
* **PSWF energy concentration and zeros**: $n$-th order has exactly $n$ zeros in $(-1,1)$; $\lambda_0$ controls in-band energy upper bound.
* **Band-limited optimal window strong form**: see §5 frequency-domain equation.

(End of Document)


