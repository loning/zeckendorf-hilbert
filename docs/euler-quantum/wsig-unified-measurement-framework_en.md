# WSIG Unified Measurement Framework (UMS)

**—— Finite-Window Covariant "Scattering—Information—Geometry" Unified Theory (Formal Academic Paper with Complete Proofs)**

**Author**: Auric (S-series / EBOC System)
**Version**: v2.5 (incremented from v2.4)

---

## Abstract

This paper takes **phase—density scale**, **windowed readout**, and **information geometry** as three main axes, welding "state—measurement—probability—pointer—scattering phase—group delay—sampling/frame—error theory—channel capacity" into a verifiable **categorified** unified theory (UMS). The core unification formula adopts **three density expressions under the same scale**:

$$
\boxed{\, d\mu_{\varphi}(E)\ :=\ \frac{\varphi'(E)}{\pi}\,dE\ =\ \frac{1}{2\pi}\,\operatorname{tr}\mathsf Q(E)\,dE\ =\ \rho_{\mathrm{rel}}(E)\,dE\ }\ \ \text{(on a.c. spectrum a.e.)}\,
$$

(The above holds a.e. on the a.c. spectrum, with $\operatorname{Arg}\det S$ taking a **continuous branch**; across thresholds/atomic points, **jump-stitch** via $\Delta\mu_\varphi=\mu_\varphi(\{E_*\})$, corresponding to jumps in the spectral shift function $\xi(E)$ consistent with bound state/threshold multiplicity—in the Levinson-type theorem context, the jump in spectral shift $\xi$ equals the number of bound/half-bound states at that energy.)

Here $\mathsf Q(E)=-i\,S^\dagger(E)\,S'(E)$ is the Wigner–Smith group delay matrix, $\rho_{\mathrm{rel}}(E)=-\xi'(E)$ is the Birman–Kreĭn spectral shift density (using the convention $\det S(E)=e^{-2\pi i\,\xi(E)}$). For multi-channel cases, the total phase is defined as $\varphi(E):=\frac{1}{2}\operatorname{Arg}\det S(E)$ (taking continuous branch).

**Normalization Statement (Unified)**: This paper treats $\mu_\varphi$ as a **locally finite signed Radon measure**, performing Lebesgue decomposition $\mu_\varphi=\mu_\varphi^{\mathrm{ac}}+\mu_\varphi^{\mathrm{s}}+\mu_\varphi^{\mathrm{pp}}$ and Jordan decomposition $\mu_\varphi=\mu_+-\mu_-$ ($\mu_\pm\ge0$). When $\mu_\varphi$ is a non-negative Borel measure satisfying the standard growth/integrability conditions of Herglotz representation (e.g., $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$, with excess absorbed into the $a+bz$ term), there exists a Herglotz function $m$ such that $\pi^{-1}\Im m(E+i0)=\rho_{\mathrm{rel}}(E)$ (a.e.), and under proper normalization (eliminating the $a+bz$ freedom) achieves a **global** representation via **trace-normed** DBK canonical systems; if $\mu_\varphi$ contains a negative part, only **local** representation can be established in a.c. segments where $\rho_{\mathrm{rel}}>0$. Its **absolutely continuous part** satisfies

$$
\boxed{\ d\mu_\varphi^{\mathrm{ac}}(E)=\rho_{\mathrm{rel}}(E)\,dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE=\frac{\varphi'(E)}{\pi}\,dE\ \ \text{(a.e.)}\ }\,.
$$

If singular/atomic parts exist, they are denoted as $\mu_\varphi^{\mathrm{s}}, \mu_\varphi^{\mathrm{pp}}$, and jumps across thresholds/atomic energy levels are manifested via $\Delta\mu_\varphi=\mu_\varphi(\{E_*\})$.

**Remark**: For general scattering pairs, $\rho_{\mathrm{rel}}(E)$ is the **relative** state density with respect to the free system, and may **change sign** (negative group delay and spectral shift density sign changes are observable in many wave scattering systems, related to pulse shaping/resonance backgrounds, see experimental/numerical reports of negative Wigner–Smith delay and complex delay in electromagnetic and non-Hermitian scattering systems). Therefore, $d\mu_{\varphi}$ is **generally a signed measure**. The main theorems of this paper (Theorems 3.1, 3.2) provide a **global** DBK representation when $\mu_\varphi$ has **no negative part entirely**; signed measure cases only yield **local** representation in a.c. segments where $\rho_{\mathrm{rel}}>0$.

**Reference Basis**: The one-to-one correspondence between Herglotz representation and trace-normed canonical systems is established on non-negative measures; for any Herglotz function there exists a unique (up to natural equivalence) trace-normed canonical system.

This formula unifies scattering phase derivative, relative spectral density, and group delay under the same scale; measurement readouts are expressed as **window—kernel** spectral integrals, with finite-order, non-asymptotic error closure given by **Nyquist–Poisson–Euler–Maclaurin (EM)** tri-decomposition; probability uniqueness is guaranteed by Naimark extension and Gleason's theorem; sampling/frame thresholds are characterized by Landau necessary density, Wexler–Raz biorthogonality, and Balian–Low impossibility; information monotonicity and capacity bounds for open systems are controlled by the GKSL master equation, quantum relative entropy monotonicity under **positive trace-preserving** maps (DPI), and the HSW theorem.

**Keywords**: Scattering phase; Wigner–Smith group delay; Birman–Kreĭn; de Branges / Herglotz; Naimark extension; Gleason; Landau density; Wexler–Raz; Balian–Low; Euler–Maclaurin; Poisson; GKSL; DPI; HSW.

---

## 0. Preliminaries and Notation

**0.1 Scattering and Group Delay.** Let $S(E)\in U(N)$ have **weak derivative** or **bounded variation** on the a.c. spectrum. The Wigner–Smith group delay matrix is defined as $\mathsf Q(E)=-i\,S^\dagger(E)\,S'(E)$, where $S'(E)$ is understood as a **distributional derivative**. For unitary $S$, $S^\dagger S'=(S^{-1}S')$ is anti-Hermitian, so the trace is purely imaginary. By Jacobi's formula $\tfrac{d}{dE}\log\det S=\operatorname{tr}(S^{-1}S')$ and $S^{-1}=S^\dagger$ (unitary), we have $\tfrac{d}{dE}\operatorname{Arg}\det S=\Im\,\operatorname{tr}(S^\dagger S')$; thus

$$
\operatorname{tr}\mathsf Q(E)=-i\,\operatorname{tr}\!\big(S^\dagger S'(E)\big)=\Im\,\operatorname{tr}\!\big(S^\dagger S'(E)\big)=\frac{d}{dE}\operatorname{Arg}\det S(E)\ \ \text{(taking continuous branch, holds a.e. on a.c. spectrum)},
$$

For single-channel $S(E)=e^{2i\varphi(E)}$, $\operatorname{tr}\mathsf Q(E)=2\,\varphi'(E)$. Across thresholds/atomic points, differentiability everywhere is not required; instead, stitching via jumps $\Delta\mu_\varphi$.

**Notation Convention**: Hereafter "a.c." denotes absolutely continuous spectral region; "a.e." means almost everywhere with respect to Lebesgue measure. The domain of $\mathsf Q$ is the a.e. point set in the a.c. spectral region; outside this interval (thresholds, atomic points), the jump part $\mu_\varphi^{\mathrm{pp}}$ of the spectral measure is used.

**Multi-channel scaled phase**: Let $\varphi(E):=\frac{1}{2}\operatorname{Arg}\det S(E)$ (choosing continuous branch, a.e. differentiable on a.c. spectrum), then

$$
d\mu_\varphi(E)=\frac{\varphi'(E)}{\pi}\,dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE.
$$

Single-channel reduces to $S=e^{2i\varphi}$. $\operatorname{Arg}\det S$ takes a locally continuous branch, differentiable only a.e. on a.c. spectrum; jumps compensate when crossing thresholds and atomic points.

**Unit Explanation**: This paper takes $\mathsf Q(E)=-i\,S^\dagger(E)S'(E)$, whose dimension is **energy$^{-1}$** ($S'(E)$ differentiated with respect to energy produces dimension $1/\text{energy}$); for **unitary scattering**, the physical time delay takes the **Wigner–Smith delay**: $\tau=\hbar\,\mathrm{eig}(\mathsf Q)$; for **non-unitary/dissipative** cases $\mathsf Q$ is generally non-self-adjoint (eigenvalues may be complex), and the definition of $\tau$ follows §6.2 specification (e.g., taking $\Re\,\mathrm{eig}(\mathsf Q)$ as dwell-related quantity); this paper does not conflate the two. At an isolated Breit–Wigner resonance, from $\tau(E)=2\hbar\,\delta'(E)$ and $\delta'(E_0)=2/\Gamma$, we get $\tau_{\max}(E_0)=4\hbar/\Gamma$, while the lifetime $\tau_{\text{life}}=\hbar/\Gamma$, differing by a **factor of 4**. **Width Notation Remark**: This paper uniformly uses pole $E_0-i\Gamma/2$ for width; if referencing literature adopting $E_0-i\Gamma$, multiply all $\tau$ values in this paper by $1/2$ for alignment (peak changes from $4\hbar/\Gamma$ to $2\hbar/\Gamma$). This convention is consistent with electromagnetic and quantum scattering literature (corresponding to non-Hermitian extension in §6.2).

**0.2 Spectral Shift and Birman–Kreĭn.** Adopting BK's **negative sign convention**: $\ \det S(E)=e^{-2\pi i\,\xi(E)}$.

**Determinant Convention (BK/Fredholm)**: In this paper, $\det S(E)$ refers to the **Fredholm determinant in Birman–Kreĭn sense** $\det_{\mathrm F}S(E)$. Under the premise $(H-z)^{-1}-(H_0-z)^{-1}\in\mathfrak S_1$ (equivalently, $S(E)-I\in\mathfrak S_1$ at a.e. $E$), $\det_{\mathrm F}S(E)$ is well-defined, $\operatorname{Arg}\det_{\mathrm F}S(E)$ can take a **continuous branch** and is **a.e. differentiable** on the a.c. spectrum, giving

$$
\frac{d}{dE}\operatorname{Arg}\det_{\mathrm F}S(E)=-2\pi\,\xi'(E),\qquad \rho_{\mathrm{rel}}(E):=-\xi'(E),
$$

thus $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$ (a.e.). Negative group delay and spectral shift density sign changes are observable in many wave scattering systems, related to pulse shaping/resonance backgrounds (see experimental/numerical reports of negative Wigner–Smith delay and complex delay in electromagnetic and non-Hermitian scattering systems, including recent sub-unitary scattering work).

**Scattering Pair Premise (BK Formula Applicability)**: The above BK identity $\det S(E)=e^{-2\pi i\xi(E)}$ and its derived relation $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}=-\xi'$ hold under **self-adjoint scattering pair** $(H,H_0)$, where $H_0$ is the free Hamiltonian, $H=H_0+V$ is the full Hamiltonian, assuming $(H-z)^{-1}-(H_0-z)^{-1}$ belongs to **trace class** (or equivalent summability conditions, such as $V(H_0-z)^{-1}$ trace class), ensuring wave operators $W_\pm=\mathrm{s-lim}_{t\to\pm\infty}e^{iHt}e^{-iH_0 t}$ exist and are complete, scattering operator $S=W_+^\dagger W_-$ is unitary, and spectral shift function $\xi$ is well-defined; non-Hermitian/dissipative cases require separate treatment under maximal dissipative extension or self-adjoint extension frameworks (see Pushnitski, A., arXiv:1006.0639; Behrndt–Malamud–Neidhardt, arXiv:0712.3120).

**0.3 DBK Canonical Systems and Herglotz Dictionary.** The Weyl–Titchmarsh function $m:\mathbb C^+\to\mathbb C^+$ of a one-dimensional de Branges–Kreĭn canonical system $JY'(t,z)=zH(t)Y(t,z)$ is a Herglotz function, with standard representation $m(z)=a+bz+\int\!\big(\frac{1}{t-z}-\frac{t}{1+t^2}\big)\,d\nu(t)$ where $d\nu\ge0$ is a non-negative Borel measure satisfying $\int (1+t^2)^{-1}\,d\nu(t)<\infty$ (excess absorbed into the $a+bz$ term), and the boundary imaginary part gives the absolutely continuous spectral density $\rho_{\mathrm{ac}}(E)=\pi^{-1}\Im m(E+i0)=\pi^{-1}\frac{d\nu^{\mathrm{ac}}}{dE}$ (a.e.); here $\rho_{\mathrm{ac}}$ refers to the spectral density of the **absolutely continuous spectral part of the operator under consideration** (this $\rho_{\mathrm{ac}}$ is not the relative spectral density $\rho_{\mathrm{rel}}$ in this paper); if singular/atomic parts exist, their contributions are reflected in the corresponding spectral measure decomposition. Under proper normalization (eliminating the $a+bz$ freedom), **trace-normed** canonical systems have a **one-to-one and unique** correspondence (up to natural equivalence) with Herglotz functions and de Branges spaces (see Remling, C., Hur, I., arXiv:1501.01268; de Branges, L., Hilbert Spaces of Entire Functions).

**Signed Measure Case Piecewise Stitching**: When $\mu_\varphi$ contains a negative part (i.e., $\rho_{\mathrm{rel}}$ changes sign), one can only construct trace-normed canonical systems $(H_j,J_j)$ and corresponding Herglotz functions $m_j$ separately on each a.c. segment $I_j$ where $\rho_{\mathrm{rel}}>0$, such that $\pi^{-1}\Im m_j(E+i0)=\rho_{\mathrm{rel}}(E)$ a.e. on $I_j$; the segments are stitched piecewise according to the Lebesgue decomposition and Jordan decomposition of the spectral measure $\mu_\varphi$; uniqueness and consistency are guaranteed by trace-normed normalization **within each segment**, but **no single canonical system** provides a global Herglotz representation.

**0.4 Sampling, Frames, and Thresholds.** Stable sampling/interpolation of Paley–Wiener classes obeys Landau necessary density (Landau 1967, see reference [4]); dual windows of Gabor systems satisfy Wexler–Raz biorthogonality (Daubechies–Landau–Landau 1995, see reference [5]); at critical density, Balian–Low impossibility is triggered (see reference [6]).

**0.5 Measurement and Probability Uniqueness.** Any POVM can be obtained from a PVM in a larger space via compression (Naimark extension); when $\dim\mathcal H\ge 3$, probability measures satisfying additivity must be of the form $\operatorname{Tr}(\rho\,\cdot)$ (Gleason's theorem). Two-level systems can be supplemented with the Busch–Gleason POVM version, but this paper does not need to address it.

**0.6 Open Systems and Information Bounds.** Markovian open evolution is described by the GKSL (Lindblad) master equation; quantum relative entropy is monotonically non-increasing under **positive trace-preserving** maps (DPI); the unassisted classical capacity of quantum channels is given by the HSW regularized formula.

**0.7 Nyquist–Poisson–EM (Finite-Order Non-asymptotic Error Theory).** Under **ideal sampling and ideal reconstruction filtering**, band-limited signals have vanishing aliasing terms when sampling rate $f_s\ge 2B$; engineering robustness typically takes $f_s>2B$. Euler–Maclaurin (EM) for discrete-continuous interchange, taking $m\in\mathbb N$ such that integrand/summand $F\in C^{2m}$ and $F^{(2m)}$ is bounded or has finite total variation, gives **explicit integral bounds** for the remainder. EM remainder adopts the formalized bound from Archive of Formal Proofs (AFP-Isabelle) entry **The Euler–MacLaurin Formula** (Eberl, M., see reference [11]), explicitly specifying in implementation the chosen order $m$ and regularity of the integrand/summand ($C^{2m}$ or finite total variation) to reproduce the bound.

**Empirical Guidance for Choosing $m$** (implementation operability):
- $m=1$ (2nd-order correction): integrand $F\in C^2$, suitable for piecewise linear windows or low-smoothness kernels;
- $m=2$ (4th-order correction): $F\in C^4$, suitable for most smooth window functions (e.g., Gaussian, Hann) and spectral integrals;
- $m=3$ (6th-order correction): $F\in C^6$, suitable for high-precision requirements or controlling tail oscillations.

In practice, first verify that the $L^\infty$ norm or total variation of $F^{(2m)}$ is finite, then substitute into the AFP-Isabelle remainder bound formula to obtain an executable bound.

---

## 1. Axiomatic System

**A1 (Dual Representation and Covariance).** $\mathcal H(E)$ (energy representation) and $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$ (phase—scale representation, where $a>0$ is determined by the Mellin weight used) are isometrically equivalent; discrete-continuous interchange uses **finite-order** EM, controlling the remainder under the smoothness and (bounded or finite variation) premise of 0.7. This "isometric equivalence" refers to the identity operator realization when the DBK canonical system/Weyl–Mellin transform **has been constructed**; readers should not interpret this as unconditional isomorphism between arbitrary systems. **Implementation Premise**: When $\mu_\varphi$ is a non-negative Borel measure satisfying Herglotz conditions (standard growth/integrability, e.g., $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$), there exists a Herglotz function $m$ such that under proper normalization (eliminating the $a+bz$ freedom), **global** DBK representation and isometric equivalence are realized via **trace-normed** DBK canonical system; in this case $\mu_\varphi^{\mathrm{ac}}$ satisfies $\rho_{\mathrm{rel}}=\pi^{-1}\Im m$ (a.e.). If $\mu_\varphi$ contains a negative part, isometric equivalence is realized piecewise only in a.c. segments where $\rho_{\mathrm{rel}}>0$, **not** guaranteeing global realization by a single canonical system. (**Parenthetical note**: $\rho_{\mathrm{rel}}=-\xi'$ is the relative state density, **generally can change sign**; thus $\mu_\varphi$ is often a **signed measure**, only its non-negative case can be **globally** represented by Herglotz–DBK, see Theorem 3.1.)

**A2 (Finite Window Readout).** Any "realizable readout" is written as a window—kernel spectral integral $K_{w,h}=\int h(E)\,w_R(E)\,d\Pi_A(E)$. To ensure that the expectation value $\operatorname{Tr}(\rho K_{w,h})$ of $K_{w,h}$ is well-defined and uniformly bounded over **all density operators** $\rho$, this paper **restricts** $g(E):=h(E)w_R(E)\in L^\infty(\mathbb R;\mathbb R)$ and Borel measurable, whereby $K_{w,h}$ is a **bounded self-adjoint** operator; error is **non-asymptotically closed** by "aliasing (Poisson) + Bernoulli layer (EM) + truncation" three terms (under ideal sampling, band-limited with $f_s\ge 2B$ gives zero aliasing). A "readout" has numerical value $\operatorname{Tr}(\rho K_{w,h})$. **Notation Convention**: Hereafter we uniformly use $\Pi_A$ for projection-valued spectral measure (avoiding notational ambiguity with energy variable $E$).

**A3 (Probability—Information Consistency).** For PVM $\{P_j\}$ and state $\rho$, the linear constraint $p_j=\operatorname{Tr}(\rho P_j)$ makes the feasible set a singleton $\{p^\star\}$; any strictly convex Bregman/KL I-projection uniquely takes value at $p^\star$; for POVM, first apply Naimark extension to PVM then push back. Gleason ($\dim\mathcal H\ge3$) ensures uniqueness of this probability form. **Dimension Condition**: Two-level systems ($\dim\mathcal H=2$) need supplementation with the Busch–Gleason POVM version (Busch, P., Phys. Rev. Lett., 2003).

**A4 (Pointer Subspace / Spectral Minimum Infimum Version).**

**(Notation Convention)** For any $r\in\mathbb N$:
1. $U:\mathbb C^r\to\mathcal H$ denotes **isometric embedding** (column vectors $(u_1,\dots,u_r)$ orthonormal), so $U^\dagger U=I_r$, and $\mathrm{tr}(U^\dagger K_{w,h}U)=\sum_{j=1}^r\langle u_j,K_{w,h}u_j\rangle$.
2. $P_M$ is the **orthogonal projection** onto an $r$-dimensional subspace $M$ of $\mathcal H$, with $\mathrm{tr}_M(P_M K_{w,h}P_M)=\mathrm{tr}(U^\dagger K_{w,h}U)$ (the image of $U$ is $M$).

Thus the following "compressed trace/variational formulations" are completely equivalent.

Let $K_{w,h}=\int g(E)\,d\Pi_A(E)$ be **bounded self-adjoint**. For any $r\in\mathbb N$, denote the spectral projection $P_t:=\mathbf{1}_{(-\infty,t]}(K_{w,h})$. Define
$$
m_r:=\inf_{U^\dagger U=I_r}\mathrm{tr}\!\big(U^\dagger K_{w,h}U\big).
$$
(**Trace Convention**: Here $\mathrm{tr}(P_M K_{w,h}P_M)$ is the **finite-dimensional trace** $\mathrm{tr}_M$ on $M$, equivalent to $\mathrm{tr}(U^\dagger K_{w,h}U)$, where $U:\mathbb C^r\to\mathcal H$ is the isometric embedding of $M$.)
Then for any $t\in\mathbb R$ and any $r$-dimensional subspace $M\subset\mathrm{Ran}\,P_t$, $\mathrm{tr}_M(P_M K_{w,h}P_M)\le r\,t$, and
$$
m_r=\inf_{t\in\mathbb R}\ \inf_{\substack{M\subset\mathrm{Ran}\,P_t \\ \dim M=r}}\mathrm{tr}_M(P_M K_{w,h}P_M),
$$
**generally only achieving the infimum** (not guaranteed to be attained). **If** $K_{w,h}$ is **compact** or on **finite-dimensional truncation** (**or** at its bottom spectral threshold $t_0:=\inf\sigma(K_{w,h})$ there exist at least $r$ **eigenvalues**, which may be **embedded** eigenvalues, counting multiplicity), then this infimum **is attained**, and the minimal subspace is spanned by eigenvectors of the **smallest $r$** eigenvalues.

**A5 (Phase—Density—Delay Scale).** Adopting BK convention,

$$
\boxed{\, \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}\ \ \text{(a.e.)}\ }\,.
$$

**Premise**: See §0.2 "Scattering Pair Premise (BK Formula Applicability)".

**A6 (Sampling—Frame Thresholds).** Stable sampling satisfies Landau necessary density; multi-window duality is described by Wexler–Raz; critical density triggers Balian–Low impossibility.

**A7 (Channel—Monotonicity—Capacity).** Evolution is governed by the GKSL master equation; quantum relative entropy is monotone under **positive trace-preserving (PTP)** maps (DPI); classical capacity is given by the HSW theorem (requiring **completely positive and trace-preserving (CPTP)** channels).

---

## 2. Categorical Definition of UMS

**Definition 2.1 (Objects).**
$U=(\mathcal H,\ \mathcal C,\ \mathscr O,\ \mathbb W,\ \mathcal S,\ D)$, where
(i) $\mathcal H$: Hilbert bundle fibrized by $\mathcal H(E)/\mathcal H_a$;
(ii) $\mathcal C$: Closed/open evolution (including GKSL semigroup);
(iii) $\mathscr O$: Observables and spectral measure $\Pi_A$;
(iv) $\mathbb W$: Window—kernel system and Nyquist–Poisson–EM error ledger;
(v) $\mathcal S$: Scattering functor $E\mapsto(S,\mathsf Q,\xi)$;
(vi) $D$: Information divergence (KL/Bregman) and its induced geometry.

**Definition 2.2 (States and Scale).** Pure/mixed states are vectors/density operators respectively; define the **phase—density scale**

$$
d\mu_{\varphi}(E)\ :=\ \frac{\varphi'(E)}{\pi}\,dE\ =\ \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE\ =\ \rho_{\mathrm{rel}}(E)\,dE\quad\text{(generally a signed measure)}\,.
$$

(The above holds a.e. on the a.c. spectrum, with $\operatorname{Arg}\det S$ taking a **continuous branch**; across thresholds/atomic points, **jump-stitch** via $\Delta\mu_\varphi=\mu_\varphi(\{E_*\})$.)

**Normalization Statement (Unified)**: This paper treats $\mu_\varphi$ as a **locally finite signed Radon measure**, performing Lebesgue decomposition $\mu_\varphi=\mu_\varphi^{\mathrm{ac}}+\mu_\varphi^{\mathrm{s}}+\mu_\varphi^{\mathrm{pp}}$ and Jordan decomposition $\mu_\varphi=\mu_+-\mu_-$ ($\mu_\pm\ge0$). When $\mu_\varphi$ is a non-negative Borel measure satisfying the standard growth/integrability conditions of Herglotz representation (e.g., $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$, with excess absorbed into the $a+bz$ term), there exists a Herglotz function $m$ such that $\pi^{-1}\Im m(E+i0)=\rho_{\mathrm{rel}}(E)$ (a.e.), and under proper normalization (eliminating the $a+bz$ freedom) achieves a **global** representation via **trace-normed** DBK canonical system; if $\mu_\varphi$ contains a negative part, only **local** representation can be established in a.c. segments where $\rho_{\mathrm{rel}}>0$. Its **absolutely continuous part** satisfies

$$
d\mu_\varphi^{\mathrm{ac}}(E)=\rho_{\mathrm{rel}}(E)\,dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE=\frac{\varphi'(E)}{\pi}\,dE\ \ \text{(a.e.)}\,.
$$

If singular/atomic parts exist, they are denoted as $\mu_\varphi^{\mathrm{s}}, \mu_\varphi^{\mathrm{pp}}$, and jumps across thresholds/atomic energy levels are manifested via $\Delta\mu_\varphi=\mu_\varphi(\{E_*\})$.

**Definition 2.3 (Morphisms).** Morphisms between objects are structure-preserving maps respecting (i)–(vi); morphisms between states default to **CPTP (quantum channels)**; only when stating DPI may we relax to **positive trace-preserving (PTP)** maps (DPI still holds in this scope, but HSW capacity theorem requires CPTP).

---

## 3. Main Theorems and Complete Proofs

### Theorem 3.1 (UMS Representation Theorem, Non-negative Measure Case)

**Proposition.** In the case where $\mu_\varphi$ **has no negative part entirely** (equivalently, each part of its Lebesgue decomposition is non-negative), any finite-window measurement theory satisfying A1–A7 is equivalent to some $U\in\mathbf{UMS}$ determined by a DBK canonical system (and its Herglotz function $m$); if $\mu_\varphi$ is a signed measure, only **local** representation can be obtained in a.c. segments where $\rho_{\mathrm{rel}}>0$, **cannot** guarantee a **global** representation by a single DBK system. Under this equivalence,

$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}\quad\text{(a.e.)},
$$

measurement-side $K_{w,h}$ and information-side (I-projection) satisfy A2–A3; frames and thresholds satisfy A6; equivalence is unique up to phase reparametrization and unitary transformation.

**Proof.**
(1) **Scattering—Phase—Density Unification.** From 0.1, $\operatorname{tr}\mathsf Q=\tfrac{d}{dE}\operatorname{Arg}\det S$; from 0.2, $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$; for single-channel, combining with $\operatorname{tr}\mathsf Q=2\varphi'$ yields the unified scale.
(2) **Herglotz—Canonical System—de Branges.** When $\mu_{\varphi}$ is a non-negative Borel measure satisfying the standard growth/integrability conditions of Herglotz representation (e.g., $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$, with excess absorbed into the $a+bz$ term), there exists Herglotz $m$ such that $\pi^{-1}\Im m=\rho_{\mathrm{rel}}$ (a.e.), and under proper normalization (eliminating the $a+bz$ freedom) this scale is determined by a de Branges–Kreĭn canonical system; de Branges theory establishes equivalence among Herglotz $m$, trace-normed canonical systems, and de Branges spaces. **In the general case** where $d\mu_{\varphi}$ is a signed measure, construction can proceed separately in a.c. segments where $\rho_{\mathrm{rel}}>0$ and stitched piecewise accordingly. **Reference Basis**: DBK inverse spectral theory provides global (trace-normed) formulation and uniqueness for non-negative measures satisfying Herglotz conditions.
(3) **Windowed Readout and Finite-Order Closure.** Under **closed-set band-limited and ideal filtering** premise, $f_s\ge2B$ can make baseband aliasing vanish; engineering robustness typically takes $f_s>2B$ (see Theorem 4.1); EM under 0.7 assumptions gives Bernoulli layer and remainder bound, so A2 holds.
(4) **Probability Consistency.** POVM is extended by Naimark to PVM; Gleason guarantees Born form uniqueness; I-projection of strictly convex divergence degenerates to Born on singleton feasible set.
(5) **Frames and Thresholds.** Landau necessary density, Wexler–Raz biorthogonality, and Balian–Low impossibility respectively give thresholds, duality, and critical barriers.
The above establishes the proof. **If $\mu_\varphi$ contains a negative part, the following conclusions are interpreted piecewise** (see §0.3/A1). ∎

---

### Theorem 3.2 (Scale Uniqueness)

**Proposition.** (**In the case where $\mu_\varphi$ has no negative part entirely and satisfies Herglotz conditions**; the BK convention used is $\det S=e^{-2\pi i\xi}$, see 0.2) If two configurations have the same $\operatorname{tr}\mathsf Q(E)$ (a.e.) and their measurement Naimark extensions are isomorphic, and we agree that $m$ takes the normalization consistent with the trace-normed canonical system (eliminating the $a+bz$ freedom), and $\operatorname{Arg}\det S$ takes the same continuous branch (up to constant), then the two are unitarily equivalent in $\mathbf{UMS}$; thus

$$
d\mu_\varphi(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE
$$

is the **unique scale** for the readout geometry (up to null sets and monotone reparametrization).

**Premise Statement**: This theorem requires $\mu_\varphi$ to have no negative part entirely and satisfy the standard growth/integrability conditions of Herglotz representation (e.g., $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$, with excess absorbed into the $a+bz$ term); the Herglotz function $m$ used takes the normalization consistent with the trace-normed canonical system (eliminating the $a+bz$ freedom); $\operatorname{Arg}\det S$ takes the same continuous branch (up to constant).

**Proof.** Same $\operatorname{tr}\mathsf Q$ $\Rightarrow$ $\operatorname{Arg}\det S$ differs by a constant; by BK, same $\xi'$ and $\rho_{\mathrm{rel}}$. Under the premise that $\mu_\varphi$ has no negative part entirely and satisfies Herglotz conditions, extensions are isomorphic, and normalization is consistent, unitary equivalence is a **sufficient condition**; from inverse spectral theory of **trace-normed** canonical systems, we obtain a uniquely determined (up to natural reparametrization) $m$, which in turn determines the canonical system and de Branges space; Naimark isomorphism ensures POVM-layer consistency, so unitary equivalence exists. Removing this isomorphism assumption yields only local equivalence. ∎

---

### Theorem 3.3 (Trinity)

**(i) Born = I-projection (Strict).** Under PVM $\{P_j\}$, the feasible set is a singleton $\{p^\star\}$; any strictly convex Bregman/KL I-projection uniquely takes value at $\,p^\star$. For POVM, first apply Naimark extension, then push back. ∎

**(ii) Pointer = Spectral Minimum (Spectral Projection Version Ky Fan, with Attainability)**. Let $K_{w,h}$ be bounded self-adjoint, $P_t:=\mathbf{1}_{(-\infty,t]}(K_{w,h})$. For any $r\in\mathbb N$,
$$
\inf_{U^\dagger U=I_r}\mathrm{tr}(U^\dagger K_{w,h}U)=\inf_{t\in\mathbb R}\ \inf_{\substack{M\subset\mathrm{Ran}\,P_t \\ \dim M=r}}\mathrm{tr}_M(P_M K_{w,h}P_M),
$$
**generally only an infimum**; **if** $K_{w,h}$ is **compact** or on **finite-dimensional truncation** (**or** at its bottom spectral threshold $t_0:=\inf\sigma(K_{w,h})$ there exist at least $r$ **eigenvalues**, which may be **embedded** eigenvalues, counting multiplicity), then this infimum **is attained**, and is equivalent to
$$
\min_{U^\dagger U=I_r}\mathrm{tr}(U^\dagger K_{w,h}U)=\sum_{k=1}^{r}\lambda^{\uparrow}_k(K_{w,h}),
$$
where $\lambda^{\uparrow}_1\le\lambda^{\uparrow}_2\le\cdots$ is the **ascending** eigenvalue sequence (counting multiplicity). **Finite-dimensional special case**: If $K_{w,h}$ is an $n\times n$ matrix with spectrum recorded in descending order $\lambda_1\ge\cdots\ge\lambda_n$, then $\sum_{k=1}^{r}\lambda^{\uparrow}_k=\sum_{k=n-r+1}^{n}\lambda_k$.

The minimal subspace is spanned by eigenvectors of the smallest $r$ eigenvalues. The above two formulations are equivalent within their respective domains of applicability.

**Reference Basis**: Ky Fan variational principle ("sum of smallest $r$ eigenvalues = minimum of compressed trace") applies to finite-dimensional/compact operator cases; general bounded self-adjoint operators adopt spectral projection formulation. See Horn, R. A. & Johnson, C. R., *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013, Chapter 4 Theorem 4.3.4 (Ky Fan minimax principle) and Corollary 4.3.3 (trace minimum); or equivalent systematic treatment of Fan max/min principles in textbooks. ∎

**(iii) Windows = Minimax (Band-limited Worst Case, Well-defined Version).** Let

$$
\mathcal F=\{f\in L^2(\mathbb R):\operatorname{supp}\widehat f\subset[-B,B]\},\quad \|f\|_2=1.
$$

Take **target window** $w_{\mathrm{tar}}\in L^2(\mathbb R)$ (e.g., $w_{\mathrm{tar}}=\mathbf{1}_{[-R,R]}/\sqrt{2R}$), and restrict **design window** to $w\in\mathcal F$, $\|w\|_2=1$. Define

$$
\mathcal E(w):=\sup_{f\in\mathcal F}\big|\langle f,w_{\mathrm{tar}}\rangle-\langle f,w\rangle\big|=\|P_{\mathcal F}(w_{\mathrm{tar}}-w)\|_2.
$$

Then the minimum is attained if and only if

$$
w^\star=\frac{P_{\mathcal F}w_{\mathrm{tar}}}{\|P_{\mathcal F}w_{\mathrm{tar}}\|_2}\quad(\|P_{\mathcal F}w_{\mathrm{tar}}\|_2\neq 0)
$$

is achieved; if $P_{\mathcal F}w_{\mathrm{tar}}=0$, then any $w\in\mathcal F$, $\|w\|_2=1$ is a minimal solution, with minimum error 1. This equality follows directly from Riesz representation and the orthogonal projection property of $P_{\mathcal F}$; the extremum is achieved by $f^\star=P_{\mathcal F}(w_{\mathrm{tar}}-w)/\|P_{\mathcal F}(w_{\mathrm{tar}}-w)\|_2$ (when denominator is non-zero). For multi-window cases, optimal dual windows are still characterized by Wexler–Raz biorthogonality. ∎

---

### Theorem 3.4 (Phase-ification of Sampling—Frame Thresholds)

**Proposition.** Define

$$
\boxed{\ T(E)\ :=\ \mu_\varphi\big((E_0,E]\big)\ }\,.
$$

On **a.c. intervals**,

$$
T'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}\quad\text{(a.e.)},
$$

**across atomic points** stitch by jump amount $\Delta T=\mu_\varphi(\{E_*\})$; equivalently, if no singular/atomic parts exist,

$$
T(E)=\int_{E_0}^E \rho_{\mathrm{rel}}(u)\,du=\frac{\varphi(E)-\varphi(E_0)}{\pi}.
$$

When $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ is **non-negative** a.e. in the interval under consideration, $T$ is **monotonically non-decreasing** and can serve as a (possibly degenerate) reparametrization; when it is a.e. **strictly positive** in that interval, $T$ is **strictly monotone** and gives an **invertible** reparametrization.

**Scale Transfer Condition for Landau Density**: Landau necessary density (see reference [4], Landau, H. J., Acta Math. 117, 37–52, 1967) originally targets the **equidistant linear scale** $E$ axis Paley–Wiener space. If the $E\mapsto T$ reparametrization is **nonlinear**, then Landau threshold equivalence between the $T$ axis and $E$ axis holds under the following **additional regularity conditions**:
(i) $T$ is **absolutely continuous** and **bi-Lipschitz** on the a.c. interval under consideration (i.e., there exist $0<c\le C<\infty$ such that $c\le T'(E)\le C$ a.e.), or more generally,
(ii) $T'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$ has **positive bounds** from above and below on that interval: $\inf_{E\in I}T'(E)>0$ and $\sup_{E\in I}T'(E)<\infty$.

Under this regularity condition, bandwidth $B_E$ on the $E$ axis and bandwidth $B_T$ on the $T$ axis maintain equivalence (up to bounded factors) via pullback/pushforward, so the Landau density threshold is not distorted. If the above regularity is not satisfied (e.g., $T'$ can approach zero or diverge arbitrarily), only the **order relation induced by monotonicity** can be guaranteed, and quantitative statements of Landau thresholds cannot be unconditionally inherited.

Multi-window reconstructibility is characterized by the frame operator and Wexler–Raz biorthogonality; at critical density, Balian–Low impossibility is satisfied. ∎

---

## 4. Finite-Order Non-asymptotic Error Theory (Nyquist–Poisson–EM)

**Theorem 4.1 (Poisson—Nyquist: Baseband Aliasing-free).** Let $\operatorname{supp}\widehat f\subset[-B,B]$. Under **ideal sampling and ideal reconstruction** premise:
- When $f_s\ge 2B$, Poisson replica frequency bands do not overlap, so within **baseband/reconstruction domain** only $k=0$ contributes, aliasing terms vanish;
- When $f_s<2B$, out-of-bounds spectral overlap produces aliasing. ∎

**Theorem 4.2 (Euler–Maclaurin: Finite-Order Bernoulli Layer and Remainder).** When $F\in C^{2m}([a,b])$ and $F^{(2m)}$ is bounded or has finite total variation, EM gives Bernoulli corrections up to order $2m$ and an **explicit** integral remainder; AFP-Isabelle provides formalized proof for the remainder and convergence conditions, thus enabling **choice of finite order $m$** in implementation and obtaining executable bounds. EM remainder adopts the **formalized bound** from AFP-Isabelle 'Euler_MacLaurin', explicitly specifying in implementation the chosen order $m$ and regularity of the integrand/summand ($C^{2m}$ or finite total variation) to reproduce the bound. ∎

**Theorem 4.3 (Tri-decomposition Closure).** Implementation of $K_{w,h}$ can be written as: discrete summation (Nyquist) $+$ EM finite-order correction (Bernoulli layer) $+$ remainder (aliasing + truncation). Under ideal sampling and reconstruction, when band-limited and $f_s\ge 2B$, the aliasing layer vanishes; EM remainder is controlled by the bound in 4.2, yielding **finite-order, non-asymptotic closure**. ∎

---

## 5. Information Monotonicity and Capacity Bounds

**Theorem 5.1 (DPI: Relative Entropy Monotone under **PTP** Maps).** For any **positive trace-preserving (PTP)** map $\Phi$,

$$
D\!\left(\Phi(\rho)\,\middle\Vert\,\Phi(\sigma)\right)\le D(\rho\Vert\sigma).
$$

**Proof Sketch.** Müller-Hermes–Reeb prove DPI under **positive trace-preserving** (not necessarily CP) via "sandwiched Rényi divergence + complex interpolation", and characterize equality cases via Petz recovery map.

**(Parenthetical Note)** DPI for Umegaki relative entropy holds **for any positive and trace-preserving linear map**; this is the result of Müller-Hermes–Reeb (Müller-Hermes & Reeb, 2015), and does not require CP/2-positive/Schwarz conditions. This paper still **restricts channels to CPTP** when stating HSW and other capacity conclusions. ∎

**Theorem 5.2 (HSW: Unassisted Classical Capacity of **CPTP** Channels).** The unassisted classical capacity of a quantum **completely positive and trace-preserving (CPTP)** channel $\mathcal N$ satisfies

$$
C(\mathcal N)=\lim_{n\to\infty}\frac{1}{n}\,\chi\!\left(\mathcal N^{\otimes n}\right),\qquad I_{\mathrm{acc}}\le \chi\,.
$$

Therefore **single-shot** Holevo information $\chi(\mathcal N)$ is generally insufficient to give capacity (requiring regularized limit).

**Proof Sketch.** See Watrous textbook for standard derivation of encoding, Holevo bound, and strong duality. ∎

---

## 6. Derived Structures and Physical Consequences

**6.1 Time Density and Delay Integral.** See §3.4 definition (and stitch by atomic point jumps). On **a.c. intervals**,

$$
T'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)\quad\text{(a.e.)}.
$$

When $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ is **non-negative** a.e. in the interval under consideration, $T$ is **monotonically non-decreasing** and can serve as a (possibly degenerate) reparametrization; when it is a.e. **strictly positive** in that interval, $T$ is **strictly monotone** and gives an **invertible** reparametrization. When $(2\pi)^{-1}\operatorname{tr}\mathsf Q\ge 0$ a.e., $T$ is monotonically non-decreasing; **only when the regularity conditions (i) or (ii) in §3.4 hold**, Landau necessary density is **quantitatively equivalent** between $T$ and $E$ axes; if conditions are not satisfied, only the order relation induced by monotonicity is retained (see §3.4 "Scale Transfer Condition for Landau Density" and reference [4]). **Single-channel** case: $S=e^{2i\varphi}$, so $T(E)=\dfrac{\varphi(E)-\varphi(E_0)}{\pi}$, characterizing measurable group delay and connecting to partial density states.

**6.2 Non-Hermitian/Dissipative and Resonance Lifetime.** Dissipative (non-unitary) systems admit "modified BK" and corresponding time delay generalizations. In single-channel Breit–Wigner approximation, $\delta'(E_0)=\tfrac{2}{\Gamma}$; defining time delay via $\tau=\hbar\,\mathrm{eig}(\mathsf Q)=2\hbar\,\delta'(E)$ gives $\boxed{\tau_{\max}(E_0)=\tfrac{4\hbar}{\Gamma}}$. Resonance lifetime is $\tau_{\text{life}}=\hbar/\Gamma$; the two concepts differ and should not be conflated.

**Dual Convention Comparison for Width Notation** (avoiding literature conversion ambiguity): In scattering theory and resonance physics there exist **two common pole notations**, corresponding to different $\tau_{\max}$ formulas:

| Pole Notation | Phase Derivative $\delta'(E_0)$ | Peak Delay $\tau_{\max}(E_0)$ | Lifetime $\tau_{\text{life}}$ | Remark |
|:--------:|:------------------------:|:---------------------------:|:-------------------------:|:-----|
| $E_0-i\Gamma/2$ | $2/\Gamma$ | $4\hbar/\Gamma$ | $\hbar/\Gamma$ | Uniformly adopted in this paper |
| $E_0-i\Gamma$ | $1/\Gamma$ | $2\hbar/\Gamma$ | $\hbar/\Gamma$ | Adopted in some electromagnetic/quantum literature |

The difference stems from the **normalization convention** of the imaginary part of $S$-matrix poles: with width counted as $E_0-i\Gamma/2$, $\delta'(E_0)=2/\Gamma$; with width counted as $E_0-i\Gamma$, $\delta'(E_0)=1/\Gamma$; from $\tau=2\hbar\delta'$ we obtain the third column above. **This paper uniformly adopts** pole $E_0-i\Gamma/2$ notation, consistent with most quantum scattering and electromagnetic scattering literature (e.g., Phys. Rev. E 103, L050203, 2021 uses $E_0-i\Gamma$ notation yielding $\tau_{\max}=2\hbar/\Gamma$; converting to this paper's notation, $\Gamma_{\text{this paper}}=\Gamma_{\text{that paper}}/2$, peak $4\hbar/\Gamma_{\text{this paper}}=2\hbar/\Gamma_{\text{that paper}}$ consistent).

**Negative Group Delay and Complex Time Delay**: In non-Hermitian/sub-unitary scattering systems, $\operatorname{tr}\mathsf Q$ can change sign and take complex values, corresponding to observable pulse shaping and superluminal/subluminal effects. For sub-unitary scattering, take $\mathsf Q(E)=-i\,S^{-1}(E)\,S'(E)$ (generally non-self-adjoint); in this case $\operatorname{tr}\mathsf Q$ may be complex; its **real/imaginary parts** respectively characterize dwell and dissipation-related quantities (specific choice depends on the **maximal dissipative extension/self-adjoint extension** used, see framework in §0.2). Complex time delay in non-Hermitian/lossy systems has been systematically studied in microwave/optics platforms, experiments, and theory; recent experimental and numerical studies in electromagnetic metamaterials, photonic crystals, and open quantum systems (including negative group delay and complex Wigner time delay statistics in subwavelength arrays) confirm this phenomenon and corroborate with spectral shift density $\rho_{\mathrm{rel}}$ sign changes (e.g., Phys. Rev. E 103, L050203, 2021; Patel et al., arXiv:2005.03211, 2020/2021).

Can be precisely expressed in the framework of "**maximal dissipative extension/coupled scattering**" via spectral shift and generalized Weyl functions. For the above dissipative/coupled cases, see **Behrndt–Malamud–Neidhardt** for systematic formulation of BK variants and trace formulas (see reference [12]), which anchor the relationships and variant formulas among "spectral shift—Weyl function—scattering matrix" to a unified theory.

---

## 7. Verification Checklist (Experimental/Numerical)

1. **Phase—Delay Consistency**: Compute $\operatorname{Arg}\det S(E)$ and $\mathsf Q(E)$, verify $\operatorname{tr}\mathsf Q(E)=\tfrac{d}{dE}\operatorname{Arg}\det S(E)$ and $\varphi'(E)$ for single-channel. Unit verification: confirm $\mathsf Q$ has dimension energy$^{-1}$, $\tau=\hbar\,\mathrm{eig}(\mathsf Q)$ has time dimension. **Electromagnetic Scattering Example**: For electromagnetic scatterers (e.g., dielectric sphere, resonant cavity, subwavelength array), adopt Patel et al. (arXiv:2005.03211, 2020) WS group delay matrix definition $\mathsf Q=-i S^\dagger S'$ and compare with $\det S$ derivative; for monopole/multipole scattering $S$ matrix with frequency $\omega$ or energy $E=\hbar\omega$ as independent variable, verify $\operatorname{tr}\mathsf Q$ consistency with phase derivative; numerical/experimental platforms see Phys. Rev. E 103, L050203 (2021) and other sub-unitary scattering reports.
2. **Scaled Sampling**: Reparametrize energy with $T(E)=\mu_\varphi((E_0,E])$ (when no atomic points, equals $\int_{E_0}^E(2\pi)^{-1}\operatorname{tr}\mathsf Q$), perform Landau threshold test and interpolation experiment on the $T$ axis, then map back to $E$ axis (see Theorem 3.4 for phase-ified expression of $T'(E)$). **Minimal Working Example**: For single-channel, single-peak $\operatorname{tr}\mathsf Q(E)$ case (e.g., Breit–Wigner resonance), plot $(E,T(E))$ curve and verify monotonicity in intervals where $T'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)>0$.
3. **Pointer Basis Minimality**: Compare any orthonormal basis with the eigenbasis of $K_{w,h}$ for Ky Fan partial sums.
4. **Window/Kernel Optimality and WR**: Under band-limited and normalization constraints, use KKT conditions to find optimal window; verify consistency with Wexler–Raz duality.
5. **Tri-decomposition Error Closure**: Report three terms "aliasing + Bernoulli layer + truncation"; under band-limited + Nyquist, aliasing vanishes; EM remainder gives explicit bound.
6. **Information Budget**: Along "preparation $\to$ channel $\to$ readout" chain, record monotone decrease of $D$ and $I_{\mathrm{acc}}\le\chi\le C$.

---

## References (Selected)

1. Patel, U. R., et al., *Wigner–Smith Time-Delay Matrix for Electromagnetics*, arXiv:2005.03211, 2020.
2. Pushnitski, A., *An Integer-Valued Version of the Birman-Kreĭn Formula*, arXiv:1006.0639, 2010; Guillarmou, C., *Generalized Krein Formula…*, 2009.
3. Remling, C., Hur, I., *Density of Schrödinger Weyl-Titchmarsh m functions on Herglotz functions*, arXiv:1501.01268; de Branges, L., *Hilbert Spaces of Entire Functions* (Purdue).
4. Landau, H. J., *Necessary Density Conditions for Sampling and Interpolation of Certain Entire Functions*, Acta Math. **117**, 37–52 (1967), https://doi.org/10.1007/BF02395039.
5. Daubechies, I., Landau, H. J., Landau, Z., *Gabor Time-Frequency Lattices and the Wexler–Raz Identity*, J. Fourier Anal. Appl. **1**(4), 437–478 (1995).
6. Caragea, A., et al., *A Balian–Low Type Theorem for Gabor Riesz Sequences…*, 2023.
7. Naimark's Dilation (review) & Busch, P., *A Simple Proof of Gleason's Theorem*, PRL, 2003.
8. Manzano, D., *A Short Introduction to the Lindblad Master Equation*, 2019.
9. Müller-Hermes, A., Reeb, D., *Monotonicity of the Quantum Relative Entropy under Positive Maps*, arXiv:1512.06117, 2015.
10. Watrous, J., *The Theory of Quantum Information*, Cambridge University Press, 2018 (HSW chapter).
11. Eberl, M., *The Euler–MacLaurin Formula*, Archive of Formal Proofs (AFP-Isabelle), https://devel.isa-afp.org/entries/Euler_MacLaurin.html.
12. Behrndt, J., Malamud, M., Neidhardt, H., *Trace Formulae for Dissipative and Coupled Scattering Systems*, arXiv:0712.3120 (and related sequels).

---

## Appendix A: Self-consistent Derivation of Core Equations

**Lemma A.1 ($\operatorname{tr}\mathsf Q=\tfrac{d}{dE}\operatorname{Arg}\det S$).** By Jacobi's formula $\tfrac{d}{dE}\log\det S=\operatorname{tr}(S^{-1}S')$ and unitarity $S^{-1}=S^\dagger$, we have $\tfrac{d}{dE}\log\det S=\operatorname{tr}(S^\dagger S')$; combining with $\mathsf Q=-i\,S^\dagger S'$ gives

$$
\operatorname{tr}\mathsf Q=-i\,\operatorname{tr}(S^\dagger S')=\Im\,\operatorname{tr}(S^\dagger S')=\frac{d}{dE}\operatorname{Arg}\det S\ \ (\text{a.e.}).
$$

∎

**Lemma A.2 (BK Chain).** $\det S=e^{-2\pi i\,\xi}\Rightarrow \tfrac{d}{dE}\operatorname{Arg}\det S=-2\pi\,\xi'$; letting $\rho_{\mathrm{rel}}:=-\xi'$ gives $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$. ∎

**Corollary A.3 (Single-channel Reduction to Phase Derivative).** If $S=e^{2i\varphi}$, then $\operatorname{tr}\mathsf Q=2\varphi'$; combining with A.2 gives $\varphi'/\pi=\rho_{\mathrm{rel}}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$. ∎

---

## Appendix B: Ky Fan Variation and Pointer Minimum

Let $K$ be self-adjoint, $\lambda^{\uparrow}_1\le\lambda^{\uparrow}_2\le\cdots$ the **ascending** eigenvalue sequence (counting multiplicity). Ky Fan principle gives

$$
\sum_{k=1}^r\lambda_k=\max_{U^\dagger U=I_r}\operatorname{tr}(U^\dagger K\,U),\quad
\sum_{k=1}^{r}\lambda^{\uparrow}_k=\min_{U^\dagger U=I_r}\operatorname{tr}(U^\dagger K\,U).
$$

(Here the first formula uses descending notation: $\lambda_1\ge\cdots\ge\lambda_r\ge\cdots$; the second formula uses ascending notation $\lambda^{\uparrow}$.)

**Finite-dimensional special case**: If $K$ is an $n\times n$ matrix with spectrum recorded in descending order $\lambda_1\ge\cdots\ge\lambda_n$, then $\sum_{k=1}^{r}\lambda^{\uparrow}_k=\sum_{k=n-r+1}^{n}\lambda_k$.

Maximum trace is attained on the subspace spanned by the first $r$ eigenvectors; minimum trace is attained on the subspace spanned by the smallest $r$ eigenvectors. ∎

---

## Appendix C: Finite-Order Bound for EM Remainder

Under the assumptions of 0.7 ($F\in C^{2m}$ and $F^{(2m)}$ bounded/finite variation), the EM formula gives Bernoulli layers up to order $2m$ and an **explicit** integral remainder; AFP–Isabelle provides formalized verification for remainder construction and convergence, thus enabling choice of finite order $m$ in numerical implementation and yielding executable bounds. EM remainder adopts the formalized bound from Archive of Formal Proofs (AFP-Isabelle) entry **The Euler–MacLaurin Formula** (Eberl, M., https://www.isa-afp.org/entries/Euler_MacLaurin.html), explicitly specifying in implementation the chosen order $m$ and regularity of the integrand/summand ($C^{2m}$ or finite total variation) to reproduce the bound. ∎

---

## Appendix D: Interfaces with S15–S26 and EBOC System

**D.1 Interface with S15–S23 (Scattering Phase, Herglotz, Weyl–Mellin, Framework).**
- The Herglotz representation and canonical systems in S15–S17 directly provide the $\mathcal S$ functor and $d\mu_\varphi$ in UMS.
- The Weyl–Mellin non-stationary framework in S18–S20 provides concrete implementation for multi-window covariance in UMS.
- The phase—scale covariance and Euler–Maclaurin finite-order error theory in S21–S23 directly support A1, A2 and Theorems 4.1–4.3.

**D.2 Interface with S24–S26 (Tight Frames, Non-stationary Frames, Phase Density).**
- The fiber Gram characterization and Wexler–Raz biorthogonality in S24 provide the concrete computational framework for A6 and Theorem 3.3(iii).
- The Calderón sum and tight/dual construction in S25 provide operational schemes for multi-window optimization in UMS (Definition 2.1(iv)).
- The phase density scale $\varphi'(x)=\pi\rho(x)$ and Landau necessary density, Balian–Low impossibility in S26 directly correspond to A5, A6 and Theorem 3.4.

**D.3 Interface with EBOC-Graph.**
- EBOC-Graph's Born = I-projection (G1) is equivalent to UMS's Theorem 3.3(i) in discrete spectrum cases.
- EBOC-Graph's pointer basis = spectral minimum (G2) is consistent with UMS's Theorem 3.3(ii) in graph Laplacian cases.
- EBOC-Graph's window minimax (G3) shares the same optimization structure with UMS's Theorem 3.3(iii) under band-limited constraints.
- EBOC-Graph's non-asymptotic error closure (G4) and UMS's Theorem 4.3 both adopt the Nyquist–Poisson–EM tri-decomposition framework.

**D.4 Interface with CCS (Covariant Multi-channel) and WSIG-QM.**
- CCS's windowed Birman–Kreĭn identity is completely consistent with UMS's core unification formula (Definition 2.2) in multi-channel cases.
- CCS's Wigner–Smith group delay matrix $\mathsf Q(E)$ adopts the same definition and convention as UMS's A5.
- WSIG-QM's seven axioms (A1–A7) are highly aligned with UMS's axiomatic system (§1) in concept and formulation; WSIG-QM can be viewed as a refined expansion of UMS in the specific context of quantum measurement.
- WSIG-QM's unified dictionary (§5) and UMS's categorical definition (§2) jointly support the full-chain unification of "state—measurement—probability—pointer—scattering—delay—frame—error—capacity".

**D.5 Maintaining "Pole = Primary Scale" Finite-Order EM Discipline.**
- UMS adopts **finite-order** EM (A1, Theorem 4.2) in all discrete-continuous interchanges, ensuring no introduction of new singularities.
- Consistent with S15–S26, EBOC-Graph, CCS, WSIG-QM: scattering poles, resonance poles, spectral singularities always serve as "primary scale" markers, with EM remainder providing only bounded perturbation.

---

### One-sentence Summary

$$
\boxed{\ \textbf{UMS}\ \Longleftrightarrow
\big(\,d\mu_\varphi=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\,dE=\rho_{\mathrm{rel}}\,dE=\tfrac{\varphi'}{\pi}\,dE;
K_{w,h}\text{ Nyquist–Poisson–EM finite-order closure};
\text{Born=I-proj,\ DPI,\ HSW};
\text{Landau/WR/BL};
\text{Pointer=Ky Fan minimum}\,\big). }
$$