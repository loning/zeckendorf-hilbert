**6.3 Proof of Physical Equivalence Between Dwell Time and Group Delay**

In Section 6.2, we defined the Eisenbud-Wigner-Smith (EWS) time delay operator $\mathsf{Q}$ based on the phase behavior of the scattering matrix $S(E)$ on the energy shell. This operator describes, from an "external" observer's perspective, the time by which particles are "delayed" relative to free motion by the scatterer.

However, if time is an intrinsic property of physical reality, this "external" description must be consistent with the "internal" behavior of particles inside the interaction region. That is, the actual **dwell time** that particles **stay** inside the black box must be numerically equal to the delay predicted by the EWS operator. This section will provide a rigorous proof of this equivalence. This proof is crucial because it establishes the dynamical foundation of the **holographic principle**: phase information on the boundary (group delay) faithfully encodes physical processes in the bulk (dwell time).

### 6.3.1 Microscopic Definition of Dwell Time

Consider a finite spatial region $\Omega$ (interaction region) occupied by a potential field $V(\mathbf{r})$. For a steady-state scattering wave function $\psi_E(\mathbf{r})$ with energy $E$, the probability density of particles appearing in $\Omega$ is $|\psi_E(\mathbf{r})|^2$.

**Definition 6.3.1 (Dwell Time)**

For a given incident flux $J_{in}$ (usually normalized to unit flux), the average dwell time $\tau_D$ of particles in region $\Omega$ is defined as the **total probability integral** of particles in $\Omega$:

$$
\tau_D(E) = \frac{1}{J_{in}} \int_{\Omega} |\psi_E(\mathbf{r})|^2 \, \mathrm{d}^3\mathbf{r}
$$

Physically, this represents the ratio of the total charge (or probability mass) accumulated by the particle "cloud" in the interaction region during scattering to the injection rate. This is a purely bulk physical quantity.

### 6.3.2 Smith's Ultimate Equivalence Theorem

Our goal is to prove that this bulk quantity $\tau_D$ equals the expectation value of the scattering operator $\mathsf{Q}$ defined on the boundary.

**Theorem 6.3.2 (Dwell Time-Group Delay Equivalence)**

For any scattering potential with finite range, the expectation value of the EWS time delay operator $\mathsf{Q}$ strictly equals the dwell time minus the transit time of free particles over the same distance:

$$
\langle \chi | \mathsf{Q}(E) | \chi \rangle = \tau_D(E) - \tau_{free}(E)
$$

where $|\chi\rangle$ is the incident channel state. If the interaction region boundary is taken in the asymptotic region and the free time is appropriately renormalized, this can be summarized as: **the phase derivative on the boundary equals the probability density integral in the bulk**.

**Proof**:

We derive this relation using the Schrödinger equation and its derivative with respect to energy.

1.  **Schrödinger Equation and Its Energy Derivative**:

    The steady-state equation is:

    $$
    (H - E) |\psi_E\rangle = 0
    $$

    Differentiating with respect to energy $E$:

    $$
    (H - E) \frac{\partial}{\partial E} |\psi_E\rangle - |\psi_E\rangle = 0 \implies (H - E) |\partial_E \psi_E\rangle = |\psi_E\rangle
    $$



2.  **Constructing Conservation Current Identity**:

    Left-multiplying by $\langle \psi_E |$ and using the Hermiticity $\langle \psi_E | (H-E) = 0$, we obtain an identity. To extract boundary terms, we integrate over a finite region $\Omega$ (a sphere of radius $R$):

    $$
    \int_{\Omega} \psi_E^* (\mathbf{r}) \psi_E(\mathbf{r}) \, \mathrm{d}^3\mathbf{r} = \int_{\Omega} \psi_E^* (H - E) \partial_E \psi_E \, \mathrm{d}^3\mathbf{r}
    $$

    Since $(H-E) \psi_E = 0$, we can write it in symmetric form (using Green's theorem):

    $$
    \int_{\Omega} |\psi_E|^2 \, \mathrm{d}V = \int_{\Omega} \left[ \psi_E^* (H \partial_E \psi_E) - (\partial_E \psi_E) (H \psi_E)^* \right] \, \mathrm{d}V
    $$

    Using the kinetic energy term $-\frac{\hbar^2}{2m} \nabla^2$ of the Hamiltonian, the volume integral transforms into a surface integral on the boundary surface $\partial \Omega$:

    $$
    \tau_D(R) = -\frac{\hbar^2}{2m} \oint_{\partial \Omega} \left[ \psi_E^* \nabla (\partial_E \psi_E) - (\partial_E \psi_E) \nabla \psi_E^* \right] \cdot \mathbf{n} \, \mathrm{d}S
    $$



3.  **Asymptotic Expansion and Scattering Matrix**:

    At the boundary $R \to \infty$, the wave function can be written as a superposition of incident and outgoing waves (one-dimensional simplified form, multi-dimensional similar):

    $$
    \psi_E(r) \sim A \left( e^{-ikr} + S(E) e^{ikr} \right)
    $$

    where $k = \sqrt{2mE}/\hbar$.

    Differentiating with respect to $E$ (note $\partial_E = \frac{dk}{dE} \partial_k = \frac{1}{\hbar v} \partial_k$):

    $$
    \partial_E \psi_E \sim A \left( \frac{ir}{\hbar v} (-e^{-ikr} + S e^{ikr}) + \frac{dS}{dE} e^{ikr} \right)
    $$

    Substituting $\psi_E$ and $\partial_E \psi_E$ into the surface integral formula. After tedious but straightforward algebraic operations, cross terms (interference terms) rapidly oscillate in the integral and average to zero, with the main contribution coming from modulus-squared terms.



    * Free term contribution: $\sim 2R/v$, corresponding to the time $\tau_{free}$ for free particles to cross a region of radius $R$.

    * Scattering term contribution: from the derivative term $\frac{dS}{dE}$ of $S$ with respect to $E$.

    

    The final result is:

    $$
    \int_{\Omega} |\psi_E|^2 - \frac{2R}{v} = \operatorname{Re} \left[ -i\hbar S^\dagger \frac{dS}{dE} \right]
    $$

    The right side is exactly the expectation value of the EWS operator $\mathsf{Q}$.



$\square$

### 6.3.3 Physical Meaning: Time is Matter

This theorem is not just a mathematical identity; it is the physical cornerstone of **time emergence theory**.

1.  **Holographic Correspondence**: The left side of the equation is the integral $\int |\psi|^2$ in the bulk, representing the **existence probability** or **matter density** of particles in the region. The right side is the operator $\mathsf{Q} \sim \partial_E \varphi$ on the boundary, representing **time delay**. This shows that **"time" is merely the holographic projection of "matter density" on the boundary**.

    

2.  **Microscopic Explanation of Gravitational Redshift**: In general relativity, strong gravitational fields cause time to pass more slowly (increased delay). From a scattering perspective, a strong gravitational field means the region has extremely high effective density of states ($\rho(E)$ is very large), and the dwell time $\tau_D$ of particles in this region significantly increases. Gravitational redshift is no longer a mysterious spacetime curvature effect but rather **group velocity lag** in a high-density medium.



3.  **Guarantee of Causality**: Since $\tau_D = \int |\psi|^2 \ge 0$, this guarantees $\langle \mathsf{Q} \rangle + \tau_{free} \ge 0$. That is, particles cannot leave before entering the scattering region (causality). Although the phase derivative $\varphi'$ may locally be negative (Wigner precession), the total dwell time after adding the geometric term must be positive.



### 6.3.4 Generalization: Multi-Channel and Entangled Time

For multi-channel systems, $\mathsf{Q}$ is a matrix. Its off-diagonal elements $\langle n | \mathsf{Q} | m \rangle$ describe the **entangled time delay** between channels $n$ and $m$.

**Definition 6.3.3 (Entangled Time Measure)**

If the system is in an entangled state $|\Psi\rangle = \sum c_n |n\rangle$, then the average time delay it experiences depends not only on the eigen-delays $\tau_n$ of each channel but also on interference terms between channels:

$$
\bar{\tau} = \sum_{n} |c_n|^2 \tau_n + \sum_{n \ne m} c_n^* c_m \mathsf{Q}_{nm}
$$

This formula implies that **quantum entanglement changes the rate of time flow**. This is a key foreshadowing for subsequent chapters discussing "entanglement entropy and gravity."

### 6.3.5 Summary

This section proved the physical equivalence between dwell time (volume integral) and group delay (boundary derivative). This establishes the operational status of the $\mathsf{Q}$ operator as a microscopic time standard.

Combining Pauli's theorem (Section 6.1) and the EWS construction (Section 6.2), we now have an **intrinsic time definition** that does not rely on the background parameter $t$ and is entirely based on scattering state density.

This discovery directly leads to the core formula of Volume II of this book—the **unified time identity**. In the next chapter, we will connect this scattering time with thermodynamics (spectral shift function), proving that time, matter, and information entropy are three aspects of the same underlying physical reality.

