**7.4 Levinson's Theorem: Relationship Between Scattering Phase Topological Number and Bound State Number**

In Section 7.3, we used Friedel's sum rule to establish a quantitative connection between scattering phase and local charge (or density of states accumulation). Friedel's rule mainly focuses on physical effects near the energy shell. However, if we examine the global behavior of scattering phase across the entire continuous spectrum ($E \in [0, \infty)$), we will discover a more profound topological constraint.

This section will derive and prove **Levinson's Theorem**. This theorem reveals that the low-energy limit ($E \to 0$) of the scattering matrix not only contains information about long-wavelength scattering but also "remembers" the exact number of **discrete bound states** that the system possesses in the negative energy region ($E < 0$). This relationship $\delta(0) - \delta(\infty) = \pi N_b$ is one of the earliest prototypes of **index theorems** in quantum mechanics. It not only establishes the conservation relationship between discrete and continuous spectra but also provides topological guarantee for information integrity in the QCA universe.

### 7.4.1 Global Topology of Scattering Phase

Consider a single-channel scattering problem under a short-range potential $V(r)$. According to the Birman-Kreĭn formula from Section 7.2, the scattering matrix determinant and spectral shift function satisfy:

$$
\det S(E) = e^{-2\pi i \xi(E)}
$$

Define the total scattering phase $\Phi(E)$ as the continuous argument of $\det S(E)$ (i.e., $\Phi(E) = \arg \det S(E)$, choosing a branch such that $\Phi(\infty)=0$). For the single-channel case, $S(E) = e^{2i\delta(E)}$, then $\Phi(E) = 2\delta(E)$.

As energy $E$ scans from $+\infty$ (very high energy, particles pass through the potential like free particles) to $0$ (very low energy, wavelength tends to infinity), the scattering phase $\Phi(E)$ changes. Levinson's theorem states that this total phase change is not arbitrary but quantized to integer multiples of $\pi$ (or $2\pi$).

**Theorem 7.4.1 (Levinson's Theorem)**

For spherically symmetric potentials satisfying certain decay conditions, the scattering phase shifts $\delta_l(E)$ for each partial wave (angular momentum $l$) satisfy the following global relation:

$$
\delta_l(0) - \delta_l(\infty) = \pi (N_l + \frac{1}{2} \nu_l)
$$

where:

1.  $N_l$ is the number of **bound states** in this partial wave channel.

2.  $\delta_l(\infty)$ is usually normalized to $0$.

3.  $\nu_l$ is a correction term related to zero-energy resonance. Usually $\nu_l=0$; if there happens to be a "half-bound state" at $E=0$, then $\nu_l=1$ (for s-wave).

In the general case without zero-energy resonance, the theorem simplifies to: **zero-energy phase shift equals the number of bound states times $\pi$**.

### 7.4.2 Rigorous Proof Based on Spectral Shift Function

Using the spectral shift function theory we established in Sections 7.1 and 7.2, the proof of Levinson's theorem becomes exceptionally transparent and profound. It is no longer a technical result about asymptotic behavior of Bessel functions but a direct corollary of **spectral flow conservation**.

**Proof Steps**:

1.  **Domain Extension of Spectral Shift Function**:

    The Kreĭn spectral shift function $\xi(E)$ is defined on the entire real axis $E \in (-\infty, \infty)$.

    * In the continuous spectrum region $E > 0$, $\xi(E) = -\frac{1}{\pi} \delta(E)$ (according to Birman-Kreĭn formula $\det S = e^{2i\delta} = e^{-2\pi i \xi}$, taking branch $\xi = -\delta/\pi$).

    * In the bound state region $E < 0$, since $H$ only has discrete eigenvalues while $H_0$ has no spectrum, the spectral shift function $\xi(E)$ is a step function. According to the energy level counting definition $\xi(E) = - (N(E) - N_0(E))$ from Section 7.1.3, for $E < 0$, $\xi(E)$ equals the number of bound states $N_b(E)$ with energy less than $E$.



2.  **High-Energy Limit (UV Behavior)**:

    For relative trace-class perturbations (i.e., potential $V$ is sufficiently weak or has high-energy cutoff), when $E \to +\infty$, the system tends to free, $\xi(\infty) \to 0$. This corresponds to $\delta(\infty) = 0$.



3.  **Low-Energy Limit (IR Behavior)**:

    Examine continuity at $E \to 0$. If $H$ does not have an eigenvalue exactly at $E=0$ (no zero-energy resonance), then the spectral shift function $\xi(E)$ is continuous at $E=0$.

    * From the left $E \to 0^-$: $\xi(0^-)$ equals the total number of all negative-energy bound states $N_b$.

    * From the right $E \to 0^+$: $\xi(0^+) = -\frac{1}{\pi} \delta(0)$.



4.  **Continuity Connection**:

    By continuity of $\xi(E)$ (under the assumption of no singularity at $E=0$), $\xi(0^-) = \xi(0^+)$.

    $$
    N_b = -\frac{1}{\pi} \delta(0) \implies \delta(0) = -\pi N_b
    $$

    (Note: Sign differences depend on the definition direction of $\delta$. If attractive potential produces positive phase shift, then $\delta(0) = \pi N_b$. Standard Levinson's theorem is usually written as $\delta(0) = \pi N_b$, meaning that as energy decreases from $\infty$ to $0$, phase shift increases by $\pi N_b$. This is consistent with the sign convention of $\xi$: positive $\xi$ represents energy levels shifting down, producing bound states.)



$\square$

### 7.4.3 Physical Picture: Conservation of States and "Squeezing" Effect

The physical picture of Levinson's theorem is **conservation of Hilbert space dimension** (or more precisely, rearrangement of completeness relations).

Imagine introducing an attractive potential $V$ into a system with a large box (discretizing continuous spectrum) as background:

1.  **Energy Level Shift Down**: The attractive potential pulls all scattering state energy levels downward.

2.  **Crossing Threshold**: If the potential is strong enough, states originally at the bottom of the continuous spectrum ($E \approx 0^+$) will be pulled into the negative energy region ($E < 0$), becoming **bound states**.

3.  **Phase Winding**: Each time a state "drops" from the continuous spectrum into the bound state spectrum, the wave function at the bottom of the continuous spectrum loses one node (or gains one node, depending on boundary conditions), causing the scattering phase shift $\delta(0)$ to change by $\pi$.

4.  **Total Balance**:

    $$
    N_{\text{bound}} + N_{\text{scattering}} = N_{\text{free}}
    $$

    Levinson's theorem tells us that the "lost" spectral density in the continuous spectrum (manifested as non-zero initial phase shift $\delta(0)$) precisely equals the number of bound states produced. This shows that **information does not disappear, it just changes storage form** (from scattering states to bound states).

### 7.4.4 Topological Invariants and Index Theorem

Mathematically, Levinson's theorem is a special case of the **Atiyah-Singer Index Theorem** on non-compact manifolds (scattering systems).

* **Topological Object**: The scattering matrix $S(E)$ is a map from the energy ray $[0, \infty]$ to the unitary group $U(1)$ (or $U(N)$). Since $S(\infty) = I$, this can be viewed as a map from circle $S^1$ to $U(N)$.

* **Winding Number**: The homotopy class of this map is characterized by the integer winding number $\frac{1}{2\pi i} \oint \text{Tr}(S^{-1} dS)$.

* **Analytic Object**: The number of bound states of Hamiltonian $H$ (dimension of negative spectrum projection).

Levinson's theorem establishes this connection:

$$
\text{Index}(H) \equiv \dim \ker H - \dim \text{coker} H \sim \frac{1}{2\pi} \Delta \arg \det S
$$

In the QCA universe, this means that **the existence of particles (bound states) is a topological twist of spacetime boundary (scattering states)**. We don't need to "enter" the particle interior to count what it's made of; we only need to measure the total winding number of scattering phase at infinity to know exactly how many bound states are inside. This is precisely the topological manifestation of the holographic principle.

### 7.4.5 Levinson Correspondence in Discrete QCA

In the discrete QCA ontology established in this book, Levinson's theorem has a more intuitive combinatorial form.

For finite lattice systems, the total number of degrees of freedom $D$ is fixed (finite information axiom).

$$
\text{Tr}(\mathbb{I}) = D
$$

After introducing interaction $U$, eigenvalues $e^{-i\omega_n}$ move on the unit circle.

* **Scattering States**: Eigenvalues densely distributed in continuous spectrum bands (e.g., $\omega \in [-\pi/2, \pi/2]$).

* **Bound States**: States "squeezed out" of continuous spectrum bands, becoming isolated eigenvalues (Gap States).

The QCA version of Levinson's theorem is a **number conservation law**:

$$
\Delta N_{\text{continuum}} = - N_{\text{bound}}
$$

The total integral change in continuous spectrum density of states (given by total phase shift $\Phi$) strictly cancels the number of bound states produced. This guarantees that during universe evolution, despite the myriad changes in matter forms (particle creation, annihilation, binding), **the underlying total quantum information amount (Hilbert space dimension) remains strictly conserved**.

**Summary**

Levinson's theorem completes Chapter 7's discussion of "spectrum-scattering duality."

1.  **Kreĭn Spectral Shift Function** (7.1) defines energy level rearrangement.

2.  **Birman-Kreĭn Formula** (7.2) maps spectral shift to scattering phase shift.

3.  **Friedel Rule** (7.3) connects phase shift to local charge.

4.  **Levinson's Theorem** (7.4) connects the global topology of phase shift to bound state number.

This chapter proves that: **thermodynamics (density of states), dynamics (scattering time), and topology (bound state index) are trinity in the discrete quantum universe**. This establishes a solid mathematical foundation for the next part "Unified Time Identity and Relativity," where we will see that it is precisely this microscopic rearrangement of density of states that emerges macroscopically as gravitational effects in curved spacetime.

