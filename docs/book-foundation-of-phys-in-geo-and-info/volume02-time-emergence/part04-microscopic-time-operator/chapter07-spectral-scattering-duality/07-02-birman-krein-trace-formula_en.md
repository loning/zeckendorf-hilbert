**7.2 Birman-Kreĭn Trace Formula: Exponential Mapping Relationship Between Scattering Matrix Determinant and Spectral Shift Function**

In Section 7.1, we introduced the Kreĭn spectral shift function $\xi(E)$ as a thermodynamic quantity measuring the overall rearrangement of energy level density caused by interactions. In Chapter 6, we defined the Wigner-Smith time delay matrix $\mathsf{Q}(E)$ as a time quantity measuring the dynamical dwell time of scattering processes. These two physical quantities—one describing "state counting" and the other describing "time flow"—seem to belong to different domains of statistical mechanics and dynamics.

This section will reveal the astonishing mathematical equivalence between them through the famous **Birman-Kreĭn Trace Formula**. We will prove that the determinant of the scattering matrix $S(E)$ is precisely the exponential mapping of the spectral shift function $\xi(E)$. This relation $\det S(E) = e^{-2\pi i \xi(E)}$ is the ultimate bridge in theoretical physics converting **topological information** (spectral shift) into **geometric phase** (scattering phase shift), establishing the holographic duality that "scattering is thermodynamics."

### 7.2.1 Connection Between Scattering Matrix and Spectral Shift Function

First, let us recall our two core objects:

1.  **Scattering Matrix $S(E)$**: An $N \times N$ unitary matrix defined on the energy shell, describing the evolution from asymptotic state $|\psi_{in}\rangle$ to $|\psi_{out}\rangle$. Its eigenvalues $e^{2i\delta_n(E)}$ contain scattering phase shift information.

2.  **Spectral Shift Function $\xi(E)$**: A real-valued function defined as the integral of the spectral density difference between $H$ and $H_0$, $\xi(E) \sim -\Delta N(E)$.

Intuitively, if we introduce a scattering potential in a large box, the change in boundary conditions causes energy levels to shift. Each small shift $\delta E_n$ of an energy level $E_n$ corresponds to a phase shift $\delta_n \approx -\pi \frac{\delta E_n}{\Delta E}$ (where $\Delta E$ is the level spacing). When the box tends to infinity, these discrete shifts accumulate into a continuous spectral shift.

### 7.2.2 Rigorous Statement of Birman-Kreĭn Theorem

**Theorem 7.2.1 (Birman-Kreĭn Theorem)**

Let $(H, H_0)$ be a pair of self-adjoint operators satisfying the relative trace-class condition, with $\xi(E)$ as their Kreĭn spectral shift function. Let $S(E)$ be the corresponding on-shell scattering matrix at energy $E$. Then for almost all $E \in \sigma_{ac}(H_0)$ (absolutely continuous spectrum), the following identity holds:

$$
\det S(E) = \exp\left[ -2\pi i \xi(E) \right]
$$

Or in logarithmic form (choosing an appropriate single-valued branch):

$$
\frac{1}{2\pi i} \text{Tr} \left[ \ln S(E) \right] = -\xi(E)
$$

**Proof Outline (Based on Invariance Principle)**:

1.  **Wave Operators and Scattering Operator**:

    The scattering operator is defined as $\hat{S} = \Omega_+^\dagger \Omega_-$, where wave operators $\Omega_\pm = \text{s-lim}_{t \to \pm\infty} e^{iHt} e^{-iH_0t}$. $\hat{S}$ commutes with the free Hamiltonian $H_0$, so it can be diagonalized as $S(E)$ in the spectral representation of $H_0$.



2.  **Resolvent Form of Trace Formula**:

    Consider the function $f(x) = (x-z)^{-1}$ (where $\text{Im} z \neq 0$). According to the Kreĭn trace formula (Theorem 7.1.2):

    $$
    \text{Tr}\left[ (H-z)^{-1} - (H_0-z)^{-1} \right] = -\int \frac{\xi(\lambda)}{(\lambda-z)^2} \mathrm{d}\lambda
    $$



3.  **Connection to Scattering Phase**:

    On the other hand, the determinant of the scattering matrix is related to the boundary value of the resolvent. By taking the limit $z \to E + i0^+$ of the above trace formula and using the Plemelj formula, the imaginary part of the resolvent can be related to the scattering amplitude. For trace-class perturbations, we can directly derive:

    $$
    \xi(E) = \frac{1}{\pi} \text{Im} \ln \det (H-E-i0^+) \dots
    $$

    In rigorous scattering theory derivations (such as Yafaev's or Birman's work), we use the fact that the trace of $\ln S(E)$ equals the total phase shift $\sum 2\delta_n(E)$. By comparing the relationship between density of states change $\Delta \rho(E)$ caused by energy level shifts and phase shift $\delta(E)$, $\pi \Delta \rho(E) = \delta'(E)$, integration gives $\pi \xi(E) = -\delta(E)$ (up to an integer constant, usually normalized to 0).

    Therefore:

    $$
    \det S(E) = e^{i \sum 2\delta_n(E)} = e^{-2\pi i \xi(E)}
    $$



$\square$

### 7.2.3 Physical Interpretation: Phase Shift is Spectral Shift

The Birman-Kreĭn formula $\det S = e^{-2\pi i \xi}$ is one of the most important "dictionary entries" in this book. It translates microscopic dynamical observations (left side) into macroscopic thermodynamic states (right side).

1.  **Geometric Meaning of Total Phase**:

    Define the total scattering phase $\Phi(E) = \arg \det S(E)$. Then the formula tells us:

    $$
    \Phi(E) = -2\pi \xi(E) \quad (\text{mod } 2\pi)
    $$

    This means that **the total scattering phase $\Phi(E)$ is essentially the angular representation of the spectral shift function $\xi(E)$**. The phase shifts we measure in the laboratory are actually measuring the degree of distortion of the vacuum energy spectrum.



2.  **Re-derivation of Time Delay**:

    Recall the Wigner-Smith time delay $\tau = \text{Tr}[\mathsf{Q}]$ defined in Chapter 6.

    Using $\mathsf{Q} = -i\hbar S^\dagger S'$ and $\det S = e^{-2\pi i \xi}$:

    $$
    \text{Tr}[\mathsf{Q}] = -i\hbar \frac{d}{dE} \ln \det S = -i\hbar \frac{d}{dE} (-2\pi i \xi) = -2\pi\hbar \xi'(E)
    $$

    This again confirms the conclusion of Section 6.4, $\text{Tr}[\mathsf{Q}] = 2\pi\hbar \Delta \rho(E)$ (note $\Delta \rho = -\xi'$). The Birman-Kreĭn formula provides a non-perturbative, global form of this relationship.



### 7.2.4 Exponential Mapping: Dynamics is the "Imaginary Time" Evolution of Thermodynamics

The formula $\det S = e^{-2\pi i \xi}$ has profound Lie group structure implications.

* $\xi(E)$ is a real number (or trace of a Hermitian operator), representing the **generator**, belonging to the Lie algebra $\mathfrak{u}(1)$ (for Abelian phase) or the trace part of $\mathfrak{u}(N)$.

* $S(E)$ is a unitary matrix, belonging to the Lie group $U(N)$.



This indicates that **dynamics (scattering $S$) is the exponential mapping of thermodynamics (spectral shift $\xi$)**.

If in the discrete ontology of QCA, we view $\xi$ as a more fundamental "information counter" (offset of integer bits), then $S$ is merely the projection of this counter onto the complex plane.

This viewpoint is crucial for understanding quantum gravity: gravitational field equations (dynamics) may be geometric phase effects caused by changes in underlying entanglement entropy (spectral shift).



### 7.2.5 Topological Robustness: Integer Spectral Flow

A remarkable feature of $\xi(E)$ is that it exhibits integer jumps at bound state energies.

For $E < 0$ (bound state region), $S(E)$ is not defined (or analytically continued as real), but $\xi(E)$ is still well-defined and takes integer values (the negative of the number of bound states).

When energy crosses the threshold $E=0$ into the continuous spectrum, $\xi(E)$ begins to change continuously, but its overall topological properties (such as $\xi(0) - \xi(\infty)$ stated in Levinson's theorem) are still controlled by the number of bound states.



This will be discussed in detail in Section 7.4 on Levinson's theorem, but the Birman-Kreĭn formula already foreshadows this: **the continuous scattering phase $\Phi(E)$ contains topological information about discrete bound states**. This is precisely the manifestation of "discrete-continuous" unification at the thermodynamic level.



**Summary**

The Birman-Kreĭn formula $\det S = e^{-2\pi i \xi}$ is the hub connecting scattering time (dynamics) and density of states (thermodynamics). It proves:

1.  Microscopic time delay originates from macroscopic energy level rearrangement.

2.  Scattering phase is the holographic projection of the spectral shift function.

This formula will find concrete condensed matter applications in the next section "Friedel Sum Rule," explaining how impurities screen charge.

