# Part V: Unified Time Identity and Relativity

## Chapter 8: Phase-Delay-Density Trinity

In the first half of Volume II (Part IV), we established scattering time delay theory from the perspective of microscopic dynamics (Chapter 6) and spectral shift function theory from the perspective of statistical thermodynamics (Chapter 7). These two seemingly independent physical pictures—one focusing on particle dwell time in the scattering region, the other on energy level rearrangement caused by interactions—first met in the Birman-Kreĭn trace formula.

This chapter elevates this meeting into a fundamental principle in physics: the **Unified Time Identity**. We will prove that the rate of time flow (phase derivative), the form of matter's existence (density of states), and information processing capacity (group delay) are mathematically completely equivalent. This "trinity" relationship not only unifies microscopic physics but will also become the axiomatic starting point for deriving general relativistic gravitational effects in subsequent chapters.

### 8.1 Derivation of Unified Time Identity: $\kappa(E) = \varphi'/\pi = \rho_{\text{rel}} = \text{Tr}\mathsf{Q}/2\pi$

Physics has long been accustomed to treating time $t$ as a background parameter external to matter, and mass or energy as entities filling spacetime. However, the discrete ontology of QCA suggests a deeper duality between these two. This section will rigorously derive and establish the **Unified Time Identity**, proving that the measurement of "time" and the density of "matter" are different manifestations of the same physical quantity at the spectral geometric level.

#### 8.1.1 Review of Three Physical Quantities

First, let us clearly define the three core physical quantities participating in the unification, which respectively represent three different aspects of physical reality:

1.  **Geometric Side: Scattering Half-Phase Derivative $\varphi'(E)$**

    In scattering theory, the determinant of the scattering matrix $S(E)$ is a unimodular complex number. Define the total scattering phase $\Phi(E)$ as:

    $$
    \det S(E) = e^{i\Phi(E)}
    $$

    Define the **half-phase** $\varphi(E) = \frac{1}{2}\Phi(E)$. Its derivative with respect to energy $\varphi'(E) = \frac{d\varphi}{dE}$ describes the geometric rotation speed of the wave function in energy space.



2.  **Thermodynamic Side: Relative Density of States $\rho_{\text{rel}}(E)$**

    Density of states (DOS) is the core of statistical mechanics. After introducing interaction $V$, the change in local density of states is defined as:

    $$
    \rho_{\text{rel}}(E) \equiv \rho(E) - \rho_0(E) = \frac{d}{dE} \text{Tr} \left[ \Theta(E-H_0) - \Theta(E-H) \right]
    $$

    It quantifies the number of new microscopic degrees of freedom (or information capacity) near the energy shell $E$.



3.  **Dynamical Side: Wigner-Smith Time Delay Trace $\text{Tr}\mathsf{Q}(E)$**

    The EWS operator $\mathsf{Q} = -i\hbar S^\dagger \frac{dS}{dE}$ describes the dwell time of wave packets in the scattering region. Its trace $\tau_{tot} = \text{Tr}\mathsf{Q}$ represents the total time delay of all scattering channels, i.e., the "time impedance" of the system as a whole to external probes.

#### 8.1.2 Rigorous Derivation of the Identity

We will use the Birman-Kreĭn theory established in Chapter 7 to complete this proof.

**Theorem 8.1.1 (Unified Time Identity)**

For scattering systems satisfying the relative trace-class condition, within the absolutely continuous spectrum region, the following three physical quantities are strictly equal (in natural units $\hbar=1$):

$$
\kappa(E) \equiv \frac{1}{\pi} \frac{d\varphi(E)}{dE} = \rho_{\text{rel}}(E) = \frac{1}{2\pi} \text{Tr}\mathsf{Q}(E)
$$

We define $\kappa(E)$ as the **Unified Time Scale Density**.

**Proof**:

**Step 1: Connecting $\text{Tr}\mathsf{Q}$ with $\varphi'$**

According to the definition of the Wigner-Smith operator and the properties of its trace (Section 6.4):

$$
\text{Tr}\mathsf{Q}(E) = \text{Tr}\left[ -i S^\dagger(E) \frac{dS(E)}{dE} \right]
$$

Using Jacobi's formula $\text{Tr}(A^{-1} dA) = d(\ln \det A)$ and $S^\dagger = S^{-1}$:

$$
\text{Tr}\mathsf{Q}(E) = -i \frac{d}{dE} \ln (\det S(E))
$$

Substituting the total phase definition $\det S = e^{i\Phi(E)} = e^{2i\varphi(E)}$:

$$
\text{Tr}\mathsf{Q}(E) = -i \frac{d}{dE} (2i\varphi(E)) = 2 \frac{d\varphi}{dE} = 2\varphi'(E)
$$

Therefore:

$$
\frac{1}{2\pi} \text{Tr}\mathsf{Q}(E) = \frac{1}{\pi} \varphi'(E)
$$



**Step 2: Connecting $\varphi'$ with $\rho_{\text{rel}}$**

Using the Birman-Kreĭn trace formula (Section 7.2):

$$
\det S(E) = e^{-2\pi i \xi(E)}
$$

This means the relationship between total phase $\Phi(E)$ and Kreĭn spectral shift function $\xi(E)$ is (taking continuous branch):

$$
\Phi(E) = -2\pi \xi(E) \implies 2\varphi(E) = -2\pi \xi(E) \implies \varphi(E) = -\pi \xi(E)
$$

Differentiating with respect to energy:

$$
\varphi'(E) = -\pi \xi'(E)
$$

Recalling the relationship between spectral shift function and density of states (Section 7.1):

$$
\xi(E) = -(N(E) - N_0(E)) \implies \xi'(E) = -(\rho(E) - \rho_0(E)) = -\rho_{\text{rel}}(E)
$$

Substituting this into the above:

$$
\varphi'(E) = -\pi (-\rho_{\text{rel}}(E)) = \pi \rho_{\text{rel}}(E)
$$

That is:

$$
\frac{1}{\pi} \varphi'(E) = \rho_{\text{rel}}(E)
$$



**Step 3: Synthesis**

Combining the results of Step 1 and Step 2, we obtain the trinity identity.

$\square$

#### 8.1.3 Physical Interpretation: Ontological Status of $\kappa(E)$

The unified time identity reveals that $\kappa(E)$ is a more fundamental physical quantity than time, energy, or entropy. It constitutes the **Master Scale** of the QCA universe.

1.  **Time is Statistics** ($\text{Time} \sim \text{DOS}$):

    The formula $\frac{1}{2\pi} \tau_{tot} = \rho_{\text{rel}}$ tells us that **the essence of time flow is the system's traversal of microscopic states**. If there are no quantum states in a region ($\rho=0$, such as a band gap), wave packets will instantly pass through (tunneling), experiencing no time delay (or extremely short group delay). Conversely, if the density of states is extremely high (such as inside a black hole), wave packets will be "stuck" by countless states, causing extreme time dilation.



2.  **Geometry is Phase** ($\text{Geometry} \sim \text{Phase}$):

    The formula $\kappa = \varphi'/\pi$ shows that this statistical property is completely encoded in the geometric phase on the boundary. We don't need to go deep into the system to count states; we only need to measure the "winding rate" of phase on the boundary.



3.  **Planck Information Density**:

    The dimension of $\kappa(E)$ is $[\text{Energy}]^{-1} = [\text{Time}]$ (with $\hbar=1$). It actually measures **information capacity per unit energy interval**. At the Planck scale, this corresponds to the number of bits per Planck energy.

#### 8.1.4 Case Verification: One-Dimensional Potential Box

To concretize this abstract identity, we examine a one-dimensional potential box (infinite square well) of length $L$.

* **Thermodynamic Side (Density of States)**:

    Eigenenergy $E_n = \frac{n^2 \pi^2}{2m L^2}$. Momentum $k_n = \frac{n\pi}{L}$.

    Density of states $\rho(k) = \frac{dn}{dk} = \frac{L}{\pi}$.

    Energy density of states $\rho(E) = \rho(k) \frac{dk}{dE} = \frac{L}{\pi} \frac{1}{v} = \frac{L}{\pi v}$, where $v$ is the group velocity.



* **Dynamical Side (Time Delay)**:

    The time for a classical particle to cross the box back and forth is $T = \frac{2L}{v}$.

    In the scattering picture, the wave function reflects at boundaries, experiencing phase shifts. Since this is a bound system, we can consider a small scatterer $L$ in a large box $L_{big}$.

    Or directly cite the dwell time concept: $\tau_D = \frac{1}{J} \int |\psi|^2 dx = \frac{1}{v/L_{norm}} \cdot 1 = \frac{L_{norm}}{v}$.

    For scattering state $S(k) = e^{-2ikL}$ (transmission coefficient phase, corresponding to free propagation), phase shift $\delta(k) = -kL$.

    $\varphi' = \frac{d\delta}{dE} = \frac{d(-kL)}{dE} = -L \frac{dk}{dE} = -\frac{L}{v}$.

    Here a sign difference appears because free propagation is usually subtracted as background. If we consider the **extra** delay caused by potential $V$ (e.g., resonance), $\Delta \rho$ and $\tau_{delay}$ will both be positive.



    Consider a resonance scattering (Breit-Wigner resonance):

    $$S(E) = \frac{E - E_0 - i\Gamma/2}{E - E_0 + i\Gamma/2}$$

    Phase derivative (delay): $\tau(E) = \frac{\Gamma}{(E-E_0)^2 + \Gamma^2/4}$.

    Density of states (Lorentzian spectrum): $\Delta \rho(E) = \frac{1}{2\pi} \frac{\Gamma}{(E-E_0)^2 + \Gamma^2/4}$.

    Clearly satisfies $\tau(E) = 2\pi \Delta \rho(E)$.

#### 8.1.5 Conclusion

The unified time identity $\kappa(E)$ is the key link connecting Volume I (discrete ontology) with Volume III (entropic origin of gravity).

* Upward, it explains why gravitational fields (metric $g_{\mu\nu}$) affect time—because gravitational fields change the vacuum density of states $\rho(E)$.

* Downward, it explains the microscopic origin of time—time is not a flowing river but the process of counting quantum states in Hilbert space.

In the next section, we will explore the deep corollary **"Time is Matter"** based on $\kappa(E)$ and explain why in general relativity, the energy-momentum tensor (matter) directly curves spacetime geometry (time).

