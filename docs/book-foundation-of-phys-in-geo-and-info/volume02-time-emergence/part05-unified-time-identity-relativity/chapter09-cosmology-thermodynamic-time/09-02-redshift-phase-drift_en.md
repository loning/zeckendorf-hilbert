**9.2 Redshift is Phase Drift: Adiabatic Scattering Interpretation of Cosmological Redshift**

In Section 9.1, we described cosmic expansion as an information dissipation process caused by non-Hermitian Hamiltonians. This picture explains decay of wave function amplitude (dilution). However, the most prominent feature in cosmological observations is not the decrease in photon number density but the **redshift** of photon frequency.

In standard general relativity, redshift is geometrically explained as wavelength stretching with spatial scale ($\lambda \propto a(t)$). But in the discrete ontology of QCA, there is no elastic background space, only constantly evolving quantum states. This section will use **adiabatic scattering theory** to prove that redshift is essentially the cumulative drift of **dynamic phase** relative to **geometric phase** when photons propagate in a slowly changing cosmic background. This perspective unifies Hubble's law $z \approx H d/c$ as an evolution equation of scattering phase shift.

### 9.2.1 Universe as Time-Dependent Scattering Medium

Consider a photon (wave packet) propagating in an expanding universe. For photons, the universe is not empty but a medium filled with quantum bits (lattice sites). As the universe evolves ($U^t$ updates), effective parameters of this medium (such as lattice density or interaction strength) slowly change.

**Definition 9.2.1 (Adiabatic Expansion Condition)**

Let the characteristic time scale of cosmic evolution be Hubble time $t_H = 1/H$, and the oscillation period of photons be $T_\gamma = 1/\omega$.

Since $H \approx 10^{-18} \text{s}^{-1}$ while visible light frequency $\omega \approx 10^{15} \text{Hz}$, the adiabatic parameter $\epsilon$ is extremely small:

$$
\epsilon = \frac{T_\gamma}{t_H} = \frac{H}{\omega} \ll 1
$$

This means photon propagation is an **adiabatic process**. Photons always remain on eigenstates of instantaneous Hamiltonian $H(t)$, without level transitions (i.e., no spontaneous particle pair production, unless in extreme high-curvature periods like inflation).

### 9.2.2 Instantaneous Frequency and Phase Drift Equation

In the scattering picture, we treat photons as standing waves (or equivalent Bloch waves) oscillating back and forth in a one-dimensional comoving cavity (or entire universe) of length $L(t) \propto a(t)$.

Let the instantaneous scattering phase shift be $\Phi(E, t)$. According to Birman-Kreĭn formula, total phase $\Phi$ counts the number of states $N(E, t)$ below energy $E$:

$$
\Phi(E, t) = \pi N(E, t)
$$

For photons (massless bosons), in $d$-dimensional space, the relationship between cumulative number of states $N(E)$ and volume $V(t)$ and energy $E$ is:

$$
N(E, t) \propto V(t) E^d \propto a(t)^d E^d
$$

In adiabatic evolution, the **adiabatic invariant** of quantum systems is their quantum number $N$ (i.e., the energy level index where photons are located remains unchanged).

$$
\frac{d}{dt} N(E(t), t) = 0
$$

This means total phase $\Phi(E(t), t)$ is a conserved quantity:

$$
\frac{d\Phi}{dt} = \frac{\partial \Phi}{\partial E} \frac{dE}{dt} + \frac{\partial \Phi}{\partial t} = 0
$$

**Theorem 9.2.2 (Redshift Drift Equation)**

The rate of change of photon energy (frequency) is determined by the ratio of partial derivatives of scattering phase:

$$
\frac{\dot{E}}{E} = - \frac{\partial \Phi / \partial t}{E \cdot \partial \Phi / \partial E}
$$

Using unified time identity $\partial \Phi / \partial E = \pi \kappa(E)$ (time density) and $N \propto a^d E^d$ leading to $\partial \Phi / \partial t = d \cdot H \Phi$ and $E \partial \Phi / \partial E = d \cdot \Phi$, substituting gives:

$$
\frac{\dot{E}}{E} = - \frac{d \cdot H \Phi}{d \cdot \Phi} = -H(t) = -\frac{\dot{a}}{a}
$$

Integration gives $E(t) \propto 1/a(t)$.

**Physical Interpretation**:

Redshift is not photon "fatigue" or energy dissipation but a necessary consequence of **phase conservation**.

* **Denominator** $\partial \Phi / \partial E \sim \text{time}$: Represents the time width of photon wave packets.

* **Numerator** $\partial \Phi / \partial t \sim \text{drift}$: Represents the rate at which background medium (universe) changes phase with time.

Redshift is photons adjusting their frequency to adapt to constantly changing boundary conditions ($a(t)$) in order to maintain their "phase identity" (quantum number $N$).

### 9.2.3 Hubble's Law from Scattering Perspective: Continuous Limit of Doppler Effect

To understand more intuitively, we can decompose cosmic expansion into a series of tiny **scattering events**.

Consider a photon passing through a local scatterer (e.g., horizon or comoving lattice site) at time $t$. Since the scatterer recedes relative to the photon source at velocity $v = H \Delta x$, the photon experiences a tiny Doppler frequency shift.

In the continuous limit, this discrete scattering becomes **continuous phase shift accumulation**.

Let the photon propagate distance $dx = c dt$ in time $dt$. Changes in background metric cause small variation $\delta S$ in scattering matrix $S$.

Wigner-Smith time delay $\tau$ tells us the effective path length that photons "feel."

$$
\Delta t_{delay} = \hbar \frac{\partial \delta}{\partial E}
$$

And Hubble flow causes explicit rate of phase change $\partial \delta / \partial t$.

Redshift $z$ is defined as the reciprocal of the ratio of received frequency to emitted frequency minus one.

$$
1+z = \frac{\omega_{emit}}{\omega_{obs}} = \exp\left( \int_{t_e}^{t_o} H(t) dt \right)
$$

This can be rewritten as drift integral of scattering phase:

$$
\ln(1+z) = \int \frac{\dot{a}}{a} dt = \int \frac{\partial_t \Phi}{\partial_E \Phi} \frac{dE}{E} \dots
$$

This shows that **cosmological redshift is the integral effect of countless tiny Doppler scatterings**. The universe itself is a huge, slowly expanding scattering cavity.

### 9.2.4 Adiabaticity Breaking and Particle Production

The above derivation relies on adiabatic condition $\epsilon \ll 1$. If this condition is broken (e.g., during reheating at the end of inflation, or Hawking radiation near black hole horizons), phase $\Phi$ will no longer be conserved.

At this point, $\frac{d}{dt} N \neq 0$, meaning **particle number is no longer conserved**.

This corresponds to non-zero $\beta$ coefficient in Bogoliubov transformation:

$$
\hat{a}_{out} = \alpha \hat{a}_{in} + \beta \hat{a}_{in}^\dagger
$$

In the QCA framework, this manifests as unitary evolution $U(t)$ producing off-diagonal mixing between bases at different times.

This explains why in the current mild expansion period (adiabatic period) we see redshift (frequency changes, particle number unchanged), while in early universe (non-adiabatic period) we see matter production (frequency changes, particle number also changes).

**Conclusion 9.2.3**

By interpreting redshift as phase drift in adiabatic scattering processes, we unify microscopic wave dynamics with macroscopic cosmological observations.

1.  **Hubble's law** is the manifestation of phase space volume (quantum number) conservation in expanding background.

2.  **Photons** are adiabatic probes maintaining their phase imprint, faithfully recording changes in cosmic scale.

This mechanism requires no introduction of the "stretching" concept of curved spacetime, completely based on evolution of states in Hilbert space, consistent with our goal of "de-geometrizing" discrete ontology.

In the next section, we will explore how this evolution of microscopic states leads to macroscopic **thermodynamic time arrow**, i.e., locking of entropy increase direction.

