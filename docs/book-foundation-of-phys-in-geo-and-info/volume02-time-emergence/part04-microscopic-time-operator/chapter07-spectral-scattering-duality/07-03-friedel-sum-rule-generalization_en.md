**7.3 Generalization of Friedel Sum Rule: From Fermi Liquids to General Scattering Systems**

In Section 7.2, we established the Birman-Kreĭn trace formula $\det S(E) = e^{-2\pi i \xi(E)}$, connecting the microscopic scattering matrix with the macroscopic spectral shift function. This mathematical identity has an extremely physically insightful application in condensed matter physics, namely the **Friedel Sum Rule**.

This rule was originally proposed by J. Friedel (1952) to explain the screening effect of impurity charges in metals. In this section, we will prove that Friedel's rule is actually a direct corollary of Birman-Kreĭn theory at the Fermi surface, and generalize it to a universal law of "information screening" in general scattering systems. This generalization reveals that scattering phase not only determines time delay but also determines the number of quantum states "captured" or "repelled" by the system in a local region.

### 7.3.1 Charge Screening Problem in Fermi Liquids

Consider a non-interacting electron gas (Fermi liquid) with Fermi energy $E_F$. When we place a charged impurity (e.g., a nucleus with charge $Z$) in it, the electron gas redistributes to screen this external potential.

Physical intuition tells us that to maintain long-range electrical neutrality, the electron gas must form a local electron cloud around the impurity, whose total induced charge $\Delta Q$ must precisely cancel the impurity charge $Z$ (i.e., $\Delta N = Z$, where $\Delta N$ is the number of extra electrons bound around the impurity).

The question is: **How is this screening achieved through the rearrangement of scattering wave functions?** After all, except for possibly a few bound states, most electrons are in scattering states of the continuous spectrum. Scattering states are extensive; how do they produce local charge accumulation?

### 7.3.2 Deriving Friedel's Formula from the Trace Formula

Using the spectral shift function theory established in Chapter 7, the answer to this question becomes obvious.

After introducing the impurity potential $V$, the system's Hamiltonian changes from $H_0$ to $H = H_0 + V$. This causes a change $\Delta \rho(E)$ in the density of states $\rho(E)$.

At zero temperature, all states below $E_F$ are occupied. Therefore, the total change in electron number $\Delta N$ caused by the impurity is the integral of density of states change below the Fermi surface:

$$
\Delta N = \int_{-\infty}^{E_F} \Delta \rho(E) \, \mathrm{d}E
$$

Using the relationship $\Delta \rho(E) = -\xi'(E)$ derived in Section 7.1.4 (Note: Here the sign convention is that $\xi$ is the counting difference $N_0 - N$. If $\xi$ is defined as phase shift $\delta/\pi$, then $\rho = \xi'$. In standard Friedel derivations, phase shift $\delta$ is usually used. Recalling Section 7.2's conclusion $\text{Tr}[\ln S] = -2\pi i \xi \implies 2i\delta = -2\pi i \xi \implies \xi = -\delta/\pi$. Therefore $\Delta \rho = -\xi' = \frac{1}{\pi} \delta'$.):

$$
\Delta \rho(E) = \frac{1}{\pi} \frac{d \delta_{tot}(E)}{dE}
$$

where $\delta_{tot}(E) = \sum \delta_n(E)$ is the total scattering phase.

Substituting into the integral:

$$
\Delta N = \frac{1}{\pi} \int_{-\infty}^{E_F} \frac{d \delta_{tot}(E)}{dE} \, \mathrm{d}E = \frac{1}{\pi} \left[ \delta_{tot}(E_F) - \delta_{tot}(-\infty) \right]
$$

Usually we take $\delta_{tot}(-\infty) = 0$, then we obtain the famous **Friedel Sum Rule**:

$$
\Delta N(E_F) = \frac{1}{\pi} \delta_{tot}(E_F)
$$

For spherically symmetric systems with spin degeneracy $g_s=2$ and angular momentum decomposition $\delta_l$, the formula is:

$$
Z = \Delta N = \frac{2}{\pi} \sum_{l} (2l+1) \delta_l(E_F)
$$

**Physical Interpretation**:

This formula shows that **the scattering phase shift $\delta(E_F)$ at the Fermi surface directly "counts" the amount of charge captured by the impurity**. Although scattering electrons are mobile, the phase lag ($\delta > 0$) means the wave function is "pulled" toward the impurity center, thereby increasing the local probability density. This cumulative effect of phase precisely equals the accumulation of integer particles.

### 7.3.3 Generalization: State Counting Principle in General Scattering Systems

Friedel's rule is not only applicable to electron gases; it is a universal manifestation of **spectrum-scattering duality**. In general quantum systems (including our QCA universe model), it can be stated as:

**Theorem 7.3.1 (Generalized Friedel Theorem)**

For any short-range scattering system, the number of extra quantum states $\Delta N(E)$ that the system "holds" below energy $E$ relative to the free background strictly equals the total scattering phase at that energy divided by $\pi$ (plus bound state contributions, if included in the $\xi$ definition):

$$
\Delta N(E) \equiv \text{Tr}\left[ \Theta(E-H) - \Theta(E-H_0) \right] = \frac{1}{2\pi i} \text{Tr} \left[ \ln S(E) \right] = \frac{1}{\pi} \Phi(E)
$$

where $\Phi(E)$ is the argument of the scattering matrix determinant.

**Meaning in the QCA Universe**:

In discrete ontology, space is a container of finite information. When we introduce a local defect or perturbation (simulating a particle), this perturbation changes the distribution of information capacity throughout the universe. The generalized Friedel theorem tells us:

* **Phase Shift is Information**: By measuring the phase shift $\Phi(E)$ of probe particles (such as photons or gravitational waves) passing through this region, we can precisely calculate how many quantum bits (degrees of freedom) this region has "more" than the vacuum.

* **Holographic Screening**: Just as electron clouds screen impurity charges, quantum fluctuations in the vacuum also rearrange to "screen" any local information source, so that its distant manifestation (phase shift) achieves precise balance with the amount of information contained internally ($\Delta N$).

### 7.3.4 Physical Picture: Charge Accumulation Caused by Time Delay

Combining with **Wigner-Smith time delay** from Chapter 6, we can give Friedel's rule a more intuitive dynamical interpretation.

Recall the trace formula (Section 6.4):

$$
\text{Tr}[\mathsf{Q}(E)] = 2\pi \hbar \Delta \rho(E)
$$

Rewriting $\Delta N(E_F) = \int^{E_F} \Delta \rho(E) dE$:

$$
\Delta N(E_F) = \frac{1}{2\pi \hbar} \int_{-\infty}^{E_F} \text{Tr}[\mathsf{Q}(E)] \, \mathrm{d}E = \frac{1}{2\pi \hbar} \int_{-\infty}^{E_F} \tau_{tot}(E) \, \mathrm{d}E
$$

If we approximate the time delay $\tau_{tot}$ as constant near the Fermi surface (broad resonance approximation), this is not intuitive. But in the quasi-classical limit, we can understand it as:

**The particle flow is delayed by the scatterer for time $\tau$. Since particles continuously flow in (current $J$), this delay causes "traffic jam" or accumulation of particles in the scattering region.**

The accumulated particle number $\Delta N$ is proportional to the product of current and delay time. Friedel's rule is actually the integral result of this dynamical process under Fermi statistics.

**Conclusion 7.3.2 (Time-Matter Equivalence)**

In general scattering systems, **the existence of local matter ($\Delta N$) is equivalent to the cumulative time delay of all historical energy modes passing through this region**.

$$
\text{Total Matter} \propto \int \text{Time Delay}
$$

This again confirms this book's core thesis: matter is not some entity filling spacetime, but rather the **delayed structure** of spacetime (scattering process) itself.

### 7.3.5 Application: Casimir Energy and Vacuum Polarization

As a higher-order application of Friedel's rule, consider the change in vacuum energy (Casimir effect).

The vacuum energy difference is defined as $\Delta E_{vac} = \sum (E_n - E_n^{(0)})$. Using the trace formula, this can be transformed into:

$$
\Delta E_{vac} = \int E \Delta \rho(E) \mathrm{d}E = -\frac{1}{\pi} \int E \frac{d\delta}{dE} \mathrm{d}E
$$

Integration by parts gives:

$$
\Delta E_{vac} = -\frac{1}{\pi} [E \delta(E)]_{-\infty}^{\infty} + \frac{1}{\pi} \int_{-\infty}^{\infty} \delta(E) \mathrm{d}E
$$

This formula completely expresses Casimir energy as an integral of scattering phase shifts. For the QCA universe, this means the vacuum energy density (dark energy) can be directly calculated from the scattering phase shift spectrum of microscopic lattice points, without introducing artificial momentum cutoffs (because phase shifts naturally vanish at the lattice momentum upper bound).

By generalizing Friedel's rule, we not only solve the problem of "how fermions occupy space" but also provide powerful spectral geometric tools for understanding the quantum structure of vacuum. In the next section, we will discuss the topological properties of scattering phase—**Levinson's Theorem**—which will reveal how zero-energy scattering phase shift "remembers" the number of bound states, thereby completing the topological closure of spectrum-scattering duality.

