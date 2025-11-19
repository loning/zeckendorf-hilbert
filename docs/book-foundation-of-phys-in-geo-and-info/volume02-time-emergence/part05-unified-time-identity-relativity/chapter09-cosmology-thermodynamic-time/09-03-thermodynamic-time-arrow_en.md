**9.3 Thermodynamic Time Arrow: From Density of States $\rho(E)$ to Partition Function and Locking of Entropy Increase Direction**

In Chapter 8, we established the microscopic definition of time: time flow rate $\kappa(E)$ equals density of states $\rho(E)$. In Sections 9.1 and 9.2, we applied this microscopic time to the dynamics of expanding universe. However, dynamical equations (whether Schrödinger equation or Einstein equations) are usually time-reversal symmetric at the microscopic level. This leads to one of the most famous paradoxes in physics: **if microscopic laws are reversible, why does macroscopic world time always point to the future (entropy increase direction)?**

This section will prove that, under the framework of unified time theory, the thermodynamic time arrow is not an additional assumption of statistical mechanics but a **natural property of spectral geometry**. Since $\kappa(E) = \rho(E)$, the direction of time flow is locked to the direction of density of states growth. Macroscopic time arrow is essentially **gradient flow of information capacity**.

### 9.3.1 Thermodynamic Representation of Spectral Geometry: From Trace to Partition Function

First, we need to connect microscopic scattering time ($\text{Tr}\mathsf{Q}$) with macroscopic thermodynamic quantities.

In statistical mechanics, the core object is the **partition function** $Z(\beta)$ of canonical ensemble, where $\beta = 1/k_B T$ is inverse temperature.

$$
Z(\beta) = \text{Tr}(e^{-\beta H}) = \int_0^\infty \rho(E) e^{-\beta E} \, \mathrm{d}E
$$

This shows that partition function is the Laplace transform of density of states $\rho(E)$.

Using unified time identity $\rho(E) = \frac{1}{2\pi\hbar} \tau_{tot}(E)$, we can rewrite partition function as **integral of time delay**:

$$
Z(\beta) = \frac{1}{2\pi\hbar} \int_0^\infty \tau_{tot}(E) e^{-\beta E} \, \mathrm{d}E
$$

This formula reveals the dynamical origin of thermodynamics: **partition function is a weighted sum of all possible microscopic time delays of the system**. The thermodynamic weight of the system at temperature $T$ depends on how long it can "dwell" at each energy layer.

### 9.3.2 Entropy as Logarithmic Time Density

Thermodynamic entropy $S(\beta)$ is defined by $S = k_B (\ln Z + \beta \bar{E})$. In microcanonical ensemble (fixed energy $E$), Boltzmann entropy is:

$$
S(E) = k_B \ln \Omega(E) \approx k_B \ln \rho(E)
$$

Substituting unified time identity:

$$
S(E) = k_B \ln \left( \frac{\tau_{tot}(E)}{2\pi\hbar} \right)
$$

**Theorem 9.3.1 (Time-Entropy Equivalence Principle)**

Microcanonical entropy strictly equals the logarithm of total scattering time delay of the system (plus fundamental constant terms).

$$
S(E) \sim \ln \tau_{tot}(E)
$$

This relationship applies not only to black holes (where $\tau \sim e^{S_{BH}}$) but to any statistical system. It gives an operational definition of entropy: **entropy is a measure of system's "viscosity" or "time impedance."**

* **Low Entropy State**: $\tau_{tot}$ is small, system responds quickly to external perturbations ("transparent").

* **High Entropy State**: $\tau_{tot}$ is large, system has extremely rich internal states, external perturbations entering will experience long multiple scattering and entanglement ("turbid").

### 9.3.3 Spectral Origin of Time Arrow: Hagedorn Growth and Asymmetry

Why does time always flow forward (entropy increase)? This depends on how $\rho(E)$ changes with $E$.

For most physical systems (QCA networks, field theory, black holes), Hilbert space dimension grows exponentially with energy (or volume). For example, **Hagedorn spectrum** in string theory or QCA:

$$
\rho(E) \sim E^\alpha e^{\beta_H E}
$$

This means $\tau_{tot}(E)$ is a strongly increasing function of energy.

**Definition 9.3.2 (Time Asymmetry of Spectral Flow)**

Examine diffusion of a wave packet in Hilbert space. Due to exponential growth of $\rho(E)$, the high-energy end (or high-entanglement end) of state space is much larger than the low-energy end.

According to Fermi's golden rule, transition rate $W_{i\to f} \propto |M_{if}|^2 \rho(E_f)$.

Even if microscopic matrix elements $|M_{if}|^2$ are symmetric, transition probabilities are greatly weighted by final state density $\rho(E_f)$.

$$
\frac{P(E \to E+\delta E)}{P(E+\delta E \to E)} = \frac{\rho(E+\delta E)}{\rho(E)} \approx e^{\beta_H \delta E} \gg 1
$$

This is the microscopic mechanism of **thermodynamic time arrow**: systems tend to evolve toward regions with higher density of states (i.e., larger time delay), purely because there are more "rooms" there.

**Corollary 9.3.3 (Time Deceleration Effect)**

As the universe evolves, entropy $S$ increases, meaning $\tau_{tot}$ increases.

This leads to a counterintuitive but profound conclusion: **the intrinsic time flow rate of the universe is gradually slowing down**.

Early low-entropy universe, physical processes (interactions) occur extremely fast ($\tau$ small); late high-entropy universe (filled with black holes and radiation), physical processes become extremely slow ($\tau$ large). We feel time flowing "uniformly" because our biological clocks are also made of the same matter, we are synchronously decelerated.

### 9.3.4 Entropy Increase Locking in Expanding Universe

In Section 9.1, we saw that cosmic expansion introduces non-Hermitian dissipation. How does this dissipation agree with the above entropy increase?

Consider horizon $\partial V$. Horizon is a sink of information. As $H$ decreases (end of inflation or matter-dominated period), horizon radius $R_H = c/H$ increases.

According to holographic principle, the maximum information capacity that horizon can accommodate (i.e., maximum potential entropy of entire universe) is $S_{max} \propto A_H \propto H^{-2}$.

Meanwhile, matter entropy $S_{matter}$ inside the universe is also increasing.

The second law of thermodynamics in cosmology is stated as increase of **generalized entropy**:

$$
\frac{d}{dt} (S_{matter} + S_{horizon}) \ge 0
$$

Since horizon expansion sweeps over more lattice sites, $\rho_{total}(E)$ (effective density of states of entire universe) monotonically increases with time $t$.

This **cosmological growth of density of states** locks the time arrow: as long as the universe is expanding (or horizon is expanding), the system is always in a non-equilibrium state with "continuously growing phase space volume," thus driving the system to diffuse into larger phase space.

**Conclusion 9.3.4**

Time arrow is not an accidental choice of initial conditions (past hypothesis) but an inevitability of QCA geometric evolution:

1.  **Microscopically**: $\tau \sim \rho$.

2.  **Structurally**: $\rho(E)$ grows exponentially with complexity.

3.  **Macroscopically**: System evolution is probability flow toward high $\rho$ (high delay) regions.

**Time flows forward because the future contains more microscopic states than the past.**

In the next section, we will explore the ultimate corollary of this logic: if vacuum itself has non-zero density of states, it will manifest as a repulsive force—this is the **geometric nature of dark energy**.

