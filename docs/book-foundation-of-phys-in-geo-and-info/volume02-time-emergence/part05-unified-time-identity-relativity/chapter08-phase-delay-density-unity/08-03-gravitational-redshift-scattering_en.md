**8.3 Scattering Mechanism of Gravitational Redshift: Rescaling Effect of Potential Field on Local Density of States**

In Sections 8.1 and 8.2, we established the unified time identity $\kappa(E) = \rho(E)$ and proposed the viewpoint "Time is Matter": the rate of time flow is determined by local density of states. This microscopic perspective provides a purely quantum statistical explanation mechanism for one of the most classic effects in general relativity—**gravitational redshift**.

In traditional general relativity, gravitational redshift is geometrically explained as wavelength stretching with spatial scale ($\lambda \propto a(t)$) caused by spacetime metric $g_{00}$: clocks in deep gravitational potential wells run slow. But in the discrete ontology of this book, there is no a priori background metric; gravitational potential manifests as local modification of the Hamiltonian. This section will prove that gravitational redshift is essentially **rescaling of local density of states by potential fields**, and this rescaling directly causes observed time dilation through Wigner-Smith time delay.

### 8.3.1 Gravitational Potential as Multiplicative Factor of Hamiltonian

Consider a quantum system (such as an atomic clock or scattering target) located in a gravitational potential $\Phi(\mathbf{x})$. In weak field approximation (or in static spherically symmetric metric $ds^2 = -(1+2\Phi)dt^2 + \dots$), the local energy $E_{loc}$ and the energy $E_{\infty}$ of observers at infinity satisfy the following relation (Tolman relation):

$$
E_{\infty} = E_{loc} \sqrt{g_{00}} \approx E_{loc} (1 + \Phi)
$$

where $\Phi < 0$ is the gravitational potential.

For quantum systems, this means the effective Hamiltonian $H_{eff}$ relative to flat space Hamiltonian $H_0$ undergoes multiplicative rescaling, not just additive displacement. For particles with mass $m$, rest energy $mc^2$ dominates, and the rescaling effect is most significant:

$$
H(\mathbf{x}) = \sqrt{g_{00}(\mathbf{x})} H_0 \approx (1 + \Phi(\mathbf{x})) H_0
$$

This differs from $V$ as an additive potential in the Schrödinger equation, but in the relativistic limit, the metric indeed couples to energy as a multiplicative factor. This **local contraction of energy scale** is the dynamical origin of gravitational redshift.

### 8.3.2 Rescaling Transformation of Density of States

Using the unified time identity $\kappa = \rho$, we examine how this energy rescaling affects density of states $\rho(E)$, and thus time delay $\tau$.

Let the density of states in the local reference frame (Local Inertial Frame) be $\rho_{loc}(E_{loc})$. This is an intrinsic property determined by the system's internal structure (such as atomic energy level spacing) and does not change with position.

For observers at infinity, the energy they measure is $E_{\infty}$. According to conservation of energy level number (diffeomorphism invariance):

$$
dN = \rho_{loc}(E_{loc}) dE_{loc} = \rho_{\infty}(E_{\infty}) dE_{\infty}
$$

Density of states $\rho_{\infty}$ is the effective density of states "seen" by observers. Using $E_{loc} = E_{\infty} / \sqrt{g_{00}}$, we have:

$$
\frac{dE_{loc}}{dE_{\infty}} = \frac{1}{\sqrt{g_{00}}}
$$

Substituting into the conservation equation:

$$
\rho_{\infty}(E_{\infty}) = \rho_{loc}\left( \frac{E_{\infty}}{\sqrt{g_{00}}} \right) \frac{1}{\sqrt{g_{00}}}
$$

This means that for external observers, **density of states in gravitational potential wells is amplified**. The factor $1/\sqrt{g_{00}} > 1$ (because $\Phi < 0, g_{00} < 1$) directly increases the number of states per unit energy interval.

### 8.3.3 Derivation of Redshift Formula from Time Delay

Now apply the unified time identity $\tau(E) = 2\pi \rho(E)$ (in natural units).

* **Local Time Delay**: $\tau_{loc} = 2\pi \rho_{loc}(E_{loc})$. This is the intrinsic time experienced by internal processes of atomic clocks (such as electron transitions).

* **Observed Time Delay**: $\tau_{\infty} = 2\pi \rho_{\infty}(E_{\infty})$. This is the process duration measured by observers at infinity.

Substituting the transformation relation of density of states:

$$
\tau_{\infty} = 2\pi \rho_{loc}(E_{loc}) \frac{1}{\sqrt{g_{00}}} = \tau_{loc} \frac{1}{\sqrt{g_{00}}}
$$

That is:

$$
\tau_{\infty} = \frac{\tau_{loc}}{\sqrt{1 + 2\Phi}} \approx \tau_{loc} (1 - \Phi)
$$

Since $\Phi < 0$, $\tau_{\infty} > \tau_{loc}$.

This is exactly the time dilation formula of general relativity $\Delta t_{\infty} = \Delta \tau / \sqrt{g_{00}}$.

**Physical Interpretation**:

From the perspective of scattering time theory, gravitational redshift is not because "time flows slower," but because **information processing becomes slower**.

1.  Gravitational potential compresses the energy scale ($E_{\infty} < E_{loc}$).

2.  Compression of energy scale causes reverse expansion of density of states $\rho(E)$ (squeezing effect).

3.  According to $\text{Tr}\mathsf{Q} \propto \rho$, increase in density of states means scattering channels become more crowded.

4.  External observers find that particles need to traverse more microscopic states to complete one quantum transition (scattering process) in the potential well, thus consuming more coordinate time.

### 8.3.4 Reconstructing Metric $g_{00}$ from Microscopic $\kappa(E)$

The above derivation shows that spacetime metric component $g_{00}$ is not a fundamental quantity but a macroscopic statistical parameter of **relative density of states**. We can conversely define gravitational potential:

**Definition 8.3.1 (Entropic Gravitational Potential)**

In the QCA universe, if there exists non-uniform distribution of vacuum density of states $\rho_{vac}(\mathbf{x}, E)$ throughout space, then define effective gravitational potential $\Phi(\mathbf{x})$ as the logarithmic deviation of density of states:

$$
\Phi(\mathbf{x}) \equiv -\ln \left( \frac{\rho_{vac}(\mathbf{x}, E)}{\rho_{ref}(E)} \right)
$$

Or more precisely, define through the unified time master scale $\kappa$:

$$
\sqrt{g_{00}(\mathbf{x})} = \frac{\kappa_{ref}(E)}{\kappa(\mathbf{x}, E)}
$$

This formula reveals the microscopic mechanism of **gravity as entropic pressure**. Matter tends to move toward regions with large $\kappa$ (high density of states), which corresponds to maximizing the number of microscopic states (entropic force) in statistical mechanics. Macroscopically, this manifests as objects falling toward gravitational sources (large $\kappa$ around gravitational sources).

**Theorem 8.3.2 (Universality of Redshift in Scattering)**

For any system satisfying the unified time identity $\kappa = \text{Tr}\mathsf{Q}/2\pi$, as long as interactions cause multiplicative rescaling of the Hamiltonian $H \to \lambda H$, the system necessarily exhibits redshift effects, with redshift amount $z = \lambda^{-1} - 1$. This applies not only to gravity but also to any medium system simulating gravity (such as optical black holes or acoustic metrics).

### 8.3.5 Unified Perspective on Experimental Verification

Using this mechanism, we can re-examine the famous **Pound-Rebka experiment**.

* **Traditional Explanation**: Photons rise in gravitational field, lose energy, frequency decreases $\nu' < \nu$.

* **Scattering Explanation**: Atomic nuclei (emitters) at the bottom of the tower (deep potential) have higher local density of states $\rho_{bottom}$. Atomic nuclei (receivers) at the top have lower local density of states $\rho_{top}$.

    The time delay of emission process $\tau_{emit} \propto \rho_{bottom}$ is greater than the time delay of absorption process $\tau_{absorb} \propto \rho_{top}$.

    To achieve resonance (time matching), photons must adjust their frequency (energy) to compensate for the difference in "time processing rates" at the two locations. Redshift is the **impedance matching** condition connecting two regions with different information densities.

**Conclusion**

This section proves that gravitational redshift can be completely derived from the **rescaling effect of potential fields on local density of states**. Combined with the unified time identity, we can reproduce the time dilation effects of general relativity without assuming curved spacetime background, solely based on microscopic scattering statistical properties ($\kappa$ density). This paves the way for Volume III to completely geometrize gravity as an entropic force.

In the next section, we will generalize this logic to the **relative scattering determinant** in curved spacetime, showing how to reconstruct the Riemann metric of spacetime by measuring scattering data.

