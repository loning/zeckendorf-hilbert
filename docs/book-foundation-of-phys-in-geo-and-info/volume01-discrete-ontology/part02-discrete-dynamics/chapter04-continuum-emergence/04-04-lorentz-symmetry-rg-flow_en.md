**4.4 Breaking and Restoration of Lorentz Symmetry: Fixed Point Analysis of Renormalization Group Flow (RG Flow)**

In Sections 4.2 and 4.3, we derived Dirac equation and gauge fields from discrete QCA respectively. These two results seem to indicate we have completely recovered relativistic quantum field theory. However, there is a profound theoretical crisis hidden here: QCA is defined on discrete lattices (such as $\mathbb{Z}^3$), and discrete lattices clearly do not possess continuous rotational symmetry $SO(3)$, let alone Poincaré group $SO(3,1)$ containing Lorentz boosts.

On lattices, rotational symmetry collapses to discrete hypercubic group, spacetime translational symmetry collapses to $\mathbb{Z}^4$. This means, in principle, particles moving along axes should have different physical properties (such as speed) from particles moving along diagonals. This contradicts all precision experimental results.

This section will use powerful tools of **Wilsonian Renormalization Group** to prove: although microscopic dynamics explicitly breaks Lorentz symmetry, in long-wavelength limit (infrared fixed point), Lorentz symmetry will automatically restore as an **Accidental Symmetry**.

### 4.4.1 Lattice Anisotropy and Collapse of Poincaré Group

Examine one-dimensional QCA dispersion relation derived in Section 4.2. For particle with momentum $k$, its energy $E_k$ (i.e., eigenvalue of Hamiltonian) is determined by the following equation (set $c=1$):

$$
\cos(E_k \tau) = \cos(k \varepsilon) \cos(\theta)
$$

where $\varepsilon$ is lattice spacing, $\tau$ is time step, $\theta = m\tau$ is mass parameter.

On three-dimensional simple cubic lattice, similar massless Weyl fermion dispersion relation usually has form:

$$
E(\mathbf{k})^2 \propto \sin^2(k_x a) + \sin^2(k_y a) + \sin^2(k_z a)
$$

Or in simpler scalar model:

$$
E^2 = \frac{4}{a^2} \sum_{i=1}^3 \sin^2\left(\frac{k_i a}{2}\right)
$$

**Anisotropy Analysis**:

When $|\mathbf{k}| a \ll 1$, expand to fourth order:

$$
E^2 \approx |\mathbf{k}|^2 - \frac{a^2}{12} \sum_{i=1}^3 k_i^4 + O(a^4)
$$

First term $|\mathbf{k}|^2$ is rotationally invariant, corresponding to standard relativistic dispersion $E=p$. However, second term $\sum k_i^4$ **explicitly breaks rotational symmetry**.

* Along axis $(k, 0, 0)$: $E^2 \approx k^2 - \frac{a^2}{12} k^4$.

* Along diagonal $(k, k, k)/\sqrt{3}$: $E^2 \approx k^2 - \frac{a^2}{36} k^4$.

This means that at extremely high energy scales (approaching cutoff frequency $1/a$), light speed is direction-dependent. This constitutes a direct challenge of discrete ontology to special relativity.

### 4.4.2 Renormalization Group Perspective: Lorentz Symmetry as Accidental Symmetry

To resolve the above contradiction, we must examine behavior of these symmetry-breaking terms under scale transformation (Scale Transformation).

**Definition 4.4.1 (Renormalization Group Flow)**

Introduce scale factor $s > 1$, rescale momentum $k' = s k$, and correspondingly renormalize field operators $\phi' = s^{-\Delta} \phi$ (where $\Delta$ is scaling dimension). Examine flow direction of coupling constants $\lambda_i$ of various operators in effective action $S_{eff}$ as $s$ changes:

$$
\frac{d \lambda_i}{d \ln s} = \beta_i(\{\lambda\})
$$

**Theorem 4.4.2 (Irrelevance of Lorentz Violation)**

In $d=3+1$ dimensional spacetime, standard kinetic term $\int d^4x (\partial \phi)^2$ is **Marginal**, its coefficient remains unchanged (or logarithmically runs) under RG flow.

However, symmetry-breaking terms introduced by lattice (such as $\sum_i \partial_i^4$) correspond to operator dimension $4+2=6$ (in energy dimension) or higher. Near free field fixed point, coupling constants $\lambda_{LIV}$ of these high-dimensional operators decay as energy scale decreases:

$$
\lambda_{LIV}(E) \sim \lambda_0 \left( \frac{E}{\Lambda_{UV}} \right)^n, \quad n \ge 2
$$

where $\Lambda_{UV} \sim 1/a$ is Planck energy scale cutoff.

**Physical Interpretation**:

When observation energy $E \ll \Lambda_{UV}$, all Lorentz symmetry-breaking terms are extremely suppressed. Lorentz symmetry is not an inherent property of microscopic laws, but an emergent property near **Infrared Fixed Point**. Just as fluids macroscopically exhibit isotropic Navier-Stokes equations, despite their microscopic molecular lattices (if they exist) not being isotropic. We call this symmetry **Accidental Symmetry**.

### 4.4.3 Fixed Point Analysis: Isotropization of Light Speed from Dispersion Relation

Let us more rigorously analyze the final state of RG flow. Consider a generic quadratic Hamiltonian density, containing all terms compatible with lattice symmetry:

$$
H(\mathbf{k}) = c_{ij} k_i k_j + d_{ijkl} k_i k_j k_k k_l a^2 + \dots
$$

where $c_{ij}$ and $d_{ijkl}$ are tensors determined by microscopic QCA rules.

1. **Diagonalization of Second-Order Terms**:

    In renormalization process, through wave function renormalization (Rescaling of coordinates), we can always diagonalize and normalize second-order term $c_{ij}$ to $\delta_{ij}$. This step establishes isotropic light speed $c_{eff}$ at low energy. If microscopic QCA has too large differences in hopping amplitudes in different directions, RG flow may lead to non-relativistic fixed point; but for QCA satisfying cubic symmetry (such as model in Section 4.2), $c_{ij}$ is naturally proportional to $\delta_{ij}$.

2. **Flow Direction of Higher-Order Terms**:

    Fourth-order term $d_{ijkl}$ has dimension $[L]^2$ (relative to second-order term). Under RG transformation $x \to s x$, derivative $\partial \to s^{-1} \partial$. Therefore fourth-order derivative term $\partial^4$ decays by $s^{-2}$ compared to $\partial^2$.

    This means RG flow drives system toward **Gaussian Fixed Point**, at which dispersion relation strictly recovers to $E^2 = c_{eff}^2 k^2 + m^2$.

**Conclusion 4.4.3**

For a wide class of QCA (satisfying discrete translation and cubic rotational symmetry), effective field theory in long-wavelength limit **necessarily** possesses Lorentz invariance. This is a dynamical attractor (Attractor) of renormalization group flow.

### 4.4.4 Planck-Scale Residue: Experimental Bounds on Lorentz Violation (LIV)

Although RG flow explains why we don't see Lorentz violation at low energy, finite information axiom ($a \neq 0$) means this symmetry is never perfect. In extremely high-energy astrophysical processes, residual lattice effects may be observed.

**Prediction 4.4.4 (Modified Dispersion Relation, MDR)**

Discrete ontology predicts dispersion relation of photons (or neutrinos) should contain Planck-scale corrections:

$$
E^2 \approx p^2 \pm \xi \frac{p^4}{M_P^2}
$$

where $M_P \approx 1.2 \times 10^{19}$ GeV, $\xi$ is dimensionless coefficient depending on specific QCA structure (usually $O(1)$).

**Experimental Verification Schemes**:

1. **Vacuum Cherenkov Radiation**: If $p^4$ term coefficient is positive, high-energy particle speed may exceed low-energy light speed, causing particles in vacuum to undergo Cherenkov radiation and rapidly decay. Observation of ultra-high-energy cosmic rays (UHECR) suggests this effect is extremely weak or coefficient is negative.

2. **Photon Arrival Time Delay**: For photons from distant gamma-ray bursts (GRB), high-energy photons and low-energy photons should have tiny speed difference $\Delta v \sim (E/M_P)^n$. LIGO and Fermi telescope data have given extremely strong constraints on linear term ($n=1$), forcing QCA models to have specific symmetries to eliminate $n=1$ term (as we showed in 4.4.1, lattices usually lead to $n=2$ corrections, which are still within experimental allowed range).

### 4.4.5 Summary of Volume I

At this point, we have completed the construction of Volume I of *Foundations of Physics in Geometry and Information*.

* **Ontology**: Starting from **Finite Information Axiom**, we established finiteness of Hilbert space dimension, negating reality of continuum (Chapter 1).

* **Geometry**: We proved that Riemannian geometry (distance) and symplectic geometry (gauge fields) both arise from **statistical structure** of quantum state space (Chapter 2).

* **Dynamics**: We introduced **Quantum Cellular Automata (QCA)** as microscopic dynamical engine, proving that causal structure's light cones are manifestations of strict locality (Chapter 3).

* **Emergence**: In this final chapter, we crossed the gap between discrete and continuous, proving that path integrals, Dirac equation, gauge fields, and Lorentz symmetry are all **effective descriptions** of QCA in **long-wavelength limit** (Chapter 4).

These four chapters form a closed loop: we don't need to assume continuous spacetime and relativistic field theory are fundamental; on the contrary, they are inevitable illusions we see as "low-resolution observers" in this discrete, finite, quantized universe.

In the upcoming **Volume II: Emergence of Time**, we will challenge the last, most stubborn parameter in physics—**Time**. We will prove that even the time parameter $t$ itself is merely statistical emergence of quantum entanglement and scattering processes.

