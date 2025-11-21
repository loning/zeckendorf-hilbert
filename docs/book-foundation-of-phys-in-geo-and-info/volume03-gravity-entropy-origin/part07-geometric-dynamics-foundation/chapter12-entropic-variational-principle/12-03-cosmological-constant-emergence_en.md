**12.3 Emergence of Cosmological Constant $\Lambda$: As Integration Constant of Equation of State**

In Section 12.2, we derived the proportionality relationship $G_{\mu\nu} = 8\pi G T_{\mu\nu}$ between Einstein tensor and energy-momentum tensor through the Maximum Entanglement Equilibrium Axiom (MEEA). In this derivation, we implicitly assumed that the volume $V$ of the causal diamond is fixed, or that when comparing changes in geometric entropy and matter entropy, we ignored the "zero-point energy" contribution of the background geometry itself.

This section will complete this picture, proving that the **cosmological constant $\Lambda$** is not an artificially added term to Einstein's field equations, but an inevitable product of the **volume constraint** in the entropic variational principle. In the IGVP framework, $\Lambda$ appears as an integration constant of the spacetime thermodynamic equation of state, and its small but non-zero observed value (dark energy) arises from the holographic spectral cutoff of vacuum fluctuations.

### 12.3.1 Volume Constraint and Lagrange Multiplier in Variational Principle

Recall the variational condition $\delta S_{\text{gen}} = 0$ from Section 12.1. In thermodynamics, finding extrema of entropy usually requires specifying constraint conditions (such as energy conservation, fixed volume, etc.). For spacetime geometry, the most natural geometric invariant is the **generalized volume** $V$ of the causal diamond.

If we require the generalized entropy of the vacuum state to be extremal under **fixed volume** constraint, then the variational problem should be expressed as:

$$
\delta \left( S_{\text{grav}} + S_{\text{mat}} \right) - \lambda \delta V = 0
$$

where $\lambda$ is a Lagrange multiplier.

**Theorem 12.3.1 (Geometric Form of Volume Variation)**

For a small causal diamond, its volume variation $\delta V$ relative to flat space is determined by the variation of the metric trace. In Riemann Normal Coordinates, this is equivalent to:

$$
\delta V = \int_{\Sigma} \frac{1}{2} g^{\mu\nu} \delta g_{\mu\nu} \sqrt{-g} \, d^dx \approx \frac{1}{2} \eta^{\mu\nu} \delta g_{\mu\nu} V_0
$$

Adding this constraint term to the equilibrium equation from Section 12.1:

$$
-\frac{1}{4G} \delta G_{\mu\nu} + 2\pi \delta T_{\mu\nu} - \lambda g_{\mu\nu} = 0
$$

Rearranging coefficients, to make the equation return to the de Sitter solution in the vacuum limit ($T_{\mu\nu} \to 0$), we denote the multiplier $\lambda$ as $-\Lambda / 4G$ (coefficient convention depends on metric signature). This yields the field equation with cosmological constant:

$$
R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu} + \Lambda g_{\mu\nu} = 8\pi G T_{\mu\nu}
$$

**Physical Interpretation**:

From this perspective, $\Lambda$ is the **"entropic pressure" required to maintain constant spacetime volume**.

* If $\Lambda > 0$, vacuum has negative pressure ($P_{vac} = -\rho_{vac} = -\Lambda/8\pi G$), tending to expand spacetime.

* This expansion tendency is balanced by gravitational attraction of matter (the $G_{\mu\nu}$ term), thereby maintaining the stability of local causal diamonds (or defining the background expansion rate).

### 12.3.2 Unimodular Gravity and Integration Constant

Another way to understand $\Lambda$ comes from differential geometric identities.

In Section 12.2.2, we proved $\nabla^\mu (G_{\mu\nu} - 8\pi G T_{\mu\nu}) = 0$.

This means the tensor $X_{\mu\nu} = G_{\mu\nu} - 8\pi G T_{\mu\nu}$ is a conserved tensor.

However, the metric tensor $g_{\mu\nu}$ itself is also covariantly conserved ($\nabla^\mu g_{\mu\nu} = 0$). Therefore, any term of the form $\Lambda g_{\mu\nu}$ can be added to the field equations without destroying energy-momentum conservation.

**Corollary 12.3.2 ($\Lambda$ as Integration Constant)**

If we start only from the **trace** part (Trace Dynamics) or **unimodular** variation, the trace part of Einstein's equations is:

$$
-R + 4\Lambda = 8\pi G T
$$

Here, $\Lambda$ appears as an integration constant. It is not directly controlled by local matter distribution, but is determined by the **global boundary conditions** of the universe.

In QCA cosmology (Chapter 9), this boundary condition is determined by holographic entropy flow balance on the horizon. $\Lambda$ must take a specific value to ensure that the horizon radius $R_H = \sqrt{3/\Lambda}$ can accommodate the total degrees of freedom inside the universe.

### 12.3.3 Holographic Renormalization: Elimination of $10^{120}$-fold Difference

Standard quantum field theory predicts vacuum zero-point energy density $\rho_{vac} \sim M_P^4$, leading to a huge cosmological constant ($10^{120}$-fold difference). The IGVP framework naturally resolves this using the holographic principle.

**Theorem 12.3.3 (Spectral Windowing Renormalization)**

In IGVP, what can cause gravitational effects (i.e., enter the right side $T_{\mu\nu}$ of field equations) is not the microscopic absolute state density $\rho_{micro}$, but the **effective state density** $\rho_{eff}$ after "spectral windowing" by small causal diamonds.

According to the PSWF theory from Chapter 5, a finite observation window $L$ provides an infrared cutoff for frequency bands. In holographic duality, degrees of freedom in the bulk are projected onto the boundary.

For a causal diamond of radius $L$, its holographic number of degrees of freedom $N \sim (L/l_P)^2$.

If these degrees of freedom are regarded as "vacuum bits" uniformly distributed in the bulk, then the effective energy density is:

$$
\rho_{\Lambda} \sim \frac{N \cdot (\text{Unit Energy})}{V} \sim \frac{(L/l_P)^2 \cdot (1/L)}{L^3} \sim \frac{1}{L^2 l_P^2}
$$

When $L$ is taken as the cosmic horizon radius $R_H$, we obtain the observed order of magnitude of dark energy density:

$$
\rho_{\Lambda} \sim \frac{1}{R_H^2 l_P^2} \approx 10^{-123} M_P^4
$$

This derivation shows that $\Lambda$ is small because it is a **holographic projection density**, not a bulk density. It reflects that spacetime, as a quantum entanglement network, has information capacity limited by surface area, not volume.

### 12.3.4 Physical Picture: Dark Energy as "Surface Tension" of Spacetime

Combining the above two points, we can give $\Lambda$ a clear physical image:

In IGVP variation, the geometric entropy term $\frac{A}{4G}$ is similar to the **surface energy** of a droplet (surface tension $\sigma \sim 1/G$).

The matter entropy term $S_{\text{mat}}$ is similar to **thermal energy** in the bulk.

The cosmological constant term $\Lambda V$ is similar to the **external pressure** or **chemical potential** maintaining the droplet's existence.

**Conclusion 12.3.4**

The cosmological constant $\Lambda$ is the projection of spacetime fluid's **surface tension** into the bulk. It is not a mysterious "dark energy fluid," but the intrinsic curvature that spacetime geometry must possess to maintain the holographic entropy bound ($S \le A/4G$). Accelerated expansion is the dynamical response of spacetime to "dilute" the continuously growing entanglement entropy inside, thereby maintaining holographic balance.

At this point, we have completed the entropic origin explanation of all terms in Einstein's field equations:

1. $R_{\mu\nu}$: Geometric focusing of entropy (Raychaudhuri).

2. $T_{\mu\nu}$: Entropy flow of matter (first law of entanglement).

3. $\Lambda g_{\mu\nu}$: Lagrange multiplier for holographic volume constraint.

In the next section, we will generalize this framework to **higher-order gravitational theories**, proving that when entanglement entropy includes higher-order corrections, IGVP naturally derives Lovelock gravity and $f(R)$ gravity, establishing general relativity's status as a low-energy effective theory.

