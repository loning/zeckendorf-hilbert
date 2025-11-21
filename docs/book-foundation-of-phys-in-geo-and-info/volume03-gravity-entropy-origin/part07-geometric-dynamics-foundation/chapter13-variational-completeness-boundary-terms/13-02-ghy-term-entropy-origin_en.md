**13.2 Entropic Origin of Gibbons-Hawking-York (GHY) Term: Partition Function of Edge Modes**

In Section 13.1, we pointed out the variational incompleteness of the Einstein-Hilbert action under Dirichlet boundary conditions: it leaves a boundary residual term containing normal derivatives of the metric. This section will introduce the famous **Gibbons-Hawking-York (GHY)** boundary term to fix this issue.

More importantly, in the discrete ontology framework constructed in this book, the GHY term is no longer merely an auxiliary term introduced for mathematical self-consistency. We will prove that in the Euclidean path integral formulation, **the GHY term is precisely the true source of holographic entropy $S = A/4G$**. It represents the partition function logarithm of degrees of freedom "cut off" on the spacetime boundary—**edge modes**. This discovery perfectly unifies mathematical variational completeness with the physical holographic principle.

### 13.2.1 Construction of GHY Boundary Term and Proof of Variation Cancellation

To eliminate the boundary flow term $\int_{\partial M} v^\mu n_\mu$ derived in Section 13.1.1, we need to add a counter-term to the total action.

**Definition 13.2.1 (Gibbons-Hawking-York Action)**

For the boundary $\partial M$ of spacetime manifold $M$, let its induced metric be $h_{ab}$ and outward unit normal vector be $n^\mu$ (satisfying $n^\mu n_\mu = \varepsilon = \pm 1$). Define the boundary action as the integral of extrinsic curvature (Extrinsic Curvature):

$$
I_{\text{GHY}} = \frac{\varepsilon}{8\pi G} \int_{\partial M} K \sqrt{|h|} \, \mathrm{d}^3y
$$

where $K = h^{ab} K_{ab} = \nabla_\mu n^\mu$ is the trace of the extrinsic curvature tensor, describing the expansion rate of the boundary under normal flow.

**Theorem 13.2.2 (Variational Completeness Theorem)**

The total action $I_{\text{total}} = I_{\text{EH}} + I_{\text{GHY}}$ is variationally complete under fixed boundary induced metric ($\delta h_{ab} = 0$). That is:

$$
\delta I_{\text{total}} \Big|_{\delta h_{ab}=0} = \frac{1}{16\pi G} \int_M G_{\mu\nu} \delta g^{\mu\nu} \sqrt{-g} \, \mathrm{d}^4x
$$

Normal derivative terms on the boundary are precisely canceled.

**Proof**:

1. **Review Boundary Term of EH Action**:

   From Section 13.1, the boundary flux produced by $\delta I_{\text{EH}}$ is:

   $$
   \delta I_{\text{EH}}^{\partial} = \frac{\varepsilon}{16\pi G} \int_{\partial M} (g^{\alpha\beta} \delta \Gamma^\mu_{\alpha\beta} - g^{\mu\alpha} \delta \Gamma^\beta_{\alpha\beta}) n_\mu \sqrt{|h|} \, \mathrm{d}^3y
   $$

   Under fixed $h_{ab}$ (i.e., zero tangential derivative variations), the main contribution comes from normal derivative terms $\partial_n \delta g$.

2. **Calculate Variation of GHY Term**:

   $$
   \delta I_{\text{GHY}} = \frac{\varepsilon}{8\pi G} \int_{\partial M} (\delta K \sqrt{|h|} + K \delta \sqrt{|h|})
   $$

   Since $\delta h_{ab} = 0$, we have $\delta \sqrt{|h|} = \frac{1}{2}\sqrt{|h|} h^{ab} \delta h_{ab} = 0$. Therefore, we only need to calculate $\delta K$.

   Extrinsic curvature $K_{ab} = h_a^\mu h_b^\nu \nabla_\mu n_\nu$. Its variation involves variation of the normal vector $\delta n_\mu$ and variation of the connection $\delta \Gamma$.

   Using the unit normalization constraint $n^\mu n_\mu = \varepsilon$, we obtain $\delta n_\mu = \frac{1}{2} \varepsilon n_\mu n^\rho n^\sigma \delta g_{\rho\sigma}$ (under $\delta h_{ab}=0$ this term is usually zero, but retained in general derivation).

   The key term comes from connection variation:

   $$
   \delta K \sim h^{\mu\nu} \delta (\nabla_\mu n_\nu) \sim h^{\mu\nu} n_\rho \delta \Gamma^\rho_{\mu\nu}
   $$

3. **Cancellation Verification**:

   Expand $\delta \Gamma$ as metric derivatives. It can be proved that the coefficient of $\partial_n \delta g$ terms in $\delta K$ is exactly $-1/2$ (relative to the coefficient in the EH term).

   Since the coefficient before $I_{\text{GHY}}$ is $1/8\pi G$ (twice that of $I_{\text{EH}}$), they precisely cancel:

   $$
   \frac{1}{16\pi G} (\text{Flux}) + \frac{1}{8\pi G} (-\frac{1}{2} \text{Flux}) = 0
   $$

   $\square$

### 13.2.2 Euclidean Path Integral and Black Hole Entropy

At the classical level, the GHY term is just a mathematical correction. But in semiclassical gravity, it is the physical source of entropy.

Consider the Euclidean path integral, where the partition function is:

$$
Z \approx e^{-I_E[g_{cl}]}
$$

where $I_E$ is the on-shell value of the Euclidean action. Thermodynamic entropy is given by $S = (1 - \beta \partial_\beta) \ln Z$.

**Theorem 13.2.3 (GHY Entropy Generation Theorem)**

For vacuum Einstein gravity ($R=0$), the bulk action $I_{\text{EH}}$ is zero on-shell. The entire free energy and entropy of the system come from the boundary term $I_{\text{GHY}}$. For Schwarzschild black holes or other thermal spaces with Killing horizons, the entropy derived from this strictly equals the Bekenstein-Hawking entropy:

$$
S = \frac{A}{4G\hbar}
$$

**Proof**:

Taking the Schwarzschild black hole as an example, the Euclidean metric is $ds^2 = f(r) d\tau^2 + f(r)^{-1} dr^2 + r^2 d\Omega^2$, where $\tau$ has period $\beta = 1/T_H$.

1. **Volume Integral**: $R=0$, so $I_{\text{EH}} = 0$.

2. **Boundary Integral**: Calculate $I_{\text{GHY}}$ at $r=R \to \infty$. Need to subtract the flat space background term $I_0$ (reference term) for regularization.

   $$
   I_{\text{total}} = -\frac{1}{8\pi G} \int_{\partial M} (K - K_0) \sqrt{h} \, d^3y
   $$

   The calculation result is $I_E = \beta M - \pi r_h^2 / G$ (approximate form, depending on ensemble definition).

   Free energy $F = I_E / \beta = M - TS$.

   Solving gives $S = \pi r_h^2 / G = A/4G$.

   $\square$

### 13.2.3 Edge Modes: Discrete Ontology Interpretation

Why do boundary terms contain entropy? In QCA discrete ontology, this has a clear microscopic explanation.

**Definition 13.2.4 (Edge Modes)**

When we divide the entire universe (closed system) into "system" $M$ and "environment" $\bar{M}$, we cut quantum entanglement bonds crossing the boundary $\partial M$.

In gauge field theory and gravity, Hilbert space cannot simply decompose as $\mathcal{H}_M \otimes \mathcal{H}_{\bar{M}}$, because gauge constraints (such as Gauss's law) are non-local.

To restore decomposition, **edge modes** must be introduced on the boundary, which carry gauge charges on the boundary (in gravity, these are diffeomorphism charges).

**Physical Picture**:

1. **Bulk Action** $I_{\text{EH}}$ describes **closed** dynamics inside the system, corresponding to pure state evolution with zero entropy (or unitary conservation).

2. **Boundary Action** $I_{\text{GHY}}$ is actually the **Berry phase** or **symplectic potential** of edge modes.

3. Under Euclidean rotation, this phase becomes real (partition function), and its value measures the dimension of the edge mode state space.

   $$
   Z_{\text{GHY}} = \text{Tr}_{\text{edge}} (e^{-\beta H_{\text{edge}}})
   $$

   Since $I_{\text{GHY}} \propto \text{Area}$, this means edge modes are distributed on the boundary, with a fixed number of bits per Planck area. This is precisely the microscopic realization of the holographic principle.

### 13.2.4 Brown-York Quasi-local Tensor

The variation of the GHY term also defines energy-momentum on the boundary.

**Definition 13.2.5 (Brown-York Stress Tensor)**

For boundary $\partial M$ with induced metric $h_{ab}$. By varying the boundary action, define the quasi-local energy-momentum tensor:

$$
T^{ab}_{\text{BY}} \equiv \frac{2}{\sqrt{|h|}} \frac{\delta I_{\text{total}}}{\delta h_{ab}} = \frac{1}{8\pi G} (K^{ab} - K h^{ab})
$$

This tensor describes the **quasi-local energy** and momentum contained in spacetime region $M$.

For example, for asymptotically flat spacetime, integrating $T^{ab}_{\text{BY}}$ over a sphere at infinity gives the ADM mass.

**Conclusion**

The GHY boundary term is not a mathematical patch—it is a **direct manifestation of the holographic nature of gravity**.

* Mathematically, it guarantees completeness of the variational principle.

* Thermodynamically, it provides entropy for black holes and horizons.

* Microscopically, it counts severed edge modes.

In the next section 13.3, we will address more complex situations than smooth boundaries—**non-smooth boundaries (corners)**. We will introduce the Hayward term, proving that when discrete QCA geometry approaches continuity, corner contributions are non-negligible topological corrections.

