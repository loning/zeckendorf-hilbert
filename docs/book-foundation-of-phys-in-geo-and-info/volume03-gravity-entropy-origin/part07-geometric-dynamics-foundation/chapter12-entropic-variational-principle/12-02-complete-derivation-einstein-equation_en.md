**12.2 Complete Derivation of Einstein's Field Equations: From Scalar Entropy Balance to Tensor Dynamics**

In Section 12.1, we preliminarily derived the scalar form of Einstein's field equations $\delta G_{00} = 8\pi G \delta T_{00}$ using the center point property of small causal diamonds. This only established the connection between energy and curvature in the time direction. To fully reproduce general relativity, we need to prove that this relationship holds in all spacetime directions and for arbitrary matter distributions.

This section will complete this tensorization process. We will prove that the Maximum Entanglement Equilibrium Axiom (MEEA) not only constrains $G_{00}$, but also, through diffeomorphism invariance and the Bianchi identity, forces the entire tensor equation $G_{\mu\nu} = 8\pi G T_{\mu\nu}$ to hold. Furthermore, we will discuss why this derivation excludes other gravitational theories (such as scalar gravity), establishing the uniqueness of tensor gravity.

### 12.2.1 Arbitrary Observers and Lorentz Covariance

In the derivation of Section 12.1, we selected a specific causal diamond whose time axis is defined by a timelike vector $u^\mu$. This led to the scalar equation:

$$
R_{\mu\nu} u^\mu u^\nu - \frac{1}{2} R g_{\mu\nu} u^\mu u^\nu = 8\pi G T_{\mu\nu} u^\mu u^\nu
$$

(Note: For simplicity, we temporarily set $\Lambda=0$, to be supplemented later).

However, according to relativistic principles, the maximum entanglement property of vacuum should be **observer-independent**. For any timelike observer $u'^\mu$ passing through the same spacetime point $p$ (connected via Lorentz transformation), the small causal diamond $\Sigma'$ they construct must also satisfy the entropy balance condition.

**Theorem 12.2.1 (Tensor Lifting Theorem)**

If for all future-pointing unit timelike vectors $u^\mu$ at spacetime point $p$, the scalar equation $X_{\mu\nu} u^\mu u^\nu = 0$ holds (where $X_{\mu\nu} = G_{\mu\nu} - 8\pi G T_{\mu\nu}$ is a symmetric tensor), then the tensor itself must vanish:

$$
X_{\mu\nu} = 0
$$

**Proof**:

A symmetric tensor $X_{\mu\nu}$ is completely determined by its quadratic form $Q(u) = X_{\mu\nu} u^\mu u^\nu$.

If $Q(u) = 0$ holds for all $u$, we can reconstruct $X_{\mu\nu}$ through the polarization identity.

Taking $u = (v+w)/\sqrt{(v+w)^2}$ (for timelike $v, w$), we can derive $X_{\mu\nu} v^\mu w^\nu = 0$.

Since timelike vector bases span the entire tangent space, we have $X_{\mu\nu} = 0$.

$\square$

**Physical Corollary**:

This means that as long as we require "gravitational focusing (geometric entropy decrease) balances matter entropy increase" in every reference frame, we automatically obtain the complete covariant field equations. Gravity is not just time dilation ($g_{00}$), it must also be spatial curvature ($g_{ij}$) and momentum flow effects ($g_{0i}$).

### 12.2.2 Consistency of Energy-Momentum Conservation and Geometric Identities

In general relativity, the consistency of Einstein's field equations relies on two famous conservation laws:

1. **Matter Side**: Local conservation of energy-momentum tensor $\nabla^\mu T_{\mu\nu} = 0$ (arising from diffeomorphism invariance of the matter action).

2. **Geometric Side**: Bianchi identity of Einstein tensor $\nabla^\mu G_{\mu\nu} = 0$ (arising from intrinsic properties of Riemannian geometry).

In the entropic variational principle, we did not presuppose these two conservation laws. However, remarkably, the entropy balance condition itself implies conservation requirements.

**Theorem 12.2.2 (Conservation of Entropy Gradient)**

If the entropy balance condition $\delta S_{\text{gen}} = 0$ holds everywhere throughout spacetime, then matter energy-momentum conservation $\nabla^\mu T_{\mu\nu} = 0$ is an inevitable corollary.

**Argument**:

Assume $G_{\mu\nu} = 8\pi G T_{\mu\nu}$ holds.

Taking the covariant divergence of both sides:

$$
\nabla^\mu G_{\mu\nu} = 8\pi G \nabla^\mu T_{\mu\nu}
$$

Since the left side is identically zero (Bianchi identity), the right side must also be zero.

This means that if we seek a geometric dynamical equation to describe gravity, **the Einstein tensor $G_{\mu\nu}$ is the only possible choice** (under the constraints of second-order derivatives and conservation, guaranteed by Lovelock's theorem). Any attempt to modify the left side (such as introducing $R_{\mu\nu}$ instead of $G_{\mu\nu}$) would lead to non-conservation of matter energy, thereby destroying thermodynamic consistency.

### 12.2.3 The Cosmological Constant $\Lambda$ as an Integration Constant

In the derivation of Section 12.1, we were actually comparing the variations of $G_{\mu\nu}$ and $8\pi G T_{\mu\nu}$. This means the two sides of the equation may differ by a constant multiple of the metric (since $\nabla^\mu g_{\mu\nu} = 0$ is also conserved).

Consider the full equation:

$$
R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu} + \Lambda g_{\mu\nu} = 8\pi G T_{\mu\nu}
$$

Here, $\Lambda$ appears as an **integration constant of the equation of state** in the entropic variational derivation.

* **Geometric Viewpoint**: $\Lambda$ represents the curvature radius when vacuum ($T_{\mu\nu}=0$). In the maximum entanglement hypothesis, this corresponds to the curvature of maximally symmetric space.

* **Thermodynamic Viewpoint**: In Section 9.4, we identified $\Lambda$ as the background phase drift caused by vacuum state density $\rho_{\text{vac}}$. In the field equations, this is precisely the $T_{\mu\nu}^{\text{vac}} = -\rho_{\text{vac}} g_{\mu\nu}$ term.

    $$
    G_{\mu\nu} = 8\pi G (T_{\mu\nu}^{\text{matter}} + T_{\mu\nu}^{\text{vac}}) \implies G_{\mu\nu} + \Lambda_{eff} g_{\mu\nu} = 8\pi G T_{\mu\nu}^{\text{matter}}
    $$

    where $\Lambda_{eff} = 8\pi G \rho_{\text{vac}}$.

### 12.2.4 Why Tensor Gravity? (Exclusion of Scalar Gravity)

One might ask: why must gravity be a tensor field $g_{\mu\nu}$? Could it be a scalar field $\phi$?

Nordström attempted to establish scalar gravity theory, but in the IGVP framework, this is impossible.

1. **Anisotropy of Entropy**: The change in entanglement entropy $\delta S_{\text{mat}}$ depends on energy flow $T_{\mu\nu} u^\mu u^\nu$. This is an anisotropic quantity (depending on observer $u^\mu$).

2. **Matching of Response**: To balance anisotropic matter entropy flow, the geometric response (area change) must also have the same directional dependence.

    * Scalar gravity causes "volume changes" that are isotropic.

    * Tensor gravity (metric changes) can produce shear and anisotropic focusing.

Only the tensor field $g_{\mu\nu}$ has sufficient degrees of freedom ($d(d+1)/2$ components) to make precise entropic balance responses to energy flow in arbitrary directions. This is why the graviton must be a spin-2 particle.

**Summary**

This section completed the full derivation of Einstein's field equations.

1. **Tensorization**: Using Lorentz covariance, we lifted scalar entropy balance to tensor equations.

2. **Conservation**: We proved the consistency of the equations with energy conservation and geometric identities.

3. **Uniqueness**: We excluded scalar gravity, establishing tensor gravity as the unique low-energy effective theory satisfying the holographic principle.

At this point, we have "derived" general relativity from purely information-theoretic principles (maximum entanglement entropy). This proves: **spacetime geometry is the fluid mechanics of quantum information**.

In the next section 12.3, we will discuss in detail the emergence mechanism of $\Lambda$ as an integration constant.

