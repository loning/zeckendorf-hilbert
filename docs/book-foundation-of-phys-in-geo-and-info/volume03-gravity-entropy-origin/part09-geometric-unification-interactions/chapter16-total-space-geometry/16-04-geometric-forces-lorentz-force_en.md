**16.4 Geometrization of Forces: Lorentz Force as Geodesic Deviation in Total Space**

In Sections 16.1 to 16.3, we constructed the geometric framework of total space, unifying gravity and gauge fields as **unified connection** $\mathbb{A}$ and **unified curvature** $\mathbb{F}$ on total space principal bundle. This pure geometric picture raises a fundamental dynamical question: if physical forces are merely manifestations of geometric curvature, then not only gravity, but all fundamental interactions (electromagnetic, weak, strong) should reduce to **inertial motion**.

This section will prove that in this higher-dimensional total space geometry, there is no concept of "force." All particles—whether charged, colored, or massive—are performing **free geodesic motion**. The "Lorentz force" or "color-electric force" we observe in four-dimensional spacetime is actually projection deviation of total space geodesics onto the base manifold. Electric charge and color charge are merely "momenta" of particles in internal dimensions.

### 16.4.1 Total Space Metric and Kaluza-Klein Ansatz

To describe particle motion, we need to define metric structure on total space $P$. Although topology of $P$ is fiber bundle $M \times G$, its Riemannian geometric structure is determined jointly by base manifold metric $g_{\mu\nu}$, fiber metric $k_{ij}$, and unified connection $\mathbb{A}$.

**Definition 16.4.1 (Total Space Metric / Bundle Metric)**

In local coordinates $(x^\mu, y^i)$ (where $x$ are spacetime coordinates, $y$ are group manifold/internal space coordinates), the line element $ds^2_{total}$ of total space is defined as direct sum of horizontal and vertical parts:

$$
ds^2_{total} = g_{\mu\nu}(x) dx^\mu dx^\nu + \phi^2 k_{ab}(y) (e^a + \mathbb{A}^a_\mu dx^\mu) (e^b + \mathbb{A}^b_\nu dx^\nu)
$$

where:

1. $g_{\mu\nu}$ is four-dimensional Einstein metric.

2. $k_{ab}$ is Killing metric on Lie group $G$, describing geometry of internal space.

3. $\mathbb{A}^a_\mu$ is unified connection (containing spin connection and Yang-Mills potential).

4. $e^a$ is Maurer-Cartan form on group manifold.

5. $\phi$ is scalar field (Dilaton), describing fluctuations of internal space scale (usually frozen to constant in Einstein-Maxwell theory).

This metric ensures "horizontal movement" in total space is orthogonal to "vertical fibers," and definition of horizontal movement is locked to physical gauge fields through $\mathbb{A}$.

### 16.4.2 Dimensional Reduction of Geodesic Equations: Charge Conservation and Force Emergence

Now consider a particle moving along geodesics in total space $P$. Its action is total arc length:

$$
S = \int \sqrt{G_{MN} \dot{X}^M \dot{X}^N} \, d\tau
$$

where $X^M = (x^\mu, y^i)$.

Through variational principle $\delta S = 0$, we obtain geodesic equations in total space:

$$
\frac{D^2 X^M}{d\tau^2} = 0
$$

This means particles in total space are subject to no external forces, only inertia.

**1. Internal Momentum Conservation (Charge Conservation)**

Since metric components $G_{MN}$ are assumed not to explicitly depend on internal coordinates $y^i$ (i.e., have isometry symmetry of group manifold), corresponding conjugate momentum $P_i$ is conserved.

$$
P_i = \frac{\partial L}{\partial \dot{y}^i} = k_{ij} (\dot{y}^j + \mathbb{A}^j_\mu \dot{x}^\mu) = \text{const}
$$

This internal momentum $P_i$ is precisely the physical **gauge charge** (such as electric charge $q$ or color charge $Q^a$).

**Physical Corollary**: **Charge is momentum**. Particles are charged because they rotate or run in internal dimensions.

**2. External Equation of Motion (Lorentz Force)**

Varying spacetime coordinates $x^\mu$ and using internal momentum conservation relation, after tedious but standard Christoffel symbol calculations, the four-dimensional projection of geodesic equations appears as:

$$
\frac{D^2 x^\mu}{d\tau^2} = \lambda g^{\mu\nu} \mathbb{F}^a_{\nu\rho} P_a \frac{dx^\rho}{d\tau}
$$

where $\mathbb{F}^a_{\nu\rho}$ is unified curvature tensor (defined in Section 16.3), $\lambda$ is coupling constant (related to Planck scale).

**Theorem 16.4.1 (Geometric Force Theorem)**

Particles performing free geodesic motion in total space, when viewed by base manifold observers, satisfy motion equations of charged particles:

$$
m \frac{d u^\mu}{d\tau} = q F^{\mu}{}_\nu u^\nu + (\text{non-Abelian correction terms})
$$

That is: **Lorentz force is generalization of Coriolis force in total space**. Particles deviate from straight lines because the local frames (fibers) they inhabit rotate relative to the base manifold (curvature $\mathbb{F} \neq 0$), and particles must produce compensatory acceleration in external space to maintain internal momentum (charge) conservation.

### 16.4.3 Non-Abelian Generalization: Wong's Equations

For non-Abelian gauge groups (such as $SU(2)$ or $SU(3)$), internal momentum $P_a$ (color charge) is no longer constant, because structure constants $f^a_{bc} \neq 0$ cause generators in different directions to not commute.

Complete projection of total space geodesic equations gives **Wong's Equations** describing non-Abelian particle motion:

1. **Trajectory Equation**:

   $$
   \frac{D u^\mu}{d\tau} = \frac{1}{m} P_a F^{a\mu\nu} u_\nu
   $$

2. **Color Charge Precession Equation**:

   $$
   \frac{D P_a}{d\tau} = - f_{abc} A_\mu^b u^\mu P^c
   $$

This shows that in curved internal geometry, **color charge vector $P_a$ undergoes precession during transport**. This is completely analogous to spin vector geodesic precession in curved spacetime in general relativity. Gauge interactions not only change particle trajectories but also change particle internal states.

### 16.4.4 QCA Discrete Ontology: Microscopic Mechanism of Geodesic Deviation

In QCA discrete networks, this geometric picture acquires concrete microscopic interpretation.

Particles are modeled as **excitation packets** on the network, their states described jointly by position $|x\rangle$ and internal register $|\psi_{int}\rangle$.

Single-step update $U$ of QCA contains a **conditional translation** (see Section 4.2):

$$
U |x\rangle \otimes |\psi_{int}\rangle = |x+\Delta x\rangle \otimes (e^{i \mathbb{A} \cdot \Delta x} |\psi_{int}\rangle)
$$

Here $e^{i \mathbb{A}}$ is the connection variable (Link Variable).

**QCA Geodesics**:

The "inertial path" of a particle is the path that extremizes discrete action (phase accumulation).

$$
S[\Gamma] = \sum_{steps} \langle \psi(t) | \psi(t+1) \rangle \sim \sum \text{Phase}
$$

When curvature exists ($\mathbb{F} \neq 0$), phase accumulation differs on different paths.

* **Constructive Interference**: Wave packet center tends to move along phase stationary paths.

* **Phase Gradient**: "Charge" (eigenvalue) carried by internal state $|\psi_{int}\rangle$ determines direction of phase gradient.

* **Result**: Wave packet center undergoes transverse drift. This drift in macroscopic limit is precisely $\Delta x^\mu \sim F^{\mu\nu} u_\nu \Delta \tau$.

**Conclusion 16.4.2**

In QCA universes, there is no such entity as "force."

The "electromagnetic attraction" or "strong force binding" we see are essentially **statistical results of quantum wave packets seeking extremal phase paths in discrete networks with non-trivial holonomy**.

* Charge $q$ is the **wavenumber** (momentum) of wave packets in internal register space.

* Field strength $F$ is the **twist rate** of network connection rules.

* Lorentz force is **refraction** of wave packets in twisted networks to maintain coherence.

At this point, we have completed discussions in Part IX on geometric unification of interactions. Through total space geometry, we proved that gravity and gauge fields are essentially different components of the same geometric structure (unified connection), and all forces are projections of higher-dimensional inertial motion. This clears the way for Part XVII to explore the topological origin of matter itself (particles as knots).

In the upcoming **Chapter 17: Topological Origin of Matter**, we will explore how fermions themselves emerge as topological defects from this geometric structure.

