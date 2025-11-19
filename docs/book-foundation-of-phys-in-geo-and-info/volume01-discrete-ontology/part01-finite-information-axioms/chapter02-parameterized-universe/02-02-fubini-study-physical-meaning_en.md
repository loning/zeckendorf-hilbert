**2.2 Distance Defined by Distinguishability: Physical Meaning of Fubini-Study Metric**

In Section 2.1, we mathematically derived the Riemannian metric of parameterized quantum state space—Quantum Fisher Information Metric (QFIM)—through perturbation expansion. However, physics is not just mathematical formal derivation; it also needs to endow mathematical objects with clear operationalist meaning. This section will deeply explore the physical essence of this metric: it is not an artificially defined "ruler," but a geometric structure uniquely determined by the fundamental physical property of quantum states—**Statistical Distinguishability**.

### 2.2.1 Operational Limits of Distinguishability

In classical physics, two points (states) in phase space can in principle be distinguished with infinite precision. But in quantum mechanics, due to the probabilistic nature of measurement collapse, distinguishing two non-orthogonal states $|\psi\rangle$ and $|\phi\rangle$ becomes a statistical inference problem.

**Definition 2.2.1 (Helstrom Bound)**

Consider a single measurement task: the system is in state $|\psi\rangle$ or $|\phi\rangle$ with equal probability. We need to choose optimal measurement operators (POVM) $\{E_\psi, E_\phi\}$ to determine which state the system is in. According to quantum detection theory, the minimum error probability $P_{\text{err}}$ is given by Helstrom bound:

$$
P_{\text{err}} = \frac{1}{2} \left( 1 - \sqrt{1 - |\langle \psi | \phi \rangle|^2} \right)
$$

This shows that the modulus square of inner product $|\langle \psi | \phi \rangle|^2$ (i.e., fidelity $F^2$) directly determines the limiting ability to distinguish two quantum states.

**Physical Interpretation**:

If we define "distance" as "difficulty of distinguishing two states," then distance should be a monotonically decreasing function of error probability. When $P_{\text{err}} = 0$ (orthogonal states), distance is maximum; when $P_{\text{err}} = 1/2$ (coincident states), distance is zero. This provides a solid operational foundation for introducing geometric metric on projective Hilbert space $\mathbb{C}P^{N-1}$.

### 2.2.2 Wootters Distance: Origin of Statistical Geometry

In 1981, W. K. Wootters raised a profound question: **"What is the distance between two points in quantum state space?"** He gave a geometric interpretation of statistical distance by calculating the number of distinguishable states.

Consider two quantum states $|\psi_1\rangle$ and $|\psi_2\rangle$, with probability distributions $p^{(1)}_i$ and $p^{(2)}_i$ respectively under some measurement basis. In classical statistical theory, the natural distance for distinguishing two probability distributions is Fisher Information Distance, whose integral form corresponds to great circle arc length between two points on a sphere:

$$
d_{\text{stat}}(p^{(1)}, p^{(2)}) = \arccos \left( \sum_i \sqrt{p^{(1)}_i p^{(2)}_i} \right)
$$

Wootters proved that if we want to define a metric in Hilbert space such that this metric equals the classical statistical distance induced under **optimal measurement**, then this metric must be Fubini-Study Distance.

**Theorem 2.2.2 (Wootters Theorem)**

The geodesic distance $s(\psi, \phi)$ between any two states $|\psi\rangle$ and $|\phi\rangle$ on projective Hilbert space $\mathbb{C}P^{N-1}$ is uniquely determined by the arccosine of their inner product modulus square:

$$
s(\psi, \phi) = \arccos \big| \langle \psi | \phi \rangle \big|
$$

This distance exactly corresponds to the statistical distance between probability distributions they produce under optimal measurement basis.

**Proof Outline**:

For any two pure states, we can always find a two-dimensional subspace (spanned by them) such that within this subspace they can be represented as two points on Bloch Sphere. The natural metric on Bloch Sphere is the Fubini-Study metric on $\mathbb{C}P^1$. In this representation, if the angle between two states is $\theta$, then $|\langle \psi | \phi \rangle| = \cos(\theta/2)$. Geometric distance (great circle arc length) is $\theta/2$ (if normalized radius is $1/2$) or $\theta$ (if normalized radius is 1). Standard Fubini-Study metric usually takes half of sphere geometry with radius 1, i.e., $s = \arccos |\langle \psi | \phi \rangle| \in [0, \pi/2]$. Distance between orthogonal states is $\pi/2$. $\square$

### 2.2.3 Geodesics on Projective Space and Quantum Speed Limit

The core of Riemannian geometry lies in **Geodesics**—shortest paths connecting two points on a manifold. On $\mathbb{C}P^{N-1}$, geodesics determined by Fubini-Study metric have extremely important dynamical significance.

Consider quantum evolution $|\psi(t)\rangle$ driven by time-dependent Hamiltonian $H(t)$. According to Schrödinger equation $i\hbar \frac{d}{dt}|\psi\rangle = H|\psi\rangle$, we can calculate the rate at which state moves on $\mathbb{C}P^{N-1}$.

**Theorem 2.2.3 (Aharonov-Anandan Relation)**

The instantaneous velocity $v(t)$ of quantum evolution in projective Hilbert space is proportional to the system's energy uncertainty (energy fluctuation):

$$
v(t) = \frac{ds}{dt} = \frac{\Delta E(t)}{\hbar}
$$

where $\Delta E(t) = \sqrt{\langle \psi | H^2 | \psi \rangle - \langle \psi | H | \psi \rangle^2}$.

**Corollary 2.2.4 (Mandelstam-Tamm Bound)**

Combining the definition of geodesic (shortest path between two points), the minimum time $\tau$ required to evolve from initial state $|\psi(0)\rangle$ to final state $|\psi(\tau)\rangle$ must satisfy:

$$
\tau \ge \frac{\hbar}{\overline{\Delta E}} s(\psi(0), \psi(\tau)) = \frac{\hbar \arccos|\langle \psi(0) | \psi(\tau) \rangle|}{\overline{\Delta E}}
$$

where $\overline{\Delta E}$ is the time-averaged energy uncertainty.

**Physical Meaning**:

This conclusion reveals the dynamical essence of Fubini-Study metric: **it is the "resistance" of quantum evolution**. To change the state of a physical system (making it distinguishable from other states), we must consume "energy fluctuation" as a resource. If energy fluctuation is zero (eigenstate), then $\Delta E = 0$, evolution velocity is zero, system is stationary in projective space (only overall phase change with no physical meaning). Therefore, geometric distance $s$ gives the **Quantum Speed Limit (QSL)** for evolution of physical processes.

### 2.2.4 "Rigidity" of Quantum Mechanics: Holomorphic Sectional Curvature

Finally, we explore curvature properties determined by $g_{\mu\nu}$. Riemannian curvature describes non-commutativity when parallel transporting vectors, or the "curvature" degree of space.

For projective Hilbert space $\mathbb{C}P^{N-1}$, its Riemann curvature tensor $R_{\mu\nu\rho\sigma}$ has a very special structure. In particular, its **Holomorphic Sectional Curvature** is constant.

**Proposition 2.2.5 (Constant Curvature Property)**

$\mathbb{C}P^{N-1}$ under Fubini-Study metric is an Einstein Manifold with positive, constant holomorphic sectional curvature $K = 4$ (under appropriate normalization).

This constant curvature has profound physical meaning, often called **Rigidity of Quantum Mechanics**. It means:

1. **Universality**: Regardless of the specific Hamiltonian of physical systems, whether systems consist of electrons, photons, or quarks, as long as they follow quantum mechanics, the geometric structure of their state space is completely identical $\mathbb{C}P^{N-1}$, with the same curvature radius.

2. **Geometric Origin of Non-local Correlations**: Just as gravity in general relativity arises from spacetime curvature, entanglement and non-local correlations in quantum mechanics (such as violation of Bell inequalities) can also be seen as direct consequences of non-flat geometry of high-dimensional projective space. In flat Euclidean space, Bell inequalities hold; but in $\mathbb{C}P^{N-1}$ with constant positive curvature, quantum correlations exceed limitations of classical statistical geometry.

**Summary**

Fubini-Study metric $g_{\mu\nu}$ is far from an abstract mathematical definition.

* From **Information Theory** perspective, it is the statistical distance for distinguishing two physical realities.

* From **Dynamics** perspective, it is the energy cost limiting physical evolution speed.

* From **Geometry** perspective, it is the constant curvature structure defining universal rigidity of quantum mechanics.

This trinity (statistical-dynamical-geometric) unification is precisely the core power of "information geometry" as a foundational theory of physics. It tells us that geometry not only describes spacetime, but also describes dynamical constraints of information evolution itself. In the next section, we will see how the imaginary part of this geometric structure—symplectic structure—naturally leads to gauge fields and geometric phases.

