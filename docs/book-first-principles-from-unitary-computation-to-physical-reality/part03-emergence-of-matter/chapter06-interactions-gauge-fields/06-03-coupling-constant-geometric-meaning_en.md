# 6.3 Geometric Meaning of Coupling Constants: Network Connectivity and Information Leakage Rate

In the standard model of quantum field theory, strengths of fundamental interactions are described by dimensionless **coupling constants** $g$. For example, fine structure constant of electromagnetic interaction $\alpha \approx 1/137$, while $\alpha_s$ of strong interaction is much larger. However, these constants are usually viewed as free parameters set by God, must be determined experimentally.

In QCA discrete ontology, since everything is information processing, "interaction strength" must correspond to some **ratio** or **probability** of information flow. Why is coupling strength between electrons and photons exactly that value?

This section will prove: **Coupling constant $g$ is essentially a geometric measure of QCA network's topological connectivity and information leakage rate.** It measures what proportion of phase information "leaks" into rotation of internal degrees of freedom ($v_{int}$) when information jumps between lattice points ($v_{ext}$).

## 6.3.1 Coupling as Branching Ratio

Consider a single-step unitary evolution operator $\hat{U}$ on QCA. When a particle carrying internal state (such as spin or color charge) moves from node $x$ to $x+1$, it faces two orthogonal evolution directions:

1. **Translation Channel**: Keep internal state unchanged, only change position. This corresponds to free propagation, amplitude $t$.

2. **Rotation Channel**: While moving, acted upon by connection field $U_{x+1, x}$, undergo internal phase rotation or mixing. This corresponds to interaction, amplitude $r$.

Due to unitarity, $|t|^2 + |r|^2 = 1$.

We define **coupling constant** $g$ as ratio (some function) of interaction amplitude to free propagation amplitude:

$$g \sim \frac{|r|}{|t|} \approx \tan \theta_{mix}$$

where $\theta_{mix}$ is mixing angle between translation generator and rotation generator.

**Physical Picture 6.3.1**:

Imagine a beam splitter. When photons pass through, most pass directly (free propagation), small part reflected or polarization changed (interaction). Coupling constant is this beam splitter's "reflectance." In QCA, every lattice connection is such a beam splitter.

## 6.3.2 Geometric Origin: Dimension and Connectivity Number

Why does $g$ take specific values? This depends on underlying lattice geometric structure.

Suppose QCA network is a $D$-dimensional hypercubic lattice. Each node has $2D$ nearest neighbors.

If particles have $N$ internal degrees of freedom (e.g., $SU(N)$ symmetry).

When particles perform one step of random walk, information can choose $2D$ spatial directions, simultaneously $N^2-1$ internal rotation directions (number of Lie algebra generators).

According to **Information Equipartition Hypothesis**, at Planck scale limit high energies, information flow is uniformly distributed among all possible channels.

$$g_{bare}^2 \propto \frac{\text{internal channel number}}{\text{spatial channel number}} = \frac{C_2(G)}{2D}$$

where $C_2(G)$ is quadratic Casimir operator of gauge group, related to group dimension.

This means, **strengths of fundamental interactions are geometrically determined by space dimension and size of internal symmetry groups.**

For example, for $U(1)$ electromagnetic field ($N=1$) in $D=3$ space, channel ratio is small, hence electromagnetic force is weak. For $SU(3)$ color charge ($N=3$) in same space, internal channels dramatically increase, leading to strong interaction.

## 6.3.3 Discrete Interpretation of Renormalization Group Flow: Resolution and Screening

Experimentally observed coupling constants vary with energy scale (resolution), this is **renormalization group (RG) flow**. In QCA, this has an extremely intuitive explanation.

**1. Screening Effect (e.g., QED)**:

When we observe network with low resolution (long wavelength $\lambda \gg a$), we are actually averaging nodes within a large region.

Due to random fluctuations of local phases (quantum noise), coherent rotations in large regions are partially canceled.

**Corollary**: As observation scale increases (energy decreases), effective coupling constant $g_{eff}$ decreases. This corresponds to infrared free behavior of Abelian gauge fields (such as electromagnetic fields).

**2. Anti-screening Effect (e.g., QCD)**:

For non-Abelian fields, connection fields themselves carry charges (gluons carry color). When we zoom out observation scale, nonlinear entanglement networks between connection fields become more complex.

Imagine a fractal network: the farther you look, the more curled details, the larger "surface area," causing effective interaction cross-section to increase.

**Corollary**: As observation scale increases (energy decreases), effective coupling constant $g_{eff}$ increases. This corresponds to **quark confinement** of non-Abelian fields—at long distances, interaction is so strong it cannot be separated.

## 6.3.4 Derivation Conjecture of Fine Structure Constant $\alpha$

Can we calculate $\alpha \approx 1/137.036$?

This requires extremely high-precision QCA lattice models. But in order of magnitude, we can give a heuristic derivation.

Consider a QCA node in 3D space. Its solid angle is $4\pi$.

A particle emitting a photon (interaction) essentially projects information toward one direction in $4\pi$ space.

If lattice points are close-packed, effective channel number relates to geometric factors.

Wyler once proposed a mathematical conjecture based on geometric volume of bounded complex domains:

$$\alpha = \frac{9}{16\pi^3} (\frac{\pi}{5!})^{1/4} \dots$$

In QCA framework, this corresponds to calculating: **geometric probability of homomorphic transmission on a discrete, unitary-satisfying $S^3 \times S^1$ discrete manifold.**

Although there is currently no numerically precise proof, QCA provides the only possible path to finding this "God's number": it is not an arbitrary parameter, but a **combinatorial constant of discrete geometry** (like $\pi$ or $e$).

## 6.3.5 Summary

Coupling constant $g$ is a bridge connecting microscopic discrete structure with macroscopic continuous field theory.

* **Microscopically**, it is **branching ratio** of information between "displacement" and "transformation."

* **Macroscopically**, it manifests as **force** strength.

* **Essentially**, it is **geometric projection** of network topological structure (dimension, connectivity number, group structure).

We feel strong force is stronger than electromagnetic force because in underlying QCA networks, channels for transmitting "color" information are much wider than channels for transmitting "phase" information.

At this point, we have completed Part III "The Emergence of Matter." We have constructed particles (topological knots), mass (impedance), fermions (square root), and interactions (connection fields) from nothing.

Hardware (spacetime) and data (matter) of this cosmic computer are in place. Next, in Part IV, we will explore the most exciting software part—what happens when this computer begins to "observe itself"? Welcome to **The Emergence of Observation**.

