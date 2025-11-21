**Chapter 17: Topological Origin of Matter**

In Chapter 16, we completed the geometrization of "forces," proving that gravity and gauge fields are different components of unified connection $\mathbb{A}$ in total space. Now, we face the most fundamental ontological question in physics: **What is "matter"?**

In standard quantum field theory, matter (fermions) is regarded as excitation fields on spacetime background, with spin and statistics introduced as axioms. But in QCA discrete ontology, spacetime and forces have already dissolved into geometric properties of information networks, so matter cannot be an external entity. If "it from bit," then "particles" must be some **non-trivial structure of the information network itself**.

This chapter proposes **topological matter theory**: elementary particles (especially fermions) are **topological knots** or **solitons** in QCA networks. We will prove that fermions have profound **self-referential** structure—they are closed loops of "self-observation" in spacetime structure.

**17.1 Fermions as Topological Knots: $\mathbb{Z}_2$ Isotopy Classification of Self-referential Scattering Loops**

Why must electrons rotate 720 degrees ($4\pi$) to return to their original state? Why cannot two electrons occupy the same state (Pauli exclusion)? These fermion-specific properties are extremely bizarre in classical intuition.

This section will reveal the topological origin of fermions through the **Self-referential Scattering Network (SSN)** model. We will prove that fermions are not point particles, but **Möbius strip**-like topological defects on spacetime manifolds. This structure endows them with a topologically protected $\mathbb{Z}_2$ index, which gives them their "indestructible" materiality.

#### 17.1.1 From Open Strings to Closed Loops: Network Definition of Particles

In QCA networks, free propagation of information corresponds to massless waves (such as photons). To form massive, localized "particles," information flow must be **bound** within a finite region.

The simplest binding mechanism is **feedback**.

**Definition 17.1.1 (Self-referential Scattering Network / SSN)**

Consider a local scattering node $S$ with $N$ inputs and $N$ outputs. If we reconnect some output ports back to its own input ports through the spacetime network, forming a closed loop, this structure is called a **self-referential scattering network**.

Mathematically, using Redheffer star product, the effective scattering matrix $S_{eff}$ of the system is determined by original matrix $S$ and feedback connection matrix $F$:

$$
S_{eff} = S \star F
$$

For a single-particle state, the simplest self-referential structure is a single loop: the particle continuously "chases its own tail" at microscopic scales. This high-frequency microscopic circulation manifests macroscopically as particle **rest mass** (Zitterbewegung frequency).

#### 17.1.2 Topological Classification: $\mathbb{Z}_2$ Spectral Flow Index

Not all closed loops can form stable particles. Most loops are unstable (resonance states). Only loops with **non-trivial topology** can gain stability.

Consider a family of SSNs in parameter space (e.g., momentum space or control parameter manifold $\mathcal{M}$). As parameter $\lambda$ varies along closed path $\gamma$, internal states of SSN undergo evolution.

**Definition 17.1.2 (Self-referential Holonomy Index)**

For a self-referential loop, we define its **mod-2 holonomy index** $\nu \in \mathbb{Z}_2$:

$$
\nu(\gamma) = \frac{1}{\pi} \oint_\gamma \text{Tr}(\mathcal{A}_{Berry}) \pmod 2
$$

Or more intuitively, through **spectral flow**:

Consider effective Hamiltonian $H(\lambda)$ of SSN. When $\lambda$ goes around once, the parity of number of eigenvalues crossing the Fermi surface (zero energy level) is $\nu$.

* **$\nu = 0$ (trivial class)**: Wave function phase changes by integer multiples of $2\pi$. State completely recovers when returning to origin. This corresponds to **bosons** or vacuum fluctuations. This structure can be continuously deformed to "nothing," i.e., can be untied or annihilated.

* **$\nu = 1$ (non-trivial class)**: Wave function phase changes by odd multiples of $\pi$ (e.g., $\pi, 3\pi$). When returning to origin, state becomes $-|\psi\rangle$. This corresponds to **fermions**.

#### 17.1.3 Möbius Topology and $4\pi$ Rotation Symmetry

What is the topological meaning of $\nu=1$?

This is equivalent to constructing a **Möbius strip** on the fiber bundle of parameter space.

Imagine a particle carrying an internal reference frame (frame).

* For bosons (trivial loops), moving around a closed path once, the frame returns to original position (0 or 360 degree rotation).

* For fermions (knotted loops), moving around a closed path once, the frame flips (180 degree rotation). This is like walking around a Möbius strip once, a person becomes inverted.

**Theorem 17.1.3 (Spin-Topology Correspondence)**

SSN structures with $\mathbb{Z}_2$ topological index $\nu=1$ necessarily acquire phase factor $-1$ under spatial rotation $2\pi$. Only rotation $4\pi$ (two full turns) can untie this topological knot, returning phase to $+1$.

**Proof Outline**:

Using the **Null-Modular double cover** structure established in Chapter 10. Fermions are objects defined on double cover space $\widetilde{\mathcal{M}}$. Spatial rotation $R(2\pi)$ corresponds to path from sheet $A$ to sheet $B$ on $\widetilde{\mathcal{M}}$. Only $R(4\pi)$ constitutes a closed loop on $\widetilde{\mathcal{M}}$.

This geometric picture intuitively explains the essence of spinors: **spinors are not vectors, they are space geometry "twisted by half"**.

#### 17.1.4 Stability of Matter: Topological Protection

Why are protons and electrons so stable, not arbitrarily absorbed or emitted like photons?

Because fermions are **topological solitons**.

In QCA networks, creating a fermion is equivalent to tying a "knot" on flat background fabric.

* You cannot remove a knot through local operations unless cutting the knot (high-energy destruction) or introducing an opposite knot (antiparticle) to annihilate with it.

* $\mathbb{Z}_2$ index is discrete. Small environmental noise or interactions can only cause small parameter deformations, unable to change discrete topological number.

**Conclusion 17.1.4 (Matter as Knots)**

Matter is not material filling spacetime, but **topological entanglement of spacetime structure itself**.

* Vacuum is smooth (no knots).

* Particles are localized, self-referential, topologically protected $\mathbb{Z}_2$ knots.

* Mass is the energy cost (or information processing frequency) of maintaining this knot's existence.

This discovery completes the final piece of ontology: **information (bits) forms topological structures (knots) through self-referential loops (feedback), thereby emerging as hard matter (fermions)**.

