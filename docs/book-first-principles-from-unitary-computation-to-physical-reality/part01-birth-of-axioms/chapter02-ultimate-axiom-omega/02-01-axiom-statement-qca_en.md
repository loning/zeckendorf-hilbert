# 2.1 Axiom Statement: The Universe is a Quantum Cellular Automaton (QCA) Operating on Discrete Lattice Points Following Local Unitary Evolution Rules

This is the core of this book, and the only foundation stone for constructing the entire edifice of physics.

We will abandon all complex, phenomenological physical assumptions (such as mass, charge, spacetime curvature, wave function collapse, etc.), retaining only the purest computational structure.

> **Ultimate Axiom $\Omega$ (The Axiom of Unitary QCA)**
>
> Physical reality $\Psi$ is equivalent to a quantum information processing system defined on a discrete lattice graph $\Lambda$, following local unitary evolution rules $\hat{U}$.
>
> Formally expressed as a triple $(\Lambda, \mathcal{H}, \hat{U})$:
>
> 1. **State Space ($\Lambda, \mathcal{H}$)**: The universe is a countable graph $\Lambda$, where each node $x \in \Lambda$ is associated with a finite-dimensional complex Hilbert space $\mathcal{H}_x \cong \mathbb{C}^d$ (i.e., qudit). The state space of the entire system is the tensor product of local spaces $\mathcal{H}_{total} = \bigotimes_{x \in \Lambda} \mathcal{H}_x$.
>
> 2. **Evolution Rule ($\hat{U}$)**: The system's evolution with discrete time steps $t \in \mathbb{Z}$ is driven by a global operator $\hat{U}$:
>
>    $$|\Psi(t+1)\rangle = \hat{U} |\Psi(t)\rangle$$
>
> 3. **Constraints**:
>
>    * **Unitarity**: $\hat{U}^\dagger \hat{U} = \mathbb{I}$. This means information (modulus of quantum states) is strictly conserved during evolution, neither created nor destroyed.
>
>    * **Locality**: $\hat{U}$ can be decomposed as a product of local operators $\hat{U} = \prod_{k} \hat{U}_k$ (or its finite-depth circuit), and each $\hat{U}_k$ acts only on finitely many adjacent nodes on $\Lambda$. This means no action at a distance; information propagation speed is limited by lattice connectivity.
>
>    * **Translation Invariance (Homogeneity)** (optional but usually assumed): Evolution rules $\hat{U}_x$ are identical across the entire graph $\Lambda$ (except possible boundary conditions). This corresponds to the universality of physical laws.

---

This axiom seems simple but contains astonishing power. It not only defines what "existence" is (quantum information), but also defines what "change" is (unitary computation).

In the next few sections, we will deeply analyze each clause of this axiom, explaining **why** the universe must be this way, not that way. We will see that these seemingly abstract mathematical requirements actually directly correspond to familiar physical iron laws—conservation of probability, causality, and conservation of energy.

