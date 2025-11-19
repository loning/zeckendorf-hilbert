# Volume II: The Emergence of Time —— Scattering, Thermodynamics, and Dynamics

## Part IV: Microscopic Operator Definition of Time

### Chapter 6: Scattering Time Delay Theory

**6.1 The Time Problem in Quantum Mechanics: Pauli's Theorem and the Nonexistence of Self-Adjoint Time Operators**

In the previous volume, we established a discrete QCA ontology that does not include the continuous time parameter $t$. However, in quantum mechanics (QM) and quantum field theory (QFT) in the macroscopic continuous limit, time plays a unique and perplexing role. This section will rigorously examine the mathematical status of "time" from the standard quantum mechanics formalism and prove through Pauli's Theorem that in Hilbert space, there does not exist a universal self-adjoint time operator conjugate to the Hamiltonian. This negative conclusion forces us to turn our attention to scattering processes, seeking an **operational definition** of time.

#### 6.1.1 The Anomaly of Time as a Parameter

In classical mechanics, position $q$ and momentum $p$ are dynamical variables in phase space, while time $t$ is both an evolution parameter and can be viewed as a variable conjugate to energy $E$ through the symplectic form. But in standard quantum mechanics, this symmetry is broken:

1.  **Position and Momentum**: Described by self-adjoint operators $\hat{x}$ and $\hat{p}$, satisfying the canonical commutation relation $[\hat{x}, \hat{p}] = i\hbar \mathbb{I}$. They possess orthonormal eigenstates and follow the uncertainty principle $\Delta x \Delta p \ge \hbar/2$.

2.  **Time and Energy**: Energy is described by the Hamiltonian operator $\hat{H}$, but time $t$ is merely an **external parameter** (c-number), marking the evolution steps of the Schrödinger equation $i\hbar \partial_t |\psi(t)\rangle = \hat{H} |\psi(t)\rangle$.

Although Heisenberg proposed the energy-time uncertainty relation $\Delta E \Delta t \ge \hbar/2$, here $\Delta t$ is not the standard deviation of an operator, but rather refers to the characteristic evolution time of the system (e.g., lifetime). Physicists attempted to introduce a "time operator" $\hat{T}$ such that $[\hat{H}, \hat{T}] = -i\hbar \mathbb{I}$, thereby restoring time and energy as fully symmetric conjugate quantities. Pauli proved in 1933 that this attempt is doomed to fail for any physically reasonable system.

#### 6.1.2 Rigorous Statement and Proof of Pauli's Theorem

**Theorem 6.1.1 (Pauli's Theorem, 1933)**

Let $\hat{H}$ be a self-adjoint Hamiltonian operator on Hilbert space $\mathcal{H}$. If there exists a self-adjoint operator $\hat{T}$ (time operator) such that they satisfy the canonical commutation relation:

$$[\hat{H}, \hat{T}] = i\hbar \mathbb{I}$$

(valid on a dense domain), then the spectrum $\sigma(\hat{H})$ of $\hat{H}$ must cover the entire real axis $\mathbb{R} = (-\infty, +\infty)$. In other words, $\hat{H}$ cannot have a lower bound (ground state), which contradicts the stability of physical systems.

**Proof**:

We adopt the generator method of operator groups for the proof.

1.  **Constructing the Translation Operator**:

    Since $\hat{T}$ is self-adjoint, according to Stone's Theorem, it generates a unitary operator group:

    $$\hat{U}_\varepsilon = \exp\left( -\frac{i}{\hbar} \varepsilon \hat{T} \right), \quad \varepsilon \in \mathbb{R}$$

    

2.  **Examining the Commutation Relation**:

    Consider the commutation relation between $\hat{H}$ and $\hat{U}_\varepsilon$. Using the Baker-Campbell-Hausdorff (BCH) formula or the series expansion of the commutator:

    $$[\hat{H}, \exp(\hat{A})] = [\hat{H}, \hat{A}] \exp(\hat{A})$$

    (if $[\hat{H}, \hat{A}]$ commutes with $\hat{A}$).

    Here, let $\hat{A} = -\frac{i}{\hbar} \varepsilon \hat{T}$. From the assumption $[\hat{H}, \hat{T}] = i\hbar \mathbb{I}$, we obtain:

    $$\left[\hat{H}, -\frac{i}{\hbar} \varepsilon \hat{T}\right] = -\frac{i}{\hbar} \varepsilon (i\hbar \mathbb{I}) = \varepsilon \mathbb{I}$$

    Since $\varepsilon \mathbb{I}$ commutes with any operator, the above BCH series truncates at the first term. Therefore:

    $$[\hat{H}, \hat{U}_\varepsilon] = \varepsilon \hat{U}_\varepsilon \implies \hat{H} \hat{U}_\varepsilon - \hat{U}_\varepsilon \hat{H} = \varepsilon \hat{U}_\varepsilon \implies \hat{H} \hat{U}_\varepsilon = \hat{U}_\varepsilon (\hat{H} + \varepsilon \mathbb{I})$$



3.  **Translation of the Spectrum**:

    Let $|\psi_E\rangle$ be an eigenstate (or generalized eigenstate) of $\hat{H}$ with eigenvalue $E$:

    $$\hat{H} |\psi_E\rangle = E |\psi_E\rangle$$

    Acting $\hat{H}$ on the state $\hat{U}_\varepsilon |\psi_E\rangle$:

    $$\hat{H} (\hat{U}_\varepsilon |\psi_E\rangle) = \hat{U}_\varepsilon (\hat{H} + \varepsilon \mathbb{I}) |\psi_E\rangle = \hat{U}_\varepsilon (E + \varepsilon) |\psi_E\rangle = (E + \varepsilon) (\hat{U}_\varepsilon |\psi_E\rangle)$$

    This shows that as long as $E$ is a point in the spectrum, $(E+\varepsilon)$ must also be in the spectrum. Since $\varepsilon$ can take any real value, this means the spectrum of $\hat{H}$ must be translation-invariant, i.e., $\sigma(\hat{H}) = \mathbb{R}$.



$\square$

#### 6.1.3 Physical Meaning: Ground State Existence and the Non-Operator Nature of Time

Pauli's theorem reveals a profound conflict in the structure of quantum mechanics:

* **Stability Requirement**: Any stable physical system must have a lower energy bound (ground state energy $E_0 > -\infty$). Otherwise, the system would infinitely transition to lower energy levels and release energy, leading to a "perpetual motion machine of the first kind" catastrophe.

* **Operator Requirement**: If time is a fundamental operator like position, its conjugate momentum (energy) must take values on the entire real axis $(-\infty, +\infty)$ like linear momentum.

Since not only atoms and molecules exist stably, but our QCA universe model is also based on finite information (implying finite energy density), **the spectrum of physical Hamiltonians must necessarily have a lower bound**.

**Corollary 6.1.2**: In any Hamiltonian system with a lower bound, there does not exist a universal, self-adjoint "time operator." "Time" cannot be defined as an observable in Hilbert space.

This also explains why in quantum gravity attempts (such as the Wheeler-DeWitt equation $\hat{H}\Psi = 0$), the time variable completely disappears (the "frozen time" problem). Because once we elevate time to an operator and make it commute with the Hamiltonian, the system's dynamical structure collapses.

#### 6.1.4 Solution Path: From Parameter Time to Scattering Time

Since there is no a priori "absolute time operator," how do we define the duration of microscopic processes? For example, how long does it take for a particle to tunnel through a potential barrier?

The answer lies in **operationalism**. We do not seek an abstract $t$, but rather measure the **delay** of one physical event relative to another. In microscopic physics, the most fundamental process is **scattering**.

* **Input**: Particle incident from infinity at $t \to -\infty$ (free state $\psi_{in}$).

* **Interaction**: Particle enters the scattering region (black box), undergoing complex quantum interference.

* **Output**: Particle leaves at $t \to +\infty$ (free state $\psi_{out}$).

Although we cannot define a clock inside the interaction region, we can compare the **phase shift** of $\psi_{out}$ relative to a non-interacting reference wave packet. The derivative of this phase shift with respect to energy, as we will see in the next section, precisely defines a physical quantity with time dimension—**Wigner-Smith time delay**.

**Definition 6.1.3 (Emergent Perspective of Time)**

In the framework of this book, time $t$ is not a fundamental background manifold coordinate, but rather a **statistical property of scattering processes**.

$$
\text{Time} \equiv \text{rate of change of phase with respect to energy}
$$

This viewpoint not only avoids the limitations of Pauli's theorem (because the scattering operator $S$ is unitary and defined on the energy shell, there is no need to introduce a global time operator), but also directly leads to the holographic principle and the entropic origin of gravity. The following chapters will construct this operator definition of microscopic time.

