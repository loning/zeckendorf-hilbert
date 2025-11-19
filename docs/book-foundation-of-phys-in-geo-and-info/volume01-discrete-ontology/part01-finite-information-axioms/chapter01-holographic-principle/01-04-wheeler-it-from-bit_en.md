**1.4 Wheeler's "It from Bit" and the Ontological Status of Quantum Information**

In the first three sections, we established the finiteness of physical reality (finite information axiom) and the failure of continuum hypothesis at Planck scale (natural cutoff). At this point, we face a fundamental ontological question: if the foundation of the physical world is not continuous spacetime geometry, nor "material entities" in infinite-dimensional field theory, then what does it consist of?

This section will introduce John Archibald Wheeler's "It from Bit" idea and elevate it from a philosophical conjecture to a strict ontological proposition of discrete quantum physics. We will argue that quantum information is not a "description" of physical reality, but the "essence" of physical reality.

### 1.4.1 Endpoint of Physical Reductionism: From Matter to Information

The history of physics development is a history of continuously stripping away appearances and seeking deeper invariants. Atomism reduced matter to particles; quantum field theory reduced particles to field excitations; general relativity reduced gravity to spacetime geometry. However, Bekenstein bound (Section 1.1) and finiteness theorem (Section 1.2) suggest a deeper level of reduction: **geometry itself is emergent**.

Wheeler proposed the famous statement in 1989: "It from Bit." He pointed out:

> "Every particle, every field force, even the spacetime continuum itself, its function, its meaning, its existence, ultimately derives entirely from binary choices to 'yes or no' questions."

This statement acquires precise mathematical meaning in our finite Hilbert space framework.

**Proposition 1.4.1 (Ontological Equivalence of Information)**:

Let physical system $\mathcal{S}$ correspond to finite-dimensional Hilbert space $\mathcal{H}_{\mathcal{S}}$ with dimension $D = 2^N$. Then any pure state $|\psi\rangle$ of system $\mathcal{S}$ is physically equivalent to a state of a register composed of $N$ quantum bits (Qubits). All physical properties (observables) of the system can be mapped to logical operations on these $N$ qubits.

Therefore, **"existing" as a physical object is equivalent to "possessing a specific set of quantum information"**.

---

### 1.4.2 Duality of Measurement and Participatory Universe

In classical physics, we are accustomed to thinking that objects possess "properties" (such as position, momentum) independent of observation. But in quantum mechanics, Bohr and Heisenberg already pointed out that physical quantities are only defined in measurement contexts. Wheeler further deepened this, proposing the concept of **Participatory Universe**.

**Definition 1.4.2 (Elementary Quantum Event)**:

The minimum unit of physical reality is not a "spacetime point," but an **elementary quantum event**. This is not only a recording process, but also an **actualization** process. An elementary event corresponds to a measurement of a rank-1 projection operator $P = |\phi\rangle\langle\phi|$ on Hilbert space $\mathcal{H}$, with result "yes (1)" or "no (0)".

Each measurement (question) extracts a definite bit (reality) from potential possibilities (superposition states). Without this interaction of questions and answers, there is no so-called "physical reality."

**Corollary 1.4.3 (Physicality of Information)**:

Information is not an abstract, immaterial concept. Landauer's Principle shows that erasing 1 bit of information requires consuming at least $k_B T \ln 2$ energy. In our framework, this principle is bidirectional:

1. Processing information requires physical resources (energy).

2. Physical entities (energy/mass) are essentially concretizations of information. $E = mc^2$ can be seen as a dual expression of $I = E / \rho_{\text{info}}$, where $\rho_{\text{info}}$ is Planck information density.

---

### 1.4.3 Ontological Status of Quantum Information: State Vector as "Knowledge Catalog"

If the world originates from bits, then what is the wave function $|\psi\rangle$ in quantum mechanics? Under the "It from Bit" perspective, $|\psi\rangle$ is not a physical wave oscillating in three-dimensional space, but a **complete catalog of information contained in the system**.

Consider a system of dimension $D$.

* **Classical Perspective**: System is in one of $D$ mutually exclusive states. Information content is $\log_2 D$ bits.

* **Quantum Perspective**: System is in a vector state in $\mathbb{C}^D$.

    $$|\psi\rangle = \sum_{i=0}^{D-1} c_i |i\rangle, \quad \sum |c_i|^2 = 1$$

    Here, $c_i$ is not the density of some fluid, but **probability amplitude**.

**Theorem 1.4.4 (Information Completeness of Quantum States)**:

In a universe following finite information axiom, pure state $|\psi\rangle$ is the maximum possible information summary of all interaction history of the system. For any future measurement operator $\hat{A}$, although results are unpredictable (probabilistic), $|\psi\rangle$ provides complete information to calculate the probability distribution $P(a) = |\langle a|\psi\rangle|^2$. Beyond $|\psi\rangle$, there are no more fundamental "hidden variables" to determine reality.

**Proof Outline**:

Based on Bell's Theorem and Kochen-Specker Theorem. Any attempt to assign "real properties" beyond $|\psi\rangle$ (such as local hidden variables) will lead to contradictions with quantum mechanical predictions or non-contextuality. Therefore, information (wave function) itself is the most fundamental reality. $\square$

This shows that **quantum uncertainty does not arise from lack of information, but from transformation of information**. When we measure between incompatible bases (such as position and momentum), we are actually asking the system to transform information encoded in one form into another form, and this transformation process is constrained by Heisenberg uncertainty.

---

### 1.4.4 Holographic Reconstruction: From Bits to Geometry

The deepest implication of "It from Bit" is that since spacetime geometry is derivative, it must be reconstructible from underlying quantum information structures. This will be detailed in Chapter 2 "Parameterized Universe and Information Geometry" of this book; here we only give the core logic.

**Definition 1.4.5 (Geometry as Entanglement)**:

If physical space consists of discrete quantum subsystems (cells), then the "geometric distance" between two regions $A$ and $B$ is not an a priori given metric $g_{\mu\nu}$, but defined by their **mutual information** or **entanglement**:

$$d(A, B) \sim -\ln \frac{I(A:B)}{I_{\max}}$$

Highly entangled subsystems are geometrically "nearby"; unentangled subsystems are "distant."

This viewpoint is currently strongly supported in holographic entanglement entropy (Ryu-Takayanagi Formula) and ER=EPR conjecture. It explains why finite information axiom (Section 1.2) and natural cutoff (Section 1.3) can lead to general relativity: because gravity itself is a macroscopic thermodynamic manifestation of quantum information entanglement.

### 1.4.5 Summary: Ontological Foundation of Part I

At this point, we have completed the construction of Chapter 1 of Part I of this book. We have established a logically rigorous ontological chain:

1. **Bound**: Bekenstein bound reveals finiteness of information capacity of physical systems (1.1).

2. **Finiteness**: This bound forces physical Hilbert space to be finite-dimensional (1.2).

3. **Discreteness**: Finite-dimensional space means continuous spacetime is only an effective approximation; natural cutoff exists at Planck scale (1.3).

4. **Essence**: Under this discrete finite framework, the essence of physical reality is quantum information (Qubits); matter and geometry both emerge from this (1.4).

On this new foundation, we will introduce mathematical tools—information geometry and Riemannian structure—in subsequent chapters to derive the familiar, curved macroscopic spacetime.

