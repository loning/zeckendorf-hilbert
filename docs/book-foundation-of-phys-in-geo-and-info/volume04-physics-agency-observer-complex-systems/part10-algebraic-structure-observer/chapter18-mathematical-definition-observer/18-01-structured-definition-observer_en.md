# Volume IV: Physics of Agency — Observers and Complex Systems

## Part X: Algebraic Structure of Observers

### Chapter 18: Mathematical Definition of Observers

In the first three volumes, we constructed a grand picture of the physical universe: continuous spacetime geometry and matter fields emerging from discrete QCA information ontology. However, this picture has been missing a key character—the **Observer**.

In standard physics, observers are usually simplified to abstract reference frame origins ($x=0$) or idealized measurement instruments. But in deep contradictions between quantum mechanics and general relativity, and in discussions involving cosmological horizons or black hole information, we find that "who is looking" and "how they look" determine the form of physical reality.

This chapter will sink "observer" from a metaphysical concept to a rigorous physical entity. We will use operator algebra and cybernetics language to give a structured definition of observers. We will prove that observers are not merely worldlines in spacetime, but open quantum systems capable of maintaining their own low-entropy states, with **Internal Algebraic Structure** and **Memory**.

**18.1 From Reference Frame Origin to Physical Entity: Structured Definition of Observers**

Physical laws are usually expressed as objective truths independent of observers (covariance). However, verification of any physical theory depends on observers' ability to extract information. In QCA discrete ontology, observers themselves are **subsystems** in the network. This section will define the mathematical structure of observers, distinguishing them from the environment.

#### 18.1.1 Limitations of Traditional Definitions: Ghost Observers

In classical mechanics and special relativity, observers are equated with **reference frames**.

* **Definition**: An observer $\mathcal{O}$ is defined by a timelike worldline $\gamma(\tau)$ and a set of orthogonal frames $e_a^\mu(\tau)$ along that line.

* **Limitations**: This definition is purely geometric and passive. It assumes observers have no mass, no volume, do not react back on the system, and have infinite measurement precision and memory capacity. This is unacceptable at the quantum gravity level (e.g., infinite precision measurements require infinite energy, collapsing into black holes).

In quantum mechanics, observers are defined by von Neumann as **measurement apparatus**, whose interaction with the system causes wave packet collapse.

* **Limitations**: This introduces the notorious "Heisenberg cut," artificially dividing quantum systems from classical observers, and does not define the physical dynamics of observers themselves.

#### 18.1.2 Algebraic Construction of Observers: Five-Tuple Definition

To intrinsically define observers in QCA universe $\mathfrak{U} = (\Lambda, \mathcal{A}, U)$, we must regard them as a **substructure** of the total algebra $\mathcal{A}$.

**Definition 18.1.1 (Physical Observer)**

A physical observer $\mathfrak{O}$ is a five-tuple structure:

$$
\mathfrak{O} = (\gamma, \mathcal{A}_{\text{int}}, H_{\text{self}}, \mathcal{M}_{\text{mem}}, \Phi_{\text{update}})
$$

where:

1. **World Tube $\gamma$**: The spacetime support set of the observer in the QCA network. Unlike a geometric point, this is a "tubular" region with finite spatial volume $\mathcal{V}$, containing all lattice points constituting the observer.

2. **Internal Algebra $\mathcal{A}_{\text{int}}$**: A subalgebra of local operator algebra $\mathcal{A}_{\gamma} \subset \mathcal{A}$ defined on $\gamma$. It represents **internal degrees of freedom** that the observer can directly control and read (such as brain neuron states or chip registers).

3. **Self Hamiltonian $H_{\text{self}}$**: A local operator driving evolution of $\mathcal{A}_{\text{int}}$. It is responsible for maintaining structural stability of the observer (resisting environmental thermal noise decoherence), defining the observer's **intrinsic time**.

4. **Memory System $\mathcal{M}_{\text{mem}}$**: A protected subspace in $\mathcal{A}_{\text{int}}$ for stably storing information extracted from the environment (low-entropy states).

5. **Perception-Update Mapping $\Phi_{\text{update}}$**: Describes interaction between the observer and environmental boundary $\partial \gamma$. It is a completely positive trace-preserving map (CPTP Map), converting environmental input into internal memory updates.

#### 18.1.3 Physical Boundary: Markov Blanket and Holographic Screen

How does an observer distinguish itself from the rest of the universe? In statistical mechanics, this is defined through the **Markov Blanket**.

**Definition 18.1.2 (Holographic Boundary)**

The observer's boundary $\mathcal{B} = \partial \gamma$ is an **information interface** in the QCA network.

* **Input Ports**: Environmental information flow $J_{in}$ crosses the boundary into $\mathcal{A}_{\text{int}}$.

* **Output Ports**: The observer exerts back-action on the environment by operating boundary operators $J_{out}$.

* **Shielding Property**: Given boundary state $\rho_{\mathcal{B}}$, observer internal state $\rho_{\text{int}}$ and external environment state $\rho_{\text{ext}}$ are **statistically independent** (conditional mutual information is zero).

This boundary geometrically corresponds to the **causal diamond horizon** we discussed in Chapter 11. For the observer, its "subjective world" is the **causal complement** enclosed by this boundary.

The holographic principle here manifests as: **the observer's maximum information processing capacity is limited by the physical area of its boundary** ($I_{max} \propto \text{Area}(\mathcal{B}) / 4G$). A finite-volume observer can only possess finite knowledge.

#### 18.1.4 Negative Entropy Flow and Life Characteristics

The key distinguishing feature of physical observers from dead matter is their **Agency**. A stone also has boundaries and internal algebra, but it is not an observer. Observers must be able to **resist the second law of thermodynamics**, maintaining their own low-entropy states.

**Theorem 18.1.3 (Schrödinger-Wiener Condition)**

A physical entity $\mathfrak{O}$ can be called an "observer" or "agent" if and only if its dynamics satisfies an **information thermodynamic cycle**:

1. **Measurement**: Consume free energy, extract information from environment, reduce uncertainty about environment (entropy decrease).

2. **Erasure**: According to Landauer's principle, discharge processed waste heat (high-entropy noise) back to environment, reset memory system.

3. **Homeostasis**: Under long-time average, internal entropy $S(\mathcal{A}_{\text{int}})$ remains at levels far below thermal equilibrium.

This shows that observers are not just geometric points, but **dissipative structures**. In QCA universes, observers manifest as **local inverse entropy flow vortices**.

**Physical Corollary**:

This structured definition transforms the quantum measurement problem into an interaction problem. Measurement is not mysterious wave function collapse, but **entanglement transfer** between environmental degrees of freedom (measured system) and observer internal degrees of freedom (memory) at the boundary. An observer "seeing" a result means this information is stably inscribed in $\mathcal{M}_{\text{mem}}$ and topologically protected from being washed away by environmental noise.

**Summary**

This section completed the physical definition of observers.

1. **Entity-ization**: Observers are local subsystems $\mathcal{A}_{\text{int}}$ in QCA networks.

2. **Boundary-ization**: Isolated from environment through holographic screens (Markov blankets).

3. **Dynamical-ization**: Maintain memory and negative entropy through dissipative processes.

This establishes the material foundation for our subsequent exploration of "agency." In the next section 18.2, we will delve into algebraic properties of $\mathcal{A}_{\text{int}}$, proving that the observer's internal world must be described by **specific subfactors of von Neumann algebras**, thereby explaining why we see a classical world rather than quantum superpositions.

