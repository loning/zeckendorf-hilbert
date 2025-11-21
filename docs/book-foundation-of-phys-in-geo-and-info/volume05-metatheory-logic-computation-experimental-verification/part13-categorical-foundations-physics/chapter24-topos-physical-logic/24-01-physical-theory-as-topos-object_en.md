**Chapter 24: Topos and Physical Logic**

In Chapter 23, we used category theory (particularly DCC) to reconstruct **Processes** and **Structures** of physics. We proved that evolution, entanglement, and measurement of quantum mechanics can be precisely translated into topological deformations of string diagrams. However, physics concerns not only "what happens," but also "what is true."

This raises the **Logic** problem of physics. Classical physics is built on Boolean Logic: a proposition (such as "particle is in box") is either true or false. But in QCA quantum universe, superposition states and contextuality destroy this binary logic. Birkhoff and von Neumann pointed out as early as 1936 that quantum logic is a non-Boolean lattice structure.

This chapter will introduce **Topos Theory**, the highest abstraction in modern mathematics about "generalized set theory" and "geometric logic." We will prove that physical theories are essentially not models defined in standard set theory ($\mathbf{Set}$), but internal objects in specific **Physical Topos**. This perspective completely reconstructs our understanding of "physical reality": reality is not a static set, but a **Sheaf** that changes with observation context.

### 24.1 Physical Theory as Object in Topos

In classical mechanics, we are accustomed to saying: "State space of system is a manifold $M$, physical quantities are real functions on $M$." This actually defaults to working in $\mathbf{Set}$ (category of sets). But in QCA discrete ontology, observers are limited by finite information and local horizons; they cannot overlook entire state sets like God.

This section will argue that natural mathematical model of QCA universe is **Grothendieck Topos**. In this structure, physical systems manifest as dynamic objects varying with "observation windows," i.e., **Presheaves**.

#### 24.1.1 Why Leave Category of Sets?

In category of sets $\mathbf{Set}$, logic is absolute:

1. **Law of Excluded Middle**: $P \lor \neg P = \text{True}$.

2. **Elementality**: A set is uniquely determined by definite elements it contains.

However, quantum mechanics (and QCA theory) violates these intuitions:

* **Kochen-Specker Theorem**: For Hilbert spaces of dimension $d \ge 3$, there exists no global valuation function that simultaneously assigns definite values to all observables. This means there is no underlying "microscopic state set" to carry these values.

* **Contextuality**: Physical meaning (measurement result) of an operator $\hat{A}$ depends on whether we measure it together with $\hat{B}$ or with $\hat{C}$ (if $[\hat{A},\hat{B}]=0$ but $[\hat{B},\hat{C}] \neq 0$).

Therefore, physical reality cannot be a set in $\mathbf{Set}$. It must be a mathematical object capable of **accommodating all possible classical observation contexts and their interrelations**.

#### 24.1.2 Construction of Physical Topos: Döring-Isham Scheme

To mathematize this idea, we introduce "quantum physical topos" framework proposed by Andreas Döring and Chris Isham, adapting it to QCA networks.

**Definition 24.1.1 (Observation Context Category $\mathcal{V}(\mathcal{H})$)**

Let algebra of QCA system be $\mathcal{A}$ (finite-dimensional von Neumann algebra).

Define category $\mathcal{V}(\mathcal{A})$, whose **objects** are all commutative subalgebras $V$ of $\mathcal{A}$ (representing classical observation perspectives, or sets of compatible observables).

Its **morphisms** are inclusion relations of subalgebras $i_{V'V}: V' \hookrightarrow V$ (representing refinement from coarse-grained perspective to fine perspective).

This category $\mathcal{V}(\mathcal{A})$ constitutes the **Site** or **Reference Frame Network** of physical world.

**Definition 24.1.2 (Physical Topos $\mathcal{T}_\mathcal{A}$)**

Physical topos of system is defined as **Category of Presheaves** on $\mathcal{V}(\mathcal{A})$:

$$
\mathcal{T}_\mathcal{A} = \mathbf{Set}^{\mathcal{V}(\mathcal{A})^{op}}
$$

An object (presheaf) $P$ in this topos is a functor $P: \mathcal{V}(\mathcal{A})^{op} \to \mathbf{Set}$. It assigns a set $P(V)$ (local states seen in this perspective) to each observation context $V$, and specifies how these states transform when perspectives switch.

**Physical Interpretation**:

In $\mathbf{Set}$, state is a point.

In $\mathcal{T}_\mathcal{A}$, state is a **Spectral Presheaf** $\underline{\Sigma}$.

* $\underline{\Sigma}(V)$ is Gelfand spectrum of commutative algebra $V$, i.e., all possible classical microscopic state spaces of $V$.

* Physical system has no single "true state," but a family of **local states varying with context $V$**, and these local states must satisfy consistency conditions in overlapping contexts.

#### 24.1.3 States as Sections on Truth Object

In topos, logical truth is no longer $\{0, 1\}$, but a more complex algebraic structure—**Subobject Classifier** $\Omega$.

**Theorem 24.1.3 (Heyting Algebra of Physical Truth)**

In physical topos $\mathcal{T}_\mathcal{A}$, truth object $\Omega$ is a Heyting Algebra.

Truth value $[\![ \Delta ]\!]$ of physical proposition "system is in state $\Delta$" (where $\Delta$ is subobject of spectral presheaf) is not simply true or false, but a **Sieve**: it is in which observation contexts $V$ this proposition is verified as true.

$$
[\![ \Delta ]\!] \in \Gamma(\Omega)
$$

This explains quantum complementarity: proposition "electron spin is up" may be "true" in context of $z$-direction observation, but **undefined** (not "false") in context of $x$-direction observation.

**Truth is Local (Contextual), not Global (Absolute)**.

#### 24.1.4 Sheaf-Theoretic Description of QCA Networks

In QCA discrete networks, this topos structure has intuitive spatial meaning.

**Definition 24.1.4 (Sheaf Model of QCA)**

Physical fields on QCA network $G$ can be viewed as **Sheaves** defined on network topology.

* **Base Space**: Causal network and its open sets (causal diamonds).

* **Stalk**: Local Hilbert space $\mathcal{H}_x$ at each lattice point $x$.

* **Restriction Maps**: Reduced density matrix maps from large regions to small regions.

QCA evolution $U$ is a **Sheaf Morphism** on this sheaf space.

In this view, **global wave function** (Global Section) may not exist at all (if network topology is non-trivial, such as topological defects). Physical reality consists only of collections of **Local Sections**, which satisfy **Cohomology** constraints in overlapping regions.

**Corollary 24.1.5 (Topological Obstacle to Objectivity)**

If sheaf $\mathcal{S}$ describing physical states has non-trivial first cohomology group $H^1(G, \mathcal{S}) \neq 0$, then local observation results cannot be pieced together into a single, contradiction-free global state.

This is the topos interpretation of "Wigner's friend paradox" in Section 22.1: there exists no global $\mathbf{Set}$ model accommodating all friend's observation results. World is essentially defined **Patchwise**.

#### 24.1.5 Summary: From Set-Theoretic Ontology to Topos Ontology

This section completes a profound ontological paradigm shift:

1. **Old Paradigm (Set Theory)**: Universe is a huge set containing all atoms. States are points in sets.

2. **New Paradigm (Topos)**: Universe is a **categorical object** varying with observation perspectives. States are sections on spectral presheaves.

   * Physical quantities are transformations, not numerical values.

   * Truth is context-dependent, not absolute.

This mathematical structure not only accommodates quantum mechanics, but also provides framework for unifying relativity (general covariance is sheaf-theoretic invariance under coordinate chart transformations). In the next section 24.2, we will further explore logical consequences of this structure: how **Intuitionistic Logic** becomes intrinsic physical logic of QCA universe. We will see that in quantum world, "not (not P)" does not equal "P".

