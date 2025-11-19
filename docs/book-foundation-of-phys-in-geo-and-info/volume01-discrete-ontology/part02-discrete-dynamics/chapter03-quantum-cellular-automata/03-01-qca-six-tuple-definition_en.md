# Part II: Discrete Dynamics and Causal Structure

## Chapter 3: Quantum Cellular Automata (QCA) Axiomatic System

In Part I, we established **discrete ontology** (Chapter 1) and **information geometric structure** (Chapter 2) of physical reality. We argued that continuous spacetime is not fundamental existence, but an effective approximation emerging from finite-dimensional Hilbert spaces and their entanglement structures. Now, we must answer a more challenging question: **How does physical evolution occur on this discrete, finite geometric stage?**

If time is no longer a continuous parameter $t \in \mathbb{R}$, Schrödinger equation $i\hbar \partial_t \psi = H \psi$ is no longer a fundamental equation, but must be seen as a continuous limit of some deeper discrete update rules. This chapter will establish the axiomatic system of **Quantum Cellular Automata (QCA)** as the fundamental mathematical framework for describing microscopic dynamics of the universe.

### 3.1 Six-Tuple Definition: Discrete Background $\Lambda$, Local Algebra $\mathcal{A}$, and Update Operator $U$

To describe a self-consistent universe that does not depend on background continuous spacetime, we need a minimal set of mathematical objects. Unlike standard quantum field theory (operator distributions built on Minkowski manifolds), our starting point is **operator algebras on graphs**.

We define the fundamental model of physical universe as a **six-tuple** structure $\mathfrak{U}$.

**Definition 3.1.1 (QCA Universe Six-Tuple)**

A QCA universe consists of the following six core elements:

$$
\mathfrak{U} = (\Lambda, \mathcal{N}, \mathcal{H}_{\text{loc}}, \mathcal{A}, U, \omega_0)
$$

where:

1. **$\Lambda$ (Lattice)**: Discrete background set (lattice set), representing basic constituent units of space.

2. **$\mathcal{N}$ (Neighborhood)**: Local neighborhood structure (or graph structure), defining topological connectivity of space.

3. **$\mathcal{H}_{\text{loc}}$ (Local Hilbert Space)**: Finite-dimensional Hilbert space at each lattice site, representing local degrees of freedom.

4. **$\mathcal{A}$ (Global Algebra)**: Quasi-local $C^*$ algebra of the entire system, describing all physical observables.

5. **$U$ (Update Operator)**: Global update operator, describing discrete dynamics of one-step time evolution.

6. **$\omega_0$ (Initial State)**: Initial state of the universe.

The following subsections will elaborate on the physical meaning and mathematical constraints of these elements.

#### 3.1.1 Discrete Background and Neighborhood Structure $(\Lambda, \mathcal{N})$

Physical space is no longer $\mathbb{R}^3$, but a countable set $\Lambda$. Elements $x \in \Lambda$ are called **Cells** or **Lattice Sites**. To define "space," we must introduce **Neighborhood Scheme** $\mathcal{N}$, which specifies which cells are "adjacent."

* **Graph Structure**: For any $x \in \Lambda$, its neighborhood $\mathcal{N}(x) \subset \Lambda$ is a finite set. This defines a directed graph $G=(\Lambda, E)$, where $(y, x) \in E$ if and only if $y \in \mathcal{N}(x)$.

* **Geometric Homogeneity** (optional): In many physical models, we assume $\Lambda$ has some translational symmetry (such as Cayley graphs), i.e., neighborhood structures of all nodes are isomorphic. But in general relativity context, this regularity can be relaxed to allow dynamic geometry or defects.

This structure directly embodies the **Finite Information Density** axiom: space itself is a discrete container of information.

#### 3.1.2 Kinematic Stage: Local Space and Quasi-local Algebra $(\mathcal{H}_{\text{loc}}, \mathcal{A})$

Each cell $x$ carries a quantum system with state space $\mathcal{H}_x$.

* **Finite-Dimensionality**: According to Axiom A2 (Section 1.2), we require $\mathcal{H}_x \cong \mathbb{C}^d$, $d < \infty$. This eliminates infinity of local Hilbert spaces, thereby avoiding UV divergence at the root.

* **Total System Space**: Formally, the Hilbert space of the entire universe is tensor product of all local spaces $\mathcal{H}_{\text{total}} = \bigotimes_{x \in \Lambda} \mathcal{H}_x$.

However, for infinite lattice systems, infinite tensor products have mathematical definition difficulties (e.g., non-separability). A more rigorous approach is to use **algebraic methods**.

* **Local Algebra**: For any finite subset $R$ of $\Lambda$, define local algebra $\mathcal{A}_R = \mathcal{B}(\bigotimes_{x \in R} \mathcal{H}_x)$ (finite-dimensional matrix algebra).

* **Quasi-local Algebra $\mathcal{A}$**: The algebra $\mathcal{A}$ of the entire system is the norm closure of inductive limit of all local algebras (Quasi-local $C^*$-algebra).

**Physical Meaning**: All physical measurements (observables) are essentially **local**. No physical experiment can simultaneously measure infinitely many degrees of freedom of the entire universe. Therefore, quasi-local algebra $\mathcal{A}$ is a more fundamental physical object than Hilbert space.

#### 3.1.3 Dynamical Core: Local Unitary Update $U$

This is the soul of QCA theory. Time evolution is no longer a continuous flow $e^{-iHt}$ generated by Hamiltonian $H$, but a mapping generated by a discrete unitary operator $U$:

$$\rho_{t+1} = U \rho_t U^\dagger$$

Or in Heisenberg picture, operators evolve as $\alpha(A) = U^\dagger A U$.

To conform to fundamental principles of physics (relativistic causality), $U$ must satisfy strict **Locality Condition**:

**Definition 3.1.2 (Structural Locality)**

If for any $x \in \Lambda$ and any local operator $A_x \in \mathcal{A}_{\{x\}}$, the support set (Support) of evolved operator $\alpha(A_x)$ is still contained within some finite neighborhood $\mathcal{N}^+(x)$ of $x$, i.e.:

$$\text{supp}(U^\dagger A_x U) \subset \mathcal{N}^+(x)$$

then $U$ is called a **QCA with finite propagation speed**.

* **Origin of Light Speed**: The size of this finite neighborhood directly defines "light speed" $c$ in this discrete universe. Information can propagate at most to the range covered by $\mathcal{N}^+(x)$ within one time step. This shows that **causality is not an externally imposed constraint, but an algebraic property of dynamical operator $U$**.

#### 3.1.4 Initial Condition $\omega_0$

The universe not only has a set of laws ($U$), but also a specific historical starting point. $\omega_0$ is a state (State) on algebra $\mathcal{A}$, usually set as some state with low entropy and high symmetry (such as vacuum state or product state $|0\rangle^{\otimes \Lambda}$).

* **Finite Complexity**: Under finite information axiom, $\omega_0$ can also be prepared from simple product states by finite-depth quantum circuits. This means the information content contained in initial conditions of the universe is also finite.

---

### 3.1.5 Summary: From Continuous Fields to Digital Universe

Through six-tuple $\mathfrak{U} = (\Lambda, \mathcal{N}, \mathcal{H}_{\text{loc}}, \mathcal{A}, U, \omega_0)$, we have completed a thorough paradigm shift:

1. **Space** changes from continuous manifold $\mathbb{R}^3$ to graph $(\Lambda, \mathcal{N})$.

2. **Fields** change from distribution functions $\phi(x)$ to algebra elements $A \in \mathcal{A}$.

3. **Time** changes from parameter $t$ to update steps $n \in \mathbb{Z}$.

4. **Laws** change from differential equations $\dot{\psi} = -iH\psi$ to algebraic mappings $\alpha(A) = U^\dagger A U$.

This framework is not only mathematically more rigorous (no divergence), but also physically more fundamental. As we predicted in Section 1.3, when we observe this discrete system at macroscopic scales, if lattice spacing is sufficiently small, continuous quantum field theory and curved spacetime geometry will naturally emerge as **effective theories** (this process will be detailed in subsequent sections of this chapter and Chapter 4).

In the next section, we will explore how this discrete structure strictly derives the familiar relativistic causal structure—light cones.

