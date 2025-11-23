# 2.4 Formal Definition: Graph $\Lambda$, Hilbert Space $\mathcal{H}$, and Update Operator $\hat{U}$

In the previous section, we established the universe's information-conserving logic through "unitarity" and endowed the universe with spatial structure and causal constraints through "locality." Now, we must transform these physical intuitions into rigorous mathematical language. This section will provide the complete mathematical formal definition of the Ultimate Axiom $\Omega$; this triple $(\Lambda, \mathcal{H}, \hat{U})$ will become the only axiomatic foundation we are allowed to use in all subsequent derivations in this book.

## 2.4.1 Definition 2.4.1: Discrete Geometric Background $\Lambda$

We define "space" as a countable, infinite (or extremely large finite) graph.

> **Definition (Lattice Graph $\Lambda$)**:
>
> Let $\Lambda = (V, E)$ be an undirected graph, where $V$ is the vertex (cell) set and $E$ is the edge (adjacency relation) set.
>
> We require $\Lambda$ to satisfy the following properties:
>
> 1. **Regularity**: The degree of each vertex is finite and constant, denoted $k$. This corresponds to spatial homogeneity.
>
> 2. **Connectivity**: The graph is connected, i.e., there exists a finite-length path between any two points.
>
> 3. **Discrete Metric**: Define the distance $d(x, y)$ between two points $x, y \in V$ as the number of edges in the shortest path connecting them.

*Note*: The simplest example is the $D$-dimensional integer lattice $\mathbb{Z}^D$, but this is not the only choice. Penrose tilings or triangulations of Regge differential geometry are also allowed. But in elementary derivations of this book, we usually default to $\Lambda \cong \mathbb{Z}^3$ to simplify discussion.

## 2.4.2 Definition 2.4.2: Quantum State Space $\mathcal{H}$

We define "matter" as quantum information distributed on the graph.

> **Definition (Local and Global Hilbert Spaces)**:
>
> 1. **Local Space**: For each vertex $x \in V$, associate a finite-dimensional complex Hilbert space $\mathcal{H}_x \cong \mathbb{C}^d$. $d$ is called the local dimension; for qubit systems, $d=2$.
>
> 2. **Global Space**: The Hilbert space $\mathcal{H}_{\text{total}}$ of the entire system is the tensor product of all local spaces:
>
>    $$\mathcal{H}_{\text{total}} = \bigotimes_{x \in V} \mathcal{H}_x$$
>
> 3. **Basis**: An orthonormal basis of the entire system can be expressed as $|\mathbf{s}\rangle = \bigotimes_x |s_x\rangle$, where $s_x \in \{0, 1, \dots, d-1\}$ is the classical state of node $x$.

*Note*: Since $V$ may be infinite, rigorous mathematical treatment requires infinite tensor product structures of von Neumann algebras or $C^*$ algebras. But physically, we always focus on finite excitation states, so we can treat it as a Hilbert space with countable basis.

## 2.4.3 Definition 2.4.3: Dynamical Evolution $\hat{U}$

We define "time" as discrete update steps $t \in \mathbb{Z}$, and "physical laws" as global update operators.

> **Definition (Global Unitary Evolution $\hat{U}$)**:
>
> The system's state evolves with discrete time steps $t$:
>
> $$|\Psi(t+1)\rangle = \hat{U} |\Psi(t)\rangle$$
>
> where operator $\hat{U}$ must satisfy:
>
> 1. **Unitarity**: $\hat{U}^\dagger \hat{U} = \hat{U} \hat{U}^\dagger = \mathbb{I}$.
>
> 2. **Causal Locality**: $\hat{U}$ has a finite-depth quantum circuit structure. Specifically, $\hat{U}$ can be decomposed as a product of local gates:
>
>    $$\hat{U} = \prod_{\text{partitions } P} \left( \bigotimes_{C \in P} \hat{u}_C \right)$$
>
>    where each $\hat{u}_C$ acts only on nodes within the neighborhood $\mathcal{N}(x)$ centered at $x$ with radius $r$ (interaction range).
>
> 3. **Translation Invariance** (for $\Lambda = \mathbb{Z}^D$): Let translation operator be $\hat{T}_\mathbf{a}$, then $[\hat{U}, \hat{T}_\mathbf{a}] = 0$. This means physical laws are identical everywhere in space.

## 2.4.4 Physical Interpretation: Definition of Light Speed $c$

In this formal system, the natural constant $c$ (light speed) is no longer an empirically measured value, but a **derived quantity** defined by graph structure and update rules.

Within one time step $\Delta t = 1$, local operator $\hat{u}_C$ can only propagate information (entanglement) from node $x$ to its neighbors $y \in \mathcal{N}(x)$.

Let lattice spacing be $a = l_P$ (Planck length), then the maximum propagation speed of information is strictly defined as:

$$c \equiv \frac{a}{\Delta t} \times r$$

where $r$ is the interaction radius of local gates (usually $r=1$).

This is the microscopic origin of light cones in physics: **It is the causal boundary defined by the connectivity of local logic gates.** Any attempt to exceed this speed for information transmission is equivalent to requiring $\hat{U}$ to contain non-local long-range connections, thus violating the locality definition.

At this point, we have completed the complete definition of the universe's "source code." These three definitions—**graph, state, operator**—constitute the entire axiomatic foundation for deriving all physical phenomena. Beyond this, there is nothing else.

In the following chapters, we will start this automaton and see how it emerges the miracles of special relativity from these simple rules.

