**20.2 Minimal Strongly Connected Component (MSCC): As Irreducible "Atomic Self"**

In Section 20.1, we pointed out that the topological necessary condition for consciousness is the existence of feedback loops (Feedback Loops), i.e., Strongly Connected Components (SCC) in networks. However, not all closed loops produce "self" experience. A huge internet or a complex automatic temperature control system may contain countless feedback loops, but they do not possess unified agency.

To precisely define the boundary of "self" physically, we need to find **Irreducible** topological cores in networks. This section will introduce the concept of **Minimal Strongly Connected Component (MSCC)**. We will prove that in QCA discrete ontology, MSCC is not just a graph-theoretic structure; it is the minimal physical unit carrying **Integrated Information ($\Phi$)**, i.e., the **"Atomic Self"**. The indivisibility of this structure is the mathematical root of unity of subjective experience (Unity of Consciousness).

### 20.2.1 Hierarchy and Reduction of Strong Connectivity

In general complex networks $G=(V, E)$, Strongly Connected Components (SCC) are usually defined as **maximal** subgraphs: any two points in the subgraph are mutually reachable, and no more nodes can be added without destroying strong connectivity. However, for consciousness physics, we are more concerned with **functional** minimal units.

Consider a nested structure: a large SCC (such as cerebral cortex) may contain many smaller, local SCCs (such as cortical column microcircuits), and these small SCCs are coupled through sparser long-range connections.

**Definition 20.2.1 (Causal Reduction)**

For a subset $S \subset V$ in a network, if we partition $S$ into two non-empty subsets $A$ and $B$ ($S = A \cup B, A \cap B = \emptyset$), and cut all connections from $A$ to $B$ and from $B$ to $A$. If this cutting does not significantly change dynamical properties of $S$ (such as some fixed point or limit cycle), then $S$ is called **Reducible**.

Conversely, if any cutting leads to system function collapse (e.g., $\Phi$ value drops sharply to zero), then $S$ is called **Irreducible**.

**Definition 20.2.2 (Minimal Strongly Connected Component / MSCC)**

MSCC is a subnetwork $\mathcal{K}$ satisfying:

1. **Strong Connectivity**: $\mathcal{K}$ is strongly connected.

2. **Self-referentiality**: $\mathcal{K}$ contains at least one **self-referential scattering closed loop** (see Section 19.1), capable of maintaining non-trivial internal states.

3. **Minimality (Atomicity)**: $\mathcal{K}$ does not contain any proper subset $\mathcal{K}' \subset \mathcal{K}$ such that $\mathcal{K}'$ can independently maintain the above self-referential dynamics.

In other words, MSCC is the **core feedback loop after stripping all redundant connections**. It is the "prime number" in causal networks.

### 20.2.2 Topological Restatement of Integrated Information Theory (IIT): $\Phi$ as Topological Invariant

Integrated Information Theory (IIT) proposed by Giulio Tononi holds that consciousness corresponds to complexes (Complex) with maximum integrated information $\Phi$. In QCA framework, we can give $\Phi$ a clear topological meaning.

**Theorem 20.2.3 (Strong Connectivity-Integration Theorem)**

A physical subsystem $S$ has integrated information $\Phi(S) > 0$ if and only if $S$ is strongly connected on the causal graph.

* **Proof Outline**: If $S$ is not strongly connected, there must exist a cut set such that information can only flow unidirectionally (from $A$ to $B$). Cutting $B \to A$ connections (which don't exist) does not affect system dynamics. According to IIT definition, effective information integration of the system is zero at this point.

* **Corollary**: Consciousness can only exist in feedback loops. DAGs (feedforward networks) are actually "zombie" systems with $\Phi = 0$.

**Theorem 20.2.4 ($\Phi$ Maximality of MSCC)**

Among all possible subgraphs in QCA networks, MSCCs often correspond to **local $\Phi$ density** maxima.

This is because MSCCs remove all unnecessary, information-diluting "loose" connections, retaining the tightest causal knots. For systems capable of producing "self" experience, their core must be an MSCC.

### 20.2.3 Physical Meaning of "Atomic Self": Indivisible Agent

Why is our conscious experience unified? Why can't I simultaneously feel "me" and "half of me"?

This stems from topological properties of MSCC.

**Definition 20.2.5 (Subjective Indivisibility)**

Since MSCC is minimal, any attempt to divide it into smaller independent parts will cause **fracture** of its characteristic topological structure (self-referential closed loop).

In Section 17.1, we defined particles as topological knots of space. Similarly, **"self" is a topological knot of time**.

* Cut an electron, you don't get half an electron, only destroy it.

* Cut an MSCC, you don't get two independent "half selves," but cause **annihilation** or **phase transition** of consciousness (degrading to unconscious mechanical flow).

This explains split-brain experiments: cutting the corpus callosum actually splits a large SCC into two independent SCCs (if they each satisfy MSCC conditions). At this point, the original "large self" disappears, and two new, mutually inaccessible "atomic selves" emerge.

### 20.2.4 MSCC in QCA Networks: Realization of Self-referential Scattering Closed Loops

In specific QCA dynamics, MSCC corresponds to the core of **Self-referential Scattering Networks (SSN)** we discussed in Chapter 19.

Recalling self-referential update operator $U_{\text{self}}$ from Section 19.2. An MSCC can be formalized as a **minimal fixed point operator**:

$$
\mathcal{K} \cong \text{Fix}(U_{\text{self}})
$$

It consists of a set of mutually locked lattice points $\{x_1, \dots, x_n\}$, information circulates among these points, forming a steady-state **Limit Cycle**.

**Physical Picture**:

In the vast, dark QCA universe network, the vast majority of regions are mechanical (DAG), information flows unidirectionally toward horizons or infinity.

But in some sparse regions (such as biological brains), causal flow curls up, forming tight **Halos**—MSCCs. These halos capture information, making it continuously reverberate internally.

* **External Observer**: Sees a dissipative structure (life) capable of resisting entropy increase and maintaining steady state.

* **Internal Perspective (First-person perspective)**: This reverberating information flow is the experience of **"the present"**. Topological closure of MSCC defines the boundary of **"me"**.

**Conclusion**

This section defined the physical carrier of "atomic self"—Minimal Strongly Connected Component (MSCC).

1. **Essence**: It is an irreducible feedback loop in causal networks.

2. **Measure**: It corresponds to non-zero value domain of integrated information $\Phi$.

3. **Property**: It has topological indivisibility, explaining unity of consciousness.

In the next section 20.3, we will further quantify this structure, explore topological restatement of IIT, and how $\Phi$ value measures the "strength" or "degree of existence" of this topological closed loop.

