# 8.1 Observer Model: Computational Structure (Agent) as Self-Referential Subsystem

In traditional physics narratives, "observers" are often treated as awkward ghosts. In classical mechanics, they are massless, volumeless "God's eyes"; in standard quantum mechanics, they are external "black boxes" causing wave function collapse. Physical laws seem to describe a universe without audience, but all physical knowledge comes from observation.

In the discrete ontology constructed in this book, we reject this dualism. Since the universe is unitary QCA, **observers must be part of this QCA network**. Consciousness is not a miracle transcending physical laws, but a special, advanced **computational structure**.

This chapter will attempt to establish foundations of "consciousness physics." We will prove: **Observers are self-referential subsystems emerging in information flow.** They acquire "agency" by maintaining **Markov blanket** on their boundaries and compressing chaotic environmental information into low-entropy **internal models**.

To define what an "observer" is, we must first define what an "individual" is. In a fully connected or uniform QCA lattice, where does "I" begin, where does "environment" end?

## 8.1.1 Mathematical Definition of Boundary: Markov Blanket

Consider entire system Hilbert space $\mathcal{H}_{total}$. Any subsystem partition $\mathcal{H}_{total} = \mathcal{H}_{in} \otimes \mathcal{H}_{out}$ is mathematically legal, but vast majority of partitions are physically meaningless (e.g., grouping one atom from moon with one neuron from your brain).

Meaningful physical individuals must have **dynamical independence**. This can be formalized through **Markov Blanket** concept.

> **Definition 8.1 (Markov Blanket and Graph Partition)**:
>
> In QCA's interaction graph $\Lambda = (V, E)$, let $V_{in} \subset V$ be a set of nodes representing "internal states."
>
> **Markov Blanket** $V_{mb}$ of $V_{in}$ is defined as boundary node set of $V_{in}$ on graph (nodes directly connected to $V_{in}$ but not belonging to $V_{in}$).
>
> Remaining nodes $V_{ext} = V \setminus (V_{in} \cup V_{mb})$ are called "external states" or "environment."
>
> If following condition is satisfied, then $(V_{in}, V_{mb})$ constitutes a **statistically independent subsystem**:
>
> **Conditional Independence**: Given blanket state $V_{mb}$, evolution of $V_{in}$ is independent of $V_{ext}$.
>
> $$P(v_{in}(t+1) | v_{in}(t), v_{mb}(t), v_{ext}(t)) = P(v_{in}(t+1) | v_{in}(t), v_{mb}(t))$$

Physically, $V_{mb}$ is further decomposed into:

1. **Sensory Nodes**: Receive information from environment $V_{ext}$, transmit to $V_{in}$.

2. **Active Nodes**: Receive commands from $V_{in}$, change environment $V_{ext}$.

**Physical Picture 8.1**:

An observer is essentially an **information membrane** in spacetime network. This membrane isolates universe into "me" (internal) and "not me" (external). Without this membrane, there is no observer, only a chaotic ocean of information.

## 8.1.2 Self-Reference and Internal Model: I Am What I Compute

Having boundary alone is not enough. A rock also has boundary, but rocks are not observers. True observers (agents) must have **internal models**.

In QCA dynamics, this means evolution rules $\hat{U}_{in}$ of internal nodes $V_{in}$ must contain a **recursive** or **self-referential** structure.

> **Definition 8.2 (Agent)**:
>
> A subsystem $\mathcal{A} = (V_{in}, V_{mb})$ is called an **agent** if its internal state $\rho_{in}$ encodes a **compressed mapping** of external environment state $\rho_{ext}$.
>
> $$\rho_{in} \approx \mathcal{M}(\rho_{ext})$$
>
> where $\mathcal{M}$ is a homomorphic mapping.

This means agents don't just react passively; they **simulate** external world internally.

* **Memory**: Agents must maintain temporal correlations of certain states, resisting environmental thermal fluctuations (forgetting). This requires $V_{in}$ to have long-range temporal entanglement structure (this is macroscopic upgrade of "topological mass" we discussed in Chapter 5).

* **Prediction**: Agents use internal model $\mathcal{M}$ to deduce future environmental states based on current sensory input.

**Minimum Threshold of "Consciousness"**:

When this internal model $\mathcal{M}$ becomes complex enough that it not only contains simulation of "external world," but also simulation of **"self's role in external world"** (i.e., model contains a symbol representing the system), **self-awareness** emerges.

$$M_{model} \supset \{ \text{World}, \text{Self} \}$$

## 8.1.3 Resisting Heat Death: Schrödinger's Definition of Life

According to second law of thermodynamics, entropy of closed systems always increases. If $V_{in}$ frequently exchanges information with $V_{ext}$, internal structure should rapidly be assimilated by environment (thermalization), causing boundary to disappear, observer to die.

But observers exist precisely because they **refuse thermalization**.

> **Axiom 8.1 (Principle of Agency)**:
>
> Observers are **non-equilibrium steady state structures (NESS)** in QCA networks that can actively maintain their Markov blankets from environmental dissipation by consuming free energy.

This returns to **topological knots** we discussed in Chapter 5.

* **Elementary Particles** (such as electrons) are simplest observers: They maintain their non-trivial structure through topological winding (winding number $\mathcal{W}=1$), resisting vacuum trivialization.

* **Living Organisms** are complex observers: They continuously repair their Markov blankets (cell membranes/skin) at molecular level through metabolism (extracting negentropy).

* **Intelligent Consciousness** are highest-level observers: They maintain logical consistency at information level through computation (cognition), resisting conceptual entropy increase (mental disorder).

## 8.1.4 Conclusion: Observers as Physics' "Solitons"

In summary, we give strict physical definition of observers:

**Observers are complex topological solitons in QCA information fluid.**

1. **Structurally**: Defined by Markov blanket boundary.

2. **Functionally**: Running simulation algorithms of environment (self-referential).

3. **Dynamically**: Maintaining their low-entropy state through dissipative structures.

This definition removes mystery of consciousness. Consciousness is not magical smoke produced by brains; it is **specific geometric form formed by information flowing in closed loops**. As long as network is complex enough, emergence of this form is as inevitable as vortices emerging in turbulence.

In the next section, we will quantitatively describe this dynamical mechanism of "maintaining low entropy"—**free energy minimization principle**. This will explain why observers always tend to "understand" the universe.

