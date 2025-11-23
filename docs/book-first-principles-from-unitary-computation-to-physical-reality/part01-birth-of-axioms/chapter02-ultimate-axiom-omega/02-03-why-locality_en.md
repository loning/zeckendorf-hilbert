# 2.3 Why Locality? — Avoiding "God's Eye View" and Action at a Distance

After establishing "unitarity" as the rigid skeleton of cosmic logic, we face a second fundamental question: How is this universe's structure organized?

In the Ultimate Axiom $\Omega$, we force the evolution operator $\hat{U}$ to be **local**. This means that within each time step $\Delta t$, any cell (Qubit) can only interact with cells directly adjacent to it on the lattice graph $\Lambda$.

Why must it be local? Why can't we allow a cell to instantly exchange information with a cell at the other end of the universe? This is not just to conform to the empirical facts of special relativity, but a necessary prerequisite for logically constructing a **self-consistent, evolvable universe**.

## 2.3.1 The End of God's Eye View: Full Connection Means No Structure

Imagine a **non-local** universe. In this universe, there exists a direct interaction channel between any two particles. No matter how far apart they are (assuming the concept of "distance" still exists), a flip of one particle can directly change another particle's state in the next instant.

In graph-theoretic language, this corresponds to a **complete graph**.

If the universe is fully connected, then:

1. **Geometry Disappears**: Since any two points are "adjacent," the concept of "space" loses meaning. There is no "near" and "far," no "inside" and "outside"; the entire universe collapses into a zero-dimensional point.

2. **Complexity Collapse**: To calculate the next state, every cell needs to know the current state of all other cells in the entire universe. This means every local computation requires infinite (or universe-scale) information input and processing capability. This actually requires every particle to possess a "God's eye view."

Therefore, **locality is not a limitation, but creation.** It is precisely by limiting the range of interactions (cutting off the vast majority of connections) that the universe acquires topological structure, dimensions, and so-called "space."

**Space is essentially the sparsity of interactions.**

## 2.3.2 The Birth of Geometry: Distance as Delay

Once we impose locality constraints, **maximum signal propagation speed (light speed $c$)** automatically emerges as a logical necessity.

In QCA, information can only propagate to neighbors within one step $\Delta t$. To propagate to a node $N$ steps away, $N$ time steps are necessary.

$$\text{Distance} \equiv \text{Minimum Communication Time}$$

This reveals the ontological definition of light speed $c$ in physics:

**$c$ is not the speed limit of object motion; it is the conversion factor for causal chain extension.**

If we allow non-local action (action at a distance), it means $c \to \infty$. In this case, causality would no longer have temporal order protection, and grandfather paradoxes would become inevitable. The locality axiom is actually the **guardian of causality**. It ensures events occur sequentially and influence transmission has a process. As physicist John Wheeler said: "Time is to prevent everything from happening at once; space is to prevent everything from happening in the same place."

## 2.3.3 Clarification: Quantum Non-locality vs. Dynamical Locality

Here we must clarify a concept that often confuses beginners: the difference between **Bell Non-locality** and **Dynamical Locality**.

Entangled states in quantum mechanics do exhibit non-local correlations—measuring one particle seems to instantly determine another particle's state. Does this violate our locality axiom?

**The answer is: No violation.**

1. **Dynamical Locality (what we insist on)**: This refers to the structure of the Hamiltonian or evolution operator. In QCA, $\hat{H} = \sum \hat{h}_{i, i+1}$. This ensures **interactions** only occur between neighbors. You cannot "touch" a distant particle.

2. **Bell Non-locality (of measurement results)**: This refers to correlations of **states**. Although two particles are far apart, they share a history (once had local interaction somewhere, then separated). This correlation is a **pre-established resource**, not **instantaneous communication**.

In a QCA universe, entanglement can exist between arbitrarily distant nodes (as long as they have causal connection in the past), but **utilizing** this entanglement to transmit information and produce physical effects must follow the point-by-point local rules.

This is like two people each taking a walkie-talkie to opposite ends of Earth. The walkie-talkies (entanglement) connect them, but radio waves (interactions) must traverse space at light speed.

## 2.3.4 Conclusion: A Universe Without Supermen

The locality axiom is actually a **humble** declaration of physics. It states:

* There is no "control center" in the universe.

* Every cell is equal and autonomous.

* Macroscopic order is not imposed top-down by global commands, but emerges bottom-up from countless local microscopic interactions.

This is not only a principle of physics, but also the fundamental reason complex systems (such as life, brains, society) can exist.

At this point, we have established the universe's **software logic (unitarity)** and **hardware architecture (locality)**. In the next section, we will formalize these concepts and write down the complete mathematical definition of the ultimate axiom.

