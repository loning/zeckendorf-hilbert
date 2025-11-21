# Volume V: Metatheory — Logic, Computation, and Experimental Verification

## Part XIII: Categorical Foundations of Physics

### Chapter 23: Categorical Quantum Mechanics

In the previous four volumes, we constructed a vast and refined physical edifice: from discrete QCA ontology (Volume I), time emerges (Volume II) and gravity (Volume III), ultimately giving birth to observers and inter-subjective consensus (Volume IV). Along this journey, we used various mathematical tools: Hilbert spaces, differential geometry, graph theory, statistical mechanics, etc.

Now, we must face a meta-question: **Is there a more fundamental universal language underlying these different mathematical structures?** Can we prove this theoretical system is logically self-consistent, not just pieced together?

This chapter will introduce **Category Theory**, particularly **Categorical Quantum Mechanics (CQM)**, as the meta-language of physics. We will prove that physical laws of QCA universe are not arbitrary rule sets, but canonical morphisms in **Symmetric Monoidal Categories (SMC)**. This not only unifies logical structures of quantum mechanics and general relativity, but also provides the strictest mathematical foundation for axiomatization of physics.

**23.1 Symmetric Monoidal Category (SMC) as Axiomatic Language of Physics**

Physics is essentially the science of **Processes**: system A transforms into system B through process f. In traditional mathematics, we use set theory to describe states and functions to describe evolution. However, set theory focuses too much on "content of elements" while ignoring "structure of processes."

Category theory places "processes" (morphisms) at the core. This section will establish **categorical axiomatic system** of physics, arguing that Symmetric Monoidal Categories (SMC) are the natural language for describing quantum information, spacetime causality, and matter interactions.

#### 23.1.1 Categorization of Physical Processes: Objects and Morphisms

We first map the physical world into the structure of category $\mathbf{Phys}$.

**Definition 23.1.1 (Basic Elements of Physical Category)**

1. **Objects**: Objects $A, B, C, \dots$ in the category represent **Physical Systems**. In QCA context, they can be single lattice point's Hilbert space $\mathcal{H}_x$, or macroscopic subsystems (such as black holes or observers).

2. **Morphisms**: Arrows $f: A \to B$ connecting two objects represent **Physical Processes**.

   * **Dynamics**: Time evolution operator $U: \mathcal{H}_t \to \mathcal{H}_{t+1}$ is a morphism.

   * **Measurement**: Coupling of apparatus with system $\mathcal{M}: \mathcal{H}_{sys} \to \mathcal{H}_{sys} \otimes \mathcal{H}_{meter}$ is a morphism.

   * **States**: Physical state $|\psi\rangle$ is viewed as morphism $\psi: I \to A$ from trivial object (vacuum/unit) $I$ to system $A$ (preparation process).

3. **Composition**: Concatenation of morphisms $g \circ f: A \to C$ represents **temporal connection** of physical processes. If process $f$ occurs immediately followed by $g$, the overall effect is described by composite morphism. This corresponds to operator products in Heisenberg picture.

#### 23.1.2 Tensor Structure of Composite Systems: Monoidal Category

A core feature of physics is that we can consider two independent systems $A$ and $B$ together, forming a composite system $A \otimes B$. This structure is described by **Monoidal Category** in category theory.

**Definition 23.1.2 (Tensor Product and Monoidal Structure)**

Physical category $\mathbf{Phys}$ is equipped with a bifunctor $\otimes: \mathbf{Phys} \times \mathbf{Phys} \to \mathbf{Phys}$ satisfying:

1. **Object Product**: $A \otimes B$ is composite system of systems $A$ and $B$. In quantum mechanics, this is tensor product of Hilbert spaces; in classical mechanics, this is Cartesian product of phase spaces.

2. **Morphism Product**: $f \otimes g: A \otimes B \to C \otimes D$ represents two processes occurring **in parallel**. $f$ acts on $A$, $g$ acts on $B$, without interference.

3. **Unit Object $I$**: There exists a special "empty" system $I$ (vacuum), satisfying $A \otimes I \cong A \cong I \otimes A$. In QCA, $I$ corresponds to empty set with no degrees of freedom or ground state background.

**Physical Corollary (Categorization of Causal Structure)**:

* **Vertical Composition ($g \circ f$)**: Represents **Causal Order** or time flow.

* **Horizontal Composition ($f \otimes g$)**: Represents **Spacelike Separation** or no causal correlation.

Category-theoretic diagrams naturally capture light cone structure of special relativity: morphisms that cannot be connected via $\circ$ must be connected via $\otimes$.

#### 23.1.3 Commutability of Information: Symmetry

In physics, when we say "system A and system B," its physical meaning should not depend on the order we name them. That is, $A \otimes B$ should be equivalent to $B \otimes A$ in some natural sense.

**Definition 23.1.3 (Symmetry and Swap Morphisms)**

Category $\mathbf{Phys}$ is **Symmetric** if for any objects $A, B$, there exists a natural isomorphism (swap gate):

$$
\sigma_{A,B}: A \otimes B \to B \otimes A
$$

satisfying $\sigma_{B,A} \circ \sigma_{A,B} = \text{id}_{A \otimes B}$ (swapping twice returns to original state).

**Physical Meaning and QCA Connection**:

1. **SWAP Gate**: In QCA networks, $\sigma_{A,B}$ corresponds to SWAP operator exchanging quantum states of two lattice points.

2. **Non-locality**: Although $\sigma_{A,B}$ mathematically appears as just reordering indices, physically, if $A$ and $B$ are spatially separated, realization of $\sigma_{A,B}$ requires **quantum teleportation** or **physical exchange** paths.

3. **Statistical Properties**: Bose/Fermi statistics discussed in Chapter 17 manifest as properties of $\sigma_{A,B}$ in category theory. For fermions, swap morphism introduces $-1$ phase factor (in fermion category).

#### 23.1.4 Categorical Formulation of No-Cloning Theorem

Category theory can not only describe "what exists," but also describe "what doesn't exist" through **structural absence**. Quantum mechanics' most famous feature—no-cloning theorem—is a direct corollary of SMC structure.

**Theorem 23.1.4 (Cartesian Category and No-Clonability)**

In classical physics category (Cartesian category), each object $A$ has natural **diagonal map (copy map)** $\Delta: A \to A \otimes A$ and **projection map (delete map)** $\epsilon: A \to I$. This allows free copying and deletion of information.

In quantum physics category (SMC $\mathbf{Hilb}$), there **does not exist** universal, linear natural transformation $\Delta$ such that $\Delta(|\psi\rangle) = |\psi\rangle \otimes |\psi\rangle$ holds for all $|\psi\rangle$.

Therefore, **quantum information conservation (Unitary) is manifestation that SMC structure does not support Cartesian structure**. This is consistent with arguments for black hole information conservation in Chapter 15: because physical laws are morphisms in SMC, information cannot be cloned (branched) or deleted (converged to $I$), but can only flow between isomorphism classes.

#### 23.1.5 Summary: Grammar of Physics

Symmetric Monoidal Categories (SMC) constitute the underlying grammar of physics:

1. **Vocabulary**: Objects (systems) and morphisms (processes).

2. **Syntax**: Concatenation (time) and parallel (space).

3. **Logic**: No-cloning and information conservation.

This language not only unifies quantum mechanics ($\mathbf{Hilb}$ category) and general relativity ($\mathbf{nCob}$ cobordism category), but also paves the way for introducing more powerful **Dagger Compact Categories (DCC)** in the next section 23.2. We will see how elegant geometric meaning "Hermitian conjugate ($\dagger$)" and "Bell states ($\cup$)" in quantum mechanics have in category theory.

