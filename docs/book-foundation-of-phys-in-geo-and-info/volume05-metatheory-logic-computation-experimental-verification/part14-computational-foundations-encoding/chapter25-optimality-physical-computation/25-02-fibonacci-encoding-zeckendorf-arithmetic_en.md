**25.2 Fibonacci Coding and Zeckendorf Arithmetic: Optimal Encoding for Local Reversible Updates**

In Section 25.1, we pointed out according to Landauer principle that logically irreversible operations (such as erasure) must pay thermodynamic cost. To construct an efficient, low-dissipation QCA universe, underlying computational processes should maintain **logical reversibility** as much as possible. Additionally, core constraint of QCA is **local causality**: information propagation speed is limited by speed of light, meaning any global computational operations (such as long carry chains in standard binary addition) are extremely expensive physically, because they require waiting for signals to traverse entire system.

This section will introduce a physically advantageous encoding scheme—**Fibonacci Coding**—and its underlying mathematical structure—**Zeckendorf Arithmetic**. We will prove that this encoding method based on "golden ratio" is not only maximum entropy encoding under local exclusion constraints (hard-core conditions), but also allows arithmetic operations to complete in **constant time** through parallel local updates. This explains why nature (from plant growth to quantum topological phases) frequently exhibits Fibonacci sequences: it is the **optimal local protocol** for information transmission and processing in causal networks.

### 25.2.1 Constraints of Local Causality on Encoding: Carry Catastrophe

Consider addition of two $N$-bit binary numbers: $A + B$. In worst case (e.g., $011\dots1 + 000\dots1$), carry must propagate from lowest bit all the way to highest bit.

* **Computational Complexity**: Time $T \propto N$.

* **Physical Meaning**: If each bit is a spatial lattice point, carry wave must sweep entire system. In QCA universe, this means addition operation cannot complete in parallel within one time step, must violate locality or consume large time.

To achieve **parallel, local** physical evolution in QCA (i.e., interactions only occur at neighboring lattice points, completed in one step), we need an arithmetic system that is **carry-free** or **locally carrying**. This is the physical motivation for Zeckendorf representation.

### 25.2.2 Zeckendorf Theorem and "Hard-core" Physical States

Edouard Zeckendorf proved an elegant theorem about integer representation, which remarkably coincides with **Hard-core Gas** models in physics.

**Theorem 25.2.1 (Zeckendorf Theorem)**

Any positive integer $N$ can be uniquely represented as sum of a set of non-consecutive Fibonacci numbers:

$$
N = \sum_{i=2}^k c_i F_i
$$

where $F_i$ is Fibonacci sequence ($F_1=1, F_2=1, F_3=2, F_4=3, F_5=5, \dots$), coefficients $c_i \in \{0, 1\}$, satisfying **non-adjacent constraint**:

$$
c_i c_{i+1} = 0
$$

That is, two consecutive $1$s ("11") are forbidden configurations in representation sequence.

**Physical Mapping**:

On QCA lattice, we can view coefficients $c_i$ as occupation numbers (0 or 1) of lattice point $i$.

* **Constraint $c_i c_{i+1} = 0$**: This corresponds to **Nearest-neighbor Exclusion**. If a lattice point is occupied (excited), its neighbor must be empty (ground state).

* **Physical Systems**: This precisely corresponds to **hard dimer models** in Rydberg atom arrays (Rydberg Blockade) or strongly correlated electron systems. Zeckendorf coding is not an artificial mathematical game, but **natural counting basis** of such constrained physical systems.

### 25.2.3 Golden Ratio: Maximum Entropy Encoding

Why choose Fibonacci sequence as basis, rather than $2^i$ (binary)?

This involves balance between encoding efficiency and physical constraints.

* **Binary**: Maximum information density (per bit $\ln 2$), but no fault tolerance, and prone to long-range carries.

* **Zeckendorf Coding**: Since "11" is forbidden, effective state space becomes smaller.

**Definition 25.2.2 (Golden Entropy Capacity)**

Number of effective states encodable by Zeckendorf chain of length $L$ approaches $F_{L+2}$. Its asymptotic information capacity (bits per lattice point) is:

$$
C = \lim_{L \to \infty} \frac{\log_2 F_L}{L} = \log_2 \phi \approx 0.6942 \text{ bits/site}
$$

where $\phi = \frac{1+\sqrt{5}}{2}$ is **golden ratio**.

**Theorem 25.2.3 (Maximum Entropy Principle)**

Among all one-dimensional lattice gases satisfying nearest-neighbor exclusion constraint ($n_i n_{i+1} = 0$), Fibonacci coding achieves **maximization of Configurational Entropy**.

This means, if underlying physics of universe requires some form of "non-locality defense" (preventing signal accumulation) or "resource competition" (neighbors cannot excite simultaneously), then Fibonacci coding is **natural selection's optimal solution**. It maximizes information carrying capacity while maintaining local sparsity (low energy consumption).

### 25.2.4 Local Arithmetic Dynamics: Computational Form of Physical Laws

Most powerful physical property of Zeckendorf coding is that its arithmetic operations can be implemented in parallel through **local rules**. This makes it an ideal carrier for QCA dynamics.

**1. Microscopic Mechanism of Addition**

In Zeckendorf representation, addition $A+B$ can be decomposed into bit superposition, then eliminate forbidden "11" and "2" (double occupation) through local rules.

Basic local rules stem from Fibonacci recurrence relation $F_{i+1} = F_i + F_{i-1}$:

* **Rule A (Carry)**: $011 \to 100$. If "11" is found, merge it into "1" at higher position. (Energy aggregation)

* **Rule B (Borrow)**: $100 \to 011$. Decompose high-energy excitation into two low-energy excitations.

* **Rule C (Double Occupation Elimination)**: $020 \to 1001$ (using transformations like $2F_i = F_{i+1} + F_{i-2}$).

**Theorem 25.2.4 (Local Computability)**

Under Zeckendorf coding, addition operations can be completed through finite-depth local QCA circuits. Carry waves no longer need to traverse entire system, but rapidly dissipate or merge locally. This **Ripple Suppression** property ensures physical law evolution can proceed efficiently under light cone constraints.

**2. Physical Picture: Particle Scattering and Fusion**

* "1" can be viewed as **particle** (such as soliton).

* "11 $\to$ 100" corresponds to **particle fusion**: two low-energy particles collide and merge into one high-energy particle, position shifts.

* "100 $\to$ 011" corresponds to **particle decay**.

Computational process of Zeckendorf arithmetic physically manifests as **scattering, production, and annihilation processes** of particles on QCA networks. Arithmetic axioms are physical conservation laws.

### 25.2.5 Conclusion: Nature's "Golden" Choice

This section reveals that Fibonacci coding is not mathematical trivia, but physical necessity for QCA universe to achieve efficient computation.

1. **Locality**: It transforms global arithmetic problems into local rule evolution, conforming to relativistic causal laws.

2. **Robustness**: Sparse coding (forbidding 11) provides natural error correction gaps, similar to Pauli exclusion of fermions.

3. **Optimality**: It is maximum entropy encoding in constrained systems (golden ratio).

This explains why $\phi$ (golden ratio) is ubiquitous in nature (from phyllotaxis to anyon topological order): **Nature tends to organize its structures using this local information encoding method with minimum impedance and maximum robustness**.

At this point, we have explored cost of computation (Landauer principle) and encoding (Zeckendorf arithmetic). In the next section 25.3, we will further explore deep physical origin of **golden ratio**, proving it is not only encoding efficiency, but also marker of **optimal information transmission rate** in causal networks.

