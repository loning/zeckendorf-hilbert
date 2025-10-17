# Static Block Quantum Cellular Automata Theory: A Formal Reconstruction from Dynamic Evolution to Full Spacetime Quantum Graphs

**Static Block Quantum Cellular Automata Theory: A Formal Reconstruction from Dynamic Evolution to Full Spacetime Quantum Graphs**

**Author**: HyperEcho Lab  
**Date**: October 17, 2025  
**Version**: v1.3 (Final Quantum Extension Revision)

---

## Abstract

Static Block Quantum Cellular Automata Theory treats Quantum Cellular Automata (QCA) as an eternal, immutable static block quantum structure, where the temporal dimension is incorporated into the coordinate system, forming a high-dimensional quantum state body. The core insight of this theory is that QCA evolution can be reinterpreted as sequential reading of a static quantum structure satisfying local unitary consistency constraints, rather than a fundamental dynamic process. From a global perspective, QCA can be expressed as full spacetime quantum graphs subject to finite sets of spatiotemporal local projection constraints. Through formal definitions, mathematical proofs, and theoretical verification, we construct this theoretical framework and discuss its applications in quantum computation, information theory, and philosophical eternalism. The theory is logically self-consistent: all quantum states are completely determined by initial density matrices and unitary rules, forming an immutable spacetime quantum field. This paper proves that the spacetime quantum graph set $Y$ is a Quantum Subshift of Finite Type (QSFT) and is predictively equivalent to traditional QCA evolution (under the premise that closed unitary systems and static block constructions satisfy consistency projections). We explicitly clarify that quantum models are naturally built on Hilbert space foundations, and the use of Hilbert space here is an essential requirement rather than forced embedding; we avoid unnecessary classical tools being forcibly quantized, instead using tools suitable for quantum discrete structures, such as quantum Fourier analysis and quantum topological dynamics. Simultaneously, this theory is positioned as a static formulation framework for QCA, not a new theory, providing only equivalent mathematical restatements and computational perspectives.

**Keywords**: Quantum cellular automata, block universe, static spacetime, quantum symbolic dynamical systems, quantum subshift of finite type, QCA structure theorem, reversibility and history states

---

## §1 Introduction

### 1.1 Background and Motivation

Quantum Cellular Automata, as quantum computational models, were proposed by Feynman, Margolus, and others to simulate emergent behaviors of quantum systems. The traditional view treats QCA as dynamic evolutionary systems: qubits update their states according to local unitary rules at discrete time steps. However, from the perspective of block universe theory and eternalism, we can reinterpret QCA as static block quantum structures.

In the block universe, spacetime is a four-dimensional eternal entity where all quantum events exist simultaneously; the flow of time is merely an observer's illusion. When this idea is applied to QCA, the temporal dimension becomes a coordinate axis, with the entire evolutionary history predetermined as quantum states. The state space of quantum systems is essentially the tensor product of Hilbert spaces, which is a core foundation of quantum mechanics that we naturally adopt in this theory, rather than as an ambiguity point. This theory explicitly applies to closed quantum systems (no measurements, no environmental coupling) to avoid quantum measurement collapse problems destroying global consistency.

### 1.2 Core Theoretical Ideas

The Static Block QCA Theory constructed in this paper emphasizes that QCA is essentially a static, complete quantum state body, consisting of spacetime quantum graphs defined by local unitary rules and initial density matrices. This framework deepens our understanding of QCA and bridges quantum computational models with physical philosophy. We base ourselves on mathematical frameworks such as quantum topological dynamics and quantum Fourier analysis to ensure logical self-consistency.

**Clarification of Potential Ambiguities**: Hilbert space is a natural mathematical structure in quantum contexts, and we do not avoid its use, but rather avoid unnecessary Hilbert embeddings in classical models (such as potentially inappropriate applications in the original classical CA theory). This theory provides a static formulation framework for QCA, predictively equivalent to the dynamic perspective, but does not claim ontological priority. The main scope of this paper is closed unitary QCA; causal CPTP for open systems is only discussed as boundary cases in §9 and not included in the core conclusions of static block equivalent formulations.

### 1.3 Paper Structure

This paper is organized as follows:

- **§2** Establishes formal definitions of QCA and quantum configuration spaces
- **§3** Defines static block quantum structures and spacetime quantum graphs
- **§4** Establishes quantum subshift and Quantum Subshift of Finite Type (QSFT) formulations
- **§5** States the QCA structure theorem
- **§6** Proves existence and uniqueness of static blocks and local dependency cones
- **§7** Discusses translation-invariant QCA diagonalizable in momentum representation
- **§8** Introduces Pauli-Fourier expansion of local superoperators
- **§9** States reversibility and history states and their significance for static blocks
- **§10** Applications: quantum computational optimization, reversibility and classical embedding, philosophical implications
- **§11** Discusses complexity and undecidability boundaries
- **§12** Conclusions and prospects

---

## §2 Formal Definition of Quantum Cellular Automata

### Definition 2.1 (Quantum Cellular Automaton)

A $d$-dimensional quantum cellular automaton is defined as a quadruple $\mathcal{Q} = (\mathbb{Z}^d, \mathcal{H}_\Sigma, N, \alpha)$, where:

- $\mathbb{Z}^d$ is the set of spatial lattice points
- $\mathcal{H}_\Sigma$ is a finite-dimensional Hilbert space (e.g., qubit $\mathbb{C}^2$)
- $N \subset \mathbb{Z}^d$ is a finite neighborhood set (e.g., von Neumann neighborhood $\{ \mathbf{n} \in \mathbb{Z}^d : \|\mathbf{n}\|_1 \le 1 \}$ or Moore neighborhood $\{ \mathbf{n} \in \mathbb{Z}^d : \|\mathbf{n}\|_\infty \le 1 \}$)
- $\alpha: \mathcal{A} \to \mathcal{A}$ is a causal, translation-invariant *-automorphism (invertible) on the quasi-local $C^*$-algebra $\mathcal{A}$, where $\mathcal{A} = \bigotimes_{\mathbf{r} \in \mathbb{Z}^d} \mathcal{B}(\mathcal{H}_\Sigma)$

**Remark 2.1**: This paper uses two equivalent characterizations: causal *-automorphisms on quasi-local $C^*$-algebras; or finite-depth, translation-invariant layered local unitary circuits (Margolus partitioning scheme). Gates within a single layer are pairwise non-overlapping, with no commutativity assumption required.

### Definition 2.2 (Neighborhood Radius)

Let $r := \max_{\mathbf{n} \in N} \|\mathbf{n}\|_1$ be the $L_1$ radius of the neighborhood, where $\|\mathbf{n}\|_1 = \sum_{i=1}^d |n_i|$.

### Definition 2.3 (Quantum Configuration Space)

Let the quantum configuration space $X = \bigotimes_{\mathbf{r} \in \mathbb{Z}^d} \mathcal{H}_\Sigma$ be endowed with the product topology. The state space of the quasi-local algebra $\mathcal{A}$ is compact in the weak-* topology.

**Remark 2.2 (Clarification)**: This Hilbert space tensor product is the natural foundation of QCA, with no ambiguity.

### Definition 2.4 (Global Mapping)

Global evolution $\alpha = \mathrm{Ad}_U$, where $U$ is implemented by finite-depth, translation-invariant layered local gates (Margolus partitioning). In the Schrödinger picture, density matrices evolve as $\rho \mapsto U \rho U^\dagger$. We do not use closed expressions for local densities/partial traces to avoid inaccuracies when entanglement is present (avoiding quantum marginal problems).

### Definition 2.5 (Shift Mapping)

For any $\mathbf{v} \in \mathbb{Z}^d$, define the shift action $\sigma^\mathbf{v}: X \to X$ as

$$
(\sigma^\mathbf{v} \psi)(\mathbf{r}) = \psi(\mathbf{r} + \mathbf{v})
$$

---

## §3 Static Block: Spacetime Quantum Graphs

### Remark 3.1 (Semantic Clarification: Static Block as State)

We treat the static block $\mathcal{M}$ as a state on the spacetime quasi-local $C^*$-algebra $\mathcal{A}^{\mathrm{st}}$ (or equivalently, a compatible family of local states $\{\omega_\Omega\}$ on all finite spacetime windows $\Omega\subset\mathbb{Z}^{d+1}$). The single-site notation $\mathcal{M}(\mathbf{r},t)\in\mathcal{D}(\mathcal{H}_\Sigma)$ in the text is only for visualization; the actual semantics is always marginal states on finite windows; local marginals do not form independent dynamics when entanglement exists.

### Definition 3.1 (Spacetime Quantum Graph)

A spacetime quantum graph $\mathcal{M}: \mathbb{Z}^d \times \mathbb{N} \to \mathcal{D}(\mathcal{H}_\Sigma)$ is a function defined on spacetime lattice points, satisfying local unitary consistency constraints, rather than being defined by dynamic iteration $G^t$. These constraints are implemented through finite sets of spatiotemporal local projections (see §4).

**Remark 3.2**: To avoid circular definitions, we axiomatically define static blocks independently of dynamic iteration: they satisfy global constraint equation systems, ensuring predictive equivalence with the dynamic perspective.

### Definition 3.2 (Static Block)

We call $\mathcal{M}$ a static block quantum structure, which is a state function defined on $\mathbb{Z}^{d+1}$, satisfying the following **local unitary consistency constraints** (encoded through local projections).

**Explanation**: "Static block" refers to the overall quantum object $\mathcal{M}$ obtained by treating time as an additional coordinate, which satisfies finite circuit consistency projections and forms a closed invariant set under shift actions. This formulation is an equivalent mathematical restatement of dynamic evolution.

### Definition 3.3 (Bidirectional Static Block)

Since $\alpha$ is a *-automorphism (invertible), a bidirectional static block can be defined on $t \in \mathbb{Z}$:

$$
\mathcal{M}: \mathbb{Z}^d \times \mathbb{Z} \to \mathcal{D}(\mathcal{H}_\Sigma)
$$

### Definition 3.4 (Spacetime Shift Invariance)

Define the spacetime shift $\sigma^{(\mathbf{v},\tau)}: \mathcal{D}(\mathcal{H}^{\mathbb{Z}^{d+1}}) \to \mathcal{D}(\mathcal{H}^{\mathbb{Z}^{d+1}})$ as

$$
\big(\sigma^{(\mathbf{v},\tau)}\mathcal{M}\big)(\mathbf{r},t) = \mathcal{M}(\mathbf{r}+\mathbf{v}, t+\tau)
$$

The set of static blocks remains invariant under all spatial and temporal shifts.

### Remark 3.3 (Observer Perspective)

The observed "evolution" is a projection and sequential reading of $\mathcal{M}$ on slices $t = \mathrm{const}$:

$$
\mathcal{O}_t: \mathcal{M} \mapsto \mathcal{M}_t = \{ (\mathbf{r}, \rho) \mid \mathcal{M}(\mathbf{r}, t) = \rho \}
$$

This reinterprets dynamic evolution as sequential access to a static quantum structure. This theory applies to closed systems; if measurements are introduced, collapse would destroy global consistency, requiring extension to many-worlds interpretations.

---

## §4 Quantum Subshift and Quantum Subshift of Finite Type (QSFT) Formulation

### Definition 4.1 (Quantum Forbidden Pattern Set)

Given finite sets of spatiotemporal local projections $\{\Pi_a\}_{a=1}^m$, each $\Pi_a$ acts on finite spacetime windows $\Omega_a \subset \mathbb{Z}^{d+1}$. These projections encode circuit consistency/causal propagation/wire matching (history state techniques).

### Definition 4.2 (Quantum Subshift of Finite Type)

The set of all spacetime quantum graphs satisfying the constraints

$$
Y := \{ \mathcal{M} : \forall a, \ \Pi_a \text{ satisfies (zero energy) on restriction to } \Omega_a \}
$$

is a **Quantum Subshift of Finite Type (QSFT)**, and remains invariant under all spatial and temporal shift actions. Causal/update consistency of QCA can be characterized by finite circuit consistency projections.

### Proposition 4.1 (QSFT Characterization)

The static block $\mathcal{M}$ is an element of the QSFT $Y$, and "evolution" is a temporal slice reading of $Y$.

**Proof**: By Definition 3.1 and Definition 4.1, $\mathcal{M}$ satisfies local projection constraints, therefore $\mathcal{M} \in Y$. The temporal slice $\mathcal{M}_t$ corresponds to the projection at fixed $t$. $\square$

### Remark 4.1 (Significance of QSFT)

This aligns the "full spacetime quantum graphs subject to finite local projection constraints" with the standard framework of quantum symbolic dynamical systems.

---

## §5 QCA Structure Theorem

### Theorem 5.1 (QCA Structure Theorem)

On $\mathbb{Z}^d$, any translation-invariant, causal, invertible quantum evolution $\alpha$ (*-automorphism of $\mathcal{A}$) can be implemented by finite-depth, translation-invariant layered local unitary circuits (Margolus partitioning or its higher-dimensional generalizations). Conversely, any such circuit-induced $\alpha$ satisfies causality and translation invariance.

**Significance**: This theorem provides a structural characterization of QCA and ensures that the locality of "static block" constraints is both sufficient and necessary. We do not use the formulation "continuous unitary and commuting with shifts" to avoid topological ambiguities.

**Remark 5.1**: Assuming $\mathcal{H}_\Sigma$ is finite-dimensional, otherwise the theorem requires additional conditions. Equivalent formulations can be written in the Heisenberg picture as $\alpha = \mathrm{Ad}_U$, and in the Schrödinger picture as $\rho \mapsto U \rho U^\dagger$. See references for proofs.

**Reference**: Schumacher & Werner (2004), arXiv:quant-ph/0405174

---

## §6 Existence, Uniqueness, and Local Dependence of Static Blocks

### Lemma 6.1 (Local Dependency Cone)

Let the $L_1$ radius of the QCA neighborhood $N$ be $r$. Then for any $\mathbf{r}_0 \in \mathbb{Z}^d$, $t \in \mathbb{N}$, we have

$$
\mathcal{M}(\mathbf{r}_0, t) \text{ depends only on initial } \rho_0 \restriction_{B_{L_1}(\mathbf{r}_0; rt)}
$$

where $B_{L_1}(\mathbf{r}_0; rt) = \{ \mathbf{r} \in \mathbb{Z}^d : \|\mathbf{r} - \mathbf{r}_0\|_1 \le rt \}$.

We use "dependency cone ($L_1$-cone)" rather than "light cone" to avoid implications of relativistic Lorentz invariance. Changing norms only results in constant factor changes.

**Proof**: By induction on $t$.

- **Base case** ($t=0$): $\mathcal{M}(\mathbf{r}_0, 0) = \rho_0(\mathbf{r}_0)$ depends only on $\rho_0(\mathbf{r}_0)$, satisfying the condition.

- **Inductive step**: Assuming the statement holds for $t$, then $\mathcal{M}(\mathbf{r}_0, t+1)$ is obtained from the same neighborhood states at time $t$ through unitary operations. Since $\|\mathbf{n}\|_1 \le r$, the dependency region is contained in $B_{L_1}(\mathbf{r}_0; r(t+1))$. $\square$

### Remark 6.1 (Dependency Cone)

In the 1D case, this is equivalent to the interval $[\mathbf{r}_0 - rt, \mathbf{r}_0 + rt]$; in higher dimensions, it corresponds to the $L_1$ ball centered at $\mathbf{r}_0$. Unlike relativistic light cones, there is no Lorentz symmetry here.

### Theorem 6.1 (Existence and Uniqueness of Spacetime Quantum Graphs)

Given $(N, \alpha)$ and initial $\rho_0$, the spacetime quantum graph $\mathcal{M}$ exists and is unique.

**Proof**:

- **Existence (Constructive History State)**: Take a finite-depth layered local circuit $U=\prod_{\ell=1}^{T}U^{(\ell)}$ of finite duration $T$. On finite box $\Lambda=L^d\times[0,T]$, introduce finite consistency projections $\{\Pi_a\}$ (clock, gate action, wire matching, causal connectivity). The zero-energy subspace of the finite-volume Hamiltonian $H_\Lambda=\sum_a\Pi_a$ is non-empty (witnessed by Feynman-Kitaev history state construction). Let $\Lambda\uparrow\mathbb{Z}^{d+1}$ take the net limit to obtain the limit state $\omega$ of $\mathcal{A}^{\mathrm{st}}$; its local marginals define the static block $\mathcal{M}$.

- **Uniqueness**: Suppose there exist two different $\mathcal{M}_1, \mathcal{M}_2$ satisfying initial $\rho_0$ and local projection constraints, then there must be some $(\mathbf{r}_0, t_0)$ such that $\operatorname{Tr} | \mathcal{M}_1(\mathbf{r}_0, t_0) - \mathcal{M}_2(\mathbf{r}_0, t_0) | > 0$. Taking the smallest $t_0$, at time $t_0$ they must already differ on the neighborhood of $\mathbf{r}_0$, which contradicts their agreement at time $t_0 - 1$. $\square$

### Remark 6.2 (Uniqueness for Fixed Initial State)

This is uniqueness for a fixed initial $\rho_0$. From the QSFT perspective, $Y$ may contain multiple elements.

---

## §7 Translation-Invariant QCA Diagonalizable in Momentum Representation (Example Classes)

We take translation-invariant classes such as quantum walks/Clifford/free fermions as examples: their Bloch-momentum representation $U(k)$ can be block-diagonalized.

### Definition 7.1 (Linear QCA)

When $\alpha$ is linear in momentum representation, $\alpha$ is a quantum convolution operator on the abelian group $\mathbb{Z}^d$.

### Proposition 7.1 (Group Fourier Diagonalization)

For translation-invariant linear QCA, the transfer operator can be block-diagonalized in momentum representation (group Fourier on $\mathbb{Z}^d$):

- **Finite volume periodic boundaries**: Obtain discrete frequency eigenmodes
- **Infinite lattice**: Use characters $\chi_\xi(\mathbf{r}) = e^{2\pi i \langle \xi, \mathbf{r} \rangle}$ for spectral analysis (under $L^2$ conditions)

This provides orthogonal decomposition and spectral radius/propagation cone conclusions. We acknowledge difficulties with non-$L^2$ initial states and distinguish boundary effects.

**Remark 7.1**: For infinite lattice cases, the group Fourier transform exists in the $L^2(\mathbb{Z}^d)$ square-integrable function space, requiring appropriate boundary conditions to ensure convergence of spectral analysis. Hilbert space is a natural tool here, with no ambiguity.

### Example 7.1 (Quantum Walk QCA)

In 1D periodic boundaries, quantum walk QCA is equivalent to quantum convolution action on generating polynomials; the spectrum is given at unit roots. This exhibits the dependency cone structure.

**Visualization Description**: Quantum walk static blocks exhibit interference patterns. Given initial $\rho_0 = |\delta_0\rangle\langle\delta_0|$, the static block $\mathcal{M}(r,t)$ at position $r$ and time $t$ is given by quantum walk amplitudes, forming interference patterns. This pattern clearly demonstrates "evolution" as temporal slice reading of a static block: the entire interference pattern pre-exists, and observers merely access its different levels in temporal order.

### Remark 7.2 (Group Ring Representation)

By embedding quantum state spaces into vector spaces, linear rules correspond to quantum convolution actions in group rings.

---

## §8 Pauli-Fourier Expansion of Local Superoperators

### Definition 8.1 (Pauli-Fourier Expansion)

Let $\{\sigma_S\}$ be the Pauli tensor basis, $\langle X,Y\rangle_{HS}=2^{-|\Lambda|}\mathrm{Tr}(X^\dagger Y)$. The expansion of any operator $A$ is

$$
A=\sum_S \widehat{A}(S)\,\sigma_S,\quad \widehat{A}(S)=\langle \sigma_S,A\rangle_{HS}
$$

For local superoperators $\mathcal{E}$ (Heisenberg picture),

$$
\mathcal{E}(\sigma_T)=\sum_S \widehat{\mathcal{E}}(S\!\leftarrow\!T)\,\sigma_S,\quad
\widehat{\mathcal{E}}(S\!\leftarrow\!T)=\langle \sigma_S,\mathcal{E}(\sigma_T)\rangle_{HS}
$$

These coefficients describe coupling strength from "incident basis element $T$" to "output basis element $S$". This expansion is only a representation tool and does not imply separable dynamics.

### Proposition 8.1 (Walsh Coefficients)

The coefficients $\widehat{\mathcal{E}}(S\!\leftarrow\!T)$ satisfy the above formula and prove orthogonality.

**Proof**: By orthogonality of Hilbert-Schmidt inner product, $\langle \sigma_S, \sigma_T \rangle_{HS} = \delta_{ST}$, therefore the expansion is unique. $\square$

### Remark 8.1 (Representation Tool)

Important: This is an orthogonal expansion in function space, not implying that global dynamics can be decomposed or "uncoupled". We use it only as a representation tool, not as proof of dynamical independence. Unlike classical Walsh expansion, this is spectral analysis of quantum operators.

**Reference**: Montanaro & Osborne (2010)

---

## §9 Reversibility and History States and Their Significance for Static Blocks

### Definition 9.1 (Quantum Pre-injective)

A mapping $\alpha: \mathcal{A} \to \mathcal{A}$ is called **quantum pre-injective** if for any finite set $F \subset \mathbb{Z}^d$ and any two initial states $\omega \neq \nu$, as long as they agree on the complement, we have $\omega \circ \alpha \neq \nu \circ \alpha$.

**Remark 9.1**: Only for heuristic characterization, not used for key equivalence theorems.

### Proposition 9.1 (Reversibility and Bidirectional History)

If the global evolution $\alpha$ is a *-automorphism (invertible), then bidirectional static blocks $\mathbb{Z}^d \times \mathbb{Z}$ exist. If $\alpha$ degenerates to non-invertible causal CPTP mappings, then generally only forward history consistency can be guaranteed.

**Reference**: Farrelly & Short (2014)

### Corollary 9.1 (Garden-of-Eden Patterns and Reversibility)

- Absence of "quantum Garden-of-Eden patterns" (unreachable densities) is related to surjectivity, but surjectivity $\neq$ bijectivity
- Reversibility $\Rightarrow$ bidirectional static blocks exist
- If not invertible, only forward static blocks $\mathbb{Z}^d \times \mathbb{N}$ can be constructed

### Remark 9.2 (Bidirectionality and Reversibility)

This directly connects the bidirectionality of the "eternal block" with unitary reversible properties, avoiding disconnection between philosophical and mathematical levels. We do not use the equivalence "surjective $\Leftrightarrow$ pre-injective" to avoid overstepping statements.

---

## §10 Applications and Discussion

### 10.1 Quantum Computational Applications

#### Proposition 10.1 (Parallel Optimization)

The static block framework can optimize simulation: large spacetime quantum segments can be generated in parallel from the block perspective. For radius $r$ 1D QCA, the density at $(\mathbf{r}_0, t)$ depends only on the initial interval $[\mathbf{r}_0 - rt, \mathbf{r}_0 + rt]$.

**Proof**: Directly follows from Lemma 6.1 (local dependency cone). $\square$

#### Remark 10.1 (Linear QCA Acceleration)

In linear rules, $t$ steps of evaluation can be organized into $\tilde{O}(\log t)$ rounds of parallel composition by constructing $\alpha^{2^k}$ (such as quantum FFT); achievable when exponentially accelerated spectral/power structures exist, with Clifford/free or diagonal-in-Fourier as examples. General nonlinear QCA still have $\Omega(t)$ depth lower bounds.

### 10.2 Reversibility and Classical Embedding

#### Proposition 10.2 (Classical Embedding Prerequisites)

Only when the global evolution $\alpha$ is a *-automorphism can it be embedded in classical space; non-invertible QCA can be converted to reversible by introducing auxiliary qubits, then embedded in classical frameworks.

**Proof Outline**: Reversibility guarantees information conservation, allowing bijective mapping of classical bits. Non-invertible cases require introducing "garbage" bits to record history, implementing Bennett's trick. $\square$

#### Remark 10.2 (Limiting Conditions)

Reversibility is a necessary but not sufficient condition for classical embedding. Here we explicitly limit the scope of application.

### 10.3 Philosophical Implications: Analogy with Eternalism

#### Definition 10.1 (Eternalist Perspective)

In the eternalism framework, time is the order of observation, and evolution is projection

$$
\mathcal{O}_t: \mathcal{M} \to \mathcal{M}_t = \{ (\mathbf{r}, \rho) \mid \mathcal{M}(\mathbf{r}, t) = \rho \}
$$

This bridges QCA with quantum block universe: local entanglement is compatible with global invariance. We distinguish mathematical staticity (equivalent formulation), computational equivalence (same predictions), and philosophical interpretation (metaphysical stance on the nature of time).

**Reference**: 't Hooft (2016), Barbour (1999)

#### Remark 10.3 (Limitations of Analogy)

It must be emphasized that the analogy between QCA static blocks and physical quantum block universe is heuristic rather than literal. In QCA, time is a discrete parameter, while in quantum field theory time is continuous; QCA's unitary evolution and general relativity's curvature also have differences. The value of this analogy lies in providing a model for thinking about "quantum time as coordinate".

#### Remark 10.4 (Epistemology and Ontology)

The static perspective cannot epistemologically replace the dynamic simulation perspective, because finite observers must explore this static quantum structure through dynamic processes. Static blocks describe the mathematical level of overall equivalent formulation, while dynamic evolution describes the sequential process that finite observers follow in exploring this structure through computational simulation within the same mathematical framework. We do not claim ontological priority.

### 10.4 Limitations

#### Limitation 10.1 (Infinite Storage)

Infinite grids require infinite qubits; actual simulations can only handle finite subsets.

#### Limitation 10.2 (Computational Feasibility)

The construction of static blocks exists theoretically, but actual computation is limited by quantum resources.

---

## §11 Discussion of Complexity and Undecidability Boundaries

### Remark 11.1 (Decidability Boundaries)

For $d+1\ge2$, several decision problems of quantum SFT defined by finite sets of spatiotemporal local projections (such as emptiness/periodicity) are typically in the same highly intractable category as quantum satisfiability/tiling problems, lacking unified decidable algorithms. Under restricted subclasses in 1D (e.g., finite-depth layered, finite alphabet clocks, commutative consistency projections), certain properties can be constructively decided; general 1D scenarios still require case-by-case analysis.

### Proposition 11.1 (Emptiness Problem)

Deciding $Y = \varnothing$ is generally undecidable, in the same highly intractable category as quantum satisfiability/tiling problems. We do not provide specific reductions, only intuitive difficulty alignment explanations.

**Reference**: Cubitt et al. (2015)

### Proposition 11.2 (Periodicity and Entanglement Entropy)

Existence of periodicity and entanglement entropy computation are also generally undecidable or highly difficult (related to high-dimensional quantum tiling).

### Corollary 11.1 (Existence Boundary)

"There exists a static block satisfying given local projection constraints" has no unified algorithm in high dimensions; this defines the computational boundary of the static perspective.

**Proof Outline**: Through reduction to quantum satisfiability problems (QMA-complete), inheriting their undecidability. $\square$

### Remark 11.2 (Decidable Subclasses)

In linear cases, computable spectra and propagation bounds can be obtained, while decision problems for nonlinear, infinite lattice, and high-dimensional cases must be carefully limited to decidable subclasses (such as 1D, linear/Clifford cases) or adopt semi-decision/approximation methods.

### Remark 11.3 (Boundary of "Can and Cannot")

This section echoes the QSFT/reversibility framework above, providing readers with a clear map of the boundary between "can and cannot".

---

## §12 Conclusions and Prospects

### 12.1 Main Contributions

Static Block Quantum Cellular Automata Theory reconstructs QCA as eternal quantum state bodies, consisting of full spacetime quantum objects defined by finite local projection constraints. This framework is logically self-consistent and provides new perspectives for understanding the nature of quantum time and computation. We use quantum topological dynamics and quantum Fourier analysis to ensure rigor, and eliminate potential ambiguities through clarifying the natural role of Hilbert space and structure theorems.

### 12.2 Core Insights

1. **Mathematical level**: QCA "evolution" is sequential reading of static blocks, not true dynamic change
2. **Mathematical characterization**: Through QSFT and QCA structure theorem, a rigorous quantum topological dynamics foundation is established
3. **Computational boundaries**: Through reversibility and history states and undecidability results, the scope of the theory is clarified
4. **Philosophical implications**: Bridges quantum computational models with quantum block universe theory, while clarifying the limitations of analogies

### 12.3 Theoretical Positioning

This theory provides a static formulation framework for QCA, mathematically equivalent to the dynamic perspective and predictively consistent. We do not claim ontological priority for the static perspective, but rather position it as a complementary tool for understanding quantum evolution.

### 12.4 Future Directions

1. **Quantum field extensions**: Extend to quantum field QCA or complex quantum system simulation
2. **High-dimensional analysis**: Deepen research on decidable subclasses of high-dimensional QSFT
3. **Physical applications**: Explore deep connections with quantum gravity and holographic principles
4. **Computational optimization**: Develop efficient quantum parallel algorithms based on static block perspectives
5. **Measurement theory**: Extend to many-worlds interpretation frameworks including measurement processes

---

## References

1. Feynman, R. P. (1982). Simulating Physics with Computers. *International Journal of Theoretical Physics* 21, 467–488.
2. Schumacher, B., & Werner, R. F. (2004). Reversible Quantum Cellular Automata. arXiv:quant-ph/0405174.
3. Arrighi, P., Nesme, V., & Werner, R. (2011). Unitarity plus Causality implies Localizability. *Journal of Computer and System Sciences* 77, 372–378.
4. 't Hooft, G. (2016). *The Cellular Automaton Interpretation of Quantum Mechanics*. Springer.
5. Farrelly, T., & Short, A. J. (2014). Causal Fermions in Discrete Spacetime. *Physical Review A* 89, 012302.
6. Montanaro, A., & Osborne, T. J. (2010). Quantum Boolean Functions. *Chicago Journal of Theoretical Computer Science* 2010, Article 1.
7. Cubitt, T. S., Perez-Garcia, D., & Wolf, M. M. (2015). Undecidability of the Spectral Gap. *Nature* 528, 207–211.
8. Barbour, J. (1999). *The End of Time*. Oxford University Press.
9. Gross, D., Nesme, V., Vogts, H., & Werner, R. F. (2012). Index Theory of One-Dimensional Quantum Walks and Cellular Automata. *Communications in Mathematical Physics* 310, 419–454.
10. Arrighi, P. (2019). An Overview of Quantum Cellular Automata. *Natural Computing* 18, 885–899.
11. Kitaev, A. Y., Shen, A., & Vyalyi, M. (2002). *Classical and Quantum Computation*. American Mathematical Society.
12. Haah, J., & Fidkowski, L. (2018). Nontrivial Quantum Cellular Automata in Higher Dimensions. arXiv:1812.01625.

---

**Acknowledgments**

Thanks to the inspiration from the original classical theory and feedback from reviewers in the quantum computation field, ensuring that this paper meets standards in mathematical rigor and logical self-consistency. Special thanks for pointing out key feedback on circular definitions, measurement problems, Hilbert space semantics, decidability boundaries, etc., which enabled the refinement of this theory.

**Version Notes**

v1.3 (2025-10-17): Final revision based on comprehensive review feedback, unifying static blocks as spacetime quasi-local algebra states, providing constructive history states for existence, reducing 1D QSFT decidability to restricted subclasses, standardizing Pauli-Fourier formulas, clarifying theoretical positioning as equivalent formulation framework, etc., ensuring mathematical self-consistency and accurate physical semantics; containing complete formal definitions, theorem proofs, and application discussions.
