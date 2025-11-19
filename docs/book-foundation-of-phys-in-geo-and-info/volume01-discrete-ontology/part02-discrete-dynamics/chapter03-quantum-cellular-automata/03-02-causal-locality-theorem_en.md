**3.2 Causal Locality Theorem: Deriving Strict Light Cone Structure from Finite Propagation Radius**

In Section 3.1, we established the kinematic foundation of QCA universe and introduced the dynamical core—local unitary update operator $U$. This section will prove that it is precisely the algebraic locality (Algebraic Locality) of $U$ that strictly derives the crucial **Light Cone Structure** in physics on discrete graph background.

In continuous quantum field theory, causality is usually imposed as an axiom a priori (e.g., microcausality axiom: field operators at spacelike separation commute). But in the discrete ontology of this book, causality is not an a priori assumption, but a **emergent** theorem from microscopic discrete dynamics. We will prove that there exists a strict upper bound on information propagation speed, which manifests as light speed $c$ in the macroscopic limit.

### 3.2.1 Algebraic Support and Heisenberg Evolution

To mathematically describe "information propagation," we need to examine evolution of observables (operators) over time in Heisenberg picture (Heisenberg Picture).

**Definition 3.2.1 (Support Set of Operator)**

For a local operator $O$ in total algebra $\mathcal{A}$, if it acts non-trivially only on subset $R \subset \Lambda$ (i.e., acts as identity operator $\mathbb{1}$ on complement of $R$), then $R$ is called the **support set** of this operator, denoted $\text{supp}(O)$.

Formally, if $O \in \mathcal{A}_R \otimes \mathbb{1}_{\Lambda \setminus R}$, then $\text{supp}(O) \subseteq R$.

**Definition 3.2.2 (Dynamical Mapping)**

Let $U$ be the one-step update operator of QCA. For any operator $A \in \mathcal{A}$, its one-step time evolution is given by automorphism $\alpha$:

$$
\alpha(A) = U^\dagger A U
$$

$t$-step evolution is denoted $\alpha^t(A) = (U^\dagger)^t A U^t$.

### 3.2.2 Strict Locality Theorem

Lieb-Robinson bounds in continuous systems show that information propagation decays exponentially outside light cones, but mathematically still not strictly zero. In sharp contrast, the discrete structure of QCA guarantees **Strict** locality, i.e., information leakage outside light cones is strictly zero.

**Theorem 3.2.3 (Finite Propagation Radius Theorem)**

Let QCA update operator $U$ satisfy structural locality (Definition 3.1.2), i.e., for any single-point operator $A_x$ (supported on $x$), $\text{supp}(\alpha(A_x)) \subset \mathcal{N}(x)$, where $\mathcal{N}(x)$ is the finite neighborhood of $x$.

Then for any local operator $O$ and its $t$-step evolution $\alpha^t(O)$, there exists a finite region $\mathcal{C}_t(\text{supp}(O))$ depending only on graph structure and $t$, such that:

$$
\text{supp}(\alpha^t(O)) \subseteq \mathcal{C}_t(\text{supp}(O))
$$

This region $\mathcal{C}_t$ grows linearly with time $t$.

**Proof**:

We proceed by induction on time step $t$.

1. **Base Case ($t=0$)**: $\alpha^0(O) = O$, support set unchanged.

2. **Inductive Step**: Assume at $t=k$, $\text{supp}(\alpha^k(O)) \subseteq R_k$.

    Consider $t=k+1$:

    $$
    \alpha^{k+1}(O) = \alpha(\alpha^k(O))
    $$

    Since $\alpha^k(O)$ can be decomposed as a linear combination of basis operators supported on $R_k$, and according to locality of $U$, operators supported on $y \in R_k$ evolve to have support within $\mathcal{N}(y)$.

    Therefore, support set of $\alpha^{k+1}(O)$ is contained in the neighborhood union of $R_k$:

    $$
    R_{k+1} = \bigcup_{y \in R_k} \mathcal{N}(y)
    $$

    If graph $\Lambda$ has uniform degree (e.g., lattice), and neighborhood radius is $r$, then linear scale (diameter) of $R_t$ grows at most by $2r$. This proves that expansion of support set is strictly bounded.

$\square$

### 3.2.3 Construction of Geometric Light Cone

Based on Theorem 3.2.3, we can define **geometric light cone** purely from graph-theoretic perspective.

**Definition 3.2.4 (Geometric Influence Cone)**

For spacetime point $(x, n) \in \Lambda \times \mathbb{Z}$, its **future geometric light cone** $C_{geo}^+(x, n)$ is defined as the set of all spacetime points that may be affected by perturbations at $x$ at time $n$:

$$
C_{geo}^+(x, n) = \{ (y, m) \in \Lambda \times \mathbb{Z} \mid m \ge n, \text{dist}(x, y) \le R \cdot (m-n) \}
$$

where $R$ is the propagation radius of $U$ (i.e., maximum graph distance of neighborhood). Similarly, **past geometric light cone** $C_{geo}^-(x, n)$ is the set of all points that may influence $(x, n)$.

This geometric definition gives the **Maximum Velocity** (Maximal Velocity) in QCA universe:

$$
v_{\max} = \frac{R}{\Delta t} \quad (\text{set } \Delta t = 1)
$$

This is the "light speed" $c$ in this discrete universe.

### 3.2.4 Causal Structure: From Commutators to Partial Order

Physical causality is usually defined as "possibility of signal transmission." In quantum mechanics, this corresponds to non-commutativity of two observables. If $[A, B] = 0$, then measuring $A$ does not affect statistical results of $B$, i.e., no signal transmission.

**Definition 3.2.5 (Causal Partial Order $\preceq$)**

Define relation $\preceq$ on event set $E = \Lambda \times \mathbb{Z}$: we say event $(x, n)$ **causally precedes** $(y, m)$, denoted $(x, n) \preceq (y, m)$, if there exist local operators $A \in \mathcal{A}_{\{x\}}$ and $B \in \mathcal{A}_{\{y\}}$ such that under Heisenberg evolution:

$$
[\alpha^{m-n}(A), B] \neq 0
$$

(Note: For $m < n$, defined as uncorrelated).

The following theorem establishes strict equivalence between QCA geometric structure and physical causality, which has profound significance in foundations of physics: **causal structure is not imposed, but a direct consequence of local dynamics**.

**Theorem 3.2.6 (Causal Locality Theorem)**

For any QCA universe satisfying locality conditions, its physical causal relation $\preceq$ is strictly contained in geometric light cone relation $\le_{geo}$. That is:

$$
(x, n) \preceq (y, m) \implies (y, m) \in C_{geo}^+(x, n)
$$

In other words, if $(y, m)$ lies outside the geometric light cone of $(x, n)$ (spacelike separation), then any local observables at the two points necessarily commute:

$$
\text{dist}(x, y) > R|m-n| \implies [\alpha^{m-n}(A_x), B_y] = 0
$$

**Proof**:

Let $\Delta t = m - n$. If $(y, m)$ is outside geometric light cone, i.e., $y \notin B_{R\Delta t}(x)$ (ball centered at $x$ with radius $R\Delta t$).

According to Finite Propagation Radius Theorem (Theorem 3.2.3), support set $\text{supp}(\alpha^{\Delta t}(A_x))$ of $\alpha^{\Delta t}(A_x)$ is contained within $B_{R\Delta t}(x)$.

Since $y \notin B_{R\Delta t}(x)$, $y$ does not intersect support set of $\alpha^{\Delta t}(A_x)$.

In quantum mechanics, operators with disjoint support sets (operators acting on different subsystems) always commute.

Therefore $[\alpha^{\Delta t}(A_x), B_y] = 0$.

QED.

### 3.2.5 Physical Picture: "Hardness" of Light Cone

In continuous quantum field theory, correlation functions outside light cones usually decay exponentially $e^{-m|x|}$ (e.g., in massive fields), leading to subtle discussions about superluminal influences (such as Hegerfeldt theorem).

However, this theorem shows that in discrete ontology, light cones are **Absolutely Hard**. Within $N$ steps of evolution, no information, energy, or entanglement can cross graph distance $N \times R$.

This conclusion lays the foundation for emergence of special relativity at discrete level. The causal structure of Minkowski spacetime ($ds^2 \ge 0$) is precisely the smooth approximation of the above discrete causal partial order $(E, \preceq)$ in the continuous limit. We will discuss this emergence mechanism in detail in Chapter 4.

