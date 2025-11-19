**3.3 Discrete Noether Theorem: Symmetry, Conserved Currents, and Unitarity on Lattices**

In continuous spacetime and field theory, Noether theorem is a bridge connecting physical symmetry and conservation laws. For discrete Quantum Cellular Automata (QCA) universe, spacetime translations are no longer continuous groups, but discrete groups (such as $\mathbb{Z}$). This seems to pose a challenge to direct application of Noether theorem. However, this section will prove that under the algebraic axiomatic system of QCA, not only does Noether theorem still hold, but its form is more rigorous and fundamental. We will show how symmetry directly constrains the structure of update operator $U$ and derive discrete continuity equations on lattices.

### 3.3.1 Algebraic Definition of Dynamical Symmetry

In QCA universe $\mathfrak{U} = (\Lambda, \mathcal{A}, U)$, symmetry no longer manifests as variational invariance of Lagrangian, but as **superoperator commutation relations** on algebras.

**Definition 3.3.1 (Dynamical Symmetry)**

Let $\mathcal{S}$ be a transformation group acting on total algebra $\mathcal{A}$ (such as translation group, rotation group, or internal gauge group $SU(N)$). For any element $g \in \mathcal{S}$ in the group, its representation on quantum states or operators is unitary operator $V_g$. If update operator $U$ commutes with $V_g$, i.e.:

$$
[U, V_g] = 0 \quad \text{or equivalently} \quad \alpha(V_g^\dagger A V_g) = V_g^\dagger \alpha(A) V_g
$$

then $g$ is called a symmetry of dynamics.

For continuous parameter Lie group symmetries (such as global phase transformation $e^{i\theta Q}$), if $U$ satisfies $[U, e^{i\theta Q}] = 0$ for all $\theta$, then by differentiating with respect to $\theta$:

$$
[U, Q] = 0
$$

This shows that generator $Q$ (as a global observable) is conserved under Heisenberg evolution, i.e., $\alpha(Q) = U^\dagger Q U = Q$. This is the **Global Discrete Noether Theorem**.

### 3.3.2 From Global Conservation to Local Current: Discrete Continuity Equation

More meaningful in physics is **local conservation laws**. If global charge $Q = \sum_x q_x$ is conserved, then on discrete lattices, change in charge of some cell necessarily accompanies current flowing to neighbors. For local QCA, this intuition can be strictly theoremized.

**Theorem 3.3.2 (Discrete Noether Theorem and Continuity Equation)**

Let $Q = \sum_{x \in \Lambda} q_x$ be a conserved quantity composed of local density operators $q_x$ (i.e., $[U, Q] = 0$), and $U$ satisfies structural locality (propagation radius $R$).

Then for any lattice site $x$ and time step $t$, there exists a set of **Current Operators** (Current Operators) $\mathcal{J}_{x \to y}(t)$ satisfying the following **Discrete Continuity Equation**:

$$
q_x(t+1) - q_x(t) + \sum_{y \in \mathcal{N}(x)} \mathcal{J}_{x \to y}(t) = 0
$$

where $\mathcal{J}_{x \to y}$ represents charge flow from $x$ to neighbor $y$, and current operators satisfy antisymmetry $\mathcal{J}_{x \to y} = -\mathcal{J}_{y \to x}$ (needs careful definition in operator sense, usually refers to net flow).

**Proof Construction**:

Consider Heisenberg evolution $q_x(t+1) = U^\dagger q_x(t) U$. Since $[U, Q] = 0$, we have $Q(t+1) = Q(t)$.

This does not mean $q_x(t+1) = q_x(t)$, but means the sum is unchanged.

According to locality of $U$, support set $\text{supp}(q_x(t+1))$ of operator $q_x(t+1)$ satisfies $\text{supp}(q_x(t+1)) \subset \mathcal{N}(x)$.

We can decompose $U^\dagger q_x U$ as:

$$
U^\dagger q_x U = q_x + \sum_{y \in \mathcal{N}(x)} J_{y \to x}
$$

The specific construction depends on Margolus blocking or local unitary decomposition. For one-dimensional systems, if $U$ is composed of local gates $u_{x, x+1}$, then current operator $J_{x, x+1}$ spanning bond $(x, x+1)$ can be explicitly written as the difference of local charges before and after gate operation.

$\square$

This equation is not only a conservation format in numerical computation, but also a mathematical guarantee that "charge" cannot be transmitted instantaneously over distance.

### 3.3.3 Unitarity as Fundamental Conservation Law: Conservation of Quantum Information

Among all conservation laws, the most fundamental is **probability conservation** (or information conservation), which corresponds to unitarity (Unitarity) of evolution operator $U$. This can be seen as invariance of physical laws under global phase transformation $e^{i\theta}$ ($U(1)$ symmetry).

**Proposition 3.3.3 (Unitarity and Information Indestructibility)**

Update operator of QCA satisfies $U^\dagger U = U U^\dagger = \mathbb{1}$, which is equivalent to modulus conservation in Hilbert space $\langle \psi(t+1) | \psi(t+1) \rangle = \langle \psi(t) | \psi(t) \rangle$.

In discrete ontology, this corresponds to **conservation of total quantum information**. If quantum states are regarded as carriers of information, unitarity guarantees that information can neither be created from nothing nor completely erased (though it can become non-locally readable due to scrambling).

This property is crucial in black hole physics. Under our QCA framework, even processes simulating black hole evaporation, since underlying evolution $U$ is strictly unitary, information paradox (Information Paradox) does not exist at the ontological level. Apparent information loss is merely because we restrict local algebras to outside horizons, ignoring degrees of freedom flowing inward or entangled radiation.

### 3.3.4 Symmetry Breaking and Restoration: Goldstone Modes on Discrete Lattices

On discrete lattices, certain continuous symmetries (such as Lorentz boosts and continuous rotations in Poincaré group) are explicitly broken (Explicitly Broken) at microscopic level. Lattices only have discrete rotational symmetry (such as $\mathbb{Z}_4$) and discrete translational symmetry ($\mathbb{Z}^d$).

**Question**: If microscopic symmetry is broken, where do angular momentum conservation and Lorentz invariance in macroscopic continuous physics come from?

This will be answered in detail in Chapter 4 "Emergence of Field Theory from Discrete to Continuous." In short, when we observe QCA in the long-wavelength limit ($k \to 0$), lattice effects are averaged out, and continuous symmetries are restored as **Accidental Symmetries**. Discrete Noether theorem guarantees that corresponding "quasi-conserved quantities" (such as lattice momentum) smoothly transition to continuous conserved quantities (physical momentum) in the low-energy limit.

**Summary**

This section proved that discreteness and locality do not prevent physical conservation laws from holding. On the contrary, QCA framework provides a divergence-free, constructive way to define "currents" and "charges."

1. **Global Symmetry** $[U, V_g] = 0$ guarantees conservation of global charges.

2. **Structural Locality** guarantees conservation laws satisfy local continuity equations.

3. **Unitarity** guarantees conservation of most fundamental information ontology.

These conservation laws constitute the "skeleton" of physical reality, constraining the form of discrete dynamics, making it not just a mathematical game, but a self-consistent physical universe model. Next, we will explore how these abstract dynamics produce complex computational structures—computational universality.

