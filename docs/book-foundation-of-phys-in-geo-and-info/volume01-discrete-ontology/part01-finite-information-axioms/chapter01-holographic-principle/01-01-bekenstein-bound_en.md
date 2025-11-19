# Volume I: Discrete Ontology — Physical Foundations of Information

## Part I: Finite Information Axioms and State Space Geometry

### Chapter 1: Holographic Principle and Finiteness Axioms

**1.1 Rigorous Derivation of Bekenstein Bound and Planck Information Density**

The foundations of physics are usually built on the assumption of spacetime continuum. However, the combination of thermodynamics and general relativity—particularly advances in black hole physics—strongly suggests that the information capacity of physical reality is finite. This section aims to rigorously derive the Bekenstein Bound from first principles and thereby introduce the concept of Planck information density, providing physical justification for establishing the discrete Quantum Cellular Automata (QCA) ontology in subsequent chapters of this book.

#### 1.1.1 Geometric Duality of Entropy and Energy

Consider a weakly gravitating system in asymptotically flat spacetime, with spatial volume $V$, total energy $E$, and characteristic linear scale $R$. In classical thermodynamics, the entropy $S$ of a system can in principle be infinite (e.g., in continuous field theory, the number of modes in a given volume diverges with frequency cutoff). However, the intervention of gravity imposes a fundamental limitation: when energy density is too high, the system will collapse into a black hole.

To rigorously express this limitation, we introduce the concept of **Generalized Entropy**. Let $\rho$ be the quantum state of the system at some moment, $\sigma$ be the vacuum state (or thermal equilibrium state). According to the non-negativity of Quantum Relative Entropy, we have:

$$
S(\rho \| \sigma) = \mathrm{Tr}(\rho \ln \rho) - \mathrm{Tr}(\rho \ln \sigma) \ge 0
$$

If $\sigma$ is a Gibbs state $\sigma = Z^{-1} e^{-\beta H}$, where $\beta$ is inverse temperature and $H$ is the Hamiltonian (which can be taken as modular Hamiltonian $K$ in asymptotically flat background), then the relative entropy can be rewritten in the form of free energy difference:

$$
S(\rho \| \sigma) = \beta \langle H \rangle_\rho - S(\rho) - (\beta \langle H \rangle_\sigma - S(\sigma)) \ge 0
$$

From this we obtain $S(\rho) \le \beta (\langle H \rangle_\rho - F_\sigma)$. This shows that entropy is bounded by energy (or modular energy).

In gravitational background, Bekenstein originally argued through a thought experiment of adiabatically lowering an object with entropy $S$ and energy $E$ into a black hole that entropy must satisfy:

$$
S \le \frac{2\pi k_B R E}{\hbar c}
$$

where $k_B$ is Boltzmann's constant, $\hbar$ is reduced Planck's constant, and $c$ is the speed of light.

**Theorem 1.1.1 (Casini-Bekenstein Bound)**:

In quantum field theory, if we consider local algebra $\mathcal{A}(V)$ restricted to a Rindler Wedge or other region with Killing Horizon, and the region satisfies Quantum Null Energy Condition (QNEC), then for any local excited state $\rho$, its von Neumann entropy $S_V(\rho)$ and vacuum-subtracted energy $E_V$ satisfy:

$$
S_V(\rho) \le 2\pi \int_V \mathrm{d}^{d-1}x \, \xi \, T_{00}
$$

where $T_{00}$ is the energy-momentum tensor component, and $\xi$ is a weight function related to geometric scale. In the spherically symmetric and weak gravity limit, this inequality reduces to the form $S \le 2\pi R E / \hbar c$.

*Proof Outline*:

Based on monotonicity of relative entropy. Consider a spatial region $V$ with complement $\bar{V}$. The reduced density matrix of vacuum state $|\Omega\rangle$ on $V$ is $\sigma_V = \mathrm{Tr}_{\bar{V}} |\Omega\rangle\langle\Omega|$. According to Bisognano-Wichmann theorem, for Rindler wedge, $\sigma_V = e^{-K_V}/Z$, where $K_V$ is the modular Hamiltonian, and $K_V = 2\pi \int x T_{00} \mathrm{d}x$.

For any state $\rho_V$, its relative entropy with respect to vacuum $S(\rho_V \| \sigma_V) = \langle K_V \rangle_\rho - S(\rho_V) \ge 0$.

Assuming vacuum entropy $S(\sigma_V)$ is normalized to zero (or considering entropy difference), we have $S(\rho_V) \le \langle K_V \rangle_\rho$. Substituting the geometric form of modular Hamiltonian yields the inequality between entropy and energy moment. $\square$

#### 1.1.2 Planck Information Density and Holographic Cutoff

The above inequality not only limits entropy, but also reveals the problem of counting microscopic degrees of freedom. If we apply the above bound to a black hole, i.e., $R$ is the Schwarzschild radius $R_s = 2GE/c^2$, substituting into the inequality gives:

$$
S \le \frac{2\pi k_B R_s}{\hbar c} \left( \frac{c^4 R_s}{2G} \right) = \frac{\pi k_B c^3 R_s^2}{\hbar G} = \frac{k_B}{4} \frac{4\pi R_s^2}{l_P^2} = \frac{k_B A}{4 l_P^2}
$$

This is the famous Bekenstein-Hawking Entropy, where $l_P = \sqrt{\hbar G / c^3}$ is the Planck length, and $A$ is the horizon area.

This result shows that the maximum information content of a physical system is not proportional to its volume $V$, but to its boundary surface area $A$. This is called the **Holographic Principle**. However, for local physical processes that are not black holes, if we assume local flatness and have not reached black hole density, we can still define an **effective information density upper bound in volume sense**.

**Definition 1.1.2 (Planck Information Density)**:

Define the minimum resolvable volume element of physical reality as Planck volume $V_P \sim l_P^3$. For a macroscopic volume $V$, if the holographic bound is not saturated (i.e., in weak gravity limit), local field theory gives degrees of freedom that appear volume-extensive. But at the ontological level, to avoid UV divergences and be compatible with gravitational entropy, we must introduce a **Natural Cutoff**.

Let the maximum information capacity of the system be $I_{\max}$. If we require the theory to be self-consistent in all physical processes including black hole formation, then the information content $I$ in any sphere of radius $R$ must satisfy:

$$
I(R) \le \min \left( \frac{V}{l_P^3}, \frac{A}{4 l_P^2} \right)
$$

At microscopic scales ($R \to l_P$), the volume term and area term are of the same order. We define Planck information density as:

$$
\rho_{\text{info}} = \frac{1}{V_P \ln 2} \quad (\text{bits/unit volume})
$$

This means that physical space is not a continuum, but a grid with discrete information-carrying capacity.

#### 1.1.3 Physical Failure of Continuum Hypothesis

In traditional physics, the dimension of Hilbert space $\mathcal{H}$ is usually assumed to be infinite (e.g., $L^2(\mathbb{R}^3)$). However, from Theorem 1.1.1, if we restrict to a region with finite energy $E$ and finite scale $R$, the number of orthogonal states allowed by physics $W = e^{S/k_B}$ must be finite.

**Corollary 1.1.3 (Finiteness of Hilbert Space Dimension)**:

For any causally closed bounded region in the universe (e.g., a causal diamond or region within observer's horizon), the dimension $D = \dim(\mathcal{H}_{\text{phys}})$ of the corresponding physical Hilbert space $\mathcal{H}_{\text{phys}}$ must satisfy:

$$
\ln D \le \frac{A_{\partial V}}{4 l_P^2}
$$

where $A_{\partial V}$ is the area of the boundary of this region.

**Proof**: If $\dim(\mathcal{H}_{\text{phys}})$ is infinite, then there exist mixed states with arbitrarily large entropy (e.g., equal probability mixture of $N$ orthogonal bases, entropy is $\ln N$). This violates the Bekenstein bound. Therefore, physically realizable Hilbert spaces must be finite-dimensional. $\square$

This conclusion forms the cornerstone of **discrete ontology** in this book: the physical world at its foundation is not fields defined on continuous manifolds, but algebraic structures defined on finite-dimensional Hilbert spaces (composed of tensor products of many discrete cells). Continuous spacetime and quantum field theory are merely effective approximations of this discrete structure in the long-wavelength limit.

#### 1.1.4 From Bound to Axiom

Based on the above derivation, we establish the first core axiom in this book.

**Axiom A1 (Finite Information Density Axiom)**:

Physical reality consists of discrete information units. For any three-dimensional spatial volume $V$, the number of independent physical degrees of freedom $N(V)$ it contains is finite, and there exists a natural cutoff at Planck scale, such that local Hilbert space is isomorphic to tensor products of finite-dimensional complex spaces $\mathbb{C}^d$.

Specifically, we model the universe as a quantum system on a graph $G=(\Lambda, E)$, where each node $x \in \Lambda$ is associated with a finite-dimensional Hilbert space $\mathcal{H}_x$, such that the state space of the entire system is:

$$
\mathcal{H}_{\text{total}} = \bigotimes_{x \in \Lambda} \mathcal{H}_x
$$

The Bekenstein bound is no longer a derived limitation, but a manifestation of the natural geometric properties of this discrete structure in the continuous limit.

