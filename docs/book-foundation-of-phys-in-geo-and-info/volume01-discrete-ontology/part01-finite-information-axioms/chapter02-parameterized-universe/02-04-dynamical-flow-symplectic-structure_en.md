**2.4 Dynamical Flow and Symplectic Structure on Projective Hilbert Space $\mathbb{C}P^{N-1}$**

In previous sections, we revealed the dual geometric properties of quantum state space (projective Hilbert space $\mathbb{C}P^{N-1}$): on one hand, Riemannian metric $g_{\mu\nu}$ derived from distinguishability (Fisher information) endows it with "rigid" distance structure; on the other hand, Berry curvature $\Omega_{\mu\nu}$ derived from geometric phase (Berry phase) endows it with non-trivial topological structure.

This section will prove that these two structures are not isolated, but tightly coupled through complex structure (Complex Structure), together constituting a rigorous mathematical object—**Kähler Manifold**. More importantly, we will reveal that the dynamical equation of standard quantum mechanics—Schrödinger equation—is essentially classical Hamiltonian Flow on this curved phase space. This conclusion completely breaks the gap between "quantum" and "classical" in geometric form, showing that evolution of physical laws is essentially symplectic transformation of information geometry.

### 2.4.1 Kähler Manifold: Perfect Unification of Riemannian and Symplectic

In the "It from Bit" discrete ontology, physical states are described by finite-dimensional Hilbert spaces. We have seen that quantum geometric tensor $\chi_{\mu\nu}$ naturally decomposes into real and imaginary parts. This suggests that the underlying manifold structure has a certain "trinity" property.

**Definition 2.4.1 (Kähler Structure)**

Projective Hilbert space $\mathcal{M} = \mathbb{C}P^{N-1}$ is a Kähler manifold, meaning it simultaneously possesses the following three compatible geometric structures:

1. **Complex Structure $J$**: A linear map $J: T_p\mathcal{M} \to T_p\mathcal{M}$ satisfying $J^2 = -\mathbf{1}$, describing the operation of "multiplying by $i$" on tangent space.

2. **Riemannian Metric $g$**: Namely Fubini-Study metric (QFIM), satisfying $g(JX, JY) = g(X, Y)$, ensuring length invariance under complex rotation.

3. **Symplectic Form $\omega$**: A closed, non-degenerate antisymmetric 2-form, defined as:

    $$\omega(X, Y) \equiv g(JX, Y)$$

    This is precisely the (normalized) Berry curvature $\Omega_{\mu\nu}$.

**Theorem 2.4.2 (Geometric Unification Theorem)**

On $\mathbb{C}P^{N-1}$, Riemannian geometry (metric) and symplectic geometry (curvature) mutually determine each other through complex structure. That is:

$$\chi_{\mu\nu} = g_{\mu\nu} - i \omega_{\mu\nu}$$

This means that as long as we know the "distance" (statistical distinguishability) between states, we automatically determine the "curvature" (symplectic structure) of space, and vice versa. The **Metric Rigidity** and **Symplectic Rigidity** of physical reality are two sides of the same coin.

### 2.4.2 Geometricization of Schrödinger Equation: As Classical Hamiltonian System

It is usually thought that Schrödinger equation $i\hbar \frac{d}{dt}|\psi\rangle = \hat{H}|\psi\rangle$ describes linear wave mechanics. However, from the perspective of projective geometry, it exhibits a surprising **nonlinear classical mechanics** appearance.

Consider $\mathbb{C}P^{N-1}$ as the "true" phase space of physical system (note: this is not position-momentum phase space, but phase space constituted by quantum states). Any Hermitian operator $\hat{H}$ defines a real-valued function on this space:

$$h(\psi) = \langle \psi | \hat{H} | \psi \rangle$$

This function $h: \mathbb{C}P^{N-1} \to \mathbb{R}$ is precisely the system's **quantum Hamiltonian function** (i.e., energy expectation value).

**Theorem 2.4.3 (Hamiltonian Nature of Schrödinger Flow)**

Unitary evolution of quantum states is equivalent to classical Hamilton equations with $h(\psi)$ as Hamiltonian and $\omega$ as symplectic form:

$$\frac{d\xi^\mu}{dt} = \{ \xi^\mu, h \}_{\text{PB}}$$

where $\xi^\mu$ are real coordinates of the manifold, $\{ \cdot, \cdot \}_{\text{PB}}$ is Poisson bracket defined by symplectic form $\omega$. The corresponding flow field vector $X_h$ satisfies:

$$\omega(X_h, \cdot) = dh$$

**Proof Outline**:

In complex coordinates $Z^k$, the Kähler potential of Fubini-Study metric is $K = \ln(1 + \bar{Z} \cdot Z)$. Symplectic form is $\omega = i \partial \bar{\partial} K$.

Schrödinger equation $i\hbar \dot{Z}^k = \frac{\partial h}{\partial \bar{Z}^k}$ exactly corresponds to Hamiltonian vector field equation $\iota_{X_h} \omega = dh$ on symplectic manifold (taking $\hbar=1$ and appropriate normalization).

This means that quantum evolution trajectories are **Hamiltonian flows** on phase space $\mathbb{C}P^{N-1}$, preserving energy $h(\psi)$ constant (energy conservation). $\square$

**Physical Interpretation**:

This conclusion profoundly reveals the essence of quantum mechanics: **quantum mechanics is not a negation of classical mechanics, but a concrete realization of classical Hamiltonian mechanics on complex projective manifolds**. The only difference is the geometric structure of phase space: classical mechanics occurs on flat $\mathbb{R}^{2n}$, while quantum mechanics occurs on compact curved $\mathbb{C}P^{N-1}$.

### 2.4.3 Geometric Essence of Unitary Evolution: Symplectomorphism and Information Conservation

In standard form, time evolution operator $U(t) = e^{-i\hat{H}t/\hbar}$ is unitary, i.e., $U^\dagger U = \mathbf{1}$. What does this correspond to in geometric language?

**Corollary 2.4.4 (Unitarity as Symplectomorphism)**

The one-parameter transformation group $\phi_t: \mathbb{C}P^{N-1} \to \mathbb{C}P^{N-1}$ generated by Schrödinger flow is a **Symplectomorphism**, i.e., it preserves symplectic form:

$$\phi_t^* \omega = \omega$$

At the same time, due to compatibility of Kähler structure, it is also an **Isometry**, preserving Riemannian metric $g$ unchanged.

**Quantum Version of Liouville's Theorem**:

Since the flow is symplectic, according to Darboux's Theorem, it necessarily preserves symplectic volume form $dV = \frac{1}{(N-1)!} \omega^{\wedge (N-1)}$ on the manifold.

This is **Liouville's Theorem** in quantum mechanics:

> **"Probability volume" in physical state space is incompressible during evolution.**

This geometrically explains **unitary conservation** of quantum information: information can neither be created nor destroyed; it can only flow in state space. If evolution causes volume contraction (such as non-unitary measurement), it means information flows to the outside (environment); if evolution preserves volume, then the system is closed and information-conserving.

### 2.4.4 Summary: From Information Statistics to Physical Geometry

At this point, we have completed the construction of Part I of Volume I on "Geometric and Information Foundations of Physics." Starting from the most fundamental finite information axiom, we step by step rebuilt the geometric edifice of physics:

1. **Ontology**: Physical reality is described by finite-dimensional Hilbert spaces (Chapter 1).

2. **Metric Structure**: Distinguishability of states (statistical distance) uniquely determines Riemannian metric $g_{\mu\nu}$ of space (Sections 2.1, 2.2).

3. **Gauge Structure**: Phase structure of states (geometric phase) uniquely determines symplectic form $\Omega_{\mu\nu}$ and gauge fields of space (Section 2.3).

4. **Dynamical Structure**: Schrödinger equation is merely Hamiltonian flow preserving information conservation (symplectic volume unchanged) on this geometric structure (Section 2.4).

The core conclusion of this chapter can be summarized as: **Geometry is not an a priori stage, but statistical properties of information; dynamics is not arbitrary rules, but geometric necessity of information conservation.**

In the next Part II, we will leave static geometric structures and enter the core of discrete dynamics: if both continuous time and space are emergent, how exactly does the most fundamental "evolution" occur? We will introduce **Quantum Cellular Automata (QCA)** as the dynamical engine of discrete ontology.

