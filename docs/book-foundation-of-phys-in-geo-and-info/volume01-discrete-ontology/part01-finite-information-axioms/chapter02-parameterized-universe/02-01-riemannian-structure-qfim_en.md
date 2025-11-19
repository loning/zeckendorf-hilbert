### Chapter 2: Parameterized Universe and Information Geometry

**2.1 Riemannian Structure of State Space: Construction of Quantum Fisher Information Metric (QFIM)**

In Chapter 1, we established that the Hilbert space dimension of physical reality is finite, and quantum information is its ontological foundation. This raises a profound question: if the foundation of the world is discrete quantum states, where does the familiar "continuous spacetime geometry" come from?

This section will argue that geometry is not an a priori background stage, but an emergent derived quantity from the statistical structure of quantum state space. Through rigorous mathematical derivation, we will prove that quantum state space naturally possesses Riemannian manifold structure, and its distance metric—Quantum Fisher Information Metric (QFIM)—is the most fundamental "ruler" of the physical world.

#### 2.1.1 From Hilbert Space to Projective Manifold

In standard quantum mechanics, physical states are usually described by non-zero vectors $|\psi\rangle$ in Hilbert space $\mathcal{H}$. However, physical states have two important redundancies:

1. **Normalization Redundancy**: $|\psi\rangle$ and $c|\psi\rangle$ ($c \in \mathbb{R}^+$) describe the same physical state.

2. **Phase Redundancy**: $|\psi\rangle$ and $e^{i\phi}|\psi\rangle$ ($\phi \in \mathbb{R}$) describe the same physical state.

Therefore, the true physical state space is not the linear space $\mathcal{H} \cong \mathbb{C}^{N}$, but the quotient space after removing the above redundancies, namely Complex Projective Space:

$$\mathcal{P}(\mathcal{H}) \cong \mathbb{C}P^{N-1} = \mathbb{C}^{N} / \mathbb{C}^*$$

This is a compact, simply connected Kähler Manifold. On this manifold, we cannot simply use Euclidean distance $\|\psi_1 - \psi_2\|$ in linear space, but must define an intrinsic geometric metric.

**Definition 2.1.1 (Parameterized Quantum State)**

Let a physical system be described by a set of real parameters $\boldsymbol{\theta} = (\theta^1, \theta^2, \dots, \theta^M)$, which can be classical external fields, spacetime coordinates, or internal control quantities of the system. The system is in parameterized pure state $|\psi(\boldsymbol{\theta})\rangle \in \mathcal{H}$. We require the mapping $\boldsymbol{\theta} \mapsto |\psi(\boldsymbol{\theta})\rangle$ to be smooth and satisfy normalization condition $\langle \psi(\boldsymbol{\theta}) | \psi(\boldsymbol{\theta}) \rangle = 1$.

#### 2.1.2 Distance Defined by Distinguishability: Derivation of Fubini-Study Metric

In the "It from Bit" ontology, the "distance" between two physical states should measure their statistical **Distinguishability**. If two states completely coincide, distance is zero; if they are orthogonal (completely distinguishable), distance is maximum.

We introduce **Fidelity** as a measure of overlap:

$$F(\boldsymbol{\theta}, \boldsymbol{\theta} + d\boldsymbol{\theta}) = \big| \langle \psi(\boldsymbol{\theta}) | \psi(\boldsymbol{\theta} + d\boldsymbol{\theta}) \rangle \big|$$

Physical distance $ds^2$ is defined as deviation from perfect overlap:

$$ds^2 \equiv 1 - F^2(\boldsymbol{\theta}, \boldsymbol{\theta} + d\boldsymbol{\theta})$$

This distance physically corresponds to: when we move a small amount $d\boldsymbol{\theta}$ in parameter space, the measure of observable changes in quantum state.

**Theorem 2.1.2 (Construction of Quantum Geometric Tensor)**

Expanding parameterized quantum state $|\psi(\boldsymbol{\theta})\rangle$ to second order via Taylor expansion, we obtain line element form on parameter space:

$$ds^2 = \frac{1}{2} g_{\mu\nu} d\theta^\mu d\theta^\nu$$

where $g_{\mu\nu}$ is the **Quantum Fisher Information Metric** (also called Fubini-Study Metric), with explicit form:

$$g_{\mu\nu} = 4 \operatorname{Re} \left( \langle \partial_\mu \psi | \partial_\nu \psi \rangle - \langle \partial_\mu \psi | \psi \rangle \langle \psi | \partial_\nu \psi \rangle \right)$$

Here $\partial_\mu \equiv \partial / \partial \theta^\mu$.

*Proof*:

Consider small displacement $d\boldsymbol{\theta}$, state vector expands as:

$$|\psi(\boldsymbol{\theta} + d\boldsymbol{\theta})\rangle = |\psi\rangle + |\partial_\mu \psi\rangle d\theta^\mu + \frac{1}{2} |\partial_\mu \partial_\nu \psi\rangle d\theta^\mu d\theta^\nu + \mathcal{O}(d\theta^3)$$

Computing inner product $\langle \psi | \psi + d\psi \rangle$:

$$\langle \psi | \psi + d\psi \rangle = 1 + \langle \psi | \partial_\mu \psi \rangle d\theta^\mu + \frac{1}{2} \langle \psi | \partial_\mu \partial_\nu \psi \rangle d\theta^\mu d\theta^\nu$$

Using derivative properties of normalization condition $\langle \psi | \psi \rangle = 1$:

$$\partial_\mu \langle \psi | \psi \rangle = \langle \partial_\mu \psi | \psi \rangle + \langle \psi | \partial_\mu \psi \rangle = 0 \implies \operatorname{Re}(\langle \psi | \partial_\mu \psi \rangle) = 0$$

$$\partial_\mu \partial_\nu \langle \psi | \psi \rangle = \langle \partial_\mu \partial_\nu \psi | \psi \rangle + \langle \partial_\mu \psi | \partial_\nu \psi \rangle + \dots = 0$$

We obtain $\langle \psi | \partial_\mu \partial_\nu \psi \rangle + c.c. = - (\langle \partial_\mu \psi | \partial_\nu \psi \rangle + \langle \partial_\nu \psi | \partial_\mu \psi \rangle)$.

Expanding modulus square of inner product to second order:

$$
\begin{aligned}
|\langle \psi | \psi + d\psi \rangle|^2 &= \left( 1 + \langle \psi | d\psi \rangle + \frac{1}{2} \langle \psi | d^2\psi \rangle \right) \left( 1 + \langle d\psi | \psi \rangle + \frac{1}{2} \langle d^2\psi | \psi \rangle \right) \\
&\approx 1 + (\langle \psi | d\psi \rangle + c.c.) + \langle d\psi | d\psi \rangle + \frac{1}{2}(\langle \psi | d^2\psi \rangle + c.c.) + |\langle \psi | d\psi \rangle|^2
\end{aligned}
$$

Substituting derivative relations and simplifying, we finally obtain the second-order term of distance $ds^2 = 1 - |\langle \psi | \psi + d\psi \rangle|^2$ as:

$$ds^2 = \left( \langle \partial_\mu \psi | \partial_\nu \psi \rangle - \langle \partial_\mu \psi | \psi \rangle \langle \psi | \partial_\nu \psi \rangle \right) d\theta^\mu d\theta^\nu$$

The tensor in parentheses is usually denoted $\chi_{\mu\nu}$, called **Quantum Geometric Tensor (QGT)**. It is defined as:

$$\chi_{\mu\nu} \equiv \langle \partial_\mu \psi | (1 - |\psi\rangle\langle\psi|) | \partial_\nu \psi \rangle$$

Since $ds^2$ must be real, physical distance is actually determined by the symmetric real part of $\chi_{\mu\nu}$. In standard definition of information geometry, factor 4 is usually taken to match classical Fisher information, yielding $g_{\mu\nu} = 4 \operatorname{Re}(\chi_{\mu\nu})$. $\square$

#### 2.1.3 Unification of Riemannian Metric and Symplectic Structure: Quantum Geometric Tensor

Theorem 2.1.2 reveals a profound structure: quantum geometric tensor $\chi_{\mu\nu}$ is not purely real; it naturally decomposes into real and imaginary parts:

$$\chi_{\mu\nu} = \frac{1}{4} g_{\mu\nu} - \frac{i}{2} \Omega_{\mu\nu}$$

where:

* **Real part $g_{\mu\nu}$**: Symmetric Riemannian metric tensor (QFIM), measuring "distance" in parameter space. It describes the **orthogonality rate** of quantum states under parameter changes.

* **Imaginary part $\Omega_{\mu\nu}$**: Antisymmetric symplectic form (Symplectic Form), namely the famous **Berry Curvature**:

    $$\Omega_{\mu\nu} = i \left( \langle \partial_\mu \psi | \partial_\nu \psi \rangle - \langle \partial_\nu \psi | \partial_\mu \psi \rangle \right)$$

    It describes the **geometric phase** accumulated by quantum states during evolution along closed paths in parameter space.

**Corollary 2.1.3 (Unification of Geometry and Topology)**

In parameterized quantum universe, Riemannian geometry (gravity/distance) and symplectic geometry (gauge fields/phase) are two aspects of the same physical object—quantum geometric tensor. Distance measures information difference, while curvature measures information completeness (Holonomy).

#### 2.1.4 Physical Interpretation: Cramér-Rao Bound

Why do we call this metric "information metric"? Because it directly determines the ultimate precision of physical measurements.

Consider any unbiased estimator $\hat{\theta}$ for parameter $\theta$. According to Quantum Cramér-Rao Theorem, variance of the estimator is bounded by the inverse of QFIM:

$$\mathrm{Var}(\hat{\theta}) \ge \frac{1}{N_{meas} g_{\theta\theta}}$$

where $N_{meas}$ is the number of measurements.

This gives Riemannian geometry strict operational meaning:

* **Large $g_{\mu\nu}$**: Means small parameter changes cause drastic quantum state changes (orthogonalization), so physical parameters at this location are easily measured precisely (high resolution region).

* **Small $g_{\mu\nu}$**: Means quantum states are insensitive to parameter changes; physical reality is "blurred" in this region.

**Summary**

In this section, we completed the leap from discrete quantum states to continuous Riemannian geometry. We proved that as long as a physical system can be parameterized, its parameter space necessarily possesses Riemannian structure. This structure is not artificially set, but uniquely determined by the statistical properties of quantum state distinguishability (QFIM).

In subsequent chapters, we will see that if we interpret these "parameters" as spacetime coordinates, then Einstein's field equations in general relativity are actually the dynamical equations of this information geometry under the principle of maximum entanglement entropy.

