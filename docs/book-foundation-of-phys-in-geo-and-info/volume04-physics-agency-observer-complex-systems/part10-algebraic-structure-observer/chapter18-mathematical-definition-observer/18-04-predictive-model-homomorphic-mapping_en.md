**18.4 Predictive Model: Homomorphic Mapping and Compression of External Environment in Internal Algebra**

In Section 18.3, we established the observer's **memory subsystem**, explaining how it acts as a "anchor" of time to resist thermodynamic decoherence. However, if memory merely passively records the past, it is far from sufficient for an agent surviving in a hostile environment (QCA complex networks). To maintain its own low-entropy steady state (Homeostasis), the observer must be able to **predict** future evolution of the environment to make adaptive responses.

This section will define the observer's **Predictive Model** from an algebraic perspective. We will prove that, based on the finite information axiom, observers cannot have perfect copies of the environment (isomorphism), but can only construct a **homomorphic** and **lossy compressed** model. This mathematical fact constitutes the physical root of the eternal difference between "subjective world" and "objective reality," and directly derives the quantum version of **Law of Requisite Variety** in cybernetics.

### 18.4.1 Internal Model Representation Theorem: Internalizing External World

Let external environment state space be $\mathcal{S}(\mathcal{A}_{\text{ext}})$, observer's internal state space be $\mathcal{S}(\mathcal{A}_{\text{int}})$. According to Axiom A2, $\dim(\mathcal{A}_{\text{int}}) \ll \dim(\mathcal{A}_{\text{ext}})$. Therefore, the observer cannot store the complete quantum state $\rho_{\text{ext}}$ of the environment.

**Definition 18.4.1 (Algebraic Representation Map)**

Observer's "cognition" of the external world is defined as a completely positive trace-preserving map (CPTP Map) $\Pi: \mathcal{S}(\mathcal{A}_{\text{ext}}) \to \mathcal{S}(\mathcal{A}_{\text{int}})$.

This map must satisfy approximate **homomorphism** conditions: the logical structure of the internal model should preserve topological features of external causal laws.

$$
\Pi(U_{\text{ext}} \rho_{\text{ext}} U_{\text{ext}}^\dagger) \approx U_{\text{model}} \Pi(\rho_{\text{ext}}) U_{\text{model}}^\dagger
$$

where $U_{\text{ext}}$ is physical evolution of the environment, $U_{\text{model}} = e^{-i H_{\text{model}} t}$ is simulated evolution run by the observer in internal algebra.

**Physical Interpretation**:

$H_{\text{model}}$ is a **physical law simulator** in the observer's brain (or chip). If the equality holds strictly, the observer is said to have a **perfect model** of the environment. But due to dimension truncation, this is an impossible task.

The non-injectivity of $\Pi$ means: **through the observer's eyes, countless different external microscopic states $\rho_{\text{ext}}^{(i)}$ are mapped (compressed) to the same internal macroscopic state $\rho_{\text{int}}$**. This defines the observer's **coarse-graining** horizon.

### 18.4.2 Compression and Semantics: Information Bottleneck

Why do observers compress information? Not only because storage space is limited, but also to extract **meaning**. In physics, "meaning" is defined as order parameters with predictive power for future evolution.

**Theorem 18.4.2 (Optimal Predictive Compression)**

Let $E$ be environmental historical input, $F$ be environmental future state. Observer's internal state $M \in \mathcal{A}_{\text{int}}$ should be a compressed representation of $E$, aiming to maximize mutual information $I(M;F)$ about $F$ while minimizing representation complexity $I(M;E)$.

This corresponds to the **Information Bottleneck** variational problem:

$$
\min_{\Pi} \left( I(M;E) - \beta I(M;F) \right)
$$

**Corollary**:

Observer's internal model automatically discards microscopic details irrelevant to predicting the future (such as Brownian motion of air molecules), retaining only macroscopic causal structures (such as trajectory of an incoming stone).

Therefore, **"subjective reality" is not degradation of objective reality, but refinement of objective reality**. What we perceive as "objects," "colors," "forces" are essentially eigenvalues of high-order causal correlations in QCA networks.

### 18.4.3 Quantum Version of Good Regulator Theorem

In classical cybernetics, Roger Conant and W. Ross Ashby proposed the famous **Good Regulator Theorem**: "Every good regulator is a model of its system."

In the QCA framework, this manifests as matching of entanglement structures.

**Theorem 18.4.3 (Quantum Law of Requisite Variety)**

For observer $\mathfrak{O}$ to effectively counteract the impact of environmental disturbance $D$ on its survival goal $G$ (i.e., maintain $H(\text{Goal}) \approx 0$), the **Control Capacity** of observer's internal algebra must be greater than or equal to the **Shannon entropy** of environmental disturbance:

$$
H(\mathcal{A}_{\text{int}}^{\text{actuator}}) \ge H(D) - H(G)
$$

Furthermore, to achieve optimal control, observer's internal Hamiltonian $H_{\text{model}}$ must be **conjugate** to environmental Hamiltonian $H_{\text{ext}}$ on the interaction subspace:

$$
H_{\text{model}} \sim - H_{\text{ext}}^{\text{eff}}
$$

This means **the observer must be "isomorphic" in physical structure to the part of the environment it attempts to control**. By running a dynamics opposite to the external one (prediction) internally, the observer can achieve destructive interference at the boundary, thereby maintaining its steady state.

### 18.4.4 Algebraic Foundation of Symbols and Reference

Finally, we explore how symbols in the model acquire physical reference.

In $\mathcal{A}_{\text{int}}$, some operator $S$ (e.g., neuron pattern representing "apple") is itself just a bunch of matrix elements. How does it refer to external apple $O_{\text{apple}}$?

**Definition 18.4.4 (Entanglement Reference)**

Internal symbol $S$ refers to external object $O$ if and only if in the joint evolution history of observer and environment, a steady-state entanglement correlation (strong correlation) of the following form is established:

$$
\rho_{\text{joint}} \approx \sum_k p_k |s_k\rangle\langle s_k| \otimes |o_k\rangle\langle o_k|
$$

where $|s_k\rangle$ are eigenstates of $S$, $|o_k\rangle$ are eigenstates of $O$.

This correlation is not accidental, but jointly reinforced by $\Phi_{\text{update}}$ (perception map) and $H_{\text{model}}$ (predictive dynamics). If $S$'s predictions persistently fail (i.e., $S$ activates but $O$ does not appear), backpropagation mechanisms (free energy minimization) will modify the structure of $\mathcal{A}_{\text{int}}$, breaking this reference.

**Conclusion**

This section proved that observers are not just passive recorders, but active **modelers**.

1. **Homomorphism**: Internal model is a homomorphic mapping of the external world, losing microscopic details, preserving causal structure.

2. **Compressibility**: Limited by finite dimensions, models are necessarily highly compressed.

3. **Isomorphism**: For survival, observer's dynamical structure must internalize environmental laws (Ashby's law).

This algebraic structure paves the way for Chapter 19 to explore **self-referential dynamics** and **free energy principle**. We will see that all observer behaviors—perception, action, even consciousness—are to optimize this internal model, minimizing prediction error (entropy) between it and external reality.

