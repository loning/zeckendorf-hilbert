# 6.1 Independence of Local Reference Frames: Why Does Each Cell Need "Translation"?

In the previous chapter, we solved the question "what is matter": matter is topological knots in QCA networks, and mass is the internal refresh rate required to maintain self-referential loops. Now, we must face a more complex question: **How do matter particles interact?**

In classical physics, interactions propagate through "fields" (such as electromagnetic fields, gravitational fields). In quantum field theory, interactions are realized through exchanging "gauge bosons." But in our discrete ontology, there are neither continuous fields nor presupposed bosons. All we have are independent cells running on lattices.

This chapter will reveal a startling fact: **Interactions are not special forces, but communication costs that different cells must pay to achieve "information consensus."**

Gauge fields are essentially **link variables** in discrete networks, geometric objects used to "translate" differences between local reference frames of different cells. Starting from the most fundamental "local independence" axiom, we will step by step derive Maxwell's equations and Yang-Mills theory.

## 6.1.1 Axiom 6.1 (Reference Frame Locality)

Imagine an internet composed of billions of independent computers. Each computer has its own clock (local time) and file system (local basis). If computer A wants to send a file to computer B, they must first establish a **communication protocol** to ensure that "0" and "1" sent by A are correctly interpreted at B.

In QCA universe, the situation is very similar.

**Axiom 6.1 (Reference Frame Locality)**:

Every cell $x$ in QCA network is an independent Hilbert space $\mathcal{H}_x$. Although all $\mathcal{H}_x$ are mathematically isomorphic (e.g., all $\mathbb{C}^2$), physically, **there is no God's-eye-view global basis**.

That is, each cell $x$ has the right to arbitrarily choose its own basis vectors $|0\rangle_x, |1\rangle_x$.

This freedom of choice constitutes **local gauge symmetry**.

* **$U(1)$ Symmetry**: Cell $x$ can arbitrarily change its wave function phase: $|\psi\rangle_x \to e^{i\alpha(x)} |\psi\rangle_x$.

* **$SU(N)$ Symmetry**: If cell has $N$ internal degrees of freedom (such as quark color), cell $x$ can arbitrarily rotate its internal coordinate axes: $|\psi\rangle_x \to \hat{U}(x) |\psi\rangle_x$.

## 6.1.2 Challenge of Communication

If cell $x$ and adjacent cell $y$ define different "phase zero" or "red direction," what happens to electron's wave function when it moves from $x$ to $y$?

If moved directly without correction, electron's phase information becomes chaotic (like recording time with two inaccurate clocks), leading to information loss, violating unitarity.

## 6.1.3 Solution: Connection Field

To achieve lossless transmission without global basis, network must maintain a **comparator** or **translator** between every two adjacent nodes $x, y$.

We define an operator $\hat{U}_{y \leftarrow x}$, called **link variable**. Its role is to "translate" $x$'s basis into $y$'s basis.

Information transmission equation:

$$|\psi\rangle_y^{\text{received}} = \hat{U}_{y \leftarrow x} |\psi\rangle_x^{\text{sent}}$$

If we perform local basis transformation $\hat{V}_x$ at $x$ and $\hat{V}_y$ at $y$, to ensure physical result (transmitted state) unchanged, link variable must transform accordingly:

$$\hat{U}'_{y \leftarrow x} = \hat{V}_y \hat{U}_{y \leftarrow x} \hat{V}_x^\dagger$$

This is the famous **gauge transformation law**. But in standard textbooks, this is a rule concocted to keep Lagrangian invariant; in QCA, this is **logical necessity to ensure different nodes can "understand" each other**.

## 6.1.4 Physical Picture

**Physical Picture 6.1**:

* **Gauge fields are not matter**; they are **metadata** carried by network connections themselves.

* **Electromagnetic potential $A_\mu$** records **clock synchronization error** (phase difference) between adjacent cells.

* **Strong interaction potential $G_\mu^a$** records **relative distortion** of internal coordinate systems of adjacent cells.

This view completely subverts our understanding of "force": **Forces are not to push objects, but to correct reference frame differences.** When reference frame differences vary with time and space (i.e., curvature exists), to maintain information consistency, objects must change motion state—this is the "force" we feel.

In the next section, we will see how this connection field, existing solely for "translation," acquires its own dynamical life and evolves into photons and gluons.

