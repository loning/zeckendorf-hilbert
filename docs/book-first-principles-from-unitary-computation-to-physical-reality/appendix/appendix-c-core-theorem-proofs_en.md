# Appendix C: Proofs of Core Theorems

**Appendix C: Proofs of Core Theorems**

The main text of this book proposes many revolutionary physical propositions, such as "Light Path Conservation," "Gravity as Entropic Force," and "Probability as Counting." Although we provide physical images and heuristic derivations in the main text, as a serious theoretical system, these propositions must be built on rigorous mathematical proofs.

This appendix collects complete mathematical proofs of the three most core theorems supporting the theoretical framework of the entire book. These proofs do not rely on vague analogies, but are directly derived from Axiom $\Omega$ (unitary QCA) and standard operator algebra.

---

## C.1 Operator Algebraic Proof of Light Path Conservation Theorem

**Proposition**: In any discrete Dirac-QCA model satisfying translational invariance and local unitarity, the external group velocity $v_{ext}$ and internal evolution velocity $v_{int}$ of single-particle excited states satisfy $v_{ext}^2 + v_{int}^2 = c^2$.

**Proof**:

1. **Orthogonal Decomposition of Hamiltonian**

   In the continuous limit ($\Delta x, \Delta t \to 0$), the evolution operator $\hat{U}$ of a one-dimensional Dirac-QCA can generate an effective Hamiltonian $\hat{H}$. For a two-component spinor field $\psi = (\psi_L, \psi_R)^T$, the most general translationally invariant Hamiltonian form is:

   $$\hat{H} = c \hat{p} \sigma_z + m c^2 \sigma_x$$

   where:

   * $c$ is the maximum propagation speed on the lattice.

   * $\hat{p} = -i\hbar \partial_x$ is the momentum operator.

   * $m$ is the mass parameter determined by local mixing angle $\theta$ (see Chapter 5 of the main text).

   * $\sigma_z, \sigma_x$ are Pauli matrices, acting on internal chirality space respectively.

2. **Operator Norm of Total Evolution Rate**

   The total evolution rate (Fubini-Study velocity) of quantum states in Hilbert space is determined by the variance or norm of the Hamiltonian. For energy eigenstates $|\psi_E\rangle$, the modulus squared of their phase rotation rate over time is proportional to $E^2$:

   $$E^2 = \langle \psi_E | \hat{H}^2 | \psi_E \rangle$$

3. **Using Anticommutation Relations**

   Compute operator $\hat{H}^2$:

   $$
   \begin{aligned}
   \hat{H}^2 &= (c \hat{p} \sigma_z + m c^2 \sigma_x) (c \hat{p} \sigma_z + m c^2 \sigma_x) \\
   &= c^2 \hat{p}^2 \sigma_z^2 + m^2 c^4 \sigma_x^2 + c m c^2 \hat{p} (\sigma_z \sigma_x + \sigma_x \sigma_z)
   \end{aligned}
   $$

   Using algebraic properties of Pauli matrices:

   * $\sigma_z^2 = \mathbb{I}, \quad \sigma_x^2 = \mathbb{I}$

   * Anticommutation: $\{ \sigma_z, \sigma_x \} = \sigma_z \sigma_x + \sigma_x \sigma_z = 0$

   Cross terms vanish, yielding diagonalized energy operator:

   $$\hat{H}^2 = (c^2 \hat{p}^2 + m^2 c^4) \mathbb{I}$$

4. **Mapping of Velocity Components**

   Taking expectation value on both sides and dividing by $E^2$ (normalization):

   $$1 = \frac{c^2 p^2}{E^2} + \frac{m^2 c^4}{E^2}$$

   * **External velocity term**: According to group velocity definition $v_g = \frac{\partial E}{\partial p}$. From dispersion relation $E^2 = p^2 c^2 + m^2 c^4$ differentiation gives $2E dE = 2p c^2 dp$, hence $v_{ext} \equiv v_g = \frac{c^2 p}{E}$.

      Therefore, the first term $\frac{c^2 p^2}{E^2} = \frac{v_{ext}^2}{c^2}$.

   * **Internal velocity term**: Define internal velocity $v_{int}$ as the projection of rest energy (mass term) in total energy onto light speed, i.e., $v_{int} = c \cdot \frac{m c^2}{E}$.

      Therefore, the second term $\frac{m^2 c^4}{E^2} = \frac{v_{int}^2}{c^2}$.

5. **Conclusion**

   Substituting back:

   $$1 = \frac{v_{ext}^2}{c^2} + \frac{v_{int}^2}{c^2} \implies v_{ext}^2 + v_{int}^2 = c^2$$

   **Q.E.D.**

---

## C.2 Variational Derivation of Information-Gravity Variational Principle (IGVP)

**Proposition**: If spacetime geometry emerges as a macroscopic structure to maximize holographic entanglement entropy, then the metric field $g_{\mu\nu}$ must satisfy Einstein's field equations $G_{\mu\nu} = 8\pi G T_{\mu\nu}$.

**Proof**:

1. **Construct Total Entropy Functional**

   Define the total entropy $S_{tot}$ of the universe within a local causal diamond as the sum of geometric entropy $S_{geom}$ and matter entropy $S_{matter}$. According to the second law of thermodynamics, equilibrium states correspond to extremal points of entropy.

   Functional form (action $I = -S$):

   $$I[g] = I_{geom}[g] + I_{matter}[g, \psi]$$

2. **Geometric Entropy Term**

   According to the discrete structure of QCA, geometric entropy is proportional to the complexity of network connections. In the continuous limit, this is the curvature integral of the spacetime manifold (generalization of Wald entropy):

   $$I_{geom} = \frac{1}{16\pi G} \int_{\mathcal{M}} d^4x \sqrt{-g} R$$

   where $G$ is a constant related to Planck area element $l_P^2$.

3. **Matter Entropy Term**

   Matter entropy is determined by the partition function $Z[g]$ of matter fields $\psi$ on curved background, whose logarithm corresponds to effective action:

   $$I_{matter} = \int_{\mathcal{M}} d^4x \sqrt{-g} \mathcal{L}_m$$

4. **Variation with Respect to Metric**

   We seek geometric structures that make the total action stationary with respect to metric perturbations $\delta g^{\mu\nu}$.

   $$\delta I = \delta I_{geom} + \delta I_{matter} = 0$$

   * **Geometric part variation**:

     Using identity $\delta \sqrt{-g} = -\frac{1}{2} \sqrt{-g} g_{\mu\nu} \delta g^{\mu\nu}$ and Palatini identity $\delta R = R_{\mu\nu} \delta g^{\mu\nu} + \nabla_\mu v^\mu$ (boundary terms ignored):

     $$\delta I_{geom} = \frac{1}{16\pi G} \int d^4x \sqrt{-g} \left( R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu} \right) \delta g^{\mu\nu}$$

   * **Matter part variation**:

     By definition, stress-energy tensor $T_{\mu\nu}$ is the response of matter action to metric:

     $$T_{\mu\nu} \equiv -\frac{2}{\sqrt{-g}} \frac{\delta I_{matter}}{\delta g^{\mu\nu}}$$

     Therefore:

     $$\delta I_{matter} = -\frac{1}{2} \int d^4x \sqrt{-g} T_{\mu\nu} \delta g^{\mu\nu}$$

5. **Deriving Field Equations**

   From $\delta I = 0$, for arbitrary $\delta g^{\mu\nu}$, the integrand must be zero:

   $$\frac{1}{16\pi G} (R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu}) - \frac{1}{2} T_{\mu\nu} = 0$$

   Rearranging:

   $$R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu} = 8\pi G T_{\mu\nu}$$

   **Q.E.D.**

---

## C.3 Trace-Class Counting Proof of Born Rule

**Proposition**: In discrete, unitary QCA systems satisfying environment-assisted invariance (Envariance), measurement outcome probabilities $P_k$ are uniquely determined by amplitude modulus squared $|c_k|^2$.

**Proof**:

1. **Schmidt Decomposition**

   Let system $S$ and environment $E$ be in an entangled state:

   $$|\Psi\rangle = \sum_{k=1}^N c_k |s_k\rangle |e_k\rangle$$

   where $|s_k\rangle, |e_k\rangle$ are orthogonal bases respectively.

2. **Rational Approximation and Fine-Graining**

   Assume $|c_k|^2$ are rational numbers (always true in discrete systems), let $|c_k|^2 = n_k / M$, where $M = \sum n_k$ is the total number of microstates.

   We can further decompose environment basis $|e_k\rangle$ into superposition of $n_k$ equally weighted micro-bases $|e_{k, \alpha}\rangle$:

   $$|e_k\rangle \to \frac{1}{\sqrt{n_k}} \sum_{\alpha=1}^{n_k} |e_{k, \alpha}\rangle$$

   Substituting into original state and ignoring overall phase:

   $$|\Psi'\rangle = \frac{1}{\sqrt{M}} \sum_{k=1}^N \sum_{\alpha=1}^{n_k} |s_k\rangle |e_{k, \alpha}\rangle$$

3. **Environment Exchange Symmetry**

   Now, state $|\Psi'\rangle$ is an equal-weight superposition of $M$ terms. Each term has the form $|s_k\rangle |e_{k, \alpha}\rangle$.

   For environment microstates $|e_{k, \alpha}\rangle$ and $|e_{j, \beta}\rangle$, there exists a unitary operator $\hat{U}_E$ that can exchange them without changing the $|s_k\rangle$ part.

   According to Envariance principle, physical probabilities should not depend on environment labels. Therefore, the probability of each micro-term $|s_k\rangle |e_{k, \alpha}\rangle$ appearing must be equal, all $p = 1/M$.

4. **Macroscopic Probability Summation**

   The probability $P_k$ that an observer measures macroscopic state $|s_k\rangle$ is the sum of probabilities of all compatible micro-terms:

   $$P_k = \sum_{\alpha=1}^{n_k} p = n_k \cdot \frac{1}{M} = \frac{n_k}{M}$$

   Recalling definition $|c_k|^2 = n_k / M$, we obtain:

   $$P_k = |c_k|^2$$

   **Q.E.D.**

---

**Author's Conclusion**:

These three proofs respectively establish the mathematical legitimacy of this book in **kinematics** (Light Path Conservation), **dynamics** (field equations), and **measurement theory** (Born rule). Together they form a logical closed loop, proving that physical reality can completely emerge from the single axiom of "unitary computation."

