# 7.2 Combinatorial Proof of Born Rule: Based on Zurek Rotation and Microstate Counting

In the previous section, we eliminated physical reality of wave function collapse through "branching" concept, interpreting measurement as update of observer's horizon. However, this only solves the qualitative part of measurement problem (why there are definite results), leaving a quantitative puzzle: **Why does probability observer finds themselves in a particular branch strictly follow Born's rule $P_k = |\psi_k|^2$?**

In standard quantum mechanics, this is an independent axiom. But in our "Ultimate Axiom $\Omega$" system, besides unitarity and locality, there are no presuppositions about probability. If Born's rule cannot be derived from unitarity, our theory is incomplete.

This section will provide a proof purely based on **combinatorics** and **symmetry**. We will show: In discrete QCA networks, so-called "probability" is essentially counting of **micro-degeneracy** in holographic networks.

## 7.2.1 Discrete Ontology of Amplitudes: Weights as Path Counting

In continuous quantum mechanics, complex amplitude $\alpha \in \mathbb{C}$ is an abstract mathematical quantity. But in discrete path integral (sum-over-histories) perspective, amplitudes have clear counting meaning.

Consider evolution from initial state $|i\rangle$ to final state $|f\rangle$. QCA's unitary operator $\hat{U}$ can be viewed as sum of path weights on graph. If underlying lattice structure has some discrete symmetry (e.g., all basic paths have equal weight modulus), then macroscopic amplitude magnitude $|\alpha|$ actually reflects **number of microscopic paths to that state** (or degeneracy of microstates).

**Axiom 7.2 (Microscopic Equal Weight Axiom)**:

At QCA's deepest level (Planck scale), all orthogonal micro-basis states are ontologically equal. There is no "this basis is more real than that basis."

This means, if two macroscopic states $|A\rangle$ and $|B\rangle$ correspond to $N_A$ and $N_B$ indistinguishable microstates respectively at the bottom level, then according to Laplace's **Principle of Insufficient Reason**, probability observer finds themselves in $|A\rangle$ should be $N_A / (N_A + N_B)$.

Our task is to connect wave function amplitude $\alpha$ with microscopic number $N$.

## 7.2.2 Schmidt Decomposition and Environment-Assisted Invariance (Envariance)

We will adopt **Environment-Assisted Invariance (Envariance)** idea proposed by Wojciech Zurek and adapt it to discrete framework.

Consider entangled state of system $\mathcal{S}$ and environment $\mathcal{E}$. According to Schmidt Decomposition, any pure state can always be written as:

$$|\Psi_{\mathcal{S}\mathcal{E}}\rangle = \sum_k c_k |s_k\rangle_{\mathcal{S}} |e_k\rangle_{\mathcal{E}}$$

where $|s_k\rangle$ are system's pointer states (such as cat dead/alive), $|e_k\rangle$ are environment's orthogonal states (such as photons recording dead/alive).

**Case One: Equal Weight Superposition**

First consider simplest case, all coefficients equal: $c_k = 1/\sqrt{N}$.

$$|\Psi\rangle \propto |s_1\rangle|e_1\rangle + |s_2\rangle|e_2\rangle + \dots + |s_N\rangle|e_N\rangle$$

We ask: What is probability $P(1)$ observer measures state $|s_1\rangle$?

**Symmetry Argument**:

1. **Unitary Swap**: We can perform unitary transformation $\hat{U}_{\mathcal{S}}$ on system $\mathcal{S}$, swapping $|s_1\rangle$ and $|s_2\rangle$. This changes physical state:

   $$|s_2\rangle|e_1\rangle + |s_1\rangle|e_2\rangle + \dots$$

   Now, $|e_1\rangle$ is associated with $|s_2\rangle$.

2. **Environment Compensation**: But we can also perform inverse transformation $\hat{U}_{\mathcal{E}}$ on environment $\mathcal{E}$, swapping $|e_1\rangle$ and $|e_2\rangle$.

   After joint operation $\hat{U}_{\mathcal{E}} \hat{U}_{\mathcal{S}}$, state becomes:

   $$|s_2\rangle|e_2\rangle + |s_1\rangle|e_1\rangle + \dots$$

   This is **mathematically identical** to initial state $|\Psi\rangle$ (only summation order changed).

3. **Corollary**: Since swapping system (changing target of physical prediction) can be completely canceled by operating on environment (not changing system physical prediction), this means **physical probability should not depend on labels $1$ or $2$**.

   Therefore, must have $P(1) = P(2) = \dots = P(N) = 1/N$.

This proves: **For entangled states with equal coefficient moduli, probabilities are equal.**

## 7.2.3 Fine-Graining: From Amplitudes to Counting

Now handle general case, coefficients unequal. For example:

$$|\Psi\rangle = \sqrt{\frac{2}{3}} |0\rangle_S |e_0\rangle_E + \sqrt{\frac{1}{3}} |1\rangle_S |e_1\rangle_E$$

How do we prove $P(0) = 2/3$?

In QCA discrete ontology, complex coefficient $\sqrt{2/3}$ is not fundamental. It is a result of **coarse-graining**. It means environment state $|e_0\rangle_E$ is actually not a single microstate, but superposition of two indistinguishable microstates.

We perform **fine-graining decomposition** on environment Hilbert space:

* $|e_0\rangle \to \frac{1}{\sqrt{2}} (|e_{0,a}\rangle + |e_{0,b}\rangle)$

* $|e_1\rangle \to |e_{1,a}\rangle$

Substituting into original expression, we get a more fundamental microstate:

$$|\Psi\rangle \propto |0\rangle_S |e_{0,a}\rangle + |0\rangle_S |e_{0,b}\rangle + |1\rangle_S |e_{1,a}\rangle$$

(ignoring normalization constant).

Now, we face 3-term equal-weight superposition.

According to previous equal probability theorem, these 3 microscopic branches each have probability $1/3$.

* Observer seeing $|0\rangle$ event corresponds to first two branches: $P(0) = 1/3 + 1/3 = 2/3$.

* Observer seeing $|1\rangle$ event corresponds to third branch: $P(1) = 1/3$.

This is exactly $|\alpha|^2$ and $|\beta|^2$!

## 7.2.4 Why Square? — Statistics of Pythagorean Theorem

Why does physical amplitude $\alpha$ correspond to $\sqrt{N}$ rather than $N$? This directly stems from QCA's **global unitarity**.

In QCA, evolution operator $\hat{U}$ preserves vector's $L_2$ norm (modulus), corresponding to geometric Pythagorean theorem.

$$||\Psi||^2 = \sum |\alpha_i|^2 = 1$$

If we assume $\alpha_i$ represents microscopic path number $N_i$, then superposition principle would become $L_1$ norm conservation (probabilities directly add), but this would destroy mathematical structure of interference phenomena.

To simultaneously satisfy:

1. **Linear Superposition Principle** (core feature of quantum mechanics);

2. **Probability Conservation** (logical consistency);

**Probability must be quadratic function of amplitude.**

In QCA's discrete geometry, **amplitude is "edge length," probability is "face area."**

* Microscopic state number $N$ corresponds to **volume (measure)** in Hilbert space.

* When we project a large vector onto basis, squared projection length represents volume share contained in that basis direction.

**Theorem 7.2 (Born Rule Derivation Theorem)**:

In a discrete QCA system satisfying unitary evolution and environment-assisted invariance, subjective probability $P_k$ any local observer measures result $k$ necessarily equals modulus squared of that branch amplitude $|c_k|^2$.

## 7.2.5 Conclusion

Born's rule is no longer a confusing axiom. It is **result of counting microstates when we perform incomplete observation in a deterministic, unitary universe.**

* **God does not throw dice**: Entire universe's evolution is 100% deterministic.

* **Dice are in our hearts**: Because we are finite observers, we can only see a slice of the vast holographic network. The "randomness" we perceive is actually our **ignorance** about which position we occupy in the network.

Probability is subjective horizon's measure of objective information.

