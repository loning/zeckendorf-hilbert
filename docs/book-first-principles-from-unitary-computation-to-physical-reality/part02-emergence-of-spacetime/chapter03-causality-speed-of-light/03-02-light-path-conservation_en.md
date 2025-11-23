# 3.2 Light Path Conservation Theorem: Proving $v_{ext}^2 + v_{int}^2 = c^2$ from Unitarity

In the previous section, we established light speed $c$ as the maximum bandwidth (causal boundary) for information propagation in the universe. However, special relativity is not just about light speed limits, but about **what happens when objects approach light speed**. Why does time dilate? Why does mass increase?

Traditional physics textbooks attribute these effects to the geometric properties of Lorentz transformations, i.e., spacetime metrics must maintain $ds^2 = -c^2 dt^2 + dx^2$ invariant. But this is only a description of phenomena, not an explanation. We must ask: **Why** must the metric be this way?

In this section, we will prove a more fundamental theorem—**Light Path Conservation Theorem (Theorem of Information Celerity Conservation)**. We will show that all strange effects of special relativity are merely inevitable mathematical consequences of **unitarity (information conservation)** allocating resources between space and internal states.

## 3.2.1 Geometric Definition of Information Rate

In QCA's Hilbert space $\mathcal{H}$, physical states $|\Psi(t)\rangle$ evolve with discrete time $t$. How do we define the "speed" of this state evolution?

In quantum mechanics, the natural distance measuring the difference between two states is the **Fubini-Study metric**. For unitary evolution driven by Hamiltonian $\hat{H}$, the evolution rate of state vectors in Hilbert space (i.e., the rate of orthogonalization with other states) is proportional to energy uncertainty or average energy.

For basic excitations (single particles) of QCA, the energy scale is set by Planck frequency $\omega_P$. Since evolution operator $\hat{U}$ is strictly unitary ($\hat{U}^\dagger \hat{U} = \mathbb{I}$), state vectors maintain constant modulus during evolution. This means **state vectors always rotate at constant "angular velocity" in Hilbert space.**

We define this constant total information update rate as $c$.

> **Definition (Total Information Rate)**:
>
> For any basic excitation in the universe, the modulus of its Fubini-Study evolution rate in the full Hilbert space (including position and internal degrees of freedom) is constant $c$.
>
> $$\| \mathbf{v}_{total} \| \equiv c$$

## 3.2.2 Orthogonal Decomposition and Pythagorean Theorem

Now, we project this total rate $\mathbf{v}_{total}$ onto two observable dimensions in the physical world.

According to Axiom $\Omega$, Hilbert space decomposes as $\mathcal{H}_{total} = \mathcal{H}_{position} \otimes \mathcal{H}_{internal}$. Correspondingly, evolution generators (effective Hamiltonian $\hat{H}_{eff}$) also consist of two parts:

1. **Translation Generator ($\hat{P}$)**: Responsible for changing particle position index $|x\rangle \to |x+1\rangle$ on lattice graph $\Lambda$. This corresponds to macroscopic **momentum**.

2. **Internal Rotation Generator ($\hat{M}$)**: Responsible for changing particle internal states (such as spin flips, phase rotations). This corresponds to macroscopic **rest mass**.

In a one-dimensional Dirac-QCA model (simplest fermion model), the effective Hamiltonian is written as:

$$\hat{H}_{eff} = c \hat{P} \otimes \hat{\sigma}_z + m_0 c^2 \hat{I} \otimes \hat{\sigma}_x$$

where $\hat{\sigma}_z, \hat{\sigma}_x$ are Pauli matrices, acting on internal chirality space respectively.

Here appears a decisive algebraic property: **Anti-commutation**.

$$\{ \hat{\sigma}_z, \hat{\sigma}_x \} = \hat{\sigma}_z \hat{\sigma}_x + \hat{\sigma}_x \hat{\sigma}_z = 0$$

Geometrically, anti-commutation of operators means the evolution directions they generate are **strictly orthogonal**. Just as $x$-axis and $y$-axis are perpendicular in Euclidean space, in Hilbert space, "changing position" and "changing internal state" are two non-interfering evolution dimensions.

Therefore, the square of total evolution rate (corresponding to energy squared $E^2 \propto \langle \hat{H}^2 \rangle$) can be simply obtained by calculating the sum of squares of operators:

$$
\begin{aligned}
\hat{H}^2 &= (c \hat{P} \sigma_z + m_0 c^2 \sigma_x)^2 \\
&= c^2 \hat{P}^2 \sigma_z^2 + m_0^2 c^4 \sigma_x^2 + c m_0 c^2 \hat{P} (\sigma_z \sigma_x + \sigma_x \sigma_z) \\
&= (c^2 P^2 + m_0^2 c^4) \mathbb{I} \quad (\text{because } \sigma_i^2 = \mathbb{I}, \{\sigma_z, \sigma_x\} = 0)
\end{aligned}
$$

We divide both sides by total energy squared $E^2$ (normalization) and introduce velocity definitions:

* **External velocity** $v_{ext} \equiv c^2 P / E$ (group velocity $dE/dP$)

* **Internal velocity** $v_{int} \equiv m_0 c^3 / E$ (contribution rate of internal oscillation to total energy)

We obtain:

$$1 = \frac{v_{ext}^2}{c^2} + \frac{v_{int}^2}{c^2}$$

Rearranging, we get one of the most important theorems of this book:

> **Theorem 3.2 (Light Path Conservation Theorem)**:
>
> In a unitary QCA universe, for any particle, external displacement velocity $v_{ext}$ and internal evolution velocity $v_{int}$ satisfy:
>
> $$v_{ext}^2 + v_{int}^2 = c^2$$

## 3.2.3 Physical Interpretation: Demystifying Special Relativity

This simple Pythagorean theorem completely removes the mystery of special relativity. It tells us that physical entity evolution is a **zero-sum game**.

1. **Resource Mutual Exclusivity**: Your total "computational power" is finite ($c$). If you use computational power to change position ($v_{ext}$ increases), you must reduce computational power for internal state updates ($v_{int}$ decreases).

2. **Essence of Time Dilation**: So-called "time dilation" is essentially **reduction of internal computation rate**. When you move at near light speed ($v_{ext} \to c$), your $v_{int}$ is forced to approach 0. Your internal clock (metabolism, atomic vibrations, thought processes) slows down due to lack of "computational quota."

   * This is not because time itself slows down, but because **you're busy traveling, with no time to age**.

3. **Definition of Mass**: In this framework, **rest mass $m_0$** is given clear geometric meaning—it is the internal oscillation frequency of particles at rest ($v_{ext}=0$). It is the "inherent cost" of particle existence.

4. **Essence of Photons**: Photons have no mass because they are pure external displacement modes. They have no projection in internal space ($v_{int} \equiv 0$), so they must use all quota for displacement, resulting in $v_{ext} \equiv c$.

## 3.2.4 Conclusion

**Relativity is not about spacetime axioms, but about statistics of information processing.**

Einstein's Lorentz factor $\gamma = 1/\sqrt{1-v^2/c^2}$ is merely another way of writing the Pythagorean theorem $\sin \theta = \sqrt{1-\cos^2 \theta}$. In this discrete, unitary universe, every particle is a pointer dancing on the information rate circle.

In the next section, we will use this theorem to directly derive the specific form of Lorentz transformations and show how four-dimensional spacetime geometry emerges from this two-dimensional velocity constraint.

