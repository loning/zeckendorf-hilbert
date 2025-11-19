**4.2 Derivation of Dirac Equation: Long-Wave Limit of Quantum Walk and Emergence of Spin**

In the previous section, we showed how Feynman path integral of scalar fields naturally emerges from discrete QCA propagators. However, the material world is not only composed of scalar particles; fermions (electrons, quarks, etc.) that form the foundation of matter follow Dirac Equation, with spin and antiparticle structures. In traditional continuous field theory, spinor structure is usually introduced through representation theory of Lorentz group.

This section will prove that in QCA discrete ontology, **spin is not an a priori introduced degree of freedom, but an inevitable product of topological motion of discrete quantum walk on spacetime grids**. We will construct the simplest discrete dynamical model and, through rigorous mathematical derivation, show how it converges to relativistic Dirac equation in a long-wavelength limit.

### 4.2.1 Discrete Fermion Model: Quantum Walk

Consider one-dimensional spatial lattice $\Lambda = \mathbb{Z}$. To describe a "walker" with non-trivial dynamics, the simplest local Hilbert space $\mathcal{H}_x$ cannot be scalar of dimension 1, but must be at least two-dimensional, i.e., $\mathcal{H}_x \cong \mathbb{C}^2$. We denote these two basis states as $| \uparrow \rangle$ and $| \downarrow \rangle$, which will correspond to two chiral components (Chirality) or spin components of fermions in continuous limit.

Total system state space is $\mathcal{H} = \ell^2(\mathbb{Z}) \otimes \mathbb{C}^2$. State $|\Psi_n\rangle$ at any moment $n$ can be written as:

$$
|\Psi_n\rangle = \sum_{x \in \mathbb{Z}} \left( \psi_n^\uparrow(x) |x, \uparrow\rangle + \psi_n^\downarrow(x) |x, \downarrow\rangle \right)
$$

Dynamical evolution is driven by unitary operator $W$: $|\Psi_{n+1}\rangle = W |\Psi_n\rangle$. In QCA framework, we choose standard **Split-step Quantum Walk** model, whose single-step update consists of "Coin Tossing" and "Conditional Shift".

**Definition 4.2.1 (Dirac-Type QCA Update Operator)**

Update operator $W$ is defined as product of two local operators: $W = S \circ C$.

1. **Local Coin Operator $C$**: Rotation operation acting independently at each lattice site, mixing up and down components.

    $$C = \bigoplus_{x \in \mathbb{Z}} R_x(\theta)$$

    where $R_x(\theta) = e^{-i\theta\sigma_y} = \begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}$. Parameter $\theta$ controls mixing degree, which will correspond to particle mass later.

2. **Conditional Shift Operator $S$**: Moves particle position according to internal state.

    $$S |x, \uparrow\rangle = |x+1, \uparrow\rangle, \quad S |x, \downarrow\rangle = |x-1, \downarrow\rangle$$

### 4.2.2 Discrete Evolution Equation

Applying the above operators to state vectors, we can write discrete evolution equations in component form.

For state at moment $n+1$, its amplitude at position $x$ comes from contributions of adjacent positions at moment $n$ after rotation:

$$
\begin{aligned}
\psi_{n+1}^\uparrow(x) &= \cos\theta \cdot \psi_n^\uparrow(x-1) - \sin\theta \cdot \psi_n^\downarrow(x-1) \\
\psi_{n+1}^\downarrow(x) &= \sin\theta \cdot \psi_n^\uparrow(x+1) + \cos\theta \cdot \psi_n^\downarrow(x+1)
\end{aligned}
$$

This set of difference equations completely describes dynamics at microscopic discrete level. Note that there is no differentiation here, no light speed $c$ or mass $m$, only pure information transfer and local mixing.

### 4.2.3 Continuous Limit and Renormalization

To "see" continuous physics from this discrete model, we need to examine **Long-wavelength Limit**. That is, we focus on solutions with wavelengths much larger than lattice spacing $\varepsilon$ and frequencies much smaller than time step frequency $1/\tau$.

Introduce scale parameters:

* Spatial step (lattice spacing): $\varepsilon$

* Time step: $\tau$

* Physical coordinates: $X = x\varepsilon, \quad T = n\tau$

* Effective light speed: $c = \varepsilon / \tau$ (set as constant, usually take $c=1$)

For mass term, we note that if $\theta=0$, equations describe massless particles propagating left and right at speed $c$. To introduce mass, rotation angle $\theta$ must tend to zero in continuous limit. We set scaling relation:

$$
\theta = m \tau = m \varepsilon / c
$$

where $m$ is physical mass parameter (in natural units).

### 4.2.4 Rigorous Derivation of Dirac Equation

Assume discrete amplitudes $\psi_n^{\uparrow/\downarrow}(x)$ are samples of continuously differentiable functions $\Psi^{\uparrow/\downarrow}(X, T)$ on lattice. We perform Taylor expansion of evolution equations at $(X, T)$.

**Step 1: Expand Left Side (Time Term)**

$$
\psi_{n+1}(x) \approx \Psi(X, T+\tau) \approx \Psi(X, T) + \tau \partial_T \Psi(X, T)
$$

**Step 2: Expand Right Side (Spatial and Rotation Terms)**

Using $\cos\theta \approx 1 - \theta^2/2 \approx 1$ and $\sin\theta \approx \theta = m\tau$, and $\Psi(X\pm\varepsilon) \approx \Psi(X) \pm \varepsilon \partial_X \Psi$.

For $\uparrow$ component equation:

$$
\begin{aligned}
\Psi^\uparrow + \tau \partial_T \Psi^\uparrow &\approx (1) \cdot (\Psi^\uparrow - \varepsilon \partial_X \Psi^\uparrow) - (m\tau) \cdot (\Psi^\downarrow - \varepsilon \partial_X \Psi^\downarrow) \\
&\approx \Psi^\uparrow - \varepsilon \partial_X \Psi^\uparrow - m\tau \Psi^\downarrow + O(\varepsilon^2, \tau^2, \varepsilon\tau)
\end{aligned}
$$

Canceling $\Psi^\uparrow$ on both sides and dividing by $\tau$, using $c = \varepsilon/\tau$:

$$
\partial_T \Psi^\uparrow = -c \partial_X \Psi^\uparrow - m \Psi^\downarrow
$$

For $\downarrow$ component equation:

$$
\begin{aligned}
\Psi^\downarrow + \tau \partial_T \Psi^\downarrow &\approx (m\tau) \cdot (\Psi^\uparrow + \varepsilon \partial_X \Psi^\uparrow) + (1) \cdot (\Psi^\downarrow + \varepsilon \partial_X \Psi^\downarrow) \\
&\approx m\tau \Psi^\uparrow + \Psi^\downarrow + \varepsilon \partial_X \Psi^\downarrow + O(\dots)
\end{aligned}
$$

Canceling $\Psi^\downarrow$ on both sides and dividing by $\tau$:

$$
\partial_T \Psi^\downarrow = c \partial_X \Psi^\downarrow + m \Psi^\uparrow
$$

**Step 3: Organize into Matrix Form**

Combining two components into spinor $\Psi(X, T) = \begin{pmatrix} \Psi^\uparrow \\ \Psi^\downarrow \end{pmatrix}$, the above system can be written as:

$$
\partial_T \begin{pmatrix} \Psi^\uparrow \\ \Psi^\downarrow \end{pmatrix} = \begin{pmatrix} -c\partial_X & -m \\ m & c\partial_X \end{pmatrix} \begin{pmatrix} \Psi^\uparrow \\ \Psi^\downarrow \end{pmatrix}
$$

This can be rewritten as:

$$
\partial_T \Psi = -c \sigma_z \partial_X \Psi - i m \sigma_y \Psi
$$

(Note: Choice of Pauli matrix basis here depends on specific form of coin operator. Through basis transformation $\Psi \to U \Psi$, this can be transformed to standard Dirac equation form $i \gamma^\mu \partial_\mu \Psi - m \Psi = 0$).

For example, multiplying both sides by $i$, and identifying Hamiltonian:

$$
i \partial_T \Psi = H_{\text{Dirac}} \Psi = \left( -i c \sigma_z \partial_X + m \sigma_y \right) \Psi
$$

This is precisely the Hamiltonian of one-dimensional massive Dirac particle.

### 4.2.5 Physical Interpretation: Spin and Zitterbewegung

This derivation reveals extremely profound physical picture:

1. **Emergence of Spin**: At discrete QCA level, there is no intrinsic angular momentum concept of "spin," only internal states of "walking left" and "walking right." However, in continuous limit, these two states naturally evolve into two components of Dirac spinor. Macroscopically observed spin is essentially statistical manifestation of microscopic particles' **Chiral Motion Modes** on discrete grids.

2. **Mass as Coupling Constant**: Mass $m$ is no longer an externally added property, but originates from **coupling strength** between left and right chiral components (i.e., rotation angle $\theta$ in QCA). Particles have mass because they continuously undergo "left-right direction changes" (Zigzag motion) microscopically, causing effective propagation speed to be lower than light speed $c$.

3. **Geometric Interpretation of Zitterbewegung**: Schrödinger predicted that relativistic electrons have microscopic trembling. In QCA picture, this is no longer a mathematical singularity, but real microscopic physical process—particles indeed perform zigzag motion at light speed $c$, and the smooth trajectories we see macroscopically are just averages of this high-frequency trembling.

**Theorem 4.2.2 (QCA Convergence Theorem)**

For Dirac-type QCA universe $\mathfrak{U}_{\mathrm{QCA}}(\Theta)$ satisfying finite information axiom, when lattice spacing $a \to 0$ and rotation angle $\theta \sim ma$, its dynamics uniformly converges to Dirac equation evolution in Sobolev Norm sense. Effective light speed is determined by lattice geometry, effective mass is determined by local interaction parameters $\Theta_{\mathrm{dyn}}$.

Through this section, we proved that the most fundamental fermions in matter fields and their relativistic wave equations can be completely derived from a simple, local, discrete quantum information processing process. This strongly supports the core argument that "matter originates from information geometry." In the next section, we will further explore how gauge fields as connection variables emerge as Wilson Lines on lattices.

