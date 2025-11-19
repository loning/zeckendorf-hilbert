**Chapter 4: Emergence of Field Theory from Discrete to Continuous**

In the first three chapters of Volume I, we established a completely discrete ontological framework: the physical universe is modeled as a Quantum Cellular Automata (QCA) $\mathfrak{U} = (\Lambda, \mathcal{A}, U, \omega_0)$ satisfying finite information axiom. In this picture, there is no continuous spacetime manifold, no differential equations, only algebraic evolution on discrete lattices.

However, the great success of macroscopic physics is built on continuous field theory (such as quantum electrodynamics and general relativity). The core task of this chapter is to build a solid mathematical bridge, proving that continuous field theory is not contradictory to discrete ontology, but its effective description in the **Long-wavelength Limit**. We will start from the most fundamental Feynman Path Integral, showing how it naturally emerges from unitary evolution of QCA.

### 4.1 Path Integral Discretization: Lattice Sum Representation of Feynman Kernel and Continuous Limit

In standard quantum mechanics, Feynman path integral provides an intuitive and powerful quantization method: the probability amplitude for a particle to move from one point to another is a weighted sum of all possible paths. In continuous spacetime, this involves mathematically subtle measure definition problems. But in our discrete QCA framework, path integral is no longer a formal definition requiring regularization, but a **strict combinatorial identity**.

#### 4.1.1 Definition of Discrete Propagator

Consider the one-step update operator $U$ in QCA universe. For any two lattice sites $x, y \in \Lambda$, we define the **discrete propagator** (or lattice kernel) $K(y, t; x, 0)$ from $x$ to $y$ after $t$ steps of evolution as:

$$
K(y, t; x, 0) = \langle y | U^t | x \rangle
$$

Here $|x\rangle$ and $|y\rangle$ are basis vectors of local Hilbert space $\mathcal{H}_\Lambda$ (for simplicity, temporarily assume each cell is a single state or consider scalar components; generalization to spinors only requires introducing internal indices).

According to definition of matrix multiplication, $U^t$ can be written as product of $t$ copies of $U$. Inserting $t-1$ sets of completeness relations $\sum_{z \in \Lambda} |z\rangle\langle z| = \mathbb{1}$, we obtain:

$$
K(y, t; x, 0) = \sum_{x_1, x_2, \dots, x_{t-1} \in \Lambda} \langle y | U | x_{t-1} \rangle \langle x_{t-1} | U | x_{t-2} \rangle \cdots \langle x_1 | U | x \rangle
$$

This formula is the **primitive form** of path integral.

#### 4.1.2 History Summation on Graphs: Feynman Checkerboard

Each sequence $\gamma = (x_0, x_1, \dots, x_t)$ in the above formula (where $x_0=x, x_t=y$) represents a **Worldline** or **History** of a particle on discrete spacetime grid $\Lambda \times \mathbb{Z}$.

**Definition 4.1.1 (Discrete Action)**

For path $\gamma$, its corresponding probability amplitude is the product of transition matrix elements at each step. We can write it in exponential form:

$$
A[\gamma] = \prod_{k=0}^{t-1} \langle x_{k+1} | U | x_k \rangle \equiv \exp\left( i S_{\text{disc}}[\gamma] \right)
$$

where $S_{\text{disc}}[\gamma]$ is defined as **discrete action**. If matrix elements of $U$ are complex $u_{ba} = |u_{ba}|e^{i\phi_{ba}}$, then discrete action contains two parts:

$$
S_{\text{disc}}[\gamma] = \sum_{k=0}^{t-1} \phi_{x_{k+1}, x_k} - i \sum_{k=0}^{t-1} \ln |u_{x_{k+1}, x_k}|
$$

If $U$ is a permutation matrix or Hadamard-type gate, modulus part is usually constant, and action is mainly determined by phase accumulation.

**Theorem 4.1.2 (Lattice Path Sum Formula)**

Discrete propagator strictly equals weighted sum of all allowed paths connecting $(x, 0)$ and $(y, t)$:

$$
K(y, t; x, 0) = \sum_{\gamma: x \to y} e^{i S_{\text{disc}}[\gamma]}
$$

Due to finite propagation radius $R$ of QCA (see Section 3.2), only paths satisfying $|x_{k+1} - x_k| \le R$ have non-zero amplitude. This means summation is only over paths within **geometric light cone**, with no divergence problems. This is called a generalization of **Feynman Checkerboard** model.

#### 4.1.3 Continuous Limit and Smoothing

Now we examine the macroscopic limit. Introduce discretization parameters: lattice spacing $\varepsilon$ (corresponding to physical length $a$) and time step $\tau$ (corresponding to physical time $\Delta t$). Macroscopic coordinates $X = x\varepsilon, T = t\tau$.

We require that in the limit $\varepsilon, \tau \to 0$, discrete propagator $K$ converges to kernel $K_{\text{cont}}(Y, T; X, 0)$ of continuous quantum mechanics. This requires fine-tuning parameters of update operator $U$.

Consider one-dimensional Dirac-type QCA (as described in Section 3.3), whose update operator in momentum space is:

$$
U(k) = e^{-ik\sigma_z \varepsilon} e^{-i m \tau \sigma_x}
$$

(Here using natural units, parameter mapping see Theorem 3.4).

For a path $\gamma$, its "large zigzag" motion on lattice corresponds to zigzag trajectory of particle. When $\varepsilon \to 0$, large numbers of microscopic "Zitterbewegung" paths are statistically averaged.

**Lemma 4.1.3 (Phase Stationarity and Classical Paths)**

In path sum $\sum e^{i S_{\text{disc}}}$, when action $S_{\text{disc}}$ is much larger than $\hbar$ (i.e., $S \gg 1$ in our dimensionless units), main contributions come from paths where first-order derivative of $S_{\text{disc}}$ with respect to path variation is zero. These paths correspond to solutions of discrete version of Euler-Lagrange equations, i.e., **classical trajectories**.

In continuous limit, discrete action $S_{\text{disc}}[\gamma]$ converges to continuous functional:

$$
S_{\text{disc}}[\gamma] \xrightarrow{\varepsilon \to 0} \int_0^T \mathcal{L}(X, \dot{X}) \, dt
$$

where Lagrangian $\mathcal{L}$ is determined by microscopic parameters of $U$.

#### 4.1.4 From Summation to Functional Integral

Through the above limit process, discrete summation symbol $\sum_{\gamma}$ formally transforms into continuous functional integral symbol $\int \mathcal{D}X$.

**Theorem 4.1.4 (Emergence of Feynman Kernel)**

Let QCA satisfy Dirac continuous limit conditions (Theorem 3.4). For macroscopic observers, lattice propagator $K(y, t; x, 0)$ weakly converges to continuous Feynman kernel after renormalization:

$$
\lim_{\varepsilon \to 0} Z(\varepsilon)^{-1} K(\lfloor X/\varepsilon \rfloor, \lfloor T/\tau \rfloor; \lfloor X_0/\varepsilon \rfloor, 0) = \int_{X(0)=X_0}^{X(T)=X} \mathcal{D}X(t) \exp\left( \frac{i}{\hbar} \int_0^T \mathcal{L}_{\text{Dirac}} \, dt \right)
$$

where $Z(\varepsilon)$ is wave function renormalization constant, $\mathcal{L}_{\text{Dirac}} = \bar{\psi}(i\gamma^\mu \partial_\mu - m)\psi$ is Lagrangian density of Dirac field (corresponding to relativistic action of particle in single-particle sector).

**Physical Interpretation**:

This result shows that **path integral is not a fundamental axiom of quantum mechanics, but statistical emergence of combinatorial properties of discrete unitary evolution in continuous limit**.

1. **Renormalization is unnecessary**: In our theory, $\varepsilon$ is physical Planck-scale cutoff, not a mathematical auxiliary quantity that needs to be taken to zero. Path integral is ontologically always a finite sum.

2. **Essence of imaginary time**: Usually Wick rotation $t \to -i\tau$ in field theory transforms path integral into statistical partition function. In QCA, this corresponds to studying spectral properties of operator $U$ and maximum eigenvalue problem of transfer matrix.

Through this section, we completed the crucial leap from "jumping operators" to "flowing fields." In this framework, Feynman Diagrams are no longer merely computational tools of perturbation theory, but topological descriptions of actual propagation histories of particles in underlying discrete spacetime networks. Next, we will specifically derive how spinor fields (Dirac equation) are born from such discrete walks.

