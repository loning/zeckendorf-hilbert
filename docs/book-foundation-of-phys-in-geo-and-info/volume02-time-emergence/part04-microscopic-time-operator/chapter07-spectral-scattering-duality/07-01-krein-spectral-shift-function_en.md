### Chapter 7: Spectrum-Scattering Duality and Thermodynamics

**7.1 Kreĭn Spectral Shift Function $\xi(E)$: The Rearrangement Mechanism of Perturbation on Energy Level Density**

In Chapter 6, we established the time delay theory based on the scattering matrix and its energy derivative (EWS operator $\mathsf{Q}$). We found that the dwell time of microscopic particles in the interaction region is closely related to changes in the density of states (DOS). This discovery suggests a profound duality between dynamics (scattering) and thermodynamics (spectrum).

This chapter will formally establish this duality. We will introduce an extremely powerful tool in mathematical physics—the **Kreĭn Spectral Shift Function** (SSF). $\xi(E)$ is not only a bridge connecting microscopic scattering phase shifts with macroscopic thermodynamic partition functions, but also the key to understanding "how matter occupies energy space." From the perspective of discrete ontology, it describes how information (quantum states) rearranges on energy levels when a perturbation (interaction) is added to the universe.

#### 7.1.1 The Perturbation Problem in Infinite-Dimensional Systems

Consider a free Hamiltonian $H_0$ and a perturbed Hamiltonian $H = H_0 + V$. In finite-dimensional systems, we can directly calculate eigenvalue shifts. Let the eigenvalues of $H_0$ be $\{E_n^{(0)}\}$ and those of $H$ be $\{E_n\}$. The total energy level shift of the system is $\sum (E_n - E_n^{(0)})$.

However, in continuum physics (such as scattering problems or quantum field theory), the Hilbert space is infinite-dimensional, and the spectrum contains continuous parts. Direct summation over eigenvalues is usually divergent. For example, although the perturbation $V$ is local (trace-class operator), it may cause infinitely many scattering states to undergo small phase shifts, making the total energy change impossible to define simply.

To solve this problem, I. M. Lifshitz (1952) and M. G. Kreĭn (1953) proposed a regularized counting method: instead of tracking individual energy levels, we track the overall migration of **density of states**.

#### 7.1.2 Axiomatic Definition of the Spectral Shift Function

We first give a sufficient condition that makes the trace formula well-defined.

**Definition 7.1.1 (Relative Trace-Class Perturbation)**

Let $H_0$ and $H$ be two self-adjoint operators on Hilbert space $\mathcal{H}$. If their resolvent difference is a trace-class operator, i.e., for some $z \in \mathbb{C} \setminus \mathbb{R}$:

$$
D(z) \equiv (H - z)^{-1} - (H_0 - z)^{-1} \in \mathcal{L}_1(\mathcal{H})
$$

then $H$ is called a relative trace-class perturbation of $H_0$. This usually requires the potential $V$ to decay sufficiently fast in space (e.g., $(1+|x|)^\alpha V \in L^1$).

**Theorem 7.1.2 (Lifshitz-Kreĭn Trace Formula)**

For a relative trace-class perturbation pair $(H, H_0)$, there exists a unique real-valued integrable function $\xi(\lambda) \in L^1(\mathbb{R})$ such that for any sufficiently nice function $f$ (such as Schwartz functions or smooth functions with appropriate decay), the following identity holds:

$$
\operatorname{Tr}\left[ f(H) - f(H_0) \right] = \int_{-\infty}^{+\infty} \xi(\lambda) f'(\lambda) \, \mathrm{d}\lambda
$$

The function $\xi(\lambda)$ is called the **Kreĭn Spectral Shift Function**.

**Physical Interpretation**:

This formula is the cornerstone of quantum statistical mechanics. The left side is the difference of macroscopic quantities (e.g., if $f(H) = e^{-\beta H}$, then the left side is the difference in partition functions $\Delta Z$). The right side transforms this trace into an integral, where the weight function $\xi(\lambda)$ contains all information about the perturbation's effect on the spectral structure.

Note that $f'(\lambda)$ appears on the right side rather than $f(\lambda)$. This suggests that $\xi(\lambda)$ itself has the nature of a "cumulative distribution," similar to a step function.

#### 7.1.3 Geometric Meaning of the Spectral Shift Function: Energy Level Counter

To intuitively understand $\xi(E)$, we examine a system placed in a large box (volume $L^3$). The spectrum is then discrete.

Let $N_0(E)$ be the number of eigenstates of $H_0$ below energy $E$ (cumulative density of states), and $N(E)$ be the corresponding number for $H$.

Formally, we can write:

$$
\operatorname{Tr}[f(H) - f(H_0)] \approx \sum_n f(E_n) - \sum_m f(E_m^{(0)}) = \int f(\lambda) \mathrm{d}(N(\lambda) - N_0(\lambda))
$$

Integration by parts gives:

$$
\int f(\lambda) \mathrm{d}(\Delta N) = f(\lambda)\Delta N(\lambda) \Big|_{-\infty}^\infty - \int \Delta N(\lambda) f'(\lambda) \mathrm{d}\lambda
$$

Comparing with the Kreĭn formula, we obtain an extremely intuitive correspondence:

$$
\xi(E) = -\left[ N(E) - N_0(E) \right]
$$

(Note: Sign conventions may vary in the literature. Kreĭn's original definition usually takes a positive sign, but this depends on the sign before $f'$. In physics literature, $\xi(E)$ is usually defined as positive to indicate that an attractive potential causes energy levels to shift down. Here we adopt the standard mathematical convention: $\xi(\lambda)$ almost everywhere equals the dimension of the spectral projection of $H_0$ minus that of $H$, but in scattering phase shift relations, we usually have $\xi(E) = \frac{1}{\pi} \delta(E)$. We will fix the sign in Section 7.2 to match the Birman-Kreĭn formula.)

**Revised Definition 7.1.3 (Physical Spectral Shift)**

In this book, we define the physical spectral shift function $\xi(E)$ as: **due to the introduction of interaction $V$, how many quantum states have crossed from above energy $E$ to below $E$**.

* $\xi(E) > 0$: Indicates an attractive potential, energy levels shift down (spectral flow to the left), "accumulating" extra states at $E$.

* $\xi(E) < 0$: Indicates a repulsive potential, energy levels shift up.

#### 7.1.4 Relationship Between Spectral Shift and Density of States

Using $\xi(E) \sim -\Delta N(E)$, we can immediately obtain its relationship with the change in local density of states $\Delta \rho(E)$.

Since the density of states $\rho(E) = \frac{dN}{dE}$, we have:

$$
\Delta \rho(E) = \rho(E) - \rho_0(E) = \frac{d}{dE} (N(E) - N_0(E)) = -\frac{d\xi}{dE}
$$

This is exactly the relationship we previewed in Section 6.4 (note the sign difference: if $\xi$ is defined as phase shift $\delta/\pi$, then $\rho \sim \xi'$; if $\xi$ is defined as counting difference, then $\rho \sim -\xi'$. The standard form of Kreĭn's theorem supports the relationship between $\xi'$ and the trace).

**Rigorous Derivation**:

In the trace formula, take $f_\epsilon(\lambda)$ as a smooth approximate step function at $E$ (integral of $\delta$ function).

$$
\operatorname{Tr}[\delta(H-E) - \delta(H_0-E)] = \Delta \rho(E)
$$

According to the formula:

$$
\int \xi(\lambda) \delta'(\lambda-E) \mathrm{d}\lambda = -\xi'(E)
$$

Therefore:

$$
\Delta \rho(E) = -\xi'(E)
$$

**Conclusion 7.1.4 (Matter is the Gradient of Spectral Shift)**

This formula reveals the ontological meaning of matter's existence: **the existence of particles manifests as local deformation of the vacuum energy spectrum**.

When we say there is "a particle" or "a scatterer" at some location in space, in the language of spectral geometry, it means the spectral shift function $\xi(E)$ at that location has a non-zero slope.

* **Bound States**: Correspond to integer jumps of $\xi(E)$. In the region $E < 0$, $\xi(E)$ is a series of steps, with each step height corresponding to the multiplicity of bound states.

* **Scattering States**: Correspond to smooth changes in $\xi(E)$. In the region $E > 0$, $\xi(E)$ changes continuously, describing the rearrangement of continuous spectrum density.

#### 7.1.5 Properties and Boundary Behavior of the Spectral Shift Function

As part of the book's "discrete-continuous" unification, $\xi(E)$ has perfect mathematical properties:

1.  **Compact Support or Fast Decay**: If the perturbation $V$ is finite-rank or local, $\xi(E)$ rapidly tends to zero at high energies. This means high-energy physics is unaffected by low-energy perturbations (decoupling theorem).

2.  **Additivity**: For mutually independent subsystems, the total spectral shift equals the sum of spectral shifts of each part. This makes $\xi$ a generalized **extensive quantity**.

3.  **Topological Robustness**: $\int_{-\infty}^\infty \xi'(E) dE = \xi(\infty) - \xi(-\infty)$. This integral usually equals the total change in bound state number or a specific topological charge (as shown by Levinson's theorem).

By introducing the Kreĭn spectral shift function, we successfully transform the time-based dynamical description (the $\mathsf{Q}$ matrix) from Chapter 6 into an energy-based static description. In the next section, we will strictly equate these two (scattering phase shift and spectral shift function) mathematically through the famous **Birman-Kreĭn trace formula**, thereby completing the triangular unification of "time-energy-information."

