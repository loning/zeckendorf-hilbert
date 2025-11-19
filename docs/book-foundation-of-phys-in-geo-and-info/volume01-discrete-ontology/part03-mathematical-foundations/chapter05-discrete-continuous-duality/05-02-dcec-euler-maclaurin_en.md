**5.2 Discrete-Continuous Error Control (DCEC): Euler-Maclaurin Expansion and Precise Control of Boundary Terms**

In Section 5.1, we established Physical Sampling Theorem through Poisson summation formula: for strictly band-limited physical fields, discrete summation and continuous integration are numerically precisely equivalent. However, in actual physical problems—especially when involving finite observation windows (finite time or space) or non-strictly band-limited functions (e.g., with exponentially decaying tails)—this perfect equivalence is broken.

At this point, a strict mathematical discipline must be introduced to quantify deviations between discrete models (QCA) and continuous effective theories (QFT). This section will establish **Discrete-Continuous Error Control (DCEC)** system, whose core tool is generalized Euler-Maclaurin expansion. We will prove that differences between discrete and continuous are not uncontrollable random noise, but structural corrections precisely determined by boundary terms and higher-order derivatives, directly related to Casimir Effect and topological anomalies in physics.

### 5.2.1 Discrete Summation Representation of Physical Quantities

In QCA universe, any macroscopic physical quantity $Q$ (such as total energy, partition function, or action) is essentially a summation defined on lattice $\Lambda$. Let $f(x)$ be density function of this physical quantity (e.g., Lagrangian density or density of states), then physical quantity $Q$ is:

$$
Q_{\text{disc}} = \sum_{n=0}^{N} f(x_n) \Delta x
$$

where $x_n = x_0 + n \Delta x$. In continuous field theory, we compute integral:

$$
Q_{\text{cont}} = \int_{x_0}^{x_N} f(x) \, \mathrm{d}x
$$

Core task of DCEC is to precisely evaluate difference $\Delta Q = Q_{\text{disc}} - Q_{\text{cont}}$. If this difference cannot be controlled, then continuous field theory is not an effective approximation of discrete ontology.

### 5.2.2 Generalized Euler-Maclaurin Formula

Euler-Maclaurin formula is one of the most powerful summation approximation tools in analysis. It not only gives integral approximation, but expands an asymptotic series containing boundary derivative information.

**Theorem 5.2.1 (Euler-Maclaurin Summation Formula)**

Let $f(x) \in C^{2k+1}[a, b]$, step size $h$ (corresponding to lattice spacing or Planck time $\tau$ in physics). Then relationship between discrete sum and continuous integral is:

$$
\sum_{n=0}^{N} f(x_n) h = \int_{x_0}^{x_N} f(x) \, \mathrm{d}x + \frac{h}{2} [f(x_N) + f(x_0)] + \sum_{j=1}^{k} \frac{h^{2j} B_{2j}}{(2j)!} \left[ f^{(2j-1)}(x_N) - f^{(2j-1)}(x_0) \right] + R_k
$$

where:

1. **Main Integral Term**: $\int f(x) \mathrm{d}x$, corresponding to predictions of continuous effective field theory.

2. **Boundary Correction Term**: $h[f(x_N) + f(x_0)]/2$, corresponding to boundary contribution of trapezoidal rule.

3. **Higher-Order Derivative Terms**: Containing Bernoulli numbers $B_{2j}$ ($B_2=1/6, B_4=-1/30, \dots$) and odd-order derivatives of function at boundaries.

4. **Remainder $R_k$**: $R_k = - \frac{h^{2k+2}}{(2k+2)!} \int_{x_0}^{x_N} B_{2k+2}(\{ \frac{x-x_0}{h} \}) f^{(2k+2)}(x) \, \mathrm{d}x$, where $B_n(t)$ are Bernoulli polynomials.

**Physical Interpretation**:

This formula shows that deviation between discrete and continuous is completely determined by **microscopic scale $h$** and **boundary behavior**.

* If physical field $f(x)$ and its derivatives all vanish at boundaries (e.g., local wave packets in vacuum), then all boundary correction terms disappear. At this point, difference between discrete sum and continuous integral is super-exponentially small (controlled by $R_k$), explaining why continuous field theory is so successful in free space.

* If physical boundaries exist (such as Casimir plates, black hole horizons, or cosmic initial/final moments), boundary terms $f^{(2j-1)}$ are non-zero. At this point, discrete summation will contain **quantum corrections** that continuous integrals cannot capture.

### 5.2.3 Physical Meaning of Boundary Terms: From Vacuum Energy to Topological Charge

Under DCEC framework, "error terms" in Euler-Maclaurin expansion often contain profound physical meaning. They are not computational waste, but **characteristic fingerprints of discrete geometry**.

**Case A: Casimir Effect**

Consider zero-point energy summation $E = \frac{1}{2} \sum \hbar \omega_n$ in one-dimensional cavity. In continuous limit, this integral is infinite (UV divergence). But under Euler-Maclaurin regularization, we subtract discrete sum from continuous integral; divergent main integral term is canceled, and remaining finite part is precisely Casimir energy contributed by Bernoulli number $B_2$:

$$
E_{\text{Casimir}} = E_{\text{sum}} - E_{\text{int}} \propto -\frac{\hbar c \pi}{24 L}
$$

Here $B_2 = 1/6$ directly determines coefficient $1/24$. This proves that discrete ontology naturally includes this macroscopic quantum effect through DCEC, without introducing artificial cutoff functions.

**Case B: Topological Indices**

In some topologically non-trivial systems (such as self-referential scattering networks or time crystals), boundary derivative terms of physical quantity $f(x)$ may not vanish, but accumulate into a topological invariant.

If $f(x)$ is some Berry curvature density or winding number density, then difference $\Delta Q$ may strictly equal an integer (i.e., discrete correction of Chern Number). At this point, DCEC reveals **topological rigidity of discrete geometry**: regardless of how lattice spacing $h$ changes (as long as phase transition point is not crossed), this integer difference remains unchanged.

### 5.2.4 Controllability of Errors and Gevrey Class Functions

To make continuous field theory a strict effective theory, we must prove remainder $R_k$ is negligible. This requires physical field functions to belong to specific smooth function classes.

**Definition 5.2.2 (DCEC Controllability Condition)**

A physical field $f(x)$ is called **DCEC controllable** in QCA limit if it satisfies Gevrey-s regularity condition (usually $s=1$ corresponds to analytic functions), such that for sufficiently large order $k$ and sufficiently small lattice spacing $h$, remainder satisfies exponential decay:

$$
|R_k| \le C e^{-\gamma / h}
$$

This means that as long as we do not probe violent oscillations of fields at Planck scale $h$, errors of continuous approximation are exponentially suppressed.

**Corollary 5.2.3 (Precision Bounds of Effective Field Theory)**

Any effective field theory (EFT) based on continuous manifolds has prediction precision essentially limited by $O(h^2)$ or $O(e^{-1/h})$. This is not only computational error, but **ontological error**. When experimental precision approaches this bound (e.g., in Planck stars or very early universe), we must switch back to summation form $\sum f(x_n)$, i.e., return to discrete dynamics of QCA.

### 5.2.5 Algorithm Implementation: Finite-Order Windowing Discipline

In experimental verification sections of Part III, we will use DCEC algorithms to process actual observation data. Since we can only observe signals within finite window $[0, T]$, direct application of Fourier transform leads to Gibbs Phenomenon.

**Definition 5.2.4 (Finite-Order Windowing Discipline)**

To implement DCEC in finite observations, a family of window functions $w(t)$ satisfying specific boundary derivative vanishing conditions (such as variants of flat prolate spheroidal wave functions PSWF) must be introduced. This discipline requires:

$$
w^{(j)}(0) = w^{(j)}(T) = 0, \quad \forall j = 0, 1, \dots, m
$$

Under such window functions, first $m$ boundary correction terms of Euler-Maclaurin expansion automatically vanish, making approximation precision of discrete sampling to continuous spectrum reach $O(h^{2m+2})$. This provides a rigorous mathematical method for eliminating discretization artifacts in gravitational wave data analysis and precision atomic clock measurements.

**Summary**

This section established a quantitative bridge connecting discrete QCA and continuous QFT through generalized Euler-Maclaurin formula.

1. **Equivalence**: In bulk regions, discrete sums and continuous integrals are highly consistent.

2. **Difference**: At boundaries and higher-order derivatives, differences are precisely controlled by Bernoulli terms, corresponding to Casimir forces, vacuum polarization, or topological charges.

3. **Controllability**: Through DCEC discipline, we can reconstruct continuous physical quantities from discrete data with arbitrarily specified precision, or conversely "discretize" predictions of continuous theories to compare with experiments.

At this point, we solved the mathematical legitimacy problem of "forming lines from points." In the next section, we will explore how to find optimal function bases to carry this information under finite observation windows, i.e., introduction of **Prolate Spheroidal Wave Functions (PSWF)**.

