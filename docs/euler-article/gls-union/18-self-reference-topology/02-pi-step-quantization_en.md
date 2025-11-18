# π-Step Quantization Mechanism

Argument Principle, Spectral Flow, and Rigorous Proof of Delay Quantization Steps

---

## Introduction

In previous chapter, we saw poles of closed-loop scattering matrix move with delay parameter $\tau$. When poles cross real axis, system's phase response jumps.

But **why π**? Why not other values? Is magnitude of this transition precisely predictable?

This chapter gives rigorous mathematical proof, revealing necessity of π-step. We will use **Argument Principle** in complex analysis and **Spectral Flow** theory in topology, establishing quantitative relationship from pole trajectories to phase transitions.

---

## Argument Principle: Topological Counting in Complex Plane

### Statement of Argument Principle

Let $f(z)$ be meromorphic function on complex plane (holomorphic except for finite poles), with $N_0$ zeros and $N_\infty$ poles (counting multiplicity) inside closed contour $\gamma$.

Then along $\gamma$ going around once, argument change of function is:

$$
\Delta_\gamma \arg f = \frac{1}{2\pi}\oint_\gamma d(\arg f)
= N_0 - N_\infty
$$

In more intuitive language: **Net winding number** of phase $\arg f$ of $f(z)$ along contour, equals number of zeros minus number of poles inside contour.

### Geometric Intuition

Imagine $f(z)$ is a mapping from complex plane to complex plane. When $z$ goes around $\gamma$ once, $f(z)$ draws a closed curve in image space.

- If $\gamma$ contains a zero, $f(z)$ winds around origin once (positive direction);
- If $\gamma$ contains a pole, $f(z)$ winds around origin once (negative direction).

Argument principle is essentially a **topological invariant**: Winding number is independent of continuous deformation of contour, only depends on number and type of singularities inside.

### Logarithmic Derivative Integral

Argument principle has equivalent integral form:

$$
\frac{1}{2\pi i}\oint_\gamma \frac{f'(z)}{f(z)}dz = N_0 - N_\infty
$$

Proof: Let $f(z) = (z-z_0)^m g(z)$, where $g(z_0)\neq 0$. Then:

$$
\frac{f'(z)}{f(z)} = \frac{m}{z-z_0} + \frac{g'(z)}{g(z)}
$$

Second term integrates to zero along small circle (because $g$ holomorphic), first term integrates to $2\pi i m$.

Summing over all zeros and poles gives argument principle.

---

## Scattering Phase and Determinant Argument

### From Scattering Matrix to Total Phase

For scattering matrix $S(\omega;\tau)$, define **total phase**:

$$
\varphi(\omega;\tau) = \arg\det S(\omega;\tau)
$$

This is a real-valued function, defined modulo $2\pi$. To study phase changes, we need to choose a continuous branch.

At fixed frequency $\omega=\omega_*$, treat $\varphi$ as function of $\tau$:

$$
\varphi(\tau) \equiv \varphi(\omega_*;\tau)
$$

When $\tau$ changes from $\tau_1$ to $\tau_2$, phase change is:

$$
\Delta\varphi = \varphi(\tau_2) - \varphi(\tau_1)
$$

Since phase defined modulo $2\pi$, we need to track phase along continuous path, ensuring no artificial $2\pi$ jumps.

### Determinant of Closed-Loop Scattering

For Schur complement form:

$$
S^{\circlearrowleft}(\omega;\tau) = S_{ee} + S_{ei}\mathcal{C}(\omega;\tau)[I - S_{ii}\mathcal{C}]^{-1}S_{ie}
$$

where $\mathcal{C}(\omega;\tau) = R(\omega)e^{i\omega\tau}$.

Using matrix determinant identity:

$$
\det(A + UCV) = \det(A)\det(I + CVA^{-1}U)
$$

Get:

$$
\det S^{\circlearrowleft} = \det S_{ee} \cdot \det\left[I + S_{ee}^{-1}S_{ei}\mathcal{C}(I-S_{ii}\mathcal{C})^{-1}S_{ie}\right]
$$

Further using $\det(I+AB)=\det(I+BA)$:

$$
\det S^{\circlearrowleft} = \det S_{ee} \cdot \frac{\det(I - S_{ii}\mathcal{C} + S_{ie}X S_{ei}\mathcal{C})}{\det(I - S_{ii}\mathcal{C})}
$$

(where $X=S_{ee}^{-1}$ and above can be simplified)

Most crucial observation:

> **Zeros and poles of determinant determined by zeros of denominator $\det(I - S_{ii}\mathcal{C})$.**

### Pole Equation and Spectral Flow

Let $S_{ii}(\omega)$ and $R(\omega)$ be smooth near real frequency. Poles satisfy:

$$
\det[I - R(\omega)e^{i\omega\tau}] = 0
$$

Extend $\omega$ to complex plane, $\omega = \omega_r + i\omega_i$.

For fixed $\tau$, pole trajectory $\omega(\tau)$ is family of curves satisfying above equation.

**Definition of Spectral Flow**: When $\tau$ changes from $\tau_1$ to $\tau_2$, sum of poles crossing real axis (from upper half-plane to lower half-plane, or reverse) is called spectral flow:

$$
\mathrm{Sf}(\tau_1\to\tau_2) = \#\{\text{downward crossings}\} - \#\{\text{upward crossings}\}
$$

This is a **signed topological count**.

---

## Proof of π-Step Theorem

### Theorem Statement

**Theorem (π-Step Transition)**

Under assumptions:
1. Scattering matrix $S(\omega;\tau)$ analytic in real frequency and parameter space;
2. At delay $\tau = \tau_c$, exactly one pole $\omega_c \in \mathbb{R}$ located on real axis;
3. This pole simple (i.e., $\partial_\tau \Im\omega(\tau_c) \neq 0$), crossing direction unique;
4. In small neighborhood of $(\omega_c, \tau_c)$, no other poles or zeros cross real axis.

Then at fixed frequency $\omega_* = \omega_c$, phase transition is:

$$
\Delta\varphi = \lim_{\epsilon\to 0^+}[\varphi(\tau_c+\epsilon) - \varphi(\tau_c-\epsilon)] = \pm\pi
$$

And sign determined by pole crossing direction:
- If pole from upper half-plane to lower half-plane (downward crossing): $\Delta\varphi = -\pi$
- If pole from lower half-plane to upper half-plane (upward crossing): $\Delta\varphi = +\pi$

### Proof Strategy

We decompose problem into three steps:

1. **Local Factorization**: Near $(\omega_c,\tau_c)$, factorize $\det S$ as product of pole factor and smooth factor;
2. **Argument Change of Pole Factor**: Calculate phase jump caused by single pole crossing real axis;
3. **Continuity of Smooth Factor**: Prove smooth factor's phase contribution continuous, produces no jump.

---

### Step 1: Local Factorization

In neighborhood $U$ of $(\omega_c, \tau_c)$, exist holomorphic functions $z(\tau)$ and $g(\omega;\tau)$ such that:

$$
\det S(\omega;\tau) = (\omega - z(\tau))^m \cdot g(\omega;\tau)
$$

where:
- $z(\tau_c) = \omega_c$ (pole exactly at $\omega_c$ when $\tau=\tau_c$)
- $m = +1$ corresponds to zero, $m = -1$ corresponds to pole
- $g(\omega_c;\tau_c) \neq 0$ (smooth factor non-zero)

This factorization comes from combination of residue theorem and implicit function theorem.

Since we consider poles (resonances), usually $m = -1$.

Taking logarithm:

$$
\log\det S(\omega;\tau) = m\log(\omega - z(\tau)) + \log g(\omega;\tau)
$$

Taking imaginary part (i.e., argument):

$$
\arg\det S(\omega;\tau) = m\arg(\omega - z(\tau)) + \arg g(\omega;\tau)
$$

---

### Step 2: Argument Change of Pole Factor

Fix $\omega = \omega_c$, define auxiliary function:

$$
h(\tau) = \omega_c - z(\tau)
$$

Linear expansion near $\tau_c$:

$$
z(\tau) \approx z(\tau_c) + (\tau - \tau_c)z'(\tau_c) = \omega_c + (\tau - \tau_c)z'(\tau_c)
$$

So:

$$
h(\tau) \approx -(\tau - \tau_c)z'(\tau_c)
$$

By assumption, $z'(\tau_c)$ has non-zero imaginary part:

$$
z'(\tau_c) = a + ib,\quad b \neq 0
$$

Then:

$$
h(\tau) = -(\tau - \tau_c)(a + ib)
$$

For $\tau > \tau_c$ and $\tau < \tau_c$:

$$
h(\tau_c + \epsilon) \approx -\epsilon(a + ib)
$$

$$
h(\tau_c - \epsilon) \approx \epsilon(a + ib)
$$

Calculating argument:

$$
\arg h(\tau_c + \epsilon) = \arg[-(a + ib)] = \pi + \arg(a + ib)
$$

$$
\arg h(\tau_c - \epsilon) = \arg(a + ib)
$$

Transition:

$$
\Delta\arg h = \arg h(\tau_c + \epsilon) - \arg h(\tau_c - \epsilon) = \pi
$$

(If $b > 0$; if $b < 0$ then $-\pi$)

---

### Step 3: Continuity of Smooth Factor

Smooth factor $g(\omega_c;\tau)$ non-zero near $\tau_c$, can choose continuous logarithm branch:

$$
\log g(\omega_c;\tau) = \log|g(\omega_c;\tau)| + i\arg g(\omega_c;\tau)
$$

Since $g$ non-zero and smooth, $\arg g$ is continuous function of $\tau$, produces no jump at $\tau_c$.

---

### Step 4: Total Phase Transition

Combining Steps 2 and 3:

$$
\varphi(\omega_c;\tau) = m\arg(\omega_c - z(\tau)) + \arg g(\omega_c;\tau)
$$

At $\tau = \tau_c$:

$$
\Delta\varphi = m \cdot \Delta\arg h + \underbrace{\Delta\arg g}_{=0}
= m \cdot (\pm\pi)
$$

For pole $m = -1$:

$$
\Delta\varphi = -(\pm\pi) = \mp\pi
$$

Sign depends on sign of imaginary part of $z'(\tau_c)$, i.e., direction of pole crossing real axis.

**Conclusion**: Phase transition magnitude exactly $\pm\pi$, QED.

---

## Calculation of Delay Quantization Steps

### Implicit Equation for Step Positions

Condition for pole crossing real axis: There exist real frequency $\omega_c \in \mathbb{R}$ and delay $\tau_c$ such that:

$$
\det[I - R(\omega_c)e^{i\omega_c\tau_c}] = 0
$$

and $\Im\omega_c = 0$.

For simple case (single eigenvalue $\lambda(\omega)$):

$$
\lambda(\omega_c)e^{i\omega_c\tau_c} = 1
$$

Writing as:

$$
|\lambda(\omega_c)| = 1,\quad \omega_c\tau_c + \arg\lambda(\omega_c) = 2\pi n
$$

First condition requires $\lambda$ has modulus 1 on real axis (lossless); second condition gives:

$$
\tau_c = \frac{2\pi n - \arg\lambda(\omega_c)}{\omega_c}
$$

This is **implicit equation**, because $\lambda(\omega_c)$ itself also depends on frequency.

### Explicit Approximation: Slow-Variation Approximation

If in small frequency window, $\lambda(\omega)$ approximately constant: $\lambda(\omega) \approx \lambda_0 e^{i\phi_0}$, then:

$$
\tau_k = \frac{2\pi k - \phi_0}{\omega_*}
$$

This gives family of equally spaced steps, spacing:

$$
\Delta\tau = \frac{2\pi}{\omega_*}
$$

Exactly "one optical period" round-trip time!

### Physical Meaning of Steps

Delay quantization steps $\tau_k$ correspond to: Each time feedback loop's round-trip phase $\omega\tau$ increases by $2\pi$, system "winds" one full circle in phase space, pole trajectory completes one "longitudinal mode" jump.

Analogy:
- **Fabry-Perot cavity**: Longitudinal mode spacing $\Delta\nu = c/(2L)$;
- **Optical microring**: Free Spectral Range (FSR) $\Delta\omega = 2\pi/\tau_{\mathrm{round}}$;
- **Self-referential scattering network**: Step spacing $\Delta\tau = 2\pi/\omega$.

This is same physical phenomenon (discrete spectrum from periodic boundary conditions) manifesting in different parameter spaces!

---

## Group Delay Double-Peak Merger and Square-Root Scaling

### Definition of Group Delay

Group delay matrix:

$$
Q(\omega;\tau) = -iS(\omega;\tau)^\dagger \frac{\partial S}{\partial\omega}
$$

Its trace gives total group delay:

$$
\tau_g(\omega;\tau) = \mathrm{tr}\,Q(\omega;\tau)
= -\Im\left[\mathrm{tr}\left(S^{-1}\frac{\partial S}{\partial\omega}\right)\right]
$$

In Schur complement form, can write as:

$$
\tau_g = \tau_g^{(0)} + \tau_g^{(\mathrm{fb})}
$$

where second term is feedback contribution.

### Origin of Double-Peak Structure

Near π-step $\tau \approx \tau_c$, pole trajectory $\omega_{\mathrm{pole}}(\tau)$ approaches real axis.

When scanning frequency $\omega$, group delay shows **Lorentzian resonance peak** near pole:

$$
\tau_g(\omega) \sim \frac{\Gamma}{(\omega - \omega_{\mathrm{pole}})^2 + \Gamma^2}
$$

where $\Gamma = |\Im\omega_{\mathrm{pole}}|$ is resonance width.

When $\tau$ approaches $\tau_c$, two poles (from $n$ and $n+1$ longitudinal modes) simultaneously approach real axis, producing two resonance peaks.

Peak positions:

$$
\omega_{\pm}(\tau) \approx \omega_c \pm \delta\omega(\tau)
$$

where $\delta\omega$ is peak spacing.

### Derivation of Square-Root Scaling Law

Near $\tau = \tau_c$, pole trajectory can use **local Puiseux expansion** (branch expansion):

$$
\omega_{\mathrm{pole}}(\tau) \approx \omega_c + A(\tau - \tau_c)^{1/2} + B(\tau - \tau_c) + \cdots
$$

This is because pole crossing real axis corresponds to **branch point** in complex frequency plane, similar to behavior of $\sqrt{z}$ at origin.

Substituting into pole equation, expanding to leading order, can rigorously derive:

$$
A^2 \sim \frac{\partial_\tau\lambda}{\partial_\omega\lambda}
$$

(Specific coefficient depends on local form of $\lambda(\omega)$)

Therefore, scaling law for peak spacing:

$$
\Delta\omega(\tau) = \delta\omega(\tau) \sim C\sqrt{|\tau - \tau_c|}
$$

where $C$ is constant determined by system parameters.

### Experimental Fingerprint

**Square-root scaling** is unique fingerprint of π-step:

1. Far from step ($|\tau - \tau_c| \gg \Delta\tau$): Group delay single peak, large peak width;
2. Approaching step: Single peak splits into double peak, peak spacing shrinks as $\sqrt{|\tau - \tau_c|}$;
3. Exactly at step: Double peaks merge into extremely sharp peak (theoretically width tends to zero);
4. Crossing step: Peak disappears or flips (phase transition $\pi$).

By fitting $\Delta\omega$ vs $\tau$ data, can precisely determine step position $\tau_c$ and scaling constant $C$.

---

## Connection with Scale Identity

### Phase Slope and Scale Density

Scale identity:

$$
\kappa(\omega;\tau) = \frac{1}{\pi}\frac{\partial\varphi}{\partial\omega}
= \frac{1}{2\pi}\mathrm{tr}\,Q(\omega;\tau)
$$

At fixed $\tau$, integrating over frequency:

$$
\int_{\omega_1}^{\omega_2} \kappa(\omega;\tau)d\omega
= \frac{1}{\pi}[\varphi(\omega_2;\tau) - \varphi(\omega_1;\tau)]
$$

This is **net phase change in frequency window** (normalized to $\pi$ units).

### Transition of Frequency Window Integral

Now fix frequency window $[\omega_c - \delta, \omega_c + \delta]$, let delay $\tau$ cross step $\tau_c$.

Define integral:

$$
I(\tau) = \int_{\omega_c - \delta}^{\omega_c + \delta} \kappa(\omega;\tau)d\omega
$$

**Proposition**: When $\tau$ crosses $\tau_c$, $I(\tau)$ jumps one unit:

$$
\Delta I = I(\tau_c + 0) - I(\tau_c - 0) = \pm 1
$$

**Proof**:
When $\tau < \tau_c$, frequency window contains one pole ($n$-longitudinal mode);
When $\tau > \tau_c$, this pole has left window, replaced by $(n+1)$-longitudinal mode.

By argument principle, phase difference at window boundaries changes by $\pm\pi$, so normalized integral changes by $\pm 1$.

This completely matches π-step theorem:

$$
\Delta\varphi = \pm\pi \quad\Leftrightarrow\quad \Delta I = \pm 1
$$

### Perspective of Unified Time Scale

Scale density $\kappa(\omega;\tau)$ can be understood as "physical time density per unit frequency".

Frequency window integral $I(\tau)$ is "total accumulated time in this frequency window".

π-step corresponds to: When delay parameter crosses quantization step, system's "effective time" in this frequency window suddenly increases or decreases by one unit.

This is a **quantized transition of time**, formally analogous to energy level transitions in quantum mechanics—except here what transitions is "time scale", not energy!

---

## Cumulative Effect of Multiple Steps

### Spectral Flow Counting and Integer Invariant

When delay $\tau$ increases from $\tau_0$ to $\tau$, may cross multiple steps $\tau_1, \tau_2, \ldots, \tau_K$.

Define **spectral flow count**:

$$
N(\tau) = \sum_{k: \tau_k < \tau} \Delta n_k
$$

where $\Delta n_k = \Delta\varphi_k/\pi = \pm 1$ is transition direction of $k$-th step.

This is an **integer topological invariant**, recording "net number of steps" system has experienced.

### Z₂ Reduction and Parity

Although $N(\tau)$ is integer, in many physical problems, only its **parity** is essential:

$$
\nu(\tau) = N(\tau) \bmod 2 \in \{0,1\}
$$

This is a **Z₂ topological index**.

In next chapter, we will discuss in detail why Z₂ parity is more "fundamental" than integer counting, and its deep connection with fermion statistics.

---

## Numerical Verification and Experimental Calibration

### Numerical Simulation Scheme

To verify π-step theory, can perform following numerical experiments:

1. **Choose Model**: Take single-channel feedback model or simple matrix model;
2. **Parameter Scan**: Fix frequency $\omega_*$, scan delay $\tau \in [\tau_{\min}, \tau_{\max}]$;
3. **Phase Calculation**: For each $\tau$, calculate $\varphi(\omega_*;\tau) = \arg S_{\mathrm{tot}}(\omega_*;\tau)$;
4. **Phase Unwrapping**: Use phase unwrapping algorithm to remove artificial $2\pi$ jumps;
5. **Step Identification**: Identify jumps of magnitude $\pm\pi$ on $\varphi(\tau)$ curve;
6. **Scaling Law Fitting**: Near each step, scan frequency, extract group delay double-peak spacing $\Delta\omega(\tau)$, fit $\Delta\omega \sim \sqrt{|\tau-\tau_c|}$.

### Experimental Measurement Protocol

On optical or microwave platform:

1. **Equipment**: Tunable delay line + vector network analyzer (or optical interferometer);
2. **Measurement**: Scan two-dimensional parameter space $(\omega,\tau)$, record complex scattering coefficients $S(\omega;\tau)$;
3. **Data Processing**:
   - Extract phase $\varphi(\omega;\tau) = \arg S(\omega;\tau)$;
   - Calculate group delay $\tau_g(\omega;\tau) = -\partial\varphi/\partial\omega$;
4. **Feature Identification**:
   - Plot phase contour map on $(\omega,\tau)$ plane, identify "phase cliffs" (π-steps);
   - Near steps, observe group delay double-peak merger;
5. **Quantitative Verification**:
   - Measure step spacing $\Delta\tau$, compare with theoretical prediction $2\pi/\omega$;
   - Fit square-root scaling law, extract system parameters.

---

## Chapter Summary

### Core Theorems

**π-Step Theorem**: Under assumption of simple pole crossing real axis, local transition of closed-loop scattering phase exactly $\pm\pi$.

**Delay Quantization**: Step positions determined by implicit equation $\omega\tau + \arg\lambda(\omega) = 2\pi n$, under slow-variation approximation, steps equally spaced, spacing equals round-trip time of one optical period.

**Square-Root Scaling Law**: Group delay double-peak spacing $\Delta\omega \sim \sqrt{|\tau-\tau_c|}$, this is local behavior from branch point, can serve as experimental fingerprint of π-step.

**Connection with Scale Identity**: Integral of scale density in frequency window $\int\kappa d\omega$ jumps one unit at step, equivalent to phase transition $\Delta\varphi=\pm\pi$.

### Physical Picture

> π-step is not "accidental behavior" of system, but **topological necessity**: Pole crosses real axis, argument principle guarantees phase exactly winds half circle. This is unified manifestation of complex analysis geometry and physical causality.

### Why is π Special?

Mathematically, $\pi$ is natural measure of "half circle"; physically, π-step corresponds to "half resonance"—system at critical point between resonance and anti-resonance.

More deeply, distinction between π vs $2\pi$ reflects topological divide of **single-valuedness vs double-valuedness**:
- Ordinary functions: Go around once return to original value (single-valued)
- Self-referential feedback: Go around once flip sign (double-valued)

This is exactly theme of next chapter's Z₂ parity transition!

---

## Thought Questions

1. **Generalization of Argument Principle**: If contour contains multiple poles crossing real axis simultaneously, is total phase transition equal to algebraic sum of contributions from each pole?

2. **Non-Simple Poles**: If pole is double (i.e., $m=2$), is phase transition $2\pi$? Try analyzing from local factor $(\omega-z(\tau))^{-2}$.

3. **Pole Merging**: If two poles simultaneously cross real axis and positions coincide, what happens? (Hint: This corresponds to "special point" or "singularity in parameter space")

4. **Experimental Noise**: In actual measurements, phase data contains noise. How to robustly identify π-steps? (Hint: Use integer property of frequency window integral)

5. **High-Dimensional Generalization**: If there are two tunable parameters $(\tau_1,\tau_2)$, does π-step generalize to "phase lines" in parameter plane? Can these lines form topological network?

---

## Preview of Next Chapter

After proving necessity of π-step, next chapter explores deeper topological structure:

**Z₂ Parity Transition and Topological Index**

We will:
- Construct topological parity index $\nu(\tau) = N(\tau) \bmod 2$
- Prove its flipping rule under evolution $\nu(\tau_k+0) = \nu(\tau_k-0) \oplus 1$
- Establish connection with fundamental group, Null-Modular double cover
- Explain why parity is more "fundamental" than integer

Let us continue deeper into topological mysteries of self-referential scattering!

