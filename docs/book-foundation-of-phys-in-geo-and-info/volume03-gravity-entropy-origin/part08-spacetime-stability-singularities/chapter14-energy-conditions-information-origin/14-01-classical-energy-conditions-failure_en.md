# Part VIII: Spacetime Stability and Singularities

## Chapter 14: Information-Theoretic Origin of Energy Conditions

In Part VII, we established the Entropic Variational Principle (IGVP) and derived Einstein's field equations $G_{\mu\nu} = 8\pi G T_{\mu\nu}$. This equation tells us how spacetime responds to matter and its motion, but it does not restrict the nature of matter itself. If the energy-momentum tensor $T_{\mu\nu}$ of matter can take arbitrary values (such as arbitrarily large negative energy density), general relativity would allow various pathological spacetime structures, such as traversable wormholes, time machines (closed timelike curves), and catastrophic vacuum instability.

To guarantee the causal structure and thermodynamic stability of spacetime, physics must impose restrictions on $T_{\mu\nu}$, namely **Energy Conditions**. This chapter will prove that classical energy conditions necessarily fail in the quantum world, replaced by the deeper **Quantum Null Energy Condition (QNEC)**. We will reveal that QNEC is not an additional assumption, but a direct corollary of **non-positivity of the second-order variation of generalized entropy**. Energy must be restricted not because of the "hardness" of matter, but because the flow rate of information cannot exceed the limit allowed by its entanglement structure.

### 14.1 Failure of Classical Energy Conditions and the Dilemma of Semiclassical Gravity

In classical general relativity, to prove singularity theorems or the positive mass theorem, we usually assume matter satisfies the Null Energy Condition (NEC). However, with the development of quantum field theory, it was discovered that this classical assumption is extremely fragile at the microscopic level. This section will analyze this contradiction and point out the stability crisis faced by semiclassical gravity as a result.

#### 14.1.1 Classical Null Energy Condition (NEC) and Its Geometric Significance

**Definition 14.1.1 (Null Energy Condition / NEC)**

For any point $p$ in spacetime and any null vector $k^\mu$, the energy-momentum tensor of matter satisfies:

$$
T_{\mu\nu} k^\mu k^\nu \ge 0
$$

Physically, this means that the local energy density measured by any observer moving at light speed must be non-negative.

**Geometric Corollary: Gravitational Focusing**

Combining Einstein's equation $R_{\mu\nu} - \frac{1}{2}Rg_{\mu\nu} = 8\pi G T_{\mu\nu}$, NEC is equivalent to the geometric condition $R_{\mu\nu} k^\mu k^\nu \ge 0$.

Substituting into the Raychaudhuri equation (Section 11.4):

$$
\frac{d\theta}{d\lambda} = -\frac{1}{d-2}\theta^2 - \sigma^2 - R_{\mu\nu} k^\mu k^\nu
$$

If NEC holds, then $\frac{d\theta}{d\lambda} \le 0$. This guarantees that **gravity is always attractive**, and beams that begin to converge will inevitably form foci (Focusing Theorem). This is the foundation of the Penrose-Hawking singularity theorem and the theorem that black hole horizon cross-sectional area monotonically increases (the geometric version of the second law of thermodynamics).

#### 14.1.2 Universal Violation of NEC by Quantum Field Theory

Although macroscopic classical fluids usually satisfy NEC, in quantum field theory (QFT), NEC is not an operator-level identity. In fact, the renormalized energy-momentum tensor expectation value $\langle T_{\mu\nu} \rangle$ can easily violate NEC.

**Case A: Casimir Effect**

In the vacuum between two parallel metal plates, due to mode truncation, the vacuum zero-point energy density $\rho_{vac}$ is lower than that of free vacuum outside the plates.

$$
\rho_{vac} = -\frac{\pi^2 \hbar c}{720 a^4} < 0
$$

For photons moving parallel to the plates, the projected energy density they experience is negative, i.e., $\langle T_{\mu\nu} \rangle k^\mu k^\nu < 0$. This means that between Casimir plates, gravity is actually repulsive (causing beam divergence).

**Case B: Squeezed Vacuum State**

In quantum optics, squeezed states can be prepared using nonlinear crystals. In certain spacetime regions, energy density can be lower than the vacuum ground state (negative energy), as long as there is positive energy compensation in other regions. Epstein et al. (1965) proved that no local operator can guarantee $\langle T_{\mu\nu} \rangle$ is non-negative everywhere.

#### 14.1.3 Stability Crisis of Semiclassical Gravity

When we consider the semiclassical Einstein equation $G_{\mu\nu} = 8\pi G \langle T_{\mu\nu} \rangle$, the failure of NEC leads to serious theoretical crises.

1. **Wormholes and Time Machines**: If $T_{\mu\nu} k^\mu k^\nu < 0$ is allowed, we can construct Morris-Thorne wormholes with "negative energy propping up" throats. Further combining wormholes can create closed timelike curves (CTC), violating causality.

2. **Horizon Stability**: If energy density near black hole horizons is negative, beams can diverge ($\theta > 0$), causing horizon area to decrease ($\dot{A} < 0$). This violates the second law of black hole thermodynamics.

3. **Vacuum Decay**: If energy density has no lower bound, spacetime itself might collapse toward negative energy states with arbitrarily large curvature.

**Summary of Dilemma**:

On one hand, quantum mechanics clearly allows local negative energy; on the other hand, the stability of general relativity strongly depends on positive energy conditions.

This suggests: **simply $T_{\mu\nu} \ge 0$ is the wrong condition**. From the perspective of information physics, the lower bound of energy density should not be zero, but should be related to **entropy flow of quantum information**.

Energy can be negative, but not "too negative." What determines this "degree"? It is determined by the **uncertainty principle** and **entanglement structure**. Negative energy is often accompanied by weakening of quantum entanglement or establishment of specific correlations. This guides us to seek a new bound that directly relates energy $T_{\mu\nu}$ to entropy $S$—this is the **Quantum Null Energy Condition (QNEC)** to be derived in the next section.

