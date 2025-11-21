# Chapter 12: Entropic Variational Principle (IGVP) and Field Equations

In Chapter 11, we completed the foundational preparation of geometry and information thermodynamics: defined small causal diamonds as detection probes, introduced the generalized entropy functional $S_{\text{gen}}$, and established the first law of entanglement and Raychaudhuri equation as response functions for matter and geometry.

This chapter will formally propose the **Entropic Variational Principle (Information Geometric Variational Principle, IGVP)**. We will prove that Einstein's field equations are not a priori physical axioms, but inevitable mathematical corollaries of the **Maximum Entanglement Equilibrium Axiom** on spacetime geometry. Spacetime curves because it must maintain the extremal state of vacuum entanglement entropy under local geometric perturbations.

## 12.1 Maximum Entanglement Equilibrium Axiom: First-Order Variation Stationary Condition for Vacuum Entanglement Entropy

Traditionally, gravitational dynamics is derived from the variation of the Einstein-Hilbert action $I_{EH} = \int R \sqrt{-g}$. However, the physical origin of this action has remained obscure. In the discrete ontology and holographic framework, we replace it with a more information-theoretically grounded principle: **the equilibrium state of spacetime is defined by the maximization of generalized entropy**.

### 12.1.1 Maximum Entanglement Equilibrium Axiom (MEEA)

Consider a small causal diamond $\Sigma$ in Minkowski vacuum or any maximally symmetric background spacetime. We assume that the vacuum state $|\Omega\rangle$ represents some "optimized" state of quantum information distribution in this region.

**Axiom 12.1.1 (Maximum Entanglement Equilibrium Axiom)**

Under fixed causal geometric volume constraints, the generalized entropy $S_{\text{gen}}$ of the vacuum state is at a **local maximum** (or stationary value).

That is, for any first-order local perturbation $(\delta g, \delta \phi)$ of spacetime geometry $g_{ab}$ and quantum fields $\phi$ that preserves the causal diamond volume $V$, the first-order variation of generalized entropy vanishes:

$$
\delta S_{\text{gen}} \big|_{V} = \delta \left( \frac{A}{4G\hbar} + S_{\text{mat}} \right) = 0
$$

and the second-order variation $\delta^2 S_{\text{gen}} < 0$ (stability condition, to be discussed in Section 14.2 on QNEC).

**Physical Interpretation**:

This axiom analogizes spacetime geometry to the **equation of state** in thermodynamic systems.

* Changes in **matter entropy $S_{\text{mat}}$** represent the injection of "heat" or information flow.

* Changes in **geometric entropy $A/4G$** represent the geometric adjustments the system must make to maintain equilibrium (such as changes in horizon area).

* The equation $\delta S_{\text{gen}} = 0$ indicates that geometric deformations always precisely compensate for fluctuations in matter entropy to maintain total information balance.

### 12.1.2 Expansion of Variational Conditions: Geometric Side and Matter Side

To derive field equations from Axiom 12.1.1, we need to separately calculate the variations of the two parts of generalized entropy.

**1. Variation of Matter Entropy: First Law of Entanglement**

According to the first law of entanglement from Section 11.3, for perturbations of the vacuum state, the change in matter entanglement entropy equals the change in expectation value of the modular Hamiltonian $K$:

$$
\delta S_{\text{mat}} = \delta \langle K \rangle
$$

Using the Bisognano-Wichmann theorem, for small causal diamonds, the modular Hamiltonian is given by the integral of the energy-momentum tensor $T_{\mu\nu}$ along the conformal Killing vector $\zeta^\mu$. For a small diamond centered at the origin with lifetime $\tau$, on the Cauchy surface $\Sigma_0$ at $t=0$ (a sphere of radius $R \approx \tau/2$):

$$
\delta S_{\text{mat}} = \frac{2\pi}{\hbar} \int_{\Sigma_0} \delta \langle T_{\mu\nu} \rangle \zeta^\mu d\Sigma^\nu
$$

In Riemann Normal Coordinates, $\zeta^\mu \approx \frac{1}{R}(R^2 - r^2) \delta^\mu_0$ (approximately a parabolic weighting function). The integral approximates to:

$$
\delta S_{\text{mat}} \approx \frac{2\pi}{\hbar} \frac{\Omega_{d-2} R^d}{d^2-1} \delta T_{00}(0)
$$

Here $T_{00}(0)$ is the energy density at the diamond center.

**2. Variation of Geometric Entropy: Area Deficit**

The change in geometric entropy arises from the area change of the diamond boundary $\partial \Sigma$. According to the area deficit theorem from Section 11.1, in curved spacetime, the area of the geodesic sphere has second-order corrections relative to flat space (under first-order perturbations, metric changes cause area changes):

$$
\delta A = A_{\text{curved}} - A_{\text{flat}} = - \frac{\Omega_{d-2} R^d}{d^2-1} \delta G_{00}(0)
$$

where $\delta G_{00}$ is the perturbation value of the Einstein tensor at the center. Note the sign: positive energy density ($G_{00}>0$) causes gravitational focusing, reducing area, hence the negative sign.

Therefore, the variation of geometric entropy is:

$$
\delta S_{\text{grav}} = \frac{\delta A}{4G\hbar} = - \frac{1}{4G\hbar} \frac{\Omega_{d-2} R^d}{d^2-1} \delta G_{00}(0)
$$

### 12.1.3 Derivation of Einstein's Equations

Now, we substitute the variations of both parts into the equilibrium equation $\delta S_{\text{gen}} = 0$:

$$
\delta S_{\text{grav}} + \delta S_{\text{mat}} = 0
$$

$$
-\frac{1}{4G\hbar} \left( \frac{\Omega_{d-2} R^d}{d^2-1} \right) \delta G_{00} + \frac{2\pi}{\hbar} \left( \frac{\Omega_{d-2} R^d}{d^2-1} \right) \delta T_{00} = 0
$$

Canceling common geometric factors (volume element and dimension constants) and $\hbar$ (note that $\hbar$ appears on both sides and cancels, indicating that the final gravitational equation is classical):

$$
-\frac{1}{4G} \delta G_{00} + 2\pi \delta T_{00} = 0
$$

Rearranging:

$$
\delta G_{00} = 8\pi G \, \delta T_{00}
$$

Since this causal diamond can be constructed at any point in spacetime, and any timelike direction can be chosen as the time axis $u^\mu$ (via Lorentz transformation), according to tensor covariance, the scalar equation $\delta G_{00} = 8\pi G \delta T_{00}$ must hold for all components.

**Theorem 12.1.2 (Entropic Origin of Einstein's Field Equations)**

If spacetime satisfies the Maximum Entanglement Equilibrium Axiom (MEEA), i.e., the generalized entropy of local vacuum remains stationary under geometric perturbations, then the dynamics of spacetime metric $g_{\mu\nu}$ must follow Einstein's field equations:

$$
R_{\mu\nu} - \frac{1}{2} R g_{\mu\nu} + \Lambda g_{\mu\nu} = 8\pi G T_{\mu\nu}
$$

(Note: The cosmological constant $\Lambda$ appears as an integration constant, to be discussed in Section 12.3).

**Physical Corollaries**:

1. **Gravity is Not a Fundamental Force**: Gravitational equations are not equations of motion for microscopic particles, but rather **equations of state** similar to fluid mechanics equations. They describe how spacetime geometry "digests" entropy flow introduced by matter through curvature.

2. **Cancellation of Planck's Constant**: Although the derivation uses quantum entanglement ($S \sim \hbar^{-1}$) and Unruh temperature ($T \sim \hbar$), $\hbar$ cancels out in the final equation. This explains why general relativity, as a classical theory, has its roots in deep quantum effects.

3. **Meaning of G**: Newton's constant $G$ is no longer a coupling constant here, but rather a **conversion factor between spacetime entropy density and energy density** ($1/4G$ is the number of bits per Planck area).

### 12.1.4 Limitations and Generalizations

The above derivation relies on first-order perturbation approximation (linearized gravity). For strong gravitational fields or higher-order curvature corrections, we need to consider higher-order variations of generalized entropy.

If higher-order curvature terms (such as $R^2$ or Gauss-Bonnet terms) are introduced in the action, the Wald entropy formula shows that geometric entropy $S_{\text{grav}}$ will no longer be simply area $A/4G$, but will depend on derivatives of the Lagrangian with respect to the Riemann tensor.

Even so, **IGVP still holds**: as long as we correctly define generalized entropy (Wald entropy + matter entropy), its extremal condition still derives the corresponding higher-order gravitational field equations. This will be discussed in detail in Section 12.4.

**Summary**

This section completed the crucial leap from information-theoretic axioms to physical dynamical equations. We proved: **Einstein's equations are the equilibrium conditions of spacetime thermodynamics**. Spacetime curvature is not the heavy pressure of matter, but the balance requirement of entropy.

In the next section 12.2, we will further refine this derivation, generalizing from scalar entropy balance to the complete covariant form of tensor dynamics, and discuss the geometric meaning of energy-momentum tensor conservation.

