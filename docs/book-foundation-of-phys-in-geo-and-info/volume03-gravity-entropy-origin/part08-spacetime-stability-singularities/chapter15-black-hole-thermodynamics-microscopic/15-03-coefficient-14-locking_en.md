**15.3 Locking of Coefficient $1/4$: Consistency Constraints of Unitarity and General Relativity**

In Section 15.2, we preliminarily established the relationship $S \propto A$ through matching microscopic counting (each edge contributes $\ln(2j+1)$) with holographic area ($A \sim \sqrt{j(j+1)}$). However, why is the coefficient exactly $1/4$? Intuitively, this means each Planck area carries only $1/4$ bit of effective entropy. The origin of this factor has always been a mystery.

This section will provide a **dynamical perspective** explanation. We will prove that the coefficient $1/4$ is not an accidental parameter of microscopic models (such as spin networks or strings), but the unique solution for compatibility between **macroscopic general relativity (GR)** and **microscopic quantum unitarity**. If we forcibly change this coefficient, we either break Einstein's equations (causing gravitational constant $G_{eff}$ to deviate from Newton's constant) or break probability conservation of QCA networks.

### 15.3.1 Coefficient Freedom in Generalized Entropy Variation

Recall the process of deriving Einstein's equations in Chapter 12. We start from generalized entropy variation $\delta S_{\text{gen}} = 0$, where:

$$
S_{\text{gen}} = \alpha \frac{A}{l_P^2} + S_{\text{mat}}
$$

Here $\alpha$ is an undetermined coefficient (in standard theory $\alpha = 1/4$).

Using the first law of entanglement $\delta S_{\text{mat}} = 2\pi \int T_{00} \zeta dV$ and area deficit formula $\delta A \propto -G_{00}$, the balance equation $\delta S_{\text{gen}} = 0$ derives field equations:

$$
-\alpha \frac{1}{l_P^2} \delta G_{00} + 2\pi \delta T_{00} = 0 \implies G_{00} = \frac{2\pi l_P^2}{\alpha} T_{00}
$$

In geometric units $8\pi G = 1$ (or $l_P^2 = G\hbar$). For this to be consistent with standard Einstein equations $G_{\mu\nu} = 8\pi G T_{\mu\nu}$, we must have:

$$
\frac{2\pi G}{\alpha} = 8\pi G \implies \alpha = \frac{1}{4}
$$

**Conclusion 1**: If we want to recover **general relativity** (i.e., Newtonian gravity as low-energy limit), the coefficient must be $1/4$. This is a requirement of gravitational dynamics.

### 15.3.2 Constraints from Unitarity and Page Curve

Now, we examine this coefficient from the perspective of quantum information theory.

Consider a black hole evaporation process. According to unitarity, the von Neumann entropy of black hole radiation $S_{\text{rad}}$ must follow the **Page curve**:

1. Early: $S_{\text{rad}}$ increases linearly with number of radiated particles (thermal radiation).

2. Page time: When $S_{\text{rad}}$ reaches the black hole coarse-grained entropy $S_{\text{BH}}$, the curve must turn.

3. Late: $S_{\text{rad}}$ decreases with decreasing black hole area, eventually returning to zero.

The key is the position of the turning point. Page time is determined by:

$$
S_{\text{rad}}(t_{\text{Page}}) \approx S_{\text{BH}}(t_{\text{Page}})
$$

If the microscopic entropy formula is $S_{\text{micro}} = \alpha A / G$, while macroscopic gravitational theory (determining black hole evaporation rate and lifetime) requires $S_{\text{macro}} = \frac{1}{4} A / G$, then:

* **If $\alpha > 1/4$** (too many microscopic degrees of freedom): The black hole interior can accommodate more information than the holographic bound. This means the black hole can evaporate longer without releasing information, leading to **remnant** problems or violating the holographic principle.

* **If $\alpha < 1/4$** (too few microscopic degrees of freedom): The black hole interior "cannot hold" the information implied by its surface area. This leads to **information cloning** or **non-unitarity**, because the information entropy carried away by radiation exceeds the maximum rate of entanglement entropy decrease the black hole can provide.

**Theorem 15.3.1 (Unitarity-Gravity Consistency Theorem)**

In QCA universes, to simultaneously satisfy:

1. **Macroscopic Dynamics**: Spacetime follows Einstein's equations (derived from IGVP).

2. **Microscopic Unitarity**: Information is conserved during evaporation (follows Page curve).

The statistical entropy density $\alpha$ of black holes must strictly equal the inverse coefficient of gravitational coupling constant $1/4$. Any deviation will lead to inconsistency of the theory in the semiclassical limit.

### 15.3.3 Microscopic Physical Explanation of Coefficient $1/4$

Why did nature choose $1/4$? In QCA discrete ontology, we can give a concrete geometric explanation.

**Explanation A: Thermal Layer Correction of Rindler Horizon**

In 't Hooft's "brick wall model," black hole entropy mainly comes from field modes within one Planck length $h$ near the horizon.

Calculations show that to obtain finite entropy, a cutoff must be introduced. And for $S = A/4G$ to hold, the cutoff distance $h$ must be precisely related to $G$.

In QCA, this means **the physical horizon is not a mathematical surface, but a physical layer of thickness $l_P$**. The coefficient $1/4$ reflects that in this thin layer, effective degrees of freedom are reduced by some gauge constraint (such as Gauss's law). For spin-1 gauge fields or spin-2 gravitational fields, counting of edge modes is suppressed by **volume redundancy** caused by gauge symmetry.

**Explanation B: Geometric Projection of Bits**

Consider a Planck area element $l_P^2$.

* **Maximum Information**: If we place a qubit on it, the information is 1 bit ($\ln 2$).

* **Gravitational Response**: Gravitational field equations require this area element to correspond to $4 \ln 2$ Planck areas of gravitational flux (to maintain Newton's force law).

This suggests spacetime geometry is a "sparse encoding" of information. The continuous geometric area $A$ we see is actually a 4-fold redundant representation of underlying quantum information. Or, **spacetime is a holographic projection of quantum entanglement, with projection ratio 4**.

### 15.3.4 Universality: From Black Holes to Cosmic Horizons

This coefficient locking applies not only to black holes, but also to de Sitter cosmic horizons.

In Chapter 9, we used $S_{dS} = A/4G$ to explain dark energy. If the coefficient were not $1/4$, the numerical value of cosmological constant $\Lambda$ would not match observations, or lead to thermodynamic instability (such as Boltzmann brain problems).

The consistency of the IGVP framework guarantees that all causal horizons in the universe follow the same entropy-area law.

**Conclusion**

The coefficient $1/4$ is the result of **geometry (Einstein equations) shaking hands with information (unitarity)**.

It does not require fine-tuning, but is the unique solution of theoretical self-consistency. It tells us that at Planck scale, every degree of freedom of physical reality precisely corresponds to 4 Planck area units of geometric cross-section. This provides the hardest quantitative constraint on the discrete structure of quantum gravity.

In the next section 15.4, we will use this entropy formula, combined with QCA's unitary evolution, to describe in detail the **information recovery mechanism** during black hole evaporation and reproduce the Page curve.

