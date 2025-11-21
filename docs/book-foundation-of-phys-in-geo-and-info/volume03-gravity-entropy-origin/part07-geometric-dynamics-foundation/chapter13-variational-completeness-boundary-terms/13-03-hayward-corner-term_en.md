**13.3 Hayward Corner Term: Entropy Additivity on Non-smooth Geometry**

In Section 13.2, we proved that the GHY boundary term $I_{\text{GHY}}$ is necessary to ensure the variational well-posedness of the gravitational action on smooth manifolds. However, spacetime regions of physical interest often have **non-smooth boundaries**. For example, causal diamonds are formed by the intersection of two light cones ($J^+(p)$ and $J^-(q)$), and their boundaries are non-smooth at the interface (edge $\partial \Sigma$), forming a codimension-2 "corner" or "joint". Additionally, when computing path integrals, we often need to divide spacetime into several pieces (such as time slices of Euclidean black holes), and these pieces also form non-smooth interfaces at junctions.

If these corner contributions are ignored, the variational principle of the action will fail again, and entropy additivity ($S_{A \cup B} = S_A + S_B$) will be violated. This section will introduce the **Hayward Corner Term**, proving it is a natural extension of the GHY term on non-smooth geometry, and ensuring strict additivity of generalized entropy under complex geometric splicing.

### 13.3.1 Variational Residual Terms on Piecewise Smooth Boundaries

Consider a spacetime region $M$ whose boundary $\partial M$ consists of several smooth segments $\mathcal{B}_i$ (e.g., $\partial M = \mathcal{B}_1 \cup \mathcal{B}_2$), which intersect at junction $\mathcal{C} = \mathcal{B}_1 \cap \mathcal{B}_2$.

On each smooth segment $\mathcal{B}_i$, the GHY term $\frac{1}{8\pi G} \int K_i$ can cancel normal derivative variations in that region. But at junction $\mathcal{C}$, the unit normal vector jumps from $n_1$ to $n_2$. Extrinsic curvature $K$ contains the divergence of the normal vector $\nabla \cdot n$, and at points where the normal vector is discontinuous, $\nabla \cdot n$ manifests as a $\delta$-function singularity.

If we directly vary the piecewise GHY term, integration by parts will leave uncanceled boundary terms at corner $\mathcal{C}$:

$$
\delta I_{\text{bulk}} + \delta I_{\text{GHY}} \sim \int_{\mathcal{C}} (\delta n_1 \cdot n_2 + \dots) \neq 0
$$

This shows that for non-smooth geometry, an additional action $I_{\text{joint}}$ defined on corner $\mathcal{C}$ must be explicitly introduced.

### 13.3.2 Definition of Hayward Term and Joint Angle Dictionary

Hayward (1993) pointed out that this corner term depends on the "angle" between the two interface normal vectors. Since spacetime has Lorentz signature, the definition of this "angle" depends on the causal nature of the interfaces (timelike, spacelike, or null).

**Definition 13.3.1 (Hayward Corner Term)**

For a codimension-2 joint $\mathcal{C}$ (e.g., the intersection of two hypersurfaces), let its induced metric be $\sigma_{ab}$ (area element $\sqrt{\sigma} d^2x$). The Hayward term is defined as:

$$
I_{\text{Hayward}} = \frac{1}{8\pi G} \int_{\mathcal{C}} \eta \, \sqrt{\sigma} \, \mathrm{d}^2x
$$

where $\eta$ is the **joint angle**, whose specific form is determined by the intersecting interface normal vectors $n_1, n_2$ and their moduli $\varepsilon_i = n_i^2 = \pm 1$.

**Joint Angle Dictionary**:

1. **Spacelike-Spacelike Junction** ($\varepsilon_1 = \varepsilon_2 = -1$): Corresponds to hyperbolic angle.

   $$\eta = \operatorname{arccosh}(-n_1 \cdot n_2)$$

   This appears in the evolution of time slices.

2. **Timelike-Timelike Junction** ($\varepsilon_1 = \varepsilon_2 = +1$): Corresponds to the usual geometric angle.

   $$\eta = \arccos(n_1 \cdot n_2)$$

   This appears in splicing of spatial regions.

3. **Mixed Junction** ($\varepsilon_1 \varepsilon_2 = -1$):

   $$\eta = \operatorname{arcsinh}(n_1 \cdot n_2)$$

   This appears at the edge of causal diamonds (junction of timelike boundary and spacelike slice).

For cases involving **null** boundaries (such as light cones), the normal vector modulus is zero, and the angle needs regularization through logarithmic form (see Section 13.3.4).

### 13.3.3 Variational Completeness and Additivity Theorem

After introducing the Hayward term, the total action $I = I_{\text{EH}} + I_{\text{GHY}} + I_{\text{Hayward}}$ regains completeness.

**Theorem 13.3.2 (Additivity Theorem)**

Let spacetime region $M$ be divided into two subregions $M_1$ and $M_2$ with common boundary $\Sigma$. Then the total action satisfies strict additivity:

$$
I[M_1 \cup M_2] = I[M_1] + I[M_2]
$$

**Proof Outline**:

At junction $\Sigma$, the GHY term contributes twice (from boundaries of $M_1$ and $M_2$ respectively). Since outward normals are opposite $n_1 = -n_2$, for smooth parts $K_1 = -K_2$, seemingly directly canceling. But at the boundary of $\Sigma$ (i.e., corners of $M$), simple $K$ integration leads to endpoint effects.

The role of the Hayward term is precisely to compensate for these endpoint effects. Specifically, when calculating $\delta I$, the corner residual terms $\delta \eta$ produced by integration by parts precisely cancel with the variation of $I_{\text{Hayward}}$. This ensures we can splice spacetime regions like building blocks without worrying about mathematical pathologies on boundaries.

**Physical Corollary (Entropy Additivity)**:

In the Euclidean path integral, entropy $S \sim I$. Theorem 13.3.2 guarantees entropy additivity.

If we calculate the entropy of a black hole, we can view its horizon as the splicing of two hemispheres. The Hayward term ensures that geometric contributions at the equatorial cross-section are correctly counted, so total entropy $S = A/4G$ still holds, rather than losing information due to division.

### 13.3.4 Special Case of Causal Diamonds: Null Joints

For the **small causal diamonds** central to this book, their boundaries are formed by null surfaces (light cones). Null normal vectors $\ell$ satisfy $\ell^2=0$, so the above $\arccos$ or $\operatorname{arccosh}$ definitions fail.

In this case, the Hayward term reduces to a **null joint term**. Let two null vectors $\ell$ and $\bar{\ell}$ intersect at edge $\partial \Sigma$ (normalized as $\ell \cdot \bar{\ell} = -2$ or other constant). The corner term takes logarithmic form:

$$
I_{\text{null-joint}} = \frac{1}{8\pi G} \int_{\partial \Sigma} \ln |-\frac{1}{2} \ell \cdot \bar{\ell}| \, \sqrt{\sigma} \, \mathrm{d}^2x
$$

This term is crucial in deriving holographic entanglement entropy. It reflects **conformal anomaly** contributions on light cone interfaces. In discrete QCA networks, this corresponds to counting corrections for lattice points at light cone tips.

### 13.3.5 Summary

This section resolved variational problems on non-smooth geometry by introducing the Hayward corner term.

1. **Mathematically**: It eliminates $\delta$-function singularities at corners, restoring well-posedness of the variational principle.

2. **Physically**: It guarantees additivity of action (and entropy) under region splicing.

3. **Holographically**: It is a complete description of physical properties of causal diamond edges (Edge), ensuring that generalized entropy $S_{\text{gen}}$ is self-consistently defined under arbitrary geometric configurations.

At this point, we have completed all discussions in Chapter 13 on variational completeness. Combined with the field equation derivation in Chapter 12, we have established a mathematically rigorous and physically self-consistent thermodynamic framework for gravity.

In the upcoming **Part VIII: Spacetime Stability and Singularities**, we will explore the behavior of this framework under extreme conditions, particularly how energy conditions (QNEC) guarantee spacetime stability, and the thermodynamic nature of singularities inside black holes.

