**8.4 Relative Scattering Determinant: Effective Density of States Calculation in Curved Spacetime and Metric Reconstruction**

In Section 8.3, we proved that gravitational redshift can be explained as the rescaling effect of local density of states (LDOS) in potential fields. This only reveals the relationship between one component of spacetime metric $g_{\mu\nu}$ ($g_{00}$) and microscopic statistical quantities. This section generalizes this logic to the entire geometric structure of Riemannian manifolds.

We will introduce the concept of **relative scattering determinant** and, combined with **Weyl's asymptotic law** in spectral geometry, prove a profound duality: macroscopic geometric information of spacetime (volume, curvature scalar, etc.) is completely encoded in the high-energy asymptotic behavior of microscopic scattering matrices. This means that, in principle, we can **reconstruct** the spacetime metric in the bulk by measuring scattering data on the boundary. This conclusion constitutes a rigorous statement of the holographic principle in scattering theory.

### 8.4.1 Formulation of Scattering Problem in Curved Space

Consider an asymptotically flat Riemannian manifold $(M, g)$, whose metric tends to Minkowski metric $\eta_{\mu\nu}$ at infinity. We treat gravity as background geometry, and particles are described by the Laplace-Beltrami operator on this background:

$$
H = -\Delta_g = -\frac{1}{\sqrt{g}} \partial_\mu (\sqrt{g} g^{\mu\nu} \partial_\nu)
$$

Relative to the free Hamiltonian $H_0 = -\Delta_\eta$ in flat space, the curved metric $g_{\mu\nu}$ acts as a generalized "scattering potential."

**Definition 8.4.1 (Relative Scattering Matrix)**

Since $H$ and $H_0$ are asymptotically identical at infinity, we can define wave operators $\Omega_\pm(H, H_0)$ and scattering operator $\hat{S} = \Omega_+^\dagger \Omega_-$. Its representation $S(E)$ on the energy shell is called the **relative scattering matrix**. It describes the additional phase shifts and mixing that curved spacetime produces on incident waves relative to flat spacetime.

### 8.4.2 Relative Density of States and Heat Kernel Expansion

According to the Birman-Kreĭn theory established in Chapter 7, the determinant of the relative scattering matrix is related to the spectral shift function $\xi(E)$:

$$
\det S(E) = e^{-2\pi i \xi(E)}
$$

where $\xi(E) \approx N_0(E) - N_g(E)$ is the difference in cumulative density of states between flat space and curved space (sign convention depends on definition).

To extract geometric information, we need to examine the behavior of density of states $\rho(E)$ in the high-energy limit ($E \to \infty$). This is usually accomplished through the asymptotic expansion of the **heat kernel** $K(t) = \text{Tr}(e^{-tH})$.

**Theorem 8.4.2 (Heat Kernel Expansion in Curved Space)**

For a $d$-dimensional Riemannian manifold, the heat kernel trace has the following asymptotic expansion at short times ($t \to 0^+$, corresponding to high energy):

$$
\text{Tr}(e^{-tH}) \sim \frac{1}{(4\pi t)^{d/2}} \left( a_0 + a_1 t + a_2 t^2 + \dots \right)
$$

The coefficients $a_k$ are the famous **Seeley-DeWitt coefficients**, which are integrals of geometric invariants of the manifold:

1.  $a_0 = \int_M \sqrt{g} \, \mathrm{d}^dx = \text{Vol}(M)$ (total volume).

2.  $a_1 = \frac{1}{6} \int_M R \, \sqrt{g} \, \mathrm{d}^dx$ (total scalar curvature).

3.  $a_2$ involves quadratic contractions of the Riemann curvature tensor (such as $R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma}$).

### 8.4.3 Weyl's Asymptotic Law for Scattering Phase

Using inverse Laplace transform, we can convert the heat kernel expansion into the asymptotic behavior of density of states $\rho(E)$ or spectral shift function $\xi(E)$. This is **Weyl's Law**.

**Theorem 8.4.3 (Geometric Encoding of Scattering Phase)**

The total scattering phase $\Phi(E) = \text{Im} \ln \det S(E)$ satisfies in the high-energy limit:

$$
\Phi(E) \sim c_d \left( \text{Vol}(M) - \text{Vol}(\mathbb{R}^d) \right) E^{d/2} + c_{d-1} \left( \int R \right) E^{d/2-1} + \dots
$$

where $c_d$ is a dimension-dependent constant.

(Note: Since $\text{Vol}(\mathbb{R}^d)$ is infinite, the volume difference here usually refers to the **renormalized volume** relative to flat background $\delta V = \int (\sqrt{g} - 1) \mathrm{d}^dx$).

**Physical Corollary**:

This formula shows that by measuring the growth rate of scattering phase $\Phi(E)$ with energy $E$, we can directly "read out" geometric properties of spacetime:

1.  **Leading Coefficient** $\propto E^{d/2}$: Gives the **effective volume** of spacetime. If gravitational fields cause spatial contraction (such as near black holes), the growth rate of scattering phase will deviate from flat space predictions.

2.  **Sub-leading Coefficient** $\propto E^{d/2-1}$: Gives the **total average curvature** of spacetime.

This answers Mark Kac's famous question: "Can you hear the shape of a drum?" In the QCA universe, the answer is yes: **we can "hear" the volume and curvature of the universe by emitting waves into it and analyzing their scattered echoes (S matrix)**.

### 8.4.4 Metric Reconstruction Theorem

Since scattering data encodes curvature integrals, is it sufficient to reconstruct the metric $g_{\mu\nu}(x)$ at each point? This belongs to the **inverse scattering problem**.

**Theorem 8.4.4 (Existence of Metric Reconstruction)**

Under specific conditions (such as the metric being analytic and decaying sufficiently fast at infinity), the scattering matrix $S(E)$ over the full energy range (including partial wave phase shifts for all angular momentum channels) uniquely determines the metric function of spherically symmetric spacetime.

For general non-symmetric spacetime, if we have scattering amplitudes $A(\mathbf{k}_{in}, \mathbf{k}_{out}, E)$ for all incident directions and energies, then we can invert to obtain the refractive index distribution $n(\mathbf{x}) = \sqrt{g_{00}(\mathbf{x})}$ (under optical metric approximation) through the **eikonal equation** in the high-energy limit.

**Constructive Steps**:

1.  **Measurement**: Obtain scattering phase $\Phi(E)$ and its dependence on angular momentum $l$, $\delta_l(E)$.

2.  **WKB Inversion**: Using semiclassical approximation (WKB), there exists an Abel transform relationship between phase shift $\delta_l(E)$ and effective potential $V_{eff}(r) = g_{00}(r) + l(l+1)/r^2$. Through inverse Abel transform, we can integrate $\delta_l$ to obtain $V_{eff}$.

3.  **Geometric Solution**: Separate the centrifugal term from $V_{eff}$, and the remaining part is a combination of metric components $g_{00}(r)$ and $g_{rr}(r)$.

### 8.4.5 Geometric Form of Unified Time Identity

Combining the unified time identity $\kappa(E) = \frac{1}{\pi} \Phi'(E) = \rho_{rel}(E)$ from Section 8.1 of this chapter, we can rewrite Weyl's law as **time-geometry duality**:

$$
\kappa(E) \approx \frac{d}{2} c_d \, \delta \text{Vol} \cdot E^{d/2-1}
$$

* Left side $\kappa(E)$: **Microscopic time flow rate** (time delay density).

* Right side $\delta \text{Vol}$: **Macroscopic spacetime volume** (geometric quantity).

This reveals the microscopic origin of volume element $\sqrt{-g} d^4x$ in general relativity: **macroscopic geometric volume is merely the accumulation of microscopic time delay (information processing capacity) on the energy spectrum**. Space appears "large" because particles need to experience enormous density of states counting during propagation, thus consuming vast amounts of "microscopic time."

**Conclusion**

This section completes the logical closure from microscopic scattering to macroscopic geometry. We not only explained gravitational redshift (Section 8.3) but also proved that the curved structure of spacetime (curvature and volume) can be completely reconstructed from spectral properties of the S matrix. This provides solid mathematical support for Volume III to completely attribute gravity to **entropic force**: because geometry is information (density of states), the dynamics of geometry (gravity) must follow statistical laws of information (maximum entropy principle).

At this point, **Volume II: The Emergence of Time** is complete. We have reduced time from a background parameter to a statistical property of scattering processes. In the upcoming **Volume III**, we will use this newly established view of time to derive Einstein's field equations themselves.

**(End of Volume II)**

