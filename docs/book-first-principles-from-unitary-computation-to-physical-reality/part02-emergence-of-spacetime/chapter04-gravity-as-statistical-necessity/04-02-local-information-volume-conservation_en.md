# 4.2 Local Information Volume Conservation: Why Must Space Expand When Information Compresses Time?

In Section 4.1, we qualitatively established the concept that "geometry is entanglement." Spacetime curvature is no longer matter distorting a background stage, but matter interfering with entanglement network connectivity.

However, to move from qualitative picture to quantitative Einstein field equations, we need a stronger mathematical constraint. If it were merely "entanglement reduction causes distance increase," we would only get some scalar gravity theory (similar to relativistic generalization of Newtonian potential). Early attempts (such as Einstein's variable speed of light theory in 1911) predicted light deflection angles only half of general relativity's prediction.

This section will solve the "half-angle problem" and derive the correct optical metric form by introducing the key principle of **"local information volume conservation."** This principle is not just a mathematical patch, but an inevitable corollary of QCA unitarity at the statistical mechanics level.

## 4.2.1 Discrete Correspondence of Liouville Theorem

In classical statistical mechanics, Liouville's theorem states: Phase space volume of Hamiltonian systems is conserved during evolution (incompressible flow). This means if we compress momentum space, we must stretch coordinate space to keep $dp \cdot dq$ constant.

In QCA, the counterpart is **unitary evolution preserves Hilbert space dimension**.

Let a local volume element $V$ contain $N$ qubits. Its Hilbert space dimension is $D = 2^N$.

Unitary evolution operator $\hat{U}$ is full rank, mapping $D$-dimensional space to $D$-dimensional space. This means information is neither compressed (lost) nor diluted (created from nothing).

When we define continuous "physical coordinates" $(t, x)$ at macroscopic scales, we are coarse-graining underlying discrete nodes.

Let physical metric be $g_{\mu\nu}$. Local physical volume element (including time) is:

$$dV_{phys} = \sqrt{-g} \, d^4x$$

This physical volume element directly corresponds to "number of operations" or "degrees of freedom" of the underlying QCA.

**Axiom (Local Information Volume Conservation)**:

In any coordinate transformation or geometric deformation, the effective quantum degree of freedom density per unit coordinate volume must remain constant.

## 4.2.2 Antagonism Between Time Dilation and Space Expansion

Consider a region with high local information processing density $\rho_{\text{info}}$ (e.g., containing massive objects).

According to Light Path Conservation, accelerated internal computation means external clock slows. We describe this time dilation using **refractive index $n(x) > 1$**:

$$d\tau = \frac{1}{n(x)} dt$$

This means physical time interval $d\tau$ is compressed (relative to coordinate time $dt$). Or, the number of physical "ticks" contained per unit coordinate time $dt$ decreases.

If only time dilation occurred, total degrees of freedom in this spacetime region would decrease (because time dimension capacity shrinks). To satisfy volume conservation (Liouville constraint), spatial dimensions must undergo compensatory **expansion**.

Let spatial scaling factor be $a(x)$, i.e., $dl = a(x) dx$.

Four-dimensional volume element change factor is:

$$\sqrt{-g} \propto \frac{1}{n} \cdot a^3$$

(for $3+1$ dimensional spacetime).

To maintain phase space volume (or total information capacity) constant, do we need $\sqrt{-g} = 1$?

More precisely, we need to examine phase space $(x, k)$ volume. Wave vector $k$ is inversely proportional to wavelength $\lambda$.

If physical length is stretched by $a$, physical momentum cutoff (Brillouin zone boundary) shrinks by $1/a$.

For photons (or massless fields), density of states $\rho(\omega) \sim \omega^2$. Frequency redshifts $\omega \to \omega/n$.

To maintain photon number conservation (or information channel number conservation), spatial volume expansion must precisely compensate frequency cutoff contraction.

After rigorous statistical counting (see appendix for details), in isotropic media, conservation condition yields the following constraint:

$$\eta_t \cdot \eta_x = 1$$

where $\eta_t = 1/n$ is time flow rate factor, $\eta_x = a$ is spatial expansion factor.

Therefore, necessarily:

$$\eta_x = \frac{1}{\eta_t} = n$$

**Conclusion**: If gravity causes time to slow by factor $n$, it must simultaneously cause space to expand by factor $n$.

$$d\tau = \frac{1}{n} dt, \quad dl = n dx$$

## 4.2.3 Derivation of Optical Metric

Based on the above dual scaling, we can write the macroscopic effective metric.

On flat background $ds^2 = -c^2 dt^2 + dx^2$, introducing scaling:

$$ds^2 = -c^2 d\tau^2 + dl^2 = -c^2 (\frac{1}{n} dt)^2 + (n dx)^2$$

Rearranging:

$$ds^2 = -\frac{1}{n^2} c^2 dt^2 + n^2 (dx^2 + dy^2 + dz^2)$$

This is the famous **Optical Metric**, also called Gordon metric.

In weak field approximation, refractive index relates to Newtonian gravitational potential $\Phi$ ($n \approx 1 - 2\Phi/c^2$, note $\Phi < 0$):

$$g_{00} \approx -(1 + 2\Phi), \quad g_{ij} \approx (1 - 2\Phi)\delta_{ij}$$

This **completely matches** the weak field expansion of Schwarzschild metric in isotropic coordinates in general relativity.

## 4.2.4 Solving the Half-Angle Problem

Why is this correction so important?

If we only consider time dilation (scalar gravity), metric is $ds^2 = -(1+2\Phi)dt^2 + dx^2$.

When calculating light deflection, light travels straight in space, only affected by time potential. Deflection angle $\theta = \frac{2GM}{rc^2}$.

But in our optical metric, space is also "expanded" ($n^2 dx^2$). Light rays not only curve due to slow time, but also because space itself deforms like a lens.

According to Fermat's principle $\delta \int n dl = 0$, spatial refractive index contribution equals temporal contribution.

Total deflection angle $\theta = \theta_{time} + \theta_{space} = \frac{4GM}{rc^2}$.

This is exactly Einstein's final corrected result in 1915, also verified by Eddington's observation in 1919.

## 4.2.5 Summary

This section proves: **Spatial curvature of spacetime is the inevitable companion of time dilation.**

As long as we acknowledge:

1. Gravity originates from local differences in information processing rates (Light Path Conservation);

2. Underlying evolution follows unitarity (Information Volume Conservation);

Then, the metric structure of general relativity is the unique mathematical solution. Space must curve because if it doesn't, information squeezed by time would have nowhere to go, violating information conservation law.

**Gravity is the geometric projection of information conservation.**

