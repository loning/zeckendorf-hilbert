# 5.4 Origin of Fermion Statistics: Riccati Square Root and $\mathbb{Z}_2$ Phase

After establishing the picture that "mass is topological knots," we face the most profound question of this chapter: **Why must these massive "knots" be fermions?**

In standard physics, the connection between spin and statistics (spin-statistics theorem) is derived through axioms in relativistic quantum field theory. It shows that particles with half-integer spin must follow Fermi-Dirac statistics (wave function changes sign upon exchange), while integer spin particles follow Bose-Einstein statistics (unchanged upon exchange). But in our discrete ontology, we do not presuppose continuous spacetime symmetry groups, nor spinor fields.

This section will prove a startling conclusion: **Fermion statistics is not an arbitrary rule, but a topological fingerprint that any self-referential structure (massive particle) capable of maintaining its existence in discrete networks necessarily carries.** This fingerprint originates from the inherent **square root structure** of Riccati equations describing feedback loops.

## 5.4.1 Input-Output Relations of Self-Referential Systems

A massive particle is essentially a "self-maintaining" information loop. We can abstract it as a black box that receives input information $\psi_{in}$ and produces output information $\psi_{out}$, while part of the output is fed back to the input to maintain its own state.

In QCA's transmission line model, the physical quantity describing this input-output relationship is **impedance** $Z$ (or reflection coefficient $r$).

$$Z = \frac{V}{I} \quad (\text{voltage/current})$$

In quantum mechanical correspondence, $Z$ corresponds to logarithmic derivative of wave function at boundary $Z \sim \psi' / \psi$.

A stable particle means its internal impedance structure $Z(x)$ must satisfy some self-consistent equation. For discrete iterative systems, impedance evolution follows **Riccati equation** (discrete form is Möbius transformation):

$$Z_{n+1} = \frac{A Z_n + B}{C Z_n + D}$$

where $A, B, C, D$ are determined by QCA's local evolution operator $\hat{U}$.

## 5.4.2 Fixed Points and Square Root Branches

A particle as a stable topological soliton means it is not only localized in space, but also a **fixed point** in time evolution. That is, after one period of internal evolution, its impedance structure should restore:

$$Z^* = \frac{A Z^* + B}{C Z^* + D}$$

Solving this equation, we get a quadratic equation:

$$C (Z^*)^2 + (D-A)Z^* - B = 0$$

Its solution is:

$$Z^* = \frac{(A-D) \pm \sqrt{(A-D)^2 + 4BC}}{2C}$$

Here appears a decisive mathematical feature: **Square Root**.

This means, **any self-consistent, non-trivial stable particle state has its physical parameters (impedance $Z$) defined on a double-sheeted Riemann surface.**

## 5.4.3 Rotation, Exchange, and $\mathbb{Z}_2$ Phase

Now, we consider particle's **exchange statistics**.

In $3+1$ dimensional spacetime, exchanging two identical particles $1$ and $2$ is topologically equivalent to rotating one particle around the other by $360^\circ$ (or rotating the particle itself by $360^\circ$ in center-of-mass frame).

In parameter space, this rotation operation corresponds to evolving along a closed path on the Riemann surface for one cycle.

Since $Z^*$ contains square root $\sqrt{\Delta}$ (where $\Delta$ is a complex function of evolution parameters), when parameters rotate $2\pi$ around origin, square root function changes sign:

$$\sqrt{e^{i2\pi}} = e^{i\pi} = -1$$

This is the origin of **$\mathbb{Z}_2$ topological phase**.

* **For Bosons (photons)**: They have no internal self-referential feedback loops ($v_{int}=0$), so they don't need to solve Riccati fixed points. Their states are directly defined on single-valued plane. Rotating $360^\circ$ returns to origin, phase unchanged ($+1$).

* **For Fermions (massive particles)**: They must maintain a self-referential dead knot ($v_{int}>0$). Mathematical solution of this knot lies on branch cut of square root. Rotating $360^\circ$ causes system to slide to another sheet of Riemann surface, wave function acquires $-1$ phase.

**Theorem 5.4 (Mass-Statistics Theorem)**:

In local unitary QCA networks, any stable excitation maintained by nonlinear self-referential feedback (i.e., massive particles) necessarily has double-valued wave functions, thus exhibiting fermion statistics under exchange operations.

## 5.4.4 Ontological Status of Spinors

This discovery completely changes our understanding of **spinors**.

In traditional geometry, spinors are defined as "geometric objects that change sign upon $360^\circ$ rotation," usually viewed as abstract mathematical constructs.

But in our theory, **spinors are "square roots of scalars."**

* Physical observables (such as energy, charge, impedance) are single-valued (scalars or vectors).

* Underlying probability amplitudes (wave functions) must be square roots of these observables to satisfy self-consistent equations.

Therefore, fermions are not strange, special particles. **Fermions are the normal state of matter existence.** Any information structure attempting to "stop" and maintain its identity in spacetime networks must anchor itself on topological structure through "square root" operations, thus inevitably becoming fermions.

## 5.4.5 Summary: The Trio of Matter

At this point, we have completed Part III "The Emergence of Matter." Starting from Axiom $\Omega$, we constructed the complete microscopic picture of matter:

1. **Photons**: Massless, non-self-referential, single-valued phase **translation modes**.

2. **Mass**: **Topological dead knots** of information flow, resisting external forces (inertia) through internal oscillation ($v_{int}$).

3. **Fermions**: **Self-referential logic** required to maintain such dead knots necessarily introduces square root structure, leading to $-1$ exchange phase.

This picture not only explains "what," but also "why." It unifies mass, spin, and statistical properties under a simple geometric-logical framework.

In the next Part IV, we will explore the most mysterious component of this cosmic machine—**observers**. We will see how, when these fermion knots form sufficiently complex networks, they begin to "see" themselves.

