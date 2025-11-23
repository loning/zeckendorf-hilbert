# 5.3 Mass as Impedance: Information Refresh Rate Required to Maintain Internal Oscillation ($v_{int}$)

After establishing the topological picture that "matter is self-referential loops of information," we must answer a quantitative dynamics question: **How does this loop resist external forces, manifesting as macroscopic inertia?**

This section will derive Newton's second law $F=ma$ in relativistic form from first principles by introducing the concept of **"Topological Impedance"**, revealing the microscopic mechanism of inertial mass: mass is not the "weight" of matter, but **response latency** of information flow to external perturbations when maintaining its internal topological structure.

## 5.3.1 Internal Refresh Rate and Cost of Existence

According to Light Path Conservation Theorem (Section 3.2), any particle's total information update amount (light path) within Planck time $t_P$ is constant $c t_P$. For massive particles, this resource is allocated as:

1. **Displacement Update**: Changing lattice position $|x\rangle \to |x+\Delta x\rangle$.

2. **State Update**: Changing internal phase $| \psi_{int} \rangle \to e^{-i\omega_{int} t} | \psi_{int} \rangle$.

Rest mass $m_0$ is defined as maximum internal frequency at rest $\omega_0 = m_0 c^2 / \hbar$. This means, to maintain particle's "existence" (i.e., keep its topological knot from disintegrating), QCA network must provide $\omega_0$ internal refresh operations per second for this particle.

**Definition 5.3 (Cost of Existence)**:

A particle's **Cost of Existence** $C_{exist}$ equals the logic gate operation rate required for its internal state updates.

$$C_{exist} \equiv \omega_{int} = \frac{m_0 c^2}{\hbar} \sqrt{1 - v^2/c^2}$$

Note that as particle speed $v$ increases, due to time dilation, its **observed** internal refresh rate $\omega_{int}$ actually decreases. This seems to suggest high-speed particles are "cheaper"?

Quite the opposite. Precisely because internal refresh rate decreases, system's **response capability** worsens.

## 5.3.2 Impedance Model: Microscopic Derivation of Inertia

Imagine a running computer program (particle).

* **At Rest**: CPU resources are abundant, program refreshes 100 times per second. If you input an instruction (force $F$), program can quickly respond and change state (acceleration $a$).

* **At High Speed**: CPU resources are 99% occupied by background transport tasks (displacement). Program can only refresh once per second.

* **Consequence**: If you input the same instruction now, program needs extremely long time to process and respond. To outsiders, this manifests as "program becomes extremely sluggish" or "enormous inertia."

We define this sluggishness as **topological impedance**.

**Theorem 5.3 (Inertial Divergence Theorem)**:

Let particle's momentum $p$ change rate over time (force $F$) be inversely proportional to internal update rate $\omega_{int}$.

That is: System's response sensitivity (Susceptibility) to external stimuli $\chi \propto \omega_{int}$.

Then inertial mass $m_{inert} \equiv F/a$ diverges as speed $v$ increases.

**Proof**:

According to energy-frequency relationship derived from Light Path Conservation (Chapter 3.3 appendix), relationship between total energy $E$ and internal frequency $\omega_{int}$ is:

$$E = \frac{m_0 c^2}{\sqrt{1 - v^2/c^2}} = m_0 c^2 \cdot \frac{\omega_0}{\omega_{int}}$$

(Note: $\omega_{int} = \omega_0 / \gamma$).

Force $F$ is defined as energy gradient with distance, or momentum derivative with time:

$$F = \frac{dp}{dt} = \frac{d}{dt} (\gamma m_0 v)$$

Expanding derivative:

$$F = m_0 \gamma^3 a$$

(Here considering longitudinal acceleration).

Substituting $\gamma$ using $\gamma = \omega_0 / \omega_{int}$:

$$F = m_0 \left( \frac{\omega_0}{\omega_{int}} \right)^3 a$$

Defining effective inertial mass $m_{eff} = F/a$:

$$m_{eff} = m_0 \left( \frac{\omega_0}{\omega_{int}} \right)^3$$

**Conclusion**:

When $v \to c$, internal refresh rate $\omega_{int} \to 0$.

At this point, $m_{eff} \to \infty$.

**Physical Picture 5.3**:

Inertia is not an inherent property of matter, but a measure of **system's "crash degree."**

When a particle runs too fast, its internal clock almost stops. To change its motion state in the time it "blinks" (completes one internal update), the external world needs to apply infinite force integral.

This is why light speed cannot be exceeded—not because there's a wall ahead, but because **the faster your legs (displacement) run, the slower your brain (inertial processing) turns**, until you completely lose ability to change the status quo.

## 5.3.3 Mass as "Vorticity" of Information Flow

At this point, we have completely demystified mass:

1. **Rest Mass $m_0$**: Is **vorticity** of information flow in QCA networks. It is the frequency at which topological knot structure forces information to rotate in place.

2. **Inertial Mass $m_{inert}$**: Is **stiffness of vortex resisting deformation**. When vortex is stretched into a helix (high-speed motion), its pitch is elongated (frequency decreases), causing stiffness to rise sharply.

In this picture, the famous Higgs mechanism is merely **effective field theory description** of this topological process.

* Higgs field $\phi$ corresponds to QCA's vacuum entanglement background.

* Yukawa coupling $y_f$ corresponds to winding strength of topological knots.

* So-called "particles acquiring mass" is originally straight-propagating information flow being tripped by background entanglement, forming knots.

## 5.3.4 Summary

We no longer need to assume "matter" exists. We only need to assume "obstructed information flow."

* **Photons** are laminar flow.

* **Electrons** are vortices in turbulence.

* **Black holes** are blocked singularities.

In the next section, we will delve into the fine structure of this "vortex"—why does it not only have mass, but must also have spin? Why is it a fermion? This will lead to the most profound mathematical chapter of this book.

