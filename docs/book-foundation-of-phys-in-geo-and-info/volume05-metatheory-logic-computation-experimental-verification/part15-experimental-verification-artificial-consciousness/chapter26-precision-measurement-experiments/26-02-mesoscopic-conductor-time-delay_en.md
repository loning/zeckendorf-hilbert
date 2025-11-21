**26.2 Time Delay Measurement in Mesoscopic Conductors: Electron Interference and Quantum Capacitance**

In Section 26.1, we used macroscopic microwave chaotic cavities to verify validity of unified time identity $\kappa(E)=\rho(E)$ for boson (photon) fields. However, material foundation in QCA ontology is fermions (Chapter 17). Fermions obey Pauli exclusion principle, their "density of states" directly relates to particle number filling and charge accumulation.

This section will advance experimental verification to **Mesoscopic Electronics** field. We will prove that in quantum dots or mesoscopic interferometers, **Scattering Phase Shift** of electrons not only determines time delay, but also directly defines **Quantum Capacitance** of system. This experimental fact provides most direct electrical evidence for "time is matter": **longer residence time, greater system's ability to store charge (matter)**.

### 26.2.1 Quantum Dots as Physical Realization of QCA Nodes

Mesoscopic quantum dots (Quantum Dot, QD) are artificially manufactured "artificial atoms," connected to external leads (Source/Drain) through tunnel junctions.

In QCA discrete model, quantum dots perfectly correspond to **Scattering Nodes** in networks.

* **Input/Output**: Electron wave functions $\psi_{in/out}$ transmit through leads.

* **Internal States**: Discrete energy levels $\{E_n\}$ inside quantum dot correspond to internal Hilbert space of QCA.

* **Control Parameters**: Gate voltage $V_g$ can adjust internal potential, equivalent to scanning energy $E$.

Our goal is to verify that for fermion systems, Wigner-Smith time delay $\tau_W$ and local density of states $\rho(E)$ still satisfy strict linear relationship:

$$
\tau_W(E) = 2\pi \hbar \rho(E)
$$

### 26.2.2 Theoretical Bridge: Quantum Capacitance and RC Time Constant

In macroscopic circuits, capacitance $C = dQ/dV$ is purely geometric quantity. But at mesoscopic scale, when we add an electron to quantum dot, must pay two parts of energy: classical Coulomb repulsion energy $E_C$ and quantum level spacing $\Delta E$.

**Definition 26.2.1 (Electrochemical Capacitance)**

Total capacitance $C_{\mu}$ of system is defined as reciprocal of chemical potential change $d\mu$ required to inject charge $dN$:

$$
\frac{1}{C_{\mu}} = \frac{1}{e^2} \frac{d\mu}{dN} = \frac{1}{C_{geo}} + \frac{1}{C_q}
$$

where $C_{geo}$ is geometric capacitance, and **Quantum Capacitance** $C_q$ is directly defined by density of states:

$$
C_q(E) = e^2 \rho(E)
$$

**Corollary 26.2.2 (Time-Capacitance Identity)**

Combining unified time identity $\tau = h \rho$ (here $h=2\pi\hbar$), we obtain a surprising electrical relationship:

$$
\tau_W(E) = \frac{h}{e^2} C_q(E) = R_K C_q(E)
$$

where $R_K = h/e^2 \approx 25.8 \, \text{k}\Omega$ is **von Klitzing Constant**, i.e., resistance quantum.

**Physical Meaning**:

This formula shows that time delay $\tau_W$ of microscopic scattering is essentially an **RC time constant**, where "resistance" is universal vacuum impedance $R_K$, and "capacitance" is quantum capacitance $C_q$ characterizing material density of states.

This not only verifies Friedel sum rule ($\Delta N = \frac{1}{\pi} \delta$), but transforms abstract "time" into measurable "capacitance." **Objects have mass (can store charge/information) because they can delay time.**

### 26.2.3 Experimental Scheme: Aharonov-Bohm (AB) Interferometer

To directly measure scattering phase $\delta(E)$ (thereby obtaining $\tau_W \sim d\delta/dE$), we need a phase-sensitive experimental setup.

**Experimental Setup**:

1. **AB Ring**: Construct a mesoscopic-scale conducting ring, electrons can flow from source (S) to drain (D).

2. **Embedded Quantum Dot**: Embed a quantum dot (QCA node under test) in one arm of ring, other arm as reference path.

3. **Magnetic Flux Control**: Magnetic flux $\Phi$ through ring introduces controllable Aharonov-Bohm phase $\varphi_{AB} = 2\pi \Phi/\Phi_0$.

**Measurement Principle**:

Transmission amplitude $t_{QD} = |t| e^{i\delta}$ through quantum dot interferes with reference arm amplitude $t_{ref}$. Total conductance $G$ oscillates with magnetic flux $\Phi$:

$$
G(\Phi) \propto |t_{QD} + t_{ref} e^{i\varphi_{AB}}|^2 = A + B \cos(\varphi_{AB} + \delta)
$$

By measuring phase shift of interference fringes, we can directly read **transmission phase $\delta(V_g)$** of quantum dot.

**Experimental Procedure**:

1. Adjust gate voltage $V_g$, changing alignment of quantum dot energy levels with Fermi surface (scanning energy $E$).

2. At each $V_g$ point, scan magnetic flux $\Phi$, extract phase $\delta$.

3. Calculate phase derivative $\frac{d\delta}{dV_g} \propto \tau_W$.

4. Simultaneously, independently measure density of states $\rho(E)$ or quantum capacitance $C_q$ through width and spacing of Coulomb blockade peaks.

### 26.2.4 Experimental Evidence and Correction of Phase Lapse

Early AB interference experiments (such as Yacoby et al., 1995) indeed observed continuous evolution of phase with energy, but also discovered a phenomenon called "Phase Lapse": between two resonance peaks, phase sometimes undergoes $\pi$ jump.

This was once considered challenge to Friedel rule. But under QCA framework, this receives perfect explanation:

* **Multi-channel Effects**: Real quantum dots are not single-channel. According to $\mathsf{Q}$ matrix theory in Section 6.4, measured phase is phase $\theta_t$ of some component of $S$ matrix, while Friedel rule relates to total phase $\Phi = \det S$.

* **Universal Verification**: Subsequent more precise experiments (such as Schuster et al., 1997) by controlling channel number confirmed that in single-channel limit, phase evolution $\Delta \delta$ precisely equals $\pi$ when passing through a resonance peak.

This provides strong experimental support for unified time identity in fermion systems, and demonstrates that **time delay and quantum capacitance are two sides of the same coin**—both measure how much "room" system has to accommodate additional charge/information.

