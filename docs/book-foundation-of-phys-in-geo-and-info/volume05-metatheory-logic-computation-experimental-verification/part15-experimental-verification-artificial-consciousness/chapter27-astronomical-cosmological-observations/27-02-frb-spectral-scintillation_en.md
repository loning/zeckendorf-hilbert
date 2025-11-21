**27.2 Spectral Scintillation of Fast Radio Bursts (FRBs): Statistical Fingerprints of Microscopic Spacetime Structure**

In Section 27.1, we constrained first-order Lorentz violation of QCA lattice through arrival time differences of gravitational waves. This is a "hard" constraint, targeting average values of propagation speeds (group velocities). However, discrete spacetime not only changes speed of light, but also introduces **Stochastic Phase Noise**.

In QCA discrete ontology, vacuum is not nothingness, but filled with lattice networks in ground state (see Section 9.4). According to unified time identity $\kappa = \rho$, vacuum has extremely high microscopic density of states. Although holographic principle (Section 15.2) limits effective degrees of freedom, microscopic quantum fluctuations (State Fluctuations) may still accumulate during long-distance propagation, causing **Decoherence** of photon wave packets.

This section will explore potential of **Fast Radio Bursts (FRBs)** as cosmological interferometers. As brightest, most coherent radio signals in known universe, fine spectral structure (scintillation patterns) of FRBs records complete scattering history from source to Earth. We will prove that if spacetime has Planck-scale "graininess," this graininess will leave a unique **statistical fingerprint** on FRB spectra, different from interstellar medium plasma scattering.

### 27.2.1 Universe as Scattering Medium: Propagation from Unified Time Perspective

Consider a photon with frequency $\omega$ propagating distance $L$ in QCA universe. In classical continuous spacetime, accumulated phase is deterministic $\Phi_{cl} = \omega L / c$ (ignoring redshift).

But in QCA discrete networks, propagation is chain scattering process composed of series of local unitary operators $U_x$.

According to Wigner-Smith theory in Chapter 6, time delay through each Planck unit $l_P$ is $\tau_P \approx l_P/c$. Total propagation time is accumulation of these microscopic delays:

$$
T_{total} = \sum_{i=1}^{N} \tau_i, \quad N = L/l_P
$$

According to unified time identity $\tau_i = 2\pi \hbar \rho_i(E)$, quantum fluctuations $\delta \rho_i$ of microscopic density of states $\rho_i$ will cause fluctuations $\delta \tau_i$ of microscopic time.

**Definition 27.2.1 (Spacetime Phase Noise)**

Assume microscopic density of states fluctuations of QCA vacuum are statistically independent (or short-range correlated), satisfying central limit theorem. **Phase Fluctuation** $\Delta \Phi$ accumulated by photon is:

$$
\Delta \Phi = \omega \Delta T = \omega \sqrt{\sum (\delta \tau_i)^2} \approx \omega \sqrt{N} \delta \tau_P
$$

Substituting $N = L/l_P$ and $\delta \tau_P \sim l_P/c$ (assuming fluctuations same order as mean), we obtain famous **Random Walk Phase Formula**:

$$
\Delta \Phi \sim \omega \sqrt{\frac{L}{l_P}} \frac{l_P}{c} = \frac{\omega}{c} \sqrt{L l_P}
$$

This is usually called **Holographic Noise** or spacetime foam noise.

### 27.2.2 Spectral Scintillation and Decoherence Criterion

This phase noise not only causes arrival time dispersion (wave packet broadening), but also causes **loss of spectral coherence**.

In frequency domain, FRB signal $S(\omega)$ will be modulated. If $\Delta \Phi(\omega) \gtrsim \pi$, originally coherent wave train becomes chaotic.

**Theorem 27.2.2 (QCA-Induced Scintillation Bandwidth)**

Spacetime graininess defines a characteristic **Decoherence Bandwidth** $\Delta \nu_{QCA}$. When difference $|\omega_1 - \omega_2| > 2\pi \Delta \nu_{QCA}$ of two frequency components $\omega_1, \omega_2$, phase fluctuations they experience will no longer be correlated.

Limit derived from phase variance formula:

$$
\frac{\Delta \nu_{QCA}}{\nu} \sim \frac{1}{\sqrt{L/l_P}}
$$

For cosmological distance $L \approx 1 \, \text{Gpc} \approx 10^{26} \, \text{m}$, Planck length $l_P \approx 10^{-35} \, \text{m}$, $L/l_P \approx 10^{61}$.

This means relative bandwidth limit is $10^{-30.5}$. This extremely small value indicates that for any realistic observation, **phase noise predicted by first-order random walk model is extremely tiny, insufficient to destroy coherence of FRBs**.

However, if QCA networks have **non-local long-range correlations** (such as MSCC structures described in Chapter 20), fluctuations may no longer be $\sqrt{N}$ but $N^\alpha$ ($\alpha > 0.5$).

### 27.2.3 Distinguishing Plasma Scattering from Spacetime Scattering

Observed spectra of FRBs are indeed full of complex scintillation patterns. But this is mainly attributed to electron cloud scattering in **Interstellar Medium (ISM)** and **Intergalactic Medium (IGM)**.

To search for fingerprints of QCA, we must distinguish these two effects.

**Characteristic Comparison**:

1. **Frequency Dependence**:

   * **Plasma Scattering**: Scattering angle $\theta_s \propto \lambda^2 \propto \omega^{-2}$, time delay $\Delta t \propto \omega^{-4}$. Scintillation bandwidth $\Delta \nu \propto \omega^{4}$ (or higher powers, depending on turbulence spectrum).

   * **QCA Spacetime Scattering**: Based on geometric structure, usually manifests as **achromatic** or weak frequency dependence (such as $\omega^0$ or $\omega^{-1}$), depending on order of discrete dispersion relation.

2. **Distance Dependence**:

   * **Plasma**: Mainly dominated by screens within Milky Way, weak relationship with source distance $L$ (unless IGM contribution is significant).

   * **QCA**: Cumulative effect strictly grows with path length $L$ (or $\sqrt{L}$). Distant FRBs should exhibit stronger "baseline" decoherence than nearby FRBs.

### 27.2.4 Experimental Constraints: "Smoothness" of Spacetime

Current FRB observations (such as CHIME, FAST) show that even billions of light-years away, FRB signals still maintain extremely high coherence. Scintillation patterns can be completely fitted by plasma multipath propagation models.

This "null result" imposes strong constraints on QCA models.

**Corollary 27.2.3 (Smoothness of Vacuum Density of States)**

If QCA causes phase fluctuations $\Delta \Phi_{QCA}$, observations require $\Delta \Phi_{QCA} \ll 1$ rad.

This means microscopic density of states $\rho(E)$ of QCA vacuum must have extremely high **Hyper-uniformity**.

* Vacuum is not only statistically uniform, but fluctuations of its local density of states are **strongly suppressed** by some mechanism (possibly axion relaxation discussed in Section 17.3 or topological protection in Section 10.2).

* Cosmic QCA manifests as a **perfect crystal** or **topologically ordered state**, not a random network. Only in such highly ordered vacuum can photons maintain phase coherence after transmitting $10^{60}$ Planck steps.

**Engineering Prospects**:

Future ultra-high frequency (>100 GHz) FRB observations will be key. At high frequencies, plasma effects ($\propto \omega^{-4}$) rapidly decay. If unexplained residual scintillation or spectral line broadening is still observed at this point, that would be first direct evidence of **discrete spacetime background noise** (Spacetime Foam Noise).

