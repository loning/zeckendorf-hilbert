**Chapter 27: Astronomical and Cosmological Observations**

In previous chapter, we used microwave cavities, mesoscopic circuits, and atomic clocks to verify unified time identity and entropy origin of gravity at laboratory scales. However, most prominent feature of QCA discrete ontology—Planck-scale spacetime lattice structure—is usually extremely suppressed under low-energy laboratory conditions, difficult to directly detect.

To find direct evidence of discrete spacetime, we must utilize universe as a huge microscope. Cosmological distances ($10^{26}$ meters) can accumulate tiny Planck-scale corrections ($10^{-35}$ meters) into observable macroscopic effects. This chapter will explore three key astronomical observation windows: gravitational wave dispersion, spectral structure of Fast Radio Bursts (FRBs), and holographic noise in Cosmic Microwave Background (CMB).

**27.1 Gravitational Wave Dispersion: High-Frequency Lorentz Violation Search in LIGO/Virgo Data**

In classical general relativity, gravitational waves (GW) are massless, propagate at speed of light $c$, and are non-dispersive (phase velocity independent of frequency). But in QCA discrete ontology, spacetime background is essentially a lattice network. Just as light disperses when propagating in crystals, gravitational waves propagating in discrete spacetime should exhibit frequency-dependent propagation speeds.

This section will establish **Modified Dispersion Relation (MDR)** on QCA lattice, and use LIGO/Virgo gravitational wave observation data (particularly binary neutron star merger event GW170817) to set strict experimental upper bounds on discrete structure of spacetime. We will prove that existing high-precision data force QCA models to possess specific **Accidental Lorentz Symmetry**, thereby excluding simple "square grid" spacetime models.

### 27.1.1 Wave Equation on Discrete Lattice and MDR

Consider continuous limit of QCA networks. In Section 4.4, we pointed out that although renormalization group flow tends to restore Lorentz invariance, near Planck energy scale, residual lattice effects cause Lorentz Invariance Violation (LIV).

For scalar gravitational wave mode $\phi$, its discrete equation of motion on lattice typically has form (one-dimensional example):

$$
\partial_t^2 \phi = \frac{c^2}{a^2} \sin^2(a \partial_x) \phi
$$

where $a \sim l_P$ is lattice spacing. In momentum space, this leads to nonlinear dispersion relation:

$$
\omega^2 = \frac{c^2}{a^2} \sin^2(ka)
$$

When wavelength is much larger than lattice spacing ($ka \ll 1$), Taylor expansion gives:

$$
\omega^2 \approx c^2 k^2 \left( 1 - \frac{1}{3} k^2 a^2 + \mathcal{O}(k^4 a^4) \right)
$$

This can be written in generic phenomenological form (natural units):

$$
E^2 = p^2 c^2 \left[ 1 \pm \xi_n \left( \frac{E}{E_{\text{QG}}} \right)^n \right]
$$

where $E_{\text{QG}}$ is quantum gravity energy scale (usually Planck energy $M_P$), $n$ is violation order (usually $n=1$ or $n=2$), $\xi_n$ is model-dependent coefficient.

**Physical Meaning**:

* **Phase Velocity** $v_p = E/p \neq c$.

* **Group Velocity** $v_g = \frac{\partial E}{\partial p} \approx c \left[ 1 \pm \frac{n+1}{2} \xi_n \left( \frac{E}{E_{\text{QG}}} \right)^n \right]$.

High-frequency gravitational waves will propagate slightly slower/faster than low-frequency waves (or speed of light). If $v_g < c$ (subluminal), high-energy waves lag; if $v_g > c$ (superluminal), high-energy waves lead.

### 27.1.2 Arrival Time Delay Formula

Consider a distant astrophysical source (distance $L$), simultaneously emitting signals of different frequencies (or gravitational waves and photons). Due to dispersion, their arrival times on Earth will differ.

**Theorem 27.1.1 (Dispersion Time Delay)**

For two wave packets with frequencies $f_1$ and $f_2$ respectively ($f_1 < f_2$), their arrival time difference $\Delta t$ is:

$$
\Delta t = L \left( \frac{1}{v_g(f_1)} - \frac{1}{v_g(f_2)} \right) \approx \pm \frac{n+1}{2} \xi_n \frac{L}{c} \left[ \left( \frac{hf_2}{E_{\text{QG}}} \right)^n - \left( \frac{hf_1}{E_{\text{QG}}} \right)^n \right]
$$

For cosmological distances, redshift $z$ corrections to energy and distance must also be considered, integral formula is:

$$
\Delta t = \pm \frac{n+1}{2} \frac{\xi_n E_0^n}{H_0 E_{\text{QG}}^n} \int_0^z \frac{(1+z')^n}{\sqrt{\Omega_m(1+z')^3 + \Omega_\Lambda}} \, dz'
$$

where $E_0$ is observed energy.

This formula is bridge connecting QCA microscopic parameters ($E_{\text{QG}}, \xi_n$) with macroscopic observations ($\Delta t, z$). Since $L$ is extremely large (Mpc scale), even if $E/E_{\text{QG}}$ is extremely small, $\Delta t$ may reach detectable millisecond or even second levels.

### 27.1.3 Strict Limits from GW170817 Event

In 2017, LIGO/Virgo detected binary neutron star merger gravitational wave signal (GW170817), Fermi satellite detected corresponding gamma-ray burst (GRB 170817A) 1.7 seconds later. Source distance is 40 Mpc.

1. **Speed of Light Invariance Test**: Arrival time difference between gravitational wave and photons $\Delta t \approx 1.7 \, \text{s}$. Considering astrophysical models themselves allow second-level emission delays, we can conservatively consider speed difference during propagation to be extremely small:

    $$
    \left| \frac{v_{gw} - c}{c} \right| \le \frac{1.7 \, \text{s}}{40 \, \text{Mpc}/c} \approx 10^{-15}
    $$

2. **Dispersion Test**: Within gravitational wave signal, frequency sweeps from 30 Hz to hundreds of Hz. Phase evolution of waveform shows no dispersion signs.

**Constraints on QCA Models**:

Using above data, for $n=1$ (linear violation) models, limits reach above Planck energy scale:

$$
E_{\text{QG}}^{(n=1)} > 10 \times M_{\text{Planck}}
$$

This means **simple linear Lorentz violation models are excluded**. Discreteness of QCA networks cannot manifest as first-order effect of $E/M_P$.

For $n=2$ (quadratic violation) models, limits are weaker (about $10^{-6} M_{\text{Planck}}$), but this still imposes strong constraints on lattice structure of QCA.

### 27.1.4 Accidental Symmetry and "Superfluid" Nature of QCA

GW170817 results negate naive "building block" spacetime view, but this does not mean negating discreteness. Instead, it points out that QCA must possess properties of **Quantum Superfluid**.

This suggests QCA networks at low energies exhibit **emergent Lorentz invariance**—discrete structure is hidden, only manifesting at extremely high energies or through subtle quantum interference effects. This provides important guidance for constructing realistic QCA models: they must be designed to automatically restore relativistic symmetry at macroscopic scales.

