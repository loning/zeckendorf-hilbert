# Part VI: Topological Structure of Time

## Chapter 10: Breaking of Time Translation Symmetry

In the previous nine chapters, the time we discussed was mostly "continuous" effective descriptions (such as scattering delay $\tau$ or Hubble expansion $H$). However, the underlying ontology of QCA is discrete ($U^n$). A natural question is: **Will this underlying discrete rhythm (Tick) leave observable traces in macroscopic physics?**

This chapter will introduce the concept of **Discrete Time Crystal (DTC)**. We will prove that DTC is not just an exotic condensed matter phase but the **topological skeleton** of the time dimension in the QCA universe. It reveals how time translation symmetry (TTS) spontaneously breaks in discrete systems, thereby producing topologically protected $\mathbb{Z}_2$ periodic structures.

### 10.1 Definition of Discrete Time Crystal (DTC): Subharmonic Response of Floquet Systems

In continuous time systems, energy conservation corresponds to continuous time translation symmetry. However, if the system itself is driven by a periodic driving field (or discrete QCA update $U$), continuous symmetry downgrades to discrete symmetry $t \to t + T$ ($T$ is the driving period).

**Definition 10.1.1 (Floquet System)**

Consider a system with explicitly time-dependent Hamiltonian $H(t) = H(t+T)$. The system's evolution is described by a periodic **Floquet operator** $U_F$:

$$
U_F = \mathcal{T} \exp\left( -i \int_0^T H(t) \, \mathrm{d}t \right)
$$

This exactly corresponds to the single-step update operator $U$ in QCA (where $T$ is Planck time step).

#### 10.1.1 Time Translation Symmetry Breaking (TTSB)

In the thermodynamic limit, if the expectation value of some observable $\mathcal{O}$ of the system exhibits periodicity longer than driving period $T$ (usually $nT$), we say **discrete time translation symmetry spontaneously breaks**.

**Definition 10.1.2 (Discrete Time Crystal)**

A quantum many-body system is called a discrete time crystal if for some local order parameter $\mathcal{O}$:

1.  **Subharmonic Response**: $\langle \mathcal{O}(t) \rangle$ exhibits $kT$ periodicity ($k > 1$ is an integer), i.e., $\langle \mathcal{O}(t+T) \rangle \neq \langle \mathcal{O}(t) \rangle$, but $\langle \mathcal{O}(t+kT) \rangle = \langle \mathcal{O}(t) \rangle$.

2.  **Long-Range Spatiotemporal Order**: This oscillation is robust in the infinite volume limit $V \to \infty$ and infinite time limit $t \to \infty$, not disappearing with small perturbations.

The most common is $\mathbb{Z}_2$ time crystal with period $2T$. This means the system does not return to its original state after each update step $U$ but undergoes a **flip**, requiring two steps $U^2$ to restore. This is the temporal domain counterpart of fermion statistics (rotation by $4\pi$ restores).

#### 10.1.2 Effective Hamiltonian and $\pi$-Modes

To understand the microscopic mechanism of DTC, we examine spectral properties of $U_F$.

$$
U_F |n\rangle = e^{-i \varepsilon_n T} |n\rangle
$$

where $\varepsilon_n$ is called **quasi-energy**, defined on circle $[-\pi/T, \pi/T)$.

**Theorem 10.1.3 (Spectral Features of DTC)**

Discrete time crystal phase corresponds to **pairing structure** in quasi-energy spectrum. Especially for period-doubling DTC, system eigenstates appear in pairs $(|\psi_+\rangle, |\psi_-\rangle)$, with quasi-energy difference strictly locked at $\pi/T$ (half the frequency):

$$
\varepsilon_+ - \varepsilon_- = \frac{\pi}{T} \quad (\text{mod } \frac{2\pi}{T})
$$

This means evolution operator in the subspace spanned by these two states behaves as:

$$
U_F \approx e^{-i \frac{\pi}{2} \sigma_x} = -i \sigma_x
$$

This is a perfect spin-flip operation. Eigenvalues $e^{-i\varepsilon T}$ are $e^{\mp i\pi/2} = \mp i$ respectively. Modes at quasi-energy region boundaries are called **$\pi$-modes**.

#### 10.1.3 Rigidity and Topological Protection

DTC is called a "crystal" because it has rigidity. If driving parameters (such as pulse strength in Hamiltonian) deviate slightly, general Rabi oscillation frequencies will change continuously. But in DTC phase, despite parameter changes, response frequency is **locked** at exact $\omega/2$ unchanged.

**Physical Mechanism**:

This locking originates from **Many-Body Localization (MBL)** or **Prethermalization** mechanisms.

* In MBL-DTC, system eigenstates maintain long-range entanglement structure over large scales, making $\pi$-modes topologically protected edge states (on Floquet operator's energy spectrum).

* This protection is similar to topological insulators: unless phase transition occurs (Gap Closing), quasi-energy difference cannot continuously change from $\pi$ to other values.

#### 10.1.4 Significance of DTC in QCA Universe

In the framework of this book, DTC is not just a condensed matter model; it is the manifestation of QCA universe's **"intrinsic frequency."**

1.  **Universe's Metronome**: If QCA's microscopic update rule $U$ is in DTC phase, then macroscopic observables of the universe will not change at every Planck time step but "macroscopically tick" with period $2T$ (or $kT$). This defines the **minimum resolution** of physical time.

2.  **Origin of Fermions**: The appearance of $\pi$-modes ($U^2=1$ but $U \neq 1$) is mathematically isomorphic to the $\mathbb{Z}_2$ property of spinors. The Dirac equation we derived in Section 4.2, its microscopic coin operator $C(\theta)$ at $\theta \to \pi/2$ is precisely a $\pi$-mode flip operation. This suggests that **fermions might be local time crystal defects on spacetime background**.

**Summary**

This section defines discrete time crystals and identifies them as rigid pairing phenomena in quasi-energy spectrum of Floquet systems. This establishes the physical foundation for topological structure of time dimension ($\mathbb{Z}_2$ periodicity).

In the next section, we will delve into its topological essence, introducing the concept of **$\mathbb{Z}_2$ holonomy**, proving that DTC's stability originates from non-trivial topological loops in parameter space.

