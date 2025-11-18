# Section 07: Gravitational Wave Dispersion Constraint—Propagation Traces of Discrete Spacetime

## 7.1 Introduction: "Fingerprint Identification" in Gravitational Waves

### 7.1.1 A Race Across the Universe

On August 17, 2017, humanity detected gravitational waves (GW170817) and electromagnetic waves (GRB170817A) simultaneously for the first time in history—signals from a neutron star merger, traveling about 130 million light-years, arriving on Earth almost simultaneously:

- **Gravitational Wave Arrival Time**: UTC 12:41:04.4
- **Gamma Ray Arrival Time**: UTC 12:41:06.5
- **Time Difference**: About **1.7 seconds**

This 1.7-second difference comes from delay in source region physics, not propagation speed difference. Through comparative analysis, physicists concluded:

$$
\left| \frac{v_{\text{gw}}}{c} - 1 \right| < 10^{-15}
$$

Relative deviation of gravitational wave propagation speed from speed of light is less than **one part in a quadrillion**!

```mermaid
graph LR
    Merger["Neutron Star Merger<br/>130 Million Light-Years Away"]

    Merger --> GW["Gravitational Wave GW170817<br/>LIGO/Virgo"]
    Merger --> EM["Gamma Ray GRB<br/>Fermi Satellite"]

    GW --> Time1["Arrival Time<br/>12:41:04.4"]
    EM --> Time2["Arrival Time<br/>12:41:06.5"]

    Time1 --> Delta["Time Difference Δt ~ 1.7s"]
    Time2 --> Delta

    Delta --> Source["Source Delay<br/>Physical Process"]
    Delta --> Propagation["Propagation Speed Difference<br/>|v_gw/c - 1|"]

    Propagation --> Constraint["Constraint<br/>< 10^(-15)"]

    style Merger fill:#2196f3,color:#fff
    style Constraint fill:#f44336,color:#fff
```

**Analogy**: Imagine two marathon runners (gravitational wave and light) starting from Moon and running to Earth. If their speed difference exceeds one part in a quadrillion, over 130 million light-years distance, would produce **thousands of years** arrival time difference. Actual difference only 1.7 seconds, meaning their speeds almost identical—this is **extremely stringent constraint** on any "discrete spacetime" or "modified gravity" theory.

### 7.1.2 Why Dispersion Is the "Imprint" of Discrete Spacetime

If spacetime is **discrete** microscopically (like quantum cellular automaton QCA universe), just as crystals have lattice constant $\ell_{\text{cell}}$, then long waves (gravitational waves, light waves) propagating through it will produce **dispersion effects** due to "seeing" this discrete structure:

$$
\omega^2(k) = c^2 k^2 \left[ 1 + \beta_2 (k\ell_{\text{cell}})^2 + \beta_4 (k\ell_{\text{cell}})^4 + \cdots \right]
$$

where:
- $\omega(k)$ is frequency-wavenumber relation
- $\beta_2, \beta_4, \ldots$ are dispersion coefficients
- $\ell_{\text{cell}}$ is "lattice spacing" of discrete spacetime

**Key Question**: If $\ell_{\text{cell}} \sim \ell_{\text{Planck}} \sim 10^{-35}\,\text{m}$ (Planck length), and gravitational wave frequency $f \sim 100\,\text{Hz}$ corresponds to wavelength $\lambda \sim 3000\,\text{km}$, why didn't dispersion effects manifest in GW170817?

```mermaid
graph TB
    Discrete["Discrete Spacetime<br/>ℓ_cell ~ 10^(-35) m"]

    Discrete --> Dispersion["Dispersion Relation<br/>ω² = c²k²[1 + β₂(kℓ)²]"]

    Dispersion --> GroupV["Group Velocity Deviation<br/>v_g/c - 1 ~ β₂(kℓ)²"]

    GroupV --> Observable["Observable Effect<br/>Propagation Time Difference"]

    Observable --> GW170817["GW170817 Constraint<br/>|v_g/c-1| < 10^(-15)"]

    GW170817 --> Bound["Upper Bound on β₂ and ℓ<br/>|β₂|ℓ² < 10^(-15) c² k^(-2)"]

    Bound --> Tension["Tension<br/>With Black Hole Entropy Lower Bound"]

    style Discrete fill:#e1f5ff
    style GW170817 fill:#f44336,color:#fff
    style Tension fill:#fff4e6
```

**Core Contradiction**: Black hole entropy constraint requires $\ell_{\text{cell}} \geq \ell_{\text{Planck}}$ (lattice spacing cannot be too small, otherwise insufficient horizon states), while gravitational wave dispersion constraint requires $\ell_{\text{cell}}$ cannot be too large (otherwise dispersion effects would be observed). These two constraints **pinch** discrete spacetime models, forming sixth lock in unified framework.

---

## 7.2 Physical Background: Theoretical Expectations of Gravitational Wave Dispersion

### 7.2.1 Dispersionless Propagation in Continuous Spacetime

In general relativity, gravitational waves are small perturbations $h_{\mu\nu}$ of spacetime metric, satisfying linearized Einstein equations:

$$
\Box h_{\mu\nu} = -16\pi G T_{\mu\nu}
$$

In vacuum ($T_{\mu\nu}=0$), get standard wave equation, dispersion relation:

$$
\omega^2 = c^2 k^2 \quad \text{(no dispersion)}
$$

This means all frequencies of gravitational waves propagate at **same speed** $c$, group velocity equals phase velocity:

$$
v_g = \frac{d\omega}{dk} = c, \quad v_p = \frac{\omega}{k} = c
$$

```mermaid
graph LR
    GR["General Relativity<br/>Continuous Spacetime"]

    GR --> Wave["Gravitational Wave Equation<br/>□h = 0"]

    Wave --> Dispersion["Dispersion Relation<br/>ω² = c²k²"]

    Dispersion --> NoDispersion["No Dispersion<br/>v_g = v_p = c"]

    NoDispersion --> AllFreq["All Frequencies<br/>Same Speed Propagation"]

    style GR fill:#e1f5ff
    style NoDispersion fill:#4caf50,color:#fff
```

**Analogy**: Continuous spacetime is like perfectly calm lake surface, ripples of different wavelengths (gravitational waves) all propagate at same speed, no distinction between "fast waves" and "slow waves".

### 7.2.2 Dispersion Effects in Discrete Spacetime

If spacetime is discrete at Planck scale, can analogize to **lattice phonons** in solid state physics:

In crystal with lattice constant $a$, dispersion relation of long-wavelength phonons is no longer linear:

$$
\omega(k) \approx c_s k \left[ 1 - \frac{1}{6}(ka)^2 + \cdots \right]
$$

This is because when wavelength approaches lattice constant, wave "feels" discrete structure.

**Analogy to Gravitational-QCA**:

If universe is discrete quantum cellular automaton, lattice spacing $\ell_{\text{cell}}$, then gravitational wave dispersion relation naturally has similar form:

$$
\omega^2 = c^2 k^2 \left[ 1 + \sum_{n=1}^\infty \beta_{2n} (k\ell_{\text{cell}})^{2n} \right]
$$

**Why Only Even-Order Terms?** Null-Modular symmetry and causality of unified framework require dispersion relation satisfy:

$$
\omega(-k) = \omega(k), \quad v_g(k) = v_g(-k)
$$

This excludes odd-order terms $(k\ell)^{2n+1}$, because they would cause **causality violation** or **time-reversal asymmetry**.

```mermaid
graph TB
    QCA["Quantum Cellular Automaton<br/>Lattice Spacing ℓ_cell"]

    QCA --> Update["Local Update Rules<br/>Finite Propagation Radius"]

    Update --> Continuum["Continuum Limit<br/>Coarse Graining"]

    Continuum --> EffectiveEOM["Effective Wave Equation<br/>Higher-Order Derivative Corrections"]

    EffectiveEOM --> Dispersion["Dispersion Relation<br/>ω² = c²k²[1 + Σβ₂ₙ(kℓ)^(2n)]"]

    Dispersion --> Even["Only Even-Order Terms<br/>Null-Modular Symmetry"]

    Even --> Beta2["Lowest Order<br/>β₂(kℓ)²"]

    style QCA fill:#e1f5ff
    style Even fill:#fff4e6
    style Beta2 fill:#f44336,color:#fff
```

**Physical Picture**: Imagine grid made of springs and masses. Long-wavelength vibrations look like continuous waves at low frequencies, but when wavelength approaches lattice spacing, will "stutter"—this is dispersion. Propagation of gravitational waves in discrete spacetime is essentially similar "lattice effect".

### 7.2.3 Deviation of Group Velocity and Phase Velocity

With dispersion relation $\omega(k)$, can calculate group velocity (energy propagation speed):

$$
v_g = \frac{d\omega}{dk} = c \frac{d}{dk}\sqrt{1 + \beta_2(k\ell)^2 + \cdots}
$$

Expanding to lowest order:

$$
v_g \approx c \left[ 1 + \frac{3}{2}\beta_2(k\ell_{\text{cell}})^2 + \cdots \right]
$$

Thus:

$$
\frac{v_g}{c} - 1 \approx \frac{3}{2}\beta_2(k\ell_{\text{cell}})^2
$$

**Accumulation of Time Delay**:

Gravitational wave propagates distance $D$ from source to observer, relative time delay compared to light:

$$
\Delta t \approx D \left( \frac{1}{v_g} - \frac{1}{c} \right) \approx \frac{D}{c} \cdot \frac{3}{2}\beta_2(k\ell_{\text{cell}})^2
$$

```mermaid
graph LR
    Source["Source Region<br/>Distance D"]

    Source --> GW["Gravitational Wave<br/>v_g ≈ c(1 + εβ₂)"]
    Source --> Light["Light<br/>v = c"]

    GW --> T_GW["Arrival Time<br/>t_gw ≈ D/v_g"]
    Light --> T_EM["Arrival Time<br/>t_em = D/c"]

    T_GW --> Delta["Time Difference<br/>Δt ≈ (D/c)·β₂(kℓ)²"]
    T_EM --> Delta

    Delta --> Observation["Observation Constraint<br/>|Δt| < 1.7s ↔ Source"]

    style Source fill:#e1f5ff
    style Delta fill:#fff4e6
    style Observation fill:#f44336,color:#fff
```

**Numerical Estimate**: For GW170817, $D \sim 40\,\text{Mpc} \sim 1.2 \times 10^{24}\,\text{m}$, frequency $f \sim 100\,\text{Hz}$ corresponds to $k \sim 2\pi f/c \sim 2\times 10^{-6}\,\text{m}^{-1}$. If $\ell_{\text{cell}} \sim 10^{-35}\,\text{m}$ and $\beta_2 \sim O(1)$, then:

$$
\Delta t \sim 10^{24} \times 10^{-12} \times 10^{-70} \times 10^{-6} \sim 10^{-64}\,\text{s}
$$

Far smaller than observation precision! This shows **GW170817 alone cannot directly probe Planck-scale dispersion**—but can give extremely strong constraint on combination $\beta_2 \ell_{\text{cell}}^2$.

---

## 7.3 Origin of Dispersion in Unified Framework

### 7.3.1 Taylor Expansion of QCA Local Updates

In quantum cellular automaton universe, spacetime evolution given by local unitary operator $U_{\text{loc}}$:

$$
|\psi(t+\Delta t)\rangle = \prod_{x \in \Lambda} U_x^{\text{loc}} |\psi(t)\rangle
$$

where $\Delta t$ is time step, $\Lambda$ is lattice site set.

In continuum limit, expand $U_{\text{loc}}$ in frequency-wavenumber:

$$
U_{\text{loc}}(k, \omega) \approx \exp\left[ -i\omega\Delta t + i c k \ell_{\text{cell}} + \alpha_2 (k\ell_{\text{cell}})^2 + \cdots \right]
$$

Requiring $U_{\text{loc}}$ unitary ($U^\dagger U = 1$), get dispersion relation:

$$
\omega^2 = c^2 k^2 + \frac{2\alpha_2}{\Delta t \ell_{\text{cell}}} k^2 (k\ell_{\text{cell}})^2 + \cdots
$$

Define dimensionless dispersion coefficient:

$$
\beta_2 = \frac{2\alpha_2}{c^2 \Delta t \ell_{\text{cell}}}
$$

```mermaid
graph TB
    QCA_Update["QCA Local Update<br/>U_loc"]

    QCA_Update --> Unitary["Unitary Condition<br/>U†U = 1"]

    Unitary --> Expansion["Frequency-Wavenumber Expansion<br/>exp[-iωΔt + ickℓ + ...]"]

    Expansion --> Dispersion["Dispersion Relation<br/>ω² = c²k²[1 + β₂(kℓ)²]"]

    Dispersion --> Coefficients["Dispersion Coefficient<br/>β₂ ~ α₂/(cΔt·ℓ)"]

    Coefficients --> Naturalness["Naturalness Assumption<br/>β₂ ~ O(1)"]

    style QCA_Update fill:#e1f5ff
    style Dispersion fill:#fff4e6
    style Naturalness fill:#ffccbc
```

**Physical Interpretation**: Dispersion coefficient $\beta_2$ characterizes "non-local correction strength" in QCA update rules. If $\beta_2 \sim O(1)$ (natural assumption), dispersion effects proportional to square of lattice spacing; if $\beta_2 \ll 1$ (fine-tuning), dispersion additionally suppressed.

### 7.3.2 High-Frequency Behavior of Unified Time Scale

Unified time scale $\kappa(\omega; \Theta)$ connects frequency and geometry through scattering matrix:

$$
\kappa(\omega) = \frac{1}{2\pi}\text{tr}\,Q(\omega), \quad Q(\omega) = -i S^\dagger(\omega)\partial_\omega S(\omega)
$$

In high-frequency limit $\omega \to \omega_{\text{Planck}}$, behavior of $\kappa(\omega)$ determines **effective Planck length**:

$$
\ell_{\text{Pl}}^{\text{eff}}(\omega) \sim \left[ G_{\text{eff}}(\omega) \right]^{1/2}
$$

Correction terms in gravitational wave dispersion relation essentially reflect deviation of $G_{\text{eff}}(\omega)$ at different frequencies:

$$
G_{\text{eff}}(\omega) = G_N \left[ 1 + \gamma_2 \left( \frac{\omega}{\omega_{\text{Pl}}} \right)^2 + \cdots \right]
$$

```mermaid
graph LR
    Kappa["Unified Time Scale<br/>κ(ω)"]

    Kappa --> HighFreq["High-Frequency Behavior<br/>ω → ω_Pl"]

    HighFreq --> G_eff["Effective Gravitational Constant<br/>G_eff(ω)"]

    G_eff --> Planck["Effective Planck Length<br/>ℓ_Pl(ω)"]

    Planck --> Dispersion["Gravitational Wave Dispersion<br/>β₂ ~ γ₂"]

    style Kappa fill:#2196f3,color:#fff
    style Dispersion fill:#f44336,color:#fff
```

**Key Insight**: Gravitational wave dispersion is not isolated correction term, but **inevitable manifestation** of unified time scale at high frequencies—it locks with black hole entropy (determines lower bound of $\ell_{\text{cell}}$) and cosmological constant (determines UV spectral structure of $\kappa(\omega)$) through same $\Theta$ parameter.

### 7.3.3 Null-Modular Symmetry Forbids Odd-Order Terms

Under Null-Modular double cover structure of unified framework, causal structure requires dispersion relation satisfy:

**Causality Condition**: Group velocity cannot exceed speed of light and cannot be negative

$$
0 < v_g(k) \leq c
$$

**Time-Reversal Symmetry**: At microscopic QCA level

$$
\omega(k) = \omega(-k)
$$

These two conditions together exclude odd-order terms $(k\ell)^{2n+1}$, because:

1. Odd-order terms cause $\omega(k) \neq \omega(-k)$, violating time-reversal symmetry
2. Odd-order terms may make $v_g(k) < 0$ or $v_g(k) > c$, violating causality

```mermaid
graph TB
    NullModular["Null-Modular<br/>Double Cover Structure"]

    NullModular --> Causality["Causality<br/>0 < v_g ≤ c"]
    NullModular --> TimeReversal["Time Reversal<br/>ω(k) = ω(-k)"]

    Causality --> NoOdd1["Forbid Odd-Order Terms<br/>Otherwise v_g May < 0"]
    TimeReversal --> NoOdd2["Forbid Odd-Order Terms<br/>Otherwise ω(k)≠ω(-k)"]

    NoOdd1 --> OnlyEven["Only Allow Even-Order Terms<br/>β₂(kℓ)², β₄(kℓ)⁴, ..."]
    NoOdd2 --> OnlyEven

    style NullModular fill:#2196f3,color:#fff
    style OnlyEven fill:#4caf50,color:#fff
```

**Physical Meaning**: This constraint is not artificially imposed, but automatically required by **geometric consistency** of unified framework—just as Möbius strip cannot define globally consistent "up-down" direction, certain topological structures naturally exclude certain physical corrections.

---

## 7.4 Constraint Function Definition: $C_{\text{GW}}(\Theta) = 0$

### 7.4.1 Dual Constraint of Velocity Deviation and Dispersion Deviation

Gravitational wave dispersion constraint consists of **two independent parts**:

**（A）Propagation Velocity Constraint**

Relative deviation of gravitational wave speed from speed of light:

$$
\Delta c(\Theta) = \left| \frac{c_{\text{gw}}(\Theta)}{c_{\text{em}}(\Theta)} - 1 \right|
$$

GW170817 gives:

$$
\Delta c < 10^{-15}
$$

**（B）Dispersion Coefficient Constraint**

In observation frequency band $[f_{\min}, f_{\max}]$, group velocity deviation:

$$
\Delta_{\text{disp}}(\Theta) = \sup_{f \in [f_{\min}, f_{\max}]} \left| \frac{v_g(f; \Theta)}{c} - 1 \right|
$$

From $v_g/c - 1 \approx \frac{3}{2}\beta_2(k\ell)^2$, get:

$$
|\beta_2(\Theta)| \ell_{\text{cell}}^2(\Theta) < \frac{2}{3} \times 10^{-15} \times \left( \frac{c}{2\pi f_{\max}} \right)^2
$$

```mermaid
graph TB
    GW["Gravitational Wave Observation"]

    GW --> Speed["Velocity Constraint<br/>Δc = |c_gw/c - 1|"]
    GW --> Dispersion["Dispersion Constraint<br/>Δ_disp = |v_g/c - 1|"]

    Speed --> GW170817["GW170817<br/>Δc < 10^(-15)"]
    Dispersion --> FreqDep["Frequency Dependence<br/>v_g(f)"]

    GW170817 --> CGW1["C_GW^(velocity)"]
    FreqDep --> CGW2["C_GW^(dispersion)"]

    CGW1 --> CGW["Total Constraint<br/>C_GW(Θ)"]
    CGW2 --> CGW

    style GW fill:#2196f3,color:#fff
    style CGW fill:#f44336,color:#fff
```

**Unified Constraint Function**

$$
C_{\text{GW}}(\Theta) = \Delta c(\Theta) + \Delta_{\text{disp}}(\Theta)
$$

Physical meaning: Requires $C_{\text{GW}}(\Theta) \lesssim 10^{-15}$, i.e., gravitational wave propagation highly consistent with speed of light at all frequencies.

### 7.4.2 Overlap Interval with Black Hole Entropy Constraint

Black hole entropy constraint gives **lower bound** of $\ell_{\text{cell}}$:

$$
\ell_{\text{cell}}^2 = 4G \log d_{\text{eff}} \sim \ell_{\text{Planck}}^2
$$

That is $\ell_{\text{cell}} \geq \ell_{\text{Pl}} \sim 1.6 \times 10^{-35}\,\text{m}$.

Gravitational wave dispersion constraint gives **upper bound** of $\ell_{\text{cell}}$ (assuming $\beta_2 \sim O(1)$):

For $f \sim 100\,\text{Hz}$, $\lambda = c/f \sim 3 \times 10^6\,\text{m}$, requires:

$$
|\beta_2| \ell_{\text{cell}}^2 < 10^{-15} \times \lambda^2 \sim 10^{-3}\,\text{m}^2
$$

If $\beta_2 \sim 1$, then:

$$
\ell_{\text{cell}} < 10^{-1.5}\,\text{m} \sim 3 \times 10^{-2}\,\text{m}
$$

This upper bound seems very loose (several centimeters!), but considering higher frequency bands (like post-merger oscillations $f \sim 10^4\,\text{Hz}$), upper bound will further tighten.

```mermaid
graph LR
    BH["Black Hole Entropy Constraint<br/>C_BH = 0"]
    GW["Gravitational Wave Dispersion Constraint<br/>C_GW = 0"]

    BH --> Lower["Lower Bound<br/>ℓ_cell ≥ ℓ_Pl"]
    GW --> Upper["Upper Bound<br/>ℓ_cell < f(β₂, f_max)"]

    Lower --> Overlap["Overlap Interval<br/>ℓ_Pl ≤ ℓ_cell < ℓ_upper"]
    Upper --> Overlap

    Overlap --> Allowed["Allowed Window<br/>If β₂ ~ O(1)"]

    Allowed --> Test["Future High-Frequency GW<br/>Tighten Upper Bound"]

    style BH fill:#e1f5ff
    style GW fill:#fff4e6
    style Overlap fill:#4caf50,color:#fff
```

**Key Tension**: If $\beta_2$ amplified by some mechanism (like $\beta_2 \gg 1$), or future detection of higher-frequency gravitational wave signals (like neutron star oscillation modes $f \sim 10^4\,\text{Hz}$), upper bound will approach $\ell_{\text{Pl}}$, making allowed window **narrow**—this is direct test of QCA universe model.

---

## 7.5 Coupling with Other Constraints

### 7.5.1 Gravitational Wave–Black Hole Entropy: Two-Way Pinch on Lattice Spacing

Black hole entropy constraint $C_{\text{BH}}(\Theta) = 0$ and gravitational wave dispersion constraint $C_{\text{GW}}(\Theta) = 0$ form **two-way pinch** through common parameter $\ell_{\text{cell}}(\Theta)$:

$$
\ell_{\text{cell}} \in \left[ \ell_{\text{lower}}(\Theta), \ell_{\text{upper}}(\Theta) \right]
$$

where:

$$
\ell_{\text{lower}} = \sqrt{4G \log d_{\text{eff}}(\Theta)}, \quad \ell_{\text{upper}} = \sqrt{\frac{c^2}{|\beta_2(\Theta)| k_{\max}^2 \times 10^{15}}}
$$

**Cross-Locking Mechanism**:

1. If $d_{\text{eff}}(\Theta)$ increases (more horizon degrees of freedom), $\ell_{\text{lower}}$ increases
2. If $\beta_2(\Theta)$ increases (stronger dispersion), $\ell_{\text{upper}}$ decreases
3. Two must satisfy $\ell_{\text{lower}} < \ell_{\text{upper}}$, otherwise no solution

```mermaid
graph TB
    Theta["Parameter Vector Θ"]

    Theta --> Cell["Lattice Spacing ℓ_cell(Θ)"]
    Theta --> d_eff["Effective Dimension d_eff(Θ)"]
    Theta --> Beta2["Dispersion Coefficient β₂(Θ)"]

    d_eff --> Lower["Black Hole Entropy Lower Bound<br/>ℓ_lower ~ √(4G log d)"]
    Beta2 --> Upper["Dispersion Upper Bound<br/>ℓ_upper ~ √(c²/β₂k²·10^15)"]

    Lower --> Window["Allowed Window<br/>ℓ_lower ≤ ℓ_cell ≤ ℓ_upper"]
    Upper --> Window

    Window --> Consistency["Consistency Condition<br/>Window Non-Empty"]

    Cell --> Window

    style Theta fill:#2196f3,color:#fff
    style Window fill:#4caf50,color:#fff
    style Consistency fill:#f44336,color:#fff
```

**Physical Prediction**: If future black hole observations (like higher resolution imaging from Event Horizon Telescope) precisely determine deviation of horizon entropy, can reverse infer $d_{\text{eff}}$, thus tighten $\ell_{\text{lower}}$; combined with $\ell_{\text{upper}}$ from gravitational wave dispersion, may **pinch** $\ell_{\text{cell}}$ to within one order of magnitude in coming decades.

### 7.5.2 Gravitational Wave–Cosmological Constant: Frequency Band Separation and Spectral Consistency

Cosmological constant constraint $C_\Lambda(\Theta) = 0$ realized through **full spectral integral** of unified time scale $\kappa(\omega; \Theta)$:

$$
\Lambda_{\text{eff}}(\Theta) \sim \int_0^{E_{\mathrm{UV}}} E^2 \Delta\rho(E)\,dE = 0
$$

Gravitational wave dispersion constraint gives $G_{\text{eff}}(\omega_{\text{GW}})$ through local behavior of $\kappa(\omega)$ at **GW frequency band $\omega_{\text{GW}} \sim 10^3\,\text{rad/s}$**:

$$
\beta_2(\Theta) \sim \frac{G_{\text{eff}}(\omega_{\text{GW}}) - G_N}{G_N}
$$

**Frequency Band Separation Principle**:

- $C_\Lambda$ mainly constrains balance of $\kappa(\omega)$ at UV ($\omega \sim E_{\text{Pl}}$) and IR ($\omega \sim H_0$) ends
- $C_{\text{GW}}$ mainly constrains smoothness of $\kappa(\omega)$ at mid-frequency band ($\omega \sim 10^3\,\text{rad/s}$)

Under natural parameter choices, these two constraints **do not conflict**: $\kappa(\omega)$ satisfying spectral sum rule can remain nearly constant at GW frequency band.

```mermaid
graph LR
    Kappa["κ(ω; Θ)"]

    Kappa --> UV["Ultraviolet ω ~ E_Pl<br/>Spectral Sum Rule"]
    Kappa --> Mid["Mid-Frequency ω ~ 10³<br/>Gravitational Wave Band"]
    Kappa --> IR["Infrared ω ~ H₀<br/>Cosmological Scale"]

    UV --> C_Lambda["C_Λ Constraint<br/>High-Energy Cancellation"]
    Mid --> C_GW["C_GW Constraint<br/>Dispersion Coefficient"]
    IR --> C_Lambda

    C_Lambda --> Separation["Frequency Band Separation<br/>Each Independent"]
    C_GW --> Separation

    style Kappa fill:#2196f3,color:#fff
    style Separation fill:#4caf50,color:#fff
```

**Physical Picture**: Unified time scale $\kappa(\omega)$ "responsible" for different physical constraints at different frequency bands—like multi-band radio, different bands play different content, but all controlled through same antenna ($\Theta$ parameter).

### 7.5.3 Gravitational Wave–ETH: Scale Separation of Propagation and Thermalization

ETH constraint $C_{\text{ETH}}(\Theta) = 0$ requires on **local causal diamonds** $\Delta x \sim 10^{-6}\,\text{m}$ (laboratory scale), quantum states quickly thermalize:

$$
\tau_{\text{thermalization}} \sim \ell_{\text{cell}} / c \sim 10^{-43}\,\text{s}
$$

Gravitational wave dispersion involves **macroscopic propagation** $D \sim 10^{24}\,\text{m}$ (intergalactic scale), time scale:

$$
t_{\text{propagation}} \sim D / c \sim 10^{16}\,\text{s}
$$

Two differ by **59 orders of magnitude**, won't interfere under natural parameters:

- ETH controls **statistical equilibrium** of microscopic states
- Dispersion controls **propagation law** of macroscopic waves

```mermaid
graph TB
    Scales["Physical Scale Separation"]

    Scales --> Micro["Microscopic<br/>Δx ~ 10^(-6) m"]
    Scales --> Macro["Macroscopic<br/>D ~ 10^(24) m"]

    Micro --> ETH["C_ETH Constraint<br/>Local Thermalization"]
    Macro --> GW["C_GW Constraint<br/>Propagation Dispersion"]

    ETH --> Time1["τ_th ~ 10^(-43) s"]
    GW --> Time2["t_prop ~ 10^(16) s"]

    Time1 --> Gap["59 Orders of Magnitude Gap"]
    Time2 --> Gap

    Gap --> Independent["Two Constraints Independent<br/>Scale Separation"]

    style Scales fill:#2196f3,color:#fff
    style Independent fill:#4caf50,color:#fff
```

**Physical Meaning**: QCA universe chaotic microscopically (satisfies ETH), smooth macroscopically (almost no dispersion), this **hierarchical separation** is key to self-consistency of unified framework—if microscopic chaos causes macroscopic unpredictability, or macroscopic dispersion destroys microscopic unitarity, framework would collapse.

---

## 7.6 Experimental Tests and Future Observations

### 7.6.1 Frequency Band Coverage of Current Gravitational Wave Detectors

**Ground-Based Detectors (LIGO, Virgo, KAGRA)**

- Frequency band: 10 Hz - 10 kHz
- Main sources: Binary black holes, binary neutron star mergers
- Existing constraint: $|v_g/c - 1| < 10^{-15}$ (from GW170817)

**Space Detectors (LISA, planned 2030s)**

- Frequency band: 0.1 mHz - 1 Hz
- Main sources: Supermassive black hole mergers, compact binaries
- Expected constraint: Through long baseline ($\sim 10^9\,\text{km}$) and long observation (year scale), sensitivity to dispersion improves to $\sim 10^{-17}$

**Pulsar Timing Arrays (NANOGrav, SKA)**

- Frequency band: nHz - μHz
- Main sources: Stochastic gravitational wave background, supermassive binary black holes
- Dispersion test: Through correlation of arrival times at different frequencies

```mermaid
graph LR
    Detectors["Gravitational Wave Detectors"]

    Detectors --> Ground["Ground-Based<br/>LIGO/Virgo"]
    Detectors --> Space["Space<br/>LISA"]
    Detectors --> PTA["Pulsar Arrays<br/>NANOGrav"]

    Ground --> Freq1["10 Hz - 10 kHz"]
    Space --> Freq2["0.1 mHz - 1 Hz"]
    PTA --> Freq3["nHz - μHz"]

    Freq1 --> Const1["Current Constraint<br/>10^(-15)"]
    Freq2 --> Const2["Future Constraint<br/>10^(-17)"]
    Freq3 --> Const3["Background Constraint<br/>Spectral Shape"]

    style Detectors fill:#2196f3,color:#fff
    style Const1 fill:#4caf50,color:#fff
    style Const2 fill:#f44336,color:#fff
```

### 7.6.2 Joint Analysis of Multi-Messenger Gravitational Wave Events

Success of GW170817 opened **multi-messenger astronomy** era, future similar events will provide more dispersion constraints:

**Strategy A: Time Delay Statistics**

Through multiple neutron star merger events (LIGO-Virgo expected to detect ~dozens per year), statistically analyze arrival time differences of different frequency components, test dispersion relation:

$$
\Delta t(f_1, f_2) \approx \frac{D}{c} \cdot \beta_2 \ell^2 (k_1^2 - k_2^2)
$$

**Strategy B: Phase Accumulation Analysis**

During propagation, gravitational wave phase accumulates:

$$
\Phi(f) = \int_0^D k(f; \Theta)\,dx
$$

Dispersion causes phase deviation from linear relation, can extract through matched filtering:

$$
\Delta\Phi \sim \beta_2 (k\ell)^2 \times D
$$

LIGO phase precision $\sim 10^{-2}$ radians, combined with $D \sim 100\,\text{Mpc}$ baseline, can probe effects at $\beta_2 \ell^2 \sim 10^{-40}\,\text{m}^2$ level.

```mermaid
graph TB
    MultiMessenger["Multi-Messenger Gravitational Waves"]

    MultiMessenger --> Strategy1["Strategy A<br/>Time Delay Statistics"]
    MultiMessenger --> Strategy2["Strategy B<br/>Phase Accumulation Analysis"]

    Strategy1 --> TimeData["Multiple Event Data<br/>Δt(f₁, f₂)"]
    Strategy2 --> PhaseData["Waveform Fitting<br/>ΔΦ(f)"]

    TimeData --> Joint["Joint Constraint<br/>β₂ℓ²"]
    PhaseData --> Joint

    Joint --> Improved["Improved Constraint<br/>Next 10 Years"]

    style MultiMessenger fill:#2196f3,color:#fff
    style Joint fill:#4caf50,color:#fff
    style Improved fill:#f44336,color:#fff
```

### 7.6.3 Post-Merger Signals and High-Frequency Gravitational Waves

After binary neutron star merger, forms supermassive neutron star or black hole, produces **post-merger oscillations**, frequency range:

$$
f_{\text{post-merge}} \sim 2 - 4\,\text{kHz}
$$

These signals are weak (require next-generation detectors like Cosmic Explorer or Einstein Telescope), but provide **high-frequency dispersion constraints**:

$$
k_{\text{high}} \sim 2\pi f_{\text{post-merge}} / c \sim 10^{-4}\,\text{m}^{-1}
$$

Compared to merger main peak $f \sim 100\,\text{Hz}$, $(k\ell)^2$ increases **400 times**, significantly amplifying dispersion effects!

```mermaid
graph LR
    Merger["Neutron Star Merger"]

    Merger --> Inspiral["Inspiral Phase<br/>f ~ 10-100 Hz"]
    Merger --> Merge["Merger<br/>f ~ 1 kHz"]
    Merger --> PostMerge["Post-Merger<br/>f ~ 2-4 kHz"]

    Inspiral --> Low["Low-Frequency Constraint<br/>Current Level"]
    PostMerge --> High["High-Frequency Constraint<br/>Future Detection"]

    High --> Enhanced["Dispersion Enhancement<br/>(kℓ)² × 400"]

    Enhanced --> Target["Target Sensitivity<br/>β₂ℓ² ~ 10^(-18) m²"]

    style Merger fill:#2196f3,color:#fff
    style Enhanced fill:#f44336,color:#fff
```

**Unified Framework Prediction**: If $\ell_{\text{cell}} \sim \ell_{\text{Pl}}$ and $\beta_2 \sim 10^{6}$ (some quantum gravity models predict), then post-merger signals may first directly detect dispersion effects—this would be **first direct evidence of quantum gravity**.

---

## 7.7 Chapter Summary

This chapter analyzes gravitational wave dispersion constraint in unified constraint framework, core conclusions include:

### Core Constraint Mechanism

**Gravitational Wave Dispersion Constraint Function**

$$
C_{\text{GW}}(\Theta) = \Delta c(\Theta) + \Delta_{\text{disp}}(\Theta)
$$

where:

$$
\Delta c = \left| \frac{c_{\text{gw}}}{c_{\text{em}}} - 1 \right| < 10^{-15}, \quad \Delta_{\text{disp}} = \sup_f \left| \frac{v_g(f)}{c} - 1 \right| \lesssim 10^{-15}
$$

Dispersion relation (only even-order terms):

$$
\omega^2 = c^2 k^2 \left[ 1 + \beta_2(k\ell_{\text{cell}})^2 + \beta_4(k\ell_{\text{cell}})^4 + \cdots \right]
$$

### Three Key Insights

1. **Two-Way Pinch**
   Gravitational wave dispersion constraint gives **upper bound** of $\ell_{\text{cell}}$, black hole entropy constraint gives **lower bound**, two form allowed window—future observations will further tighten, may eventually determine precise value of $\ell_{\text{cell}}$.

2. **Frequency Band Separation**
   Gravitational wave dispersion constraint through behavior of $\kappa(\omega)$ at GW frequency band ($\omega \sim 10^3\,\text{rad/s}$), achieves **scale separation** with cosmological constant constraint (UV/IR ends) and ETH constraint (microscopic scale), each acts on different frequency ranges.

3. **Even-Order Term Mechanism**
   Null-Modular symmetry and causality automatically exclude odd-order dispersion terms $(k\ell)^{2n+1}$, this is not artificial tuning, but **geometric consistency** requirement of unified framework.

### Experimental Test Paths

```mermaid
graph TB
    Future["Future Gravitational Wave Observations"]

    Future --> LISA["LISA Space Detection<br/>Sensitivity 10^(-17)"]
    Future --> ET["Einstein Telescope<br/>Post-Merger Signals"]
    Future --> Multi["Multi-Messenger Statistics<br/>Dozens of Events"]

    LISA --> Improve1["Improve Low-Frequency Constraint<br/>Supermassive Binary Black Holes"]
    ET --> Improve2["Detect High-Frequency Dispersion<br/>f ~ kHz"]
    Multi --> Improve3["Phase Accumulation Analysis<br/>β₂ℓ²"]

    Improve1 --> Joint["Joint Constraint ℓ_cell<br/>Next 20 Years"]
    Improve2 --> Joint
    Improve3 --> Joint

    style Future fill:#2196f3,color:#fff
    style Joint fill:#f44336,color:#fff
```

### Harmony with Other Constraints

- **With Black Hole Entropy Constraint**: Two-way pinch on $\ell_{\text{cell}}$, forming allowed window
- **With Cosmological Constant Constraint**: Through frequency band separation of $\kappa(\omega)$, each acts on different energy scales
- **With ETH Constraint**: Through scale separation (microscopic thermalization vs macroscopic propagation), avoiding conflict
- **With Neutrino/Strong CP Constraints**: Indirect association (through global consistency of unified time scale)

Gravitational wave dispersion constraint is **most directly observable** of six locks—it doesn't require extreme experimental conditions (like black hole horizons or Planck energy), just wait for next multi-messenger gravitational wave event. In next 10-20 years, with LISA, Einstein Telescope and more neutron star merger event detections, this constraint will transform from "upper bound test" to "precise measurement", providing decisive experimental support for unified framework.

---

## Theoretical Sources

This chapter synthesizes content from following two source theory documents:

1. **Six Ununified Physics as Consistency Constraints of Unified Matrix–QCA Universe**
   (`euler-gls-extend/six-unified-physics-constraints-matrix-qca-universe.md`)
   - Section 3.6: Theorem 3.6 (Even-Order Gravitational Wave Dispersion and Lattice Spacing Upper Bound)
   - Appendix E: Estimation of Gravitational–QCA Dispersion and LIGO/Virgo Constraints
   - Section 5.1: Upper bound setting of dispersion coefficients $\beta_{2n}$ in prototype parameter table

2. **Unified Constraint System of Six Unsolved Problems**
   (`euler-gls-info/19-six-problems-unified-constraint-system.md`)
   - Section 3.1: Definition of gravitational wave dispersion constraint $C_{\text{GW}}(\Theta)$ among six scalar constraint functions
   - Section 5.1: Spectral–geometric locking mechanism of black hole entropy and gravitational wave dispersion
   - Section 5.3: Many-body–gravitational coupling analysis of ETH–black hole–gravitational wave

Key technical details include: derivation of gravitational wave dispersion relation $\omega^2 = c^2k^2[1+\sum\beta_{2n}(k\ell)^{2n}]$, calculation of group velocity deviation $v_g/c - 1 \simeq \frac{3}{2}\beta_2(k\ell)^2$, conversion of constraint $|v_g/c-1| < 10^{-15}$ from GW170817/GRB170817A, and analysis of two-way pinch window formed with black hole entropy constraint $\ell_{\text{cell}}^2 = 4G\log d_{\text{eff}}$.

