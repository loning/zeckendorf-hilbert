# 05. Detailed Explanation of Initial State Parameters: Universe's Factory Settings

## Introduction: Quantum State at Big Bang Moment

In previous articles, we established:
- **Article 03**: Universe's spatial structure $\Theta_{\text{str}}$ (stage)
- **Article 04**: Universe's evolution rules $\Theta_{\text{dyn}}$ (script)

But still missing a key element: **Starting point**.

**Core Questions**:
- What quantum state is universe in at $t=0$ (big bang moment)?
- How to encode this initial state with finite bit string?
- How does initial state affect entire universe history?

Answer lies in **initial state parameter** $\Theta_{\text{ini}}$.

### Popular Analogy: Factory's Factory Settings

Continuing our building/factory analogy:

**Already Have**:
- $\Theta_{\text{str}}$: Factory blueprint (how many machines, how to layout)
- $\Theta_{\text{dyn}}$: Production process (how to operate machines)

**Missing**:
- $\Theta_{\text{ini}}$: Machines' initial state (switch positions, temperature, inventory...)

**Why Important**?

Imagine two identical coffee machines (same $\Theta_{\text{str}}$ and $\Theta_{\text{dyn}}$):
- Machine A: Bean hopper full, water tank full, preheated → Coffee immediately
- Machine B: Bean hopper empty, water tank empty, not preheated → Need preparation

**Same structure and rules, different initial states → Different evolution histories!**

Universe is similar:

| Coffee Machine Analogy | Universe QCA | Mathematical Object |
|----------------------|--------------|-------------------|
| Machine factory settings | Initial state parameter $\Theta_{\text{ini}}$ | Parameter bit string |
| Switches/temperature/inventory | Initial quantum state $\omega_0$ | State functional |
| Setup manual | State preparation circuit $V$ | Unitary operator |
| Reference state (all off) | Reference product state $|0_\Lambda\rangle$ | Simple product state |
| Factory setup process | From $|0\rangle$ to $|\Psi_0\rangle$ | Finite depth circuit |

This article will explain in detail how to encode entire universe's initial quantum state with about **500 bits**.

## Part I: Physical Meaning of Initial State

### Initial Condition Problem in Cosmology

**Classical Cosmology** (Friedmann-Lemaître-Robertson-Walker model):

Initial conditions need to specify:
- Initial matter density $\rho_0$
- Initial Hubble constant $H_0$
- Initial curvature $k$
- Initial temperature $T_0$
- Initial fluctuation spectrum $\Delta\rho(\mathbf{k})$
- ...

**Problem**: These are all **real numbers**, need infinite precision → Infinite information!

**Quantum Cosmology** (Hartle-Hawking, Vilenkin, etc.):

Attempts to derive initial state from "no-boundary" or "tunneling" principles, but still needs:
- Wave function $\Psi[\text{three-geometry}]$ (functional on superspace)
- Continuous, infinite-dimensional → Still needs infinite information

**QCA Framework Solution**:

Initial state is a **state in finite-dimensional Hilbert space**:

$$
|\Psi_0\rangle \in \mathcal{H}_\Lambda = \bigotimes_{x \in \Lambda} \mathcal{H}_x
$$

**Dimension**:
$$
\dim \mathcal{H}_\Lambda = d_{\text{cell}}^{N_{\text{cell}}} \sim 10^{6 \times 10^{90}}
$$

Although dimension huge, but **finite**!

### Three Formulations of Initial State

**Formulation 1** (Quantum State Vector):

$$
|\Psi_0^{\Theta}\rangle \in \mathcal{H}_\Lambda
$$

A normalized quantum state.

**Formulation 2** (Density Matrix):

$$
\rho_0^{\Theta} = |\Psi_0^{\Theta}\rangle\langle\Psi_0^{\Theta}|
$$

Density operator of pure state.

**Formulation 3** (State Functional):

$$
\omega_0^{\Theta}(A) = \langle\Psi_0^{\Theta}|A|\Psi_0^{\Theta}\rangle, \quad A \in \mathcal{A}(\Lambda)
$$

Positive normalized functional on quasi-local algebra.

**Three Equivalent** (for pure states). This article mainly uses Formulations 1 and 3.

### Initial State Determines Universe History

Given initial state $\omega_0$ and evolution $\alpha$, entire universe history uniquely determined:

$$
\boxed{\omega_n = \omega_0 \circ \alpha^{-n}}
$$

That is:

$$
\omega_n(A) = \omega_0(\alpha^{-n}(A)) = \langle\Psi_0|U^{\dagger n} A U^n|\Psi_0\rangle
$$

**Physical Meaning**:
- $\omega_0$: "Frame zero" (big bang moment)
- $\alpha$: "Frame-by-frame evolution rule" (from $\Theta_{\text{dyn}}$)
- $\omega_n$: "Frame $n$" (time $t = n\Delta t$)

**Popular Analogy**:
- Initial state = First frame of movie
- Evolution rule = How each frame transforms to next
- Entire movie = Generated frame by frame from first frame

**Philosophical Implication**:
Universe history is **deterministic** (under unitary evolution):
$$
\text{Initial State} + \text{Evolution Rule} \Rightarrow \text{Entire History}
$$

## Part II: Reference Product State $|0_\Lambda\rangle$

### Simplest State: Vacuum State

How much information needed to directly encode an arbitrary quantum state $|\Psi_0\rangle \in \mathcal{H}_\Lambda$?

**Naive Counting**:
- $\mathcal{H}_\Lambda \cong \mathbb{C}^D$, where $D = d_{\text{cell}}^{N_{\text{cell}}}$
- Quantum state: $|\Psi\rangle = \sum_{i=1}^D c_i |i\rangle$
- Coefficients $c_i \in \mathbb{C}$, satisfy $\sum_i |c_i|^2 = 1$
- Degrees of freedom: $2(D-1)$ real numbers (excluding normalization and global phase)

**Information Content** (if each real number needs $m$ bit precision):
$$
I \sim 2D \times m \sim 2 \times 10^{10^{91}} \times m
$$

This is **double exponential**! Far exceeds $I_{\max} \sim 10^{123}$!

**Solution**: Don't directly encode state vector, but **generate from simple state**.

### Definition of Reference Product State

**Definition 5.1** (Reference Product State):

Choose a fixed "vacuum state" $|0_{\text{cell}}\rangle \in \mathcal{H}_{\text{cell}}$ for each cell, define:

$$
\boxed{|0_\Lambda\rangle = \bigotimes_{x \in \Lambda} |0_{\text{cell}}\rangle_x}
$$

**Properties**:
1. **Product state**: No entanglement
2. **Translation-invariant**: Same at each lattice point
3. **Simple**: Completely determined by $|0_{\text{cell}}\rangle$

**Example 1** (Spin Chain):

If $\mathcal{H}_{\text{cell}} = \mathbb{C}^2$, basis $\{|\uparrow\rangle, |\downarrow\rangle\}$:

$$
|0_{\text{cell}}\rangle = |\downarrow\rangle
$$

Then:

$$
|0_\Lambda\rangle = |\downarrow\downarrow\downarrow\cdots\downarrow\rangle
$$

(All spins down)

**Example 2** (Fermion QCA):

If $\mathcal{H}_{\text{cell}}$ contains fermion annihilation/creation operators $\hat{a}, \hat{a}^\dagger$:

$$
|0_{\text{cell}}\rangle = |\text{vac}\rangle
$$

(Fermion vacuum state, no particles)

**Encoding Overhead**:

Reference product state completely determined by $|0_{\text{cell}}\rangle$, and $|0_{\text{cell}}\rangle$ already specified in $\Theta_{\text{str}}$ (as part of Hilbert space).

Therefore: **No additional encoding needed!**

### Physical Interpretation

**Universe's "Absolute Zero"**:

$|0_\Lambda\rangle$ similar to physics' "ground state" or "vacuum state":
- No particles
- No entanglement
- No excitations
- Zero entropy (pure state)

**Popular Analogy**:
- Reference product state = Blank white paper fresh from factory
- Initial state = Picture drawn on white paper
- State preparation circuit = "Drawing process" from white paper to picture

## Part III: State Preparation Circuit $V_{\Theta_{\text{ini}}}$

### Generating Initial State from Reference State

**Core Idea**: Use **finite depth unitary circuit** to generate $|\Psi_0\rangle$ from $|0_\Lambda\rangle$.

**Definition 5.2** (State Preparation Circuit):

Exists finite depth unitary operator $V_{\Theta_{\text{ini}}}$, composed of gates from gate set $\mathcal{G}$:

$$
V_{\Theta_{\text{ini}}} = V_{D_{\text{ini}}} V_{D_{\text{ini}}-1} \cdots V_2 V_1
$$

such that:

$$
\boxed{|\Psi_0^{\Theta}\rangle = V_{\Theta_{\text{ini}}} |0_\Lambda\rangle}
$$

**Structure** (completely similar to Article 04 dynamical circuit):
- Depth: $D_{\text{ini}} \in \mathbb{N}$
- Each layer $V_\ell$: Parallel combination of several local gates $G_k \in \mathcal{G}$
- Gate parameters: Discrete angles $\theta = 2\pi n / 2^m$

**Difference**:
- Dynamical circuit $U_{\Theta_{\text{dyn}}}$: Defines time evolution (applied repeatedly)
- State preparation circuit $V_{\Theta_{\text{ini}}}$: Generates initial state (applied only once)

**Popular Analogy**:
- $U$: Factory production process (repeated daily)
- $V$: Machine installation and debugging process (done only once)

### Circuit Depth and Entanglement Structure

**Consequence of Finite Depth** (Lieb-Robinson bound):

If circuit depth is $D_{\text{ini}}$, Lieb-Robinson velocity is $v_{\text{LR}}$, then:

**Theorem 5.3** (Entanglement Range Limitation):

Mutual information of two regions $A, B$ at distance $d(x, y) > v_{\text{LR}} D_{\text{ini}}$ satisfies:

$$
I(A:B) \lesssim e^{-c(d - v_{\text{LR}} D_{\text{ini}})}
$$

(exponential decay)

**Physical Meaning**:
- Short depth circuit $\Rightarrow$ **Short-range entangled state**
- Long-range entanglement needs depth $D \sim N_{\text{cell}}$ $\Rightarrow$ Parameter explosion

**Cosmological Application**:

Observations show cosmic microwave background (CMB) has finite correlation length:
- Sound horizon: $\sim 10^5$ light years
- Observable universe: $\sim 10^{10}$ light years
- Ratio: $\sim 10^{-5}$

**Corollary**: Initial entanglement is **local**, depth $D_{\text{ini}} \sim \log N_{\text{cell}}$ sufficient.

### Examples of State Preparation Circuits

**Example 1** (Hadamard Layer):

For spin chain, apply Hadamard gate:

$$
V = \bigotimes_{x \in \Lambda} H_x
$$

where $H = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$.

**Initial State**:

$$
|\Psi_0\rangle = V |\downarrow\downarrow\cdots\downarrow\rangle = \frac{1}{2^{N_{\text{cell}}/2}} \sum_{\{s_x\}} |s_1 s_2 \cdots s_{N_{\text{cell}}}\rangle
$$

(Equal-weight superposition of all spin configurations)

**Properties**:
- Maximum entanglement (in some sense)
- Depth $D=1$ (extremely shallow)
- Entropy $S = N_{\text{cell}} \log 2$ (maximum entropy)

**Example 2** (GHZ State Generation):

Generate GHZ state for 3 lattice points:

$$
|\text{GHZ}\rangle = \frac{1}{\sqrt{2}}(|\downarrow\downarrow\downarrow\rangle + |\uparrow\uparrow\uparrow\rangle)
$$

**Circuit** (depth 3):
1. Apply Hadamard to 1st lattice point: $H_1$
2. CNOT gates: 1 controls 2, 2 controls 3
3. Result: $|\text{GHZ}\rangle$

**Example 3** (Thermal State Approximation):

Construct "thermalized" state through random local unitaries:

$$
V = \prod_{\ell=1}^D \prod_x R_x^{(\ell)}(\theta_{\ell,x})
$$

where $R(\theta)$ are random rotations, angles sampled from distribution (discretized).

**Depth**: $D \sim \log N_{\text{cell}}$ can achieve near-thermal state.

## Part IV: Encoding of $\Theta_{\text{ini}}$

### Encoding Structure

Similar to $\Theta_{\text{dyn}}$ (Article 04), $\Theta_{\text{ini}}$ encodes state preparation circuit $V$:

$$
\Theta_{\text{ini}} = (D_{\text{ini}}, \{k_\ell\}, \{R_\ell\}, \{\theta_{\ell,j}\})
$$

**Components**:
1. **Depth** $D_{\text{ini}}$
2. **Gate type per layer** $k_\ell \in \{1, \ldots, K\}$
3. **Action region** $R_\ell \subset \Lambda$
4. **Angle parameters** $\theta_{\ell,j} = 2\pi n_{\ell,j} / 2^m$

### Bit Count

$$
|\Theta_{\text{ini}}| = \lceil\log_2 D_{\text{ini}}\rceil + D_{\text{ini}} \times (I_{\text{gate}} + I_{\text{region}} + I_{\text{angles}})
$$

**Translation-Invariant Case** (typical):

- $D_{\text{ini}} = 5$ (short-range entanglement sufficient)
- Gate type: $\log_2 K = 4$ bits/layer
- Action region: 1 bit/layer (odd/even)
- Angle parameters: $2 \times 50 = 100$ bits/layer (2 angles, precision 50)

**Total**:
$$
|\Theta_{\text{ini}}| = \lceil\log_2 5\rceil + 5 \times (4 + 1 + 100) = 3 + 525 = 528 \text{ bits}
$$

$$
\boxed{|\Theta_{\text{ini}}| \sim 500 \text{ bits}}
$$

**Key Observation**:
$$
|\Theta_{\text{ini}}| \sim 500 \ll I_{\max} \sim 10^{123}
$$

Initial state parameter information **negligible**!

## Part V: Symmetry Constraints on Initial State

### Translation-Invariant Initial State

Simplest symmetry: Translation invariance.

**Definition 5.4** (Translation-Invariant Initial State):

$$
V_{\Theta_{\text{ini}}} = \left( \bigotimes_{x \in \Lambda} V_{\text{local}} \right)
$$

Apply same local unitary $V_{\text{local}}$ to each lattice point.

**Example**:

$$
V_{\text{local}} = R_y(\theta) = \exp(-i\theta \sigma_y / 2)
$$

Applied to all lattice points:

$$
|\Psi_0\rangle = \bigotimes_x R_y(\theta) |\downarrow\rangle_x
$$

**Encoding Overhead**:
- Only need to encode $V_{\text{local}}$ (independent of $N_{\text{cell}}$!)
- Example: Single rotation gate + 1 angle parameter = ~50 bits

**Information Compression**:
- Without symmetry: $\sim N_{\text{cell}} \times I_{\text{local}}$ bits
- Translation-invariant: $\sim I_{\text{local}}$ bits
- **Compression ratio**: $N_{\text{cell}} \sim 10^{90}$ (astronomical number!)

### Ground State and Thermal State

**Ground State Initial State**:

If initial state is ground state of some effective Hamiltonian $H_{\text{eff}}$:

$$
|\Psi_0\rangle = |\text{GS}(H_{\text{eff}})\rangle
$$

**Encoding**:
- Only need to encode $H_{\text{eff}}$ (usually implicit in $\Theta_{\text{dyn}}$)
- Additional information: $\sim 0$ bits (if agree "initial state = ground state")

**Thermal State Initial State** (density matrix):

$$
\rho_0 = \frac{e^{-\beta H_{\text{eff}}}}{Z}
$$

**Encoding**:
- Hamiltonian $H_{\text{eff}}$ (already in $\Theta_{\text{dyn}}$)
- Temperature $\beta = 1/k_B T$ (needs discretization, ~50 bits)

**Total**: $\sim 50$ bits

### Symmetry Breaking and Phase Transitions

**Spontaneous Symmetry Breaking**:

If theory has symmetry, but initial state breaks symmetry:

**Example** (Ferromagnetic State):
- Hamiltonian: $H = -J\sum_{\langle i,j\rangle} \sigma_i^z \sigma_j^z$ ($Z_2$ symmetric)
- Ground state: Two degenerate states $|\uparrow\uparrow\cdots\uparrow\rangle$ and $|\downarrow\downarrow\cdots\downarrow\rangle$
- Initial state: Choose one (breaks $Z_2$ symmetry)

**Encoding**:
- Hamiltonian (symmetric): In $\Theta_{\text{dyn}}$
- Which ground state chosen: 1 bit ($\uparrow$ or $\downarrow$)

**Cosmological Application** (Inflation and Vacuum Selection):
- After inflation, universe may fall into different "vacua"
- Each vacuum corresponds to different physical constants
- $\Theta_{\text{ini}}$ encodes "which vacuum chosen"

## Part VI: Initial Entropy and Information

### von Neumann Entropy of Initial State

**Definition 5.5** (von Neumann Entropy):

For pure state:

$$
S(\omega_0) = -\text{tr}(\rho_0 \log \rho_0) = 0
$$

(pure state entropy zero)

For mixed state:

$$
S(\rho_0) = -\text{tr}(\rho_0 \log \rho_0) > 0
$$

**Physical Meaning**:
- Pure state: Completely determined quantum state, no classical uncertainty
- Mixed state: Partial uncertainty (thermal fluctuations, coarse-graining, etc.)

### Initial Entropy and Universe Evolution

**Theorem 5.6** (Unitary Evolution Preserves Entropy):

If evolution is unitary ($\alpha$ realized by unitary operator), then:

$$
S(\omega_n) = S(\omega_0), \quad \forall n
$$

**Corollary**:
- If $\omega_0$ is pure state ($S=0$), then $\omega_n$ always pure state ($S=0$)
- Unitary evolution **does not increase entropy**

**Question**: Why does universe have second law of thermodynamics (entropy increase)?

**Answer**:
- Global quantum state: Pure state, entropy=0 (conserved)
- Local subsystems: Entanglement causes reduced states to be mixed, entropy>0
- **Entanglement entropy growth** = Apparent "thermodynamic entropy increase"

**Popular Analogy**:
- Two dice: Initially both in determined state (e.g., both 6)
- Operation: Entangle two dice (quantum gate)
- Look at single die: Becomes mixed state (seems random)
- But look at both together: Still pure state (completely determined entangled state)

**Cosmological Application**:
- Initial state: Extremely low entropy (near pure state)
- Evolution: Produces large entanglement
- What local observers see: Entropy increase (but global still pure state)

### Initial State Complexity

**Definition 5.7** (State Complexity):

Minimum circuit depth needed to generate state $|\Psi\rangle$:

$$
C(|\Psi\rangle) = \min\{D : \exists V \text{ depth } D, \, V|0\rangle = |\Psi\rangle\}
$$

**Properties**:
- Simple states (e.g., product states): $C = O(1)$
- Highly entangled states (e.g., random states): $C = O(N_{\text{cell}})$

**Finite Information Constraint**:

Since $|\Theta_{\text{ini}}| < I_{\max}$, complexity cannot be too high:

$$
C(|\Psi_0\rangle) \lesssim I_{\max} / I_{\text{per-gate}}
$$

**Numerical Example**:
- $I_{\max} = 10^{123}$ bits
- Each gate encoding $\sim 100$ bits
- Maximum complexity: $C \lesssim 10^{121}$ layers

(Although still astronomical number, but much larger than $N_{\text{cell}} \sim 10^{90}$)

## Part VII: QCA Version of Hartle-Hawking No-Boundary State

### Classical Hartle-Hawking Proposal

**Quantum Cosmology** (Hartle-Hawking, 1983):

Universe wave function defined by path integral:

$$
|\Psi[h_{ij}, \phi] = \int_{\text{compact}} \mathcal{D}[g, \phi] \, e^{iS[g, \phi]/\hbar}
$$

where integral over "no-boundary" compact four-geometries.

**Physical Meaning**:
- Universe "spontaneously emerges", no initial singularity needed
- Time becomes "imaginary time" in very early universe (Euclidean geometry)
- Similar: Quantum tunneling

**Problems**:
- Path integral diverges on continuous geometries
- Need to introduce cutoff or regularization
- Wave function defined on infinite-dimensional superspace

### QCA Version: Minimum Depth Principle

In QCA framework, can similarly define:

**QCA No-Boundary Principle**:

Initial state $|\Psi_0\rangle$ chosen by following condition:

$$
\boxed{|\Psi_0\rangle = \arg\min_{V} \left\{ D(V) : V|0_\Lambda\rangle \text{ satisfies certain symmetry constraints} \right\}}
$$

where $D(V)$ is depth of circuit $V$.

**Physical Meaning**:
- Universe chooses "simplest" (minimum depth) initial state compatible with symmetries
- Similar: Principle of least action
- "Occam's razor": Simplest explanation without additional assumptions

**Example** (Translation-Invariant + Low Energy):

Constraints:
1. Translation invariance
2. Energy below threshold $E < E_0$

**Result**:
- Unique solution (in symmetry class): Ground state $|\text{GS}\rangle$
- Depth: $D = 0$ (if ground state = reference state) or $D = O(1)$

**Connection with IGVP**:

In GLS theory, IGVP (Information Geometric Variational Principle) derives Einstein's equations from entropy variation. Similarly:

$$
\delta S_{\text{complexity}} = 0 \Rightarrow \text{Choose minimum depth initial state}
$$

**Conjecture** (not strictly proven):
- Minimum complexity $\Leftrightarrow$ Maximum symmetry
- Maximum symmetry $\Rightarrow$ Near-uniform initial state of inflationary universe
- This perhaps explains why universe's initial state so "special" (low entropy)

## Part VIII: Measurement and Observation of Initial State Parameters

### How Do We Know Initial State?

**Question**: We are at moment $n \sim 10^{60}$ (universe age), how to infer initial state at $t=0$?

**Answer**: **Reverse inference** from current observations.

**Cosmic Microwave Background (CMB)**:
- Observation: Temperature fluctuations $\Delta T / T \sim 10^{-5}$ (anisotropy)
- Power spectrum: $C_\ell$ as function of $\ell$
- Inference: Initial density fluctuation spectrum $P(k)$

**Inflation Theory Predictions**:
- Near scale-invariant spectrum: $P(k) \propto k^{n_s}$, $n_s \approx 0.96$
- Gaussian distribution (minimal non-Gaussianity)
- Adiabatic fluctuations (not isocurvature)

**QCA Language Translation**:
- Near scale-invariant $\Rightarrow$ Initial state approximately translation-invariant in momentum space
- Gaussian $\Rightarrow$ Simple entanglement structure (near product state)
- Adiabatic $\Rightarrow$ Some symmetry (e.g., supersymmetry in early universe)

### "Archaeology" of Initial State Parameters

**Analogy**: Archaeologists infer ancient civilizations from relics.

| Archaeology | Cosmology |
|------------|----------|
| Relics (pottery, buildings) | CMB, large-scale structure |
| Stratigraphic age | Redshift $z$ |
| Infer ancient life | Infer initial state $\omega_0$ |
| Archaeological report | Parameter $\Theta_{\text{ini}}$ |

**Current Measurement Precision**:
- CMB temperature fluctuations: $\sim 10^{-6}$ K (Planck satellite)
- Large-scale structure: Galaxy surveys (SDSS, DES, LSST)
- Primordial gravitational waves: Not yet detected (target: $r \sim 10^{-3}$)

**Constraints on $\Theta_{\text{ini}}$**:
- Spectral index $n_s$: Constrains certain angle parameters
- Tensor-to-scalar ratio $r$: Constrains shape of inflation potential
- Non-Gaussianity $f_{\text{NL}}$: Constrains nonlinear interactions

**Future Prospects**:
- 21cm hydrogen line observations ("cosmic dawn")
- Primordial black hole detection
- Quantum gravity effects (possibly at very small scales)

## Summary of Core Points of This Article

### Definition of Initial State Parameters

$$
\Theta_{\text{ini}} = (D_{\text{ini}}, \{k_\ell\}, \{R_\ell\}, \{\theta_{\ell,j}\})
$$

**Generate Initial State**:
$$
|\Psi_0^{\Theta}\rangle = V_{\Theta_{\text{ini}}} |0_\Lambda\rangle
$$

### Reference Product State

$$
|0_\Lambda\rangle = \bigotimes_{x \in \Lambda} |0_{\text{cell}}\rangle_x
$$

**Properties**: No entanglement, translation-invariant, simple.

### Bit Count

| Component | Typical Value | Bit Count |
|-----------|--------------|-----------|
| Depth $D_{\text{ini}}$ | 5 | 3 |
| Gate type/layer | $K=16$ | 4 |
| Action region/layer | Translation-invariant | 1 |
| Angle parameters/layer | 2 angles, $m=50$ | 100 |
| **Total** | | **~530** |

$$
\boxed{|\Theta_{\text{ini}}| \sim 500 \text{ bits}}
$$

### Consequences of Finite Depth

**Lieb-Robinson Constraint**:
$$
I(A:B) \lesssim e^{-c(d - v_{\text{LR}} D_{\text{ini}})}
$$

**Physical Meaning**: Short-range entangled state, depth $D \sim \log N_{\text{cell}}$ sufficient.

### Symmetry Compression

**Translation-Invariant**:
- Encoding overhead: $O(1)$ (independent of $N_{\text{cell}}$)
- Compression ratio: $\sim 10^{90}$

### Initial State and Evolution

$$
\omega_n = \omega_0 \circ \alpha^{-n}
$$

**Complete Universe History**:
$$
\Theta = (\Theta_{\text{str}}, \Theta_{\text{dyn}}, \Theta_{\text{ini}}) \Rightarrow \text{Entire Universe Evolution}
$$

### Core Insights

1. **Initial state parameters tiny**: $|\Theta_{\text{ini}}| \sim 500 \ll I_{\max}$
2. **Symmetry necessary**: Translation-invariance → Information from $10^{90}$ reduced to $10^2$
3. **Short-range entanglement**: Finite depth → Long-range entanglement impossible
4. **Initial state inferable**: CMB and other observations → Constrain $\Theta_{\text{ini}}$
5. **No-boundary principle**: Minimum complexity → Naturally selects simple initial state

### Key Terminology

- **Reference Product State**: $|0_\Lambda\rangle$
- **State Preparation Circuit**: $V_{\Theta_{\text{ini}}}$
- **Short-Range Entanglement**: Entanglement range limitation due to finite depth
- **State Complexity**: $C = \min\{D\}$
- **Hartle-Hawking No-Boundary State**: QCA version of minimum depth principle

---

**Next Article Preview**: **06. Information-Entropy Inequality: Ultimate Constraint on Universe Scale**
- Detailed derivation of finite information inequality $I_{\text{param}} + S_{\max} \leq I_{\max}$
- Trade-off relation between number of cells $N_{\text{cell}}$ and local dimension $d_{\text{cell}}$
- Information budget allocation of observable universe
- Why symmetry, locality, finite precision are necessary
- Limitations of information constraints on physical theories

