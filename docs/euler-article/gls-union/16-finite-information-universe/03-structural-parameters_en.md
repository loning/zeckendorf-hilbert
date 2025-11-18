# 03. Detailed Explanation of Structural Parameters: Discrete Blueprint of Spacetime

## Introduction: First Step of Building Blocks—Blueprint

In Article 02, we established triple decomposition of parameter vector $\Theta = (\Theta_{\text{str}}, \Theta_{\text{dyn}}, \Theta_{\text{ini}})$. Now we dive deep into first type of parameter: **Structural parameter** $\Theta_{\text{str}}$.

### Popular Analogy: Architectural Blueprint Determines Skeleton of House

Imagine building a castle with LEGO blocks. Before starting, you need an **architectural blueprint** answering following questions:

**Basic Questions**:
1. How many blocks? (Number of lattice points $N_{\text{cell}}$)
2. What type is each block? (Cell Hilbert space $\mathcal{H}_{\text{cell}}$)
3. How are blocks connected? (Graph structure, neighbor relations)
4. Built on plane or circular base? (Topology and boundary conditions)

**Advanced Questions**:
5. Do blocks have special symmetries? (e.g., mirror symmetry, rotation invariance)
6. Are some positions unable to place blocks? (Defects, non-uniform structure)

**Universe's situation completely analogous**:

Structural parameter $\Theta_{\text{str}}$ is universe's "LEGO blueprint", answering:
- How many "spacetime lattice points"? → Lattice set $\Lambda$
- What "internal structure" does each lattice point have? → Cell Hilbert space $\mathcal{H}_x$
- How are lattice points "connected"? → Graph structure $(\Lambda, E)$
- Is universe "open" or "closed"? → Boundary conditions
- What symmetries exist? → Symmetry group $G$

This article will explain these in detail.

## Part I: Construction of Lattice Set $\Lambda$

### Simplest Case: Regular Rectangular Lattice

**Definition 3.1** ($d$-Dimensional Rectangular Lattice):

$$
\Lambda = \prod_{i=1}^d \{0, 1, \ldots, L_i - 1\} = \mathbb{Z}_{L_1} \times \cdots \times \mathbb{Z}_{L_d}
$$

**Parameters**:
- Dimension $d \in \{1, 2, 3, 4, \ldots\}$
- Lattice lengths in each direction $L_1, \ldots, L_d \in \mathbb{N}$

**Total Number of Lattice Points**:
$$
N_{\text{cell}} = \prod_{i=1}^d L_i
$$

**Example 1** (One-Dimensional Chain):
$$
\Lambda = \{0, 1, \ldots, 99\} = \mathbb{Z}_{100}
$$
- $d=1$, $L_1 = 100$
- Total lattice points: $N_{\text{cell}} = 100$

**Example 2** (Two-Dimensional Square):
$$
\Lambda = \{0, \ldots, 999\} \times \{0, \ldots, 999\}
$$
- $d=2$, $L_1 = L_2 = 1000$
- Total lattice points: $N_{\text{cell}} = 10^6$

**Example 3** (Three-Dimensional Cube):
$$
\Lambda = \{0, \ldots, L-1\}^3
$$
- $d=3$, $L_1 = L_2 = L_3 = L$
- Total lattice points: $N_{\text{cell}} = L^3$

**Cosmological Scale** (in Planck length units $\ell_p \sim 10^{-35}\,\text{m}$):
- Observable universe radius: $R_{\text{uni}} \sim 10^{26}\,\text{m} = 10^{61} \ell_p$
- If three-dimensional cubic lattice: $L \sim 10^{61}$
- Total lattice points: $N_{\text{cell}} \sim (10^{61})^3 = 10^{183}$

(But this exceeds $I_{\max} \sim 10^{123}$! Will discuss how to reconcile later)

### Encoding Lattice Set

**Encoded Content** (part of $\Theta_{\text{str}}$):

1. **Dimension** $d$:
   - Use $\lceil \log_2 d_{\max} \rceil$ bits
   - If restrict $d \leq 16$ (sufficient for physics), need 4 bits

2. **Lattice Lengths in Each Direction** $L_1, \ldots, L_d$:
   - If each $L_i \leq 2^{64}$, each needs 64 bits
   - Total: $64d$ bits

**Bit Count**:
$$
I_{\Lambda} = 4 + 64d
$$

**Example** ($d=3$):
$$
I_{\Lambda} = 4 + 64 \times 3 = 196 \text{ bits}
$$

### Graph Structure and Neighbor Relations

Lattice set $\Lambda$ itself is just set of points. To define "which lattice points are neighbors", need **graph structure**.

**Definition 3.2** (Lattice Graph):

$$
\mathcal{G}_{\Lambda} = (\Lambda, E)
$$

where $E \subset \Lambda \times \Lambda$ is edge set, $(x, y) \in E$ means $x, y$ are neighbors.

**Standard Choice** (Rectangular Lattice):

**(1) Nearest-Neighbor Graph**:

$$
(x, y) \in E \quad \Leftrightarrow \quad \sum_{i=1}^d |x_i - y_i| = 1
$$

(Manhattan distance equals 1)

**Example** (Two-Dimensional Square):
- Nearest neighbors of point $(5, 7)$: $(4,7), (6,7), (5,6), (5,8)$ (4 neighbors)

**(2) Next-Nearest-Neighbor Graph**:

$$
(x, y) \in E \quad \Leftrightarrow \quad 1 \leq \sum_{i=1}^d |x_i - y_i| \leq 2
$$

**Example** (Two-Dimensional Square):
- Next-nearest neighbors of point $(5, 7)$: Besides 4 nearest neighbors, also 4 diagonal directions (total 8)

**(3) Chebyshev Graph**:

$$
(x, y) \in E \quad \Leftrightarrow \quad \max_{i=1}^d |x_i - y_i| = 1
$$

**Degree**:

Number of neighbors (degree $\deg(x)$) for each lattice point:
- One-dimensional nearest neighbor: $\deg = 2$ (interior points), $\deg=1$ (boundary points)
- Two-dimensional square nearest neighbor: $\deg = 4$ (interior), $\deg \in \{2,3\}$ (boundary)
- Three-dimensional cube nearest neighbor: $\deg = 6$ (interior)

**Encoding Graph Structure**:

For standard regular lattices, graph structure uniquely determined by **neighbor type**:
- "Nearest neighbor" → 1 bit encoding option
- "Next-nearest neighbor" → Another 1 bit
- Total: 2-3 bits

For non-regular graphs, need to encode adjacency matrix (expensive, usually avoided).

### Physical Meaning: Lattice Points = "Pixels" of Spacetime Events

**Classical Continuous Spacetime**:
- Events: $(t, x, y, z) \in \mathbb{R}^4$ (continuous)
- Uncountably infinite points

**Discrete QCA Spacetime**:
- Events: $x \in \Lambda \subset \mathbb{Z}^d$ (discrete)
- Finite number of lattice points $N_{\text{cell}}$

**Lattice Spacing** $a$:

$$
a = \frac{L_{\text{physical}}}{L_{\text{lattice}}}
$$

**Example**:
- Physical length: $L_{\text{physical}} = 1\,\text{m}$
- Number of lattice points: $L_{\text{lattice}} = 10^{35}$ (in Planck length units)
- Lattice spacing: $a = 10^{-35}\,\text{m} = \ell_p$

**Popular Analogy**:
- Continuous spacetime = Photo with infinite resolution
- QCA lattice = Pixels of digital photo
- Lattice spacing $a$ = Physical size represented by each pixel

## Part II: Cell Hilbert Space $\mathcal{H}_{\text{cell}}$

### Internal Degrees of Freedom of Single Cell

Each lattice point $x \in \Lambda$ carries a **finite-dimensional Hilbert space** $\mathcal{H}_x$.

**Definition 3.3** (Cell Hilbert Space):

$$
\mathcal{H}_x \cong \mathbb{C}^{d_{\text{cell}}}
$$

where $d_{\text{cell}} \in \mathbb{N}$ is cell dimension.

**Physical Meaning**:
- $d_{\text{cell}}$: How many "internal quantum states" each lattice point has
- Analogy: How many color channels each pixel has (RGB = 3 channels)

### Physical Origin of Cell Dimension

In real physics, $\mathcal{H}_{\text{cell}}$ usually decomposes as tensor product of multiple subsystems:

$$
\boxed{\mathcal{H}_{\text{cell}} = \mathcal{H}_{\text{fermion}} \otimes \mathcal{H}_{\text{gauge}} \otimes \mathcal{H}_{\text{aux}}}
$$

#### (1) Fermion Degrees of Freedom $\mathcal{H}_{\text{fermion}}$

**Simplest** (Dirac-QCA):
$$
\mathcal{H}_{\text{fermion}} = \mathbb{C}^2
$$
- Basis: $\{|\uparrow\rangle, |\downarrow\rangle\}$ (spin up/down)
- Dimension: $\dim \mathcal{H}_{\text{fermion}} = 2$

**Standard Model** (3 generations leptons+quarks):
- Leptons: Electron, muon, tau (each with neutrino) → 6 types
- Quarks: Up, down, strange, charm, bottom, top → 6 types
- Spin: Up/down → 2 types
- Particle/antiparticle → 2 types
- Total: $(6+6) \times 2 \times 2 = 48$

But considering color charge (quarks have 3 colors):
$$
\dim \mathcal{H}_{\text{fermion}} \sim 3 \times 6 \times 2 \times 2 = 72
$$

(Actually need more refined Fock space construction)

#### (2) Gauge Field Degrees of Freedom $\mathcal{H}_{\text{gauge}}$

**Electromagnetic Field** (U(1)):
- Photon: 2 polarization states
- Dimension: $\dim \mathcal{H}_{\text{gauge}}^{\text{EM}} = 2$

**Non-Abelian Gauge Fields** (SU(N)):
- Gluons (SU(3) color gauge): 8 gluons × 2 polarizations = 16 states
- Weak gauge bosons (SU(2)): 3 bosons (W⁺, W⁻, Z) × 2 polarizations = 6 states

**Combined** (Standard Model SU(3)×SU(2)×U(1)):
$$
\dim \mathcal{H}_{\text{gauge}} \sim 16 + 6 + 2 = 24
$$

#### (3) Auxiliary Qubits $\mathcal{H}_{\text{aux}}$

**Why Needed**: To ensure **reversibility** of QCA evolution.

**Principle** (Bennett garbage bits):
Classical reversible computation needs "garbage registers" to store intermediate results, quantum QCA similar.

**Dimension Estimate**:
If main degrees of freedom have $d_{\text{main}}$ states, auxiliary qubits usually need $d_{\text{aux}} \sim \log_2 d_{\text{main}}$.

**Standard Model QCA**:
- Main degrees of freedom: $d_{\text{main}} \sim 72 \times 24 \sim 1700$
- Auxiliary qubits: $d_{\text{aux}} \sim \log_2 1700 \sim 11$ → $2^{11} = 2048$

**Total Cell Dimension**:
$$
d_{\text{cell}} = d_{\text{fermion}} \times d_{\text{gauge}} \times d_{\text{aux}} \sim 72 \times 24 \times 2048 \sim 3.5 \times 10^6
$$

(This is Hilbert space dimension of **single lattice point**!)

### Encoding Cell Hilbert Space

**Method 1** (Direct Encoding of Dimension):
- Store $d_{\text{cell}}$
- Need $\lceil \log_2 d_{\text{cell}} \rceil$ bits
- Example: $d_{\text{cell}} = 3.5 \times 10^6$ → $\log_2(3.5 \times 10^6) \approx 22$ bits

**Method 2** (Decomposition Encoding):
- Separately store $d_{\text{fermion}}, d_{\text{gauge}}, d_{\text{aux}}$
- Total bits: $\log_2 d_{\text{fermion}} + \log_2 d_{\text{gauge}} + \log_2 d_{\text{aux}}$
- Example: $\log_2 72 + \log_2 24 + \log_2 2048 = 7 + 5 + 11 = 23$ bits

**Method 3** (Specify Physical Model):
- Encode "Standard Model" (string)
- Dimension implicit in model
- Need: $\sim 50$ bits (encode model name+parameters)

**Usually Choose**: Method 3 (Physical model encoding)

**Bit Count**:
$$
I_{\mathcal{H}} \sim 50 \text{ bits}
$$

### Tensor Product of Global Hilbert Space

**Definition 3.4** (Global Hilbert Space):

$$
\boxed{\mathcal{H}_{\Lambda} = \bigotimes_{x \in \Lambda} \mathcal{H}_x}
$$

**Dimension**:
$$
\dim \mathcal{H}_{\Lambda} = \prod_{x \in \Lambda} d_{\text{cell}}(x) = d_{\text{cell}}^{N_{\text{cell}}}
$$

(Assuming cell dimensions same at all lattice points)

**Numerical Example** (Cosmological Scale):
- $d_{\text{cell}} = 10^6$
- $N_{\text{cell}} = 10^{90}$ (Observable universe in Planck units)
- $\dim \mathcal{H}_{\Lambda} = (10^6)^{10^{90}} = 10^{6 \times 10^{90}}$

This is a **double exponential** large number!

**Maximum Entropy** (Information Capacity):
$$
S_{\max} = \log_2 \dim \mathcal{H}_{\Lambda} = N_{\text{cell}} \log_2 d_{\text{cell}}
$$

**Example**:
- $N_{\text{cell}} = 10^{90}$, $d_{\text{cell}} = 10^6$
- $S_{\max} = 10^{90} \times \log_2(10^6) = 10^{90} \times 20 = 2 \times 10^{91}$ bits

(Far exceeds $I_{\max} \sim 10^{123}$, meaning universe cannot "fill" entire Hilbert space!)

## Part III: Boundary Conditions and Topology

### Why Need Boundary Conditions?

Lattice set $\Lambda$ is finite, necessarily has "boundary". How boundary is handled affects physical properties.

**Classical Analogy**:
- Open system: Energy can flow in/out (open boundary)
- Closed system: Energy conserved (periodic boundary)

### Open Boundary Conditions

**Definition 3.5** (Open Boundary):

Boundary lattice points only have partial neighbors (interior lattice points have normal number of neighbors).

**One-Dimensional Example**:
$$
\Lambda = \{0, 1, 2, \ldots, L-1\}
$$
- Boundaries: $x=0, x=L-1$
- Interior: $x \in \{1, \ldots, L-2\}$

**Neighbor Structure**:
- $x=0$: Only right neighbor $x=1$
- $x=L-1$: Only left neighbor $x=L-2$
- $x \in \{1, \ldots, L-2\}$: Both left and right neighbors

**Physical Meaning**:
- Boundary is "real" (e.g., container wall)
- Quantum states can reflect or absorb at boundary
- **Boundary effects** significant (when $L$ not large enough)

**Encoding**:
- For each direction specify "open" → 1 bit/direction
- Total: $d$ bits

### Periodic Boundary Conditions

**Definition 3.6** (Periodic Boundary):

Boundary lattice points connect to opposite side through "wrapping".

**One-Dimensional Example**:
$$
\Lambda = \mathbb{Z}_L = \{0, 1, \ldots, L-1\}
$$

**Neighbor Structure** (Nearest Neighbor):
- $x=0$: Left neighbor is $x=L-1$, right neighbor is $x=1$
- $x=L-1$: Left neighbor is $x=L-2$, right neighbor is $x=0$
- (Forms a "ring")

**Topology**:
- One-dimensional periodic: Circle $S^1$
- Two-dimensional periodic: Torus $\mathbb{T}^2 = S^1 \times S^1$
- Three-dimensional periodic: Three-dimensional torus $\mathbb{T}^3$

**Physical Meaning**:
- Eliminates boundary effects
- Preserves translation symmetry
- Simulates "infinitely large" system (when $L$ large enough)

**Encoding**:
- For each direction specify "periodic" → 1 bit/direction
- Total: $d$ bits

**Popular Analogy**:
- **Open boundary**: Walking on flat map, stop at edge
- **Periodic boundary**: In game "Snake", snake exits right side, re-enters from left

### Twisted Boundary Conditions

**Definition 3.7** (Twisted Boundary):

Apply a phase or symmetry transformation when wrapping.

**One-Dimensional Example** (Anti-Periodic):
$$
\psi(L) = -\psi(0)
$$

(Wave function changes sign when wrapping)

**Physical Meaning**:
- Fermions: Usually use anti-periodic boundary (Pauli exclusion principle)
- Bosons: Use periodic boundary
- Topological phases: Need twisted boundary to detect topological invariants

**Encoding**:
- Specify twist type (none, anti-periodic, U(1) phase) → 2 bits/direction
- Total: $2d$ bits

### Non-Trivial Topology

**Example 1** (Three-Dimensional Sphere $S^3$):
- Closed, no boundary
- Need special lattice gluing

**Example 2** (RP³, Manifolds):
- Complex topological invariants
- Need additional encoding of gluing maps

**Encoding Overhead**:
- Simple topology ($\mathbb{R}^d$, $\mathbb{T}^d$, $S^d$): $\sim 10$ bits
- Complex topology (arbitrary manifolds): $\sim 100$ bits (Morse theory, CW complexes)

**Cosmological Application**:
- Observable universe topology unknown (may be $\mathbb{R}^3$, $\mathbb{T}^3$, hyperbolic space...)
- $\Theta_{\text{str}}$ needs to encode topology type

### Bit Count of Boundary Conditions

$$
I_{\text{boundary}} \sim 2d \text{ bits}
$$

(Assuming standard or twisted periodic boundary)

**Example** ($d=3$):
$$
I_{\text{boundary}} = 6 \text{ bits}
$$

## Part IV: Symmetries and Conservation Laws

### Why Are Symmetries Important?

Physical laws usually have symmetries:
- **Time translation symmetry** → Energy conservation
- **Space translation symmetry** → Momentum conservation
- **Rotation symmetry** → Angular momentum conservation
- **Gauge symmetry** → Charge conservation

In QCA framework, symmetries encoded in $\Theta_{\text{str}}$, affecting representation-theoretic structure of $\mathcal{H}_{\text{cell}}$.

### Global Symmetry Group $G_{\text{global}}$

**Definition 3.8** (Global Symmetry):

A unitary representation $\rho: G \to U(\mathcal{H}_{\text{cell}})$ such that dynamics remains unchanged.

**Example 1** (U(1) Symmetry):
- Particle number conservation
- Group: $G = U(1) = \{e^{i\theta} : \theta \in [0, 2\pi)\}$
- Representation: $\rho(e^{i\theta}) = e^{i\theta \hat{N}}$ ($\hat{N}$ is particle number operator)

**Example 2** (SU(2) Spin Symmetry):
- Rotation invariance
- Group: $G = SU(2)$
- Representation: Spin-1/2, spin-1, etc.

**Example 3** (Z₂ Symmetry):
- Parity symmetry ($x \to -x$)
- Group: $G = \mathbb{Z}_2 = \{+1, -1\}$
- Representation: $\rho(-1) = P$ (parity operator)

### Local Gauge Symmetry $G_{\text{local}}$

**Definition 3.9** (Gauge Symmetry):

Symmetry transformations acting independently at each lattice point, physical states equivalent under gauge transformations.

**Standard Model**:
$$
G_{\text{local}} = SU(3)_{\text{color}} \times SU(2)_{\text{weak}} \times U(1)_Y
$$

- SU(3): Color gauge symmetry (strong interaction)
- SU(2): Weak isospin symmetry
- U(1): Hypercharge symmetry

**Physical Hilbert Space**:
Need states satisfying **Gauss law** (gauge constraints).

**Example** (Lattice Gauge Theory):
- Place gauge field variables $U_e \in SU(N)$ on each edge
- Physical states satisfy: $\prod_{e \text{ out of } x} U_e = \mathbb{1}$ (at each lattice point)

### Encoding Symmetries

**Encoded Content**:

1. **Symmetry Group Type**:
   - "U(1)", "SU(2)", "SU(3)", ...
   - Use string or enumeration type → $\sim 20$ bits

2. **Representation Choice**:
   - Fundamental representation, adjoint representation, spin-$j$ representation...
   - Each representation $\sim 10$ bits

3. **How Acts on $\mathcal{H}_{\text{cell}}$**:
   - Specify matrix representation of generators on basis vectors
   - For standard groups (U(1), SU(2), SU(3)), can preset
   - Additional encoding $\sim 10$ bits

**Total Bits**:
$$
I_{\text{symmetry}} \sim 20 + 10 + 10 = 40 \text{ bits}
$$

(For single symmetry group)

**Standard Model** (SU(3)×SU(2)×U(1)):
$$
I_{\text{symmetry}} \sim 3 \times 40 = 120 \text{ bits}
$$

### Symmetries and Information Compression

**Key Insight**: Symmetries can **greatly compress** parameter information!

**Example** (Translation Invariance):

**Without Symmetry**:
- Hamiltonian parameters at each lattice point independent → $N_{\text{cell}}$ sets of parameters
- Information: $\sim N_{\text{cell}} \times I_{\text{local}}$

**With Translation Symmetry**:
- All lattice point Hamiltonians same → Only need 1 set of parameters
- Information: $\sim I_{\text{local}}$

**Compression Ratio**: $N_{\text{cell}}$ (astronomical number!)

**Physical Necessity**:
If universe had no symmetry, parameter information needed would exceed $I_{\max}$ → Contradiction

Therefore: **Symmetry is not coincidence, but necessary consequence of finite information axiom!**

## Part V: Defects and Non-Uniform Structure

### Topological Defects

**Definition 3.10** (Topological Defect):

Positions in space where field configuration or geometry has singularity, cannot be eliminated by continuous deformation.

**Example 1** (Cosmic String):
- One-dimensional defect ("string" in three-dimensional space)
- Field configuration gains non-trivial phase when circling string once
- Produces conical geometry (deficit angle)

**Example 2** (Magnetic Monopole):
- Zero-dimensional defect ("point")
- Gauge field at infinity similar to magnetic monopole field
- Dirac quantization condition

**Example 3** (Domain Wall):
- Two-dimensional defect ("wall" in three-dimensional space)
- Vacuum states on two sides different (spontaneous symmetry breaking)

### Encoding Defects in QCA

**Method 1** (Position List):
- Defect positions: $(x_1, y_1, z_1), (x_2, y_2, z_2), \ldots$
- Each coordinate $\sim 3 \times \log_2 L$ bits
- $k$ defects: $\sim k \times 3 \log_2 L$ bits

**Method 2** (Field Configuration Encoding):
- Near defects, field configuration special
- Encode defect type (string, monopole, domain wall) + orientation
- Each defect $\sim 50$ bits

**Cosmology** (Post-Inflation Remnants):
- Inflation theory predicts: Universe may have $\sim 0$ large-scale defects (diluted by inflation)
- Or $\sim 10$ defects (formed during phase transition)

**Encoding Overhead**:
$$
I_{\text{defect}} \sim k_{\text{defect}} \times 50 \text{ bits}
$$

**Example** ($k_{\text{defect}} = 0$):
$$
I_{\text{defect}} = 0 \text{ bits}
$$

(Uniform universe, no defects)

### Non-Uniform Lattice Lengths (Refinement)

**Motivation**: Some regions need higher resolution.

**Example** (Astronomy):
- Near galaxy clusters: High resolution ($a \sim 10^{-10} \ell_p$)
- Interstellar space: Low resolution ($a \sim 10^{-5} \ell_p$)

**Implementation** (Adaptive Grid):
- "Subdivide" some coarse lattice points into $2^d$ sub-lattice points
- Recursive subdivision

**Encoding**:
- Subdivision tree structure (like quadtree/octree)
- Each subdivision decision $\sim 1$ bit
- If subdivide $k_{\text{refine}}$ times: $\sim k_{\text{refine}}$ bits

**Cosmological Application**:
- Observations show universe **large-scale uniform** (CMB fluctuations $\sim 10^{-5}$)
- Non-uniform structure mainly at small scales (galaxies, stars)
- If use coarse-graining, small scales emerge
- $\Theta_{\text{str}}$ can only encode large-scale uniform lattice

**Typical Value**:
$$
I_{\text{refine}} \sim 0 \text{ bits}
$$

(Uniform lattice sufficient)

## Part VI: Total Bit Count of Structural Parameters

Combining above parts:

$$
\boxed{|\Theta_{\text{str}}| = I_{\Lambda} + I_{\mathcal{H}} + I_{\text{boundary}} + I_{\text{symmetry}} + I_{\text{defect}} + I_{\text{refine}}}
$$

**Numerical Table** (Standard Universe QCA):

| Item | Content | Bit Count |
|------|---------|-----------|
| $I_{\Lambda}$ | Dimension + Lattice lengths | $4 + 64 \times 3 = 196$ |
| $I_{\mathcal{H}}$ | Cell Hilbert space | 50 |
| $I_{\text{boundary}}$ | Boundary conditions | $2 \times 3 = 6$ |
| $I_{\text{symmetry}}$ | Symmetry groups | 120 |
| $I_{\text{defect}}$ | Topological defects | 0 |
| $I_{\text{refine}}$ | Non-uniform refinement | 0 |
| **Total** | | **372** |

**Key Observation**:
$$
|\Theta_{\text{str}}| \sim 400 \text{ bits} \ll I_{\max} \sim 10^{123} \text{ bits}
$$

Structural parameter information **extremely small**!

## Part VII: Construction of Quasi-Local $C^*$ Algebra

### From Lattice Points to Algebra

With lattice set $\Lambda$ and cell Hilbert space $\mathcal{H}_x$, can construct **quasi-local operator algebra**.

**Definition 3.11** (Local Algebra):

For finite subset $F \subset \Lambda$, define:

$$
\mathcal{H}_F = \bigotimes_{x \in F} \mathcal{H}_x
$$

$$
\mathcal{A}_F = \mathcal{B}(\mathcal{H}_F)
$$

(All bounded operators on $\mathcal{H}_F$)

**Embedding**:

If $F \subset F'$, then $\mathcal{A}_F \subset \mathcal{A}_{F'}$ through:

$$
\iota_{F \subset F'}(A_F) = A_F \otimes \mathbb{1}_{F' \setminus F}
$$

(Act as identity outside $F$)

**Definition 3.12** (Quasi-Local $C^*$ Algebra):

$$
\boxed{\mathcal{A}(\Lambda) = \overline{\bigcup_{F \Subset \Lambda} \mathcal{A}_F}^{\|\cdot\|}}
$$

(Closure of all local operators, in operator norm)

**Physical Meaning**:
- $\mathcal{A}(\Lambda)$: All "local observables"
- Observables act on finite regions, but can be arbitrarily large

### State Space

**Definition 3.13** (State):

State is positive, normalized linear functional on $\mathcal{A}(\Lambda)$:

$$
\omega: \mathcal{A}(\Lambda) \to \mathbb{C}
$$

Satisfying:
- Positivity: $\omega(A^\dagger A) \geq 0$
- Normalization: $\omega(\mathbb{1}) = 1$

**Pure and Mixed States**:
- Pure state: $\omega(A) = \langle \psi | A | \psi \rangle$ (some vector state)
- Mixed state: $\omega(A) = \text{tr}(\rho A)$ (density matrix)

**State Space Dimension**:
$$
\dim(\text{pure state manifold}) = 2 \dim \mathcal{H}_{\Lambda} - 2 = 2 d_{\text{cell}}^{N_{\text{cell}}} - 2
$$

(Real dimension of complex projective space $\mathbb{CP}^{d-1}$)

This is **double exponential** large!

### Relationship Between $C^*$ Algebra and Finite Information

**Key Theorem**:

On finite-dimensional $\mathcal{H}_{\Lambda}$, $\mathcal{A}(\Lambda) = \mathcal{B}(\mathcal{H}_{\Lambda})$ is also finite-dimensional:

$$
\dim_{\mathbb{C}} \mathcal{A}(\Lambda) = (\dim \mathcal{H}_{\Lambda})^2 = d_{\text{cell}}^{2N_{\text{cell}}}
$$

**Information Content**:
$$
\log_2 \dim \mathcal{A}(\Lambda) = 2 N_{\text{cell}} \log_2 d_{\text{cell}} = 2 S_{\max}
$$

But **number of physically observable operators** far less than $\dim \mathcal{A}$, because:
- Symmetry constraints (gauge invariant, translation invariant)
- Locality (experiments can only measure local operators)

**Effective Information**:
$$
I_{\text{eff}}^{\text{obs}} \ll 2 S_{\max}
$$

(Usually $\sim S_{\max}$ or less)

## Summary of Core Points of This Article

### Five Components of Structural Parameters

$$
\Theta_{\text{str}} = (\Lambda, \mathcal{H}_{\text{cell}}, \text{boundary}, G_{\text{symm}}, \text{defects})
$$

| Component | Physical Meaning | Typical Bit Count |
|-----------|-----------------|------------------|
| $\Lambda$ | Lattice set (dimension+lattice lengths+graph) | 200 |
| $\mathcal{H}_{\text{cell}}$ | Cell internal degrees of freedom | 50 |
| Boundary conditions | Open/periodic/twisted | 6 |
| Symmetry groups | Global/gauge symmetry | 120 |
| Defects | Topological defects, non-uniform | 0 |
| **Total** | | **~400** |

### Global Hilbert Space

$$
\mathcal{H}_{\Lambda} = \bigotimes_{x \in \Lambda} \mathcal{H}_x, \quad \dim \mathcal{H}_{\Lambda} = d_{\text{cell}}^{N_{\text{cell}}}
$$

**Maximum Entropy**:
$$
S_{\max} = N_{\text{cell}} \log_2 d_{\text{cell}}
$$

**Numerical Example** (Cosmological):
- $N_{\text{cell}} \sim 10^{90}$, $d_{\text{cell}} \sim 10^6$
- $S_{\max} \sim 2 \times 10^{91}$ bits

### Quasi-Local $C^*$ Algebra

$$
\mathcal{A}(\Lambda) = \overline{\bigcup_{F \Subset \Lambda} \mathcal{B}(\mathcal{H}_F)}^{\|\cdot\|}
$$

**Physical Meaning**: Set of all local observables.

### Core Insights

1. **Structural parameters tiny**: $|\Theta_{\text{str}}| \sim 400 \ll I_{\max} \sim 10^{123}$
2. **State space huge**: $S_{\max} \sim 10^{91}$ dominates information capacity
3. **Symmetry necessary**: No symmetry → Parameter explosion → Exceeds $I_{\max}$
4. **Finite information forces discreteness**: Continuous spacetime needs infinite information → Must discretize
5. **Lattice spacing $a$ and physical scale**: $a \sim \ell_p$ (Planck length) is natural unit

### Relationship with Continuous Field Theory

| Continuous Field Theory | QCA Discrete Realization |
|-------------------------|------------------------|
| Spacetime manifold $M$ | Lattice set $\Lambda$ |
| Point $x \in M$ | Lattice point $x \in \Lambda$ |
| Field $\phi(x)$ | Cell state $\psi_x \in \mathcal{H}_x$ |
| Field operator $\hat{\phi}(x)$ | Cell operator $A_x \in \mathcal{B}(\mathcal{H}_x)$ |
| Infinite degrees of freedom | Finite $N_{\text{cell}}$ lattice points |
| Continuous symmetry | Discrete symmetry (finite precision) |

**Continuous Limit** (Article 07 will detail):
$$
a, \Delta t \to 0 \Rightarrow \text{QCA} \to \text{Field Theory}
$$

---

**Next Article Preview**: **04. Detailed Explanation of Dynamical Parameters: Source Code of Physical Laws**
- Construction of QCA automorphism $\alpha_{\Theta}$
- Finite depth local unitary circuits
- Gate set $\mathcal{G}$ and universality
- Discrete angle parameters $\theta \to 2\pi n/2^m$
- Lieb-Robinson bound and light cone
- From discrete gates to continuous Hamiltonian

