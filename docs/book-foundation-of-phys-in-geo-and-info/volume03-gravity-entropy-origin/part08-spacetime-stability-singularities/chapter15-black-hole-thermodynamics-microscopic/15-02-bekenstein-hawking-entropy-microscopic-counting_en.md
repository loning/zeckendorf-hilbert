**15.2 Microscopic Counting Derivation of Bekenstein-Hawking Entropy $S=A/4G$**

In Section 15.1, we defined black hole horizons as **information truncation surfaces** in QCA networks and pointed out that black hole entropy arises from counting entanglement bonds crossing the horizon. Although this naturally derives the area law $S \propto A$, the proportionality coefficient $1/4$ has always been the holy grail of quantum gravity. In loop quantum gravity (LQG) or string theory, derivation of this coefficient often depends on specific microscopic model parameters (such as the Immirzi parameter).

This section will prove that in the unified framework of QCA discrete ontology and the Generalized Entropic Variational Principle (IGVP), the coefficient $1/4$ is locked by **Unitarity** and **consistency with general relativity** together, without introducing additional artificial parameters. We will perform precise microscopic state counting, showing how each QCA link severed by the horizon contributes exactly $1/4$ Planck area of entropy.

### 15.2.1 Microscopic Degrees of Freedom on Horizon: Spin Networks and Punctures

In the QCA universe graph $G = (\Lambda, E)$, the horizon $\Sigma$ is a two-dimensional closed surface that severs a series of edges connecting the inside and outside of the black hole. Let the total number of edges crossing the horizon be $N$.

Each edge $e_i$ carries a Hilbert space $\mathcal{H}_{e_i}$. For simplicity, assume the QCA is constructed based on $SU(2)$ spin networks, with each edge carrying spin quantum number $j_i$ (e.g., $j=1/2$ corresponds to fermionic QCA).

**Definition 15.2.1 (Puncture Area Spectrum)**

According to the area operator of loop quantum gravity, each puncture $p_i$ contributes to horizon area as:

$$
A_i = 8\pi l_P^2 \sqrt{j_i(j_i+1)}
$$

(Note: Here we adopt the standard LQG spectrum, but in the QCA framework, we can more generally assume each edge contributes a characteristic area $a_0$).

Total area is $A = \sum_{i=1}^N A_i \approx N \langle A \rangle$.

### 15.2.2 Microscopic Calculation of Entanglement Entropy

For external observers, each severed edge $e_i$ is an entanglement source. Assuming the QCA is in a typical entangled state (e.g., maximally entangled state or thermal state), the von Neumann entropy contributed by each edge is:

$$
S_i = \ln (\dim \mathcal{H}_{e_i})
$$

For an edge with spin $j_i$, the dimension is $2j_i + 1$.

Total entropy is:

$$
S_{BH} = \sum_{i=1}^N \ln (2j_i + 1)
$$

### 15.2.3 Holographic Logic of Coefficient Locking

Now we face a matching problem:

* **Geometric Side**: $A = 8\pi l_P^2 \gamma \sum \sqrt{j(j+1)}$ (where $\gamma$ is the Immirzi parameter).

* **Information Side**: $S = \sum \ln(2j+1)$.

For $S = A/4 l_P^2$ to hold, we must have:

$$
\frac{\ln(2j+1)}{8\pi \gamma \sqrt{j(j+1)}} = \frac{1}{4}
$$

In LQG, this is usually used to fix parameter $\gamma$. But in QCA discrete ontology, we have a deeper principle: **self-consistency of IGVP**.

Recalling Chapter 12, we derived Einstein's equations $G_{\mu\nu} = 8\pi G T_{\mu\nu}$ through $\delta S_{\text{gen}} = 0$. In this derivation, we used the first law of entanglement $\delta S = \delta \langle K \rangle$ and the area deficit theorem $\delta A \propto G_{00}$.

If in the derivation, the proportionality coefficient between $S$ and $A$ is not $1/4G$ but $\alpha/G$, then the derived field equations would be:

$$
G_{\mu\nu} = \frac{2\pi}{\alpha} G T_{\mu\nu}
$$

To recover the Newtonian gravity limit ($G_{00} \approx \nabla^2 \phi = 4\pi G \rho$), we must have $2\pi/\alpha = 8\pi$, i.e., $\alpha = 1/4$.

**Theorem 15.2.2 (Coefficient Locking Theorem)**

In QCA universes satisfying the low-energy limit of general relativity (i.e., Newtonian potential), the ratio of statistical entropy $S$ to geometric area $A$ for microscopic degrees of freedom on the horizon must be strictly locked to $1/4 l_P^2$. Any microscopic discrete model (such as choice of spin $j$ or lattice spacing $a$) must satisfy this ratio at the fixed point of the renormalization flow, otherwise the model will lead to incorrect macroscopic gravitational laws.

### 15.2.4 QCA's "Bit-Area" Correspondence

We can use this theorem in reverse to constrain the microscopic structure of QCA.

Assume QCA is composed of the simplest qubits ($j=1/2$, qubit).

* Dimension of each link $\dim = 2$, entropy contribution $\ln 2$.

* "Physical area" of each link should be $a_{qubit} = 4 l_P^2 \ln 2$.

This means that **Planck length $l_P$ itself is defined by the information density of qubits**.

$$
A = N \cdot (4 \ln 2) l_P^2 \implies S = N \ln 2 = \frac{A}{4 l_P^2}
$$

This is the geometric expression of **"It from Bit"**: spacetime area $A$ is nothing but a macroscopic measure of the underlying quantum entangled bit number $N$ (multiplied by constant $4 l_P^2 \ln 2$).

### 15.2.5 Saturation of Horizon as Holographic Screen

Why is the coefficient $1/4$ rather than $1$?

The factor $4$ suggests some **unavailability** or **redundancy** of spacetime degrees of freedom.

In some derivations of the holographic principle (such as 't Hooft's brick wall model), this factor originates from the **thermal atmosphere** of fields near the horizon.

From the QCA perspective, we can understand: although each Planck area unit can geometrically carry 1 bit of information, dynamically, to maintain unitary evolution and causal structure (light cones), only $1/4$ of the degrees of freedom are **active** and can be read by external observers as "entropy." The remaining degrees of freedom are "frozen" in short-range correlations of the vacuum and do not participate in long-range entanglement.

**Conclusion**

Bekenstein-Hawking entropy $S=A/4G$ is the inevitable statistical result of QCA discrete networks under constraints of Einstein's equations.

* **$S \propto A$**: Arises from QCA's local connectivity (boundary cutting).

* **Coefficient $1/4$**: Arises from self-consistency requirements of general relativity as entropic force dynamics (Newton constant matching).

This derivation does not require introducing D-branes of string theory or details of LQG spin networks; it is **universal**, applicable to any discrete quantum system that can emerge as classical gravity.

In the next section 15.3, we will further explore how this $1/4$ coefficient relates to unitarity (information conservation) and the Page curve, resolving the black hole information paradox.

