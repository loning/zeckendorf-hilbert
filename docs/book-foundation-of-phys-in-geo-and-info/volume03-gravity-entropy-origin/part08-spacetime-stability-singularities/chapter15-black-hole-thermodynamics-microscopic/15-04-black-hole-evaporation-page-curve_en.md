**15.4 Black Hole Evaporation and Page Curve: Information Recovery Mechanism under QCA Unitary Evolution**

In Sections 15.1 to 15.3, we established the microscopic origin of black hole entropy and the holographic necessity of the coefficient $1/4$. However, the most severe challenge in black hole physics is not the static entropy formula, but the dynamic **Black Hole Information Paradox**. Hawking's semiclassical calculation in 1976 showed that black hole radiation is purely thermal, meaning black hole evaporation is a non-unitary process, and pure quantum information of the initial state seems permanently destroyed at the singularity.

This section will use the strict unitarity of QCA discrete ontology to prove that information conservation is an inevitable result of QCA dynamics. We will show that black hole horizons are not information devourers, but **information scramblers** and **re-radiators**. By modeling black hole evaporation as dynamic evolution of subsystem dimensions in QCA networks, we will derive the famous **Page curve**, revealing how information is precisely recovered in the late stages of evaporation.

### 15.4.1 Essence of the Paradox: Failure of Semiclassical Approximation

Hawking's original calculation was based on quantum field theory (QFT) evolution on a fixed curved spacetime background. Under this approximation, the horizon produces entangled pairs $(b_{in}, b_{out})$. $b_{in}$ falls into the singularity, $b_{out}$ escapes. Since $b_{in}$ degrees of freedom continuously accumulate and never return, the entanglement entropy of external radiation $S_{rad}$ monotonically increases with time. When the black hole completely evaporates and disappears, $S_{rad}$ remains large, causing pure states to evolve into mixed states.

In QCA universes, this picture is wrong for two reasons:

1. **Singularities Don't Exist**: As described in Section 14.4, singularities are cut off by information saturation mechanisms. Internal degrees of freedom do not "fall out" of the universe, but remain trapped in high-density QCA cores.

2. **Background Not Fixed**: QCA evolution operator $U$ simultaneously updates geometry (connection structure) and matter. As radiation carries away energy, the QCA subgraph size $N_{BH}$ corresponding to the black hole must decrease.

### 15.4.2 QCA Model of Black Hole Evaporation

We decompose the total universe Hilbert space $\mathcal{H}$ into two parts:

$$
\mathcal{H} = \mathcal{H}_{BH}(t) \otimes \mathcal{H}_{rad}(t)
$$

where $\mathcal{H}_{BH}$ is the set of QCA nodes inside the horizon, and $\mathcal{H}_{rad}$ is the escaped radiation modes outside the horizon.

As evaporation proceeds, discrete time step $n$ increases, $\dim \mathcal{H}_{BH}$ decreases, $\dim \mathcal{H}_{rad}$ increases, but total dimension $D = \dim \mathcal{H}$ remains constant (assuming the universe is a closed system).

**Axiom 15.4.1 (QCA Local Scrambling Hypothesis)**

The QCA dynamics $U_{BH}$ inside the black hole is highly chaotic (Fast Scrambler). After a short **scrambling time** ($t_{scr} \sim \log N_{BH}$), the internal state of the black hole is approximately a **Haar random state** for any local observer.

This means information inside the black hole is rapidly smeared across the entire horizon surface and randomly leaks out through coupling $U_{int}$ with external radiation modes.

### 15.4.3 Rigorous Derivation of Page Curve

Based on the above assumption, we can directly apply Don Page's (1993) entropy theorem for random quantum systems.

**Theorem 15.4.2 (QCA Radiation Entropy Theorem)**

Let the total system be in pure state $|\Psi\rangle$. The von Neumann entropy $S_{rad}(t)$ of radiation subsystem $\mathcal{H}_{rad}$ is determined by the ratio of dimensions of the two subsystems:

$$
S_{rad}(t) \approx \min \left( S_{BH}(t), S_{rad}^{therm}(t) \right)
$$

where $S_{BH} \propto \text{Area}$ is the current coarse-grained entropy (capacity) of the black hole, and $S_{rad}^{therm} \propto t$ is the accumulated thermodynamic entropy of radiation (if entanglement is not considered).

**Evolution Stages**:

1. **Early ($t < t_{Page}$)**: $\dim \mathcal{H}_{rad} \ll \dim \mathcal{H}_{BH}$.

   The black hole interior is a huge "entanglement reservoir." Newly produced radiation particles are highly entangled with the black hole interior. Entropy $S_{rad}$ increases linearly with number of radiated particles, manifesting as thermal radiation.

   $$
   S_{rad}(t) \approx \beta E_{rad}(t)
   $$

2. **Page Time ($t = t_{Page}$)**: $\dim \mathcal{H}_{rad} \approx \dim \mathcal{H}_{BH}$.

   When the black hole has evaporated half its degrees of freedom (approximately half the initial area), entropy reaches maximum $S_{max} \approx A_0 / 4G$.

3. **Late ($t > t_{Page}$)**: $\dim \mathcal{H}_{rad} \gg \dim \mathcal{H}_{BH}$.

   At this point, remaining degrees of freedom inside the black hole are insufficient to support independent entanglement with external radiation. According to Schmidt decomposition, entanglement entropy is limited by the dimension of the smaller system:

   $$
   S_{rad}(t) = S_{BH}(t) \le \frac{A(t)}{4G}
   $$

   As black hole area $A(t)$ decreases, $S_{rad}(t)$ is forced to decrease. This means newly radiated particles not only don't increase entanglement, but actually reduce total system entropy by carrying correlations with early radiation (Purifying Partners).

4. **Final State**: Black hole disappears, $A \to 0$, then $S_{rad} \to 0$. Radiation as a whole returns to pure state.

This inverted V-shaped entropy evolution curve is the **Page curve**.

### 15.4.4 Microscopic Mechanism of Information Recovery: Holographic Channels

In the QCA picture, how does information "escape" the horizon? This relies on the property of the horizon as a **holographic channel**.

In Section 15.2, we proved that each Planck area element on the horizon corresponds to an entanglement channel.

* In early stages, these channels are mainly used to establish new entanglement (emitting thermal photons).

* In late stages (after Page time), the black hole interior is highly mixed. Any new information falling into the black hole quickly becomes entangled with the entire horizon.

* The next emitted photon, its microscopic state $\rho_{out}$ actually carries subtle imprints of internal states. Since internal states are already highly correlated with early radiation, this new photon actually acts as a **key** for early radiation.

**Definition 15.4.3 (Black Hole as Mirror)**

In late QCA stages, the black hole acts as a quantum mirror. If we collect all early radiation and perform joint measurements (decoding operations) with newly emitted photons, we can reconstruct the information that originally fell into the black hole with extremely high fidelity. The information release rate is approximately 1 bit of information per 1 bit of energy emitted.

### 15.4.5 Victory of Unitarity and Resolution of Firewall

Traditional Page curve derivations once triggered the "firewall paradox" (AMPS Paradox): if late radiation must be entangled with early radiation (to reduce entropy), it cannot simultaneously be entangled with the black hole interior (violating entanglement monogamy). This seems to mean entanglement must be cut at the horizon, forming a high-energy firewall.

In the QCA framework, this paradox is resolved through **non-local connections** or **wormhole geometry**.

According to the **ER=EPR** conjecture to be discussed in Chapter 17, the black hole interior and early radiation are connected through microscopic wormholes (non-local links in QCA networks).

* **Physical Space**: Radiation is outside the black hole, far away.

* **Information Space**: On the QCA topological graph, late radiation is produced at the horizon edge, while early radiation is tightly connected to the horizon interior through wormholes.

Therefore, local operations near the horizon actually always act on a connected quantum network, achieving information transfer without destroying horizon smoothness (i.e., no firewall needed).

**Conclusion**

The Page curve is a direct corollary of unitary evolution in QCA universes.

1. **Conservation**: Information is never lost, only scrambled into complex radiation entangled states.

2. **Recovery**: The horizon is a unitary encoder. As long as enough radiation is collected (beyond Page time), information can be decoded.

3. **Consistency**: The finite dimension of QCA models makes infinite entropy increase impossible, forcing entropy decrease, thereby saving quantum mechanics.

At this point, we have completed the microscopic reconstruction of black hole thermodynamics. We proved that black holes are normal physical systems following quantum statistical laws, and their mysterious area-law entropy and information paradoxes all stem from our neglect of the discrete nature and holographic properties of spacetime.

In the upcoming **Part IX: Geometric Unification of Interactions**, we will leave individual black holes to explore grander questions: How to unify gravity with other forces in the Standard Model (gauge fields) in the same geometric framework? This will lead to the modern revival of Kaluza-Klein theory—**Total Space Geometry**.

