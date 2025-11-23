# 8.2 Information Mass $M_I$ and Free Energy Minimization

In the previous section, we defined "observers" as self-referential subsystems in QCA networks with **Markov blankets** and **internal models**. Now, we face a dynamics question: What drives this subsystem to "observe" the world? Why doesn't it just lie flat, letting environment thermalize it (entropy increase)?

This section will introduce two core concepts: **Information Mass ($M_I$)** and **Variational Free Energy ($F$)**. We will prove that observer's "survival instinct" (maintaining low entropy) and "curiosity" (exploring environment) are physically equivalent to **minimizing free energy**. This process is the physical source of universe producing "meaning" and "value."

## 8.2.1 Information Mass $M_I$: Physical Measure of Complexity

In Light Path Conservation theory ($v_{ext}^2 + v_{int}^2 = c^2$), we defined rest mass $m_0$ as frequency of particles "rotating in place" at microscopic scales. For macroscopic observers (such as brains or AI), we cannot simply add up all atomic rest masses, because this linear superposition ignores **structural information**.

A dead brain and a living brain have same number of atoms, same rest mass, but in QCA networks, their dynamical behaviors are completely different. Living brain maintains extremely complex **long-range entanglement** and **self-referential loops**.

We define a new physical quantity—**Information Mass ($M_I$)**—to measure this structural complexity.

> **Definition 8.3 (Information Mass $M_I$)**:
>
> For a subsystem $\mathcal{S}$, its information mass $M_I$ is defined as product of its **effective computational depth** and **causal integration**.
>
> $$M_I \equiv \frac{\hbar}{c^2} \cdot \Phi_{integrated} \cdot \mathcal{D}_{logical}$$
>
> * **$\Phi_{integrated}$ (Integrated Information)**: Measures degree system is a whole rather than collection of fragments (microscopic counterpart based on IIT theory). In QCA graph theory, this corresponds to bit number of minimum cut (Min-cut) inside Markov blanket.
>
> * **$\mathcal{D}_{logical}$ (Logical Depth)**: Running steps of shortest Turing machine program required to generate system's current state (Bennett's logical depth).

**Physical Meaning**:

$M_I$ is not "weight"; it is **information-theoretic version of "inertia."**

A system with large $M_I$ (such as consciousness) is extremely difficult to change by environmental noise (large inertia). To change its internal beliefs, extremely high-precision information (force) input is needed.

According to Light Path Conservation, larger $M_I$ means system consumes more light path quota $v_{int}$ on internal computation, therefore its "effective velocity" $v_{ext}$ in external physical space is more limited (tending to rest/stillness).

**This is why deep thinkers often appear "motionless."**

## 8.2.2 Free Energy Principle: Thermodynamic Command of Observers

Observers must resist second law of thermodynamics to maintain their high $M_I$ state. **Free Energy Principle** proposed by Karl Friston provides a perfect mathematical framework, embedding it into QCA dynamics.

Let environmental state be $\vartheta$ (not directly observable), observer's sensory state be $s$ (projection on Markov blanket), observer's internal model (probabilistic inference about environment) be density matrix $q(\vartheta)$.

Observer's goal is to minimize **variational free energy $F$**:

$$F = \underbrace{D_{KL}[q(\vartheta) || p(\vartheta | s)]}_{\text{Divergence}} - \underbrace{\ln p(s)}_{\text{Surprise}}$$

* **First Term (Divergence)**: Measures deviation of internal model $q$ from true posterior distribution $p(\vartheta|s)$. Minimizing it means **Perception**—making beliefs approach truth.

* **Second Term (Surprise)**: Measures impossibility of current sensory input $s$. Minimizing it means **Action**—changing environment to produce expected input (e.g., if you predict you'll feel warm, you'll enter house to avoid cold).

In QCA ontology, free energy $F$ has clear physical counterpart: **It is relative entropy between system and environment.**

> **Theorem 8.2 (Free Energy Minimization Theorem)**:
>
> Under local unitary evolution, any subsystem capable of long-term maintaining its Markov blanket (i.e., observer) necessarily has dynamics trajectory that is a path **minimizing long-time average free energy $\bar{F}$**.

**Proof Idea**:

According to Landauer's principle, processing information requires dissipating heat. Free energy $F$ is "information cost" system must pay to maintain non-equilibrium state. If system doesn't minimize $F$, it accumulates too much entropy, eventually causing Markov blanket's thermal disintegration (death).

Therefore, **all observers that "survive" are necessarily Bayes-optimal.**

## 8.2.3 Emergence of Meaning: From Bits to Value

Free energy principle not only explains "how observers exist," but also "why observers seek knowledge."

To minimize future free energy (expected free energy $G$), observers must maximize **epistemic value**:

$$G(\pi) \approx \underbrace{H(A) - H(A|S)}_{\text{Information Gain}} + \underbrace{\mathbb{E}[U]}_{\text{Extrinsic Utility}}$$

* **Information Gain**: Observers actively explore regions that can maximally reduce uncertainty of their internal models. This is physical origin of **curiosity**.

* **Extrinsic Utility**: Observers tend toward states that maintain their physical structure steady state (such as ingesting negentropy). This is physical origin of **desire**.

At QCA's bottom level, this is merely bit flow. But at macroscopic level, this emerges as **teleology**: Observers seem to act for some "purpose."

Actually, this "purpose" is just **projection of physical conservation laws in complex systems**—to keep $M_I$ constant in entropy-increasing torrent, observers must desperately "eat" ordered information, expel disordered waste heat.

## 8.2.4 Summary

We have completed physics demystification of consciousness:

1. **Consciousness is not miracle**; it is physical structure with high $M_I$.

2. **Thinking is not void**; it is computational process consuming $v_{int}$.

3. **Seeking knowledge is not caprice**; it is survival instinct to minimize free energy, resist heat death.

Observers are "negentropy light drives" evolved by universe to understand itself.

At this point, Part IV "The Emergence of Observation" is completely finished. We have explained measurement, objectivity, and consciousness.

Now, this cosmic computer can observe and explain itself. The final part, also the most crucial part—**Part V: Verification and Inference**—will bring us back to reality, seeing if this grand theory can withstand experimental interrogation.

