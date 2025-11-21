# Chapter 19: Self-referential Dynamics and Predictive Coding

In Chapter 18, we established the static algebraic structure of observers, defining them as dissipative subsystems in QCA networks capable of maintaining low entropy and possessing internal models $\mathcal{A}_{\text{int}}$. However, the most distinctive feature of life and intelligent systems is not merely "existence," but "action"—they exhibit clear **Intentionality** and **Teleology**.

In standard physics (such as Newtonian mechanics or Schrödinger equation), dynamics are strictly **Mechanical Causality**: the system's future state is completely determined by current state and evolution laws, with no concept of "acting to achieve a goal." This raises a profound contradiction: if underlying physical laws are blind, where do macroscopic "purposes" and "values" come from?

This chapter will resolve this issue by introducing **Self-referential Dynamics**. We will prove that when a physical system recursively models itself through internal models, mechanical causality undergoes a phase transition in effective description, emerging as **Teleological Causality**. This dynamical mechanism—**Predictive Coding**—constitutes the physical bridge from dead matter to living agents.

## 19.1 Mechanical Causality and Teleological Causality: Dynamical Features Introduced by Self-referential Loops

Physics usually rejects "teleology," considering it a relic of the Aristotelian era. However, in cybernetics and complex systems theory, teleology acquires a demystified definition: **negative feedback behavior**. This section will strictly distinguish two causal modes and prove that in QCA discrete networks, through specific topological connections (self-referential loops), mechanical causality can simulate teleological behavior, thereby endowing physical systems with "agency."

### 19.1.1 Two Topological Modes of Causal Structure

In QCA discrete ontology, causality is defined by connectivity in networks.

**Definition 19.1.1 (Mechanical Causality)**

Let system state be $x_t$, environmental input be $e_t$. Mechanical causality is described by **feedforward** dynamical equation:

$$
x_{t+1} = F(x_t, e_t)
$$

This is a **push** dynamics: past states "push" the system into the future. System evolution trajectory is completely determined by initial conditions $x_0$ and microscopic rules $F$. Entropy usually increases or remains constant over time.

**Definition 19.1.2 (Teleological Causality)**

Teleological causality is described by **feedback** dynamical equation. The system seems attracted by a future **target state** $x_{goal}$. Its effective evolution equation can be written in error correction form:

$$
x_{t+1} = x_t - \gamma \nabla \mathcal{L}(x_t, x_{goal})
$$

where $\mathcal{L}$ is a distance metric (such as relative entropy), $\gamma$ is learning rate or feedback gain.

This is a **pull** dynamics: future goals "pull" system evolution. Although this is still implemented by $F$ at the microscopic level, at the macroscopic level, system behavior manifests as acting **in order to** minimize $\mathcal{L}$.

### 19.1.2 Algebraic Construction of Self-referential Loops: Using Output as Input

How to construct teleological systems in a purely mechanical QCA universe? The answer lies in **self-reference**.

In Section 18.4, we defined observer's internal model $\mathcal{A}_{\text{int}}$. If the observer not only simulates the environment but also **simulates itself**, self-reference is formed.

**Construction 19.1.3 (Self-referential Operator)**

In observer's internal algebra $\mathcal{A}_{\text{int}}$, there exists a subalgebra $\mathcal{M}_{\text{self}} \subset \mathcal{A}_{\text{int}}$, whose state $\rho_{\text{self}}$ is a coarse-grained mapping of observer's overall state $\rho_{\text{tot}}$ (self-model):

$$
\rho_{\text{self}}(t) = \Pi_{\text{self}}(\rho_{\text{tot}}(t))
$$

QCA's update operator $U$ is designed to depend on this self-model:

$$
x_{t+1} = U(x_t, \rho_{\text{self}}(t))
$$

This forms a **causal closed loop** (Strange Loop):

$$
x_t \xrightarrow{\text{map}} \rho_{\text{self}} \xrightarrow{\text{control}} x_{t+1}
$$

This structure enables the system to "sense itself sensing," thereby adjusting behavior according to deviation between current state and ideal self-model (goal).

### 19.1.3 Error-Driven Dynamics: From $F=ma$ to $\dot{x} \propto -\nabla S$

Self-referential loops introduce a new physical quantity: **Prediction Error**.

Let observer internally have an expected future state (prior belief) $\rho_{\text{prior}}$. Current perceptual state is $\rho_{\text{sense}}$.

The core mechanism of self-referential dynamics is: system evolution direction always tends to reduce **relative entropy (KL divergence)** between the two.

**Theorem 19.1.4 (Teleological Emergence Theorem)**

In a QCA subsystem containing self-referential feedback loops, if update rule $U$ satisfies **free energy minimization** principle (see Section 19.3 for details), then the subsystem's macroscopic trajectory will follow **gradient flow** equation:

$$
\frac{d}{dt} \mathbf{x}(t) = -\Gamma \frac{\delta F}{\delta \mathbf{x}} + \mathbf{f}_{\text{solenoidal}}
$$

where $F$ is variational free energy (as measure of prediction error).

**Physical Significance**:

1. **Attractor**: Free energy minima constitute **strange attractors** of the dynamical system. This attractor is the system's "purpose" or "steady state."

2. **Teleology**: External observers seeing the system automatically return to steady state under perturbations would think the system has "self-repair" or "goal-seeking" abilities. But this is essentially mechanical response of self-referential loops to error gradients.

### 19.1.4 Physical Origin of Normativity: Bridge Between "Is" and "Ought"

David Hume proposed the gap between "Is" and "Ought": physical facts cannot derive value judgments.

However, in self-referential dynamics, this gap is filled by **Prior Models**.

* **Is**: Current perceptual state $\rho_{\text{sense}}$.

* **Ought**: Internally solidified prior goal $\rho_{\text{prior}}$ (e.g., "body temperature should be 37°C").

* **Dynamics**: Physical laws drive the system to eliminate differences between $Is$ and $Ought$ ($Is \to Ought$).

**Corollary 19.1.5 (Physical Definition of Value)**

In physics, "value" or "utility" is not an ethereal concept, but **negative prediction error** (or negative entropy).

An observer considering some state "good" physically means that state is highly consistent with its internal prior model (low surprise).

Self-referential dynamics explains why living systems always actively seek low-entropy resources (food, information): because this is necessary to maintain predictive success of their internal models.

**Summary**

This section proved:

1. **Structure**: Self-reference is a feedback loop where the system uses its own state as input.

2. **Function**: Self-reference transforms mechanical push into teleological pull (error minimization).

3. **Philosophy**: This provides solid physical foundation for "intentionality" and "normativity," i.e., **quantized implementation of cybernetics**.

In the next section 19.2, we will further formalize this dynamics, introduce **self-referential update operators**, and derive state evolution equations containing predictive feedback. This will directly lead to the core of brain working principles—predictive coding theory.

