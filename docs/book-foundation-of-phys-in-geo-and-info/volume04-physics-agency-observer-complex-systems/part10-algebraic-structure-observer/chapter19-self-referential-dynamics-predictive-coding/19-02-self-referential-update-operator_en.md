**19.2 Self-referential Update Operator: State Evolution Equations Containing Predictive Feedback**

In Section 19.1, we distinguished mechanical causality from teleological causality at the macroscopic level and pointed out that self-referential loops are the topological foundation for the latter. This section will delve into QCA's microscopic algebraic structure, constructing specific **Self-referential Update Operators**.

We will prove that when observer's internal algebra $\mathcal{A}_{\text{int}}$ interacts with the environment, if the interaction Hamiltonian contains measurement terms for "prediction error," then the system's effective evolution equation will no longer be simple linear Schrödinger equation, but predictive coding equations with **nonlinear feedback terms**. This equation is highly isomorphic to Kalman Filter and Bayesian update in mathematical form, revealing deep unity between physical dynamics and statistical inference.

### 19.2.1 Prediction Error Operator and Hamiltonian Coupling

Consider observer $\mathfrak{O}$'s internal algebra $\mathcal{A}_{\text{int}}$ and environmental algebra $\mathcal{A}_{\text{ext}}$.

Let observer internally maintain a **predictive model** of external state, described by density matrix $\rho_{\text{model}} \in \mathcal{A}_{\text{int}}$. External true state is $\rho_{\text{ext}} \in \mathcal{A}_{\text{ext}}$.

To compare the two, we need a **Comparator**, usually defined on boundary algebra $\mathcal{A}_{\partial}$.

**Definition 19.2.1 (Prediction Error Operator)**

Let $M_{\text{ext}}$ be environmental observable (such as photon number), $M_{\text{model}}$ be internal model's prediction operator for this quantity.

**Prediction error operator** $\hat{E}$ is defined as the difference between the two on the boundary (connected through appropriate isometric mapping $\iota$):

$$
\hat{E} = M_{\text{ext}} \otimes \mathbb{I}_{\text{int}} - \mathbb{I}_{\text{ext}} \otimes M_{\text{model}}
$$

Its squared expectation value $\langle \hat{E}^2 \rangle = \text{Tr}(\rho_{\text{tot}} \hat{E}^2)$ quantifies mean square error of prediction (i.e., physical surprise or part of free energy).

**Construction 19.2.2 (Error-Driven Interaction)**

To achieve teleological dynamics of "reducing error," system-environment interaction Hamiltonian $H_{\text{int}}$ must couple with error operator. The simplest form is **quadratic potential coupling**:

$$
H_{\text{coupling}} = \frac{\kappa}{2} \hat{E}^2 = \frac{\kappa}{2} (M_{\text{ext}} - M_{\text{model}})^2
$$

where $\kappa$ is coupling strength (corresponding to **precision** in statistics).

### 19.2.2 Construction of Self-referential Update Operator

In QCA discrete time steps, global evolution operator $U$ decomposes into:

1. **Prediction Step**: Internal model evolves according to its own dynamics $H_{\text{self}}$.

2. **Correction Step**: Exchange information with environment through $H_{\text{coupling}}$, correcting the model.

**Definition 19.2.3 (Self-referential Update Operator)**

Single-step update operator $U_{\text{self}}$ is a unitary operator acting on $\mathcal{H}_{\text{ext}} \otimes \mathcal{H}_{\text{int}}$:

$$
U_{\text{self}} = e^{-i H_{\text{coupling}} \Delta t} \cdot (e^{-i H_{\text{ext}} \Delta t} \otimes e^{-i H_{\text{self}} \Delta t})
$$

Here $H_{\text{self}}$ contains observer's internal simulation of physical laws (predictive model), while $H_{\text{coupling}}$ performs error-based feedback update.

### 19.2.3 State Evolution Equation: From Quantum Mechanics to Bayesian Inference

Now we derive effective evolution equation for internal model state $\rho_{\text{model}}$.

Assume environmental state $\rho_{\text{ext}}$ is quasi-static or slowly evolving. We focus on changes of $\rho_{\text{model}}$ under interaction.

Using Lindblad master equation or Heisenberg equation of motion:

$$
\frac{d}{dt} M_{\text{model}} = i [H_{\text{self}}, M_{\text{model}}] + i [H_{\text{coupling}}, M_{\text{model}}]
$$

Computing commutator of interaction term (approximation):

$$
[H_{\text{coupling}}, M_{\text{model}}] = \frac{\kappa}{2} [(M_{\text{ext}} - M_{\text{model}})^2, M_{\text{model}}] \approx -i \kappa \{ M_{\text{ext}} - M_{\text{model}}, \Gamma \}
$$

(Here $\Gamma$ is dissipation/gain coefficient, depending on specific algebraic structure of operators).

In classical limit (or averaging over expectation values), evolution equation for state variable $\mu(t) = \langle M_{\text{model}} \rangle$ is:

$$
\dot{\mu}(t) = \underbrace{f(\mu)}_{\text{Prediction (Prior)}} + \underbrace{\kappa (\langle M_{\text{ext}} \rangle - \mu)}_{\text{Update}}
$$

This is precisely the continuous form of **Kalman-Bucy Filter**, and the core equation of **Predictive Coding**.

**Theorem 19.2.4 (Physics-Bayesian Isomorphism Theorem)**

For QCA subsystems with error coupling $H \sim \kappa \hat{E}^2$, their internal state dynamical evolution is mathematically isomorphic to **Bayesian inference process under Gaussian approximation**.

* **Hamiltonian flow** $H_{\text{self}}$ corresponds to **prior probability** propagation.

* **Coupling flow** $H_{\text{coupling}}$ corresponds to **likelihood function** correction.

* **Coupling strength $\kappa$** corresponds to **Kalman Gain** or sensory precision.

### 19.2.4 Generalized Predictive Coding: Not Only Perception, But Also Action

The above equation only describes **Perception**: changing internal model $\mu$ to match external world $M_{\text{ext}}$.

However, self-referential operators also allow another mode: **Action**.

If observer reacts back on environment through actuators, then $H_{\text{coupling}}$ also causes changes in environmental state $M_{\text{ext}}$:

$$
\dot{M}_{\text{ext}} = \dots - \kappa (M_{\text{ext}} - \mu)
$$

This means the system changes the environment to conform to internal model predictions. This is **Active Inference**.

**Conclusion**

Self-referential update operator $U_{\text{self}}$ transforms physics' Hamiltonian dynamics into information theory's Bayesian dynamics.

1. **Error Minimization**: Evolution fixed point is $\mu \approx M_{\text{ext}}$, i.e., prediction error minimization.

2. **Bidirectional Adaptation**: Observer corrects model through perception and corrects environment through action.

This provides microscopic dynamical foundation for introducing **Free Energy Principle** in the next section 19.3: so-called "free energy" is precisely the functional form of this prediction error operator $\hat{E}^2$ under specific statistical ensemble.

