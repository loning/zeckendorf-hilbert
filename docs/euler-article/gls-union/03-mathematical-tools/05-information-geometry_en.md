# Information Geometry: Metric Structure of Probability

> *"Probability distributions form a manifold, Fisher information is its metric."* — Shun-ichi Amari

## 🎯 Core Idea

We usually think probability distributions are just sets of numbers.

**Information geometry** reveals: Probability distribution space is actually a **manifold with metric**!

- **Points** = Probability distributions
- **Distance** = Relative entropy (KL divergence)
- **Metric** = Fisher information matrix
- **Geodesics** = Optimal inference paths

This is the mathematical foundation of IGVP (Information Geometric Variational Principle).

## 🗺️ Space of Probability Distributions

### Simple Example: Coin Toss

Consider a biased coin with probability $p$ of heads:

$$
P(H) = p, \quad P(T) = 1-p, \quad p \in [0, 1]
$$

All possible probability distributions form a **one-dimensional manifold** (interval $[0,1]$).

```mermaid
graph LR
    P0["p=0<br/>Always Tails"] --> P25["p=0.25"]
    P25 --> P50["p=0.5<br/>Fair Coin"]
    P50 --> P75["p=0.75"]
    P75 --> P1["p=1<br/>Always Heads"]

    style P50 fill:#fff4e1,stroke:#ff6b6b,stroke-width:2px
```

Question: How to measure "distance" between two distributions $p_1$ and $p_2$?

## 📏 Kullback-Leibler Divergence (Relative Entropy)

### Definition

**KL divergence** (Kullback-Leibler divergence):

$$
\boxed{D_{KL}(p || q) = \sum_i p_i \ln \frac{p_i}{q_i}}
$$

Or continuous case:

$$
D_{KL}(p || q) = \int p(x) \ln \frac{p(x)}{q(x)} dx
$$

**Physical meaning**:

- Extra information needed to encode true distribution $p$ using distribution $q$
- "Distance" from $p$ to $q$ (but asymmetric!)

### Properties

1. **Non-negativity**: $D_{KL}(p || q) \ge 0$
2. **Zero if and only if**: $D_{KL}(p || q) = 0 \Leftrightarrow p = q$
3. **Asymmetry**: $D_{KL}(p || q) \neq D_{KL}(q || p)$ (not a true distance!)

```mermaid
graph LR
    P["Distribution p"] --> |"D_KL(p||q)"| Q["Distribution q"]
    Q --> |"D_KL(q||p) ≠ D_KL(p||q)"| P

    style P fill:#e1f5ff
    style Q fill:#ffe1e1
```

## 🧮 Fisher Information Matrix

### From KL Divergence to Fisher Metric

Consider parameterized distribution family $p_\theta$, where $\theta = (\theta^1, \ldots, \theta^n)$.

**Fisher information matrix** is defined as Hessian of KL divergence:

$$
\boxed{g_{ij}(\theta) = \frac{\partial^2}{\partial \theta^i \partial \theta^j} D_{KL}(p_\theta || p_{\theta'})\Big|_{\theta'=\theta}}
$$

Or equivalently:

$$
g_{ij}(\theta) = \mathbb{E}_\theta\left[\frac{\partial \ln p_\theta}{\partial \theta^i} \frac{\partial \ln p_\theta}{\partial \theta^j}\right]
$$

**This is a Riemannian metric!**

### Fisher-Rao Metric

**Fisher-Rao metric** turns probability distribution space into Riemannian manifold.

Line element:

$$
ds^2 = g_{ij}(\theta) d\theta^i d\theta^j
$$

"Distance" between two nearby distributions $p_\theta$ and $p_{\theta+d\theta}$:

$$
ds^2 \approx 2 D_{KL}(p_\theta || p_{\theta+d\theta})
$$

```mermaid
graph TB
    M["Probability Distribution Manifold 𝓜"] --> G["Fisher Metric g_ij"]
    G --> D["Geodesics = Optimal Paths"]
    G --> C["Curvature = Higher Correlations"]

    style M fill:#fff4e1,stroke:#ff6b6b,stroke-width:2px
    style G fill:#e1ffe1
```

## 🌀 Simple Example: Bernoulli Distribution

### Parameterization

Bernoulli distribution:

$$
p(x | \theta) = \theta^x (1-\theta)^{1-x}, \quad x \in \{0, 1\}, \quad \theta \in (0, 1)
$$

Log-likelihood:

$$
\ln p = x \ln \theta + (1-x) \ln(1-\theta)
$$

### Fisher Information

Calculate:

$$
\frac{\partial \ln p}{\partial \theta} = \frac{x}{\theta} - \frac{1-x}{1-\theta}
$$

$$
g(\theta) = \mathbb{E}\left[\left(\frac{x}{\theta} - \frac{1-x}{1-\theta}\right)^2\right] = \frac{1}{\theta(1-\theta)}
$$

### Fisher-Rao Distance

Distance between two Bernoulli distributions $p_{\theta_1}$ and $p_{\theta_2}$:

$$
d(\theta_1, \theta_2) = \int_{\theta_1}^{\theta_2} \sqrt{g(\theta)} d\theta = \int_{\theta_1}^{\theta_2} \frac{d\theta}{\sqrt{\theta(1-\theta)}}
$$

Calculating:

$$
d(\theta_1, \theta_2) = 2 \arccos\left(\sqrt{\theta_1\theta_2} + \sqrt{(1-\theta_1)(1-\theta_2)}\right)
$$

(This is called **Bhattacharyya distance**)

## 🔄 Quantum Relative Entropy

### Definition

For quantum states $\rho$ and $\sigma$, define **quantum relative entropy**:

$$
\boxed{S(\rho || \sigma) = \text{tr}(\rho \ln \rho) - \text{tr}(\rho \ln \sigma)}
$$

### Properties

1. **Non-negativity**: $S(\rho || \sigma) \ge 0$ (Klein inequality)
2. **Monotonicity**: For any completely positive map $\Phi$, $S(\Phi(\rho) || \Phi(\sigma)) \le S(\rho || \sigma)$
3. **Additivity**: $S(\rho_1 \otimes \rho_2 || \sigma_1 \otimes \sigma_2) = S(\rho_1 || \sigma_1) + S(\rho_2 || \sigma_2)$

### Physical Meaning

Quantum relative entropy measures "distinguishability" of two quantum states.

In thermodynamics:

$$
S(\rho || \rho_{\text{thermal}}) = \beta(F - F_{\text{thermal}})
$$

(Free energy difference)

## 🎓 Applications in IGVP

### Variation of Generalized Entropy

In IGVP framework, first-order condition:

$$
\delta S_{\text{gen}} = 0
$$

involves **generalized entropy**:

$$
S_{\text{gen}} = \frac{A}{4G\hbar} + S_{\text{out}}
$$

### Second-Order Condition: Relative Entropy Non-Negative

Second-order condition requires:

$$
\delta^2 S_{\text{rel}} \ge 0
$$

where $S_{\text{rel}}$ is relative entropy.

This ensures stability of Einstein equation.

```mermaid
graph TB
    I["IGVP"] --> F["First-Order: δS_gen = 0"]
    I --> S["Second-Order: δ²S_rel ≥ 0"]

    F --> E["Einstein Equation<br/>G_ab + Λg_ab = 8πGT_ab"]
    S --> H["Hollands-Wald<br/>Stability"]

    style I fill:#fff4e1,stroke:#ff6b6b,stroke-width:3px
    style E fill:#e1ffe1
    style H fill:#ffe1e1
```

### Fisher Metric and Metric Variation

From information geometry perspective, variation of metric $g_{\mu\nu}$ corresponds to variation of probability distributions.

Fisher information matrix gives natural metric on metric space.

## 📝 Key Concepts Summary

| Concept | Definition/Formula | Meaning |
|---------|-------------------|---------|
| KL Divergence | $D_{KL}(p||q) = \sum p_i \ln(p_i/q_i)$ | Relative entropy |
| Fisher Information | $g_{ij} = \mathbb{E}[\partial_i \ln p \cdot \partial_j \ln p]$ | Probability metric |
| Fisher-Rao Metric | $ds^2 = g_{ij} d\theta^i d\theta^j$ | Metric on distribution space |
| Quantum Relative Entropy | $S(\rho||\sigma) = \text{tr}(\rho\ln\rho - \rho\ln\sigma)$ | Quantum version of KL divergence |
| Cramér-Rao Bound | $\text{Var}(\hat{\theta}) \ge \frac{1}{g(\theta)}$ | Lower bound on estimation precision |

## 🎓 Further Reading

- Classic textbook: S. Amari, *Information Geometry and Its Applications* (Springer, 2016)
- Quantum information: M. Hayashi, *Quantum Information Theory* (Springer, 2017)
- GLS application: igvp-einstein-complete.md
- Next: [06-category-theory_en.md](06-category-theory_en.md) - Category Theory Basics

## 🤔 Exercises

1. **Conceptual Understanding**:
   - Why is KL divergence asymmetric?
   - Why is Fisher information a metric?
   - What is the physical meaning of monotonicity of quantum relative entropy?

2. **Calculation Exercises**:
   - Calculate KL divergence of two normal distributions $N(\mu_1, \sigma^2)$ and $N(\mu_2, \sigma^2)$
   - Verify Fisher information formula for Bernoulli distribution
   - For $2\times 2$ density matrix, calculate quantum relative entropy

3. **Physical Applications**:
   - Application of Cramér-Rao bound in quantum measurement
   - What is the relationship between Fisher information and quantum Fisher information?
   - Role of relative entropy in black hole thermodynamics

4. **Advanced Thinking**:
   - Can we define symmetric "distance"? (Hint: Bhattacharyya distance)
   - What is the meaning of curvature of Fisher metric?
   - What is the connection between information geometry and thermodynamic geometry?

---

**Next Step**: Finally, we will learn **Category Theory Basics**—"mathematics of mathematics," key to understanding QCA universe and matrix universe!

