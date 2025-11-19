**4.3 Gauge Fields as Connection Variables: Wilson Lines and Curvature on Lattices**

In Section 4.2, we proved that spin and Dirac equation can emerge from discrete quantum walks. However, matter fields do not exist in isolation; there are interactions between them. In modern physics, all fundamental interactions (electromagnetic force, weak force, strong force) are described by **Gauge Fields**.

This section will argue that gauge fields are not some kind of "fluid" "added" to spacetime, but inevitable products of **geometric comparison** in discrete ontology. When we compare quantum states at different positions on discrete lattices, due to arbitrariness of local Hilbert space bases, we must introduce **Connection Variables**—namely Wilson lines. The dynamics of these connection variables is precisely gauge field theory.

### 4.3.1 Geometric Dilemma of Local Phases

Consider discrete fermion field $\psi(x)$ derived in previous section. In QCA framework, each lattice site $x$ has independent Hilbert space $\mathcal{H}_x$. According to finite information axiom, we can only define local operations. This means we can independently choose phase of basis (or more general unitary transformations) at each lattice site.

**Definition 4.3.1 (Local Gauge Transformation)**

Perform the following local unitary transformation on total system state:

$$
\psi(x) \mapsto e^{i\alpha(x)} \psi(x)
$$

where $\alpha(x)$ is an arbitrary real function depending on position.

Now examine the "hopping" term in Section 4.2 (i.e., kinetic term caused by conditional shift), which involves inner products or superpositions of states at adjacent lattice sites, e.g., $\psi^\dagger(x) \psi(x+1)$. Under transformation:

$$
\psi^\dagger(x) \psi(x+1) \mapsto e^{-i\alpha(x)} \psi^\dagger(x) e^{i\alpha(x+1)} \psi(x+1) = e^{i(\alpha(x+1) - \alpha(x))} \psi^\dagger(x) \psi(x+1)
$$

Unless $\alpha(x)$ is constant (global symmetry), phase factor $e^{i(\alpha(x+1) - \alpha(x))}$ will destroy form invariance of Hamiltonian or update operator $U$. This is called **breaking of local gauge symmetry**.

**Crisis and Resolution of Physical Ontology**:

If it were a continuous manifold, we are accustomed to thinking that adjacent points are "smoothly connected." But on discrete lattices, two Hilbert spaces $\mathcal{H}_x$ and $\mathcal{H}_{x+1}$ are completely separate algebraic objects. To compare or superpose vectors from these two spaces, we must first establish a **comparison standard**, i.e., parallel transport protocol.

### 4.3.2 Restoring Symmetry: Wilson Lines as Parallel Transport

To keep physical laws invariant under local basis transformations (i.e., physical reality does not depend on observer's reference frame choice), we must introduce a new degree of freedom to "absorb" this phase difference. This degree of freedom exists on edges (Links) connecting two lattice sites.

**Definition 4.3.2 (Link Variable)**

For each directed edge $(x, y)$ on lattice graph $\Lambda$, introduce a unitary operator $\mathcal{U}_{x,y}$ acting on auxiliary "gauge register" space. Under $U(1)$ gauge group (e.g., electromagnetic field), it is a complex phase:

$$
\mathcal{U}_{x,y} = e^{i \theta_{x,y}} \in U(1)
$$

We require it to transform under local gauge transformation according to:

$$
\mathcal{U}_{x,y} \mapsto e^{i\alpha(x)} \mathcal{U}_{x,y} e^{-i\alpha(y)}
$$

**Construction 4.3.3 (Gauge Covariant Derivative)**

Using connection variables, we can correct hopping terms in QCA, constructing **gauge covariant hopping**:

$$
\psi^\dagger(x) \mathcal{U}_{x,x+1} \psi(x+1)
$$

Under transformation:

$$
\begin{aligned}
(\psi^\dagger(x) e^{-i\alpha(x)}) (e^{i\alpha(x)} \mathcal{U}_{x,x+1} e^{-i\alpha(x+1)}) (e^{i\alpha(x+1)} \psi(x+1)) \\
= \psi^\dagger(x) \mathcal{U}_{x,x+1} \psi(x+1)
\end{aligned}
$$

This term remains unchanged. This is precisely the prototype of discrete version of covariant derivative $D_\mu = \partial_\mu - i A_\mu$. Here, $\mathcal{U}_{x,y}$ corresponds to **Wilson Line** from $y$ to $x$, i.e., parallel transport operator over finite distance:

$$
\mathcal{U}_{x,y} \sim \mathcal{P} \exp\left( i \int_y^x A_\mu dx^\mu \right)
$$

### 4.3.3 Discrete Curvature: Plaquette and Holonomy

Connection variable $\mathcal{U}_{x,y}$ itself can be transformed to any value through gauge transformation (e.g., for open chains, we can always choose gauge such that $\mathcal{U}=1$). True physical information is not contained in a single edge, but in closed loops.

**Definition 4.3.4 (Plaquette Operator)**

Consider minimal closed loops (Plaquette) on spacetime grid, e.g., quadrilateral formed by $x \to x+\hat{\mu} \to x+\hat{\mu}+\hat{\nu} \to x+\hat{\nu} \to x$ (where $\hat{\mu}, \hat{\nu}$ are unit vectors). Define **Holonomy** operator on loop:

$$
W_{\mu\nu}(x) = \mathcal{U}_{x, x+\hat{\mu}} \mathcal{U}_{x+\hat{\mu}, x+\hat{\mu}+\hat{\nu}} \mathcal{U}_{x+\hat{\mu}+\hat{\nu}, x+\hat{\nu}} \mathcal{U}_{x+\hat{\nu}, x}
$$

In $U(1)$ case, this is sum of a series of phases:

$$
W_{\mu\nu}(x) = \exp\left( i (\theta_{x, x+\hat{\mu}} + \theta_{x+\hat{\mu}, x+\hat{\mu}+\hat{\nu}} - \theta_{x+\hat{\nu}, x+\hat{\mu}+\hat{\nu}} - \theta_{x, x+\hat{\nu}}) \right) \equiv e^{i \Phi_{\mu\nu}(x)}
$$

**Physical Meaning: Discrete Curvature**

This phase $\Phi_{\mu\nu}(x)$ is a **gauge-invariant** observable. It quantifies phase shift produced when a vector parallel transports around a closed path. According to geometric definition, this is precisely **curvature**.

* On space-space faces, it corresponds to **Magnetic Flux**.

* On time-space faces, it corresponds to **Electric Field** (manifested through phase differences in time step evolution).

### 4.3.4 Continuous Limit: From Lattice to Maxwell and Yang-Mills

To prove this discrete structure is equivalent to familiar field theory macroscopically, we again take long-wavelength limit.

**Theorem 4.3.5 (Emergence of Yang-Mills Action)**

Let lattice spacing be $a$, relationship between connection variable and continuous gauge potential $A_\mu(x)$ be $\mathcal{U}_{x, x+\hat{\mu}} \approx e^{i a g A_\mu(x)}$, where $g$ is coupling constant.

When $a \to 0$, real part of plaquette operator (corresponding to Wilson action) converges to continuous Yang-Mills action:

$$
\sum_{P} \left( 1 - \frac{1}{N} \operatorname{Re} \operatorname{Tr} W_P \right) \xrightarrow{a \to 0} \int d^4x \, \frac{1}{4} F_{\mu\nu}^a F^{a\mu\nu}
$$

where $F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu + ig [A_\mu, A_\nu]$ is field strength tensor.

**Proof Outline**:

1. **Taylor Expansion**: Use Baker-Campbell-Hausdorff formula to expand product $W_{\mu\nu}$.

    $$
    W_{\mu\nu}(x) \approx \exp\left( i a^2 g (\partial_\mu A_\nu - \partial_\nu A_\mu + ig [A_\mu, A_\nu]) + O(a^3) \right)
    $$

2. **Identify Field Strength**: Term in exponent is precisely $i a^2 g F_{\mu\nu}$.

3. **Expand Cosine**: For Wilson action $S_W = \sum (1 - \cos(a^2 g F_{\mu\nu})) \approx \sum \frac{1}{2} (a^2 g F_{\mu\nu})^2$.

4. **Integral Limit**: Summation $\sum$ transforms into integral $\frac{1}{a^4} \int d^4x$. Factor $a^4$ cancels with $(a^2)^2$, leaving term proportional to $\int F^2$.

**Conclusion 4.3.6**

Gauge field theory is not imposed on physics because of "aesthetics" or "symmetry principles," but an inevitable requirement of **discrete spacetime geometric consistency**.

* Matter (fermions) is defined on lattices.

* To compare matter at adjacent lattice sites, connectors (Wilson lines) must be introduced.

* Non-trivial structure of connectors (holonomy) manifests as force fields (electromagnetic force, strong force).

This completes the derivation loop from discrete ontology to continuous interaction field theory. In the next section, we will explore symmetry breaking and restoration, explaining why we see Lorentz symmetry macroscopically, despite microscopic lattices clearly breaking it.

