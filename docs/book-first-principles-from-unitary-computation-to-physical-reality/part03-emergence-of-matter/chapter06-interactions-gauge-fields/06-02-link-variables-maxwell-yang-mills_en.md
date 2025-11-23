# 6.2 Necessity of Link Variables: Derivation of Maxwell and Yang-Mills Equations

In the previous section, we introduced **local gauge symmetry** as a fundamental property of QCA networks: each cell can freely choose its internal reference frame, and to transmit information between adjacent cells, network must maintain a set of **connection fields** $U_{yx}$ as "translators."

This section will show a more profound result: merely to maintain **consistency** and **minimal error** of this communication network, connection fields themselves must follow specific dynamical equations. Remarkably, these equations are precisely the familiar **Maxwell's equations** (for Abelian groups) and **Yang-Mills equations** (for non-Abelian groups).

In this picture, photons and gluons are not particles "added" to the universe, but **dynamic curvature** produced by spacetime networks to **correct information transmission errors**.

## 6.2.1 Closed Loops and Information Distortion: Geometric Definition of Field Strength

If connection field $U_{yx}$ were merely a static translation table, physics would be very boring. Interesting things happen when we examine closed paths (loops).

Consider a minimal closed loop (plaquette) on QCA lattice, denoted $\Box$. Suppose information starts from node 1, passes through 2, 3, 4 in sequence, finally returning to 1.

The total transformation operator of this process is called **holonomy** or **Wilson loop**:

$$U_{\Box} = U_{14} U_{43} U_{32} U_{21}$$

* **Flat Connection**: If $U_{\Box} = \mathbb{I}$ (identity operator), information returns unchanged after one round. This means network geometry is flat, parallel transport is path-independent.

* **Curvature**: If $U_{\Box} \neq \mathbb{I}$, information acquires extra phase or rotation during transmission. This "non-closure" degree is **field strength**.

In continuous limit, let lattice spacing be $a$, connection field $U_{x+\mu, x} = e^{-ig a A_\mu(x)}$.

Using Baker-Campbell-Hausdorff formula expansion (see appendix), we can derive:

$$U_{\Box} \approx e^{-ig a^2 F_{\mu\nu}}$$

where $F_{\mu\nu}$ is precisely the field strength tensor:

$$F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu - ig [A_\mu, A_\nu]$$

**Physical Picture 6.2**:

* **Magnetic Field $\mathbf{B}$**: Not just force deflecting needles; it is **phase accumulation on spatial loops**. When you walk around a magnetic field once, your wave function phase cannot restore.

* **Electric Field $\mathbf{E}$**: Is **phase accumulation on spacetime loops**. It represents synchronization error in "time updates" between two adjacent nodes (non-commutativity of $U_{t, t+1}$ and $U_{x, x+1}$).

## 6.2.2 Minimal Distortion Principle: Origin of Action

Why must electromagnetic fields follow Maxwell's equations?

In classical mechanics, this is determined by least action principle $\delta S = 0$. But in QCA, we can give a more fundamental explanation.

QCA evolution must be unitary, meaning information must be as faithful as possible. If network is full of random curvature ($U_{\Box}$ jumping randomly), information will rapidly decohere during transmission, causing universe to "heat death" or "white noise."

Therefore, a universe capable of supporting complex structures must have connection fields in a **low curvature state**.

We define network's **channel cost function**, i.e., sum of "information distortion" on all loops:

$$S_{\text{noise}} = \sum_{\Box} \text{Re} \text{Tr} (\mathbb{I} - U_{\Box})$$

This quantity measures how much network deviates from "perfect flatness."

Meanwhile, changes in connection fields themselves require cost (because changing connections consumes computational resources). This corresponds to kinetic energy term.

In continuous limit, this cost function (action) converges to:

$$S \sim \int d^4x \, \text{Tr} (F_{\mu\nu} F^{\mu\nu})$$

This is precisely **Yang-Mills action**! For $U(1)$ group, it's Maxwell action $-\frac{1}{4} F^2$.

## 6.2.3 Derivation of Dynamical Equations

With action, dynamical equations are inevitable results of **minimizing channel noise**. Varying connection field $A_\mu$:

$$\frac{\delta S}{\delta A_\mu} = 0 \implies D_\mu F^{\mu\nu} = J^\nu$$

* **$D_\mu F^{\mu\nu}$**: This is diffusion term of curvature. It tells us that if there's strong curvature somewhere (like near charges), it won't exist abruptly, but will smoothly diffuse to surrounding space. This is the origin of **Coulomb's law** and **wave equations**.

* **$J^\nu$**: This is matter flow (source). When matter particles (topological knots carrying local basis rotations) move, they force surrounding connection fields to change accordingly, thus producing radiation.

**Conclusion**:

Photons (Maxwell waves) are not independent entities. They are **"elastic waves" produced by spacetime networks to smooth out local phase distortions caused by charges**.

Just like placing a ball on a rubber membrane causes deformation, placing a charge causes connection field distortion. When charge moves, propagation of distortion forms light.

## 6.2.4 Special Properties of Non-Abelian Fields: Why Do Gluons Self-Interact?

For $U(1)$ electromagnetic fields, photons themselves carry no charge, because phase rotations are commutative ($e^{i\alpha} e^{i\beta} = e^{i\beta} e^{i\alpha}$).

But for $SU(N)$ non-Abelian fields (such as color charge), internal rotations are non-commutative.

This means: **Changes in connection field $A_\mu$ itself also cause further distortion of connection fields.**

$$[A_\mu, A_\nu] \neq 0$$

This nonlinear term causes gluons to carry color charge and undergo self-interactions.

From QCA graph-theoretic perspective, this corresponds to **topological entanglement** of network connections. Information flows along different paths not only have different phases, but also different "directions" in internal space. To coordinate such complex distortions, connection fields must become extremely dense and strong. This is the geometric origin of **quark confinement**—if trying to separate two quarks, distortion energy on one-dimensional path (flux tube) connecting them grows linearly until breaking produces new quark pairs.

## 6.2.5 Summary

We have reconstructed gauge field theory from the perspective of "communication protocols."

* **Maxwell's equations** are **synchronization algorithms** networks run to maintain phase consistency.

* **Yang-Mills equations** are **error correction algorithms** networks run to maintain internal reference frame alignment.

* **Photons and gluons** are data packets (data packets) produced when these algorithms run.

Forces exist in nature because the universe is not just a computational system, but a **distributed** computational system. Without centralized clocks, every node must continuously "handshake" (exchanging bosons) to confirm each other's states. The macroscopic manifestation of this handshaking is interactions.

In the next section, we will explore parameters determining strengths of these interactions—**coupling constants**—and reveal their deep connection with network topological structure.

