# 3.3 Derivation of Lorentz Transformation: No Geometry, Only Statistics of Resource Allocation

In the previous section, we established the **Light Path Conservation Theorem**: For any particle, its external displacement velocity $v_{ext}$ and internal evolution velocity $v_{int}$ satisfy $v_{ext}^2 + v_{int}^2 = c^2$. This is an equation about resource allocation in information processing.

Now, we face the greatest challenge: **How to derive the complete Lorentz transformation solely from this resource allocation equation?**

Usually, Lorentz transformations are viewed as results of spacetime geometric rotation ($SO(1,3)$ symmetry of Minkowski space). But in our discrete ontology, we do not presuppose continuous spacetime geometry. All we have are counters on lattices. We will prove that Lorentz transformations are essentially **statistical results of two observers in different reference frames decomposing the same conserved information flow differently**.

## 3.3.1 Definition of Reference Frames: Who Is Watching?

What is a "reference frame" in QCA?

* **Rest Frame (Laboratory Frame $S$)**: This is the perspective of the lattice background itself. We can imagine "daemon processes" distributed across lattice points, synchronized with each other (based on lattice connectivity), recording global update steps $t$ and lattice coordinates $x$. For frame $S$, the maximum signal speed is obviously $c$.

* **Moving Frame (Co-moving Frame $S'$)**: This is the perspective of a local observer attached to a particle (or spaceship) moving through the lattice at speed $v$. This observer carries their own internal clock (based on $v_{int}$) and measuring rod (based on signal round trips).

Our task is to establish the mapping relationship between $(t, x)$ and $(t', x')$.

## 3.3.2 Time Dilation: Relativity of Counting

Consider a particle $P$ moving at constant speed $v$ relative to the lattice (i.e., $v_{ext} = v$).

**In Co-moving Frame $S'$**:

The particle considers itself at rest ($v'_{ext} = 0$). According to the Light Path Conservation Axiom, it must use all light path quota for internal evolution.

$$v'_{int} = c$$

This means the particle's internal clock (proper time $\tau$) runs at maximum efficiency: for each physical moment, its state updates by one step.

$$d\tau \propto 1$$

**In Laboratory Frame $S$**:

We see the particle moving in space ($v_{ext} = v$). According to the Light Path Conservation Theorem, its internal evolution speed is forced to decrease:

$$v_{int} = \sqrt{c^2 - v^2}$$

This means that for each laboratory time step $dt$, the particle's internal state only updates by $\sqrt{c^2-v^2}/c$ steps.

**Mapping Relationship**:

Since "time" is physically defined as the cumulative number of internal state updates, the time $dt$ recorded in frame $S$ and time $dt'$ (i.e., $d\tau$) recorded in frame $S'$ satisfy the proportional relationship:

$$dt' = \frac{v_{int}}{c} dt = \frac{\sqrt{c^2-v^2}}{c} dt = \sqrt{1 - \frac{v^2}{c^2}} dt$$

This is the time dilation formula:

$$dt = \gamma dt', \quad \text{where } \gamma = \frac{1}{\sqrt{1-v^2/c^2}}$$

Note: No spacetime geometric assumptions are used here, only **conservation allocation of counting rate (Clock Rate)**.

## 3.3.3 Length Contraction: Counting Signal Round Trips

Next, we derive spatial transformation. We need to define how to measure length in a moving frame. The most operational definition is the **radar echo method**: send a light signal, reflect from one end to the other, measure round trip time.

Imagine a particle carrying a rod of length $L'$ (at rest in frame $S'$). The particle moves at speed $v$ along the $x$-axis relative to frame $S$.

In frame $S'$, the light signal travels from rod tail to head and back, taking time $\Delta t' = 2L'/c$.

In frame $S$, we see the rod length as $L$.

* **Outbound**: Light at speed $c$ chases the rod head escaping at speed $v$. Relative speed is $c-v$. Time taken $\Delta t_1 = L / (c-v)$.

* **Return**: Light at speed $c$ collides head-on with rod tail. Relative speed is $c+v$. Time taken $\Delta t_2 = L / (c+v)$.

Total round trip time (frame $S$):

$$\Delta t = \Delta t_1 + \Delta t_2 = \frac{L}{c-v} + \frac{L}{c+v} = \frac{2Lc}{c^2-v^2} = \frac{2L}{c(1-v^2/c^2)} = \frac{2L}{c} \gamma^2$$

Now, using the time dilation relationship derived earlier. The round trip time $\Delta t$ measured in frame $S$ should be $\gamma$ times the round trip time $\Delta t'$ measured in frame $S'$ (because the clock on $S'$ runs slow, it reads fewer numbers, corresponding to longer physical duration as seen by $S$... wait, need to be careful here).

**Strict Logic**:

"Time dilation" means: $S'$'s clock runs slow. If $S'$ reads $\Delta t'$ seconds, then $S$ will think this actually took $\gamma \Delta t'$ seconds.

That is: $\Delta t = \gamma \Delta t'$.

Substituting into the above equation:

$$\frac{2L}{c} \gamma^2 = \gamma \left( \frac{2L'}{c} \right)$$

$$\frac{2L}{c} \gamma = \frac{2L'}{c}$$

$$L = \frac{L'}{\gamma} = L' \sqrt{1 - v^2/c^2}$$

This is **Lorentz Length Contraction**. Again, we did not assume space curves; we merely derived a **pursuit problem under a limiting speed $c$**.

## 3.3.4 Algebraic Reconstruction of Lorentz Transformation Matrix

With $\Delta t = \gamma \Delta t'$ and $L = L'/\gamma$, can we write the coordinate transformation $(t, x) \to (t', x')$?

Based on QCA's **translation invariance** (clause 3 of Axiom $\Omega$), the transformation must be linear:

$$x' = A(x - vt)$$

$$t' = D(t - Bx)$$

(Form determined by "origin $x=vt$ is $x'=0$ in $S'$").

1. **Using Length Contraction**:

   Consider moment $t=0$, frame $S$ measures a rod at rest in frame $S'$ (endpoints $x=0$ and $x=L$).

   Corresponding $S'$ coordinates are $x'_1 = A(0) = 0$ and $x'_2 = A(L)$.

   Length $L' = x'_2 - x'_1 = AL$.

   Known $L = L'/\gamma \implies L' = \gamma L$.

   Therefore, coefficient **$A = \gamma$**.

   $$x' = \gamma (x - vt)$$

2. **Using Light Speed Invariance** (direct corollary of causality axiom):

   If a signal satisfies $x = ct$, then it must satisfy $x' = ct'$ in frame $S'$.

   Substituting expressions for $x'$ and $t'$:

   $$ct' = \gamma (ct - vt) = \gamma c t (1 - v/c)$$

   $$t' = \gamma t (1 - v/c)$$

   On the other hand, substituting linear form for $t'$:

   $$t' = D (t - B ct) = D t (1 - Bc)$$

   Equating the two:

   $$\gamma (1 - v/c) = D (1 - Bc)$$

   Since this holds for any light signal ($x = ct$ and $x = -ct$), we can solve:

   **$D = \gamma$**, **$B = v/c^2$**.

Thus, we have completely derived the Lorentz transformation:

$$
\begin{cases}
x' = \gamma (x - vt) \\
t' = \gamma (t - \frac{v}{c^2}x)
\end{cases}
$$

## 3.3.5 Conclusion: Geometry is a Statistical Illusion

This is not just a reproduction of mathematical derivation, but an ontological declaration.

In standard textbooks, Lorentz transformations are considered spacetime geometric rotations (hyperbolic rotation):

$$\begin{pmatrix} ct' \\ x' \end{pmatrix} = \begin{pmatrix} \cosh \eta & -\sinh \eta \\ -\sinh \eta & \cosh \eta \end{pmatrix} \begin{pmatrix} ct \\ x \end{pmatrix}$$

where $\tanh \eta = v/c$.

In our QCA theory, this "hyperbolic rotation" originates from Euclidean rotation on the **information rate circle**:

$$v_{ext} = c \sin \theta, \quad v_{int} = c \cos \theta$$

Lorentz factor $\gamma = 1/\cos \theta = \sec \theta$.

**Profound Insight**:

* The **hyperbolic angle (rapidity $\eta$)** in Minkowski space is mathematically equivalent to the **allocation angle $\theta$** in QCA Hilbert space.

* We think we live in a $3+1$ dimensional pseudo-Euclidean spacetime, but actually, we live in a Hilbert space projection governed by **information rate conservation ($L_2$ norm)**.

Spacetime geometry is not a stage; it is **statistical behavior collectively exhibited by vast numbers of qubits to satisfy conservation laws**. Special relativity is not wrong, but it is not ultimate truth; it is macroscopic emergence of underlying unitary computation.

