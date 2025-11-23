# 3.1 The Discrete Origin of Light Cones: Deriving Maximum Signal Velocity $c$ from Lattice Hopping

In the Ultimate Axiom $\Omega$, we only defined a static graph $\Lambda$ and a dynamic rule $\hat{U}$. We did not presuppose "relativity," "Lorentz symmetry," or that sacred constant $c \approx 299,792,458$ meters/second.

However, remarkably, as soon as this automaton starts running, the **light cone** structure automatically emerges like crystal growth from the logical foundation. The core of special relativity—causality and limiting velocity—is not traffic laws imposed by God on the universe, but inevitable properties of discrete information processing systems.

This chapter will prove: **Light speed $c$ is merely the ratio of the "grid constant" and "refresh rate" of spacetime lattice points.**

In Newton's continuous spacetime, instantaneous action at a distance is mathematically allowed. Forces can propagate at infinite speed; causality has no boundary. But in a discrete QCA universe, this is strictly forbidden by the "locality" clause in Axiom $\Omega$.

## 3.1.1 Definition of Influence: Commutators as Causal Detectors

First, we need to physically define what "influence" or "signal" means. In quantum mechanics, if two observable operators $\hat{A}$ and $\hat{B}$ commute (i.e., $[\hat{A}, \hat{B}] = 0$), then measuring $\hat{A}$ does not interfere with the statistical distribution of $\hat{B}$, and vice versa. This means there is no causal connection between them.

Conversely, if $[\hat{A}, \hat{B}] \neq 0$, it indicates that one operation interferes with another's result; information has been transmitted between them.

Therefore, we can define:

> **Definition (Causal Connection)**:
>
> If for local operator $\hat{O}_x$ at location $x$ and local operator $\hat{O}_y$ at location $y$, in the Heisenberg picture they satisfy:
>
> $$[\hat{O}_x(t), \hat{O}_y(0)] \neq 0$$
>
> then event $(y, 0)$ causally influences event $(x, t)$.

## 3.1.2 Strict Light Cone Theorem

Now, we prove that in QCA defined by Axiom $\Omega$, the propagation range of such influence is strictly limited.

> **Theorem 3.1 (Strict Causal Bound of QCA)**
>
> Let the graph distance on QCA graph $\Lambda$ be $d(x,y)$, and the interaction radius of evolution operator $\hat{U}$ be $r$.
>
> For any two nodes $x, y$ and any time step $t \ge 0$, if:
>
> $$d(x, y) > r \cdot t$$
>
> then necessarily:
>
> $$[\hat{O}_x(t), \hat{O}_y(0)] = 0$$

**Proof (Mathematical Induction)**:

1. **Heisenberg Evolution**: $\hat{O}_x(t) = (\hat{U}^\dagger)^t \hat{O}_x(0) \hat{U}^t$. This is equivalent to operator evolution backward in time.

2. **Base Case ($t=0$)**: If $x \neq y$, according to the tensor product structure of local Hilbert spaces, operators on different lattice points naturally commute. $[\hat{O}_x(0), \hat{O}_y(0)] = 0$. Theorem holds.

3. **Single-Step Diffusion ($t=1$)**:

   Consider $\hat{O}_x(1) = \hat{U}^\dagger \hat{O}_x \hat{U}$.

   Since $\hat{U}$ is a product of local gates $\hat{u}_C$, only those local gates covering node $x$ will have non-trivial action on $\hat{O}_x$.

   The support set of these gates is at most the neighborhood $\mathcal{N}_r(x)$ centered at $x$ with radius $r$.

   Therefore, the evolved operator $\hat{O}_x(1)$, though formally more complex, still only contains algebraic combinations of operators defined within $\mathcal{N}_r(x)$.

   For any $y \notin \mathcal{N}_r(x)$ (i.e., $d(x,y) > r$), $\hat{O}_x(1)$ and $\hat{O}_y(0)$ act on disjoint Hilbert subspaces, hence they commute.

4. **Inductive Step**:

   Assume for $t=k$, the support set $\text{supp}(\hat{O}_x(k)) \subseteq \mathcal{N}_{k \cdot r}(x)$.

   At $t=k+1$, $\hat{O}_x(k+1) = \hat{U}^\dagger \hat{O}_x(k) \hat{U}$.

   Applying single-step evolution logic again, the support set expands outward by at most $r$.

   Therefore $\text{supp}(\hat{O}_x(k+1)) \subseteq \mathcal{N}_{(k+1)r}(x)$.

   Conclusion: For any point $y$ with distance $d(x, y) > r \cdot t$, its operator $\hat{O}_y$ lies outside the support set of $\hat{O}_x(t)$, so they necessarily commute.

**Q.E.D.**

## 3.1.3 Ontological Definition of Light Speed $c$

The above theorem gives a purely graph-theoretic and logical step number inequality:

$$\text{Causal Distance} \le r \times \text{Time Steps}$$

To connect with physical reality, we need to introduce **units**.

* Let the physical spacing between lattice points be Planck length $l_P$.

* Let the physical duration of one logical update be Planck time $t_P$.

Physical distance $D = d(x,y) \cdot l_P$, physical time $T = t \cdot t_P$.

The inequality becomes:

$$D/l_P \le r \cdot (T/t_P)$$

$$D/T \le r \cdot \frac{l_P}{t_P}$$

We define this insurmountable speed limit as $c$:

$$c \equiv r \frac{l_P}{t_P}$$

From this perspective, light speed $c$ is no longer a mysterious constant; it is the **aspect ratio of spacetime pixels**.

* **If $c$ were infinite**: It would mean $t_P \to 0$ or $l_P \to \infty$, corresponding to fully connected graphs or instantaneous computation, violating our discrete axiom.

* **If $c$ were variable**: It would mean the lattice structure is non-uniform (non-translationally invariant). Under our uniform QCA assumption, $c$ must be a universal constant.

## 3.1.4 Geometrization of Causality

Theorem 3.1 not only defines speed, but also defines **geometric structure**.

On graph $\Lambda \times \mathbb{Z}$ (spacetime lattice), all point pairs $(y, 0)$ satisfying $d(x, y) \le r \cdot t$ constitute the **past light cone** of point $(x, t)$. Only events within this light cone can possibly be "causes" of $(x, t)$.

Conversely, all point pairs $(z, t)$ satisfying $d(x, z) \le r \cdot t$ constitute the **future light cone** of $(x, 0)$. Only events within this light cone can be "influenced" by $(x, 0)$.

In regions outside the light cone (spacelike separation), $[\hat{O}_x, \hat{O}_z] \equiv 0$. This means:

**For spacelike separated events, there is no objective temporal order.** Because there is no causal connection between them, which comes first or second will not lead to logical contradictions. This is precisely the microscopic origin of "relativity of simultaneity" in special relativity.

## 3.1.5 Summary

Starting from Axiom $\Omega$, without invoking any relativistic assumptions, we "derived" the light cone structure and limiting velocity merely by analyzing operator diffusion on discrete lattices.

In this universe, **photons** are not special particles; they are **information wave packets that exactly reach the lattice propagation bandwidth limit**. They are the exposed skeleton of causal chains.

After establishing the existence of $c$, the next question naturally is: What happens if objects try to move as fast as light? This leads to the most core theorem of this book—Light Path Conservation.

