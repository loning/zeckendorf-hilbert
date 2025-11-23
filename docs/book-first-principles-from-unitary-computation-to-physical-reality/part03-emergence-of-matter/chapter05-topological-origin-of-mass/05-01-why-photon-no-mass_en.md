# 5.1 Why Do Photons Have No Mass? — Pure Translation Modes

In the Light Path Conservation Axiom $v_{ext}^2 + v_{int}^2 = c^2$, we have already seen the shadow of mass. Rest mass $m_0$ corresponds to the maximum internal oscillation frequency when $v_{ext} = 0$.

For photons, experiments tell us their rest mass is zero ($m_\gamma < 10^{-18}$ eV). This means in our theory, photons must satisfy:

$$v_{int} \equiv 0$$

which leads to:

$$v_{ext} \equiv c$$

Why must photons be this way? This stems from their evolution mode in QCA networks.

## 5.1.1 Definition 5.1 (Translation-Invariant Mode)

Consider a one-dimensional simplified model of QCA. Let quantum state be $|\psi(x, t)\rangle$.

If evolution operator $\hat{U}$ merely maps state from $x$ to $x+a$ (or $x-a$) without changing its internal phase or spin structure, then this excitation is called a **Pure Translation Mode**.

$$\hat{U} |\psi(x)\rangle = |\psi(x \pm a)\rangle$$

## 5.1.2 Theorem 5.1 (Massless Theorem)

If an excitation's evolution operator $\hat{U}$ can be globally diagonalized as pure translation generator $e^{i\hat{P}a}$ without any local mixing terms, then this excitation's internal evolution speed $v_{int} = 0$, i.e., this particle is massless.

**Proof**:

Pure translation means Hamiltonian $\hat{H} \sim \hat{P}$.

In Hilbert space, state vector $|\psi(t)\rangle$ merely moves between position bases $|x\rangle$ without evolving on internal degrees of freedom (such as spin flips).

According to microscopic derivation of Light Path Conservation (see Chapter 3, Section 3.2), $v_{int}$ corresponds to parts of Hamiltonian that **anti-commute** with momentum $\hat{P}$ (i.e., mass term $\hat{M}$).

If $\hat{H}$ only has $\hat{P}$ term, then $\hat{M} \equiv 0 \implies v_{int} \equiv 0$.

Q.E.D.

## 5.1.3 Physical Picture

Photons are "heartless" information packets. When transmitting on lattices, they need no internal computation. They simply transport bits from A to B.

Because they have no "internal life," they have no proper time ($\tau = 0$) and no rest mass. They are destined to eternally wander at the universe's maximum allowed speed.

This also explains why gauge bosons (under unbroken symmetry) are usually massless: they are **messengers** for transmitting information in networks, not **nodes** for processing information.

So, what has mass? It must be things that **"stop to think."** In the next section, we will see that matter particles are precisely products of this "thinking."

