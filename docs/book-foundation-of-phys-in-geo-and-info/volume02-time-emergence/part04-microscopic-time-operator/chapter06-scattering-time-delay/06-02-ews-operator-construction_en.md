**6.2 Complete Construction of the Eisenbud-Wigner-Smith (EWS) Operator $\mathsf{Q}$**

In Section 6.1, through the negative proof of Pauli's theorem, we were forced to abandon the search for a universal time operator globally conjugate to the Hamiltonian. This forces us to shift our focus from the static Hilbert space structure to dynamic physical processes. For an open physical system, the most fundamental dynamical process is **scattering**.

This section will rigorously define the scattering time delay operator, namely the Eisenbud-Wigner-Smith (EWS) operator $\mathsf{Q}$. We will prove that, despite the absence of a global time coordinate, for any scattering process, one can intrinsically construct a self-adjoint operator whose eigenvalues precisely correspond to the **dwell time** of particles in the interaction region relative to the **delay** of free motion. This is the first mathematical pillar of this book's "time emergence" program.

### 6.2.1 Analytic Properties of the Scattering Matrix $S(E)$

Consider a multi-channel quantum scattering system. Let the Hilbert space decompose as $\mathcal{H} = \mathcal{H}_{int} \oplus \mathcal{H}_{ext}$, where the interaction region $\mathcal{H}_{int}$ is finite, and the external region $\mathcal{H}_{ext}$ consists of several scattering channels.

In the energy representation, the asymptotic states of the system are described by the incident state $|\psi_{in}\rangle$ and the outgoing state $|\psi_{out}\rangle$. They are related through the **scattering operator** $\hat{S}$:

$$
|\psi_{out}\rangle = \hat{S} |\psi_{in}\rangle
$$

On the energy shell $E$, $\hat{S}$ manifests as an $N \times N$ unitary matrix $S(E)$ ($N$ is the number of channels), satisfying:

$$
S(E)^\dagger S(E) = S(E) S(E)^\dagger = \mathbb{I}
$$

This means the scattering process conserves probability. However, unitarity only guarantees particle number conservation and does not contain time information. Time information is hidden in the **phase gradient** of the $S$ matrix as it varies with energy $E$.

### 6.2.2 Definition of the EWS Operator and Proof of Self-Adjointness

To extract the hidden time information, Eisenbud (1948), Wigner (1955), and Smith (1960) introduced a Hermitian operator $\mathsf{Q}$.

**Definition 6.2.1 (EWS Time Delay Operator)**

For a scattering system with energy $E$, the Eisenbud-Wigner-Smith operator $\mathsf{Q}(E)$ is defined as:

$$
\mathsf{Q}(E) \equiv -i\hbar S(E)^\dagger \frac{d S(E)}{dE}
$$

This operator acts on the channel space $\mathbb{C}^N$.

**Theorem 6.2.2 (Self-Adjointness of the EWS Operator)**

If $S(E)$ is unitary, then $\mathsf{Q}(E)$ must be a self-adjoint (Hermitian) operator, i.e., $\mathsf{Q}^\dagger = \mathsf{Q}$.

**Proof**:

Starting from the unitarity of $S(E)$:

$$
S(E)^\dagger S(E) = \mathbb{I}
$$

Differentiating with respect to energy $E$:

$$
\frac{dS^\dagger}{dE} S + S^\dagger \frac{dS}{dE} = 0
$$

This gives the identity for derivative operators:

$$
S^\dagger \frac{dS}{dE} = - \frac{dS^\dagger}{dE} S
$$

Now consider the adjoint operator $\mathsf{Q}^\dagger$ of $\mathsf{Q}$:

$$
\begin{aligned}

\mathsf{Q}^\dagger &= \left( -i\hbar S^\dagger \frac{dS}{dE} \right)^\dagger \\

&= i\hbar \left( \frac{dS}{dE} \right)^\dagger (S^\dagger)^\dagger \\

&= i\hbar \frac{dS^\dagger}{dE} S

\end{aligned}
$$

Substituting using the above derivative identity:

$$
\mathsf{Q}^\dagger = i\hbar \left( - S^\dagger \frac{dS}{dE} \right) = -i\hbar S^\dagger \frac{dS}{dE} = \mathsf{Q}
$$

$\square$

This property is crucial: because $\mathsf{Q}$ is self-adjoint, it has a real spectrum, allowing us to interpret its eigenvalues as physically observable time quantities.

### 6.2.3 Physical Interpretation: Wave Packet Delay and Eigen-Time

To understand the physical meaning of $\mathsf{Q}$, we examine the group delay of a narrow wave packet in the scattering process.

Let the incident wave packet be $|\psi_{in}(t)\rangle = \int dE \, g(E) e^{-iEt/\hbar} |\chi\rangle$, where $|\chi\rangle$ is a fixed vector in channel space. The outgoing wave packet is $|\psi_{out}(t)\rangle = \hat{S} |\psi_{in}(t)\rangle$.

Using the stationary phase approximation, the arrival time of the wave packet center is determined by the energy derivative of the phase. For a scattering state $S(E) = e^{2i\delta(E)}$ (one-dimensional case), the group delay is:

$$
\Delta t = 2\hbar \frac{d\delta}{dE}
$$

In the one-dimensional case, $\mathsf{Q} = -i\hbar e^{-2i\delta} (2i\delta' e^{2i\delta}) = 2\hbar \delta'$. This is exactly the group delay.

**Generalization to Multi-Channel Case**:

The expectation value $\langle \chi | \mathsf{Q} | \chi \rangle$ of the operator $\mathsf{Q}(E)$ gives the average time delay when the incident state is $|\chi\rangle$.

Since $\mathsf{Q}$ is a Hermitian matrix, it can be diagonalized. Let its eigenvalue equation be:

$$
\mathsf{Q}(E) |q_n\rangle = \tau_n(E) |q_n\rangle, \quad n=1,\dots,N
$$

**The eigenvalues $\tau_n(E)$** are called **eigen-time delays**. They correspond to the time dwell of the eigenchannels of the scattering matrix in the interaction region. This shows that for a complex quantum system, time is not singular but a **spectrum**.

### 6.2.4 Connection to the Holographic Principle: Trace Formula

The EWS operator not only defines microscopic time but also establishes a profound connection with the density of states (DOS) through the trace formula. This directly leads to the discussion of the "unified time identity" in subsequent chapters of this book.

**Definition 6.2.3 (Wigner Time Delay Sum Rule)**

The total time delay of the system is the trace of the $\mathsf{Q}$ matrix:

$$
\tau_{tot}(E) = \text{Tr}[\mathsf{Q}(E)] = \sum_{n=1}^N \tau_n(E)
$$

Using the derivative form of $\text{Tr}(\ln A) = \ln(\det A)$, namely $\text{Tr}(A^{-1} A') = (\ln \det A)'$, we have:

$$
\text{Tr}[\mathsf{Q}] = -i\hbar \text{Tr}[S^\dagger S'] = -i\hbar \frac{d}{dE} \ln \det S(E)
$$

According to Birman-Kreĭn theory (to be detailed in Chapter 7), $\det S(E) = e^{-2\pi i \xi(E)}$, where $\xi(E)$ is the spectral shift function. Therefore:

$$
\text{Tr}[\mathsf{Q}(E)] = -i\hbar \frac{d}{dE} (-2\pi i \xi(E)) = 2\pi\hbar \frac{d\xi}{dE} = 2\pi\hbar \Delta \rho(E)
$$

where $\Delta \rho(E)$ is the change in **local density of states** caused by the interaction.

**Physical Corollary**:

This formula $\text{Tr}[\mathsf{Q}] = 2\pi\hbar \Delta \rho$ is the mathematical expression of this book's core concept **"time is matter"**.

* The left side is a **time** quantity (trace of delays).

* The right side is a **matter** quantity (increase in energy level density).

This shows that a particle "spending time" in a region is equivalent to that region "having density of states" to accommodate the particle. In gravitational theory, this will explain why strong gravitational fields (high density of states) cause time dilation (large delay).

### 6.2.5 Summary

This section resolves the time definition crisis brought by Pauli's theorem through the rigorous construction of the EWS operator $\mathsf{Q}$.

1.  **Existence**: Although there is no global time operator, there exists a local, process-dependent scattering time operator $\mathsf{Q}$.

2.  **Observability**: $\mathsf{Q}$ is self-adjoint, and its eigenvalues correspond to physically measurable delays.

3.  **Holographic Nature**: The trace of $\mathsf{Q}$ directly corresponds to the system's density of states, establishing a bridge between spacetime geometry and quantum statistics.

In the next section, we will delve deeper into the physical connotation of the $\mathsf{Q}$ operator, particularly the proof of physical equivalence between **dwell time** and group delay, further solidifying the ontological status of microscopic time.

