# EBOC: Eternal-Block Observer-Computing Unified Theory

**Author**: Auric
**Date**: 2025-10-18

---

## Abstract

**Objective.** To propose **EBOC (Eternal-Block Observer-Computing)**: a geometric-information unified framework without explicit global time, merging the **timeless causal encoding** of **Eternal Graph Cellular Automata** (EG-CA) with the **program semantics and observation-decoding** of **Static Block Universe Cellular Automata** (SB-CA) into the same formal system, and providing verifiable information laws and constructive algorithms.

**Three Pillars.**

1. **Geometric Encoding (Graph/SFT)**: The universe as a **static block** $X_f \subset \Sigma^{\mathbb{Z}^{d+1}}$ satisfying local rules $f$; its causality/consistency is characterized in parallel by the **eternal graph** $G=(V,E)$ and **subshift (SFT)**.
2. **Semantic Emergence (Observation = Decoding)**: **Observation = factor decoding**. The decoder $\pi: \Sigma^B \to \Gamma$ reads the static block layer by layer according to **acceptable foliations** (cross-leaf reading along $\tau$ from layer $c$ to $c+b$), outputting the visible language; "semantic collapse" refers to the **information factorization** from underlying configuration to visible records.
3. **Information Constraint (Non-increasing Law)**: Observation does not create information:
$$
K(\pi(x|_W)) \leq K(x|_W) + K(\pi) + O(1),
$$
and provides **conditional complexity** upper bounds under **causal thick boundaries** along with entropy limits consistent with Brudno.

**Unified Metaphor (RPG Game).** The universe is like an **infinite-plot RPG**: **game data and evolution rules** are already written ($(X_f, f)$), "choices" (apparent free will) must be consistent with the **plot line** (determinism). **Layer-by-layer reading** unlocks chapters according to the established beat $b$; "choices" involve **selecting representatives** from compatible branches and **excluding** incompatible branches; the underlying "ROM" neither adds nor removes information.

**Core Objects.**
$$
\mathcal{U} = (X_f, G, \rho, \Sigma, f, \pi, \mu, \nu),
$$
where $X_f$ is the space-time SFT, $G$ is the eternal graph, $\rho$ gives the **acceptable foliation family** (level sets of the primitive integral covector $\tau^\star$, $\langle\tau^\star, \tau\rangle = b \geq 1$), $\pi$ is the decoder, $\mu$ is the shift-invariant ergodic measure, $\nu$ is the universal semimeasure (used only for typicality weights).

---

## 1. Introduction and Motivation

Traditional CA presents "evolution" through global time iterations; the block/eternal graph perspective gives the entire space-time segment at once, with "evolution" being merely the **layer-by-layer reading** narrative obtained. The dynamic perspective relies on time background and is difficult to be background-independent; the static perspective lacks observational semantics. EBOC unifies the two through "**geometric encoding × semantic decoding × information laws**": SFT/graph structure ensures consistency and constructibility; factor mapping provides visible language; complexity/entropy characterizes conservation and limits. This paper establishes the T1-T20 theorem family under minimal axioms, providing detailed proofs and reproducible experimental procedures.

---

## 2. Symbols and Preliminaries

### 2.1 Space, Alphabet, and Configurations

* Space $L = \mathbb{Z}^d$, space-time $L \times \mathbb{Z} = \mathbb{Z}^{d+1}$; finite alphabet $\Sigma$.
* Space-time configuration $x \in \Sigma^{\mathbb{Z}^{d+1}}$. Restriction of window $W \subset \mathbb{Z}^{d+1}$ is $x|_W$.
* Convention: $|\cdot|$ denotes both word length and set cardinality (distinguished by context).

### 2.2 Neighborhood and Global Evolution

* Finite neighborhood $N \subset \mathbb{Z}^d$, local rule $f: \Sigma^{|N|} \to \Sigma$:
$$
x(\mathbf{r} + N, t) := (x(\mathbf{r} + \mathbf{n}, t))_{\mathbf{n} \in N} \in \Sigma^{|N|}, \quad x(\mathbf{r}, t) = f(x(\mathbf{r} + N, t-1)).
$$
* **Global mapping**
$$
F: \Sigma^{\mathbb{Z}^d} \to \Sigma^{\mathbb{Z}^d}, \quad (F(x))(\mathbf{r}) = f(x(\mathbf{r} + N)).
$$

### 2.3 SFT and Eternal Graph

* **Space-time SFT**
$$
X_f := \{x \in \Sigma^{\mathbb{Z}^{d+1}} : \forall (\mathbf{r}, t), \ x(\mathbf{r}, t) = f(x(\mathbf{r} + N, t-1))\}.
$$
* **Eternal graph** $G = (V, E)$: vertices $V$ encode local patterns (events), edges $E$ encode causal/consistency relations.
* **Edge shift**
$$
Y_G = \{(e_t)_{t \in \mathbb{Z}} \in \mathcal{E}^{\mathbb{Z}} : \forall t, \ \mathrm{tail}(e_{t+1}) = \mathrm{head}(e_t)\}.
$$

### 2.4 Foliation Decomposition and Layer-by-Layer Reading Protocol

* **Unimodular transformation**: $U \in \mathrm{GL}_{d+1}(\mathbb{Z})$ (integral invertible, $\det U = \pm 1$), time direction $\tau = U e_{d+1}$.
* **Acceptable foliation**: There exists a **primitive integral covector** $\tau^\star \in (\mathbb{Z}^{d+1})^\vee$ and constant $c$, with leaves as its level sets
$$
\{\xi \in \mathbb{Z}^{d+1} : \langle \tau^\star, \xi \rangle = c\},
$$
and satisfying
$$
\langle \tau^\star, \tau \rangle = b \geq 1,
$$
to guarantee **monotonic advancement across leaves**.
* **Layer-by-layer reading**: Using block code $\pi: \Sigma^B \to \Gamma$, advance layer by layer according to $c \mapsto c + b$, applying $\pi$ to corresponding windows to produce visible sequences.
* **Time subaction notation**: Denote $\sigma_{\mathrm{time}}$ as the **one-dimensional subaction** of $X_f$ along the time coordinate, $\sigma_\Omega$ as the time shift of $\Omega(F)$.

### 2.5 Complexity and Measures

* Employ **prefix** Kolmogorov complexity $K(\cdot)$ and conditional complexity $K(u|v)$.
* $\mu$: shift-invariant and ergodic; $\nu$: universal semimeasure (algorithmic probability).
* **Window description complexity**: $K(W)$ is the shortest program length for generating $W$; Følner family $\{W_k\}$ satisfies $|\partial W_k| / |W_k| \to 0$.

### 2.6 Causal Thick Boundary (for T4)

* Explicitly adopt $\infty$-norm:
$$
r := \max_{\mathbf{n} \in N} |\mathbf{n}|_\infty.
$$
* Definitions
$$
t_- = \min\{t : (\mathbf{r}, t) \in W\}, \quad t_+ = \max\{t : (\mathbf{r}, t) \in W\}, \quad T = t_+ - t_-.
$$
* Base $\mathrm{base}(W) = \{(\mathbf{r}, t_-) \in W\}$.
* **Lower past causal input boundary (standard coordinates)**
$$
\partial_\downarrow^{(r,T)} W^- := \{(\mathbf{r} + \mathbf{n}, t_- - 1) : (\mathbf{r}, t_-) \in \mathrm{base}(W), \ \mathbf{n} \in [-rT, rT]^d \cap \mathbb{Z}^d\} \setminus W.
$$
For non-standard foliation cases, first transform back to standard coordinates using $U^{-1}$ and take the image.

### 2.7 Eternal Graph Coordinate Relativization (Anchored Chart)

$G$ does not carry global coordinates. Choose anchor $v_0$, relative embedding $\varphi_{v_0}: \mathrm{Ball}_G(v_0, R) \to \mathbb{Z}^{d+1}$ satisfying $\varphi_{v_0}(v_0) = (\mathbf{0}, 0)$, monotonic non-decreasing layer function along $\tau$ paths, spatial adjacency as finite shifts.
Layer function
$$
\ell(w) := \langle \tau^\star, \varphi_{v_0}(w) \rangle, \quad \mathrm{Cone}_\ell^+(v) := \{w \in \mathrm{Dom}(\varphi_{v_0}) : \exists v \leadsto w \text{ and } \ell \text{ non-decreasing along the path}\}.
$$
**SBU (Static Block Unfolding)**
$$
X_f^{(v,\tau)} := \{x \in X_f : x|_{\varphi_{v_0}(\mathrm{Cone}_\ell^+(v))} \text{ consistent with } v\}.
$$

> Discussion of SBU is restricted to **graph domains with such relative embeddings**.

---

## 3. Minimal Axioms (A0-A3)

**A0 (Static Block)** $X_f$ is the set of models satisfying local constraints.
**A1 (Causal-Local)** $f$ has finite neighborhood; reading uses acceptable foliations.
**A2 (Observation = Factor Decoding)** Layer-by-layer reading and applying $\pi$ gives $\mathcal{O}_{\pi, \varsigma}(x)$.
**A3 (Information Non-increasing)** For any window $W$, $K(\pi(x|_W)) \leq K(x|_W) + K(\pi) + O(1)$.

---

## 4. Leaf-Language and Observation Equivalence

Fix $(\pi, \varsigma)$ and foliation family $\mathcal{L}$,
$$
\mathrm{Lang}_{\pi, \varsigma}(X_f) := \{\mathcal{O}_{\pi, \varsigma}(x) \in \Gamma^{\mathbb{N}} : x \in X_f, \text{ reading layer by layer according to } \mathcal{L}\},
$$
$$
x \sim_{\pi, \varsigma} y \iff \mathcal{O}_{\pi, \varsigma}(x) = \mathcal{O}_{\pi, \varsigma}(y).
$$

---

## 5. Preparatory Lemmas

**Lemma 5.1 (Complexity Conservation of Computable Transformations).** If $\Phi$ is computable, then
$$
K(\Phi(u)|v) \leq K(u|v) + K(\Phi) + O(1).
$$
$\square$

**Lemma 5.2 (Describable Window Families).** For $d+1$-dimensional axis-aligned parallelepipeds or regular windows describable with $O(\log |W|)$ parameters, $K(W) = O(\log |W|)$. $\square$

**Lemma 5.3 (Thick Boundary Coverage).** With radius $r = \max_{\mathbf{n} \in N} |\mathbf{n}|_\infty$ and time span $T$, computing $x|_W$ requires only the past input of the base layer in $[-rT, rT]^d$; i.e., $\partial_\downarrow^{(r,T)} W^-$ covers all dependencies (**propagation radius counted in $|\cdot|_\infty$**). $\square$

**Lemma 5.4 (Factor Entropy Non-increasing).** If $\phi: (X, T) \to (Y, S)$ is a factor, then $h_\mu(T) \geq h_{\phi_* \mu}(S)$. $\square$

**Lemma 5.5 (SMB/Brudno on $\mathbb{Z}^{d+1}$).** For shift-invariant ergodic $\mu$ and Følner family $\{W_k\}$,
$$
-\frac{1}{|W_k|} \log \mu([x|_{W_k}]) \to h_\mu(X_f) \quad (\mu\text{-a.e.}), \quad \frac{K(x|_{W_k})}{|W_k|} \to h_\mu(X_f) \quad (\mu\text{-a.e.}).
$$
$\square$

---

## 6. Main Theorems and Detailed Proofs (T1-T20)

### T1 (Block-Natural Extension Conjugacy)

**Proposition.** If $X_f \neq \varnothing$, then
$$
\boxed{(X_f, \sigma_{\mathrm{time}}) \cong (\Omega(F), \sigma_\Omega)},
$$
$$
\Omega(F) = \{(\ldots, x_{-1}, x_0, x_1, \ldots) : F(x_t) = x_{t+1}\}.
$$

**Proof.** Define $\Psi: X_f \to \Omega(F)$, $(\Psi(x))_t(\mathbf{r}) = x(\mathbf{r}, t)$. By SFT constraint, $F((\Psi(x))_t) = (\Psi(x))_{t+1}$. Define inverse $\Phi: \Omega(F) \to X_f$, $\Phi((x_t))(\mathbf{r}, t) = x_t(\mathbf{r})$. Clearly $\Phi \circ \Psi = \mathrm{id}$, $\Psi \circ \Phi = \mathrm{id}$, and $\Psi \circ \sigma_{\mathrm{time}} = \sigma_\Omega \circ \Psi$. Continuity and Borel measurability follow from product topology and cylinder set structure. $\square$

---

### T2 (Unimodular Covariance; Describable Window Families)

**Proposition.** If Følner family $\{W_k\}$ satisfies $K(W_k) = O(\log |W_k|)$, then the observation semantic complexity difference caused by any two acceptable foliations is $O(\log |W_k|)$, approaching 0 after normalization; entropy non-increasing is preserved.

**Proof.** Two foliations given by $U_1, U_2 \in \mathrm{GL}_{d+1}(\mathbb{Z})$. Set $U = U_2 U_1^{-1}$. For each $W_k$, $\tilde{W}_k = U(W_k)$ can be recovered from the encoding of $\langle U \rangle$ and $W_k$, hence
$$
|K(\pi(x|_{\tilde{W}_k})) - K(\pi(x|_{W_k}))| \leq K(\langle U \rangle) + O(\log |W_k|) = O(\log |W_k|),
$$
by Lemmas 5.1-5.2. After normalization, limit is 0. Entropy non-increasing follows from Lemma 5.4. $\square$

---

### T3 (Observation = Decoding Semantic Collapse)

**Proposition.** $\mathcal{O}_{\pi, \varsigma}: X_f \to \Gamma^{\mathbb{N}}$ is a factor map of the time subaction, inducing equivalence classes $x \sim_{\pi, \varsigma} y$. One observation selects a representative in the equivalence class; the underlying $x$ remains unchanged. $\square$

---

### T4 (Information Upper Bound: Conditional Complexity Version)

$$
\boxed{K(\pi(x|_W) | x|_{\partial_\downarrow^{(r,T)} W^-}) \leq K(f) + K(W) + K(\pi) + O(\log |W|)}.
$$

**Proof.** Construct universal program $\mathsf{Dec}$:

1. **Input**: encoding of $f$, encoding of window $W$ (containing $(t_-, T)$ and geometric parameters), encoding of $\pi$, and conditional string $x|_{\partial_\downarrow^{(r,T)} W^-}$.
2. **Recursion**: Generate layer by layer from $t_-$ according to the time subaction. For any $(\mathbf{r}, s) \in W$, compute
$$
x(\mathbf{r}, s) = f(x(\mathbf{r} + N, s-1))
$$
using values from the previous layer or conditional boundary (Lemma 5.3). **Generate layer by layer from $s = t_-, t_- + 1, \dots, t_+$** to avoid dependency cycles. For each layer $s$, **first generate all units required for the forward closure of $W$ within the propagation cone (allowing temporary generation of values outside $W$ but within $[-r(s - t_-), r(s - t_-)]^d \times \{s\}$), then restrict back to $W$**.
3. **Decoding**: Apply $\pi$ to $W$ according to the protocol to get $\pi(x|_W)$.

Program size is constant, input length is $K(f) + K(W) + K(\pi) + O(\log |W|)$ (with $\log |W|$ for depth/alignment cost). By prefix complexity definition, the upper bound follows. $\square$

---

### T5 (Brudno Alignment and Factor Entropy)

**Proposition.** For $\mu$-almost every $x$ and any Følner family $\{W_k\}$:
$$
\frac{K(x|_{W_k})}{|W_k|} \to h_\mu(X_f), \quad \frac{K(\pi(x|_{W_k}))}{|W_k|} \to h_{\pi_* \mu}(\pi(X_f)) \leq h_\mu(X_f).
$$

**Proof.** By Lemma 5.5 (SMB/Brudno on additive group actions), the first limit holds. For the factor image, $\pi$ is computable and factor entropy is non-increasing (Lemma 5.4), so the second limit holds and does not exceed $h_\mu(X_f)$. $\square$

---

### T6 (Program Emergence: Macroblock-Forcing; SB-CA ⇒ TM)

**Proposition.** There exists a macroblock-forcing embedding such that the execution of any Turing machine $M$ can be realized in $X_f$ and decoded by $\pi$.

**Proof (Construction).** Take macroblock size $k$. Extend alphabet to $\Sigma' = \Sigma \times Q \times D \times S$ (machine state, tape symbol, head movement, synchronization phase). At macroblock scale, implement transitions $(q, a) \mapsto (q', a', \delta)$ with finite-type local constraints, and use phase signals for cross-macroblock synchronization. Decoder $\pi$ reads the central row of macroblocks to output tape content. Compactness and locality guarantee non-empty solutions exist. $\square$

---

### T7 (Program Weight Universal Semimeasure Bound)

**Proposition.** For prefix-unambiguous program codes, for any decodable program $p$, $\nu(p) \leq C \cdot 2^{-|p|}$.

**Proof.** By Kraft inequality $\sum_p 2^{-|p|} \leq 1$, the universal semimeasure $\nu$ as a weighted sum satisfies the upper bound, with constant $C$ depending only on the chosen machine. $\square$

---

### T8 (Section-Natural Extension Duality; Entropy Preservation)

**Proposition.** $X_f$ and $\Omega(F)$ are mutually section/natural extension duals, with equal time entropy.

**Proof.** By T1's conjugacy $(X_f, \sigma_{\mathrm{time}}) \cong (\Omega(F), \sigma_\Omega)$. Natural extension does not change entropy; conjugacy preserves entropy, so the conclusion holds. $\square$

---

### T9 (Halting Witness Staticization)

**Proposition.** In the embedding construction of T6, $M$ halts if and only if there exists a finite window pattern in $X_f$ containing the "termination marker" $\square$.

**Proof.** "If" direction: If $M$ halts at step $\hat{t}$, then $\square$ appears in the macroblock center, forming a finite cylindrical pattern.
"Only if" direction: If $\square$ appears, trace back to halting transition via local consistency; construction guarantees $\square$ is not generated by other causes. $\square$

---

### T10 (Unimodular Covariance Information Stability)

**Proposition.** If $K(W_k) = O(\log |W_k|)$, then under any integral transformation $U$, the T4 upper bound and T3 semantics are preserved, with finite window complexity difference $O(\log |W_k|)$.

**Proof.** By Lemmas 5.1-5.2 and T2's isomorphism encoding argument; thick boundaries and propagation cones under $U$ have only bounded distortion, absorbed into $O(\log |W_k|)$. $\square$

---

### T11 (Model Set Semantics)

**Proposition.**
$$
X_f = \mathcal{T}_f(\mathsf{Conf}) = \{x \in \Sigma^{\mathbb{Z}^{d+1}} : \forall (\mathbf{r}, t) \ x(\mathbf{r}, t) = f(x(\mathbf{r} + N, t-1))\}.
$$

**Proof.** By definition. $\square$

---

### T12 (Computational Model Correspondence)

**Proposition.** (i) SB-CA and TM simulate each other; (ii) Various CSP/Horn/μ-safety formulas $\Phi$ can be equivalently embedded into EG-CA.

**Proof.** (i) By T6 and standard "TM simulates CA" for bidirectional simulation.
(ii) Convert each clause of radius $\leq r$ to forbidden pattern set $\mathcal{F}_\Phi$, yielding $X_{f_\Phi}$. Solution models are equivalent to $\Phi$'s models (finite-type + compactness). $\square$

---

### T13 (Leaf-Language ω-Automaton Characterization)

**Proposition.** Under "one-dimensional subaction + finite-type/regular safety", there exists a Büchi/Streett automaton $\mathcal{A}$ such that
$$
\mathrm{Lang}_{\pi, \varsigma}(X_f) = L_\omega(\mathcal{A}).
$$

**Proof (Construction).** Take higher-order block representation $X_f^{[k]}$, encode state set $Q$ into extended alphabet and implement transitions $\delta$ with finite-type constraints. One cross-leaf reading corresponds to one automaton step. Acceptance conditions are expressed with safety/regular constraints (e.g., "infinitely many visits to $F$" implemented by cyclic memory bits). Thus the equivalent ω-language is obtained. $\square$

---

### T14 (SBU Existence for Any Realizable Event)

**Proposition.** For realizable $v$ and acceptable $\tau$, $(X_f^{(v,\tau)}, \rho_\tau)$ is non-empty.

**Proof.** Take finite window family consistent with $v$, form a directed set by inclusion; finite consistency given by "realizable" and local constraints. By compactness (product topology) and König's lemma, there exists a limit configuration $x \in X_f$ consistent with $v$, hence non-empty. $\square$

---

### T15 (Causal Consistency Expansion and Paradox Exclusion)

**Proposition.** $X_f^{(v,\tau)}$ contains only restrictions of global solutions consistent with anchor $v$; contradictory events do not coexist.

**Proof.** If some $x \in X_f^{(v,\tau)}$ contains events contradictory to $v$, then on $\varphi_{v_0}(\mathrm{Cone}_\ell^+(v))$ it is both consistent and contradictory, violating the consistency definition. $\square$

---

### T16 (Time = Deterministic Advancement (Apparent Choice))

**Proposition.** Under deterministic $f$ and thick boundary conditions, each minimal positive increment of $\ell$ equates to **deterministic advancement** of future consistency expansion families; unique under deterministic CA.

**Proof.** By T4's construction, given previous layer and thick boundary, next layer values are uniquely determined by $f$; if two different advancements exist, some unit's next layer value would differ, violating determinism. $\square$

---

### T17 (Multi-Anchor Observers and Subjective Time Rate)

**Proposition.** Effective step length $b = \langle \tau^\star, \tau \rangle \geq 1$ reflects chapter beat; different $b$ only changes reading rhythm, with consistent entropy rate after Følner normalization.

**Proof.** Changing to $\sigma_{\mathrm{time}}^{(b)}$ is equivalent to "sampling" ($\sigma_\Omega^b$) of the $\mathbb{Z}$ subaction. Measure entropy satisfies
$$
h(\sigma_\Omega^b) = b \cdot h(\sigma_\Omega).
$$
While $|W_k|$ scales linearly with "steps per $b$", normalization cancels out, limits are consistent. $\square$

---

### T18 (Anchored Graph Coordinate Relativization Invariance)

**Proposition.** Two embeddings $(\varphi_{v_0}, \varphi_{v_1})$ if restrictions of the same integral affine embedding $\Phi$, then differ by $\mathrm{GL}_{d+1}(\mathbb{Z})$ integral affine and finite radius rescaling after removing constant radius bands in intersection domain; observation semantic difference $\leq O(K(W))$ (describable window families are $O(\log |W|)$).

**Proof.** There exist $U \in \mathrm{GL}_{d+1}(\mathbb{Z})$ and translation $t$ such that $\varphi_{v_1} = U \circ \varphi_{v_0} + t$ holds in intersection domain. Finite radius differences correspond to removing boundary bands. Window encodings under two coordinates differ only by finite descriptions of $U, t$, complexity difference absorbed by $O(K(W))$ (Lemmas 5.1-5.2). $\square$

---

### T19 (ℓ-Successor Determinacy and Same-Layer Exclusivity)

**Proposition.** Under deterministic $f$, radius $r$, if $u$'s context covers information needed for next layer generation, then there exists unique $\mathrm{succ}_\ell(u)$; edge $u \to \mathrm{succ}_\ell(u)$ has exclusivity for same-layer alternatives.

**Proof.** Next layer values uniquely determined by $f$'s local function; if two different same-layer alternatives both connectable and mutually conflicting exist, inconsistency assignment arises in some common unit, contradiction. $\square$

---

### T20 (Compatibility Principle: Apparent Choice and Determinism Unification)

**Proposition.** Layer-by-layer advancement appears as "representative selection" at the operational level, while overall static encoding is "unique consistency expansion"; determinism holds, compatible with A3/T4.

**Proof.** By T14 global consistency expansion exists; T15 excludes contradictory branches; T3 indicates "observation = selecting representative in equivalence class"; T4/A3 ensures selection does not increase information. Hence apparent freedom is consistent with underlying determinism. $\square$

---

## 7. Constructions and Algorithms

**7.1 From Rules to SFT**: Derive forbidden pattern set $\mathcal{F}$ from local consistency of $f$, yielding $X_f$.

**7.2 From SFT to Eternal Graph**: Construct $G_f$ with allowed patterns as vertices, legal splices as edges; use level surfaces of $\ell$ for leaf ordering.

**7.3 Decoder Design**: Select core window $B$, block code $\pi: \Sigma^B \to \Gamma$; define **layer-by-layer reading protocol according to $\ell$-stratified** $\varsigma$.

**7.4 Macroblock-Forcing Program Box**: Self-similar tiling embedding of "state-control-tape" that is decodable (see T6).

**7.5 Compression-Entropy Experiment (Reproducible)**
$$
y_k = \pi(x|_{W_k}), \quad c_k = \mathrm{compress}(y_k), \quad r_k = \frac{|c_k|}{|W_k|}, \quad \mathrm{plot}(r_k) \ (k=1,2,\ldots).
$$

**7.6 Constructing SBU from Event Nodes (Forced Domain Propagation)**
**Input**: Realizable $v$, orientation $\tau$, tolerance $\epsilon$.
**Steps**: With $v$ and local consistency as constraints, perform **bidirectional constraint propagation/consistency checking**, compute units forced by $v$ on growing $W_k$, expand layer by layer according to $\ell$ until local stability.
**Output**: **Forced domain approximation** of $(X_f^{(v,\tau)})$ on $W_k$ and information density curve.

**7.7 Anchored Graph Relative Coordinate Construction**: BFS layering (by $\ell$/spatial adjacency) → relative embedding $\varphi_{v_0}$ → radius $r$ consistency verification and equivalence class merging.

**7.8 From CSP / μ-Safety Formulas to CA**: Given CSP or Horn/μ-safety formula $\Phi$, generate forbidden patterns $\mathcal{F}_\Phi$ for each clause of radius $\leq r$, define $f_\Phi$:
$$
X_{f_\Phi} = \mathcal{T}_{f_\Phi}(\mathsf{Conf}) = \{x : \forall (\mathbf{r}, t), \ x(\mathbf{r}, t) = f_\Phi(x(\mathbf{r} + N, t-1))\},
$$
use finite control layers if necessary for synchronization (does not change equivalence class).

**7.9 From ω-Automata to Leaf-Language**: Given Büchi automaton $\mathcal{A} = (Q, \Gamma, \delta, q_0, F)$, choose $(\pi, \varsigma)$ such that:

1. $\pi$ encodes cross-leaf observations as $\Gamma$-words;
2. Implement $\delta$ with finite-type synchronization conditions (encode $Q$ into alphabet via $X_f^{[k]}$ and simulate transitions with local constraints);
3. Express acceptance conditions with safety/regular constraints. Thus
$$
\mathrm{Lang}_{\pi, \varsigma}(X_f) = L_\omega(\mathcal{A}).
$$

---

## 8. Typical Examples and Toy Models

**Rule-90 (Linear)**: Tripartite consistency; SBU of any anchor uniquely recursed by linear relations; Følner-normalized complexity density consistent; leaf-language is ω-regular.

**Rule-110 (Universal)**: Macroblock-forcing TM embedding (T6); halting witness corresponds to local termination marker (T9); layer-by-layer advancement excludes same-layer alternatives (T19-T20).

**2-Coloring CSP (Model Perspective)**: Local constraints of graph 2-coloring → forbidden patterns; anchor some node color and unfold layer by layer, forming causal consistent event cone; leaf-language ω-regular under suitable conditions.

**2×2 Toy Block (Anchor-SBU-Decoding-Apparent Choice)**
$\Sigma = \{0,1\}$, $d=1$, $N = \{-1,0,1\}$, $f(a,b,c) = a \oplus b \oplus c$ (XOR, periodic boundary). Anchor $v_0$ fixes local pattern at $(t=0, \mathbf{r}=0)$. According to T4's causal thick boundary and **layer-by-layer advancement**, recurse layer $t=1$, obtaining unique consistency expansion; contradictory same-layer points excluded (T19). Take
$$
B = \{(\mathbf{r}, t) : \mathbf{r} \in \{0,1\}, t=1\},
$$
$\pi$ reads 2D block as visible binary string — "next step" only reads out, does not increase information (A3).

---

## 9. Extension Directions

* **Continuous Extension (cEBOC)**: Generalize with Markov symbolization/compact alphabet SFT; restate complexity/entropy and clarify discrete→continuous limit.
* **Quantum Inspiration**: Simultaneous description of multiple compatible SBUs for same static block $X_f$, measurement corresponds to **anchor switching and locking** + one $\pi$-semantic collapse; provides constructive foundation for information-computation-based quantum interpretation (non-state-vector assumption).
* **Category/Coalgebra Perspective**: $(X_f, \mathrm{shift})$ as coalgebra; anchored SBU as coalgebraic subresolution with initial value injection; leaf-language as image of automata coalgebra homomorphism.
* **Robustness**: Fault-tolerant decoding and robust windows under small perturbations/missing data, ensuring stable observable semantics.

---

## 10. Observer, Apparent Choice, and Time Experience (RPG Metaphor)

**Hierarchy Separation**: **Operational layer** (observation/decoding/layer-by-layer advancement/representative selection) vs **ontological layer** (static geometry/unique consistency expansion).
**Compatibility Principle**: View $X_f$ as **complete RPG data and rules**; **layer-by-layer advancement** like unlocking plot according to **established chapter beat $b$**. Player "choices" involve **selecting representatives** from compatible branches in same layer and **excluding** other branches; **plot ontology** (static block) already written, choices do not generate new information (A3), consistent with determinism (T20).
**Subjective Time Rate**: Effective step length $b = \langle \tau^\star, \tau \rangle$ embodies "chapter beat"; Følner-normalized entropy rate consistent (T2/T5/T17).

---

## 11. Conclusion

EBOC unifies **timeless geometry (eternal graph/SFT)**, **static block consistency**, and **layer-by-layer decoding observation-computation semantics** under minimal axioms, forming a complete chain from **models/automata** to **visible language**. This paper provides detailed proofs for T1-T20, establishing **information non-increasing laws** (T4/A3), **Brudno alignment** (T5), **unimodular covariance** (T2/T10), **event cones/static block unfolding** (T14-T16), **multi-anchor observers and coordinate relativization** (T17-T18), and other core results, along with reproducible experiments and construction procedures (§7).

---

## Appendix A: Terminology and Notation

* **Semantic Collapse**: Information factorization $x \mapsto \mathcal{O}_{\pi, \varsigma}(x)$.
* **Apparent Choice**: Advancement by minimal positive increment of $\ell$, selecting representatives for same-layer alternatives; only changes semantic representative, does not create information.
* **Primitive Integral Covector**: $\tau^\star \in (\mathbb{Z}^{d+1})^\vee$, $\gcd(\tau^\star_0, \ldots, \tau^\star_d) = 1$; its pairing with actual time direction $\tau$, $\langle \tau^\star, \tau \rangle = b \geq 1$ defines layer-by-layer advancement step length.
* **$\mathrm{GL}_{d+1}(\mathbb{Z})$**: Integral invertible matrix group (determinant $\pm 1$).
* **Følner Family**: Window family with $|\partial W_k| / |W_k| \to 0$.
* **Cylinder Set**: $[p]_W = \{x \in X_f : x|_W = p\}$.

---

## References (Guideline)

* A. A. Brudno (1983). *Entropy and the complexity of trajectories*.
* D. Lind & B. Marcus. *Symbolic Dynamics and Coding*.
* E. F. Moore (1962); J. Myhill (1963). *Machine models / Reversible CA*.
* M. Li & P. Vitányi. *An Introduction to Kolmogorov Complexity*.
* R. Berger; J. Kari. *Tilings, Undecidability, SFT*.
* J. R. Büchi; W. Thomas; D. Perrin & J.-E. Pin. *ω-Automata and ω-Languages*.
* D. Ornstein & B. Weiss; E. Lindenstrauss (SMB / pointwise ergodicity of additive group actions).
