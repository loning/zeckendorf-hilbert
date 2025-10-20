# EBOC: Eternal-Block Observer-Computing Unified Theory

**Author**: Auric
**Date**: 2025-10-18

---

## Abstract

**Goal.** We propose **EBOC (Eternal-Block Observer-Computing)**: a geometry-information unified framework without explicit global time, merging the **timeless causal encoding** of **Eternal-Graph Cellular Automata** (EG-CA) with the **program semantics and observation-decoding** of **Static-Block Universe Cellular Automata** (SB-CA) within a single formal system, providing verifiable information laws and constructive algorithms. This paper treats the static block $X_f$ and the eternal graph edge shift $(Y_G,\sigma)$ as **equivalent dual representations**; below we primarily narrate through $X_f$, but every conclusion can be equivalently restated on $(Y_G,\sigma)$ via finite-type presentation/encoding equivalence.

**Three Pillars.**

1. **Geometric Encoding (Graph/SFT)**: The universe as a **static block** $X_f\subset\Sigma^{\mathbb{Z}^{d+1}}$ satisfying local rule $f$; its causality/consistency is characterized in parallel by the **eternal graph** $G=(V,E)$ and **subshift (SFT)**.
2. **Semantic Emergence (Observation = Decoding)**: **Observation = factor decoding**. The decoder $\pi:\Sigma^{B}\to\Gamma$ reads the static block **leaf-by-leaf according to acceptable foliation** (cross-leaf reading advancing from layer $c$ to $c+b$ along $\tau$), outputting visible language; "semantic collapse" is the **information factorization** from underlying configuration to visible record.
3. **Information Constraint (Non-increase Law)**: Observation does not create information:
$$
K\big(\pi(x|_W)\big)\ \le\ K(x|_W)+K(\pi)+O(1),
$$
and under **causal thick boundary** provides upper bounds on **conditional complexity** and entropy limits consistent with Brudno.

**Unified Metaphor (RPG Game).** The universe is like an **infinite-plot RPG**: **game data and evolution rules** are already written ($(X_f,f)$), "choices" (apparent free will) must be consistent with the **storyline** (determinism). **Leaf-by-leaf reading** unlocks chapters progressively at the established pace $b$; "choice" is **selecting a representative** among compatible branches and **excluding** incompatible branches—the ontological "ROM" neither increases nor decreases information.

**Core Object.**
$$
\mathcal U=(X_f, G, \rho, \Sigma, f, \pi, \mu, \nu),
$$
where $X_f$ is the space-time SFT, $G$ is the eternal graph, $\rho$ provides the **acceptable leaf family** (level sets of the primitive integral covector $\tau^\star$, $\langle\tau^\star,\tau\rangle=b\ge1$), $\pi$ is the decoder, $\mu$ is a shift-invariant ergodic measure, and $\nu$ is the universal semimeasure (serving only as typicality weight). Equivalently, all results can be expressed via the **edge shift** $Y_G$ and its **path shift** $(Y_G,\sigma)$ of $G$; observation/information laws hold equally for both representations.

---

## 1. Introduction and Motivation

Traditional CA presents "evolution" through global time iteration; the block/eternal-graph perspective gives the entire spacetime at once, with "evolution" being merely a **path narrative obtained by leaf-by-leaf reading**. The dynamical viewpoint depends on a time background and is difficult to make background-independent; the static viewpoint lacks observational semantics. EBOC unifies the two through "**geometric encoding × semantic decoding × information law**": SFT/graph structure ensures consistency and constructiveness; factor mapping provides visible language; complexity/entropy characterizes conservation and limits. This paper establishes the theorem family T1–T20 under minimal axioms, providing refined proofs and reproducible experimental procedures.

---

## 2. Notation and Preliminaries

### 2.1 Space, Alphabet, and Configuration

* Space $L=\mathbb{Z}^{d}$, spacetime $L\times\mathbb{Z}=\mathbb{Z}^{d+1}$; finite alphabet $\Sigma$.
* Spacetime configuration $x\in \Sigma^{\mathbb{Z}^{d+1}}$. Restriction of window $W\subset\mathbb{Z}^{d+1}$ is $x|_W$.
* Convention: $|\cdot|$ denotes both string length and set cardinality (distinguished by context).

### 2.2 Neighborhood and Global Evolution

* Finite neighborhood $N\subset \mathbb{Z}^{d}$, local rule $f:\Sigma^{|N|}\to\Sigma$:
$$
x(\mathbf r+N,t)\coloneqq\big(x(\mathbf r+\mathbf n,t)\big)_{\mathbf n\in N}\in\Sigma^{|N|},\qquad
x(\mathbf r,t)=f\big(x(\mathbf r+N, t-1)\big).
$$
* **Global map**
$$
F:\Sigma^{\mathbb{Z}^{d}}\to\Sigma^{\mathbb{Z}^{d}},\qquad (F(x))(\mathbf r)=f\big(x(\mathbf r+N)\big).
$$

### 2.3 SFT and Eternal Graph

* **Space-time SFT**
$$
X_f\ :=\ \Big\{x\in\Sigma^{\mathbb{Z}^{d+1}}:\ \forall(\mathbf r,t),\ x(\mathbf r,t)=f\big(x(\mathbf r+N,t-1)\big)\Big\}.
$$
* **Eternal graph** $G=(V,E)$: vertices $V$ encode local patterns (events), edges $E$ encode causal/consistency relations.
* **Edge shift**
$$
Y_G=\Big\{(e_t)_{t\in\mathbb{Z}}\in\mathcal E^{\mathbb{Z}}:\ \forall t,\ \mathrm{tail}(e_{t+1})=\mathrm{head}(e_t)\Big\}.
$$

### 2.4 Foliation and Leaf-by-Leaf Reading Protocol

* **Unimodular transformation**: $U\in \mathrm{GL}_{d+1}(\mathbb{Z})$ (integer invertible, $\det U=\pm1$), time direction $\tau=Ue_{d+1}$.
* **Acceptable leaf**: There exists a **primitive integral covector** $\tau^\star\in(\mathbb{Z}^{d+1})^\vee$ and constant $c$, with leaves being its level sets
$$
\Big\{\ \xi\in\mathbb{Z}^{d+1}:\ \langle\tau^\star,\xi\rangle=c\ \Big\},
$$
satisfying
$$
\langle\tau^\star, \tau\rangle=b\ge 1,
$$
to ensure **monotonic progression across leaves**.
* **Leaf-by-leaf reading**: Using block code $\pi:\Sigma^B\to\Gamma$, advance leaf-by-leaf from layer $c$ to $c+b$, applying $\pi$ to corresponding windows to produce visible sequence.
* **Temporal subaction notation**: Denote $\sigma_{\mathrm{time}}$ as the **one-dimensional subaction** of $X_f$ along the time coordinate, $\sigma_\Omega$ as the time shift of $\Omega(F)$.

### 2.5 Complexity and Measure

* We adopt **prefix** Kolmogorov complexity $K(\cdot)$ and conditional complexity $K(u|v)$.
* $\mu$: shift-invariant and ergodic; $\nu$: universal semimeasure (algorithmic probability).
* **Window description complexity**: $K(W)$ is the shortest program length generating $W$; Følner family $\{W_k\}$ satisfies $|\partial W_k|/|W_k|\to 0$.

### 2.6 Causal Thick Boundary (for T4)

* We explicitly adopt the $\infty$-norm:
$$
r\ :=\ \max_{\mathbf n\in N}\ |\mathbf n|_{\infty}.
$$
* Define
$$
t_-=\min\Big\{t:(\mathbf r,t)\in W\Big\},\quad
t_+=\max\Big\{t:(\mathbf r,t)\in W\Big\},\quad
T=t_+-t_-.
$$
* Base layer $\mathrm{base}(W)=\Big\{(\mathbf r,t_-)\in W\Big\}$.
* **Past causal input boundary of base layer (standard coordinates)**
$$
\partial_{\downarrow}^{(r,T)}W^-\ :=\ \Big\{(\mathbf r+\mathbf n,\ t_--1)\ :\ (\mathbf r,t_-)\in\mathrm{base}(W),\ \mathbf n\in[-rT,rT]^d\cap\mathbb{Z}^d\Big\}\setminus W.
$$
For non-standard leaf cases, take the image after first returning to standard coordinates via $U^{-1}$.

### 2.7 Coordinate Relativization of Eternal Graph (Anchored Chart)

$G$ carries no global coordinates. Choose anchor $v_0$, relative embedding $\varphi_{v_0}:\mathrm{Ball}_G(v_0,R)\to\mathbb{Z}^{d+1}$ satisfying $\varphi_{v_0}(v_0)=(\mathbf 0,0)$, with path layer function along $\tau$ monotonically non-decreasing, and spatial adjacency as finite shifts.
Layer function
$$
\ell(w):=\langle\tau^\star,\ \varphi_{v_0}(w)\rangle,\qquad
\mathrm{Cone}^+_{\ell}(v):=\Big\{w\in \mathrm{Dom}(\varphi_{v_0})\ :\ \exists\ v\leadsto w\ \text{and }\ell\ \text{non-decreasing along the path}\Big\}.
$$
**SBU (Static Block Unfolding)**
$$
X_f^{(v,\tau)}:=\Big\{x\in X_f:\ x\big|_{\varphi_{v_0}(\mathrm{Cone}^+_{\ell}(v))}\ \text{consistent with }v\Big\}.
$$

### 2.8 Eternal Graph–SFT Dual Representation (Working Principle)

- Dual representation: All conclusions in this paper stated in terms of static block $X_f$ have an equivalent version in terms of eternal graph edge shift $(Y_G,\sigma)$; the two are mutually related through standard finite-type presentation/encoding. For brevity, the main text primarily uses $X_f$, with path version statements bracketed as "(EG)" where necessary.
- Correspondence: Window $W$ and thick boundary correspond to finite path segments and finite adjacency radius; leaf-by-leaf reading corresponds to time-shift reading along paths; the definition of observation factor $\pi$ on $X_f$ can be equivalently realized on $Y_G$ through path block code $\pi_G$.


> Below we discuss SBU only **on the graph domain where such relative embedding exists**.

**Definition: Realizable Event.** Given eternal graph $G=(V,E)$. Call $v\in V$ **realizable** if there exists $x\in X_f$ with some relative embedding $\varphi_{v_0}$ and radius $R$ such that $x\big|_{\varphi_{v_0}(\mathrm{Ball}_G(v,R))}$ is consistent with the local pattern of $v$ (according to the "local pattern → vertex" encoding convention in the text).

---

## 3. Minimal Axioms (A0–A3)

**A0 (Static Block)** $X_f$ is the model set of local constraints.
**A1 (Causal-Local)** $f$ has finite neighborhood; reading uses acceptable leaves.
**A2 (Observation = Factor Decoding)** Leaf-by-leaf reading with application of $\pi$ yields $\mathcal O_{\pi,\varsigma}(x)$.
**A3 (Information Non-increase)** For any window $W$, $K(\pi(x|_W))\le K(x|_W)+K(\pi)+O(1)$.

---

## 4. Leaf-Language and Observation Equivalence

Fix $(\pi,\varsigma)$ and leaf family $\mathcal L$,
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f):=\Big\{\ \mathcal O_{\pi,\varsigma}(x)\in\Gamma^{\mathbb N}:\ x\in X_f,\ \text{leaf-by-leaf reading stratified by }\mathcal L\ \Big\},
\qquad
x\sim_{\pi,\varsigma}y\iff \mathcal O_{\pi,\varsigma}(x)=\mathcal O_{\pi,\varsigma}(y).
$$

---

## 5. Preparatory Lemmas

**Lemma 5.1 (Complexity Conservation under Computable Transformation).** If $\Phi$ is computable, then
$$
K\big(\Phi(u)|v\big)\ \le\ K\big(u|v\big)+K(\Phi)+O(1).
$$
$\square$

**Lemma 5.2 (Describable Window Families).** For $d+1$ dimensional axis-aligned parallelepipeds or regular windows described by $O(\log |W|)$ parameters, we have $K(W)=O(\log|W|)$. $\square$

**Lemma 5.3 (Thick Boundary Coverage).** Under radius $r=\max_{\mathbf n\in N}|\mathbf n|_\infty$ and time span $T$, computing $x|_W$ requires only the past input from the previous layer of $\mathrm{base}(W)$ within $[-rT,rT]^d$; i.e., $\partial_{\downarrow}^{(r,T)}W^-$ covers all dependencies (**propagation radius measured in $|\cdot|_\infty$**). $\square$

**Lemma 5.4 (Factor Entropy Non-increase).** If $\phi:(X,T)\to(Y,S)$ is a factor, then $h_\mu(T)\ge h_{\phi_\ast\mu}(S)$. $\square$

**Lemma 5.5 (SMB/Brudno on $\mathbb{Z}^{d+1}$).** For shift-invariant ergodic $\mu$ and Følner family $\{W_k\}$,
$$
-\frac1{|W_k|}\log \mu\big([x|_{W_k}]\big)\ \to\ h_\mu(X_f)\quad (\mu\text{-a.e.}),\qquad
\frac{K(x|_{W_k})}{|W_k|}\ \to\ h_\mu(X_f)\quad (\mu\text{-a.e.}).
$$
$\square$

---

## 6. Main Theorems and Detailed Proofs (T1–T20)

### T1 (Block–Natural Extension Conjugacy)

**Proposition.** If $X_f\neq\varnothing$, then
$$
\boxed{ (X_f,\ \sigma_{\mathrm{time}})\ \cong\ (\Omega(F),\ \sigma_\Omega) },
\quad
\Omega(F)=\Big\{(\ldots,x_{-1},x_0,x_1,\ldots):\ F(x_t)=x_{t+1}\Big\}.
$$

**Proof.** Define $\Psi:X_f\to\Omega(F)$, $(\Psi(x))_t(\mathbf r)=x(\mathbf r,t)$. By SFT constraint we have $F((\Psi(x))_t)=(\Psi(x))_{t+1}$. Define inverse $\Phi:\Omega(F)\to X_f$, $\Phi((x_t))(\mathbf r,t)=x_t(\mathbf r)$. Clearly $\Phi\circ\Psi=\mathrm{id}$, $\Psi\circ\Phi=\mathrm{id}$, and $\Psi\circ\sigma_{\mathrm{time}}=\sigma_\Omega\circ\Psi$. Continuity and Borel measurability follow from product topology and cylinder set structure. $\square$

---

### T2 (Unimodular Covariance; Describable Window Families)

**Proposition.** If Følner family $\{W_k\}$ satisfies $K(W_k)=O(\log|W_k|)$, then the observation semantic complexity difference induced by any two acceptable leaf families is $O(\log|W_k|)$, tending to 0 after normalization; entropy non-increase is preserved.

**Proof.** Two leaf families are given by $U_1,U_2\in\mathrm{GL}_{d+1}(\mathbb Z)$. Set $U=U_2U_1^{-1}$. For each $W_k$, $\tilde W_k=U(W_k)$ can be recovered from the description of $\langle U\rangle$ and the encoding of $W_k$, so
$$
\big|K(\pi(x|_{\tilde W_k}))-K(\pi(x|_{W_k}))\big|\ \le\ K(\langle U\rangle)+O(\log|W_k|)=O(\log|W_k|),
$$
by Lemmas 5.1–5.2. After normalization the limit is 0. Entropy non-increase follows from Lemma 5.4. $\square$

---

### T3 (Observation = Semantic Collapse via Decoding)

**Proposition.** $\mathcal O_{\pi,\varsigma}:X_f\to\Gamma^{\mathbb N}$ is a factor map of the time subaction, inducing equivalence classes $x\sim_{\pi,\varsigma}y$. One observation selects a representative within the equivalence class; the underlying $x$ remains unchanged. $\square$

---

### T4 (Information Upper Bound: Conditional Complexity Version)

$$
\boxed{ K\Big(\ \pi(x|_{W})\ \Big|\ x\big|_{\partial_{\downarrow}^{(r,T)} W^-}\Big)\ \le\ K(f)+K(W)+K(\pi)+O(\log |W|) }.
$$

**Proof.** Construct universal program $\mathsf{Dec}$:

1. **Input**: Encoding of $f$, encoding of window $W$ (including $(t_-,T)$ and geometric parameters), encoding of $\pi$, and conditional string $x|_{\partial_{\downarrow}^{(r,T)}W^-}$.
2. **Recursion**: Starting from layer $t_-$, generate layer by layer according to time subaction. For any $(\mathbf r,s)\in W$, compute via
$$
x(\mathbf r,s)=f\big(x(\mathbf r+N,s-1)\big);
$$
the required right-hand side is either already generated from the previous layer or comes from the conditional boundary (Lemma 5.3). **Generate layer by layer for $s=t_-,t_-+1,\dots,t_+$**, avoiding dependency cycles. For each layer $s$, **first generate all cells within the propagation cone needed for the forward closure of $W$ (allowing temporary production of values outside $W$ but within $[-r(s-t_-)$, $r(s-t_-)]^d \times \{s\}$), finally restricting to $W$**.
3. **Decoding**: Apply $\pi$ within $W$ according to protocol to obtain $\pi(x|_W)$.

The program body has constant size, input length is $K(f)+K(W)+K(\pi)+O(\log|W|)$ ($\log|W|$ for layer depth/alignment cost). The upper bound follows immediately from the prefix complexity definition. $\square$

---

### T5 (Brudno Alignment and Factor Entropy)

**Proposition.** For $\mu$-almost every $x$ and any Følner family $\{W_k\}$:
$$
\frac{K(x|_{W_k})}{|W_k|}\ \to\ h_\mu(X_f),\qquad
\frac{K(\pi(x|_{W_k}))}{|W_k|}\ \to\ h_{\pi_\ast\mu}\big(\pi(X_f)\big)\ \le\ h_\mu(X_f).
$$

**Proof.** By Lemma 5.5 (SMB/Brudno on amenable group actions), the first limit holds. For the factor image, $\pi$ is a computable transformation and factor entropy is non-increasing (Lemma 5.4), so the second limit holds and does not exceed $h_\mu(X_f)$. $\square$

---

### T6 (Program Emergence: Macroblock-Forcing; SB-CA $\Rightarrow$ TM)

**Proposition.** There exists a macroblock-forcing embedding such that the run of any Turing machine $M$ can be realized in $X_f$ and decoded by $\pi$.

**Proof (Construction).** Take macroblock size $k$. Extend alphabet to $\Sigma'=\Sigma\times Q\times D\times S$ (machine state, tape symbol, head movement, synchronization phase). At macroblock scale, implement transition $(q,a)\mapsto (q',a',\delta)$ via finite-type local constraints, and implement cross-macroblock synchronization via phase signals. Decoder $\pi$ reads the center row of macroblocks to output tape content. Compactness and locality ensure non-empty solutions exist. $\square$

---

### T7 (Program Weight Universal Semimeasure Bound)

**Proposition.** Let program code be prefix-free, then for any decodable program $p$, we have $\nu(p)\le C\cdot 2^{-|p|}$.

**Proof.** By Kraft inequality $\sum_p2^{-|p|}\le1$, the universal semimeasure $\nu$ as a weighted sum satisfies the upper bound, with constant $C$ depending only on the chosen machine. $\square$

---

### T8 (Section–Natural Extension Duality; Entropy Preservation)

**Proposition.** $X_f$ and $\Omega(F)$ are mutually section/natural-extension duals, with equal temporal entropy.

**Proof.** By the conjugacy $(X_f,\sigma_{\mathrm{time}})\cong (\Omega(F),\sigma_\Omega)$ from T1. Natural extension does not change entropy; conjugacy preserves entropy, so the conclusion holds. $\square$

---

### T9 (Staticization of Halting Witness)

**Proposition.** In the embedding construction of T6, $M$ halts if and only if there exists a finite window pattern in $X_f$ containing the "termination marker" $\square$.

**Proof.** "If" direction: If $M$ halts at step $\hat t$, then $\square$ appears in the macroblock center, forming a finite columnar pattern.
"Only if" direction: If $\square$ appears, backtrack to the halting transition via local consistency; the construction ensures $\square$ is not produced by other causes. $\square$

---

### T10 (Information Stability under Unimodular Covariance)

**Proposition.** If $K(W_k)=O(\log|W_k|)$, then under any integer transformation $U$ the T4 upper bound and T3 semantics are preserved, with finite window complexity difference $O(\log|W_k|)$.

**Proof.** By Lemmas 5.1–5.2 and the isomorphic encoding argument of T2; thick boundary and propagation cone undergo only bounded distortion under $U$, absorbed into $O(\log|W_k|)$. $\square$

---

### T11 (Model Set Semantics)

**Proposition.**
$$
X_f=\mathcal T_f(\mathsf{Conf})=\Big\{x\in\Sigma^{\mathbb{Z}^{d+1}}:\forall(\mathbf r,t)\ x(\mathbf r,t)=f(x(\mathbf r+N,t-1))\Big\}.
$$
**Proof.** By definition. $\square$

---

### T12 (Computational Model Correspondence)

**Proposition.** (i) SB-CA and TM mutually simulate each other; (ii) CSP/Horn/$\mu$-safety formulas $\Phi$ can be equivalently embedded in EG-CA.

**Proof.** (i) By T6 and standard "TM simulates CA" we obtain bidirectional simulation.
(ii) Convert each clause with radius $\le r$ into forbidden pattern set $\mathcal F_\Phi$, obtaining $X_{f_\Phi}$. Solution models are equivalent to models of $\Phi$ (finite-type + compactness). $\square$

---

### T13 (Leaf-Language $\omega$-Automaton Characterization)

**Proposition.** Under "one-dimensional subaction + finite-type/regular safety", there exists a Büchi/Streett automaton $\mathcal A$ such that
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f)=L_\omega(\mathcal A).
$$

**Proof (Construction).** Take higher-order block representation $X_f^{[k]}$, encode state set $Q$ into extended alphabet and implement transition $\delta$ via finite-type constraints (simulating transitions via local constraints after encoding $Q$ into the alphabet via $X_f^{[k]}$). Cross-leaf reading once corresponds to one automaton step. Acceptance condition is expressed via local safety/regularity constraints (e.g., "infinitely often visiting $F$" implemented via cyclic memory bits). Thus we obtain the equivalent $\omega$-language. $\square$

---

### T14 (Existence of SBU for Any Realizable Event)

**Proposition.** For realizable $v$ and acceptable $\tau$, $\big(X_f^{(v,\tau)},\rho_\tau\big)$ is non-empty.

**Proof.** Take finite window families consistent with $v$, forming a directed set under inclusion; finite consistency follows from "realizability" and local constraints. By compactness (product topology) and König's lemma, there exists a limit configuration $x\in X_f$ consistent with $v$, hence non-empty. $\square$

---

### T15 (Causal Consistent Extension and Paradox Exclusion)

**Proposition.** $X_f^{(v,\tau)}$ contains only restrictions of global solutions consistent with anchor $v$; contradictory events do not coexist.

**Proof.** If some $x\in X_f^{(v,\tau)}$ simultaneously contains an event contradicting $v$, then on $\varphi_{v_0}(\mathrm{Cone}^+_\ell(v))$ it is both consistent and contradictory, violating the consistency definition. $\square$

---

### T16 (Time = Deterministic Progression (Apparent Choice))

**Proposition.** Under deterministic $f$ and thick boundary conditions, each minimal positive increment of $\ell$ is equivalent to **deterministic progression** on the family of future consistent extensions; under deterministic CA it is unique.

**Proof.** By the construction of T4, given the previous layer and thick boundary, the next layer values are uniquely defined by $f$; if two different progressions exist, then the next-layer value of some cell differs, violating determinism. $\square$

---

### T17 (Multi-Anchor Observers and Subjective Time Rate)

**Proposition.** Effective step size $b=\langle\tau^\star,\tau\rangle\ge 1$ reflects chapter pacing; different $b$ only change reading rhythm, with entropy rate consistent after Følner normalization.

**Proof.** Time subaction changed to $\sigma_{\mathrm{time}}^{(b)}$ is equivalent to "sampling" the $\mathbb{Z}$ subaction ($\sigma_\Omega^b$). Measure entropy satisfies
$$
h(\sigma_\Omega^b)\ =\ b\cdot h(\sigma_\Omega).
$$
And $|W_k|$ under "each step crosses $b$" also scales linearly, canceling after normalization, with consistent limit. $\square$

---

### T18 (Coordinate Relativization Invariance of Anchored Graph)

**Proposition.** If two embeddings $(\varphi_{v_0},\varphi_{v_1})$ are restrictions of the same integer affine embedding $\Phi$, then after removing constant-radius bands from the intersection domain, they differ only by $\mathrm{GL}_{d+1}(\mathbb Z)$ integer affine and finite-radius relabeling; observation semantic difference $\le O(K(W))$ (for describable window families $O(\log|W|)$).

**Proof.** There exists $U\in\mathrm{GL}_{d+1}(\mathbb Z)$ and translation $t$ such that $\varphi_{v_1}=U\circ\varphi_{v_0}+t$ holds on the intersection domain. Finite-radius discrepancies correspond to removing boundary bands. Window encoding in two coordinates differs only by the finite description of $U,t$, with complexity difference absorbed by $O(K(W))$ (Lemmas 5.1–5.2). $\square$

---

### T19 ($\ell$-Successor Determinism and Same-Layer Exclusivity)

**Proposition.** Under deterministic $f$ and radius $r$, if the context of $u$ covers the information needed for next-layer generation, then there exists unique $\mathrm{succ}_\ell(u)$; the edge $u\to\mathrm{succ}_\ell(u)$ is exclusive to same-layer alternatives.

**Proof.** Next-layer values are uniquely determined by the local function of $f$; if two different same-layer alternatives can both continue and mutually conflict, then they produce inconsistent assignment at some common cell, contradiction. $\square$

---

### T20 (Compatibility Principle: Unification of Apparent Choice and Determinism)

**Proposition.** Leaf-by-leaf progression appears operationally as "representative selection", while globally statically encoded as "unique consistent extension"; determinism holds and is compatible with A3/T4.

**Proof.** By T14 there exists a global consistent extension; T15 excludes contradictory branches; T3 shows "observation = selecting representative in equivalence class"; T4/A3 ensure selection does not increase information. Thus apparent freedom and ontological determinism are consistent. $\square$

---

### T21 (Information Non-increase Law: General CA and Observation Factor)

**Proposition.** Let $F$ be a radius-$r$ $d$-dimensional CA, take any Følner window family $\{W_k\}$ (axis-aligned parallelepipeds satisfying $K(W_k)=O(\log|W_k|)$). Define information density
$$
I(x):=\limsup_{k\to\infty}\frac{K\big(x|_{W_k}\big)}{|W_k|},\qquad
I_\pi(x):=\limsup_{k\to\infty}\frac{K\big(\pi(x|_{W_k})\big)}{|W_k|}.
$$
Then for each fixed $T\in\mathbb N$ and configuration $x$,
$$
I\big(F^T x\big)\ \le\ I(x),\qquad I_\pi\big(F^T x\big)\ \le\ I\big(F^T x\big)\ \le\ I(x).
$$

**Proof.** Thick boundary and propagation cone provide dependency domain: there exists $W_k^{+rT}$ such that $\big(F^T x\big)|_{W_k}$ can be computably recovered from $x|_{W_k^{+rT}}$ (see Lemma 5.3's $r,T$ control). By complexity upper bound of computable transformation,
$$
K\big((F^T x)|_{W_k}\big)\ \le\ K\big(x|_{W_k^{+rT}}\big)+O(\log|W_k|).
$$
Følner property gives $|W_k^{+rT}|/|W_k|\to1$, taking $\limsup$ yields $I(F^T x)\le I(x)$. Factor decoding does not increase information (A3, or Lemma 5.1's computable transformation), yielding $I_\pi(F^T x)\le I(F^T x)$. Combining gives the conclusion. $\square$

---

### T22 (Information Conservation Law: Reversible CA)

**Proposition.** If $F$ is reversible and $F^{-1}$ is also a CA (reversible cellular automaton), then for each fixed $T\in\mathbb N$ and configuration $x$,
$$
I\big(F^T x\big)=I(x),\qquad I_\pi\big(F^T x\big)\ \le\ I(x),
$$
with equality in the second when $\pi=\mathrm{id}$ or a lossless factor conjugate with $F$. If $\mu$ is a shift-invariant ergodic measure, then Brudno limit and entropy invariance give $h_\mu= h_{F_\ast\mu}$, hence information density conservation $\mu$-almost everywhere.

**Proof.** By T21 applied to $F$ and $F^{-1}$ separately we get $I(F^T x)\le I(x)$ and $I(x)\le I(F^T x)$, combining gives $I(F^T x)=I(x)$. Non-increase for $\pi$ follows from A3. Measure-theoretic version follows from conjugacy $(X_f,\sigma_{\mathrm{time}})\cong(\Omega(F),\sigma_\Omega)$ and entropy preservation under reversibility (T8), combined with Brudno (Lemma 5.5). $\square$

---

### T23 (Observation Pressure Function and Information Geometry)

**Definition.** Take a set of visible categories (given by decoding/counting rules) indexed by $j=1,\dots,J$, with weights $a_j>0$ and vectors $\beta_j\in\mathbb R^n$. Define
$$
Z(\rho)=\sum_{j=1}^{J} a_j\,e^{\,\langle\beta_j,\Re\rho\rangle},\qquad
P(\rho)=\log Z(\rho),\qquad
p_j(\rho)=\frac{a_j e^{\,\langle\beta_j,\Re\rho\rangle}}{Z(\rho)}.
$$
In the domain where $Z(\rho)$ converges, and satisfying standard conditions allowing interchange of summation/differentiation via local uniform convergence, we have
$$
\nabla_{\rho}P(\rho)=\mathbb E_p[\beta]=\sum_j p_j\,\beta_j,\qquad
\nabla_{\rho}^2 P(\rho)=\mathrm{Cov}_p(\beta)\succeq 0.
$$
Thus $P$ is **convex**, with Hessian being the Fisher information. Along direction $\rho(s)=\rho_\perp+s\mathbf v$,
$$
\frac{d^2}{ds^2}P\big(\rho(s)\big)=\mathrm{Var}_p\big(\langle\beta,\mathbf v\rangle\big)\ge0.
$$
If we further denote Shannon entropy $H(\rho)=-\sum_j p_j\log p_j$, then
$$
H(\rho)=P(\rho)-\sum_j p_j\log a_j-\big\langle\Re\rho,\,\mathbb E_p[\beta]\big\rangle.
$$

**Proof Sketch.** By standard differentiation of log-sum-exp (under the aforementioned local uniform convergence conditions allowing interchange of summation and differentiation), we obtain gradient and Hessian expressions; directional second derivative is variance. Entropy identity follows by substituting $p_j\propto a_j e^{\langle\beta_j,\Re\rho\rangle}$ into $H=-\sum p_j\log p_j$ and expanding. $\square$

---

### T24 (Phase Transition/Dominance Switch Criterion)

**Proposition.** Let amplitude $A_j(\rho):=a_j e^{\langle\beta_j,\rho\rangle}$, and define
$$
H_{jk}=\Big\{\rho:\ \langle\beta_j-\beta_k,\rho\rangle=\log\frac{a_k}{a_j}\Big\},\qquad
\delta(\rho):=\min_{j<k}\Big|\ \langle\beta_j-\beta_k,\rho\rangle-\log\frac{a_k}{a_j}\ \Big|.
$$
If $\delta(\rho)>\log(J-1)$, then there exists unique index $j_\star$ such that $A_{j_\star}(\rho)=\max_j A_j(\rho)$ and
$$
\sum_{k\ne j_\star}A_k(\rho)<A_{j_\star}(\rho),
$$
hence no dominance switch; dominance switches can only occur in the thin band $\{\rho:\ \delta(\rho)\le\log(J-1)\}$, whose skeleton is the hyperplane family $\{H_{jk}\}$.

**Proof.** By definition of $\delta(\rho)$, $\log A_{j_\star}-\log A_k\ge\delta(\rho)$, so $A_k\le e^{-\delta(\rho)}A_{j_\star}$, summing gives the conclusion. $\square$

---

### T25 (Directional Pole = Growth Exponent)

**Proposition.** Fix direction $\mathbf v$ and decomposition $\rho=\rho_\perp+s\mathbf v$. Let the weighted cumulative distribution along $\mathbf v$ be
$$
M_{\mathbf v}(t)=\sum_{t_j\le t} w_j,\qquad t_j:=\langle-\beta_j,\mathbf v\rangle,\quad w_j:=a_j e^{\langle\beta_j,\rho_\perp\rangle},
$$
when $t\to+\infty$ has exponential–polynomial asymptotics
$$
M_{\mathbf v}(t)=\sum_{\ell=0}^{L} Q_\ell(t)\,e^{\gamma_\ell t}+O\!\big(e^{(\gamma_L-\delta)t}\big),\qquad \gamma_0>\cdots>\gamma_L,
$$
and $M_{\mathbf v}$ has bounded variation and satisfies mild growth. Then its Laplace–Stieltjes transform
$$
\mathcal L_{\mathbf v}(s):=\int_{(-\infty,+\infty)} e^{-s t}\,dM_{\mathbf v}(t)=\sum_j w_j e^{-s t_j}
$$
converges for $\Re s>\gamma_0$, and can be meromorphically continued to $\Re s>\gamma_L-\delta$, with at most $\deg Q_\ell+1$ order poles at $s=\gamma_\ell$. In particular, the real part of the rightmost convergence abscissa equals the maximum growth exponent $\gamma_0$.

**Proof Sketch.** Belongs to classical Laplace–Stieltjes Tauberian dictionary: integrate piecewise for exponential–polynomial asymptotics using integration by parts/residue control to obtain pole locations and orders; absolute convergence domain critical value given by $\gamma_0$. $\square$

---

### T26 (Reversible vs Non-reversible: Criteria and Consequences)

**Proposition (Criterion).** Global map $F: \Sigma^{\mathbb Z^d}\to\Sigma^{\mathbb Z^d}$ is CA-reversible $\iff$ it is bijective and $F^{-1}$ is also a CA (there exists a finite-radius inverse local rule). On $\mathbb Z^d$, Garden-of-Eden theorem gives: $F$ surjective $\iff$ $F$ pre-injective; reversibility is equivalent to being both surjective and injective.

**Proposition (Consequences).** If $F$ is reversible, then:
1) Information density conservation: $I(F^T x)=I(x)$ (see T22);
2) Non-increase under observation factor: $I_\pi(F^T x)\le I(x)$;
3) No true attractor: No unidirectional attraction compressing open sets into proper subsets (each point has bidirectional orbit, may have periods but no irreversible collapse dissipating information to a single fixed point).

**Proof.** Criterion is standard result; consequences 1–2 follow immediately from T21–T22; consequence 3 follows from reversibility and bidirectional reachability (existence of true attractor contradicts bijectivity). $\square$

---



## 7. Constructions and Algorithms

**7.1 From Rule to SFT**: From local consistency of $f$ derive forbidden pattern set $\mathcal F$, obtaining $X_f$.

**7.2 From SFT to Eternal Graph**: Construct $G_f$ with allowed patterns as vertices, legal concatenations as edges; use level sets of $\ell$ to provide leaf ordering.

**7.3 Decoder Design**: Choose core window $B$, block code $\pi:\Sigma^B\to\Gamma$; define **leaf-by-leaf reading stratified by $\ell$** protocol $\varsigma$.

**7.4 Macroblock-Forcing Program Box**: Self-similar tiling embedding "state-control-tape" and decodable (see T6).

**7.5 Compression-Entropy Experiment (Reproducible)**
$$
y_k=\pi\big(x|_{W_k}\big),\quad
c_k=\mathrm{compress}(y_k),\quad
r_k=\frac{\lvert c_k\rvert}{\lvert W_k\rvert},\quad
\mathrm{plot}(r_k)\ \ (k=1,2,\ldots).
$$

**7.6 Constructing SBU from Event Node (Forcing Domain Propagation)**
**Input**: Realizable $v$, orientation $\tau$, tolerance $\epsilon$.
**Steps**: With $v$ and local consistency as constraints, perform **bidirectional constraint propagation/consistency checking**, compute cell set **forced** by $v$ on increasing $W_k$, and expand leaf-by-leaf along $\ell$ until locally stable.
**Output**: **Forcing domain approximation** and information density curve of $\big(X_f^{(v,\tau)}\big)$ on $W_k$.

**7.7 Anchored Graph Relative Coordinate Construction**: BFS stratification (by $\ell$/spatial adjacency) → relative embedding $\varphi_{v_0}$ → radius-$r$ consistency verification and equivalence class merging.

**7.8 From CSP / $\mu$-Safety Formula to CA**: Given CSP or Horn/$\mu$-safety formula $\Phi$, for each clause with radius $\le r$ generate forbidden patterns $\mathcal F_\Phi$, define $f_\Phi$:
$$
X_{f_\Phi}=\mathcal T_{f_\Phi}(\mathsf{Conf})
=\Big\{x:\ \forall(\mathbf r,t),\ x(\mathbf r,t)=f_\Phi\big(x(\mathbf r+N,t-1)\big)\Big\},
$$
using finite control layers to maintain synchronization when necessary (without changing equivalence class).

**7.9 From $\omega$-Automaton to Leaf-Language**: Given Büchi automaton $\mathcal A=(Q,\Gamma,\delta,q_0,F)$, choose $(\pi,\varsigma)$ such that:

1. $\pi$ encodes cross-leaf observations as $\Gamma$-words;
2. Implement $\delta$ via finite-type synchronization conditions (encode $Q$ into alphabet via $X_f^{[k]}$ and simulate transitions via local constraints);
3. Express acceptance condition via safety/regularity constraints. Thus
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f)=L_\omega(\mathcal A).
$$

---

## 8. Typical Examples and Toy Models

**Rule-90 (Linear)**: Three perspectives consistent; SBU of any anchor uniquely recursive via linear relations; complexity density consistent after Følner normalization; leaf-language is $\omega$-regular.

**Rule-110 (Universal)**: Macroblock-forcing embeds TM (T6); halting witness corresponds to local termination marker (T9); leaf-by-leaf progression excludes same-layer alternatives (T19–T20).

**Two-coloring CSP (Model Perspective)**: Graph two-coloring local constraints → forbidden patterns; anchor certain node color and unfold leaf-by-leaf, forming causal consistent event cone; leaf-language is $\omega$-regular under appropriate conditions.

**2×2 Toy Block (Anchor–SBU–Decoding–Apparent Choice)**
$\Sigma=\{0,1\},\ d=1,\ N=\{-1,0,1\},\ f(a,b,c)=a\oplus b\oplus c$ (XOR, periodic boundary). Anchor $v_0$ fixes local pattern at $(t=0,\mathbf r=0)$. By T4's causal thick boundary and **leaf-by-leaf progression**, recurse to layer $t=1$, obtaining unique consistent extension; same-layer points contradicting anchor are excluded (T19). Take
$$
B=\Big\{(\mathbf r,t):\ \mathbf r\in\{0,1\},\ t=1\Big\},
$$
$\pi$ reads out two-dimensional block as visible binary string—"next step" only reads out, does not increase information (A3).

---

## 9. Extension Directions

* **Continuous Extension (cEBOC)**: Generalize via Markov symbolization/compact alphabet SFT; restate complexity/entropy and clarify discrete→continuous limit.
* **Quantum-Inspired**: Simultaneously describe multiple compatible SBUs of the same static block $X_f$, measurement corresponds to **anchor switching and locking** + one $\pi$-semantic collapse; provides constructive foundation for information- and computation-based quantum interpretation (no state-vector assumption).
* **Categorical/Coalgebraic Perspective**: $(X_f,\mathrm{shift})$ as coalgebra; anchored SBU as coalgebraic subsolution with injected initial value; leaf-language as automaton coalgebra homomorphism image.
* **Robustness**: Fault-tolerant decoding and robust windows under small perturbations/omissions, ensuring observable semantic stability.

---

## 10. Observer, Apparent Choice, and Temporal Experience (RPG Metaphor)

**Layer Separation**: **Operational layer** (observation/decoding/leaf-by-leaf progression/representative selection) versus **Ontological layer** (static geometry/unique consistent extension).
**Compatibility Principle**: Treat $X_f$ as **complete RPG data and rules**; **leaf-by-leaf progression** is like unlocking plot according to **established chapter pacing $b$**. Player "choice" is **selecting representative** among same-layer compatible branches and **excluding** other branches; **plot ontology** (static block) is already written, choice does not generate new information (A3), compatible with determinism (T20).
**Subjective Time Rate**: Effective step size $b=\langle\tau^\star,\tau\rangle$ reflects "chapter pacing"; entropy rate consistent after Følner normalization (T2/T5/T17).

---

## 11. Conclusion

EBOC unifies under minimal axioms the **timeless geometry (eternal graph/SFT)**, **static block consistent body**, and **leaf-by-leaf decoding observation-computation semantics**, forming a complete chain from **model/automaton** to **visible language**. This paper provides refined proofs of T1–T20, establishing core results including **information non-increase law** (T4/A3), **Brudno alignment** (T5), **unimodular covariance** (T2/T10), **event cone/static block unfolding** (T14–T16), **multi-anchor observers and coordinate relativization** (T17–T18), and provides reproducible experiments and construction procedures (§7).

---

## Appendix A: Terminology and Notation

* **Semantic Collapse**: Information factorization of $x\mapsto\mathcal O_{\pi,\varsigma}(x)$.
* **Apparent Choice**: Progression by minimal positive increment of $\ell$, selecting representative among same-layer alternatives; only changes semantic representative, does not create information.
* **Primitive Integral Covector**: $\tau^\star\in(\mathbb{Z}^{d+1})^\vee$, $\gcd(\tau^\star_0,\ldots,\tau^\star_d)=1$; its pairing with actual time direction $\tau$, $\langle\tau^\star,\tau\rangle=b\ge1$, defines leaf-by-leaf progression step size.
* **$\mathrm{GL}_{d+1}(\mathbb{Z})$**: Integer invertible matrix group (determinant $\pm1$).
* **Følner Family**: Window family with $|\partial W_k|/|W_k|\to0$.
* **Cylinder Set**: $[p]_W=\Big\{x\in X_f:\ x|_W=p\Big\}$.

---

## References (Guidance)

* A. A. Brudno (1983). *Entropy and the complexity of trajectories*.
* D. Lind & B. Marcus. *Symbolic Dynamics and Coding*.
* E. F. Moore (1962); J. Myhill (1963). *Machine models / Reversible CA*.
* M. Li & P. Vitányi. *An Introduction to Kolmogorov Complexity*.
* R. Berger; J. Kari. *Tilings, Undecidability, SFT*.
* J. R. Büchi; W. Thomas; D. Perrin & J.-E. Pin. *$\omega$-Automata and $\omega$-Languages*.
* D. Ornstein & B. Weiss; E. Lindenstrauss (SMB / pointwise ergodic for amenable group actions).

