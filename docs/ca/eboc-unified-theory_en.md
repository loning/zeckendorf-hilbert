# EBOC: Eternal-Block Observer-Computing Unified Theory

**Author**: Auric
**Date**: 2025-10-18

---

## Abstract

**Objective.** We propose **EBOC (Eternal-Block Observer-Computing)**: a geometry-information unified framework without explicit global time, merging the **timeless causal encoding** of **Eternal-Graph Cellular Automata** (EG-CA) with the **program semantics and observation-decoding** of **Static-Block Universe Cellular Automata** (SB-CA) into a single formal system, with verifiable information laws and constructive algorithms. This paper treats the static block $X_f$ and the eternal graph edge shift $(Y_G,\sigma)$ as **equivalent dual representations**; the exposition below primarily uses $X_f$, but every conclusion can be equivalently restated on $(Y_G,\sigma)$ via finite-type presentation/encoding equivalence.

**Three Pillars.**

1. **Geometric Encoding (Graph/SFT)**: The universe as a **static block** $X_f\subset\Sigma^{\mathbb{Z}^{d+1}}$ satisfying local rule $f$; its causality/consistency characterized in parallel by an **eternal graph** $G=(V,E)$ and a **subshift (SFT)**.
2. **Semantic Emergence (Observation = Decoding)**: **Observation = factor decoding**. The decoder $\pi:\Sigma^{B}\to\Gamma$ reads the static block **leaf-by-leaf according to an acceptable foliation** (cross-leaf reading advancing from layer $c$ to $c+b$ along $\tau$), outputting a visible language; "semantic collapse" is the **information factorization** from base configuration to visible record.
3. **Information Constraint (Non-increase Law)**: Observation does not create information:
$$
K\big(\pi(x|_W)\big)\ \le\ K(x|_W)+K(\pi)+O(1),
$$
and under **causal thick boundary** conditions, provides conditional complexity upper bounds consistent with Brudno entropy limits.

**Unified Metaphor (RPG Game).** The universe as an **RPG with infinite storyline**: the **game data and evolution rules** are already written ($(X_f,f)$), "choices" (apparent free will) must be consistent with **storylines** (determinism). **Leaf-by-leaf reading** unlocks chapters according to a preset rhythm $b$; "choice" is to **select a representative** among compatible branches and **exclude** incompatible ones, without adding or removing information from the ontological "ROM".

**Core Object.**
$$
\mathcal U=(X_f, G, \rho, \Sigma, f, \pi, \mu, \nu),
$$
where $X_f$ is the space-time SFT, $G$ is the eternal graph, $\rho$ provides the **acceptable leaf family** (level sets of the primitive integral covector $\tau^\star$, $\langle\tau^\star,\tau\rangle=b\ge1$), $\pi$ is the decoder, $\mu$ is a shift-invariant ergodic measure, and $\nu$ is a universal semimeasure (used only for typicality weighting). Equivalently, all results can be expressed using the **edge shift** $Y_G$ of $G$ and its **path shift** $(Y_G,\sigma)$; observation/information laws hold equally for both representations.

---

## 1. Introduction and Motivation

Traditional CA present "evolution" via global time iteration; the block/eternal-graph perspective gives the entire spacetime at once, with "evolution" being merely the narrative path obtained by **leaf-by-leaf reading**. The dynamical view depends on a time background and is difficult to make background-independent; the static view lacks observational semantics. EBOC unifies the two via "**geometric encoding × semantic decoding × information laws**": SFT/graph structure ensures consistency and constructiveness; factor maps provide visible language; complexity/entropy characterize conservation and limits. This paper establishes theorem family T1–T26 under minimal axioms, with detailed proofs and reproducible experimental protocols.

---

## 2. Notation and Preliminaries

### 2.1 Space, Alphabet, and Configuration

* Space $L=\mathbb{Z}^{d}$, spacetime $L\times\mathbb{Z}=\mathbb{Z}^{d+1}$; finite alphabet $\Sigma$.
* Spacetime configuration $x\in \Sigma^{\mathbb{Z}^{d+1}}$. Restriction to window $W\subset\mathbb{Z}^{d+1}$ denoted $x|_W$.
* Convention: $|\cdot|$ denotes both string length and set cardinality (disambiguated by context).

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

### 2.4 Foliation Decomposition and Leaf-by-Leaf Reading Protocol

* **Unimodular transformation**: $U\in \mathrm{GL}_{d+1}(\mathbb{Z})$ (integrally invertible, $\det U=\pm1$), time direction $\tau=Ue_{d+1}$.
* **Acceptable leaf**: There exists a **primitive integral covector** $\tau^\star\in(\mathbb{Z}^{d+1})^\vee$ and constant $c$, with leaves being level sets
$$
\Big\{\ \xi\in\mathbb{Z}^{d+1}:\ \langle\tau^\star,\xi\rangle=c\ \Big\},
$$
satisfying
$$
\langle\tau^\star, \tau\rangle=b\ge 1,
$$
to ensure **monotonic cross-leaf advancement**.
* **Leaf-by-leaf reading**: Using block code $\pi:\Sigma^B\to\Gamma$, advancing leaf-by-leaf from layer $c\mapsto c+b$, applying $\pi$ to corresponding windows to produce visible sequences.
* **Leaf counting and time-slice cuboid families**: For time-slice cuboid family windows $W=R\times[t_0, t_0+T-1]$ ($R\subset\mathbb{Z}^d$), define $L(W)=T$ as the temporal thickness (number of leaf layers traversed). Under step-size $b$ protocol, the **observation step count** is $\lfloor L(W)/b\rfloor$ (ignoring $O(1)$ boundary effects). Such window families are compatible with the one-dimensional Følner theory of the time subaction $\sigma_{\mathrm{time}}$. The complexity upper bounds in this paper can absorb this $O(1)$ boundary effect into the $O(\log|W|)$ term (see T4).
* **Time subaction notation**: Denote $\sigma_{\mathrm{time}}$ as the **one-dimensional subaction** of $X_f$ along the time coordinate, $\sigma_\Omega$ as the time shift of $\Omega(F)$.

### 2.5 Complexity and Measure

* We use **prefix** Kolmogorov complexity $K(\cdot)$ and conditional complexity $K(u|v)$.
* $\mu$: invariant and ergodic for **time subaction** $\sigma_{\mathrm{time}}$ (unless otherwise noted); $\nu$: universal semimeasure (algorithmic probability).
* **Window description complexity**: $K(W)$ is the length of the shortest program generating $W$; Følner family $\{W_k\}$ satisfies $|\partial W_k|/|W_k|\to 0$.
* **Entropy notation convention**: This paper distinguishes two types of entropy: $h_\mu(\sigma_{\mathrm{time}})$ (compatible with leaf count $L(W)$ normalization) and $h_\mu^{(d+1)}$ (compatible with voxel count $|W|$ normalization). They generally have no fixed conversion relation; results throughout are stated and proven under their respective compatible normalizations, without cross-normalization conversion. Furthermore, for any finite spatial section $R\subset\mathbb Z^d$, denote the **observation partition for the time subaction** as
  $$
  \alpha_R\ :=\ \big\{\, [p]_{R\times\{0\}}\ :\ p\in\Sigma^{R}\,\big\},
  $$
  and define the relative entropy $h_\mu(\sigma_{\mathrm{time}},\alpha_R)$; by Kolmogorov–Sinai definition
  $$
  h_\mu(\sigma_{\mathrm{time}}):=\sup_{R\text{ finite}}\ h_\mu(\sigma_{\mathrm{time}},\alpha_R).
  $$
  For observation factor $\pi$, the corresponding observation partition is denoted
  $$
  \alpha_R^\pi\ :=\ \big\{\, [q]_{R\times\{0\}}^\pi\ :\ q\in \pi(\Sigma^{B})^{R}\,\big\},
  $$
  where $[q]_{R\times\{0\}}^\pi$ denotes the cylinder set of configurations yielding visible pattern $q$ when $\pi$ block-reading is applied at $R\times\{0\}$.

### 2.6 Causal Thick Boundary (for T4)

* Explicitly use $\infty$-norm:
$$
r\ :=\ \max_{\mathbf n\in N}\ |\mathbf n|_{\infty}.
$$
* Define
$$
t_-=\min\Big\{t:(\mathbf r,t)\in W\Big\},\quad
t_+=\max\Big\{t:(\mathbf r,t)\in W\Big\},\quad
T=t_+-t_-+1.
$$
* Bottom layer $\mathrm{base}(W)=\Big\{(\mathbf r,t_-)\in W\Big\}$.
* **Past causal input boundary at bottom (standard coordinates)**
$$
\partial_{\downarrow}^{(r,T)}W^-\ :=\ \Big\{(\mathbf r+\mathbf n,\ t_--1)\ :\ (\mathbf r,t_-)\in\mathrm{base}(W),\ \mathbf n\in[-rT,\,rT]^d\cap\mathbb{Z}^d\Big\}\setminus W.
$$
Convention: $T$ in this section and in subsequent T4 always refers to the number of time layers traversed (consistent with $L(W)$ in §2.4).
For non-standard leaf cases, first map back to standard coordinates via $U^{-1}$ then take image.

### 2.7 Coordinate Relativization of Eternal Graph (Anchored Chart)

$G$ carries no global coordinates. Choose anchor $v_0$, relative embedding $\varphi_{v_0}:\mathrm{Ball}_G(v_0,R_0)\to\mathbb{Z}^{d+1}$ with $\varphi_{v_0}(v_0)=(\mathbf 0,0)$, path layer function along $\tau$ monotonically non-decreasing, spatial adjacency as finite shift. Fix in advance the minimal presentation radius $R_0$ for "local pattern $\to$ vertex" encoding; all related definitions and constructions below use this fixed $R_0$.
Layer function
$$
\ell(w):=\langle\tau^\star,\ \varphi_{v_0}(w)\rangle,\qquad
\mathrm{Cone}^+_{\ell}(v):=\Big\{w\in \mathrm{Dom}(\varphi_{v_0})\ :\ \exists\ v\leadsto w\ \text{with }\ell\ \text{monotonically non-decreasing along path}\Big\}.
$$
**SBU (Static Block Unfolding)**
$$
X_f^{(v,\tau)}:=\Big\{x\in X_f:\ x\big|_{\varphi_{v_0}(\mathrm{Ball}_G(v,R_0))}=\mathrm{pat}(v)\ \text{and}\ x\ \text{is a consistent extension on}\ \varphi_{v_0}\!\big(\mathrm{Cone}^+_\ell(v)\big)\Big\},
$$
where "consistent extension" means: all cells within this cone forced by $v$ and the local rule match $x$.

### 2.8 Eternal Graph–SFT Dual Representation (Working Principle)

- Dual representation: All conclusions stated in terms of static block $X_f$ in this paper have an equivalent version in terms of eternal graph edge shift $(Y_G,\sigma)$; the two are given by standard finite-type presentation/encoding. For conciseness, the main text uses $X_f$, with path version statements bracketed as "(EG)" where necessary.
- Correspondence: Window $W$ and thick boundary correspond to finite path segment and finite adjacency radius; leaf-by-leaf reading corresponds to time-shift reading along paths; observation factor $\pi$ defined on $X_f$ can be equivalently realized on $Y_G$ via path block code $\pi_G$.


> Below we discuss SBU only **on the graph domain where this relative embedding exists**.

**Definition: Realizable Event.** Let eternal graph $G=(V,E)$. Call $v\in V$ **realizable** if there exists $x\in X_f$ with some relative embedding $\varphi_{v_0}$ and radius $R_0$ such that $x\big|_{\varphi_{v_0}(\mathrm{Ball}_G(v,R_0))}$ is consistent with the local pattern of $v$ (according to the "local pattern→vertex" encoding convention in the text).

---

## 3. Minimal Axioms (A0–A3)

**A0 (Static Block)** $X_f$ is the set of locally constrained models.
**A1 (Causal-Local)** $f$ has finite neighborhood; reading uses acceptable leaves.
**A2 (Observation = Factor Decoding)** Leaf-by-leaf reading with $\pi$ applied yields $\mathcal O_{\pi,\varsigma}(x)$.
**A3 (Information Non-increase)** For any window $W$, $K(\pi(x|_W))\le K(x|_W)+K(\pi)+O(1)$.

---

## 4. Leaf-Language and Observational Equivalence

Fix $(\pi,\varsigma)$ and leaf family $\mathcal L$,
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f):=\Big\{\ \mathcal O_{\pi,\varsigma}(x)\in\Gamma^{\mathbb N}:\ x\in X_f,\ \text{leaf-by-leaf reading per }\mathcal L\ \Big\},
\qquad
x\sim_{\pi,\varsigma}y\iff \mathcal O_{\pi,\varsigma}(x)=\mathcal O_{\pi,\varsigma}(y).
$$

---

## 5. Preliminary Lemmas

**Lemma 5.1 (Complexity Conservation for Computable Transformation).** If $\Phi$ is computable, then
$$
K\big(\Phi(u)|v\big)\ \le\ K\big(u|v\big)+K(\Phi)+O(1).
$$
$\square$

**Lemma 5.2 (Describable Window Families).** For $(d+1)$-dimensional axis-aligned parallelotopes or regular windows described by $O(\log |W|)$ parameters, $K(W)=O(\log|W|)$. $\square$

**Lemma 5.3 (Thick Boundary Coverage).** For radius $r=\max_{\mathbf n\in N}|\mathbf n|_\infty$ and time span $T$, computing $x|_W$ requires only the previous layer of $\mathrm{base}(W)$ within $[-rT,\,rT]^d$ past input; i.e., $\partial_{\downarrow}^{(r,T)}W^-$ covers all dependencies (**propagation radius measured in $|\cdot|_\infty$**). $\square$

**Lemma 5.4 (Factor Entropy Non-increase).** If $\phi:(X,T)\to(Y,S)$ is a factor map, then $h_\mu(T)\ge h_{\phi_\ast\mu}(S)$. $\square$

**Lemma 5.5 (Time Subaction Version SMB/Brudno).** For **$\sigma_{\mathrm{time}}$-invariant and ergodic** $\mu$ and **time-slice cuboid family** $W_k = R \times [t_k, t_k+T_k-1]$, where $T_k\to\infty$, and **$R\subset\mathbb{Z}^d$ is a fixed finite set**. Denote $L(W_k)=T_k$ (temporal thickness), we have
$$
-\frac1{T_k}\log \mu\big([x|_{W_k}]\big)\ \to\ h_\mu(\sigma_{\mathrm{time}},\alpha_R)\quad (\mu\text{-a.e.}),\qquad
\limsup_{k\to\infty}\frac{K(x|_{W_k})}{T_k}\ =\ h_\mu(\sigma_{\mathrm{time}},\alpha_R)\quad (\mu\text{-a.e.}).
$$
This is the one-dimensional SMB/Brudno theorem for time subaction $\sigma_{\mathrm{time}}$ or equivalently $(\Omega(F),\sigma_\Omega)$. **The window shape must be time-slice cuboid family** (or satisfy equivalent "time-uniform slicing" condition) to ensure cylinder sets $[x|_{W_k}]$ are generated by iteration of the one-dimensional generating partition of the time subaction, making normalization match the action. If general $W_k$ is used, one can only guarantee that the limit with $|W_k|$ normalization is the $\mathbb{Z}^{d+1}$ action entropy $h_\mu^{(d+1)}$, or recover the time entropy limit under additional uniform slicing/density assumptions. $\square$
Furthermore, for fixed finite $R$, the above limit equals $h_\mu(\sigma_{\mathrm{time}},\alpha_R)$; taking $\sup_R$ recovers $h_\mu(\sigma_{\mathrm{time}})$. If instead using $|R_k|\to\infty$ with generating section families (hence corresponding generating partitions), the limit directly equals the complete $h_\mu(\sigma_{\mathrm{time}})$ (this case is a supplementary remark, not within the fixed $R$ premise of this lemma).
【Note】Only when $\alpha_R$ is a **generating partition** for the time subaction (e.g., using generating section family $R_k\uparrow$), does the limit equal the complete $h_\mu(\sigma_{\mathrm{time}})$; for fixed finite $R$ the limit is $h_\mu(\sigma_{\mathrm{time}},\alpha_R)$.

---

## 6. Main Theorems with Detailed Proofs (T1–T26)

### T1 (Block–Natural Extension Conjugacy)

**Proposition.** If $X_f\neq\varnothing$, then
$$
\boxed{ (X_f,\ \sigma_{\mathrm{time}})\ \cong\ (\Omega(F),\ \sigma_\Omega) },
\quad
\Omega(F)=\Big\{(\ldots,x_{-1},x_0,x_1,\ldots):\ F(x_t)=x_{t+1}\Big\}.
$$

**Proof.** Define $\Psi:X_f\to\Omega(F)$, $(\Psi(x))_t(\mathbf r)=x(\mathbf r,t)$. By SFT constraint we have $F((\Psi(x))_t)=(\Psi(x))_{t+1}$. Define inverse $\Phi:\Omega(F)\to X_f$, $\Phi((x_t))(\mathbf r,t)=x_t(\mathbf r)$. Clearly $\Phi\circ\Psi=\mathrm{id}$, $\Psi\circ\Phi=\mathrm{id}$, and $\Psi\circ\sigma_{\mathrm{time}}=\sigma_\Omega\circ\Psi$. Continuity and Borel measurability follow from product topology and cylinder structure. $\square$

---

### T2 (Unimodular Covariance; Complexity Density Invariance)

**Proposition.** For any shift-invariant ergodic measure $\mu$ and two sets of acceptable leaves (given by $U_1,U_2\in\mathrm{GL}_{d+1}(\mathbb Z)$), let $\tilde W_k=U_2U_1^{-1}(W_k)$. **Assumptions**: (i) Both $\{W_k\}$ and $\{\tilde W_k\}$ are time-slice cuboid Følner families, with spatial section $R\subset\mathbb{Z}^d$ being a **fixed finite set** independent of $k$; (ii) the two leaf families are given by primitive integral covector–time vector pairs $(\tau_i^\star,\tau_i)$ with pairing constants $b_i=\langle\tau_i^\star,\tau_i\rangle\ge1$ being constants **independent of $k$**. Then for $\mu$-a.e. $x$,
$$
\limsup_{k\to\infty}\frac{K(\pi(x|_{W_k}))}{L(W_k)}
= h_{\pi_\ast\mu}\big(\sigma_{\mathrm{time}},\alpha_R^\pi\big),\qquad
\limsup_{k\to\infty}\frac{K(\pi(x|_{\tilde W_k}))}{L(\tilde W_k)}
= h_{\pi_\ast\mu}\big(\sigma_{\mathrm{time}},\tilde\alpha_R^\pi\big).
$$

**Proof.** The integer isomorphism $U=U_2U_1^{-1}$ preserves Følner property: if $\{W_k\}$ is Følner then so is $\{\tilde W_k\}$, with $|\tilde W_k|=|W_k|$ (integer determinant $\pm1$; here $\tilde W_k$ denotes the lattice image set $U(W_k)$, even if shape is non-axis-aligned, lattice point count remains equal). **Under the time-slice cuboid family assumption**, there exist constants $c_-,c_+>0$ depending only on $\big(U,\tau_1^\star,\tau_1,\tau_2^\star,\tau_2\big)$ (independent of $k$) such that leaf counts (temporal thickness) satisfy $c_-L(W_k)\le L(\tilde W_k)\le c_+L(W_k)$. Applying Lemma 5.5 to the factor system for each window family yields time entropy limits relative to respective observation partitions: $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\alpha_R^\pi)$ and $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\tilde\alpha_R^\pi)$. If the two observation schemes are related by a **finite-memory invertible block code** isomorphism along the time subaction, they are equivalent and yield the same entropy rate; under this condition coordinate choice does not change the limit value. $\square$

---

### T3 (Observation = Decoding as Semantic Collapse)

**Proposition.** $\mathcal O_{\pi,\varsigma}:X_f\to\Gamma^{\mathbb N}$ is a factor map of the time subaction, inducing equivalence class $x\sim_{\pi,\varsigma}y$. One observation selects a representative within the equivalence class; the underlying $x$ remains unchanged. $\square$

---

### T4 (Information Upper Bound: Conditional Complexity Version)

$$
\boxed{ K\Big(\ \pi(x|_{W})\ \Big|\ x\big|_{\partial_{\downarrow}^{(r,T)} W^-}\Big)\ \le\ K(f)+K(W)+K(\pi)+O(\log |W|) }.
$$
where $T$ is the number of time layers traversed (consistent with $L(W)$ in §2.4).
【Premise Note】The following upper bound holds under the **single-step time dependence** premise of §2.2; if the rule depends on past $m>1$ layers, change the past causal input boundary to the corresponding thick boundary at $\{t_- -1,\dots,t_- -m\}$, replace $rT$ with $r\,(T+m-1)$, and the rest of the reasoning remains unchanged.

**Proof.** Construct universal program $\mathsf{Dec}$:

1. **Input**: Encoding of $f$, encoding of window $W$ (including $(t_-,T)$ and geometric parameters), encoding of $\pi$, and conditional string $x|_{\partial_{\downarrow}^{(r,T)}W^-}$.
2. **Recursion**: Generate layer-by-layer from layer $t_-$ according to time subaction. For any $(\mathbf r,s)\in W$, compute via
$$
x(\mathbf r,s)=f\big(x(\mathbf r+N,s-1)\big)
$$
with required right-hand side either already generated from previous layer or from conditional boundary (Lemma 5.3). **Generate by layers $s=t_-,t_-+1,\dots,t_+$**, avoiding dependency cycles. For each layer $s$, **first generate all cells needed for the forward closure of $W$ within the propagation cone (allowing temporary generation of values outside $W$ but within $[-r(s-t_-)$, $r(s-t_-)]^d \times \{s\}$), finally restrict to $W$**.
3. **Decoding**: Apply $\pi$ within $W$ according to protocol to obtain $\pi(x|_W)$.

Program body is constant size, input length is $K(f)+K(W)+K(\pi)+O(\log|W|)$ ($\log|W|$ for layer depth/alignment cost). By definition of prefix complexity, the upper bound follows. $\square$

---

### T5 (Brudno Alignment and Factor Entropy)

**Proposition.** For **fixed finite spatial section $R$** and **time-slice cuboid family** $\{W_k = R \times [t_k, t_k+T_k-1]\}$ (where $T_k\to\infty$ and satisfying window premise of Lemma 5.5), normalizing by temporal thickness $L(W_k)=T_k$ (【Note】Only when $\alpha_R$ is a **generating partition**, does the limit equal the complete $h_\mu(\sigma_{\mathrm{time}})$; for fixed finite $R$ it is $h_\mu(\sigma_{\mathrm{time}},\alpha_R)$):
$$
\limsup_{k\to\infty}\frac{K(x|_{W_k})}{T_k}\ =\ h_\mu(\sigma_{\mathrm{time}},\alpha_R),\qquad
\limsup_{k\to\infty}\frac{K(\pi(x|_{W_k}))}{T_k}\ =\ h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\alpha_R^\pi)\ \le\ h_\mu(\sigma_{\mathrm{time}}).
$$

**Proof.** By Lemma 5.5 (time subaction version SMB/Brudno, window family shape matching normalization), the first limsup equality holds. For factor image, $\pi$ is computable transformation and factor entropy is non-increasing (Lemma 5.4), so the second limsup equality holds and does not exceed $h_\mu(\sigma_{\mathrm{time}})$. Moreover, applying Lemma 5.5 to the factor system $\big(\pi(X_f),\sigma_{\mathrm{time}},\pi_\ast\mu\big)$ (same window premise), we get the limsup value equals $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\alpha_R^\pi)$ for $(\pi_\ast\mu)$-a.e.; by $\mu(\pi^{-1}A)=\pi_\ast\mu(A)$ the limsup equality also holds for $\mu$-a.e. $x$. If using generating partition (or growing section family $|R_k|\to\infty$), the right-hand side can be directly written as $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}})$. $\square$

---

### T6 (Program Emergence: Macro-block Forcing; SB-CA $\Rightarrow$ TM)

**Proposition.** (Allowing finite higher-block representation/alphabet extension) There exists a macro-block forcing embedding scheme $\mathsf{Emb}(M)$ such that **if** the finite-type constraint family of this scheme is **non-empty** (extended SFT non-empty), **then** there exists $x^{\mathrm{ext}}\in X_f^{\mathrm{ext}}$ (if using only higher blocks without alphabet extension, write $x^{[k]}\in X_f^{[k]}\cong X_f$) that under decoder $\pi$ can be decoded to yield some (expected) run trace of Turing machine $M$. **If further assuming the embedding constraints are complete and without spurious solutions**, we obtain "if and only if".

**Proof (Construction).** Take macro-block size $k$. Extend alphabet to $\Sigma'=\Sigma\times Q\times D\times S$ (machine state, tape symbol, head movement, synchronization phase). At macro-block scale, implement transition $(q,a)\mapsto (q',a',\delta)$ via finite-type local constraints, and implement cross-macro-block synchronization via phase signals. Denote the extended SFT obtained from above finite-type constraints as $X_f^{\mathrm{ext}}$, and denote the forgetting projection $\rho: \Sigma'\to\Sigma$ (if needing to relate extended configuration back to base). Decoder $\pi$ reads macro-block centerline to output tape content. If these finite-type constraint families are globally compatible (extended SFT non-empty), then by compactness we can take limit to obtain global configuration $x^{\mathrm{ext}}$; non-emptiness thus depends on compatibility premise, not automatically derived from compactness. $\square$

---

### T7 (Program Weight Universal Semimeasure Bound)

**Proposition.** Let program codes be prefix-unambiguous, then for any decodable program $p$, $\nu(p)\le C\cdot 2^{-|p|}$.

**Proof.** By Kraft inequality $\sum_p2^{-|p|}\le1$, universal semimeasure $\nu$ as weighted sum satisfies upper bound, constant $C$ depends only on chosen machine. $\square$

---

### T8 (Section–Natural Extension Duality; Entropy Preservation)

**Proposition.** $X_f$ and $\Omega(F)$ are mutually section/natural extension dual, with equal time entropy.

**Proof.** By conjugacy $(X_f,\sigma_{\mathrm{time}})\cong (\Omega(F),\sigma_\Omega)$ of T1. Natural extension does not change entropy; conjugacy preserves entropy, so the conclusion holds. $\square$

---

### T9 (Halting Witness Staticization)

**Proposition.** Under compatible embedding scheme of T6 (i.e., corresponding extended SFT non-empty), $M$ halts if and only if there exists $x^{\mathrm{ext}}\in X_f^{\mathrm{ext}}$ and finite window $W$ such that visible pattern $\pi\big(x^{\mathrm{ext}}\big|_W\big)$ contains "termination marker" $\square$; conversely likewise.

**Proof.** "If" direction: If $M$ halts at step $\hat t$, then macro-block center decoding output shows $\square$, forming finite visible pattern. "Only if" direction: If $\square$ appears in visible layer, by local consistency backtrack to halting transition; construction ensures $\square$ is not produced by other causes. Above equivalence all premise on global compatibility of embedding scheme (extended SFT non-empty). $\square$

---

### T10 (Unimodular Covariance Information Stability)

**Proposition.** If window families satisfy $K(W_k)=O(\log|W_k|)$, then under any integer transformation $U\in\mathrm{GL}_{d+1}(\mathbb{Z})$, the T4 upper bound and T3 semantics are preserved; window description complexity difference of transformed windows is $O(\log|W_k|)$, not involving data complexity $K(x|_{W_k})$ or $K(\pi(x|_{W_k}))$ pointwise upper bounds.

**Proof.** By Lemmas 5.1–5.2, window description complexity $K(W)$ is the shortest program length for generating window geometric parameters. Encoding of integer transformation $U$ and translation adds only $O(1)$ constant; bounded distortion of thick boundary $\partial_{\downarrow}^{(r,T)}W^-$ under $U$ is absorbed into $O(\log|W_k|)$. By measure-theoretic version of T2, data complexity density after normalization is coordinate-independent. $\square$

---

### T11 (Model Set Semantics)

**Proposition.**
$$
X_f=\mathcal T_f(\mathsf{Conf})=\Big\{x\in\Sigma^{\mathbb{Z}^{d+1}}:\forall(\mathbf r,t)\ x(\mathbf r,t)=f(x(\mathbf r+N,t-1))\Big\}.
$$
**Proof.** By definition. $\square$

---

### T12 (Computational Model Correspondence)

**Proposition.** (i) SB-CA and TM mutually simulate; (ii) Various CSP/Horn/$\mu$-safe formulas $\Phi$ can be equivalently embedded in EG-CA.

**Proof.** (i) By T6 and standard "TM simulates CA" gives bidirectional simulation.
(ii) Convert each clause of radius $\le r$ to forbidden pattern set $\mathcal F_\Phi$, obtain $X_{f_\Phi}$. Solution models are equivalent to models of $\Phi$ (finite-type + compactness). $\square$

---

### T13 (Leaf-Language $\omega$-Automaton Characterization; Sofic Sufficient Condition)

**Proposition.** If (i) using path version $(Y_G,\sigma)$ or there exists $k$ such that $X_f$ under time subaction can via higher-block representation $X_f^{[k]}$ make cross-leaf consistency depend only on adjacent $k$ layers (time direction can be Markovianized); and (ii) decoder $\pi:\Sigma^B\to\Gamma$ has kernel window $B$ with finite cross-leaf thickness, then $\mathsf{Lang}_{\pi,\varsigma}(X_f)$ is sofic (hence $\omega$-regular), accepted by some Büchi automaton $\mathcal A$:
$$
\mathsf{Lang}_{\pi,\varsigma}(X_f)=L_\omega(\mathcal A).
$$

**Proof (Construction).** Under time direction finite-memory condition, take higher-block representation $X_f^{[k]}$, encode finite state set $Q$ into extended alphabet and implement transition $\delta$ via finite-type constraints. One cross-leaf reading corresponds to one automaton step. Acceptance condition is realized via local safety/regularity constraints (e.g., "infinitely often visit $F$" via loop memory bit). Thus obtain equivalent $\omega$-language. $\square$

---

### T14 (SBU Existence for Any Realizable Event)

**Proposition.** For realizable $v$ and acceptable $\tau$, $\big(X_f^{(v,\tau)},\rho_\tau\big)$ is non-empty.

**Proof.** Take finite window family consistent with $v$, forming directed set by inclusion; finite consistency given by "realizable" and local constraints. By compactness (product topology) and Kőnig lemma, there exists limit configuration $x\in X_f$ consistent with $v$, hence non-empty. $\square$

---

### T15 (Causal Consistent Extension and Paradox Exclusion)

**Proposition.** $X_f^{(v,\tau)}$ contains only restrictions of global solutions consistent with anchor $v$; contradictory events do not coexist.

**Proof.** If some $x\in X_f^{(v,\tau)}$ simultaneously contains event contradictory to $v$, then on $\varphi_{v_0}(\mathrm{Cone}^+_\ell(v))$ it is both consistent and contradictory, violating consistency definition. $\square$

---

### T16 (Time = Deterministic Advancement (Apparent Choice))

**Proposition.** Under deterministic $f$ and thick boundary conditions, each minimal positive increment advancement of $\ell$ is equivalent to **deterministic advancement** on the future consistent extension family; unique under deterministic CA.

**Proof.** By construction of T4, given previous layer and thick boundary, next layer values uniquely defined by $f$; if two different advancements exist at same layer both acceptable and mutually conflicting, then at some common cell produces inconsistent assignments, contradiction. $\square$

---

### T17 (Multi-anchor Observers and Subjective Time Rate)

**Proposition.** Effective step size $b=\langle\tau^\star,\tau\rangle\ge 1$ reflects chapter rhythm; different $b$ only changes reading rhythm, under time-slice cuboid Følner family premise with fixed or uniformly bounded spatial section, entropy rate normalized by temporal thickness $L(W_k)=T_k$ is consistent.

**Proof.** Changing time subaction to $\sigma_{\mathrm{time}}^{(b)}$ is equivalent to "sampling" the $\mathbb{Z}$ subaction ($\sigma_\Omega^b$). Measure entropy satisfies (version relative to chosen partition also holds)
$$
h_\mu(\sigma_\Omega^b)\ =\ b\cdot h_\mu(\sigma_\Omega).
$$
For time-slice cuboid $W$, **observation step count** is $\lfloor L(W)/b\rfloor$ (see §2.4), while normalization uses **temporal thickness** $L(W)=T$. Hence
$$
\frac{K\big(\pi(x|_W)\big)}{L(W)}\ \sim\ \frac{\lfloor L(W)/b\rfloor}{L(W)}\cdot h_{\pi_\ast\mu}\big(\sigma_{\mathrm{time}}^{b}\big)\ =\ \frac1b\cdot b\,h_{\pi_\ast\mu}(\sigma_{\mathrm{time}})\ =\ h_{\pi_\ast\mu}(\sigma_{\mathrm{time}}),
$$
where $h_{\pi_\ast\mu}(\sigma_{\mathrm{time}}^{b})=b\,h_{\pi_\ast\mu}(\sigma_{\mathrm{time}})$. **If using fixed finite section $R$, should write**
$$
h_{\pi_\ast\mu}(\sigma_{\mathrm{time}}^{b},\alpha_R^\pi)=b\,h_{\pi_\ast\mu}\!\Big(\sigma_{\mathrm{time}},\ \bigvee_{i=0}^{b-1}\sigma_{\mathrm{time}}^{-i}\alpha_R^\pi\Big),
$$
**and only when** the above joined partition generates (or there exists finite-memory invertible block code isomorphism along time) **can** we write $b\,h_{\pi_\ast\mu}(\sigma_{\mathrm{time}},\alpha_R^\pi)$. Observation step count $\lfloor L(W)/b\rfloor$ factor $1/b$ exactly cancels $b$, entropy rate after normalization independent of $b$ choice. By Lemma 5.5, for $\mu$-a.e. $x$ the two family density limits agree. $\square$

---

### T18 (Anchored Graph Coordinate Relativization Invariance)

**Proposition.** Two embeddings $(\varphi_{v_0},\varphi_{v_1})$ if sourced from restrictions of same integer affine embedding $\Phi$, then on intersection domain after removing constant-radius boundary strip, differ only by $\mathrm{GL}_{d+1}(\mathbb Z)$ integer affine and finite-radius relabeling; additional encoding/description overhead between two embedding protocols $\le O(K(W))$ (for describable window families is $O(\log|W|)$), not involving data complexity or entropy difference pointwise upper bound for observation sequences themselves.

**Proof.** There exist $U\in\mathrm{GL}_{d+1}(\mathbb Z)$ and translation $t$ such that $\varphi_{v_1}=U\circ\varphi_{v_0}+t$ holds on intersection domain. Finite radius difference corresponds to removing boundary strips. Window encoding in two coordinates adds only finite description of $U,t$; this is additional description cost for protocol conversion, absorbed into $O(K(W))$ (Lemmas 5.1–5.2). Data complexity of observation sequences given coordinate-independence after normalization by measure-theoretic version of T2. $\square$

---

### T19 ($\ell$-Successor Determinism and Same-layer Exclusivity)

**Proposition.** Under deterministic $f$, radius $r$, if context of $u$ covers information needed to generate next layer, then unique $\mathrm{succ}_\ell(u)$ exists; edge $u\to\mathrm{succ}_\ell(u)$ has exclusivity against same-layer alternatives.

**Proof.** Next layer values uniquely determined by local function of $f$; if two different same-layer alternatives can both continue and mutually conflict, then at some common cell produce inconsistent assignment, contradiction. $\square$

---

### T20 (Compatibility Principle: Apparent Choice and Determinism Unified)

**Proposition.** Leaf-by-leaf advancement at operational level manifests as "representative selection", while holistic static encoding is "unique consistent extension"; determinism holds, compatible with A3/T4.

**Proof.** By T14 global consistent extension exists; T15 excludes contradictory branches; T3 shows "observation = select representative in equivalence class"; T4/A3 ensure choice does not increase information. Hence apparent freedom and ontological determinism are consistent. $\square$

---

### T21 (Information Non-increase Law: General CA and Observation Factor)

**Proposition.** Let $F$ be radius $r$ CA in $d$ dimensions, take any Følner window family $\{W_k\}$ (axis-aligned parallelotopes satisfy $K(W_k)=O(\log|W_k|)$). Define spatial information density (per cell)
$$
I(x):=\limsup_{k\to\infty}\frac{K\big(x|_{W_k}\big)}{|W_k|},\qquad
I_\pi(x):=\limsup_{k\to\infty}\frac{K\big(\pi(x|_{W_k})\big)}{|W_k|}.
$$
Then for each fixed $T\in\mathbb N$ and configuration $x$,
$$
I\big(F^T x\big)\ \le\ I(x),\qquad I_\pi\big(F^T x\big)\ \le\ I\big(F^T x\big)\ \le\ I(x).
$$
**Note**: This theorem is for $d$-dimensional spatial configurations, normalized by voxel count. When applied to time subaction of spacetime SFT, should use leaf count normalization (see T5).

**Proof.** Thick boundary and propagation cone give dependency domain: there exists $W_k^{+rT}$ such that $\big(F^T x\big)|_{W_k}$ can be computably recovered from $x|_{W_k^{+rT}}$ (see Lemma 5.3's $r,T$ control). By computable transformation complexity upper bound,
$$
K\big((F^T x)|_{W_k}\big)\ \le\ K\big(x|_{W_k^{+rT}}\big)+O(\log|W_k|).
$$
Følner property gives $|W_k^{+rT}|/|W_k|\to1$, taking $\limsup$ yields $I(F^T x)\le I(x)$. Factor decoding non-increase of information (A3, or computable transformation of Lemma 5.1), yields $I_\pi(F^T x)\le I(F^T x)$. Combining gives conclusion. $\square$

---

### T22 (Information Conservation Law: Reversible CA)

**Proposition.** If $F$ is reversible and $F^{-1}$ is also CA (reversible cellular automaton), then for each fixed $T\in\mathbb N$ and configuration $x$, spatial information density (per cell) is conserved:
$$
I\big(F^T x\big)=I(x),\qquad I_\pi\big(F^T x\big)\ \le\ I(x),
$$
with equality when $\pi=\mathrm{id}$ or lossless factor conjugate to $F$. If $\mu$ is shift-invariant ergodic measure, applied to time subaction of spacetime SFT $(X_f,\sigma_{\mathrm{time}})$, by conjugacy of T1 and entropy preservation under reversibility we know $h_\mu(\sigma_{\mathrm{time}})$ is invariant; spatial marginal distributions at each time $(\nu_t)$ satisfy stationarity $\nu_{t+1}=F_\ast\nu_t=\nu_t$; this notation has no direct mixing with computation of $h_\mu(\sigma_{\mathrm{time}})$. Hence $\mu$-almost everywhere time direction information density is conserved.

**Proof.** By T21 applying to $F$ and $F^{-1}$ respectively yields $I(F^T x)\le I(x)$ and $I(x)\le I(F^T x)$, combining gives $I(F^T x)=I(x)$. Non-increase for $\pi$ given by A3. Measure-theoretic version by conjugacy $(X_f,\sigma_{\mathrm{time}})\cong(\Omega(F),\sigma_\Omega)$ and entropy preservation under reversibility (T8), combined with Brudno theorem of leaf count normalization (Lemma 5.5). $\square$

---

### T23 (Observation Pressure Function and Information Geometry)

【Source Mapping】For each visible category $j$, let $a_j$ be the a priori weight (or count weight) for decoded unit time slice, $\beta_j$ be the fixed vector of corresponding **leaf-by-leaf statistical features** (e.g., frequency vector/energy cost); when taking limit over window family $W_k$, $\{p_j(\eta)\}$ are these observation statistics reweighted by exponential family.

**Definition.** To avoid confusion with leaf family notation $\rho$ in §2, below we use $\eta$ for parameters. Take a set of visible categories (given by decoding/counting rules) indexed $j=1,\dots,J$ (here take $J<\infty$), with weights $a_j>0$ and vectors $\beta_j\in\mathbb R^n$. Define
$$
Z(\eta)=\sum_{j=1}^{J} a_j\,e^{\,\langle\beta_j,\Re\eta\rangle},\qquad
P(\eta)=\log Z(\eta),\qquad
p_j(\eta)=\frac{a_j e^{\,\langle\beta_j,\Re\eta\rangle}}{Z(\eta)}.
$$
In the domain where $Z(\eta)$ converges, and satisfying standard conditions of local uniform convergence allowing sum/derivative interchange, we have
$$
\nabla_{\eta}P(\eta)=\mathbb E_p[\beta]=\sum_j p_j\,\beta_j,\qquad
\nabla_{\eta}^2 P(\eta)=\mathrm{Cov}_p(\beta)\succeq 0.
$$
Hence $P$ is **convex**, its Hessian being the Fisher information. Along direction $\eta(s)=\eta_\perp+s\mathbf v$,
$$
\frac{d^2}{ds^2}P\big(\eta(s)\big)=\mathrm{Var}_p\big(\langle\beta,\mathbf v\rangle\big)\ge0.
$$
If we further denote Shannon entropy $H(\eta)=-\sum_j p_j\log p_j$, then
$$
H(\eta)=P(\eta)-\sum_j p_j\log a_j-\big\langle\Re\eta,\,\mathbb E_p[\beta]\big\rangle.
$$

**Proof Sketch.** By standard differentiation of log-sum-exp (under aforementioned local uniform convergence condition allowing interchange of sum and differentiation), obtain gradient and Hessian expressions; directional second derivative is variance. Entropy identity obtained by substituting $p_j\propto a_j e^{\langle\beta_j,\Re\eta\rangle}$ into $H=-\sum p_j\log p_j$ and expanding. $\square$

---

### T24 (Phase Transition/Dominance Switching Criterion; Finite $J$ Version)

**Proposition.** Let amplitude $A_j(\eta):=a_j e^{\langle\beta_j,\eta\rangle}$, and define
$$
H_{jk}=\Big\{\eta:\ \langle\beta_j-\beta_k,\eta\rangle=\log\frac{a_k}{a_j}\Big\},\qquad
\delta(\eta):=\min_{j<k}\Big|\ \langle\beta_j-\beta_k,\eta\rangle-\log\frac{a_k}{a_j}\ \Big|.
$$
If $\delta(\eta)>\log(J-1)$, then unique index $j_\star$ exists such that $A_{j_\star}(\eta)=\max_j A_j(\eta)$ and
$$
\sum_{k\ne j_\star}A_k(\eta)<A_{j_\star}(\eta),
$$
hence no dominance switching; dominance switching can only occur in thin band $\{\eta:\ \delta(\eta)\le\log(J-1)\}$, whose skeleton is hyperplane family $\{H_{jk}\}$.

**Proof.** By definition of $\delta(\eta)$, $\log A_{j_\star}-\log A_k\ge\delta(\eta)$, hence $A_k\le e^{-\delta(\eta)}A_{j_\star}$, summing yields conclusion. $\square$

---

### T25 (Directional Pole = Growth Exponent; Countable Infinite Version)

**Proposition.** Fix direction $\mathbf v$ and decomposition $\eta=\eta_\perp+s\mathbf v$. Let index family $\{(a_j,\beta_j)\}_{j\ge1}$ be **countably infinite**, and assume there exists $\eta_0$ such that $\sum_{j\ge1} a_j e^{\langle\beta_j,\Re\eta_0\rangle}<\infty$. Let weighted cumulative distribution along $\mathbf v$
$$
M_{\mathbf v}(t)=\sum_{t_j\le t} w_j,\qquad t_j:=\langle-\beta_j,\mathbf v\rangle,\quad w_j:=a_j e^{\langle\beta_j,\eta_\perp\rangle},
$$
have exponential–polynomial asymptotics as $t\to+\infty$ (and assume $M_{\mathbf v}$ has bounded variation and moderate growth)
$$
M_{\mathbf v}(t)=\sum_{\ell=0}^{L} Q_\ell(t)\,e^{\gamma_\ell t}+O\!\big(e^{(\gamma_L-\delta)t}\big),\qquad \gamma_0>\cdots>\gamma_L,
$$
and $M_{\mathbf v}$ has bounded variation and satisfies moderate growth. Then its Laplace–Stieltjes transform
$$
\mathcal L_{\mathbf v}(s):=\int_{(-\infty,+\infty)} e^{-s t}\,dM_{\mathbf v}(t)=\sum_j w_j e^{-s t_j}
$$
converges for $\Re s>\gamma_0$, and can be meromorphically continued to $\Re s>\gamma_L-\delta$, with poles of order at most $\deg Q_\ell+1$ at $s=\gamma_\ell$. In particular, the real part of the rightmost convergence line equals the maximal growth exponent $\gamma_0$. If $J<\infty$, the above sum is finite and pole case does not occur.

**Proof Sketch.** Belongs to classical Laplace–Stieltjes Tauberian dictionary: integrate segment-by-segment for exponential–polynomial asymptotics using integration by parts/residue control to obtain pole locations and orders; absolute convergence domain critical value given by $\gamma_0$. $\square$

---

### T26 (Reversible vs Non-reversible: Criterion and Consequences)

**Proposition (Criterion).** Global map $F: \Sigma^{\mathbb Z^d}\to\Sigma^{\mathbb Z^d}$ is CA-reversible $\iff$ it is bijective and $F^{-1}$ is also CA (there exists inverse local rule of finite radius). On $\mathbb Z^d$, Garden-of-Eden theorem gives: $F$ surjective $\iff$ $F$ pre-injective; reversibility equivalent to simultaneously surjective and injective.

**Proposition (Consequences).** If $F$ is reversible, then:
1) Information density conserved: $I(F^T x)=I(x)$ (see T22);
2) Non-increase under observation factor: $I_\pi(F^T x)\le I(x)$;
3) No true attractors: no unidirectional attraction compressing open sets into proper subsets (each point has bidirectional orbit, may have periods but no information dissipation into irreversible collapse to single fixed point).

**Proof.** Criterion is standard result; consequences 1–2 immediately follow from T21–T22; consequence 3 given by reversibility and bidirectional reachability (if true attractor exists contradicts bijection). $\square$

---



## 7. Constructions and Algorithms

**7.1 From Rule to SFT**: From local consistency of $f$ derive forbidden pattern set $\mathcal F$, obtain $X_f$.

**7.2 From SFT to Eternal Graph**: Use allowed patterns as vertices, legal tilings as edges to construct $G_f$; use level sets of $\ell$ to give leaf ordering.

**7.3 Decoder Design**: Choose kernel window $B$, block code $\pi:\Sigma^B\to\Gamma$; define **leaf-by-leaf reading protocol** $\varsigma$ **stratified by $\ell$**.

**7.4 Macro-block Forcing Program Box**: Self-similar tiling embeds "state-control-tape" and can be decoded (see T6).

**7.5 Compression-Entropy Experiment (Reproducible)**
$$
y_k=\pi\big(x|_{W_k}\big),\quad
c_k=\mathrm{compress}(y_k),\quad
r_k=\frac{\lvert c_k\rvert}{\lvert W_k\rvert},\quad
\mathrm{plot}(r_k)\ \ (k=1,2,\ldots).
$$
**Note**: Here normalizing by $|W_k|$ for experimental convenience; theoretically for time subaction entropy should use temporal thickness $L(W_k)=T_k$ normalization (see T5, requires time-slice cuboid family). To align with time entropy of T5, should keep $R$ fixed and simultaneously report $|c_k|/T_k$; if $|R_k|$ varies or using general Følner windows, then $r_k$ reflects $h_\mu^{(d+1)}$ scale rather than time entropy.

**7.6 Constructing SBU from Event Node (Forcing Domain Propagation)**
**Input**: Realizable $v$, orientation $\tau$, tolerance $\epsilon$.
**Steps**: Using $v$ and local consistency as constraints, perform **bidirectional constraint propagation/consistency checking**, compute the set of cells **forced** by $v$ on growing $W_k$, and leaf-by-leaf extend according to $\ell$ until locally stable.
**Output**: **Forcing domain approximation** of $\big(X_f^{(v,\tau)}\big)$ on $W_k$ and information density curve.

**7.7 Anchored Graph Relative Coordinate Construction**: BFS stratification (by $\ell$/spatial adjacency) → relative embedding $\varphi_{v_0}$ → radius $r$ consistency verification and equivalence class merging.

**7.8 From CSP / $\mu$-Safe Formula to CA**: Given CSP or Horn/$\mu$-safe formula $\Phi$, for each clause of radius $\le r$ generate forbidden pattern $\mathcal F_\Phi$, define $f_\Phi$:
$$
X_{f_\Phi}=\mathcal T_{f_\Phi}(\mathsf{Conf})
=\Big\{x:\ \forall(\mathbf r,t),\ x(\mathbf r,t)=f_\Phi\big(x(\mathbf r+N,t-1)\big)\Big\},
$$
if necessary use finite control layer to maintain synchronization (without changing equivalence class).

**7.9 From $\omega$-Automaton to Leaf-Language**: Given Büchi automaton $\mathcal A=(Q,\Gamma,\delta,q_0,F)$, choose $(\pi,\varsigma)$ and construct extended SFT $X_{f,\mathcal A}$ such that:

1. $\pi$ encodes cross-leaf observations as $\Gamma$-words;
2. Implement $\delta$ via finite-type synchronization conditions: overlay finite-type "control/synchronization layer" on $X_f$ (or equivalently first take $X_f^{[k]}$ encode $Q$ into alphabet and simulate transition via local constraints), obtain extended SFT $X_{f,\mathcal A}$;
3. Acceptance condition expressed via safety/regularity constraints. Thus
$$
\mathsf{Lang}_{\pi,\varsigma}\big(X_{f,\mathcal A}\big)=L_\omega(\mathcal A).
$$

---

## 8. Typical Examples and Toy Models

**Rule-90 (Linear)**: Three perspectives consistent; SBU of any anchor uniquely recursed by linear relations; complexity density after Følner normalization consistent; leaf-language is $\omega$-regular.

**Rule-110 (Universal)**: Macro-block forcing embeds TM (T6); halting witness corresponds to local termination marker (T9); leaf-by-leaf advancement excludes same-layer alternatives (T19–T20).

**2-Coloring CSP (Model Perspective)**: Graph 2-coloring local constraints → forbidden patterns; anchor certain node color and leaf-by-leaf unfold, forming causal consistent event cone; leaf-language under appropriate conditions is $\omega$-regular.

**2×2 Toy Block (Anchor–SBU–Decoding–Apparent Choice)**
$\Sigma=\{0,1\},\ d=1,\ N=\{-1,0,1\},\ f(a,b,c)=a\oplus b\oplus c$ (XOR, periodic boundary). Anchor $v_0$ fixes local pattern at $(t=0,\mathbf r=0)$. By T4's causal thick boundary and **leaf-by-leaf advancement** recurse $t=1$ layer, obtain unique consistent extension; same-layer points contradicting anchor excluded (T19). Take
$$
B=\Big\{(\mathbf r,t):\ \mathbf r\in\{0,1\},\ t=1\Big\},
$$
$\pi$ reads out 2D block as visible binary string—"next step" only reads, does not increase information (A3).

---

## 9. Extension Directions

* **Continuous Extension (cEBOC)**: Generalize via Markov symbolization/compact alphabet SFT; restate complexity/entropy and clarify discrete→continuous limit.
* **Quantum Inspiration**: Simultaneously describe multiple compatible SBUs of same static block $X_f$, measurement corresponds to **anchor switching and locking** + one $\pi$-semantic collapse; provides constructive foundation for information and computation based quantum interpretation (no state-vector assumption).
* **Categorical/Coalgebra Perspective**: $(X_f,\mathrm{shift})$ as coalgebra; anchored SBU as coalgebra subsolution injecting initial values; leaf-language as automaton coalgebra homomorphism image.
* **Robustness**: Fault-tolerant decoding and robust windows under small perturbations/missing data, ensuring observable semantic stability.

---

## 10. Observer, Apparent Choice, and Time Experience (RPG Metaphor)

**Level Separation**: **Operational level** (observation/decoding/leaf-by-leaf advancement/representative selection) and **Ontological level** (static geometry/unique consistent extension).
**Compatibility Principle**: View $X_f$ as **RPG's complete data and rules**; **leaf-by-leaf advancement** like unlocking story according to **preset chapter rhythm $b$**. Player "choice" is to **select representative** among same-layer compatible branches and **exclude** other branches; **story ontology** (static block) already written, choice does not generate new information (A3), compatible with determinism (T20).
**Subjective Time Rate**: Effective step size $b=\langle\tau^\star,\tau\rangle$ embodies "chapter rhythm"; entropy rate after Følner normalization consistent (T2/T5/T17).

---

## 11. Conclusion

EBOC under minimal axioms unifies **timeless geometry (eternal graph/SFT)**, **static block consistent body**, and **leaf-by-leaf decoding observation-computation semantics**, forming complete chain from **model/automaton** to **visible language**. This paper provides detailed proofs of T1–T26, establishing **information non-increase law** (T4/A3), **Brudno alignment** (T5), **unimodular covariance** (T2/T10), **event cone/static block unfolding** (T14–T16), **multi-anchor observers and coordinate relativization** (T17–T18), and other core results, with reproducible experimental and construction protocols (§7).

---

## Appendix A: Terminology and Notation

* **Semantic Collapse**: Information factorization of $x\mapsto\mathcal O_{\pi,\varsigma}(x)$.
* **Apparent Choice**: Advancement by minimal positive increment of $\ell$, representative selection among same-layer alternatives; only changes semantic representative, does not create information.
* **Time-Slice Cuboid Family**: Windows of form $W_k=R_k\times[t_k, t_k+T_k-1]$, where $R_k\subset\mathbb{Z}^d$ is spatial section, $T_k\to\infty$ is temporal thickness; compatible with one-dimensional Følner theory of time subaction $\sigma_{\mathrm{time}}$.
* **Leaf Count (Temporal Thickness)**: For time-slice cuboid $W=R\times[t_0, t_0+T-1]$, define $L(W)=T$ as number of leaf layers traversed, corresponding to observation step count.
* **Primitive Integral Covector**: $\tau^\star\in(\mathbb{Z}^{d+1})^\vee$, $\gcd(\tau^\star_0,\ldots,\tau^\star_d)=1$; its pairing with actual time direction $\tau$ as $\langle\tau^\star,\tau\rangle=b\ge1$ defines leaf-by-leaf advancement step size.
* **$\mathrm{GL}_{d+1}(\mathbb{Z})$**: Integer invertible matrix group (determinant $\pm1$).
* **Følner Family**: Window family $|\partial W_k|/|W_k|\to0$.
* **Cylinder Set**: $[p]_W=\Big\{x\in X_f:\ x|_W=p\Big\}$.
* **Entropy Normalization Correspondence**: $h_\mu(\sigma_{\mathrm{time}})$ compatible with temporal thickness $L(W)=T$ normalization (time-slice cuboid family); $h_\mu^{(d+1)}$ compatible with voxel count $|W|$ normalization (general Følner family).

---

## References (Indicative)

* A. A. Brudno (1983). *Entropy and the complexity of trajectories*.
* D. Lind & B. Marcus. *Symbolic Dynamics and Coding*.
* E. F. Moore (1962); J. Myhill (1963). *Machine models / Reversible CA*.
* M. Li & P. Vitányi. *An Introduction to Kolmogorov Complexity*.
* R. Berger; J. Kari. *Tilings, Undecidability, SFT*.
* J. R. Büchi; W. Thomas; D. Perrin & J.-E. Pin. *$\omega$-Automata and $\omega$-Languages*.
* D. Ornstein & B. Weiss; E. Lindenstrauss (SMB / pointwise ergodic for additive group actions).

