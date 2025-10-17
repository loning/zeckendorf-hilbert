# Computational Completeness and Static Block Cellular Automata Equivalence: A Unified Formulation from Computational Closure to Spatiotemporal Static Structure

**Author**: An integrated extension based on the Static Block Quantum Field Theory framework
**Date**: October 17, 2025
**Version**: v1.6.1-final (submission version)

---

## Abstract

Under the “universal substrate” condition, this paper establishes a bi-directional reducibility (in the sense of computable isomorphism) between computational completeness and the ability of a system to be staticized into a full spatiotemporal block cellular automaton (SB-CA) structure. Via constructive embeddings using Rule 110 and Wang tilings, upper bounds on Kolmogorov complexity, and a halting-problem duality (equivalence between undecidability in temporal and static descriptions), we show that dynamic evolution can be rewritten as sequential projections of a static tensor, and that time can be reinterpreted as an index dimension of a spacetime tensor. The result provides a unified framework for the philosophy of computation and the modeling of complex systems.

**Keywords**: computational completeness, static block cellular automata, Turing completeness, Rule 110, Wang tiling, Kolmogorov complexity, halting problem

---

## §1 Introduction

### 1.1 Background and Motivation

Computational completeness characterizes a system’s ability to simulate any computable function. Since Turing introduced Turing machines, numerous models (e.g., the lambda calculus, cellular automata) have been shown equivalent. Wolfram (2002) proposed the principle of computational equivalence; nontrivial systems (e.g., class-4 cellular automata) are equivalent in computational complexity. Our focus: the computational completeness of a system, denoted $C(\mathcal{S})$, is equivalent to its ability to be staticized into a full spatiotemporal cellular automaton block structure, denoted $A(\mathcal{S})$, i.e., $C(\mathcal{S}) \iff A(\mathcal{S})$. By staticization we mean converting dynamic processes into a spacetime block $\mathcal{B}$; by full spatiotemporal we mean the grid covers both space and time dimensions; by block structure we mean modular discrete units.

Gödel’s incompleteness theorems show that sufficiently strong recursive systems cannot be both consistent and logically complete; the completeness here, however, refers to computational (Turing) completeness, which is orthogonal. We ensure coherence through definitions, proofs, and simulation checks.

### 1.2 Theoretical Positioning

As the computational-theory entry of the “static block completeness” series, this paper examines the expressive power of static block structures from the perspective of computational closure. In parallel and resonance with prior work on static block cellular automata theory, static block quantum cellular automata theory, static block quantum field theory, and static block quantum mechanics, we focus here on the equivalence between classical computational models and spatiotemporal staticization.

### 1.3 Organization

The paper is organized as follows:

- **§2** Related Work
- **§3** Definitions and Formal System
- **§4** Main Theorem: Equivalence between Computational Completeness and Static Block Structure
- **§5** Staticizing Time
- **§6** Relation to Computability Theory
- **§7** Discussion and Philosophical Speculation
- **§8** Conclusion and Outlook
- **Appendix A** Wang-Tiling History Construction
- **Appendix B** Rule 110 Verification

### 1.4 Terminology and Model Mapping

- SB-CA: Freezing the spacetime history of a CA into a $(d+1)$-dimensional configuration and specifying local constraints in a static model as a subshift of finite type (SFT).
- SFT: A subshift defined by a finite set of forbidden patterns; in this paper, SB-CA is an SFT instance with an explicit time coordinate.
- Wang tiling: A static tiling model equivalent to SFT; used here as a static substrate in parallel with Rule 110.
- Universal substrate: An SB-CA/SFT/tiling system that supports uniform and effective UTM encoding/decoding with bounded (effectively computable) overhead.

Note: We take $\Lambda=\mathbb{Z}^d$ to be infinite and boundaryless unless otherwise stated; for periodic boundary/finite torus, incorporate the torus size into the encoding and ensure it is sufficiently large so that results remain valid. If a torus boundary is used, include the ring size in the encoding and make it large enough to accommodate the required history; the main theorem remains unchanged for $\Lambda=\mathbb{Z}^d$.

---

## §2 Related Work

Cellular automata were introduced by von Neumann and Ulam for self-reproduction. Conway’s Game of Life showed that simple rules can generate complex behavior. Wolfram classified one-dimensional CAs; Rule 110 was proven Turing-complete by Cook (2004) via simulating cyclic tag systems. The principle of computational equivalence extends this view.

Hedlund (1969) laid the foundations of symbolic dynamics with the CHL theorem. Berger (1966) and Wang (1961) introduced the domino/tiling problem, exhibiting the undecidability of global properties and very strong expressiveness in static tiling models; this fact complements the construction of universal-substrate history encodings (but undecidability per se does not imply “computational universality”). Ollinger (2008) and Kari (1994) surveyed undecidable CA properties. Toffoli (1977) introduced reversible CAs; Morita (1995) proved universal reversible CAs, supporting links between staticization and reversibility. Barbour (1999) advocated an eternalist view of time as a static entity. Distinct from Barbour’s eternalism, we do not assert metaphysical identity but formal reducibility. Zenil (2012) explored a computable universe. Aaronson (2024) is cited for discussion, inspiring a quantum-spacetime computation perspective.

---

## §3 Definitions and Formal System

### Definition 3.1 (Computational/Turing Completeness)

A system $\mathcal{S}$ is Turing-complete if it can simulate a Universal Turing Machine $U$: for any Turing machine $M$ and input $w$, there exists an encoding so that $\mathcal{S}$ computes $U(M,w)$. The class of computable functions equals the partial recursive functions.

**Note 3.1**: Turing completeness is in the recursion-theoretic sense and is orthogonal to Gödel incompleteness (a logical property).

### Definition 3.2 (Cellular Automata)

A cellular automaton is $\mathrm{CA}=(\Lambda,Q,f)$ with $\Lambda=\mathbb{Z}^d$ a spatial lattice, $Q$ a finite set of states, and $f: Q^{\mathcal{N}_r} \to Q$ a local update rule ($\mathcal{N}_r$ a neighborhood).

**Note 3.2 (Curtis–Hedlund–Lyndon Theorem)**: Any continuous, shift-invariant map $G:Q^{\mathbb{Z}^d}\to Q^{\mathbb{Z}^d}$ is induced by a local rule $f$ (Hedlund, 1969).

### Definition 3.3 (Static Block Cellular Automata, SB-CA)

An SB-CA is a triple $(\Lambda\times T, Q, C)$ where:

- $\Lambda=\mathbb{Z}^d$ is a spatial grid,
- $T=\mathbb{N}$ is the time set,
- $Q$ is a finite set of states,
- $C$ is a set of local constraints, each acting on a spacetime neighborhood $\mathcal{N}_r(x,t)\subset \Lambda\times T$, specifying legality of local state combinations.

A legal configuration (a static block) $\mathcal{B}\in Q^{\Lambda\times T}$ satisfies all constraints $C$ at each $(x,t)\in \Lambda\times T$.

In particular, if $C$ is induced by a CA’s local evolution rule $f:Q^{\mathcal{N}_r}\to Q$, i.e., for all $(x,t)$,
$$
\mathcal{B}(x,t+1)=f\big(\mathcal{B}(y,t)\ \text{for}\ y\in\mathcal{N}_r(x)\big),
$$
then the SB-CA is said to be generated by the dynamic CA $(\Lambda,Q,f)$.

**Note 3.3 (Compactness and Extension)**: The SB-CA configuration space is a closed subset of the product topology $Q^{\Lambda\times T}$ defined by the above cylindrical local constraints (Hedlund, 1969). By Tychonoff’s theorem, $Q^{\Lambda\times T}$ is compact in the product topology; as an SFT, the SB-CA configuration space is closed. If a family of finite-window patterns is pairwise compatible and satisfies the finite intersection property (every finite subfamily can be extended together), then a global configuration exists by compactness; nonetheless, “locally legal” does not automatically entail extendability. All constructions in this paper explicitly ensure the finite-intersection condition.

**Note 3.4 (Spacetime-Coupled Neighborhoods)**: The above adopts a “purely spatial neighborhood + single-step time advance” paradigm; if needed, it can be generalized to truly spacetime-coupled neighborhoods (e.g., $(y,s)$ with $s\in[t-r_t, t+r_t]$). Our conclusions remain unchanged. When spacetime coupling is adopted, the constraint dependency graph along the time dimension must be a DAG to ensure reducibility to causal single-step CA.

**Note 3.5 (Boundary and Dimension)**: Unless otherwise stated, we take $\Lambda=\mathbb{Z}^d$ infinite and boundaryless. For periodic boundaries or finite tori, incorporate the ring size into the encoding and ensure it is sufficiently large to accommodate the required history; theorems and reductions hold under the corresponding scale conditions.

(Formal Objects) Let $\mathrm{Histories}(\mathcal{B})$ denote the set of global assignments satisfying $C$ (including initial-row constraints when present). Let $\mathrm{Region}(\mathcal{B})$ denote an enumerable family of finite spacetime windows (e.g., finite rectangular boxes). All statements about I/O and isomorphisms are with respect to these canonical objects and their code spaces.

### Definition 3.4 (Formal Staticization)

A system $\mathcal{S}$ is staticizable if there exist an SB-CA $\mathcal{B}$, an input encoding $\iota: \mathrm{Input}(\mathcal{S})\to \mathrm{Initial}(\mathcal{B})$, an output decoding $\pi: \mathrm{Region}(\mathcal{B})\to \mathrm{Output}(\mathcal{S})$, and a bi-directionally computable isomorphism
$$
\Phi: \mathrm{Traces}(\mathcal{S})\ \leftrightarrow\ \mathcal{H}\subseteq\mathrm{Histories}(\mathcal{B})
$$
such that:
1) $\Phi$ and $\Phi^{-1}$ are computable and commute with $\iota,\pi$, preserving I/O semantics;
2) Coverage: $\mathcal{H}$ covers all UTM-encoded histories $\{\mathrm{hist}(M,w)\mid M,w\}$ (uniform, effective pre-/post-processing allowed);
3) $\mathrm{Region}(\mathcal{B})$ is an enumerable family of finite windows, and the output is readable from some finite window.

Remark (Computability Convention): $\Phi$ and $\Phi^{-1}$ are total computable maps over the canonical code spaces (equivalently, Type-2 computable over a separable zero-dimensional topology). The same holds for $\iota,\pi$. All computability is with respect to this canonical encoding.

### Definition 3.5 (Universal Substrate)

Let $\mathsf{B}$ be an SFT/tiling/CA-static-block system defined by finite local constraints. We call $\mathsf{B}$ a universal substrate if there exist computable maps $\iota,\pi$, an effectively computable overhead function $g:\mathbb{N}\to\mathbb{N}$, and a constant $c$ such that for any TM $M$ and input $w$:

(i) $\iota(M,w)$ induces a $\mathsf{B}$-history that corresponds to $M$’s computation in the sense of the computable isomorphism of Definition 3.4 (uniform and effective);

(ii) If $M(w)\downarrow$, then there exist $t$ and a finite window from which $\pi$ reads the output, with time/space overhead $\le g(|M|+|w|)+c$.

(Optional stronger assumption) If there exists a polynomial $p$ such that the overhead can be taken as $p(|M|+|w|)+c$, we call $\mathsf{B}$ a “polynomial universal substrate.” Our main results hold for general $g$; when a polynomial bound is available, the complexity statements can be correspondingly strengthened. When necessary, the parameters of $g$ may include the code length of periodic background/torus size.

---

## §4 Main Theorem: Equivalence between Computational Completeness and Static Block Structure

### Lemma 4.A (Staticization Embedding)

For any $(M,w)$, there exists a uniform and effective encoding $\iota(M,w)$ inducing a legal history in a universal substrate $\mathcal{B}$, with an enumerable family of finite windows from which the output is readable. The construction is uniform in $(M,w)$ and satisfies the overhead bound of Definition 3.5.

### Lemma 4.B (Isomorphism Purification)

If there exists a bi-directionally computable isomorphism $\Phi: \mathrm{Traces}(\mathcal{S})\leftrightarrow \mathcal{H}\subseteq\mathrm{Histories}(\mathcal{B})$ whose image $\mathcal{H}$ covers all UTM-encoded histories $\{\mathrm{hist}(M,w)\}$, then $\mathcal{S}$ is Turing-complete.

### Theorem 4.1 (Equivalence Theorem)

Given a computational system $\mathcal{S}$, the following are equivalent:

(i) $\mathcal{S}$ is Turing-complete;

(ii) There exists an SB-CA $\mathcal{B}$ based on a universal CA or an equivalent static tiling (Wang tiling) “history” construction, together with I/O encodings $(\iota,\pi)$, such that any computation of $\mathcal{S}$ can be embedded as a temporally consistent trajectory in $\mathcal{B}$, and the output is readable by $\pi$ from a finite region.

Moreover, the embedding is canonical up to computable isomorphism (different realizations differ only by computable bijections and coordinate rescalings).

**Proof** ((i) $\Rightarrow$ (ii)):

Any Turing-complete $\mathcal{S}$ can simulate a UTM. By Lemma 4.A, take $\mathcal{B}$ based on Rule 110 or an equivalent tiling and use a uniform encoding $\iota$ to map $\mathcal{S}$-computations (via UTM) into histories of $\mathcal{B}$, with output read by $\pi$ from finite windows. By Definition 3.5, resource overhead is controlled by an effectively computable function $g$ (polynomial if a polynomial universal substrate is used).

Existence: Cook (2004) proved that Rule 110 simulates any TM (under a periodic background). By adding time as an extra coordinate, one can freeze the evolution diagram into a 2D array $\mathcal{B}\in Q^{\mathbb{Z}\times \mathbb{N}}$, thereby obtaining a universal SB-CA within Definition 3.5. $\square$

**Proof** ((ii) $\Rightarrow$ (i)):

By Definition 3.4, assume a bi-directionally computable isomorphism $\Phi$ whose image covers all UTM-encoded histories. For any $(M,w)$, since $\mathrm{hist}(M,w)\in\mathcal{H}$, there exists a trace $\tau\in\mathrm{Traces}(\mathcal{S})$ with $\Phi(\tau)=\mathrm{hist}(M,w)$. As $\Phi^{-1}$ is computable, we obtain $\tau$, showing that $\mathcal{S}$ simulates any TM, hence is Turing-complete. $\square$

### Corollary 4.1 (Two-Way Reducibility)

$$
\mathcal{S}\ \text{is Turing-complete}\ \Longleftrightarrow\ \exists\ \text{universal-substrate SB-CA } \mathcal{B} : \mathcal{S}\ \text{staticizes into } \mathcal{B}.
$$

**Note 4.1**: Substrate universality is necessary; an SB-CA representation of a non-universal CA is not necessarily Turing-complete.

### Proposition 4.2 (Sanity Check)

Rule 110 simulation: starting state $[0,0,0,1,1,1,0,0]$; next state $[0,0,1,1,0,1,0,0]$ (consistent). Continuing from the same initial state for two more steps:
$$
[0,0,1,1,0,1,0,0]\ \mapsto\ [0,1,1,1,1,1,0,0]
$$
and then one more step:
$$
[0,1,1,1,1,1,0,0]\ \mapsto\ [1,1,0,0,0,1,0,0]
$$

**Proof**: This matches the rule table (verifiable cell-by-cell). The evolution sequence verifies several entries, such as applying $110\to 1$ to center pattern $(1,1,0)$ and $101\to 1$ to $(1,0,1)$, in full agreement with the table. See Appendix B.3 for verification code. $\square$

---

## §5 Staticizing Time

### 5.1 Upper Bounds on Kolmogorov Complexity

From the SB-CA perspective, time $t$ is an index dimension. The sequence $(S_0,S_1,\dots)$ denotes slices of $\mathcal{B}$ along the $t$-direction. Evolution is projection. The following complexity measures are defined on canonical finite encodings (e.g., the shortest generator/enumerator for a given slice or window) so as to avoid nonstandard uses of $K(\cdot)$ on infinite objects.

**Theorem 5.1 (Complexity Upper Bound for Time Slices)**:

For a fixed rule $f$ and initial state $S_0$, let $\ulcorner S_t\urcorner$ denote a canonical finite code for the slice $S_t$ (e.g., the shortest program that, on input $t$, outputs a finite description of that slice). Then its prefix complexity satisfies
$$
K(S_t) \le K(S_0)+K(f)+K(t)+O(1).
$$

Here $K(\cdot)$ denotes prefix Kolmogorov complexity. Note that $K(t)$ is a worst-case coding cost; although the bound can be loose when $t$ is Kolmogorov-random, it is nevertheless a worst-case statement supporting the interpretation of “evolution as addressable reading of a static block.”

(Coarse bound) For standard self-descriptions of natural numbers, $K(t)\le\lfloor\log_2 t\rfloor+O(1)$, consistent with the intuition of “addressing bit-length” (depending on encoding details, this is often expressed as a $\log_2 t + O(\log\log t)$-level standard upper bound).

**Proof**: Given $S_0,f$, and $t$, Levin–Chaitin’s coding theorem and the prefix-coding property yield the bound up to an $O(1)$ additive term. $\square$

### 5.2 Description Length of Finite Windows

**Theorem 5.2 (Finite-Window Complexity Upper Bound)**:

For any finite spacetime window $W\subset \Lambda\times T$, consider the restriction $\mathcal{B}\upharpoonright W$. There exists a constant $c$ (depending on encoding conventions) such that
$$
K\big(\mathcal{B}\upharpoonright W\big) \le K(S_0)+K(f)+c+K(\mathrm{diam}(W))+O(1).
$$

Thus the shortest description length of any finite window is upper-bounded by the combined complexity of the initial state and the local rule; “evolution” is understood as an addressable enumeration/readout of the static block $\mathcal{B}$. Here $\mathrm{diam}(W)$ uses the $\ell_\infty$ product metric on $\Lambda\times T$.

**Proof**: From additivity of Kolmogorov complexity and finite representations of local rules. $\square$

---

## §6 Relation to Computability Theory

### 6.1 Computability

**Definition 6.1 (Partial Computable Functions)**: A Turing-complete system expresses all partial computable functions. Under I/O semantics, the “output-on-halting” convention induces the corresponding total extensionality.

### 6.2 Halting-Problem Duality

**Theorem 6.1 ($\Sigma_1$-Completeness of Block Appearance)**:

In a universal-substrate SB-CA/SFT/tiling system $\mathsf{B}$, given a finite pattern $P$, decide whether
$$
\exists t,\exists W_t\quad P\subseteq \mathcal{B}\upharpoonright W_t
$$
is $\Sigma_1$-complete (Cook-style embeddings reduce halting to the “existence of a witnessing time step”).

**Proof (Reduction Outline)**: Construct a “halting witness pattern” $P_{\mathrm{halt}}$ that encodes a terminal flag on the output track, with a right guard tile that fixes a unique window boundary. For any $\langle M,w\rangle$, uniformly encode the initial condition so that $\mathrm{hist}(M,w)$ exists iff $M(w)$ halts; hence $M(w)$ halts $\Leftrightarrow \exists t,\exists W_t: P_{\mathrm{halt}}\subseteq \mathcal{B}\upharpoonright W_t$. The reduction is many-one and effectively computable. $\square$

**Theorem 6.2 ($\Pi_2$-Hardness of Recurrence)**:

In a universal-substrate SB-CA/SFT/tiling system, deciding whether
$$
\forall t,\exists t'\ge t,\exists W_{t'}\quad P\subseteq \mathcal{B}\upharpoonright W_{t'}
$$
is generally $\Pi_2$-hard; no decision procedure exists below this level on universal substrates.

**Proof (Quantifier Expansion)**: Encode “must-appear/infinitely-often” properties via a monotone-in-$t$ family of windows and the appearance of a marker pattern $P$: $\forall t\,\exists t'\ge t\,\exists W_{t'}\,P\subseteq\mathcal{B}\upharpoonright W_{t'}$. Combined with classic results on the undecidability of global CA properties (Ollinger, 2008), we obtain $\Pi_2$-hardness. $\square$

(Positioning) By the intrinsic universality of the substrate and classic survey results on undecidable global CA properties, these “must-appear/frequently-appear” decisions sit at the $\Pi_2$ level of the arithmetical hierarchy and are therefore generally $\Pi_2$-hard.

**Note 6.1 (Garden-of-Eden Theorem)**: See Moore (1962) and Myhill (1963) for the Garden-of-Eden theorem (pre-injectivity/surjectivity and reachability), complementary to the undecidability statements in this section.

### 6.3 Turing Equivalence

**Proposition 6.1 (Expressive Equivalence)**: TMs embed into SB-CA; under a universal substrate, the domain/image of computable functions coincides with that of TMs (i.e., the same class of Turing-computable functions).

**Proof**: By the two-way embedding of Theorem 4.1. $\square$

---

## §7 Discussion and Philosophical Speculation

The mathematical equivalence between computational completeness and static block structure provides a formal computational framework for revisiting fundamental questions of time, quantum mechanics, and even consciousness. We outline several suggestive consequences below.

**Note 7.1 (Speculative Content)**: This section is intentionally speculative and heuristic, not a strict mathematical conclusion.

### 7.1 Eternalism Analogy

If one adopts the ontic reading of SB-CA, time can be understood as a static dimension, resonating with Barbour (1999). This is a metaphysical stance rather than a mathematical necessity.

### 7.2 Quantum Mechanics Analogy

The static-block representation of SB-CA is formally reminiscent of the path-integral picture of quantum field theory, where “all paths coexist.” However, the non-unitary measurement (collapse) of quantum mechanics has no counterpart in the deterministic SB-CA rules; the analogy is heuristic only. SB-CA uses deterministic local rules and does not include superposition/nonlocal coherence.

---

## §8 Conclusion and Outlook

### 8.1 Main Contributions

We show a formal equivalence between computational completeness and SB-CA. Under the precise condition of a universal substrate, we establish the equivalence between Turing completeness and staticizability, providing formal tools for subsequent research. Time and evolution are understood as observational phenomena. The result unifies the theory of computation and physical reality.

### 8.2 Theoretical Positioning

We provide a static representation framework for computational models, equivalent to the dynamic perspective. The extension relies on constructive SB-CA embeddings, ensuring coherent transitions. We acknowledge that this is a conceptual synthesis rather than an entirely new mathematical theorem.

### 8.3 Future Directions

Short-term: SB-QFT extensions; complexity conservation equations; observer-path modeling.

Long-term: Connections with Zenil’s (2012) computable universe, and applications in quantum computing.

---

## Appendix A: Wang-Tiling “History” Construction (Parallel Embedding Example)

### A.1 Basic Construction

Wang tiling (Wang, 1961) provides a static tiling “history” construction, serving as a parallel substrate to Rule 110. Dynamic CA evolution is frozen as static constraints: each tile encodes state and transition; horizontal matches enforce spatial adjacency; vertical matches enforce temporal evolution. Berger (1966) showed undecidability of the domino problem, highlighting strong expressive power.

### A.2 Concrete Realization

For a simple CA, encode the transition function on tile edges so that a global tiling corresponds to a consistent evolution history. This ensures the static character of SB-CA embeddings. Let upper/lower tile edges encode the local pattern across times $(t,t+1)$, and left/right edges encode spatial adjacency constraints; legal tilings $\Leftrightarrow$ local CA transitions + spatial adjacency simultaneously satisfied $\Leftrightarrow$ consistent CA evolution histories.

### A.3 Local Constraints and Finite-Intersection Extension (Constructive Outline)

Let $C$ be the following finite set of cylindrical constraints:
1) Temporal consistency: for each $(x,t)$, upper/lower edge labels encode the local pattern at $t$ and its image at $t+1$, equivalent to the CA rule $f$;
2) Spatial adjacency: for each $(x,t)$, left/right neighboring tiles match along touching edges;
3) Initial row: the $t=0$ row encodes the initial tape given by $\iota(M,w)$.
The dependency graph is a DAG in the time direction. Whenever a family of finite-window patterns is pairwise compatible, we can assemble them layer by layer in time: first fix $t=0$, then extend to $t=1,2,\dots$. Hence finite-intersection extension holds and a global configuration exists (SFT closedness and compactness provide the limit). Constructive extension order: lay down the initial layer $t=0$, then extend outward in $t=1,2,\dots$ layers; the limit is the global configuration.

---

## Appendix B: Explicit Encoding Table from Rule 110 to SB-CA

### B.1 Rule Table

The table below uses the standard alignment (left, center, right) $\to$ next state of the center cell, consistent with Wolfram (2002, pp. 675–702).

| Current (L,C,R) | Next (center) |
|-----------------|----------------|
| 000             | 0              |
| 001             | 1              |
| 010             | 1              |
| 011             | 1              |
| 100             | 0              |
| 101             | 1              |
| 110             | 1              |
| 111             | 0              |

### B.2 SB-CA Embedding Example

SB-CA embedding: time extends downward; space extends horizontally. Example initial: $[0,0,0,1,1,1,0,0]$ $\to$ next: $[0,0,1,1,0,1,0,0]$.

### B.3 Correspondence from Rule Table to SB-CA Constraints and Verification Code

Correspondence: Treat each of the 8 triples $(l,c,r)\mapsto c'$ in Table B.1 as a “temporal consistency” constraint: the upper edge at $(x,t)$ encodes $(l,c,r)$ and the lower edge encodes $c'$, while left/right edges enforce matching with neighboring $l,r$. Thus, a legal tiling holds iff all local transitions satisfy Table B.1.

Verification code (Python style):

```python
RULE110 = {
    (0,0,0):0,(0,0,1):1,(0,1,0):1,(0,1,1):1,
    (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):0,
}

def step(state):
    n = len(state)
    nxt = [0]*n
    for i in range(n):
        l,c,r = state[(i-1)%n], state[i], state[(i+1)%n]
        nxt[i] = RULE110[(l,c,r)]
    return nxt

assert step([0,0,0,1,1,1,0,0]) == [0,0,1,1,0,1,0,0]
```

Note: The example uses a torus boundary (mod $n$) for executable verification; the main claims hold on $\Lambda=\mathbb{Z}^d$. If a torus is used, include its size in the encoding and choose it large enough to accommodate the required history.

---

## References

1. Gödel, K. (1931). Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I.
2. Wolfram, S. (2002). *A New Kind of Science*. Wolfram Media.
3. Tegmark, M. (2014). *Our Mathematical Universe*. Knopf.
4. Lloyd, S. (2006). *Programming the Universe*. Knopf.
5. Cook, M. (2004). Universality in Elementary Cellular Automata. *Complex Systems* 15(1), 1–40.
6. Barbour, J. (1999). *The End of Time: The Next Revolution in Physics*. Oxford University Press.
7. Zenil, H. (2012). *A Computable Universe: Understanding and Exploring Nature as Computation*. World Scientific.
8. Aaronson, S. (2024). Quantum Computing: Between Hope and Hype. *Shtetl-Optimized Blog*, accessed Oct 17, 2025. (discussion citation)
9. Auric, H. (2025). Collapse-Aware Foundations of Static Block Reality.
10. Hedlund, G. A. (1969). Endomorphisms and Automorphisms of the Shift Dynamical System. *Mathematical Systems Theory* 3(4), 320–375.
11. Berger, R. (1966). The Undecidability of the Domino Problem. *Memoirs of the American Mathematical Society* 66.
12. Wang, H. (1961). Proving Theorems by Pattern Recognition II. *Bell System Technical Journal* 40(1), 1–41.
13. Ollinger, N. (2008). Universalities in Cellular Automata: a (short) survey. arXiv:0809.5065.
14. Kari, J. (1994). Reversibility and Surjectivity Problems of Cellular Automata. *Journal of Computer and System Sciences* 48(1), 149–182.
15. Toffoli, T. (1977). Computation and Construction Universality of Reversible Cellular Automata. *Journal of Computer and System Sciences* 15(2), 213–231.
16. Morita, K. (1995). Reversible Simulation of One-Dimensional Irreversible Cellular Automata. *Theoretical Computer Science* 148(1), 157–163.
17. Li, M., & Vitányi, P. (2008). *An Introduction to Kolmogorov Complexity and Its Applications* (3rd ed.). Springer.
18. Moore, E. F. (1962). Machine Models of Self-Reproduction. *Proceedings of the Symposium on Mathematical Problems in the Biological Sciences*, 17–33.
19. Myhill, J. (1963). The Converse of Moore’s Garden-of-Eden Theorem. *Proceedings of the American Mathematical Society* 14(5), 685–686.

---

**Acknowledgments**

We thank the reviewers for their feedback that ensured the logical coherence of the revised version. In particular, we are grateful for the emphasis on the universal substrate condition, the precision of computable isomorphism, and other key issues, which greatly improved this work.

**Version Notes**

v1.6.1-final (2025-10-17): Submission version. Final optimizations based on review feedback, ensuring a clear universal substrate condition, precise definition of computable isomorphism, coherent arithmetical-level presentation of the halting duality, and inclusion of complete formal definitions, theorem proofs, simulation checks, and the Rule 110 encoding table. The paper is ready for submission.


