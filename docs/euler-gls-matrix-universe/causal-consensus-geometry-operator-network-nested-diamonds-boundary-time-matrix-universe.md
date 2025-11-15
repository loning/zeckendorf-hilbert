# 因果共识的几何与算子网络：嵌套因果菱形、边界时间几何与矩阵宇宙

---

## Abstract

A causal description of the universe that simultaneously respects Lorentzian geometry, quantum field theory, modular theory and holographic information bounds can be organized around small causal diamonds and their boundary algebras. In this work, a unified framework is constructed in which:

1. The space–time background is encoded by a nested family of small causal diamonds $(D_{p,r})$ on a globally hyperbolic Lorentzian manifold. Their partial order and generalized entropy arrow define a time-free "causal manifold" structure.

2. On the boundary $\partial D$ of each small causal diamond, a boundary algebra, a state and a local scattering matrix $S_D(\omega)$ are assigned. Using the Birman–Kreĭn formula and Wigner–Smith time-delay operator, a unified time scale

   $$
   \kappa(\omega)
   =\frac{\varphi'(\omega)}{\pi}
   =\rho_{\mathrm{rel}}(\omega)
   =\frac{1}{2\pi}\operatorname{tr}Q(\omega),
   \quad Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega),
   $$

   is defined, where $\varphi$ is the total scattering half-phase and $\rho_{\mathrm{rel}}$ the relative spectral density. This realizes "time" as a boundary-generated operator-valued scale.

3. Observers are modeled as paths $\gamma$ in a causal-diamond complex equipped with a Hilbert bundle and an operator-valued connection $\mathcal A$. The experienced world of an observer is given by the path-ordered product

   $$
   U_\gamma(\omega)=\mathcal P\exp\int_\gamma\mathcal A(\omega;x,\chi),
   $$

   which combines local scattering matrices and modular flows along the path. Causal consensus between multiple observers is then expressed as equivalence of these ordered products, under curvature bounds and topological constraints.

4. On overlapping chains of causal diamonds, the modular Hamiltonians obey a Markov property along null boundaries, leading to conditional mutual information $I(D_{j-1}:D_{j+1}\mid D_j)$ as a quantitative measure of "causal gaps". This is controlled by quantum null energy–entropy inequalities (QNEC) and the Markov property of null-plane modular Hamiltonians.

Within this structure, three main results are obtained: (i) under geometric and Čech-type consistency conditions, local scattering data on small causal diamonds glue to a Hilbert bundle with connection over $M\times X^\circ$, providing a precise geometric realization of a "matrix universe"; (ii) in curvature-bounded and topologically trivial $\mathbb Z_2$ sectors, homotopic observer paths with equal endpoints define unitaries that are equivalent up to controlled errors, giving a notion of scale-invariant causal consensus; (iii) when Bekenstein–Hawking–type generalized entropy bounds hold, the number of effective degrees of freedom of the matrix universe inside a finite causal region is bounded by $\exp S_{\mathrm{gen}}$, relating matrix size to area, curvature and entanglement entropy.

The framework yields a geometric and operator-theoretic interpretation of the slogan "causal consensus = a huge matrix computation": consistent global causal structure appears as a flatness and anomaly-free condition on an operator-valued connection over the causal-diamond complex, while disagreements and gaps between observers are encoded as curvature, conditional mutual information and $\mathbb Z_2$ holonomy.

---

## Keywords

因果结构；小因果菱形；因果流形；边界时间几何；统一时间刻度；散射矩阵；Wigner–Smith 群延迟；Hilbert 丛与联络；观察者共识；Null–Modular 双覆盖；$\mathbb Z_2$ holonomy；矩阵宇宙

---

## 1 Introduction & Historical Context

### 1.1 Causal structure without external time

In general relativity, causal structure is encoded by the light cones of a Lorentzian manifold $(M,g)$, together with global hyperbolicity and the absence of closed timelike curves. Classical results show that the causal order already determines much of the topology and conformal structure of space–time. A complementary line of work in causal set theory replaces the continuum by a locally finite partially ordered set, under the slogan "Order + Number = Geometry".

These developments suggest that "causality" is more primitive than metric or time functions. Nevertheless, in practical physics, time usually re-enters as a parameter in Hamiltonian or Lagrangian dynamics, and as a coordinate in PDE formulations. A formulation in which causal structure is primary, while "time" is understood as a derived, observer-relative scale, remains conceptually attractive but technically challenging.

The present work adopts the following guiding idea:

*The universe at the ontological level is a time-parameter-free causal manifold; what observers call "time" and "evolution" arises from the way local operator algebras on small causal diamonds are glued and compared, under finite information capacity.*

### 1.2 Scattering theory, spectral shift and unified time scale

On the spectral side, scattering theory relates a pair of self-adjoint operators $(H,H_0)$ to a scattering matrix $S(\lambda)$ and a spectral shift function $\xi(\lambda)$. Under trace class perturbation hypotheses, Birman and Kreĭn established the fundamental relation

$$
\det S(\lambda)=\exp\bigl(-2\pi i\,\xi(\lambda)\bigr),
$$

which connects phase shifts and spectral shifts. In many concrete models, the derivative $\xi'(\lambda)$ coincides with a relative density of states and can be written in terms of the Wigner–Smith time-delay operator

$$
Q(\lambda)=-i S(\lambda)^\dagger\partial_\lambda S(\lambda).
$$

In parallel, Wigner and Smith introduced the lifetime matrix and group delay in collision theory. Combined with the Birman–Kreĭn formula, one can identify, in appropriate units,

$$
\kappa(\lambda)
=\frac{\varphi'(\lambda)}{\pi}
=\rho_{\mathrm{rel}}(\lambda)
=\frac{1}{2\pi}\operatorname{tr}Q(\lambda),
$$

where $\varphi(\lambda)$ is the total half-phase of $S(\lambda)$ and $\rho_{\mathrm{rel}}(\lambda)=\xi'(\lambda)$ is the relative spectral density. This quantity $\kappa$ will serve as a *universal time scale* in the present framework.

### 1.3 Modular flow, null surfaces and generalized entropy

On the algebraic side, Tomita–Takesaki modular theory associates to any von Neumann algebra $\mathcal M$ with cyclic and separating vector $\Omega$ a modular operator $\Delta$, unitary modular group $\sigma_t(A)=\Delta^{it}A\Delta^{-it}$ and modular Hamiltonian $K=-\log\Delta$. Modular flow provides an intrinsic notion of "thermal time" determined purely by the state and the algebra.

For quantum field theories on null hypersurfaces, Casini, Teste and Torroba have computed modular Hamiltonians of regions whose future horizon lies on a null plane, and shown that these modular Hamiltonians enjoy a Markov property along the null direction, saturating strong subadditivity of entropy. This Markov property underlies a vanishing conditional mutual information and will play a central role in quantifying "causal gaps" in chains of small causal diamonds.

Quantum null energy inequalities (QNEC) refine this picture by bounding the expectation value of the null–null component of the stress tensor $T_{kk}$ from below by the second variation of von Neumann entropy along null deformations of a surface. Together with the quantum focusing conjecture and Bousso bounds, these results connect entropy, energy and causality in a sharp inequality framework.

Finally, Jacobson has shown that imposing *entanglement equilibrium*—maximization of vacuum entanglement entropy in small geodesic balls at fixed volume—yields the semiclassical Einstein equation. This indicates that small causal diamonds and their entanglement properties encode not only causal structure but curvature.

### 1.4 Causal diamonds and matrix universes

Small causal diamonds $D_{p,r}=J^+(p^-)\cap J^-(p^+)$ are natural local units of causal geometry. For globally hyperbolic space–times, appropriately chosen families of such diamonds form good covers whose Čech nerves recover the topology of $M$. At the same time, each diamond carries a boundary algebra, a state and an effective scattering matrix encoding the response of the quantum fields to the geometry and matter content inside the diamond.

If one assigns to each small diamond a scattering matrix $S_D(\omega)$ (with $\omega$ a spectral parameter) and organizes these matrices into a Hilbert bundle over $M\times X^\circ$, with an operator-valued connection $\mathcal A$, then any observer path $\gamma\subset M$ lifts to a path in this bundle and determines a path-ordered unitary

$$
U_\gamma(\omega)=\mathcal P\exp\int_\gamma \mathcal A(\omega;x,\chi).
$$

The universe, from this perspective, is a *matrix universe*: its causal structure and observer experiences are encoded in consistency conditions and curvature properties of $\mathcal A$.

### 1.5 Contributions

This work develops a unified geometric and operator-theoretic framework for "causal consensus as a huge matrix computation" along the following lines:

1. **Causal-diamond geometry and causal gaps.** A family of small causal diamonds on a globally hyperbolic Lorentzian manifold is organized into a causal-diamond complex. On overlapping chains of diamonds, the conditional mutual information and Markov property along null boundaries define a quantitative notion of "causal gap".

2. **Boundary-time geometry and matrix universe.** To each diamond is associated a boundary algebra, state and scattering matrix satisfying a unified time-scale identity $\kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\mathrm{tr}Q(\omega)$. Under Čech-type consistency conditions, these local data glue to a Hilbert bundle with operator-valued connection $\mathcal A$, yielding a matrix universe $(M,\mathcal H,\mathcal A)$.

3. **Causal consensus and topological sectors.** Observers are modeled as paths in the causal-diamond complex. Causal consensus between observers corresponds to equivalence of path-ordered unitaries for homotopic paths with equal endpoints, controlled by the curvature of $\mathcal A$ and the absence of $\mathbb Z_2$ anomalies (Null–Modular double cover). Causal disagreement is encoded as holonomy and curvature, and linked to conditional mutual information.

4. **Information capacity and emergent classical geometry.** When generalized entropy $S_{\mathrm{gen}}$ satisfies Bekenstein–Hawking–type bounds, the effective Hilbert dimension associated with a finite causal region is bounded by $\exp S_{\mathrm{gen}}$. In coarse-grained regimes where Markov gaps and curvature are small, strong causal consensus holds and classical Lorentzian geometry emerges.

The remainder of the paper develops this framework systematically, states and sketches proofs of the main theorems, and discusses modeling and engineering aspects of matrix universes as causal-consensus computing networks.

---

## 2 Model & Assumptions

### 2.1 Lorentzian background and small causal diamonds

Let $(M,g)$ be a four-dimensional, oriented, time-oriented Lorentzian manifold with signature $(-+++)$, satisfying:

1. **Global hyperbolicity.** There exists a Cauchy surface $\Sigma\subset M$ such that every inextendible causal curve intersects $\Sigma$ exactly once.

2. **Stable causality.** There exists a smooth time function $T\colon M\to\mathbb R$ strictly increasing along future-directed timelike curves; no closed causal curves exist.

3. **Curvature scale.** For each point $p\in M$, a local curvature scale $L_{\mathrm{curv}}(p)$ is defined such that in normal coordinates $g_{ab}(x)=\eta_{ab}+O(|x|^2/L_{\mathrm{curv}}^2)$ as $|x|\to 0$.

For each $p\in M$ and sufficiently small $r\ll L_{\mathrm{curv}}(p)$, choose a unit future-directed timelike vector $u^a\in T_pM$ and define

$$
p^\pm=\exp_p(\pm r,u^a),
\quad
D_{p,r}=J^+(p^-)\cap J^-(p^+),
$$

the small causal diamond centered at $p$ with time scale $2r$. Its boundary $\partial D_{p,r}$ consists of two null hypersurfaces generated by null geodesics from $p^\pm$, meeting along a spacelike codimension-2 "edge".

**Geometric Axiom G.**

1. $(M,g)$ satisfies global hyperbolicity and stable causality as above.

2. For all $p$ and sufficiently small $r$, the diamond $D_{p,r}$ is causally convex and diffeomorphic to a diamond in Minkowski space; deviations of volumes and areas from the flat case are $O(r^2)$.

The family of all such diamonds $\mathcal D=\{D_\alpha\}_{\alpha\in A}$ will be called a *small-diamond family*.

### 2.2 Causal-diamond complex and causal gaps

Given a small-diamond family $\mathcal D$, define its Čech nerve $\mathsf K(\mathcal D)$ as follows:

* Vertices correspond to nonempty diamonds $D_\alpha$.

* A $k$-simplex $[\alpha_0\cdots\alpha_k]$ is present whenever $D_{\alpha_0}\cap\cdots\cap D_{\alpha_k}\neq\varnothing$.

The geometric realization $|\mathsf K(\mathcal D)|$ is homotopy equivalent to $M$ when $\mathcal D$ is a good cover.

Restricting the global causal order $\prec$ on $M$ to each diamond defines local partial orders $\prec_\alpha$ on $D_\alpha$. The compatibility of these partial orders on overlaps is captured by:

**Assumption C (Čech causal consistency).**

For every nonempty finite intersection $D_J=\bigcap_{j\in J}D_{\alpha_j}$, there exists a partial order $\prec_J$ on $D_J$ such that $\prec_J$ restricts to $\prec_{\alpha_j}$ on each $D_{\alpha_j}\cap D_J$.

Under this assumption, a global partial order $\prec$ can be reconstructed on $M$ by taking the transitive closure of the local relations; this will be made precise and proved in Appendix A.

For a chain of overlapping diamonds

$$
\cdots,D_{j-1},D_j,D_{j+1},\cdots,
$$

one can consider the algebras and states associated with the corresponding regions and define the conditional mutual information

$$
I(D_{j-1}:D_{j+1}\mid D_j)
$$

with respect to the vacuum or another reference state. In algebraic QFT on null surfaces, null-plane modular Hamiltonians exhibit a Markov property implying the saturation of strong subadditivity and the vanishing of such conditional mutual information in idealized configurations.

Deviations from zero can be interpreted as *causal gaps*; they will be quantified in terms of an entropy density along null generators in Section 3.

### 2.3 Boundary-time geometry and unified time scale

On each diamond boundary $\partial D$, we consider a Hilbert space $\mathcal H_{\partial D}$ describing the degrees of freedom crossing the null boundary (for instance, the one-particle Hilbert space of a free field restricted to the boundary, or an appropriate Fock-space factor). We then assign:

* A von Neumann algebra $\mathcal A_{\partial D}\subset\mathcal B(\mathcal H_{\partial D})$ of boundary observables;

* A reference state $\omega_{\partial D}$ (e.g. the vacuum or a thermal state);

* A scattering matrix $S_D(\omega)\in\mathcal U(\mathcal H_{\partial D})$ depending measurably on a spectral parameter $\omega\in X^\circ$ (such as energy, momentum or other quantum numbers).

From the pair $(H_D,H_{0,D})$ of self-adjoint generators of interacting and reference dynamics, one can define a spectral shift function $\xi_D(\omega)$ and a Wigner–Smith operator

$$
Q_D(\omega)=-i S_D(\omega)^\dagger \partial_\omega S_D(\omega),
$$

so that, under standard hypotheses of scattering theory, a Birman–Kreĭn-type formula holds:

$$
\det S_D(\omega)=\exp\bigl(-2\pi i\,\xi_D(\omega)\bigr),
$$

and in particular

$$
\rho_{\mathrm{rel},D}(\omega)
:=\xi_D'(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q_D(\omega)
=\frac{\varphi_D'(\omega)}{\pi},
$$

with $\varphi_D$ the total half-phase of $S_D$.

This suggests the following:

**Time-scale Axiom T.**

For each diamond $D$, there exists a function $\kappa_D(\omega)$ such that

$$
\kappa_D(\omega)
=\frac{\varphi_D'(\omega)}{\pi}
=\rho_{\mathrm{rel},D}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q_D(\omega),
$$

and the corresponding modular flow parameter for the state $\omega_{\partial D}$ restricted to $\mathcal A_{\partial D}$ is affinely equivalent to $\omega\mapsto\int^\omega\kappa_D(\omega')\,\mathrm d\omega'$. In particular, the "scattering time", "modular time" and "geometric time" based on Brown–York boundary Hamiltonians lie in the same equivalence class $[\tau]$.

This axiom formalizes the unification of time scales from scattering, modular theory and boundary geometry.

### 2.4 Observers as local causal fragments

Let $X$ denote the abstract set of events in the causal manifold, endowed with the global partial order $\prec$. An *observer* $O_i$ is modeled as a multi-component structure

$$
O_i=(C_i,\prec_i,\Lambda_i,\mathcal A_i,\omega_i,\mathcal M_i,U_i,u_i,\mathcal C_{ij}),
$$

where:

* $C_i\subset X$ is the observer's accessible causal domain;

* $\prec_i$ is a local partial order on $C_i$, compatible with $\prec$;

* $\Lambda_i$ is a resolution scale (cutoff function on spacetime and frequency);

* $\mathcal A_i\subset\mathcal B(\mathcal H_i)$ is the observer's accessible algebra;

* $\omega_i$ is the observer's state (belief state) on $\mathcal A_i$;

* $\mathcal M_i$ is a model family (parametrized dynamics or hypotheses);

* $U_i$ is an update or learning operator (possibly CPTP);

* $u_i$ is a preference or utility functional;

* $\mathcal C_{ij}$ encodes communication channels between observers $i$ and $j$.

The family $\{O_i\}_{i\in I}$ yields local causal data and local operator-algebraic descriptions that must be glued to obtain a coherent global causal network.

### 2.5 Null–Modular double cover and $\mathbb Z_2$ sectors

On chains of overlapping diamonds whose boundaries are related by null deformations, modular Hamiltonians often exhibit a Markov property: the vacuum state restricted to unions of adjacent regions is a quantum Markov chain along the null direction.

At the same time, feedback loops and self-referential scattering networks can produce a square-root branch structure for scattering determinants, defining a principal $\mathbb Z_2$ bundle with holonomy

$$
\nu_{\sqrt S}(\gamma)\in\{\pm1\}
$$

for closed loops $\gamma$ in parameter space. The corresponding obstruction class

$$
[K]\in H^2(Y,\partial Y;\mathbb Z_2),
\quad Y=M\times X^\circ,
$$

measures possible topological anomalies.

For the main existence and consensus theorems, we impose:

**Topological Axiom A.**

In the region and energy window of interest, the $\mathbb Z_2$ obstruction class vanishes:

$$
[K]=0,\quad
\nu_{\sqrt S}(\gamma)=+1\ \text{for all relevant closed loops }\gamma.
$$

This ensures that the matrix universe is free of discrete $(\mathbb Z_2)$ anomalies and that path holonomy depends continuously on the connection curvature alone.

---

## 3 Main Results: Geometry of Matrix Universe and Causal Consensus

### 3.1 Reconstruction from small causal diamonds

The first result states that a dense family of small causal diamonds with compatible local partial orders reconstructs the causal manifold $(M,g)$.

**Theorem 3.1 (Causal-diamond reconstruction).**

Let $(M,g)$ satisfy Axiom G. Let $\mathcal D=\{D_\alpha\}_{\alpha\in A}$ be a small-diamond family forming a good cover and satisfying Čech causal consistency (Assumption C). Then:

1. The geometric realization $|\mathsf K(\mathcal D)|$ of the Čech nerve is homotopy equivalent to $M$.

2. The global causal partial order $\prec$ on $M$ is uniquely determined by the family of local partial orders $\{\prec_\alpha\}$ via transitive closure of the relation

   $$
   xRy\iff\exists\alpha:\ x,y\in D_\alpha,\ x\prec_\alpha y.
   $$

3. In the limit of arbitrarily small diamonds, the metric $g$ can be reconstructed (up to diffeomorphism) from the volumes, edge areas and entanglement properties of the diamonds.

The proof uses the Čech nerve theorem for good covers, combined with standard results that causal structure plus local volume data fix the conformal and metric structure, and with entanglement-equilibrium arguments for small geodesic balls. Detailed arguments are given in Appendix A.

### 3.2 Matrix universe: Hilbert bundle and operator connection

Organize the local boundary data into a global Hilbert bundle and operator-valued connection.

Let

$$
Y:=M\times X^\circ
$$

where $X^\circ$ is an open set of spectral parameters (e.g. energy–momentum–spin labels). For each diamond $D_\alpha$, choose a neighborhood $U_\alpha\subset M$ containing $D_\alpha$ and define a local Hilbert bundle $\mathcal H_\alpha\to U_\alpha\times X^\circ$ with fiber $\mathcal H_{\partial D_\alpha}$, together with a local scattering field $S_\alpha(\omega;x,\chi)$.

On overlaps $U_{\alpha\beta}=U_\alpha\cap U_\beta$, assume there exist unitary transition functions

$$
U_{\alpha\beta}(x,\chi)\colon
\mathcal H_\beta|_{(x,\chi)}\to\mathcal H_\alpha|_{(x,\chi)}
$$

such that

$$
S_\alpha(\omega;x,\chi)
=U_{\alpha\beta}(x,\chi)\,S_\beta(\omega;x,\chi)\,U_{\alpha\beta}(x,\chi)^\dagger,
$$

and the Čech 1-cocycle condition

$$
U_{\alpha\beta}U_{\beta\gamma}=U_{\alpha\gamma}
\quad\text{on }U_{\alpha\beta\gamma}
$$

holds.

**Theorem 3.2 (Existence and uniqueness of matrix universe).**

Under Axioms G, T and A, and the above consistency conditions, there exist:

1. A Hilbert bundle $\pi\colon\mathcal H\to Y$ with local trivializations agreeing with $\mathcal H_\alpha$ on $U_\alpha\times X^\circ$;

2. A global unitary-valued field $S(\omega;x,\chi)\in\mathcal U(\mathcal H_{(x,\chi)})$;

3. An operator-valued connection one-form

   $$
   \mathcal A(\omega;x,\chi)
   =S(\omega;x,\chi)^\dagger\,\mathrm d S(\omega;x,\chi),
   $$

   whose frequency component encodes the Wigner–Smith time-delay operator and whose space–parameter components encode the variation of scattering with respect to geometry and external parameters,

such that, for every $D_\alpha$, the restriction of $(\mathcal H,\mathcal A,S)$ to $\partial D_\alpha\times X^\circ$ reproduces the local data, and the unified time-scale identity

$$
\kappa(\omega;x,\chi)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega;x,\chi)
=\frac{\partial\varphi(\omega;x,\chi)}{\partial\omega}
$$

holds in the prescribed scattering window.

Moreover, $(\mathcal H,\mathcal A)$ is unique up to Hilbert bundle isomorphisms that act by unitary gauge transformations on the fibers.

The proof uses standard gluing of Hilbert bundles from Čech data and the transformation properties of $S$ under local unitaries to define a gauge-covariant connection. Details appear in Appendix B.

The triple

$$
\mathfrak U:=(M,\mathcal H,\mathcal A)
$$

will be called a *matrix universe*.

### 3.3 Causal consensus for observer paths

Let $\gamma\colon[0,1]\to M$ be a piecewise smooth curve representing an observer's worldline or, more generally, a concatenation of small causal-diamond centers. Lifting $\gamma$ to $Y$ with a parameter path $\chi(t)$ yields a path $(\gamma(t),\chi(t))$ along which we can define the path-ordered unitary

$$
U_\gamma(\omega)
=\mathcal P\exp\int_\gamma \mathcal A(\omega;x,\chi).
$$

Two observers with the same initial and final events but different paths $\gamma_1,\gamma_2$ may produce different unitaries. Their disagreement is measured by a gauge-invariant distance:

$$
d\bigl(U_{\gamma_1}(\omega),U_{\gamma_2}(\omega)\bigr)
:=\inf_{V\in\mathcal U(\mathcal H)}\,\bigl|U_{\gamma_1}(\omega)-V U_{\gamma_2}(\omega) V^\dagger\bigr|.
$$

Let $\Gamma=\gamma_1\circ\gamma_2^{-1}$ be the closed loop formed by $\gamma_1$ followed by the reverse of $\gamma_2$. The holonomy of $\mathcal A$ around $\Gamma$ is

$$
\mathcal U(\Gamma,\chi)
=\mathcal P\exp\oint_\Gamma \mathcal A(\omega;x,\chi).
$$

Suppose the curvature two-form $\mathcal F=\mathrm d\mathcal A+\mathcal A\wedge\mathcal A$ is bounded in operator norm by $\delta$ on a region $\Omega\subset M$ and energy window $I\subset X^\circ$. The area of any surface spanning $\Gamma$ inside $\Omega$ is denoted $\mathrm{Area}(\Gamma)$.

**Theorem 3.3 (Strong causal consensus in almost flat matrix universes).**

Let $\mathfrak U=(M,\mathcal H,\mathcal A)$ be a matrix universe satisfying Axioms G, T, A. Assume there exist $\Omega\subset M$ and $I\subset X^\circ$ such that:

1. $\gamma_1,\gamma_2\subset\Omega$, with $\gamma_1(0)=\gamma_2(0)$, $\gamma_1(1)=\gamma_2(1)$, and $\gamma_1$ homotopic to $\gamma_2$ within $\Omega$;

2. $\lVert\mathcal F\rVert_{L^\infty(\Omega\times I)}\le\delta$;

3. The $\mathbb Z_2$ obstruction class $[K]=0$ on the relevant portion of $M\times X^\circ$.

Then there exists a constant $C>0$ depending only on geometric data of $\Omega$ such that, for all $\omega\in I$,

$$
d\bigl(U_{\gamma_1}(\omega),U_{\gamma_2}(\omega)\bigr)
\le C\,\delta\,\mathrm{Area}(\Gamma).
$$

In particular, in the limit $\delta\to 0$ with bounded area, we have

$$
U_{\gamma_1}(\omega)\sim U_{\gamma_2}(\omega),
$$

i.e. they differ only by a global unitary conjugation and an overall phase equivalent to a reparametrization of the unified time scale.

The proof uses a non-Abelian Stokes theorem and curvature estimates, together with the triviality of $\mathbb Z_2$ holonomy ensured by $[K]=0$. Details are deferred to Appendix C.

### 3.4 Causal gaps and Markov defect

On a chain of overlapping diamonds $(D_{j-1},D_j,D_{j+1})$ whose boundaries share portions of null hypersurfaces, let $\omega$ be a reference state (e.g. vacuum) and denote by $K_{D_j}$ the modular Hamiltonian for region $D_j$. Casini–Teste–Torroba showed that, for a wide class of regions stretching along null surfaces, the modular Hamiltonian is local on the null boundary and satisfies a Markov property.

Define the conditional mutual information

$$
I(D_{j-1}:D_{j+1}\mid D_j)
:=S(D_{j-1}D_j)+S(D_jD_{j+1})-S(D_j)-S(D_{j-1}D_jD_{j+1}),
$$

where $S$ denotes von Neumann entropy of the reduced state. In ideal Markov chains along null directions, this quantity vanishes.

Introduce an entropy density $\iota(v,x_\perp)$ along each null generator, where $v$ is an affine parameter and $x_\perp$ labels transverse directions; then

$$
I(D_{j-1}:D_{j+1}\mid D_j)
=\iint\iota(v,x_\perp)\,\mathrm dv\,\mathrm d^{d-2}x_\perp.
$$

**Definition 3.4 (Causal gap density).**

The causal gap density is defined as

$$
\mathfrak g(v,x_\perp)
:=\iota(v,x_\perp).
$$

The integrated causal gap

$$
G[D_{j-1},D_j,D_{j+1}]
:=I(D_{j-1}:D_{j+1}\mid D_j)
=\iint\mathfrak g(v,x_\perp)\,\mathrm dv\,\mathrm d^{d-2}x_\perp
$$

measures the deviation from perfect Markovianity along the chain.

Quantum null energy inequalities imply that $\iota$ is bounded below by a multiple of the expansion of null congruences and stress tensor components. Thus $\mathfrak g$ encodes both geometric focusing and information-theoretic non-Markovianity.

Chains with small $G$ correspond to regions where local causal order is close to a total order and where small diamonds behave approximately as Markov links in an information-theoretic sense.

### 3.5 Information-capacity bound

Finally, consider a finite causal region $\mathcal R\subset M$ with boundary $\partial\mathcal R$. The generalized entropy associated with $\partial\mathcal R$ is

$$
S_{\mathrm{gen}}[\partial\mathcal R]
=\frac{\mathrm{Area}[\partial\mathcal R]}{4G\hbar}
+S_{\mathrm{out}},
$$

where $S_{\mathrm{out}}$ is the von Neumann entropy of quantum fields outside the region. In semi-classical regimes, this functional obeys generalized second-law-type monotonicity and extremality conditions.

Within the matrix-universe description, the degrees of freedom accessible inside $\mathcal R$ form an effective Hilbert space $\mathcal H_{\mathcal R}$ obtained by restricting $\mathcal H$ to $Y_{\mathcal R}=\mathcal R\times X^\circ$ and imposing UV and IR cutoffs appropriate to the unified time scale.

**Theorem 3.5 (Matrix-universe information-capacity bound).**

Under Axioms G, T, A, and assuming semi-classical gravity with generalized entropy $S_{\mathrm{gen}}[\partial\mathcal R]$ finite, the dimension of the effective Hilbert space $\mathcal H_{\mathcal R}$ satisfies

$$
\log\dim\mathcal H_{\mathcal R}
\lesssim S_{\mathrm{gen}}[\partial\mathcal R],
$$

up to $O(1)$ constants depending on the choice of UV and IR cutoffs and on the unified time scale.

Thus, the matrix size associated with $\mathcal R$ is exponentially bounded by its generalized entropy, tying together area, curvature, entanglement and matrix degrees of freedom.

---

## 4 Proofs: Strategy and Geometric Picture

### 4.1 Proof strategy for Theorem 3.1

For Theorem 3.1, the key steps are:

1. **Topological reconstruction.** The small-diamond family $\mathcal D$ forms a good cover: each intersection of diamonds is either empty or contractible, due to the local Minkowskian structure and small curvature corrections. The Čech nerve theorem then implies that $|\mathsf K(\mathcal D)|$ is homotopy equivalent to $M$.

2. **Causal order reconstruction.** Define the relation $R$ on $M$ by

   $$
   xRy\iff\exists\alpha:\ x,y\in D_\alpha,\ x\prec_\alpha y.
   $$

   Using Čech causal consistency, one shows that $R$ is antisymmetric and that its transitive closure $\prec$ has no nontrivial cycles. This yields a partial order. Local agreement with $\prec_\alpha$ implies that $\prec$ coincides with the original causal order.

3. **Metric reconstruction.** Standard results show that the causal order and local volume information fix $g$ up to conformal factor; the conformal factor can be recovered from volume densities, or, more refined, from entanglement entropies in small balls using Jacobson's entanglement-equilibrium argument.

Details, including the handling of nontrivial causal boundaries and curvature corrections, are given in Appendix A.

### 4.2 Proof strategy for Theorem 3.2

For Theorem 3.2, the argument proceeds as follows:

1. **Čech data for Hilbert bundles.** The local Hilbert spaces $\mathcal H_\alpha$ and unitaries $U_{\alpha\beta}$ define a Čech 1-cocycle with values in the unitary group of infinite-dimensional Hilbert space. Standard bundle theory produces a Hilbert bundle $\mathcal H\to Y$ whose restriction to $U_\alpha\times X^\circ$ is isomorphic to $\mathcal H_\alpha$.

2. **Global scattering field.** On overlaps, the local scattering matrices transform as

   $$
   S_\alpha=U_{\alpha\beta}S_\beta U_{\alpha\beta}^\dagger,
   $$

   ensuring that the local definitions patch to a global $S(\omega;x,\chi)$.

3. **Connection construction.** Define on each local trivialization

   $$
   \mathcal A_\alpha
   =S_\alpha^\dagger\,\mathrm d S_\alpha.
   $$

   Under unitary gauge transformations $S_\alpha\mapsto V_\alpha S_\alpha$, the local connection transforms as

   $$
   \mathcal A_\alpha\mapsto V_\alpha\mathcal A_\alpha V_\alpha^\dagger + V_\alpha\,\mathrm d V_\alpha^\dagger,
   $$

   which is the usual transformation law for a connection. The cocycle relations for $U_{\alpha\beta}$ ensure that the $\mathcal A_\alpha$ glue to a global connection $\mathcal A$.

4. **Unified time scale.** The frequency component of $\mathcal A$ reproduces $Q=-iS^\dagger\partial_\omega S$, whose trace yields $\kappa(\omega)$. Under Axiom T, this matches the modular and geometric times, giving a unified time scale.

Uniqueness follows from the uniqueness of Hilbert bundles up to isomorphism given fixed Čech data, and from the gauge covariance of the connection construction. Full details are provided in Appendix B.

### 4.3 Proof strategy for Theorem 3.3

The key idea in Theorem 3.3 is to relate the difference between unitaries along homotopic paths to the integral of curvature over a spanning surface.

1. **Non-Abelian Stokes theorem.** For a connection $\mathcal A$ with curvature $\mathcal F$, the holonomy around a small loop is approximated by

   $$
   \mathcal U(\Gamma)\approx \mathbb I+\int_\Sigma \mathcal F + O(\lVert\mathcal F\rVert^2),
   $$

   where $\Sigma$ is a surface spanning $\Gamma$. For finite loops, a non-Abelian Stokes theorem expresses $\mathcal U(\Gamma)$ as a path-ordered exponential of the pullback of $\mathcal F$ to $\Sigma$.

2. **Curvature bound.** If $\lVert\mathcal F\rVert\le\delta$ and $\Sigma$ has area $\mathrm{Area}(\Gamma)$, then a Grönwall-type estimate yields

   $$
   \bigl|\mathcal U(\Gamma)-\mathbb I\bigr|
   \le C\,\delta\,\mathrm{Area}(\Gamma).
   $$

3. **Gauge-invariant distance.** The gauge-invariant distance between $U_{\gamma_1}$ and $U_{\gamma_2}$ is controlled by $|\mathcal U(\Gamma)-\mathbb I|$. Triviality of the $\mathbb Z_2$ holonomy removes possible sign flips, leaving only the continuous part controlled by curvature.

The detailed inequalities and gauge-invariance properties are established in Appendix C.

### 4.4 Proof strategy for Theorem 3.5

For Theorem 3.5, one combines:

1. The holographic-type bounds relating generalized entropy $S_{\mathrm{gen}}$ to the logarithm of Hilbert-space dimension in semi-classical gravity.

2. The identification of the effective Hilbert factor $\mathcal H_{\mathcal R}$ in the matrix-universe description with the subspace of $\mathcal H$ localized in $\mathcal R$ and in the relevant frequency window, once appropriate cutoffs are chosen.

This yields $\log\dim\mathcal H_{\mathcal R}\lesssim S_{\mathrm{gen}}$, with constants encoding the choice of cutoffs and the unified time scale. A more refined statement would relate the local density of matrix degrees of freedom to the integrand of the generalized entropy functional.

---

## 5 Model Applications

### 5.1 Continuum quantum field theory on curved space–time

Consider a free scalar or conformal field theory on $(M,g)$. For a small diamond $D_{p,r}$, the modular Hamiltonian of the vacuum state restricted to $D_{p,r}$ can be approximated, in appropriate limits, by an integral of the stress tensor along the boundary, especially for regions whose boundary lies on null surfaces.

The boundary Hilbert space $\mathcal H_{\partial D}$ consists of modes localized on the null boundary, and the scattering matrix $S_D(\omega)$ expresses how these modes are mixed by the dynamics inside $D$. The Wigner–Smith operator $Q_D(\omega)$ encodes the group-delay (time-delay) distribution associated with these modes, and its trace yields the local contribution to the unified time scale $\kappa(\omega)$.

Chains of overlapping diamonds along null directions realize the situation analyzed by Casini–Teste–Torroba, with modular Hamiltonians exhibiting a Markov property and causal gaps measured by conditional mutual information. Nonzero causal gaps arise from curvature, matter excitations and deviations from ideal null configurations.

In this context, the matrix-universe description amounts to organizing all such local diamond scattering matrices into a global Hilbert bundle with connection, where parallel transport along an observer's worldline captures the cumulative scattering and modular evolution experienced by the observer.

### 5.2 Discrete causal sets and tensor networks

In causal set theory, one replaces $(M,g)$ by a locally finite partially ordered set $(C,\preceq)$. Small intervals $I(x,y)=\{z\in C\mid x\preceq z\preceq y\}$ play the role of discrete causal diamonds. To each such interval one can assign a finite-dimensional Hilbert space $\mathcal H_{I(x,y)}$ and a unitary or quantum channel describing the effect of the sub-dynamics between $x$ and $y$.

In the presence of a faithful embedding of the causal set into a Lorentzian manifold, the intervals $I(x,y)$ approximate continuum causal diamonds. The matrix-universe framework then becomes a tensor-network-like structure: each discrete diamond corresponds to a tensor or channel; gluing corresponds to tensor contraction along overlapping regions. Causal consensus becomes the statement that, for homotopic discrete paths with the same endpoints, the resulting contracted tensors are equivalent up to gauge transformations, provided curvature-like invariants associated with cycles are small.

This provides a bridge between causal set quantum gravity and tensor network approaches to holography and quantum error correction, with the unified time scale $\kappa$ playing the role of an emergent discrete proper-time parameter.

### 5.3 Matrix universe and large-$N$ models

Matrix models and large-$N$ gauge theories have long been proposed as nonperturbative descriptions of emergent space–time. In the present framework, the matrix universe is not a specific large-$N$ model but a systematic way of organizing all local scattering and modular information into a Hilbert bundle with connection.

In regimes where the effective Hilbert spaces $\mathcal H_{\mathcal R}$ associated with regions $\mathcal R$ are finite-dimensional and large, one may attempt to approximate the connection $\mathcal A$ by a family of finite-dimensional matrix connections, leading to effective matrix models whose dynamics reproduce the parallel transport of the underlying quantum field theory.

In this setting, Theorem 3.3 describes a universality class of "matrix universes" in which causal consensus is guaranteed in almost flat sectors, while Theorem 3.5 constrains the matrix sizes via generalized entropy bounds.

---

## 6 Engineering Proposals: Causal-Consensus Computing Networks

Although the framework is primarily geometric and operator-theoretic, it suggests several engineering-type proposals in which causal consensus and matrix universes could be emulated or approximated by controllable physical or computational systems.

### 6.1 Analog scattering networks

One may construct a network of microwave cavities, waveguides or photonic circuits whose nodes represent small "lab diamonds". Each node is characterized by a local scattering matrix $S_D(\omega)$ measurable via a vector network analyzer, with group-delay matrices $Q_D(\omega)$ extracted from frequency derivatives.

By wiring these nodes in patterns that mimic causal-diamond complexes (with oriented edges representing allowed signal paths and feedback loops), one obtains an analog matrix universe in which observer paths correspond to specific traversals through the network, and causal consensus can be studied experimentally by comparing group-delay-based unitaries along different routes.

Curvature corresponds to noncommutativity of scattering along loops, and causal gaps to deviations from Markov behavior in cascaded scattering.

### 6.2 Digital matrix-universe simulators

On the computational side, define a finite set of diamonds $\{D_\alpha\}$ and assign to each a finite-dimensional unitary $S_\alpha$ drawn from a parametric family (e.g. random unitary ensembles with constraints). The connection $\mathcal A$ is represented by discrete differences, and the unitaries $U_\gamma$ along observer paths are products of the $S_\alpha$ along the path.

Causal consensus can then be studied as a function of curvature-like invariants (nontrivial products around loops) and Markov defects (conditional mutual information) computed from reduced density matrices in the network. This provides a testbed for theorems such as Theorem 3.3 and for exploring the transition from consensus to disagreement.

### 6.3 Error budgets and consensus thresholds

In practical implementations, observational and experimental errors must be controlled. The bound in Theorem 3.3 suggests that, given an error tolerance $\epsilon$, a curvature bound $\delta$ and loop areas $\mathrm{Area}(\Gamma)$, one can derive thresholds for acceptable disagreement:

$$
C\,\delta\,\mathrm{Area}(\Gamma)\le\epsilon.
$$

Such inequalities can be translated into engineering constraints on network design (e.g. maximum loop length, maximum variation of scattering parameters) to ensure that different observers or routes achieve causal consensus within prescribed tolerances. This aligns the geometric concept of flatness with practical error budgets in distributed sensing or communication networks.

---

## 7 Discussion: Relations, Limitations and Outlook

### 7.1 Relation to causal set and boundary constructions

The present framework is closely related to causal set theory and causal boundary constructions. Causal set approaches emphasize partial orders and local finiteness as fundamental, with continuum manifolds emerging in appropriate limits. Here, the partial order arises from small causal diamonds, while local finiteness is effectively imposed by generalized entropy and information-capacity bounds.

Causal boundary constructions, such as those of Geroch, Kronheimer and Penrose, add "ideal points" to encode asymptotic behavior. In the matrix-universe picture, ideal points correspond to ends of observer paths where scattering cease to change or where $\kappa(\omega)$ reaches limiting behavior, potentially relating causal boundaries to limits of the unified time scale.

The main novelty lies in the use of boundary-time geometry and operator-valued connections to encode both causal order and observer experiences in a single structure $(M,\mathcal H,\mathcal A)$.

### 7.2 Relation to modular theory and QNEC/QFC

Modular theory provides intrinsic time flows determined by state–algebra pairs, while QNEC and quantum focusing conjectures connect entropy variations with null energy. The matrix-universe framework integrates these by:

* Identifying the modular parameter with the unified time scale $\kappa$.

* Interpreting QNEC bounds as inequalities constraining the causal gap density $\mathfrak g$.

* Viewing modular Markov properties as the vanishing of curvature-like invariants along null chains.

Thus, causal consensus becomes a geometrized form of modular consistency across overlapping regions.

### 7.3 Limitations and open questions

Several limitations and open issues remain:

1. **Dynamical law for the connection.** The present framework treats $\mathcal A$ kinematically, as a connection derived from scattering and modular data. A full dynamical theory would specify field equations for $\mathcal A$ and its curvature, possibly linked to Einstein's equations and matter dynamics.

2. **Microscopic definition of small diamonds.** The small-diamond family is assumed but not derived from a more fundamental discrete structure. In causal set or lattice models, one must define and control the continuum limit carefully.

3. **Backreaction and nonunitarity.** In realistic scenarios with dissipation, decoherence and gravitational backreaction, local scattering maps may not be strictly unitary. Extending the connection formalism to completely positive maps and to non-Hermitian generators is necessary.

4. **Topological sectors.** The triviality of $[K]$ was assumed. Incorporating nontrivial $\mathbb Z_2$ sectors and their physical meaning (e.g. fermionic statistics, spin structures or self-referential scattering loops) remains an important extension.

5. **Universality and uniqueness.** Whether all physically reasonable space–times and quantum field theories admit a matrix-universe description with unified time scale and causal consensus properties, or whether this selects a special subclass, is an open question.

### 7.4 Conceptual outlook

Conceptually, the picture that emerges is:

* The *causal manifold* is a nested network of small diamonds with partial orders and entropic arrows.

* The *matrix universe* is a Hilbert bundle with operator-valued connection whose parallel transport encodes how observers stitch local scattering and modular information into a global view.

* *Causal consensus* arises when the connection is almost flat and topologically trivial in the relevant region and energy window, so that different observer paths between the same endpoints yield equivalent unitaries.

The slogan "因果共识 = 巨大矩阵运算" thus acquires a geometric and operator-theoretic meaning: global causal consistency is equivalent to the flatness (up to controlled curvature and holonomy) of an underlying matrix-valued connection defined by local scattering and modular data.

---

## 8 Conclusion

A unified framework for causal consensus has been developed, combining small causal diamonds, boundary-time geometry, modular theory and scattering into a single concept of matrix universe $(M,\mathcal H,\mathcal A)$. In this framework:

* Small causal diamonds and their local partial orders reconstruct the causal manifold.

* Boundary algebras, states and scattering matrices on diamonds define a Hilbert bundle with an operator-valued connection, whose frequency component yields a unified time scale $\kappa$.

* Observers correspond to paths in this bundle; their experienced worlds are encoded by path-ordered unitaries $U_\gamma$.

* Causal consensus between observers is characterized by controlled equivalence of these unitaries for homotopic paths, governed by curvature and $\mathbb Z_2$ holonomy constraints.

* Generalized entropy bounds limit the matrix size associated with finite causal regions, tying information capacity to area and curvature.

This provides a precise reading of the idea that the universe's causal consensus is realized as a gigantic matrix computation. Beyond its conceptual appeal, the framework suggests concrete modeling and engineering directions, from analog scattering networks to digital simulators, and connects naturally with ongoing work in causal sets, modular theory, holography and quantum gravity inequalities.

---

## 9 Acknowledgements, Code Availability

The construction of the matrix-universe framework makes essential use of established results in scattering theory, modular theory, quantum energy inequalities and causal set/causal boundary constructions, as cited in the references. No specific code implementations are required for the theoretical results presented here; numerical explorations of finite-dimensional matrix universes can be carried out with standard linear-algebra and tensor-network libraries in any scientific computing environment.

---

## References

1. M. Sh. Birman, M. G. Kreĭn, "On the theory of wave operators and scattering operators", Dokl. Akad. Nauk SSSR 144 (1962).

2. J. Behrndt, M. Malamud, H. Neidhardt, "Scattering matrices and Weyl functions", J. Funct. Anal. 256 (2009) 2221–2248.

3. H. Casini, E. Teste, G. Torroba, "Modular Hamiltonians on the null plane and the Markov property of the vacuum state", J. Phys. A 50 (2017) 364001.

4. R. Bousso, Z. Fisher, J. Koeller, S. Leichenauer, A. C. Wall, "Proof of the Quantum Null Energy Condition", Phys. Rev. D 93 (2016) 024017.

5. S. Balakrishnan et al., "A general proof of the quantum null energy condition", JHEP 09 (2019) 020.

6. T. Jacobson, "Entanglement Equilibrium and the Einstein Equation", Phys. Rev. Lett. 116 (2016) 201101.

7. R. D. Sorkin, "Causal Sets: Discrete Gravity (Notes for the Valdivia Summer School)", arXiv:gr-qc/0309009.

8. L. Bombelli, J. Lee, D. Meyer, R. D. Sorkin, "Space–time as a causal set", Phys. Rev. Lett. 59 (1987) 521–524.

9. R. Geroch, E. Kronheimer, R. Penrose, "Ideal points in space-time", Proc. Roy. Soc. Lond. A 327 (1972) 545–567.

10. F. Dowker, "Causal sets and discrete space–time", Contemp. Phys. 47 (2006) 1–9.

---

## Appendix A: Causal-Diamond Gluing and Reconstruction

### A.1 From local partial orders to a global causal net

Let $X$ be the set of events of $M$. Let $\{D_\alpha\}_{\alpha\in A}$ be a small-diamond family covering $M$. For each $\alpha$, let $\prec_\alpha$ denote the restriction of the global causal order to $D_\alpha$, assumed known.

Define a relation $R$ on $X$ by

$$
xRy\iff\exists\alpha\in A:\ x,y\in D_\alpha,\ x\prec_\alpha y.
$$

Let $\prec$ be the transitive closure of $R$:

$$
x\prec y\iff\exists n\ge1,\ \exists x_0=x,x_1,\dots,x_n=y\ \text{such that }x_kRx_{k+1}\ \forall k.
$$

**Lemma A.1 (Antisymmetry of $R$).**

Assume Čech causal consistency (Assumption C). If $xRy$ and $yRx$, then $x=y$.

*Proof.* There exist $\alpha,\beta$ such that $x,y\in D_\alpha\cap D_\beta$ and $x\prec_\alpha y$, $y\prec_\beta x$. By Assumption C, there exists a partial order $\prec_{\alpha\beta}$ on $D_{\alpha\beta}:=D_\alpha\cap D_\beta$ that restricts to $\prec_\alpha$ and $\prec_\beta$ on each component. Hence $x\prec_{\alpha\beta} y$ and $y\prec_{\alpha\beta} x$, which by antisymmetry of $\prec_{\alpha\beta}$ implies $x=y$. ∎

**Lemma A.2 (No nontrivial $\prec$-cycles).**

If $x\prec y$ and $y\prec x$ with $x\neq y$, then there is a finite cycle

$$
x=x_0Rx_1R\cdots Rx_n=x
$$

contradicting Lemma A.1.

*Proof.* From $x\prec y$, there exists a chain $x=x_0Rx_1R\cdots Rx_n=y$; similarly, from $y\prec x$, there exists $y=y_0Ry_1R\cdots Ry_m=x$. Concatenating yields a finite $R$-cycle. Each $R$ relation occurs inside some diamond $D_{\alpha_k}$; the intersection of finitely many such diamonds is nonempty by smallness and local convexity. On this intersection, Čech consistency induces a partial order under which the chain yields a cycle, impossible for a partial order. Hence no such $x\neq y$ exist. ∎

**Theorem A.3 (Global partial order).**

The relation $\prec$ is a partial order on $X$ that restricts to $\prec_\alpha$ on each $D_\alpha$.

*Proof.* Reflexivity follows by convention or by augmenting $\prec$ to $\preceq$. Transitivity is by construction. Antisymmetry follows from Lemma A.2. Restriction to $D_\alpha$ coincides with the original $\prec_\alpha$ because any chain of $R$-relations within $D_\alpha$ must coincide with chains in $\prec_\alpha$. ∎

This reconstructs a global causal partial order from local diamond orders.

### A.2 Topological reconstruction via Čech nerve

Since the small diamonds form a good cover (each finite intersection is contractible due to local Minkowskian structure and smallness compared to curvature radius), the Čech nerve $\mathsf K(\mathcal D)$ satisfies the hypotheses of the Čech nerve theorem, yielding:

**Theorem A.4 (Homotopy equivalence).**

The canonical map $M\to|\mathsf K(\mathcal D)|$ is a homotopy equivalence.

In particular, topological invariants such as homotopy and homology groups of $M$ can be recovered from $\mathsf K(\mathcal D)$.

### A.3 Metric reconstruction and entanglement equilibrium

Given the causal order $\prec$ and a volume measure $\mu$ derived from counting diamonds or from entanglement entropy, one can reconstruct the conformal class of $g$ and the volume form. Classical results show that causal structure together with a measure determines the metric up to diffeomorphism under suitable regularity assumptions.

Refinements using entanglement equilibrium assert that demanding stationarity of vacuum entanglement entropy in small geodesic balls at fixed volume yields the Einstein equation. Small causal diamonds can be related to such balls, allowing the reconstruction of curvature from entanglement data along diamond boundaries.

---

## Appendix B: Construction of Hilbert Bundle and Operator Connection

### B.1 Čech data and Hilbert bundle

Let $Y=M\times X^\circ$. The local trivializations $\mathcal H_\alpha\to U_\alpha\times X^\circ$ and unitaries $U_{\alpha\beta}$ define a Čech 1-cocycle with values in the unitary group of a separable Hilbert space.

Standard Hilbert bundle theory asserts:

**Proposition B.1.**

Given local trivializations $\mathcal H_\alpha$ and unitaries $U_{\alpha\beta}$ satisfying $U_{\alpha\beta}U_{\beta\gamma}=U_{\alpha\gamma}$, there exists a Hilbert bundle $\mathcal H\to Y$ and bundle isomorphisms $\Phi_\alpha\colon\mathcal H|_{U_\alpha\times X^\circ}\to\mathcal H_\alpha$ such that

$$
\Phi_\alpha\Phi_\beta^{-1}=U_{\alpha\beta}.
$$

Uniqueness holds up to bundle isomorphism.

### B.2 Global scattering field

On each $U_\alpha\times X^\circ$, define

$$
S_\alpha(\omega;x,\chi)
:=\Phi_\alpha\bigl(S_D(\omega)\bigr)\Phi_\alpha^{-1},
$$

where $D$ is a diamond associated with $U_\alpha$. On overlaps,

$$
S_\alpha=U_{\alpha\beta}S_\beta U_{\alpha\beta}^\dagger
$$

ensures that $\{S_\alpha\}$ glue to a global unitary field $S(\omega;x,\chi)$ on $\mathcal H$.

### B.3 Connection one-form and gauge transformation

Define on each local patch

$$
\mathcal A_\alpha
:=S_\alpha^\dagger\,\mathrm d S_\alpha,
$$

where $\mathrm d$ is the exterior derivative on $Y$. On overlaps,

$$
S_\alpha
=U_{\alpha\beta}S_\beta U_{\alpha\beta}^\dagger
$$

implies

$$
\mathcal A_\alpha
=U_{\alpha\beta}\mathcal A_\beta U_{\alpha\beta}^\dagger
+U_{\alpha\beta}\,\mathrm dU_{\alpha\beta}^\dagger,
$$

so the collection $\{\mathcal A_\alpha\}$ defines a global connection $\mathcal A$ on $\mathcal H$.

Under a gauge transformation $V\colon Y\to\mathcal U(\mathcal H)$, $S\mapsto S^V=VS$ and

$$
\mathcal A\mapsto\mathcal A^V
=V\mathcal A V^\dagger + V\,\mathrm dV^\dagger.
$$

### B.4 Frequency component and unified time scale

Let $\omega$ be a coordinate in $X^\circ$. The component of $\mathcal A$ along $\mathrm d\omega$ is

$$
\mathcal A_\omega
=S^\dagger\partial_\omega S
=i Q(\omega),
$$

giving

$$
Q(\omega)=-i S^\dagger\partial_\omega S.
$$

Its trace yields

$$
\kappa(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega),
$$

realizing the unified time scale.

Under gauge transformations, $Q$ transforms by conjugation, leaving $\kappa$ invariant, as required for a physical time scale.

---

## Appendix C: Causal Consensus and Information-Theoretic Lyapunov Functions

### C.1 Holonomy bounds and causal consensus

Let $\gamma_1,\gamma_2$ be homotopic paths in $\Omega\subset M$, with fixed endpoints. Let $\Gamma=\gamma_1\circ\gamma_2^{-1}$ be the resulting loop, and let $\Sigma\subset\Omega$ be a surface with $\partial\Sigma=\Gamma$.

The holonomy of $\mathcal A$ around $\Gamma$ is

$$
\mathcal U(\Gamma)
=\mathcal P\exp\oint_\Gamma \mathcal A.
$$

A non-Abelian Stokes theorem yields

$$
\mathcal U(\Gamma)
=\mathcal P_\Sigma\exp\iint_\Sigma \Phi^\ast\mathcal F,
$$

where $\Phi$ is a parameterization of $\Sigma$ and $\mathcal P_\Sigma$ denotes surface ordering.

If $\lVert\mathcal F\rVert\le\delta$ in operator norm on $\Omega\times I$, then one obtains an estimate

$$
\bigl|\mathcal U(\Gamma)-\mathbb I\bigr|
\le C\,\delta\,\mathrm{Area}(\Sigma)
$$

for some constant $C$ depending on the dimension and the precise definition of the operator norm and surface ordering.

Since $U_{\gamma_1}U_{\gamma_2}^{-1}=\mathcal U(\Gamma)$, this implies

$$
d\bigl(U_{\gamma_1},U_{\gamma_2}\bigr)
\le C\,\delta\,\mathrm{Area}(\Sigma),
$$

establishing the bound in Theorem 3.3.

The absence of nontrivial $\mathbb Z_2$ holonomy ensures that $\mathcal U(\Gamma)$ is close to $\mathbb I$ and not to $-\mathbb I$, so that consensus is not spoiled by discrete sign flips.

### C.2 State consensus and information Lyapunov functions

Consider a network of observers $\{O_i\}$ exchanging information and updating their states $\omega_i^{(t)}$ at discrete times $t$. A generic update rule can be written as

$$
\omega_i^{(t+1)}
=\sum_j w_{ij} T_{ij}(\omega_j^{(t)}),
$$

where $w_{ij}$ is a stochastic matrix and $T_{ij}$ are completely positive trace-preserving maps (communication channels and local processing). Assume there exists a unique fixed point $\omega_\ast$ and a stationary left eigenvector $\lambda$ of $W=(w_{ij})$.

Define an information-theoretic Lyapunov function

$$
\Phi^{(t)}
:=\sum_i\lambda_i D\bigl(\omega_i^{(t)}\Vert\omega_\ast\bigr),
$$

where $D$ is relative entropy. Monotonicity of relative entropy under CPTP maps implies

$$
\Phi^{(t+1)}\le\Phi^{(t)},
$$

with strict inequality unless all $\omega_i^{(t)}$ are equal to $\omega_\ast$.

Thus the network converges to a consensus state $\omega_\ast$, provided appropriate primitivity conditions hold for $W$ and $T_{ij}$.

In the matrix-universe setting, the unitaries $U_\gamma$ along observer paths act on the states $\omega_i^{(t)}$. When curvature is small and causal gaps are negligible, different paths from a common initial state to a common end region yield similar unitaries, ensuring that the consensus state is independent of the specific path chosen, up to small errors controlled by curvature and loop areas.

This couples the geometric notion of causal consensus (Theorem 3.3) with information-theoretic consensus in observer networks, providing a unified picture in which causality, matrices and information flow are tightly interwoven.

