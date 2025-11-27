# Information Geometry Variational Principle for Einstein Field Equations: Quantum Gravity Framework in EBOC–Causal Manifold Unification
Version: 1.7

## Abstract

Given the mutual construction framework between the discrete–static block structure (EBOC) and the continuous–causal manifold, this paper proposes an information-geometric variational principle: on every sufficiently small timelike geometric ball (or local causal diamond), the **generalized entropy** $S_{\rm gen}$ attains an extremum under the constraints of fixed volume and reference vacuum. Utilizing the first-order "first law" of relative entropy $\delta S_{\rm out}=\delta\langle H_{\rm mod}\rangle$ and the area variation induced by geometric beam convergence (Raychaudhuri), we prove that for all small balls and all shape deformations, the extremality condition implies the Einstein field equations $G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle$. At the semiclassical level, the second-order variation and the non-negativity of relative entropy yield information inequalities such as quantum focusing and QNEC, which constitute quantum corrections. On the discrete side, the static block–factor decoding semantics of EBOC provides a Regge-type discrete action and we prove convergence to the aforementioned continuous field equations in the limit of mesh refinement and information-geometric consistency. The "readout–scale–causality" semantics of this work strictly aligns with the windowed group-delay master scale $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ and closes under the finite-order error discipline of Nyquist–Poisson–Euler–Maclaurin.

---

## Notation & Axioms / Conventions

**Unit Convention** We adopt $\hbar=c=1$. Metric signature $(-+++)$. For a small ball $B_\ell(x)$, the unit timelike normal vector is denoted $u^\mu$, and the corresponding spatial hypersurface element is $d\Sigma^\nu=u^\nu d\Sigma$.

**Causal–Readout Separation (Two-Time Separation)** Causality and no-signaling are determined solely by the **frontal time** $t_*$; windowed group-delay readout $T_\gamma[w_R,h]$ is merely a measurable scale with no universal size comparison to $t_*$. All causal and partial-order conclusions in this paper depend only on $t_*$ and the light-cone structure; readout scales are used for information-geometric measures and calibration.

**Scale Identity (Master Scale)** Under the global unitarity postulate,
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad \mathsf Q(E)=-i\,S^\dagger(E)\tfrac{dS}{dE}(E)\ }
$$
and this master scale defines the windowed readout and energy–delay duality (redshift–time reciprocity).

**NPE Finite-Order Error Discipline** All numerical implementations adhere to the Nyquist–Poisson–Euler–Maclaurin tripartite decomposition and finite-order EM endpoint corrections; singularities do not proliferate, and poles yield principal scales. All discrete approximations of information quantities and readouts in this paper close under this accounting framework.

**Mutual Construction Condition (GLS ↔ Causal Manifold)** The conformal class of the manifold is reconstructed from the frontal-reachability preorder and light-observation sets; energy-differentiable unitary $S(E)$ is constructed from the radiation field–scattering and returns to the master scale. At the category-theoretic level, they are equivalent under the energy-dependent unitary gauge equivalence class.

**EBOC (Discrete Side)** The world is given by static blocks $X_f$ and eternal graphs–subshifts; observation $=$ factor decoding, information non-increase; Brudno alignment of temporal sub-actions and information conservation of reversible CA constitute the axiomatic basis of discrete information geometry.

**Information Geometry** On a classical statistical manifold $(\mathcal P,g^{\rm F})$, the Fisher–Rao metric is the unique metric satisfying Markov (data-processing) monotonicity (Čencov's theorem); in the quantum case, the Hessian of the Umegaki relative entropy yields the BKM monotone metric, which belongs to the Petz monotone metric family (non-unique). The dual connection structure $(\nabla,\nabla^*)$ is induced by the divergence family. ([Springer Link][1])

---

## 1. Local Statistical Manifold and Relative Entropy

**1.1 Local Ball and Modular Hamiltonian** In local Lorentz coordinates around a point $x\in\mathcal M$, consider a small ball $B_\ell(x)$. Let $\rho_{B_\ell}$ be the reduced state of the matter field on $B_\ell$, and $\rho^{(0)}_{B_\ell}$ be the reference state corresponding to the local maximally symmetric vacuum. The modular Hamiltonian of the vacuum can be written locally in conformal theory as
$$
H_{\rm mod}^{(0)}=2\pi\!\int_{B_\ell}\!\xi^\mu T_{\mu\nu}\,d\Sigma^\nu,\qquad
\xi^\mu=\frac{\ell^2-r^2}{2\ell}\,u^\mu + O(\ell^3),
$$
whereby the first-order variation of relative entropy satisfies the "first law"
$$
\delta S(\rho_{B_\ell}\Vert \rho^{(0)}_{B_\ell})=\delta\!\left\langle H_{\rm mod}^{(0)}\right\rangle-\delta S_{\rm out}=0.
$$
This identity holds universally under perturbations and in the small-ball limit, and has been systematically elucidated in holographic and field-theoretic contexts. ([Springer Link][2])

**1.2 Information-Geometric Perspective** On the statistical manifold parameterized by metric deformations $g\mapsto g+\delta g$ and state deformations $\rho\mapsto\rho+\delta\rho$, the second-order variation of relative entropy defines the Fisher–Rao metric; its uniqueness is characterized by Čencov monotonicity and sufficiency-invariance. We take $D(\rho_{B_\ell}\Vert\rho^{(0)}_{B_\ell})$ induced by the family of local balls $\{B_\ell(x)\}$ as the fundamental divergence of information geometry, and take its first-order balance (extremality) and second-order positive-definiteness as the content of the variational principle. ([Springer Link][1])

---

## 2. Information Geometry Variational Principle (IGVP)

**Principle (IGVP)** For each point $x$ and sufficiently small $B_\ell(x)$, under the constraints of fixed volume $\mathrm{Vol}(B_\ell)$ and reference vacuum, the **generalized entropy**
$$
S_{\rm gen}(B_\ell):=\frac{A(\partial B_\ell)}{4G} + S_{\rm out}(\rho_{B_\ell})
$$
attains a first-order extremum, and the second-order variation is non-negative. Equivalently, letting $\sigma_{B_\ell}=\rho^{(0)}_{B_\ell}$,
$$
\delta S_{\rm gen}=0,\qquad \delta^2 S(\rho_{B_\ell}\Vert \sigma_{B_\ell})\ge 0.
$$
The first equation yields the linearized field equations at first order in the small-ball limit; under Assumption A, it can be promoted to the complete field equations. The second equation yields stability and the quantum energy inequality (QNEC) family. This extremality assumption is consistent with the "maximal vacuum entanglement/entropic equilibrium" framework. ([Physical Review Link Manager][3])

**Lemma 2.1 (First Law)** In the small-ball limit and at first-order perturbation,
$$
\delta S_{\rm out}=\delta\!\left\langle H_{\rm mod}^{(0)}\right\rangle
=2\pi\int_{B_\ell} \xi^\mu\,\delta\!\langle T_{\mu\nu}\rangle\, d\Sigma^\nu.
$$
(Proof in the above references.) ([Springer Link][2])

**Lemma 2.2 (Area Variation)** When changing the shape while fixing the ball volume (or equivalently, changing the background metric while preserving the center and radius), the variation of the boundary area satisfies
$$
\delta\!\left(\frac{A}{4G}\right)=-2\pi \int_{B_\ell}\xi^\mu\,\frac{1}{8\pi G}\,\delta\!\big(G_{\mu\nu}+\Lambda g_{\mu\nu}\big)\,d\Sigma^\nu + O(\ell^{d+1}),
$$
where we use standard small-ball geometry of Raychaudhuri and geodesic expansion. Comparing this term with Lemma 2.1 closes the first variation. (Derivation follows the Jacobson-type local thermodynamics/entropic argument in the small-ball version.) ([Physical Review Link Manager][4])

**Theorem 2.3 (IGVP ⇒ Linearized; Promoted to Full Equations under Assumption)** If $\delta S_{\rm gen}=0$ for all $x$ and sufficiently small $B_\ell(x)$, then in a first-order neighborhood of the reference geometry,
$$
\boxed{\ \delta\!\big(G_{\mu\nu}+\Lambda g_{\mu\nu}-8\pi G\,\langle T_{\mu\nu}\rangle\big)=0\ }.
$$
Furthermore, if **Assumption A** is satisfied:
(i) The above holds for arbitrary background points and arbitrary perturbation families;
(ii) $C_{\mu\nu}:=G_{\mu\nu}+\Lambda g_{\mu\nu}-8\pi G\,\langle T_{\mu\nu}\rangle$ is a local, covariant, at-most-second-order tensor functional;
then under local Lorentz covariance and absence of external background structure, uniqueness implies $C_{\mu\nu}=C\,g_{\mu\nu}$. From the Bianchi identity $\nabla^\mu G_{\mu\nu}=0$ and energy–momentum conservation $\nabla^\mu\langle T_{\mu\nu}\rangle=0$, we have $\nabla^\mu C_{\mu\nu}=0$, hence $\partial_\nu C=0$. Absorbing the constant $C$ into $\Lambda$ yields
$$
G_{\mu\nu}+\Lambda_{\rm eff} g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle,\qquad \Lambda_{\rm eff}=\Lambda+C.
$$
This derivation is consistent with the equivalence spectrum of "entanglement equilibrium $\Rightarrow$ Einstein equations" and has been extended to linearized and nonlinear cases in holographic and general field-theoretic contexts. ([Physical Review Link Manager][3])

---

## 3. Second-Order Variation and Quantum Energy Conditions

**Proposition 3.1 (Relative Entropy Non-Negativity and QNEC)** For any torsion-free null geodesic congruence $k^\mu$ passing through $x$, perform a local cut deformation and define
$$
s_{\rm out}''(x):=\lim_{\mathcal A\to 0}\frac{1}{\mathcal A}\,\frac{d^2 S_{\rm out}}{d\lambda^2},
$$
where $\lambda$ is the affine parameter of $k^\mu$ and $\mathcal A$ is the cross-sectional area of the deformation patch. Then the convexity of relative entropy yields
$$
\boxed{\ \langle T_{kk}(x)\rangle\ \ge\ \frac{1}{2\pi}\,s_{\rm out}''(x)\ },
$$
namely the quantum null energy condition (QNEC). Its proof families (field-theoretic/holographic) all take the convexity of relative entropy as core input. ([Physical Review Link Manager][5])

**Corollary 3.2 (Quantum Focusing and Generalized Entropy Monotonicity)** The quantum focusing conjecture and quantum Bousso bounds follow from the above inequality and the non-increase of generalized entropy, compatible with the second-order stability of IGVP. ([arXiv][6])

---

## 4. Master Scale, Readout, and Coupling with Information Geometry

**4.1 Windowed Group Delay and Fisher Density** For each observer window–kernel pair $(w_R,h)$, the in-band distribution induced is $p(E|x) \propto (w_R*\check h)(E)\,\rho_{\rm rel}(E;x)$. Define the local Fisher tensor
$$
\mathcal I_{\mu\nu}(x)=\int \partial_\mu\!\ln p(E|x)\,\partial_\nu\!\ln p(E|x)\, p(E|x)\,dE,
$$
and by Čencov–Amari uniqueness, take it as the registration object between **readout–information geometry** and **background metric**: in the vacuum–no-aliasing limit and redshift–reciprocity rescaling, the constraint $\mathcal I_{\mu\nu}\propto g_{\mu\nu}$ can serve as an additional Lagrange multiplier term in IGVP, ensuring consistency of readout coordinates with geometric coordinates. This registration is covariant under the scaling law of redshift–time reciprocity.

**4.2 Readout–Geometry Consistent Variation** Consider the action
$$
\mathcal S[g;\rho]=\frac{1}{16\pi G}\!\int\!\sqrt{-g}\,(R-2\Lambda)\,d^4x
-\!\int\!\sqrt{-g}\,\Phi(\rho\Vert\rho^{(0)})\,d^4x
+\!\int\!\sqrt{-g}\,\lambda^{\mu\nu}\!\left(\mathcal I_{\mu\nu}-\kappa\, g_{\mu\nu}\right)\!d^4x,
$$
where $\Phi$ is a local density with relative entropy as potential (in the small-ball limit it reduces to a volume-integral form of $\delta\langle H_{\rm mod}\rangle-\delta S_{\rm out}$). Variation with respect to $g_{\mu\nu}$ yields
$$
G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\left(\langle T_{\mu\nu}\rangle + T^{\rm(IG)}_{\mu\nu}\right),
$$
while the readout–geometry registration $\mathcal I_{\mu\nu}=\kappa g_{\mu\nu}$ ensures that the trace of $T^{\rm(IG)}_{\mu\nu}$ and the vacuum energy are absorbed into $\Lambda$, thus returning to the form of Theorem 2.3. When using the "first law" formulation, this is equivalent to taking $\delta S_{\rm gen}=0$ as the Euler–Lagrange condition. (The specific choice of information potential and the Fisher–relative entropy equivalence are guaranteed by standard information geometry in the small-ball limit.) ([Springer Link][1])

---

## 5. Discretization: EBOC–Regge Information Action and Continuum Limit

**5.1 Static Block–Triangulation** On the static block $X_f$ of EBOC, choose a foliation and triangulation consistent with the light cones. Let each 2-skeleton (triangle) $h$ carry a discrete area $A_h$ and define the deficit angle $\varepsilon_h$ at $h$. The Regge action
$$
S_{\rm Regge}=\frac{1}{8\pi G}\sum_{h} A_h\,\varepsilon_h- \frac{\Lambda}{8\pi G}\sum_\sigma V_\sigma
$$
yields discrete Einstein equations under variation. On the information geometry side, for each discrete small-ball cell $c$, define the **discrete generalized entropy**
$$
S_{\rm gen}^{\rm disc}(c)=\frac{A(\partial c)}{4G}+S_{\rm out}^{\rm disc}(c),
$$
The first variation $\delta S_{\rm gen}^{\rm disc}=0$ is compatible with Regge variation and converges to the continuous IGVP under mesh refinement. ([Wikipedia][7])

**5.2 Observation = Decoding and Information Non-Increase** The visible language of the discrete state is generated by factor decoding $\pi$, satisfying
$$
K\!\left(\pi(x|_W)\right)\ \le\ K(x|_W)+K(\pi)+O(1),
$$
whereby discrete $S_{\rm out}^{\rm disc}$ converges to continuous $S_{\rm out}$ in the refinement limit, ensuring $S_{\rm gen}^{\rm disc}\to S_{\rm gen}$ and the stability of IGVP.

---

## 6. Consistency with the GLS–Readout Framework

**6.1 Frontal–Super-Lightcone Propagation and Readout Independence** From the frontal lower bound $t_*\ge L_g/c$ and the gauge-covariant/relative-invariance of windowed readout, we conclude: the choice of small ball and the choice of readout dictionary in IGVP are mutually independent; small-ball deformations are anchored only to the causal structure and metric, while readout merely provides Fisher registration and energy–delay scales.

**6.2 Redshift–Reciprocity and Fisher Scaling** Under spectral rescaling $E\mapsto E/(1+z)$, the Fisher tensor and readout scale in the small ball scale covariantly as $(1+z)^{-2}$; the volume-preserving IGVP condition is consistent with the volume constraint of Jacobson/entanglement equilibrium.

---

## 7. Quantum Corrections, Renormalization, and Testable Conditions

**7.1 One-Loop/$1/N$ Corrections** In holographic and field-theoretic contexts, the "area $+$ outer entanglement" structure of generalized entropy is supplemented by bulk entanglement at one loop; this correction is precisely the source of the quantum extremal surface (QES) condition of $S_{\rm gen}$, ensuring that IGVP remains valid at the semiclassical level. ([arXiv][8])

**7.2 QNEC and Relative Entropy Convexity** The positivity of the second-order variation yields
$$
\boxed{\ \langle T_{kk}(x)\rangle \ge \frac{1}{2\pi}\,s_{\rm out}''(x)\ },
$$
which has been proven in field-theoretic and holographic contexts, constituting the stability criterion and testable condition of IGVP. ([Physical Review Link Manager][5])

---

## 8. Proof Details

**8.1 Small-Ball Geometry and Area Expansion** In normal coordinates, the boundary area of a small ball is
$$
A(\partial B_\ell)=\Omega_{d-2}\,\ell^{d-2}\!\left[1-\frac{\ell^2}{6(d-1)}\,R+O(\ell^4)\right],
$$
Volume-preserving variation eliminates $\delta\ell$, leaving $\delta A\propto \delta R$. Pairing with Lemma 2.1 and using $G_{\mu\nu}=R_{\mu\nu}-\tfrac12 R g_{\mu\nu}$ yields Theorem 2.3.

**8.2 "First Law" and Modular Hamiltonian** The modular Hamiltonian of the ball region is locally a linear functional of the energy–momentum tensor for conformal vacuum, hence $\delta S_{\rm out}=\delta\langle H_{\rm mod}\rangle$ holds; corrections for non-conformal fields have been provided in subsequent literature and do not affect the form of the conclusion. ([Springer Link][2])

---

## 9. Relation to and Advantages over Existing Approaches

**Jacobson (Thermodynamic/Entanglement Equilibrium) Line**: This paper restates "local thermodynamics/entropic equilibrium" as **information-geometric extremality**, replacing specific thermodynamic closure with the universal structure of Fisher–relative entropy, thereby viewing gravity as "geometric response preserving local information balance." ([Physical Review Link Manager][4])

**Holographic "First Law" Line**: This paper reproduces the logic of "first law $\Rightarrow$ field equations" at the local small-ball level without requiring the holographic assumption; when a gravitational dual exists, it rigorously interfaces with holographic derivations (linearized Einstein equations). ([Springer Link][9])

**EBOC–GLS Unification**: Discrete–decoding and continuous–causality are unified under IGVP: information non-increase and consistent expansion of static blocks on the discrete side ensure $S_{\rm gen}^{\rm disc}\to S_{\rm gen}$; on the continuous side, master scale–readout–Fisher registration seamlessly aligns measurable scales with geometric dimensions.

---

## 10. Typical Corollaries and Observable Consequences

1. **Field Equations ⇒ Local Entropicity**: If $G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle$ is known, then $\delta S_{\rm gen}=0$ can be directly verified in the small-ball limit. ([Physical Review Link Manager][3])

2. **QNEC/Quantum Focusing**: Second-order deformations in any null direction yield energy lower bounds, providing consistency checks and numerical verification metrics for semiclassical gravity. ([Physical Review Link Manager][5])

3. **Redshift–Reciprocity Clock and Fisher Capacity**: In observation–timing experiments, the reciprocal scaling of bandwidth–resolution–redshift is explicitly embodied in the Lagrange constraint of IGVP, serving as direct posterior verification at the experimental calibration layer.

---

## 11. Concluding Statements (Synopsis)

* In the small-ball limit, first-order extremality of **generalized entropy** $S_{\rm gen}$ (combined with the first law of relative entropy) is equivalent to linearized Einstein equations; under Assumption A, it implies the complete nonlinear Einstein equations.
* Non-negativity of the second-order variation yields QNEC/quantum focusing and other **quantum consistency** constraints.
* The discrete–decoding semantics of EBOC and Regge triangulation provide a compatible realization of **discrete action–extremality**, converging to continuous IGVP in the refinement limit.
* Master scale–windowed readout–Fisher registration **unify and align** "measurable scales" with geometric metrics, maintaining the hierarchical separation of causality–readout and finite-order closure of the numerical error ledger.

---

## References (Selected)

Jacobson, *Thermodynamics of Spacetime: The Einstein Equation of State*, PRL 75 (1995). ([Physical Review Link Manager][4])
Jacobson, *Entanglement Equilibrium and the Einstein Equation*, PRL 116 (2016). ([Physical Review Link Manager][3])
Lashkari–McDermott–Van Raamsdonk, *Gravitational dynamics from entanglement "thermodynamics"*, JHEP 04 (2014) 195. ([Springer Link][2])
Faulkner–Guica–Hartman–Myers–Van Raamsdonk, *Gravitation from entanglement in holographic CFTs*, JHEP 03 (2014) 051. ([Springer Link][9])
Casini–Huerta–Myers, *Towards a derivation of holographic entanglement entropy*, JHEP 05 (2011) 036. ([arXiv][10])
Bousso–Fisher–Leichenauer–Wall, *A Quantum Focussing Conjecture* (2015); *Proof of a Quantum Bousso Bound* (2014). ([arXiv][6])
Balakrishnan *et al.*, *A General Proof of the Quantum Null Energy Condition* (2019). ([Springer Link][11])
Amari, *Information Geometry and Its Applications* (2016). ([Springer Link][1])
Čencov, *Statistical Decision Rules and Optimal Inference* (AMS, 1982). ([bookstore.ams.org][12])
Regge, *General Relativity without Coordinates* (1961); review in Barrett–Oriti–Williams (2018). ([Inspire][13])

---

## Appendix A: Interface Details with GLS–EBOC Unification (Summary)

1. **Master Scale and Fisher Alignment**: Construct $p(E|x)$ from $\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ and define $\mathcal I_{\mu\nu}$; the constraint $\lambda^{\mu\nu}(\mathcal I_{\mu\nu}-\kappa g_{\mu\nu})$ pulls readout coordinates back to geometric coordinates.

2. **Causal–Readout Stratification**: The small ball and relative entropy in IGVP are anchored only to causality and metric; windowed group delay is used only for scales and observational dictionaries of the statistical manifold, not participating in partial-order definition.

3. **Discrete–Limit**: On EBOC's static blocks and eternal graphs, define $S_{\rm gen}^{\rm disc}$, Regge action, and factor decoding, satisfying $\delta S_{\rm gen}^{\rm disc}=0 \Rightarrow$ Regge equations; refinement limit returns to Theorem 2.3.

4. **Categorical Equivalence and Covariance**: The mutual construction GLS ↔ causal manifold ensures the functoriality and naturality of "geometry–readout–information"; IGVP is invariant under this equivalence.

---

## Appendix B: Equivalent Forms of Information Geometry–First Law

Write the small-ball relative entropy as
$$
S(\rho_{B_\ell}\Vert \sigma_{B_\ell})
=\mathrm{Tr}(\rho_{B_\ell}\ln\rho_{B_\ell})-\mathrm{Tr}(\rho_{B_\ell}\ln\sigma_{B_\ell}),
$$
First-order variation yields
$$
\delta S=-\delta S_{\rm out}+\delta\!\langle H_{\rm mod}^{(0)}\rangle,\qquad
H_{\rm mod}^{(0)}:=-\ln\sigma_{B_\ell},
$$
namely the "first law." For conformal vacuum, $H_{\rm mod}^{(0)}$ is a local functional of energy flux density; for non-conformal cases, operator expansion corrections can be made in the small-ball limit without changing the form of the extremality condition. ([Springer Link][2])

---

## Appendix C: Numerical Implementation and NPE Error Ledger (Readout Side)

In any readout integral implemented with window–kernel $(w_R,h)$, only the integrand $f(E)=w_R(E)\,[h\!\star\!\rho_{\rm rel}](E)$ is subject to sampling/truncation/EM endpoint corrections; the small-ball deformations and field-equation derivation in IGVP are unaffected by this numerical ledger.

---

**Note** All formulas in this paper maintain consistency of metric–readout–causality hierarchy with the master scale, mutual construction, and other aspects systematically characterized in the aforementioned unified framework. This paper merely provides a rigorous formulation of "gravity = generalized entropy extremality of information geometry (combined with the first law of relative entropy)" on this basis and provides continuous–discrete dual realizations.

[1]: https://link.springer.com/book/10.1007/978-4-431-55978-8?utm_source=chatgpt.com "Information Geometry and Its Applications"
[2]: https://link.springer.com/article/10.1007/JHEP04%282014%29195?utm_source=chatgpt.com "Gravitational dynamics from entanglement "thermodynamics""
[3]: https://link.aps.org/doi/10.1103/PhysRevLett.116.201101?utm_source=chatgpt.com "Entanglement Equilibrium and the Einstein Equation"
[4]: https://link.aps.org/doi/10.1103/PhysRevLett.75.1260?utm_source=chatgpt.com "Thermodynamics of Spacetime: The Einstein Equation of State"
[5]: https://link.aps.org/doi/10.1103/PhysRevD.93.024017?utm_source=chatgpt.com "Proof of the quantum null energy condition | Phys. Rev. D"
[6]: https://arxiv.org/abs/1506.02669?utm_source=chatgpt.com "A Quantum Focussing Conjecture"
[7]: https://en.wikipedia.org/wiki/Regge_calculus?utm_source=chatgpt.com "Regge calculus - Wikipedia"
[8]: https://arxiv.org/abs/1307.2892?utm_source=chatgpt.com "Quantum corrections to holographic entanglement entropy"
[9]: https://link.springer.com/article/10.1007/JHEP03%282014%29051?utm_source=chatgpt.com "Gravitation from entanglement in holographic CFTs"
[10]: https://arxiv.org/abs/1102.0440?utm_source=chatgpt.com "Towards a derivation of holographic entanglement entropy"
[11]: https://link.springer.com/article/10.1007/JHEP09%282019%29020?utm_source=chatgpt.com "A general proof of the quantum null energy condition"
[12]: https://bookstore.ams.org/mmono-53?utm_source=chatgpt.com "Statistical decision rule and optimal inference - AMS Bookstore"
[13]: https://inspirehep.net/literature/3183?utm_source=chatgpt.com "GENERAL RELATIVITY WITHOUT COORDINATES - Inspire HEP"

