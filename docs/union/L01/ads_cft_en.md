# AdS/CFT Bridge (Canonical; Full Forms)

## Dependencies (Upward)
- L00 · ../L00/hilbert_foundations_en.md
- L00 · ../L00/zeta_foundations_en.md

## GKPW Relation (canonical)
$$
Z_{\mathrm{CFT}}[J] = Z_{\mathrm{gravity}}\big[ \phi\big|_{\partial} = J \big]
$$
with
$$
Z_{\mathrm{CFT}}[J] = \left\langle \exp\!\left( \int d^{d}x\, J(x)\, \mathcal{O}(x) \right) \right\rangle_{\mathrm{CFT}},
$$
$$
\langle \mathcal{O}(x_{1})\cdots\mathcal{O}(x_{n}) \rangle = \left. \frac{\delta^{n} S_{\mathrm{on\text{-}shell}}}{\delta J(x_{1})\cdots\delta J(x_{n})} \right|_{J=0}.
$$

## RT/HRT Entanglement Entropy (canonical)
$$
S_{A} = \frac{\operatorname{Area}(\gamma_{A})}{4\,G_{N}},
$$
where $\gamma_{A}$ is the (covariant) extremal surface homologous to region $A$ on the boundary.

## AdS Metric (Poincaré patch; canonical)
$$
\,ds^{2} = \frac{L^{2}}{z^{2}}\,\big( dz^{2} + \eta_{\mu\nu}\,dx^{\mu}\,dx^{\nu} \big),\qquad z>0.
$$

## Fefferman–Graham Expansion (canonical form)
$$
\,ds^{2} = \frac{L^{2}}{z^{2}}\,\Big( dz^{2} + g_{ij}(x,z)\,dx^{i}\,dx^{j} \Big),\qquad g_{ij}(x,z) = g_{ij}^{(0)}(x) + z^{2}\,g_{ij}^{(2)}(x) + \cdots.
$$

## Dense Summary (non‑canonical)
- We record canonical AdS/CFT relations (GKPW, RT/HRT, metric, FG) as‑is, to be referenced by equivalence maps without modification.
- The boundary symmetry encoded by $\xi(s)=\xi(1-s)$ (L00) is used as an analogy point; explicit‑formula boundary data provide spectral anchors.

## Proof chain bullets (from original sources; upward only)
- GKPW and RT/HRT must cite the source documents under `docs/zeta/zeta-ads-cft-correspondence*.md` (and physics references admitted by the project), keeping formulas in full.
- AdS metric and FG expansion in Poincaré patch must cite canonical AdS references and the admitted project pages (e.g., `docs/zeta/zeta-ads-cft-correspondence.md`).
- Any linkage to boundary symmetry must cite the completed functional equation $\xi(s)=\xi(1-s)$ recorded in L00 (`docs/union/L00/zeta_foundations_en.md`).
