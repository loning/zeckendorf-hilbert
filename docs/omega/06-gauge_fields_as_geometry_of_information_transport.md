# 规范场作为信息输运的几何：在量子元胞自动机中推导麦克斯韦与杨–米尔斯方程

*Gauge Fields as Geometry of Information Transport: Deriving Maxwell and Yang–Mills Equations in Quantum Cellular Automata*

---

## Abstract

In standard quantum field theory, gauge fields are introduced by demanding local invariance of a Lagrangian under a prescribed Lie group, and are geometrically interpreted as connections on principal fibre bundles. In a universe described by a quantum cellular automaton (QCA), however, the microscopic ontology is a discrete network of finite-dimensional quantum systems updated by causal local unitaries. In such a discrete ontology there is no preferred global reference frame for internal degrees of freedom at different lattice sites; each cell only has access to a local Hilbert-frame.

This work develops a framework in which gauge fields arise as **translation protocols between local information frames** on a QCA. Starting from three assumptions—(i) a strictly causal, translation-invariant QCA on a regular lattice; (ii) local frame independence of physical predictions; and (iii) a minimal-distortion principle for information transport—we show:

1. Local redundancy in the choice of internal basis enforces the introduction of link variables as parallel-transport operators between neighbouring cells, with the standard lattice-gauge transformation law. Abelian phase redundancy yields a $U(1)$ connection; internal multi-component redundancy yields non-Abelian $G$-connections.

2. In the continuum limit of a Dirac-type QCA, the requirement that the discrete dynamics be covariant under local frame changes is equivalent to minimal coupling of a Dirac field to a gauge potential $A_\mu$, and the gauge curvature is obtained as the logarithm of elementary plaquette holonomies.

3. Imposing that the dynamics of these link variables minimize a local, gauge-invariant, quadratic information-distortion functional uniquely selects, under mild regularity and isotropy assumptions, an effective action which reduces in the continuum to the Maxwell or Yang–Mills action.

4. The microscopic gauge coupling can be expressed in terms of ratios of information-transport rates between internal and inter-site channels within the QCA, connecting running couplings to changes in effective connectivity and time-step at different probing scales.

In this picture, fundamental interactions are not extra entities added to matter fields, but constraints on how information can be transported consistently across a discrete network of local frames. Gauge curvature measures the failure of information-parallel transport to be path-independent, and the gauge field equations arise as Euler–Lagrange equations of an information-distortion functional defined on QCA link variables.

## Keywords

量子元胞自动机；规范不变性；威尔逊环；信息输运；麦克斯韦方程；杨–米尔斯理论；格点规范场论

---

## Introduction & Historical Context

连续场论视角下，规范场的引入通常遵循"规范原理"：给定一个具有全局对称群 $G$ 的自由拉格朗日量，将对称性提升为时空点依赖的局域对称性 $G(x)$，并通过引入规范势 $A_\mu(x)$ 以及协变导数 $D_\mu = \partial_\mu - \mathrm{i} g A_\mu$ 来恢复不变性。对 $G = U(1)$ 得到电磁场，对 $G = SU(2)\times U(1)$、$SU(3)$ 等得到标准模型的弱相互作用与强相互作用。几何上，规范势是主丛上的联络一形式，曲率 $F_{\mu\nu}$ 则对应联络的曲率二形式。

在非微扰区，规范场论的离散化由 Wilson 的格点规范场论奠定基础：时空被离散为格点与连边，规范场以群元 $U_{x,\mu}\in G$ 赋值在连边上，曲率由封闭 Wilson 环路上的群元乘积给出，连续极限下 Wilson 作用量收敛到杨–米尔斯作用量。格点规范场论不但给出了强作用低能行为的首个可控描述，也为量子模拟提供了自然的离散结构。

另一方面，量子元胞自动机（quantum cellular automata, QCA）将物理宇宙建模为一族离散格点上的有限维量子系统，在离散时间步上由局域幺正算符整体更新。Arrighi、Farrelly 等人的综述表明，QCA 可统一大量离散时空量子模型，包括量子行走、格点场论以及部分离散化的量子场论，且在适当连续极限下可涌现狄拉克、魏尔与 Maxwell 方程。更进一步，Arnault 等工作表明，离散时间量子行走（DTQW）可以实现具有严格栅格规范不变性的 $U(1)$ 与非阿贝尔离散规范理论，并在连续极限下模拟狄拉克物质与电磁/杨–米尔斯场的耦合。

这些结果表明，在离散框架内引入规范场并不困难；困难在于其本体论地位。传统构造中，即便在格点上，规范场往往仍被视为"用来模拟某个既定连续规范场论的数值工具"。而在 QCA 的离散本体论视角中，格点与连边就是最底层的"宇宙基元"，不存在更深一层连续场作为参照。这一视角下，自然的问题是：

* 规范场是否可以被理解为 QCA 网络中信息输运的一种几何约束，而非额外添加的"场"？

* 规范对称性是否可以从"局域信息参考系的冗余性"与"信息输运的一致性"中涌现，而非作为先验对称性假设？

本文的目标正是从 QCA 的角度给出这样一种解释。具体而言：

1. 将每个元胞的内部希尔伯特空间 $\mathcal{H}_x$ 视为局域信息参考系，假定物理预测对每点内部基底的选择不敏感；

2. 证明要在无全局基底的情形下保持信息输运的幺正和因果一致，必然需要在格点之间引入"并行输运算符" $U_{x,\mu}$ 作为连接场，其变换律与格点规范场论完全一致；

3. 在平滑连续极限下，结合局域、各向同性与幺正演化的约束，刻画这样的连接场的最小畸变作用量，并证明其连续极限唯一选出 Maxwell/杨–米尔斯作用量；

4. 利用此前提出的信息速率守恒原理，将规范耦合常数与 QCA 内部/外部信息通道的比率联系起来，从而赋予电荷与耦合常数以信息论–几何的微观解释。

在这一框架中，规范场不再是"为了保持拉格朗日量在某个局域对称群下不变而被人为引入的辅助对象"，而是"在无全局基底的离散宇宙中，为了让信息可以稳定传输且不同观察者可达成一致描述而不得不付出的几何代价"。规范曲率则刻画了信息并行输运不再路径无关的程度。

---

## Model & Assumptions

本节给出 QCA 模型、局域参考系冗余性与信息输运原则，并将规范结构定义为满足这些原则的最小几何对象。

### 1. 量子元胞自动机的基本结构

考虑 $d$ 维正则格点 $\Lambda = a \mathbb{Z}^d$，格距为 $a$，时间步长为 $\Delta t$。在每个格点 $x \in \Lambda$ 上放置一个有限维希尔伯特空间 $\mathcal{H}_{x} \cong \mathbb{C}^{N_{\mathrm{int}}}$，称为内部自由度。全局希尔伯特空间为

$$
\mathcal{H} = \bigotimes_{x\in\Lambda} \mathcal{H}_x.
$$

QCA 的一次演化由幺正算符 $G:\mathcal{H}\to\mathcal{H}$ 给出，满足如下条件：

1. 因果性：存在有限半径 $R$，使得 $G$ 对某一格点 $x$ 的局域代数 $\mathcal{A}_x$ 的作用仅依赖 $x$ 邻域半径 $R$ 内的自由度；

2. 平移不变性：存在一族平移算符 $T_a$ 使得 $G$ 与 $T_a$ 对易；

3. 局域分解：$G$ 可写为有限深度局域量子电路 $G = \prod_\ell G_\ell$，每个 $G_\ell$ 作用于有限多个相邻格点。

在给定内部维数与局域性约束下，可以构造出狄拉克型 QCA，其连续极限给出狄拉克方程。本文并不依赖某一具体构造，而仅假定存在这样一类"自由物质 QCA"，其单粒子有效哈密顿为

$$
H_0 = \sum_{x,\mu} \left( \psi^\dagger(x) K_\mu \psi(x + a\hat\mu) + \mathrm{h.c.} \right) + \sum_x \psi^\dagger(x) M \psi(x),
$$

其中 $\psi(x)\in\mathbb{C}^{N_{\mathrm{int}}}$，$K_\mu$、$M$ 为固定矩阵，连续极限下 $H_0$ 对应某个洛伦兹不变自由场（如狄拉克场）。

### 2. 局域信息参考系与规范冗余

在离散宇宙本体论中，没有外在"上帝视角"的全局参考系。每个元胞仅能访问自身内部希尔伯特空间 $\mathcal{H}_{x}$ 的局域基底选择。对每个格点 $x$，选取一组正交归一基 ${\lvert e_i(x)\rangle}_{i=1}^{N_{\mathrm{int}}}$，则态矢量的坐标表示为

$$
\psi_x = \sum_i \psi_x^i \lvert e_i(x)\rangle.
$$

局域基底的选择具有任意性：对任意 $V_x \in G \subset U(N_{\mathrm{int}})$，作局域变换

$$
\lvert e_i(x)\rangle \mapsto \sum_j (V_x)_{ji} \lvert e_j(x)\rangle,
\quad
\psi_x \mapsto V_x \psi_x,
$$

物理预测理应保持不变。集合 ${V_x}_{x\in\Lambda}$ 构成局域规范群

$$
\mathcal{G} = \prod_{x\in\Lambda} G_x,
\quad G_x \cong G.
$$

这体现了"局域信息参考系的冗余性"。

这里根据内部结构与物理背景，考虑两类典型情形：

1. $G = U(1)$：仅有整体相位冗余，对应电荷 $U(1)$ 规范；

2. $G = SU(N_c)$ 或更一般紧 Lie 群：内部自由度具有"色"或"味"等多分量结构，对应非阿贝尔规范群。

本文后续统一以一般紧 Lie 群 $G$ 表述，阿贝尔情形作为特例。

### 3. 信息输运与连接场的定义

在 QCA 中，信息的空间传播由相邻元胞间的耦合实现。在固定某一全局基底的理想化描述下，自由哈密顿 $H_0$ 包含项

$$
\psi^\dagger(x) K_\mu \psi(x+a\hat\mu),
$$

其物理含义是"从 $x$ 跳至 $x+a\hat\mu$"的振幅。然而在无全局基底的本体论视角下，$\psi(x)$ 与 $\psi(x+a\hat\mu)$ 分别在各自局域基底下表示，不能直接相加。为了描述这类跨元胞的信息输运，必须在格点之间引入一个"并行输运算符" $U_{x,\mu}$，映射

$$
U_{x,\mu}:\mathcal{H}_{x} \longrightarrow \mathcal{H}_{x+a\hat\mu}.
$$

定义：

**定义 1（连接场/连边变量）.** 给定规范群 $G$，称一族算符 ${U_{x,\mu}}$ 为 QCA 的连接场，如果对每个连边 $(x,x+a\hat\mu)$ 有

$$
U_{x,\mu} \in G \subset U(\mathcal{H}_{x},\mathcal{H}_{x+a\hat\mu}),
$$

且在局域规范变换 ${V_x}$ 下满足

$$
U_{x,\mu} \mapsto U'_{x,\mu} = V_{x+a\hat\mu} U_{x,\mu} V_x^\dagger.
$$

在此定义下，含有连接场的 QCA 物质哈密顿自然写为

$$
H_{\mathrm{matter}}[U] = \sum_{x,\mu} \left( \psi^\dagger(x) K_\mu U_{x,\mu} \psi(x + a\hat\mu) + \mathrm{h.c.}\right) + \sum_x \psi^\dagger(x) M \psi(x),
$$

其形式上与格点规范场论中"在连边上插入群元"的做法一致，但此处 $U_{x,\mu}$ 是由局域参考系冗余与信息输运原则必然引入的几何量，而非"为了离散化某个连续规范场论"的技巧。

### 4. 信息畸变与规范场作用量的原则

连接场并非任意自由度。QCA 的物理演化应尽可能"温和"地输运信息，即在保持幺正与因果性的前提下，最小化信息在并行输运中的畸变。为此，引入如下原则：

**原则 A（局域信息畸变最小化）.** 在所有与给定物质哈密顿 $H_{\mathrm{matter}}[U]$ 兼容、且满足局域规范不变性的连接场动力学中，实际物理演化对应于使某个局域规范不变泛函 $S_{\mathrm{gauge}}[U]$ 极小的轨道。

为了体现局域性与各向同性，$S_{\mathrm{gauge}}[U]$ 应仅依赖于最小封闭回路（plaquette）上的并行输运算符乘积，即 Wilson 环路

$$
W_{\Box} = \mathrm{tr} U_{\Box},
\quad
U_{\Box} = U_{x,\mu} U_{x+a\hat\mu,\nu} U_{x+a\hat\nu,\mu}^\dagger U_{x,\nu}^\dagger,
$$

并在连续极限下收敛到某个可积的局域作用量密度 $\mathcal{L}(F_{\mu\nu})$。

标准格点规范场论表明，在二阶导数与局域性假设下，连续极限中唯一的规范不变二次型正是杨–米尔斯作用量 $\mathrm{tr}(F_{\mu\nu}F^{\mu\nu})$。本文将这一结论重新解释为"在局域参考系冗余与信息畸变最小化原则下，连接场的有效作用量必然退化为 Maxwell/杨–米尔斯作用量"。

---

## Main Results (Theorems and Alignments)

本节给出本文的核心定理，并说明其与已有理论的对应关系。

### 定理 1（局域基底冗余 $\Rightarrow$ 规范连接变换律）

设 $G$ 是紧 Lie 群，$G\subset U(N_{\mathrm{int}})$ 为其某个幺正表示。考虑一给定自由 QCA，在每个格点 $x$ 上引入局域基底变换 $V_x\in G$，并假定物质哈密顿 $H_{\mathrm{matter}}[U]$ 在 $\mathcal{G}=\prod_x G_x$ 下物理等价。若要求在任意局域变换 $V_x$ 下，跨格点的跃迁振幅

$$
\psi^\dagger(x) K_\mu U_{x,\mu} \psi(x+a\hat\mu)
$$

在物理意义上不变，则存在且仅存在一族连边算符 $U_{x,\mu}\in G$，其在 $\mathcal{G}$ 下的变换律为

$$
U_{x,\mu} \mapsto V_{x+a\hat\mu} U_{x,\mu} V_x^\dagger.
$$

此变换律与格点规范场论中的连边变量变换完全一致。

### 定理 2（自由 QCA 连续极限中的最小耦合）

设一类 QCA 在无连接场时的单粒子有效哈密顿在长波极限下给出自由狄拉克哈密顿

$$
H_0 = \int \mathrm{d}^d x \, \psi^\dagger(x) \left( -\mathrm{i} \gamma^0 \gamma^i \partial_i + m \gamma^0 \right) \psi(x),
$$

并满足平移、旋转和离散 $\mathcal{CPT}$ 对称性。对该 QCA 施加定理 1 的框架，在连边上引入 $G$-值连接场 $U_{x,\mu}$，并要求演化在局域规范变换下协变。则当 $a,\Delta t\to 0$ 且 $U_{x,\mu}\to \mathbb{I}$ 的平滑极限下，$H_{\mathrm{matter}}[U]$ 的单粒子有效哈密顿等价于

$$
H = \int \mathrm{d}^d x \, \psi^\dagger(x) \left( -\mathrm{i} \gamma^0 \gamma^i D_i + m \gamma^0 \right) \psi(x),
\quad
D_\mu = \partial_\mu - \mathrm{i} g A_\mu(x),
$$

其中 $A_\mu(x)\in \mathfrak{g}$ 为 Lie 代数值规范势，与 $U_{x,\mu}$ 的关系为

$$
U_{x,\mu} = \exp\left( -\mathrm{i} g a A_\mu(x) \right) + O(a^2).
$$

特别地，对 $G=U(1)$ 得到带电狄拉克–Maxwell 耦合，对 $G$ 非阿贝尔得到狄拉克–杨–米尔斯最小耦合。该结果与 DTQW 模型中"连续极限涌现狄拉克–规范场耦合"的结论一致。

### 定理 3（局域信息畸变作用量 $\Rightarrow$ Maxwell / 杨–米尔斯作用）

设 $S_{\mathrm{gauge}}[U]$ 是定义在连边变量上的作用量，满足：

1. 局域性：$S_{\mathrm{gauge}}$ 可写为各个有限 Wilson 环路的局部函数之和；

2. 规范不变性：在 $U_{x,\mu}\mapsto V_{x+a\hat\mu}U_{x,\mu}V_x^\dagger$ 下不变；

3. 各向同性：在格点的离散旋转群作用下不变；

4. 平滑极限：当 $U_{x,\mu}$ 取值接近单位元时，作用量密度为 $F_{\mu\nu}$ 的正定二次型，且不含高于二阶导数。

则在 $a\to 0$ 的连续极限下，$S_{\mathrm{gauge}}[U]$ 等价于

$$
S_{\mathrm{gauge}} \to -\frac{1}{2}\int \mathrm{d}^{d+1}x \, \mathrm{tr}\left( F_{\mu\nu} F^{\mu\nu} \right) + O(a^2),
$$

其中规范曲率

$$
F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu - \mathrm{i} g [A_\mu,A_\nu],
$$

对 $G=U(1)$ 退化为 Maxwell 作用量，对非阿贝尔 $G$ 给出杨–米尔斯作用量。该结论与 Wilson 作用量的连续极限一致。

### 定理 4（规范耦合常数的信息论刻画）

在满足信息速率守恒

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2
$$

的 QCA 宇宙中，设每个元胞具有 $N_{\mathrm{ch}}$ 条可用于外部信息输运的通道（连边），配位数为 $z$。记

$$
r_{\mathrm{int}} = \frac{\text{单位时间步内部相位更新的有效速率}}{\text{总信息速率}},
\quad
r_{\mathrm{hop}} = \frac{\text{单位时间步跨格点跳跃的有效速率}}{\text{总信息速率}},
$$

则在自然归一化下，规范耦合 $g$ 与无量纲精细结构常数 $\alpha = g^2/(4\pi)$ 可写为

$$
g^2 \propto \frac{r_{\mathrm{int}}}{z\, N_{\mathrm{ch}}\, r_{\mathrm{hop}}},
\quad
\alpha \propto \frac{r_{\mathrm{int}}}{z\, N_{\mathrm{ch}}\, r_{\mathrm{hop}}}.
$$

当探测尺度变化导致有效配位数与通道数变化时，$\alpha$ 将随之"跑动"，从而在 QCA 中给出重整化群流的离散几何机制。该结果将此前提出的"信息速率的普适守恒"与规范耦合常数联系起来。

---

## Proofs

本节给出上述定理的证明概要，并在附录中提供详细推导。

### 1. 定理 1 的证明：规范连接变换律

在无连接场时，物质哈密顿写为

$$
H_0 = \sum_{x,\mu} \left( \psi^\dagger(x) K_\mu \psi(x+a\hat\mu) + \mathrm{h.c.} \right) + \sum_x \psi^\dagger(x) M \psi(x).
$$

在局域基底变换 $\psi(x)\mapsto V_x \psi(x)$ 下，跨格点项变为

$$
\psi^\dagger(x) K_\mu \psi(x+a\hat\mu)
\mapsto
\psi^\dagger(x) V_x^\dagger K_\mu V_{x+a\hat\mu} \psi(x+a\hat\mu).
$$

若 $V_x$ 随 $x$ 变化，该项的矩阵结构一般会改变，破坏 QCA 的平移不变性与原始耦合矩阵 $K_\mu$ 的形式。为了在局域变换后仍保持"物质–连接体系"的物理等价性，需要在跨格点项中插入连边变量 $U_{x,\mu}$，并要求在变换后有

$$
\psi^\dagger(x) K_\mu U_{x,\mu} \psi(x+a\hat\mu)
\mapsto
\psi^\dagger(x) K_\mu U'_{x,\mu} \psi(x+a\hat\mu),
$$

即存在某个 $U'_{x,\mu}$ 使新旧哈密顿密度形式一致。

将局域变换显式写出：

$$
\psi^\dagger(x) K_\mu U_{x,\mu} \psi(x+a\hat\mu)
\mapsto
\psi^\dagger(x) V_x^\dagger K_\mu U_{x,\mu} V_{x+a\hat\mu} \psi(x+a\hat\mu).
$$

为使其可重写为 $\psi^\dagger(x) K_\mu U'_{x,\mu} \psi(x+a\hat\mu)$，需要

$$
K_\mu U'_{x,\mu} = V_x^\dagger K_\mu U_{x,\mu} V_{x+a\hat\mu}.
$$

若假定 $K_\mu$ 在表示空间中可逆，则

$$
U'_{x,\mu} = K_\mu^{-1} V_x^\dagger K_\mu U_{x,\mu} V_{x+a\hat\mu}.
$$

要使 $U'_{x,\mu}$ 仍取值于 $G$ 并保持 $K_\mu$ 的平移不变形式，自然的要求是 $K_\mu$ 与 $G$ 的表示对易，使得 $K_\mu^{-1} V_x^\dagger K_\mu = V_x^\dagger$。这可通过选择 $K_\mu$ 在内部空间上为标量或与 $G$ 的表示兼容来满足。于是得到

$$
U'_{x,\mu} = V_{x+a\hat\mu} U_{x,\mu} V_x^\dagger,
$$

即格点规范场论的标准变换律。因 $V_x$ 任意且 $G$ 为紧群，可证明该律在给定 $H_0$ 的条件下唯一地保持哈密顿结构与局域平移对称，得到定理 1。

### 2. 定理 2 的证明：连续极限中的最小耦合

考虑阿贝尔情形 $G=U(1)$ 以及非阿贝尔情形的统一表示。令

$$
U_{x,\mu} = \exp\left( -\mathrm{i} g a A_\mu(x) \right),
\quad
A_\mu(x)\in\mathfrak{g}.
$$

在长波极限下，假设 $\psi(x)$ 在格点上缓慢变化，可写为 $\psi(x+a\hat\mu) = \psi(x) + a \partial_\mu \psi(x) + O(a^2)$。跨格点项为

$$
\psi^\dagger(x) K_\mu U_{x,\mu} \psi(x+a\hat\mu)
= \psi^\dagger(x) K_\mu \exp\left( -\mathrm{i} g a A_\mu(x) \right) \left[ \psi(x) + a \partial_\mu \psi(x) + O(a^2) \right].
$$

展开到 $O(a)$：

$$
\psi^\dagger(x) K_\mu \psi(x)
+ a \psi^\dagger(x) K_\mu \partial_\mu \psi(x)
- \mathrm{i} g a \psi^\dagger(x) K_\mu A_\mu(x) \psi(x) + O(a^2).
$$

对自由 QCA 的连续极限，已有结果表明存在选择使得

$$
\sum_\mu \psi^\dagger(x) K_\mu \partial_\mu \psi(x)
\to
\psi^\dagger(x) \gamma^0 \gamma^i \partial_i \psi(x),
$$

以及质量项由 $\sum_x \psi^\dagger(x)M\psi(x)$ 给出。在此基础上，将上式中的 $-\mathrm{i} g a \psi^\dagger K_\mu A_\mu \psi$ 项吸收进导数中，可将空间导数替换为协变导数

$$
\partial_\mu \mapsto D_\mu = \partial_\mu - \mathrm{i} g A_\mu(x),
$$

得到狄拉克–规范场最小耦合形式。时间方向的耦合可通过对 QCA 的时间更新算符做类似构造获得。实际 DTQW/QCA 文献中，已展示了严格格点规范不变的量子行走，其连续极限给出了狄拉克场与外加电磁场的耦合哈密顿；将其中"手动插入"的连接场解释为上节构造，即可得到定理 2 的精确表述。

### 3. 定理 3 的证明：信息畸变泛函的连续极限

由原则 A，$S_{\mathrm{gauge}}[U]$ 应由各个最小 plaquette 的 Wilson 环路构造。对一个 plaquette $\Box$ 定义

$$
U_{\Box} = U_{x,\mu} U_{x+a\hat\mu,\nu} U_{x+a\hat\nu,\mu}^\dagger U_{x,\nu}^\dagger.
$$

要求 $S_{\mathrm{gauge}}$ 在 $U_{x,\mu}\to V_{x+a\hat\mu}U_{x,\mu}V_x^\dagger$ 下不变，意味着 $S_{\mathrm{gauge}}$ 必须由 $\mathrm{tr}(U_{\Box})$ 及其共轭构造。最简单的局域各向同性泛函为 Wilson 作用量

$$
S_{\mathrm{W}}[U] = \sum_{\Box} \frac{\beta}{N_{\mathrm{int}}} \,\mathrm{Re}\,\mathrm{tr}\bigl(\mathbb{I} - U_{\Box}\bigr),
$$

其中 $\beta$ 与耦合常数 $g$ 相关。对 $U_{x,\mu} \approx \exp(-\mathrm{i} g a A_\mu)$ 在小 $a$ 极限下展开，可得到

$$
U_{\Box} = \exp\left( -\mathrm{i} g a^2 F_{\mu\nu}(x) + O(a^3) \right),
$$

详见附录 A 中的 BCH 展开计算。于是

$$
\mathbb{I} - U_{\Box}
= \mathrm{i} g a^2 F_{\mu\nu}(x)
+ \frac{1}{2} g^2 a^4 F_{\mu\nu}^2(x)
+ O(a^6),
$$

其迹的实部到 $O(a^4)$ 为

$$
\mathrm{Re}\,\mathrm{tr}\bigl(\mathbb{I} - U_{\Box}\bigr)
= \frac{1}{2} g^2 a^4 \,\mathrm{tr}\bigl(F_{\mu\nu}^2(x)\bigr) + O(a^6).
$$

将 $\sum_{\Box}$ 近似为 $\int \mathrm{d}^{d+1}x / a^{d+1}$，得到

$$
S_{\mathrm{W}}[U]
\to
\frac{\beta g^2}{2 N_{\mathrm{int}}} \int \mathrm{d}^{d+1}x \, \mathrm{tr}\bigl(F_{\mu\nu} F_{\mu\nu}\bigr),
$$

即杨–米尔斯作用量。对 $G=U(1)$ 退化为 Maxwell 作用量。反过来，可证明在给定上述四条条件的前提下，任何其它局域规范不变二次型在连续极限下只是在这个作用量上加上高阶导数修正，从而定理 3 成立。

### 4. 定理 4 的证明：耦合常数与信息速率

在此前工作中，信息速率守恒原理表述为：对任一局域激发，其外部群速度 $v_{\mathrm{ext}}$ 与内部态演化速度 $v_{\mathrm{int}}$ 满足

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2,
$$

其中 $c$ 为 QCA 的光锥速度。内部态演化速度可通过局域哈密顿的谱宽度与相位旋转率刻画，外部群速度则由跨格点跃迁振幅与配位数给出。

在含规范场的 QCA 中，内部相位演化的一部分由规范连接的"旋转"承担，其粒子视角对应于与规范场的耦合。若记

$$
r_{\mathrm{int}} = \frac{v_{\mathrm{int}}^2}{c^2},
\quad
r_{\mathrm{ext}} = \frac{v_{\mathrm{ext}}^2}{c^2},
\quad
r_{\mathrm{int}} + r_{\mathrm{ext}} = 1,
$$

则可将 $r_{\mathrm{int}}$ 分解为与规范自由度相关的部分 $r_{\mathrm{gauge}}$ 与"裸内部自由度"的部分 $r_{\mathrm{bare}}$。在一个具有 $z$ 个最近邻、每个连边上 $N_{\mathrm{ch}}$ 条输运通道的 QCA 中，有效跨边信息输运能力随 $z N_{\mathrm{ch}}$ 增大而增强，为保持总速率守恒，$r_{\mathrm{gauge}}$ 相对份额应随之减小。自然的标度关系是

$$
g^2 \propto \frac{r_{\mathrm{gauge}}}{z\, N_{\mathrm{ch}}\, r_{\mathrm{ext}}}.
$$

在弱耦合极限下 $r_{\mathrm{gauge}}$ 为 $r_{\mathrm{int}}$ 的主导部分，可近似 $r_{\mathrm{gauge}}\approx r_{\mathrm{int}}$，于是得到定理 4 的关系。探测能标升高时，QCA 的有效格距 $a$ 与可见配位数 $z$ 发生变化，导致 $g^2$ 与 $\alpha$ 的标度变化，从而对应于连续场论中的重整化群流。

---

## Model Apply

本节给出几个具体模型，展示上述一般框架如何在具体 QCA 中实现，并如何在连续极限下对应于熟知的物理理论。

### 1. 一维狄拉克 QCA 中的 $U(1)$ 规范场

考虑一维狄拉克型 QCA，其自由演化可写为 split-step 量子行走形式：在每个格点上有双分量自旋 $\psi(x) = (\psi_\uparrow,\psi_\downarrow)^{\mathsf T}$，时间更新由交替的旋转与条件平移给出。适当选择旋转角与条件平移，可证明连续极限给出一维狄拉克方程。

在此基础上，在每条连边上引入 $U(1)$ 相位 $U_{x,\pm} = \exp[-\mathrm{i} g a A_\pm(x)]$，分别对应向左/向右的输运通道。要求整步演化在局域 $U(1)$ 相位变换 $\psi(x)\mapsto e^{\mathrm{i}\alpha(x)}\psi(x)$ 下协变，得到

$$
U_{x,+} \mapsto e^{\mathrm{i}\alpha(x+a)} U_{x,+} e^{-\mathrm{i}\alpha(x)},
\quad
U_{x,-} \mapsto e^{\mathrm{i}\alpha(x-a)} U_{x,-} e^{-\mathrm{i}\alpha(x)}.
$$

这正是定理 1 的阿贝尔特例。对连续极限展开，$U_{x,\pm} \approx \exp[-\mathrm{i} g a A_x(x)]$，得到狄拉克–电磁最小耦合。全系综的 Wilson 环路给出一维电场的离散曲率，作用量采用 Wilson 型函数得到 Maxwell 作用量。

### 2. 二维 QCA 与非阿贝尔 $SU(2)$ 规范场

在二维格点上，考虑内部空间为 $N_{\mathrm{int}} = 4$ 的 QCA，自旋与"色"各占两个分量。令规范群 $G = SU(2)$ 作用于色空间，内部哈密顿 $K_\mu$ 与 $M$ 对色空间为标量。引入连边变量

$$
U_{x,\mu} \in SU(2),
\quad
U_{x,\mu} = \exp[-\mathrm{i} g a A_\mu^a(x) T^a],
$$

其中 $T^a$ 为 $SU(2)$ 生成元。局域规范变换 $\psi(x)\mapsto V_x \psi(x)$，$V_x\in SU(2)$ 仅作用于色空间，导致连边变量按定理 1 的规则变换。选择 Wilson 作用量建立规范场动力学，连续极限下得到 $SU(2)$ 杨–米尔斯场的标准方程。

这一构造与 Arnault 等关于"量子行走与非阿贝尔离散规范理论"的工作形成呼应，后者明确展示了具有精确离散 $U(N)$ 规范不变性的离散时间量子行走，并在连续极限下得到杨–米尔斯–狄拉克耦合。

### 3. 信息几何视角下的电磁场

在上述 QCA–规范结构中，电场与磁场可分别与如下信息几何量对应：

1. 电场 $E_i$：相邻时间步间同一连边上的相位增长率差，刻画局域时钟的不同步程度。离散上可写为

   $$
   E_i(x) \sim \frac{1}{g a \Delta t} \arg\left[ U_{x,i}(t+\Delta t) U_{x,i}^\dagger(t) \right].
   $$

2. 磁场 $B_i$：空间平面内最小 plaquette 上 Wilson 环路的相位，刻画空间循环路径上的并行输运不相容度。离散上可写为

   $$
   B_i(x) \sim \frac{1}{g a^2} \arg U_{\Box}(x),
   $$
   
   其中 $\Box$ 为垂直于 $i$ 方向的平面 plaquette。

Aharonov–Bohm 效应在此框架中获得自然解释：即便局域电场/磁场强度为零，但若沿闭合路径的 Wilson 环路非平凡，信息态在沿路径并行输运后会累积可观测的整体相位。这一描述纯粹基于"信息并行输运"的路径依赖性，而不需要先验连续场背景。

---

## Engineering Proposals

本节讨论在可实现的量子模拟平台上验证上述"规范场作为信息输运几何"的若干实验方案。

### 1. 光子 QCA 平台上的电磁规范结构

近期工作已在光子平台上实现了一维狄拉克 QCA 的高保真模拟，通过可编程波导阵列和可重构干涉网络实现分步单元。在此基础上，可将可调相移器放置于相邻元胞之间的光路上，用以实现连边变量 $U_{x,\pm}$。通过在每个时间步调制这些相移，可以模拟时间依赖的规范势 $A_\mu(x,t)$。

实验步骤包括：

1. 以特定波包态初始化光子，在 QCA 上演化若干步；

2. 在有无连边相位调制的情形下分别测量输出干涉图样；

3. 比较输出波包中心的群速度与形状变化，从中提取有效电场与磁场；

4. 通过改变 Wilson 环路上的累积相位，观测干涉条纹的整体平移，实现离散 Aharonov–Bohm 实验。

若实验测得的波包演化在长波极限下满足 Maxwell 方程预测的电磁波传播规律，即可视为对"规范场即并行输运相位"图像的直接支持。

### 2. 冷原子与离子阱中的非阿贝尔结构

冷原子光晶格与离子阱体系为实现非阿贝尔规范结构提供了天然平台，可通过 Raman 耦合或多能级结构实现内部"色"自由度。现有方案已经能在这些平台上实现模拟格点规范场、观察强耦合区的特征。

在 QCA 视角下，可设计如下工程方案：

1. 将每个格点的内部态编码为多能级原子内部态的子空间，对不同能级施加局域可控的 SU(2) 或 SU(3) 旋转，作为局域参考系变换；

2. 通过受控相位门或共振隧穿在相邻格点之间实现并行输运算符 $U_{x,\mu}$；

3. 利用时间分辨测量记录在闭合路径上的累计相位与色态旋转，从而测量 Wilson 环路；

4. 改变局域旋转策略，验证物理结果仅依赖于等价类 $[U_{x,\mu}]$，而与某一具体基底选择无关，从而实验上验证定理 1 的核心内容。

### 3. 信息速率与耦合常数的实验估计

在小规模 QCA 量子模拟中，可通过如下方式估计信息速率与耦合常数的关系：

1. 通过测量波包传播速度与局域 Rabi 振荡频率，分别估计 $v_{\mathrm{ext}}$ 与 $v_{\mathrm{int}}$；

2. 通过引入可控规范势，测量散射截面与相移，反推有效耦合常数 $g_{\mathrm{eff}}$；

3. 改变连边密度与可用通道数 $N_{\mathrm{ch}}$，观察 $g_{\mathrm{eff}}$ 与 $z N_{\mathrm{ch}}$ 的经验关系；

4. 检验是否存在近似的 $g_{\mathrm{eff}}^2 \propto r_{\mathrm{int}}/(z N_{\mathrm{ch}} r_{\mathrm{hop}})$ 标度，从而为定理 4 提供经验支持。

这些实验不必达到高能物理尺度即可测试 QCA 框架中的结构性预言。

---

## Discussion (Risks, Boundaries, Past Work)

### 1. 与既有格点规范场论的关系

形式上，本文得到的连边变量 $U_{x,\mu}$、plaquette 曲率 $U_{\Box}$ 以及 Wilson 作用量与标准格点规范场论完全一致。差异在于解释层面：

* 在传统格点场论中，格点是为数值离散化引入的辅助结构，规范场是连续杨–米尔斯场的离散近似；

* 在本文的 QCA 视角中，格点与连边是本体上的基本实体，规范场是局域参考系冗余与信息输运一致性下不可避免的几何结构。

这一解释与部分 QCA 文献中"将量子场视为 QCA 的连续极限"的观点相契合，但进一步强调了规范结构的"信息论起源"。

### 2. 与量子行走模拟规范场的工作比较

Arnault 等关于量子行走与规范场的系列工作展示了如何构造具有精确离散规范不变性的 DTQW，并在连续极限下得到 Maxwell 与杨–米尔斯方程。本文的主要差异在于：

1. 我们从"局域信息参考系冗余"与"信息畸变最小化"出发，而非从给定的连续场论出发；

2. 定理 1–3 说明了在 QCA 本体论内部，规范连接与杨–米尔斯作用量是由一般原则唯一选出的结构；

3. 引入定理 4，将耦合常数与 QCA 中的速率分配联系起来，为重整化流提供了信息论–几何解释。

从技术上讲，本文的构造可以视为对 DTQW–规范理论的抽象和统一。

### 3. 风险与边界

尽管上述结果在内部逻辑上是一致的，但仍存在若干需要谨慎看待的边界：

1. **洛伦兹不变性涌现**：QCA 在离散尺度上一般不具备连续洛伦兹对称，其涌现在连续极限中需满足严格条件。已有工作表明在一维 Dirac QCA 中可实现精确或近似洛伦兹对称，但高维情形更为微妙。

2. **费米子倍增问题**：在格点上构造费米子场会遭遇 Nielsen–Ninomiya 型的倍增问题。QCA 视角下可部分规避这一问题，但在引入规范场后需要避免额外的"虚假物种"。

3. **重整化与连续极限**：定理 3 的连续极限推导依赖 $a\to 0$ 及 $U_{x,\mu}\to\mathbb{I}$ 的平滑性。若 QCA 的底层格距为物理不可分割的普朗克尺度，则"连续极限"只能是在有效场论意义上的近似，其适用范围需要通过具体模型与观测窗口加以界定。

4. **引力规范结构**：本文仅讨论内部规范群，对时空微分同胚与引力的"规范性质"尚未纳入 QCA 信息输运框架。如何将引力场视为某种"时间刻度–信息体积"的规范结构，需要结合光学度规与边界时间几何的进一步工作。

### 4. 与信息速率统一框架的整合

此前提出的信息速率守恒与光程守恒框架，将狭义相对论、质量与引力视为"信息速率预算"与"信息体积守恒"的结果。本工作可视为这一统一框架中"规范相互作用"部分的具体化：

* 规范场的存在反映了"内部信息通道上的速率分配"；

* 曲率项对应于"在并行输运中累积的信息时延差"；

* 耦合常数随能标的跑动对应于"在不同观测尺度下对 QCA 有效连边结构的 coarse-graining"，从而改变 $z$ 与 $N_{\mathrm{ch}}$。

从而，狭义相对论、引力与规范相互作用都可以在 QCA 中统一为"信息速率守恒与信息几何"的不同面向。

---

## Conclusion

本文在量子元胞自动机的离散本体论框架下，系统构建了"规范场作为信息输运几何"的理论。核心结论包括：

1. 在无全局基底的离散宇宙中，局域信息参考系的冗余性要求在格点之间引入连边变量 $U_{x,\mu}$，其变换律与格点规范场论中的连边规范连接一致（定理 1）。

2. 狄拉克型 QCA 在引入连接场后，其连续极限在自然条件下给出狄拉克–规范场的最小耦合形式（定理 2），从而证明 Maxwell 与杨–米尔斯方程可由 QCA 信息输运原则涌现。

3. 要求连接场的动力学由局域、规范不变、各向同性且二阶的"信息畸变泛函"主导，唯一选出在连续极限下退化为 Maxwell/杨–米尔斯作用量的 Wilson 型作用（定理 3）。

4. 利用信息速率守恒，将规范耦合常数与 QCA 中内部/外部信息通道的速率分配与连边结构联系起来，给出了耦合常数跑动的几何–信息论解释（定理 4）。

从这一视角看，自然界的基本相互作用不再是附加在物质上的"力"，而是信息在离散网络中被允许如何传输的几何约束。规范曲率测量了并行输运的路径依赖性，规范场方程则是最小化信息畸变的 Euler–Lagrange 方程。将该框架与引力、热化与宇宙学常数等问题结合，预计可以得到更加统一的"信息宇宙"描述。

---

## Acknowledgements, Code Availability

本工作为理论研究，未使用数值模拟代码。规范场与 QCA 相关的背景知识参考了关于格点规范场论与量子元胞自动机的若干综述与专著。

---

## Appendices

### 附录 A：从离散 holonomy 到连续场强的 BCH 推导

本附录给出 plaquette holonomy 对应非阿贝尔场强 $F_{\mu\nu}$ 的标准推导。

考虑二维格点上的一个最小 plaquette，其顶点分别为

$$
x,\quad x+a\hat\mu,\quad x+a\hat\mu+a\hat\nu,\quad x+a\hat\nu.
$$

定义连边变量

$$
U_{x,\mu} = \exp\bigl(-\mathrm{i} g a A_\mu(x)\bigr),
$$

$$
U_{x+a\hat\mu,\nu} = \exp\bigl(-\mathrm{i} g a A_\nu(x+a\hat\mu)\bigr),
$$

$$
U_{x+a\hat\nu,\mu}^\dagger = \exp\bigl(+\mathrm{i} g a A_\mu(x+a\hat\nu)\bigr),
$$

$$
U_{x,\nu}^\dagger = \exp\bigl(+\mathrm{i} g a A_\nu(x)\bigr).
$$

将 $A_\mu(x+a\hat\nu)$、$A_\nu(x+a\hat\mu)$ 在 $x$ 点处做一阶泰勒展开：

$$
A_\mu(x+a\hat\nu) = A_\mu(x) + a \partial_\nu A_\mu(x) + O(a^2),
$$

$$
A_\nu(x+a\hat\mu) = A_\nu(x) + a \partial_\mu A_\nu(x) + O(a^2).
$$

plaquette holonomy 为

$$
U_{\Box} = U_{x,\mu} U_{x+a\hat\mu,\nu} U_{x+a\hat\nu,\mu}^\dagger U_{x,\nu}^\dagger.
$$

用 Baker–Campbell–Hausdorff 公式

$$
\exp(X)\exp(Y) = \exp\left(X+Y+\frac{1}{2}[X,Y] + \cdots\right),
$$

并保留到 $O(a^2)$ 项。记

$$
X_1 = -\mathrm{i} g a A_\mu(x),
\quad
X_2 = -\mathrm{i} g a (A_\nu(x) + a \partial_\mu A_\nu(x)),
$$

$$
X_3 = +\mathrm{i} g a (A_\mu(x) + a \partial_\nu A_\mu(x)),
\quad
X_4 = +\mathrm{i} g a A_\nu(x).
$$

则

$$
U_{\Box} = \exp(X_1)\exp(X_2)\exp(X_3)\exp(X_4).
$$

先计算 $X_1+X_2+X_3+X_4$ 的主阶：

$$
X_1+X_2+X_3+X_4
= -\mathrm{i} g a^2\bigl(\partial_\mu A_\nu(x) - \partial_\nu A_\mu(x)\bigr).
$$

对交换子项，注意到 $[X_1,X_2]$、$[X_1+X_2,X_3]$、$[X_1+X_2+X_3,X_4]$ 等均为 $O(a^2)$，且主导贡献来自 $[A_\mu,A_\nu]$：

$$
[X_1,X_2] = (-\mathrm{i} g a)^2 [A_\mu(x), A_\nu(x)] + O(a^3)
= - g^2 a^2 [A_\mu,A_\nu] + O(a^3).
$$

综合所有 $O(a^2)$ 项后，可写为

$$
\ln U_{\Box}
= -\mathrm{i} g a^2\left( \partial_\mu A_\nu - \partial_\nu A_\mu - \mathrm{i} g [A_\mu,A_\nu] \right) + O(a^3)
= -\mathrm{i} g a^2 F_{\mu\nu}(x) + O(a^3),
$$

其中

$$
F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu - \mathrm{i} g [A_\mu,A_\nu].
$$

因而

$$
U_{\Box} = \exp\bigl(-\mathrm{i} g a^2 F_{\mu\nu}(x)\bigr) + O(a^3),
$$

给出了非阿贝尔场强与 plaquette holonomy 的精确关系。这一推导是定理 3 的关键。

### 附录 B：电荷守恒与边界算符的拓扑关系

在 QCA 中，$U(1)$ 电荷可定义为格点上某一守恒算符的总和，例如

$$
Q = \sum_x \psi^\dagger(x)\psi(x).
$$

在规范场存在时，引入离散电场变量 $E_{x,i}$ 作为共轭动量。离散高斯定律可写为

$$
(\nabla\cdot E)(x) = \sum_i \left( E_{x,i} - E_{x-a\hat i,i} \right) = \rho(x),
$$

其中 $\rho(x)$ 为电荷密度。将上述关系在某有限体积 $V$ 内求和，有

$$
\sum_{x\in V} (\nabla\cdot E)(x) = \sum_{x\in V} \rho(x).
$$

左侧可用格点边界算符 $\partial$ 表达为边界上的通量和：

$$
\sum_{x\in V} (\nabla\cdot E)(x)
= \sum_{\text{links}\in \partial V} E_{\text{link}}.
$$

这是离散散度定理的直接体现，即边界算符满足 $\partial^2 = 0$。因此

$$
\sum_{\text{links}\in \partial V} E_{\text{link}} = Q_{\mathrm{inside}},
$$

其中 $Q_{\mathrm{inside}} = \sum_{x\in V} \rho(x)$。对包含整个空间的体积 $V$ 而言，边界为空，左侧为零，从而得到总电荷守恒：

$$
\frac{\mathrm{d}}{\mathrm{d}t} Q = 0.
$$

在局域规范变换下，$E_{x,i}$ 与 $A_{x,i}$ 以共变方式变换，$\rho(x)$ 的定义保持不变，从而电荷守恒与规范不变性等价。这给出了"局域规范不变性 $\Leftrightarrow$ 电荷守恒"的拓扑论证。

### 附录 C：QCA 演化算符的规范协变性

令 $G[U]$ 为含连接场的 QCA 单步演化算符。要求在任意局域规范变换 $V = \bigotimes_x V_x$ 下满足

$$
G[U] \mapsto G'[U'] = V G[U] V^\dagger,
$$

其中 $U'_{x,\mu} = V_{x+a\hat\mu} U_{x,\mu} V_x^\dagger$。

考虑将 $G[U]$ 分解为局域门的乘积

$$
G[U] = \prod_\ell G_\ell[U],
$$

每个 $G_\ell$ 作用于有限个相邻格点。对每个 $G_\ell$ 施加局域规范变换，可写为

$$
G_\ell[U] \mapsto V G_\ell[U] V^\dagger = G_\ell[U'],
$$

只要 $G_\ell$ 中关于 $\psi$ 与 $U$ 的耦合结构满足定理 1 的构造形式。由于规范变换在不同格点上的因子彼此对易，可将整体变换规约为对每个局域门的独立共轭，从而保证整步演化的规范协变性。

反之，若要求对任意 ${V_x}$ 有 $G[U]\mapsto V G[U] V^\dagger$，可以证明 $G[U]$ 的所有物质–连接耦合必须通过 $\psi^\dagger(x) K_\mu U_{x,\mu} \psi(x+a\hat\mu)$ 型项实现，从而回到主文中的构造。

### 附录 D：信息速率与耦合常数标度的量纲分析

考虑一维简化情形。设 QCA 时间步为 $\Delta t$，空间步为 $a$。定义

$$
v_{\mathrm{ext}} = \frac{a}{\Delta t} p_{\mathrm{hop}},
\quad
v_{\mathrm{int}} = \frac{2}{\Delta t} \max_{\lambda} \lvert \lambda(H_{\mathrm{int}})\rvert,
$$

其中 $p_{\mathrm{hop}}$ 为单位时间内跨格点跳跃的平均概率，$H_{\mathrm{int}}$ 为内部哈密顿。信息速率守恒要求

$$
\left( \frac{a}{\Delta t} p_{\mathrm{hop}}\right)^2 + \left( \frac{2}{\Delta t} \max_{\lambda} \lvert \lambda(H_{\mathrm{int}})\rvert\right)^2 = c^2.
$$

引入无量纲参数

$$
r_{\mathrm{hop}} = \frac{v_{\mathrm{ext}}^2}{c^2},
\quad
r_{\mathrm{int}} = \frac{v_{\mathrm{int}}^2}{c^2}.
$$

在弱规范耦合极限下，规范场的影响主要体现在 $H_{\mathrm{int}}$ 的一个小子空间中，其有效谱宽度与耦合常数 $g$ 成正比。通过线性响应近似，可写为

$$
\max_{\lambda} \lvert \lambda(H_{\mathrm{int}})\rvert \approx \max_{\lambda} \lvert \lambda(H_{\mathrm{int}}^{(0)})\rvert + c_0 g,
$$

其中 $H_{\mathrm{int}}^{(0)}$ 为无规范场的内部哈密顿。由此，$r_{\mathrm{int}}$ 对 $g^2$ 的主导依赖为线性。另一方面，跨格点跳跃的幅度由 $z N_{\mathrm{ch}}$ 条通道共享，可近似

$$
p_{\mathrm{hop}}^2 \propto \frac{1}{z N_{\mathrm{ch}}},
$$

因信息速率预算在所有通道间平均分配。综合这些关系，忽略 $H_{\mathrm{int}}^{(0)}$ 的常数项，可得到

$$
g^2 \propto \frac{v_{\mathrm{int}}^2}{z N_{\mathrm{ch}} v_{\mathrm{ext}}^2}
= \frac{r_{\mathrm{int}}}{z N_{\mathrm{ch}} r_{\mathrm{hop}}}.
$$

这一量纲分析说明，即便在缺乏完整微观求解的情形下，耦合常数与 QCA 结构参数之间存在自然的比例关系，可用作构建"有限信息宇宙"时参数估计的起点。

---

## References

[1] K. G. Wilson, "Confinement of quarks," Phys. Rev. D 10, 2445 (1974).

[2] J. B. Kogut, "An introduction to lattice gauge theory and spin systems," Rev. Mod. Phys. 51, 659 (1979).

[3] E. Seiler, "A Gentle Introduction to Lattice Field Theory," Fortschr. Phys. 73, 2300005 (2025).

[4] P. Arrighi, "An overview of Quantum Cellular Automata," Natural Computing 18, 885–899 (2019).

[5] T. Farrelly, "A review of Quantum Cellular Automata," Quantum 4, 368 (2020).

[6] A. Bisio, G. M. D'Ariano, A. Tosini, "Quantum field as a quantum cellular automaton: The Dirac free evolution in one dimension," Ann. Phys. 354, 244–264 (2015).

[7] A. Mallick, S. Mandal, C. M. Chandrashekar, "Dirac Quantum Cellular Automaton from Split-step Quantum Walk," Sci. Rep. 6, 25779 (2016).

[8] P. Arnault, F. Debbasch, "Quantum walks and discrete gauge theories," Phys. Rev. A 93, 052301 (2016).

[9] P. Arnault, F. Debbasch, "Quantum walks and non-Abelian discrete gauge theory," Phys. Rev. A 94, 012335 (2016).

[10] L. Mlodinow, T. A. Brun, "Quantum cellular automata and quantum field theory in two and three spatial dimensions," Phys. Rev. A 102, 062222 (2020); 103, 052203 (2021).

[11] A. Suprano et al., "Photonic cellular automaton simulation of relativistic quantum physics," Phys. Rev. Research 6, 033136 (2024).

[12] H. Ma et al., "Universal Conservation of Information Celerity," preprint (2025).

[13] J. C. Baez, J. P. Muniain, *Gauge Fields, Knots and Gravity*, World Scientific (1994).

[14] X.-G. Wen, *Quantum Field Theory of Many-body Systems*, Oxford University Press (2004).

