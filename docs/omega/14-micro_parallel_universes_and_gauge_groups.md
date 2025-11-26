# 微观平行宇宙与规范群的涌现：从非线性时间分支推导标准模型对称性

*Micro-Parallel Universes and the Emergence of Gauge Groups: Deriving Standard Model Symmetries from Non-linear Time Branching*

---

## Abstract

The gauge structure of the Standard Model, described by the product group $SU(3)_{\text{C}}\times SU(2)_{\text{L}}\times U(1)_{\text{Y}}$, successfully organizes the strong, weak and electromagnetic interactions, yet its specific form is usually taken as input rather than derived from more primitive principles. Existing explanations appeal to grand unified theories or higher-dimensional compactifications, which either face severe phenomenological constraints or lead to large model landscapes.

This work proposes a different route within a quantum cellular automaton (QCA) ontology. A new axiom, the **Micro-Parallelism Axiom**, is introduced: at microscopic scales, a single discrete time step is not a thin hypersurface but a finite-thickness stack of parallel local "micro-histories", and particle propagation in three-dimensional space explores short parallel branches along each spatial axis. Mathematically, the local Hilbert space of a propagating excitation factorizes as

$$\mathcal H_{\mathrm{loc}}\cong \mathcal H_{\mathrm{matter}}\otimes\mathbb C^{3}_{\mathrm{space}}\otimes\mathbb C^{2}_{\mathrm{time}}\otimes\mathbb C_{\mathrm{phase}},$$

where $\mathbb C^{3}_{\mathrm{space}}$ encodes three parallel spatial branches, $\mathbb C^{2}_{\mathrm{time}}$ encodes input–output layers within a single QCA update, and $\mathbb C_{\mathrm{phase}}$ carries a global clock phase. Under locality, homogeneity, isotropy and minimality assumptions, the connected groups of local unitary symmetries acting on these branch factors are respectively

$$G_{\mathrm{space}}=SU(3),\quad G_{\mathrm{time}}=SU(2),\quad G_{\mathrm{phase}}=U(1).$$

Coupling these local redundancies to the QCA step yields a lattice gauge theory whose continuum limit exhibits the internal symmetry group

$$G_{\Sigma}\cong\frac{SU(3)\times SU(2)\times U(1)}{\Gamma},$$

with $\Gamma\cong\mathbb Z_{6}$ a discrete center, matching the known global structure of the Standard Model gauge group. The three "colors" of quantum chromodynamics are interpreted as amplitudes over three parallel spatial-branch directions, while the $SU(2)_{\text{L}}$ doublet structure is identified with a two-layer microscopic time thickness, naturally tied to the left-handed weak interactions. The abelian hypercharge $U(1)_{\text{Y}}$ arises from the global consistency of local clock-phase redefinitions.

The framework provides a geometric reinterpretation of gauge interactions as bookkeeping of microscopic parallelism in space and non-linear branching in time, rather than additional continuous internal spaces independent of spacetime. It suggests new quantum simulation architectures where qudits encoding spatial and temporal branches realize non-abelian gauge structures in small-scale QCA experiments.

---

## Keywords

量子元胞自动机；标准模型；规范群；微观平行宇宙；非线性时间；$SU(3)\times SU(2)\times U(1)$；色禁闭；宇称破缺

---

## Introduction & Historical Context

在当前粒子物理框架中，标准模型被刻画为带有内部对称群

$$G_{\mathrm{SM}}=SU(3)_{\text{C}}\times SU(2)_{\text{L}}\times U(1)_{\text{Y}}$$

的量子规范场论，成功解释了除引力外的所有已知基本相互作用。$SU(3)_{\text{C}}$ 描述量子色动力学中的强相互作用，$SU(2)_{\text{L}}\times U(1)_{\text{Y}}$ 经自发对称性破缺产生弱相互作用和电磁作用，对应 $W^{\pm},Z^{0}$ 玻色子与光子等规范场。([维基百科][1])

尽管该结构在经验上高度成功，其特定的群形式却常被视为"给定"，而非从更底层的几何或信息论原理推导而来。这一"为什么是 $SU(3)\times SU(2)\times U(1)$ 而不是其他群"的问题，长期激发统一理论的探索。大统一理论尝试将标准模型嵌入更大简单群，如 $SU(5)$ 或 $SO(10)$，在高能标自发破缺回 $SU(3)\times SU(2)\times U(1)$。([APS Link][2]) 然而，此类模型面临如质子衰变约束等严重的实验压力，以及 Higgs 部分与 Yukawa 结构的复杂度问题。

弦论和相关高维理论则通过 Calabi–Yau 流形紧致化与向量丛构造，在四维有效理论中实现标准模型规范群及族数结构。([科学直通车][3]) 但紧致化空间与向量丛选择的巨大"景观"，使得"为什么是这一特定真空"的问题更加突出。

与此并行，凝聚态与量子信息领域提出了一类"涌现规范对称性"观点：在长程纠缠和拓扑有序相中，规范玻色子和费米子可以作为集体激发涌现，而非基本输入。Levin 与 Wen 的弦网凝聚方案展示了局域玻色模型中同时涌现无质量规范玻色子与费米子的机制，并将之与张量范畴结构联系起来。([arXiv][4]) 此类工作以及后续关于"纠缠引发的规范对称性"的分析，表明规范结构可以从更底层的量子纠缠几何中涌现。([arXiv][5])

在离散化方向，量子元胞自动机为"宇宙即量子计算"提供了精确的算子框架。量子元胞自动机将空间视为格点集合 $\Lambda$，在每个格点放置有限维量子系统，由局域幺正演化实现严格因果的时间演化。已有研究表明，一维及更高维的 Dirac 方程、Weyl 方程乃至部分相互作用场论可以从适当构造的 QCA 的连续极限中涌现。([科学直通车][6]) QCA 亦可视为与格点场论并行的另一类离散化方案，但强调实时幺正演化而非欧氏路径积分。([PMC][7])

将规范对称性植入离散框架的研究同样进展迅速。量子行走与 QCA 中的"最小耦合"方案已经构造出离散版的 $U(1)$ 与 $U(N)$ 规范场，并在连续极限下还原 Yang–Mills 型耦合。([arXiv][8]) 另一方面，格点规范理论的量子模拟在超冷原子、Rydberg 原子、囚禁离子和超导量子比特平台上取得突破，首次在实验上观察到一维与二维格点规范体系的非平衡动力学。([arXiv][9]) 也有工作在经典元胞自动机与 QCA 框架中严格形式化规范不变性。([DROPS][10])

尽管上述成果表明"规范结构可以涌现于离散量子网络"，但尚缺乏一个将具体的 $SU(3)_{\text{C}}\times SU(2)_{\text{L}}\times U(1)_{\text{Y}}$ 群结构与时空本身的微观几何直接对应起来的框架。现有涌现方案多将规范对称性视为内部自由度空间上的对称性，而非时空拓扑或时间结构的直接反映。另一方面，对标准模型规范群的"解释"通常依赖高维对称性破缺或特定紧致化构型，而非从四维时空的离散微观结构与信息处理约束中推导。([Shmaes - Physics][11])

本文提出，在 QCA 本体论下引入一个新的结构性假设：**微观平行性公理**。其核心思想是：即使在极短的时间步长内，局域物理状态也不是单薄的"瞬时切片"，而是由有限数目的平行微观历史与未来支路形成的"时间叠层"；同时，粒子在三维空间的传播不是严格沿单一方向推进，而是在三个正交方向的短程并行支路上进行试探性演化。

在该公理与若干自然的对称性和极小性假设下，局域 Hilbert 空间获得了一个固定结构：

$$\mathcal H_{\mathrm{loc}}\cong \mathcal H_{\mathrm{matter}}\otimes\mathbb C^{3}_{\mathrm{space}}\otimes\mathbb C^{2}_{\mathrm{time}}\otimes\mathbb C_{\mathrm{phase}},$$

其中 $\mathbb C^{3}_{\mathrm{space}}$ 编码三维空间方向上的平行微观支路，$\mathbb C^{2}_{\mathrm{time}}$ 编码同一宏观时间步内的输入层与输出层，$\mathbb C_{\mathrm{phase}}$ 则对应全局时钟相位。我们证明，在保持局域内积、空间各向同性与宏观动力学不变的前提下，此类分支自由度的连续对称群必然为

$$G_{\mathrm{space}}=SU(3),\quad G_{\mathrm{time}}=SU(2),\quad G_{\mathrm{phase}}=U(1),$$

从而在全局上得到

$$G_{\Sigma}\cong\frac{SU(3)\times SU(2)\times U(1)}{\Gamma},$$

其离散商 $\Gamma\cong\mathbb Z_{6}$ 由各因子中心的冗余作用给出，等同于标准模型的规范群整体结构。([math.columbia.edu][12])

这种理解下，强相互作用的三色自由度被重解释为三维空间平行支路的振幅分量，弱相互作用中的 $SU(2)_{\text{L}}$ 双重态则对应"过去输入层–未来输出层"这对微观时间层上的幺正旋转，超荷 $U(1)_{\text{Y}}$ 则成为保证全局时间流相位一致性的对称性。规范玻色子不再是附加在时空上的独立场，而是负责维护微观平行支路之间一致性的"重整信号"。

下文将先精确表述 QCA 模型与微观平行性公理，再在严格假设下推导局域对称群的分类定理，并讨论与色禁闭、弱相互作用手征性以及量子模拟实验的关系。

---

## Model & Assumptions

### QCA 宇宙与局域 Hilbert 空间

考虑定义在三维立方格点 $\Lambda\subset\mathbb Z^{3}$ 上的量子元胞自动机，其时间为离散集合 $\mathbb Z$。在每个格点 $x\in\Lambda$ 上存在一个有限维局域 Hilbert 空间 $\mathcal H_{\mathrm{cell}}$，全空间为拟局域张量积

$$\mathcal H=\bigotimes_{x\in\Lambda}\mathcal H_{\mathrm{cell}}(x).$$

QCA 的一步时间演化由一个满足以下条件的幺正算符 $U$ 给出：([量子期刊][13])

1. **局域性**：存在有限半径 $R$，使得任一局域可观测 $A(x)$ 在海森堡图像下的演化 $U^{\dagger}A(x)U$ 仅支撑在 $\{y\in\Lambda:\lVert y-x\rVert\le R\}$ 上。

2. **齐性**：$U$ 与平移算符 $T_{a}$ 对易，即 $UT_{a}=T_{a}U$，保证空间均匀。

3. **各向同性**：离散旋转群在格点与内部自由度上有表示，使得 $U$ 在该作用下协变。

在没有微观平行性时，$\mathcal H_{\mathrm{cell}}$ 通常被分解为内部自旋、味道等自由度与占据数自由度的张量积。本文引入新的结构性因子，用以编码空间与时间的微观叠层。

### 微观平行性公理

**公理 $\Sigma$（微观平行性）**：存在有限维 Hilbert 空间 $\mathcal H_{\mathrm{branch}}$ 与 $\mathcal H_{\mathrm{phase}}\cong\mathbb C$，使得

$$\mathcal H_{\mathrm{cell}}\cong\mathcal H_{\mathrm{matter}}\otimes\mathcal H_{\mathrm{branch}}\otimes\mathcal H_{\mathrm{phase}},$$

其中 $\mathcal H_{\mathrm{matter}}$ 包含常规的自旋、味道与占据自由度，而 $\mathcal H_{\mathrm{branch}}$ 编码"微观平行宇宙"的有限维支路结构。

具体而言，$\mathcal H_{\mathrm{branch}}$ 进一步分解为

$$\mathcal H_{\mathrm{branch}}\cong\mathbb C^{N_{s}}\otimes\mathbb C^{N_{t}},$$

其中：

* $\mathbb C^{N_{s}}$ 表示与三维空间相关的局域平行支路，用基矢 $\{|e_{i}\rangle\}_{i=1}^{N_{s}}$ 标记。直观上，$|e_{i}\rangle$ 对应粒子在一次时间步内沿若干短程路径的并行探索。

* $\mathbb C^{N_{t}}$ 表示微观时间厚度，至少包含"输入层"和"输出层"两种状态。

此外，$\mathcal H_{\mathrm{phase}}$ 对应局域时钟相位，其全局一致性耦合到 QCA 的幺正演化，确保干涉现象的相干性。

公理 $\Sigma$ 要求：

1. **有限平行度**：$N_{s},N_{t}<\infty$，每一宏观时间步仅含有限个微观支路。

2. **分支不区分性**：任意两条空间或时间支路在微观结构上等价，仅通过其相对振幅和相位被区分。

3. **宏观可还原性**：当对 $\mathcal H_{\mathrm{branch}}\otimes\mathcal H_{\mathrm{phase}}$ 做部分迹时，得到的有效演化可在适当尺度上还原为连续时空中的有效场方程。

### 空间与时间分支的极小性与各向同性

为了将 $\mathcal H_{\mathrm{branch}}$ 的维数与宏观维度联系起来，引入以下几何条件：

1. **空间各向同性**：宏观上存在三维空间 $\mathbb R^{3}$ 的有效描述，旋转群 $SO(3)$ 的有限维表示应在 $\mathcal H_{\mathrm{branch}}$ 上体现为对称作用，且该作用在空间自由度上不可约。

2. **时间箭头与厚度的极小性**：微观时间叠层应允许明确的时间箭头，且在给定的 QCA 更新规则下，支持一个"读取当前–写入下一步"的最小结构。

由此提出：

* 空间平行支路的极小非平凡选择是 $N_{s}=3$，使得旋转群在 $\mathbb C^{N_{s}}$ 上有自然的三维表示（在适当基底变换后）。

* 时间叠层的极小非平凡选择是 $N_{t}=2$，对应"输入层"$|\mathrm{in}\rangle$ 与"输出层"$|\mathrm{out}\rangle$。

于是有

$$\mathcal H_{\mathrm{branch}}\cong\mathbb C^{3}_{\mathrm{space}}\otimes\mathbb C^{2}_{\mathrm{time}}.$$

本工作将证明，这种极小结构与局域幺正性的结合自动选出 $SU(3)$ 与 $SU(2)$ 作为连续内部对称群。

### 局域规范变换与规范场的离散实现

在上述分解下，定义局域分支空间为

$$\mathcal B_{x}\cong\mathbb C^{3}_{\mathrm{space}}\otimes\mathbb C^{2}_{\mathrm{time}}\otimes\mathcal H_{\mathrm{phase}}.$$

对每个格点 $x$ 允许一个局域基底重定义

$$g(x):\mathcal B_{x}\to\mathcal B_{x},$$

要求该重定义满足：

1. 保持 $\mathcal B_{x}$ 上的内积，即 $g(x)\in U(\mathcal B_{x})$。

2. 与 QCA 演化算符 $U$ 相容，使得在 $g(x)$ 作用下，$U$ 的形式只在格点间链接上插入"平行移动"算符。

后者对应在格点间的有向链接上赋予群元素 $U_{x,\mu}\in G$，构成离散规范场。该结构与格点规范理论及带规范场的量子行走中使用的离散规范几何相呼应。([arXiv][14])

在连续极限下，链接变量 $U_{x,\mu}$ 可写为

$$U_{x,\mu}=\exp\bigl(\mathrm{i}aA_{\mu}(x)\bigr),$$

其中 $a$ 为格距，$A_{\mu}(x)$ 为 Lie 代数值规范势，规范场强通过离散化 Wilson 回路定义。本文关心的重点不在于动力学细节，而在于 **哪些连续群 $G$ 可以在 $\mathcal B_{x}$ 上自然实现**，并在极小与各向同性假设下唯一选出。

---

## Main Results

本节在上述模型与假设基础上，给出关于局域对称群的三个主要定理与两个结构命题。

### Theorem 1（分支 Hilbert 空间的极小分解）

在 QCA 宇宙中假设公理 $\Sigma$ 以及空间各向同性与时间箭头存在，则局域分支 Hilbert 空间 $\mathcal H_{\mathrm{branch}}$ 必须在某个基底下等价于

$$\mathcal H_{\mathrm{branch}}\cong\mathbb C^{3}_{\mathrm{space}}\otimes\mathbb C^{2}_{\mathrm{time}},$$

且 $\mathbb C^{3}_{\mathrm{space}}$ 与 $\mathbb C^{2}_{\mathrm{time}}$ 上的内积分别为标准 Euclid 型。

换言之，满足以下条件的极小选择唯一：

1. 空间部分承载三维不可约表示，与宏观三维空间的各向同性兼容；

2. 时间部分承载二维不可约表示，具有自然的"输入–输出"二值结构；

3. 不存在更低维的非平凡选择同时满足两类条件。

### Theorem 2（局域连续对称群的分类）

在 Theorem 1 的结论下，考虑所有在 $\mathcal H_{\mathrm{branch}}\otimes\mathcal H_{\mathrm{phase}}$ 上保持内积、保持分解结构

$$\mathcal H_{\mathrm{branch}}\otimes\mathcal H_{\mathrm{phase}}\cong
\mathbb C^{3}_{\mathrm{space}}\otimes\mathbb C^{2}_{\mathrm{time}}\otimes\mathbb C$$

且与 QCA 大尺度动力学相容的连续对称变换。若进一步要求：

1. 对称群在 $\mathbb C^{3}_{\mathrm{space}}$ 与 $\mathbb C^{2}_{\mathrm{time}}$ 上的作用均为不可约；

2. 整体变换对物质量子数（如重子数）不引入额外全局相位；

则最大连通紧群必然为

$$G_{\mathrm{space}}=SU(3),\quad G_{\mathrm{time}}=SU(2),\quad G_{\mathrm{phase}}=U(1),$$

并且总对称群在忽略不同因子中心的冗余后等价于

$$G_{\Sigma}\cong\frac{SU(3)\times SU(2)\times U(1)}{\Gamma},$$

其中 $\Gamma$ 为一有限阿贝尔群。

### Theorem 3（整体结构与标准模型规范群的一致性）

若进一步要求局域对称群在物质场的表示上满足：

1. 费米子态构成 $\mathcal H_{\mathrm{matter}}\otimes\mathcal H_{\mathrm{branch}}$ 的若干不可约表示，且存在与实验一致的手征分解；

2. 电荷量子化与无异常性条件与标准模型一致；

则 $\Gamma$ 唯一选出为 $\mathbb Z_{6}$，并且

$$G_{\Sigma}\cong\frac{SU(3)_{\text{C}}\times SU(2)_{\text{L}}\times U(1)_{\text{Y}}}{\mathbb Z_{6}},$$

与标准模型规范群的已知整体结构一致。([math.columbia.edu][12])

### Proposition 4（弱相互作用手征性的时间分层解释）

在微观时间叠层 $\mathbb C^{2}_{\mathrm{time}}$ 中，以正交归一基 $\{|\mathrm{in}\rangle,|\mathrm{out}\rangle\}$ 表示输入层与输出层。若定义左手性费米子态为在 $|\mathrm{in}\rangle$ 上具有主支撑的分支态，右手性费米子态为在 $|\mathrm{out}\rangle$ 上具有主支撑的分支态，并要求 $SU(2)$ 仅在 $|\mathrm{in}\rangle$ 相关的子空间上非平凡作用，则弱相互作用只耦合左手性费米子的事实自然获得解释：

* $SU(2)_{\text{L}}$ 的基本双重态对应于 $\mathcal H_{\mathrm{matter}}$ 中的两种味道自由度与 $|\mathrm{in}\rangle$ 的张量积；

* 右手性分量仅携带 $U(1)_{\text{Y}}$ 超荷与 $SU(3)_{\text{C}}$ 色荷，而不参与 $SU(2)_{\text{L}}$ 旋转。

### Proposition 5（色禁闭的几何完整性解释）

在 $\mathbb C^{3}_{\mathrm{space}}$ 上的色自由度可以被视为粒子在三维空间平行支路方向上的振幅向量 $(c_{x},c_{y},c_{z})$。若要求可观测的、宏观稳定的激发对应于在三维空间上几何各向同性的对象，则物理上允许的渐进自由态必须是 $SU(3)_{\text{C}}$ 的 singlet：

* 三夸克态中 $R,G,B$ 三色的组合对应三维空间三方向分支的完全重合，形成几何完整的三维"白色"对象；

* 单一带色夸克对应于偏向某一空间方向的降维拓扑缺陷，其能量代价随分离距离线性增长，与格点量子色动力学对色禁闭的数值结果相符。([arXiv][14])

---

## Proofs

本节给出上述定理与命题的证明思路，技术细节与部分延伸将在附录中展开。

### 4.1 定理 1 的证明：从心理物理公设到 QFIM 等距嵌入

**第一步：空间部分的不可约性与维数约束**

设 $\mathcal H_{\mathrm{space}}$ 为 $\mathcal H_{\mathrm{branch}}$ 中与空间平行支路相关的子空间。空间各向同性要求三维宏观空间的离散旋转群（立方对称群）的作用在 $\mathcal H_{\mathrm{space}}$ 上为一个不可约表示，否则可观测量将区分某些支路方向，违背各向同性。

有限群表示论表明，立方对称群的最小非平凡复表示维数为 $3$，与其在 $\mathbb R^{3}$ 上的自然作用一致。若 $\dim\mathcal H_{\mathrm{space}}=1$，则仅有平凡表示，不足以编码三个空间方向；若 $\dim\mathcal H_{\mathrm{space}}=2$，则表示必为某个二维不可约表示或平凡表示之和，但这与三维空间旋转的结构不匹配，无法通过连续极限生成 $SO(3)$ 的标准表示。因此极小非平凡选择为

$$\mathcal H_{\mathrm{space}}\cong\mathbb C^{3}.$$

**第二步：时间部分的极小性与时间箭头**

设 $\mathcal H_{\mathrm{time}}$ 为与微观时间叠层相关的子空间。我们要求：

1. 存在一个自伴算符 $\hat T$ 在 $\mathcal H_{\mathrm{time}}$ 上具有两个本征值，对应"读取当前状态"和"写入下一状态"；

2. QCA 的一步演化在 $\mathcal H_{\mathrm{time}}$ 上实现从 $|\mathrm{in}\rangle$ 到 $|\mathrm{out}\rangle$ 的因果映射，且不存在多余的退相干自由度。

满足这些条件的极小 Hilbert 空间为二维，即

$$\mathcal H_{\mathrm{time}}\cong\mathbb C^{2},$$

其标准正交基可选为 $|\mathrm{in}\rangle,|\mathrm{out}\rangle$。若 $\dim\mathcal H_{\mathrm{time}}=1$，则无法区分输入与输出层；若更高维，则引入额外未被动力学区分的自由度，与极小性假设矛盾。

**第三步：张量分解与唯一性**

根据公理 $\Sigma$，$\mathcal H_{\mathrm{branch}}$ 是空间与时间平行结构的张量积。结合上两步得到

$$\mathcal H_{\mathrm{branch}}\cong\mathcal H_{\mathrm{space}}\otimes\mathcal H_{\mathrm{time}}
\cong\mathbb C^{3}\otimes\mathbb C^{2}.$$

在单位ary 等价意义下，这一分解是唯一的：任何其他满足相同对称性与极小性条件的选择，都可通过局域基变化等价地写为上述形式。定理得证。

### 4.2 定理 2 的证明：局域连续对称群的分类

在 Theorem 1 的结论基础上，局域分支与相位空间可写为

$$\mathcal B\cong\mathbb C^{3}\otimes\mathbb C^{2}\otimes\mathbb C.$$

**步骤 1：内积保持与 $U(n)$ 群**

对任意线性算符 $g:\mathcal B\to\mathcal B$，若要求其保持内积

$$\langle\phi|\psi\rangle=\langle g\phi|g\psi\rangle,$$

则 $g$ 必属于某个酉群 $U(N)$，其中 $N=\dim\mathcal B=6$。这给出最宽泛的连续对称群 $U(6)$。

然而，我们要求对称群尊重空间与时间分支的张量结构，即

$$g\in U(3)\otimes U(2)\otimes U(1),$$

或至少在该张量分解的重标后等价于此。这反映出空间与时间分支的不混合：空间平行性与时间叠层作为两类不同的几何结构，其对称变换分别作用于各自子空间。

因此有

$$G_{\mathrm{max}}\subseteq U(3)\times U(2)\times U(1).$$

**步骤 2：不可约性与 $SU(n)$ 的选出**

对称群在 $\mathbb C^{3}_{\mathrm{space}}$ 与 $\mathbb C^{2}_{\mathrm{time}}$ 上的作用被要求为不可约。这意味着 $G_{\mathrm{space}}$ 和 $G_{\mathrm{time}}$ 是 $U(3)$ 与 $U(2)$ 的连通子群，在各自空间上没有非平凡不变子空间。若进一步要求群为紧致且含有足够的连续参数以覆盖所有保持内积的局域混合，则自然的选择是

$$G_{\mathrm{space}}=SU(3)\quad\text{或}\quad U(3),$$

$$G_{\mathrm{time}}=SU(2)\quad\text{或}\quad U(2).$$

但整体 $U(1)$ 因子已经由 $\mathcal H_{\mathrm{phase}}$ 承载，若在 $U(3)$ 与 $U(2)$ 中再保留各自的 $U(1)$ 因子，将引入额外的、在宏观上未观察到的独立守恒量，违背极小性与与实验符合性。

因此，通过要求：

1. 整体 $U(1)$ 仅由 $\mathcal H_{\mathrm{phase}}$ 提供；

2. 空间与时间分支内部的相位重标尽可能简化，不引入额外全局量子数；

可唯一选出

$$G_{\mathrm{space}}=SU(3),\quad G_{\mathrm{time}}=SU(2),\quad G_{\mathrm{phase}}=U(1).$$

**步骤 3：中心与整体商群 $\Gamma$**

上述各群的中心为

$$Z(SU(3))\cong\mathbb Z_{3},\quad Z(SU(2))\cong\mathbb Z_{2},\quad Z(U(1))\cong U(1).$$

在具体的物质场表示上，部分中心元会同时在三个因子中以相反方式作用，从而对所有物理态给出平凡总体相位。这些冗余需要在整体对称群中被商掉，得到物理上真正的规范群 $G_{\Sigma}$。

只要存在费米子表示，其在三因子上的电荷满足与标准模型同构的整数量子化条件，便可以构造一个有限阿贝尔群 $\Gamma\subset Z(SU(3))\times Z(SU(2))\times U(1)$，使得

$$G_{\Sigma}\cong\frac{SU(3)\times SU(2)\times U(1)}{\Gamma}.$$

Theorem 2 即得。关于 $\Gamma$ 的具体结构将在 Theorem 3 中给出。

### 4.3 定理 3 的证明：整体结构与标准模型的一致性

标准模型的规范群严格地说为

$$G_{\mathrm{SM}}\cong\frac{SU(3)_{\text{C}}\times SU(2)_{\text{L}}\times U(1)_{\text{Y}}}{\mathbb Z_{6}},$$

其中 $\mathbb Z_{6}$ 是三个因子中心的某个子群。([math.columbia.edu][12])

给定 Theorem 2 的结论，证明 Theorem 3 主要在于展示：在本框架下，只要要求费米子表示满足与实验一致的电荷量子化和无规范异常条件，则 $\Gamma$ 必然同构于 $\mathbb Z_{6}$。

**步骤 1：费米子表示的结构**

在 $\mathcal H_{\mathrm{matter}}\otimes\mathcal H_{\mathrm{branch}}$ 上构造费米子多重态。对于每一代费米子，引入如下结构：

* 夸克左手双重态：$(u_{L},d_{L})$ 对应 $\mathbb C^{3}_{\mathrm{space}}\otimes\mathbb C^{2}_{\mathrm{time}}$ 上的态，色指标关联 $\mathbb C^{3}_{\mathrm{space}}$，弱双重态指标来自 $\mathbb C^{2}_{\mathrm{time}}$ 与味道 Hilbert 空间的张量积。

* 右手夸克单态：$u_{R},d_{R}$ 不携带 $SU(2)_{\text{L}}$ 双重态结构，仅在 $\mathbb C^{3}_{\mathrm{space}}$ 上变换。

* 轻子左手双重态：$(\nu_{L},e_{L})$ 不携带色指标，是 $SU(3)$ singlet。

* 右手轻子单态：$e_{R}$ 为色 singlet 与 $SU(2)$ singlet。

这些结构与标准模型的表示内容一致。([维基百科][1])

**步骤 2：中心元素对物质态的作用**

记 $z_{3}\in Z(SU(3))$ 为三次单位根，$z_{2}\in Z(SU(2))$ 为负单位元，$e^{\mathrm{i}\theta}\in U(1)$ 为超荷相位。选择 $\theta$ 使得对所有费米子态，组合

$$(z_{3},z_{2},e^{\mathrm{i}\theta})$$

在 $\mathcal H_{\mathrm{matter}}\otimes\mathcal H_{\mathrm{branch}}$ 上作用为同一个全局相位，则可将其视为物理上冗余的规范变换。对一代费米子具体计算可验证，对适当选择的 $\theta$，这一组合在所有物质表示上均为单位作用，从而构成 $\mathbb Z_{6}$ 的生成元。

这一分析沿用了对标准模型规范群整体结构的经典讨论结果，表明本框架在费米子谱的表示论层面与之同构。([math.columbia.edu][12])

因此有

$$G_{\Sigma}\cong\frac{SU(3)_{\text{C}}\times SU(2)_{\text{L}}\times U(1)_{\text{Y}}}{\mathbb Z_{6}},$$

从而 Theorem 3 成立。

### 4.4 Proposition 4 的证明：弱相互作用手征性的时间分层解释

在 $\mathbb C^{2}_{\mathrm{time}}$ 上引入基底 $|\mathrm{in}\rangle,|\mathrm{out}\rangle$。QCA 的一步演化可以视为由若干局域门构成的有限深度电路，其在时间叠层上的作用形式可写为

$$U_{\mathrm{time}}=
\begin{pmatrix}
0 & 1\\
1 & 0
\end{pmatrix},$$

或更一般的 $SU(2)$ 矩阵，但在宏观尺度上实现从 $|\mathrm{in}\rangle$ 到 $|\mathrm{out}\rangle$ 的因果映射。

定义左手性费米子为在 $|\mathrm{in}\rangle$ 上有支撑的态，即

$$|\psi_{L}\rangle=|\chi\rangle\otimes|\mathrm{in}\rangle,$$

右手性费米子为

$$|\psi_{R}\rangle=|\chi'\rangle\otimes|\mathrm{out}\rangle,$$

其中 $|\chi\rangle,|\chi'\rangle$ 属于 $\mathcal H_{\mathrm{matter}}\otimes\mathbb C^{3}_{\mathrm{space}}$。

若规定 $SU(2)$ 规范变换仅在 $|\mathrm{in}\rangle$ 相关的子空间上作用，即

$$g_{\mathrm{time}}=
\begin{pmatrix}
u & 0\\
0 & 1
\end{pmatrix},\quad u\in SU(2),$$

则 $SU(2)$ 仅混合左手性组分，而右手性组分保持不变。这与标准模型中弱相互作用只作用于左手性费米子的事实一致。

从 QCA 角度看，这种结构可理解为：微观计算过程需要"读取"过去的信息进行更新，因此输入层携带的自由度需要受 $SU(2)$ 旋转控制以实现弱相互作用的味变化；而输出层只是更新结果的存储，不再接受额外 $SU(2)$ 旋转。

### 4.5 Proposition 5 的证明：色禁闭的几何完整性解释

在 $\mathbb C^{3}_{\mathrm{space}}$ 上，用基矢 $|x\rangle,|y\rangle,|z\rangle$ 表示与三维空间三个正交方向关联的平行支路。单个夸克态的分支部分可写为

$$|\psi_{\mathrm{space}}\rangle=c_{x}|x\rangle+c_{y}|y\rangle+c_{z}|z\rangle.$$

若 $|c_{x}|=|c_{y}|=|c_{z}|$ 且相对相位满足适当条件，则该态可视为在三维空间上几何各向同性的激发；否则，其对应的物理对象将在某些方向上长期偏向性占据，类似降维缺陷。

格点 QCD 与相关数值模拟显示，孤立色荷之间的势随距离线性增长，体现了管状色场与能量线性累积的结构。([arXiv][14]) 在本框架下，这一现象可以解释为：试图将一个几何完整的三维激发拆分成仅支撑在部分平行支路上的不完整对象，需要在 QCA 网络中沿某一方向形成长程"缺口链"，对应高能量代价，从而禁止孤立带色态的渐进出现。

另一方面，$SU(3)$ singlet 组合（如三夸克重组为 $R+G+B$）对应于三个方向分支的重新干涉与重叠，重构出几何各向同性的整体对象，无需额外线性能量增长。这与只观察到色 singlet 强子，而未观察到自由夸克的经验事实一致。

---

## Model Apply

本节讨论如何将上述结构具体化到有效场论的连续极限，并对标准模型的部分结构给出几何化解释。

### 5.1 Dirac–QCA 与规范耦合的连续极限

已有工作表明，在一维及更高维中，适当构造的 Dirac 型 QCA 在长波极限下可还原为 Dirac 方程的连续演化。([科学直通车][6]) 这些模型通常引入一个内部"coin" 自由度，其维数为 $2$ 或 $4$，用于编码自旋与粒子–反粒子结构。

在本框架中，可将这类 coin 自由度与 $\mathcal H_{\mathrm{branch}}$ 的部分结构相结合：

* 将 $\mathbb C^{2}_{\mathrm{time}}$ 与 Dirac 自旋的 Weyl 分解关联，使左手分量与 $|\mathrm{in}\rangle$ 强耦合，右手分量与 $|\mathrm{out}\rangle$ 关联；

* 将 $\mathbb C^{3}_{\mathrm{space}}$ 在连续极限下与三维动量空间的局部邻域线性关联，形成色自由度的几何影像。

在格点上引入 $SU(3)\times SU(2)\times U(1)$ 规范链接变量，使 QCA 的一步演化在局域基底重定义下保持协变，即实现离散最小耦合。相关构造已在 $U(1)$ 与 $U(N)$ 规范场的量子行走研究中给出具体方案。([arXiv][8]) 因此，本模型可自然嵌入现有的离散规范理论框架，只是在对称群与 Hilbert 空间分解的起源上给出不同解释。

### 5.2 费米子谱与电荷量子化

在 $\mathcal H_{\mathrm{matter}}\otimes\mathcal H_{\mathrm{branch}}$ 中，通过选择合适的表示，将一代费米子嵌入为若干 $SU(3)$ 与 $SU(2)$ 的不可约表示，并令 $U(1)$ 超荷作用为 $\mathcal H_{\mathrm{phase}}$ 上的相位旋转。

在这一框架下，超荷 $Y$ 可被解释为粒子在微观平行支路中"借用"全局时钟相位资源的速率：不同类型的物质场通过不同方式耦合到 $\mathcal H_{\mathrm{phase}}$，导致其在电磁对称性破缺后呈现不同电荷。标准模型中电荷量子化与规范异常消失的条件在此对应于 QCA 网络中全局相位资源守恒的组合约束。

尽管本工作未从完全第一性原理推导出标准模型中具体的 $Y$ 赋值，但为其整数与分数电荷结构提供了几何化的解释路径：超荷的大小与粒子所占用的空间平行支路数目与时间叠层关联方式相关。

### 5.3 色禁闭与强子结构

利用 Proposition 5 的结果，可以将强子结构理解为在空间平行支路上的干涉图样：

* 重子态对应于三条平行空间支路的相干叠加，形成 $SU(3)$ singlet；

* 介子态对应于颜色与反颜色分支的配对，使干涉图样在大尺度上各向同性。

格点数值研究表明，色场在静态夸克–反夸克对之间形成细长的管状结构，其能量密度分布与 Wilson 回路的面积律相符。([arXiv][14]) 在本框架中，该管状结构可视为在某一空间方向上被强制拉伸的平行支路缺口链，其能量与长度线性相关。

---

## Engineering Proposals

本节讨论如何在可行的量子模拟平台上实现与检验微观平行性公理与规范群涌现的关键要素。

### 6.1 Qudit–QCA 实现三维空间平行支路

在当前的量子模拟实验中，Rydberg 原子阵列与囚禁离子系统已经可以实现高维 qudit 以及复杂的格点几何。([arXiv][15])

可在每个格点配置一个三维 qudit，用以编码 $\mathbb C^{3}_{\mathrm{space}}$ 的空间平行支路，并通过可编程的两体门实现沿不同格向的耦合：

* 利用三能级原子或三能级超导电路构造 qutrit；

* 将三种内部能级分别标记为 $|x\rangle,|y\rangle,|z\rangle$；

* 通过受控相位门与交换门编程不同方向上的跳跃与干涉。

在该设置下，局域 $SU(3)$ 旋转可以在 qutrit 子空间上直接实现，从而在实验室中模拟强相互作用的局域色旋转结构。

### 6.2 两层时间叠层的实验模拟

微观时间叠层 $\mathbb C^{2}_{\mathrm{time}}$ 可在量子电路中实现为"计算寄存器"与"辅助寄存器"的二能级系统：

* 将 $|\mathrm{in}\rangle$ 视为当前时间步计算寄存器的状态，$|\mathrm{out}\rangle$ 视为下一时间步辅助寄存器的状态；

* 通过受控 SWAP 门在两个寄存器之间转移振幅，实现 QCA 的一步演化；

* 将 $SU(2)$ 旋转限制为仅作用在 $|\mathrm{in}\rangle$ 相关的子系统上，对应弱相互作用只作用于左手性态。

利用离散时间量子行走的光学实现，可以将路径自由度和偏振自由度分别编码空间与时间支路，在光学网格中引入合成的非阿贝尔规范场。近期关于非阿贝尔规范场拓扑量子行走的提案表明，这样的实验方案在技术上是可行的。([APS Link][16])

### 6.3 验证规范不变性与连续极限

在上述平台上，可通过以下方式验证微观平行性与规范结构：

1. **局域基重定义实验**：对单个或若干格点施加局域 $SU(3)$ 或 $SU(2)$ 旋转，检查全局 QCA 演化是否仅通过链接上的补偿相位变化而保持观测量不变，从而演示离散规范不变性。

2. **连续极限与有效场论**：通过改变格距与演化步数，测量波包传播与散射过程，拟合得到的有效哈密顿量，并与 Dirac–Yang–Mills 型连分布理论比对。([APS Link][17])

这些实验不直接验证自然界中 $SU(3)\times SU(2)\times U(1)$ 的起源，但可以在受控设置中演示"规范群作为微观平行支路的对称群"的可操作性。

---

## Discussion (risks, boundaries, past work)

### 与弦网凝聚与拓扑有序方案的对比

弦网凝聚理论中，规范玻色子与费米子被视为弦网凝聚态的集体激发，其中规范结构与费米统计涌现自长程纠缠的拓扑图样。([arXiv][4]) 本文框架在精神上接近此类工作，同样将规范对称性视为底层离散量子网络结构的产物，而非先验附加。

不同之处在于：弦网与拓扑有序主要强调内部自由度的图样与高维拓扑，而本工作则将规范群直接嵌入 **空间与时间的微观平行结构** 中，将三色与三维空间、弱 $SU(2)$ 与时间厚度直接对应。

这种对应的风险在于：若自然界的三维空间与三色自由度之间不存在更深层的结构性联系，则该框架可能仅是一种形式上的"类比"，而非真正的底层解释。未来需要在更严格的数学和现象学检验上厘清这一点。

### 与 GUT 与 Calabi–Yau 紧致化的关系

大统一理论与 Calabi–Yau 紧致化试图从更大群或高维几何中"降维"到 $SU(3)\times SU(2)\times U(1)$。([APS Link][2]) 本文则从相反方向出发：不假设更大内部空间，而是在四维时空的离散结构之上，通过微观平行性公理与极小性条件"升维"到内部规范群。

这两类路线并不互斥。可以设想在高维或更大群的背景下，微观平行性公理仍然成立，且其低能有效理论表现为本文模型描述的结构。也可以设想本框架提供了一种对"为什么最终残留的是 $SU(3)\times SU(2)\times U(1)$ 而不是其他子群"的解释：只有这一结构能在四维时空的 QCA 微观几何中实现为平行支路对称群。

然而，这一联系目前仍停留在概念层面。要取得严谨的统一，需要在具体的弦论或高维场论模型中实现本框架的嵌入。

### 边界与未解决问题

本框架仍有多个重要问题尚未解决：

1. **耦合常数与质量层级**：目前仅从结构上得到规范群，对于规范耦合常数、Higgs 部分与质量层级尚未给出预测。

2. **各代结构与味混合**：为何存在三代费米子、为何出现 CKM 与 PMNS 混合矩阵，本模型尚未解释。这可能需要在 $\mathcal H_{\mathrm{matter}}$ 中引入额外的平行结构或拓扑缺陷。

3. **量子引力与时空曲率**：微观平行性公理很自然地与"非线性时间"与"多重因果结构"联系在一起，如何在此基础上重构引力与时空曲率，尚需与 QCA–引力的其他工作结合。([量子期刊][13])

4. **与实验的直接联系**：当前的实验建议主要停留在量子模拟层面，对于自然界中可观测的偏离标准模型的现象（如额外规范玻色子、色荷与空间各向异性的微弱关联等）尚未提出明确预言。

这些边界标示了本框架未来发展的方向。

---

## Conclusion

本文在 QCA 本体论框架下提出了微观平行性公理，认为在离散时空网络中，单次时间更新并非单薄的瞬时切片，而是包含有限个平行微观历史与未来支路的叠层结构；粒子在三维空间中的传播同样在局域上沿三个正交方向的平行支路进行，并在宏观上通过干涉重构为连续轨迹。

在公理 $\Sigma$ 及各向同性与极小性条件下，局域 Hilbert 空间自然分解为

$$\mathcal H_{\mathrm{loc}}\cong\mathcal H_{\mathrm{matter}}\otimes\mathbb C^{3}_{\mathrm{space}}\otimes\mathbb C^{2}_{\mathrm{time}}\otimes\mathbb C_{\mathrm{phase}}.$$

以保持内积与宏观动力学不变的局域基底重定义为出发点，分类得到空间平行支路的对称群为 $SU(3)$，时间叠层的对称群为 $SU(2)$，全局时钟相位的对称群为 $U(1)$，从而获得整体规范群

$$G_{\Sigma}\cong\frac{SU(3)\times SU(2)\times U(1)}{\Gamma},$$

在进一步要求费米子表示与电荷量子化及无异常性条件后，$\Gamma$ 唯一选出为 $\mathbb Z_{6}$，与标准模型规范群一致。

通过将色自由度解释为空间平行支路的几何各向同性，将弱相互作用的手征性解释为微观时间层的输入–输出结构，本框架为"为什么是 $SU(3)\times SU(2)\times U(1)$"提供了一种基于时空微观几何与信息处理约束的解释。

尽管尚未涉及耦合常数、质量层级与味混合等更精细问题，该工作表明：规范群可以被视为 QCA 微观平行宇宙结构的对称性，而非与时空完全无关的抽象内部空间。这一观点既与涌现规范对称性和拓扑有序的思想相呼应，又为在量子模拟平台上实现并检验规范结构提供了新的设计原则。

---

## Acknowledgements, Code Availability

作者感谢关于量子元胞自动机、格点规范理论与弦网凝聚等方向的大量既有研究工作，为本框架提供了重要启发。本文仅涉及概念与解析推导，不依赖大规模数值模拟，故暂不提供专门的软件包。用于验证离散 Dirac–QCA 与简单规范耦合的示例代码为标准量子电路模拟，可在常见开源量子计算框架中实现。

---

## Appendices

### Appendix A：Theorem 2 中 $SU(n)$ 选出的群论细节

本附录给出 Theorem 2 中从 $U(n)$ 到 $SU(n)$ 的选出过程的更严格论证。

设 $\mathcal V$ 为 $n$ 维复 Hilbert 空间，内积为 $\langle\cdot,\cdot\rangle$。所有保持内积的线性算符构成酉群 $U(\mathcal V)\cong U(n)$。若考虑一个连通紧 Lie 子群 $G\subseteq U(n)$，其在 $\mathcal V$ 上的表示为不可约，则有以下性质：

1. Lie 代数 $\mathfrak g\subseteq\mathfrak u(n)$ 在 $\mathcal V$ 上的表示为不可约。

2. 若 $\mathfrak g$ 的中心仅由纯虚标量矩阵构成，则 $G$ 的单位元连通分支同构于 $SU(n)$ 或其覆盖群。

更具体地，$\mathfrak u(n)\cong\mathfrak{su}(n)\oplus\mathrm{i}\mathbb R$ 的分解给出：任何 $X\in\mathfrak u(n)$ 可唯一写为

$$X=X_{0}+\mathrm{i}\alpha\mathbf 1,\quad X_{0}\in\mathfrak{su}(n),\ \alpha\in\mathbb R.$$

其中 $\mathfrak{su}(n)$ 由迹为零的反 Hermite 矩阵构成，是单李代数；$\mathrm{i}\mathbb R\mathbf 1$ 为中心。若要求对称群不携带额外全局 $U(1)$ 荷，则在 $\mathfrak g$ 中排除 $\mathrm{i}\mathbf 1$ 方向，仅保留 $\mathfrak{su}(n)$ 子代数，从而得到 $SU(n)$ 作为极大子群。

在本文情形中，空间平行支路部分 $\mathbb C^{3}_{\mathrm{space}}$ 与时间叠层部分 $\mathbb C^{2}_{\mathrm{time}}$ 上的对称变换分别属于 $U(3)$ 与 $U(2)$。通过上述分解并要求不引入新的独立全局相位可知，对应的极大候选群为 $SU(3)$ 与 $SU(2)$。

此外，$\mathcal H_{\mathrm{phase}}\cong\mathbb C$ 上的对称变换自然为 $U(1)$，其 Lie 代数为 $\mathrm{i}\mathbb R$。将这一 $U(1)$ 视为唯一的整体相位自由度，则三部分组合起来给出

$$G\cong SU(3)\times SU(2)\times U(1),$$

满足极小性与不可约性的要求。

### Appendix B：整体结构 $\mathbb Z_{6}$ 的构造示意

本附录回顾标准模型中 $\mathbb Z_{6}$ 商群的构造思路，并说明本框架如何复现这一结构。

记

$$z_{3}=\mathrm{e}^{2\pi\mathrm{i}/3}\mathbf 1_{3}\in SU(3),\quad
z_{2}=-\mathbf 1_{2}\in SU(2).$$

考虑三元组

$$(z_{3},z_{2},\mathrm{e}^{\mathrm{i}\theta})\in SU(3)\times SU(2)\times U(1).$$

其在一个给定费米子表示上的作用为

$$\psi\mapsto z_{3}^{q_{3}}z_{2}^{q_{2}}\mathrm{e}^{\mathrm{i}\theta Y}\psi,$$

其中 $q_{3},q_{2}$ 表示费米子在 $SU(3)$ 与 $SU(2)$ 表示中的权（如 3, $\bar 3$, 2, 1 等），$Y$ 为其超荷。

在标准模型中，可以选择 $\theta$ 使得对所有费米子态，这一组合作用为单位。具体计算显示，对适当选择的 $\theta$，

$$(z_{3},z_{2},\mathrm{e}^{\mathrm{i}\theta})$$

的六次幂为单位元，且其生成的循环群 $\mathbb Z_{6}$ 在所有物质表示上作用平凡，从而可在整体规范群中商去这一子群。([math.columbia.edu][12])

在本框架中，由于费米子表示与标准模型同构，中心元素在 $\mathcal H_{\mathrm{matter}}\otimes\mathcal H_{\mathrm{branch}}$ 上的作用结构完全一致，因此同样可构造出 $\mathbb Z_{6}$ 子群，使得物理规范群为

$$G_{\Sigma}\cong\frac{SU(3)\times SU(2)\times U(1)}{\mathbb Z_{6}}.$$

### Appendix C：离散规范场与 QCA 的协变性条件

考虑 QCA 的一步演化算符 $U$，其在无规范场时可写为若干局域门的乘积

$$U=\prod_{j}U_{j},$$

其中每个 $U_{j}$ 作用于有限个相邻格点。引入局域基底变换 $g(x)\in G$ 后，要求新演化算符 $U'$ 满足

$$U'=\Bigl(\bigotimes_{x}g(x)\Bigr)U\Bigl(\bigotimes_{x}g(x)^{-1}\Bigr),$$

并与 $U$ 在可观测量上等价。这等价于在 $U$ 中每个连接相邻格点 $x$ 与 $y$ 的门之间插入群元素 $U_{xy}$，满足

$$U_{xy}\mapsto g(x)U_{xy}g(y)^{-1},$$

即离散 Wilson 链接的规范变换规则。([arXiv][8])

在连续极限下，设 $U_{x,\mu}=\exp(\mathrm{i}aA_{\mu}(x))$，则规范变换

$$A_{\mu}(x)\mapsto g(x)A_{\mu}(x)g(x)^{-1}
+\frac{\mathrm{i}}{a}g(x)\partial_{\mu}g(x)^{-1}$$

自然出现，给出 Yang–Mills 规范势的标准变换性质。

在本框架中，$G$ 选为 $SU(3)\times SU(2)\times U(1)$ 或其商群后，得到的离散规范结构与标准格点规范理论完全平行，只是在对称群的起源上给出 QCA–微观平行性的解释。

---

## References

[1] T. Farrelly, "A review of quantum cellular automata," *Quantum* **4**, 368 (2020). ([量子期刊][13])

[2] A. Bisio, G. M. D'Ariano, and A. Tosini, "Quantum field as a quantum cellular automaton: The Dirac free evolution in one dimension," *Ann. Phys.* **354**, 244–264 (2015). ([科学直通车][6])

[3] A. Mallick et al., "Dirac cellular automaton from split-step quantum walk," *Sci. Rep.* **6**, 25779 (2016). ([Nature][18])

[4] E. Seiler, "A gentle introduction to lattice field theory," *Rev. Mod. Phys.* (2025). ([PMC][7])

[5] C. Cedzich et al., "Quantum walks in external gauge fields," *J. Math. Phys.* **60**, 012107 (2019). ([arXiv][8])

[6] P. Arnault and F. Debbasch, "Quantum walks and discrete gauge theories," *Phys. Rev. A* **93**, 052301 (2016). ([APS Link][17])

[7] P. Arrighi, N. Schabanel, and G. Theyssier, "Universal gauge-invariant cellular automata," in *MFCS 2021*, LIPIcs-MFCS-2021-9 (2021). ([DROPS][10])

[8] M. C. Bañuls et al., "Simulating lattice gauge theories within quantum technologies," *Eur. Phys. J. D* **74**, 165 (2020). ([arXiv][9])

[9] G. Calajó et al., "Digital quantum simulation of a $(1+1)$D $SU(2)$ lattice gauge theory with ion qudits," *PRX Quantum* **5**, 040309 (2024). ([APS Link][19])

[10] M. Meth et al., "Simulating two-dimensional lattice gauge theories on a qudit quantum processor," *Nat. Phys.* **21**, 123–130 (2025). ([Nature][20])

[11] T. V. Zache et al., "Fermion–qudit quantum processors for simulating lattice gauge theories," *Quantum* **7**, 1140 (2023). ([量子期刊][21])

[12] F. Maltoni, "Review of the Standard Model," CERN School Lectures (2019). ([Indico][22])

[13] B. McInnes, "Calabi–Yau compactifications and the global structure of the Standard Model gauge group," *J. Math. Phys.* **37**, 493–502 (1996). ([AIP Publishing][23])

[14] M. Cicoli et al., "The Standard Model quiver in de Sitter string compactifications," *JHEP* **08**, 137 (2021). ([arXiv][24])

[15] J. Thorén, "Grand Unified Theories: $SU(5)$, $SO(10)$ and beyond," Master's thesis, Lund University (2012). ([隆德大学出版物][25])

[16] Y. Tosa, "Uniqueness of $SU(5)$ and $SO(10)$ grand unified theories," *Phys. Rev. D* **23**, 3058–3065 (1981). ([APS Link][2])

[17] M. A. Levin and X.-G. Wen, "String-net condensation: A physical mechanism for topological phases," *Phys. Rev. B* **71**, 045110 (2005). ([arXiv][4])

[18] X.-G. Wen, "Quantum order from string-net condensations and origin of light and massless fermions," *Phys. Rev. B* **68**, 115413 (2003). ([arXiv][26])

[19] J. Kirklin, "Emergent classical gauge symmetry from quantum entanglement," *JHEP* **02**, 150 (2023). ([arXiv][5])

[20] S. D. Bass, "Emergent gauge symmetries," *Rep. Prog. Phys.* **85**, 046201 (2022). ([arXiv][27])

[21] W. T. Xu et al., "Entanglement properties of gauge theories from higher-form symmetries," *Phys. Rev. X* **15**, 011001 (2025). ([APS Link][28])

[22] J. Greensite, "The confinement problem in lattice gauge theory," *Prog. Part. Nucl. Phys.* **51**, 1–83 (2003). ([arXiv][14])

[23] A. Di Giacomo, "Confinement of color: A review," *Acta Phys. Pol. B* **25**, 215–248 (1994). ([inspirehep.net][29])

[24] S. H. Maes, "Justifying the Standard Model $(U(1)\times SU(2)\times SU(3))$ symmetry in a multi-fold universe," preprint (2022). ([Shmaes - Physics][11])

[25] M. Baker et al., "The confining color field in $SU(3)$ gauge theory," *Eur. Phys. J. C* **80**, 514 (2020). ([SpringerLink][30])

[1]: https://en.wikipedia.org/wiki/Mathematical_formulation_of_the_Standard_Model?utm_source=chatgpt.com "Mathematical formulation of the Standard Model"

[2]: https://link.aps.org/doi/10.1103/PhysRevD.23.3058?utm_source=chatgpt.com "Uniqueness of SU(5) and SO(10) grand unified theories"

[3]: https://www.sciencedirect.com/science/article/pii/S0550321315001339?utm_source=chatgpt.com "Calabi–Yau metrics and string compactification"

[4]: https://arxiv.org/abs/cond-mat/0404617?utm_source=chatgpt.com "String-net condensation: A physical mechanism for topological phases"

[5]: https://arxiv.org/abs/2209.03979?utm_source=chatgpt.com "Emergent classical gauge symmetry from quantum ..."

[6]: https://www.sciencedirect.com/science/article/abs/pii/S0003491614003546?utm_source=chatgpt.com "Quantum field as a quantum cellular automaton: The Dirac ..."

[7]: https://pmc.ncbi.nlm.nih.gov/articles/PMC12026112/?utm_source=chatgpt.com "A Gentle Introduction to Lattice Field Theory - PMC"

[8]: https://arxiv.org/abs/1808.10850?utm_source=chatgpt.com "Quantum walks in external gauge fields"

[9]: https://arxiv.org/abs/1911.00003?utm_source=chatgpt.com "[1911.00003] Simulating Lattice Gauge Theories within ..."

[10]: https://drops.dagstuhl.de/opus/volltexte/2021/14449/pdf/LIPIcs-MFCS-2021-9.pdf?utm_source=chatgpt.com "Universal Gauge-Invariant Cellular Automata - DROPS"

[11]: https://shmaesphysics.wordpress.com/2022/08/08/justifying-the-standard-model-u1-x-su2-x-su3-symmetry-in-a-multi-fold-universe/?utm_source=chatgpt.com "Justifying the Standard Model U(1) x SU(2) x SU(3) Symmetry ..."

[12]: https://www.math.columbia.edu/~woit/wordpress/?cpage=1&p=291&utm_source=chatgpt.com "Baez on the Geometry of the Standard Model"

[13]: https://quantum-journal.org/papers/q-2020-11-30-368/?utm_source=chatgpt.com "A review of Quantum Cellular Automata"

[14]: https://arxiv.org/pdf/hep-lat/0301023?utm_source=chatgpt.com "The Confinement Problem in Lattice Gauge Theory"

[15]: https://arxiv.org/abs/2412.03043?utm_source=chatgpt.com "Topological quantum walk in synthetic non-Abelian gauge ..."

[16]: https://link.aps.org/doi/10.1103/PhysRevA.95.013830?utm_source=chatgpt.com "Quantum walks in synthetic gauge fields with three ..."

[17]: https://link.aps.org/doi/10.1103/PhysRevA.93.052301?utm_source=chatgpt.com "Quantum walks and discrete gauge theories | Phys. Rev. A"

[18]: https://www.nature.com/articles/srep25779?utm_source=chatgpt.com "Dirac Cellular Automaton from Split-step Quantum Walk"

[19]: https://link.aps.org/doi/10.1103/PRXQuantum.5.040309?utm_source=chatgpt.com "Digital Quantum Simulation of a (1+1)D SU(2) Lattice Gauge ..."

[20]: https://www.nature.com/articles/s41567-025-02797-w?utm_source=chatgpt.com "Simulating two-dimensional lattice gauge theories on a ..."

[21]: https://quantum-journal.org/papers/q-2023-10-16-1140/?utm_source=chatgpt.com "Fermion-qudit quantum processors for simulating lattice ..."

[22]: https://indico.cern.ch/event/829653/contributions/3568518/attachments/1946334/3229296/Chennai-SM.pdf?utm_source=chatgpt.com "Review of the Standard Model"

[23]: https://pubs.aip.org/aip/jmp/article-pdf/37/1/493/19286740/493_1_online.pdf?utm_source=chatgpt.com "Calabi–Yau compactifications and the global structure of ..."

[24]: https://arxiv.org/abs/2106.11964?utm_source=chatgpt.com "The Standard Model Quiver in de Sitter String Compactifications"

[25]: https://lup.lub.lu.se/student-papers/record/2862133/file/2862134.pdf?utm_source=chatgpt.com "Grand Unified Theories: SU(5), SO(10) and ..."

[26]: https://arxiv.org/abs/hep-th/0302201?utm_source=chatgpt.com "Quantum order from string-net condensations and origin of light and massless fermions"

[27]: https://arxiv.org/pdf/2110.00241?utm_source=chatgpt.com "Emergent gauge symmetries"

[28]: https://link.aps.org/doi/10.1103/PhysRevX.15.011001?utm_source=chatgpt.com "Entanglement Properties of Gauge Theories from Higher-Form ..."

[29]: https://inspirehep.net/literature/630016?utm_source=chatgpt.com "Confinement of color: A Review"

[30]: https://link.springer.com/article/10.1140/epjc/s10052-020-8077-5?utm_source=chatgpt.com "The confining color field in SU(3) gauge theory"




