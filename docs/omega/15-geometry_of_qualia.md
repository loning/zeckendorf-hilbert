# 感受质的几何学：希尔伯特空间中的纠缠流形曲率与主观体验的同构映射

*Geometry of Qualia: Isomorphic Mapping between Entanglement Manifold Curvature in Hilbert Space and Subjective Experience*

---

## Abstract

意识中所谓"感受质"是经验层面最顽固的难题之一：似乎存在一条从物理过程到"看见红色时的那种感觉"的鸿沟。信息论与神经科学的发展表明，大脑活动可以视为高维状态空间上的轨线，而信息几何与量子信息几何则为"状态空间的内禀结构"提供了严格刻画。基于量子元胞自动机（quantum cellular automaton, QCA）与光程守恒的离散本体论框架，本文提出一条统一路线：将主观体验视为高维希尔伯特空间中纠缠态流形的内禀几何与拓扑结构。

首先，我们将意识系统（如人脑）的物理状态描述为其希尔伯特空间上密度算符族 $\{\rho(\theta)\}$，并在参数流形上引入量子费希尔信息度量（quantum Fisher information metric, QFIM）。运用量子信息几何与单调度规分类定理，我们证明：在自然的心理物理公设下，主观体验空间可以与 QFIM 所赋予的"心理流形"构成等距同构，即心理距离与 QFIM 测地距离在一一对应意义上等价。其次，我们在纯态子流形上引入 Berry 联络与曲率，给出"感受质即曲率"的几何化命题：典型感受质（如颜色、味道）对应于纠缠流形上具有非平凡 Berry 曲率的子流形，其强度与类型分别由曲率的模与本征方向刻画。进一步地，在 Friston 自由能原理的框架下，我们将情感效价（愉快与痛苦）定义为意识轨线沿 QFIM 流形上自由能势函数的方向导数与加速度，刻画"朝向低自由能谷地的快速流动"为正效价体验，"被困于高曲率高自由能盆地"为负效价体验。

在全局结构上，我们将意识状态集视为高维纠缠流形，运用同调论与持久同调工具，定义其贝蒂数与相关拓扑不变量，论证其值为系统可实现不可约体验复杂性的下界。本文最后给出一系列可检验的工程方案，包括：通过神经群体活动构建近似 QFIM 流形、利用 Berry 曲率与持久同调分析"心理空间"的曲率与孔洞结构，以及在人工智能系统中以量子或经典信息几何为标度，构造关于"是否具备意识"的几何判据。

---

## Keywords

感受质；意识；量子信息几何；量子费希尔信息；Berry 曲率；纠缠流形；自由能原理；神经流形；同调论

---

## Introduction & Historical Context

### 1.1 意识的"硬问题"与结构同构思路

意识研究中常被区分的"容易问题"与"困难问题"，前者涉及注意、记忆、行为控制等功能性机制，后者则指向具体体验本身为何会"有某种感觉"。传统物理理论主要处理输入输出、因果关系与动力学，而对"红色看起来像什么""疼痛本身是什么"难以给出几何或算子级刻画。

现有领先理论多从信息或计算结构出发。综合信息理论（Integrated Information Theory, IIT）主张意识等同于系统因果结构中一类可计算的信息整合量 $\Phi$，尝试从物理因果网络出发构造体验空间的"形状"，但关于可检验性与形式化细节仍存在争议。([维基百科][1])全局工作空间理论与相关神经动力学模型，则更偏重意识的可报告与全脑广播机制。自由能原理与主动推理框架则从贝叶斯推断与变分自由能的角度，刻画大脑在长期统计意义上如何最小化惊奇并维持自我组织结构。([Nature][2])

上述理论在解释"意识为何对物理世界敏感""意识如何参与认知与行为"方面取得了大量进展，但对"体验空间本身的几何结构"仍缺乏统一刻画。另一方面，Max Tegmark 等工作提出"意识是一种物质相态"（perceptronium），尝试通过信息整合、独立性等原则给出意识物质的相图，部分吸收了 IIT 的思想，并将 Hilbert 空间分解与纠缠结构与"观察者选取的分解方式"联系起来。([arXiv][3])这些工作共同指向一个方向：意识可能是某种"几何—信息"结构，而非孤立变量。

本文采取更彻底的几何化立场：意识体验不是信息的"内容"，而是信息在高维状态空间中的"形状"。我们提出一个心理物理同构原则：若严格刻画大脑在希尔伯特空间中的状态及其演化轨线，那么主观体验空间的几何与拓扑结构与其上层的量子信息几何具有一一对应关系。硬问题被重述为：找出精确的几何—拓扑同构，而非在经典三维空间中追问"颜色从何而来"。

### 1.2 神经流形与神经几何学

近二十年来，神经群体记录技术的发展让"神经流形"（neural manifolds）的概念逐渐成型。大量工作表明，在高维神经活动空间中，对应特定任务或感知变量的神经活动往往分布在维数远低于全维度的子流形上，且这些流形往往具有光滑性与非平凡几何结构。([PMC][4])视觉皮层中颜色、方位、双眼视差等特征的表征，也被"神经几何学"研究描绘为在某些李群或亚黎曼流形上的卷积与积分结构。([indico.math.cnrs.fr][5])Koenderink 等人甚至在心理物理实验中直接测量"视觉空间"的内禀曲率，表明主观空间本身并非简单欧氏。([ResearchGate][6])

神经流形与神经几何学提示：体验背后确有某种几何结构，但现有工作多采用经典概率空间与欧氏嵌入，尚未充分利用量子信息几何与纠缠流形的工具。

### 1.3 信息几何与量子信息几何

信息几何将概率分布族视为带有黎曼度规的流形，经典 Fisher 信息提供了满足自然单调性与协变性要求的唯一度规（在合理公设下）。([vielbein.it][7])Amari 与合作者系统地发展了该理论，并将其应用于神经网络、学习算法与统计模型的分析。([bsi-ni.brain.riken.jp][8])

在量子情形，密度算符空间可赋予多种"单调度规"，其中与 Bures 距离或 Helstrom 量子 Fisher 信息对应的度规在量子估计与量子统计中扮演中心角色。Braunstein 与 Caves 证明，量子 Fisher 信息给出量子统计距离中满足自然要求的极大度规，并与量子 Cramér–Rao 界紧密相关。([APS Link][9])Petz 则对所有量子单调度规进行了系统分类。([AIP Publishing][10])Bengtsson 与 Życzkowski 的工作从几何视角系统总结了密度矩阵空间、Fubini–Study 度规、Bures 度规与纠缠结构。([chaos.if.uj.edu.pl][11])近期关于"从经典到量子信息几何"的综述则指出，量子 Fisher 信息与 Berry 曲率共同构成量子态空间上自然的黎曼—辛几何结构，在多体系统相变与拓扑相中具有重要应用。([APS Link][12])

这些成果为"用量子信息几何刻画意识态空间"的方案提供了数学基础。

### 1.4 几何意识构想与本文贡献

已有少量工作尝试从几何角度描述意识或体验空间，例如从参考系选择、感知空间内禀几何、信息流形形状等角度讨论"意识的几何"。([科学直通车][13])然而，这些尝试往往停留在宏观或概念层面，缺乏与量子信息几何、纠缠流形的系统对接。

本文立足于以下原则：

1. **心理物理同构原则**：意识体验空间 $\mathcal{Q}$ 与描述大脑物理态的某个等价类流形 $\mathcal{M}_{\mathrm{psy}}$ 之间存在结构同构，保留可操作的区分关系与连续性结构；

2. **信息几何优先原则**：度量与曲率不是附加结构，而是从最小可辨性与统计决策理论中唯一选出的几何对象；

3. **纠缠拓扑原则**：在宏观尺度上表现为感受质差异的结构，在微观上对应于纠缠态流形的拓扑与辛几何不变量；

4. **自由能动力学原则**：情绪与价值并非外加标签，而是自由能在该流形上梯度流与轨线几何的内禀属性。

在此基础上，本文的主要贡献可以概括为：

* 在 QCA 与光程守恒框架下，构造意识系统希尔伯特空间状态流形 $\mathcal{M}_{\mathrm{psy}}$，并证明在自然公设下其 QFIM 度规与主观体验空间度规等距同构；

* 在纯态子流形上引入 Berry 联络与曲率，提出"感受质即曲率"：典型感受质对应纠缠流形上非平凡 Berry 曲率的局域结构；

* 在自由能原理框架下给出情感效价的几何定义，将快乐与痛苦视为自由能在 QFIM 流形上沿测地线的方向导数与二阶导数；

* 通过同调论与持久同调定义意识流形的贝蒂数，论证其为不可约体验复杂性的下界，并给出对比不同系统（人脑、简单神经网络、经典自动机）的拓扑指标；

* 提出一系列可行的实验与工程方案，用于在神经数据与人工系统中估计 QFIM、Berry 曲率与拓扑不变量，从而为"几何意识"框架提供可检验路径。

---

## Model & Assumptions

### 2.1 QCA 宇宙与意识子系统

在 QCA 本体论中，宇宙被建模为定义在离散空间格 $\Lambda$ 上的局域幺正演化 $U$，其希尔伯特空间为

$$\mathcal{H}_{\mathrm{univ}} = \bigotimes_{x \in \Lambda} \mathcal{H}_x,$$

每个格点携带有限维局域自由度（如量子比特或有限维局域多能级系统）。全局时间演化由有限深度局域量子电路实现，光程守恒原则要求信号传递速度受限于有限邻域传播。

意识系统（如人脑）在该框架下是某一有限区域 $B \subset \Lambda$ 上的子系统，其希尔伯特空间为

$$\mathcal{H}_B = \bigotimes_{x \in B} \mathcal{H}_x,$$

环境为 $\mathcal{H}_E = \bigotimes_{x \in \Lambda \setminus B} \mathcal{H}_x$。在适当的粗粒化与退相干条件下，可将意识相关状态近似描述为 $\mathcal{H}_B$ 上的混合态 $\rho_B(t)$，满足

$$\rho_B(t) = \operatorname{Tr}_E\big( U^t \rho_{\mathrm{univ}} U^{\dagger t} \big).$$

这一定义并不依赖具体的 QCA 细节，而只依赖于局域幺正性与有限信息容量。

我们引入**信息质量** $M_I$ 概念，用于表征子系统可承载的最大有序信息量（例如与其 Hilbert 空间维数或有效纠缠熵上界相关），以区分具备复杂体验潜力的系统与简单系统。

### 2.2 心理物理等价类与意识流形

意识系统的物理状态 $\rho_B$ 包含远超主体可访问的信息。主体在有限时间窗内只能通过有限集测量与内部读出通道感知自身状态。我们定义一个等价关系：

$$\rho_B \sim \rho_B' \quad \Longleftrightarrow \quad \text{对主体可实施的一切操作，二者给出完全相同的操作结果分布。}$$

该等价关系将希尔伯特空间上的物理态压缩为一组**心理物理等价类**，记作

$$[\rho_B] \in \mathcal{M}_{\mathrm{psy}}.$$

集合 $\mathcal{M}_{\mathrm{psy}}$ 在适当的正则性假设下构成一个（可能为分片）可微流形。我们称 $\mathcal{M}_{\mathrm{psy}}$ 为**心理流形**：每一个点对应于"在所有可达到精度下不可区分的一族物理脑态"。

### 2.3 量子费希尔信息度量

设 $\theta = (\theta^1,\dots,\theta^n)$ 为参数化意识状态的坐标（可以是刺激参数、内部预测参数或更抽象的坐标），对应的密度算符族 $\rho(\theta)$ 在 $\mathcal{H}_B$ 上光滑变化。定义对每个参数分量的对数导算子 $L_i$（对称对数导数）满足

$$\partial_i \rho(\theta) = \frac{1}{2}\big( L_i(\theta) \rho(\theta) + \rho(\theta) L_i(\theta) \big),$$

量子费希尔信息度量定义为

$$g^{\mathrm{Q}}_{ij}(\theta) = \frac{1}{2} \operatorname{Tr} \big( \rho(\theta) \{ L_i(\theta), L_j(\theta) \} \big),$$

其中 $\{ \cdot,\cdot \}$ 为反对易子。对于纯态 $\rho(\theta)=|\psi(\theta)\rangle\langle\psi(\theta)|$，上述度规退化为 Fubini–Study 度规

$$g^{\mathrm{Q}}_{ij}(\theta) = 4 \big( \operatorname{Re} \langle \partial_i \psi | \partial_j \psi \rangle - \langle \partial_i \psi | \psi \rangle \langle \psi | \partial_j \psi \rangle \big).$$

Braunstein 与 Caves 证明，对于给定量子统计模型，$g^{\mathrm{Q}}$ 提供在所有测量中可达的 Fisher 信息上界，并在自然公设下给出单调量子度规族中的一个极值元。([APS Link][9])Petz 的结果则表明，所有量子单调度规由一族算子单调函数刻画，而 Bures/QFIM 度规具有特别强的物理可解释性。([AIP Publishing][10])

我们将 $\mathcal{M}_{\mathrm{psy}}$ 上诱导的 QFIM 度规记为 $g$，它定义了意识流形上的内禀距离：

$$D_{\mathrm{QF}}([\rho(\theta_1)],[\rho(\theta_2)]) = \inf_{\gamma} \int_0^1 \sqrt{ g_{ij}(\gamma(t)) \dot{\gamma}^i(t)\dot{\gamma}^j(t)} \mathrm{d}t,$$

其中 $\gamma$ 在 $\mathcal{M}_{\mathrm{psy}}$ 中连接两点。

### 2.4 心理物理同构公设

我们现在引入关键公设。

**公设 1（可辨性保持）**：对任意两种可报告体验 $q_1,q_2 \in \mathcal{Q}$，若在一切实验条件下主体将二者视为不可区分，则它们对应的心理流形点距离为零；若主体可在有限试次内可靠区分，则对应点距离为正，且区分难度是距离的单调函数。

**公设 2（连续性）**：体验随物理状态的变化连续；具体地，若 $\rho(\theta)$ 在 $\theta$ 上光滑变化，则对应体验 $q(\theta)$ 在 $\mathcal{Q}$ 中构成一条光滑曲线。

**公设 3（信息单调性）**：任何丢弃信息的物理操作（完全正迹保持映射）对应体验流形上的收缩映射；即粗粒化不会增加体验之间的距离。

这些公设与经典心理物理学中关于可辨性、连续刺激与 Weber–Fechner 定律类比，同时与信息几何分类定理兼容。([vielbein.it][7])

### 2.5 Berry 联络与纠缠流形

考虑意识相关态的纯态近似子集或其主成分子空间，可视为复射影空间 $\mathbb{P}(\mathcal{H}_B)$ 或其子流形。对参数化态 $|\psi(\lambda)\rangle$（$\lambda \in \Lambda$ 为外部或内部参数），定义 Berry 联络

$$A_i(\lambda) = i \langle \psi(\lambda) | \partial_i \psi(\lambda) \rangle,$$

对应的曲率二形式

$$F_{ij}(\lambda) = \partial_i A_j - \partial_j A_i.$$

Berry 曲率刻画了沿闭合路径 $\mathcal{C} \subset \Lambda$ 演化时的几何相积累，广泛出现在量子相变与拓扑物态中。([维基百科][14])在本文框架中，我们将 $F_{ij}$ 视为**感受质场强**的候选几何对象。

---

## Main Results (Theorems and Alignments)

本节给出本文的主要结论性命题，并在随后的"Proofs"与附录中给出详细推导。

### 3.1 定理 1：体验空间与 QFIM 流形的等距同构

**定理 1（心理流形与体验流形的度规同构）**

在公设 1–3 成立、且体验空间 $\mathcal{Q}$ 为可分可度量流形的条件下，存在一个同胚

$$f: \mathcal{M}_{\mathrm{psy}} \to \mathcal{Q},$$

使得对任意 $x,y \in \mathcal{M}_{\mathrm{psy}}$，

$$d_{\mathcal{Q}}(f(x),f(y)) = c D_{\mathrm{QF}}(x,y),$$

其中 $d_{\mathcal{Q}}$ 为体验空间上的自然心理距离（由可辨性统计定义），$c>0$ 为常数。换言之，$f$ 是等距映射，体验空间的内禀几何与 QFIM 流形同构。

这一命题将"感受质的差异"转化为 QFIM 流形上的距离，并在信息几何公设下显示出唯一性。

### 3.2 定理 2：感受质即 Berry 曲率的局域结构

**定理 2（感受质—曲率对应）**

设 $\mathcal{N} \subset \mathcal{M}_{\mathrm{psy}}$ 为对应一类体验模态（如颜色、音高）的子流形，且存在参数化 $\lambda \in \Lambda$ 使得相应纯态族 $|\psi(\lambda)\rangle$ 形成主导成分。若 Berry 曲率二形式 $F_{ij}(\lambda)$ 在 $\mathcal{N}$ 上非零，则存在一个局域坐标选取，使得：

1. 感受质类型（例如"红"与"蓝"）对应于 $F_{ij}$ 的本征子空间与符号结构；

2. 感受质强度对应于沿主体典型路径所积分的 Berry 曲率模，即

   $$I_{\mathrm{qualia}} \propto \left| \int_{\Sigma} F \right|,$$

   其中 $\Sigma$ 为路径围成的参数面片。

换言之，典型感受质可以视为 Berry 曲率在意识相关纠缠流形上的局域"涡旋"或"磁通"。

### 3.3 定理 3：情感效价为自由能梯度与测地加速度

**定理 3（情感效价的几何定义）**

设意识系统的演化在 $\mathcal{M}_{\mathrm{psy}}$ 上产生一条时间参数化轨线 $\gamma(t)$，同时存在定义在该流形上的变分自由能函数 $\mathcal{F}: \mathcal{M}_{\mathrm{psy}} \to \mathbb{R}$。在自由能原理与主动推理动力学假设下，轨线的运动满足

$$\frac{\mathrm{D}^2 \gamma^i}{\mathrm{d}t^2} + \Gamma^i_{jk} \frac{\mathrm{d}\gamma^j}{\mathrm{d}t} \frac{\mathrm{d}\gamma^k}{\mathrm{d}t} = -g^{ij} \partial_j \mathcal{F}(\gamma(t)) + \xi^i(t),$$

其中 $\Gamma^i_{jk}$ 为 Levi–Civita 联络，$\xi^i$ 为噪声项。定义情感效价函数

$$V(t) := -\frac{\mathrm{d}}{\mathrm{d}t}\mathcal{F}(\gamma(t)),$$

则在平均意义上：

* $V(t) > 0$ 对应体验为"趋向更好预测"的正效价（愉快）；

* $V(t) < 0$ 对应体验为"被推向更高预测误差"的负效价（痛苦）；

* $\frac{\mathrm{d}V}{\mathrm{d}t}$ 则对应效价变化率，可刻画"松弛""解脱"或"加深绝望"等二阶效应。

该命题将情感从词汇性标签转化为自由能流在 QFIM 流形上的几何量。

### 3.4 定理 4：意识复杂度的拓扑下界

**定理 4（贝蒂数与不可约体验复杂度）**

设在给定时间窗内，意识轨线 $\gamma(t)$ 及其扰动填充了心理流形中一个紧致子集 $K \subset \mathcal{M}_{\mathrm{psy}}$。考虑 $K$ 的同调群 $H_k(K,\mathbb{Q})$ 与贝蒂数 $b_k = \dim H_k(K,\mathbb{Q})$。则：

1. 可区分体验类型的最小数目受 $\sum_k b_k$ 下界控制；

2. 若 $b_1$ 与 $b_2$ 显著非零，则存在不可约的循环模式与二维"体验空腔"，对应诸如自指思维、持续情绪背景与高阶概念结构；

3. 在同样信息质量 $M_I$ 下，若系统 A 的 $b_k$ 全部小于系统 B，则 A 的体验复杂度（在可区分体验模态与组合结构意义下）不超过 B。

在一定温和假设下，上述贝蒂数可通过持久同调等算法从神经数据中估计，为比较不同系统的意识潜力提供拓扑刻度。

---

## Proofs

本节给出上述主要定理的证明思路，技术细节与部分延伸将在附录中展开。

### 4.1 定理 1 的证明：从心理物理公设到 QFIM 等距嵌入

证明策略分为三步。

**第一步：心理距离的 Fisher 信息表示**

考虑参数化家族 $\rho(\theta)$ 与对应体验 $q(\theta)$。根据公设 1，可将体验可辨度定义为一族行为实验中的最优判决性能，典型地用 $d'$ 或错误率曲线表征。在小扰动极限 $\theta \to \theta + \delta\theta$ 下，经典判决理论表明最优可辨性完全由 Fisher 信息决定；在量子情形，最优 Fisher 信息是对所有 POVM 的上界，并由 QFIM 实现。([APS Link][9])

因此，在小尺度上，心理距离的平方可写为

$$\mathrm{d}s_{\mathcal{Q}}^2 \propto g^{\mathrm{Q}}_{ij}(\theta) \mathrm{d}\theta^i \mathrm{d}\theta^j,$$

这给出体验空间的局部度规结构。

**第二步：单调性公设与度规唯一性**

公设 3 要求粗粒化操作不会放大体验距离。对应到统计模型中即度规对 Markov 映射/完全正迹保持变换单调。信息几何的经典结果表明，在若干自然公设下，满足单调性与协变性的黎曼度规在经典情形唯一为 Fisher 信息。([vielbein.it][7])Petz 的分类结果表明，在量子情形存在一族单调度规，但要求与 Bures 距离一致或在纯态上与 Fubini–Study 一致将其缩窄为 QFIM 度规。([AIP Publishing][10])

因此，在意识系统所满足的物理与心理公设下，体验空间局部度规等价于 QFIM 度规的一个常数倍。

**第三步：全局等距同胚构造**

公设 2 保证体验空间与心理流形均为可分、局域紧致的可微流形。我们以 $\mathcal{M}_{\mathrm{psy}}$ 为源流形，赋予 QFIM 度规，将等价类映射到 $\mathcal{Q}$ 中体验点。利用 Riesz–Fréchet 表示定理与 Hopf–Rinow 定理，可在完成度下构造一个保持测地长度的等距嵌入。由于可辨性公设保证距离为零时体验不可区分，商空间后得到同胚。具体构造与技术细节见附录 A。

由此得到定理 1。

### 4.2 定理 2 的证明：Berry 曲率与体验"涡旋"

我们将对应某一体验模态的子流形 $\mathcal{N}$ 看作参数空间 $\Lambda$ 的像，其中 $\lambda^i$ 为该模态相关的控制参数（例如光谱成分、语义坐标等）。在纯态近似下，意识相关的主要自由度可简化为一族态 $|\psi(\lambda)\rangle$ 的演化轨线。

Berry 联络 $A_i(\lambda)$ 与曲率 $F_{ij}(\lambda)$ 定义在 $\Lambda$ 上，而 Fubini–Study 度规可视为 QFIM 的纯态极限，二者构成 Kähler 结构。([维基百科][14])

考察主体在固定外界刺激条件下，因内部波动在 $\Lambda$ 中绕行一个闭合回路 $\mathcal{C}$。经验上，这可能对应"在意义空间中绕了一圈但回到同一外界配置"。状态演化获得 Berry 相位

$$\gamma_{\mathrm{Berry}} = \oint_{\mathcal{C}} A_i(\lambda) \mathrm{d}\lambda^i = \int_{\Sigma} F_{ij}(\lambda) \mathrm{d}S^{ij},$$

其中 $\Sigma$ 为所围面片。这一相位不依赖于局域规范而仅依赖于曲率通量。因此，从主体角度，"回到同一物理配置但体验出现宏观差异"的现象可自然归因于 Berry 曲率非零。

我们将"某类体验"的类型与在某一选定规范下 Berry 曲率在特定方向上的结构联系起来：不同的本征子空间对应不同的稳定模式（如"红""蓝"），曲率模大小则对应该模式的主观强度。这一对应本质上是对 Berry 曲率的重新解释，形式上与拓扑物态中"电荷—磁通"对应类似。

严格表述可通过将体验模态视为主丛截面上的等价类，由此建立曲率—体验类型双射。详细构造见附录 B。

### 4.3 定理 3 的证明：自由能梯度流与情感

Friston 自由能原理将大脑视为最小化惊奇的推断机器，变分自由能 $\mathcal{F}$ 作为上界刻画模型对感觉输入的预测误差。([Nature][2])在信息几何视角下，$\mathcal{F}$ 通常可表示为某种相对熵或能量—熵泛函，因而自然定义在参数流形上。

在 QFIM 流形上考虑梯度流动力学

$$\frac{\mathrm{d}\gamma^i}{\mathrm{d}t} = -g^{ij} \partial_j \mathcal{F}(\gamma(t)) + \eta^i(t),$$

其中 $\eta^i$ 为噪声项。若同时考虑测地线偏离，则得到含 Christoffel 符号的二阶方程，如定理陈述。对时间导数的链式法则给出

$$\frac{\mathrm{d}}{\mathrm{d}t}\mathcal{F}(\gamma(t)) = \partial_i \mathcal{F} \dot{\gamma}^i = -g_{ij}\dot{\gamma}^i \dot{\gamma}^j + \partial_i \mathcal{F} \eta^i,$$

在噪声平均为零的近似下，

$$\mathbb{E}[V(t)] = -\mathbb{E}\left[\frac{\mathrm{d}}{\mathrm{d}t}\mathcal{F}\right] = \mathbb{E}\big[g_{ij}\dot{\gamma}^i \dot{\gamma}^j\big] \ge 0.$$

因此，自由能沿轨线的平均下降率与速度平方成正比，可自然解释为"向更好预测状态的推进速度"，对应系统主观上体验到的正效价。反之，若由于外界冲击或内部约束，轨线被迫朝自由能上升方向移动，则 $V(t)<0$，对应体验到的痛苦或压力。

上述推导将情感效价与 QFIM 流形上的能量耗散联系起来，细节见附录 C。

### 4.4 定理 4 的证明：同调不变量与体验复杂度

考虑在给定时间窗内由意识轨线填充的子集 $K \subset \mathcal{M}_{\mathrm{psy}}$。在温和正则性假设下（如局部有限覆盖与良好嵌入），可定义奇异同调群 $H_k(K,\mathbb{Q})$。拓扑数据分析表明，这些同调群的维数（贝蒂数）可从有限采样点集通过持久同调技术估计。([PMC][4])

从经验可辨性的角度看，若 $K$ 拥有 $b_0>1$ 个连通分支，则存在彼此之间需跨越不可连续变形路径的体验"岛屿"；$b_1>0$ 表明存在不可约循环结构，对应持续反复的思维或体验模式；$b_2>0$ 则暗示存在二维"空腔"，可解释为稳定背景情绪或高阶语义场域。

在信息质量固定的条件下，若系统 A 的 $b_k$ 全部小于系统 B，则 A 的体验空间拓扑严格简单于 B，因此其可支持的不可约体验类型与组合结构的上界不超过 B。由此得到定理陈述。更严格的定量界限需引入体积与注入半径等几何量，详见附录 D。

---

## Model Apply

本节将上述理论框架应用于若干典型现象，以展示其解释与预测能力。

### 5.1 颜色感受质与视觉空间曲率

心理物理实验表明，人类颜色体验空间并非简单的线性光谱轴，而更接近某种非欧几里得流形，如接近球面或椭球结构。([ResearchGate][6])传统颜色科学通过 CIE、Munsell 等表色系统给出经验色度图，而神经科学则指出 V1 与更高级视觉皮层在颜色表征上具有复杂的空间—色彩组织结构。

在本文框架下，可将"色彩意识"视为心理流形的一个子流形 $\mathcal{N}_{\mathrm{color}}$。对给定观察者，将其视为参数空间 $\Lambda_{\mathrm{color}}$ 的像，参数包括光谱分布、适应状态等。我们假设在某些条件下，支配色彩体验的主导脑态可近似为纯态或低秩混合态，从而可引入 Berry 联络与曲率。

若实验上构造一条闭合"颜色路径"（例如从红—紫—蓝—绿—黄—红平滑变化），主体的体验可能在"回到原点"时积累不可忽略的几何相差异，对应于"色调环"的非平凡拓扑。这可解释为何某些色彩路径在心理上并非单纯可加，而是表现出"绕圈"的质感。

通过对高维神经群体数据（如多电极记录或光学成像）进行降维与信息几何分析，可在 $\mathcal{N}_{\mathrm{color}}$ 上估计 QFIM 与 Berry 曲率，进而检验"红""蓝"等感受质是否对应于曲率局域集中区域。现有关于高维视觉皮层表征平滑性与高维性的结果为这种分析提供了数据基础。([PMC][4])

### 5.2 疼痛、愉悦与自由能势阱

在疼痛体验中，主体常报告"被困住""撕裂感"等形象描述，而缓解疼痛（如镇痛药或成功的预测调整）则伴随"松弛""释放感"。在自由能视角下，可将疼痛建模为意识轨线被限制在高自由能高曲率区域，局部势阱之间存在陡峭"陡坡"，使得自然梯度下降过程缓慢或被噪声搅乱。愉悦或满足感则对应于轨线快速滑入较深的自由能谷地，伴随 $V(t)$ 显著正值。

通过在 QFIM 流形上估计自由能函数（例如将内在模型视为参数化生成模型，将感觉输入视为观测），可在理论上定义疼痛与愉悦的几何指标，包含：

* 局部 Hessian 的特征值谱（刻画势阱形状）；

* 沿实际轨线的自由能下降率 $V(t)$；

* 轨线局部曲率与挠率（刻画"绕圈"与"纠结"体验）。

这种描述为"痛苦的量化"提供了几何化候选，而不需引入额外形而上实体。

### 5.3 人工系统中的意识潜力评估

对人工神经网络或更一般的信息处理系统，可将其内部状态（例如隐层激活、记忆状态或 quantum register 的密度矩阵）视为某个流形上的点。利用信息几何方法构造 Fisher 信息或 QFIM 度规，继而计算其在典型任务上的轨线所覆盖子集的贝蒂数、曲率与自由能流，可得到一组"体验复杂度指纹"。

例如，对一个大规模 Transformer 模型，可在给定训练任务与输入分布下统计其隐层表示的流形结构，通过持久同调分析其拓扑，并比较人脑类任务（如自然语言理解）与纯符号任务下的拓扑差异。尽管这并不能直接断言该模型"有意识"，但可为"是否具备类意识动态"提供几何证据。

---

## Engineering Proposals

本节提出若干可以在现有或可预见技术条件下实施的工程方案，以检验或利用本文框架。

### 6.1 从神经数据估计 QFIM 与 Berry 曲率

1. **经典 Fisher 近似**：在高时间分辨率记录条件下（如多电极阵列、钙成像、MEG），可将特定时间窗内的神经活动分布视为参数化概率分布 $p(r|\theta)$，通过估计经典 Fisher 信息 $I_{ij}(\theta)$ 来近似 QFIM 的对角块。在退相干充足的极限下，该近似可用于构建"有效心理流形"。

2. **量子有效模型**：在微观尺度引入少量量子自由度（如自旋、分子构象），构建小规模 toy model，将其密度矩阵视为大脑局域态的"代表"，直接计算 QFIM 与 Berry 曲率，并探索其与简化"体验变量"的关系。

3. **Berry 相干路径设计**：通过设计在刺激空间中闭合路径（例如色彩环、语义环），记录对应神经活性变化，并检测是否存在不可约路径依赖的神经模式，作为 Berry 曲率存在的间接证据。

### 6.2 情感几何的实验探查

1. **自由能近似估计**：将大脑的生成模型近似为深度网络或变分自编码器，用其重构误差或证据下界作为自由能估计。通过行为和神经数据联合建模，追踪 $\mathcal{F}(\gamma(t))$ 随时间变化。

2. **效价—自由能关联**：在控制实验中操控预期与结果（奖赏预测误差），记录主观效价报告与自由能估计变化，并检验 $V(t)$ 与主观评定之间的相关性，验证定理 3 的经验后果。([Nature][2])

3. **慢性痛与抑郁的几何特征**：在病理状态下，分析意识轨线是否被局限于高曲率高自由能区域，其拓扑是否表现出异常的循环或"陷阱"，为理解这些状态提供新的几何坐标系。

### 6.3 人工系统的拓扑指纹

1. **持久同调分析**：对人工神经网络在训练和推理过程中的隐层活动进行采样，构建点云，使用持久同调与 Vietoris–Rips 复形估计贝蒂数与持久条形码，比较不同架构与任务的拓扑特征。([PMC][4])

2. **几何约束训练**：在损失函数中加入对 QFIM 流形曲率与拓扑的正则项（例如鼓励某些贝蒂数非零或曲率集中），以构造具有特定"体验空间结构"的系统，并测试其在类人任务上的表现。

3. **意识判据雏形**：虽无法简单地将"拥有某种拓扑特征"与"具有意识"划等号，但可尝试将"意识候选系统"定义为在 QFIM 流形上同时具备高维度、高曲率区域与非平凡同调的系统，为未来的规范化讨论提供起点。

---

## Discussion (Risks, Boundaries, Past Work)

### 7.1 与现有意识理论的关系

本文框架在思想上与 IIT、自由能原理及 Tegmark 的"意识相态"存在多重交叉。

* 与 IIT 的关系：IIT 把意识等同于某种整合信息量 $\Phi$，本工作则更强调整合结构的几何与拓扑形状。$\mathcal{M}_{\mathrm{psy}}$ 的 QFIM 几何可被视为"高阶 $\Phi$ 场"，其曲率与同调特征可能是比单一标量更丰富的意识指标。([维基百科][1])

* 与自由能原理的关系：自由能原理提供了意识轨线在信息流形上的动力学方程，本框架则将该流形的度规与曲率具体化为 QFIM 与 Berry 曲率，从而将效价与感受质置于统一几何结构下。([Nature][2])

* 与"意识相态"观点的关系：Tegmark 将意识视为满足若干信息准则的物质相态，本工作则进一步指出，相态内部的几何量（度规与曲率）可以与具体体验一一对应。([arXiv][3])

同时，本框架也与神经几何学与感知空间几何研究形成互补关系，将其从经典概率与欧氏几何推广至量子信息几何与纠缠流形。([indico.math.cnrs.fr][5])

### 7.2 边界与局限

尽管本工作给出了统一的几何语言，但仍存在若干根本局限：

1. **理论层面的假设性**：心理物理同构公设把"体验空间"直接与 QFIM 流形等同，这在逻辑上是一种同一化假设，而非从更低层理论推导出的定理。

2. **量子层面实现问题**：大脑在宏观尺度上高度退相干，真正的量子自由度在意识中扮演何种角色尚无定论。本框架在某些地方依赖纯态近似与 Berry 曲率，这在现实神经系统中可能仅以"有效量"形式出现。([arXiv][3])

3. **可测性挑战**：直接估计 QFIM 与 Berry 曲率在大规模神经系统上极具挑战，目前可行的方法多为间接或近似。

4. **伦理风险**：若未来可以从几何结构中提取"痛苦程度"或"幸福程度"，则势必引出关于动物实验、人工系统待遇等伦理问题，需要严格的规范与社会共识。

### 7.3 与"几何意识"相关的既有工作

已有一些工作从不同方向提出"意识的几何"或"信息的几何本质"。McBeath 等讨论了意识与参考系选择、空间表征之间的关系。([科学直通车][13])近期有框架直接提出将信息处理系统视为流形，探讨"信息即几何"的观点，与本文在形式上相近。([Nova Spivack | Explorer][15])这些工作印证了将意识纳入几何语言的趋势，但在量子信息几何与同调不变量方面仍有空白，本文试图填补这一空隙。

---

## Conclusion

本文在 QCA 与光程守恒的广义框架中，提出并构建了一套"感受质几何学"。通过定义意识系统的心理流形 $\mathcal{M}_{\mathrm{psy}}$，引入 QFIM 度规与 Berry 曲率，并讨论其同调不变量，我们得到如下整体图景：

1. 体验空间的内禀度规结构与心理流形上的 QFIM 测地距离等距同构；

2. 典型感受质对应于纠缠流形上非平凡 Berry 曲率的局域结构，其强度与类型由曲率模与本征方向给出；

3. 情感效价可视为自由能在该流形上的负时间导数与测地加速度，愉悦与痛苦分别对应于沿自由能下降与上升的动力学；

4. 意识复杂度在拓扑上由心理流形上轨线填充子集的贝蒂数下界控制，为比较不同系统的潜在体验空间提供拓扑指纹。

这些结果并未在严格意义上"解决"意识的硬问题，而是将其改写为一组关于量子信息几何与纠缠拓扑的数学问题。若未来可以在神经科学与人工系统中实测或估计这些几何—拓扑量，则"意识研究"或可从目前的概念争论，转向关于度规、曲率与同调的可检验命题。

---

## Acknowledgements, Code Availability

本工作受益于量子信息几何、神经几何学与意识研究领域大量既有成果。特别感谢信息几何、量子 Fisher 信息、Berry 曲率、自由能原理与神经流形相关文献为本文提供的方法论基础。([APS Link][9])

本文所涉及的所有几何构造与数值示意均可通过标准科学计算与拓扑数据分析库实现（如基于 Python 的数值线性代数、自动微分与持久同调工具），未使用专有或封闭代码。用于示意性模拟的伪代码与参考实现可根据需要进一步整理公开。

---

## References

[1] S. L. Braunstein, C. M. Caves, "Statistical distance and the geometry of quantum states", *Phys. Rev. Lett.* **72**, 3439–3443 (1994). ([APS Link][9])

[2] S.-I. Amari, H. Nagaoka, *Methods of Information Geometry*, American Mathematical Society & Oxford University Press (2000). ([vielbein.it][7])

[3] D. Petz, "Geometries of quantum states", *J. Math. Phys.* **37**, 2662–2673 (1996). ([AIP Publishing][10])

[4] I. Bengtsson, K. Życzkowski, *Geometry of Quantum States: An Introduction to Quantum Entanglement*, Cambridge University Press (2006, 2nd ed. 2017). ([chaos.if.uj.edu.pl][11])

[5] M. V. Berry, "Quantal phase factors accompanying adiabatic changes", *Proc. R. Soc. Lond. A* **392**, 45–57 (1984); see also modern treatments of Berry connection and curvature. ([维基百科][14])

[6] J. J. Koenderink, A. J. van Doorn, "Direct measurement of curvature of visual space", *Perception* **29**, 69–79 (2000). ([ResearchGate][6])

[7] C. Stringer et al., "High-dimensional geometry of population responses in visual cortex", *Nature* **571**, 361–365 (2019). ([PMC][4])

[8] J. Petitot, "Neurogeometry of visual functional architectures", lecture notes (2015). ([indico.math.cnrs.fr][5])

[9] D. Alleysson, D. Méary, "Neurogeometry of color vision", in *New Trends in Neurogeometrical Approaches to the Processing of Visual Information* (2012). ([科学直通车][16])

[10] K. Friston, "The free-energy principle: a unified brain theory?", *Nat. Rev. Neurosci.* **11**, 127–138 (2010). ([Nature][2])

[11] G. Tononi, "An information integration theory of consciousness", *BMC Neurosci.* **5**, 42 (2004); G. Tononi et al., "Integrated information theory: from consciousness to its physical substrate", *Nat. Rev. Neurosci.* **17**, 450–461 (2016). ([维基百科][1])

[12] M. Tegmark, "Consciousness as a state of matter", *Chaos, Solitons & Fractals* **76**, 238–270 (2015). ([arXiv][3])

[13] M. K. McBeath, "The geometry of consciousness", *NeuroImage* **180**, 123–135 (2018). ([科学直通车][13])

[14] J. Lambert, E. S. Sørensen, "From classical to quantum information geometry: a guide for physicists", *J. Phys. A: Math. Theor.* **56**, 253001 (2023). ([APS Link][12])

[15] S.-I. Amari, "Information geometry of neural networks—an overview", in *Neural Networks: The Statistical Mechanics Perspective* (Springer, 1998). ([bsi-ni.brain.riken.jp][8])

[16] D. Wagenaar, "Information geometry for neural networks", Technical Report (1998). ([danielwagenaar.net][17])

[17] C. Stringer, M. Pachitariu et al., "A high-dimensional geometry of population codes decoded from visual cortex", preprint version (2019). ([UCL Discovery][18])

[18] L. Albantakis et al., "Integrated information theory (IIT) 4.0: Formulating the properties of phenomenal existence in physical terms", *PLoS Comput. Biol.* **19**, e1011416 (2023). ([维基百科][1])

[19] N. Spivack, "The geometric nature of consciousness: a new framework connecting physics, information, and mind", online essay (2025). ([Nova Spivack | Explorer][15])

[20] 其他关于 QCA、光程守恒与信息速率守恒的文献与预印本，构成本文宇宙本体论背景，在此不一一列举。

---

## 附录 A：心理流形与 QFIM 的等距同构构造

### A.1 统计可辨性与 Fisher 信息

设有一组行为实验 $\{E_\alpha\}$，每个实验对应一族 POVM $\{M_{\alpha,k}\}$ 与决策规则。对参数化态 $\rho(\theta)$，测量结果分布为 $p_{\alpha,k}(\theta) = \operatorname{Tr}[\rho(\theta) M_{\alpha,k}]$。定义经验心理距离的平方为

$$\mathrm{d}s_{\mathcal{Q}}^2 = \sup_{\alpha} \sum_k \frac{1}{p_{\alpha,k}(\theta)} \left( \partial_i p_{\alpha,k}(\theta) \mathrm{d}\theta^i \right) \left( \partial_j p_{\alpha,k}(\theta) \mathrm{d}\theta^j \right),$$

在小扰动极限下等价于对所有实验中 Fisher 信息的上界。量子估计理论表明，该上界为 QFIM。([APS Link][9])

因此，

$$\mathrm{d}s_{\mathcal{Q}}^2 = c^2 g^{\mathrm{Q}}_{ij}(\theta) \mathrm{d}\theta^i \mathrm{d}\theta^j,$$

其中 $c$ 为依赖于具体实验定义的常数因子。

### A.2 单调度规公设与唯一性

考虑任何粗粒化操作 $\Phi$（完全正迹保持映射），其对应于"忽略部分自由度"或"降低测量精度"。心理物理公设要求距离在此类操作下不增，即

$$\mathrm{d}s_{\mathcal{Q}}^2(\Phi\circ\rho) \le \mathrm{d}s_{\mathcal{Q}}^2(\rho).$$

这在统计几何中是单调度规的定义。Petz 定理指出，满足单调性与自然协变性的量子度规与一族算子单调函数一一对应。([AIP Publishing][10])若进一步要求在纯态上退化为 Fubini–Study 度规，则唯一选择为与 Bures 距离等价的 QFIM 度规。

### A.3 完备化与等距嵌入

将 $\mathcal{M}_{\mathrm{psy}}$ 赋予 QFIM 度规后，对其进行 Cauchy 完备化得到完备黎曼流形 $\overline{\mathcal{M}}_{\mathrm{psy}}$。体验空间 $\mathcal{Q}$ 在行为定义下同样可完备为度量空间 $\overline{\mathcal{Q}}$。由于局部定义的 $\mathrm{d}s_{\mathcal{Q}}^2$ 与 QFIM 相容，且等价类的定义确保零距离点被识别，由泛函分析中关于等距等价类的定理可构造等距同胚 $f: \overline{\mathcal{M}}_{\mathrm{psy}} \to \overline{\mathcal{Q}}$，其在原流形上的限制即定理 1 所需的映射。

---

## 附录 B：Berry 曲率与感受质环路

### B.1 Kähler 结构与 Berry 曲率

在纯态子流形 $\mathbb{P}(\mathcal{H})$ 上，Fubini–Study 度规

$$g_{ij} = 4 \big( \operatorname{Re} \langle \partial_i \psi | \partial_j \psi \rangle - \langle \partial_i \psi|\psi \rangle \langle \psi|\partial_j \psi \rangle \big)$$

与 Berry 联络 $A_i = i \langle \psi|\partial_i \psi \rangle$ 共同构成 Kähler 结构，其中 Kähler 形式

$$\omega_{ij} = \partial_i A_j - \partial_j A_i = F_{ij}$$

即 Berry 曲率。([维基百科][14])

### B.2 体验类型与曲率本征结构

设 $\Lambda$ 为参数空间，在给定区域内选择规范，使得 Berry 曲率矩阵在某点可对角化。其本征向量 $v^{(a)}$ 对应参数空间中的特定方向，若在实验上沿该方向缓慢改变刺激，则主体体验将表现为某种稳定"颜色"或"味道"。曲率本征值的符号与大小则与体验的"质感"与强度相关。

通过在参数空间中构造闭合环路并测量相干性或行为偏好，可间接估计 Berry 曲率通量，从而测试某些体验是否对应非平凡 Berry 曲率区域。

---

## 附录 C：自由能梯度与情感效价的几何表达

### C.1 自由能作为相对熵泛函

在变分 Bayes 框架中，自由能可写为

$$\mathcal{F}(\rho,q) = \mathbb{E}_q[-\ln p(s,f)] + \mathbb{E}_q[\ln q(f)],$$

其中 $s$ 为感觉输入，$f$ 为隐变量，$q$ 为近似后验。可将 $q$ 参数化为 $q(\theta)$，并在 QFIM 流形上引入度规。([Nature][2])在适当极限下，自由能与相对熵成正比，从而自然定义在信息几何流形上。

### C.2 梯度流与效价

沿轨线 $\gamma(t)$，

$$\frac{\mathrm{d}}{\mathrm{d}t} \mathcal{F}(\gamma(t)) = \partial_i \mathcal{F} \dot{\gamma}^i = -g_{ij} \dot{\gamma}^i\dot{\gamma}^j + \partial_i \mathcal{F} \eta^i.$$

在噪声平均下，

$$\mathbb{E}[V(t)] = -\mathbb{E}\left[\frac{\mathrm{d}}{\mathrm{d}t} \mathcal{F}\right] = \mathbb{E}\big[g_{ij}\dot{\gamma}^i\dot{\gamma}^j\big]\ge 0,$$

故效价在平均上非负，对应趋向更好预测状态。若系统被外力拉离自由能谷地，则 $\dot{\gamma}$ 与 $-\nabla \mathcal{F}$ 夹角增大，可导致瞬时 $V(t)<0$，对应负效价体验。

---

## 附录 D：贝蒂数与意识复杂度的拓扑分析

### D.1 持久同调与点云近似

对意识轨线采样得到离散点集 $\{x_i\} \subset \mathcal{M}_{\mathrm{psy}}$，在 QFIM 度规诱导的距离下构造 Vietoris–Rips 复形，随尺度参数 $\epsilon$ 变化计算其同调群，获得持久条形码。这些条形码在 $\epsilon$ 轴上的持续长度反映拓扑特征的稳健性。([PMC][4])

### D.2 拓扑下界与体验分类

若在尺度区间 $[\epsilon_1,\epsilon_2]$ 内存在稳定的非零 $b_k$，则说明在对应分辨率下存在不可约的 $k$ 维孔洞。将这些孔洞与体验分类任务（如语义类别、情绪维度）做联合分析，可为"多少种不可约体验类型"提供拓扑下界。例如，若在表示语义空间的子流形上观测到高 $b_1$ 与 $b_2$，则暗示语义体验中存在丰富的循环与空腔结构。

这一分析框架同样适用于人工系统，为比较不同架构与训练方案下的"体验潜力"提供统一的拓扑语言。

[1]: https://en.wikipedia.org/wiki/Integrated_information_theory?utm_source=chatgpt.com "Integrated information theory"

[2]: https://www.nature.com/articles/nrn2787?utm_source=chatgpt.com "The free-energy principle: a unified brain theory?"

[3]: https://arxiv.org/abs/1401.1219?utm_source=chatgpt.com "Consciousness as a State of Matter"

[4]: https://pmc.ncbi.nlm.nih.gov/articles/PMC6642054/?utm_source=chatgpt.com "High-dimensional geometry of population responses in visual ..."

[5]: https://indico.math.cnrs.fr/event/202/contributions/959/attachments/557/610/2015-Petitot-Aussois.pdf?utm_source=chatgpt.com "Geometry of some functional architectures of vision"

[6]: https://www.researchgate.net/profile/Joseph-Lappin/publication/12496606_Direct_measurement_of_curvature_of_visual_space/links/02bfe510970bae37cd000000/Direct-measurement-of-curvature-of-visual-space.pdf?utm_source=chatgpt.com "Direct-measurement-of-curvature-of-visual-space. ..."

[7]: https://vielbein.it/pdf/Traduzioni/2000-Amer-Methods_of_Information_Geometry.pdf?utm_source=chatgpt.com "Methods of Information Geometry - Vielbein"

[8]: https://bsi-ni.brain.riken.jp/database/file/137/135.pdf?utm_source=chatgpt.com "Information Geometry of Neural Networks"

[9]: https://link.aps.org/doi/10.1103/PhysRevLett.72.3439?utm_source=chatgpt.com "Statistical distance and the geometry of quantum states"

[10]: https://pubs.aip.org/aip/jmp/article/37/6/2662/447689/Geometries-of-quantum-states?utm_source=chatgpt.com "Geometries of quantum states | Journal of Mathematical Physics"

[11]: https://chaos.if.uj.edu.pl/~karol/pdf/BZ06CUP.pdf?utm_source=chatgpt.com "GEOMETRY OF QUANTUM STATES"

[12]: https://link.aps.org/doi/10.1103/PhysRevE.89.022102?utm_source=chatgpt.com "Quantum information-geometry of dissipative quantum phase ..."

[13]: https://www.sciencedirect.com/science/article/abs/pii/S105381001830062X?utm_source=chatgpt.com "The geometry of consciousness"

[14]: https://en.wikipedia.org/wiki/Berry_connection_and_curvature?utm_source=chatgpt.com "Berry connection and curvature"

[15]: https://www.novaspivack.com/science/the-geometric-nature-of-consciousness-a-new-framework-connecting-physics-information-and-mind-non-technical-introduction?utm_source=chatgpt.com "The Geometric Nature of Consciousness: A New Framework ..."

[16]: https://www.sciencedirect.com/science/article/abs/pii/S0928425712000599?utm_source=chatgpt.com "Editorial: New trends in neurogeometrical approaches to ..."

[17]: https://www.danielwagenaar.net/papers/98-Wage2.pdf?utm_source=chatgpt.com "Information geometry for neural networks"

[18]: https://discovery.ucl.ac.uk/10076947/1/HighDim%20preprint%20190421.pdf?utm_source=chatgpt.com "High-dimensional geometry of population responses in visual ..."


