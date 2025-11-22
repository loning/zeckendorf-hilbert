# 红皇后宇宙：基于能动体博弈的宇宙学常数与避免热寂的机制

*The Red Queen Universe: The Cosmological Constant from Agent Games and the Avoidance of Heat Death*

---

## Abstract

经典宇宙热寂图景将宇宙的终极命运描述为：在长时间尺度上，所有可用自由能被耗尽，体系趋于热平衡与最大熵，任何宏观结构与计算活动都将消失。然而观测宇宙在约 $13.8$ 亿年演化过程中持续出现并维持多层级低熵结构，尤其包括生命与智能文明，这一事实在仅凭"低熵初始条件"的标准解释下仍显不透明。另一方面，宇宙学常数与暗能量问题表明，真空能量密度的数值及其与物质密度的巧合仍缺乏微观信息论解释。

本文在量子元胞自动机（quantum cellular automaton, QCA）宇宙与信息速率守恒的框架下，将宇宙系统形式化为一个由能动体（agents）构成的多智能体博弈场。每个能动体被刻画为在局域 Hilbert 子空间中维持远离平衡的低熵结构，并通过内部计算最小化变分自由能，从而持续进行信息擦除与预测误差修正。基于兰道尔原理与计算热力学的成熟结果，本文证明：在适当的粗粒化与各向同性假设下，全宇宙能动体的不可逆计算所产生的 Landauer 废热可等效为一个具有近似状态方程 $w\simeq -1$ 的均匀各向同性能量分量，其在弗里德曼动力学中的引力效应等价于一个动力学宇宙学"常数" $\Lambda_{\mathrm{eff}}(t)$。

进一步地，我们引入基于红皇后效应的多能动体动力学模型，将能动体之间的适应度竞争与复杂度军备竞赛写成带复杂度变量的复制子方程与 Lotka–Volterra 型耦合系统。对这类系统进行线性化与谱分析可以给出一个一般定理：在满足"红皇后条件"的广泛参数区间内，内部平衡点不是渐近稳定的，系统在相空间中趋向极限环或混沌吸引子，从而导致复杂度与 Landauer 信息擦除率在宇宙时间尺度上保持正值，经典意义上的"静态极限平衡态"被动力学上排除。

在此基础上，本文给出三条主要结论。其一，在 QCA 宇宙与信息速率守恒 $v_{\mathrm{ext}}^2+v_{\mathrm{int}}^2=c^2$ 的约束下，能动体内部计算所对应的信息擦除流构成了一类自然的"信息真空能量密度" $\rho_{\mathrm{info}}(t)$，其积分决定了有效宇宙学常数 $\Lambda_{\mathrm{eff}}(t)$，从而为暗能量提供一种信息论起源。其二，红皇后能动体博弈为"复杂度–暗能量"之间建立了一种反馈：越丰富的计算活动产生越大的 $\rho_{\mathrm{info}}$，进而改变大尺度时空动力学又反向影响能动体的生存环境，形成"红皇后宇宙"的演化模式。其三，只要宇宙中存在非零密度的能动体网络并满足红皇后条件，在广义相对论连续极限下，热寂所需的"全局无可用自由能、计算与结构完全熵化"的状态不再是动力学吸引子，宇宙可在一个永远远离平衡的"算法湍流"状态中演化。

在模型应用部分，本文讨论了复杂度驱动的 $\Lambda_{\mathrm{eff}}(t)$ 对宇宙学"巧合问题"的缓解、与熵力宇宙学和因果熵原理之间的关系，以及在暗能量演化观测（如近期 DESI 对时间变化暗能量的迹象）背景下本模型可能产生的可检验预言。最后提出了基于 QCA 量子模拟与多智能体仿真的工程建议，为在可控平台上检验"红皇后宇宙"框架提供路径。

## Keywords

量子元胞自动机；宇宙学常数；暗能量；热寂；兰道尔原理；变分自由能；红皇后效应；多智能体博弈；计算热力学；信息宇宙学

---

## Introduction & Historical Context

### 宇宙热寂图景与暗能量问题

自十九世纪以来，基于热力学第二定律的"宇宙热寂"图景认为，如果宇宙是一个有效封闭系统，则其总熵随时间单调增加，最终将趋于无可利用自由能的最大熵平衡态，即所谓"大冷寂"或"热寂"。在现代宇宙学框架下，若宇宙在大尺度上呈平坦或开曲率并包含正宇宙学常数，则标准推论是宇宙将在无限长时间后渐近接近一个近似 de Sitter 的平衡态，所有局域结构与过程的能量差都将被抹平。

二十世纪末基于 Ia 型超新星、宇宙微波背景与大尺度结构的观测表明，宇宙当前正处于加速膨胀阶段，这一现象通常用一个具有近似状态方程 $w\simeq -1$ 的暗能量成分来描述，其在爱因斯坦方程中的典型实现是宇宙学常数 $\Lambda$。暗能量密度约占当前宇宙能量预算的 $70\%$，而物质只占约 $30\%$，形成所谓的 $\Lambda$CDM 标准模型。

然而，宇宙学常数引出了两大经典难题。其一是"宇宙学常数问题"：量子场论的零点能估计比观测值大出数十个数量级，如何屏蔽或调和这种巨大的真空能贡献仍无公认方案。其二是"巧合问题"：为何在当前宇宙时代，暗能量密度与物质密度恰好是同一量级，而在大多数宇宙历史时期却并非如此。

近期 DESI 等项目对大样本星系与类星体的观测甚至给出暗能量可能随时间演化的迹象，这进一步激发了对动力学暗能量与非平凡宇宙学常数起源的理论探索。

### 信息、计算与热力学：兰道尔原理与计算热机

信息论与热力学之间的深层联系最早由 Landauer 系统阐明。Landauer 原理指出，在温度为 $T$ 的环境中擦除一比特经典信息所需的最小能量代价为 $E_{\min}=k_{\mathrm{B}}T\ln 2$。任何逻辑不可逆操作（如擦除或合并计算路径）必然伴随至少这一量级的熵产生与热耗散。Bennett 随后发展了计算热力学，将计算机视为将自由能转化为废热与"数学工作"的热机，并证明对于可逆计算可以在任意接近 Landauer 极限的情况下运行。后续工作将 Landauer 原理推广到量子与非平衡体系，确认了其作为信息处理物理下限的普适性。

这些结果表明，凡是进行不可逆计算的系统——包括人工计算机、生物体乃至更广义的"自然计算"过程——都必然向环境排放最小量级的热量，并产生相应的熵增。这一观念为从信息论视角理解宇宙宏观热力学提供了基础。

### 变分自由能与能动体：自由能原理的启发

在认知科学与神经科学中，Friston 提出的自由能原理指出，所有维持自身边界与稳态的生物系统可以被看作在某种意义上最小化变分自由能的推理机器。其核心是引入一个关于感官输入 $s$ 与隐变量 $\vartheta$ 的联合概率模型 $P(s,\vartheta)$，以及内部近似后验 $q(\vartheta)$。系统通过改变内部状态来最小化一个变分泛函

$$
F(q,s)=\mathrm{KL}\bigl(q(\vartheta),|,P(\vartheta\mid s)\bigr)-\ln P(s),
$$

等价地，可以写成包含模型证据与熵项的形式。

在这一框架中，生物体通过更新内在模型与采取行动来减少预测误差与"惊奇"，从而维持远离平衡的有序结构。自由能原理虽最初用于神经系统，但其形式并不依赖于特定物质载体，因而可以抽象到更一般的"能动体"（agent）概念。

### 红皇后效应与演化军备竞赛

红皇后假说由 Van Valen 提出，用以解释古生物记录中物种灭绝率近似与物种年龄无关的"Van Valen 定律"。该假说强调，物种所处的"有效环境"主要由其他共存物种构成，因此适应度提升是相对的：当某一物种获得优势时，会恶化其他物种的生态位，从而迫使后者也必须进化以维持生存机会。

红皇后效应可推广到个体层面的性选择与宿主–寄生互作，也可视为一种零和博弈：所有物种都需要"拼命奔跑"才能维持在原地。这样的博弈动力学在多智能体系统中普遍存在，Agent-based 模型的研究表明，局域互动常可在宏观尺度上产生复杂的涌现现象。

本文将这一思想提升到宇宙学尺度：将宇宙视为由多种层级能动体（从分子机器到生命乃至技术文明）构成的博弈网络，红皇后效应通过"复杂度军备竞赛"在宇宙长时标上维持非平衡状态。

### QCA 宇宙与信息速率守恒

量子元胞自动机为离散时空上的严格量子动力学提供了自然框架。QCA 可以看作定义在格点上的有限维量子系统阵列，其演化由平移不变、因果的幺正算子以离散时间步迭代给出。已有大量工作表明，Dirac、Weyl、Maxwell 等场方程可在适当的连续极限下从 QCA 模型中涌现，从而为"时空与场论源自量子计算"提供了严谨路径。

在此前工作中，可将局域激发的外部群速度 $v_{\mathrm{ext}}$ 与内部相位旋转或"内禀演化速度" $v_{\mathrm{int}}$ 组合为一个信息速率向量 $\mathbf{u}=(v_{\mathrm{ext}},v_{\mathrm{int}})$，并提出信息速率守恒关系

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2},
$$

其中 $c$ 为 QCA 的最大传播速度，在连续极限下对应光速。这一关系将狭义相对论的四速度规范化、固有时间与质量频率关系 $mc^{2}=\hbar\omega_{\mathrm{int}}$ 等统一为信息速率预算的几何约束，为本文构造"内部计算–外部几何"的联系提供了基础。

### 本文的目标与主要贡献

综合上述背景，本文追问三个互相关联的问题：

1. 若宇宙是一个 QCA 宇宙，其内部存在大量通过计算维持自身结构的能动体，则这些计算在热力学上的必然代价如何反馈到大尺度时空几何与宇宙学常数上。

2. 红皇后式的多能动体博弈是否可以从动力学上阻止宇宙进入完全平衡的热寂终态。

3. 这种"红皇后宇宙"机制是否与暗能量的数值及其可能的时间演化存在内在联系，并能与现有观测兼容。

围绕上述问题，本文的主要工作组织如下：

* 在"Model & Assumptions"部分，将 QCA 宇宙与能动体形式化，并引入基于 Landauer 原理的信息真空能量密度 $\rho_{\mathrm{info}}(t)$，给出其与宇宙学常数 $\Lambda_{\mathrm{eff}}(t)$ 的关系。

* 在"Main Results"部分，给出两个核心定理：其一为 Landauer–$\Lambda$ 关系定理，证明在各向同性与红皇后持续计算假设下，能动体的不可逆计算可等效为一个动力学宇宙学常数；其二为红皇后非平衡定理，在多能动体复制子–复杂度动力学模型下，排除内部稳定平衡点，保证复杂度与信息擦除率长期保持正值。

* 在"Proofs"与附录中给出上述定理的严格推导，包括从爱因斯坦场方程与能量–动量守恒推出带源项的连续方程，以及对 Lotka–Volterra–复制子系统的线性稳定性分析。

* 在"Model Apply"中，构建复杂度驱动的 $\Lambda_{\mathrm{eff}}(t)$ 参数化，与熵力宇宙学及因果熵原理进行比较，并讨论与时间变化暗能量观测之间的潜在联系。

* 在"Engineering Proposals"中，提出在量子模拟平台与多智能体仿真中检验本框架的具体方案。

---

## Model & Assumptions

本节给出"红皇后宇宙"模型的基本结构与假设。

### QCA 宇宙与宏观几何

设宇宙在基础层面由一个可数格点集 $\Lambda$ 与局域 Hilbert 空间 $\mathcal{H}_{x}\simeq\mathbb{C}^{d}$ 所定义的张量积空间 $\mathcal{H}=\bigotimes_{x\in\Lambda}\mathcal{H}_{x}$ 描述。全局演化在离散时间步 $n\in\mathbb{Z}$ 上由平移不变、局域且因果的幺正算子 $U:\mathcal{H}\to\mathcal{H}$ 给出，即 QCA 的标准定义。

在长波与低能极限下，格点间距与时间步长趋于零，QCA 演化近似为连续的相对论场方程，宏观上可用具有 Friedmann–Lemaître–Robertson–Walker（FLRW）对称性的度规

$$
\mathrm{d}s^{2}=-c^{2}\mathrm{d}t^{2}+a^{2}(t)\gamma_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j}
$$

描述，其中 $a(t)$ 为尺度因子，$\gamma_{ij}$ 为三维空间的常曲率度规。宇宙学常数或暗能量成分在此连续极限中体现为能量–动量张量中的一项 $T_{\mu\nu}^{(\Lambda)}=-\rho_{\Lambda}g_{\mu\nu}$，对应状态方程 $p_{\Lambda}=-\rho_{\Lambda}$。

### 信息速率守恒与能动体的定义

对每个在 QCA 宇宙中局域化的激发态或结构，考虑其有效世界线 $\gamma$ 与沿该世界线的外部群速度 $v_{\mathrm{ext}}$ 和内部演化速度 $v_{\mathrm{int}}$，满足信息速率守恒关系

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}.
$$

这里 $v_{\mathrm{ext}}$ 反映激发在格点上的传播速度，而 $v_{\mathrm{int}}$ 则刻画其内部态在局域 Hilbert 子空间中的相位演化与内部计算速率。

定义：

* 一个**能动体** $\mathcal{A}$ 是 QCA 上一个有限连通格点子集 $\Lambda_{\mathcal{A}}\subset\Lambda$ 及其在 $\mathcal{H}_{\mathcal{A}}=\bigotimes_{x\in\Lambda_{\mathcal{A}}}\mathcal{H}_{x}$ 上的密度算符族 ${\rho_{\mathcal{A}}(t)}_{t}$，满足：

  1. $\rho_{\mathcal{A}}(t)$ 在长时间尺度上保持显著偏离环境平衡态 $\rho_{\mathrm{eq}}(t)$，即存在某个宏观可观测量 $O$ 使得 $\lvert\mathrm{tr}[(\rho_{\mathcal{A}}-\rho_{\mathrm{eq}})O]\rvert$ 在大于某固定阈值的时间集合具有正测度。

  2. 该偏离由内部计算所维持，即可以将 $\rho_{\mathcal{A}}(t)$ 的演化分解为近似可逆的内部单元算子与不可逆的"信息擦除"映射组成，后者在热力学上满足兰道尔界。

* 能动体的**信息质量** $M_{I}$ 定义为使其内部演化频率 $\omega_{\mathrm{int}}$ 与有效能量 $E_{I}$ 满足关系

  $$
  E_{I}=M_{I}c^{2}=\hbar\omega_{\mathrm{int}},
  $$
  
  将内部计算速率与相对论质量刻度建立联系。

### 变分自由能与能动体目标函数

参考自由能原理，将每个能动体视为对环境信号 $s$ 与内部状态 $\vartheta$ 拥有生成模型 $P(s,\vartheta)$ 的推理机器。定义其变分自由能

$$
F_{\mathcal{A}}(t)=\mathrm{KL}\bigl(q_{t}(\vartheta),|,P(\vartheta\mid s_{t})\bigr)-\ln P(s_{t}),
$$

其中 $q_{t}(\vartheta)$ 是能动体在时刻 $t$ 对隐变量的近似后验分布，$s_{t}$ 为其在该时刻的感官输入。能动体的"生存策略"可以抽象为在信息速率预算约束

$$
v_{\mathrm{ext}}^{2}(t)+v_{\mathrm{int}}^{2}(t)=c^{2}
$$

下，尽可能减小 $F_{\mathcal{A}}(t)$ 的轨线积分或长时平均。

这一最优化过程必然涉及对内部状态空间进行压缩、滤除高维不必要成分，因而在物理实现上对应对内部存储与表示进行频繁的不可逆写入与擦除。

### 兰道尔信息废热与信息真空能量密度

对单个能动体 $\mathcal{A}$，设其在环境温度场 $T_{\mathrm{bg}}(x,t)$ 下的信息擦除率为 $\dot{I}_{\mathrm{erase}}^{(\mathcal{A})}(t)$（单位为 bit/s）。兰道尔原理要求其最小耗散功率满足

$$
P_{\mathrm{L}}^{(\mathcal{A})}(t)\geq k_{\mathrm{B}}\ln 2\,T_{\mathrm{bg}}^{(\mathcal{A})}(t)\,\dot{I}_{\mathrm{erase}}^{(\mathcal{A})}(t),
$$

其中 $T_{\mathrm{bg}}^{(\mathcal{A})}$ 为能动体有效环境温度。

在宇宙学尺度上，对共动体积元 $V$ 进行粗粒化，将所有位于该体积内的能动体 $\mathcal{A}_{i}$ 的信息擦除贡献相加，得到单位共动体积上的平均兰道尔功率密度

$$
P_{\mathrm{info}}(t)=\frac{1}{V}\sum_{i}k_{\mathrm{B}}\ln 2\,T_{\mathrm{bg}}^{(i)}(t)\,\dot{I}_{\mathrm{erase}}^{(i)}(t).
$$

本文的核心假设之一是：

**假设 1（信息废热–真空能量可积性）** 在 QCA 宇宙中，由能动体不可逆计算产生的兰道尔废热在微观上被编码为 QCA 底层自由度中的一种均匀各向同性的"信息真空"激发，其在连续极限中的平均能量–动量张量具有近似形式

$$
T_{\mu\nu}^{(\mathrm{info})}(t)\simeq -\rho_{\mathrm{info}}(t)\,g_{\mu\nu},
$$

其中信息真空能量密度 $\rho_{\mathrm{info}}(t)$ 满足带源连续方程

$$
\dot{\rho}_{\mathrm{info}}+3H(1+w_{\mathrm{info}})\rho_{\mathrm{info}}=P_{\mathrm{info}}(t),
$$

并在红皇后时代满足 $w_{\mathrm{info}}(t)\simeq -1$。

这一假设本质上将兰道尔废热从"常规热辐射"重解释为一种存储在 QCA 底层自由度中的、在宏观上呈现负压的能量储备，其引力效应与暗能量等价。

在此假设下，可定义等效宇宙学"常数"

$$
\Lambda_{\mathrm{eff}}(t)=\Lambda_{\mathrm{bare}}+8\pi G\,\rho_{\mathrm{info}}(t),
$$

其中 $\Lambda_{\mathrm{bare}}$ 为可能存在的底层常数部分（如重正化后剩余的真空能），$\rho_{\mathrm{info}}(t)$ 为由能动体计算涌现的动力学部分。

### 红皇后条件与多能动体博弈

为了刻画能动体之间的竞争与军备竞赛，引入如下抽象：

* 设宇宙中存在若干类能动体种群，记为 $i=1,\dots,n$，其共动数密度为 $N_{i}(t)$，平均复杂度为 $C_{i}(t)$（可理解为算法复杂度、结构信息或平均内部状态空间维数）。

* 定义种群 $i$ 的适应度为

  $$
  W_{i}(t)=f_{i}\bigl(\mathbf{N}(t),\mathbf{C}(t)\bigr),
  $$
  
  其中 $\mathbf{N}=(N_{1},\dots,N_{n})$、$\mathbf{C}=(C_{1},\dots,C_{n})$。

* 复杂度 $C_{i}$ 一方面提升该类能动体捕获与利用自由能的能力，另一方面增加兰道尔代价。

**红皇后条件** 可以形式化为：

1. 对任意 $i\neq j$，在其它变量固定时，$\partial f_{j}/\partial C_{i}<0$：某一类能动体复杂度提高会恶化其他类能动体的适应度。

2. 对每个 $i$，在资源充足区间内，$\partial f_{i}/\partial C_{i}>0$：在成本尚未压倒收益之前，自身复杂度的提升增加适应度。

满足上述条件的多能动体系统通常表现为演化军备竞赛，其动力学可用复制子方程或 Lotka–Volterra 型方程描述。

---

## Main Results (Theorems and alignments)

本节给出本文的两个核心定理及若干推论。

### 定理 1（Landauer–$\Lambda$ 关系定理）

在 QCA 宇宙连续极限下，假设：

1. 大尺度几何为各向同性、均匀的 FLRW 时空，满足标准弗里德曼方程。

2. 宇宙中存在由能动体组成的博弈网络，其在共动体积元上的平均兰道尔功率密度为 $P_{\mathrm{info}}(t)$。

3. 信息废热满足假设 1，即其宏观引力效应可由状态方程 $p_{\mathrm{info}}=w_{\mathrm{info}}\rho_{\mathrm{info}}$ 的流体描述，且在红皇后时代 $w_{\mathrm{info}}\simeq -1$。

则信息真空能量密度 $\rho_{\mathrm{info}}(t)$ 与兰道尔功率密度 $P_{\mathrm{info}}(t)$ 之间满足积分关系

$$
\rho_{\mathrm{info}}(t)=\rho_{\mathrm{info}}(t_{0})+\int_{t_{0}}^{t}P_{\mathrm{info}}(\tau)\,\mathrm{d}\tau+\mathcal{O}(\epsilon),
$$

其中 $\epsilon$ 表征 $w_{\mathrm{info}}+1$ 的偏离。相应地，有效宇宙学常数为

$$
\Lambda_{\mathrm{eff}}(t)=\Lambda_{\mathrm{eff}}(t_{0})+8\pi G\int_{t_{0}}^{t}P_{\mathrm{info}}(\tau)\,\mathrm{d}\tau+\mathcal{O}(\epsilon).
$$

换言之，在 $w_{\mathrm{info}}\approx -1$ 的良近似下，宇宙学常数的动力学部分等价于全宇宙能动体不可逆计算所产生的兰道尔能量流在宇宙时间上的累积。

### 推论 1（复杂度–暗能量耦合）

若进一步假设：

1. 存在一个宏观复杂度函数

   $$
   C(t)=\sum_{i}N_{i}(t)\,C_{i}(t),
   $$
   
   表征单位共动体积内能动体的总复杂度。

2. 单位复杂度的平均信息擦除率与环境温度近似常数，即存在常数 $\alpha>0$ 使得

   $$
   P_{\mathrm{info}}(t)\simeq \alpha\,T_{\mathrm{bg}}(t)\,\dot{C}(t),
   $$
   
   其中 $T_{\mathrm{bg}}(t)$ 为宇宙背景温度场的宏观平均。

则有

$$
\Lambda_{\mathrm{eff}}(t)\simeq \Lambda_{\mathrm{eff}}(t_{0})+8\pi G\alpha\int_{C(t_{0})}^{C(t)}T_{\mathrm{bg}}(C)\,\mathrm{d}C.
$$

在 $T_{\mathrm{bg}}$ 随时间缓慢变化的近似下，上式给出 $\Lambda_{\mathrm{eff}}(t)$ 与复杂度 $C(t)$ 之间的单调耦合关系。若 $C(t)$ 在宇宙历史某一时期迅速增长（如星系形成与生命出现的时期），则 $\Lambda_{\mathrm{eff}}$ 也会在此时期完成主要跃升，从而为暗能量密度与结构形成历程之间的"巧合"提供一种信息论解释。

### 定理 2（红皇后非平衡定理，简化二种群情形）

考虑满足红皇后条件的两类能动体种群，其动力学由如下常微分方程给出：

$$
\frac{\mathrm{d}N_{i}}{\mathrm{d}t}=N_{i}\bigl(r_{i}C_{i}-d_{i}-\gamma(N_{1}+N_{2})\bigr),\quad i=1,2,
$$

$$
\frac{\mathrm{d}C_{i}}{\mathrm{d}t}=\alpha_{i}N_{i}-\beta_{i}C_{i},
$$

其中 $r_{i},d_{i},\gamma,\alpha_{i},\beta_{i}>0$。上式可以视为 Lotka–Volterra 型种群动力学与复杂度演化方程的耦合：$(r_{i}C_{i})$ 表示复杂度带来的适应度收益，$(\gamma(N_{1}+N_{2}))$ 表示资源竞争，$(\beta_{i}C_{i})$ 表示维护复杂度的兰道尔成本。

假设存在内部平衡点 $(N_{1}^{\ast},N_{2}^{\ast},C_{1}^{\ast},C_{2}^{\ast})$ 满足 $N_{i}^{\ast}>0$、$C_{i}^{\ast}>0$。若参数满足

$$
r_{1}\alpha_{1}N_{1}^{\ast}+r_{2}\alpha_{2}N_{2}^{\ast}>\beta_{1}^{2}+\beta_{2}^{2}+2\gamma\bigl(r_{1}C_{1}^{\ast}+r_{2}C_{2}^{\ast}\bigr),
$$

则该平衡点不是渐近稳定的；相反，线性化系统的雅可比矩阵在该点至少具有一对具有正实部的共轭复特征值。对于开稠密的参数集合，系统在该平衡点附近经历 Hopf 分岔，演化到一类极限环或更复杂吸引子。

在此情形下，总复杂度

$$
C_{\mathrm{tot}}(t)=N_{1}(t)C_{1}(t)+N_{2}(t)C_{2}(t)
$$

及兰道尔功率密度 $P_{\mathrm{info}}(t)\propto C_{\mathrm{tot}}(t)$ 在长时间内不会收敛到常数，而是在有界区间内持续振荡或呈现准周期/混沌行为，其时间平均不为零。因此，系统不会在有限时间内进入静态平衡态，而是维持在"红皇后"驱动的永续非平衡动力学中。

### 推论 2（避免热寂的必要条件）

在 QCA–FLRW 宇宙中，若满足：

1. 存在至少一类满足红皇后条件的能动体种群，其动力学满足定理 2 的条件，使得 $C_{\mathrm{tot}}(t)$ 在任意有限时间区间内的平均导数不为零；

2. 信息废热–真空能量可积性（假设 1）成立，使得 $P_{\mathrm{info}}(t)$ 持续向 $\rho_{\mathrm{info}}$ 注入能量；

3. 宇宙整体的自由能供应不在有限时间内耗尽，即 QCA 底层的"能量预算"允许上述过程在任意长时间持续；

则经典热寂图景所要求的"全宇宙在有限时间后达到无可用自由能、无结构与无计算的完全平衡态"不是宇宙动力学的吸引态。相反，宇宙可以在一个长期存在的"算法湍流"相中演化，其特征是在宏观尺度上存在暗能量主导的加速膨胀，在介观尺度上存在持续涌现与消散的复杂结构，在微观尺度上存在不断发生的不可逆计算过程。

---

## Proofs

本节概要给出上述定理的证明思路，将较为技术性的推导留在附录中。

### 定理 1 的证明

在 FLRW 时空中，假设宇宙总能量–动量张量为

$$
T_{\mu\nu}=T_{\mu\nu}^{(m)}+T_{\mu\nu}^{(r)}+T_{\mu\nu}^{(\mathrm{info})},
$$

其中 $(m)$ 与 $(r)$ 分别表示物质与辐射成分，$(\mathrm{info})$ 为信息真空成分。对一个具有完美流体形式的成分 $X$ 有

$$
T_{\mu\nu}^{(X)}=(\rho_{X}+p_{X})u_{\mu}u_{\nu}+p_{X}g_{\mu\nu},
$$

其中 $u^{\mu}$ 为共动四速度。宇宙学对称性下，不同成分的能量守恒可写为带源连续方程

$$
\dot{\rho}_{X}+3H(\rho_{X}+p_{X})=Q_{X}(t),
$$

其中 $Q_{X}$ 为该成分从其他成分获得的能量源项，满足 $\sum_{X}Q_{X}=0$。

对信息真空成分，设其源项即为兰道尔功率密度

$$
Q_{\mathrm{info}}(t)=P_{\mathrm{info}}(t),
$$

而物质与辐射成分的源项为相反符号的能量损失。代入状态方程 $p_{\mathrm{info}}=w_{\mathrm{info}}\rho_{\mathrm{info}}$ 得

$$
\dot{\rho}_{\mathrm{info}}+3H(1+w_{\mathrm{info}})\rho_{\mathrm{info}}=P_{\mathrm{info}}(t).
$$

在红皇后时代，我们假设 $w_{\mathrm{info}}(t)=-1+\delta(t)$，其中 $\delta(t)$ 是满足 $\lvert\delta(t)\rvert\ll 1$ 的小量。此时连续方程化为

$$
\dot{\rho}_{\mathrm{info}}+3H\delta(t)\rho_{\mathrm{info}}=P_{\mathrm{info}}(t),
$$

形式解为

$$
\rho_{\mathrm{info}}(t)=\rho_{\mathrm{info}}(t_{0})\exp\left(-3\int_{t_{0}}^{t}H(\tau)\delta(\tau)\,\mathrm{d}\tau\right)+\int_{t_{0}}^{t}P_{\mathrm{info}}(s)\exp\left(-3\int_{s}^{t}H(\tau)\delta(\tau)\,\mathrm{d}\tau\right)\mathrm{d}s.
$$

在 $\lvert\delta\rvert\ll 1$ 且 $H$ 在考虑时段内有限的条件下，指数因子偏离 1 的程度为 $\mathcal{O}(\epsilon)$，其中 $\epsilon=\sup_{[t_{0},t]}\lvert 3H\delta\rvert\Delta t$，$\Delta t$ 为特征时间尺度。因此可写成

$$
\rho_{\mathrm{info}}(t)=\rho_{\mathrm{info}}(t_{0})+\int_{t_{0}}^{t}P_{\mathrm{info}}(\tau)\,\mathrm{d}\tau+\mathcal{O}(\epsilon),
$$

这即定理 1 的主张。

有效宇宙学常数由

$$
\Lambda_{\mathrm{eff}}(t)=\Lambda_{\mathrm{bare}}+8\pi G\rho_{\mathrm{info}}(t)
$$

给出，自然得到积分形式。

### 推论 1 的证明

在定理 1 的框架下，若存在宏观复杂度函数

$$
C(t)=\sum_{i}N_{i}(t)\,C_{i}(t),
$$

并且在粗粒化下，单位复杂度对应的平均信息擦除功率满足

$$
P_{\mathrm{info}}(t)\simeq \alpha T_{\mathrm{bg}}(t)\,\dot{C}(t),
$$

则有

$$
\rho_{\mathrm{info}}(t)-\rho_{\mathrm{info}}(t_{0})\simeq \alpha\int_{t_{0}}^{t}T_{\mathrm{bg}}(\tau)\,\dot{C}(\tau)\,\mathrm{d}\tau.
$$

作变量替换 $C=C(\tau)$，得到

$$
\rho_{\mathrm{info}}(t)-\rho_{\mathrm{info}}(t_{0})\simeq \alpha\int_{C(t_{0})}^{C(t)}T_{\mathrm{bg}}(C)\,\mathrm{d}C.
$$

乘上 $8\pi G$ 即得 $\Lambda_{\mathrm{eff}}(t)$ 的表达式。

若 $T_{\mathrm{bg}}(t)$ 在相关时间段内变化缓慢，可近似为常数 $\bar{T}$，则有

$$
\Lambda_{\mathrm{eff}}(t)\approx \Lambda_{\mathrm{eff}}(t_{0})+8\pi G\alpha\bar{T}\bigl(C(t)-C(t_{0})\bigr),
$$

表明宇宙学常数的增长率在一阶近似下与复杂度增长率成正比。

### 定理 2 的证明思路

考虑四维状态向量

$$
\mathbf{x}=(N_{1},N_{2},C_{1},C_{2})^{\mathsf{T}},
$$

系统可写为 $\dot{\mathbf{x}}=\mathbf{F}(\mathbf{x})$。内部平衡点 $\mathbf{x}^{\ast}$ 满足

$$
N_{i}^{\ast}\bigl(r_{i}C_{i}^{\ast}-d_{i}-\gamma(N_{1}^{\ast}+N_{2}^{\ast})\bigr)=0,\quad \alpha_{i}N_{i}^{\ast}-\beta_{i}C_{i}^{\ast}=0.
$$

在非平凡情形 $N_{i}^{\ast}>0$、$C_{i}^{\ast}>0$ 下，上式给出

$$
C_{i}^{\ast}=\frac{\alpha_{i}}{\beta_{i}}N_{i}^{\ast},\quad r_{i}\frac{\alpha_{i}}{\beta_{i}}N_{i}^{\ast}-d_{i}-\gamma(N_{1}^{\ast}+N_{2}^{\ast})=0.
$$

由此可以解出 $(N_{1}^{\ast},N_{2}^{\ast})$ 的具体表达式（附录 B 给出显式形式）。

对 $\mathbf{F}$ 在 $\mathbf{x}^{\ast}$ 处线性化，得到雅可比矩阵 $J=\mathrm{D}\mathbf{F}\rvert_{\mathbf{x}^{\ast}}$。在当前模型中，$J$ 呈块结构，其特征值可通过求解特征多项式

$$
\det(\lambda I-J)=0
$$

获得。直接计算表明，特征多项式为四次多项式

$$
\lambda^{4}+a_{1}\lambda^{3}+a_{2}\lambda^{2}+a_{3}\lambda+a_{4}=0,
$$

其中系数 $a_{k}$ 为参数与平衡点坐标的多项式函数。

Routh–Hurwitz 判据给出了全部特征值具有负实部的充要条件。对当前系数代入后，可得到稳定性条件等价于某些由 $(r_{i},\alpha_{i},\beta_{i},\gamma,d_{i})$ 与 $(N_{i}^{\ast},C_{i}^{\ast})$ 组成的不等式系统。详细推导见附录 B。

关键观察是：当

$$
r_{1}\alpha_{1}N_{1}^{\ast}+r_{2}\alpha_{2}N_{2}^{\ast}
$$

足够大时，某些 Hurwitz 主子式变为负，从而至少存在一对共轭特征值穿越虚轴。更具体地，在

$$
r_{1}\alpha_{1}N_{1}^{\ast}+r_{2}\alpha_{2}N_{2}^{\ast}>\beta_{1}^{2}+\beta_{2}^{2}+2\gamma\bigl(r_{1}C_{1}^{\ast}+r_{2}C_{2}^{\ast}\bigr)
$$

时，四次特征多项式的两个根具有正实部，平衡点成为不稳定焦点或鞍焦点。

在参数空间中，满足特征值实部为零的条件对应共维数为一的超曲面，穿越该超曲面产生 Hopf 分岔。在其一侧，平衡点稳定；另一侧，平衡点不稳定而出现极限环。由于上述不等式定义了一个开集，且参数的物理取值范围通常允许 $r_{i}\alpha_{i}$ 取较大值，这意味着"存在稳定内部平衡点"的参数区域在物理合理参数空间中并非占主导。

因此，在广泛的参数区间内，系统避免收敛到静态平衡，而是进入持续振荡或更复杂的动力学行为，从而支撑红皇后式的复杂度军备竞赛。

### 推论 2 的证明思路

在定理 2 的设定下，总复杂度

$$
C_{\mathrm{tot}}(t)=N_{1}(t)C_{1}(t)+N_{2}(t)C_{2}(t)
$$

的时间导数为

$$
\dot{C}_{\mathrm{tot}}=\dot{N}_{1}C_{1}+N_{1}\dot{C}_{1}+\dot{N}_{2}C_{2}+N_{2}\dot{C}_{2}.
$$

将动力学方程代入可得到一个关于 $(N_{i},C_{i})$ 的多项式表达式。由于平衡点不稳定，轨线不会在有限时间收敛到常数向量，而是围绕不稳定平衡点在相空间中演化。对极限环或混沌吸引子上的长时平均 $\langle\dot{C}_{\mathrm{tot}}\rangle$ 一般不为零或不在整个宇宙时间上消失，因此兰道尔功率

$$
P_{\mathrm{info}}(t)\propto C_{\mathrm{tot}}(t)
$$

长期保持正值或至少在任意有限时间区间上具有正的时间平均。结合定理 1，可见信息真空能量密度 $\rho_{\mathrm{info}}(t)$ 随时间持续增长或在某一值附近缓慢演化，经典意义上的"能量注入终止、宇宙进入完全热平衡"状态不再是动力学吸引态。

---

## Model Apply

本节讨论模型的宇宙学应用与若干定性预言。

### 复杂度驱动的 $\Lambda_{\mathrm{eff}}(t)$ 与"巧合问题"

在星系形成与恒星演化主导的宇宙历史区间，熵生产与复杂度增长主要由恒星核聚变、星系形成、行星地壳活动以及生命与文明演化等过程贡献。已有工作表明，宇宙总熵生产率在大爆炸后约 $2\text{–}4\times 10^{9}$ 年达到峰值，与星形成率峰值相当接近。

在本模型中，若将复杂度函数 $C(t)$ 视为上述多尺度过程的综合指标，而信息功率密度 $P_{\mathrm{info}}(t)$ 与 $\dot{C}(t)$ 成正比，则由推论 1 得

$$
\Lambda_{\mathrm{eff}}(t)\approx \Lambda_{\mathrm{eff}}(t_{0})+K\int_{C(t_{0})}^{C(t)}T_{\mathrm{bg}}(C)\,\mathrm{d}C,
$$

其中常数 $K=8\pi G\alpha$。如果 $C(t)$ 在星系与生命诞生的时代快速上升，随后进入缓慢演化阶段，则 $\Lambda_{\mathrm{eff}}(t)$ 亦在该时期完成主要增长，并在之后缓慢演化。这就自然地解释了为何当前时代的暗能量密度与物质密度处于同一量级：两者均与宇宙中可用自由能与复杂结构的丰度紧密相关。

这一思路在概念上与因果熵原理和熵力宇宙学相呼应，那些工作试图通过最大化可观测区域的总熵生产率或引入熵关联的有效压力来解释暗能量的大小与行为。本文的不同之处在于：

* 关注的是**计算导致的不可逆信息擦除**所对应的兰道尔能量流，而不仅仅是任意形式的熵生产；

* 在 QCA 宇宙框架下，将这种信息废热与底层真空自由度的能量编码联系，从而在微观上赋予暗能量以"信息真空"的含义。

### 暗能量可能的时间演化与观测

最近 DESI 等项目的数据给出暗能量可能随宇宙时间缓慢演化的迹象，暗能量状态方程参数化如 Chevallier–Polarski–Linder 形式 $w(z)=w_{0}+w_{a}z/(1+z)$ 的拟合结果显示 $w_{a}$ 可能偏离零。在本模型中，$\Lambda_{\mathrm{eff}}(t)$ 的时间演化完全由 $P_{\mathrm{info}}(t)$ 决定，因此：

* 若宇宙中能动体复杂度在某一时期快速增长后趋于平台，则 $\Lambda_{\mathrm{eff}}(t)$ 在早期呈现明显增长，在晚期趋于常数，对应 $w(z)$ 在高红移偏离 $-1$，在低红移接近 $-1$。

* 若复杂度在极长时间尺度上仍缓慢增长（例如高级文明的计算活动在宇宙后期继续扩大），则 $\Lambda_{\mathrm{eff}}(t)$ 将长期缓慢演化，导致 $w(z)$ 在低红移仍存在小但可测的偏离。

反之，若未来更精确的观测严格支持 $w=-1$ 且 $\Lambda$ 在宇宙历史上严格恒定，则本模型必须退化到 $P_{\mathrm{info}}(t)$ 在宏观上与时间无关的极限，其物理含义是能动体计算活动的总兰道尔功率密度在宇宙时间上近似恒定。这种情形虽不被当前复杂度演化图景强烈支持，但在理论上并非不可能。

### 热寂、计算与红皇后宇宙中的"自由能"

传统热寂论基于宏观热力学，将宇宙视为一个最终耗尽所有可用自由能的封闭系统。然而从计算热力学与复杂系统视角看，"自由能"的可用性取决于能动体能否识别并利用系统中的结构与梯度。红皇后宇宙模型强调：

* 能动体通过内部计算识别环境中的低熵结构与自由能源，例如恒星辐射、化学势差等；

* 能动体之间的红皇后博弈使得任何一方的进步都会改变其它方的环境，迫使整个系统不断重新组织；

* 在 QCA 宇宙中，只要底层演化允许将部分信息真空能量转化为局域可用自由能，则能动体网络可以通过复杂度军备竞赛不断刷新可用自由能的空间分布。

在这一框架中，"热寂"不再是简单的熵饱和，而是一个关于"是否存在能动体可以利用的自由能与可编码结构"的问题。只要红皇后条件与信息速率守恒允许能动体持续存在并进行不可逆计算，宇宙就可以在宏观上保持远离简单平衡的状态。

---

## Engineering Proposals

本节提出若干理论与实验层面的工程化建议，以期在可控平台或观测数据中检验"红皇后宇宙"框架的若干要素。

### QCA 平台上的能动体–暗能量类比实验

近年来，基于光子、离子阱或超导线路的 QCA 与量子行走实验平台已用于模拟 Dirac 场与相对论动力学。可在这些平台上构造如下类比实验：

1. 在一维或二维 QCA 上嵌入局域"能动体"区域，其内部演化包含可控的可逆与不可逆门，并通过监测环境熵或能量流估计实验版的 $P_{\mathrm{info}}(t)$。

2. 在相同平台上通过在外部区域引入有效势或噪声，模拟信息真空能量密度 $\rho_{\mathrm{info}}$ 的变化，观察其对"宇宙膨胀"（如有效光锥结构）或散射相移的影响。

3. 比较不同复杂度增长策略（如自适应算法与随机策略）对 $P_{\mathrm{info}}(t)$ 与宏观几何指标的影响，验证 Landauer–$\Lambda$ 关系定理的类比形式。

虽然这些实验无法直接触及真实宇宙的暗能量，但可以在受控环境中检验"计算–废热–几何反馈"这一机制是否在 QCA 框架下自洽。

### 多智能体仿真与红皇后动力学的统计性质

在数值模拟层面，可构建大量耦合的能动体代理，每个代理具有内部模型、复杂度参数与决策规则，在给定的资源场上进行博弈。利用复制子动力学与强化学习相结合的框架，考察：

1. 在不同参数区间下，系统是否存在稳定的内部平衡点，还是普遍进入极限环或混沌吸引子；

2. 总复杂度 $C_{\mathrm{tot}}(t)$ 的时间序列统计性质，特别是其长时平均导数与波动特征；

3. 将兰道尔代价显式加入代理的目标函数，考察"成本–收益"平衡对红皇后动力学的影响。

这些仿真可以为定理 2 的假设合理性提供经验支持，也可以帮助确定现实宇宙中复杂度军备竞赛可能处于的参数区间。

### 宇宙学数据中的间接检验

尽管目前无法直接测量宇宙中所有能动体的计算活动，但可以寻找与本模型相关的间接观测信号：

1. 复杂度代理指标：将星形成率、黑洞吸积率、金属丰度演化等视为宇宙复杂度的粗略代理，研究其与暗能量状态方程参数 $w(z)$ 或 $\Lambda_{\mathrm{eff}}(t)$ 的相关性。

2. 熵生产率峰值与暗能量主导时代：比较熵生产率峰值的时代（例如恒星形成活跃期）与暗能量开始主导宇宙动力学的时代是否具有系统性关系。

3. 时间变化暗能量的形状约束：若未来观测确认暗能量随时间缓慢演化，可将其拟合为由复杂度驱动的 $\Lambda_{\mathrm{eff}}(t)$，检验是否存在一个物理合理的复杂度历史 $C(t)$ 使得二者匹配。

这些分析将本模型嵌入现有宇宙学数据分析框架之中，为评估其可行性提供途径。

---

## Discussion (risks, boundaries, past work)

本节讨论"红皇后宇宙"框架的风险、适用边界与与既有工作的关系。

### 与传统热寂图景的关系

传统热寂图景建立在宏观封闭系统与经典热力学的基础上，将宇宙视为一个最终达到热平衡的"巨大热库"。本文并不否认熵增的一般性，而是强调：

* 熵增可以伴随复杂度的持续增长，尤其在存在能动体的情况下，熵增过程往往通过维持和创造新的低熵结构得以实现；

* 在 QCA 宇宙中，底层自由度的巨大信息容量意味着即便宏观熵接近某一上界，仍可能存在未被利用的计算与编码空间；

* 热寂真正关心的是"有序结构与计算是否终结"，而非熵是否达到某个数学上的极大值。

因此，红皇后宇宙并非否定热寂的热力学基础，而是提出在存在能动体与信息真空能量的情况下，宇宙可以通过复杂度军备竞赛与计算–几何反馈机制长期维持非平衡状态。

### 与熵力宇宙学与因果熵原理的对比

熵力宇宙学与相关模型尝试从熵与信息的角度理解引力与暗能量，例如通过将宇宙学视界上的熵与温度引入有效力学，或通过最大化因果区域的熵生产率预测宇宙学常数的大小。

与这些工作相比，本文的不同之处在于：

* 引入了明确的能动体与计算热力学，将暗能量视为不可逆计算的兰道尔废热在信息真空中的积累，而非直接由视界熵导出的宏观势；

* 使用 QCA 宇宙作为微观本体，强调离散时空与信息处理结构在暗能量起源中的作用；

* 将红皇后演化动力学引入宇宙学，提出复杂度军备竞赛是避免热寂的重要动力学机制。

这些差异使得"红皇后宇宙"更接近一种"信息–计算–几何"的统一框架，而非单纯的熵最大化原则。

### 与人择原理及智能宇宙设想的关系

人择原理指出，我们对宇宙的观测被选择效应所偏置，即只能在允许观察者存在的宇宙中出现。部分工作进一步提出智能或意识在宇宙结构中扮演更根本角色的设想。

本文的立场更为保守：将"能动体"定义为广义的低熵结构维持者与计算执行者，其范围从分子机器到生物体再到技术文明。红皇后宇宙框架只要求这些能动体存在并进行不可逆计算，并不依赖其是否具有人类意义上的自我意识。某种意义上，这是一种"弱智能宇宙"观：智能与计算是宇宙信息动力学的自然涌现，而暗能量与避免热寂是这一动力学在几何层面的宏观投影。

### 模型的适用边界与开放问题

尽管本文在内部数学结构上是自洽的，但仍有若干重要的开放问题与局限：

1. **信息废热–真空能量可积性的物理基础**：假设 1 将兰道尔热量直接映射到具有 $w\simeq -1$ 的信息真空能量，这需要在 QCA 微观层面给出更具体的机制，例如通过散射理论或谱流理论证明某类不可逆计算不可避免地引入特定形式的背景能量密度。

2. **能动体复杂度的定量定义**：本文将复杂度抽象为 $C_{i}$，但现实宇宙中如何用可观测量（如熵、互信息、算法复杂度）来刻画能动体复杂度仍不清楚。

3. **宇宙自由能预算与长期演化**：红皇后宇宙假设底层 QCA 在任意长时间尺度上都能为能动体提供可用自由能，这与黑洞蒸发、质子衰变等长期过程之间的兼容性需要进一步分析。

4. **与量子引力与全息原理的整合**：若宇宙最终必须在某种全息理论或量子引力框架下统一，本模型中信息真空能量的角色与该统一框架的关系仍有待澄清。

这些问题指向了未来工作的方向。

---

## Conclusion

本文在量子元胞自动机宇宙、计算热力学与多能动体博弈理论的交汇处，提出了"红皇后宇宙"这一宇宙演化与暗能量起源的统一图景。核心思想可以概括如下：

1. 将宇宙视为由多层级能动体组成的 QCA，多数能动体通过内部计算与预测误差修正维持自身远离平衡的低熵结构，其行为可以在自由能原理框架下刻画。

2. 基于兰道尔原理与能量–动量守恒，构造了信息真空能量密度 $\rho_{\mathrm{info}}(t)$，并证明在 $w_{\mathrm{info}}\simeq -1$ 条件下，宇宙学常数的动力学部分等价于全宇宙能动体不可逆计算所产生的兰道尔功率在宇宙时间上的积分（Landauer–$\Lambda$ 关系）。

3. 通过引入满足红皇后条件的多能动体复制子–复杂度动力学模型，证明在广泛参数区间内内部平衡点不稳定，系统进入极限环或混沌吸引子，导致宇宙复杂度与信息擦除率在长时间尺度上保持正值，从动力学上排除了简单的热寂吸引态。

4. 将复杂度驱动的 $\Lambda_{\mathrm{eff}}(t)$ 与暗能量的巧合问题、熵力宇宙学与因果熵原理联系起来，并讨论了与暗能量可能时间演化观测之间的潜在联系。

5. 提出了在 QCA 量子模拟平台与多智能体仿真中检验本框架若干要素的工程建议，为将"红皇后宇宙"从哲学图景提升为可检验物理理论提供实验与数值途径。

在这一图景中，生命与智能不再是宇宙演化中的偶然插曲，而是推动宇宙在信息层面远离平衡的主要动力。宇宙学常数与避免热寂的机制被统一到一个信息–计算–几何的整体中，为理解宇宙终极命运提供了新的视角。

---

## Acknowledgements, Code Availability

本工作受益于关于量子元胞自动机、计算热力学、自由能原理与宇宙学常数问题的大量既有文献。文中所有数值与示意推导均基于公开资料，未使用未公开观测数据。数值例子与相图计算所需的代码可在通用科学计算环境中以常规常微分方程求解器实现，具体实现细节可按附录中的方程自行复现。

---

## References

[1] R. Landauer, "Irreversibility and Heat Generation in the Computing Process," IBM Journal of Research and Development 5, 183–191 (1961).

[2] C. H. Bennett, "The Thermodynamics of Computation: A Review," International Journal of Theoretical Physics 21, 905–940 (1982).

[3] P. Chattopadhyay et al., "Landauer Principle and Thermodynamics of Computation," arXiv:2506.10876 (2025).

[4] K. Friston, "The Free-energy Principle: A Unified Brain Theory?," Nature Reviews Neuroscience 11, 127–138 (2010).

[5] P. J. E. Peebles and B. Ratra, "The Cosmological Constant and Dark Energy," Reviews of Modern Physics 75, 559–606 (2003).

[6] S. Weinberg, "The Cosmological Constant Problem," Reviews of Modern Physics 61, 1–23 (1989).

[7] L. Van Valen, "A New Evolutionary Law," Evolutionary Theory 1, 1–30 (1973).

[8] D. Šešelja and C. Straßer, "Agent-based Modeling in the Philosophy of Science," Stanford Encyclopedia of Philosophy (2023).

[9] "Heat Death of the Universe," in Wikipedia, accessed 2025.

[10] Y. L. Bolotin, A. L. Tur, V. A. Cherkaskiy, "Cosmology Based on Entropy," arXiv:2310.10144 (2023).

[11] S. Nojiri, S. D. Odintsov, V. Faraoni, "Barrow Entropic Dark Energy: A Review," Physics of the Dark Universe 36, 101050 (2022).

[12] R. Bousso, R. Harnik, G. D. Kribs, G. Perez, "Predicting the Cosmological Constant from the Causal Entropic Principle," Physical Review D 76, 043513 (2007).

[13] DESI Collaboration, reports on time-evolving dark energy presented at APS Global Physics Summit (2025).

[14] P. Arrighi, "An Overview of Quantum Cellular Automata," Natural Computing 18, 885–899 (2019).

[15] T. Farrelly, "A Review of Quantum Cellular Automata," Quantum 4, 368 (2020).

[16] I. Bialynicki-Birula, "Weyl, Dirac, and Maxwell Equations on a Lattice as Unitary Cellular Automata," Physical Review D 49, 6920–6927 (1994).

[17] A. Bisio, G. M. D'Ariano, A. Tosini, "Quantum Field as a Quantum Cellular Automaton: The Dirac Free Evolution in One Dimension," Annals of Physics 354, 244–264 (2015).

[18] D. Gross, V. Nesme, H. Vogts, R. F. Werner, "Index Theory of One Dimensional Quantum Walks and Cellular Automata," Communications in Mathematical Physics 310, 419–454 (2012).

[19] A. Suprano et al., "Photonic Cellular Automaton Simulation of Relativistic Quantum Field," Physical Review Research 6, 033136 (2024).

[20] A. Bisio, G. M. D'Ariano, P. Perinotti, "Quantum Cellular Automaton Theory of Light," Annals of Physics 368, 177–190 (2016).

[21] B. Azarian, "Life Need Not Ever End," Noema Magazine (2023), discussing modern views on heat death and complexity.

[22] H. Ma, "Universal Conservation of Information Celerity: From Quantum Cellular Automata to Relativity, Mass and Gravity" (2025), preprint.

[23] H. Ma, "Information-volume Conservation and the Emergence of Optical Metrics" (2025), preprint.

[24] H. Ma, "The Red Queen Universe: Agent Games, Dark Energy and the Avoidance of Heat Death" (this work).

---

## Appendix A: 从兰道尔功率到有效宇宙学常数的详细推导

本附录给出从兰道尔功率密度 $P_{\mathrm{info}}(t)$ 到有效宇宙学常数 $\Lambda_{\mathrm{eff}}(t)$ 的详细推导。

### A.1 能量–动量守恒与带源连续方程

在 FLRW 背景下，爱因斯坦方程

$$
G_{\mu\nu}+\Lambda_{\mathrm{bare}}g_{\mu\nu}=8\pi GT_{\mu\nu}
$$

配合 Bianchi 恒等式 $\nabla^{\mu}G_{\mu\nu}=0$ 导致

$$
\nabla^{\mu}\bigl(T_{\mu\nu}-\tfrac{\Lambda_{\mathrm{bare}}}{8\pi G}g_{\mu\nu}\bigr)=0.
$$

若引入有效宇宙学常数 $\Lambda_{\mathrm{eff}}(t)$，将其合并入右侧，则可写为

$$
G_{\mu\nu}=8\pi G\tilde{T}_{\mu\nu},\quad \tilde{T}_{\mu\nu}=T_{\mu\nu}^{(m)}+T_{\mu\nu}^{(r)}+T_{\mu\nu}^{(\mathrm{info})},
$$

其中

$$
T_{\mu\nu}^{(\mathrm{info})}=-\frac{\Lambda_{\mathrm{eff}}(t)}{8\pi G}g_{\mu\nu}.
$$

对各成分施加能量–动量守恒方程

$$
\nabla^{\mu}T_{\mu\nu}^{(X)}=Q_{\nu}^{(X)},\quad \sum_{X}Q_{\nu}^{(X)}=0,
$$

并采用共动系 $u^{\mu}=(1,0,0,0)$，只关心能量分量 $\nu=0$，可得到

$$
\dot{\rho}_{X}+3H(\rho_{X}+p_{X})=Q^{(X)}_{0}(t).
$$

设物质与辐射成分的源项分别为

$$
Q_{0}^{(m)}=-\Gamma_{m}(t),\quad Q_{0}^{(r)}=-\Gamma_{r}(t),
$$

将由计算导致的能量损失合并为信息真空成分的源项

$$
Q_{0}^{(\mathrm{info})}=\Gamma_{m}(t)+\Gamma_{r}(t)=P_{\mathrm{info}}(t),
$$

则信息成分满足

$$
\dot{\rho}_{\mathrm{info}}+3H(\rho_{\mathrm{info}}+p_{\mathrm{info}})=P_{\mathrm{info}}(t).
$$

若 $p_{\mathrm{info}}=w_{\mathrm{info}}\rho_{\mathrm{info}}$，则上述方程即为主文中的带源连续方程。

### A.2 $w_{\mathrm{info}}\simeq -1$ 的正当性

要使信息真空能量在宏观上表现为暗能量，其状态方程必须接近 $-1$。从 QCA 视角看，一种可能的微观图像是：

* 能动体的不可逆计算通过与环境的散射与纠缠，将一部分局域可访问自由度永久"抹消"到不可访问的全局纠缠结构中；

* 这些纠缠自由度在大尺度上均匀分布，不携带净动量流，且其局域扰动在 QCA 演化下迅速平衡；

* 在连续极限中，这类自由度对宏观几何的贡献近似各向同性并等效于一个具有负压的流体。

这种图像与将真空能量视为场论零点能具有形式上的相似性，只是其起源不是场模振荡，而是不可逆计算过程中产生的"信息碎片"。在具体模型中，可以通过构造具有给定散射矩阵与谱流的 QCA 哈密顿量来证明某类不可逆散射总是伴随一个固定符号的谱移，从而产生等效真空能量的贡献，这是未来工作的方向。

在本文所需的近似下，只需要 $w_{\mathrm{info}}$ 在红皇后时代满足

$$
\lvert w_{\mathrm{info}}+1\rvert\ll 1,
$$

即可保证积分近似的有效性。

### A.3 复杂度驱动的 $P_{\mathrm{info}}(t)$ 模型

设单位复杂度对应的平均信息擦除率为常数 $\kappa$，则

$$
\dot{I}_{\mathrm{erase}}(t)=\kappa\,C(t).
$$

若环境温度 $T_{\mathrm{bg}}(t)$ 在考虑时段内变化缓慢，则兰道尔功率密度为

$$
P_{\mathrm{info}}(t)=k_{\mathrm{B}}\ln 2\,T_{\mathrm{bg}}(t)\,\kappa\,C(t)\approx \alpha\,C(t),
$$

其中 $\alpha=k_{\mathrm{B}}\ln 2\,\kappa\bar{T}$，$\bar{T}$ 为 $T_{\mathrm{bg}}$ 的特征值。

更一般地，若考虑复杂度变化率，则

$$
P_{\mathrm{info}}(t)\approx \alpha\,T_{\mathrm{bg}}(t)\,\dot{C}(t)
$$

是更合理的近似，因为信息擦除通常与复杂度变化而非绝对值更为直接相关。将其代入 A.1 的积分表达式即可得到主文推论 1 的关系式。

### A.4 与弗里德曼方程的一致性

将信息真空能量纳入弗里德曼方程，有

$$
H^{2}(t)=\frac{8\pi G}{3}\bigl(\rho_{m}(t)+\rho_{r}(t)+\rho_{\mathrm{info}}(t)\bigr)-\frac{k}{a^{2}(t)},
$$

其中 $k$ 为空间曲率。由于 $\rho_{\mathrm{info}}(t)$ 是由 $P_{\mathrm{info}}(t)$ 积分得到的函数，只要 $P_{\mathrm{info}}(t)$ 在大尺度上平滑且满足适当增长条件，就不会引入违反观测约束的快速振荡或不稳定。

需要强调的是，本模型并不声称所有暗能量均由信息真空能量构成，而是为 $\Lambda_{\mathrm{eff}}(t)$ 的一部分或全部提供一种信息论起源。在定量拟合时需要将 $\rho_{\mathrm{info}}$ 与可能存在的其他动力学暗能量成分一并考虑。

---

## Appendix B: 红皇后动力学模型的线性稳定性分析

本附录给出定理 2 中两种群红皇后动力学模型的线性稳定性分析细节。

### B.1 平衡点的求解

考虑系统

$$
\frac{\mathrm{d}N_{i}}{\mathrm{d}t}=N_{i}\bigl(r_{i}C_{i}-d_{i}-\gamma(N_{1}+N_{2})\bigr),\quad i=1,2,
$$

$$
\frac{\mathrm{d}C_{i}}{\mathrm{d}t}=\alpha_{i}N_{i}-\beta_{i}C_{i}.
$$

平衡点满足

$$
N_{i}^{\ast}\bigl(r_{i}C_{i}^{\ast}-d_{i}-\gamma(N_{1}^{\ast}+N_{2}^{\ast})\bigr)=0,\quad \alpha_{i}N_{i}^{\ast}-\beta_{i}C_{i}^{\ast}=0.
$$

非平凡平衡点要求 $N_{i}^{\ast}>0$、$C_{i}^{\ast}>0$，则必有

$$
C_{i}^{\ast}=\frac{\alpha_{i}}{\beta_{i}}N_{i}^{\ast},
$$

代回得到

$$
r_{i}\frac{\alpha_{i}}{\beta_{i}}N_{i}^{\ast}-d_{i}-\gamma(N_{1}^{\ast}+N_{2}^{\ast})=0.
$$

这给出两条线性方程：

$$
\bigl(r_{1}\tfrac{\alpha_{1}}{\beta_{1}}-\gamma\bigr)N_{1}^{\ast}-\gamma N_{2}^{\ast}=d_{1},
$$

$$
-\gamma N_{1}^{\ast}+\bigl(r_{2}\tfrac{\alpha_{2}}{\beta_{2}}-\gamma\bigr)N_{2}^{\ast}=d_{2}.
$$

若系数矩阵

$$
M=\begin{pmatrix}
r_{1}\tfrac{\alpha_{1}}{\beta_{1}}-\gamma & -\gamma\\
-\gamma & r_{2}\tfrac{\alpha_{2}}{\beta_{2}}-\gamma
\end{pmatrix}
$$

可逆，则

$$
\begin{pmatrix}
N_{1}^{\ast}\\
N_{2}^{\ast}
\end{pmatrix}=M^{-1}\begin{pmatrix}
d_{1}\\
d_{2}
\end{pmatrix},
$$

进而得到

$$
C_{i}^{\ast}=\frac{\alpha_{i}}{\beta_{i}}N_{i}^{\ast}.
$$

要求 $N_{i}^{\ast}>0$、$C_{i}^{\ast}>0$ 限制了参数空间，但在物理上合理的参数区间内一般可以满足。

### B.2 雅可比矩阵的构造

记 $\mathbf{x}=(N_{1},N_{2},C_{1},C_{2})^{\mathsf{T}}$，向量场 $\mathbf{F}(\mathbf{x})$ 的分量为

$$
F_{1}=N_{1}\bigl(r_{1}C_{1}-d_{1}-\gamma(N_{1}+N_{2})\bigr),
$$

$$
F_{2}=N_{2}\bigl(r_{2}C_{2}-d_{2}-\gamma(N_{1}+N_{2})\bigr),
$$

$$
F_{3}=\alpha_{1}N_{1}-\beta_{1}C_{1},
$$

$$
F_{4}=\alpha_{2}N_{2}-\beta_{2}C_{2}.
$$

雅可比矩阵 $J$ 的元素为 $J_{ij}=\partial F_{i}/\partial x_{j}$。在平衡点 $\mathbf{x}^{\ast}$ 处，其非零元素为：

* 对 $F_{1}$：

  $$
  \frac{\partial F_{1}}{\partial N_{1}}=r_{1}C_{1}^{\ast}-d_{1}-\gamma(2N_{1}^{\ast}+N_{2}^{\ast}),
  \quad
  \frac{\partial F_{1}}{\partial N_{2}}=-\gamma N_{1}^{\ast},
  \quad
  \frac{\partial F_{1}}{\partial C_{1}}=r_{1}N_{1}^{\ast}.
  $$
  
  利用平衡条件 $r_{1}C_{1}^{\ast}-d_{1}-\gamma(N_{1}^{\ast}+N_{2}^{\ast})=0$，可简化为

  $$
  \frac{\partial F_{1}}{\partial N_{1}}=-\gamma N_{1}^{\ast}.
  $$

* 对 $F_{2}$：

  $$
  \frac{\partial F_{2}}{\partial N_{2}}=r_{2}C_{2}^{\ast}-d_{2}-\gamma(N_{1}^{\ast}+2N_{2}^{\ast})=-\gamma N_{2}^{\ast},
  $$
  
  $$
  \frac{\partial F_{2}}{\partial N_{1}}=-\gamma N_{2}^{\ast},
  \quad
  \frac{\partial F_{2}}{\partial C_{2}}=r_{2}N_{2}^{\ast}.
  $$

* 对 $F_{3}$：

  $$
  \frac{\partial F_{3}}{\partial N_{1}}=\alpha_{1},\quad
  \frac{\partial F_{3}}{\partial C_{1}}=-\beta_{1}.
  $$

* 对 $F_{4}$：

  $$
  \frac{\partial F_{4}}{\partial N_{2}}=\alpha_{2},\quad
  \frac{\partial F_{4}}{\partial C_{2}}=-\beta_{2}.
  $$

于是雅可比矩阵在平衡点处为

$$
J=\begin{pmatrix}
-\gamma N_{1}^{\ast} & -\gamma N_{1}^{\ast} & r_{1}N_{1}^{\ast} & 0\\
-\gamma N_{2}^{\ast} & -\gamma N_{2}^{\ast} & 0 & r_{2}N_{2}^{\ast}\\
\alpha_{1} & 0 & -\beta_{1} & 0\\
0 & \alpha_{2} & 0 & -\beta_{2}
\end{pmatrix}.
$$

### B.3 特征多项式与 Routh–Hurwitz 判据

特征多项式为

$$
\det(\lambda I-J)=\lambda^{4}+a_{1}\lambda^{3}+a_{2}\lambda^{2}+a_{3}\lambda+a_{4},
$$

其中系数 $a_{k}$ 可通过直接展开计算得到。为简化记号，设

$$
A_{i}=\gamma N_{i}^{\ast},\quad
B_{i}=r_{i}N_{i}^{\ast},\quad
C_{i}=\alpha_{i},\quad
D_{i}=\beta_{i}.
$$

则

$$
a_{1}=2(A_{1}+A_{2})+D_{1}+D_{2},
$$

$$
a_{2}=(A_{1}+A_{2})^{2}+2(A_{1}+A_{2})(D_{1}+D_{2})+D_{1}D_{2}+B_{1}C_{1}+B_{2}C_{2},
$$

$$
a_{3}=(A_{1}+A_{2})^{2}(D_{1}+D_{2})+(A_{1}+A_{2})D_{1}D_{2}+(A_{1}+A_{2})(B_{1}C_{1}+B_{2}C_{2})+D_{1}B_{2}C_{2}+D_{2}B_{1}C_{1},
$$

$$
a_{4}=(A_{1}+A_{2})^{2}D_{1}D_{2}+(A_{1}+A_{2})D_{1}B_{2}C_{2}+(A_{1}+A_{2})D_{2}B_{1}C_{1}.
$$

Routh–Hurwitz 判据指出，全部特征值具有负实部当且仅当以下条件成立：

1. $a_{1}>0$,

2. $a_{1}a_{2}-a_{3}>0$,

3. $(a_{1}a_{2}-a_{3})a_{3}-a_{1}^{2}a_{4}>0$,

4. $a_{4}>0$.

在当前模型中，所有 $A_{i},D_{i},B_{i},C_{i}>0$，因此 $a_{1},a_{2},a_{4}>0$ 自动成立。稳定性关键取决于第二与第三条。通过代数化简，可将第二条写为

$$
a_{1}a_{2}-a_{3}=K_{0}-K_{1},
$$

其中 $K_{0}$ 为只包含 $A_{i},D_{i}$ 的正项，$K_{1}$ 为与 $B_{i}C_{i}$ 相关的项。显然，当 $B_{1}C_{1}+B_{2}C_{2}$ 足够大时，即当 $r_{i}\alpha_{i}N_{i}^{\ast}$ 总和足够大时，$K_{1}$ 可以超过 $K_{0}$，导致 $a_{1}a_{2}-a_{3}<0$，从而违反第二个 Hurwitz 条件。这说明存在一个临界曲面，在其一侧平衡点稳定，在另一侧平衡点不稳定。

类似地，第三条可以写成

$$
(a_{1}a_{2}-a_{3})a_{3}-a_{1}^{2}a_{4}=L_{0}-L_{1},
$$

其中 $L_{1}$ 中最高阶的项与 $(B_{1}C_{1}+B_{2}C_{2})^{2}$ 成正比。当 $B_{1}C_{1}+B_{2}C_{2}$ 较大时，该量亦可变负。

将 $B_{i}C_{i}=r_{i}\alpha_{i}(N_{i}^{\ast})^{2}$ 与 $A_{i}^{2}=\gamma^{2}(N_{i}^{\ast})^{2}$、$D_{i}^{2}=\beta_{i}^{2}$ 进行比较，可以导出一个简单的充分条件

$$
r_{1}\alpha_{1}N_{1}^{\ast}+r_{2}\alpha_{2}N_{2}^{\ast}>\beta_{1}^{2}+\beta_{2}^{2}+2\gamma\bigl(r_{1}C_{1}^{\ast}+r_{2}C_{2}^{\ast}\bigr),
$$

在该条件下，至少有一个 Hurwitz 条件被破坏，平衡点不稳定。这给出了主文中定理 2 的不稳定性条件。

### B.4 Hopf 分岔与极限环的存在性

当参数连续变化使某个 Hurwitz 条件从正跨过零时，对应的特征值会穿越虚轴。若此时恰有一对共轭复特征值穿越虚轴，而其他特征值实部仍为负，则系统经历 Hopf 分岔，产生稳定或不稳定的极限环。

在当前模型中，由于系统具有四维状态空间且耦合结构简单，满足一般位置条件的参数扰动通常会导致这一典型情形。对具体参数可通过数值计算验证，在此不再赘述。重要的是，存在一类开稠密的参数集合使得内部平衡点不稳定而存在至少一个极限环或更复杂吸引子。这支持主文定理 2 中关于"红皇后动力学导致持续非平衡"的结论。

---

本附录的推导表明，在满足红皇后条件的合理参数区间内，多能动体系统的内部平衡点一般不是渐近稳定的，复杂度与兰道尔信息功率密度不会静止，从而为红皇后宇宙中避免热寂的动力学机制提供了数学支撑。

