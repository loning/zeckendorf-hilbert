# 概率的涌现：从量子元胞自动机的全局幺正性推导波恩规则

The Emergence of Probability: Deriving the Born Rule from Global Unitarity and Observer-Relative States in Quantum Cellular Automata

---

## Abstract

量子元胞自动机（quantum cellular automaton, QCA）给出一种离散、局域、幺正的宇宙本体论图景：全局状态在离散时间步之间按确定性的幺正算子更新，不含任何本征随机过程。另一方面，实验室量子力学以波恩规则为核心，将测量结果视为固有概率事件。二者之间的张力构成量子测量问题的核心。

本文在 QCA 框架下，引入"有限信息容量的局域观察者"及其环境纠缠结构，给出一套纯组合学的概率涌现机制。具体而言，在一个具有严格有限传播速度与全局幺正性的 QCA 宇宙中：测量过程被建模为被测系统、观察者记忆寄存器与环境之间的局域幺正耦合；退相干（einselection）选出稳定的指针态；观察者由于信息视界与记忆容量限制，只能访问与自身记录相容的宏观分支而无法区分其下的所有微观 QCA 基态。对这些微观基态施加环境辅助不变性（environment-assisted invariance, envariance）的对称性论证，并结合"等本体权重"假设，可以将复振幅的模长解释为微观路径简并度的平方根。由此证明：观察者对各测量结果赋予的主观概率等于与之相容的微观构型数在全部可达构型中的比例，即标准波恩权重 $p_k = \lvert \psi_k \rvert^2$。

在理性一致性、公理化的意义上，本文给出如下结果：在维数大于等于三的局域希尔伯特空间内，若要求（i）全局动力学由局域 QCA 幺正演化给出，（ii）测量概率满足非情境性与环境不敏感性，（iii）不存在超光速信号传播，则 Gleason 型定理与 QCA 微观计数共同推出波恩规则为唯一可行的概率标度。波函数坍缩在此被重新理解为：局域观察者在全局幺正态上的贝叶斯条件化与自定位（self-location）更新，而非基本动力学的非线性中断。因而，量子概率不是自然界的本质成分，而是有限观察者在离散全息纠缠网络中进行自我定位的统计必然。

---

## Keywords

量子元胞自动机；波恩规则；量子测量问题；环境辅助不变性；退相干；相对态诠释；自定位不确定性；信息视界

---

## Introduction & Historical Context

### 1.1 量子测量问题与波恩规则的地位

标准量子理论由两套看似不相容的演化律组成：孤立体系的时间演化由线性、幺正的薛定谔方程控制，而测量过程则由非线性、随机的"坍缩"规则描述。实验上得到的频率符合波恩公式 $p_k = \lvert \langle k \vert \psi \rangle \rvert^2$，然而这一公式在多数教科书中被直接作为独立公理引入，并未从更原始的结构中推导。

退相干理论显示，系统与环境的耦合导致相干项在有效描述中迅速抑制，从而选出稳定的指针态并解释经典轨迹的涌现。退相干已在数学和实验上被系统发展，并在量子到经典过渡的研究中占据中心位置。然而，多数作者承认：退相干本身并不生成具体数值的概率，而是在假定波恩规则成立的前提下刻画干涉项如何被环境"湮灭"。

由此，一个自然的问题是：波恩规则是否可以在不先验假设概率公理的前提下，从更为基本的结构出发导出？

### 1.2 既有波恩规则推导方案

围绕波恩规则的推导已形成广泛文献。Gleason 定理在维数至少为三的希尔伯特空间中证明：若对投影测度赋予的概率满足非情境性与可列可加性，则该概率必然由某个密度算符通过迹公式实现，即实质上等价于波恩规则。Deutsch 与 Wallace 等则在 Everett 诠释下，借助古典决策理论，论证理性主体在多世界分支上的效用最大化要求波恩权重。

Zurek 提出的环境辅助不变性（envariance）路线，将系统与环境的纠缠对称性作为出发点：在完美纠缠态下，对系统施加的某些酉变换可以通过对环境施加另一酉变换"抵消"，从而使整体态不变。借助此对称性以及对等幅叠加态的路径细分，可在形式上推导出 $p_k \propto \lvert \psi_k \rvert^2$。另一些工作尝试从非情境概率假设、无超光速信号原则等推出波恩规则。

与此同时，对这些推导的批评指出：所有已知方案都在显性或隐性地引入了与波恩规则近似等价的假设，例如概率的连续性、加性或对测量上下文的独立性，因此严格意义上的"无额外公理"推导仍是开放问题。

### 1.3 QCA 与元胞自动机诠释

与此平行，关于量子理论是否可以还原为离散、局域、确定性的元胞自动机动力学的探讨不断发展。't Hooft 提出的元胞自动机诠释，将量子态视为在更底层经典自动机上的统计包络，寻求一种本质决定论的微观理论。另一方面，D'Ariano、Bisio、Perinotti 等构造的量子元胞自动机（QCA）模型表明，在满足局域性、齐次性与各向同性的离散格点上，可以涌现出 Weyl、Dirac 与 Maxwell 方程的连续极限，使 QCA 成为"宇宙即量子计算"设想的具体数学实现。

在 QCA 宇宙图景中，全局状态 $\lvert \Psi_t \rangle$ 按照某个局域幺正算子 $U$ 在离散时间步上演化：$\lvert \Psi_{t+1} \rangle = U \lvert \Psi_t \rangle$。动力学严格确定，没有内在随机性。测量所表现出的概率特征，从何而来，是这一图景中最紧要的基础问题。

### 1.4 本文目标与基本思路

本文的目标是在如下前提下给出波恩规则的涌现性推导：

1. 宇宙由一个局域、平移不变、幺正的 QCA 描述；

2. 观察者是 QCA 上具有有限信息容量的局域子系统，其"记录"实现为经环境退相干选出的指针态；

3. 概率被理解为观察者在全局幺正态上的自定位不确定性，而非本体论随机过程。

在此框架中，测量被建模为被测系统 $S$、观察者记忆寄存器 $O$ 与环境 $E$ 之间的局域纠缠过程，随后环境引发的退相干使得不同测量结果分支之间的干涉在 $O$ 的可及算符上不可见。我们引入一个"等本体权重假设"：在 QCA 的本体基底中，每一个正交的微观构型（或路径）具有相同本体权重。借助 QCA 的离散性，可以将复振幅写成等权重微观态叠加的简并度平方根，从而将概率解释为"与某一宏观记录相容的微观构型数目"的归一化比值。

为了使这一构造具有普适性与唯一性，本文在 Gleason 定理、无超光速信号约束和 envariance 对称性的支撑下证明：在 QCA 宇宙中，只要要求局域测量概率满足非情境性与环境不敏感性，波恩规则即为唯一与全局幺正性、局域性及观察者有限性相容的概率赋值。

---

## Model & Assumptions

### 2.1 QCA 宇宙与本体基底

设宇宙被建模为定义在离散格点集合 $\Lambda \subset \mathbb{Z}^d$ 上的量子元胞自动机。每个格点 $x \in \Lambda$ 携带有限维 Hilbert 空间 $\mathcal{H}_x \simeq \mathbb{C}^{d_{\mathrm{cell}}}$，全局 Hilbert 空间为张量积 $\mathcal{H} = \bigotimes_{x \in \Lambda} \mathcal{H}_x$。QCA 动力学由一族离散时间幺正算子 $U$ 给出，满足：

1. 局域性：$U$ 可以分解为作用在有限邻域上的局域幺正门的有限深度电路；

2. 齐次性与平移不变性：格点之间的局域规则相同；

3. 有限传播速度：存在 Lieb–Robinson 速度 $v_{\mathrm{LR}}$ 使得任一局域扰动的支持在时间 $t$ 内被限制在半径约为 $v_{\mathrm{LR}} t$ 的有效光锥中。

选定每个元胞的本征基底 $\{ \lvert \gamma_x \rangle \}$，全局本体基底由张量积 $\lvert \gamma \rangle = \bigotimes_{x} \lvert \gamma_x \rangle$ 构成。在本文中，"微观构型"与"本体基矢"一词等价。

**等本体权重假设（A1）**：在 QCA 本体论中，每一个正交的本体基态 $\lvert \gamma \rangle$ 具有相等的基础权重；任意概率性陈述都源自在某个条件下对这些基态进行计数或加权。

该假设对应 't Hooft 等元胞自动机方案中"本征序列等价"的思想，同时与 QCA 中对本体基底的平移不变性与局域规则的同一性相协调。

### 2.2 系统–观察者–环境的划分

在全局 QCA 宇宙中，选取一个有限区域 $\Lambda_S$ 作为被测系统 $S$，另一有限区域 $\Lambda_O$ 作为观察者及其测量仪器 $O$，其余格点并入环境 $E$。相应 Hilbert 空间分解为

$$
\mathcal{H} \simeq \mathcal{H}_S \otimes \mathcal{H}_O \otimes \mathcal{H}_E.
$$

观察者 $O$ 的 Hilbert 空间分为"记录子空间"与"其余自由度"：

$$
\mathcal{H}_O \simeq \mathcal{H}_M \otimes \mathcal{H}_{O,\mathrm{rest}},
$$

其中 $\mathcal{H}_M$ 的一组正交基 $\{ \lvert M_j \rangle \}$ 实现经典测量结果的记忆。退相干理论与环境诱导超选（einselection）表明，对于宏观仪器而言，存在一组"指针态"在环境监测下保持鲁棒，这些态在实际测量中扮演经典记录的角色。

**有限信息容量假设（A2）**：观察者记录子空间 $\mathcal{H}_M$ 维数有限；其对宇宙的知识与记忆必须编码在有限个"可区分记录" $\lvert M_j \rangle$ 上。我们以 $\log_2 \dim \mathcal{H}_M$ 作为观察者可存储经典信息的上界。

### 2.3 测量相互作用与退相干

考虑被测系统初态

$$
\lvert \psi_S \rangle = \sum_{k} \alpha_k \lvert s_k \rangle_S,
$$

其中 $\{ \lvert s_k \rangle \}$ 是待测可观测量的本征基（或相应的指针态基）。观察者与环境初始处于某一参考态

$$
\lvert \Psi_0 \rangle = \lvert \psi_S \rangle \otimes \lvert M_{\mathrm{ready}} \rangle_O \otimes \lvert E_0 \rangle_E.
$$

测量过程由 QCA 上的一段局域幺正演化实现，可抽象为一个在有限时间内支持于 $\Lambda_S \cup \Lambda_O \cup \Lambda_{E,\mathrm{near}}$ 的幺正算子 $U_{\mathrm{meas}}$。其理想形式满足

$$
U_{\mathrm{meas}} \bigl( \lvert s_k \rangle_S \otimes \lvert M_{\mathrm{ready}} \rangle_O \otimes \lvert E_0 \rangle_E \bigr)
= \lvert s_k \rangle_S \otimes \lvert M_k \rangle_O \otimes \lvert \tilde{E}_k \rangle_E.
$$

对叠加态线性延拓后得到测量前后状态

$$
\lvert \Psi_{\mathrm{pre}} \rangle = \sum_k \alpha_k \lvert s_k \rangle_S \otimes \lvert M_{\mathrm{ready}} \rangle_O \otimes \lvert E_0 \rangle_E,
$$

$$
\lvert \Psi_{\mathrm{post}} \rangle = U_{\mathrm{meas}} \lvert \Psi_{\mathrm{pre}} \rangle
= \sum_k \alpha_k \lvert s_k \rangle_S \otimes \lvert M_k \rangle_O \otimes \lvert \tilde{E}_k \rangle_E.
$$

随后，在 QCA 全局演化下，环境与 $S$–$O$ 复合体继续耦合，产生进一步的退相干，使得不同 $k$ 分支的环境态近乎正交，满足

$$
\langle \tilde{E}_k(t) \vert \tilde{E}_\ell(t) \rangle \approx \delta_{k\ell},
$$

并保持指针态 $\lvert M_k \rangle$ 的鲁棒性。于是，对观察者局域可观测量而言，系统–仪器–环境的全局纯态与一个经典混合态在可观测统计上无法区分。

### 2.4 概率公理与对称性假设

为了从结构上推导具体的概率权重，需要对"观察者如何在分支之间分配主观概率"作出若干一般性要求。

**非情境性（A3）**：设 $\{ P_k \}$ 为在子空间 $\mathcal{H}_S \otimes \mathcal{H}_M$ 内的一组互斥完全集投影算符，且 $\sum_k P_k = I$。观察者对结果 $k$ 赋予的概率 $p_k$ 仅依赖于当前状态在 $P_k$ 上的投影，而不依赖在更大 Hilbert 空间中对这一测量的嵌入方式。这一假设与 Gleason 定理中对概率测度的非情境性要求相同。

**环境不敏感性（A4）**：对任一测量方案，只要系统–观察者的约化态 $\rho_{S O}$ 不变，则观察者对各结果的概率分配不因环境态的改变而改变。该假设与 envariance 推导及 Everett 框架中"纯粹环境变换不应影响局域概率"的原则一致。

**有限理性与连续性（A5）**：对给定测量基 $\{ \lvert s_k \rangle \}$，若状态 $\lvert \psi \rangle$ 被一个小范数扰动 $\lvert \psi' \rangle$ 替换，则合理的概率分配 $p_k(\psi)$ 与 $p_k(\psi')$ 之间不应发生不连续跃变。形式上，$p_k$ 是关于状态的连续函数。

**无超光速信号约束（A6）**：QCA 动力学与测量规则的组合不得允许利用纠缠与局域操作实现超光速经典信息传递。这一原则在广泛文献中被用来约束非线性量子演化与非常规概率规则。

通过这些结构性假设，本文将在 QCA 宇宙内推导出波恩规则，并讨论其唯一性。

---

## Main Results (Theorems and Statements)

为便于表述，本节先给出主要定理与命题，证明细节置于后文与附录。

### 定理 1（QCA 测量的相对态结构）

在满足 A1–A2 的 QCA 宇宙中，考虑任一有限维被测系统 $S$ 与观察者记忆寄存器 $M$，以及实现理想测量的局域幺正算子 $U_{\mathrm{meas}}$。则对任一初态

$$
\lvert \psi_S \rangle = \sum_k \alpha_k \lvert s_k \rangle_S, \quad
\lvert \Psi_0 \rangle = \lvert \psi_S \rangle \otimes \lvert M_{\mathrm{ready}} \rangle_O \otimes \lvert E_0 \rangle_E,
$$

测量与随后的退相干过程产生的全局态可写为 Schmidt 分解形式

$$
\lvert \Psi_{\mathrm{post}} \rangle
= \sum_k \alpha_k \lvert s_k \rangle_S \otimes \lvert M_k \rangle_O \otimes \lvert E_k \rangle_E,
$$

其中 $\{ \lvert E_k \rangle \}$ 在环境 Hilbert 空间内近乎正交。观察者的主观"所在分支"可被建模为对这组带标签项的自定位不确定性。

### 定理 2（离散 QCA 中的等幅分支与等概率）

在定理 1 的设定下，若 $\lvert \alpha_k \rvert^2 = N_k / N$ 为有理数，且 $N = \sum_k N_k$ 为正整数，则存在一个环境 Hilbert 空间的细粒化分解，使得

$$
\lvert \Psi_{\mathrm{post}} \rangle
= \frac{1}{\sqrt{N}}
\sum_{k} \sum_{j=1}^{N_k}
\lvert s_k \rangle_S \otimes \lvert M_k \rangle_O \otimes \lvert \varepsilon_{k,j} \rangle_E,
$$

其中全部 $\lvert \varepsilon_{k,j} \rangle$ 两两正交，且每一项具有相同复振幅模长 $1/\sqrt{N}$。若进一步假设：

1. 每一微观构型 $\lvert s_k, M_k, \varepsilon_{k,j} \rangle$ 的本体权重相等（A1）；

2. 对环境子空间的任意置换在物理上是 envariant 的，对应分支在观察者视角下等价；

则观察者自定位在携带记录 $M_k$ 的分支上的主观概率为

$$
p_k = \frac{N_k}{N} = \lvert \alpha_k \rvert^2.
$$

### 定理 3（连续极限与一般 Born 规则）

在 A1–A5 假设下，将定理 2 中的有理比 $N_k/N$ 推广到一般复振幅情况：对任一归一化态

$$
\lvert \psi_S \rangle = \sum_k \alpha_k \lvert s_k \rangle,
$$

存在一列有理数 $\{ N_k^{(n)}/N^{(n)} \}$ 使得 $N_k^{(n)}/N^{(n)} \to \lvert \alpha_k \rvert^2$。对每一 $n$ 按定理 2 构造对应的等幅 QCA 微观态，并令概率分配 $p_k^{(n)} = N_k^{(n)}/N^{(n)}$。连续性假设 A5 保证极限 $p_k = \lim_{n\to\infty} p_k^{(n)}$ 存在且满足

$$
p_k = \lvert \alpha_k \rvert^2.
$$

因此，波恩规则对所有纯态成立。

### 定理 4（Gleason 型唯一性与非情境性）

在维数至少为三的局域 Hilbert 空间上，假定对每个投影算符 $P$ 赋予的概率 $p(P)$ 满足：

1. 非负性与归一性；

2. 若 $\{ P_i \}$ 互相正交且 $\sum_i P_i = I$，则 $\sum_i p(P_i) = 1$；

3. 非情境性（A3）；

则存在唯一的密度算符 $\rho$ 使得 $p(P) = \mathrm{tr}(\rho P)$。这就是 Gleason 定理的陈述。在 QCA 宇宙中，结合 A4–A6，可将 $\rho$ 取为系统–观察者的约化态，从而唯一选出波恩型概率 $p_k = \lvert \alpha_k \rvert^2$，并排除所有与无超光速信号原则不相容的非常规概率规则。

### 定理 5（坍缩的有效性与信息视界）

在上述框架中，全局 QCA 状态始终按幺正算子演化，不存在物理上的非线性坍缩。然而，对任一局域观察者与其可访问算符代数而言，将全局态

$$
\lvert \Psi_{\mathrm{post}} \rangle
= \sum_k \alpha_k \lvert s_k \rangle \otimes \lvert M_k \rangle \otimes \lvert E_k \rangle
$$

替换为条件化态

$$
\lvert \Psi_{\mathrm{eff}}^{(k)} \rangle
= \lvert s_k \rangle \otimes \lvert M_k \rangle \otimes \lvert E_k \rangle
$$

并以 $p_k = \lvert \alpha_k \rvert^2$ 作为权重，对任何未来实验的可观测统计后果完全等价。这种"有效坍缩"可被解释为观察者在自身信息视界内进行的贝叶斯更新，而非全局动力学的改变。

---

## Proofs

本节给出定理 1–5 的证明要点，更细致的构造与技术细节置于附录。

### 4.1 定理 1：QCA 中的相对态结构

**证明要点：**

1. **测量幺正性的实现。** 在 QCA 框架下，任一有限维系统–仪器复合体可以通过在有限空间–时间区块内拼接局域门阵列来实现所需的幺正 $U_{\mathrm{meas}}$，这与在有限量子电路中实现任意有限维幺正算子的通用性结论一致。

2. **Schmidt 分解与退相干。** 对 $\mathcal{H}_{SO} \otimes \mathcal{H}_E$ 这样的双分系统，任一纯态都存在 Schmidt 分解。测量后适当选择指针基 $\{ \lvert M_k \rangle \}$，可以将 $\lvert \Psi_{\mathrm{post}} \rangle$ 写成

   $$
   \lvert \Psi_{\mathrm{post}} \rangle = \sum_k \alpha_k \lvert s_k \rangle \otimes \lvert M_k \rangle \otimes \lvert E_k \rangle,
   $$

   其中 $\lvert E_k \rangle$ 经过环境–系统相互作用在短时间内趋于近乎正交。退相干理论与模型计算表明，在宏观仪器尺度上，指针态的干涉项在可观测时间尺度内迅速衰减，且对后续动力学贡献可忽略。

3. **相对态与自定位不确定性。** Everett 相对态诠释认为，测量后全局态为一组带标签的分支，每个标签对应一个观察者记录。观察者虽"内在"于某一分支，却可在分支形成与记录读取之间的时间窗内，将自身的不确定性视为"我究竟处于哪一个分支"的自定位不确定性。这一结构无需额外假设，直接源自 QCA 的幺正演化与退相干选出的指针态。

综上，定理 1 得证。

### 4.2 定理 2：等幅分支与微观计数

定理 2 是波恩规则的组合学核心。

**步骤 1：有理振幅平方与环境细分。**

假设 $\lvert \alpha_k \rvert^2 = N_k / N$，其中 $N_k$ 与 $N$ 为整数且 $N = \sum_k N_k$。在 Hilbert 空间中，可引入一个辅助环境子空间，将每一项 $\alpha_k \lvert s_k, M_k, E_k \rangle$ 拆分为 $N_k$ 个等幅正交态：

$$
\alpha_k \lvert s_k, M_k, E_k \rangle
= \sqrt{\frac{N_k}{N}} \mathrm{e}^{\mathrm{i}\theta_k} \lvert s_k, M_k, E_k \rangle
= \frac{1}{\sqrt{N}}
\sum_{j=1}^{N_k} \mathrm{e}^{\mathrm{i}\theta_k} \lvert s_k, M_k, \varepsilon_{k,j} \rangle,
$$

其中 $\{ \lvert \varepsilon_{k,j} \rangle \}_{j=1}^{N_k}$ 在环境 Hilbert 空间中正交，且对所有 $k$ 与 $j$ 组成一组正交基的一部分。这样的分解总是可以通过扩展环境维度实现，这在 QCA 图景中对应于在额外元胞或内部自由度上编码微观标签。

将全部 $k$ 汇总，有

$$
\lvert \Psi_{\mathrm{post}} \rangle
= \frac{1}{\sqrt{N}}
\sum_{k} \sum_{j=1}^{N_k} \mathrm{e}^{\mathrm{i}\theta_k} \lvert s_k, M_k, \varepsilon_{k,j} \rangle.
$$

整体相位 $\mathrm{e}^{\mathrm{i}\theta_k}$ 对概率无关，可忽略。

**步骤 2：envariance 与等概率。**

考虑某一给定的 $k$。在环境 Hilbert 空间内部，对 $\{ \lvert \varepsilon_{k,j} \rangle \}_{j=1}^{N_k}$ 的任意置换可由一个环境酉算子 $V_k$ 实现。定义联合酉变换

$$
V = \bigotimes_{k} V_k
$$

作用在环境上，对系统–观察者部分保持恒等，则全局态在形式上不变：

$$
V \lvert \Psi_{\mathrm{post}} \rangle = \lvert \Psi_{\mathrm{post}} \rangle.
$$

这正是 Zurek 所定义的环境辅助不变性（envariance）：系统–观察者与环境完美纠缠时，对环境的某些变换可以"补偿"对系统的变换，使整体态不变，从而迫使观察者对相关分支赋予相等概率。

在本情形中，对任意固定的 $k$，各个 $j$ 标签唯一差异在于环境状态 $\lvert \varepsilon_{k,j} \rangle$，而环境对观察者不可访问。若观察者对这些微观差异赋予不同的主观概率，将导致在仅改变环境而不改变系统–观察者可观测量的操作下概率发生变化，这与 A4（环境不敏感性）直接矛盾。因此，满足 envariance 与 A4 的唯一选择是：在同一 $k$ 下的全部 $j$ 上赋予相同概率。

记 $q_{k,j}$ 为观察者自定位于微观分支 $(k,j)$ 的概率，则对任一固定 $k$ 有

$$
q_{k,1} = q_{k,2} = \cdots = q_{k,N_k} \equiv q_k.
$$

总体归一化条件为

$$
\sum_{k} \sum_{j=1}^{N_k} q_{k,j} = 1
\quad \Rightarrow \quad
\sum_k N_k q_k = 1.
$$

由对称性以及 A1 的"等本体权重"也可直接取 $q_{k,j} = 1/N$。二者结合得到

$$
q_k = \frac{1}{N},\quad p_k \equiv \sum_{j=1}^{N_k} q_{k,j} = \frac{N_k}{N}.
$$

从而

$$
p_k = \lvert \alpha_k \rvert^2,
$$

定理 2 得证。

### 4.3 定理 3：连续扩展到一般振幅

对任意纯态 $\lvert \psi_S \rangle = \sum_k \alpha_k \lvert s_k \rangle$，令 $r_k = \lvert \alpha_k \rvert^2$，满足 $\sum_k r_k = 1$。由于有理数在实数中稠密，可以构造一列有理近似

$$
r_k^{(n)} = \frac{N_k^{(n)}}{N^{(n)}} \to r_k,
\quad
\sum_k r_k^{(n)} = 1
$$

（例如取 $r_k^{(n)}$ 为把 $r_k$ 保留 $n$ 位小数后归一化的结果）。对每一 $n$，按定理 2 构造等幅微观态与概率分配 $p_k^{(n)} = r_k^{(n)}$。连续性假设 A5 要求当 $\lVert \psi^{(n)} - \psi \rVert \to 0$ 时，$p_k^{(n)} \to p_k$；由于 $r_k^{(n)} \to r_k$，于是得到

$$
p_k = \lim_{n\to\infty} p_k^{(n)} = \lim_{n\to\infty} r_k^{(n)} = r_k = \lvert \alpha_k \rvert^2.
$$

因此，一般情况下波恩规则成立。

需要强调的是，这里的连续性并非任意附加的数学条件，而是源自以下物理与决策论动机：实验上任何状态制备必然伴随有限精度误差；若概率对这样微小误差高度敏感，则概率陈述将失去可操作意义。类似的连续性要求也出现在 Deutsch–Wallace 与非情境概率推导的讨论中。

### 4.4 定理 4：Gleason 型唯一性与无超光速信号

定理 2 与 3 给出了在特定测量情形下波恩规则的构造性推导。为了说明其唯一性，需要调用 Gleason 类结果与无超光速信号约束。

Gleason 定理表明：在维数至少为三的（实或复）Hilbert 空间内，若对每个投影算符 $P$ 赋予的概率测度 $\mu(P)$ 满足

1. $\mu(P) \ge 0$，且 $\mu(I) = 1$；

2. 对任一可数族互相正交的投影 $\{ P_i \}$ 有 $\mu(\sum_i P_i) = \sum_i \mu(P_i)$；

则必存在唯一的密度算符 $\rho$ 使得 $\mu(P) = \mathrm{tr}(\rho P)$。

在 QCA 宇宙中，对被测系统 $S$ 来说，其 Hilbert 空间维数通常大于等于二，且在引入仪器与部分环境后更是巨大。若对 $\mathcal{H}_S \otimes \mathcal{H}_M$ 上的投影算符族 $\{ P_k \}$ 要求满足 A3 的非情境性以及上述加性，则由 Gleason 定理可知存在某个约化态 $\rho_{S O}$ 使得

$$
p_k = \mu(P_k) = \mathrm{tr}(\rho_{S O} P_k).
$$

另一方面，定理 2–3 已经在一大类具体测量下展示：当 $\rho_{S O}$ 恰为全局 QCA 纯态在 $S \otimes O$ 上的约化态时，$p_k = \lvert \alpha_k \rvert^2$。在此基础上，任何试图修改 $p_k$ 为其他函数（例如 $\lvert \alpha_k \rvert^q$）的方案都必须违反 Gleason 结构中的某一项（如非情境性），或引入非线性演化。

关于非线性演化与无超光速信号的张力，Gisin 及后续工作已表明：在存在纠缠的情形下，对密度矩阵施加非线性演化或在局域上引入非常规概率更新往往导致远程信号可被操纵，从而违背相对论因果律与无超光速信号原则。在 QCA 宇宙中，由于局域更新规则与 Lieb–Robinson 速度为基础的"光锥"结构，若测量规则允许通过远程操作改变本地测量结果的分布，则等价于在 QCA 上实现超出 $v_{\mathrm{LR}}$ 的有效信息传播，直接违反 A6。

因此，在 A1–A6 的联合约束下，波恩规则不仅是一个可行的概率赋值，而且是唯一与 QCA 全局幺正性、局域性与无超光速信号相容的赋值。

### 4.5 定理 5：坍缩的有效性

定理 5 的论证本质上是退相干理论中"有效坍缩"思想在 QCA 语境中的严格化。

设测量后全局态

$$
\lvert \Psi_{\mathrm{post}} \rangle
= \sum_k \alpha_k \lvert s_k \rangle \otimes \lvert M_k \rangle \otimes \lvert E_k \rangle,
$$

对任一局域可观测量 $A$（其支持在 $S \cup O$ 的有限区域内），其期望值为

$$
\langle A \rangle
= \langle \Psi_{\mathrm{post}} \vert A \otimes I_E \vert \Psi_{\mathrm{post}} \rangle
= \sum_{k,\ell} \alpha_k \alpha_\ell^\ast
\langle s_\ell, M_\ell \vert A \vert s_k, M_k \rangle
\langle E_\ell \vert E_k \rangle.
$$

退相干保证当 $k \ne \ell$ 时 $\langle E_\ell \vert E_k \rangle \approx 0$，于是

$$
\langle A \rangle \approx \sum_k \lvert \alpha_k \rvert^2
\langle s_k, M_k \vert A \vert s_k, M_k \rangle.
$$

若采用"有效坍缩"表述：以概率 $p_k = \lvert \alpha_k \rvert^2$ 将系统–观察者状态置于纯态 $\lvert s_k, M_k \rangle$，则相应统计平均值恰为

$$
\langle A \rangle_{\mathrm{coll}}
= \sum_k p_k \langle s_k, M_k \vert A \vert s_k, M_k \rangle
= \sum_k \lvert \alpha_k \rvert^2
\langle s_k, M_k \vert A \vert s_k, M_k \rangle,
$$

与上式一致。因此，就任何实际可测量的局域算符而言，用"坍缩后的混合态"代替全局纯态不会改变预测。观察者在获得记录 $M_k$ 后，将自己的世界描述更新为条件化态 $\lvert s_k, M_k \rangle$ 是一种贝叶斯更新，而非物理态的突变。

在 QCA 宇宙中，这一逻辑特别清晰：全局更新规则始终是固定的局域幺正 $U$；"坍缩"仅是嵌入在 QCA 上的某个局域子系统对自身可访问信息作出的重新编码。

---

## Model Apply

本节通过几个标准测量情景展示上述理论如何再现常规量子力学的概率预言。

### 5.1 自旋测量：Stern–Gerlach 实验

设一个自旋 $1/2$ 粒子被建模为 QCA 上某一局域元胞组 $S$，其内部自由度实现自旋自由度。初态为

$$
\lvert \psi_S \rangle = \alpha \lvert \uparrow_z \rangle + \beta \lvert \downarrow_z \rangle.
$$

测量设备 $O$ 包含一个可切换磁场与屏幕，其指针态 $\lvert M_\uparrow \rangle, \lvert M_\downarrow \rangle$ 对应"上偏转"和"下偏转"两个宏观结果。环境 $E$ 包含大量背景自由度，如空气分子、晶体晶格振动等。

QCA 中的测量相互作用 $U_{\mathrm{meas}}$ 将该粒子与仪器耦合，使得

$$
\lvert \Psi_{\mathrm{post}} \rangle
= \alpha \lvert \uparrow_z \rangle \otimes \lvert M_\uparrow \rangle \otimes \lvert E_\uparrow \rangle
+ \beta \lvert \downarrow_z \rangle \otimes \lvert M_\downarrow \rangle \otimes \lvert E_\downarrow \rangle.
$$

在 QCA 本体基底的细粒化下，可将 $\alpha, \beta$ 写成简并度平方根，并按定理 2–3 赋予概率

$$
p(\uparrow_z) = \lvert \alpha \rvert^2,\quad p(\downarrow_z) = \lvert \beta \rvert^2,
$$

与标准量子力学一致。该结论与自旋测量的长期统计实验结果相符。

### 5.2 干涉实验：双缝与 which-way 信息

考虑双缝干涉实验，被测系统 $S$ 为单光子在空间离散格点上的波包。QCA 动力学实现自由传播与障碍散射；双缝被编码为 QCA 上允许或禁止传播的局域规则。

若在无 which-way 测量时，QCA 的演化使末端屏幕上形成干涉条纹，其概率分布由相干叠加产生。此时，与特定屏幕位置 $x$ 相应的态 $\lvert s_x \rangle$ 的振幅 $\psi(x)$ 在本体基底的路径计数中由干涉路径的复权和给出，其微观简并度对应 $\lvert \psi(x) \rvert^2$。因此，粒子在 $x$ 处被探测到的概率为 $\lvert \psi(x) \rvert^2$。

若在路径上引入探测器（属于观察者 $O$ 的一部分），则 QCA 中的局域耦合将路径信息编码到指针态 $\lvert M_{\mathrm{left}} \rangle, \lvert M_{\mathrm{right}} \rangle$ 中，环境退相干抑制相干项，从而破坏干涉条纹。此时，概率分布为两条路径上的经典混合。该现象在实验上广泛观测并由退相干理论成功解释。

在 QCA 视角下，这说明概率始终源自微观路径简并度；是否出现干涉仅取决于观察者与环境是否在 QCA 上编码了 which-way 信息。

### 5.3 重复测量与频率律

考虑对相同准备态 $\lvert \psi_S \rangle = \alpha \lvert 0 \rangle + \beta \lvert 1 \rangle$ 进行 $n$ 次独立测量的情形。QCA 图景中，这对应于在不同时间片或不同空间区域上复制系统并实施相同测量。

全局态可写为

$$
\lvert \Psi_{\mathrm{post}}^{(n)} \rangle
= \sum_{\mathbf{k} \in \{0,1\}^n}
\alpha^{m(\mathbf{k})} \beta^{n-m(\mathbf{k})}
\lvert \mathbf{k} \rangle_S \otimes \lvert M_{\mathbf{k}} \rangle_O \otimes \lvert E_{\mathbf{k}} \rangle_E,
$$

其中 $m(\mathbf{k})$ 为序列 $\mathbf{k}$ 中"0"的次数。对每一给定的 $m$，存在 $\binom{n}{m}$ 个微观分支具有同样的振幅模长 $\lvert \alpha^{m} \beta^{n-m} \rvert$，对应的总微观构型数简并度为

$$
N_m \propto \binom{n}{m} \lvert \alpha \rvert^{2m} \lvert \beta \rvert^{2(n-m)}.
$$

为一个有限信息观察者，其自定位在"看到 $m$ 次结果 0"这一宏观记录上的概率正比于 $N_m$，即服从二项分布。这一结果与大数定律共同说明，在大多数分支中，观察者记录的频率 $m/n$ 将非常接近 $\lvert \alpha \rvert^2$。因此，频率解释与组合学解释在 QCA 宇宙中自然统一。

---

## Engineering Proposals

尽管本文主要是理论性工作，QCA 框架也允许提出若干与实验和量子信息工程相关的建议。

### 6.1 在可控量子平台上模拟 QCA 测量

当前的超导量子比特、离子阱与光子平台已能实现一维与二维量子行走与简化 QCA 的实验模拟。可以设计如下方案：

1. 在有限个量子比特上实现 Dirac 型 QCA 的单粒子演化，将其中一部分比特编码为被测系统 $S$，另一部分作为测量寄存器 $O$ 与环境 $E$；

2. 通过可编程幺正电路实现测量耦合 $U_{\mathrm{meas}}$，并引入可控退相干通道模拟环境；

3. 在不同的电路分解下实现同一抽象测量，并验证局域统计仅依赖于 $\lvert \psi \rvert^2$，而与环境具体实现无关，从而间接验证 A4 与 envariance 原则的有效性。

### 6.2 测试非常规概率规则的约束

不少实验方案旨在检验是否存在偏离波恩规则的微小效应，例如高精度干涉实验与量子光学统计。结合 Gisin 等关于非线性量子力学与超光速信号的分析，可以在 QCA 语境中设计如下检验：

1. 构造空间分离的纠缠对；

2. 在一侧实施不同测量基的选择，在另一侧高精度测量统计分布；

3. 利用 QCA 局域性分析任何可见偏离波恩分布是否会导致有效传播速度超过 Lieb–Robinson 速度，从而对非常规概率规则施加新的约束。

### 6.3 有限观察者模型与量子信息压缩

有限信息容量假设 A2 在量子信息理论中有自然实现：观察者的"记忆"可以视为有限维寄存器，任何关于环境的知识需要通过量子压缩或经典编码存储。将本文概率涌现框架与可逆压缩、纠缠辅助编码等技术结合，有望在实际量子通信或计算协议中引入"显式观察者"模块，用以分析实验结果在不同信息视界下的再解释。

---

## Discussion (Risks, Boundaries, Past Work)

### 7.1 与既有波恩规则推导的比较

本文的推导路线与 Zurek 的 envariance 方案在形式上有显著相似：都通过对等幅叠加态的环境细分与对称性论证，得到有理振幅情况下的波恩规则，然后通过连续性推广到一般情形。与 Deutsch–Wallace 的决策论路线不同，这里并未显式引用效用函数与理性公理，而是将"有限信息观察者的自定位不确定性"与"等本体权重"作为核心直觉。

与纯 Hilbert 空间抽象推导相比，QCA 框架的主要附加价值在于：

1. 给出一个明确的本体基底与微观构型计数方法，使"等幅态的微观简并度"具有具体的离散实现；

2. 将无超光速信号原则与 Lieb–Robinson 速度联系起来，在微观层面解释为何非常规概率规则通常与局域 QCA 动力学不相容；

3. 为"有限信息观察者"的物理解读提供载体：记忆寄存器、指针态与环境均可在 QCA 上具体实现。

### 7.2 潜在风险与假设的强度

尽管上述推导在结构上闭合，仍存在若干值得强调的边界与风险：

1. **等本体权重假设的地位。** A1 要求所有本体基态具有相同基础权重，这一假设在 QCA 与元胞自动机诠释中常被视为自然，但在更广泛的基础讨论中仍可被质疑。其物理基础可以从 QCA 局域规则的平移不变性与无优先基底性中获得一定辩护。

2. **非情境性与环境不敏感性。** Gleason 型推导表明非情境性是连接 Hilbert 空间结构与波恩规则的关键，但这一要求在一些诠释中被视为强假设。本文通过 envariance 与 QCA 局域性论证 A4 的合理性，但是否存在更加弱的物理原则足以取代这些假设，仍是开放问题。

3. **维数与 POVM 的推广。** Gleason 定理在二维 Hilbert 空间上需要额外假设或 POVM 推广方可成立。在 QCA 宇宙中，系统–观察者的有效 Hilbert 空间通常高维，因此这一技术限制对宏观测量影响有限，但在分析单量子比特系统时需谨慎。

4. **无超光速信号的使用方式。** Gisin 与后续工作表明，许多非线性修改将导致超光速信号，但也存在精心构造的非常规方案试图规避这一结论。在 QCA 宇宙中，由于离散格点与局域更新的刚性结构，这些规避方案的可行性有待进一步分析。

### 7.3 Decoherence 方案与测量问题的剩余部分

大量文献指出，退相干虽可解释经典可观测结构的涌现，却并未单独解决测量问题。本文的贡献在于：在退相干所提供的指针态与分支结构基础上，引入 QCA 微观计数与有限观察者模型，从而在 Everett–相对态框架中赋予概率一个组合学与信息论的起源。但从哲学角度看，"等本体权重"、"自定位不确定性"等概念本身也具有解释色彩，其是否优于传统诠释仍需进一步比较。

---

## Conclusion

本文在离散、局域、幺正的量子元胞自动机宇宙框架下，给出了波恩规则的组合学–信息论推导，并将量子概率解释为有限信息观察者在全局幺正态上的自定位不确定性，而非基本随机过程。其核心要点可概括如下：

1. QCA 宇宙为全局确定性动力学提供本体论基础：每一个本体基态按局域元胞规则演化，无内在随机；

2. 测量过程被建模为系统–观察者–环境的局域幺正耦合，退相干在指针态空间选出稳定分支，使全局态具有明确的相对态结构；

3. 在"等本体权重"、envariance 与环境不敏感性假设下，等幅叠加态的分支在有限观察者视角下等概率，微观构型简并度自然对应振幅模方；

4. 通过有理近似与连续性，将等幅情况推广到一般振幅，得到波恩规则 $p_k = \lvert \alpha_k \rvert^2$；

5. 结合 Gleason 定理与无超光速信号约束，可论证在 QCA 宇宙中，波恩规则是唯一与 Hilbert 空间结构、局域性与因果律相容的概率赋值；

6. 波函数坍缩被重新理解为观察者在自身信息视界内的贝叶斯更新与自定位，而非全局态的真实突变。

在此意义下，自然界在微观层面并不"掷骰子"；概率的出现是离散全息纠缠网络在有限观察者视角下的统计必然。

---

## Acknowledgements, Code Availability

本研究基于量子元胞自动机、退相干理论与量子概率基础方面既有工作的综合与延展，对相关文献与前人成果深表感谢。

本文所有推导均为解析性，不依赖数值模拟。若需要在具体量子平台上实现小规模 QCA 测量模型，可以借助通用量子电路编译器构造相应的局域幺正电路，其细节留待后续工作开展。

---

## References

1. W. H. Zurek, "Environment-assisted invariance, entanglement, and probabilities in quantum physics," *Phys. Rev. Lett.* **90**, 120404 (2003).

2. W. H. Zurek, "Probabilities from entanglement, Born's rule ( $p_k = \lvert \psi_k \rvert^2$ ) from envariance," *Phys. Rev. A* **71**, 052105 (2005).

3. M. Schlosshauer, *Decoherence and the Quantum-to-Classical Transition*, Springer (2007).

4. E. Joos et al., *Decoherence and the Appearance of a Classical World in Quantum Theory*, Springer (2003).

5. A. M. Gleason, "Measures on the closed subspaces of a Hilbert space," *J. Math. Mech.* **6**, 885–893 (1957).

6. F. Logiurato and A. Smerzi, "Born Rule and Noncontextual Probability," *J. Mod. Phys.* **3**, 1930–1939 (2012).

7. D. Deutsch, "Quantum theory of probability and decisions," *Proc. R. Soc. Lond. A* **455**, 3129–3137 (1999).

8. C. T. Sebens and S. M. Carroll, "Self-locating Uncertainty and the Origin of Probability in Everettian Quantum Mechanics," *Br. J. Philos. Sci.* **69**, 25–74 (2018).

9. L. Vaidman, "Derivations of the Born Rule," *arXiv:1907.03623* (2019).

10. G. 't Hooft, *The Cellular Automaton Interpretation of Quantum Mechanics*, Springer (2016).

11. G. M. D'Ariano and P. Perinotti, "Quantum cellular automata and free quantum field theory," *Front. Phys.* **12**, 120301 (2017).

12. P. Raynal et al., "Simple derivation of the Weyl and Dirac quantum cellular automata," *Phys. Rev. A* **95**, 062344 (2017).

13. N. Gisin, "Weinberg's non-linear quantum mechanics and superluminal communications," *Phys. Lett. A* **143**, 1–2 (1990).

14. C. Simon, V. Buzek, and N. Gisin, "The no-signaling condition and quantum dynamics," *Phys. Rev. Lett.* **87**, 170405 (2001).

15. M. Schlosshauer, "Decoherence, the measurement problem, and interpretations of quantum mechanics," *Rev. Mod. Phys.* **76**, 1267–1305 (2004).

16. G. Bacciagaluppi, "The Role of Decoherence in Quantum Mechanics," *Stanford Encyclopedia of Philosophy* (2003/2011).

17. S. Saunders et al. (eds.), *Many Worlds? Everett, Quantum Theory, and Reality*, Oxford University Press (2010).

18. J. Earman, "The Status of the Born Rule and the Role of Gleason's Theorem," *PhilSci Archive* (2022).

（关于 QCA 宇宙、信息速率守恒与光学度规等相关工作的进一步发展，将另文系统阐述。）

---

## Appendix A：离散 envariance 推导的细节

本附录补充定理 2 中关于等幅分支与 envariance 的严格论证。

### A.1 环境细分的构造

设测量后全局态

$$
\lvert \Psi \rangle = \sum_k \alpha_k \lvert \chi_k \rangle,
\quad
\lvert \chi_k \rangle \equiv \lvert s_k \rangle_S \otimes \lvert M_k \rangle_O \otimes \lvert E_k \rangle_E,
$$

且 $\lvert \alpha_k \rvert^2 = N_k / N$。为每个 $k$ 选取一个 $N_k$ 维环境子空间 $\mathcal{H}_{E,k} \subset \mathcal{H}_E$，并在其中取标准正交基 $\{ \lvert \varepsilon_{k,j} \rangle \}_{j=1}^{N_k}$。扩展 Hilbert 空间为

$$
\mathcal{H}_{E'} = \bigoplus_k \mathcal{H}_{E,k} \oplus \mathcal{H}_{E,\perp},
$$

其中 $\mathcal{H}_{E,\perp}$ 为补空间。定义等幅态

$$
\lvert \tilde{\chi}_{k,j} \rangle
\equiv \lvert s_k \rangle_S \otimes \lvert M_k \rangle_O \otimes \lvert \varepsilon_{k,j} \rangle_E,
$$

并令

$$
\lvert \Psi' \rangle
= \frac{1}{\sqrt{N}} \sum_k \sum_{j=1}^{N_k} \mathrm{e}^{\mathrm{i}\theta_k} \lvert \tilde{\chi}_{k,j} \rangle.
$$

可以构造一个环境酉 $W$ 使得

$$
W \lvert E_k \rangle_E = \frac{1}{\sqrt{N_k}} \sum_{j=1}^{N_k} \lvert \varepsilon_{k,j} \rangle_E,
$$

并对其他正交方向做适当补充，让 $W$ 成为 $\mathcal{H}_E$ 上的完备酉算子。则全局酉 $I_{SO} \otimes W$ 将 $\lvert \Psi \rangle$ 映射为 $\lvert \Psi' \rangle$，且两者物理等价（仅差一个在环境空间中的酉变换），故可将后者视为测量后状态的等价表示。

### A.2 envariance 与等概率的形式化

考虑子系统 $R$（"分支标签"）的 Hilbert 空间 $\mathcal{H}_R$，其基底标记为 $\{ \lvert r_{k,j} \rangle \}$，与 $S \otimes O$ 共同构成

$$
\lvert \Psi' \rangle
= \frac{1}{\sqrt{N}} \sum_{k,j} \lvert s_k, M_k \rangle \otimes \lvert r_{k,j} \rangle.
$$

envariance 的关键观察是：对于任意给定的 $(k,j)$ 与 $(k,j')$，存在一个仅作用于 $R$ 的酉 $U_{(j,j')}$ 将 $\lvert r_{k,j} \rangle$ 与 $\lvert r_{k,j'} \rangle$ 交换，但保持其他基矢不变。该酉作用于 $\lvert \Psi' \rangle$ 后的态为

$$
\lvert \Psi'' \rangle
= \frac{1}{\sqrt{N}} \Bigl(
\cdots + \lvert s_k, M_k \rangle \otimes \lvert r_{k,j'} \rangle
+ \cdots + \lvert s_k, M_k \rangle \otimes \lvert r_{k,j} \rangle + \cdots
\Bigr),
$$

在形式上与 $\lvert \Psi' \rangle$ 完全相同，只是对 $R$ 的标记进行了重排。

由于观察者 $O$ 无法访问 $R$ 的内部结构（其所有观测均通过 $S \otimes O$ 实现），若其赋予 $(k,j)$ 与 $(k,j')$ 不同概率，则对 $R$ 的这种纯局域操作将改变其主观概率分配，但在物理上却是不可区分的，这违背了 A4 的环境不敏感性。因此，所有 $(k,j)$ 必须等概率。

形式化地，令 $p_{k,j}$ 为"观察者位于微观分支 $(k,j)$ 上"的概率。envariance 与 A4 要求：

1. 对任一置换群 $G$ 作用于 $R$，概率分布 $\{ p_{k,j} \}$ 在 $G$ 的作用下不变；

2. 置换表示在 $R$ 上是传递的。

因此 $p_{k,j}$ 必为常数 $1/N$，从而 $p_k = \sum_j p_{k,j} = N_k/N$。

---

## Appendix B：QCA 微观计数与有理近似

本附录说明为何在 QCA 宇宙中，将振幅模方写成有理数并进行微观计数是自然且稳定的。

### B.1 有限精度制备与有理逼近

任何实际物理过程制备的量子态均伴随有限精度与噪声。若某一过程目标制备态为

$$
\lvert \psi \rangle = \sum_k \alpha_k \lvert s_k \rangle,
$$

则其实际制备态 $\lvert \psi_{\mathrm{real}} \rangle$ 与理想态之间存在一定距离 $\lVert \psi_{\mathrm{real}} - \psi \rVert \le \varepsilon$。在 QCA 中，该偏差可视为在额外环境自由度上的微小扰动，因此不改变组合学结构的本质。

对每个 $\alpha_k$，总可以找到有理数 $r_k^{(n)} = N_k^{(n)}/N^{(n)}$ 使得 $\lvert r_k^{(n)} - \lvert \alpha_k \rvert^2 \rvert \le 1/2^n$。只要 $n$ 足够大，在任何可实验分辨的统计误差范围内，$r_k^{(n)}$ 与真实值不可区分。

### B.2 QCA 本体路径与振幅模方

在路径积分视角下，一个给定末态振幅可以写成在全部本体路径集合上的复权和。QCA 的局域规则保证每一步演化仅依赖有限邻域，使得路径权重以局域转移矩阵条目为基本因子。若 QCA 的局域转移矩阵条目为代数数或有理数，则任意有限长路径的振幅亦为代数数，其模方可以被有理数以任意精度逼近。

因此，将 $\lvert \alpha_k \rvert^2$ 替换为 $N_k/N$ 的操作，在 QCA 微观动力学中可理解为通过增加环境自由度、细化路径标签，将原本复杂权重分解为大量等权路径的简并度。该过程并不改变物理可观测量，只是改变了我们对微观自由度的计数方式。

---

## Appendix C：Gleason 定理、非情境性与 QCA

本附录简要回顾 Gleason 定理，并说明其在 QCA 测量中的适用性。

### C.1 Gleason 定理的内容

设 $\mathcal{H}$ 为维数至少为三的复 Hilbert 空间，$\mathcal{P}(\mathcal{H})$ 为其闭子空间（或等价的正交投影）集合。一个概率测度为映射 $\mu: \mathcal{P}(\mathcal{H}) \to [0,1]$，满足：

1. $\mu(I) = 1$，$\mu(0) = 0$；

2. 若 $\{ P_i \}$ 为互相正交的投影族且 $\sum_i P_i = I$，则 $\sum_i \mu(P_i) = 1$。

Gleason 定理证明存在唯一的正迹一算符 $\rho$ 使得

$$
\mu(P) = \mathrm{tr}(\rho P)
$$

对所有 $P \in \mathcal{P}(\mathcal{H})$ 成立。

### C.2 在 QCA 测量中的角色

在 QCA 宇宙中，任何实际测量对应于在某一有限区域 $\Lambda_{\mathrm{meas}} \subset \Lambda$ 上的一组正交投影 $\{ P_k \}$，这些投影作用在 $\mathcal{H}_{\Lambda_{\mathrm{meas}}}$ 上，维数通常远大于三。若要求观察者对这些投影的概率赋值满足 A3 的非情境性与可数可加性，则 Gleason 定理确保存在约化态 $\rho_{\Lambda_{\mathrm{meas}}}$ 使得

$$
p_k = \mathrm{tr}(\rho_{\Lambda_{\mathrm{meas}}} P_k).
$$

另一方面，QCA 的全局态 $\lvert \Psi \rangle$ 决定了每一有限区域的约化态。定理 2–3 已经说明，当 $P_k$ 是系统–观察者–环境退相干后选出的指针投影时，$p_k$ 必为振幅模方。于是，在满足 A1–A6 的 QCA 宇宙中，波恩规则不仅从组合学上可以构造，而且在 Gleason 框架下是唯一的非情境概率测度。

这完成了从 QCA 全局幺正性与观察者相对态出发推导标准量子概率的闭环。

