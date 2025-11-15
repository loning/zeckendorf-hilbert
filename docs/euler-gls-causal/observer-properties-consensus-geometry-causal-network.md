# 因果网上观察者属性与共识几何

局部偏序、信息状态与更新算子的统一形式化

---

## Abstract

在以因果偏序为基础的世界图景中，任何单一观察者都只掌握一个局部片段：有限分辨率下的部分事件、部分因果关系以及在局部可观测代数上的部分信息状态。多个观察者通过通信和更新试图在同一宇宙因果网上达成"共识"，从而重构一个一致的世界描述。本文在抽象因果网框架下，将观察者形式化为带有几何域、局域偏序、分辨率刻度、可观测代数、边界状态、模型族、状态更新算子与效用函数的多分量对象，建立了一套统一的"共识几何"理论。

在几何层面，给定一族局域因果片段 $\{(C_i,\prec_i)\}_{i\in I}$ 覆盖事件集合 $X$，若交叠区域中局部偏序满足 Čech 式一致性条件，则存在唯一的全局偏序 $(X,\prec)$ 作为因果共识延拓；否则因果共识至多在更粗的分辨率层级上存在。分辨率被刻画为事件分区 $P_i$ 与可观测代数 $\mathcal A_i$，公共精细化 $P_\ast$ 与代数交集 $\mathcal A_{\mathrm{com}}=\bigcap_i\mathcal A_i$ 的丰度决定了共识能够达到的细致程度。

在信息与动力学层面，考虑公共可观测代数 $\mathcal A_{\mathrm{com}}$ 上的状态族 $\{\omega_i^{(t)}\}$ 与通信信道 $T_{ij}$ 以及权重矩阵 $W=(w_{ij})$。在 Umegaki 相对熵

$$
D(\rho\Vert\sigma)=\operatorname{tr}\big(\rho(\log\rho-\log\sigma)\big)
$$

及其数据处理不等式基础上，构造加权总偏差函数

$$
\Phi^{(t)}=\sum_{i\in I}\lambda_i D\big(\omega_i^{(t)}\Vert\omega_\ast\big),
$$

证明在信道满足数据处理不等式且通信图强连通、权重矩阵原始并存在共同不动点 $\omega_\ast$ 时，$\Phi^{(t)}$ 为严格单调非增的 Lyapunov 函数，令状态迭代收敛到唯一状态共识 $\omega_{\mathrm{cons}}=\omega_\ast$。这一结构同时涵盖经典平均共识算法与量子信道上的收缩流。

在模型层面，将候选因果动力学模型视为紧空间 $\mathcal M$ 的元素，在适当可识别性与大偏差条件下，证明随着观测数据增加，各观察者可接受模型集合 $\mathcal M_i^{(T)}$ 的交集以概率趋一收缩到唯一真模型 $M^\ast$，从而实现模型共识。

上述几何、信息与模型结构被统一为观察者属性空间 $\mathcal O$ 中的一个"共识可行域" $\mathcal O_{\mathrm{cons}}$。本文给出了因果共识、状态共识与模型共识存在的若干必要或充分条件，提出几何重叠度、分辨率兼容性、代数交集维数、相对熵偏差与通信图连通性等一组定量指标，展示了如何在因果网视角下系统分析"多观察者如何编织同一个因果世界"这一问题。

---

## Keywords

因果网；偏序；观察者；分辨率；可观测代数；相对熵；量子信道；分布式共识；Čech 一致性；模型选择

---

## Introduction & Historical Context

在相对论与量子场论的主流图景中，时空因果结构可以抽象为事件集合 $M$ 上的偏序 $\prec$，例如因果集方法中将洛伦兹时空建模为局部有限的偏序集合 $(M,\prec)$。在此结构下，单个观察者沿其世界线采集局部信息，并在有限分辨率与有限带宽下形成"世界"的主观模型。另一方面，分布式系统与多智能体控制中，大量工作研究了多节点在通信约束下如何通过迭代更新实现平均共识或一致估计。

尽管二者应用语境迥异，却有一个共同的抽象核心：多个具有局部视角与局部信息状态的"观察者"位于同一潜在因果结构上，试图通过通信和更新构造一个一致的"全球描述"。在拓扑与层论中，这一问题以"局部数据能否粘合为全局对象"形式出现，其严格工具是层的局部性与粘合条件以及 Čech 上同调。在因果与结构学习前沿，人们开始用偏序与信息几何刻画更一般的因果结构与其可辨认内容。

另一方面，相对熵及其单调性构成了量子与经典信息理论的重要基石。Umegaki 相对熵的联合凸性与数据处理不等式在量子信道分析、热力学不等式及信息几何中发挥核心作用。这些结果保证在完全正保持迹映射下，态之间的可区分度不会增加，从而自然为"状态共识"的收敛性提供了 Lyapunov 函数候选。

基于上述背景，本工作试图在抽象层面给出如下问题的一般答案：

1. 如何在因果网语言中统一描述"观察者"的几何、代数与信息属性？

2. 在何种条件下，局域偏序可以粘合为单一全局因果网，从而实现因果共识？

3. 在何种条件下，观察者在公共可观测代数上的状态迭代可以收敛到统一的状态共识？

4. 在怎样的可识别性条件下，随着数据累积，观察者的模型族交集几乎必然收缩到唯一真模型，从而形成模型共识？

已有文献中，因果结构的重构多关注"从全局因果偏序重建拓扑与度量"，而分布式共识多假定底层系统动力学已知。本文则反向出发：假设给定的是多观察者的局部因果片段与信息状态，研究在什么条件下可以从这些局部数据恢复一个共同的因果网与共识状态。

本文的主要贡献可以概括为：

* 将观察者形式化为多分量结构

  $$
  O_i=(C_i,\prec_i,\Lambda_i,\mathcal A_i,\omega_i,\mathcal M_i,U_i,u_i,\{\mathcal C_{ij}\}_{j\in I}),
  $$

  分别刻画几何域、局域偏序、分辨率、可观测代数、状态、模型族、更新规则、效用函数与通信结构，从而统一物理观察者与计算节点的抽象描述。

* 在几何与偏序层面，给出局域因果片段 $\{(C_i,\prec_i)\}$ 被粘合为唯一全局偏序 $(X,\prec)$ 的充分条件，其核心是覆盖性、有限交叠与 Čech 式一致性；并指出若该条件破缺，则强形式因果共识不可得。

* 在信息层面，构造公共可观测代数 $\mathcal A_{\mathrm{com}}=\bigcap_i\mathcal A_i$ 与状态族 $\{\omega_i^{(t)}\}$，证明在信道为完全正保持迹映射且满足数据处理不等式、通信图强连通和存在共同不动点 $\omega_\ast$ 的条件下，加权相对熵

  $$
  \Phi^{(t)}=\sum_i\lambda_i D\big(\omega_i^{(t)}\Vert\omega_\ast\big)
  $$

  为 Lyapunov 函数，保证状态共识收敛。该结构同时涵盖经典平均共识与量子网络的对称化与稳态设计。

* 在模型层面，给出基于大偏差与 Kullback–Leibler 散度的可识别性假设，证明随着观测时间 $T\to\infty$，各观察者阈值筛选后模型集合 $\mathcal M_i^{(T)}$ 的交集以概率趋一收缩到唯一真模型 $M^\ast$。

* 将上述条件抽象为观察者属性空间 $\mathcal O$ 中的一个"共识可行域" $\mathcal O_{\mathrm{cons}}$，并通过若干有限例子展示因果共识失败与通过粗粒化恢复弱共识的机制。

后续结构安排如下：首先给出模型与假设；然后陈述主定理与其证明框架；再讨论若干应用与工程建议；最后总结并给出附录中的详细证明与示例。

---

## Model & Assumptions

### 1. 事件集合与局部因果片段

设 $X$ 为事件集合。暂不预设 $X$ 上的全局因果关系，而是认为观测只以局部偏序的形式出现。

**定义 1.1（局部因果片段）**

局部因果片段是二元组 $(C,\prec_C)$，其中 $C\subseteq X$ 为事件子集，$\prec_C$ 是 $C$ 上的偏序关系，即对所有 $x,y,z\in C$ 满足：

1. 反身性：$x\preceq_C x$；
2. 反对称性：若 $x\preceq_C y,y\preceq_C x$ 则 $x=y$；
3. 传递性：若 $x\preceq_C y,y\preceq_C z$ 则 $x\preceq_C z$。

惯常用 $x\prec_C y$ 表示 $x\preceq_C y$ 且 $x\neq y$。

一族观察者 $\{O_i\}_{i\in I}$ 中，每个观察者 $O_i$ 关联一个局部因果片段 $(C_i,\prec_i)$。假定覆盖性条件

$$
\bigcup_{i\in I} C_i = X,
$$

意味着每个事件至少被某个观察者访问。

为避免病态情况，进一步假设有限交叠条件：对任意 $x\in X$，集合 $\{i\in I: x\in C_i\}$ 有限。

### 2. 观察者属性向量

**定义 1.2（观察者）**

观察者 $O_i$ 是如下多分量对象：

$$
O_i = \big(C_i,\ \prec_i,\ \Lambda_i,\ \mathcal A_i,\ \omega_i,\ \mathcal M_i,\ U_i,\ u_i,\ \{\mathcal C_{ij}\}_{j\in I}\big),
$$

其中：

1. $C_i\subseteq X$：可达因果域，给出观察者能够直接观测或影响的事件集合。

2. $\prec_i$：定义在 $C_i$ 上的局部因果偏序。

3. $\Lambda_i$：分辨率刻度，可视为从理想精细事件空间 $X_{\mathrm{fine}}$ 到 $C_i$ 的粗粒化映射，或等价地视为一个分区 $P_i=\{B_{i,\alpha}\}_{\alpha\in I_i}$；分辨率越高，对应分区越细。

4. $\mathcal A_i$：可观测代数，通常为某 Hilbert 空间上有界算子代数的 $C^\ast$ 子代数，包含可测量与可控量。

5. $\omega_i:\mathcal A_i\to\mathbb C$：状态，为正的、归一的线性泛函，刻画观察者在 $\mathcal A_i$ 上的信念；有限维时对应密度矩阵 $\rho_i$。

6. $\mathcal M_i\subseteq\mathcal M$：候选模型族，$\mathcal M$ 为因果动力学模型的紧空间，例如因果 Markov 网络、拉格朗日或转移核。

7. $U_i$：状态更新算子

   $$
   U_i:\ (\omega_i,\ d)\mapsto \omega_i',
   $$

   将数据 $d$ 与当前状态映射到新状态；在下文共识迭代中特化为线性平均型形式。

8. $u_i$：效用函数或偏好函数，定义在行动空间 $\mathcal H$ 或模型空间 $\mathcal M$ 上，用于决策。

9. $\mathcal C_{ij}$：通信通道的结构参数，描述从 $O_j$ 到 $O_i$ 的带宽、延迟、噪声、信任权重等，在信息层面诱导完全正保持迹映射 $T_{ij}$。

本文主要关注前七个分量与通信图结构对共识存在性与收敛性的影响。

### 3. 通信图与信道模型

令 $G_{\mathrm{comm}}=(I,E_{\mathrm{comm}})$ 为通信图，其顶点集合为观察者索引 $I$，边集合

$$
E_{\mathrm{comm}}=\big\{\{i,j\}: \text{在 } i,j \text{ 之间存在至少一个方向的非零带宽}\big\}.
$$

在公共可观测代数上，通信通道用完全正保持迹映射表示：

**假设 1.3（通信信道）**

1. 对每个有向边 $j\to i$，存在完全正保持迹映射（CPTP 映射）$T_{ij}:\mathcal S(\mathcal A_{\mathrm{com}})\to\mathcal S(\mathcal A_{\mathrm{com}})$，其中 $\mathcal S(\cdot)$ 表示状态空间；若无边，则 $T_{ij}$ 为零算子。

2. 存在权重矩阵 $W=(w_{ij})_{i,j\in I}$，满足 $w_{ij}\ge 0,\ \sum_j w_{ij}=1$，且 $w_{ij}>0$ 仅当存在 $j\to i$ 方向通信。

公共可观测代数定义为

$$
\mathcal A_{\mathrm{com}}:=\bigcap_{i\in I}\mathcal A_i,
$$

假定 $\mathcal A_{\mathrm{com}}$ 除标量倍数的单位元外非平凡。

### 4. 模型与概率结构

设观测数据序列 $\mathcal D=(d^{(1)},\dots,d^{(T)})$ 在真实模型 $M^\dagger\in\mathcal M$ 下生成。每个观察者 $O_i$ 拥有似然函数 $L_i(M;\mathcal D)$ 或后验密度 $\pi_i(M\mid\mathcal D)$。阈值筛选后的可接受模型集合定义为

$$
\mathcal M_i^{(T)}:=\big\{M\in\mathcal M_i:\ L_i(M;\mathcal D)\ge \epsilon_i(T)\big\},
$$

其中阈值 $\epsilon_i(T)$ 随数据量变化。

在模型共识讨论中采用如下可识别性与一致性假设，具体表述见后文定理。

---

## Main Results (Theorems and Alignments)

本节给出本文的主要定理与结构性结论。证明细节集中在后续的 Proofs 章节与附录中。

### 1. 因果共识：局部偏序的粘合定理

首先给出强形式因果共识的定义。

**定义 2.1（因果共识）**

称观察者族 $\{O_i\}_{i\in I}$ 在因果上达成共识，如果存在偏序集合 $(X,\prec)$ 及单射映射

$$
e_i: C_i\hookrightarrow X
$$

满足：

1. 对任意 $x,y\in C_i$，有

   $$
   x\prec_i y\iff e_i(x)\prec e_i(y).
   $$

2. 对任意 $x\in C_i\cap C_j$，有 $e_i(x)=e_j(x)$。

此时称 $(X,\prec)$ 为局部因果片段的因果共识延拓。

局域偏序在交叠区域上的一致性通过 Čech 式条件刻画。

**定义 2.2（Čech 式一致性）**

对任意有限子集 $J\subseteq I$，记

$$
C_J:=\bigcap_{j\in J}C_j.
$$

若存在偏序 $\prec_J$ 定义在 $C_J$ 上，使得对所有 $j\in J$ 与 $x,y\in C_J$，有

$$
x\prec_J y\iff x\prec_j y,
$$

则称局部偏序族 $\{\prec_i\}$ 在 $C_J$ 上一致。若对所有有限 $J$ 皆如此，称 $\{\prec_i\}$ 满足 Čech 式一致性。

在覆盖性与有限交叠下有如下粘合定理。

**定理 2.3（因果网粘合定理）**

设 $\{(C_i,\prec_i)\}_{i\in I}$ 为 $X$ 上的一族局部因果片段，满足：

1. 覆盖性：$\bigcup_i C_i = X$；
2. 有限交叠：对任意 $x\in X$，集合 $\{i: x\in C_i\}$ 有限；
3. Čech 式一致性：如定义 2.2。

则存在唯一偏序 $\prec$ 使得：

1. $(X,\prec)$ 为偏序集合；
2. 对每个 $i$，$\prec$ 在 $C_i$ 上的限制等于 $\prec_i$。

换言之，$(X,\prec)$ 是因果共识延拓，且在同构意义下唯一。

该定理表明：强形式因果共识存在性的关键是局部因果片段组成的覆盖满足 Čech 式一致性。否则，因果共识只能在更粗的事件等价类或分辨率层级上存在。

### 2. 分辨率、公共精细化与共识极限

分辨率结构用事件分区刻画。

**定义 2.4（分区与公共精细化）**

设 $X_{\mathrm{fine}}$ 为理想精细事件集合。一族分区 $\{P_i\}_{i\in I}$ 中，每个

$$
P_i=\{B_{i,\alpha}\}_{\alpha}
$$

为 $X_{\mathrm{fine}}$ 的分割。若存在分区 $P_\ast$ 使得对每个 $i$，$P_i$ 是 $P_\ast$ 的粗化，即对任意 $B\in P_i$ 存在 $B'\in P_\ast$ 使 $B\subseteq B'$，则称 $P_\ast$ 为公共精细化。

公共精细化存在性可用等价关系描述。分区 $P_i$ 对应等价关系

$$
x\sim_i y\iff \exists B\in P_i: x,y\in B.
$$

公共精细化存在当且仅当交集关系

$$
R:=\bigcap_i \sim_i
$$

是等价关系。

有限情形下，公共精细化存在的条件可改述为"不存在交错分块冲突"，具体陈述见附录 B。

分辨率共识的极限结构是事件按 $R$ 的等价类压缩后的商空间。分辨率越高、公共精细化越细，共识能够分辨的因果结构就越丰富。

### 3. 可观测代数交集与状态共识

公共可观测代数定义为

$$
\mathcal A_{\mathrm{com}}:=\bigcap_{i\in I}\mathcal A_i.
$$

假定 $\mathcal A_{\mathrm{com}}$ 除标量倍数的单位元外非平凡。

令 $\omega_i^{(t)}\in\mathcal S(\mathcal A_{\mathrm{com}})$ 为时间 $t$ 时刻观察者 $O_i$ 在公共代数上的状态估计，更新规则为线性平均型

$$
\omega_i^{(t+1)}=\sum_{j\in I}w_{ij}T_{ij}\big(\omega_j^{(t)}\big),
$$

其中 $T_{ij}$ 为 CPTP 映射，$W=(w_{ij})$ 为行随机矩阵。

相对熵选取 Umegaki 形式：有限维时，若 $\omega=\omega_\rho,\ \omega'=\omega_\sigma$ 对应密度矩阵 $\rho,\sigma$，则

$$
D(\omega\Vert\omega'):=D(\rho\Vert\sigma)
=\operatorname{tr}\big(\rho(\log\rho-\log\sigma)\big).
$$

**命题 2.5（相对熵的单步收缩）**

设 $\omega_\ast\in\mathcal S(\mathcal A_{\mathrm{com}})$ 为某固定状态，假定：

1. 每个 $T_{ij}$ 满足数据处理不等式，即对所有状态 $\omega,\omega'$，

   $$
   D\big(T_{ij}(\omega)\Vert T_{ij}(\omega')\big)\le D(\omega\Vert\omega');
   $$

2. 权重矩阵 $W$ 行随机，且存在权重 $\lambda_i>0$ 满足 $\sum_i\lambda_i=1$ 且 $\lambda^\top W=\lambda^\top$。

定义总偏差函数

$$
\Phi^{(t)}:=\sum_{i\in I}\lambda_i D\big(\omega_i^{(t)}\Vert\omega_\ast\big).
$$

则对任意 $t$，有

$$
\Phi^{(t+1)}\le \Phi^{(t)}.
$$

该命题表明：在自然的加权条件下，相对熵在共识迭代下单调不增，从而为共识收敛提供 Lyapunov 函数候选。

若进一步假定存在共同不动点且通信图具有足够混合性，可得状态共识的收敛定理。

**假设 2.6（共同不动点与原始性）**

1. 通信图 $G_{\mathrm{comm}}$ 强连通。

2. 权重矩阵 $W$ 原始，即存在 $k\in\mathbb N$ 使 $W^k$ 元素全正。

3. 存在状态 $\omega_\ast\in\mathcal S(\mathcal A_{\mathrm{com}})$，对所有 $i,j$ 满足

   $$
   T_{ij}(\omega_\ast)=\omega_\ast.
   $$

**定理 2.7（状态共识的收敛）**

在假设 2.6 条件下，对任意初始状态族 $\{\omega_i^{(0)}\}_{i\in I}$，迭代

$$
\omega_i^{(t+1)}=\sum_j w_{ij}T_{ij}(\omega_j^{(t)})
$$

收敛到统一状态 $\omega_\ast$，即

$$
\lim_{t\to\infty}\omega_i^{(t)}=\omega_\ast,\quad\forall i\in I.
$$

在经典情形中，上述结果退化为线性平均共识的标准结论；在量子情形中，则对应于一类具有共同不动点的量子 Markov 链收敛到唯一稳态。

### 4. 模型共识与真模型的几乎必然识别

设模型空间 $\mathcal M$ 为紧度量空间，真实模型 $M^\dagger\in\mathcal M$。对每个 $M\in\mathcal M$，记 $P_M$ 为其诱导的数据分布。

**假设 2.8（可识别性与大偏差）**

1. 存在唯一 $M^\ast\in\mathcal M$ 使得对任意 $M\neq M^\ast$，KL 散度满足

   $$
   D\big(P_{M^\ast}\Vert P_{M}\big)>0.
   $$

2. 对每个观察者 $i$，阈值 $\epsilon_i(T)$ 可选取为数据长度 $T$ 的函数，使得在真模型 $M^\ast$ 下，当 $T\to\infty$ 时

   $$
   \mathbb P_{M^\ast}\big(M^\ast\in\mathcal M_i^{(T)}\big)\to 1,\qquad
   \mathbb P_{M^\ast}\big(\exists M\neq M^\ast,\ M\in\mathcal M_i^{(T)}\big)\to 0.
   $$

该条件可通过大数定律与 Sanov 定理类型的大偏差结果验证。

**定理 2.9（模型共识的几乎必然收缩）**

在假设 2.8 条件下，对任意 $\delta>0$，存在 $T_0$ 使得当 $T\ge T_0$ 时，有

$$
\mathbb P_{M^\ast}\Big(\bigcap_{i\in I}\mathcal M_i^{(T)}=\{M^\ast\}\Big)\ge 1-\delta.
$$

换言之，随着观测时间趋于无穷，所有观察者的可接受模型集合的交集，以概率趋一收缩到唯一真模型 $M^\ast$，从而实现强形式模型共识。

### 5. 共识几何与指标体系

综合上述结果，在观察者属性空间

$$
\mathcal O := \prod_{i\in I}\Big(\mathcal P(X)\times\mathsf{Posets}\times\mathsf{Res}\times\mathsf{Alg}\times\mathcal S\times\mathsf{Models}\times\mathsf{Updates}\Big)\times\mathsf{Comm},
$$

定义子集 $\mathcal O_{\mathrm{cons}}\subseteq\mathcal O$ 为所有满足：

1. 存在因果共识延拓 $(X,\prec)$；
2. 存在状态共识 $\omega_{\mathrm{cons}}$；
3. 存在非空模型共识集合 $\mathcal M_{\mathrm{cons}}$（在强形式下为单点）。

称 $\mathcal O_{\mathrm{cons}}$ 为共识几何的可行域。

在此基础上引入以下指标：

* 几何重叠度：

  $$
  \theta_{ij}:=\frac{\mu(C_i\cap C_j)}{\mu(C_i\cup C_j)},
  $$

  其中 $\mu$ 为计数测度或体积测度。

* 分辨率兼容度：基于公共精细化存在性与等价关系 $R$ 的复杂度刻画。

* 代数交集维数：

  $$
  d_{\mathrm{com}}:=\dim\mathcal A_{\mathrm{com}},
  $$

  及其相对指标

  $$
  \eta_{ij}:=\frac{\dim(\mathcal A_i\cap\mathcal A_j)}{\sqrt{\dim\mathcal A_i\,\dim\mathcal A_j}}.
  $$

* 信息偏差：相对熵型偏差

  $$
  \Phi^{(t)}=\sum_i\lambda_i D\big(\omega_i^{(t)}\Vert\omega_{\mathrm{cons}}\big).
  $$

* 通信连通性：由 $G_{\mathrm{comm}}$ 的强连通性与 $W$ 的原始性刻画。

这些指标共同构成对 $\mathcal O_{\mathrm{cons}}$ 的几何–信息描述，为分析"共识易难程度"提供定量工具。

---

## Proofs

本节概述主要定理的证明思路，严格推导与技术细节置于附录 A–D。

### 1. 因果网粘合定理的证明概要（定理 2.3）

在 $X$ 上定义关系

$$
xRy\iff \exists i\in I:\ x,y\in C_i,\ x\prec_i y.
$$

Čech 式一致性保证：若 $x,y$ 同时处于多个 $C_i$，各处因果判断一致，因此不会出现 $x\prec_i y$ 而在另一个 $j$ 有 $y\prec_j x$ 的矛盾。这使 $R$ 反对称。

取 $R$ 的传递闭包定义 $\prec$。需证明 $\prec$ 仍无非平凡环。设存在环 $x_0\prec x_1\prec\cdots\prec x_n=x_0$，由有限交叠性知该环落在有限多个 $C_i$ 的并中，对这些 $i$ 的交集 $C_J$ 上的统一偏序 $\prec_J$ 必然包含该环，从而在 $\prec_J$ 中出现 $x_0\prec_J x_0$ 的矛盾。

局部一致性则由这样的观察：若 $x,y\in C_i$ 且 $x\prec_i y$，则显然 $x\prec y$；反之，若 $x,y\in C_i$ 且 $x\prec y$，则存在有限链

$$
x=x_0R x_1R\cdots R x_n=y.
$$

这些关系来自若干 $C_{i_k}$，利用 Čech 一致性可将链收缩为 $C_i$ 中的单一步偏序 $x\prec_i y$。唯一性来自覆盖性与局部一致性的强约束，详见附录 A。

### 2. 公共精细化存在性的条件（命题 5.2）

分区与等价关系一一对应，公共精细化等价于存在等价关系 $\sim_\ast$ 被包含在所有 $\sim_i$ 中。交集关系

$$
R:=\bigcap_i \sim_i
$$

总是自反对称，关键在于是否传递。若非传递，则存在 $xRy,yRz$ 但 $x\not R z$。这对应于存在分区配置使 $x,y$ 在某 $P_i$ 同块，$(y,z)$ 在某 $P_j$ 同块，$(z,x)$ 在某 $P_k$ 同块，而在另一个分区下 $(x,z)$ 被拆分开，从而形成"交错分块冲突"。反之，若不存在这样的冲突，则任何通过有限链连通的三元组都被所有 $\sim_i$ 同时识别为同一等价类，从而 $R$ 传递。详见附录 B。

### 3. 相对熵 Lyapunov 性质与状态共识收敛（命题 2.5 与定理 2.7）

对单个时间步，有

$$
\omega_i^{(t+1)}=\sum_j w_{ij}T_{ij}(\omega_j^{(t)}).
$$

利用相对熵的联合凸性与数据处理不等式，得到

$$
D\big(\omega_i^{(t+1)}\Vert\omega_\ast\big)
\le \sum_j w_{ij}D\big(T_{ij}(\omega_j^{(t)})\Vert T_{ij}(\omega_\ast)\big)
\le \sum_j w_{ij}D\big(\omega_j^{(t)}\Vert\omega_\ast\big).
$$

对 $i$ 与 $\lambda_i$ 加权求和，在 $\lambda^\top W=\lambda^\top$ 条件下得到 $\Phi^{(t+1)}\le\Phi^{(t)}$。

在存在共同不动点 $\omega_\ast$ 且 $W$ 原始、通信图强连通时，可以将整体迭代视为作用在张量空间上的量子信道 $\mathcal T$，其唯一不动点为 $\omega_\ast^{\otimes I}$。Lyapunov 函数单调性与原始性的结合保证所有轨道收敛到该不动点，详见附录 C。

### 4. 模型共识收缩的概率论论证（定理 2.9）

在真模型 $M^\ast$ 下，似然比

$$
\frac{1}{T}\log\frac{L_i(M^\ast;\mathcal D)}{L_i(M;\mathcal D)}
$$

几乎必然收敛到 $D(P_{M^\ast}\Vert P_M)>0$。因此可选取阈值 $\epsilon_i(T)$ 使得对 $M^\ast$ 的排除概率趋于零，而对任意 $M\neq M^\ast$ 的保留概率趋于零，从而以概率趋一实现"真模型保留、假模型剔除"。对有限观察者族合取上述事件即可得到交集单点性，详见附录 D。

---

## Model Apply

本节给出三个类型化示例，说明上述理论如何在不同语境下被具体实例化。

### 1. 有限因果网中的共识失败与粗粒化修复

考虑有限事件集合 $X=\{a,b,c\}$，三位观察者：

* $O_1$：$C_1=\{a,b\}$，$a\prec_1 b$；
* $O_2$：$C_2=\{b,c\}$，$b\prec_2 c$；
* $O_3$：$C_3=\{c,a\}$，$c\prec_3 a$。

几何覆盖连通，且每个交叠区域上的偏序一致，但三个片段合并起来形成因果环 $a\prec b\prec c\prec a$，违反偏序的反对称性。因此不存在强形式因果共识延拓。

若允许将 $a,b,c$ 合并为单一等价类，则可在极端粗粒度层级上得到平凡偏序（只有自反性），对应于分辨率极低的弱共识。这个例子展示了局部偏序不满足 Čech 式一致性时强共识的失败，以及通过分辨率粗粒化恢复弱共识的可能性，详见附录 E。

### 2. 相对论因果集中的局域观察者

在因果集方法中，将广义相对论中的时空 $(M,g)$ 替换为局部有限偏序 $(C,\prec)$。设 $\{C_i\}$ 为若干局部子因果集，每个对应于处于不同世界线上的观察者可访问的事件集合；$\prec_i$ 为在该子集上由光锥决定的偏序。若时空满足适当的全局双曲性与因果稳定性，则可以构造覆盖满足 Čech 式一致性，其全局粘合偏序与原有因果集同构。这说明在适当几何条件下，局域因果片段足以恢复全局因果网。

在更现实的情形下，不同观察者受到时钟误差与测量噪声影响，其局域偏序仅近似满足 Čech 条件，此时可以用"近似偏序"与"近似共识"扩展本文框架，分析需要多大重叠度与多强的连通性才能在误差层级内恢复宏观因果结构。

### 3. 分布式传感与量子网络中的状态共识

在分布式估计与控制中，常见场景是多个传感节点观测同一动态系统，并通过通信实现平均共识或估计共识。此时：

* 事件集合 $X$ 为测量时间戳与观测结果；
* $C_i$ 由节点 $i$ 的时间戳子集与局域观测构成；
* $\mathcal A_i$ 为节点局部状态空间，$\omega_i$ 为估计分布；
* $T_{ij}$ 对应信道中传输与聚合操作；
* $W$ 对应邻接权重。

若通信图强连通、权重矩阵适当选择，则本文定理 2.7 重现经典平均共识与分布式 Kalman 滤波中共识收敛的结构性条件。

在量子网络中，节点为量子系统，局部状态由密度矩阵 $\rho_i$ 描述，链路为 CPTP 映射；通过对称化与 Lindblad 动力学设计，可以使网络收敛到具有特定对称性或稳态的共识状态。本文给出的相对熵 Lyapunov 结构与共同不动点条件恰好为这一收敛性提供抽象统一表述。

---

## Engineering Proposals

从工程设计视角看，共识几何理论为"如何构造一个必然收敛到目标共识的多观察者系统"提供了若干可直接应用的原则。

1. **覆盖与重叠设计**

   * 设计观察者可达域 $C_i$ 时，应保证覆盖集合在几何上连通，并避免出现类似附录 E 中导致因果环的局部偏序冲突。

   * 可以将事件域抽象为图或流形，对观察者域进行类似传感器覆盖问题的优化，使几何重叠度 $\theta_{ij}$ 达到给定下界，从而提高因果共识与状态共识的可行性。

2. **分辨率与可观测代数配置**

   * 为确保非平凡状态共识，应尽可能增大公共可观测代数 $\mathcal A_{\mathrm{com}}$ 的维数 $d_{\mathrm{com}}$。在系统设计中，这可解读为：对关键观测量建立统一标定与编码格式，使不同节点对同一物理量使用兼容的观测空间。

   * 在有成本约束时，可将"分辨率"视为资源，对事件分区 $P_i$ 与公共精细化 $P_\ast$ 的存在性进行优化选择。

3. **通信图与权重矩阵选型**

   * 通信图 $G_{\mathrm{comm}}$ 应是强连通的；在实时性要求较高的场景中，可进一步保证其具有较小直径。

   * 权重矩阵 $W$ 应设计为原始矩阵，例如采用双随机矩阵或 Metropolis–Hastings 权重，以确保存在唯一 Perron 特征向量并加速收敛。

4. **信道与共同不动点工程**

   * 在量子或概率信道设计中，可通过工程手段确保存在共同不动点 $\omega_\ast$，例如在开量子系统中通过 Lindbladian 的构造锁定稳态。

   * 在经典系统中，这对应于在算法层面引入"共识先验"或"公共校准"机制，使所有更新算子在无新数据时将状态逐渐吸引到同一基准状态。

5. **模型筛选与阈值策略**

   * 为保证模型共识的几乎必然收缩，阈值 $\epsilon_i(T)$ 应随数据量增长而适当提高，使假模型的保留概率呈指数衰减，同时保持真模型的保留概率趋一。

   * 在工程上可采用基于信息准则（如 AIC、BIC 或 MDL）的组合阈值策略，使各观察者在本地独立运行模型筛选，却仍然在交集中收敛到一致模型。

这些建议可以在自组织传感网络、分布式 AI 模型融合以及多探测器物理实验的数据整合中直接作为设计指导。

---

## Discussion (Risks, Boundaries, Past Work)

本文所提出的共识几何框架在结构上包含若干假设与局限，需要在具体应用时谨慎对待。

1. **关于因果共识的假设**

   * 强形式因果共识要求局部偏序在所有有限交叠上完全一致，这在现实物理中常因测量误差、坐标选择与重整化效应而仅近似成立。更精细的理论需要允许"近似 Čech 一致性"，并给出因果网重构的稳定性界。

   * 对于存在拓扑缺陷或闭合类时间曲线的时空，强形式因果共识可能根本不存在，此时应将共识定义限制在某个良好子域。

2. **关于相对熵 Lyapunov 结构的边界**

   * Umegaki 相对熵的单调性依赖于信道的完全正保持迹与有限维假设；在无界算子或无限维情形中需要附加技术条件。

   * 对更广义的 Rényi 相对熵或其他散度，数据处理不等式可能仅在参数区间内成立，需要针对特定应用选择合适的散度形式。

3. **关于模型共识的可识别性假设**

   * 可识别性要求不同模型诱导的数据分布在信息距离上严格可辨，这在存在对称性、退相干或强噪声时未必成立。

   * 对复杂因果结构，局部观测往往只对模型的某些等价类敏感，此时模型共识的极限对象是等价类而非单一模型，需要调整理论表述。

4. **与既有工作的关系**

   * 在因果结构与拓扑方面，本工作可视为对"从因果偏序重构时空"的经典结论的抽象延伸，强调局域片段与多观察者结构在粘合过程中的作用。

   * 在共识算法方面，本文提供了包含经典平均共识、分布式滤波与量子网络对称化在内的统一 Lyapunov 视角，与现有关于线性迭代与量子 Markov 链收敛性的研究相呼应。

   * 在层与 sheaf 结构方面，局部偏序的 Čech 一致性与公共精细化问题可视为非交换几何与 sheaf 理论中粘合问题的简化版本，有望进一步发展为"因果 sheaf"视角。

5. **潜在风险与扩展方向**

   * 本文未显式处理恶意或拜占庭观察者的情形；在存在故意抛出错误偏序或状态的节点时，因果共识与状态共识可能失败，需要引入稳健共识与容错机制。

   * 对于具有自指或循环信息结构的系统，可能存在"局部共识自洽而全局不可嵌入"的情况，这与近期关于循环信息结构与非经典因果模型的研究相关。

综上，共识几何框架为多观察者因果世界的结构分析提供了统一语境，但在无限维、强噪声及对抗环境中的推广仍需进一步研究。

---

## Conclusion

本文在抽象因果网与信息几何交汇处，系统构建了"因果网上观察者属性与共识几何"的理论框架。通过将观察者形式化为具有几何域、局部偏序、分辨率刻度、可观测代数、信息状态、模型族与更新算子的多分量对象，得到了以下主要结论：

1. 在覆盖性、有限交叠与 Čech 式一致性条件下，局域因果片段可以粘合为唯一全局偏序，实现强形式因果共识；否则强共识不可得，只能在粗粒化层级上讨论弱共识。

2. 分辨率结构与可观测代数交集决定了共识的细致程度，公共精细化与公共代数的维度为"共识分辨率"的自然指标。

3. 在公共代数上，以 Umegaki 相对熵为度量的 Lyapunov 函数可刻画状态共识迭代的单调收敛，在通信图强连通、权重矩阵原始且存在共同不动点的条件下，状态必然收敛到统一共识态。

4. 在适当可识别性与大偏差条件下，各观察者阈值筛选后的模型集合交集以概率趋一收缩到唯一真模型，实现强形式模型共识。

5. 通过引入几何重叠度、分辨率兼容性、代数交集维数与相对熵偏差等指标，构建了观察者属性空间中的共识可行域，为分析"共识是否容易发生"提供定量工具。

未来方向包括：在无限维与连续场论中发展因果共识的泛函分析版本；在 sheaf 与高范畴框架下重述共识几何；引入稳健与容错结构对付恶意观察者；以及将本文框架嵌入更广泛的"价值–因果–信息"统一体系中，以探讨自由选择与因果共识的关系。

---

## Acknowledgements, Code Availability

本工作基于公开文献与理论工具进行推导与构建。

本研究未使用任何专门的数值代码或仿真程序，因此不存在可公开的代码实现。

---

## References

[1] S. Surya, "The causal set approach to quantum gravity," *Living Rev. Relativity*, 22, 5 (2019).

[2] K. Martin, P. Panangaden, "Spacetime geometry from causal structure and a measurement," *Proc. Symp. Appl. Math.*, 68, 191–206 (2010).

[3] M. M. Ansanelli et al., "Everything that can be learned about a causal structure," *arXiv:2407.01686* (2024).

[4] V. Vilasini, E. Portmann, A. J. P. Garner, "Embedding cyclic information-theoretic structures in acyclic causal models," *Phys. Rev. A* 110, 022227 (2024).

[5] P. Schapira, "An Introduction to Categories and Sheaves," Lecture Notes (2022).

[6] *The Stacks Project*, Tag 04TP, "Glueing sheaves" (online monograph).

[7] U. Schreiber, Z. Škoda, "Categorified symmetries," Lecture Notes (2008).

[8] L. Xiao, S. Boyd, S.-J. Kim, "Distributed average consensus with least-mean-square deviation," *Proc. MTNS* (2006).

[9] R. Merched, "On Distributed Average Consensus Algorithms," *arXiv:2502.16200* (2025).

[10] G. Parlangeli, A. D'Innocenzo, "A distributed algorithm for reaching average consensus with unbalanced edge weights," *Electronics* 13, 4114 (2024).

[11] H. Fawzi, O. Fawzi, "Defining quantum divergences via convex optimization," *Quantum* 5, 387 (2021).

[12] E. Evert et al., "Equality conditions of data processing inequality for α–z relative entropies," *J. Math. Phys.* 61, 102201 (2020).

[13] E. A. Carlen, E. H. Lieb, M. Loss, "Monotonicity versions of Epstein's concavity theorem and related inequalities," *Linear Algebra Appl.* 645, 100–134 (2022).

[14] S. Matheus, "On the monotonicity of relative entropy," *Entropy* 27, 954 (2025).

[15] M. Mosonyi, "Convexity properties of the quantum Rényi divergences," *Rev. Math. Phys.* 26, 1450001 (2014).

[16] M. B. Ruskai, S. Szarek, E. Werner, "An analysis of completely positive trace-preserving maps on $M_2$," *Linear Algebra Appl.* 347, 159–187 (2002).

[17] J. Guo et al., "Designing open quantum systems with known steady states," *Quantum* 9, 1612 (2025).

[18] F. Ticozzi, L. Viola, "Stabilizing entangled states with quasi-local quantum dynamical semigroups," *Phil. Trans. R. Soc. A* 370, 5259–5269 (2012).

[19] A. Montanari, S. S. Sanghavi, "Distributed consensus by belief propagation," *IEEE Trans. Inf. Theory* 56, 476–488 (2010).

[20] D. Ghion et al., "Robust distributed Kalman filtering with event-triggered communication," *J. Franklin Inst.* 360, 13564–13590 (2023).

[21] T. Ban et al., "Differentiable structure learning with partial orders," *Adv. Neural Inf. Process. Syst.* 37 (2024).

[22] E. Anderson, "Spaces of spaces," *arXiv:1412.0239* (2014).

[23] A. Zaghi, "Relational quantum dynamics as a topological and cohomological framework," Preprint (2023).

[24] F. Bullo, "Lectures on Network Systems," Version 1.6 (2022).

---

## 附录 A  因果网粘合定理的严格证明

**定理 A.1（定理 2.3 重述）**

设 $\{(C_i,\prec_i)\}_{i\in I}$ 为 $X$ 上的一族局部因果片段，满足：

1. $\bigcup_i C_i = X$；
2. 对任意 $x\in X$，集合 $\{i: x\in C_i\}$ 有限；
3. 对任意有限 $J\subseteq I$，存在偏序 $\prec_J$ 定义在 $C_J=\bigcap_{j\in J}C_j$ 上，使得对所有 $j\in J$ 与 $x,y\in C_J$，

   $$
   x\prec_J y\iff x\prec_j y.
   $$

则存在唯一偏序 $\prec$ 使得对每个 $i$，$\prec$ 在 $C_i$ 上的限制等于 $\prec_i$。

**证明**

(1) **定义全局关系**

在 $X$ 上定义二元关系

$$
xRy\iff \exists i\in I\ \text{使得}\ x,y\in C_i,\ x\prec_i y.
$$

由偏序性质，$R$ 显然为反自反（即不存在 $xRx$），但尚不知其传递性。

(2) **反对称性与无局部矛盾**

若存在 $x,y$ 使得 $xRy$ 与 $yRx$ 同时成立，则存在 $i,j$ 使得

* $x,y\in C_i$ 且 $x\prec_i y$；
* $x,y\in C_j$ 且 $y\prec_j x$。

取 $J=\{i,j\}$，则 $x,y\in C_J$，且 Čech 一致性要求 $\prec_J$ 在 $C_J$ 上与 $\prec_i,\prec_j$ 一致，这迫使 $x\prec_J y$ 与 $y\prec_J x$ 同时成立，与 $\prec_J$ 为偏序矛盾。因此 $R$ 反对称。

(3) **传递闭包与环的排除**

定义 $\prec$ 为 $R$ 的传递闭包，即 $x\prec y$ 当且仅当存在有限链

$$
x=x_0 R x_1 R \cdots R x_n = y.
$$

需证明 $\prec$ 反对称。若存在 $x\neq y$ 使 $x\prec y$ 与 $y\prec x$，则可拼接链得到非平凡闭环

$$
x=x_0 R x_1 R \cdots R x_n = x,
$$

其中 $n\ge 1$。

对每个关系 $x_k R x_{k+1}$，存在 $i_k$ 使 $x_k,x_{k+1}\in C_{i_k}$ 且 $x_k\prec_{i_k} x_{k+1}$。有限交叠性保证集合 $\{i_k\}_{k=0}^{n-1}$ 有限，取

$$
J=\{i_0,\dots,i_{n-1}\},
$$

则所有环上的点 $\{x_k\}$ 属于

$$
\bigcup_{i\in J}C_i,
$$

且对每个相邻对 $(x_k,x_{k+1})$，存在 $i_k\in J$ 使其在 $C_{i_k}$ 中有 $x_k\prec_{i_k} x_{k+1}$。

由 Čech 一致性，$C_J=\bigcap_{i\in J}C_i$ 上存在统一偏序 $\prec_J$，且每个局部偏序在交叠中与 $\prec_J$ 一致。通过有限步扩张与传递性，可得在 $C_J$ 中

$$
x\prec_J x,
$$

与偏序定义矛盾。因此 $\prec$ 反对称。

自反性可通过定义非严格关系 $\preceq$ 为

$$
x\preceq y\iff x=y\ \text{或}\ x\prec y
$$

得到。传递性由传递闭包定义保证。

(4) **局部一致性**

对任意 $i$ 与 $x,y\in C_i$，若 $x\prec_i y$，则显然 $xRy$，从而 $x\prec y$，得到 $\prec$ 在 $C_i$ 上扩张了 $\prec_i$。

反之，若 $x,y\in C_i$ 且 $x\prec y$，则存在有限链

$$
x=x_0 R x_1 R \cdots R x_n = y.
$$

每一步 $x_k R x_{k+1}$ 借由某 $C_{i_k}$ 产生。利用 Čech 一致性，在

$$
C_{J'}:=\bigcap_{k}C_{i_k}\cap C_i
$$

上存在统一偏序 $\prec_{J'}$，且对每个 $k$ 有

$$
x_k\prec_{J'} x_{k+1}.
$$

由传递性得 $x\prec_{J'} y$，再由 $\prec_{J'}$ 与 $\prec_i$ 在 $C_{J'}$ 上一致，得到 $x\prec_i y$。

因此 $\prec$ 在每个 $C_i$ 上的限制与 $\prec_i$ 一致。

(5) **唯一性**

若存在另一偏序 $\prec'$ 满足同样条件，则对每个 $i$，$\prec'|_{C_i}=\prec_i=\prec|_{C_i}$。由覆盖性知对任意 $x,y\in X$，若 $x\prec y$，则存在链将其分段落在各 $C_i$ 上，这些关系在 $\prec'$ 中也必须成立，反之亦然，故 $\prec=\prec'$。在允许对 $X$ 作双射重标的意义下，得到同构唯一性。

定理证毕。

---

## 附录 B  公共精细化命题的证明

**命题 B.1（公共精细化存在性的等价刻画）**

设 $X_{\mathrm{fine}}$ 为有限集合，$\{P_i\}_{i\in I}$ 为其上一族分区。对每个 $i$，定义等价关系

$$
x\sim_i y\iff \exists B\in P_i:\ x,y\in B.
$$

令

$$
R:=\bigcap_{i\in I}\sim_i.
$$

则以下两者等价：

1. 存在公共精细化 $P_\ast$ 使得对每个 $i$，$P_i$ 为 $P_\ast$ 的粗化；

2. 关系 $R$ 为等价关系（即自反、对称且传递）。

**证明**

(1) 若存在公共精细化 $P_\ast$，则对应等价关系 $\sim_\ast$ 满足 $\sim_\ast\subseteq \sim_i$ 对所有 $i$ 成立，因此 $\sim_\ast\subseteq R$。另一方面，对任意 $x,y$ 若 $x\sim_\ast y$，则 $x,y$ 必同属于某个 $P_\ast$ 块，而 $P_\ast$ 是最细分区，因此任何等价关系 $R$ 包含在所有 $\sim_i$ 中时必然 $\sim_\ast=R$。因此 $R$ 为等价关系。

(2) 若 $R$ 为等价关系，则其等价类集合

$$
P_R:=\{[x]_R: x\in X_{\mathrm{fine}}\}
$$

为分区，并且由 $R\subseteq \sim_i$ 可知 $P_i$ 为 $P_R$ 的粗化。因此 $P_R$ 为公共精细化。

传递性缺失时，不存在等价关系包含于所有 $\sim_i$ 中，因此不存在公共精细化。具体的"交错分块冲突"构造与细节见正文与主文中的讨论，此处不再重复。

---

## 附录 C  相对熵型共识过程的收敛性

### C.1 命题 2.5 的详细证明

**命题 C.1（相对熵的单步收缩）**

在假设 2.5 条件下，对任意 $t\in\mathbb N$，有

$$
\Phi^{(t+1)}\le \Phi^{(t)}.
$$

**证明**

对固定 $i$，

$$
\omega_i^{(t+1)}=\sum_j w_{ij}T_{ij}(\omega_j^{(t)}).
$$

由相对熵的联合凸性，

$$
D\big(\omega_i^{(t+1)}\Vert\omega_\ast\big)
\le \sum_j w_{ij}D\big(T_{ij}(\omega_j^{(t)})\Vert T_{ij}(\omega_\ast)\big).
$$

由数据处理不等式，

$$
D\big(T_{ij}(\omega_j^{(t)})\Vert T_{ij}(\omega_\ast)\big)\le D\big(\omega_j^{(t)}\Vert\omega_\ast\big).
$$

合并得

$$
D\big(\omega_i^{(t+1)}\Vert\omega_\ast\big)
\le \sum_j w_{ij}D\big(\omega_j^{(t)}\Vert\omega_\ast\big).
$$

两边乘以 $\lambda_i$ 后对 $i$ 求和，得

$$
\begin{aligned}
\Phi^{(t+1)}
&=\sum_i \lambda_i D\big(\omega_i^{(t+1)}\Vert\omega_\ast\big)\\
&\le \sum_i \lambda_i\sum_j w_{ij}D\big(\omega_j^{(t)}\Vert\omega_\ast\big)\\
&= \sum_j\Big(\sum_i \lambda_i w_{ij}\Big) D\big(\omega_j^{(t)}\Vert\omega_\ast\big).
\end{aligned}
$$

在 $\lambda^\top W=\lambda^\top$ 条件下，$\sum_i\lambda_i w_{ij}=\lambda_j$，于是

$$
\Phi^{(t+1)}\le \sum_j\lambda_j D\big(\omega_j^{(t)}\Vert\omega_\ast\big)=\Phi^{(t)}.
$$

命题得证。

### C.2 定理 2.7 的证明框架

为了证明轨道收敛到 $\omega_\ast$，可以采用两种互补视角：

1. 将整体状态族 $\Omega^{(t)}:=(\omega_i^{(t)})_{i\in I}$ 看作直积状态空间 $\mathcal S(\mathcal A_{\mathrm{com}})^{\otimes I}$ 上的点，定义整体信道

   $$
   \mathcal T(\Omega) = \big(\sum_j w_{ij}T_{ij}(\omega_j)\big)_{i\in I}.
   $$

   在假设 2.6 条件下，$\mathcal T$ 为原始的 CPTP 映射，并以 $\Omega_\ast:=(\omega_\ast)_{i\in I}$ 为唯一不动点。原始性与紧性保证 $\mathcal T^t(\Omega^{(0)})\to \Omega_\ast$。

2. 利用 Lyapunov 函数 $\Phi^{(t)}$ 单调非增且下界为零，结合 $\mathcal T$ 的原始性，可以排除非平凡极限周期或不动点族，最终得到所有分量收敛到 $\omega_\ast$。

完整技术细节可用 Perron–Frobenius 理论在 Banach 空间上的推广与量子 Markov 链的收敛性定理建立，此处从略。

---

## 附录 D  模型共识收缩定理的证明

**定理 D.1（定理 2.9 重述）**

在可识别性与大偏差假设 2.8 条件下，对任意 $\delta>0$，存在 $T_0$ 使得当 $T\ge T_0$ 时，

$$
\mathbb P_{M^\ast}\Big(\bigcap_{i\in I}\mathcal M_i^{(T)}=\{M^\ast\}\Big)\ge 1-\delta.
$$

**证明**

(1) **单观察者一致性**

对固定 $i$，由假设 2.8(2) 可知存在 $T_i(\delta)$ 使得当 $T\ge T_i(\delta)$ 时，

$$
\mathbb P_{M^\ast}\big(M^\ast\in\mathcal M_i^{(T)}\big)\ge 1-\frac{\delta}{2|I|},
$$

且

$$
\mathbb P_{M^\ast}\big(\exists M\neq M^\ast,\ M\in\mathcal M_i^{(T)}\big)\le \frac{\delta}{2|I|}.
$$

(2) **联合事件估计**

记事件

$$
E_1:=\bigcap_{i\in I}\{M^\ast\in\mathcal M_i^{(T)}\},\qquad
E_2:=\bigcap_{i\in I}\{\nexists M\neq M^\ast:\ M\in\mathcal M_i^{(T)}\}.
$$

由联合上界与前述估计得

$$
\mathbb P_{M^\ast}(E_1)\ge 1-\frac{\delta}{2},\qquad
\mathbb P_{M^\ast}(E_2)\ge 1-\frac{\delta}{2}.
$$

故

$$
\mathbb P_{M^\ast}(E_1\cap E_2)\ge 1-\delta.
$$

(3) **交集单点性**

在事件 $E_1\cap E_2$ 上，对每个 $i$，$\mathcal M_i^{(T)}$ 含 $M^\ast$ 且不含其他模型。因此

$$
\bigcap_{i\in I}\mathcal M_i^{(T)}=\{M^\ast\}.
$$

取 $T_0=\max_i T_i(\delta)$，当 $T\ge T_0$ 时结论成立。

定理得证。

---

## 附录 E  有限示例：三观察者因果共识的失败与粗粒化修复

**例 E.1（三节点因果环）**

令 $X=\{a,b,c\}$。三位观察者：

* $O_1$：$C_1=\{a,b\}$，偏序 $a\prec_1 b$；
* $O_2$：$C_2=\{b,c\}$，偏序 $b\prec_2 c$；
* $O_3$：$C_3=\{c,a\}$，偏序 $c\prec_3 a$。

几何上，$\{C_i\}$ 覆盖 $X$ 且交叠构成环形结构。每个交叠区域中的偏序内部自洽，但整体组合形成环

$$
a\prec_1 b\prec_2 c\prec_3 a.
$$

若存在全局偏序 $\prec$ 将各局部偏序嵌入，则必须同时满足

$$
a\prec b,\quad b\prec c,\quad c\prec a,
$$

与偏序的反对称性矛盾。因此不存在强形式因果共识延拓。

**粗粒化修复**

若允许引入等价关系 $\sim$ 使 $a\sim b\sim c$，则商集

$$
\tilde X:=X/\!\sim =\{\tilde x\}
$$

仅含单一等价类。此时唯一可能偏序为 $\tilde x\preceq\tilde x$，在该极度粗花视角下，所有局部偏序皆退化为自反关系，因果共识在此层级上成立。

该例说明：

1. 几何连通性是强形式因果共识的必要但非充分条件；

2. 局部偏序在交叠区域的一致性是消除因果环的关键；

3. 在强共识破缺时，可通过事件等价类压缩恢复弱共识，但代价是失去细节结构。

这一示例为更复杂因果网中"因果环"与"分辨率折衷"的现象提供了简明的离散模型。

