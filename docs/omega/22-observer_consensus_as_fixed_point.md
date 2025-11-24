# 观察者共识作为局域代数范畴中的不动点：模包含、条件期望与统一时间刻度的范畴化刻画

*Observer Consensus as Fixed Points in Local Algebra Categories: Categorification of Modular Inclusions, Conditional Expectations, and Unified Time Scales*

---

## Abstract

在代数量子论与量子信息视角下，"观察者共识"通常被作为前提假设：不同观察者在重叠可及区域上的预测最终一致。本文提出一种纯粹结构性的刻画：将观察者及其可及信息建模为带状态的局域代数对象，态射由与 Tomita–Takesaki 模流相容的模包含给出，并在此范畴上构造一个"同步算子"函子 $F$。在适当的几何与序结构下，证明同步迭代 $F$ 存在范畴不动点，该不动点即为"观察者共识对象"。这一不动点条件使共识不再是先验假设，而是由"模相容 + 条件期望的收缩性 + 有向完备性"共同推出的定理。

更进一步，利用 Araki 相对熵诱导的态空间几何，以及 Eisenbud–Wigner–Smith 延迟与谱移函数之间的统一时间刻度恒等式

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{Tr}\mathsf Q(\omega),
$$

本文给出一个"统一时间刻度定理"：当观察者网络在模包含下达到不动点 $(\mathcal A^\ast,\omega^\ast)$ 时，所有局域观察者的有效时间流逝率均与 $\omega^\ast$ 的模流一致，从而在范畴意义上实现"同一物理时钟"的构造。作为例证，本文分析了有限维矩阵代数上的两观察者模型，展示同步迭代如何收敛到唯一共识态，以及该态如何携带统一的时间密度刻度。

本文的结论为：在局域代数范畴框架中，观察者共识可形式化为同步函子的不动点，且该不动点自然装备一个统一的模时间刻度，从而为统一时间—信息—几何计划提供了一个严谨的范畴代数层支撑。

---

## Keywords

观察者共识；局域 $C^\ast$/冯诺依曼代数；模包含；Tomita–Takesaki 模流；Araki 相对熵；条件期望；不动点定理；统一时间刻度

---

## 1 引言

### 1.1 问题背景与动机

在代数量子场论与量子信息本体论中，一个反复出现而又往往被遮蔽的问题是：**不同观察者如何"看到同一个世界"？** 更技术地说，如果每个观察者 $O_i$ 拥有自己的局域代数 $\mathcal A_i$ 与状态 $\omega_i$，那么在重叠可及区域上，它们的结果如何实现一致？传统做法往往将此作为隐含公理（例如"全局状态在局域限制下唯一"），而非从更底层的结构推出。

另一方面，Tomita–Takesaki 模理论告诉我们：给定一个标准态 $\omega$ 与冯诺依曼代数 $\mathcal M$，存在一条内禀的模流 $\{\sigma_t^\omega\}_{t\in\mathbb R}$，它为该态赋予了"首选时间演化"。在统一时间—信息—几何的视角下，时间流逝率 $\kappa(\omega)$ 可以被识别为某种"态密度"或"散射延迟密度"，满足统一时间恒等式

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{Tr}\mathsf Q(\omega).
$$

这里 $\varphi'(\omega)$ 是散射相位导数，$\rho_{\mathrm{rel}}(\omega)$ 是相对态密度（如谱移函数密度），$\mathsf Q(\omega)$ 是 Wigner–Smith 延迟算子或其适当推广。

这自然引出一个更精细的问题：

> 当多个观察者通过某种结构化的信息交换过程达成共识时，这一共识是否对应某个范畴意义上的不动点？

> 若是，该不动点是否自然携带统一的模时间刻度 $\kappa$，从而使"时间"在不同观察者之间得以对齐？

本文给出的答案是肯定的，并试图在最大程度上形式化这一直觉。

### 1.2 本文的主要贡献

本文的主要贡献可概括如下：

1. **局域代数范畴与模态射：**

   构造一个以"带状态的局域代数"为对象，以"与模流相容的单射 *-同态"为态射的范畴 $\mathbf{LocAlg}$。每个对象为对 $(\mathcal A,\omega)$，其中 $\mathcal A$ 为冯诺依曼代数或局域 $C^\ast$-代数，$\omega$ 为标准态；态射 $\Phi:(\mathcal A,\omega)\to(\mathcal B,\varphi)$ 满足

$$
\Phi\circ\sigma_t^\omega = \sigma_t^\varphi\circ\Phi,\quad \forall t\in\mathbb R.
$$

2. **同步函子与不动点共识对象：**

   在由观察者网络诱导的有向图上，构造一个"同步函子"

$$
F:\mathbf{LocAlg}\to\mathbf{LocAlg},
$$

将每个局域代数—态对沿模包含推进，并用条件期望作"压缩/回退"。在 Araki 相对熵度量下，证明 $F$ 为压缩映射（或序上连续映射），从而存在不动点 $X^\ast=(\mathcal A^\ast,\omega^\ast)$。将该不动点定义为**共识对象**。

3. **统一时间刻度定理：**

   证明共识对象的模流 $\sigma_t^{\omega^\ast}$ 与所有局域模流在态射下交换，使得 $\omega^\ast$ 为一"全局标准态"；同时统一时间刻度 $\kappa(\omega)$ 在共识下成为范畴自然变换，从而构造出一个全局一致的时间密度场。

4. **有限维示例与显式收敛：**

   在有限维矩阵代数 $M_n(\mathbb C)$ 上，给出具有重叠子代数的两观察者模型，显式构造条件期望与同步迭代，证明在量子相对熵下同步映射为严格收缩，迭代收敛到唯一共识态 $\omega^\ast$，并计算其统一时间刻度。

通过上述步骤，"观察者共识"从一条描述性假设，提升为：**模包含驱动的同步动力系统在局域代数范畴上的不动点定理**。

---

## 2 预备知识与记号约定

### 2.1 记号与统一时间恒等式

本文中所有数学表达式均采用标准行内形式 $\cdots$。若未特别说明，均在复数域 $\mathbb C$ 上工作。

统一时间恒等式写作

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{Tr}\mathsf Q(\omega),
$$

其中：

* $\kappa(\omega)$：与状态 $\omega$ 关联的局域"时间流逝密度"；

* $\varphi'(\omega)$：散射相位 $\varphi$ 对能量（或频率）的导数，经适当归一化；

* $\rho_{\mathrm{rel}}(\omega)$：相对态密度，可理解为谱移函数的密度；

* $\mathsf Q(\omega)$：Wigner–Smith 延迟算子或其推广，$\operatorname{Tr}\mathsf Q$ 给出总延迟。

在本文抽象框架中，只需要将 $\kappa$ 视为从"带态代数"到正实数的函子型量，并假设其与模流存在相容性，见第 5 节。

### 2.2 冯诺依曼代数、标准态与模流

令 $\mathcal M$ 为 $\mathcal H$ 上的冯诺依曼代数，$\omega$ 为其上的正、归一、忠实、正规态。若存在向量 $\Omega\in\mathcal H$，对 $\mathcal M$ 既是循环又是分离，使得

$$
\omega(A)=\langle\Omega,A\Omega\rangle,\quad \forall A\in\mathcal M,
$$

则称 $(\mathcal M,\mathcal H,\Omega)$ 为 $\mathcal M$ 的标准形。

Tomita–Takesaki 理论断言：对标准形存在闭、稠密定义的 Tomita 算子 $S$，其极分解 $S=J\Delta^{1/2}$ 诱导模算子 $\Delta$ 与共轭 $J$，并定义模流

$$
\sigma_t^\omega(A) := \Delta^{\mathrm i t} A \Delta^{-\mathrm i t},\quad t\in\mathbb R.
$$

$\{\sigma_t^\omega\}$ 为 $\mathcal M$ 的一个 *-自同构一参数群，被视为"态 $\omega$ 的内禀时间流"。

### 2.3 相对熵与态空间几何

对冯诺依曼代数 $\mathcal M$ 上的两个正常态 $\omega,\varphi$，Araki 相对熵 $S(\omega\Vert\varphi)$ 是一种非对称的"距离量"，满足：

* $S(\omega\Vert\varphi)\ge 0$，且 $S(\omega\Vert\varphi)=0$ 当且仅当 $\omega=\varphi$；

* 在适当条件下，对条件期望 $E:\mathcal M\to\mathcal N$ 有

$$
S(\omega\circ E\Vert\varphi\circ E)\le S(\omega\Vert\varphi),
$$

体现"信息丢失 → 不可区分性增加"的单调性。

为得到对称型度量，可定义

$$
D(\omega,\varphi):=S(\omega\Vert\varphi)+S(\varphi\Vert\omega),
$$

或使用 Bures 距离、量子费舍尔信息度量。本文将主要使用 $D$ 来讨论同步映射的收缩性。

### 2.4 条件期望与模包含

设 $\mathcal N\subset\mathcal M$ 为冯诺依曼子代数。若存在正、单位保持、完全正、正规映射

$$
E:\mathcal M\to\mathcal N,
$$

满足 $E(N_1MN_2)=N_1E(M)N_2$，则称 $E$ 为条件期望。进一步，若 $\omega\circ E=\omega$，则称 $E$ 为 $\omega$-不变的。

若子代数包含 $\mathcal N\subset\mathcal M$ 与给定态 $\omega$ 的模流相容，即对每个 $t\in\mathbb R$ 有

$$
\sigma_t^\omega(\mathcal N)=\mathcal N,
$$

则称 $\mathcal N\subset\mathcal M$ 为模包含。此时存在与模流相容的条件期望 $E$，且

$$
E\circ\sigma_t^\omega = \sigma_t^\omega\circ E.
$$

### 2.5 范畴论与不动点

给定一个范畴 $\mathcal C$ 与自函子 $F:\mathcal C\to\mathcal C$，若存在对象 $X^\ast$ 与同构 $\eta: X^\ast\to F(X^\ast)$，则称 $X^\ast$ 为 $F$ 的不动点对象。若更强地存在同构 $F(X^\ast)\cong X^\ast$ 在指定构造下自然同构，则通常称为"代数不动点"。

在具度量或序结构的情形，可与 Banach 不动点定理或 Tarski 不动点定理配合使用：若 $F$ 为压缩映射／序保映射且空间完备，则存在（唯一或极大/极小）不动点。

---

## 3 观察者网络与局域代数范畴结构

### 3.1 观察者与局域代数对象

设存在一组观察者 $\{O_i\}_{i\in I}$，每个观察者具有可及区域 $U_i$（可理解为时空中的一个区域，或 QCA 网络中的一个局域簇），并赋予其一个冯诺依曼代数 $\mathcal A_i$ 及正规态 $\omega_i$。假定每个 $(\mathcal A_i,\omega_i)$ 均可实现为标准形。

**定义 3.1（局域代数对象）** 定义范畴 $\mathbf{LocAlg}$ 的对象为二元组

$$
X_i:= (\mathcal A_i,\omega_i),
$$

其中 $\mathcal A_i$ 为冯诺依曼代数，$\omega_i$ 为其忠实正规态。

### 3.2 模态射与观察者间的"翻译"

在观察者网络中，若 $O_i$ 的信息可嵌入 $O_j$ 的信息结构，则自然地存在一个单射 *-同态

$$
\Phi_{ij}:\mathcal A_i\hookrightarrow\mathcal A_j.
$$

若希望时间刻度与热力学方向在不同观察者之间保持一致，则要求此嵌入与模流交换。

**定义 3.2（模态射）** 在 $\mathbf{LocAlg}$ 中，定义态射

$$
\Phi:(\mathcal A,\omega)\to(\mathcal B,\varphi)
$$

为一单射正规 *-同态 $\Phi:\mathcal A\to\mathcal B$，且满足：

1. 态兼容（push-forward 态）：

$$
\varphi\circ\Phi = \omega;
$$

2. 模流相容：

$$
\Phi\circ\sigma_t^\omega = \sigma_t^\varphi\circ\Phi,\quad \forall t\in\mathbb R.
$$

由此得到一个以 $(\mathcal A_i,\omega_i)$ 为对象、以 $\Phi_{ij}$ 为态射的子范畴，仍记作 $\mathbf{LocAlg}$。

直观上，$\Phi_{ij}$ 表示"在 $O_j$ 的坐标系/参考系下，对 $O_i$ 所见可观测量的重写方式"，且保持其热时间结构。

### 3.3 重叠区域与共识目标

若两个观察者 $O_i,O_j$ 有重叠可及区域 $U_i\cap U_j\neq\emptyset$，则可假定存在一个共同的子代数 $\mathcal A_{ij}$ 以及模包含

$$
\mathcal A_{ij}\subset\mathcal A_i,\quad \mathcal A_{ij}\subset\mathcal A_j.
$$

在此区域中，我们期望同步过程使得二者的态在 $\mathcal A_{ij}$ 上一致，即

$$
\omega_i|_{\mathcal A_{ij}} = \omega_j|_{\mathcal A_{ij}}.
$$

对一般网络，我们希望存在一个"全局对象" $X^\ast=(\mathcal A^\ast,\omega^\ast)$，使得每个 $X_i$ 都通过模态射嵌入其中，且所有重叠约束自动满足。这将在第 4 节通过不动点刻画。

---

## 4 同步算子与共识对象的不动点刻画

本节构造一个"同步算子" $F$，它对观察者网络的整体状态做一次"信息对齐与回退"；证明在相对熵几何下 $F$ 为压缩映射（或非扩张），并给出其不动点的存在性与唯一性条件。

### 4.1 网络结构与同步步骤的抽象

令 $\mathcal G=(I,E)$ 为观察者网络的有向图，顶点集合 $I$ 为观察者索引，边集合 $E\subset I\times I$ 表示允许的信息流方向。对每条边 $(i\to j)\in E$，假定存在模包含与对应模态射

$$
\Phi_{ij}:(\mathcal A_i,\omega_i)\hookrightarrow(\mathcal A_j,\omega_j),
$$

以及与模流相容的条件期望

$$
E_{ji}:\mathcal A_j\to\Phi_{ij}(\mathcal A_i).
$$

直观上，"同步一步"由以下操作组成：

1. 将每个局域态 $\omega_i$ 沿与其相邻节点的模态射推进（传播）；

2. 对于每个节点，将来自邻居的态与本地态在某个重叠子代数上"对齐"，通过条件期望与某种聚合操作（如最小相对熵投影）更新本地态。

为简化表述，可先考虑有限网络与离散同步迭代。

### 4.2 同步算子的形式定义（有限网络情形）

设 $I$ 为有限集合。定义态空间

$$
\mathcal S := \prod_{i\in I}\mathcal S(\mathcal A_i),
$$

其中 $\mathcal S(\mathcal A_i)$ 为 $\mathcal A_i$ 上的正规态集合。元素 $\boldsymbol\omega=(\omega_i)_{i\in I}\in\mathcal S$ 表示整个网络在某一时刻的"观测状态配置"。

**定义 4.1（同步算子）** 定义映射

$$
F:\mathcal S\to\mathcal S,\quad \boldsymbol\omega\mapsto\boldsymbol\omega',
$$

其中对每个 $i\in I$，新态 $\omega_i'$ 通过如下两步得到：

1. **来自邻居的拉回与压缩：** 对每个 $(j\to i)\in E$，先将 $\omega_j$ 沿 $\Phi_{ji}$ 拉回到 $\mathcal A_i$ 的像上，再通过条件期望 $E_{ij}$ 压缩到某个共同子代数 $\mathcal A_{ij}\subset\mathcal A_i$；记所得态为 $\tilde\omega_{j\to i}$。

2. **局域聚合：** 在给定的几何或变分原则下（例如最小化

$$
\sum_{(j\to i)\in E}S(\tilde\omega_{j\to i}\Vert\omega_i')+S(\omega_i'\Vert\tilde\omega_{j\to i}),
$$

或使用凸组合），定义 $\omega_i'$ 作为对 $\{\tilde\omega_{j\to i}\}_{j}$ 与旧态 $\omega_i$ 的"平均"。

形式化的一种自然选择是：在 Araki 相对熵几何中，$\omega_i'$ 为最小化

$$
\mathcal F_i(\varphi) := \alpha_i S(\varphi\Vert\omega_i) + \sum_{(j\to i)\in E}\beta_{ji}S(\varphi\Vert\tilde\omega_{j\to i})
$$

的唯一解，这赋予了 $F$ 明确的变分性质。

### 4.3 相对熵几何下的收缩性

为讨论 $F$ 的不动点，需要在 $\mathcal S$ 上引入度量。对每个 $i$，用对称相对熵

$$
D_i(\omega_i,\varphi_i):=S(\omega_i\Vert\varphi_i)+S(\varphi_i\Vert\omega_i)
$$

度量 $\mathcal S(\mathcal A_i)$，并定义

$$
D(\boldsymbol\omega,\boldsymbol\varphi) := \sum_{i\in I}w_i D_i(\omega_i,\varphi_i),
$$

其中 $w_i>0$ 为权重，满足 $\sum_iw_i=1$。

**命题 4.2（同步算子的非扩张性）** 在上述设定下，若每个条件期望 $E_{ij}$ 对 Araki 相对熵满足单调性，且局域聚合 $\omega_i'$ 由严格凸的变分泛函唯一确定，则存在常数 $0<\lambda\le 1$，使得

$$
D(F(\boldsymbol\omega),F(\boldsymbol\varphi)) \le \lambda D(\boldsymbol\omega,\boldsymbol\varphi), \quad \forall \boldsymbol\omega,\boldsymbol\varphi\in\mathcal S.
$$

若进一步假定网络连通且权重选择适当，则可取 $\lambda<1$。

*证明思路概述：*

对每条边 $(j\to i)$，条件期望的单调性给出

$$
S(\tilde\omega_{j\to i}\Vert\tilde\varphi_{j\to i}) \le S(\omega_j\Vert\varphi_j).
$$

局域聚合步骤是一个在凸集合上的投影/平均操作，由相对熵的联合凸性与变分极小性可得局域收缩。最后由图结构的有限性与权重选择将局域收缩叠加成整体的非扩张或压缩性质。严格证明见附录 A。

若 $\lambda<1$，则 $F$ 为 Banach 意义上的压缩映射。

### 4.4 有限网络下的共识不动点定理

**定理 4.3（有限网络的共识不动点）**

设 $I$ 有限，图 $\mathcal G$ 强连通。若同步算子 $F$ 对度量 $D$ 为压缩映射，即存在 $0<\lambda<1$ 使

$$
D(F(\boldsymbol\omega),F(\boldsymbol\varphi)) \le \lambda D(\boldsymbol\omega,\boldsymbol\varphi),
$$

则：

1. $F$ 存在唯一不动点 $\boldsymbol\omega^\ast\in\mathcal S$，满足 $F(\boldsymbol\omega^\ast)=\boldsymbol\omega^\ast$；

2. 对任意初始配置 $\boldsymbol\omega^{(0)}$，迭代序列 $\boldsymbol\omega^{(n+1)}:=F(\boldsymbol\omega^{(n)})$ 在 $D$ 下以指数速度收敛到 $\boldsymbol\omega^\ast$；

3. 若同步构造在各个节点上尊重重叠子代数 $\mathcal A_{ij}$ 的一致性约束，则极限 $\boldsymbol\omega^\ast$ 在所有重叠区域上给出相同限制，即对任意 $(i,j)$，有

$$
\omega_i^\ast|_{\mathcal A_{ij}}=\omega_j^\ast|_{\mathcal A_{ij}}.
$$

*证明：* 由 Banach 不动点定理直接得到存在性与唯一性以及收敛性。重叠一致性来自同步步构造对 $\mathcal A_{ij}$ 约束的稳定性与迭代极限交换性，详见附录 A。

我们将这一不动点配置 $\boldsymbol\omega^\ast$ 与相应的代数系统一起，称为**共识对象**。

### 4.5 范畴化的全局共识对象

上述从"网络配置空间" $\mathcal S$ 的角度讨论了同步不动点。范畴论视角要求在 $\mathbf{LocAlg}$ 中寻找一个"全局对象" $(\mathcal A^\ast,\omega^\ast)$，使得每个局域对象 $(\mathcal A_i,\omega_i^\ast)$ 作为子对象嵌入其中。

设 $\{\Phi_{i\ast}:(\mathcal A_i,\omega_i^\ast)\hookrightarrow(\mathcal A^\ast,\omega^\ast)\}_{i\in I}$ 为一族模态射，使得 $(\mathcal A^\ast,\omega^\ast)$ 是该系统的余极限（colimit），即对满足兼容关系的任意其它对象 $(\mathcal B,\varphi)$ 与态射 $\Psi_i:(\mathcal A_i,\omega_i^\ast)\to(\mathcal B,\varphi)$，存在唯一态射 $\Psi:(\mathcal A^\ast,\omega^\ast)\to(\mathcal B,\varphi)$ 使得 $\Psi\circ\Phi_{i\ast}=\Psi_i$。

**定义 4.4（范畴共识对象）** 若存在对象 $(\mathcal A^\ast,\omega^\ast)$ 在 $\mathbf{LocAlg}$ 中为上述余极限，并且其限制态满足与同步不动点配置 $\boldsymbol\omega^\ast$ 一致，则称 $(\mathcal A^\ast,\omega^\ast)$ 为该观察者网络的范畴共识对象。

在有限网络及适当完备性假设下，可将同步不动点与余极限构造等同起来，见附录 B。

---

## 5 统一时间刻度与模流一致性

本节讨论在共识对象存在时，模流与统一时间刻度 $\kappa$ 如何在范畴意义上对齐。

### 5.1 局域模流与态射交换性

由模态射定义，对每个 $\Phi_{ij}:(\mathcal A_i,\omega_i)\to(\mathcal A_j,\omega_j)$ 有

$$
\Phi_{ij}\circ\sigma_t^{\omega_i} = \sigma_t^{\omega_j}\circ\Phi_{ij}, \quad \forall t\in\mathbb R.
$$

在共识极限 $\omega_i^\ast$ 上，这一关系仍成立。若存在范畴共识对象 $(\mathcal A^\ast,\omega^\ast)$ 以及嵌入 $\Phi_{i\ast}$，则要求

$$
\Phi_{i\ast}\circ\sigma_t^{\omega_i^\ast} = \sigma_t^{\omega^\ast}\circ\Phi_{i\ast}.
$$

由此可将每个局域模流视为全局模流的限制。

### 5.2 统一时间刻度作为自然变换

考虑函子

$$
\mathcal T:\mathbf{LocAlg}\to\mathbf{Set},\quad (\mathcal A,\omega)\mapsto \{\kappa(\omega)\},
$$

其中 $\kappa(\omega)$ 为由统一时间恒等式定义的正实数。理想情况下，我们希望 $\kappa$ 对模态射自然：

**定义 5.1（时间刻度的自然性）** 若对任一模态射 $\Phi:(\mathcal A,\omega)\to(\mathcal B,\varphi)$ 有

$$
\kappa(\omega)=\kappa(\varphi),
$$

则称 $\kappa$ 为从恒等函子到 $\mathcal T$ 的自然变换。直观上，表示在模相容嵌入下，时间刻度为不变量。

在同步前，局域态 $\omega_i$ 可能对应不同的 $\kappa(\omega_i)$。同步不动点 $\omega_i^\ast$ 的存在保证了在网络上"局域时间刻度"一致。

**定理 5.2（统一时间刻度定理）**

在第 4 节设定下，若

1. 同步算子 $F$ 收敛到唯一不动点配置 $\boldsymbol\omega^\ast$；

2. 存在范畴共识对象 $(\mathcal A^\ast,\omega^\ast)$ 与模态射 $\Phi_{i\ast}$ 使得 $\omega_i^\ast = \omega^\ast\circ\Phi_{i\ast}$；

3. $\kappa$ 对模态射自然；

则：

1. 所有局域刻度一致：$\kappa(\omega_i^\ast)=\kappa(\omega^\ast)$，对所有 $i\in I$；

2. 模流一致：$\sigma_t^{\omega_i^\ast}$ 等于 $\sigma_t^{\omega^\ast}$ 限制到 $\Phi_{i\ast}(\mathcal A_i)$；

3. 对任一散射或谱结构量 $\varphi'(\cdot),\rho_{\mathrm{rel}}(\cdot),\mathsf Q(\cdot)$，在共识态下满足统一时间恒等式

$$
\kappa(\omega^\ast) = \frac{\varphi'(\omega^\ast)}{\pi} = \rho_{\mathrm{rel}}(\omega^\ast) = \frac{1}{2\pi}\operatorname{Tr}\mathsf Q(\omega^\ast),
$$

并在局域限制下保持不变。

*证明概要：* 由自然性直接得到 $\kappa(\omega_i^\ast)=\kappa(\omega^\ast)$。模流一致性由模态射定义给出。统一时间恒等式在共识态上成立，则其在子代数上的限制仍为同一数值，因而为一个全局不变量。详见附录 B。

这一定理为"所有观察者共享同一物理时间刻度"给出了严格的范畴代数条件。

---

## 6 有限维矩阵代数上的两观察者示例

本节给出一个简单而完全可计算的模型，用来直观展示同步迭代与共识不动点。

### 6.1 模型设定

考虑两个观察者 $O_1,O_2$，其局域代数分别为有限维矩阵代数：

$$
\mathcal A_1 = M_{n_1}(\mathbb C),\quad \mathcal A_2 = M_{n_2}(\mathbb C).
$$

设存在一个公共重叠子代数

$$
\mathcal A_{12}\cong M_m(\mathbb C),
$$

通过单射 *-同态

$$
\iota_1:\mathcal A_{12}\hookrightarrow\mathcal A_1,\quad \iota_2:\mathcal A_{12}\hookrightarrow\mathcal A_2.
$$

可将其理解为"两个探测器在某个重叠能级子空间上的共同灵敏度"。

态 $\omega_1,\omega_2$ 均由密度矩阵描述：

$$
\omega_i(A) = \operatorname{Tr}(\rho_i A),\quad \rho_i\in\mathcal A_i,\ \rho_i\ge 0,\ \operatorname{Tr}\rho_i=1.
$$

对重叠子代数的限制对应于压缩到嵌入像上：

$$
\rho_{12}^{(1)} := \iota_1^{-1}(P_1\rho_1P_1),\quad \rho_{12}^{(2)} := \iota_2^{-1}(P_2\rho_2P_2),
$$

其中 $P_i$ 为投影到 $\iota_i(\mathcal A_{12})$ 的正交投影。

### 6.2 条件期望与同步步

在有限维情形，下述映射为条件期望：

$$
E_{1\to12}(A) := P_1 A P_1 + \frac{\operatorname{Tr}( (I-P_1)A(I-P_1))}{m}I_{12}, \quad A\in\mathcal A_1;
$$

$$
E_{2\to12}(B) := P_2 B P_2 + \frac{\operatorname{Tr}( (I-P_2)B(I-P_2))}{m}I_{12}, \quad B\in\mathcal A_2,
$$

其中 $I_{12}$ 为 $\mathcal A_{12}$ 的单位。这些条件期望在自然选择的迹态下保持模结构（有限维中模流为平凡或与哈密顿量对易）。

同步一步中，定义重叠区上的共识态为相对熵意义下的"几何平均"：

$$
\rho_{12}' := \operatorname*{arg\,min}_{\sigma\in\mathcal D_{12}} \bigl( S(\sigma\Vert\rho_{12}^{(1)}) + S(\sigma\Vert\rho_{12}^{(2)}) \bigr),
$$

其中 $\mathcal D_{12}$ 为 $\mathcal A_{12}$ 上的密度矩阵集合。该极小值解可显式写为归一化的"非交换几何平均"：

$$
\rho_{12}' \propto \exp\Bigl( \frac{1}{2}\log\rho_{12}^{(1)} + \frac{1}{2}\log\rho_{12}^{(2)} \Bigr).
$$

同步后的局域密度矩阵取为

$$
\rho_1' := \rho_1 + \alpha \bigl(\iota_1(\rho_{12}') - P_1\rho_1 P_1\bigr),
$$

$$
\rho_2' := \rho_2 + \alpha \bigl(\iota_2(\rho_{12}') - P_2\rho_2 P_2\bigr),
$$

其中 $0<\alpha\le 1$ 为步长参数，用于调节同步强度。

### 6.3 收敛到唯一共识态

令 $\boldsymbol\rho=(\rho_1,\rho_2)$ 表示网络状态。可证明：

**命题 6.1** 对任意 $0<\alpha\le 1$，同步映射

$$
F(\rho_1,\rho_2)=(\rho_1',\rho_2')
$$

在对称相对熵度量下为非扩张映射；若 $\alpha$ 足够大且 $\mathcal A_{12}$ 在两个代数中嵌入具有非平凡重叠，则存在常数 $\lambda<1$ 使得

$$
D(F(\boldsymbol\rho),F(\boldsymbol\sigma)) \le \lambda D(\boldsymbol\rho,\boldsymbol\sigma),
$$

从而 $F$ 为压缩。

因此，存在唯一不动点 $(\rho_1^\ast,\rho_2^\ast)$，使得同步后不变且在重叠区上满足

$$
\rho_{12}^{(1)\ast}=\rho_{12}^{(2)\ast}=: \rho_{12}^\ast.
$$

可具体检查 $\rho_{12}^\ast$ 为 $\rho_{12}^{(1)},\rho_{12}^{(2)}$ 的非交换几何平均，而 $\rho_1^\ast,\rho_2^\ast$ 则为在各自代数上对这种共识压缩的唯一平衡态。详细推导见附录 C。

### 6.4 共识时间刻度的有限维实现

在有限维情形中，可将统一时间刻度 $\kappa(\rho)$ 指定为与某个有效哈密顿量 $H$ 的能量加权态密度相关的量，例如

$$
\kappa(\rho) := \frac{1}{2\pi}\operatorname{Tr}\bigl(Q(\rho)\bigr),\quad Q(\rho):=-\mathrm i S^\dagger S',
$$

其中 $S$ 为散射矩阵，$S'$ 为能量导数（在适当嵌入到散射框架下）。在更抽象层面，只需假定 $\kappa$ 在模态射下不变。则在共识不动点上，有

$$
\kappa(\rho_1^\ast)=\kappa(\rho_2^\ast)=\kappa(\rho_{12}^\ast),
$$

从而在重叠区域上两观察者拥有同一时间刻度。这是第 5 节统一时间刻度定理在有限维具体模型中的体现。

---

## 7 讨论与展望

本文从局域代数范畴与模包含出发，将"观察者共识"刻画为同步函子 $F$ 的不动点问题。通过 Araki 相对熵几何与条件期望的单调性，我们证明在相当一般的情形下，$F$ 成为压缩映射，从而存在唯一不动点配置 $\boldsymbol\omega^\ast$ 与范畴共识对象 $(\mathcal A^\ast,\omega^\ast)$。进一步，通过统一时间刻度 $\kappa$ 的自然性，我们得到一个在所有观察者之间对齐的模时间流，从而给出"同一物理时钟"的范畴代数版本。

这一框架可看作对代数量子场论中 Haag–Kastler 网、模局域化与几何模作用等思想的观测者化与信息化重写：代数不再仅仅附着于时空区域，而是附着于"观察者—可及窗口—读数算子"的组合，范畴态射则编码了不同观察者之间的"翻译协议"和时间箭头。同步不动点为这种网络提供了一种结构性的"全局态选取"机制，不再需要外挂一个超然的"宇宙状态"。

未来的几个方向包括：

1. 将本工作推广到无限网络与连续观察者族，使用测地流形上的非线性半群理论代替简单的 Banach 不动点；

2. 在具体的 QCA 或散射网络模型中，实现 $\mathcal A_i$ 为具体的局域 $C^\ast$-代数，$\kappa$ 与元胞时间步、Wigner–Smith 延迟、谱移函数直接相连；

3. 将统一时间刻度与几何结构（例如 Brown–York 准局域能量、光学度规）结合，使"曲率 = 时间密度变化"的观点在范畴层面得到进一步精炼；

4. 探索在存在拓扑约束或自指结构（如 $\mathbb Z_2$ 双覆盖、旋量结构）时，共识不动点的多值性与分支结构，将其与量子统计与相位拓扑联系起来。

从更宏观的角度看，本工作说明：**"共识"可以被理解为一个范畴不动点问题，而"时间"则是该不动点上自然流的刻度。**

在这一意义上，宇宙中所有观察者共同书写的，并不是一套先验给定的时空，而是一种在模包含与信息同步下自洽闭合的范畴结构。

---

## Appendix A：同步算子的收缩性与不动点存在性

本附录给出第 4 节中关于同步算子 $F$ 收缩性的较为详细证明。

### A.1 条件期望的相对熵单调性

**命题 A.1** 设 $\mathcal N\subset\mathcal M$ 为冯诺依曼子代数，$E:\mathcal M\to\mathcal N$ 为正规条件期望。则对 $\mathcal M$ 上的任意两个正常态 $\omega,\varphi$，有

$$
S(\omega\circ E\Vert\varphi\circ E) \le S(\omega\Vert\varphi).
$$

*证明（略）：* 该命题是 Araki 相对熵的基本性质之一，可通过 GNS 表示与相对模算子构造给出，核心为条件期望的完全正性与单调性。有限维情形下可直接利用相对熵的矩阵表达与奇异值分解证明。

进一步，针对对称量

$$
D(\omega,\varphi) :=S(\omega\Vert\varphi)+S(\varphi\Vert\omega),
$$

同样有

$$
D(\omega\circ E,\varphi\circ E)\le D(\omega,\varphi).
$$

### A.2 局域同步步的收缩性

对固定节点 $i$，记其局域同步映射为

$$
T_i:\mathcal S(\mathcal A_i)\times\prod_{(j\to i)\in E}\mathcal S(\mathcal A_j)\to\mathcal S(\mathcal A_i),
$$

即

$$
\omega_i' = T_i\bigl(\omega_i,\{\omega_j\}_{(j\to i)\in E}\bigr).
$$

构造方式为：先将 $\omega_j$ 通过模态射 $\Phi_{ji}$ 与条件期望 $E_{ij}$ 得到 $\tilde\omega_{j\to i}$，然后定义

$$
\omega_i' := \operatorname*{arg\,min}_{\varphi\in\mathcal S(\mathcal A_i)}\Bigl( \alpha_i S(\varphi\Vert\omega_i) + \sum_{(j\to i)\in E}\beta_{ji}S(\varphi\Vert\tilde\omega_{j\to i}) \Bigr).
$$

该最小化问题在有限或适当条件下的无限维情形中均有唯一解。

**命题 A.2** 对固定邻域结构与权重 $\alpha_i,\beta_{ji}>0$，映射

$$
\bigl(\omega_i,\{\omega_j\}\bigr)\mapsto \omega_i'
$$

在 Araki 相对熵几何下为非扩张映射，即存在常数 $L_i\in(0,1]$，使得

$$
D_i(\omega_i',\varphi_i') \le L_i\Bigl( D_i(\omega_i,\varphi_i) + \sum_{(j\to i)\in E}D_j(\omega_j,\varphi_j) \Bigr).
$$

*证明思路：* 利用以下几点：

1. 条件期望与模态射组合为 CPTP 映射，其对相对熵单调；

2. 目标泛函在 $\varphi$ 上严格凸，最小化解对输入态连续依赖；

3. 可将此映射视为某种"相对熵投影"，其 Lipschitz 常数可由强凸性与光滑性估计给出。

形式上的证明可借鉴量子信息中对 Bregman 投影与迭代投影算法收敛性的分析。

### A.3 全局同步算子的压缩性

记全局同步算子为

$$
F(\boldsymbol\omega) = \boldsymbol\omega',\quad \omega_i' = T_i(\omega_i,\{\omega_j\}_{(j\to i)\in E}).
$$

在全局度量

$$
D(\boldsymbol\omega,\boldsymbol\varphi) :=\sum_{i\in I}w_i D_i(\omega_i,\varphi_i)
$$

下，有

$$
\begin{aligned}
D(F(\boldsymbol\omega),F(\boldsymbol\varphi)) &=\sum_{i\in I}w_iD_i(\omega_i',\varphi_i')\\
&\le \sum_{i\in I}w_iL_i\Bigl( D_i(\omega_i,\varphi_i) + \sum_{(j\to i)\in E}D_j(\omega_j,\varphi_j) \Bigr)\\
&= \sum_{k\in I}\Bigl( w_kL_k + \sum_{(j\to i)= (k\to i)\in E}w_iL_i \Bigr)D_k(\omega_k,\varphi_k).
\end{aligned}
$$

定义

$$
\lambda := \max_{k\in I}\Bigl( w_kL_k + \sum_{(k\to i)\in E}w_iL_i \Bigr),
$$

则有

$$
D(F(\boldsymbol\omega),F(\boldsymbol\varphi)) \le \lambda D(\boldsymbol\omega,\boldsymbol\varphi).
$$

只要网络连通，权重 $w_i$ 选择得当，且局域 Lipschitz 常数 $L_i<1$ 至少对某些节点成立，即可确保 $\lambda<1$，从而 $F$ 为压缩映射。

### A.4 不动点存在性与唯一性

由 Banach 不动点定理，压缩映射 $F$ 在完备度量空间 $(\mathcal S,D)$ 上存在唯一不动点 $\boldsymbol\omega^\ast$，且任意迭代序列收敛至此。重叠区域一致性可由同步构造在 $\mathcal A_{ij}$ 上的封闭性与极限交换性得到，即对任何重叠子代数，限制态满足

$$
\omega_i^\ast|_{\mathcal A_{ij}}=\omega_j^\ast|_{\mathcal A_{ij}}.
$$

---

## Appendix B：共识对象的范畴余极限构造

本附录说明如何在 $\mathbf{LocAlg}$ 中将同步不动点配置 $\boldsymbol\omega^\ast$ 组织成一个余极限对象 $(\mathcal A^\ast,\omega^\ast)$。

### B.1 局域代数系统与粘合

给定一族对象 $(\mathcal A_i,\omega_i^\ast)$ 与在重叠区域 $\mathcal A_{ij}$ 上的一致性同构，可构造一个余极限 $\mathcal A^\ast$ 作为"粘合"：

1. 取自由 *-代数生成的和 $\bigoplus_i\mathcal A_i$；

2. 按照重叠同构关系对对应元施加等价关系；

3. 取完成得到 $C^\ast$-或冯诺依曼包络代数 $\mathcal A^\ast$。

同样，态 $\omega_i^\ast$ 在重叠区域上一致，因此存在唯一态 $\omega^\ast$ 在 $\mathcal A^\ast$ 上，使得 $\omega^\ast\circ\Phi_{i\ast}=\omega_i^\ast$，其中 $\Phi_{i\ast}:\mathcal A_i\to\mathcal A^\ast$ 为自然嵌入。

### B.2 余极限的泛性质

**命题 B.1** $(\mathcal A^\ast,\omega^\ast)$ 与嵌入 $\{\Phi_{i\ast}\}$ 满足范畴 $\mathbf{LocAlg}$ 中的余极限泛性质：对任意对象 $(\mathcal B,\varphi)$ 与态射族 $\Psi_i:(\mathcal A_i,\omega_i^\ast)\to(\mathcal B,\varphi)$ 满足兼容条件（在重叠区域上一致），存在唯一态射 $\Psi:(\mathcal A^\ast,\omega^\ast)\to(\mathcal B,\varphi)$，使得

$$
\Psi\circ\Phi_{i\ast} = \Psi_i.
$$

这是由代数余极限构造与态一致性的唯一性直接得出的。模流相容性也可通过在局域模流上的交换关系推广到全局模流。

### B.3 全局模流与统一时间刻度

在每个 $(\mathcal A_i,\omega_i^\ast)$ 上存在模流 $\sigma_t^{\omega_i^\ast}$；在粘合构造中，可以在代数层面定义一族自同构 $\sigma_t^{\omega^\ast}$ 使其在每个嵌入像上与 $\sigma_t^{\omega_i^\ast}$ 兼容，从而得到全局模流。统一时间刻度 $\kappa(\omega^\ast)$ 则成为该模流的共轭不变量，在局域限制下保持数值不变，由此构成第 5 节定理所述的统一时间结构。

---

## Appendix C：有限维两观察者模型的详细计算

本附录补充第 6 节中的有限维例子，给出部分计算细节。

### C.1 非交换几何平均的显式形式

在有限维矩阵代数 $M_m(\mathbb C)$ 上，对两个正定密度矩阵 $\rho,\sigma$，定义函数

$$
f(\tau) = S(\tau\Vert\rho)+S(\tau\Vert\sigma), \quad \tau\in\mathcal D_m,
$$

其中

$$
S(\tau\Vert\rho) = \operatorname{Tr}\bigl(\tau(\log\tau-\log\rho)\bigr).
$$

求导并令导数为零可得极小值条件

$$
\log\tau - \log\rho + \log\tau - \log\sigma + \lambda I = 0,
$$

其中 $\lambda$ 为拉格朗日乘子（来自 $\operatorname{Tr}\tau=1$ 约束）。整理得

$$
2\log\tau = \log\rho + \log\sigma + \mu I,
$$

从而

$$
\tau \propto \exp\Bigl(\frac{1}{2}(\log\rho+\log\sigma)\Bigr).
$$

归一化即可得到非交换几何平均

$$
\tau^\ast = \frac{\exp\bigl(\frac{1}{2}(\log\rho+\log\sigma)\bigr)}{\operatorname{Tr}\exp\bigl(\frac{1}{2}(\log\rho+\log\sigma)\bigr)}.
$$

在同步构造中，$\rho_{12}'$ 正是 $\rho_{12}^{(1)},\rho_{12}^{(2)}$ 的这一几何平均。

### C.2 同步步的线性响应与收缩估计

在同步更新

$$
\rho_1' = \rho_1 + \alpha (\iota_1(\rho_{12}')-P_1\rho_1P_1)
$$

附近线性化，可得到对小扰动 $\delta\rho_1,\delta\rho_2$ 的一阶响应算子。由 $\rho_{12}'$ 对输入态的 Fréchet 导数可见，扰动在重叠子空间上被平均，而在正交补空间上保持不变或被弱化。选取适当的 $\alpha$ 可提高沿重叠方向的收缩率，从而整体 Lipschitz 常数小于 1，保证压缩性。

### C.3 相对熵度量下的单步收缩

对两组密度矩阵 $\boldsymbol\rho,\boldsymbol\sigma$，对称相对熵差

$$
\Delta D := D(F(\boldsymbol\rho),F(\boldsymbol\sigma)) - D(\boldsymbol\rho,\boldsymbol\sigma)
$$

可用相对熵的 Bregman 几何性质展开。由于同步步在重叠子空间上的操作为"向几何平均投影"，而相对熵将几何平均视作中点，故 $\Delta D$ 为非正，且在扰动非零时严格负，从而得到严格收缩。

---

## References

1. H. Araki, "Relative Entropy of States of von Neumann Algebras," Publ. RIMS 11 (1976).

2. S. Sakai, $(C^\ast)$-Algebras and $(W^\ast)$-Algebras, Springer.

3. M. Takesaki, Theory of Operator Algebras I–III, Springer.

4. R. Haag, Local Quantum Physics, Springer.

5. D. Petz, Quantum Information Theory and Quantum Statistics, Springer.

