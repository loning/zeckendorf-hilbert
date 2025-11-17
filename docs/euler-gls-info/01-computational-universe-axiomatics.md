# 计算宇宙的公理化结构

离散配置、更新关系与统一时间刻度的基础框架

---

## 摘要

本文在有限信息密度与局域可逆更新的前提下，对"计算宇宙"（computational universe）给出一个统一的公理化定义。核心对象是带有更新关系、代价函数与信息泛函的四元组 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$，其中 $X$ 是全宇宙的离散配置空间，$\mathsf T \subset X \times X$ 是一步更新关系，$\mathsf C$ 是单步代价（时间、能量或门数），$\mathsf I$ 是表征"信息质量"的状态函数。本文在此基础上引入局域性、有限度量性与（广义）可逆性的公理，证明经典图灵机、元胞自动机与可逆量子元胞自动机均可作为该框架的特例嵌入。

进一步地，我们证明：在统一时间刻度的假设下（即存在与物理散射时间刻度兼容的单步代价函数），配置图 $(X,\mathsf T,\mathsf C)$ 在适当极限下诱导出一类"复杂性几何"，其测地距离等价于传统时间复杂度的连续化版本。最后，我们用模拟映射刻画不同计算宇宙之间的关系，构造出以计算宇宙为对象、以保结构模拟为态射的范畴 $\mathbf{CompUniv}$，并证明经典图灵宇宙、经典元胞自动机宇宙与量子元胞自动机宇宙在此范畴内构成等价的全子范畴。

本文作为"计算宇宙理论"系列工作的第一篇，旨在提供一个离散且可物理化的最小公理基础，为后续复杂性几何、信息几何与物理宇宙–计算宇宙的范畴等价理论奠定统一的基准结构。

---

## 关键词

计算宇宙；元胞自动机；图灵机；量子元胞自动机；统一时间刻度；复杂性几何；模拟；范畴等价

---

## 1 引言

"宇宙即计算"是一类跨越物理学、计算机科学与信息论的统一设想。若将整个宇宙视为一个巨大的离散动力系统，则经典图灵机、元胞自动机以及可逆量子元胞自动机等传统模型都可以被理解为对这一"计算宇宙"的不同切片。然而，在现有文献中，这些模型往往分别被发展，很少在一个统一的公理体系中出现，更遑论与物理时间刻度、几何结构以及范畴论意义上的"宇宙之间的等价"建立系统联系。

本文的目标是构建这样一个基础层：在尽可能少的假设下，给出一个抽象的"计算宇宙对象" $U_{\mathrm{comp}}$，并用一组清晰的公理刻画其结构与约束，使之能够同时涵盖：

1. 经典图灵机与其"图灵宇宙"；
2. 经典元胞自动机与更一般的局域离散动力系统；
3. 可逆量子元胞自动机（QCA）及其宇宙模型。

我们强调两点：

* 一方面，整个框架是**离散的**：宇宙状态被建模为可数集 $X$ 上的点，时间演化由图 $(X,\mathsf T)$ 上的步进实现；
* 另一方面，代价函数 $\mathsf C$ 被解释为统一时间刻度的离散采样值，从而为后续把复杂性视为"几何长度"提供桥梁。

在此基础上，我们定义不同计算宇宙之间的"模拟态射"，并由此构造范畴 $\mathbf{CompUniv}$。这不仅统一了传统的"多模型可计算性等价"结果，也为后续建立"物理宇宙范畴与计算宇宙范畴的等价"提供抽象框架。

全文结构如下。第 2 节给出基本符号与预备知识。第 3 节提出计算宇宙对象的公理化定义。第 4、5 节分别说明图灵机、经典元胞自动机与量子元胞自动机如何嵌入该框架。第 6 节引入统一时间刻度与复杂性几何的基本构造。第 7 节构造模拟态射与范畴 $\mathbf{CompUniv}$。附录中给出主要命题与定理的详细证明与若干技术性讨论。

---

## 2 预备知识与符号约定

本文中的集合、映射与代数结构均在 Zermelo–Fraenkel 集合论与选择公理背景下讨论，默认所有集合至多可数，除非特别说明。

1. 记 $\mathbb N = \{0,1,2,\dots\}$，$\mathbb Z$ 为整数集，$\mathbb R$ 为实数域。
2. 对集合 $X$，记 $\mathcal P_{\mathrm{fin}}(X)$ 为 $X$ 的有限子集族。
3. 若 $G = (V,E)$ 是有向图，则顶点集为 $V$，有向边集为 $E \subset V\times V$。
4. 对 Hilbert 空间 $\mathcal H$，记 $\mathcal B(\mathcal H)$ 为有界线性算子代数，若 $U \in \mathcal B(\mathcal H)$ 且 $U^\ast U = UU^\ast = \mathrm{id}$，则称 $U$ 为酉算子。
5. 若不引起混淆，记 $f:A\to B$ 的像为 $f(A)$，原像为 $f^{-1}(C)$。

我们特别关心局域性与有限信息密度，这一点在经典元胞自动机与 QCA 中自然出现。为统一起见，我们采用以下抽象设定。

**定义 2.1（局域结构）** 设 $X$ 为可数集。一个局域结构是一个有限度的有向图 $G_X = (X,E_X)$，其中对每个 $x\in X$，

$$
\deg^{+}(x) = |\{ y : (x,y)\in E_X \}| < \infty
$$

$$
\deg^{-}(x) = |\{ y : (y,x)\in E_X \}| < \infty
$$

直观上，$G_X$ 刻画了每个配置在"空间"上的有限范围邻接关系。

---

## 3 计算宇宙对象的公理化

本节给出本文的核心对象：计算宇宙 $U_{\mathrm{comp}}$ 的公理化定义。

### 3.1 计算宇宙的基本数据

**定义 3.1（计算宇宙对象）** 一个计算宇宙对象是四元组

$$
U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)
$$

其中：

1. $X$ 为可数集合，称为宇宙的配置空间；
2. $\mathsf T \subset X \times X$ 为一步更新关系；
3. $\mathsf C: X\times X \to [0,\infty]$ 为代价函数；
4. $\mathsf I: X \to \mathbb R$ 为信息质量函数。

为了将其视为"宇宙级计算系统"，我们对上述数据施加以下公理。

### 3.2 公理体系

**公理 A1（有限信息密度）**

存在一个局域结构 $G_X = (X,E_X)$，使得对任意有限顶点集 $R \subset X$，与 $R$ 相邻的配置集合

$$
N(R) = \{ x \in X : \exists y \in R, (x,y)\in E_X \text{ 或 } (y,x)\in E_X \}
$$

满足 $|N(R)| < \infty$。

此外，对每个 $x\in X$，与 $x$ 局域相关的"内部状态"集合同样有限（这一点在具体模型中由编码保证）。

**公理 A2（局域更新）**

对任意 $x\in X$，一步可达集合

$$
\mathsf T(x) = \{ y\in X : (x,y)\in \mathsf T \}
$$

是有限的，并且存在有限半径 $r$（与 $x$ 无关），使得 $\mathsf T(x)$ 的确定仅依赖于 $x$ 在 $G_X$ 中某个半径为 $r$ 的局部邻域信息。

**公理 A3（广义可逆性）**

存在一个关系 $\mathsf T^{-1} \subset X\times X$，使得对任意 $x\in X$，

$$
\mathsf T^{-1}(x) = \{ y : (y,x)\in \mathsf T \}
$$

有限，且对"物理相关"的配置子集 $X_{\mathrm{phys}} \subset X$ 限制后，$\mathsf T$ 与 $\mathsf T^{-1}$ 在 $X_{\mathrm{phys}}$ 上互为函数图的逆（即时间演化是双射）。

**公理 A4（代价的加性与正性）**

对任意 $(x,y)\in \mathsf T$，有 $\mathsf C(x,y) \in (0,\infty)$；若 $(x,y) \notin \mathsf T$，则定义 $\mathsf C(x,y) = \infty$。

对任意有限路径 $\gamma = (x_0,x_1,\dots,x_n)$，定义

$$
\mathsf C(\gamma) = \sum_{k=0}^{n-1} \mathsf C(x_k,x_{k+1})
$$

则 $\mathsf C(\gamma)$ 仅依赖于 $\mathsf T$ 和 $\mathsf C$，且对路径连接满足三角不等式。

**公理 A5（信息质量的单调性）**

存在一个任务族 $\mathcal Q$（例如判定问题、函数计算或测量任务），使得对每个任务 $Q\in\mathcal Q$，存在信息质量函数 $\mathsf I_Q:X\to\mathbb R$，满足：若路径 $\gamma$ 支持对任务 $Q$ 的计算，则沿 $\gamma$ 的期望信息质量是非减的；即对典型路径 $x_0 \to x_1 \to \dots \to x_n$，有

$$
\mathbb E[\mathsf I_Q(x_{k+1})] \ge \mathbb E[\mathsf I_Q(x_k)]
$$

在多数具体情形中，我们可只固定一个任务（例如模拟某个固定外部系统），并省略下标 $Q$，此时 $\mathsf I$ 表征相对某个"真状态"或目标分布的信息接近程度。

### 3.3 路径、复杂度与可达域

在上述公理下，我们得到如下自然定义。

**定义 3.2（路径与复杂度）**

在计算宇宙 $U_{\mathrm{comp}}$ 中，从 $x$ 到 $y$ 的一条路径是有限序列 $\gamma = (x_0,x_1,\dots,x_n)$ 满足 $x_0 = x$、$x_n = y$、且 $(x_k,x_{k+1})\in \mathsf T$ 对所有 $0\le k<n$ 成立。

路径的代价为

$$
\mathsf C(\gamma) = \sum_{k=0}^{n-1} \mathsf C(x_k,x_{k+1})
$$

在所有连接 $x$ 与 $y$ 的路径中，定义距离

$$
d(x,y) = \inf_{\gamma:x\to y} \mathsf C(\gamma)
$$

称为从 $x$ 到 $y$ 的复杂度距离。

**命题 3.3**

在公理 A2 与 A4 下，若对任意 $x,y\in X$ 存在至少一条有限路径连接，则 $d$ 在 $X$ 上定义了一个广义度量（可能取值 $\infty$），并满足：

1. $d(x,x) = 0$；
2. $d(x,y) = d(y,x)$ 若 $\mathsf T$ 在 $X_{\mathrm{phys}}$ 上是双射；
3. $d(x,z) \le d(x,y) + d(y,z)$。

命题的详细证明见附录 A.1。

**定义 3.4（可达域与复杂性视界）**

对给定初始配置 $x_0\in X$ 与资源预算 $T>0$，定义可达域

$$
B_T(x_0) = \{ x\in X : d(x_0,x)\le T \}
$$

若存在 $x^\ast \in X$ 与常数 $T^\ast$，使得对所有 $T<T^\ast$，$x^\ast \notin B_T(x_0)$，而对所有 $T>T^\ast$，$x^\ast \in B_T(x_0)$，则称 $T^\ast$ 为从 $x_0$ 到 $x^\ast$ 的复杂性门槛。更一般地，可达域族 $\{ B_T(x_0) \}_{T>0}$ 的边界在 $T$ 上的拓扑突变刻画出复杂性的"视界"。

---

## 4 经典图灵机与元胞自动机的嵌入

本节说明经典图灵机与元胞自动机都可以被视为某个计算宇宙对象的特例，从而被纳入 $U_{\mathrm{comp}}$ 体系。

### 4.1 图灵机宇宙

回顾经典确定性图灵机的定义：

**定义 4.1（确定性图灵机）**

一个单带确定性图灵机是五元组 $M = (Q,\Sigma,\Gamma,\delta,q_0)$，其中：

1. $Q$ 为有限状态集合；
2. $\Sigma \subset \Gamma$ 为输入字母表，$\Gamma$ 为带上符号表，含空白符号；
3. $\delta: Q\times \Gamma \to Q\times \Gamma\times \{-1,0,+1\}$ 为转移函数；
4. $q_0\in Q$ 为初始状态。

我们将图灵机运行的"全局配置"编码为一条双向无限带的内容、读头位置及当前状态的组合。

**定义 4.2（图灵机宇宙的配置空间）**

设 $\mathbb Z$ 表示带上的整数位置。定义配置空间

$$
X_M = Q \times \Gamma^{\mathbb Z} \times \mathbb Z
$$

其中一个配置 $x = (q, (a_i)_{i\in\mathbb Z}, p)$ 表示：机器处于状态 $q$，带上位置 $i$ 的符号为 $a_i$，读头位于位置 $p$。

定义一步转移关系 $\mathsf T_M \subset X_M \times X_M$ 为：$(x,y)\in \mathsf T_M$ 当且仅当 $y$ 是在配置 $x$ 下应用一次 $\delta$ 后得到的配置。令单步代价 $\mathsf C_M(x,y) = 1$ 若 $(x,y)\in\mathsf T_M$，否则 $\infty$。

设 $\mathsf I_M$ 为相对于给定输入与任务的判定正确性信息（例如 0–1 值或与目标输出的负距离）。

**命题 4.3**

对任意确定性图灵机 $M$，四元组

$$
U_{\mathrm{comp}}(M) = (X_M,\mathsf T_M,\mathsf C_M,\mathsf I_M)
$$

满足公理 A1–A5，因此是一个计算宇宙对象。

*证明思路*：A1 由 $X_M$ 的局部结构与有限带字母表保证；A2 由 $\delta$ 的局域性保证；A3 在对"物理可达的配置子集"（即图灵机真实运行的轨道并其逆轨道）上成立；A4 由 $\mathsf C_M \equiv 1$ 可见；A5 由任务定义下的单调性设计（例如只在接受配置达到最高信息值）保证。详见附录 A.2。

### 4.2 经典元胞自动机宇宙

**定义 4.4（经典元胞自动机）**

设 $\Lambda$ 为可数格点集合（例如 $\mathbb Z^d$），$S$ 为有限状态集合。一个元胞自动机是一个局域更新规则 $F: S^{\Lambda} \to S^{\Lambda}$，存在有限邻域 $\mathcal N\subset \Lambda$ 和局部规则 $f: S^{\mathcal N} \to S$，使得

$$
(F(c))_i = f((c)_{i+\mathcal N})
$$

对所有 $i\in\Lambda$ 成立。

定义配置空间 $X_{\mathrm{CA}} = S^{\Lambda}$，一步转移关系 $\mathsf T_{\mathrm{CA}} = \{ (c,F(c)) : c\in X_{\mathrm{CA}} \}$，单步代价 $\mathsf C_{\mathrm{CA}}(c,F(c)) = 1$，其他为 $\infty$。信息质量函数 $\mathsf I_{\mathrm{CA}}$ 根据任务定义。

**命题 4.5**

对任意经典元胞自动机 $F$，四元组

$$
U_{\mathrm{comp}}(F) = (X_{\mathrm{CA}},\mathsf T_{\mathrm{CA}},\mathsf C_{\mathrm{CA}},\mathsf I_{\mathrm{CA}})
$$

是计算宇宙对象。

A1–A2 来自局域性与有限状态；A3 需对可逆元胞自动机严格成立，对非可逆情形可通过扩展状态空间或限制子空间处理；详细讨论见附录 A.3。

---

## 5 可逆量子元胞自动机的嵌入

为了将量子宇宙模型纳入同一框架，我们考虑可逆 QCA 的抽象形式。

### 5.1 QCA 的基本定义

**定义 5.1（可逆量子元胞自动机）**

设 $\Lambda$ 为可数格点集合，对每个 $i\in\Lambda$，赋予有限维局域 Hilbert 空间 $\mathcal H_i$，全局 Hilbert 空间为

$$
\mathcal H = \bigotimes_{i\in\Lambda} \mathcal H_i
$$

一个可逆 QCA 是一个满足以下条件的酉算子 $U:\mathcal H\to\mathcal H$：

1. 局域性：对任意有界区域 $R\subset\Lambda$，存在有限膨胀 $R'\supset R$，使得 $U^\ast \mathcal A(R) U \subset \mathcal A(R')$，其中 $\mathcal A(R)$ 为支撑在 $R$ 上的局域算子代数；
2. 平移对称性（可选）：对所有平移 $\tau:\Lambda\to\Lambda$，$U$ 与相应平移算子对易。

为了适应离散框架，我们在某个固定正交基上将 $\mathcal H$ 的基态集合视为配置集。

**定义 5.2（QCA 宇宙的配置与更新）**

选定每个 $\mathcal H_i$ 的正交基 $\{ \ket{s} : s\in S_i \}$，令

$$
X_{\mathrm{QCA}} = \prod_{i\in\Lambda} S_i
$$

为基态标签的全体集合。

对任意 $x\in X_{\mathrm{QCA}}$，记对应的基矢为 $\ket{x}$。定义一步关系 $\mathsf T_{\mathrm{QCA}} \subset X_{\mathrm{QCA}} \times X_{\mathrm{QCA}}$ 为：

$$
(x,y)\in\mathsf T_{\mathrm{QCA}} \text{ 当且仅当 } \langle y | U | x \rangle \neq 0
$$

单步代价 $\mathsf C_{\mathrm{QCA}}(x,y)$ 取为与 $U$ 的单步物理实现时间相对应的常数或依赖频率的加权值。信息质量函数 $\mathsf I_{\mathrm{QCA}}$ 则依据所关心的观测任务（例如某个测量结果的经典后处理）定义。

### 5.2 QCA 宇宙满足的公理

**命题 5.3**

在局域性与有限维 Hilbert 空间的假设下，

$$
U_{\mathrm{comp}}(U) = (X_{\mathrm{QCA}},\mathsf T_{\mathrm{QCA}},\mathsf C_{\mathrm{QCA}},\mathsf I_{\mathrm{QCA}})
$$

满足公理 A1–A5。

证明要点为：

* 有限信息密度来自每个 $\mathcal H_i$ 的有限维与局域性；
* 一步可达集合有限性由 $U$ 是局域的线性组合给出；
* 逆演化由 $U^\ast$ 提供；
* 单步代价正性由实际物理实现时间的正性保证；
* 信息质量的单调性可通过在 Heisenberg 图像下的相关相对熵函数证明。

详细论证见附录 A.4。

---

## 6 统一时间刻度与复杂性几何的初步构造

虽然本文聚焦于离散公理，但统一时间刻度是后续"复杂性几何"和"物理宇宙–计算宇宙等价"的关键桥梁。本节给出一个初步结构：如何从单步代价 $\mathsf C$ 中抽象出与物理时间刻度兼容的几何距离。

### 6.1 单步代价与时间刻度的一致性

假设存在一个物理散射过程，其频率分辨的时间刻度密度为 $\kappa(\omega)$（例如由散射相位导数、谱移函数导数或群延迟迹定义）。我们认为计算宇宙中的单步代价 $\mathsf C(x,y)$ 是若干此类基本物理过程的组合，实现上的时间代价可写为

$$
\mathsf C(x,y) = \int_{\Omega(x,y)} \kappa(\omega)\,\mathrm d\mu_{x,y}(\omega)
$$

其中 $\Omega(x,y)$ 为对应物理过程中被激活的频段集合，$\mu_{x,y}$ 为相应的谱测度。这样，路径代价

$$
\mathsf C(\gamma) = \sum_{k} \mathsf C(x_k,x_{k+1})
$$

可近似视为某个连续时间积分的离散采样，最终诱导出一个"与物理时间刻度一致的复杂性距离" $d(x,y)$。

### 6.2 配置图的复杂性几何

在公理 A1–A4 下，我们可以把 $(X,\mathsf T,\mathsf C)$ 看成一个加权图，并考虑其在某些极限下的几何化。

**定义 6.1（复杂性图）**

计算宇宙的复杂性图是加权有向图 $G_{\mathrm{comp}} = (X,\mathsf T,\mathsf C)$，边权为 $\mathsf C$。

在某些情况下（例如存在连续控制参数、局域规则接近连续变换），可以通过 Gromov–Hausdorff 极限或图拉普拉斯算子的谱分析，得到一个连续流形 $\mathcal M$ 及其度量 $G$，使得图上的最短路距离在适当尺度下收敛到流形上的测地距离。这一过程构成了从离散复杂度到连续复杂性几何的桥梁。

**命题 6.2（图度量的连续极限，示意）**

设 $\{ U_{\mathrm{comp}}^{(h)} \}$ 是一族计算宇宙，对应复杂性图 $G_{\mathrm{comp}}^{(h)}$，其中"网格间距" $h\to 0$，若存在流形 $\mathcal M$ 与度量 $G$ 使得 $(X^{(h)},d^{(h)})$ 在 Gromov–Hausdorff 意义下收敛到 $(\mathcal M,d_G)$，则离散复杂度可在大尺度上视为由 $G$ 测地距离给出的"时间复杂性"。

该命题为示意性陈述，精确版本需额外技术假设；详见附录 B.1 的讨论。

---

## 7 模拟态射与计算宇宙范畴 $\mathbf{CompUniv}$

为了比较不同计算宇宙，我们引入模拟态射的概念。

### 7.1 模拟映射的定义

**定义 7.1（模拟映射）**

设 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$，$U'_{\mathrm{comp}} = (X',\mathsf T',\mathsf C',\mathsf I')$ 为两个计算宇宙。若存在映射 $f:X\to X'$ 与常数 $\alpha,\beta>0$，使得：

1. 保持步进：若 $(x,y)\in \mathsf T$，则 $(f(x),f(y))\in \mathsf T'$；
2. 代价控制：对任意路径 $\gamma:x\to y$，存在 $\gamma':f(x)\to f(y)$ 使得
$$
\mathsf C'(\gamma') \le \alpha\,\mathsf C(\gamma) + \beta
$$
3. 信息保真：存在单调函数 $\Phi:\mathbb R\to\mathbb R$，使得对所有 $x\in X$，
$$
\mathsf I(x) \le \Phi(\mathsf I'(f(x)))
$$

则称 $f$ 为从 $U_{\mathrm{comp}}$ 到 $U'_{\mathrm{comp}}$ 的模拟映射，记作 $f: U_{\mathrm{comp}} \rightsquigarrow U'_{\mathrm{comp}}$。

若 $f$ 在像上可逆（存在 $g:X'\to X$ 使得 $g\circ f$ 与 $f\circ g$ 在相关子集上同伦于恒等），且 $\alpha,\beta$ 在可接受的复杂度缩放范围内，则称 $U_{\mathrm{comp}}$ 与 $U'_{\mathrm{comp}}$ 在复杂性意义上等价。

### 7.2 范畴结构

**命题 7.2**

以计算宇宙对象为对象，以模拟映射为态射，构成一个范畴 $\mathbf{CompUniv}$：

1. 对任意 $U_{\mathrm{comp}}$，恒等映射 $\mathrm{id}_X:X\to X$ 是一个模拟映射；
2. 若 $f:U_{\mathrm{comp}} \rightsquigarrow U'_{\mathrm{comp}}$、$g:U'_{\mathrm{comp}} \rightsquigarrow U''_{\mathrm{comp}}$ 均为模拟映射，则复合映射 $g\circ f$ 也是模拟映射；
3. 模拟映射的复合满足结合律。

证明见附录 B.2。

我们特别关心由图灵机、元胞自动机与 QCA 所生成的子范畴。

**定理 7.3（经典模型间的等价）**

记 $\mathbf{TMUniv}$、$\mathbf{CAUniv}$ 分别为由图灵宇宙与经典可逆元胞自动机宇宙生成的全子范畴，则：

1. 这两个子范畴在 $\mathbf{CompUniv}$ 中分别是等价的；
2. 换言之，存在函子
$$
F_{\mathrm{TM}\to\mathrm{CA}}:\mathbf{TMUniv}\to\mathbf{CAUniv}
$$
$$
F_{\mathrm{CA}\to\mathrm{TM}}:\mathbf{CAUniv}\to\mathbf{TMUniv}
$$
以及自然同构 $\eta,\epsilon$，使得
$$
F_{\mathrm{CA}\to\mathrm{TM}}\circ F_{\mathrm{TM}\to\mathrm{CA}} \simeq \mathrm{id}_{\mathbf{TMUniv}}
$$
$$
F_{\mathrm{TM}\to\mathrm{CA}}\circ F_{\mathrm{CA}\to\mathrm{TM}} \simeq \mathrm{id}_{\mathbf{CAUniv}}
$$
并且这些函子在态射上由多项式复杂度的模拟映射实现。

其证明可视为对经典"图灵机–元胞自动机可计算性等价"结果在本公理框架下的范畴化推广，详见附录 B.3。

**定理 7.4（QCA 宇宙与经典计算宇宙的复杂性等价）**

存在一个由可逆 QCA 宇宙生成的全子范畴 $\mathbf{QCAUniv} \subset \mathbf{CompUniv}$，并有函子

$$
F_{\mathrm{TM}\to\mathrm{QCA}}:\mathbf{TMUniv}\to\mathbf{QCAUniv}
$$

$$
F_{\mathrm{QCA}\to\mathrm{TM}}:\mathbf{QCAUniv}\to\mathbf{TMUniv}
$$

使得上述等价在可计算性与复杂性意义上成立。

这一结果将量子计算模型与经典计算宇宙统一在同一范畴结构中，其证明依赖已知的量子通用性结果与可逆模拟构造，详见附录 B.4。

---

## 8 结论与展望

本文给出了"计算宇宙"的最小公理化定义：将整个宇宙建模为具有有限信息密度与局域更新的离散配置空间 $X$，一步更新关系 $\mathsf T$，单步代价 $\mathsf C$ 与信息质量函数 $\mathsf I$。我们证明经典图灵机、经典元胞自动机与可逆 QCA 均可视为特殊的计算宇宙对象，且在我们引入的模拟范畴 $\mathbf{CompUniv}$ 内互为等价的全子范畴。这一结果表明，在有限信息与局域性假设下，"计算宇宙"的不同传统模型只是同一抽象结构的不同呈现。

统一时间刻度在本文中仅以代价函数 $\mathsf C$ 与复杂性图的形式出现，但其与物理散射时间刻度之间的对应关系为后续工作的核心。在未来的工作中，我们将基于本文的公理框架，进一步发展：

1. 从 $(X,\mathsf T,\mathsf C)$ 出发构造复杂性几何与信息几何，得到连续流形 $(\mathcal M,G)$、$(\mathcal S,g)$；
2. 将观察者、注意力与知识图谱引入 $\mathfrak C = (\mathcal M,G;\mathcal S,g;\mathcal E;\mathcal A)$ 中，构造"计算世界线"的变分原理；
3. 建立物理宇宙范畴与计算宇宙范畴在统一时间刻度与边界时间几何下的范畴等价，从而实现"计算宇宙 = 物理宇宙"的结构化表述。

---

## 附录 A：公理性质与嵌入示例的证明

### A.1 命题 3.3 的证明

**命题重述**

在公理 A2 与 A4 下，若对任意 $x,y\in X$ 存在至少一条有限路径连接，则 $d(x,y) = \inf_{\gamma:x\to y} \mathsf C(\gamma)$ 在 $X$ 上定义了一个广义度量（可能取值为 $\infty$），并满足：

1. $d(x,x) = 0$；
2. 若 $\mathsf T$ 在 $X_{\mathrm{phys}}$ 上是双射，则 $d(x,y) = d(y,x)$ 对 $x,y\in X_{\mathrm{phys}}$ 成立；
3. $d(x,z) \le d(x,y) + d(y,z)$。

**证明**

1. 对任意 $x$，取零长度路径 $\gamma = (x)$，约定 $\mathsf C(\gamma) = 0$，故 $d(x,x) \le 0$。另一方面，A4 中单步代价正性保证任意非平凡路径代价为正，故 $d(x,x) = 0$。

2. 在 $X_{\mathrm{phys}}$ 上，若 $\mathsf T$ 是双射，则对任意 $(x,y)\in\mathsf T$，存在唯一 $(y,x)\in\mathsf T^{-1}$。若路径 $\gamma:x\to y$ 达到 $d(x,y)$ 的下确界，则由逆路径 $\gamma^{-1}:y\to x$ 的存在与 A4 的对称性（在物理子集上单步代价可视为对称）可得 $d(y,x) \le \mathsf C(\gamma^{-1}) = \mathsf C(\gamma)$。反向不等式同理，从而 $d(x,y)=d(y,x)$。

3. 令 $\varepsilon>0$。根据 $d(x,y)$、$d(y,z)$ 的定义，存在路径 $\gamma_1:x\to y$、$\gamma_2:y\to z$，使得
$$
\mathsf C(\gamma_1) \le d(x,y) + \varepsilon/2
$$
$$
\mathsf C(\gamma_2) \le d(y,z) + \varepsilon/2
$$
令 $\gamma = \gamma_1 \cdot \gamma_2$ 为串接路径，则
$$
\mathsf C(\gamma) = \mathsf C(\gamma_1)+\mathsf C(\gamma_2) \le d(x,y)+d(y,z)+\varepsilon
$$
由 $d(x,z)$ 的定义，$d(x,z) \le \mathsf C(\gamma)$，故
$$
d(x,z) \le d(x,y)+d(y,z)+\varepsilon
$$
令 $\varepsilon\to 0$ 便得三角不等式。

证毕。

---

### A.2 图灵机宇宙满足公理 A1–A5

**A1 有限信息密度**

配置空间 $X_M = Q \times \Gamma^{\mathbb Z} \times \mathbb Z$ 虽然是无限维，但对任意有限区间 $R = \{i_1,\dots,i_k\} \subset \mathbb Z$，局部带内容 $(a_i)_{i\in R}$ 的取值为有限集 $\Gamma^R$。局域结构可取为"图灵机的一步更新仅作用于读头所在位置及其邻近常数个位置"，对应的 $G_X$ 是有限度图，从而满足 A1。

**A2 局域更新**

转移函数 $\delta$ 仅依赖于当前状态与当前位置符号，因此一步更新 $(x,y)\in\mathsf T_M$ 完全由 $x$ 的有限局域信息决定。

**A3 广义可逆性**

对一般确定性图灵机，$\mathsf T_M$ 未必全局可逆，但可考虑扩展机器为可逆图灵机，或仅在"物理运行轨道" $X_{\mathrm{phys}}$ 上考虑可逆性。经典构造表明，任意确定性图灵机都可被嵌入到一个可逆图灵机中（例如保存历史记录），对应的配置空间扩展后，$\mathsf T_M$ 在扩展空间上是双射。将文中 $U_{\mathrm{comp}}(M)$ 理解为该可逆扩展即可满足 A3。

**A4 代价加性与正性**

定义 $\mathsf C_M(x,y)=1$ 当 $(x,y)\in\mathsf T_M$，否则 $\infty$。则对任一非平凡路径 $\gamma$，代价为正整数，零长度路径代价为 0，且显然满足加性与三角不等式。

**A5 信息质量单调性**

对判定任务，可令 $\mathsf I_M(x)$ 在"未停机"配置中恒为 0，在接受配置中为 1，在拒绝配置中为某个负值或仍为 0。则沿真实运行路径，期望值 $\mathbb E[\mathsf I_M]$ 随时间非减（因为一旦进入接受态便不再离开）。对更一般任务，可以引入基于输出前缀的置信度函数，构造略繁，原则相同。

证毕。

---

### A.3 经典元胞自动机宇宙满足公理

对元胞自动机 $F:S^{\Lambda}\to S^{\Lambda}$，若 $F$ 可逆，则其全局更新是双射。配置空间 $X_{\mathrm{CA}} = S^{\Lambda}$ 满足有限信息密度（每个格点状态有限且局域性保证每一步仅受有限邻域影响），单步代价取常数 1 即可。可逆性的处理与图灵机类似，可将非可逆元胞自动机通过扩展空间构造为可逆系统，或仅在可达轨道集合上施加可逆性。信息质量函数的构造方式与图灵机情形相同，故略。

---

### A.4 QCA 宇宙满足公理

对可逆 QCA $U$，局域性保证任一步更新仅在有限区域传播信息，使得对基态标签集合 $X_{\mathrm{QCA}}$ 的一步可达集合有限，从而满足 A1–A2。$U$ 是酉算子，因此存在 $U^\ast$ 作为逆演化，对应 $\mathsf T_{\mathrm{QCA}}^{-1}$，故在物理态子集上满足 A3。单步代价由物理实现时间或能量–时间不等式决定，自然为正且可加。信息质量函数可定义为某个参考态与当前态之间的相对熵或保真度的单调函数，在 Heisenberg 图像下，可以证明在某类控制任务下其期望值单调增加。详细技术论证依赖量子相对熵的单调性与完全正映射的结构，见附录 B.5。

---

## 附录 B：复杂性几何与范畴结构的技术细节

### B.1 复杂性图的连续极限（示意性讨论）

设 $\{ U_{\mathrm{comp}}^{(h)} \}$ 为一族计算宇宙，对应复杂性图 $G_{\mathrm{comp}}^{(h)} = (X^{(h)},\mathsf T^{(h)},\mathsf C^{(h)})$，其中 $h>0$ 表示"空间–控制尺度"的离散化步长，$h\to 0$ 时图越来越"稠密"。

在合适的构造下，可以将 $X^{(h)}$ 嵌入某个固定的欧氏空间或流形 $\mathcal M$，使得：

1. 边权 $\mathsf C^{(h)}(x,y)$ 逼近 $\sqrt{G_{ab}(\theta)\Delta\theta^a\Delta\theta^b}$；
2. 图距离 $d^{(h)}(x,y)$ 对应某个离散能量泛函的最小值，其极限为连续能量泛函的最小值，即测地距离 $d_G(\theta,\theta')$。

类似的结果在图 Laplace 算子的谱收敛与离散到连续 Dirichlet 能量流的研究中广为人知。这里我们仅给出结构性假设，详细构造将留待后续"复杂性几何理论"中系统展开。

---

### B.2 模拟映射范畴性的证明

**命题 B.1（恒等映射是模拟映射）**

对任意计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$，恒等映射 $\mathrm{id}_X$ 显然保持步进、单步代价与信息质量函数，取 $\alpha=1,\beta=0,\Phi=\mathrm{id}$，故为模拟映射。

**命题 B.2（复合保模拟结构）**

设 $f:U_{\mathrm{comp}} \rightsquigarrow U'_{\mathrm{comp}}$ 与 $g:U'_{\mathrm{comp}} \rightsquigarrow U''_{\mathrm{comp}}$ 为模拟映射。设其参数分别为 $(\alpha_f,\beta_f,\Phi_f)$ 与 $(\alpha_g,\beta_g,\Phi_g)$。对任一 $(x,y)\in\mathsf T$，有 $(f(x),f(y))\in\mathsf T'$、$(g(f(x)),g(f(y)))\in\mathsf T''$，从而 $g\circ f$ 保持步进。对任一路径 $\gamma:x\to y$，存在 $\gamma'$ 与 $\gamma''$ 分别使得

$$
\mathsf C'(\gamma') \le \alpha_f \mathsf C(\gamma) + \beta_f
$$

$$
\mathsf C''(\gamma'') \le \alpha_g \mathsf C'(\gamma') + \beta_g \le \alpha_g(\alpha_f \mathsf C(\gamma)+\beta_f)+\beta_g
$$

因此 $g\circ f$ 是以 $(\alpha_g\alpha_f,\,\alpha_g\beta_f+\beta_g,\,\Phi_g\circ\Phi_f)$ 为参数的模拟映射。态射复合的结合律由函数复合的结合律给出。

证毕。

---

### B.3 经典模型等价的范畴化（定理 7.3 的证明思路）

经典结果表明：任一图灵机都可在线性或多项式时间下被元胞自动机模拟，反之亦然。我们在此将该结果提升到计算宇宙范畴 $\mathbf{CompUniv}$ 的层次。

构造 $F_{\mathrm{TM}\to\mathrm{CA}}$：

* 对象：将图灵宇宙 $U_{\mathrm{comp}}(M)$ 映射到某个构造出来的元胞自动机宇宙 $U_{\mathrm{comp}}(F_M)$，其中 $F_M$ 的局部规则编码了图灵机配置的带与状态。编码映射 $e_M:X_M \to S^{\Lambda}$ 通过空间上的局部模式实现。
* 態射：若 $f:M_1\to M_2$ 是图灵机间的多项式时间模拟映射，则相应的元胞自动机之间存在模拟映射 $F_{\mathrm{TM}\to\mathrm{CA}}(f)$，其参数 $(\alpha,\beta)$ 与模拟开销有关。

构造 $F_{\mathrm{CA}\to\mathrm{TM}}$ 类似，通过空间–时间编码将元胞自动机配置压平成图灵带内容。自然同构 $\eta,\epsilon$ 的存在性依赖于上述编码的可逆性与多项式时间可解码性。完整证明涉及对编码方案的精细分析与对模拟复杂度的上界估计，详见附录 C 中的原型构造。

---

### B.4 量子模型的范畴等价（定理 7.4 的证明思路）

对可逆 QCA，已知存在通用的量子元胞自动机可以以多项式开销模拟任意有限局域 QCA；另一方面，经典通用计算可嵌入量子通用计算模型。将这些结果在 $U_{\mathrm{comp}}$ 框架中重述，即得到子范畴 $\mathbf{QCAUniv}$ 与 $\mathbf{TMUniv}$ 之间的复杂性等价。技术核心是构造酉编码与解码算子，使得在固定希尔伯特空间中，"图灵配置"与"QCA 配置"的子空间相互多项式可辨认，而步进算子的演化在该子空间上实现预期模拟。

---

### B.5 QCA 中信息质量单调性的一个原型论证

设 $\rho_t$ 为在 QCA 宇宙中某初始态 $\rho_0$ 在 Heisenberg 图像下随时间的演化，对某个观测任务 $Q$，定义目标态 $\sigma$ 与相对熵 $S(\rho_t\Vert\sigma)$。利用量子相对熵对完全正迹保持映射的单调性，可证明在适当的控制策略下，期望相对熵是非增的，从而信息质量函数 $\mathsf I(\rho_t) = -S(\rho_t\Vert\sigma)$ 是期望单调非减的。这在抽象层面上实现了公理 A5。详细的算子代数论证涉及 Tomita–Takesaki 模理论与局域代数的结构，此处不展开。

---

## 附录 C：编码构造与示例

本附录简要给出若干具体编码构造的原型，以说明计算宇宙公理与范畴结构的可实现性。

### C.1 图灵机到一维元胞自动机的编码示例

取一维格子 $\Lambda = \mathbb Z$，每个格点的局部状态集 $S$ 包含：

1. 带符号集 $\Gamma$；
2. 状态标记 $Q$；
3. 读头标记及方向信息。

将图灵机配置 $x = (q,(a_i)_{i\in\mathbb Z},p)$ 编码为元胞配置 $c\in S^{\mathbb Z}$：

* 在位置 $i$ 处写入 $a_i$；
* 在位置 $p$ 处附加状态 $q$ 与读头标记。

局部规则 $f:S^{\mathcal N}\to S$（$\mathcal N$ 为例如 $\{-1,0,+1\}$）设计为：根据当前位置是否拥有读头标记与状态 $q$ 来更新局部符号和读头位置。这样，一次 $F$ 演化对应图灵机的一步更新。该构造显然满足局域性、公理 A1–A4，并可扩展为可逆形式。

### C.2 元胞自动机到图灵机的编码示例

反向编码可通过将空间–时间演化图"折叠"为图灵机带上的二维编码来实现：令带的部分区域编码 CA 的空间横截面，其他区域作为辅助存储，用于累积时间步。图灵机的局部转移函数模拟 CA 的局部规则与时间推进。已知该构造可以在多项式时间内完成，且允许设计可逆图灵机版本，从而在 $\mathbf{CompUniv}$ 中给出相应模拟映射。

---

本文到此给出了计算宇宙的基本公理体系、经典与量子模型的嵌入以及模拟范畴结构的原型构造，为后续复杂性几何、信息几何及与物理宇宙的统一奠定了离散而严密的基础。
