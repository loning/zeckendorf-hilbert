# 宇宙作为量子离散元胞自动机的公理化刻画

## Abstract

在量子元胞自动机、准局域 $C^\ast$ 代数与因果集合的框架下，构造一个"宇宙 = 单一量子离散元胞自动机"的公理系统。具体地，以可数连通图 $\Lambda$ 作为离散空间；以有限维局域 Hilbert 空间 $\mathcal H_{\rm cell}$ 及其无限张量积上的准局域代数 $\mathcal A$ 描述局域量子自由度；以具有有限传播半径的 $*$ 自同构 $\alpha:\mathcal A\to\mathcal A$ 及其幺正实现 $U$ 描述离散时间演化；以初始宇宙态 $\omega_0$ 描述 $n=0$ 时刻的宇宙状态。证明在这些公理下，事件集合 $E=\Lambda\times\mathbb Z$ 上自然诱导的关系构成一个局域有限的偏序，从而得到一个离散因果集合，其局域有限性与量子元胞自动机的有限传播半径条件严格对应，形成与因果集理论中"局域有限偏序"的结构对齐。进一步定义"宇宙 QCA 对象"$\mathfrak U_{\rm QCA}=(\Lambda,\mathcal H_{\rm cell},\mathcal A,\alpha,\omega_0)$，给出"QCA 局域性 $\Longleftrightarrow$ 因果偏序的局域有限性"的等价定理，并在单粒子极限下构造一维 Dirac 型 QCA，示范如何在合适的缩放极限中得到连续狄拉克方程。最后讨论观测、熵与时间箭头在该框架中的表达，以及与因果集量子引力与量子场论离散化方案之间的关系。

## Keywords

量子元胞自动机；准局域 $C^\ast$ 代数；离散宇宙模型；因果集合；离散时间动力学；狄拉克方程的格点实现

---

## Introduction & Historical Context

量子元胞自动机（quantum cellular automata, QCA）可以被视为"在无限量子晶格上的离散时间、局域幺正动力学"，其代表性公理化出现在 Schumacher–Werner 对可逆 QCA 的工作中：将 QCA 定义为准局域代数上的平移不变 $*$ 自同构，具有严格有限的传播半径，从而保证每一步演化仅在有限邻域内传播支撑。随后 Arrighi、Farrelly 等对 QCA 的结构定理、可计算性、量子模拟与连续极限进行了系统综述，展示了 QCA 作为离散化量子场论与拓扑相模拟工具的广泛适用性。

另一方面，以 Sorkin、Surya 为代表的因果集（causal set）方案提出：时空本体可以被替换为一个局域有限的偏序集合，其偏序编码因果结构，局域有限性编码离散性，满足"order + number $\sim$ geometry"的纲领。在该方案中，因果偏序与局域有限性共同刻画了一个离散的"原始时空"，连续洛伦兹流形仅是其某种极限插值。

现有关于 QCA 的研究主要将其视作"模拟工具"或"离散化方案"：用来近似给定的连续量子场或凝聚态系统，并在适当极限下收敛回连续理论。本文选择反向视角：不将 QCA 作为连续宇宙的数值近似，而是将"宇宙本体"本身定义为一个满足若干公理的 QCA 对象；因果结构与"时空"从该对象的局域性与时间迭代中导出，而非预先给定。

更具体地，本文的核心问题是：

1. 在 QCA 语境下，如何定义"宇宙"这一整体对象，使其同时包含空间、局域自由度、动力学与初始态？

2. 能否从 QCA 的局域性与图结构出发，在事件集合上导出一个局域有限的因果偏序，从而与因果集理论的基本结构对齐？

3. 在该公理系统中，如何抽象观测、熵与时间箭头，并在适当极限下恢复连续的 relativistic 场方程，如狄拉克方程？

围绕这些问题，本文构造宇宙 QCA 对象 $\mathfrak U_{\rm QCA}$，证明其诱导的事件集合 $(E,\preceq)$ 为局域有限偏序，并给出 Dirac 型 QCA 的连续极限构造，展示在单粒子扇区下如何得到标准狄拉克方程的格点版本及其极限。

---

## Model & Assumptions

本节给出本文使用的基本数学结构与公理假设，包括离散空间、局域 Hilbert 空间、准局域 $C^\ast$ 代数以及 QCA 的定义，并在此基础上定义"宇宙 QCA 对象"。

### 离散空间与图结构

令 $\Lambda$ 为可数集合，作为"格点集合"或"离散空间"。假设 $\Lambda$ 携带一张无向连通图结构，边集记为 $E_\Lambda\subset\Lambda\times\Lambda$，满足

1. $(x,y)\in E_\Lambda\Rightarrow (y,x)\in E_\Lambda$；

2. 不存在自环 $(x,x)\in E_\Lambda$。

在此基础上定义图距离 $\operatorname{dist}:\Lambda\times\Lambda\to\mathbb N\cup\{0\}$ 为连接 $x$ 与 $y$ 的最短路径边数（若无路径则为 $+\infty$）。连通性假设保证任意 $x,y\in\Lambda$ 间距离有限。

对任意 $R\in\mathbb N$ 与 $x\in\Lambda$，定义闭球

$$
B_R(x):=\{y\in\Lambda:\operatorname{dist}(x,y)\le R\}
$$

。

假设每个 $B_R(x)$ 为有限集。该假设在标准晶格 $\mathbb Z^d$ 上自动成立。

当 $\Lambda=\mathbb Z^d$ 时，定义平移作用 $\tau_a:\Lambda\to\Lambda$ 为 $\tau_a(x):=x+a$，其中 $a\in\mathbb Z^d$。后文在讨论空间齐次性时将使用这一结构。

### 局域 Hilbert 空间与准局域 $C^\ast$ 代数

对每个格点 $x\in\Lambda$，关联一个有限维 Hilbert 空间 $\mathcal H_x$，并假设存在一个固定的有限维 Hilbert 空间 $\mathcal H_{\rm cell}$ 使得

$$
\mathcal H_x\simeq\mathcal H_{\rm cell}\simeq\mathbb C^d
$$

对所有 $x\in\Lambda$ 成立，其中 $d\in\mathbb N$ 为元胞的局域自由度维数。

对任意有限子集 $F\Subset\Lambda$，定义有限体积 Hilbert 空间

$$
\mathcal H_F:=\bigotimes_{x\in F}\mathcal H_x,
$$

对应的有界算子代数为

$$
\mathcal A_F:=\mathcal B(\mathcal H_F)
$$

。

若 $F\subset G\Subset\Lambda$，则有自然嵌入

$$
\iota_{F,G}:\mathcal A_F\hookrightarrow\mathcal A_G,\quad A\mapsto A\otimes\mathbf 1_{G\setminus F},
$$

其中 $\mathbf 1_{G\setminus F}$ 为 $\bigotimes_{x\in G\setminus F}\mathcal H_x$ 上恒等算子。

令

$$
\mathcal A_{\rm loc}:=\bigcup_{F\Subset\Lambda}\mathcal A_F,
$$

定义准局域 $C^\ast$ 代数为

$$
\mathcal A:=\overline{\mathcal A_{\rm loc}}^{|\cdot|},
$$

其中 $|\cdot|$ 为算子范数。元素 $A\in\mathcal A_{\rm loc}$ 的支撑 $\operatorname{supp}(A)\subset\Lambda$ 定义为最小的有限集合 $F$ 使得 $A\in\mathcal A_F$。对一般 $A\in\mathcal A$，支撑可定义为所有逼近 $A$ 的局域算子支撑的闭包。

该构造与量子自旋系与量子格点系统的标准准局域代数形式论一致。

### 态与 GNS 表象

在 $C^\ast$ 代数 $\mathcal A$ 上，一个态是正的、归一的线性泛函

$$
\omega:\mathcal A\to\mathbb C,\quad \omega(A^\ast A)\ge 0,\ \omega(\mathbf 1)=1
$$

。

物理上，$\omega(A)$ 给出可观测量 $A$ 的期望值。

由 GNS 构造可知，对任意态 $\omega$，存在三元组 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$，其中 $\pi_\omega:\mathcal A\to\mathcal B(\mathcal H_\omega)$ 是 $*$ 表象，$\Omega_\omega\in\mathcal H_\omega$ 是循环向量，使得

$$
\omega(A)=\langle\Omega_\omega,\pi_\omega(A)\Omega_\omega\rangle,\quad A\in\mathcal A,
$$

且集合 $\{\pi_\omega(A)\Omega_\omega:A\in\mathcal A\}$ 在 $\mathcal H_\omega$ 中稠密。

### QCA 的 Heisenberg 图像定义

采用 Schumacher–Werner 与后续工作的代数化定义，将 QCA 视为准局域代数上的 $*$ 自同构，具有有限传播半径并与平移作用对易。

**定义 2.1（量子元胞自动机）** 设 $R\in\mathbb N$。映射 $\alpha:\mathcal A\to\mathcal A$ 称为半径至多为 $R$ 的量子元胞自动机，若满足：

1. $\alpha$ 是 $C^\ast$ 代数的 $*$ 自同构，即对任意 $A,B\in\mathcal A$ 与 $\lambda\in\mathbb C$ 有

   $$
   \alpha(AB)=\alpha(A)\alpha(B),\quad \alpha(A^\ast)=\alpha(A)^\ast,\quad \alpha(\mathbf 1)=\mathbf 1,
   $$

   且 $\alpha$ 为双射与连续映射。

2. 局域性：对任意有限 $F\Subset\Lambda$ 与任意 $A_F\in\mathcal A_F$，存在有限集合 $G\subset\Lambda$ 使得 $\alpha(A_F)\in\mathcal A_G$，并满足

   $$
   G\subset B_R(F):=\bigcup_{x\in F}B_R(x)
   $$

   。

3. 若 $\Lambda$ 带平移作用 $\tau_a$，则存在相应平移自同构 $\theta_a:\mathcal A\to\mathcal A$，对所有 $a$ 与 $A\in\mathcal A$ 有

   $$
   \alpha\circ\theta_a=\theta_a\circ\alpha
   $$

   。

若存在某个有限 $R$ 使上述条件成立，则称 $\alpha$ 为局域 QCA。

由 $\alpha$ 可以定义整数次迭代

$$
\alpha^n:=\underbrace{\alpha\circ\cdots\circ\alpha}_{n\text{ 次}},\quad n\in\mathbb Z,
$$

其中 $\alpha^0=\mathrm{id}$，$\alpha^{-n}:=(\alpha^{-1})^n$。

### Schrödinger 图像与幺正实现

在 Schrödinger 图像中，态随时间演化。给定 QCA $\alpha$，对任意态 $\omega$ 定义第 $n$ 步后的态为

$$
\omega_n:=\omega\circ\alpha^{-n},\quad n\in\mathbb Z
$$

。

在合适的 GNS 表象中，QCA 可以由幺正算子实现。设 $\omega$ 为忠实且 $\alpha$ 不变的态，即 $\omega\circ\alpha=\omega$，且 $\omega(A^\ast A)=0\Rightarrow A=0$。则在 GNS 表象 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$ 中存在唯一幺正算子 $U:\mathcal H_\omega\to\mathcal H_\omega$，使得

$$
\pi_\omega(\alpha(A))=U\pi_\omega(A)U^\dagger,\quad A\in\mathcal A,
$$

且 $U\Omega_\omega=\Omega_\omega$。该结果是 GNS 形式论应用的标准结论，证明见附录 B。

在具体模型中，常直接在给定 Hilbert 空间 $\mathcal H$ 上指定幺正算子 $U$，令 $\alpha(A):=U^\dagger A U$，然后验证其满足局域性与平移对称性条件。

### 宇宙 QCA 对象

在上述结构上定义"宇宙 QCA 对象"，将空间、局域自由度、动力学与初始态汇总为一个五元组。

**定义 2.2（宇宙 QCA 对象）** 一组数据

$$
\mathfrak U_{\rm QCA}=(\Lambda,\mathcal H_{\rm cell},\mathcal A,\alpha,\omega_0)
$$

称为宇宙 QCA 对象，若满足：

1. $\Lambda$ 为可数无限连通图的顶点集合，带图距离 $\operatorname{dist}$，且对任意 $x\in\Lambda,R\in\mathbb N$，球 $B_R(x)$ 有限。

2. $\mathcal H_x\simeq\mathcal H_{\rm cell}$ 为有限维 Hilbert 空间，$\mathcal A$ 是其准局域 $C^\ast$ 代数。

3. $\alpha:\mathcal A\to\mathcal A$ 为某个有限半径 $R$ 的 QCA。

4. 若 $\Lambda$ 带平移作用，则 $\alpha$ 与相应平移自同构对易。

5. $\omega_0:\mathcal A\to\mathbb C$ 为归一态，称为初始宇宙态；对 $n\in\mathbb Z$ 定义

   $$
   \omega_n:=\omega_0\circ\alpha^{-n}
   $$

   。

在该定义中，$\Lambda$ 与 $\mathcal H_{\rm cell}$ 固定了"宇宙的离散空间与局域自由度类型"，$\alpha$ 固定了"动力学规律"，$\omega_0$ 固定了"初始条件"。

---

## Main Results (Theorems and alignments)

本节给出主要结果：从宇宙 QCA 对象导出的因果结构、其局域有限性与 QCA 局域性的等价刻画，以及 Dirac 型 QCA 的连续极限。

### 事件集合与因果可达关系

在宇宙 QCA 对象中，自然的事件集合为

$$
E:=\Lambda\times\mathbb Z,
$$

其中 $(x,n)$ 表示时间步 $n$ 时格点 $x$ 处的事件。对 $e=(x,n)\in E$，记空间坐标为 $\operatorname{sp}(e)=x$，时间为 $\operatorname{tm}(e)=n$。

QCA 的有限传播半径决定"离散光锥"。设 $\alpha$ 的传播半径为 $R$。对任意 $n<m$ 与支撑在单点 $\{y\}$ 上的局域算子 $B_y$，由局域性有

$$
\operatorname{supp}\bigl(\alpha^{m-n}(B_y)\bigr)\subset B_{R(m-n)}(y)
$$

。

定义几何关系

$$
(x,n)\leq_{\rm geo}(y,m)\iff m\ge n,\ \operatorname{dist}(x,y)\le R(m-n)
$$

。

为了获得因果关系，需要将统计相关性与几何光锥联系起来。定义

**定义 3.1（因果可达关系）** 对 $(x,n),(y,m)\in E$，称

$$
(x,n)\preceq(y,m)
$$

若满足：

1. $m\ge n$；

2. 存在支撑包含 $\{x\}$ 的局域算子 $A_x\in\mathcal A_{\{x\}}$，以及 $B_y\in\mathcal A_{\{y\}}$，以及某个态 $\omega$，使得

   $$
   \omega\bigl(\alpha^n(A_x)\alpha^m(B_y)\bigr)\neq\omega\bigl(\alpha^n(A_x)\bigr)\omega\bigl(\alpha^m(B_y)\bigr)
   $$

   。

即时间 $n$ 在 $x$ 处的局域扰动可以在 $m$ 时刻于 $y$ 处产生统计影响。

### 定理 1：QCA 因果结构为局域有限偏序

**定理 3.2（偏序与局域有限性）** 在任意宇宙 QCA 对象 $\mathfrak U_{\rm QCA}$ 中，由定义 3.1 诱导的关系 $\preceq$ 与几何关系 $\leq_{\rm geo}$ 等价，即

$$
(x,n)\preceq(y,m)\iff (x,n)\leq_{\rm geo}(y,m)
$$

。

从而：

1. $(E,\preceq)$ 是偏序集合（反身、反对称、传递）；

2. $(E,\preceq)$ 局域有限，即对任意 $e_1,e_2\in E$，因果区间

   $$
   I(e_1,e_2):=\{e\in E: e_1\preceq e\preceq e_2\}
   $$

   为有限集。

因此 $(E,\preceq)$ 与因果集理论中的"局域有限偏序"具有同一结构类型。

证明思路基于两点：其一，若 $(x,n)$ 位于 $(y,m)$ 的几何光锥内，则存在局域算子与态使二者产生非平凡统计相关性；其二，若距离条件不满足，则可以将算子支撑分解到不相交区域，从而期望值因子化，不存在因果影响。局域有限性则由图结构中每个球 $B_R(x)$ 的有限性与时间步数的有限差异给出。详细证明见附录 A。

### 定理 2：QCA 局域性与局域有限偏序的等价刻画

定理 3.2 给出从 QCA 到因果集合的构造。反向表述为：若给定一个离散时间动力学与事件集合上的局域有限偏序，则 QCA 的传播半径可从该偏序的"光锥界面"中重建。

**定理 3.3（等价刻画）** 设 $\alpha:\mathcal A\to\mathcal A$ 为某个 $C^\ast$ 代数自同构，$\Lambda$ 为连通图，$E=\Lambda\times\mathbb Z$。以下两条等价：

1. 存在 $R<\infty$，使得对任意有限 $F\Subset\Lambda$ 与 $A_F\in\mathcal A_F$，有 $\operatorname{supp}(\alpha(A_F))\subset B_R(F)$；

2. 存在一个关系 $\preceq$ 使 $(E,\preceq)$ 为局域有限偏序，且满足：若 $(x,n)\preceq(y,m)$ 且 $m=n+1$，则 $\operatorname{dist}(x,y)\le R$，并且对所有 $(x,n)$，其一步未来的可达点集合包含于 $B_R(x)\times\{n+1\}$。

换言之，QCA 的有限传播半径条件与事件集合上"每一步时间的因果连线仅连接有限邻域"的局域有限偏序结构等价。这一等价刻画将 Schumacher–Werner 与后续工作中的 QCA 定义，用因果集合的语言重述为"离散时间 + 局域有限偏序 + 准局域代数上的自同构"。

### 定理 3：Dirac 型 QCA 的连续极限

QCA 被广泛用作连续量子场论的离散化框架。下面给出一维 Dirac 型 QCA 的连续极限结果，以示范在宇宙 QCA 对象内部如何得到标准狄拉克方程。

考虑 $\Lambda=\mathbb Z$，每个格点携带 $\mathcal H_x\simeq\mathbb C^2$，基矢量记为 $|x,\uparrow\rangle,|x,\downarrow\rangle$。定义时间步演化算子

$$
U:=S\circ R,
$$

其中

1. 局域自旋旋转

   $$
   R_x=\mathrm e^{-\mathrm i\theta\sigma_y}=\cos\theta\,\mathbf 1-\mathrm i\sin\theta\,\sigma_y
   $$

   在每个格点上独立作用；

2. 条件平移

   $$
   S|x,\uparrow\rangle=|x+1,\uparrow\rangle,\quad S|x,\downarrow\rangle=|x-1,\downarrow\rangle
   $$

   。

该 $U$ 为幺正算子，其传播半径为 $R=1$，对应一维 Dirac 型 QCA。记时间步 $n$ 的单粒子态为

$$
|\psi_n\rangle=\sum_{x\in\mathbb Z}\bigl(\psi_n^\uparrow(x)|x,\uparrow\rangle+\psi_n^\downarrow(x)|x,\downarrow\rangle\bigr),
$$

演化方程为

$$
|\psi_{n+1}\rangle=U|\psi_n\rangle
$$

。

令格距 $\varepsilon>0$，定义连续坐标 $X=\varepsilon x$、$T=\varepsilon n$。取旋转角缩放为 $\theta=\varepsilon m$，其中 $m>0$ 为常数。若假设波函数在 $\varepsilon\to 0$ 极限下光滑，满足

$$
\psi_n^\uparrow(x)\approx\psi^\uparrow(X,T),\quad \psi_n^\downarrow(x)\approx\psi^\downarrow(X,T),
$$

则在保留到 $\varepsilon$ 一阶项的泰勒展开后，可得到如下连续方程：

$$
\partial_T\psi^\uparrow=-\partial_X\psi^\uparrow-m\,\psi^\downarrow,\quad
\partial_T\psi^\downarrow=\partial_X\psi^\downarrow+m\,\psi^\uparrow
$$

。

将 $\Psi=(\psi^\uparrow,\psi^\downarrow)^{\mathsf T}$ 记为二分量自旋子，上式可写为

$$
\mathrm i\partial_T\Psi=\bigl(-\mathrm i\sigma_z\partial_X+m\sigma_y\bigr)\Psi,
$$

即一维狄拉克方程的一种标准形式。该结果说明在合适缩放极限下，宇宙 QCA 对象中的 Dirac 型 QCA 在单粒子扇区上产生与连续狄拉克方程一致的动力学。详细推导见附录 C。

---

## Proofs

本节给出主要定理的证明框架，完整细节置于附录。

### 定理 3.2 的证明概述

需要证明两点：

1. 因果关系 $\preceq$ 与几何关系 $\leq_{\rm geo}$ 等价；

2. 在此基础上，$(E,\preceq)$ 为局域有限偏序。

**几何光锥内的可致因性** 若 $(x,n)\leq_{\rm geo}(y,m)$，则 $m\ge n$ 且 $\operatorname{dist}(x,y)\le R(m-n)$。由局域性，对任意支撑在 $\{y\}$ 上的 $B_y$ 有

$$
\operatorname{supp}\bigl(\alpha^{m-n}(B_y)\bigr)\subset B_{R(m-n)}(y),
$$

从而该支撑包含 $x$ 附近的自由度。选择 $A_x$ 与 $B_y$ 使得 $\alpha^{m-n}(B_y)$ 在 $x$ 附近与 $A_x$ 不对易，并取能够分辨该不对易性的态 $\omega$，则

$$
\omega\bigl(\alpha^n(A_x)\alpha^m(B_y)\bigr)-\omega\bigl(\alpha^n(A_x)\bigr)\omega\bigl(\alpha^m(B_y)\bigr)
$$

可构造成非零，从而 $(x,n)\preceq(y,m)$。这一构造利用了局域 Hilbert 空间的有限维性与可选 Pauli 型算子的自由度。

**几何光锥外的无因果性** 若 $m\ge n$ 且 $\operatorname{dist}(x,y)>R(m-n)$，则 $\alpha^{m-n}(B_y)$ 的支撑完全包含在某有限集合 $G\subset\Lambda$ 中，且 $x\notin G$。选取有限集合 $F\Subset\Lambda$ 包含 $x$ 且与 $G$ 不交，则

$$
A_x\in\mathcal A_F,\quad \alpha^{m-n}(B_y)\in\mathcal A_G,\quad F\cap G=\varnothing
$$

。

在张量分解 $\mathcal A_{F\cup G}\cong\mathcal A_F\otimes\mathcal A_G$ 下，二者作用在不同因子上。对任意积态 $\omega_F\otimes\omega_G$ 有

$$
\omega\bigl(\alpha^n(A_x)\alpha^m(B_y)\bigr)=\omega_F(\dots)\omega_G(\dots),
$$

一般态可由积态极限构造，从而得到因子化。于是 $(x,n)\not\preceq(y,m)$。

综合上述两点得到 $\preceq$ 与 $\leq_{\rm geo}$ 的等价。偏序性质由 $\leq_{\rm geo}$ 的反身、反对称与传递性直接推出。

局域有限性：对 $e_1=(x,n)\preceq e_2=(y,m)$，若 $m<n$ 则区间为空集。若 $m\ge n$，任意 $e=(z,k)\in I(e_1,e_2)$ 满足

$$
n\le k\le m,\quad \operatorname{dist}(x,z)\le R(k-n),\quad \operatorname{dist}(z,y)\le R(m-k),
$$

从而

$$
\operatorname{dist}(x,z)\le R(m-n),\quad \operatorname{dist}(y,z)\le R(m-n),
$$

即 $z\in B_{R(m-n)}(x)\cap B_{R(m-n)}(y)$，该集合有限；而 $k$ 仅能取有限多个整数值，因而 $I(e_1,e_2)$ 为有限集。

完整技术细节见附录 A。

### 定理 3.3 的证明概述

从 QCA 的有限传播条件到局域有限偏序的构造已在定理 3.2 中完成。反向方向：假设已知 $(E,\preceq)$ 为局域有限偏序，且存在整数 $R$ 使得任意 $(x,n)$ 的一步未来 $\{(y,n+1):(x,n)\preceq(y,n+1)\}$ 均满足 $\operatorname{dist}(x,y)\le R$。通过该条件，可以定义每一步时间的"邻域传播界"，从而刻画自同构 $\alpha$ 的传播半径不超过 $R$。

具体做法是在任意有限区域 $F$ 上考察一步演化后所有可能发生相关性的格点集合，并利用局域有限性保证这一集合仍有限。进而可证明对任意 $A_F\in\mathcal A_F$，$\alpha(A_F)$ 支撑包含于 $B_R(F)$，从而得到有限传播半径条件。完整证明需要将"统计相关性"与"支撑包含关系"之间的关系形式化，见附录 A。

### 定理 3.4 的证明概述

Dirac 型 QCA 的连续极限证明基于标准的缩放极限分析。关键步骤为：

1. 将离散空间与时间坐标缩放为 $X=\varepsilon x,T=\varepsilon n$，并令旋转角 $\theta=\varepsilon m$ 随 $\varepsilon$ 缩放；

2. 对 $\cos\theta,\sin\theta$ 与波函数 $\psi_n^{\uparrow,\downarrow}(x\pm 1)$ 做一阶泰勒展开；

3. 将离散演化方程

   $$
   \psi_{n+1}^\uparrow(x)=\cos\theta\,\psi_n^\uparrow(x-1)-\sin\theta\,\psi_n^\downarrow(x-1),
   $$

   $$
   \psi_{n+1}^\downarrow(x)=\sin\theta\,\psi_n^\uparrow(x+1)+\cos\theta\,\psi_n^\downarrow(x+1)
   $$

   中的各项替换为连续函数及其导数表达，忽略 $\varepsilon^2$ 及更高阶项；

4. 得到一阶偏微分方程组，并将其整理为自旋子形式，得到一维狄拉克方程。

该构造与量子行走与 QCA 模拟狄拉克方程的典型做法一致。完整展开计算见附录 C。

---

## Model Apply

本节展示宇宙 QCA 对象在具体模型中的应用，重点为 Dirac 型 QCA 示例及其在宇宙 QCA 框架中的嵌入。

### 一维 Dirac 型宇宙截面

设 $\Lambda=\mathbb Z$，$\mathcal H_{\rm cell}\simeq\mathbb C^2$，$\mathcal A$ 为相应准局域代数。选取 Dirac 型 QCA 演化 $\alpha(A)=U^\dagger A U$，其中 $U=S\circ R$ 如前所述。取某个平移不变基态 $\omega_0$ 作为初始态，例如自旋向上填充态、KMS 态或高斯态。

则五元组

$$
\mathfrak U_{\rm QCA}^{\rm Dirac}=(\mathbb Z,\mathcal H_{\rm cell},\mathcal A,\alpha,\omega_0)
$$

构成宇宙 QCA 对象，其事件集合 $E=\mathbb Z\times\mathbb Z$ 在 QCA 半径 $R=1$ 下诱导出因果结构

$$
(x,n)\preceq(y,m)\iff m\ge n,\ \operatorname{dist}(x,y)\le m-n
$$

。

在单粒子扇区与 $\varepsilon\to 0$ 缩放极限下，本模型的有效动力学由一维狄拉克方程控制，展示了如何在宇宙 QCA 框架中重构 relativistic 场的低能行为。

### 多维与多场自由度的推广

在更高维空间 $\Lambda=\mathbb Z^d$ 上，可以采用类似构造，引入更复杂的局域 Hilbert 空间 $\mathcal H_{\rm cell}$（例如携带多个自旋和内部自由度），构造出对应的 Dirac、Weyl 或 Majorana 型 QCA。已有工作表明，通过适当的 QCA，可以在连续极限中得到多种 free-field 以及某些相互作用场论的有效描述。在宇宙 QCA 视角下，这些模型对应于不同的"宇宙局部截面"或"不同的宇宙实例"。

---

## Engineering Proposals

尽管本文构造的是抽象公理框架，QCA 本身具有明确的实验与工程实现途径。在"宇宙 = QCA"视角中，可以将现有量子模拟与量子信息平台视为对该宇宙结构的"子宇宙仿真"。

### 量子行走与 QCA 在实验平台上的实现

1. **光学晶格与冷原子**

   在一维或二维光学晶格中，利用原子的内部自由度作为自旋，格点位置作为离散空间，可以通过交替施加自旋旋转与条件平移实现 Dirac 型 QCA。实验上已实现多种量子行走与 Dirac 型演化，其哈密顿近似与本文 Dirac 型 QCA 在结构上相同。

2. **离子阱与超导量子比特阵列**

   在线性离子阱或二维超导量子比特阵列中，局域单、双量子门可以组合成有限深度量子电路，实现给定传播半径的 QCA。特别地，有限半径 QCA 在物理上可以实现为有限深度量子电路与有限范围相互作用的组合。

3. **拓扑量子比特与费米型 QCA**

   在拓扑超导或 Majorana 线性阵列中，可以构造具有 $\mathbb Z_2$ 指数的费米型 QCA，用于模拟拓扑相与边界模。该类模型与宇宙 QCA 对象的框架兼容，可以在因果结构与 quasi-particle 传播上得到一致的描述。

### 宇宙 QCA 公理的检验思路

尽管无法在实验中直接操控"全宇宙的 QCA"，可以通过以下方式间接检验该框架的合理性：

1. **传播半径与"光速"**

   在 QCA 模型中，传播半径 $R$ 与时间步长共同决定最大传播速度。若宇宙本体确为 QCA，则物理上观测到的最大传播速度（如光速）应与这一离散传播界限一致，在连续极限中呈现洛伦兹不变性。

2. **局域有限性与信息传播**

   在实际量子系统中，Lieb–Robinson 界给出了有限传播速度的有界算子传播。QCA 作为严格局域模型，其传播界限清晰。观测各类量子系统中的信息传播锥形边界，为"宇宙动力学具有 QCA 型局域性"提供间接证据。

3. **连续极限与场方程恢复**

   通过构造 QCA 并在实验平台模拟其演化，观察其在大尺度上的有效行为是否遵循已知的 relativistic 场方程，是检验"宇宙 QCA 对象"是否足以支撑现有物理的关键途径。

---

## Discussion (risks, boundaries, past work)

本节讨论宇宙 QCA 框架的适用边界、潜在风险以及与既有工作的关系。

### 与传统 QCA 文献的关系

Schumacher–Werner、Richter–Werner 等工作采用准局域代数与有限传播条件定义 QCA，为本文宇宙 QCA 对象中的动力学部分提供了成熟基础。Arrighi 与 Farrelly 等综述了 QCA 的结构定理、分类与量子模拟应用，展示了 QCA 与拓扑相、量子信息处理之间的联系。这些工作主要聚焦于"给定物理系统的离散化描述"，而本文则将 QCA 提升为宇宙本体的公理对象。

因果集方案则从因果偏序与局域有限性出发，将时空视为离散偏序集合，并在极限中恢复连续几何。本文展示宇宙 QCA 对象自然诱导出局域有限偏序 $(E,\preceq)$，与因果集结构对齐，从而将 QCA 与因果集统一在一个框架中：前者赋予每个事件以局域量子自由度与动力学，后者通过偏序与局域有限性刻画"时空结构"。

### 概念与技术边界

1. **洛伦兹不变性与连续极限**

   在离散晶格上实现精确的洛伦兹不变性存在困难。QCA 模型通常在低能与长波长极限下近似呈现洛伦兹不变行为，但在高能尺度上会出现"晶格各向异性"与色散。宇宙 QCA 框架需要给出系统的连续极限构造与误差估计，以确保可观测能量尺度下的物理符合现有实验。

2. **引力与曲率的编码方式**

   本文仅在固定图结构 $\Lambda$ 与固定传播半径 $R$ 的设定下讨论因果结构与量子动力学，尚未将引力与曲率效应纳入 QCA 公理中。要与广义相对论或量子引力方案对接，需要在 QCA 框架中引入随状态或能量动量分布变化的图结构与传播参数，或在因果集合极限中重构有效度规与曲率。

3. **相互作用与重整化**

   虽然已知 QCA 可以模拟 free-field 与部分相互作用场论，但完整的重整化群结构与连续极限中的相互作用流仍是开放问题。宇宙 QCA 框架需要与重整化群和有效场论机制兼容，才能在宽能标上重现物理现象。

4. **本体论与可检验性**

   将宇宙定义为单一 QCA 对象是一种本体论选择。其可检验性依赖于是否能从该框架推导出与连续理论不同的可观测预测，例如高能散射中的偏离、宇宙早期的离散迹象等。

### 过去工作的对齐

本文在结构上与以下方向形成对齐：

1. 使用准局域 $C^\ast$ 代数与有限传播自同构刻画离散时间动力学，与可逆 QCA 文献一致；

2. 使用局域有限偏序刻画因果结构，与因果集理论的基本定义一致；

3. 使用 Dirac 型 QCA 实现 relativistic 场的离散化与连续极限，与量子行走与 QCA 模拟文献中的典型模型一致。

差异在于：本文将这三条线索统一为单一公理化对象 $\mathfrak U_{\rm QCA}$，将"宇宙"定义为满足这些公理的整体，而非在既定连续时空上构造 QCA。

---

## Conclusion

本文在量子元胞自动机与因果集合的框架内，提出"宇宙作为量子离散元胞自动机"的公理化刻画。主要内容包括：

1. 以可数连通图 $\Lambda$、有限维局域 Hilbert 空间 $\mathcal H_{\rm cell}$、准局域 $C^\ast$ 代数 $\mathcal A$ 与有限传播半径的 QCA $\alpha$ 构造宇宙 QCA 对象 $\mathfrak U_{\rm QCA}$，并以初始态 $\omega_0$ 赋予其统计结构；

2. 由 QCA 局域性与图结构导出事件集合 $E=\Lambda\times\mathbb Z$ 上的因果可达关系 $\preceq$，证明 $(E,\preceq)$ 为局域有限偏序，与因果集理论的基本结构对齐；

3. 给出 QCA 局域性与事件集合上局域有限偏序之间的等价刻画，将 Schumacher–Werner 的 QCA 定义重述为"离散时间 + 局域有限偏序 + 准局域代数自同构"的统一形式；

4. 构造一维 Dirac 型 QCA，并在合适缩放极限下得到连续狄拉克方程，展示宇宙 QCA 对象可以在低能极限中重现 relativistic 场论；

5. 简要讨论观测、熵与时间箭头在 QCA 宇宙中的抽象表达，以及潜在实验检验途径与与既有 QCA、因果集文献的对接。

这一框架为离散宇宙模型提供了严格的算子代数与因果结构基础。未来工作方向包括：在 QCA 公理中显式引入引力与曲率结构；构建与重整化群兼容的多尺度 QCA 宇宙；在宇宙学与高能物理情境下提取潜在可观测预测，并与实验结果对比。

---

## Acknowledgements, Code Availability

本工作依托于量子元胞自动机、准局域 $C^\ast$ 代数与因果集理论的既有成果。在此对相关研究社群长期发展的理论基础表示感谢。

文中 Dirac 型 QCA 与宇宙 QCA 对象的构造均为解析形式，未附带特定软件实现代码。任意可编程量子模拟平台（如量子电路模拟器、冷原子或超导量子比特装置）均可依据附录 C 中给出的演化算子分解实现相应模型。

---

## References

1. B. Schumacher, R. F. Werner, "Reversible Quantum Cellular Automata", arXiv:quant-ph/0405174, 2004.

2. P. Arrighi, "An Overview of Quantum Cellular Automata", Natural Computing, 18, 885–899, 2019.

3. T. Farrelly, "A Review of Quantum Cellular Automata", Quantum, 4, 368, 2020.

4. S. Richter, R. F. Werner, "Ergodicity of Quantum Cellular Automata", arXiv:cond-mat/9504001, 1995.

5. S. Surya, "The Causal Set Approach to Quantum Gravity", Living Reviews in Relativity, 22, 5, 2019.

6. D. D. Reid, "Causal Sets: An Alternative View of Spacetime Structure", AIP Conf. Proc. 991, 1–9, 2008.

7. G. Brightwell, R. Gregory, "Structure of Random Discrete Spacetime", Physical Review Letters, 66, 260–263, 1991.

8. C. Jones, "DHR Bimodules of Quasi-Local Algebras and Symmetric Fusion Categories", J. Eur. Math. Soc., 2024.

9. A. Tosini, "A Quantum Cellular Automata Framework for Quantum Field Theory", PhD Thesis, 等。

---

## 附录 A：QCA 因果结构为局域有限偏序的详细证明

本附录补完定理 3.2 与定理 3.3 的技术细节。

### A.1 因果关系与几何关系的等价性

回顾定义：几何关系

$$
(x,n)\leq_{\rm geo}(y,m)\iff m\ge n,\ \operatorname{dist}(x,y)\le R(m-n),
$$

因果关系 $\preceq$ 定义为存在局域算子与态产生非平凡统计相关性。

**命题 A.1（几何光锥内可致因）** 若 $(x,n)\leq_{\rm geo}(y,m)$，则 $(x,n)\preceq(y,m)$。

*证明*：$\operatorname{dist}(x,y)\le R(m-n)$ 保证

$$
x\in B_{R(m-n)}(y)
$$

。

对任意 $B_y\in\mathcal A_{\{y\}}$，由局域性

$$
\operatorname{supp}\bigl(\alpha^{m-n}(B_y)\bigr)\subset B_{R(m-n)}(y)
$$

。

因此存在 $x$ 的邻域 $N(x)\subset B_{R(m-n)}(y)$，使得 $\alpha^{m-n}(B_y)$ 在 $\mathcal A_{N(x)}$ 中具有非平凡作用。选取 $A_x\in\mathcal A_{\{x\}}$ 使得其在 $\mathcal A_{N(x)}$ 中与 $\alpha^{m-n}(B_y)$ 不对易。例如在 $\mathcal H_x\simeq\mathbb C^2$ 上取 Pauli 算子 $\sigma_x,\sigma_z$ 等，通过线性组合构造出满足 $[A_x,\alpha^{m-n}(B_y)]\neq 0$ 的算子。

在某个纯态 $\omega$ 下，选取 $\omega$ 使得

$$
\omega\bigl([A_x,\alpha^{m-n}(B_y)]\bigr)\neq 0,
$$

则

$$
\omega\bigl(\alpha^n(A_x)\alpha^m(B_y)\bigr)
=\omega\bigl(\alpha^n(A_x\alpha^{m-n}(B_y))\bigr),
$$

$$
\omega\bigl(\alpha^n(A_x)\bigr)\omega\bigl(\alpha^m(B_y)\bigr)
=\omega\bigl(\alpha^n(A_x)\bigr)\omega\bigl(\alpha^n(\alpha^{m-n}(B_y))\bigr),
$$

二者之差与 $\omega\bigl([A_x,\alpha^{m-n}(B_y)]\bigr)$ 相关，可构造为非零。于是 $(x,n)\preceq(y,m)$。证毕。

**命题 A.2（几何光锥外的无因果性）** 若 $m\ge n$ 且 $\operatorname{dist}(x,y)>R(m-n)$，则对任意局域算子 $A_x\in\mathcal A_{\{x\}}$、$B_y\in\mathcal A_{\{y\}}$ 与任意态 $\omega$，有

$$
\omega\bigl(\alpha^n(A_x)\alpha^m(B_y)\bigr)
=\omega\bigl(\alpha^n(A_x)\bigr)\omega\bigl(\alpha^m(B_y)\bigr)
$$

。

*证明*：有

$$
\alpha^m(B_y)=\alpha^n\bigl(\alpha^{m-n}(B_y)\bigr),
$$

且

$$
\operatorname{supp}\bigl(\alpha^{m-n}(B_y)\bigr)\subset B_{R(m-n)}(y)
$$

。

由于 $\operatorname{dist}(x,y)>R(m-n)$，可取有限 $F\Subset\Lambda$ 满足 $x\in F$，且 $F\cap B_{R(m-n)}(y)=\varnothing$。则

$$
A_x\in\mathcal A_F,\quad \alpha^{m-n}(B_y)\in\mathcal A_G,
$$

其中 $G\subset B_{R(m-n)}(y)$，且 $F\cap G=\varnothing$。

在 $\mathcal A_{F\cup G}\cong\mathcal A_F\otimes\mathcal A_G$ 的张量分解下，有

$$
A_x=A_F\otimes\mathbf 1_G,\quad \alpha^{m-n}(B_y)=\mathbf 1_F\otimes B_G,
$$

因而

$$
\alpha^n(A_x)\alpha^m(B_y)
=\alpha^n(A_F\otimes\mathbf 1_G)\alpha^n(\mathbf 1_F\otimes B_G)
=\alpha^n(A_F\otimes B_G)
$$

。

对任意积态 $\omega=\omega_F\otimes\omega_G$，有

$$
\omega\bigl(\alpha^n(A_x)\alpha^m(B_y)\bigr)
=\omega_F\bigl(\alpha_F^n(A_F)\bigr)\omega_G\bigl(\alpha_G^n(B_G)\bigr),
$$

与

$$
\omega\bigl(\alpha^n(A_x)\bigr)\omega\bigl(\alpha^m(B_y)\bigr)
=\omega_F\bigl(\alpha_F^n(A_F)\bigr)\omega_G\bigl(\alpha_G^n(B_G)\bigr)
$$

相同。一般态可由积态的弱$^*$ 极限取得，从而得到因子化关系。于是不存在非平凡统计相关性，即 $(x,n)\not\preceq(y,m)$。证毕。

命题 A.1 与 A.2 共同给出

$$
(x,n)\preceq(y,m)\iff(x,n)\leq_{\rm geo}(y,m),
$$

从而因果关系与几何光锥等价。

### A.2 偏序性质与局域有限性的证明

由几何关系定义：

1. 反身性：对任意 $(x,n)$，有 $\operatorname{dist}(x,x)=0\le R(0)$，且 $n\ge n$，故 $(x,n)\leq_{\rm geo}(x,n)$，从而 $(x,n)\preceq(x,n)$。

2. 反对称性：若 $(x,n)\leq_{\rm geo}(y,m)$ 且 $(y,m)\leq_{\rm geo}(x,n)$，则 $m\ge n$ 与 $n\ge m$ 蕴含 $m=n$，此时

   $$
   \operatorname{dist}(x,y)\le 0,\quad \operatorname{dist}(y,x)\le 0,
   $$

   故 $x=y$，从而 $(x,n)=(y,m)$。

3. 传递性：若 $(x,n)\leq_{\rm geo}(y,m)$ 与 $(y,m)\leq_{\rm geo}(z,k)$，则 $m\ge n$、$k\ge m$ 与

   $$
   \operatorname{dist}(x,y)\le R(m-n),\quad \operatorname{dist}(y,z)\le R(k-m)
   $$

   成立。由图距离的三角不等式，

   $$
   \operatorname{dist}(x,z)\le\operatorname{dist}(x,y)+\operatorname{dist}(y,z)
   \le R(m-n)+R(k-m)=R(k-n),
   $$

   且 $k\ge n$，故 $(x,n)\leq_{\rm geo}(z,k)$，即 $(x,n)\preceq(z,k)$。

局域有限性：设 $e_1=(x,n)\preceq e_2=(y,m)$。若 $m<n$，区间为空集。若 $m\ge n$，则对任意 $e=(z,k)\in I(e_1,e_2)$，由几何等价性有

$$
n\le k\le m,
$$

$$
\operatorname{dist}(x,z)\le R(k-n),\quad \operatorname{dist}(z,y)\le R(m-k)
$$

。

因此

$$
\operatorname{dist}(x,z)\le R(m-n),\quad \operatorname{dist}(y,z)\le R(m-n),
$$

即 $z\in B_{R(m-n)}(x)\cap B_{R(m-n)}(y)$。由对图结构的假设，该交集为有限集，记其基数为 $N<\infty$。另一方面，$k$ 只能在有限集合 $\{n,n+1,\dots,m\}$ 中取值，故可能的 $(z,k)$ 组合至多 $N\cdot(m-n+1)$ 个，从而 $I(e_1,e_2)$ 有限。

由此完成定理 3.2 的证明。

---

## 附录 B：QCA 幺正实现定理的证明

本附录证明 QCA 在 $\alpha$ 不变忠实态的 GNS 表象中可以由唯一幺正算子实现。

设 $\alpha:\mathcal A\to\mathcal A$ 为 QCA，$\omega$ 为忠实且 $\alpha$ 不变的态，即 $\omega\circ\alpha=\omega$，且 $\omega(A^\ast A)=0\Rightarrow A=0$。令 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$ 为其 GNS 表象。

### B.1 算子 $U$ 的构造与等距性

在稠密子空间 $\mathcal D_0:=\{\pi_\omega(A)\Omega_\omega:A\in\mathcal A\}$ 上定义线性算子

$$
U_0:\mathcal D_0\to\mathcal H_\omega,\quad
U_0\bigl(\pi_\omega(A)\Omega_\omega\bigr):=\pi_\omega(\alpha(A))\Omega_\omega
$$

。

对任意 $A,B\in\mathcal A$，有

$$
\langle U_0\pi_\omega(A)\Omega_\omega,U_0\pi_\omega(B)\Omega_\omega\rangle
=\langle\pi_\omega(\alpha(A))\Omega_\omega,\pi_\omega(\alpha(B))\Omega_\omega\rangle
=\omega\bigl(\alpha(A)^\ast\alpha(B)\bigr)
$$

。

利用 $\alpha$ 为 $*$ 自同构与 $\omega\circ\alpha=\omega$，

$$
\omega\bigl(\alpha(A)^\ast\alpha(B)\bigr)
=\omega\bigl(A^\ast B\bigr)
=\langle\pi_\omega(A)\Omega_\omega,\pi_\omega(B)\Omega_\omega\rangle
$$

。

故 $U_0$ 在 $\mathcal D_0$ 上保持内积，为等距线性算子。由 $\mathcal D_0$ 在 $\mathcal H_\omega$ 中稠密，$U_0$ 可以唯一延拓为界算子 $U:\mathcal H_\omega\to\mathcal H_\omega$，且 $U$ 是等距的，即

$$
\langle U\phi,U\psi\rangle=\langle\phi,\psi\rangle,\quad \phi,\psi\in\mathcal H_\omega
$$

。

### B.2 满射性与幺正性

需要证明 $U$ 为满射。对任意 $B\in\mathcal A$，由于 $\alpha$ 为双射，存在 $A\in\mathcal A$ 使 $B=\alpha(A)$。于是

$$
\pi_\omega(B)\Omega_\omega=\pi_\omega(\alpha(A))\Omega_\omega=U_0\pi_\omega(A)\Omega_\omega\in\operatorname{Ran}(U_0)
$$

。

因此 $\operatorname{Ran}(U_0)$ 中包含 $\{\pi_\omega(B)\Omega_\omega:B\in\mathcal A\}$，该集合在 $\mathcal H_\omega$ 中稠密。由于 $U$ 是 $U_0$ 的连续延拓，$\operatorname{Ran}(U)$ 为 $\operatorname{Ran}(U_0)$ 的闭包，既闭又稠密，从而 $\operatorname{Ran}(U)=\mathcal H_\omega$，$U$ 为满射等距算子，即幺正算子。

### B.3 共轭作用实现 $\alpha$

对任意 $A,B\in\mathcal A$，有

$$
U\pi_\omega(A)U^\dagger\pi_\omega(B)\Omega_\omega
=U\pi_\omega(A)\bigl(U^\dagger\pi_\omega(B)\Omega_\omega\bigr)
$$

。

注意到

$$
U^\dagger\pi_\omega(B)\Omega_\omega
$$

是某个向量，且由定义可写为 GNS 向量的线性组合。更方便的做法是直接在 $\mathcal D_0$ 上计算：

$$
\begin{aligned}
U\pi_\omega(A)U^\dagger\pi_\omega(B)\Omega_\omega
&=U\pi_\omega(A)\bigl(U^\dagger\pi_\omega(B)\Omega_\omega\bigr)\\
&=U\pi_\omega(A)\bigl(\pi_\omega(\alpha^{-1}(B))\Omega_\omega\bigr)\\
&=U_0\bigl(\pi_\omega(A\alpha^{-1}(B))\Omega_\omega\bigr)\\
&=\pi_\omega(\alpha(A\alpha^{-1}(B)))\Omega_\omega\\
&=\pi_\omega(\alpha(A)B)\Omega_\omega\\
&=\pi_\omega(\alpha(A))\pi_\omega(B)\Omega_\omega
\end{aligned}
$$

。

由于 $\{\pi_\omega(B)\Omega_\omega:B\in\mathcal A\}$ 在 $\mathcal H_\omega$ 中稠密，上式说明

$$
U\pi_\omega(A)U^\dagger=\pi_\omega(\alpha(A))
$$

在整个 Hilbert 空间上成立。

最后，

$$
U\Omega_\omega=U\pi_\omega(\mathbf 1)\Omega_\omega
=\pi_\omega(\alpha(\mathbf 1))\Omega_\omega
=\pi_\omega(\mathbf 1)\Omega_\omega
=\Omega_\omega,
$$

说明 GNS 向量为 $U$ 不变向量。至此完成幺正实现定理的证明。

---

## 附录 C：一维 Dirac 型 QCA 与狄拉克方程的连续极限

本附录给出一维 Dirac 型 QCA 的具体构造与连续极限推导。

### C.1 模型定义与离散演化方程

取 $\Lambda=\mathbb Z$，每个格点携带 $\mathcal H_x\simeq\mathbb C^2$，基矢量记为 $|x,\uparrow\rangle,|x,\downarrow\rangle$。整体 Hilbert 空间形式上为

$$
\mathcal H=\bigotimes_{x\in\mathbb Z}\mathcal H_x
$$

。

定义局域自旋旋转算子

$$
R_x=\mathrm e^{-\mathrm i\theta\sigma_y}
=\cos\theta\,\mathbf 1-\mathrm i\sin\theta\,\sigma_y,
$$

全局旋转

$$
R:=\bigotimes_{x\in\mathbb Z}R_x
$$

。

定义条件平移算子 $S$ 在单粒子基上作用为

$$
S|x,\uparrow\rangle=|x+1,\uparrow\rangle,\quad S|x,\downarrow\rangle=|x-1,\downarrow\rangle
$$

。

时间步演化算子为

$$
U:=S\circ R
$$

。

$U$ 为幺正算子且具有传播半径 $R=1$。

在单粒子扇区，可写

$$
|\psi_n\rangle=\sum_{x\in\mathbb Z}\bigl(\psi_n^\uparrow(x)|x,\uparrow\rangle+\psi_n^\downarrow(x)|x,\downarrow\rangle\bigr),
$$

离散演化为

$$
|\psi_{n+1}\rangle=U|\psi_n\rangle
$$

。

展开得到递推关系：

$$
\psi_{n+1}^\uparrow(x)=\cos\theta\,\psi_n^\uparrow(x-1)-\sin\theta\,\psi_n^\downarrow(x-1),
$$

$$
\psi_{n+1}^\downarrow(x)=\sin\theta\,\psi_n^\uparrow(x+1)+\cos\theta\,\psi_n^\downarrow(x+1)
$$

。

### C.2 连续极限与泰勒展开

引入格距 $\varepsilon>0$，定义连续变量

$$
X=\varepsilon x,\quad T=\varepsilon n
$$

。

假设存在光滑函数 $\psi^{\uparrow,\downarrow}(X,T)$，使得

$$
\psi_n^\uparrow(x)\approx\psi^\uparrow(X,T),\quad \psi_n^\downarrow(x)\approx\psi^\downarrow(X,T)
$$

在 $X=\varepsilon x,T=\varepsilon n$ 处。令旋转角随 $\varepsilon$ 缩放为

$$
\theta=\varepsilon m,
$$

其中 $m>0$ 为常数。

对 $\cos\theta$ 与 $\sin\theta$ 作一阶展开：

$$
\cos\theta=\cos(\varepsilon m)\approx 1-\frac{1}{2}\varepsilon^2 m^2,
$$

$$
\sin\theta=\sin(\varepsilon m)\approx \varepsilon m
$$

。

对空间平移与时间步进作一阶展开：

$$
\psi_n^\uparrow(x\pm 1)\approx\psi^\uparrow(X\pm\varepsilon,T)\approx\psi^\uparrow(X,T)\pm\varepsilon\partial_X\psi^\uparrow(X,T),
$$

$$
\psi_n^\downarrow(x\pm 1)\approx\psi^\downarrow(X\pm\varepsilon,T)\approx\psi^\downarrow(X,T)\pm\varepsilon\partial_X\psi^\downarrow(X,T),
$$

$$
\psi_{n+1}^\uparrow(x)\approx\psi^\uparrow(X,T+\varepsilon)\approx\psi^\uparrow(X,T)+\varepsilon\partial_T\psi^\uparrow(X,T),
$$

$$
\psi_{n+1}^\downarrow(x)\approx\psi^\downarrow(X,T+\varepsilon)\approx\psi^\downarrow(X,T)+\varepsilon\partial_T\psi^\downarrow(X,T)
$$

。

将上述展开代入离散演化方程，并保留 $\varepsilon$ 的一阶项。

对自旋向上分量：

$$
\psi^\uparrow(X,T)+\varepsilon\partial_T\psi^\uparrow(X,T)
\approx
\left(1-\frac{1}{2}\varepsilon^2 m^2\right)\bigl[\psi^\uparrow(X-\varepsilon,T)\bigr]
-\varepsilon m\,\psi^\downarrow(X-\varepsilon,T)
$$

。

右侧展开为

$$
\left(1-\frac{1}{2}\varepsilon^2 m^2\right)\bigl[\psi^\uparrow(X,T)-\varepsilon\partial_X\psi^\uparrow(X,T)\bigr]
-\varepsilon m\bigl[\psi^\downarrow(X,T)-\varepsilon\partial_X\psi^\downarrow(X,T)\bigr]
$$

。

忽略 $\varepsilon^2$ 项，得到

$$
\psi^\uparrow(X,T)+\varepsilon\partial_T\psi^\uparrow(X,T)
\approx
\psi^\uparrow(X,T)-\varepsilon\partial_X\psi^\uparrow(X,T)-\varepsilon m\,\psi^\downarrow(X,T)
$$

。

两边减去 $\psi^\uparrow(X,T)$，整理为

$$
\partial_T\psi^\uparrow(X,T)=-\partial_X\psi^\uparrow(X,T)-m\,\psi^\downarrow(X,T)
$$

。

对自旋向下分量：

$$
\psi^\downarrow(X,T)+\varepsilon\partial_T\psi^\downarrow(X,T)
\approx
\varepsilon m\,\psi^\uparrow(X+\varepsilon,T)+\left(1-\frac{1}{2}\varepsilon^2 m^2\right)\psi^\downarrow(X+\varepsilon,T)
$$

。

右侧展开为

$$
\varepsilon m\bigl[\psi^\uparrow(X,T)+\varepsilon\partial_X\psi^\uparrow(X,T)\bigr]
+\bigl[\psi^\downarrow(X,T)+\varepsilon\partial_X\psi^\downarrow(X,T)\bigr],
$$

忽略 $\varepsilon^2$ 项，得到

$$
\psi^\downarrow(X,T)+\varepsilon\partial_T\psi^\downarrow(X,T)
\approx
\psi^\downarrow(X,T)+\varepsilon\partial_X\psi^\downarrow(X,T)+\varepsilon m\,\psi^\uparrow(X,T)
$$

。

两边减去 $\psi^\downarrow(X,T)$，整理为

$$
\partial_T\psi^\downarrow(X,T)=\partial_X\psi^\downarrow(X,T)+m\,\psi^\uparrow(X,T)
$$

。

将二者写成自旋子形式。定义

$$
\Psi(X,T):=\begin{pmatrix}\psi^\uparrow(X,T)\\\psi^\downarrow(X,T)\end{pmatrix},
$$

则上式为

$$
\partial_T\Psi(X,T)=-\sigma_z\partial_X\Psi(X,T)-m\,\sigma_x\Psi(X,T)
$$

。

乘以 $\mathrm i$ 并重排列得

$$
\mathrm i\partial_T\Psi(X,T)=\bigl(-\mathrm i\sigma_z\partial_X+m\sigma_y\bigr)\Psi(X,T),
$$

其中经过基底重定义可将 $-m\sigma_x$ 与 $m\sigma_y$ 互换。本方程即一维狄拉克方程的标准表示之一。

### C.3 与宇宙 QCA 对象的关系

在宇宙 QCA 框架中，一维 Dirac 型模型对应

$$
\mathfrak U_{\rm QCA}^{\rm Dirac}=(\mathbb Z,\mathcal H_{\rm cell},\mathcal A,\alpha,\omega_0),
$$

其中 $\alpha(A)=U^\dagger A U$。该对象诱导事件集合 $E=\mathbb Z\times\mathbb Z$ 及其因果偏序 $\preceq$，QCA 的传播半径 $R=1$ 对应"最大传播速度"，连续极限下的狄拉克方程则是该宇宙在低能、长波长尺度上的有效描述。

这一示例说明：在宇宙被定义为 QCA 对象的前提下，通过适当的缩放与 coarse-graining，可以在内部构造中重现连续 relativistic 场论，从而为"宇宙作为量子离散元胞自动机"的合理性提供具体数学支撑。

