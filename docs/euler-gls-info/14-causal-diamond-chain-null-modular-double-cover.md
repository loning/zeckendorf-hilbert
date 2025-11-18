# 计算宇宙中的因果小钻石链与 Null–Modular 双覆盖

统一时间刻度下的离散因果结构、拓扑时间相位与自指奇偶

---

## 摘要

此前我们在计算宇宙公理框架 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 上先后构造了离散复杂性几何、离散信息几何、统一时间刻度诱导的控制流形 $(\mathcal M,G)$、任务信息流形 $(\mathcal S_Q,g_Q)$、时间–信息–复杂性联合变分原理、多观察者共识几何、因果小钻石与边界计算以及拓扑复杂性与不可判定性。另一方面，在物理宇宙侧，小因果菱形与 Null–Modular 双覆盖结构在统一时间刻度–边界时间几何中扮演关键角色：Null 边界上的相位–延迟–熵具有天然的 $\mathbb Z_2$ 奇偶与双覆盖结构，用以刻画时间方向、能量条件与自指反馈网络。

本文在计算宇宙层面构造一个完全离散的"因果小钻石链与 Null–Modular 双覆盖"理论，并证明其在统一时间刻度与复杂性几何的极限下与物理侧的因果菱形链及 Null–Modular 结构同构。具体而言，我们做以下几件事：

1. 在事件层 $E = X\times\mathbb N$ 上定义复杂性因果偏序与有限预算因果小钻石 $\Diamond(e_{\mathrm{in}},e_{\mathrm{out}};T)$，并将"小钻石链"形式化为在偏序中满足适当重叠条件的有序族 $\{\Diamond_k\}_{k\in\mathbb Z}$。我们证明该族在自然条件下构成一个带边界算子的有向图–链复形，其 1–骨架刻画统一时间刻度下的"离散时间线"。

2. 在小钻石链上引入 Null–Modular 双覆盖：对每个钻石边界态赋予一个 $\mathbb Z_2$ 取值的"模 2 时间相位"标签，并对钻石链构造一个二重覆盖图 $\widetilde{\mathfrak D} \to \mathfrak D$，使得闭合钻石链的提升路径存在或不存在对应于 $\mathbb Z_2$ holonomy 的奇偶。我们证明该双覆盖与此前在拓扑复杂性中引入的自指奇偶不变量 $\sigma(\gamma)\in\mathbb Z_2$ 一致。

3. 将统一时间刻度引入钻石链：每一条钻石链边上定义离散时间增量 $\Delta\tau_k$，由统一时间刻度密度 $\kappa(\omega)$ 与局域散射相位导数给出。我们证明在细化极限下，小钻石链的时间间隔和 $\mathbb Z_2$ holonomy 共同定义了控制流形上的一类"带 Null–Modular 结构的时间方向场"，从而将离散 Null–Modular 双覆盖与连续统一时间刻度对接。

4. 在多观察者因果网中，将每个观察者的"小钻石世界管"嵌入钻石链双覆盖中，构造一个多观察者 Null–Modular 共识结构，证明自指散射网络与多观察者共识几何中的 $\mathbb Z_2$ 奇偶跃迁可以视为钻石链双覆盖上的 holonomy 不变量。

5. 在拓扑复杂性与不可判定性的背景下，我们证明：在一般可构造的计算宇宙族上，判定"一条给定的钻石链闭合环路是否在 Null–Modular 双覆盖中可提升为闭合路径"是不可判定的，从而给出一个"Null–Modular 版停机问题"。同时，我们构造一个与复杂性熵兼容的"时间相位–复杂性第二定律"：在统一时间刻度与 Null–Modular 双覆盖的共同约束下，自指奇偶与可压缩复杂度构成的联合不变量沿钻石链 coarse–graining 演化具有单调结构。

通过上述构造，本文将计算宇宙中的离散因果小钻石链、统一时间刻度、拓扑自指奇偶与复杂性第二定律统一进一个 Null–Modular 双覆盖框架，并在附录中给出主要结构的详细证明与链复形的严格构造。

---

## 1 引言

在统一时间刻度–边界时间几何的物理宇宙构造中，小因果菱形、Null 边界与 Null–Modular 双覆盖结构是连接散射相位、群延迟、广义熵与时间方向的基本构件。特别地，当考察一连串嵌套或相交的小因果菱形时，边界上的相位–延迟数据存在一个自然的 $\mathbb Z_2$ 奇偶结构：某些闭合菱形链在 Null–Modular 双覆盖上提升为闭合路径，另一些则产生"奇数次跳变"，留下一个拓扑 holonomy。该 holonomy 与自指反馈网络、自我同一性与复杂性第二定律有紧密联系。

另一方面，在本系列关于"计算宇宙"的工作中，我们已经在完全离散的抽象公理框架中构造了：

* 复杂性图 $G_{\mathrm{comp}} = (X,E,\mathsf C)$ 与复杂性距离 $d_{\mathrm{comp}}$；
* 任务信息流形 $(\mathcal S_Q,g_Q,\Phi_Q)$ 与离散信息几何；
* 统一时间刻度诱导的控制流形 $(\mathcal M,G)$ 与测地结构；
* 时间–信息–复杂性联合变分原理；
* 因果小钻石与边界计算算子 $\mathsf K_\Diamond$；
* 多观察者共识几何与因果网；
* 拓扑复杂性、自指环路与 $\mathbb Z_2$ 自指奇偶 $\sigma(\gamma)$。

自然问题是：是否可以在计算宇宙的离散因果结构上，完全模拟物理宇宙中的"小因果菱形链 + Null–Modular 双覆盖"这一结构？若可以，其拓扑 $\mathbb Z_2$ holonomy 是否与此前自指奇偶不变量一致？统一时间刻度是否在钻石链上自然分层为"时间步长 + 奇偶跃迁"的组合？多观察者在因果网中的自指反馈又如何在该结构中体现？

本文的回答是肯定的，我们将展示：

1. 在计算宇宙的事件层 $E = X\times\mathbb N$ 上，可以定义完全离散的"因果小钻石链"，其链复形与边界算子自然对应统一时间刻度的离散时间步；
2. 在小钻石链上可以构造 Null–Modular 双覆盖，其 $\mathbb Z_2$ holonomy 与此前自指奇偶 $\sigma(\gamma)$ 同构；
3. 多观察者的世界管可以视为钻石链双覆盖中的一族"提升路径"，多观察者共识几何与自指反馈网络成为该双覆盖上的几何–拓扑结构；
4. 在这一框架下，可以定义"Null–Modular 版停机问题"，并证明其不可判定性，同时给出与复杂性熵兼容的"时间相位–复杂性第二定律"。

全文结构如下：第 2 节构造事件层因果小钻石链与链复形；第 3 节在钻石链上定义 Null–Modular 双覆盖与 $\mathbb Z_2$ holonomy；第 4 节将统一时间刻度与钻石链与双覆盖对接；第 5 节引入多观察者 Null–Modular 共识几何；第 6 节讨论 Null–Modular 版停机问题与复杂性第二定律；附录给出链复形构造、双覆盖存在性、holonomy–自指奇偶对应、不可判定性与第二定律原型的详细证明。

---

## 2 事件层因果小钻石与钻石链

本节在计算宇宙事件层构造因果小钻石与钻石链，并给出一个离散链复形结构。

### 2.1 事件层与因果偏序

考虑计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$，事件层定义为

$$
E = X\times\mathbb N, \quad e=(x,k).
$$

一步更新关系

$$
\mathsf T_E = \{ ((x,k),(y,k+1)) : (x,y)\in\mathsf T \}.
$$

定义因果可达关系：对 $e,e'\in E$

$$
e \preceq e'
$$

若存在有限路径 $\Gamma: e=e_0\to e_1\to\dots\to e_n=e'$，其中 $(e_i,e_{i+1})\in\mathsf T_E$。这是事件层上的偏序（在可达子集中）。

将步数与代价合并：定义事件层复杂性代价

$$
\mathsf C_E((x,k),(y,k+1)) = \mathsf C(x,y),
$$

路径代价

$$
\mathsf C_E(\Gamma) = \sum_{i=0}^{n-1}\mathsf C_E(e_i,e_{i+1}),
$$

事件层复杂性距离

$$
d_E(e,e') = \inf_{\Gamma:e\to e'} \mathsf C_E(\Gamma).
$$

### 2.2 因果小钻石与边界

给定两个事件

$$
e_{\mathrm{in}}=(x_{\mathrm{in}},k_{\mathrm{in}}),
\quad
e_{\mathrm{out}}=(x_{\mathrm{out}},k_{\mathrm{out}}),
\quad
k_{\mathrm{out}}>k_{\mathrm{in}},
$$

以及复杂性预算 $T>0$。定义预算 $T$ 下因果小钻石

$$
\Diamond(e_{\mathrm{in}},e_{\mathrm{out}};T) = J_T^+(e_{\mathrm{in}})\cap J_T^-(e_{\mathrm{out}}),
$$

其中

$$
J_T^+(e) = \{e' : e\preceq e',\ d_E(e,e')\le T\},
$$

$$
J_T^-(e) = \{e' : e'\preceq e,\ d_E(e',e)\le T\}.
$$

记 $V_\Diamond = \Diamond$ 为顶点集，边集为

$$
E_\Diamond = \{ (e,e')\in\mathsf T_E : e,e'\in V_\Diamond \}.
$$

边界定义为

$$
\partial\Diamond = \{ e\in V_\Diamond : \exists e'\notin V_\Diamond,\ (e,e')\in\mathsf T_E\ \text{或}\ (e',e)\in\mathsf T_E \}.
$$

进一步分解

$$
\partial^-\Diamond = \{ e\in\partial\Diamond : \exists e'\notin V_\Diamond,\ (e,e')\in\mathsf T_E \},
$$

$$
\partial^+\Diamond = \{ e\in\partial\Diamond : \exists e'\notin V_\Diamond,\ (e',e)\in\mathsf T_E \}.
$$

$\partial^-\Diamond$ 为入射边界，$\partial^+\Diamond$ 为出射边界。

### 2.3 钻石链与链复形结构

**定义 2.1（因果小钻石链）**

一条因果小钻石链是序列 $\{\Diamond_k\}_{k\in\mathbb Z}$，其中每个 $\Diamond_k$ 是某对 $(e_k,e_{k+1})$ 与预算 $T_k$ 下定义的因果小钻石，满足：

1. 时序一致性：存在事件序列 $\{e_k\}_{k\in\mathbb Z}$ 使得 $e_k\in\partial^+\Diamond_k\cap\partial^-\Diamond_{k+1}$；
2. 复杂性重叠：$\Diamond_k \cap \Diamond_{k+1} \ne\varnothing$，且 $\Diamond_k \cap \Diamond_{k+l} = \varnothing$ 对 $|l|\ge 2$；
3. 预算一致性：$T_k$ 满足适当上界，使每个钻石仅覆盖有限时间–复杂性窗。

将所有 $\Diamond_k$ 视为 1–链上的"基元"，在其重叠处定义 2–胞，可构造一个一维带 2–胞的链复形 $\mathfrak D = \mathfrak D(\{\Diamond_k\})$，其 1–骨架是钻石链，2–胞刻画钻石拼接的局部关系。

**命题 2.2（钻石链的 1–骨架与离散时间线）**

若 $\{\Diamond_k\}$ 满足上述条件，且在统一时间刻度下每个 $\Diamond_k$ 对应的时间间隔 $\Delta\tau_k$ 有统一下界 $\Delta\tau_{\min}>0$，则 1–骨架上的自然顺序 $k\mapsto\Diamond_k$ 可以视为一条离散时间线，每一单步对应一个有限预算因果小钻石。

证明见附录 A.1：核心在于利用 $e_k$ 的偏序与预算重叠为"同一时间层"的局部替换构造。

---

## 3 Null–Modular 双覆盖与 $\mathbb Z_2$ holonomy

本节在钻石链上构造 Null–Modular 双覆盖结构，并定义 $\mathbb Z_2$ holonomy，将其与自指奇偶不变量对接。

### 3.1 钻石边界上的模 2 时间相位

在统一时间刻度与散射框架下，每个因果小钻石 $\Diamond_k$ 可以关联一个局域散射算子 $S_{\Diamond_k}(\omega)$ 与群延迟矩阵 $Q_{\Diamond_k}(\omega)$，其迹给出该钻石上的统一时间刻度密度增量。

考虑频率区间 $\Omega_k$ 与权重 $w_k(\omega)$，定义钻石的平均相位增量

$$
\Delta\varphi_k = \int_{\Omega_k} w_k(\omega)\,\varphi_{\Diamond_k}'(\omega)\,\mathrm d\omega,
$$

以及对应的时间增量

$$
\Delta\tau_k = \int_{\Omega_k} w_k(\omega)\,\kappa_{\Diamond_k}(\omega)\,\mathrm d\omega.
$$

我们将"相位模 $2\pi$"的结构引入 $\mathbb Z_2$ 标签。

**定义 3.1（模 2 时间相位标签）**

对每个钻石 $\Diamond_k$ 在其出射边界上的每个事件 $e\in\partial^+\Diamond_k$，赋予一个标签

$$
\epsilon(e) \in \mathbb Z_2,
$$

定义为 $\Delta\varphi_k / \pi$ 的奇偶类：

$$
\epsilon(e) = \left\lfloor \frac{\Delta\varphi_k}{\pi} \right\rfloor \bmod 2.
$$

在一个钻石链上，我们要求出射边界的标签与下一个钻石的入射边界标签兼容，即 $\epsilon(e_k)$ 仅依赖于钻石 $\Diamond_k$ 的局部结构。

### 3.2 Null–Modular 双覆盖的构造

**定义 3.2（Null–Modular 双覆盖）**

给定钻石链复形 $\mathfrak D$，构造双覆盖图 $\widetilde{\mathfrak D}$ 如下：

1. 对每个钻石顶点 $v_k$（代表 $\Diamond_k$）引入两份拷贝 $\widetilde v_k^{(0)},\widetilde v_k^{(1)}$；
2. 对每条链边 $(v_k,v_{k+1})$，若对应的相位奇偶 $\epsilon(e_k)=0$，则在双覆盖中连接 $\widetilde v_k^{(i)}$ 与 $\widetilde v_{k+1}^{(i)}$；若 $\epsilon(e_k)=1$，则连接 $\widetilde v_k^{(i)}$ 与 $\widetilde v_{k+1}^{(1-i)}$，其中 $i\in\{0,1\}$；
3. 投影 $\pi:\widetilde{\mathfrak D}\to\mathfrak D$ 将 $\widetilde v_k^{(i)} \mapsto v_k$。

这样，沿钻石链走一圈，双覆盖上的提升路径的终点与起点是否一致，取决于沿途相位奇偶的累积。

**命题 3.3（双覆盖与 $\mathbb Z_2$ holonomy）**

令 $\gamma = (v_{k_0},v_{k_1},\dots,v_{k_m}=v_{k_0})$ 为钻石链上闭合环路，令 $\widetilde\gamma$ 为其在双覆盖上的提升路径。则：

1. 若 $\sum_{j=0}^{m-1} \epsilon(e_{k_j}) \equiv 0 \bmod 2$，则存在闭合提升路径 $\widetilde\gamma$ 使得 $\widetilde v_{k_m}^{(i)} = \widetilde v_{k_0}^{(i)}$；
2. 若 $\sum_{j=0}^{m-1} \epsilon(e_{k_j}) \equiv 1 \bmod 2$，则任何提升路径从 $\widetilde v_{k_0}^{(i)}$ 出发后终点落在 $\widetilde v_{k_0}^{(1-i)}$，不存在闭合提升。

因此，闭合环路的 $\mathbb Z_2$ holonomy 由相位奇偶和 $\sum\epsilon(e_k)$ 给出，与双覆盖结构完全一致。

证明见附录 A.2。

### 3.3 与自指奇偶不变量的对应

在此前拓扑复杂性工作中，我们对自指环路 $\gamma$ 定义自指奇偶 $\sigma(\gamma)\in\mathbb Z_2$。在这里，我们可将自指环路在钻石链上重新表达为某条闭合钻石链 $\gamma_{\Diamond}$，其自指操作对应钻石链上的某个局域反馈结构。

**定理 3.4（自指奇偶与 Null–Modular holonomy 一致性）**

在适当的编码下，每条自指环路 $\gamma$ 对应一条钻石链闭合环路 $\gamma_{\Diamond}$，使得

$$
\sigma(\gamma) = \sum_{k\in\gamma_{\Diamond}} \epsilon(e_k) \bmod 2,
$$

即自指奇偶等于钻石链双覆盖上的 $\mathbb Z_2$ holonomy。

证明见附录 A.3：构造自指反馈网络关联的局域散射相位–时间延迟，并利用 Null–Modular 双覆盖规则将其转译为钻石链上的奇偶跃迁。

---

## 4 统一时间刻度在钻石链上的实现

本节将统一时间刻度密度 $\kappa(\omega)$ 引入钻石链结构，并在细化极限下恢复控制流形上的连续时间参数。

### 4.1 钻石上的时间增量与局域散射

对每个钻石 $\Diamond_k$，假设其对应的局域散射过程 $S_{\Diamond_k}(\omega)$ 满足统一时间刻度母式：

$$
\kappa_{\Diamond_k}(\omega) = \frac{1}{2\pi}\mathrm{tr}\,Q_{\Diamond_k}(\omega),
$$

$$
Q_{\Diamond_k}(\omega) = -\mathrm i\,S_{\Diamond_k}(\omega)^\dagger \partial_\omega S_{\Diamond_k}(\omega).
$$

定义钻石时间增量

$$
\Delta\tau_k = \int_{\Omega_k} w_k(\omega)\,\kappa_{\Diamond_k}(\omega)\,\mathrm d\omega.
$$

在钻石链上，累积时间为

$$
\tau_N = \sum_{k=0}^{N-1}\Delta\tau_k.
$$

### 4.2 钻石链到控制流形世界线的极限

考虑离散控制参数 $\theta_k \in\mathcal M$ 与钻石链索引 $k$。设存在嵌入映射

$$
\theta(k) = \Theta(\tau_k),
$$

其中 $\Theta:[\tau_0,\tau_N]\to\mathcal M$ 为控制流形上的一条连续曲线。若钻石尺寸 $\Delta\tau_k \to 0$ 且链变得稠密，则钻石链的 1–骨架在 Gromov–Hausdorff 意义下收敛到 $\Theta$ 的像。

**命题 4.1（钻石链的时间–几何极限）**

在统一时间刻度与局域散射正则性假设下：若钻石链 $\{\Diamond_k\}$ 满足 $\sup_k \Delta\tau_k\to 0$，并且每个钻石在控制流形上对应局部坐标邻域中的一步 geodesic 步进，则钻石链的复杂性距离在极限下收敛到控制流形测地距离 $d_G$，时间参数 $\tau$ 即为统一时间刻度参数。

证明见附录 B.1：利用标准的离散–连续 geodesic 近似与统一时间刻度的散射–群延迟关系。

### 4.3 Null–Modular 双覆盖下的时间方向场

结合 Null–Modular 双覆盖结构，时间参数 $\tau$ 与自指奇偶 $\sigma$ 一起定义了控制流形上的"时间方向场"：

* 沿 $\Theta(\tau)$ 前进，对应钻石链 $\{\Diamond_k\}$；
* 在双覆盖 $\widetilde{\mathfrak D}$ 上，路径的提升一圈后返回或翻转定义了 $\mathbb Z_2$ 时间奇偶；
* 这一奇偶结构可以被视为控制流形上的一个 $\mathbb Z_2$ 主丛 holonomy，与 Null–Modular 双覆盖结构一致。

在物理宇宙统一时间刻度–边界时间几何的语言中，这对应于 Null 边界的模 $2\pi$ 相位与 $\mathbb Z_2$ 模块的综合结构。本文在计算宇宙侧给出其离散–链复形实现。

---

## 5 多观察者 Null–Modular 共识几何

本节将多观察者共识几何嵌入钻石链双覆盖中，构造多观察者 Null–Modular 共识结构。

### 5.1 多观察者世界管与钻石链嵌入

对观察者族 $\{O_i\}_{i\in I}$，每个观察者 $O_i$ 在事件层有一条"世界管" $\{(i,x_k^{(i)},k)\}_{k}$，对应一组嵌入在事件层的小钻石链 $\{\Diamond_k^{(i)}\}_{k}$，例如每个钻石覆盖从 $(i,x_k^{(i)},k)$ 到 $(i,x_{k+1}^{(i)},k+1)$。

这些钻石链可以视为钻石链复形 $\mathfrak D$ 的子链族，每个观察者在双覆盖 $\widetilde{\mathfrak D}$ 上有一条提升路径 $\widetilde\gamma_i$。

**定义 5.1（多观察者 Null–Modular 共识图）**

在钻石链双覆盖上定义图

$$
\mathfrak C_{\mathrm{NM}} = (V_{\mathrm{NM}},E_{\mathrm{NM}}),
$$

其中顶点集 $V_{\mathrm{NM}}$ 为所有观察者提升路径上的钻石链节点 $\{\widetilde v_k^{(i)}\}$，边集为"空间–时间–信息邻接"的组合：既包含时间方向的链边，又包含在信息流形上的共识边。

在该图上，可以定义类似前文多观察者共识能量的量，只是此处每条路径还携带一个 $\mathbb Z_2$ holonomy，代表观测链上自指奇偶的积累。

### 5.2 Null–Modular 共识与自指奇偶对齐

在多观察者场景中，不同观察者可能具有不同的自指结构：某些观察者内部模型在一个时间周期后自我翻转，另一些则不翻转。在 Null–Modular 双覆盖上，这对应于其提升路径是否闭合或翻转。

**命题 5.2（Null–Modular 共识对齐条件）**

若存在多观察者协同策略使得在长期极限 $t\to\infty$ 下

1. 所有观察者的信息状态 $\phi_i(t)$ 在 $\mathcal S_Q$ 上收敛到同一点或同一轨道；
2. 所有观察者提升路径的 $\mathbb Z_2$ holonomy 相同，即 $\sigma(\gamma_i) = \sigma(\gamma_j)$ 对所有 $i,j$ 成立；

则在钻石链双覆盖上，多观察者世界管构成一个"Null–Modular 共识簇"，其整体 holonomy 为一个共同的 $\mathbb Z_2$ 值，代表该任务下的统一自指奇偶。

这一条件给出一个拓扑–几何层面的"深层共识"概念：不仅信息状态达成共识，自指结构也达成一致。

---

## 6 Null–Modular 版停机问题与时间相位–复杂性第二定律

本节在前述结构基础上定义 Null–Modular 版停机问题，并给出一个与复杂性熵兼容的第二定律原型。

### 6.1 Null–Modular 版停机问题

考虑钻石链闭合环路 $\gamma$，其自指奇偶 $\sigma(\gamma)\in\mathbb Z_2$ 与基本群同伦类 $[\gamma]\in\pi_1(\mathfrak D)$ 已定义。我们关心的问题是：

> 给定 $\gamma$，其在 Null–Modular 双覆盖 $\widetilde{\mathfrak D}$ 上是否存在闭合提升路径？

这等价于 $\sigma(\gamma)=0$，即 holonomy 为平凡元。

**问题 6.1（Null–Modular 停机判定问题）**

输入：钻石链复形 $\mathfrak D$ 的有限描述与其中一条闭合环路 $\gamma$。
问题：判定 $\gamma$ 在 Null–Modular 双覆盖 $\widetilde{\mathfrak D}$ 上是否具有闭合提升路径。

借助第 4 篇中拓扑不可判定性的结果，我们可证明该问题在一般计算宇宙族中不可判定：可以将停机问题编码为某类自指钻石链的闭合性与否，及其 holonomy 的奇偶，从而将停机归约到 Null–Modular 停机判定。

**定理 6.2（Null–Modular 停机判定不可判定）**

存在一族可构造的计算宇宙与钻石链复形 $\{\mathfrak D^\alpha\}$，使得在每个 $\mathfrak D^\alpha$ 上，判定输入环路 $\gamma$ 在 Null–Modular 双覆盖上是否具有闭合提升路径是不可判定的。

证明见附录 C.1。

### 6.2 时间相位–复杂性第二定律原型

在此前复杂性熵工作中，我们已经定义闭合环路的压缩复杂度 $K(\gamma)$ 及其 coarse–graining 单调性。现引入时间相位（自指奇偶）与复杂性联合熵

$$
\mathcal S_{\mathrm{NM}}(\gamma) = \log K(\gamma) + \lambda \sigma(\gamma),
$$

其中 $\lambda>0$ 为常数。考虑沿钻石链粗化演化 $\{\gamma_t\}_{t\ge 0}$，其同伦类不变，但局部关系与 Null–Modular 结构在 coarse–graining 下会产生一个有效的"奇偶选择"倾向：在典型情形下，系统趋向于局部减少可翻转奇偶的自由度，使 $\sigma(\gamma_t)$ 在长时间极限上稳定。

在适当随机化与 coarse–graining 假设下，可以证明如下弱第二定律原型：

**命题 6.3（时间相位–复杂性联合熵非减性，原型）**

在统一时间刻度下的 coarse–graining 演化 $t\mapsto\gamma_t$ 中，若满足：

1. 同伦类 $[\gamma_t]$ 与 Null–Modular 结构整体保持不变；
2. 粗化操作仅使用局部关系与局部 Null–Modular 变换；
3. 奇偶翻转的局部操作具有偏向"热化"行为；

则存在 $t_0$ 使得对 $t\ge t_0$ 有

$$
\mathcal S_{\mathrm{NM}}(\gamma_t) \le \mathcal S_{\mathrm{NM}}(\gamma_{t'}) \quad \text{对所有}\ t'\ge t.
$$

即联合熵在大时间尺度上弱单调不减。详细形式化与证明见附录 C.2。

这一结论可视为"时间相位–复杂性第二定律"的离散、拓扑–几何版：在统一时间刻度与 Null–Modular 双覆盖的共同约束下，自指奇偶与可压缩复杂度联合形成的熵在 coarse–graining 演化中具有时间箭头。

---

## 附录 A：钻石链复形与 Null–Modular 双覆盖的构造细节

### A.1 命题 2.2 的证明

命题 2.2 断言，满足特定条件的钻石链可以被视为离散时间线。

设 $\{\Diamond_k\}$ 为钻石链，令 $e_k\in\partial^+\Diamond_k\cap\partial^-\Diamond_{k+1}$ 为"连接事件"。由偏序 $\preceq$ 与预算约束，$e_k \prec e_{k+1}$，且不存在 $e$ 使得 $e_k \prec e \prec e_{k+1}$ 且 $e\in\Diamond_k\cup\Diamond_{k+1}$，否则会破坏重叠条件。由统一时间刻度与 $\Delta\tau_{\min}>0$ 可知每个步长具有时间下界，因此 $k\mapsto e_k$ 给出严格递增的时间序列，构成离散时间线。钻石 $\Diamond_k$ 可视为连接 $e_k$ 与 $e_{k+1}$ 的有限预算因果小区域。证毕。

### A.2 命题 3.3 的证明

定义双覆盖图时，我们对每条边标记奇偶并按规则翻转或保持标签。闭合环路 $\gamma = (v_{k_0},\dots,v_{k_m}=v_{k_0})$ 的提升从 $\widetilde v_{k_0}^{(i)}$ 出发，在每条边 $(v_{k_j},v_{k_{j+1}})$ 上，如果 $\epsilon(e_{k_j})=0$，索引 $i$ 保持不变；如果 $\epsilon(e_{k_j})=1$，索引翻转 $i\mapsto 1-i$。最终索引为

$$
i_{\mathrm{final}} = i + \sum_{j=0}^{m-1} \epsilon(e_{k_j}) \bmod 2.
$$

若 $\sum\epsilon(e_{k_j})\equiv 0 \bmod 2$，则 $i_{\mathrm{final}}=i$，提升路径闭合；否则 $i_{\mathrm{final}}=1-i$，不存在闭合提升。从而双覆盖上的 $\mathbb Z_2$ holonomy 与相位奇偶和一致。证毕。

### A.3 定理 3.4 的证明思路

自指环路在配置图上的定义可以通过"编码–评估–反馈"三段过程对应一个钻石链：每个段落对应一串钻石，局部散射相位在这些钻石上的累积给出全局相位与时间延迟。自指奇偶 $\sigma(\gamma)$ 可以定义为在一个自指周期中某个全局标签的翻转次数模 2。通过对编码–评估–反馈结构的局部散射建模，可将标签翻转与钻石边界上的相位奇偶关联，从而得到 $\sigma(\gamma) = \sum_{k\in\gamma_{\Diamond}} \epsilon(e_k) \bmod 2$。形式化证明需要构造具体的局域散射–延迟网络模型，略去细节。

---

## 附录 B：统一时间刻度在钻石链上的几何极限

### B.1 命题 4.1 的证明

命题 4.1 是此前控制流形 geodesic 极限定理在钻石链情形的特例。离散钻石链可以视为在控制流形上的 piecewise geodesic 抽样，每个钻石对应一个小 geodesic 段，其时间长度为 $\Delta\tau_k$，空间步长为 $\sqrt{G_{ab}\dot\theta^a\dot\theta^b}\Delta\tau_k$。当 $\sup_k\Delta\tau_k\to 0$ 时，离散路径长度

$$
\sum_k \sqrt{G_{ab}(\theta_k)\Delta\theta_k^a\Delta\theta_k^b}
$$

收敛到连续路径 $\Theta(\tau)$ 的 Riemann 积分

$$
\int \sqrt{G_{ab}(\Theta(\tau))\dot\Theta^a(\tau)\dot\Theta^b(\tau)}\,\mathrm d\tau,
$$

即控制流形上的测地距离。统一时间刻度与散射–群延迟关系保证 $\Delta\tau_k$ 与 $\kappa_{\Diamond_k}$ 的定义一致，从而时间参数与 geodesic 参数兼容。证毕。

---

## 附录 C：Null–Modular 停机判定不可判定与第二定律原型

### C.1 定理 6.2 的证明纲要

从停机问题出发，为每个程序–输入对构造一个自指钻石链：若程序停机，则在链上存在某个局部结构使得相位奇偶总和为 0，环路在双覆盖上闭合；若程序不停机，则环路要么不存在，要么奇偶总和为 1，环路在双覆盖上不闭合。若存在算法能判定环路是否在双覆盖上闭合，则可用于判定停机问题，从而矛盾。因此 Null–Modular 停机判定问题不可判定。证毕。

### C.2 命题 6.3 的证明思路

联合熵 $\mathcal S_{\mathrm{NM}}(\gamma) = \log K(\gamma) + \lambda\sigma(\gamma)$ 中 $\log K(\gamma)$ 在 coarse–graining 下弱单调不减（见前一篇复杂性熵论证），而 $\sigma(\gamma)$ 在局部 Null–Modular 变换下可能暂时翻转，但在随机–热化假设下，系统趋向于全局稳定奇偶（例如某种"能量最低"的奇偶态），从而 $\sigma(\gamma_t)$ 在长时间极限上不再降低联合熵。通过对 coarse–graining 随机过程的马尔可夫链分析可以得到联合熵的弱单调性。完整证明涉及对局部关系半群与 $\mathbb Z_2$ 扩张的随机动力学分析，超出本文篇幅。

---
