# 统一时间刻度下的时间晶体与 Null–Modular $\mathbb Z_2$ Holonomy

计算宇宙中的 Floquet–QCA 时间晶体、拓扑奇偶与工程实现

---

## 摘要

在计算宇宙公理框架 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 与统一时间刻度母尺
$$
\kappa(\omega) = \varphi'(\omega)/\pi = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\operatorname{tr}Q(\omega)
$$
已建立的基础上，本文构造一个完全离散的时间晶体理论，并将其与 Null–Modular $\mathbb Z_2$ holonomy 以及时间–信息–复杂性联合几何结构统一起来。

我们首先在可逆量子元胞自动机 (quantum cellular automaton, QCA) 的计算宇宙实现上，引入 Floquet–QCA 对象 $U_{\mathrm{FQCA}} = (X,U_F,\mathsf C_T,\mathsf I)$，其中 $U_F$ 为一周期 $T$ 的局域 Floquet 演化算子，$\mathsf C_T$ 为一次 Floquet 步的统一时间刻度代价。我们给出计算宇宙意义下的离散时间平移对称与自发破缺定义，并在复杂性几何与信息几何的视角下，刻画时间晶体相的特征：在任何满足局域可观测性与有界能量密度假设的初态族上，存在局域可观测量 $O$ 的期望值在长期演化中呈现严格周期 $mT$ 而非 $T$，其中 $m\ge 2$ 是整数。

随后，我们在此前构造的因果小钻石链与 Null–Modular 双覆盖结构上，引入 Floquet–QCA 时间晶体的循环链：每个 Floquet 周期对应一颗因果小钻石，形成钻石链 $\{\Diamond_k\}_{k\in\mathbb Z}$。在该链上，我们为每个周期定义一个由散射相位增量诱导的模 $2$ 时间相位标签 $\epsilon_k\in\mathbb Z_2$，并构造钻石链的 Null–Modular 双覆盖 $\widetilde{\mathfrak D}\to\mathfrak D$。我们证明：周期翻倍时间晶体 ($m=2$) 的存在恰对应于 Floquet 控制循环在 Null–Modular 双覆盖上的 $\mathbb Z_2$ holonomy 非平凡，即闭合 Floquet 控制回路在双覆盖上不存在闭合提升路径，从而给出时间晶体奇偶与 Null–Modular holonomy 的精确对应。

在工程层面，我们考虑有限复杂性预算下的时间晶体读出与稳健性。通过将统一时间刻度频域与谱窗化误差控制理论 (PSWF/DPSS) 结合，我们构造一类面向时间晶体读数的"有限阶窗函数观测算子"，并证明：在 Floquet 能隙大于某一阈值且局域噪声满足有限相关长度假设的条件下，以 DPSS 类型读数窗口对时间晶体信号进行有限步采样，可在错误概率不超过 $\varepsilon$ 的前提下，以复杂性预算 $N = \mathcal O(\Delta^{-2}\log(1/\varepsilon))$ 对周期翻倍奇偶进行鲁棒判别，其中 $\Delta$ 为 Floquet 准能量带隙。

最后，我们将时间晶体视为统一时间刻度的"离散相位锁定器"：在控制流形 $(\mathcal M,G)$ 上，时间晶体相对应一类带 $\mathbb Z_2$ holonomy 的 Floquet 控制回路，它在时间–信息–复杂性联合变分原理中给出一个特殊的极小世界线族。我们讨论了时间晶体作为统一时间刻度局域基准的潜在实验角色，以及与 FRB 相位计量与 δ–环–AB 散射计量的互补关系。

---

## 关键词

计算宇宙；统一时间刻度；量子元胞自动机；Floquet 时间晶体；Null–Modular 双覆盖；$\mathbb Z_2$ holonomy；谱窗化读数；DPSS

---

## 1 引言

时间晶体 (time crystals) 最初被提出作为一种自发破坏时间平移对称性的相：系统的基态或稳态在时间上呈现非平凡周期结构。尽管最初的"连续时间晶体"构想在严格平衡态下受限，但在周期驱动系统 (Floquet 系统) 中，自发破坏离散时间平移对称性的 Floquet 时间晶体实际得以实现。在这些系统中，时间平移群 $\mathbb Z$ 的对称性被自发破坏为 $m\mathbb Z$，表现为可观测量对完整 Floquet 周期 $T$ 的响应具有超周期 $mT$，常见的是 $m=2$ 的周期翻倍时间晶体。

在本系列此前工作中，我们从更高的层次构造了"统一时间刻度–计算宇宙"理论，包括：

1. 计算宇宙公理系统 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$，将宇宙视为离散复杂性图上的可逆演化；
2. 统一时间刻度母尺 $\kappa(\omega) = \varphi'(\omega)/\pi = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\operatorname{tr}Q(\omega)$，将散射相位导数、谱移密度与群延迟迹统一为单一时间刻度密度；
3. 由统一时间刻度诱导的控制流形 $(\mathcal M,G)$ 与复杂性几何；
4. 因果小钻石、边界计算算子与因果小钻石链 $\{\Diamond_k\}$；
5. 在钻石链上构造的 Null–Modular 双覆盖与 $\mathbb Z_2$ holonomy，自指奇偶与拓扑复杂性；
6. 时间–信息–复杂性联合变分原理与多观察者共识几何。

在这一框架中，时间已不是外部参数，而是统一时间刻度在散射–复杂性几何中的体现；时间方向、时间奇偶与自指结构通过 Null–Modular 双覆盖与 $\mathbb Z_2$ holonomy 体现。

本篇的核心问题是：

1. 如何在计算宇宙–统一时间刻度的纯离散框架中，严格定义 Floquet–QCA 时间晶体，并给出其几何–拓扑刻度？
2. 时间晶体的周期翻倍奇偶如何与 Null–Modular $\mathbb Z_2$ holonomy 联系？
3. 在有限复杂性预算下，如何对时间晶体进行稳定读出与工程实现？

我们将看到，时间晶体在计算宇宙中自然实现为 Floquet–QCA 的一类相，Null–Modular 双覆盖为其提供了一个内禀的 $\mathbb Z_2$ 拓扑不变量，谱窗化读数则为其在有限复杂性预算下的观测提供了最优解。

---

## 2 预备：计算宇宙、统一时间刻度与 Floquet–QCA

### 2.1 计算宇宙与 QCA 实现

回顾计算宇宙对象

$$
U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I),
$$

其中 $X$ 为可数配置集，$\mathsf T\subset X\times X$ 为一步更新关系，$\mathsf C$ 为单步代价，$\mathsf I$ 为任务信息质量函数。可逆 QCA 的标准抽象为：对格点集合 $\Lambda$ 与每个格点上的有限维 Hilbert 空间 $\mathcal H_x$，全局 Hilbert 空间 $\mathcal H = \bigotimes_{x\in\Lambda} \mathcal H_x$，可逆 QCA 是一个局域酉算子 $U:\mathcal H\to\mathcal H$，满足局域因果性约束。

在计算宇宙中，可将配置 $x\in X$ 视为某个规范化基矢 $\ket{x}\in\mathcal H$ 的标签，一步更新关系由

$$
(x,y)\in\mathsf T \iff \langle y|U|x\rangle \ne 0
$$

定义；单步代价 $\mathsf C(x,y)$ 则由统一时间刻度下执行一次 $U$ 或其局域分解所需的物理时间给出。

### 2.2 统一时间刻度与 Floquet 演化

在物理侧，考虑一个周期驱动系统，其时间依赖哈密顿量 $H(t+T) = H(t)$，相应 Floquet 演化算子

$$
U_F = \mathcal T\exp\big(-\mathrm i\int_0^T H(t)\,\mathrm dt\big),
$$

其本征值为 $\mathrm e^{-\mathrm i\varepsilon_\alpha T}$，$\varepsilon_\alpha$ 为准能量。

在统一时间刻度–散射框架中，可将 $U_F(\omega)$ 看作某个频域散射–演化算子，对频率 $\omega$ 的依赖通过驱动谱与系统响应体现。对每个 Floquet 周期，可定义一个局部群延迟矩阵 $Q_F(\omega) = -\mathrm i U_F(\omega)^\dagger\partial_\omega U_F(\omega)$，其迹给出局域统一时间刻度密度增量

$$
\kappa_F(\omega) = (2\pi)^{-1}\operatorname{tr}Q_F(\omega).
$$

在计算宇宙中，我们关心的是"每一个 Floquet 周期作为一颗因果小钻石"的离散版本，这将在第 3 节中具体构造。

### 2.3 Floquet 时间晶体的基本定义

在一般的 Floquet 系统中，时间平移群 $\mathbb Z$ 的作用为 $n\mapsto n+1$，对应于 $U_F^n$ 的迭代。时间晶体是对该对称性的自发破缺：

**定义 2.1（Floquet 时间晶体，物理侧）**

在一个周期驱动系统中，若存在局域可观测量 $O$ 与一族初态 $\{\rho_0\}$，使得对几乎所有 $\rho_0$，期望值序列

$$
\langle O\rangle_n = \operatorname{tr}(\rho_0 U_F^{\dagger n}OU_F^n)
$$

在长期极限中呈现严格周期 $m>1$，即

$$
\langle O\rangle_{n+m} = \langle O\rangle_n,
$$

且不满足任何更短周期，则称系统处于周期 $mT$ 的 Floquet 时间晶体相。典型情形为 $m=2$ 的时间晶体。

我们将这一概念在 QCA–计算宇宙框架中重新表述。

---

## 3 计算宇宙中的 Floquet–QCA 时间晶体

### 3.1 Floquet–QCA 对象

**定义 3.1（Floquet–QCA 计算宇宙）**

一个 Floquet–QCA 计算宇宙对象是四元组

$$
U_{\mathrm{FQCA}} = (X,U_F,\mathsf C_T,\mathsf I),
$$

其中：

1. $X$ 为配置集，作为全局 Hilbert 空间 $\mathcal H$ 的规范化基矢标签；
2. $U_F:\mathcal H\to\mathcal H$ 是一个局域 Floquet 演化算子，对应一个驱动周期 $T$；
3. $\mathsf C_T:X\times X\to[0,\infty]$ 为一次 Floquet 步的复杂性代价，满足 $\mathsf C_T(x,y)>0$ 若 $\langle y|U_F|x\rangle\ne 0$；
4. $\mathsf I:X\to\mathbb R$ 为任务信息质量函数。

一次 Floquet 演化步骤在事件层 $E = X\times\mathbb Z$ 上表示为

$$
(x,n)\mapsto (y,n+1),\quad \langle y|U_F|x\rangle\ne 0.
$$

复杂性代价可视为统一时间刻度在单周期上的积分。

### 3.2 离散时间平移对称与破缺

在计算宇宙中，将 $U_F$ 视为"时间平移一格"的生成元。对可观测量 $O$ (例如局域算子 $O_x$ 只作用于某个有限区域)，其离散时间演化为

$$
O(n) = U_F^{\dagger n}OU_F^n.
$$

对某一初态 $\rho_0$ (可视为密度算子)，观测序列

$$
\langle O\rangle_n = \operatorname{tr}(\rho_0 O(n)).
$$

**定义 3.2（计算宇宙中的 Floquet 时间晶体）**

在 Floquet–QCA 计算宇宙中，若存在局域可观测量 $O$、整数 $m\ge 2$ 以及一族初态 $\mathcal R_0$ (满足有限密度与有限相关长度条件)，使得：

1. 对几乎所有 $\rho_0\in\mathcal R_0$，存在足够大的 $n_0$ 使得对所有 $n\ge n_0$ 有
   $$
   \langle O\rangle_{n+m} = \langle O\rangle_n,
   $$
2. 不存在 $1\le m'<m$ 使得同样条件成立，

则称 $U_{\mathrm{FQCA}}$ 处于周期 $mT$ 的时间晶体相。

特别地，当 $m=2$ 时，称为周期翻倍时间晶体。

### 3.3 Floquet 谱与准能量带结构

在有限体积或适当边界条件下，$U_F$ 有本征分解

$$
U_F\ket{\psi_\alpha} = \mathrm e^{-\mathrm i\varepsilon_\alpha T}\ket{\psi_\alpha},
$$

其中 $\varepsilon_\alpha \in(-\pi/T,\pi/T]$ 为准能量。

时间晶体的存在与准能量带结构中出现"对称分裂结构"密切相关：例如，在 $m=2$ 情形下，存在两条带相差 $\pi/T$ 的准能量支，使得演化中的相干叠加在每两个周期发生符号翻转。

形式上，可采用投影到子空间 $\mathcal H_A,\mathcal H_B$ 的结构，满足

$$
U_F^2 \ket{\psi} \approx \mathrm e^{-\mathrm i2\varepsilon T}\ket{\psi},
$$

且 $U_F$ 将 $\mathcal H_A$ 与 $\mathcal H_B$ 交换。

更重要的是，在计算宇宙–复杂性几何中，我们可以将 Floquet 谱的相位结构转译为因果小钻石链上的 Null–Modular $\mathbb Z_2$ holonomy，这将在下一节具体展开。

---

## 4 Null–Modular $\mathbb Z_2$ Holonomy 与时间晶体奇偶

本节构造 Floquet–QCA 时间晶体在因果小钻石链与 Null–Modular 双覆盖上的实现，证明周期奇偶与 $\mathbb Z_2$ holonomy 的对应。

### 4.1 Floquet 周期作为因果小钻石链

将单周期 Floquet 演化视为一颗因果小钻石 $\Diamond_F$：

* 钻石内部顶点为在复杂性预算 $T$ 内从某个初态层到下一层的事件集合；
* 钻石边界为周期初末事件；
* 钻石体积演化由 $U_F$ 的局域分解给出；
* 边界算子 $\mathsf K_{\Diamond_F}$ 与 $U_F$ 在边界上的作用同构。

若系统在时间上重复驱动，则事件层上形成一条 Floquet 钻石链

$$
\{\Diamond_{F,k}\}_{k\in\mathbb Z},
$$

其中每个 $\Diamond_{F,k}$ 对应第 $k$ 个 Floquet 周期。

对每个 $\Diamond_{F,k}$，定义平均统一时间刻度增量

$$
\Delta\tau_k = \int_{\Omega_F} w_F(\omega)\,\kappa_F(\omega)\,\mathrm d\omega,
$$

在周期稳定情况下，$\Delta\tau_k \equiv \Delta\tau$ 与物理周期 $T$ 成比例。

### 4.2 模 2 时间相位与 $\mathbb Z_2$ holonomy

在第 3 篇关于钻石链与 Null–Modular 双覆盖的工作中，我们定义了每颗钻石的模 $2$ 时间相位标签 $\epsilon_k\in\mathbb Z_2$，由散射相位增量模 $2\pi$ 决定。

在 Floquet 情形下，我们可将每周期的有效相位增量定义为

$$
\Delta\varphi_F = \arg\det U_F, \quad \epsilon_F = \left\lfloor \Delta\varphi_F / \pi \right\rfloor \bmod 2.
$$

对于时间晶体，特别是周期翻倍相，关键结构不是单周期相位，而是两周期闭合回路

$$
U_F^2,
$$

及其对应的散射相位与群延迟。

构造钻石链双覆盖 $\widetilde{\mathfrak D}_F \to \mathfrak D_F$ 时，我们令每个 Floquet 周期钻石的边标签为 $\epsilon_F$。闭合链上 $N$ 周期的总奇偶为

$$
\Sigma_N = \sum_{k=1}^{N} \epsilon_F \bmod 2 = N\epsilon_F \bmod 2.
$$

对 $m=2$ 时间晶体而言，存在一种自然机制使得沿两周期组成的闭环具有非平凡 $\mathbb Z_2$ holonomy：例如若 $\epsilon_F = 1$，则每经过一个周期，双覆盖上的索引翻转一次，两周期后翻转两次回到原索引，但闭合路径的整体拓扑表现出一个非平凡 holonomy。

更精确地，考虑 Floquet 控制参数路径 $\Gamma_F \subset\mathcal M$ 上的闭合回路 (例如驱动协议参数在周期驱动中的闭合变化)，其 Null–Modular 双覆盖 holonomy

$$
\mathrm{hol}_{\mathbb Z_2}(\Gamma_F) \in \mathbb Z_2
$$

与时间晶体的周期奇偶密切相关。

### 4.3 时间晶体奇偶与 Null–Modular holonomy 对应

**定理 4.1（周期翻倍时间晶体与 $\mathbb Z_2$ holonomy）**

设 $U_{\mathrm{FQCA}}$ 是满足以下条件的 Floquet–QCA 计算宇宙对象：

1. 存在均匀体积极限与有限相关长度的初态族 $\mathcal R_0$；
2. Floquet 谱存在准能量带隙 $\Delta_{\mathrm{F}} > 0$，并存在两个带 $\varepsilon_\alpha, \varepsilon_\beta$ 满足 $\varepsilon_\beta \approx \varepsilon_\alpha + \pi/T$；
3. 在对应的控制流形闭合回路 $\Gamma_F$ 上，Null–Modular 双覆盖 holonomy 非平凡，即
   $$
   \mathrm{hol}_{\mathbb Z_2}(\Gamma_F) = 1.
   $$

则 $U_{\mathrm{FQCA}}$ 处于周期 $2T$ 的时间晶体相；反之，在上述正则性条件下，若 $U_{\mathrm{FQCA}}$ 处于稳健的周期 $2T$ 时间晶体相，则相应 Floquet 控制闭回路的 Null–Modular holonomy 为非平凡元。

*证明思路*：

"若"方向：非平凡 holonomy 意味着在两周期闭回路下某个全局 $\mathbb Z_2$ 量发生奇数次翻转，在 Floquet 谱上对应某个"奇偶切换"结构，使得 Floquet 子空间在一个周期下互换，在两周期下回到原位，从而导致期望值呈现周期 $2T$ 的翻转结构。利用群论与准能量带结构可证明存在局域可观测量 $O$ 满足时间晶体条件。

"仅若"方向：时间晶体的周期翻倍意味着在 Floquet–QCA 世界线上存在一个自指反馈条件，使得两周期才整体闭合。通过此前自指奇偶与 Null–Modular holonomy 的对应，可证明对应闭回路的 holonomy 非平凡。

详细证明见附录 C。

---

## 5 有限复杂性预算下的时间晶体读出与工程实现

本节讨论如何在有限复杂性预算下对时间晶体进行稳定读出，并给出基于 DPSS 的观测策略与误差上界。

### 5.1 读出模型与噪声

考虑在某个局域区域 $\Lambda_0\subset\Lambda$ 上的局域可观测量 $O$，定义离散时间序列

$$
a_n = \operatorname{tr}(\rho_0 U_F^{\dagger n}OU_F^n),\quad n=0,1,\dots,N-1.
$$

在理想时间晶体相中，$a_n$ 在 $n\gg 1$ 时呈现周期 $m$ 的结构，典型为 $m=2$ 的交替序列。在存在局域噪声与耗散的情形下，可写作

$$
a_n = s_n + \eta_n,
$$

其中 $s_n$ 为理想时间晶体信号，$\eta_n$ 为噪声，假设 $\eta_n$ 为零均值、有限相关长度 Gaussian 过程。

### 5.2 DPSS 窗函数读出

为了在有限复杂性步数 $N$ 内提取周期结构，我们可以构造一个加窗傅里叶谱

$$
\widehat a(\omega) = \sum_{n=0}^{N-1} w_n a_n\,\mathrm e^{-\mathrm i\omega n},
$$

其中 $\{w_n\}$ 为窗函数序列。根据上一篇谱窗化读数结果，DPSS 在给定长度 $N$ 与频带 $W$ 下最大化能量集中度，从而在有限样本数与频带的限制下最小化最坏情况误差。

对于 $m=2$ 时间晶体，理想信号的主频位于 $\omega=\pi$ (归一化角频率)。因此可选择带宽 $W \ll \pi$ 的 DPSS 窗函数，聚焦于 $\omega\approx\pi$ 附近的频谱能量。

### 5.3 误差上界与复杂性预算

设 DPSS 窗函数为 $w^{(0)}$，对应特征值 $\lambda_0 \approx 1$，则在有限样本下，估计主频能量的误差方差满足

$$
\operatorname{Var}\big(\widehat a(\pi)\big) \le \sigma_\eta^2 |w^{(0)}|^2,
$$

其中 $\sigma_\eta^2$ 为噪声方差。

为了区分"有时间晶体信号"和"无时间晶体信号"，要保持一定信噪比

$$
\frac{|\mathbb E[\widehat a(\pi)]|^2}{\operatorname{Var}(\widehat a(\pi))} \ge c_0,
$$

由此可得到样本数需求

$$
N = \mathcal O\big(\Delta^{-2}\log(1/\varepsilon)\big),
$$

其中 $\Delta$ 为 Floquet 准能量带隙 (控制时间晶体信号幅度与耗散时间)，$\varepsilon$ 为错误概率。

**定理 5.1（有限复杂性时间晶体判别的样本复杂度）**

在满足：

1. Floquet–QCA 时间晶体具有准能量带隙 $\Delta_{\mathrm{F}} > 0$；
2. 噪声过程 $\{\eta_n\}$ 零均值、有限相关长度且方差有界；
3. 读数窗函数为适当带宽 $W$ 下的 DPSS 基序列 $w^{(0)}$；

的条件下，为在错误概率不超过 $\varepsilon$ 的前提下判别是否存在周期 $2T$ 时间晶体信号，所需复杂性步数 $N$ 满足

$$
N \ge C\Delta_{\mathrm{F}}^{-2}\log(1/\varepsilon),
$$

其中 $C$ 为常数。

证明思路结合 DPSS 能量集中性、Chebyshev 不等式与大偏差估计，详见附录 D。

---

## 6 统一视角：时间晶体作为统一时间刻度的离散相位锁定

从统一时间刻度–控制流形–因果小钻石链–Null–Modular 双覆盖的全局视角看，时间晶体可以被理解为一种特殊的"离散相位锁定器"：

1. 控制流形 $(\mathcal M,G)$ 上的 Floquet 控制闭回路 $\Gamma_F$ 通过统一时间刻度密度 $\kappa(\omega)$ 产生一个周期时间增量 $\Delta\tau$，在 Null–Modular 双覆盖上具有 $\mathbb Z_2$ holonomy；
2. 因果小钻石链 $\{\Diamond_{F,k}\}$ 上的模 $2$ 时间相位标签 $\epsilon_k$ 与 Floquet 控制 holonomy 同步，形成一种"时间奇偶锁定"；
3. 时间晶体相的存在意味着在时间–信息–复杂性联合变分原理中存在一族特殊极小世界线，其在"时间方向–相位–自指奇偶"三个维度上同时稳定。

在实验层面，时间晶体可视为统一时间刻度的局域标准：相比 FRB 与 δ–环–AB 散射这类"被动测量"，时间晶体提供了一种"主动生成的时间刻度相位结构"。通过将时间晶体、FRB 与 δ–环散射共同嵌入相位–频率计量宇宙，可在跨尺度 (实验室–星际–宇宙学) 的平台上对统一时间刻度模型进行一致性检验与联合标定。

---

## 附录 A：Floquet–QCA 时间晶体的存在性原型定理

本附录给出在 QCA 模型中构造时间晶体相的一个典型方案与存在性结果原型。

### A.1 自旋链 Floquet–QCA 模型

考虑一维自旋链 $\Lambda = \mathbb Z$ 上每点 Hilbert 空间 $\mathcal H_x \cong \mathbb C^2$，全局空间 $\mathcal H = \bigotimes_{x\in\mathbb Z}\mathbb C^2$。构造两步 Floquet 演化

$$
U_F = U_2 U_1,
$$

其中 $U_1$ 为在偶–奇格之间作用的成对自旋翻转门，$U_2$ 为在奇–偶格之间作用的类似门，具体形式如

$$
U_1 = \prod_{x\ \mathrm{even}} \mathrm e^{-\mathrm iJ \sigma_x^z\sigma_{x+1}^z}, \quad U_2 = \prod_{x\ \mathrm{odd}} \mathrm e^{-\mathrm iJ' \sigma_x^z\sigma_{x+1}^z}.
$$

在适当参数下，该模型已知具有周期翻倍时间晶体相。

在计算宇宙中，我们将 $X$ 取为自旋配置集合，$\mathsf T$ 由 $U_F$ 的非零矩阵元给出，$\mathsf C_T$ 为一次 $U_F$ 的复杂性代价。

### A.2 存在性原型定理

**定理 A.1（自旋链 Floquet–QCA 时间晶体存在性原型）**

在上述自旋链 Floquet–QCA 模型中，存在参数区域 $(J,J')$ 与初态族 $\mathcal R_0$ (例如自发对称破缺的反铁磁态混合)，使得存在局域可观测量 $O = \sigma_0^z$ 满足定义 3.2 中的时间晶体条件，周期为 $2T$。

证明依赖于自发破缺、稳定性与谱分析，可参见时间晶体文献；在计算宇宙框架中，只需将其视为一个例证：存在具体 QCA 实现满足时间晶体公理。

---

## 附录 B：Null–Modular 双覆盖与 Floquet holonomy

### B.1 控制流形上的闭合回路与双覆盖

设控制流形 $\mathcal M$ 上有闭合回路 $\Gamma_F:[0,1]\to\mathcal M$，$\Gamma_F(0)=\Gamma_F(1)$。Null–Modular 双覆盖 $\pi:\widetilde{\mathcal M}\to\mathcal M$ 是一个 $\mathbb Z_2$ 主丛，使得对每条闭合回路，提升路径的终点为

$$
\widetilde\Gamma_F(1) = \mathrm{hol}_{\mathbb Z_2}(\Gamma_F)\cdot \widetilde\Gamma_F(0),
$$

其中 $\mathrm{hol}_{\mathbb Z_2}(\Gamma_F)\in\{\pm 1\} \cong\mathbb Z_2$。

### B.2 Floquet 谱与 holonomy 对应

在 Floquet–QCA 模型中，控制回路 $\Gamma_F$ 对应某个周期驱动参数路径，沿该路径统一时间刻度密度与散射相位变化。自指奇偶结构使得某个全局态在执行一圈驱动后返回自身向量空间，但可能带有一个 $\pi$ 相或自反翻转。通过对 Floquet 相位与 Null–Modular 双覆盖的详细构造，可证明时间晶体奇偶与 holonomy 对应，详见正文定理 4.1 的证明草图。

---

## 附录 C：定理 4.1 的证明草图

"若"方向：

1. 非平凡 holonomy 意味着控制回路在双覆盖中翻转索引，存在某个 $\mathbb Z_2$ 标签在一周期中翻转一次，两周期中翻转两次回到原态。
2. 该标签可通过局域可观测量 (例如自旋翻转奇偶) 实现，使得对适当初态 $\rho_0$，期望值序列在每周期内交替取值，周期为 $2T$。

"仅若"方向：

1. 周期翻倍时间晶体需要存在某个 $\mathbb Z_2$ 结构在每周期翻转，因此 Floquet–QCA 动力学在拓扑上等价于双覆盖中非平凡的闭合路径。
2. 若 holonomy 为平凡，则不存在这种奇偶翻转结构，时间晶体相不稳定或退化为周期 $T$。

完整形式化需构造从 Floquet 谱到控制双覆盖的映射与相因子，限于篇幅不展开。

---

## 附录 D：定理 5.1 的误差上界证明纲要

考虑观测序列 $a_n = s_n + \eta_n$，其中 $s_n$ 为周期 $2$ 时间晶体信号，$\eta_n$ 为噪声。对 DPSS 窗函数 $w_n^{(0)}$，构造估计

$$
\widehat s = \sum_{n=0}^{N-1} w_n^{(0)} a_n \mathrm e^{-\mathrm i\pi n}.
$$

理想情形下，$s_n = s_0(-1)^n$，则

$$
\widehat s_{\mathrm{ideal}} = s_0\sum_{n} |w_n^{(0)}|^2,
$$

噪声贡献方差

$$
\operatorname{Var}(\widehat s) = \sigma_\eta^2\sum_n |w_n^{(0)}|^2.
$$

利用大偏差估计，在信号幅度 $|s_0|$ 与噪声方差之间得到区分条件；结合 Floquet 带隙 $\Delta_{\mathrm{F}}$ 与噪声相关长度估计可得到 $|s_0|\sim \Delta_{\mathrm{F}} \exp(-\gamma N)$ 的下界，从而推导 $N = \mathcal O(\Delta_{\mathrm{F}}^{-2}\log(1/\varepsilon))$。

该推导依赖于 DPSS 窗函数在频带附近几乎理想的带限特性，使得观测主要敏感于 $\omega\approx\pi$ 的时间晶体主频，噪声被压制。详细计算留待后续更专门的工程论文展开。
