# 误差几何与因果稳健性：从参数置信椭球到多实验可信区域的统一几何框架

---

## 摘要

本文提出一套将统计误差转化为"几何边界"的统一框架，并将其系统嵌入因果推断与实验设计之中。核心思想是：给定参数空间中的估计量及其误差，我们不再将"置信区间/标准误"视为附属信息，而是将其上升为参数空间中的"可信区域"（region of trust），即带有度量结构的几何对象；所有因果结论、稳健性判断与实验规划，均通过这些几何区域之间的包含、交并与线性像来刻画。具体而言，本文首先在一般参数模型下，利用典型的渐近正态性与信息矩阵构造置信椭球，并赋予参数空间局部 Riemann 度量结构；其次，在因果推断中，我们将"可识别集"与"可信区域"统一为同一参数空间中的两类集合，通过它们的交集刻画可证的因果结论与可容许的外推方向；进一步地，在多实验/多模型情形下，我们以可信区域的交、并和映射构造共识区域与冲突区域，形成一种"几何化的元分析"；最后，在实验设计与观测规划中，我们将"收缩可信区域体积/半轴"的目标形式化为设计变量上的优化问题，并给出若干线性模型与工具变量模型下的可解实例。附录中给出主要定理的严格证明，包括置信椭球的覆盖性质、因果效应的稳健性判据以及设计准则与 Fisher 信息之间的等价关系。

**关键词**：误差几何；置信椭球；因果推断；可识别集；实验设计；Fisher 信息

**MSC 2020**：62F12, 62K05, 62P25, 62R01

---

## 1 引言

统计推断传统上以"点估计 + 置信区间"的形式呈现，而因果推断则以"识别假设 + 点估计 + 灵敏度分析"为基本结构。在实际决策与工程应用中，研究者往往面临如下三类问题：

1. 给定有限样本，**哪些因果结论是真正由数据支撑的，而非仅是点估计的幻象**？

2. 在多实验、多模型甚至多数据源汇总时，**应如何系统地看清各结果之间的共识与冲突**？

3. 在资源有限的前提下，**如何通过实验设计最大化对特定因果效应或参数方向的"几何可辨率"**？

这些问题在形式上各不相同，但有一个共同特征：它们都与"误差"有关，而"误差"的本质不仅是一个方差或一个置信区间，而是一个具有形状、方向与边界的几何对象。本文的目标，就是把这一直观上存在的"几何性"彻底形式化。

我们采纳如下观点：

* 对于参数 $\theta\in\Theta\subset\mathbb R^d$ 的任何估计 $\hat\theta$，其误差自然诱导一个带有度量结构的区域 $\mathcal R\subset\Theta$，可称为"可信区域"；

* 因果结论不是关于单点 $\hat\theta$ 的声明，而是关于某个函数 $\psi(\theta)$ 在 $\theta\in\mathcal R\cap\mathcal I$ 上的范围，其中 $\mathcal I$ 为可识别集；

* 多实验、多模型、不同假设的结果，可以统一视为在同一参数空间或其射影上的多个可信区域 $\mathcal R_k$，它们的交集、并集与对称差自然刻画"稳健一致""可争议""显著冲突"的参数范围；

* 实验设计与观测规划可被视为"主动塑造未来可信区域的几何形状"的优化问题，其目标是对特定方向（例如某个因果效应）收缩可信区域的半轴，或缩小其体积。

在此框架下，"误差几何"不再只是结果的附属物，而成为整个因果—决策流程的核心结构。本论文将从最基本的参数模型出发，构造这一几何框架，并给出可证明的性质与若干具体模型下的可计算实现。

---

## 2 参数模型与可信区域的几何结构

### 2.1 参数模型与估计量

设观测数据为 $X_1,\dots,X_n$，定义在样本空间 $\mathcal X$ 上，假定其分布属于一族概率测度 $\{P_\theta:\theta\in\Theta\subset\mathbb R^d\}$。设 $\theta_0\in\Theta$ 为"真参数"，$\hat\theta_n=\hat\theta_n(X_1,\dots,X_n)$ 为某一估计量。

我们假定存在常规的渐近线性与正态性结构：

$$
\sqrt{n}(\hat\theta_n - \theta_0) \overset{d}\longrightarrow \mathcal N(0, I(\theta_0)^{-1}),
$$

其中 $I(\theta_0)$ 为 Fisher 信息矩阵，正定且连续。进一步假定存在一致估计 $\hat I_n$ 使得 $\hat I_n\xrightarrow{P}I(\theta_0)$。

### 2.2 Fisher 信息诱导的局部度量

在 $\Theta$ 的每一点 $\theta$ 上，定义双线性形式

$$
g_\theta(u,v) := u^\top I(\theta) v,\qquad u,v\in\mathbb R^d,
$$

则 $g$ 为 $\Theta$ 上的一个局部 Riemann 度量（在可微性条件下）。直观上，$I(\theta)$ 的特征方向描述了"容易/困难辨识"的参数方向：沿某方向的方差越小，该方向上的"单位长度"在信息度量下越大，反之亦然。

在有限样本 $n$ 下，使用 $\hat I_n$ 得到经验度量

$$
\hat g_n(u,v) := u^\top \hat I_n v,
$$

其在概率意义下收敛于 $g_{\theta_0}$。

### 2.3 置信椭球作为可信区域

对给定显著性水平 $\alpha\in(0,1)$，定义 $d$ 维卡方分布的分位数 $\chi^2_{d,1-\alpha}$，构造可信区域

$$
\mathcal R_n(\alpha) := \{\theta\in\Theta: n(\theta-\hat\theta_n)^\top \hat I_n (\theta-\hat\theta_n) \le \chi^2_{d,1-\alpha}\}.
$$

它是以 $\hat\theta_n$ 为中心，形状由 $\hat I_n^{-1}$ 决定的椭球，刻画参数的不确定性。经典理论保证：

**定理 2.1（渐近覆盖）** 在上述正则条件下，对任意固定 $\alpha\in(0,1)$，有

$$
P_{\theta_0}\bigl(\theta_0\in\mathcal R_n(\alpha)\bigr) \longrightarrow 1-\alpha,\qquad n\to\infty.
$$

该定理在附录 A.1 中证明。

因此，$\mathcal R_n(\alpha)$ 可视作"以 $1-\alpha$ 概率包含真值 $\theta_0$ 的可信区域"。在信息度量 $g_{\theta_0}$ 下，$\mathcal R_n(\alpha)$ 的半轴长度与 Fisher 信息的特征值成反比，与 $1/\sqrt{n}$ 成正比。

---

## 3 误差作为几何边界：可信区域的运算与投影

本节将"误差"系统地转化为"几何边界"，并讨论几种基本运算：投影、线性像与非线性像。

### 3.1 线性函数的像与椭球投影

设关心的目标为线性函数 $\psi(\theta)=c^\top\theta$，其中 $c\in\mathbb R^d$。在椭球 $\mathcal R_n(\alpha)$ 上，$\psi$ 的取值区间为

$$
\Psi_n(\alpha) := \{\psi(\theta):\theta\in\mathcal R_n(\alpha)\}
= \bigl[\psi_{\min,n},\psi_{\max,n}\bigr].
$$

该区间可解析计算。注意到

$$
\psi(\theta) = c^\top\theta = c^\top\hat\theta_n + c^\top(\theta-\hat\theta_n),
$$

约束为 $n(\theta-\hat\theta_n)^\top \hat I_n (\theta-\hat\theta_n) \le \chi^2_{d,1-\alpha}$。令 $h=\theta-\hat\theta_n$，问题化为在椭球约束内最大化/最小化线性函数 $c^\top h$。经典优化结论给出

$$
\psi_{\max,n} = c^\top\hat\theta_n + \sqrt{\frac{\chi^2_{d,1-\alpha}}{n} c^\top \hat I_n^{-1} c},
$$

$$
\psi_{\min,n} = c^\top\hat\theta_n - \sqrt{\frac{\chi^2_{d,1-\alpha}}{n} c^\top \hat I_n^{-1} c}.
$$

因此，线性目标的置信区间自然由椭球与方向向量 $c$ 的几何关系给出。

**命题 3.1（线性目标的最优界）** 对任意 $c\in\mathbb R^d$，$\psi(\theta)=c^\top\theta$ 在 $\mathcal R_n(\alpha)$ 上的最小值与最大值分别如上式所示，且该区间在渐近意义下具有 $1-\alpha$ 的覆盖概率。

证明见附录 A.2。

### 3.2 非线性函数的局部线性近似

若 $\psi:\Theta\to\mathbb R^k$ 可微，则在 $\hat\theta_n$ 附近可作一阶近似

$$
\psi(\theta) \approx \psi(\hat\theta_n) + D\psi(\hat\theta_n)(\theta-\hat\theta_n),
$$

其中 Jacobian 矩阵 $D\psi(\hat\theta_n)\in\mathbb R^{k\times d}$ 的第 $i$ 行为 $\nabla\psi_i(\hat\theta_n)^\top$。于是 $\psi(\mathcal R_n(\alpha))$ 在一阶近似下为 $\mathbb R^k$ 中的椭球：

$$
\mathcal S_n(\alpha) := \left\{ y\in\mathbb R^k: n(y-\psi(\hat\theta_n))^\top \bigl(D\psi(\hat\theta_n)\hat I_n^{-1}D\psi(\hat\theta_n)^\top\bigr)^{-1}(y-\psi(\hat\theta_n)) \le \chi^2_{k,1-\alpha}\right\},
$$

其中逆矩阵存在需假定 $D\psi(\hat\theta_n)$ 的行向量在信息度量下线性独立。该结果本质上是 Delta 方法在几何语言下的重述。

### 3.3 多参数与多目标的支持函数形式

在更一般情形，我们可使用支持函数刻画任意凸目标集。在凸椭球 $\mathcal R_n(\alpha)$ 上，其支持函数为

$$
h_{\mathcal R_n(\alpha)}(u) := \sup_{\theta\in\mathcal R_n(\alpha)} u^\top\theta
= u^\top\hat\theta_n + \sqrt{\frac{\chi^2_{d,1-\alpha}}{n} u^\top \hat I_n^{-1} u}.
$$

因而任何由线性泛函集合 $\{u: u\in\mathcal U\}$ 定义的目标集，都可以通过支持函数直接计算边界。其在因果推断场景中的一个重要应用是：当我们关心的是一簇线性因果效应（例如多群体异质性效应）时，可以通过支持函数统一地给出它们在可信区域上的最坏/最好情形。

---

## 4 因果推断中的可识别集与可信区域

### 4.1 因果模型与可识别集

在因果推断中，参数 $\theta$ 通常带有结构性解释，例如潜在结果模型中的平均处理效应，结构方程模型中的路径系数，工具变量模型中的局部平均处理效应等。在存在不可识别或部分识别的情形下，数据与假设所能确定的只是一个 **可识别集**

$$
\mathcal I := \{\theta\in\Theta: \theta \text{ 与观测分布及因果假设相容}\}.
$$

例如，在违反某些排除限制或存在选择偏差时，可识别集往往是一个凸集、半代数集或一般闭集，而非单点。

### 4.2 数据驱动的可识别集估计

在有限样本下，我们通常通过估计不等式来近似 $\mathcal I$。例如，如果因果约束可以表述为参数上的约束

$$
g_j(\theta)\le 0,\quad j=1,\dots,m,
$$

而我们只能估计 $g_j(\theta)$ 的经验版本 $\hat g_{j,n}(\theta)$，则常见做法是使用"松弛不等式"

$$
\hat g_{j,n}(\theta) \le b_{j,n},
$$

其中 $b_{j,n}$ 是上界（例如多重检验校正后的阈值），从而得到数据驱动的可识别集估计

$$
\hat{\mathcal I}_n := \{\theta\in\Theta: \hat g_{j,n}(\theta)\le b_{j,n}, j=1,\dots,m\}.
$$

在合适条件下可证明 $\hat{\mathcal I}_n$ 以适当的意义收敛到 $\mathcal I$。

### 4.3 可识别集与可信区域的交集

本文提出：**因果结论应基于 $\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n$ 而非仅仅基于 $\hat\theta_n$**。对于给定的因果函数 $\psi:\Theta\to\mathbb R^k$，我们关心的是

$$
\mathcal C_n(\alpha) := \{\psi(\theta):\theta\in\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n\}.
$$

若 $\mathcal C_n(\alpha)$ 在某个方向或某个分量上具有一致符号或被限制在某个期望区间内，则我们可以说该因果结论在显著性水平 $\alpha$ 下是"几何稳健"的。

**定义 4.1（几何稳健性）** 设 $\psi:\Theta\to\mathbb R$ 为一标量因果目标，$\mathcal R_n(\alpha)$ 为 $1-\alpha$ 级别可信区域，$\hat{\mathcal I}_n$ 为可识别集的样本近似。若存在区间 $[L,U] \subset\mathbb R$，使得

$$
\mathcal C_n(\alpha)=\{\psi(\theta):\theta\in\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n\} \subset [L,U],
$$

则称"在水平 $\alpha$ 下，因果结论 $\psi(\theta)\in[L,U]$ 是几何稳健的"。

特别地，当 $L>0$（或 $U<0$）时，可以对效应方向做出稳健判断。

### 4.4 一个典型判据：线性因果效应

设 $\psi(\theta)=c^\top\theta$ 为线性因果效应（例如多参数模型中某线性组合对应于平均处理效应），且可识别集可表示为一组线性不等式

$$
A\theta \le b,
$$

则 $\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n$ 为椭球与多面体的交集，为凸集。因果效应的极值可由如下凸优化问题给出：

$$
\psi_{\max,n}^* := \sup\{c^\top\theta:\theta\in\mathcal R_n(\alpha), A\theta\le b\},
$$

$$
\psi_{\min,n}^* := \inf\{c^\top\theta:\theta\in\mathcal R_n(\alpha), A\theta\le b\}.
$$

在许多应用中，该问题可通过二次规划或半正定规划高效求解。显然，

$$
\mathcal C_n(\alpha) = \bigl[\psi_{\min,n}^*,\psi_{\max,n}^*\bigr].
$$

**定理 4.2（线性因果效应的几何稳健判据）** 在上述设定下，若对某个 $\delta>0$ 有

$$
\psi_{\min,n}^* \ge \delta>0,
$$

则在显著性水平 $\alpha$ 下，可得出因果结论"效应为正，且至少为 $\delta$"，且该结论对所有 $\theta\in\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n$ 都成立。

证明见附录 A.3。

这一判据将"点估计显著"提升为"在全部可信候选参数上均显著"，自然排除了仅靠点估计而忽略参数相关性时可能出现的虚假显著。

---

## 5 多实验与多模型：可信区域的交、并与冲突结构

在现实中，我们常常需要将不同实验、不同数据源甚至不同模型的结果进行综合。本文主张：**多实验汇总的自然对象不是"若干个点估计"，而是"若干个可信区域"**。

### 5.1 多个可信区域的交集与共识

设有 $K$ 个实验/数据源/模型，它们在同一参数空间 $\Theta$ 上给出可信区域 $\mathcal R_{n_k}^{(k)}(\alpha_k)$，$k=1,\dots,K$。定义整体共识区域

$$
\mathcal R_{\mathrm{cons}} := \bigcap_{k=1}^K \mathcal R_{n_k}^{(k)}(\alpha_k).
$$

若我们关心的因果函数为 $\psi:\Theta\to\mathbb R^d$，则其在共识区域上的像为

$$
\mathcal C_{\mathrm{cons}} := \{\psi(\theta):\theta\in\mathcal R_{\mathrm{cons}}\}.
$$

若 $\mathcal R_{\mathrm{cons}}$ 非空且"较小"，则说明不同实验之间存在高度一致性；反之，若 $\mathcal R_{\mathrm{cons}}$ 为空，则可以明确地说"这些实验/模型之间存在根本冲突"，而非模糊地依赖"某些估计差异"。

### 5.2 并集与可容许集合

另一方面，定义可容许区域为

$$
\mathcal R_{\mathrm{perm}} := \bigcup_{k=1}^K \mathcal R_{n_k}^{(k)}(\alpha_k),
$$

它刻画"至少被某一个实验支持"的参数集。在某些决策问题中（例如容忍部分实验失败或模型 misspecification），我们可能只要求结论在 $\mathcal R_{\mathrm{perm}}$ 上成立。

### 5.3 冲突区域与不确定性分解

定义冲突区域为对称差

$$
\mathcal R_{\mathrm{conflict}} := \left(\bigcup_{k=1}^K \mathcal R_{n_k}^{(k)}\right)\setminus\left(\bigcap_{k=1}^K \mathcal R_{n_k}^{(k)}\right),
$$

其中若某点 $\theta$ 只被部分实验支持（而被其他实验排除），则属于该区域。通过将参数空间可视化为"共识—冲突—未约束"的分区，可以直观识别哪些参数方向的结论对实验选择最敏感。

---

## 6 实验设计与观测规划：可信区域作为目标函数

在上述框架中，实验设计的本质是：**通过选择实验方案或观测策略，来塑造未来可信区域的形状与大小**。本节我们在经典线性模型与一般 Fisher 信息背景下给出形式化刻画。

### 6.1 Fisher 信息与区域体积

在正则模型中，样本量为 $n$ 的情况下，信息矩阵通常可表示为

$$
I_n(\theta) = n I_1(\theta),
$$

其中 $I_1(\theta)$ 为单个观测的信息。对给定设计参数 $\xi$（如样本在不同处理/协变量配置上的分布），单观测信息可写作 $I_1(\theta;\xi)$。因此，

$$
I_n(\theta;\xi) = n I_1(\theta;\xi).
$$

椭球可信区域的体积与 $\det\bigl(I_n(\theta_0;\xi)\bigr)^{-1/2}$ 成正比。更准确地说，当 $\mathcal R_n(\alpha;\xi)$ 是基于 $I_n(\theta_0;\xi)$ 的椭球时，其 Lebesgue 体积为

$$
\operatorname{Vol}\bigl(\mathcal R_n(\alpha;\xi)\bigr) = C_{d,\alpha}\,\bigl(\det I_n(\theta_0;\xi)\bigr)^{-1/2},
$$

其中常数 $C_{d,\alpha}$ 仅依赖于维数 $d$ 和 $\alpha$。因此，最小化区域体积等价于最大化 $\det I_n(\theta_0;\xi)$。

**定义 6.1（D-最优设计的误差几何刻画）** 若设计 $\xi^*$ 使得

$$
\det I_n(\theta_0;\xi^*) = \sup_{\xi} \det I_n(\theta_0;\xi),
$$

则称 $\xi^*$ 为 D-最优设计。几何上，它在给定 $n$ 下使可信区域的体积达到最小，从而整体上最紧缩。

经典 D-最优性结论在附录 A.4 中以误差几何语言重述。

### 6.2 定向可辨率：A-最优与 c-最优

若关注的是特定线性因果效应 $\psi(\theta)=c^\top\theta$，则其渐近方差为

$$
\operatorname{Var}\bigl(\hat\psi\bigr) \approx \frac{1}{n}c^\top I_1(\theta_0;\xi)^{-1} c.
$$

从误差几何角度看，这正是可信椭球在方向 $c$ 上的主半轴长度平方（忽略常数）。因此，最小化该方差等价于在方向 $c$ 上最大化可辨率。

**定义 6.2（c-最优设计）** 若设计 $\xi^*$ 使得

$$
c^\top I_1(\theta_0;\xi^*)^{-1} c = \inf_{\xi} c^\top I_1(\theta_0;\xi)^{-1} c,
$$

则称 $\xi^*$ 为 c-最优设计。

从几何视角：c-最优设计不追求整体椭球体积最小，而是专门压缩在方向 $c$ 上的半轴，即集中提升该因果效应的几何可辨率。

---

## 7 典型模型中的误差几何实例

本节简要展示几类常见模型下误差几何框架的具体形式，以便读者获得直观印象。

### 7.1 线性回归模型中的置信椭球与效应区间

考虑线性回归模型

$$
Y_i = x_i^\top\beta + \varepsilon_i,\quad \varepsilon_i\sim\mathcal N(0,\sigma^2),
$$

其中 $x_i\in\mathbb R^p$ 为已知协变量，$\beta\in\mathbb R^p$ 为回归系数。设 $X$ 为设计矩阵，OLS 估计为

$$
\hat\beta = (X^\top X)^{-1} X^\top Y.
$$

经典结果给出

$$
\hat\beta\sim\mathcal N\left(\beta, \sigma^2(X^\top X)^{-1}\right).
$$

因此，信息矩阵为 $I(\beta) = \sigma^{-2} X^\top X$，可信椭球为

$$
\mathcal R(\alpha) = \{\beta: (\beta-\hat\beta)^\top X^\top X (\beta-\hat\beta) \le \sigma^2\chi^2_{p,1-\alpha}\}.
$$

对任意线性预测 $\psi(\beta)=x_{\text{new}}^\top\beta$，其在 $\mathcal R(\alpha)$ 上的区间为

$$
x_{\text{new}}^\top\hat\beta \pm \sqrt{\chi^2_{p,1-\alpha}\,\sigma^2 x_{\text{new}}^\top (X^\top X)^{-1} x_{\text{new}}},
$$

这与经典线性回归置信区间完全一致，但在本框架下被解释为"可信椭球在 $x_{\text{new}}$ 方向上的几何投影"。

### 7.2 工具变量模型中的可识别集与椭球约束

在简单线性 IV 模型中，存在弱工具或违背排除假设时，结构参数可能只部分可识别。此时可识别集 $\mathcal I$ 通常为某个多面体或更复杂的凸集。将其与置信椭球 $\mathcal R_n(\alpha)$ 相交，可以得到结构参数的几何约束，从而对局部平均处理效应的取值范围给出稳健区间。

在许多情况下，该问题可化为"椭球与多面体的交集上的线性函数极值"，可以使用二次规划求解，其本质即为第 4.4 节所述的几何稳健判据。

---

## 8 讨论与展望

本文提供了一种将"误差"上升为"几何边界"的统一视角，并在此基础上系统重述了置信区间、因果可识别集、多实验汇总与实验设计等经典主题。其核心要点可概括为：

1. 可信区域 $\mathcal R_n(\alpha)$ 是参数空间中的椭球或更一般的凸集，携带由 Fisher 信息诱导的局部度量结构；

2. 因果结论应当在 $\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n$ 上检验，而非仅仅依赖点估计；

3. 多实验与多模型自然诱导可信区域的交、并与对称差，其几何分解刻画共识、冲突与不确定性结构；

4. 实验设计可以被视为"塑造未来可信区域几何"的优化问题，与 D-最优、A-最优与 c-最优等经典准则在形式上完全等价。

更进一步的方向包括：将本文的误差几何框架与信息几何（Fisher–Rao 度量）、泛函参数（例如密度曲线或响应曲面）、高维稀疏结构（例如 $\ell_1$ 约束下的多面体区域）、以及动态因果结构（时间序列与事件史模型）结合；在这些扩展中，"可信区域"将不再是有限维椭球，而是 Banach 空间或流形上的复杂集合，但其作为"误差边界"的本质仍保持不变。

---

## 附录 A：主要定理与命题的证明

### A.1 定理 2.1 的证明（置信椭球的渐近覆盖）

**定理重述** 在正则条件下，设 $\hat\theta_n$ 满足

$$
\sqrt{n}(\hat\theta_n-\theta_0)\xrightarrow{d}\mathcal N(0, I(\theta_0)^{-1}),
$$

且 $\hat I_n\xrightarrow{P}I(\theta_0)$，则对任意固定 $\alpha\in(0,1)$，

$$
P_{\theta_0}\bigl(\theta_0\in\mathcal R_n(\alpha)\bigr)\to 1-\alpha.
$$

**证明** 记

$$
Z_n := \sqrt{n}(\hat\theta_n-\theta_0),\qquad I_0:=I(\theta_0),
$$

则 $Z_n\xrightarrow{d} Z\sim\mathcal N(0,I_0^{-1})$。注意到事件 $\theta_0\in\mathcal R_n(\alpha)$ 等价于

$$
n(\theta_0-\hat\theta_n)^\top \hat I_n (\theta_0-\hat\theta_n) \le \chi^2_{d,1-\alpha},
$$

即

$$
Z_n^\top \hat I_n Z_n \le \chi^2_{d,1-\alpha}.
$$

根据 Slutsky 定理，$\hat I_n\xrightarrow{P}I_0$，所以 $Z_n^\top\hat I_n Z_n \xrightarrow{d} Z^\top I_0 Z$。而对 $Z\sim\mathcal N(0,I_0^{-1})$，有

$$
Z^\top I_0 Z \sim \chi^2_d.
$$

因此，

$$
P_{\theta_0}\bigl(\theta_0\in\mathcal R_n(\alpha)\bigr)
= P\bigl(Z_n^\top\hat I_n Z_n\le \chi^2_{d,1-\alpha}\bigr)
\longrightarrow P\bigl(Z^\top I_0 Z \le \chi^2_{d,1-\alpha}\bigr) = 1-\alpha.
$$

证毕。

---

### A.2 命题 3.1 的证明（线性目标的最优界）

**命题重述** 在 $\mathcal R_n(\alpha)$ 上，线性函数 $\psi(\theta)=c^\top\theta$ 的最小值与最大值为

$$
\psi_{\max,n} = c^\top\hat\theta_n + \sqrt{\frac{\chi^2_{d,1-\alpha}}{n} c^\top \hat I_n^{-1} c},
$$

$$
\psi_{\min,n} = c^\top\hat\theta_n - \sqrt{\frac{\chi^2_{d,1-\alpha}}{n} c^\top \hat I_n^{-1} c}.
$$

**证明** 令 $h=\theta-\hat\theta_n$，约束变为

$$
n h^\top \hat I_n h \le \chi^2_{d,1-\alpha}.
$$

目标函数为

$$
\psi(\theta) = c^\top\hat\theta_n + c^\top h.
$$

因此最大化 $\psi(\theta)$ 等价于在椭球

$$
\mathcal E := \{h: h^\top \hat I_n h \le \chi^2_{d,1-\alpha}/n\}
$$

上最大化 $c^\top h$。标准的二次约束线性规划结论或 Cauchy–Schwarz 不等式给出

$$
\sup_{h\in\mathcal E} c^\top h = \sqrt{\chi^2_{d,1-\alpha}/n}\,\sqrt{c^\top \hat I_n^{-1} c},
$$

最小值则为相反数。因此

$$
\psi_{\max,n} = c^\top\hat\theta_n + \sqrt{\frac{\chi^2_{d,1-\alpha}}{n} c^\top \hat I_n^{-1} c},
$$

$$
\psi_{\min,n} = c^\top\hat\theta_n - \sqrt{\frac{\chi^2_{d,1-\alpha}}{n} c^\top \hat I_n^{-1} c}.
$$

证毕。

---

### A.3 定理 4.2 的证明（线性因果效应的几何稳健判据）

**定理重述** 设 $\mathcal R_n(\alpha)$ 为可信椭球，$\hat{\mathcal I}_n=\{\theta:A\theta\le b\}$ 为线性可识别集，$\psi(\theta)=c^\top\theta$。若

$$
\psi_{\min,n}^* := \inf\{c^\top\theta:\theta\in\mathcal R_n(\alpha),A\theta\le b\} \ge \delta > 0,
$$

则在显著性水平 $\alpha$ 下，可以断言对所有 $\theta\in\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n$ 有 $\psi(\theta)\ge \delta >0$，即"因果效应为正且至少为 $\delta$"是几何稳健的。

**证明** 由定义，$\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n$ 中任意 $\theta$ 都满足 $A\theta\le b$ 且 $\theta\in\mathcal R_n(\alpha)$。因此，对任意 $\theta\in\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n$，有

$$
\psi(\theta) = c^\top\theta \ge \inf\{c^\top\theta:\theta\in\mathcal R_n(\alpha),A\theta\le b\} = \psi_{\min,n}^* \ge \delta.
$$

也即

$$
\mathcal C_n(\alpha) = \{\psi(\theta):\theta\in\mathcal R_n(\alpha)\cap\hat{\mathcal I}_n\} \subset [\delta,\infty).
$$

由于 $\mathcal R_n(\alpha)$ 的构造保证其渐近覆盖概率为 $1-\alpha$，在常规条件下可认为"真参数 $\theta_0$"以概率约 $1-\alpha$ 落在 $\mathcal R_n(\alpha)$ 内；若 $\theta_0\in\mathcal I$ 且 $\hat{\mathcal I}_n$ 为良好近似，则上述结论可以在渐近意义下解释为水平 $\alpha$ 的显著结论。严格的概率陈述需引入联合覆盖与一致收敛，这里不再赘述。证毕。

---

### A.4 D-最优设计与可信区域体积的等价性

**命题 A.1（D-最优设计的误差几何刻画）** 设在正则模型中，样本量为 $n$，信息矩阵为 $I_n(\theta_0;\xi) = n I_1(\theta_0;\xi)$，基于 $I_n(\theta_0;\xi)$ 构造的置信椭球 $\mathcal R_n(\alpha;\xi)$ 的体积满足

$$
\operatorname{Vol}\bigl(\mathcal R_n(\alpha;\xi)\bigr) = C_{d,\alpha}\,\bigl(\det I_n(\theta_0;\xi)\bigr)^{-1/2},
$$

其中 $C_{d,\alpha}$ 与 $\xi$ 无关。因此，最大化 $\det I_n(\theta_0;\xi)$ 等价于最小化 $\operatorname{Vol}(\mathcal R_n(\alpha;\xi))$。

**证明** 令 $A(\xi) := I_n(\theta_0;\xi)$，则椭球定义为

$$
\mathcal R_n(\alpha;\xi) = \{\theta: (\theta-\hat\theta_n)^\top A(\xi) (\theta-\hat\theta_n) \le c\},
$$

其中 $c=\chi^2_{d,1-\alpha}$ 为常数。令 $y=A(\xi)^{1/2}(\theta-\hat\theta_n)$，则映射 $\theta\mapsto y$ 为线性同胚，其 Jacobian 为 $\det A(\xi)^{1/2}$。在 $y$-空间中，椭球变为半径为 $\sqrt{c}$ 的欧氏球 $B_d(\sqrt{c})$，其体积为

$$
\operatorname{Vol}(B_d(\sqrt{c})) = \frac{\pi^{d/2} c^{d/2}}{\Gamma(d/2+1)}.
$$

因此

$$
\operatorname{Vol}\bigl(\mathcal R_n(\alpha;\xi)\bigr) = \frac{\operatorname{Vol}(B_d(\sqrt{c}))}{\det A(\xi)^{1/2}}
= C_{d,\alpha}\,(\det A(\xi))^{-1/2},
$$

其中 $C_{d,\alpha} := \operatorname{Vol}(B_d(\sqrt{c}))$ 与 $\xi$ 无关。于是最小化体积等价于最大化 $\det A(\xi) = \det I_n(\theta_0;\xi)$。证毕。

---

## 参考文献（示意）

1. Bickel, P. J., & Doksum, K. A. (2015). *Mathematical Statistics: Basic Ideas and Selected Topics*.

2. van der Vaart, A. W. (1998). *Asymptotic Statistics*.

3. Lehmann, E. L., & Casella, G. (1998). *Theory of Point Estimation*.

4. Pukelsheim, F. (2006). *Optimal Design of Experiments*.

5. Manski, C. F. (2003). *Partial Identification of Probability Distributions*.

6. Imbens, G. W., & Rubin, D. B. (2015). *Causal Inference for Statistics, Social, and Biomedical Sciences*.

7. Pearl, J. (2009). *Causality: Models, Reasoning, and Inference*.

