**11.3 纠缠第一定律：模哈密顿量（Modular Hamiltonian）与能量动量张量**

在 11.2 节中，我们将广义熵 $S_{\text{gen}}$ 定义为几何面积项与物质纠缠熵项的总和。为了构建引力的动力学方程，我们需要知道当系统状态发生微小变化时，这些熵项是如何演化的。在经典热力学中，能量变化与熵变通过第一定律 $dE = T dS$ 相联系。在量子信息论中，存在一个与之严格对应的定律——**纠缠第一定律（First Law of Entanglement）**。

本节将证明，对于任何量子态的微小扰动，纠缠熵的变化精确等于一个特定算符——**模哈密顿量（Modular Hamiltonian）**——的期望值变化。更关键的是，对于小因果菱形中的真空态，这个抽象的信息算符直接对应于物理上的**能量动量张量**通量。这建立了"信息（熵）"与"物质（能量）"之间最坚实的数学桥梁。

### 11.3.1 模哈密顿量的代数定义

考虑希尔伯特空间中的一个密度矩阵 $\rho$。由于 $\rho$ 是正定厄米算符（假设满秩），我们可以将其写成指数形式。

**定义 11.3.1 (模哈密顿量)**

对于任意密度矩阵 $\rho$，其**模哈密顿量** $K_\rho$ 定义为：

$$
K_\rho \equiv -\ln \rho
$$

这使得 $\rho = e^{-K_\rho}$（通常归一化使得 $\text{Tr}(e^{-K_\rho})=1$，或者将归一化因子吸收到 $K$ 的常数项中，即 $\rho = e^{-K}/Z$）。

**物理意义**：

虽然 $K_\rho$ 被称为"哈密顿量"，但它通常不是控制系统时间演化的物理哈密顿量 $H$。它是一个由系统状态 $\rho$ **内禀定义**的算符，描述了该状态在信息几何意义下的"能量"权重。只有在热平衡态（吉布斯态 $\rho = e^{-\beta H}/Z$）下，$K_\rho$ 才与物理哈密顿量成正比（$K_\rho = \beta H + \ln Z$）。

### 11.3.2 纠缠第一定律的严格推导

现在考察系统状态从基准态 $\sigma$（例如真空态）发生微小偏离，变为 $\rho = \sigma + \delta \rho$。我们需要计算纠缠熵 $S(\rho) = -\text{Tr}(\rho \ln \rho)$ 的变化 $\delta S$。

**定理 11.3.2 (纠缠第一定律)**

设 $\sigma$ 为任意参考态，$\rho = \sigma + \delta \rho$ 为其微扰态（满足 $\text{Tr}(\delta \rho) = 0$ 以保持归一化）。在 $\delta \rho$ 的一阶近似下，冯·诺依曼熵的变化量 $\delta S$ 等于模哈密顿量 $K_\sigma$ 的期望值变化量：

$$
\delta S = \delta \langle K_\sigma \rangle \equiv \text{Tr}(K_\sigma \delta \rho)
$$

**证明**：

相对熵（Relative Entropy）$S(\rho \| \sigma)$ 定义为：

$$
S(\rho \| \sigma) = \text{Tr}(\rho \ln \rho) - \text{Tr}(\rho \ln \sigma) = -S(\rho) + \text{Tr}(\rho K_\sigma)
$$

即 $S(\rho \| \sigma) = \langle K_\sigma \rangle_\rho - S(\rho)$。

对于微小扰动 $\rho = \sigma + \epsilon \Delta \rho$，相对熵具有二阶极小性（即 $S(\sigma + \epsilon \Delta \rho \| \sigma) \sim \mathcal{O}(\epsilon^2)$），这是因为 $\sigma$ 使 $S(\cdot \| \sigma)$ 在一阶变分下为零（类似于自由能在平衡态取极小值）。

因此，在一阶近似下：

$$
0 = \delta \langle K_\sigma \rangle - \delta S \implies \delta S = \delta \langle K_\sigma \rangle
$$

$\square$

**物理诠释**：

这一公式是热力学第一定律 $dS = dE/T$ 的量子推广。在这里，模哈密顿量 $K_\sigma$ 扮演了"能量/温度"的角色。它告诉我们，要改变一个量子态的纠缠熵，必须在模哈密顿量的共轭方向上注入"模能量"。

### 11.3.3 几何化：Bisognano-Wichmann 定理

对于任意量子系统，模哈密顿量 $K$ 往往是非局域的、复杂的。然而，在**量子场论**和**小因果菱形**的背景下，$K$ 具有惊人的几何简单性。

考虑闵可夫斯基真空态 $|\Omega\rangle$ 限制在小因果菱形（或林德勒楔）$\Sigma$ 内的约化密度矩阵 $\sigma_\Sigma$。根据 Bisognano-Wichmann 定理，模哈密顿量 $K_\Sigma$ 生成的流不仅是代数上的自同构，更是时空几何上的**共形基尔灵流（Conformal Killing Flow）**。

**定理 11.3.3 (模哈密顿量的几何形式)**

对于小因果菱形 $\Sigma$，其真空模哈密顿量 $K_{vac}$ 由能量动量张量 $T_{\mu\nu}$ 沿共形基尔灵矢量 $\zeta^\mu$ 的积分给出：

$$
K_{vac} = \frac{2\pi}{\hbar} \int_{\Sigma} T_{\mu\nu} \zeta^\mu d\Sigma^\nu + \text{const}
$$

其中 $\zeta^\mu$ 是保持菱形边界 $\partial \Sigma$ 不变的矢量场。在菱形中心附近的惯性系中，$\zeta^\mu$ 近似为洛伦兹推进（Boost）生成元，其模长与距离中心的距离成正比。

**物理推论**：

将纠缠第一定律 $\delta S = \delta \langle K \rangle$ 与几何形式结合，我们得到：

$$
\delta S_{\text{mat}} = \frac{2\pi}{\hbar} \int_{\Sigma} \delta \langle T_{\mu\nu} \rangle \zeta^\mu d\Sigma^\nu
$$

这表明，**物质纠缠熵的变化 $\delta S_{\text{mat}}$ 直接对应于穿过因果菱形的能量通量（Energy Flux）**。

系数 $2\pi/\hbar$ 实际上包含了 Unruh 温度的信息（$T_U = \hbar a / 2\pi$），使得上式在量纲上符合 $dS = dE/T$。

### 11.3.4 广义熵平衡与引力场方程的预演

至此，我们拥有了推导引力方程的所有组件：

1.  **几何侧**：根据 11.1 节，时空曲率导致菱形面积亏损 $\delta A \propto - G_{00}$。

2.  **物质侧**：根据本节，物质能量通量导致纠缠熵增加 $\delta S_{\text{mat}} \propto T_{00}$。

如果我们假设时空遵循**广义熵平衡原理**（即总熵 $S_{\text{gen}} = A/4G + S_{\text{mat}}$ 在真空微扰下保持极值或平衡），则几何熵的减少必须被物质熵的增加所补偿：

$$
\delta S_{\text{grav}} + \delta S_{\text{mat}} = 0
$$

代入各自的表达式，我们将看到 $G_{00}$ 与 $T_{00}$ 之间必须存在线性关系。这正是第十二章要严格证明的内容。

**总结**

本节确立了纠缠第一定律 $\delta S = \delta \langle K \rangle$，并利用 Bisognano-Wichmann 定理将模哈密顿量识别为能量动量张量的积分。这一步至关重要，它将抽象的量子信息（熵）"翻译"成了具体的物理实体（能量），从而让爱因斯坦方程能够从纯粹的信息论原则中涌现出来。

在下一节 11.4 中，我们将引入描述几何聚焦效应的**瑞查德乌利（Raychaudhuri）方程**，它是连接几何改变（面积变化）与能量条件（QNEC）的最后一道几何工序。

