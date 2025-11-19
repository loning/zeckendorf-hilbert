# 第十三章：变分完备性与边界项

在第十二章中，我们通过熵变分原理（IGVP）成功推导了爱因斯坦场方程及其高阶推广。然而，物理学中的变分原理不仅仅是求导令其为零那么简单。当我们将理论应用到具有边界的时空区域（如黑洞视界、宇宙视界或有限的实验室系统）时，必须面对一个严峻的数学挑战：**变分原理的边界项问题**。

在标准广义相对论中，爱因斯坦-希尔伯特作用量本身在狄利克雷（Dirichlet）边界条件下是**变分不完备**的——变分过程会产生无法消除的边界通量。为了修补这一点，Gibbons, Hawking 和 York 引入了著名的边界项（GHY 项）。在我们的离散本体论与熵引力框架下，这个"补丁"具有了全新的、更深刻的物理含义：它不再是数学上的修正，而是**全息边缘模式（Edge Modes）的熵**。

本章将深入探讨这一问题，证明 GHY 项、海沃德（Hayward）角点项以及零类边界项都是维持理论**数学完备性（Mathematical Completeness）** 与 **物理幺正性** 的必然要求。

---

### 13.1 变分原理中的边界项问题与数学完备性

任何涉及二阶微分方程的物理理论（如引力），其作用量通常包含场的一阶或二阶导数。当我们在有界区域 $M$ 上对作用量 $I[\phi]$ 进行变分时，分部积分（Integration by Parts, IBP）必然会产生边界项。如果这些边界项不能在给定的边界条件下自然消失，变分原理就是**病态的（Ill-posed）**，即泛函导数不存在。

本节将严格剖析这一问题在引力理论中的表现，并定义何为"变分完备性"。

#### 13.1.1 爱因斯坦-希尔伯特作用量的变分危机

考虑标准的爱因斯坦-希尔伯特作用量（不含边界项）：

$$
I_{\text{EH}} = \frac{1}{16\pi G} \int_M R \sqrt{-g} \, \mathrm{d}^4x
$$

我们要计算其在度规微扰 $g_{\mu\nu} \to g_{\mu\nu} + \delta g_{\mu\nu}$ 下的变分 $\delta I_{\text{EH}}$。

利用帕拉蒂尼恒等式（Palatini Identity）$\delta R_{\mu\nu} = \nabla_\rho (\delta \Gamma^\rho_{\mu\nu}) - \nabla_\nu (\delta \Gamma^\rho_{\mu\rho})$，我们可以将变分分解为**体（Bulk）**部分和**边界（Boundary）**部分：

$$
\delta I_{\text{EH}} = \frac{1}{16\pi G} \int_M G_{\mu\nu} \delta g^{\mu\nu} \sqrt{-g} \, \mathrm{d}^4x + \frac{1}{16\pi G} \int_M \nabla_\mu v^\mu \sqrt{-g} \, \mathrm{d}^4x
$$

其中边界流矢量 $v^\mu$ 为：

$$
v^\mu = g^{\alpha\beta} \delta \Gamma^\mu_{\alpha\beta} - g^{\mu\alpha} \delta \Gamma^\beta_{\alpha\beta}
$$

利用斯托克斯定理，第二项转化为边界 $\partial M$ 上的积分。设边界单位法向量为 $n^\mu$（$\varepsilon = n^2 = \pm 1$），诱导度规为 $h_{ab}$。边界项可写为：

$$
\delta I_{\partial M} = \frac{\varepsilon}{16\pi G} \int_{\partial M} v^\mu n_\mu \sqrt{|h|} \, \mathrm{d}^3y
$$

#### 13.1.2 狄利克雷条件的失效与法向导数困境

为了使最小作用量原理 $\delta I = 0$ 导出爱因斯坦方程 $G_{\mu\nu} = 0$，我们必须要求边界项 $\delta I_{\partial M}$ 消失。

通常，物理系统遵循**狄利克雷边界条件（Dirichlet Boundary Condition）**：固定边界上的场值。在引力中，这意味着固定边界上的诱导度规 $h_{ab}$，即 $\delta h_{ab} = 0$。

然而，仔细分析 $v^\mu n_\mu$ 的结构，我们发现它包含度规的**法向导数**的变分：

$$
v^\mu n_\mu \sim n^\rho h^{\alpha\beta} \nabla_\rho (\delta g_{\alpha\beta}) + \dots
$$

这意味着，即使我们固定了边界上的度规（$\delta g|_{\partial M} = 0$），我们**不能**同时也固定度规的法向导数（$\partial_n \delta g|_{\partial M} = 0$），除非我们过度约束了系统（导致运动方程无解）。

**结论**：

对于仅包含 $I_{\text{EH}}$ 的理论，固定边界度规并不能使边界变分项消失。泛函导数 $\frac{\delta I}{\delta g_{\mu\nu}}$ 在边界处是**未定义的（Undefined）**。这就像试图对一个函数 $f(x)$ 在端点求导，但该函数在端点处不可微。这就是**变分不完备性**。

#### 13.1.3 变分完备性的定义

为了修复这一数学病态，我们需要修改作用量或边界条件。

**定义 13.1.1 (变分完备性 / Variational Completeness)**

一个作用量泛函 $I[\phi]$ 在给定的边界条件集合 $\mathcal{C}$ 下被称为是**变分完备的**（或可微的），如果对于切空间中满足该边界条件的任意微扰 $\delta \phi$，作用量的变分可以严格表示为体积分形式：

$$
\delta I = \int_M E(\phi) \cdot \delta \phi
$$

而不包含任何非零的边界残留项。此时，欧拉-拉格朗日方程 $E(\phi) = 0$ 才是该变分问题的极值条件。

为了实现引力的变分完备性，我们必须在原作用量 $I_{\text{EH}}$ 上添加一个**边界修正项（Counter-term）** $I_{\text{bdy}}$，使得：

$$
\delta (I_{\text{EH}} + I_{\text{bdy}}) \Big|_{\delta h_{ab}=0} = (\text{体项}) + 0
$$

这意味着 $\delta I_{\text{bdy}}$ 必须精确抵消 $I_{\text{EH}}$ 产生的法向导数流。

#### 13.1.4 物理视角：从数学修补到物理自由度

在传统的几何视角下，添加边界项（如 GHY 项）常被视为一种数学上的修补技术（"Fixing the variational principle"）。但在我们的 **QCA 信息本体论** 和 **IGVP** 框架下，边界项具有极其深刻的本体论地位。

1.  **全息对偶**：在全息原理中，体（Bulk）物理与边界（Boundary）物理是对偶的。体作用量 $I_{\text{EH}}$ 描述了体内的动力学，而边界作用量 $I_{\text{bdy}}$ 描述了边界自由度（Edge Modes）的动力学。

2.  **熵的配分函数**：在欧几里得路径积分表述中，配分函数 $Z = \int Dg \, e^{-I}$。对于黑洞或因果菱形，经典的鞍点近似给出 $Z \approx e^{-I_{class}}$。如果忽略边界项，$I_{class}$ 的值（以及导出的熵 $S = (1 - \beta \partial_\beta) \ln Z$）通常是错误的，甚至为零。

3.  **边界即系统**：当我们划定一个小因果菱形来定义广义熵 $S_{\text{gen}}$ 时，我们人为地切割了时空。这种切割切断了量子纠缠，暴露了**边缘模式**。边界项正是对这些被切断的边缘模式的能量或熵的计数。

因此，变分完备性不仅仅是数学要求，它是**物理系统完整性**的要求。一个没有正确边界项的理论，就像一个没有考虑表面张力的液滴理论，无法正确描述系统的热力学性质。

在下一节 13.2 中，我们将具体推导这个必需的边界项——Gibbons-Hawking-York 项，并揭示它与外微曲率（Extrinsic Curvature）及熵的直接联系。

