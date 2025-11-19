**4.3 规范场作为连接变量：格点上的威尔逊线（Wilson Line）与曲率**

在 4.2 节中，我们证明了自旋和狄拉克方程可以从离散的量子行走中涌现。然而，物质场并非孤立存在，它们之间存在相互作用。在现代物理学中，所有基本相互作用（电磁力、弱力、强力）都由**规范场（Gauge Fields）** 描述。

本节将论证，规范场并非是被"添加"到时空中的某种流体，而是离散本体论中**几何比较的必然产物**。当我们在离散格点上比较不同位置的量子态时，由于局域希尔伯特空间基底的任意性，必须引入**连接变量（Connection Variable）**——即威尔逊线。这些连接变量的动力学正是规范场论。

### 4.3.1 局域相位的几何困境

考虑上一节导出的离散费米子场 $\psi(x)$。在 QCA 框架下，每个格点 $x$ 都有独立的希尔伯特空间 $\mathcal{H}_x$。根据有限信息公理，我们只能定义局域操作。这意味着，我们可以在每个格点独立地选择基底的相位（或更一般的幺正变换）。

**定义 4.3.1 (局域规范变换)**

对全系统状态进行如下局域幺正变换：

$$
\psi(x) \mapsto e^{i\alpha(x)} \psi(x)
$$

其中 $\alpha(x)$ 是依赖于位置的任意实函数。

现在考察 4.2 节中的"跳跃"项（即条件平移导致的动能项），它涉及相邻格点态的内积或叠加，例如 $\psi^\dagger(x) \psi(x+1)$。在变换下：

$$
\psi^\dagger(x) \psi(x+1) \mapsto e^{-i\alpha(x)} \psi^\dagger(x) e^{i\alpha(x+1)} \psi(x+1) = e^{i(\alpha(x+1) - \alpha(x))} \psi^\dagger(x) \psi(x+1)
$$

除非 $\alpha(x)$ 是常数（全局对称），否则相位因子 $e^{i(\alpha(x+1) - \alpha(x))}$ 将破坏哈密顿量或更新算符 $U$ 的形式不变性。这被称为**局域规范对称性的破坏**。

**物理本体论的危机与解决**：

如果是连续流形，我们习惯认为相邻点是"平滑连接"的。但在离散格点上，两个希尔伯特空间 $\mathcal{H}_x$ 和 $\mathcal{H}_{x+1}$ 是完全分离的代数对象。要比较或叠加这两个空间的向量，必须先建立一个**比较标准**，即平行移动协议。

### 4.3.2 恢复对称性：作为平行移动的威尔逊线

为了使物理定律在局域基底变换下保持不变（即物理实在不依赖于描述者的参考系选择），我们必须引入一个新的自由度来"吸收"这个相位差。这个自由度存在于连接两个格点的边（Link）上。

**定义 4.3.2 (连接变量 / Link Variable)**

对于格点图 $\Lambda$ 上的每一条有向边 $(x, y)$，引入一个幺正算符 $\mathcal{U}_{x,y}$，作用于辅助的"规范寄存器"空间。在 $U(1)$ 规范群（如电磁场）下，它是一个复相位：

$$
\mathcal{U}_{x,y} = e^{i \theta_{x,y}} \in U(1)
$$

我们要求它在局域规范变换下按如下规则变换：

$$
\mathcal{U}_{x,y} \mapsto e^{i\alpha(x)} \mathcal{U}_{x,y} e^{-i\alpha(y)}
$$

**构造 4.3.3 (规范协变导数)**

利用连接变量，我们可以修正 QCA 中的跳跃项，构造出**规范协变跳跃**：

$$
\psi^\dagger(x) \mathcal{U}_{x,x+1} \psi(x+1)
$$

在变换下：

$$
\begin{aligned}

(\psi^\dagger(x) e^{-i\alpha(x)}) (e^{i\alpha(x)} \mathcal{U}_{x,x+1} e^{-i\alpha(x+1)}) (e^{i\alpha(x+1)} \psi(x+1)) \\

= \psi^\dagger(x) \mathcal{U}_{x,x+1} \psi(x+1)

\end{aligned}
$$

该项保持不变。这正是离散版本的协变导数 $D_\mu = \partial_\mu - i A_\mu$ 的原型。在这里，$\mathcal{U}_{x,y}$ 对应于从 $y$ 到 $x$ 的**威尔逊线（Wilson Line）**，即有限距离的平行移动算符：

$$
\mathcal{U}_{x,y} \sim \mathcal{P} \exp\left( i \int_y^x A_\mu dx^\mu \right)
$$

### 4.3.3 离散曲率：帕拉克特（Plaquette）与和乐

连接变量 $\mathcal{U}_{x,y}$ 本身可以通过规范变换变成任何值（例如，对于开链，总可以选规范使得 $\mathcal{U}=1$）。真正的物理信息不蕴含在单条边中，而蕴含在闭合回路中。

**定义 4.3.4 (帕拉克特算符 / Plaquette Operator)**

考虑时空网格上的最小闭合回路（Plaquette），例如由 $x \to x+\hat{\mu} \to x+\hat{\mu}+\hat{\nu} \to x+\hat{\nu} \to x$ 构成的四边形（其中 $\hat{\mu}, \hat{\nu}$ 为单位矢量）。定义回路上的**和乐（Holonomy）**算符：

$$
W_{\mu\nu}(x) = \mathcal{U}_{x, x+\hat{\mu}} \mathcal{U}_{x+\hat{\mu}, x+\hat{\mu}+\hat{\nu}} \mathcal{U}_{x+\hat{\mu}+\hat{\nu}, x+\hat{\nu}} \mathcal{U}_{x+\hat{\nu}, x}
$$

在 $U(1)$ 情形下，这是一系列相位的和：

$$
W_{\mu\nu}(x) = \exp\left( i (\theta_{x, x+\hat{\mu}} + \theta_{x+\hat{\mu}, x+\hat{\mu}+\hat{\nu}} - \theta_{x+\hat{\nu}, x+\hat{\mu}+\hat{\nu}} - \theta_{x, x+\hat{\nu}}) \right) \equiv e^{i \Phi_{\mu\nu}(x)}
$$

**物理意义：离散曲率**

这个相位 $\Phi_{\mu\nu}(x)$ 是**规范不变**的可观测量。它量化了当一个矢量沿闭合路径平行移动一周后产生的相移。根据几何定义，这正是**曲率**。

* 在空间-空间面上，它对应**磁通量**（Magnetic Flux）。

* 在时间-空间面上，它对应**电场**（Electric Field，通过时间步的演化相位差体现）。

### 4.3.4 连续极限：从格点到麦克斯韦与杨-米尔斯

为了证明这一离散结构在宏观上等价于我们熟悉的场论，我们再次取长波极限。

**定理 4.3.5 (杨-米尔斯作用量的涌现)**

设格距为 $a$，连接变量与连续规范势 $A_\mu(x)$ 的关系为 $\mathcal{U}_{x, x+\hat{\mu}} \approx e^{i a g A_\mu(x)}$，其中 $g$ 为耦合常数。

当 $a \to 0$ 时，帕拉克特算符的实部（对应于威尔逊作用量）收敛于连续杨-米尔斯作用量：

$$
\sum_{P} \left( 1 - \frac{1}{N} \operatorname{Re} \operatorname{Tr} W_P \right) \xrightarrow{a \to 0} \int d^4x \, \frac{1}{4} F_{\mu\nu}^a F^{a\mu\nu}
$$

其中 $F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu + ig [A_\mu, A_\nu]$ 为场强张量。

**证明概要**：

1.  **泰勒展开**：利用 Baker-Campbell-Hausdorff 公式展开乘积 $W_{\mu\nu}$。

    $$
    W_{\mu\nu}(x) \approx \exp\left( i a^2 g (\partial_\mu A_\nu - \partial_\nu A_\mu + ig [A_\mu, A_\nu]) + O(a^3) \right)
    $$

2.  **识别场强**：指数上的项正是 $i a^2 g F_{\mu\nu}$。

3.  **展开余弦**：对于威尔逊作用量 $S_W = \sum (1 - \cos(a^2 g F_{\mu\nu})) \approx \sum \frac{1}{2} (a^2 g F_{\mu\nu})^2$。

4.  **积分极限**：求和 $\sum$ 转化为积分 $\frac{1}{a^4} \int d^4x$。因子 $a^4$ 与 $(a^2)^2$ 抵消，留下正比于 $\int F^2$ 的项。

**结论 4.3.6**

规范场论并非因为"美学"或"对称性原理"被强加于物理学，而是**离散时空几何一致性**的必然要求。

* 物质（费米子）在格点上定义。

* 为了比较相邻格点的物质，必须引入连接器（威尔逊线）。

* 连接器的非平凡结构（和乐）表现为力场（电磁力、强力）。

这完成了从离散本体论到连续相互作用场论的推导闭环。在下一节，我们将探讨对称性破缺与恢复，解释为何宏观上我们会看到洛伦兹对称性，尽管微观格点显然破坏了它。

