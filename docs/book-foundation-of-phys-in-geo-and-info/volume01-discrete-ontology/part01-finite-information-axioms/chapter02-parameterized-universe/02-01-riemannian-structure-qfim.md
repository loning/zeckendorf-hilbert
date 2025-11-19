### 第二章：参数化宇宙与信息几何

**2.1 状态空间的黎曼结构：量子费希尔信息度量（QFIM）的构造**

在第一章中，我们确立了物理实在的希尔伯特空间维数是有限的，且量子信息是其本体论基础。这就引出了一个深刻的问题：如果世界的基础是离散的量子态，那么我们所熟悉的"连续时空几何"从何而来？

本节将论证，几何并非先验存在的背景舞台，而是从量子状态空间的统计结构中涌现的派生量。我们将通过严格的数学推导，证明量子态空间天然具备黎曼流形结构，其上的距离度量——量子费希尔信息度量（Quantum Fisher Information Metric, QFIM）——即为物理世界最底层的"尺子"。

#### 2.1.1 从希尔伯特空间到射影流形

在标准量子力学中，物理态通常由希尔伯特空间 $\mathcal{H}$ 中的非零矢量 $|\psi\rangle$ 描述。然而，物理态具有两个重要的冗余性：

1.  **归一化冗余**：$|\psi\rangle$ 与 $c|\psi\rangle$ ($c \in \mathbb{R}^+$) 描述同一物理态。

2.  **相位冗余**：$|\psi\rangle$ 与 $e^{i\phi}|\psi\rangle$ ($\phi \in \mathbb{R}$) 描述同一物理态。

因此，真正的物理状态空间不是线性空间 $\mathcal{H} \cong \mathbb{C}^{N}$，而是去除上述冗余后的商空间，即复射影空间（Complex Projective Space）：

$$\mathcal{P}(\mathcal{H}) \cong \mathbb{C}P^{N-1} = \mathbb{C}^{N} / \mathbb{C}^*$$

这是一个紧致的、单连通的凯勒流形（Kähler Manifold）。在这个流形上，我们不能简单地使用线性空间中的欧几里得距离 $\|\psi_1 - \psi_2\|$，而必须定义一个内禀的几何度量。

**定义 2.1.1 (参数化量子态)**

设物理系统由一组实参数 $\boldsymbol{\theta} = (\theta^1, \theta^2, \dots, \theta^M)$ 描述，这些参数可以是经典外场、时空坐标或系统内部的控制量。系统处于参数化纯态 $|\psi(\boldsymbol{\theta})\rangle \in \mathcal{H}$。我们要求映射 $\boldsymbol{\theta} \mapsto |\psi(\boldsymbol{\theta})\rangle$ 是光滑的，且满足归一化条件 $\langle \psi(\boldsymbol{\theta}) | \psi(\boldsymbol{\theta}) \rangle = 1$。

#### 2.1.2 距离即由可区分性定义：富比尼-施图迪度量的推导

在"It from Bit"的本体论中，两个物理态之间的"距离"应当衡量它们在统计上的**可区分度**（Distinguishability）。若两个态完全重合，距离为零；若它们正交（完全可区分），距离最大。

我们引入**保真度**（Fidelity）作为重叠程度的度量：

$$F(\boldsymbol{\theta}, \boldsymbol{\theta} + d\boldsymbol{\theta}) = \big| \langle \psi(\boldsymbol{\theta}) | \psi(\boldsymbol{\theta} + d\boldsymbol{\theta}) \rangle \big|$$

物理距离 $ds^2$ 定义为偏离完美重叠的程度：

$$ds^2 \equiv 1 - F^2(\boldsymbol{\theta}, \boldsymbol{\theta} + d\boldsymbol{\theta})$$

这一距离在物理上对应于：当我们在参数空间移动微小量 $d\boldsymbol{\theta}$ 时，量子态发生的可观测变化的量度。

**定理 2.1.2 (量子几何张量的构造)**

对参数化量子态 $|\psi(\boldsymbol{\theta})\rangle$ 进行泰勒展开至二阶，可得参数空间上的线元形式：

$$ds^2 = \frac{1}{2} g_{\mu\nu} d\theta^\mu d\theta^\nu$$

其中 $g_{\mu\nu}$ 为**量子费希尔信息度量**（亦称富比尼-施图迪度量，Fubini-Study Metric），其显式为：

$$g_{\mu\nu} = 4 \operatorname{Re} \left( \langle \partial_\mu \psi | \partial_\nu \psi \rangle - \langle \partial_\mu \psi | \psi \rangle \langle \psi | \partial_\nu \psi \rangle \right)$$

此处 $\partial_\mu \equiv \partial / \partial \theta^\mu$。

*证明*：

考虑微小位移 $d\boldsymbol{\theta}$，态矢量展开为：

$$|\psi(\boldsymbol{\theta} + d\boldsymbol{\theta})\rangle = |\psi\rangle + |\partial_\mu \psi\rangle d\theta^\mu + \frac{1}{2} |\partial_\mu \partial_\nu \psi\rangle d\theta^\mu d\theta^\nu + \mathcal{O}(d\theta^3)$$

计算内积 $\langle \psi | \psi + d\psi \rangle$：

$$\langle \psi | \psi + d\psi \rangle = 1 + \langle \psi | \partial_\mu \psi \rangle d\theta^\mu + \frac{1}{2} \langle \psi | \partial_\mu \partial_\nu \psi \rangle d\theta^\mu d\theta^\nu$$

利用归一化条件 $\langle \psi | \psi \rangle = 1$ 的导数性质：

$$\partial_\mu \langle \psi | \psi \rangle = \langle \partial_\mu \psi | \psi \rangle + \langle \psi | \partial_\mu \psi \rangle = 0 \implies \operatorname{Re}(\langle \psi | \partial_\mu \psi \rangle) = 0$$

$$\partial_\mu \partial_\nu \langle \psi | \psi \rangle = \langle \partial_\mu \partial_\nu \psi | \psi \rangle + \langle \partial_\mu \psi | \partial_\nu \psi \rangle + \dots = 0$$

可得 $\langle \psi | \partial_\mu \partial_\nu \psi \rangle + c.c. = - (\langle \partial_\mu \psi | \partial_\nu \psi \rangle + \langle \partial_\nu \psi | \partial_\mu \psi \rangle)$。

将内积模方展开至二阶：

$$

\begin{aligned}

|\langle \psi | \psi + d\psi \rangle|^2 &= \left( 1 + \langle \psi | d\psi \rangle + \frac{1}{2} \langle \psi | d^2\psi \rangle \right) \left( 1 + \langle d\psi | \psi \rangle + \frac{1}{2} \langle d^2\psi | \psi \rangle \right) \\

&\approx 1 + (\langle \psi | d\psi \rangle + c.c.) + \langle d\psi | d\psi \rangle + \frac{1}{2}(\langle \psi | d^2\psi \rangle + c.c.) + |\langle \psi | d\psi \rangle|^2

\end{aligned}

$$

代入导数关系化简，最终得到距离 $ds^2 = 1 - |\langle \psi | \psi + d\psi \rangle|^2$ 的二阶项为：

$$ds^2 = \left( \langle \partial_\mu \psi | \partial_\nu \psi \rangle - \langle \partial_\mu \psi | \psi \rangle \langle \psi | \partial_\nu \psi \rangle \right) d\theta^\mu d\theta^\nu$$

上式括号内的张量通常记为 $\chi_{\mu\nu}$，称为**量子几何张量**（Quantum Geometric Tensor, QGT）。其定义为：

$$\chi_{\mu\nu} \equiv \langle \partial_\mu \psi | (1 - |\psi\rangle\langle\psi|) | \partial_\nu \psi \rangle$$

由于 $ds^2$ 必须为实数，实际上物理距离由 $\chi_{\mu\nu}$ 的对称实部决定。在信息几何的标准定义中，通常取因子 4 以匹配经典费希尔信息，即得 $g_{\mu\nu} = 4 \operatorname{Re}(\chi_{\mu\nu})$。$\square$

#### 2.1.3 黎曼度量与辛结构的统一：量子几何张量

定理 2.1.2 揭示了一个深刻的结构：量子几何张量 $\chi_{\mu\nu}$ 并非纯实数，它自然分解为实部和虚部：

$$\chi_{\mu\nu} = \frac{1}{4} g_{\mu\nu} - \frac{i}{2} \Omega_{\mu\nu}$$

其中：

* **实部 $g_{\mu\nu}$**：是对称的黎曼度量张量（QFIM），度量参数空间中的"距离"。它描述了量子态在参数变化下的**正交性速率**。

* **虚部 $\Omega_{\mu\nu}$**：是反对称的辛形式（Symplectic Form），即著名的**贝里曲率**（Berry Curvature）：

    $$\Omega_{\mu\nu} = i \left( \langle \partial_\mu \psi | \partial_\nu \psi \rangle - \langle \partial_\nu \psi | \partial_\mu \psi \rangle \right)$$

    它描述了量子态在参数空间闭合路径演化中积累的**几何相位**。

**推论 2.1.3 (几何与拓扑的统一)**

在参数化量子宇宙中，黎曼几何（引力/距离）与辛几何（规范场/相位）是同一物理对象——量子几何张量——的两个侧面。距离衡量了信息的差异，而曲率衡量了信息的完整性（Holonomy）。

#### 2.1.4 物理诠释：克拉美-罗下界（Cramér-Rao Bound）

为什么我们要把这个度量称为"信息度量"？因为它直接决定了物理测量的极限精度。

考虑对参数 $\theta$ 的任意无偏估计量 $\hat{\theta}$。根据量子克拉美-罗定理（Quantum Cramér-Rao Theorem），估计量的方差受限于 QFIM 的逆：

$$\mathrm{Var}(\hat{\theta}) \ge \frac{1}{N_{meas} g_{\theta\theta}}$$

其中 $N_{meas}$ 为测量次数。

这赋予了黎曼几何以严格的操作主义意义：

* **大 $g_{\mu\nu}$**：意味着参数微小的变化会导致量子态急剧变化（正交化），因此该处的物理参数很容易被精确测量（高分辨区）。

* **小 $g_{\mu\nu}$**：意味着量子态对参数变化不敏感，物理实在在该区域是"模糊"的。

**总结**

本节我们完成了从离散量子态到连续黎曼几何的跨越。我们证明了，只要物理系统可以被参数化，其参数空间就必然具备黎曼结构。这个结构不是人为设定的，而是由量子态区分度的统计学性质（QFIM）唯一确定的。

在接下来的章节中，我们将看到，如果我们把这些"参数"解释为时空坐标，那么广义相对论中的爱因斯坦场方程，实际上就是这一信息几何在最大纠缠熵原理下的动力学方程。

