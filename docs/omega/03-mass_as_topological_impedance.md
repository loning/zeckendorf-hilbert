# 质量作为拓扑阻抗：狄拉克-QCA 模型中的自指散射与手性对称性破缺

**Mass as Topological Impedance: Self-Referential Scattering and Chiral Symmetry Breaking in Dirac-QCA**

---

## 摘要

在相对论量子场论中，基本粒子的质量通常通过与希格斯场的汤川耦合引入，并作为自由参数出现，没有微观的信息论或拓扑起源。然而，在量子元胞自动机（QCA）本体论中，宇宙被建模为格点上的离散、严格因果的量子更新规则，其内在速度极限 $c$ 由局部幺正算子的光锥设定。这提出了一个结构性问题：为什么某些激发以亚光速传播并表现为有质量粒子，而不是饱和更新速度的无质量信号？

在这项工作中，我们处理一个一维狄拉克型 QCA，将其表述为具有内部（硬币）自由度的离散时间量子行走。基于早期显示狄拉克方程作为此类模型的连续极限而出现的结果，我们证明了有效狄拉克质量无非是混合左右移动分量的局部自指散射过程的振幅。在动量空间的 Floquet 算子层面，这种混合导致布洛赫向量在布里渊区上的非平凡绕数，将模型置于手性对称的 Floquet 拓扑相中。非零质量因此获得了拓扑阻抗的解释：一种拓扑保护的阻碍，阻止手性分量解耦为纯粹的弹道、类光传播。

我们证明这种机制产生 Zitterbewegung（颤动）作为局部背散射的不可避免的后果。在狄拉克连续极限中，位置算符分解为具有群速度 $v_{\mathrm{ext}}$ 的均匀漂移项和频率为 $\omega_{\mathrm{ZB}} = 2 E / \hbar$ 的振荡项，其中 $E$ 是准能量。我们将这种振荡解释为"内部运动"，并证明了一个精确的分解

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2},
$$

其中 $v_{\mathrm{int}}$ 定义为速度算符的标准差。因此，每个激发都饱和了微观信息速度界限 $c$，但每当质量间隙非零时，拓扑强制分配的这部分预算被困在内部振荡中。这为狄拉克-QCA 模型中的质量提供了纯粹的运动学、拓扑和信息论解释，与传统的希格斯型质量产生机制兼容且互补。

---

## 关键词

量子元胞自动机；离散时间量子行走；狄拉克方程；拓扑质量；绕数；手性对称性；Zitterbewegung；Floquet 拓扑相；信息速度守恒

---

## 引言与历史背景

### 质量及其开放的概念地位

在相对论量子场论（QFT）中，自由狄拉克方程

$$
\left( \mathrm{i} \hbar \gamma^{\mu} \partial_{\mu} - m c \right) \psi = 0
$$

将静质量 $m$ 作为拉格朗日量中的参数引入，而在标准模型中，质量通过汤川耦合到希格斯场而产生。尽管这种机制在现象学上很成功，但它留下了两个概念性问题：

1. 费米子质量的数值是自由参数，不是由更深层的原理确定的。

2. 质量项 $m \bar{\psi} \psi$ 显式地破坏了手性对称性，但这种破坏并不直接与任何拓扑不变量或离散信息处理结构相关联。

在标准模型之外，已知许多"拓扑质量"机制，例如 $(2+1)$ 维规范理论中的 Chern–Simons 项，或格点 QCD 中的畴壁和重叠费米子，其中质量间隙与指标定理和谱流相关联。然而，这些机制仍然预设了连续量子场，并且它们通常用有效作用量而不是底层离散信息动力学来表述。

### QCA 和量子行走作为离散狄拉克动力学

量子元胞自动机（QCA）提供了一种替代本体论，其中动力学由有限维量子系统格点上的因果、平移不变的幺正算子定义。量子场论可能从这样的自动机中出现的想法可以追溯到费曼关于物理可以用量子计算机模拟的建议，此后由 Bisio、D'Ariano、Tosini 等人详细发展，他们构造了其长波长极限重现 Weyl、Dirac 和 Maxwell 方程的 QCA。

在一个空间维度中，狄拉克型动力学的特别简单的实现由离散时间量子行走（DTQW）提供，其中双分量"硬币"自由度控制向左和向右的条件位移。Strauch 表明，对于硬币参数和格点间距的适当缩放，DTQW 的连续极限重现了 $(1+1)$ 维狄拉克方程，后续工作将这种联系推广到更高维度和更一般的行走协议。

同时，QCA 的系统理论已经发展起来，包括将一维自动机分类到同伦的局域性和指标定理。在这种设置中，DTQW 可以被视为具有内部自由度（硬币）和有限传播半径的一维 QCA 的特殊情况。

### 拓扑相和量子行走

拓扑能带理论最初是为静态哈密顿量开发的，已扩展到周期驱动（Floquet）系统，其中一个周期的时间演化算子扮演 Floquet 幺正算子的角色。这种幺正算子的拓扑分类，特别是在存在手性对称性的情况下，自然适用于 DTQW。Kitagawa 及其合作者表明，分步和多步量子行走实现了一组丰富的一维拓扑相，具有整数绕数，并在不同不变量的域之间的边界处伴随有鲁棒的边缘态。

Asbóth 和 Obuse 后来为 Floquet 量子行走制定了体-边界对应关系和手性对称性的系统定义，识别了一个 $\mathbb{Z} \times \mathbb{Z}$ 值的拓扑不变量，控制零和 $\pi$ 准能量边缘态。使用光子和冷原子平台的实验直接观察了这些拓扑束缚态，并测量了绕数和动力学拓扑序参数。

重要的是，对于我们的目的，即使是最简单的单硬币量子行走，当用适当的硬币旋转表述时，对于一般的硬币角度也表现出隐藏的手性对称性和非平凡绕数，间隙闭合和绕数变化仅在硬币参数的特殊值处发生。

### 狄拉克动力学和 QCA 中的 Zitterbewegung

Zitterbewegung（ZB），狄拉克方程预测的快速振荡运动，长期以来被理解为由波包的正负能量分量之间的干涉产生。在海森堡图像中，位置算符分解为均匀漂移项加上频率为 $2 E / \hbar$ 的振荡项，速度算符具有特征值 $\pm c$，因此即使平均运动是亚光速的，速度也在这些极值之间波动。

在近似狄拉克动力学的 QCA 和量子行走模型中，同样的现象已被分析和数值研究：Bisio 等人构造的狄拉克 QCA 表现出 ZB 和 Klein 隧穿，振荡频率和振幅在适当极限下与连续狄拉克理论匹配。

### 信息速度守恒和质量的作用

在之前的工作中，我们为 QCA 型模型中的局部激发提出了一个信息论守恒定律，即

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2},
$$

其中 $v_{\mathrm{ext}}$ 测量激发在物理空间中的有效群速度，$v_{\mathrm{int}}$ 量化希尔伯特空间中的内部演化速率，用速度算符的方差或 Fubini–Study 度量表示。这种关系表达了"信息速度预算"固定在 $c$ 的想法，无质量激发将其全部分配给平移运动，而有质量激发将其一部分转移到内部振荡中。

本文在狄拉克-QCA 设置中具体实现了这一想法，并将其与拓扑不变量联系起来。

### 目标与贡献

中心目标是重新解释狄拉克方程的质量参数，正如在狄拉克-QCA 模型中实现的那样，作为拓扑阻抗：将左右移动自由度解耦为独立弹道通道的量化阻碍。具体来说，我们：

1. 将一维狄拉克型 QCA 指定为具有单个硬币角度的离散时间量子行走，并在标准局域性和均匀性假设下，证明其长波长极限重现了 $(1+1)$ 维狄拉克方程，质量 $m$ 由硬币角度确定。

2. 证明动量空间中的时间步幺正算子具有手性对称性，并为任何非零硬币角度定义了布洛赫球上布洛赫向量的非平凡绕数，这与量子行走中 Floquet 拓扑相的早期分类一致。当准能量 $0$ 或 $\pi$ 处的间隙闭合时，绕数才会改变，对应于 $m = 0$。

3. 给出硬币角度作为局部自指散射振幅的散射理论解释，该振幅反复将左移分量转换为右移分量，反之亦然。这产生了亚光速群速度和 Zitterbewegung，我们将相关的能量间隙解释为阻止纯粹类光传播的拓扑阻抗。

4. 在狄拉克连续极限中推导出精确的分解

   $$
   v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}
   $$
   
   对于任意状态，通过将 $v_{\mathrm{ext}}$ 定义为速度算符的期望值，$v_{\mathrm{int}}$ 定义为其方差的平方根，从而为内部运动提供精确的信息论意义并将其与质量联系起来。

5. 讨论拓扑阻抗图像如何与传统的质量产生机制相互作用，并提出在光子和冷原子量子行走平台上观察群速度、内部振荡和拓扑不变量之间权衡的实验方案。

---

## 模型与假设

### 格点、希尔伯特空间和局域性

我们考虑一个间距为 $a > 0$ 的一维空间格点，其格点由整数 $n \in \mathbb{Z}$ 标记，对应于位置 $x = n a$。时间是离散的，步长为 $\Delta t > 0$，因此 $t = m \Delta t$，其中 $m \in \mathbb{Z}$。微观因果速度由下式固定

$$
c = \frac{a}{\Delta t},
$$

这将在连续极限中被识别为涌现的光速。

在每个格点处，局部希尔伯特空间是二维硬币空间 $\mathbb{C}^{2}$，解释为手性或左/右自由度。全局希尔伯特空间是

$$
\mathcal{H} = \ell^{2}(\mathbb{Z}) \otimes \mathbb{C}^{2}.
$$

我们在位置-硬币基中写出状态为

$$
\Psi = \sum_{n \in \mathbb{Z}} \left( \psi_{L}(n) \lvert n \rangle \otimes \lvert L \rangle + \psi_{R}(n) \lvert n \rangle \otimes \lvert R \rangle \right),
$$

或以列向量形式

$$
\Psi(n, t) = \begin{pmatrix} \psi_{L}(n, t) \\ \psi_{R}(n, t) \end{pmatrix}.
$$

我们假设一个单步、平移不变的 QCA 演化算子

$$
U : \mathcal{H} \to \mathcal{H},
$$

它是幺正的、均匀的（与空间平移对易）、具有有限传播半径的因果性（每个格点在单个时间步内仅与有界邻域耦合）并且具有宇称对称性。

### 硬币算子和条件位移

时间步幺正算子被取为局部硬币旋转后跟条件位移的分解：

$$
U = S \, C(\theta),
$$

其中 $\theta \in [0,\pi]$ 是实参数。

硬币算子是形式为

$$
C(\theta) = \sum_{n \in \mathbb{Z}} \lvert n \rangle \langle n \rvert \otimes R(\theta),
$$

的格点局部幺正算子，其中

$$
R(\theta) = \mathrm{e}^{-\mathrm{i} \theta \sigma_{x}}
= \begin{pmatrix}
\cos \theta & -\mathrm{i} \sin \theta \\
-\mathrm{i} \sin \theta & \cos \theta
\end{pmatrix}
$$

而 $\sigma_{x}$ 是通常的泡利矩阵。

条件位移算子将左右分量向相反方向移动：

$$
S = \sum_{n \in \mathbb{Z}} \left( \lvert n - 1 \rangle \langle n \rvert \otimes \lvert L \rangle \langle L \rvert
+ \lvert n + 1 \rangle \langle n \rvert \otimes \lvert R \rangle \langle R \rvert \right).
$$

等价地，

$$
S = \sum_{n \in \mathbb{Z}} \lvert n \rangle \langle n \rvert \otimes \left( \lvert L \rangle \langle L \rvert \, T_{+} + \lvert R \rangle \langle R \rvert \, T_{-} \right),
$$

其中 $T_{\pm}$ 是格点平移算子（$T_{\pm} \lvert n \rangle = \lvert n \pm 1 \rangle$）。

一个时间步的演化方程是

$$
\Psi(t + \Delta t) = U \Psi(t).
$$

在位置空间中，这产生耦合的更新方程：

$$
\begin{aligned}
\psi_{L}(n, t + \Delta t) &= \cos \theta \, \psi_{L}(n + 1, t) - \mathrm{i} \sin \theta \, \psi_{R}(n + 1, t), \\
\psi_{R}(n, t + \Delta t) &= - \mathrm{i} \sin \theta \, \psi_{L}(n - 1, t) + \cos \theta \, \psi_{R}(n - 1, t).
\end{aligned}
$$

我们将参数 $\theta$ 解释为控制左右移动分量之间局部"自散射"的强度；$\theta = 0$ 对应于以速度 $c$ 的纯粹弹道运动，而 $\theta \neq 0$ 引入了背散射。

### 动量空间表示和有效哈密顿量

通过平移不变性，我们可以通过

$$
\Psi(n, t) = \int_{-\pi}^{\pi} \frac{\mathrm{d} k}{2 \pi} \, \mathrm{e}^{\mathrm{i} k n} \, \widetilde{\Psi}(k, t),
$$

转换到动量空间，其中 $k \in [-\pi,\pi]$ 是无量纲格点动量；物理动量是 $p = \hbar k / a$。

位移算子在 $k$ 中是对角的，

$$
\widetilde{S}(k) = \mathrm{e}^{-\mathrm{i} k \sigma_{z}},
$$

动量空间中的时间步幺正算子是

$$
\widetilde{U}(k) = \widetilde{S}(k) R(\theta)
= \begin{pmatrix}
\mathrm{e}^{-\mathrm{i} k} \cos \theta & - \mathrm{i} \mathrm{e}^{-\mathrm{i} k} \sin \theta \\
\mathrm{i} \mathrm{e}^{\mathrm{i} k} \sin \theta & \mathrm{e}^{\mathrm{i} k} \cos \theta
\end{pmatrix}.
$$

我们通过

$$
\widetilde{U}(k) = \exp\left( - \frac{\mathrm{i}}{\hbar} H_{\mathrm{eff}}(k) \, \Delta t \right),
$$

定义 Floquet 准能量 $E(k)$ 和有效哈密顿量 $H_{\mathrm{eff}}(k)$。

$\widetilde{U}(k)$ 的特征值是 $\mathrm{e}^{-\mathrm{i} E(k) \Delta t}$ 和 $\mathrm{e}^{+\mathrm{i} E(k) \Delta t}$，其中

$$
\cos \bigl( E(k) \Delta t \bigr) = \cos \theta \, \cos k,
$$

这是硬币量子行走的众所周知的色散关系。

我们可以写成

$$
H_{\mathrm{eff}}(k) = E(k) \, \hat{\boldsymbol{n}}(k) \cdot \boldsymbol{\sigma},
$$

其中 $\hat{\boldsymbol{n}}(k)$ 是布洛赫球上的单位向量。

---

## 主要结果（定理与对齐）

在本节中，我们总结主要定理；详细的证明在后续章节和附录中给出。

### 定理 1（狄拉克连续极限）

设格点间距和时间步长满足 $a = c \, \Delta t$，并将硬币角度缩放为

$$
\theta = \frac{m c^{2}}{\hbar} \, \Delta t + \mathcal{O}(\Delta t^{3}),
$$

其中固定参数 $c > 0$ 和 $m \ge 0$。考虑振幅在格点尺度上缓慢变化的初始状态，即

$$
\psi_{L/R}(n \pm 1, 0) - \psi_{L/R}(n, 0) = \mathcal{O}(a)
$$

在 $n$ 中一致成立。那么在极限 $\Delta t \to 0$ 中，离散演化收敛到 $(1+1)$ 维连续狄拉克方程，误差为 $\mathcal{O}(\Delta t^{2})$ 阶，

$$
\mathrm{i} \hbar \, \partial_{t} \Psi(x,t)
= \left( - \mathrm{i} \hbar c \, \sigma_{z} \partial_{x} + m c^{2} \sigma_{x} \right) \Psi(x,t),
$$

其中 $x = n a$。收敛在算子范数中在任何有限时间区间上成立，并且对于支撑在紧致动量区域中的波包成立。

这一结果改进并专门化了量子行走和狄拉克型 QCA 的已建立的连续极限构造。

### 定理 2（手性对称性和绕数）

定义手性对称性算子

$$
\Gamma = \sigma_{x}.
$$

那么对于所有动量 $k$，Floquet 幺正算子满足

$$
\Gamma \, \widetilde{U}(k) \, \Gamma = \widetilde{U}^{\dagger}(k),
$$

因此 QCA 属于手性对称的 Floquet 类 AIII。相应的一维拓扑不变量（绕数）是

$$
\mathcal{W} = \frac{1}{2 \pi \mathrm{i}} \int_{-\pi}^{\pi} \mathrm{d} k \,
\mathrm{Tr} \left( \Gamma \, \widetilde{U}^{-1}(k) \, \partial_{k} \widetilde{U}(k) \right).
$$

对于当前模型，

$$
\mathcal{W} =
\begin{cases}
0, & \theta = 0 \text{ 或 } \theta = \pi, \\
1, & 0 < \theta < \pi.
\end{cases}
$$

因此，如定理 1 中定义的任何非零质量参数 $m$ 对应于拓扑非平凡的 Floquet 相，该相不能在不闭合 $E = 0$ 或 $E = \pi / \Delta t$ 处的准能量间隙的情况下绝热变形到无质量情况。这与单硬币和分步量子行走中拓扑相的早期分析一致。

### 定理 3（质量作为自指散射）

在位置空间中，格点 $n$ 处的单步演化可以写成局部散射矩阵对由左右移动振幅组成的入射双分量场的作用。明确地，在动量空间中，这等价于具有反射和透射振幅的双通道幺正散射

$$
r(\theta) = - \mathrm{i} \sin \theta,
\quad
t(\theta) = \cos \theta.
$$

对于在动量 $k_{0}$ 附近尖锐峰值的波包，群速度满足

$$
v_{\mathrm{ext}}(k_{0},\theta) = \frac{\partial E(k)}{\partial p} \Bigg\rvert_{k=k_{0}}
= \frac{1}{\hbar} \frac{\partial E(k)}{\partial k} \, a,
$$

色散关系为 $\cos(E \Delta t) = \cos \theta \cos k$。在定理 1 描述的狄拉克连续极限中，这产生

$$
v_{\mathrm{ext}}(p) \approx \frac{c^{2} p}{\sqrt{p^{2} c^{2} + m^{2} c^{4}}}
$$

和能量间隙

$$
E(p) \approx \sqrt{p^{2} c^{2} + m^{2} c^{4}}.
$$

因此，相同的参数 $\theta$ 同时控制（i）狄拉克极限中的质量间隙大小和（ii）左右移动分量之间的局部背散射强度。这种局部散射的重复应用产生有效惯性：混合越强（$\theta$ 越大），给定动量下的渐近群速度越小。我们将此解释为质量来自将激发与其自身历史联系起来的自指散射过程。

### 定理 4（Zitterbewegung 和信息速度分解）

设 $H = c p \sigma_{z} + m c^{2} \sigma_{x}$ 表示连续极限中的狄拉克哈密顿量，并定义速度算符

$$
\hat{v} = \frac{\mathrm{i}}{\hbar} [H, X] = c \sigma_{z}.
$$

那么对于任何归一化状态 $\Psi$，

$$
\langle \hat{v}^{2} \rangle = c^{2},
$$

我们可以定义

$$
v_{\mathrm{ext}} = \langle \hat{v} \rangle,
\quad
v_{\mathrm{int}} = \sqrt{ \langle \hat{v}^{2} \rangle - \langle \hat{v} \rangle^{2} }.
$$

对于所有状态，

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}.
$$

此外，在海森堡图像中，位置算符分解为

$$
X(t) = X(0) + v_{\mathrm{ext}} t + \Xi(t),
$$

其中 $\Xi(t)$ 是频率为 $\omega_{\mathrm{ZB}} = 2 E / \hbar$、振幅与 $\hbar c / (2 E)$ 成正比的振荡项。这是通常的 Zitterbewegung 项，我们因此将其解释为内部信息速度 $v_{\mathrm{int}}$ 的表现。有质量激发必然具有 $0 < \lvert v_{\mathrm{ext}} \rvert < c$ 和相应的非零 $v_{\mathrm{int}}$；无质量激发满足 $\lvert v_{\mathrm{ext}} \rvert = c$ 和 $v_{\mathrm{int}} = 0$。

在离散 QCA 中，在长波长区域的有效哈密顿量和速度算子层面存在类似的分解，Zitterbewegung 表现为叠加在群速度漂移上的位置算子期望值的快速振荡。

---

## 证明

在本节中，我们概述主要论证；详细的逐步推导推迟到附录。

### 定理 1 的证明（狄拉克连续极限）

我们设 $a = c \Delta t$ 和 $\theta = (m c^{2} / \hbar) \Delta t + \mathcal{O}(\Delta t^{3})$，并工作到 $\Delta t$ 的一阶。将位置空间更新方程重写为

$$
\begin{aligned}
\psi_{L}(n, t + \Delta t)
&= \cos \theta \, \psi_{L}(n + 1, t) - \mathrm{i} \sin \theta \, \psi_{R}(n + 1, t), \\
\psi_{R}(n, t + \Delta t)
&= - \mathrm{i} \sin \theta \, \psi_{L}(n - 1, t) + \cos \theta \, \psi_{R}(n - 1, t),
\end{aligned}
$$

我们将所有项在 $\Delta t$ 中泰勒展开。使用

$$
\cos \theta = 1 + \mathcal{O}(\Delta t^{2}),
\quad
\sin \theta = \frac{m c^{2}}{\hbar} \Delta t + \mathcal{O}(\Delta t^{3}),
$$

和

$$
\psi_{L/R}(n \pm 1, t) = \psi_{L/R}(x \pm a, t)
= \psi_{L/R}(x, t) \pm a \partial_{x} \psi_{L/R}(x,t) + \mathcal{O}(a^{2}),
$$

其中 $x = n a$，我们得到一阶

$$
\begin{aligned}
\psi_{L}(x, t) + \Delta t \, \partial_{t} \psi_{L}(x,t)
&= \psi_{L}(x,t) + c \Delta t \, \partial_{x} \psi_{L}(x,t)
- \mathrm{i} \frac{m c^{2}}{\hbar} \Delta t \, \psi_{R}(x,t) + \mathcal{O}(\Delta t^{2}), \\
\psi_{R}(x, t) + \Delta t \, \partial_{t} \psi_{R}(x,t)
&= \psi_{R}(x,t) - c \Delta t \, \partial_{x} \psi_{R}(x,t)
- \mathrm{i} \frac{m c^{2}}{\hbar} \Delta t \, \psi_{L}(x,t) + \mathcal{O}(\Delta t^{2}).
\end{aligned}
$$

从两边减去 $\psi_{L/R}(x,t)$ 并除以 $\Delta t$ 得到

$$
\begin{aligned}
\partial_{t} \psi_{L} - c \partial_{x} \psi_{L} &= - \mathrm{i} \frac{m c^{2}}{\hbar} \psi_{R} + \mathcal{O}(\Delta t), \\
\partial_{t} \psi_{R} + c \partial_{x} \psi_{R} &= - \mathrm{i} \frac{m c^{2}}{\hbar} \psi_{L} + \mathcal{O}(\Delta t).
\end{aligned}
$$

乘以 $\mathrm{i} \hbar$ 并以旋量形式 $\Psi = (\psi_{L}, \psi_{R})^{\mathsf{T}}$ 收集项，我们得到

$$
\mathrm{i} \hbar \, \partial_{t} \Psi
= \left( - \mathrm{i} \hbar c \, \sigma_{z} \partial_{x} + m c^{2} \sigma_{x} \right) \Psi
+ \mathcal{O}(\Delta t),
$$

这就是所需的狄拉克方程，误差为 $\mathcal{O}(\Delta t)$ 修正。使用傅里叶方法和范数估计的更仔细分析表明，对于具有有界动量支撑的波包，误差在任何固定时间区间上在算子范数中保持为 $\mathcal{O}(\Delta t)$，这与量子行走的严格连续极限结果一致。

### 定理 2 的证明（手性对称性和绕数）

我们首先验证手性对称性。使用 $\Gamma = \sigma_{x}$ 和 $\widetilde{U}(k)$ 的显式形式，

$$
\widetilde{U}(k)
= \begin{pmatrix}
\mathrm{e}^{-\mathrm{i} k} \cos \theta & - \mathrm{i} \mathrm{e}^{-\mathrm{i} k} \sin \theta \\
\mathrm{i} \mathrm{e}^{\mathrm{i} k} \sin \theta & \mathrm{e}^{\mathrm{i} k} \cos \theta
\end{pmatrix},
$$

我们计算

$$
\Gamma \widetilde{U}(k) \Gamma
= \sigma_{x} \widetilde{U}(k) \sigma_{x}
= \begin{pmatrix}
\mathrm{e}^{\mathrm{i} k} \cos \theta & \mathrm{i} \mathrm{e}^{-\mathrm{i} k} \sin \theta \\
\mathrm{i} \mathrm{e}^{\mathrm{i} k} \sin \theta & \mathrm{e}^{-\mathrm{i} k} \cos \theta
\end{pmatrix}
= \widetilde{U}^{\dagger}(k),
$$

其中最后一个等式来自幺正性和复共轭。因此手性对称性条件成立。

为了计算绕数，我们写成 $\widetilde{U}(k) = \mathrm{e}^{-\mathrm{i} E(k) \hat{\boldsymbol{n}}(k) \cdot \boldsymbol{\sigma}}$，其中

$$
\cos(E \Delta t) = \cos \theta \cos k,
$$

而 $\hat{\boldsymbol{n}}(k)$ 是位于布洛赫球上的布洛赫向量。一个方便的参量化，在 Lam 对 Hadamard 量子行走的分析中使用，是

$$
\hat{\boldsymbol{n}}(k) = \frac{1}{\sin(E \Delta t)}
\begin{pmatrix}
\sin \theta \sin k \\
\sin \theta \cos k \\
\cos \theta \sin k
\end{pmatrix},
$$

在间隙闭合点之外有效，其中 $\sin(E \Delta t) \neq 0$。

手性对称性意味着相关的绕数是 $\hat{\boldsymbol{n}}(k)$ 在垂直于 $\Gamma$ 的平面上的投影的绕数，这里就是 $(yz)$ 平面。当 $k$ 从 $-\pi$ 运行到 $\pi$ 时，向量 $(\sin \theta \cos k, \cos \theta \sin k)$ 对于 $0 < \theta < \pi$ 绕原点一次，对于 $\theta = 0$ 或 $\theta = \pi$ 是平凡的。得到的绕数可以写成

$$
\mathcal{W} = \frac{1}{2 \pi} \int_{-\pi}^{\pi} \mathrm{d} k \, \frac{\partial}{\partial k} \arg\left( \sin \theta \cos k + \mathrm{i} \cos \theta \sin k \right)
=
\begin{cases}
1, & 0 < \theta < \pi, \\
0, & \theta = 0 \text{ 或 } \pi.
\end{cases}
$$

这与已知结果一致，即具有这种硬币旋转的单硬币量子行走位于非平凡的 Floquet 拓扑相中，对于一般的硬币角度，间隙在 $\theta = 0$ 和 $\theta = \pi$ 处闭合。

结合定理 1，它将 $\theta$ 与狄拉克质量 $m$ 联系起来，我们得出结论，任何非零狄拉克质量对应于拓扑非平凡的 QCA 相。

### 定理 3 的证明（自指散射和惯性）

将 $\widetilde{U}(k)$ 解释为双通道散射矩阵从其结构来看是直接的：对角项表示左右移动分量的透射振幅 $t(\theta) = \cos \theta \, \mathrm{e}^{\pm \mathrm{i} k}$，而非对角项表示反射振幅 $r(\theta) = - \mathrm{i} \sin \theta \, \mathrm{e}^{\mp \mathrm{i} k}$，将左移分量转换为右移分量，反之亦然。因此，在每个时间步，行走者经历耦合两个手性通道的局部自散射过程。

色散关系

$$
\cos(E \Delta t) = \cos \theta \cos k
$$

来自 $\widetilde{U}(k)$ 的特征多项式，对 $k$ 求导得到

$$
- \sin(E \Delta t) \, \Delta t \, \frac{\partial E}{\partial k}
= - \cos \theta \sin k.
$$

因此群速度是

$$
v_{\mathrm{ext}}(k,\theta)
= \frac{1}{\hbar} \frac{\partial E}{\partial k} a
= c \, \frac{\cos \theta \sin k}{\sin(E \Delta t)}.
$$

在长波长区域 $\lvert k \rvert \ll 1$ 和小 $\theta$ 中，可以展开

$$
\cos(E \Delta t) \approx 1 - \frac{(E \Delta t)^{2}}{2},
\quad
\cos k \approx 1 - \frac{k^{2}}{2},
\quad
\cos \theta \approx 1 - \frac{\theta^{2}}{2},
$$

导致

$$
E^{2} \approx c^{2} \left( \frac{\hbar k}{a} \right)^{2} + \left( \frac{\hbar \theta}{\Delta t} \right)^{2}
= c^{2} p^{2} + m^{2} c^{4},
$$

其中 $m c^{2} = \hbar \theta / \Delta t$，与定理 1 和狄拉克型量子行走的先前分析一致。

群速度然后简化为熟悉的狄拉克表达式

$$
v_{\mathrm{ext}}(p) = \frac{\partial E}{\partial p}
= \frac{c^{2} p}{\sqrt{p^{2} c^{2} + m^{2} c^{4}}},
$$

当 $m \to 0$ 或 $\lvert p \rvert \to \infty$ 时接近 $c$，对于非零 $m$ 在 $p = 0$ 处消失。控制反射振幅 $r(\theta) = - \mathrm{i} \sin \theta$ 的相同参数 $\theta$ 也控制质量间隙和群速度的抑制。因此，将质量解释为来自手性通道之间重复的自指散射是自然的，动态地延迟了激发的净传播。

### 定理 4 的证明（Zitterbewegung 和信息速度）

对于连续狄拉克哈密顿量

$$
H = c p \sigma_{z} + m c^{2} \sigma_{x},
$$

其中 $X$ 是位置算符，$p = - \mathrm{i} \hbar \partial_{x}$，速度算符是

$$
\hat{v} = \frac{\mathrm{i}}{\hbar} [H, X] = c \sigma_{z}.
$$

由于 $\sigma_{z}^{2} = \mathbb{I}$，我们立即有

$$
\hat{v}^{2} = c^{2} \mathbb{I},
$$

对于任何归一化状态 $\Psi$，

$$
\langle \hat{v}^{2} \rangle = c^{2}.
$$

定义

$$
v_{\mathrm{ext}} = \langle \Psi, \hat{v} \Psi \rangle,
\quad
v_{\mathrm{int}} = \sqrt{ \langle \hat{v}^{2} \rangle - \langle \hat{v} \rangle^{2} }.
$$

那么

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2}
= \langle \hat{v} \rangle^{2} + \left( \langle \hat{v}^{2} \rangle - \langle \hat{v} \rangle^{2} \right)
= \langle \hat{v}^{2} \rangle
= c^{2},
$$

建立了所声称的恒等式。这是速度算符二分谱的代数结果。

为了与 Zitterbewegung 联系起来，我们考虑海森堡运动方程

$$
\frac{\mathrm{d} X(t)}{\mathrm{d} t} = \frac{\mathrm{i}}{\hbar} [H, X(t)] = c \sigma_{z}(t),
$$

和

$$
\frac{\mathrm{d} \sigma_{z}(t)}{\mathrm{d} t}
= \frac{\mathrm{i}}{\hbar} [H, \sigma_{z}(t)]
= \frac{2 m c^{2}}{\hbar} \sigma_{y}(t).
$$

求解这些耦合方程得到

$$
X(t) = X(0) + v_{\mathrm{ext}} t + \Xi(t),
$$

其中 $v_{\mathrm{ext}}$ 是与给定波包中的期望值相关的群速度，而

$$
\Xi(t) = \frac{\hbar c}{2 \mathrm{i} H} \left( \mathrm{e}^{2 \mathrm{i} H t / \hbar} - 1 \right) \left( \hat{v}(0) - v_{\mathrm{ext}} \right)
$$

是在每个能量扇区中频率为 $2 E / \hbar$ 的振荡项。对于正负能量本征态的叠加状态，$\Xi(t)$ 非零，并产生位置期望值的快速颤动运动，其振幅按 $\hbar c / (2 E)$ 缩放。

在离散 QCA 设置中，Bisio 等人明确计算了狄拉克自动机的 Zitterbewegung，并表明振荡频率和振幅在小质量、小动量极限下收敛到狄拉克值。因此，将速度分解为确定性部分 $v_{\mathrm{ext}}$ 和方差为 $v_{\mathrm{int}}^{2}$ 的涨落部分提供了信息论解释：$v_{\mathrm{ext}}$ 测量跨格点的净"外部"信息流，而 $v_{\mathrm{int}}$ 量化锁定在手性自由度中的剩余"内部"运动。

---

## 模型应用

在本节中，我们讨论"质量作为拓扑阻抗"图像产生具体预测或重新解释的几个设置。

### 畴壁和拓扑保护的束缚态

考虑一个空间不均匀的 QCA，其中硬币角度 $\theta$ 依赖于位置 $n$，在 $n \to -\infty$ 和 $n \to +\infty$ 时在两个渐近值 $\theta_{-}$ 和 $\theta_{+}$ 之间插值。相应的渐近绕数 $\mathcal{W}_{\pm}$ 由定理 2 给出。在 $\mathcal{W}_{+} \neq \mathcal{W}_{-}$ 的界面处，Floquet 体-边界对应关系预测在准能量 $0$ 或 $\pi / \Delta t$ 处存在拓扑保护的束缚态，局域在畴壁附近。

在狄拉克连续极限中，这样的界面可以通过位置相关的质量项 $m(x)$ 建模，其中 $m(-\infty) < 0$ 和 $m(+\infty) > 0$。众所周知，这支持狄拉克方程的局域零模解，这是 Jackiw–Rebbi 束缚态的原型。在当前解释中，束缚态是局部拓扑阻抗改变符号的配置，产生稳定的"被困"激发，该激发不能在没有拓扑相变的情况下离域化。

因此，QCA 观点将量子行走中的拓扑边缘态直接连接到有效质量参数的空间变化，并将这些状态解释为由绕数变化固定的自指散射缺陷。

### 拓扑相边界处的无质量通道

在体间隙闭合的参数值处，例如 $\theta = 0$ 或 $\theta = \pi$，绕数改变，系统可以承载以最大速度 $c$ 传播的无间隙通道。在连续狄拉克图像中，这对应于 $m = 0$，其中左右移动分量解耦，Zitterbewegung 消失。

从信息速度守恒的角度来看，这样的通道是纯"外部"信息流模式，具有 $v_{\mathrm{ext}} = \pm c$ 和 $v_{\mathrm{int}} = 0$。在不均匀 QCA 中，$\theta$ 跨越这些临界值的界面因此可以充当嵌入在有质量背景中的"无质量波导"，为量子行走实验中相对论畴壁费米子的类似物提供自然设置。

### 具有拓扑阻抗的有效场论

给定具有质量 $m$ 的狄拉克连续极限，可以写出一个有效的低能场论，其中质量项不仅仅是局部参数，而是与底层 QCA 的拓扑不变量相关联。特别是：

1. $m$ 的符号和大小决定绕数，从而决定不均匀性处受保护边缘态的存在或不存在。

2. 空间变化的 $m(x)$ 可以编码拓扑界面和缺陷的网络，其低能激发对应于由拓扑阻抗变化引导的局域模式。

3. 时间相关的硬币参数可以实现跨越拓扑相边界的淬火动力学，允许通过时间分辨的量子行走实验测量动力学拓扑序参数。

这种观点将基于 QCA 的狄拉克场离散化与 Floquet 拓扑能带理论相结合，并提供了质量、拓扑和信息速度处于同等地位的统一语言。

---

## 工程提案

质量作为拓扑阻抗的图像建议在实现 DTQW 或 QCA 的平台上进行一些具体的实验测试。

### 具有可调硬币角度的光子量子行走

集成光子设置已成功实现具有可调硬币算子的离散时间量子行走，观察拓扑束缚态并测量绕数。在这样的系统中：

1. 硬币角度 $\theta$ 可以通过 $m c^{2} = \hbar \theta / \Delta t$ 直接映射到有效质量参数。

2. 通过准备具有窄动量展宽的波包并改变 $\theta$，可以测量群速度 $v_{\mathrm{ext}}$ 对推断质量的依赖性，检查类狄拉克关系

   $$
   v_{\mathrm{ext}}(p,\theta) \approx \frac{c^{2} p}{\sqrt{p^{2} c^{2} + m^{2} c^{4}}}.
   $$

3. 通过将硬币自由度编码在偏振中，并解析空间和偏振动力学，可以重建有效速度算子统计，并直接测试不同初始状态的信息速度分解 $v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}$。

### 冷原子量子行走和 Zitterbewegung

在光学晶格中用冷原子实现的量子行走提供了长相干时间和对硬币参数的灵活控制。先前的工作已经提出并实现了具有冷原子的拓扑量子行走。在这样的实验中：

1. 可以准备正负准能量能带的相干叠加波包，并测量时间相关的期望值 $\langle X(t) \rangle$。

2. 观察到的振荡分量可以拟合以提取 Zitterbewegung 频率 $\omega_{\mathrm{ZB}}$ 和振幅作为 $\theta$ 和初始动量的函数。

3. 将这些与狄拉克预测 $\omega_{\mathrm{ZB}} = 2 E / \hbar$ 和 $\mathrm{amp} \sim \hbar c / (2 E)$ 进行比较，提供了自指散射图像的直接测试。

### 基于 QCA 的数字量子模拟

在数字量子处理器上，可以通过在砖墙电路中组合局部双量子比特幺正算子的层来实现有限大小的 QCA。这里考虑的狄拉克-QCA 对应于由硬币层和条件位移组成的深度二电路，可以分解为最近邻门。

在这个框架内：

1. 改变硬币旋转角度实现不同的有效质量。

2. 使用层析成像或随机测量协议，可以在小系统中重建 Floquet 幺正算子并数值计算其绕数。

3. 研究对局部缺陷或不均匀硬币角度的响应可以揭示拓扑保护模式，并测试拓扑阻抗对噪声和退相干的鲁棒性。

---

## 讨论（风险、边界、过去的工作）

### 与标准希格斯质量产生的关系

这里分析的机制纯粹是运动学和拓扑的。它将质量归因于 QCA 更新规则中手性混合项的存在，其系数由拓扑不变量约束。它不涉及自发对称性破缺或标量序参数，特别是没有解决希格斯真空期望值的起源或标准模型汤川耦合的数值。

然而，这并不意味着与希格斯机制不兼容。可以将基于 QCA 的质量视为有效狄拉克方程中运动学质量项的微观起源，而希格斯机制提供了这种质量项如何从标量扇区动态出现的低能场论描述。在结合规范对称性和非阿贝尔内部自由度的更高维狄拉克-QCA 中探索这种关系是未来工作的重要方向。

### 维度和手性

当前分析严格是一维的。在更高维度中，手性结构和拓扑不变量变得更加丰富：例如，在 $(2+1)$ 维中会遇到 Chern 数，在 $(3+1)$ 维中会遇到动量空间中的 Weyl 节点和相关的单极子电荷。狄拉克型 QCA 已在更高维度中构造，它们的色散关系和连续极限已被分析，但就 QCA 指标和 Floquet 不变量而言的系统拓扑分类仍在开发中。

将质量作为拓扑阻抗的图像扩展到 $(3+1)$ 维狄拉克 QCA，其中手性、宇称和异常抵消起核心作用，是非平凡的，可能需要更复杂的内在硬币空间和更新规则。

### QCA 的指标理论和稳定性

一维 QCA 承认严格的指标理论，表征每个时间步的净信息流，用整数表示，该整数在保持局域性和平移不变性的同伦下保持不变。该指标与信息的净"流"密切相关，并约束可能的体动力学。这里分析的绕数是动量空间幺正算子的 Floquet 型不变量，在手性对称性存在下定义。

理解这两个不变量之间的精确关系很重要：它们都在局部扰动下稳定，但捕获 QCA 的不同方面。在当前模型中，全局指标消失（无净漂移），而绕数对于 $\theta \neq 0$ 是非零的。这表明质量对应于具有零净传输的信息的非平凡内部"循环"的图像，与拓扑阻抗解释一致。

### 噪声、退相干和非幺正效应

真实实验不可避免地涉及损失、退相干和控制不完美。最近的工作已将拓扑分类扩展到非幺正量子行走，并研究了拓扑相在这种扰动下的鲁棒性。基本信息是，只要某些谱和对称性条件近似保持，拓扑特征就可以持续存在。

在当前上下文中，噪声可能降低精确的信息速度恒等式 $v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}$，这依赖于幺正性和二分速度谱。尽管如此，这种关系的近似版本可能仍然在相关时间尺度上成立，偏差本身可以作为退相干的探针。

---

## 结论

我们分析了一个简单而丰富的一维狄拉克型量子元胞自动机，并表明其有效质量参数允许自然解释为来自手性通道之间自指散射的拓扑阻抗。这种图像的关键要素是：

1. QCA 演化算子，定义为硬币旋转和条件位移的组合，在连续极限中重现 $(1+1)$ 维狄拉克方程，质量与硬币角度成正比。

2. 动量空间 Floquet 幺正算子具有手性对称性，并为任何非零硬币角度携带非平凡绕数，将自动机置于拓扑 Floquet 相中。无质量点与准能量间隙闭合的拓扑相变重合。

3. 设置质量间隙的相同硬币参数也决定了左右移动模式之间的局部反射振幅。由此产生的重复自指散射抑制了群速度，并为惯性提供了微观机制。

4. 在狄拉克极限中，速度算符具有特征值 $\pm c$，这意味着任何激发都满足 $v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}$，其中 $v_{\mathrm{ext}}$ 是平均群速度，$v_{\mathrm{int}}$ 量化与 Zitterbewegung 相关的内部涨落。因此，有质量激发将固定信息速度预算的一部分转移到内部运动中。

5. 有效质量改变符号的界面支持拓扑保护的束缚态，自然解释为拓扑阻抗模式中的缺陷。基于光子和冷原子量子行走的实验平台可以测试这些预测，并直接探测质量、拓扑和信息流之间的相互作用。

综合起来，这些结果表明，在 QCA 本体论内，质量不必是插入连续场论的任意参数。相反，它可以作为离散信息动力学的拓扑保护性质出现，约束激发如何在外部传播和内部自指运动之间分配其有限的信息速度预算。

---

## 致谢、代码可用性

作者感谢支撑这项研究的量子行走、量子元胞自动机和拓扑相的现有工作体系，特别是 Strauch、Childs、Kitagawa、Asbóth、Bisio、D'Ariano、Tosini、Farrelly 和其他许多人的贡献。

这里提出的推导不需要超出标准解析计算的数值模拟。足以重现本文讨论的色散关系、Zitterbewegung 和畴壁束缚态的简单量子行走模拟器可以在标准科学计算环境中直接实现；不提供专用代码库。

---

## 附录 A：狄拉克连续极限的详细推导

在本附录中，我们提供狄拉克连续极限的更系统推导，强调近似成立的条件。

### A.1 缩放和平滑性假设

我们采用缩放

$$
a = c \, \Delta t,
\quad
\theta = \frac{m c^{2}}{\hbar} \Delta t,
$$

并假设 $t = 0$ 时的格点波函数 $\Psi(n,t)$ 通过在位置 $x = n a$ 处采样平滑连续旋量 $\Psi(x,0)$ 获得。明确地，

$$
\Psi(n,0) = \Psi(x = n a,0),
$$

其中 $\Psi$ 二次连续可微，并在无穷远处足够快地衰减。

目标是构造满足狄拉克方程的连续旋量 $\Psi(x,t)$，使得

$$
\Psi(n,t) = \Psi(x = n a,t) + \mathcal{O}(\Delta t^{2})
$$

对于有界区间中的 $t$ 成立。误差估计可以在 Sobolev 范数中精确化，遵循在量子行走的严格连续极限分析中使用的方法。

### A.2 离散更新的展开

我们将离散更新方程写成

$$
\Psi(n,t + \Delta t) = \mathcal{U} \Psi(\cdot,t)(n),
$$

其中 $\mathcal{U}$ 根据

$$
\mathcal{U} \Psi(n)
= \begin{pmatrix}
\cos \theta \, \psi_{L}(n + 1) - \mathrm{i} \sin \theta \, \psi_{R}(n + 1) \\
- \mathrm{i} \sin \theta \, \psi_{L}(n - 1) + \cos \theta \, \psi_{R}(n - 1)
\end{pmatrix},
$$

作用于格点旋量。

我们现在将 $\Psi(n,t)$ 解释为连续场 $\Psi(x,t)$ 的采样，并在 $x = n a$ 附近泰勒展开。使用

$$
\Psi(x \pm a,t) = \Psi(x,t) \pm a \partial_{x} \Psi(x,t) + \frac{a^{2}}{2} \partial_{x}^{2} \Psi(x,t) + \mathcal{O}(a^{3}),
$$

和

$$
\cos \theta = 1 - \frac{\theta^{2}}{2} + \mathcal{O}(\theta^{4})
= 1 - \mathcal{O}(\Delta t^{2}),
$$

$$
\sin \theta = \theta + \mathcal{O}(\theta^{3})
= \frac{m c^{2}}{\hbar} \Delta t + \mathcal{O}(\Delta t^{3}),
$$

我们得到

$$
\begin{aligned}
\psi_{L}(x, t + \Delta t)
&= \psi_{L}(x,t) + a \partial_{x} \psi_{L}(x,t)
- \mathrm{i} \frac{m c^{2}}{\hbar} \Delta t \, \psi_{R}(x,t)
+ \mathcal{O}(\Delta t^{2}), \\
\psi_{R}(x, t + \Delta t)
&= \psi_{R}(x,t) - a \partial_{x} \psi_{R}(x,t)
- \mathrm{i} \frac{m c^{2}}{\hbar} \Delta t \, \psi_{L}(x,t)
+ \mathcal{O}(\Delta t^{2}).
\end{aligned}
$$

这里我们使用了 $a = c \Delta t$ 并忽略了 $\Delta t^{2}$ 或更高阶的项。

将其重写为连续方程的一阶时间离散化，

$$
\Psi(x,t + \Delta t) = \Psi(x,t) + \Delta t \, \partial_{t} \Psi(x,t) + \mathcal{O}(\Delta t^{2}),
$$

我们识别

$$
\partial_{t} \Psi
= - c \sigma_{z} \partial_{x} \Psi - \mathrm{i} \frac{m c^{2}}{\hbar} \sigma_{x} \Psi
+ \mathcal{O}(\Delta t),
$$

因此

$$
\mathrm{i} \hbar \, \partial_{t} \Psi
= \left( - \mathrm{i} \hbar c \sigma_{z} \partial_{x} + m c^{2} \sigma_{x} \right) \Psi
+ \mathcal{O}(\Delta t).
$$

单步格式的标准稳定性和一致性论证然后表明，离散演化在有限时间内以误差 $\mathcal{O}(\Delta t)$ 收敛到狄拉克演化。

---

## 附录 B：狄拉克和 QCA 动力学中的 Zitterbewegung

这里我们给出狄拉克哈密顿量的 Zitterbewegung 的标准推导，并概述它如何在 QCA 中出现。

### B.1 狄拉克理论中的 Zitterbewegung

考虑 $(1+1)$ 维中的自由狄拉克哈密顿量，

$$
H = c p \sigma_{z} + m c^{2} \sigma_{x},
$$

作用于旋量 $\Psi(x)$。在海森堡图像中，

$$
\frac{\mathrm{d} X(t)}{\mathrm{d} t} = \frac{\mathrm{i}}{\hbar} [H, X(t)],
\quad
\frac{\mathrm{d} \sigma_{z}(t)}{\mathrm{d} t} = \frac{\mathrm{i}}{\hbar} [H, \sigma_{z}(t)].
$$

使用 $[p, X] = - \mathrm{i} \hbar$，我们发现

$$
\frac{\mathrm{d} X(t)}{\mathrm{d} t} = c \sigma_{z}(t)
= \hat{v}(t),
$$

和

$$
\frac{\mathrm{d} \sigma_{z}(t)}{\mathrm{d} t}
= \frac{2 m c^{2}}{\hbar} \sigma_{y}(t),
\quad
\frac{\mathrm{d} \sigma_{y}(t)}{\mathrm{d} t}
= - \frac{2}{\hbar} \left( c p \sigma_{x}(t) + m c^{2} \sigma_{z}(t) \right).
$$

求解这些耦合方程得到

$$
\hat{v}(t) = c^{2} p H^{-1} + \mathrm{e}^{2 \mathrm{i} H t / \hbar} \left( \hat{v}(0) - c^{2} p H^{-1} \right),
$$

并对时间积分，

$$
X(t) = X(0) + c^{2} p H^{-1} t + \frac{\mathrm{i} \hbar c}{2 H} \left( \mathrm{e}^{2 \mathrm{i} H t / \hbar} - 1 \right) \left( \hat{v}(0) - c^{2} p H^{-1} \right).
$$

第一项表示以群速度 $v_{\mathrm{ext}} = c^{2} p / E$ 的均匀运动，而第二项是频率为 $\omega_{\mathrm{ZB}} = 2 E / \hbar$、振幅为 $\hbar c / (2 E)$ 量级的振荡项。对于完全由正能量本征态组成的波包，$\hat{v}(0)$ 与 $c^{2} p H^{-1}$ 重合，振荡项消失；Zitterbewegung 仅在正负能量分量都存在时出现。

### B.2 狄拉克-QCA 中的 Zitterbewegung

对于 QCA，海森堡方程必须相对于有效哈密顿量 $H_{\mathrm{eff}}(k)$ 制定，或者更直接地，通过离散时间海森堡演化

$$
X_{m+1} = U^{\dagger} X_{m} U,
$$

其中 $m$ 标记时间步。在动量空间中工作，人们发现对于在小动量和质量附近峰值的波包，$\langle X_{m} \rangle$ 的离散演化以良好的精度重现狄拉克行为，包括频率接近 $2 E / \hbar$ 的振荡贡献。对狄拉克自动机的详细计算和数值模拟已在先前的工作中进行，确认 Zitterbewegung 是 QCA 动力学的内在特征。

这支持了 Zitterbewegung（在连续和 QCA 中）是固定信息速度预算的内部分量 $v_{\mathrm{int}}$ 的表现的解释，而群速度 $v_{\mathrm{ext}}$ 解释了净传输。

---

## 附录 C：绕数的计算

我们简要详述这里考虑的单硬币量子行走的绕数计算。

### C.1 手性分解

对于手性对称性 $\Gamma = \sigma_{x}$ 和 Floquet 幺正算子 $\widetilde{U}(k)$，我们可以切换到 $\Gamma$ 对角的基：

$$
\Gamma = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix},
$$

而 $\widetilde{U}(k)$ 可以写成块形式

$$
\widetilde{U}(k) = \begin{pmatrix}
A(k) & B(k) \\
C(k) & D(k)
\end{pmatrix}.
$$

手性对称性意味着

$$
\Gamma \widetilde{U}(k) \Gamma = \widetilde{U}^{\dagger}(k),
$$

这导致约束 $A = D^{\dagger}$，$B = -B^{\dagger}$，$C = -C^{\dagger}$。特别是，非对角块 $B(k)$ 编码非平凡拓扑；其作为 $k$ 的函数的相位在复平面上绕原点缠绕。

对于我们的双分量模型，可以直接使用布洛赫向量 $\hat{\boldsymbol{n}}(k)$ 及其在垂直于 $\Gamma$ 的平面上的投影，如正文中所述。

### C.2 显式相位缠绕

关键对象是

$$
z(k) = \sin \theta \cos k + \mathrm{i} \cos \theta \sin k
= \sqrt{ \sin^{2} \theta \cos^{2} k + \cos^{2} \theta \sin^{2} k } \,
\mathrm{e}^{\mathrm{i} \varphi(k)},
$$

其辐角

$$
\varphi(k) = \arg \left( \sin \theta \cos k + \mathrm{i} \cos \theta \sin k \right)
$$

是 $k$ 的连续函数，对于 $0 < \theta < \pi$，有

$$
\varphi(-\pi) = - \arctan\left( \cot \theta \right),
\quad
\varphi(\pi) = \varphi(-\pi) + 2 \pi.
$$

因此，当 $k$ 从 $-\pi$ 运行到 $\pi$ 时，相位 $\varphi(k)$ 增加 $2 \pi$，绕数

$$
\mathcal{W} = \frac{1}{2 \pi} \int_{-\pi}^{\pi} \frac{\partial \varphi(k)}{\partial k} \, \mathrm{d} k
$$

等于 $1$。

在 $\theta = 0$ 或 $\theta = \pi$ 处，量 $z(k)$ 坍缩到实轴，间隙在准能量 $0$ 或 $\pi / \Delta t$ 处闭合，绕数变得不确定；在这些情况下，系统是拓扑平凡的，$\mathcal{W} = 0$。

这个计算与一维手性对称量子行走的一般分类以及相关模型中绕数的显式评估一致。

---

## 参考文献

[1] R. P. Feynman, "Simulating physics with computers," International Journal of Theoretical Physics 21, 467–488 (1982).

[2] A. Bisio, G. M. D'Ariano, and A. Tosini, "Quantum field as a quantum cellular automaton," Annals of Physics 354, 244–264 (2015).

[3] A. Bisio, G. M. D'Ariano, and A. Tosini, "Dirac quantum cellular automaton in one dimension," Physical Review A 88, 032301 (2013).

[4] F. W. Strauch, "Relativistic quantum walks," Physical Review A 73, 054302 (2006).

[5] F. W. Strauch, "Connecting the discrete- and continuous-time quantum walks," Physical Review A 74, 030301 (2006).

[6] A. M. Childs, "On the relationship between continuous- and discrete-time quantum walk," Communications in Mathematical Physics 294, 581–603 (2010).

[7] M. Manighalam, "General methods and properties for evaluation of continuum limits of quantum walks," Quantum Information Processing 19, 288 (2020).

[8] J. K. Asbóth, L. Oroszlány, and A. Pályi, A Short Course on Topological Insulators: Band-Structure Topology and Edge States in One and Two Dimensions (Springer, 2016).

[9] T. Kitagawa, M. S. Rudner, E. Berg, and E. Demler, "Exploring topological phases with quantum walks," Physical Review A 82, 033429 (2010).

[10] T. Kitagawa, "Topological phenomena in quantum walks: Elementary introduction to the physics of topological phases," Quantum Information Processing 11, 1107–1148 (2012).

[11] J. K. Asbóth and H. Obuse, "Bulk–boundary correspondence for chiral symmetric quantum walks," Physical Review B 88, 121406 (2013).

[12] H. T. Lam, L. C. Kwek, and J. K. Asbóth, "Quantum walks and hidden topological phases," (2015), arXiv:1508.07528.

[13] T. Farrelly, "A review of quantum cellular automata," Quantum 4, 368 (2020).

[14] A. Bisio, G. M. D'Ariano, and A. Tosini, "The Dirac quantum cellular automaton in one dimension: Zitterbewegung and scattering from potential," preprint (2013).

[15] T. Kitagawa et al., "Observation of topologically protected bound states in photonic quantum walks," Nature Communications 3, 882 (2012).

[16] S. Mugel et al., "Topological bound states of a quantum walk with cold atoms," Physical Review A 94, 023631 (2016).

[17] Y. Meng et al., "Topological quantum walks in cavity-based quantum networks," European Physical Journal Plus 135, 355 (2020).

[18] C. Sun et al., "Measuring a dynamical topological order parameter in quantum walks," Light: Science & Applications 9, 249 (2020).

[19] Y. Jia, C. Lv, and Z. Wang, "High winding number of topological phase in periodic quantum walks," Physics Letters A 404, 127408 (2021).

[20] V. Mittal et al., "Persistence of topological phases in non-Hermitian quantum walk," Scientific Reports 11, 9095 (2021).

[21] Q. Wang, X. Luo, and J. Gong, "Topological invariants of nonunitary quantum walks with gain and loss," Physica E 141, 115222 (2022).

[22] J. M. Guilar, B. Tarasinski, and C. W. J. Beenakker, "Chiral symmetry and bulk-boundary correspondence in periodically driven one-dimensional systems," Physical Review B 90, 125143 (2014).

[23] H. Ma, "Universal conservation of information celerity," preprint (2025).

[24] Additional standard references on Dirac theory, Zitterbewegung and lattice fermions.




