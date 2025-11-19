# 第五编：统一时间恒等式与相对论

## 第八章：相位-延迟-密度 三位一体

在第二卷的前半部分（第四编），我们分别从微观动力学的角度建立了散射时间延迟理论（第六章），并从统计热力学的角度建立了谱移函数理论（第七章）。这两个看似独立的物理图像——一个关注粒子在散射区的滞留时间，另一个关注相互作用引起的能级重排——在 Birman-Kreĭn 迹公式中初次相遇。

本章将这一相遇升华为物理学中的一个基本原理：**统一时间恒等式（Unified Time Identity）**。我们将证明，时间流逝的速率（相位导数）、物质的存在形式（态密度）以及信息的处理容量（群延迟）在数学上是完全等价的。这一"三位一体"的关系不仅统一了微观物理，更将成为我们在后续章节推导广义相对论引力效应的公理化起点。

### 8.1 统一时间恒等式推导：$\kappa(E) = \varphi'/\pi = \rho_{\text{rel}} = \text{Tr}\mathsf{Q}/2\pi$

物理学长期以来习惯将时间 $t$ 视为一个外在于物质的背景参数，而将质量或能量视为填充在时空中的实体。然而，QCA 的离散本体论暗示了这两者之间存在更深层的对偶性。本节将严格推导并确立**统一时间恒等式**，证明"时间"的计量与"物质"的密度在谱几何层面上是同一物理量的不同表象。

#### 8.1.1 三个物理量的回顾

首先，让我们清晰地定义参与统一的三个核心物理量，它们分别代表了物理实在的三个不同侧面：

1.  **几何侧：散射半相位导数 $\varphi'(E)$**

    在散射理论中，散射矩阵 $S(E)$ 的行列式是一个幺模复数。定义总散射相位 $\Phi(E)$ 为：

    $$
    \det S(E) = e^{i\Phi(E)}
    $$

    定义**半相位（Half-phase）** $\varphi(E) = \frac{1}{2}\Phi(E)$。其关于能量的导数 $\varphi'(E) = \frac{d\varphi}{dE}$ 描述了波函数在能量空间中的几何旋转速度。



2.  **热力学侧：相对态密度 $\rho_{\text{rel}}(E)$**

    态密度（DOS）是统计力学的核心。引入相互作用 $V$ 后，局域态密度的变化定义为：

    $$
    \rho_{\text{rel}}(E) \equiv \rho(E) - \rho_0(E) = \frac{d}{dE} \text{Tr} \left[ \Theta(E-H_0) - \Theta(E-H) \right]
    $$

    它量化了能量壳层 $E$ 附近新增的微观自由度数目（或信息容量）。



3.  **动力学侧：Wigner-Smith 时间延迟迹 $\text{Tr}\mathsf{Q}(E)$**

    EWS 算符 $\mathsf{Q} = -i\hbar S^\dagger \frac{dS}{dE}$ 描述了波包在散射区的滞留时间。其迹 $\tau_{tot} = \text{Tr}\mathsf{Q}$ 代表了所有散射通道的总时间延迟，即系统作为一个整体对外部探针的"时间阻抗"。

#### 8.1.2 恒等式的严格推导

我们将利用第七章建立的 Birman-Kreĭn 理论来完成这一证明。

**定理 8.1.1 (统一时间恒等式)**

对于满足相对迹类条件的散射系统，在绝对连续谱区域内，以下三个物理量严格相等（在自然单位制 $\hbar=1$ 下）：

$$
\kappa(E) \equiv \frac{1}{\pi} \frac{d\varphi(E)}{dE} = \rho_{\text{rel}}(E) = \frac{1}{2\pi} \text{Tr}\mathsf{Q}(E)
$$

我们将 $\kappa(E)$ 定义为**统一时间刻度密度（Unified Time Scale Density）**。

**证明**：

**步骤 1：连接 $\text{Tr}\mathsf{Q}$ 与 $\varphi'$**

根据 Wigner-Smith 算符的定义及其迹的性质（6.4 节）：

$$
\text{Tr}\mathsf{Q}(E) = \text{Tr}\left[ -i S^\dagger(E) \frac{dS(E)}{dE} \right]
$$

利用雅可比公式 $\text{Tr}(A^{-1} dA) = d(\ln \det A)$，且 $S^\dagger = S^{-1}$：

$$
\text{Tr}\mathsf{Q}(E) = -i \frac{d}{dE} \ln (\det S(E))
$$

代入总相位定义 $\det S = e^{i\Phi(E)} = e^{2i\varphi(E)}$：

$$
\text{Tr}\mathsf{Q}(E) = -i \frac{d}{dE} (2i\varphi(E)) = 2 \frac{d\varphi}{dE} = 2\varphi'(E)
$$

因此：

$$
\frac{1}{2\pi} \text{Tr}\mathsf{Q}(E) = \frac{1}{\pi} \varphi'(E)
$$



**步骤 2：连接 $\varphi'$ 与 $\rho_{\text{rel}}$**

利用 Birman-Kreĭn 迹公式（7.2 节）：

$$
\det S(E) = e^{-2\pi i \xi(E)}
$$

这意味着总相位 $\Phi(E)$ 与 Kreĭn 谱移函数 $\xi(E)$ 的关系为（取连续分支）：

$$
\Phi(E) = -2\pi \xi(E) \implies 2\varphi(E) = -2\pi \xi(E) \implies \varphi(E) = -\pi \xi(E)
$$

对能量求导：

$$
\varphi'(E) = -\pi \xi'(E)
$$

回顾谱移函数与态密度的关系（7.1 节）：

$$
\xi(E) = -(N(E) - N_0(E)) \implies \xi'(E) = -(\rho(E) - \rho_0(E)) = -\rho_{\text{rel}}(E)
$$

将此代入上式：

$$
\varphi'(E) = -\pi (-\rho_{\text{rel}}(E)) = \pi \rho_{\text{rel}}(E)
$$

即：

$$
\frac{1}{\pi} \varphi'(E) = \rho_{\text{rel}}(E)
$$



**步骤 3：综合**

联立步骤 1 和步骤 2 的结果，即得三位一体恒等式。

$\square$

#### 8.1.3 物理诠释：$\kappa(E)$ 的本体论地位

统一时间恒等式揭示了 $\kappa(E)$ 是一个比时间、能量或熵更基本的物理量。它构成了 QCA 宇宙的**母尺（Master Scale）**。

1.  **时间即统计** ($\text{Time} \sim \text{DOS}$)：

    公式 $\frac{1}{2\pi} \tau_{tot} = \rho_{\text{rel}}$ 告诉我们，**时间流逝的本质是系统对微观状态的遍历**。如果一个区域内没有量子态（$\rho=0$，如禁带），波包将瞬间穿过（隧穿），不经历时间延迟（或经历极短的群延迟）。反之，如果态密度极高（如黑洞内部），波包将被无数个态"绊住"，导致时间极度延缓。



2.  **几何即相位** ($\text{Geometry} \sim \text{Phase}$)：

    公式 $\kappa = \varphi'/\pi$ 表明，这一统计属性完全编码在边界的几何相位中。我们不需要深入系统内部去数状态，只需要在边界测量相位的"卷绕速率"。



3.  **普朗克信息密度**：

    $\kappa(E)$ 的量纲是 $[\text{Energy}]^{-1} = [\text{Time}]$（在 $\hbar=1$ 下）。它实际上度量了**单位能量间隔内的信息容量**。在普朗克尺度下，这对应于每普朗克能量包含的比特数。

#### 8.1.4 案例验证：一维势箱

为了使这一抽象恒等式具体化，我们考察一个长度为 $L$ 的一维势箱（无限深方势阱）。

* **热力学侧（态密度）**：

    本征能量 $E_n = \frac{n^2 \pi^2}{2m L^2}$。动量 $k_n = \frac{n\pi}{L}$。

    态密度 $\rho(k) = \frac{dn}{dk} = \frac{L}{\pi}$。

    能量态密度 $\rho(E) = \rho(k) \frac{dk}{dE} = \frac{L}{\pi} \frac{1}{v} = \frac{L}{\pi v}$，其中 $v$ 是群速度。



* **动力学侧（时间延迟）**：

    经典粒子穿过盒子往返一次的时间是 $T = \frac{2L}{v}$。

    在散射图像中，波函数在边界反射，经历相移。由于这是束缚系统，我们可以考虑一个大盒子 $L_{big}$ 中的小散射体 $L$。

    或者直接引用滞留时间概念：$\tau_D = \frac{1}{J} \int |\psi|^2 dx = \frac{1}{v/L_{norm}} \cdot 1 = \frac{L_{norm}}{v}$。

    对于散射态 $S(k) = e^{-2ikL}$（透射系数相位，对应自由传播），相移 $\delta(k) = -kL$。

    $\varphi' = \frac{d\delta}{dE} = \frac{d(-kL)}{dE} = -L \frac{dk}{dE} = -\frac{L}{v}$。

    这里出现了符号差异，因为自由传播通常作为背景被减去。若考虑由势 $V$ 引起的**额外**延迟（例如共振），$\Delta \rho$ 和 $\tau_{delay}$ 将同时为正。



    考虑一个共振散射（Breit-Wigner 共振）：

    $$S(E) = \frac{E - E_0 - i\Gamma/2}{E - E_0 + i\Gamma/2}$$

    相位导数（延迟）：$\tau(E) = \frac{\Gamma}{(E-E_0)^2 + \Gamma^2/4}$。

    态密度（洛伦兹谱）：$\Delta \rho(E) = \frac{1}{2\pi} \frac{\Gamma}{(E-E_0)^2 + \Gamma^2/4}$。

    显然满足 $\tau(E) = 2\pi \Delta \rho(E)$。

#### 8.1.5 结论

统一时间恒等式 $\kappa(E)$ 是连接第一卷（离散本体论）与第三卷（引力熵起源）的关键纽带。

* 向上，它解释了为何引力场（度规 $g_{\mu\nu}$）会影响时间——因为引力场改变了真空的态密度 $\rho(E)$。

* 向下，它解释了时间的微观起源——时间不是流逝的河水，而是量子态在希尔伯特空间中被计数的过程。

在下一节中，我们将基于 $\kappa(E)$ 探讨**"时间即物质"**的深层推论，并解释为何在广义相对论中，能量动量张量（物质）直接弯曲了时空几何（时间）。

