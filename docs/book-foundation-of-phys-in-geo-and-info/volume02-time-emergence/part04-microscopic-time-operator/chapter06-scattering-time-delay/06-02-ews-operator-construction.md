**6.2 Eisenbud-Wigner-Smith (EWS) 算符 $\mathsf{Q}$ 的完整构造**

在 6.1 节中，通过泡利定理的否定性证明，我们不得不放弃寻找一个与哈密顿量全局共轭的通用时间算符。这迫使我们将视线从静态的希尔伯特空间结构转向动态的物理过程。对于一个开放的物理系统，最基本的动力学过程莫过于**散射**（Scattering）。

本节将严格定义散射时间延迟算符，即 Eisenbud-Wigner-Smith (EWS) 算符 $\mathsf{Q}$。我们将证明，尽管不存在全局时间坐标，但对于任何散射过程，都可以内禀地构造一个自伴算符，其本征值精确对应于粒子在相互作用区域内的**滞留时间**（Dwell Time）相对于自由运动的**延迟**。这是本书"时间涌现"纲领的第一个数学支柱。

### 6.2.1 散射矩阵 $S(E)$ 的解析性质

考虑一个多通道量子散射系统。设希尔伯特空间可分解为 $\mathcal{H} = \mathcal{H}_{int} \oplus \mathcal{H}_{ext}$，其中相互作用区域 $\mathcal{H}_{int}$ 有限，外部区域 $\mathcal{H}_{ext}$ 由若干散射通道（Channels）组成。

在能量表象下，系统的渐近态由入射态 $|\psi_{in}\rangle$ 和出射态 $|\psi_{out}\rangle$ 描述。两者通过**散射算符**（Scattering Operator）$\hat{S}$ 联系：

$$
|\psi_{out}\rangle = \hat{S} |\psi_{in}\rangle
$$

在能量壳层 $E$ 上，$\hat{S}$ 表现为一个 $N \times N$ 的幺正矩阵 $S(E)$（$N$ 为通道数），满足：

$$
S(E)^\dagger S(E) = S(E) S(E)^\dagger = \mathbb{I}
$$

这意味着散射过程是概率守恒的。然而，幺正性仅保证了粒子数的守恒，并未包含时间信息。时间信息隐藏在 $S$ 矩阵随能量 $E$ 变化的**相位梯度**中。

### 6.2.2 EWS 算符的定义与自伴性证明

为了提取隐藏的时间信息，Eisenbud (1948), Wigner (1955) 和 Smith (1960) 引入了一个厄米算符 $\mathsf{Q}$。

**定义 6.2.1 (EWS 时间延迟算符)**

对于能量为 $E$ 的散射系统，Eisenbud-Wigner-Smith 算符 $\mathsf{Q}(E)$ 定义为：

$$
\mathsf{Q}(E) \equiv -i\hbar S(E)^\dagger \frac{d S(E)}{dE}
$$

该算符作用于通道空间 $\mathbb{C}^N$。

**定理 6.2.2 (EWS 算符的自伴性)**

若 $S(E)$ 是幺正的，则 $\mathsf{Q}(E)$ 必然是自伴（厄米）算符，即 $\mathsf{Q}^\dagger = \mathsf{Q}$。

**证明**：

从 $S(E)$ 的幺正性出发：

$$
S(E)^\dagger S(E) = \mathbb{I}
$$

对能量 $E$ 求导：

$$
\frac{dS^\dagger}{dE} S + S^\dagger \frac{dS}{dE} = 0
$$

这给出了导数算符的恒等式：

$$
S^\dagger \frac{dS}{dE} = - \frac{dS^\dagger}{dE} S
$$

现在考察 $\mathsf{Q}$ 的伴随算符 $\mathsf{Q}^\dagger$：

$$
\begin{aligned}

\mathsf{Q}^\dagger &= \left( -i\hbar S^\dagger \frac{dS}{dE} \right)^\dagger \\

&= i\hbar \left( \frac{dS}{dE} \right)^\dagger (S^\dagger)^\dagger \\

&= i\hbar \frac{dS^\dagger}{dE} S

\end{aligned}
$$

利用上述导数恒等式代换：

$$
\mathsf{Q}^\dagger = i\hbar \left( - S^\dagger \frac{dS}{dE} \right) = -i\hbar S^\dagger \frac{dS}{dE} = \mathsf{Q}
$$

$\square$

这一性质至关重要：因为 $\mathsf{Q}$ 是自伴的，它拥有实数谱，这使得我们可以将其本征值解释为物理可观测的时间量。

### 6.2.3 物理诠释：波包延迟与本征时间

为了理解 $\mathsf{Q}$ 的物理意义，我们考察一个窄波包在散射过程中的群延迟。

设入射波包为 $|\psi_{in}(t)\rangle = \int dE \, g(E) e^{-iEt/\hbar} |\chi\rangle$，其中 $|\chi\rangle$ 是通道空间中的固定矢量。出射波包为 $|\psi_{out}(t)\rangle = \hat{S} |\psi_{in}(t)\rangle$。

利用稳相法（Stationary Phase Approximation），波包中心的到达时间由相位的能量导数决定。对于散射态 $S(E) = e^{2i\delta(E)}$（一维情形），群延迟为：

$$
\Delta t = 2\hbar \frac{d\delta}{dE}
$$

在一维情形下，$\mathsf{Q} = -i\hbar e^{-2i\delta} (2i\delta' e^{2i\delta}) = 2\hbar \delta'$。这正是群延迟。

**推广到多通道情形**：

算符 $\mathsf{Q}(E)$ 的期望值 $\langle \chi | \mathsf{Q} | \chi \rangle$ 给出了入射态为 $|\chi\rangle$ 时的平均时间延迟。

由于 $\mathsf{Q}$ 是厄米矩阵，它可以对角化。设其本征方程为：

$$
\mathsf{Q}(E) |q_n\rangle = \tau_n(E) |q_n\rangle, \quad n=1,\dots,N
$$

**本征值 $\tau_n(E)$** 称为**本征时间延迟**（Eigen-time Delays）。它们对应于散射矩阵的本征通道（Eigenchannels）在相互作用区经历的时间滞留。这表明，对于一个复杂的量子系统，时间不是单一的，而是一个**谱（Spectrum）**。

### 6.2.4 与全息原理的连接：迹公式

EWS 算符不仅定义了微观时间，还通过迹公式与态密度（Density of States, DOS）建立了深刻联系。这直接通向本书后续关于"统一时间恒等式"的讨论。

**定义 6.2.3 (Wigner 时间延迟求和规则)**

系统的总时间延迟是 $\mathsf{Q}$ 矩阵的迹：

$$
\tau_{tot}(E) = \text{Tr}[\mathsf{Q}(E)] = \sum_{n=1}^N \tau_n(E)
$$

利用 $\text{Tr}(\ln A) = \ln(\det A)$ 的导数形式 $\text{Tr}(A^{-1} A') = (\ln \det A)'$，我们有：

$$
\text{Tr}[\mathsf{Q}] = -i\hbar \text{Tr}[S^\dagger S'] = -i\hbar \frac{d}{dE} \ln \det S(E)
$$

根据 Birman-Kreĭn 理论（将在第七章详述），$\det S(E) = e^{-2\pi i \xi(E)}$，其中 $\xi(E)$ 是谱移函数。因此：

$$
\text{Tr}[\mathsf{Q}(E)] = -i\hbar \frac{d}{dE} (-2\pi i \xi(E)) = 2\pi\hbar \frac{d\xi}{dE} = 2\pi\hbar \Delta \rho(E)
$$

其中 $\Delta \rho(E)$ 是相互作用引起的**局域态密度**的变化。

**物理推论**：

这一公式 $\text{Tr}[\mathsf{Q}] = 2\pi\hbar \Delta \rho$ 是本书**"时间即物质"**核心理念的数学表达。

* 左侧是**时间**量（延迟的迹）。

* 右侧是**物质**量（能级密度的增加）。

这表明，粒子在一个区域"花费时间"，等价于该区域"拥有态密度"来接纳该粒子。在引力理论中，这将解释为何强引力场（高态密度）会导致时间膨胀（大延迟）。

### 6.2.5 总结

本节通过严格构造 EWS 算符 $\mathsf{Q}$，解决了泡利定理带来的时间定义危机。

1.  **存在性**：虽然没有全局时间算符，但存在局域的、依赖于过程的散射时间算符 $\mathsf{Q}$。

2.  **可观测性**：$\mathsf{Q}$ 是自伴的，其本征值对应物理上可测量的延迟。

3.  **全息性**：$\mathsf{Q}$ 的迹直接对应于系统的态密度，建立了时空几何与量子统计的桥梁。

在下一节，我们将深入探讨 $\mathsf{Q}$ 算符的物理内涵，特别是**滞留时间（Dwell Time）** 与群延迟的物理等价性证明，进一步夯实微观时间的本体论地位。

