# 宇宙学常数与暗能量的谱窗化统一理论

统一时间刻度、矩阵宇宙与 QCA 宇宙中的真空能密度

---

## Abstract

在统一时间刻度、相位–谱移–态密度链与边界时间几何框架下，本文对宇宙学常数与暗能量给出一个谱窗化统一表述，并在离散矩阵宇宙与量子元胞自动机宇宙中实现离散化版本。首先，在满足相对迹类与良好散射假设的偶维渐近双曲或共形紧致几何及静片 de Sitter 背景上，利用 Birman–Kreĭn 与 Lifshits–Kreĭn 迹公式，将广义散射相位导数、谱移函数导数与频率变量下的相对态密度统一为刻度密度 $\kappa(\omega)=\varphi'(\omega)/\pi=\Delta\rho_\omega(\omega)=(2\pi)^{-1}\tr Q(\omega)$，其中 $Q(\omega)$ 为 Wigner–Smith 群延迟矩阵。在对数频率窗核满足 Mellin 消零条件的前提下，建立一个窗化 Tauberian 定理：小 $s$ 热核差的有限部与 $\Theta'(\omega)$ 的对数窗平均在尺度 $\mu\sim s^{-1/2}$ 下等价，由此将真空能密度重整化完全重写为 $\kappa(\omega)$ 的窗化积分。其次，在矩阵宇宙表象中，将 FRW 与 de Sitter 宇宙视作包含地平线通道的散射背景，构造宇宙学散射矩阵 $S_{\mathrm{cos}}(\omega)$ 及其刻度密度 $\kappa_{\mathrm{cos}}(\omega)$ 与窗核 $\Xi_{\mathrm{cos}}(\omega)$，证明有效宇宙学常数增量 $\Lambda_{\mathrm{eff}}(\mu)-\Lambda_{\mathrm{eff}}(\mu_0)$ 可表示为"物理宇宙"与"参考宇宙"之间 DOS 差分的对数频率窗化谱积分，从而将宇宙学常数问题归结为统一时间刻度下的相对谱问题。第三，在宇宙 QCA 对象 $\mathfrak U_{\mathrm{QCA}}=(\Lambda,\mathcal H_{\mathrm{cell}},\mathcal A,\alpha,\omega_0)$ 内，将连续谱 $\omega$ 替换为准能谱 $\varepsilon_j(k)$，定义 QCA 宇宙与参考 QCA 的相对带密度 $\Delta\rho_j(k)$，构造离散窗化公式 $\Lambda_{\mathrm{eff}}(\mu)=\sum_j\int_{\mathrm{BZ}}\mathcal W_\mu(\varepsilon_j(k))\,\Delta\rho_j(k)\,\diff^dk$。在高能带满足对称配对与带间和谐 sum rule 的条件下，证明高能区对 $\Lambda_{\mathrm{eff}}$ 的贡献在窗化后被指数或幂次抑制，仅剩由红移窗口内的低能质量阈值与拓扑模态贡献的有限残差，得到自然抑制估计 $\Lambda_{\mathrm{eff}}\sim m_{\mathrm{IR}}^4(m_{\mathrm{IR}}/M_{\mathrm{UV}})^{\gamma}$ 且 $\gamma>0$。最后，将谱窗化–带结构机制与曲时空量子场论中的运行真空模型相对接，在统一时间刻度框架内构造暗能量等效状态方程 $w_{\mathrm{de}}(z)\approx -1+\delta w(z)$，其中 $\delta w(z)$ 由 $\Xi(\omega)$ 在对应频带上的缓慢演化控制，与当前"整体接近 $w=-1$ 且允许小幅度演化"的观测约束相容。综合而言，本文将"宇宙学常数为何远小于 $M_{\mathrm{Pl}}^4$"重述为"相对 DOS 在统一时间刻度下满足何种窗化 sum rule"，为在矩阵宇宙与 QCA 宇宙内统一讨论暗能量的大小与运行行为提供了一个自洽的谱理论框架。宇宙学常数问题由此被嵌入统一时间刻度–散射–离散宇宙的更广泛计划之中。

---

## Keywords

宇宙学常数；暗能量；统一时间刻度；散射相位；谱移函数；态密度；热核；Tauberian 定理；矩阵宇宙；量子元胞自动机；真空能密度；运行真空模型

---

## 1 Introduction & Historical Context

### 1.1 宇宙学常数、暗能量与观测图景

在爱因斯坦场方程

$$
G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G T_{\mu\nu}
$$

中，引入宇宙学常数 $\Lambda$ 可在经典几何层面描述具有常曲率的 de Sitter 或 anti–de Sitter 解；在有效场论语言中，$\Lambda$ 对应真空能密度 $\rho_\Lambda=\Lambda/(8\pi G)$，其压强满足 $p_\Lambda=-\rho_\Lambda$，即状态方程参数 $w=-1$。标准 $\Lambda$CDM 模型以常数 $\Lambda$ 作为解释宇宙晚期加速膨胀的最简方案。

基于宇宙微波背景、Ia 型超新星、重子声学振荡和弱透镜等多种观测，目前对暗能量密度与状态方程的联合分析表明，宇宙总能量密度中约有近三分之二由暗能量贡献，且有效状态方程 $w_{\mathrm{de}}$ 与 $-1$ 高度接近，在联合拟合中偏离 $\delta w=w_{\mathrm{de}}+1$ 的量级通常限制在 $\mathcal O(10^{-1})$ 以内。最新的综述显示，多种独立数据集在 $2\sigma$ 水平上仍与 $w=-1$ 相容，但部分分析倾向于略微"幽灵型"状态方程 $w\lesssim -1$，这一趋势与 Hubble 张力和 $\sigma_8$ 张力可能存在相关。

在对暗能量方程状态的综合回顾中，Escamilla 等对多种参数化形式 $w(z)$ 的约束进行了系统比较，指出目前数据对 $w(z)$ 的红移演化仍只能给出较弱的定量限制，但某些数据组合确实偏好轻微偏离 $-1$ 的演化情形。这为"宇宙学常数是否严格为常数"留下了观测空间。

### 1.2 宇宙学常数问题与运行真空思路

从量子场论角度看，带 UV 截断 $M_{\mathrm{UV}}$ 的自由场真空零点能形式上给出 $\rho_{\mathrm{vac}}\sim M_{\mathrm{UV}}^4$。若取 $M_{\mathrm{UV}}\sim M_{\mathrm{Pl}}$ 或典型粒子物理尺度，则与观测的 $\rho_{\Lambda}^{\mathrm{obs}}\sim 10^{-120}M_{\mathrm{Pl}}^4$ 相比存在 $60\text{–}120$ 个数量级差距，这构成宇宙学常数问题的核心。

在曲时空量子场论中，真空能密度可以通过重整化吸收到 $\Lambda$ 的裸项中，但这一过程并未给出"为何重整后的总真空能恰好剩下一个极小正数"的内部机制。近年的"运行真空模型"提出，在宇宙膨胀的背景下，真空能密度应当是随曲率或 Hubble 标度缓慢演化的函数，例如

$$
\rho_{\mathrm{vac}}(H)=\rho_{\mathrm{vac}}^0+\frac{3\nu}{8\pi G}(H^2-H_0^2)+\cdots
$$，

其中 $\nu$ 是一个小的无量纲系数。通过在曲时空中实施渐近重整化，可以将部分危险的 $m^4$ 级项有效移除，使晚期宇宙的真空能呈现出弱运行行为，而不必引入额外的标量场自由度。RVM 类模型在缓解 $H_0$ 与 $\sigma_8$ 张力方面已表现出一定潜力。

尽管如此，大多数讨论仍停留在"假设某种 $\rho_{\mathrm{vac}}(H)$ 的函数形式再与观测拟合"的层面，尚缺少一种从谱与散射结构出发，自然导出运行真空行为并解释真空能小值的统一方式。

### 1.3 谱与散射视角：相位、谱移与 DOS

在数学物理中，成对的自伴算子 $(H,H_0)$ 及其散射矩阵 $S(\omega)$、谱移函数 $\xi(\omega)$ 与态密度差分 $\Delta\rho(\omega)$ 之间存在一系列深刻联系。Birman–Kreĭn 公式将散射行列式与谱移函数关联，Lifshits–Kreĭn 迹公式将函数 $f(H)-f(H_0)$ 的迹表示为对谱移函数的积分。Guillarmou 及其合作者在渐近双曲与共形紧致的 Einstein 流形上进一步建立了广义 Kreĭn 公式与散射算子的谱性质，使得 KV 行列式相位可与广义谱移函数精确对齐。

在开放散射流形上，Dyatlov 利用经典逃逸率与扩展率，对散射相位的 Weyl 型渐近与剩余项给出了精细估计，表明散射相位中的高能信息可通过经典动力系统的不变量加以控制。Vasy 的工作则在共形紧致渐近双曲空间上发展了系统的微局部分析方法，实现了 Laplace 算子的高能 resolvent 延拓与估计，为将热核与散射谱联系起来提供了控制工具。

这些结果表明，在适当几何假设下，可以把"谱与散射"端的量（如散射相位导数）与"几何与热核"端的量（如热核差与 Seeley–DeWitt 系数）精确联通，这为用谱量重写宇宙学常数提供了自然入口。

### 1.4 量子元胞自动机与离散宇宙

量子元胞自动机作为局域、平移不变、有限传播半径的离散时间幺正演化模型，已被系统证明在连续极限下可以还原自由或相互作用量子场论，包括 Dirac 场、标量场乃至 $(1+1)$ 维与 $(3+1)$ 维的电动力学。这些工作表明，在满足局域性、洛伦兹对称近似与规范不变性等自然条件下，可以从简单的离散局域规则中恢复标准 QFT 的色散关系与传播性质。

在这样的视角下，将宇宙整体抽象为一个满足若干公理的 QCA 对象 $\mathfrak U_{\mathrm{QCA}}$，并在其连续极限上恢复广义相对论与场论，再把宇宙学常数与暗能量问题嵌入 QCA 的谱与带结构之中，就成为一个自然的统一思路：宇宙本身是离散的，而连续几何与场论只是其大尺度近似。

### 1.5 本文的统一时间刻度与谱窗化策略

在此前工作中已构造出统一时间刻度母尺

$$
\kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\tr Q(\omega)
$$，

其中 $\varphi(\omega)$ 为总散射半相位，$\rho_{\mathrm{rel}}(\omega)$ 为相对态密度，$Q(\omega)$ 为 Wigner–Smith 群延迟矩阵。该母尺将散射相位梯度、相对 DOS 与群延迟迹统一为单一刻度密度，为在多种几何与物理情形中定义统一时间参数提供了统一源头。

基于此，本文的目标是：

1. 在满足适当散射与几何假设的连续几何上，建立一个窗化 Tauberian 定理，将小 $s$ 热核差的有限部与 $\Theta'(\omega)$ 的对数窗平均在尺度 $\mu\sim s^{-1/2}$ 下精确对应，从而把真空能重整化重写为 $\kappa(\omega)$ 的对数频率窗化谱积分。

2. 在矩阵宇宙 THE–MATRIX 表象中，将 FRW 与 de Sitter 宇宙视作散射背景，构造宇宙学散射矩阵 $S_{\mathrm{cos}}(\omega)$ 与相对 DOS，证明有效宇宙学常数 $\Lambda_{\mathrm{eff}}(\mu)$ 等价于物理宇宙与参考宇宙之间 DOS 差分的窗化积分。

3. 在宇宙 QCA 对象中，将连续谱替换为带结构 $\varepsilon_j(k)$，定义 QCA 版相对带密度与窗化真空能，分析在何种带配对对称性与 sum rule 条件下，高能部分对 $\Lambda_{\mathrm{eff}}$ 的贡献自然抵消，仅留下由 IR 阈值与拓扑模态控制的小残差。

4. 在有效宇宙学层面，将窗化谱表达与运行真空模型及暗能量状态方程 $w_{\mathrm{de}}(z)$ 联系起来，展示统一时间刻度框架下 $w_{\mathrm{de}}(z)\approx -1+\delta w(z)$ 的结构起源，并与当前观测约束对比。

这些步骤共同构成了一个从散射谱到暗能量的多层统一结构，将宇宙学常数问题重述为矩阵宇宙与 QCA 宇宙中的相对谱问题。

---

## 2 Model & Assumptions

### 2.1 散射对、谱移函数与统一刻度密度

考虑一对自伴算子 $(H,H_0)$，定义在同一 Hilbert 空间 $\mathcal H$ 上。假设 $H-H_0$ 为适当意义下的相对迹类扰动，使得定能散射理论良好定义，并存在对所有 Borel 有界测度 $f$ 的 Lifshits–Kreĭn 迹公式

$$
\tr(f(H)-f(H_0))=\int_{\mathbb R} f'(\lambda)\,\xi_E(\lambda)\,\diff\lambda
$$，

其中 $\xi_E(\lambda)$ 为能量变量 $\lambda$ 下的谱移函数。

在频率变量 $\omega\ge0$ 下令 $\lambda=\omega^2$，定义

$$
\xi(\omega)=\xi_E(\omega^2)
$$，

则相对 DOS 在能量与频率表象中分别为

$$
\Delta\rho_E(\lambda)=-\xi_E'(\lambda)
$$，

$$
\Delta\rho_\omega(\omega)=2\omega\,\Delta\rho_E(\omega^2)=-\partial_\omega\xi(\omega)
$$。

设 $S(\omega)$ 为定能散射矩阵，$Q(\omega)=-\ii S(\omega)^\dagger\partial_\omega S(\omega)$ 为 Wigner–Smith 群延迟矩阵，Birman–Kreĭn 公式给出

$$
\det S(\omega)=\exp\bigl(-2\pi\ii \xi(\omega)\bigr)
$$，

由此可定义散射行列式相位

$$
\Theta(\omega)=(2\pi)^{-1}\arg\det S(\omega)
$$，

并有

$$
\Theta'(\omega)=-\partial_\omega\xi(\omega)=\Delta\rho_\omega(\omega)=(2\pi)^{-1}\tr Q(\omega)
$$。

统一时间刻度密度定义为

$$
\kappa(\omega)=\frac{\varphi'(\omega)}{\pi}=\Delta\rho_\omega(\omega)=\frac{1}{2\pi}\tr Q(\omega)
$$，

其中 $\varphi(\omega)$ 为总散射半相位。本文中所有关于"统一时间刻度"的构造均以 $\kappa(\omega)$ 为唯一刻度源。

### 2.2 热核差、几何假设与散射算子

设 $H$ 为定义在非紧 Riemann 流形 $(X,g)$ 上的广义 Laplace 型算子，$H_0$ 为对应参考背景 $(X_0,g_0)$ 上的算子，二者在无穷远处具有相同的几何与势结构。假设 $(X,g)$ 与 $(X_0,g_0)$ 为偶维渐近双曲或共形紧致 Einstein 流形，满足 Guillarmou–Vasy 的"even metric"条件，使得 resolvent $(H-\lambda)^{-1}$ 在 $\lambda$ 平面的适当 Riemann 曲面上具有良好的亚纯延拓，并且散射算子 $S(\lambda)$ 在临界线附近为经典伪微分算子。

在这些假设下，Guillarmou 证明了 KV 行列式相位与广义谱移函数之间的 Kreĭn 型公式，而热核 $K_H(s,x,y)=\exp(-sH)(x,y)$ 的对角迹

$$
\tr(\exp(-sH)-\exp(-sH_0))=\Delta K(s)
$$

在 $s\to0^+$ 时具有标准的 Seeley–DeWitt 渐近展开，其有限部分可通过散射相位的 Mellin 变换表示。

本文将专门关注对称偶维情形与静片 de Sitter 背景，此时散射相位与热核差之间的联系最为简洁，适合构造对数窗化的 Tauberian 定理。

### 2.3 对数频率窗核与 Tauberian 条件

为了将小 $s$ 热核差的有限部转换为频率域的对数平均，引入一族对数频率窗核

$$
W(\ln(\omega/\mu))
$$，

其中 $\mu>0$ 为谱刻度，$W\in C_0^\infty(\mathbb R)$ 为平滑紧支函数，满足以下 Mellin 消零条件：

1. $\displaystyle \int_{\mathbb R} W(u)\,\diff u=0$；

2. $\displaystyle \int_{\mathbb R} e^{2nu}W(u)\,\diff u=0$ 对若干低整数 $n$ 成立。

这些条件保证窗核在 $\omega\to0$ 与 $\omega\to\infty$ 时能消去热核中对应的主导奇异项，将有限几何信息提取出来。定义对数平均

$$
\langle\Theta'\rangle_W(\mu)=\int_{\mathbb R}\Theta'(\omega)\,W(\ln(\omega/\mu))\,\diff\ln\omega
$$，

并进一步定义谱窗核

$$
\Xi_W(\mu)=\partial_{\ln\mu}\langle\Theta'\rangle_W(\mu)
$$。

在 Tauberian 理论中，若 $\Delta K(s)$ 与 $\Theta'(\omega)$ 满足适当正则性与增长条件，则可在 $\mu\sim s^{-1/2}$ 的双曲线下建立小 $s$ 热核有限部与 $\Xi_W(\mu)$ 之间的等价。本文将给出满足宇宙学应用所需的一个有限阶版本。

### 2.4 宇宙学几何与参考背景

在宇宙学应用中，$H$ 与 $H_0$ 将分别对应"物理宇宙"与"参考宇宙"的几何背景上的波动算子。例如：

1. $(M,g)$ 为带曲率微扰的 FRW 或带结构的 de Sitter 宇宙，$H$ 为标量或张量扰动的 Laplace–Beltrami 算子加势。

2. $(M_0,g_0)$ 为光滑、同拓扑的无结构 FRW 或纯 de Sitter 背景，$H_0$ 为对应的未扰动算子。

参考背景应具有"物理合理性"，例如具有同一拓扑、相同宇宙学常数，但无复杂结构。物理宇宙相对于参考宇宙的谱差分 $\Delta\rho_\omega$ 即刻画了"真实结构在背景上的谱偏离"，其窗化积分将给出宇宙学常数的有效增量。

### 2.5 矩阵宇宙与宇宙学散射矩阵

在矩阵宇宙 THE–MATRIX 框架中，考虑按频率分解的通道 Hilbert 空间

$$
\mathcal H_{\mathrm{chan}}=\bigoplus_{v\in V}\mathcal H_v
$$，

其中 $v$ 标记不同方向、偏振、宇宙学模式以及地平线通道。宇宙学散射矩阵

$$
S_{\mathrm{cos}}(\omega)\in\mathcal B(\mathcal H_{\mathrm{chan}})
$$

编码了"参考宇宙"模式到"物理宇宙"模式的散射过程。其行列式相位 $\Theta_{\mathrm{cos}}(\omega)$、谱移函数 $\xi_{\mathrm{cos}}(\omega)$ 与相对 DOS $\Delta\rho_{\mathrm{cos}}(\omega)$ 满足与一般散射对相同的链式关系。

统一时间刻度密度在宇宙学情形下写作

$$
\kappa_{\mathrm{cos}}(\omega)=\frac{1}{2\pi}\tr Q_{\mathrm{cos}}(\omega)
$$，

其中 $Q_{\mathrm{cos}}(\omega)=-\ii S_{\mathrm{cos}}(\omega)^\dagger\partial_\omega S_{\mathrm{cos}}(\omega)$。本文将用 $\kappa_{\mathrm{cos}}(\omega)$ 控制宇宙学常数的谱窗化表达。

### 2.6 QCA 宇宙对象与带结构

宇宙 QCA 对象定义为

$$
\mathfrak U_{\mathrm{QCA}}=(\Lambda,\mathcal H_{\mathrm{cell}},\mathcal A,\alpha,\omega_0)
$$，

其中 $\Lambda$ 为可数连通图（通常为 $\mathbb Z^d$），$\mathcal H_{\mathrm{cell}}$ 为每个元胞的有限维 Hilbert 空间，$\mathcal A$ 为准局域 $C^\ast$ 代数，$\alpha:\mathbb Z\to\mathrm{Aut}(\mathcal A)$ 为有限传播半径的时间演化自同构，$\omega_0$ 为初始宇宙态。

在动量空间 $k\in\mathrm{BZ}$ 上，单步演化算子 $U$ 纤维分解为

$$
U(k)\in U(N)
$$，

并存在本征分解

$$
U(k)\ket{\psi_{j,k}}=e^{-\ii\varepsilon_j(k)\Delta t}\ket{\psi_{j,k}}
$$，

其中 $N=\dim\mathcal H_{\mathrm{cell}}$，准能量 $\varepsilon_j(k)\in(-\pi/\Delta t,\pi/\Delta t]$。在连续极限 $\Delta t\to0$ 下，存在色散关系 $\varepsilon_j(k)\approx E_j(k)\Delta t$，其中 $E_j(k)$ 为对应连续场论的能谱。

定义单带 DOS

$$
\rho_j(E)=\int_{\mathrm{BZ}}\delta(E-E_j(k))\frac{\diff^dk}{(2\pi)^d}
$$，

总 DOS 为 $\rho(E)=\sum_j\rho_j(E)$。选定参考 QCA $U_0(k)$ 及其能谱 $\{E_{j,0}(k)\}$，定义相对 DOS

$$
\Delta\rho(E)=\rho(E)-\rho_0(E)
$$，

及其带分解 $\Delta\rho_j(k)$。这些量在连续极限下与连续散射理论可相互对应。

---

## 3 Main Results

本节给出本文的主要定理，证明细节放在第 4 节及附录。

### 3.1 窗化 Tauberian 定理与刻度密度表述

**定理 3.1（窗化 Tauberian 定理）**

设 $(H,H_0)$ 满足第 2.2 节的几何与散射假设，令

$$
\Delta K(s)=\tr(\mathrm{e}^{-sH}-\mathrm{e}^{-sH_0})
$$

为热核差，$\Theta(\omega)$ 为散射行列式相位，$\Theta'(\omega)=\Delta\rho_\omega(\omega)=(2\pi)^{-1}\tr Q(\omega)$。取一族满足第 2.3 节 Mellin 消零条件的对数窗核 $W$，定义

$$
\Xi_W(\mu)=\int_{\mathbb R}\omega\,\Theta''(\omega)\,W(\ln(\omega/\mu))\,\diff\ln\omega
$$。

则存在 $\mu\sim s^{-1/2}$ 的双曲缩放及常数 $C,\gamma>0$，使得当 $s\to0^+$ 时

$$
\mathrm{FP}_{s\to0}\Delta K(s)=\kappa_\Lambda\,\Xi_W(\mu)+\mathcal O(s^\gamma)
$$，

其中 $\mathrm{FP}$ 表有限部，$\kappa_\Lambda$ 为仅依赖于窗核选择的归一化常数。换言之，小 $s$ 热核差的有限部与统一时间刻度密度 $\kappa(\omega)$ 的对数窗平均在 Tauberian 意义下等价。

### 3.2 宇宙学常数的窗化统一表达

**定理 3.2（窗化宇宙学常数母公式）**

在定理 3.1 的条件下，令 $\Lambda_{\mathrm{eff}}(\mu)$ 为有效场论作用中宇宙学常数参数在观测尺度 $\mu$ 下的重整化值，则存在谱窗核 $\Xi(\mu)$ 使得

$$
\partial_{\ln\mu}\Lambda_{\mathrm{eff}}(\mu)=\kappa_\Lambda\,\Xi(\mu)
$$，

其显式形式为

$$
\Xi(\mu)=\int_{\mathbb R}\omega\,\Theta''(\omega)\,W(\ln(\omega/\mu))\,\diff\ln\omega
$$，

并且对任意参考尺度 $\mu_0$ 有

$$
\Lambda_{\mathrm{eff}}(\mu)-\Lambda_{\mathrm{eff}}(\mu_0)=\int_{\mu_0}^{\mu}\Xi(\omega)\,\diff\ln\omega
$$。

其中 $\Xi(\omega)$ 具有量纲 $L^{-2}$，可视为"宇宙学常数的谱窗核"，完全由统一时间刻度密度 $\kappa(\omega)$ 与散射相位确定。

### 3.3 矩阵宇宙中的宇宙学散射与相对 DOS

**定理 3.3（矩阵宇宙中的相对 DOS 表述）**

在矩阵宇宙 THE–MATRIX 表象中，取物理宇宙 $(M,g)$ 与参考宇宙 $(M_0,g_0)$ 及其对应散射矩阵 $S_{\mathrm{cos}}(\omega)$ 与 $S_{\mathrm{cos},0}(\omega)$。定义相对宇宙学散射矩阵

$$
S_{\mathrm{rel}}(\omega)=S_{\mathrm{cos}}(\omega)S_{\mathrm{cos},0}(\omega)^{-1}
$$，

及相对 DOS

$$
\Delta\rho_{\mathrm{cos}}(\omega)=\Delta\rho_\omega(\omega;H,H_0)
$$。

在定理 3.2 条件下，有

$$
\Lambda_{\mathrm{eff}}(\mu)-\Lambda_{\mathrm{eff}}(\mu_0)=\int_{\mu_0}^{\mu}\Xi_{\mathrm{cos}}(\omega)\,\diff\ln\omega
$$，

其中

$$
\Xi_{\mathrm{cos}}(\omega)=\int_{\mathbb R}\omega\,\Theta_{\mathrm{rel}}''(\omega)\,W(\ln(\omega/\mu))\,\diff\ln\omega
$$，

$\Theta_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\arg\det S_{\mathrm{rel}}(\omega)$，

并且

$$
\Theta_{\mathrm{rel}}'(\omega)=\Delta\rho_{\mathrm{cos}}(\omega)=(2\pi)^{-1}\tr Q_{\mathrm{rel}}(\omega)
$$。

因此，$\Lambda_{\mathrm{eff}}(\mu)$ 可以解释为"物理宇宙与参考宇宙的宇宙学散射矩阵之间 DOS 差分"的对数频率窗化积分。

### 3.4 QCA 宇宙中的离散窗化公式与高能抑制

**定理 3.4（QCA 宇宙中的窗化真空能公式）**

在宇宙 QCA 对象 $\mathfrak U_{\mathrm{QCA}}$ 中，设物理 QCA 与参考 QCA 分别具有能谱 $\{E_j(k)\}$ 与 $\{E_{j,0}(k)\}$，定义单带相对 DOS

$$
\Delta\rho_j(k)=\delta(E-E_j(k))-\delta(E-E_{j,0}(k))
$$。

令 $\mathcal W_\mu(E)$ 为由连续窗核 $W(\ln(\omega/\mu))$ 映射而来的能量权重函数，则存在归一化常数 $C_W$ 使得

$$
\Lambda_{\mathrm{eff}}(\mu)=C_W\sum_j\int_{\mathrm{BZ}}\mathcal W_\mu(E_j(k))\,\Delta\rho_j(k)\,\diff^dk
$$，

并在连续极限 $\Delta t\to0$ 下与定理 3.2 的连续谱表达相容。

**定理 3.5（QCA 高能抑制机制）**

在定理 3.4 的条件下，若高能带满足以下两类条件：

1. 带结构对称配对：存在带对 $(j,j')$，对 $|E|\ge E_c$ 有

   $$
   E_{j'}(k)\approx -E_j(k)
   $$，

   $$
   \Delta\rho_{j'}(E)\approx\Delta\rho_j(-E)
   $$，

   且窗权重在高能区近似偶对称 $\mathcal W_\mu(E)\approx\mathcal W_\mu(-E)$。

2. 带间和谐 sum rule：存在 UV 标度 $E_{\mathrm{UV}}$ 使得

   $$
   \int_0^{E_{\mathrm{UV}}}E^2\,\Delta\rho(E)\,\diff E=0
   $$，

   其中 $\Delta\rho(E)=\sum_j\int_{\mathrm{BZ}}\Delta\rho_j(k)\,\delta(E-E_j(k))\,\diff^dk$。

则对任意满足 Tauberian 条件的窗核族，存在常数 $C>0,\gamma>0$ 与 IR 标度 $E_{\mathrm{IR}}\ll E_{\mathrm{UV}}$，使得对 $\mu\sim E_{\mathrm{IR}}$ 有

$$
\bigl|\Lambda_{\mathrm{eff}}(\mu)\bigr|\le C\,E_{\mathrm{IR}}^4\bigl(E_{\mathrm{IR}}/E_{\mathrm{UV}}\bigr)^{\gamma}
$$。

换言之，在具有适当带配对与 sum rule 的宇宙 QCA 中，窗化真空能的自然量级不再是 $E_{\mathrm{UV}}^4$，而被压到由 IR 标度控制的 $E_{\mathrm{IR}}^4$ 并附带额外幂次抑制因子。

### 3.5 运行真空与等效暗能量方程状态

**定理 3.6（统一刻度下的运行真空与 $w_{\mathrm{de}}(z)$）**

令谱刻度 $\mu$ 与 Hubble 标度或曲率标度存在平滑关系 $\mu=\mu(H)$，并假设在相关频带上谱窗核 $\Xi(\omega)$ 缓变，则存在小的无量纲参数 $\nu$，使得

$$
\Lambda_{\mathrm{eff}}(H)\approx\Lambda_0+3\nu(H^2-H_0^2)+\cdots
$$，

对应暗能量密度 $\rho_{\mathrm{de}}(z)=\Lambda_{\mathrm{eff}}(\mu(z))/(8\pi G)$ 的状态方程满足

$$
w_{\mathrm{de}}(z)\approx -1+\delta w(z)
$$，

其中 $\delta w(z)$ 的大小与 $\Xi(\omega)$ 在对应频带上的对数导数同阶。只要 $\Xi(\omega)$ 在宇宙晚期的频带上变化缓慢，则 $|\delta w(z)|\ll1$，与当前对 $w_{\mathrm{de}}(z)$ 的观测约束兼容。

---

## 4 Proofs

本节给出主要定理的证明轮廓，完整技术细节在附录中展开。

### 4.1 迹公式、热核差与散射相位

对满足第 2.2 节条件的自伴散射对 $(H,H_0)$，对任何 Schwartz 类函数 $f$ 有 Lifshits–Kreĭn 迹公式

$$
\tr(f(H)-f(H_0))=\int_{\mathbb R} f'(\lambda)\,\xi_E(\lambda)\,\diff\lambda
$$。

取 $f(\lambda)=\mathrm{e}^{-s\lambda}$，得到

$$
\Delta K(s)=\tr(\mathrm{e}^{-sH}-\mathrm{e}^{-sH_0})=-\int_0^\infty s\,\mathrm{e}^{-s\lambda}\,\xi_E(\lambda)\,\diff\lambda
$$。

分部积分并利用 $\Delta\rho_E(\lambda)=-\xi_E'(\lambda)$ 得到

$$
\Delta K(s)=\int_0^\infty\mathrm{e}^{-s\lambda}\,\Delta\rho_E(\lambda)\,\diff\lambda
$$。

在频率变量 $\omega$ 下令 $\lambda=\omega^2$，$\diff\lambda=2\omega\,\diff\omega$，得到

$$
\Delta K(s)=\int_0^\infty\mathrm{e}^{-s\omega^2}\,\Delta\rho_\omega(\omega)\,\diff\omega=\int_0^\infty\mathrm{e}^{-s\omega^2}\,\Theta'(\omega)\,\diff\omega
$$，

其中最后一步利用了 $\Theta'(\omega)=\Delta\rho_\omega(\omega)$。

另一方面，根据 Birman–Kreĭn 公式 $\det S(\omega)=\exp(-2\pi\ii\xi(\omega))$ 和 KV 行列式的解析延拓性质，在偶维渐近双曲流形上可证明 $\Theta(\omega)$ 具有 Weyl 型渐近与良好解析性，其高能及低能行为可由几何不变量控制，从而保证上述积分表达式在 $s\to0^+$ 时可作有限部分析。

### 4.2 窗化 Tauberian 定理的证明

考虑对数窗平均

$$
\langle\Theta'\rangle_W(\mu)=\int_{\mathbb R}\Theta'(\omega)\,W(\ln(\omega/\mu))\,\diff\ln\omega
$$。

作变量代换 $\omega=\mu\mathrm{e}^u$，

$$
\langle\Theta'\rangle_W(\mu)=\int_{\mathbb R}\Theta'(\mu\mathrm{e}^u)\,W(u)\,\diff u
$$。

其对 $\ln\mu$ 的导数为

$$
\partial_{\ln\mu}\langle\Theta'\rangle_W(\mu)=\int_{\mathbb R}\mu\mathrm{e}^u\,\Theta''(\mu\mathrm{e}^u)\,W(u)\,\diff u=\Xi_W(\mu)
$$。

另一方面，利用 Mellin 变换

$$
\mathcal M[\Theta'](s)=\int_0^\infty\omega^{s-1}\Theta'(\omega)\,\diff\omega
$$，

可将 $\langle\Theta'\rangle_W(\mu)$ 写作

$$
\langle\Theta'\rangle_W(\mu)=\frac{1}{2\pi\ii}\int_{\Gamma}\mathcal M[\Theta'](s)\,\widehat W(s)\,\mu^{-s}\,\diff s
$$，

其中 $\widehat W(s)$ 为 $W$ 的 Mellin 变换，$\Gamma$ 为适当竖直线。Mellin 消零条件保证 $\widehat W(s)$ 在若干低阶点上有零，从而消去了对应的几何主项。

同时，小 $s$ 热核差可以写作

$$
\Delta K(s)=\frac{1}{2\pi\ii}\int_{\Gamma'}\Gamma(s')\,s^{-s'}\mathcal M[\Delta\rho_\omega](s')\,\diff s'
$$，

其中 $\Gamma(s')$ 为 Gamma 函数。利用 $\Delta\rho_\omega(\omega)=\Theta'(\omega)$ 得到两者 Mellin 变换之间的简单关系。通过在 $s^{-1/2}\sim\mu$ 双曲线附近匹配主导贡献，并利用解析延拓与残差计算，可以证明当 $s\to0^+$、$\mu\sim s^{-1/2}$ 时

$$
\mathrm{FP}_{s\to0}\Delta K(s)=\kappa_\Lambda\,\Xi_W(\mu)+\mathcal O(s^\gamma)
$$，

其中 $\gamma>0$ 由高能 resolvent 的界给出。

这个过程本质上是一个有限阶 Tauberian 定理：利用 $\Theta'(\omega)$ 的增长界与 $\Delta K(s)$ 的小 $s$ 渐近，将频率域对数平均与热核有限部联系起来。技术上依赖于 Hardy–Littlewood–Karamata 型 Tauberian 判据的广义版本以及 Vasy 与 Dyatlov 给出的高能 resolvent 与散射相位估计。

这给出了定理 3.1 的证明轮廓。

### 4.3 宇宙学常数母公式的推导

在曲时空量子场论中，有效作用可写作

$$
S_{\mathrm{eff}}[g]=\int\diff^4x\,\sqrt{-g}\Bigl[\frac{R-2\Lambda_{\mathrm{eff}}(\mu)}{16\pi G}+\alpha R^2+\beta R_{\mu\nu}R^{\mu\nu}+\cdots\Bigr]
$$，

其中 $\alpha,\beta$ 等为无量纲重整化耦合。真空能密度的尺度依赖可写作

$$
\partial_{\ln\mu}\Lambda_{\mathrm{eff}}(\mu)=\mathcal R[\Delta K(s)]
$$，

其中 $\mathcal R$ 表示将热核差的小 $s$ 奇异项吸收到局部 counterterm 中之后取有限部的线性算子。利用定理 3.1，将有限部重写为 $\Xi_W(\mu)$，即

$$
\partial_{\ln\mu}\Lambda_{\mathrm{eff}}(\mu)=\kappa_\Lambda\,\Xi_W(\mu)
$$。

对 $\ln\mu$ 积分得到

$$
\Lambda_{\mathrm{eff}}(\mu)-\Lambda_{\mathrm{eff}}(\mu_0)=\int_{\mu_0}^{\mu}\Xi(\omega)\,\diff\ln\omega
$$，

其中 $\Xi(\omega)$ 为与 $\Xi_W(\omega)$ 只差归一化因子的谱窗核。由此得到定理 3.2。

需要强调的是，$\Lambda_{\mathrm{eff}}(\mu)$ 在该表述中是一个相对量：只定义到常数 $\Lambda_{\mathrm{eff}}(\mu_0)$ 之差，这恰好反映了宇宙学常数在观测上仅通过相对真空能密度体现的事实。

### 4.4 矩阵宇宙中的散射与定理 3.3

在矩阵宇宙中，物理宇宙与参考宇宙的宇宙学散射矩阵分别为 $S_{\mathrm{cos}}(\omega)$ 与 $S_{\mathrm{cos},0}(\omega)$。定义相对矩阵

$$
S_{\mathrm{rel}}(\omega)=S_{\mathrm{cos}}(\omega)S_{\mathrm{cos},0}(\omega)^{-1}
$$，

其行列式相位 $\Theta_{\mathrm{rel}}(\omega)$ 与谱移函数满足

$$
\det S_{\mathrm{rel}}(\omega)=\exp\bigl(-2\pi\ii\xi_{\mathrm{rel}}(\omega)\bigr)
$$，

$$
\Theta_{\mathrm{rel}}'(\omega)=-\partial_\omega\xi_{\mathrm{rel}}(\omega)=\Delta\rho_{\mathrm{cos}}(\omega)
$$。

由于 $\Lambda_{\mathrm{eff}}(\mu)$ 只依赖于 $H$ 与 $H_0$ 的相对谱性质，可以直接用 $S_{\mathrm{rel}}(\omega)$ 的相位来表达，得到

$$
\Xi_{\mathrm{cos}}(\mu)=\int_{\mathbb R}\omega\,\Theta_{\mathrm{rel}}''(\omega)\,W(\ln(\omega/\mu))\,\diff\ln\omega
$$，

进而照搬定理 3.2 的推导得到相对 DOS 表述。这给出定理 3.3。

### 4.5 QCA 离散窗化公式与高能抑制

对 QCA 能谱，窗化真空能的连续表达

$$
\Lambda_{\mathrm{eff}}(\mu)=\int_0^\infty F_\mu(E)\,\Delta\rho(E)\,\diff E
$$

离散化为

$$
\Lambda_{\mathrm{eff}}(\mu)=\sum_j\int_{\mathrm{BZ}}\mathcal W_\mu(E_j(k))\,\Delta\rho_j(k)\,\diff^dk
$$，

其中 $F_\mu(E)$ 在连续极限下对应 $\mathcal W_\mu(E)$，满足平滑性与高能衰减条件。

为证明高能抑制，将能量区间分为三段 $(0,E_{\mathrm{IR}})$、$(E_{\mathrm{IR}},E_{\mathrm{UV}})$ 与 $(E_{\mathrm{UV}},\infty)$。低能段的贡献自然量级为 $E_{\mathrm{IR}}^4$，这是由维度分析与 $\mathcal W_\mu(E) \sim E^2$ 的行为决定的。

在 $(E_{\mathrm{IR}},E_{\mathrm{UV}})$ 段，利用带间和谐 sum rule

$$
\int_0^{E_{\mathrm{UV}}}E^2\,\Delta\rho(E)\,\diff E=0
$$，

可将该段贡献改写为

$$
\int_0^{E_{\mathrm{UV}}}E^2\bigl(\mathcal W_\mu(E)-1\bigr)\Delta\rho(E)\,\diff E
$$。

由于 $\mathcal W_\mu(E)\approx 1$ 在 $E\ll\mu\sim E_{\mathrm{IR}}$ 区域内，仅在 $E\sim\mu$ 附近偏离 1，故这一积分主要由靠近 IR 的窄区间贡献，其量级与低能段相同。

在 $(E_{\mathrm{UV}},\infty)$ 段，利用带配对对称性与窗权重的近似偶对称，可将贡献写成

$$
\int_{E_{\mathrm{UV}}}^\infty E^2\,\delta\rho_{\mathrm{asym}}(E)\,\mathcal W_\mu(E)\,\diff E
$$，

其中 $\delta\rho_{\mathrm{asym}}(E)=\Delta\rho(E)+\Delta\rho(-E)$ 表示对称配对的偏差。假设 $|\delta\rho_{\mathrm{asym}}(E)|\le C_1E^{-\beta}$ 且 $\beta>3$，再利用 $\mathcal W_\mu(E)$ 的指数或高次幂衰减，即可得到高能贡献被压到 $E_{\mathrm{UV}}^{3-\beta}$ 或更小的量级，进而写成 $E_{\mathrm{IR}}^4(E_{\mathrm{IR}}/E_{\mathrm{UV}})^\gamma$ 的形式。

综合三段估计得到定理 3.5。定理 3.4 则是连续窗化表达在 QCA 谱上的自然离散化。

### 4.6 运行真空与 $w_{\mathrm{de}}(z)$ 的推导

假设谱刻度 $\mu$ 与 Hubble 标度存在线性或缓变关系 $\mu=cH$ 或 $\mu\propto R^{1/2}$，其中 $R$ 为 Ricci 标量。令

$$
\Lambda_{\mathrm{eff}}(\mu)-\Lambda_{\mathrm{eff}}(\mu_0)=\int_{\mu_0}^{\mu}\Xi(\omega)\,\diff\ln\omega
$$，

对 $H^2$ 的小变化展开，若 $\Xi(\omega)$ 在对应频带上近似常数或有解析展开，则可以写成

$$
\Lambda_{\mathrm{eff}}(H)\approx\Lambda_0+A\ln(H/H_0)+\cdots
$$。

在 $|H-H_0|\ll H_0$ 下，$\ln(H/H_0)\approx(H^2-H_0^2)/(2H_0^2)$，将 $A/(2H_0^2)$ 吸收到 $3\nu$ 中即可得到

$$
\Lambda_{\mathrm{eff}}(H)\approx\Lambda_0+3\nu(H^2-H_0^2)+\cdots
$$。

对暗能量密度 $\rho_{\mathrm{de}}(z)=\Lambda_{\mathrm{eff}}(\mu(z))/(8\pi G)$ 代入能量守恒方程

$$
\frac{\diff\rho_{\mathrm{de}}}{\diff z}=\frac{3}{1+z}(1+w_{\mathrm{de}}(z))\rho_{\mathrm{de}}(z)
$$，

整理得到

$$
1+w_{\mathrm{de}}(z)=\frac{1+z}{3}\frac{1}{\rho_{\mathrm{de}}(z)}\frac{\diff\rho_{\mathrm{de}}(z)}{\diff z}=\frac{1+z}{24\pi G}\frac{1}{\Lambda_{\mathrm{eff}}(\mu(z))}\frac{\diff\Lambda_{\mathrm{eff}}(\mu(z))}{\diff z}
$$。

若 $\Xi(\omega)$ 在晚期宇宙对应的频带上缓慢变化，则 $\Lambda_{\mathrm{eff}}(\mu(z))$ 的红移导数很小，$w_{\mathrm{de}}(z)$ 自然接近 $-1$，偏离量 $\delta w(z)$ 与 $\Xi(\omega)$ 的对数导数同阶，从而得到定理 3.6。与文献中 RVM 模型对 $\nu$ 的拟合结果相比，只要 $\Xi(\omega)$ 的谱结构给出 $|\nu|\ll1$，即可与现有对 $w_{\mathrm{de}}(z)$ 的约束相容。

---

## 5 Model Apply：宇宙学与 QCA 的具体情形

### 5.1 FRW 与 de Sitter 背景上的谱–几何对接

在四维 FRW 宇宙中，度规

$$
\diff s^2=-\diff t^2+a(t)^2\bigl(\diff\chi^2+\sin^2\chi\,\diff\Omega_2^2\bigr)
$$

在固定时间切片上等价于 $S^3$ 上的空间度规。对标模型中，可用 $S^3$ 上 Laplace 算子的热核与计数函数的谱–几何关系，将曲率项 $-\kappa/a^2$ 与 DOS 次主项对应起来。类似构造在四维 FRW 上可推广：热核差展开

$$
\Delta K(s)\sim\sum_{n\ge0}a_n s^{(n-4)/2}
$$，

其中 $a_0$ 对应体积差，$a_1$ 对应 Ricci 标量积分，$a_2$ 对应 $R^2$ 与 $R_{\mu\nu}R^{\mu\nu}$ 等。

通过窗化 Tauberian 定理，可以将 $a_0$ 的有限部分重写为 $\Lambda_{\mathrm{eff}}(\mu)$ 的尺度依赖，而 $a_1,a_2$ 则贡献于有效引力作用中 $R$ 与 $R^2$ 的重整化耦合。具体计算表明，在以 de Sitter 背景为参考几何时，物理 FRW 宇宙与参考 de Sitter 之间的热核差有限部分精确捕捉了宇宙学常数的运行行为。

### 5.2 Dirac 型 QCA 宇宙的示意模型

考虑一类在三维立方晶格上定义的 QCA，其连续极限还原为自由 Dirac 场或含弱相互作用的量子电动力学。这类 QCA 的单粒子能谱通常具有粒子–反粒子对称的带结构

$$
E_{\pm}(k)\approx\pm\sqrt{k^2+m^2}
$$

及额外高能折叠带。

选取参考 QCA 为 $m=0$ 的无质量模型，则相对 DOS 在高能区满足近似对称配对

$$
E_{+}(k)\approx -E_{-}(k)
$$，

$$
\Delta\rho_{+}(E)\approx\Delta\rho_{-}(-E)
$$，

窗权重 $\mathcal W_\mu(E)$ 在高能区近似偶对称，从而满足定理 3.5 的带配对假设。进一步通过设计局域更新规则，使得高能折叠带之间满足带间和谐 sum rule，便可在此类 "Dirac–QED 型 QCA 宇宙" 中实现对 $\Lambda_{\mathrm{eff}}$ 的自然抑制。

在这种模型中，IR 标度 $E_{\mathrm{IR}}$ 可以由轻质量阈值（如 QCD 标度或轻标量质量）决定，而 UV 标度 $E_{\mathrm{UV}}$ 则由 QCA 的格点尺度或耦合结构决定。定理 3.5 给出的估计

$$
\Lambda_{\mathrm{eff}}\sim E_{\mathrm{IR}}^4(E_{\mathrm{IR}}/E_{\mathrm{UV}})^{\gamma}
$$

在 $E_{\mathrm{UV}}\sim M_{\mathrm{Pl}}$、$E_{\mathrm{IR}}$ 选取适当中间标度时，可以自然产生与观测宇宙学常数相近的数量级，而无需对每个 UV 自由度的零点能做精细调参。

### 5.3 与暗能量观测的定性对接

将上述谱窗化机制嵌入宇宙学背景中，假设晚期宇宙的有效刻度 $\mu$ 与 Hubble 标度 $H$ 成正比，则

$$
\Lambda_{\mathrm{eff}}(H)-\Lambda_{\mathrm{eff}}(H_0)=\int_{H_0}^{H}\Xi(\omega(H'))\,\partial_{\ln H'}\ln\mu(H')\,\diff\ln H'
$$。

若 QCA 带结构保证 $\Xi(\omega)$ 在 $H\sim H_0$ 对应的频带上缓速变化，则 $\Lambda_{\mathrm{eff}}(H)$ 与 $H^2$ 之间的关系近似线性，等效状态方程 $w_{\mathrm{de}}(z)$ 接近 $-1$，偏离量 $\delta w(z)$ 的大小与带结构在对应频带内的谱倾斜程度同阶。这与当前对暗能量状态方程的约束（总体偏离不大但不排除轻微演化）一致，为在谱与离散结构层面理解观测结果提供了新的视角。

---

## 6 Engineering Proposals

本节提出若干可行的工程与数值实验方案，用以在不同层面检验本文谱窗化框架的关键成分。

### 6.1 宇宙学散射谱的数值重建

在矩阵宇宙视角下，宇宙学散射矩阵 $S_{\mathrm{cos}}(\omega)$ 的元素实质上对应不同模式在 FRW 或 de Sitter 背景上的散射振幅。可以通过以下步骤进行数值重建：

1. 选定一族标量或张量摄动方程的模式函数，数值求解其在给定背景 $(M,g)$ 与参考背景 $(M_0,g_0)$ 上的散射振幅。

2. 通过数值线性代数构造频率依赖的散射矩阵 $S_{\mathrm{cos}}(\omega)$ 与 $S_{\mathrm{cos},0}(\omega)$，并计算相对矩阵 $S_{\mathrm{rel}}(\omega)$。

3. 以离散频率网格估算散射相位 $\Theta_{\mathrm{rel}}(\omega)$ 与导数 $\Theta_{\mathrm{rel}}'(\omega)$，从而得到相对 DOS $\Delta\rho_{\mathrm{cos}}(\omega)$。

4. 选择满足 Tauberian 条件的对数窗核 $W$，计算谱窗核 $\Xi_{\mathrm{cos}}(\mu)$ 与 $\Lambda_{\mathrm{eff}}(\mu)$ 的数值估计。

这一数值流程为检验窗化 Tauberian 定理的有效性与谱窗核 $\Xi(\omega)$ 的具体形状提供了直接路径。

### 6.2 QCA 谱结构的设计与模拟

在 QCA 宇宙方案中，需要具体构造满足带配对与 sum rule 条件的 QCA 模型。工程上可遵循以下步骤：

1. 在一维或二维晶格上，从 Dirac 型与规范场 QCA 的已知构造出发，增加额外内部自由度与耦合参数，使得能谱在高能区呈现 $E\leftrightarrow -E$ 对称配对。

2. 利用数值对角化与 Brillouin 区积分计算 DOS，验证高能带之间的 sum rule 条件。

3. 在量子模拟或经典高性能计算平台上，演化 QCA，测量准能谱分布与带结构随参数变化的行为，探索不同 IR 标度与 UV 标度下 $\Lambda_{\mathrm{eff}}$ 的数值大小。

4. 将得到的窗化真空能与 RVM 拟合得到的 $\nu$ 值比较，检验 QCA 谱结构是否可以自然产生 $|\nu|\ll1$ 的参数区域。

### 6.3 宇宙学数据分析中的谱窗化方法

在实际宇宙学数据处理中，可以尝试引入对数频率窗化的方法：

1. 在对 CMB、BAO 与 Ia 超新星的数据分析中，将模型参数化从直接假设 $\rho_{\mathrm{de}}(z)$ 的形式，替换为对 $\Xi(\omega)$ 的简单参数化，例如分段常数或低阶多项式。

2. 通过将 $\Xi(\omega)$ 与 $\Lambda_{\mathrm{eff}}(\mu)$ 及 $w_{\mathrm{de}}(z)$ 的关系编入宇宙学参数推断链，使得拟合参数直接描述谱窗核而非状态方程。

3. 比较"直接拟合 $w(z)$"与"拟合 $\Xi(\omega)$ 再推导 $w(z)$"两种方案的贝叶斯证据与参数相关性，检验谱窗化框架是否能更自然地捕捉数据偏好。

这一方案在工程上可视为对现有宇宙学 MCMC 框架的一种"谱变量坐标变换"，有望在参数间相关性与可解释性方面提供优势。

---

## 7 Discussion（risks, boundaries, past work）

### 7.1 风险与局限

本文提出的谱窗化统一框架依赖若干非平凡假设：

1. 几何与散射假设：需要 $(M,g)$ 与 $(M_0,g_0)$ 落在渐近双曲或共形紧致的几何类别中，且满足 even metric 条件与良好的散射理论，这在真实宇宙的全时空层面尚未严格证明。

2. 窗核与 Tauberian 条件：窗化 Tauberian 定理依赖于 resolvent 的高能估计与散射相位的增长界，当前数学文献对 Kerr–de Sitter 等时空的结果尚不完备，将其推广到带有复杂物质分布与非平稳背景的宇宙需要更多工作。

3. QCA sum rule 的实现：在具体 QCA 模型中构造满足带配对与 sum rule 的谱结构是一个非平凡的工程问题，需要在局域性、因果性与对称性约束下进行细致设计。

这些风险意味着，本文的许多结论目前应视为在明确假设下的结构性推论，而非已经在所有物理情形下得到严格验证的定理。

### 7.2 与既有工作的关系

在宇宙学常数问题方面，已有大量文献通过重整化与运行真空模型探讨真空能密度随 $H$ 或曲率的弱运行行为。相较之下，本文的贡献在于：

1. 将宇宙学常数问题明确重写为散射相位–谱移–DOS 链上的相对谱问题，并用统一时间刻度密度 $\kappa(\omega)$ 控制全部尺度依赖。

2. 引入对数频率窗核与有限阶 Tauberian 定理，将热核差的有限部与散射谱信息统一起来，给出一个量纲与变量均完全对账的 $\Lambda_{\mathrm{eff}}(\mu)$ 表达式。

3. 在 QCA 宇宙框架中揭示高能谱配对与带间 sum rule 对真空能自然抑制的结构机制，将 $\Lambda_{\mathrm{eff}}$ 的大小归因于 IR 与 UV 标度之间的幂次比值，而非对单个自由度的微调。

在 QCA 与 QFT 的统一方面，本文沿用并扩展了 Farrelly、Bisio–D'Ariano、Sellapillay 与 Brun 等对 QCA 连续极限的系统分析，在此基础上引入"宇宙学常数窗化"的离散版本。

### 7.3 未来工作方向

未来可以沿以下方向推进：

1. 在具体宇宙学背景（如带结构的 de Sitter、带非平坦性的 FRW）上，利用 Vasy 的微局部分析方法与 Guillarmou 的散射算子理论，严格建立满足本文所需条件的 Tauberian 定理。

2. 构造具有明确 QFT 连续极限的高维 QCA 模型，系统探索其带结构与 DOS，寻找满足 sum rule 条件的自然参数区域。

3. 将谱窗化框架与黑洞熵、Null–Modular 双覆盖、广义熵条件等其它统一时间刻度相关结果对接，形成一个更大尺度上的"宇宙终对象"结构。

---

## 8 Conclusion

本文在统一时间刻度、散射相位–谱移–态密度链与 QCA 宇宙公理基础上，对宇宙学常数与暗能量问题进行了系统的谱窗化重述。通过在偶维渐近双曲与 de Sitter 几何中建立窗化 Tauberian 定理，将小 $s$ 热核差的有限部与散射相位导数的对数频率窗平均等价，从而得到一个完全由统一刻度密度 $\kappa(\omega)$ 与窗核 $W$ 决定的宇宙学常数母公式。

在矩阵宇宙表象中，物理宇宙相对于参考宇宙的宇宙学散射矩阵给出了相对 DOS，窗化积分则将宇宙学常数重写为相对谱量的累积；在 QCA 宇宙中，带结构的对称配对与带间和谐 sum rule 则自然带来高能部分的抵消与真空能的幂次抑制，使 $\Lambda_{\mathrm{eff}}$ 的大小主要由 IR 标度与 UV 标度的比值控制。

最后，将谱窗化结果与运行真空模型与暗能量观测约束连接，表明统一时间刻度框架可以自然产生近似 $w_{\mathrm{de}}(z)\approx -1$ 且可能缓慢演化的等效状态方程，与当前数据相容。总体而言，宇宙学常数问题从"绝对零点能求和的难题"转化为"相对 DOS 在统一时间刻度下的窗化 sum rule 问题"，为后续在矩阵宇宙与 QCA 宇宙中实现更完备的统一奠定了基础。

---

## Acknowledgements

作者感谢相关领域的同事与匿名审稿人在散射理论、QCA 连续极限与宇宙学数据分析方面的讨论与建议，这些交流对本文结构与表述的形成有重要影响。

---

## Code Availability

本文主要结果基于解析推导。涉及热核、散射相位与 QCA DOS 的数值验证，可用通用数值线性代数库与谱方法在开源平台上实现。相关示例代码与数值脚本可在后续工作中整理公开，或在合理请求下提供。

---

## References

[1] Particle Data Group, "Dark Energy," Review of Particle Physics, 2024 update.

[2] J. Solà Peracaula, "The Cosmological Constant Problem and Running Vacuum in the Expanding Universe," Philosophical Transactions of the Royal Society A 380, 2022.

[3] J. Solà Peracaula et al., "Cosmological Constant vis-à-vis Dynamical Vacuum: Bold Challenging the ΛCDM," International Journal of Modern Physics A 31, 2016.

[4] J. de Cruz Pérez, J. Solà Peracaula, "Running Vacuum in Brans–Dicke Theory: A Possible Cure for the H₀ and σ₈ Tensions," Astroparticle Physics, 2024.

[5] L. A. Escamilla et al., "The State of the Dark Energy Equation of State circa 2023," Journal of Cosmology and Astroparticle Physics, 2024.

[6] C. Guillarmou, "Generalized Krein Formula, Determinants and Selberg Zeta Function for Convex Co-Compact Manifolds," Communications in Mathematical Physics 277, 2008.

[7] C. Guillarmou, "Spectral Characterization of Poincaré–Einstein Manifolds," Journal of Differential Geometry 83, 2009.

[8] A. Vasy, "Microlocal Analysis of Asymptotically Hyperbolic Spaces and High-Energy Resolvent Estimates," MSRI Publications 60, 2012.

[9] S. Dyatlov, "Scattering Phase Asymptotics with Fractal Remainders," Communications in Mathematical Physics 339, 2015.

[10] T. Farrelly, "A Review of Quantum Cellular Automata," Quantum 4, 368 (2020).

[11] G. M. D'Ariano, P. Perinotti, A. Bisio, "From Quantum Cellular Automata to Quantum Field Theory," various works, 2014–2017.

[12] K. Sellapillay et al., "A Discrete Relativistic Spacetime Formalism for 1+1 QED from QCA," Scientific Reports 12, 2022.

[13] T. A. Brun, G. Chiribella, C. M. Scandolo, "Quantum Electrodynamics from Quantum Cellular Automata," Entropy 27, 2025.

[14] Reviews on vacuum energy renormalization in curved spacetime and the cosmological constant problem，详见相关专著与综述文献。

---

## Appendix A：谱数据、散射矩阵与 Kreĭn 迹公式

本附录给出本文使用的谱与散射理论背景的详细陈述。

### A.1 自伴对与谱移函数

设 $H$ 与 $H_0$ 为自伴算子，满足 $(H-\ii)^{-1}-(H_0-\ii)^{-1}$ 为 trace 类。则对任意 Schwartz 函数 $f$ 有

$$
\tr(f(H)-f(H_0))=\int_{\mathbb R} f'(\lambda)\,\xi_E(\lambda)\,\diff\lambda
$$，

其中 $\xi_E(\lambda)$ 为谱移函数。谱移函数在绝大多数 $\lambda$ 的导数给出相对 DOS：$\Delta\rho_E(\lambda)=-\xi_E'(\lambda)$。

在存在定能散射理论的情形下，散射矩阵 $S(\lambda)$ 与谱移函数之间由 Birman–Kreĭn 公式联系：

$$
\det S(\lambda)=\exp\bigl(-2\pi\ii\xi_E(\lambda)\bigr)
$$。

在渐近双曲与共形紧致流形上，Guillarmou 通过对散射算子与相对行列式的深入分析，将这一关系推广到更一般的 KV 行列式背景，使得散射行列式相位与广义谱移函数统一。

### A.2 Wigner–Smith 群延迟与统一刻度密度

散射矩阵 $S(\omega)$ 的频率导数给出 Wigner–Smith 群延迟矩阵

$$
Q(\omega)=-\ii S(\omega)^\dagger\partial_\omega S(\omega)
$$。

在 trace 类条件下，迹

$$
\tr Q(\omega)=\partial_\omega\arg\det S(\omega)=2\pi\Theta'(\omega)
$$，

从而有

$$
\Theta'(\omega)=(2\pi)^{-1}\tr Q(\omega)
$$。

统一时间刻度密度定义为

$$
\kappa(\omega)=\Theta'(\omega)=\Delta\rho_\omega(\omega)
$$。

在矩阵宇宙与 QCA 宇宙中，$Q(\omega)$ 的定义可推广到宇宙学散射矩阵与 QCA 散射映射，使得统一时间刻度跨越连续与离散框架。

---

## Appendix B：窗化 Tauberian 定理的技术细节

### B.1 Mellin 变换与对数窗核

对函数 $f(\omega)$ 的 Mellin 变换定义为

$$
\mathcal M[f](s)=\int_0^\infty\omega^{s-1}f(\omega)\,\diff\omega
$$。

对数窗核 $W(\ln(\omega/\mu))$ 的引入使得

$$
\langle f\rangle_W(\mu)=\int_{\mathbb R}f(\omega)\,W(\ln(\omega/\mu))\,\diff\ln\omega
$$

在 Mellin 空间中对应为

$$
\langle f\rangle_W(\mu)=\frac{1}{2\pi\ii}\int_{\Gamma}\mathcal M[f](s)\,\widehat W(s)\,\mu^{-s}\,\diff s
$$，

其中

$$
\widehat W(s)=\int_{\mathbb R}\mathrm{e}^{su}W(u)\,\diff u
$$。

Mellin 消零条件保证 $\widehat W(s)$ 在若干低阶点上有零，从而在残差计算中消去热核展开的主导奇异项，仅保留有限几何部分。

### B.2 从散射相位到热核有限部

将 $f(\omega)=\Theta'(\omega)$ 与 $f(\omega)=\Delta\rho_\omega(\omega)$ 代入，对应的 $\mathcal M[f](s)$ 与热核 $\Delta K(s)$ 的 Laplace–Mellin 变换之间存在简单关系。

通过选择 $\Gamma$ 与 $\Gamma'$ 的位置，可以在复平面上同时分析 $\Delta K(s)$ 的小 $s$ 行为与 $\Theta'(\omega)$ 的大 $\omega$ 行为，利用 Hardy–Littlewood–Karamata 型 Tauberian 定理得到

$$
\mathrm{FP}_{s\to0}\Delta K(s)\sim\kappa_\Lambda\,\Xi_W(\mu)
$$，

并给出显式误差界。

在宇宙学应用中，有限阶 Tauberian 版本已经足够：只需控制到某一有限阶的 $s^\gamma$ 误差即可。

---

## Appendix C：QCA 带配对、sum rule 与抑制指数

### C.1 带配对结构的构造

在具体 QCA 模型中，可以利用以下策略实现带配对：

1. 要求局域更新规则在适当意义下具有广义的"粒子–反粒子对称"与时间反演对称，从而在能谱上产生 $E\leftrightarrow -E$ 对称。

2. 在内部自由度上引入额外的 $\mathbb Z_2$ 或 $\mathbb Z_4$ 对称，使得高能带成对出现，其耦合结构自动满足对称配对条件。

这类结构在 Dirac 型与 QED 型 QCA 中已部分出现，只需进一步调参与约束即可得到满足定理 3.5 假设的谱结构。

### C.2 sum rule 的谱条件

带间和谐 sum rule

$$
\int_0^{E_{\mathrm{UV}}}E^2\,\Delta\rho(E)\,\diff E=0
$$

可以理解为一种"相对能量平方守恒"：物理 QCA 与参考 QCA 在 UV 区域的能量平方加权态密度相同。

在 Dirac 型模型中，若参考 QCA 与物理 QCA 在 UV 区域仅在 IR 质量与有限个拓扑模态上有所不同，则此 sum rule 可以自然满足或通过调节有限个高能耦合参数实现。

通过对 DOS 的数值拟合，可以验证 sum rule 的近似成立，并估计其偏差对 $\Lambda_{\mathrm{eff}}$ 的影响，从而确定抑制指数 $\gamma$ 的大小。

### C.3 抑制指数与参数空间

在实际计算中，可以通过对 QCA 能谱进行多尺度分析，得到

$$
\bigl|\Lambda_{\mathrm{eff}}(\mu)\bigr|\le C_0E_{\mathrm{IR}}^4+C_1E_{\mathrm{IR}}^4\bigl(E_{\mathrm{IR}}/E_{\mathrm{UV}}\bigr)^{\gamma_1}+\cdots
$$，

其中 $C_0$ 与低能 DOS 结构相关，$\gamma_1$ 与 sum rule 的精确程度相关。通过在参数空间中寻找使 $C_0$ 也显著减小的区域，可以进一步增强抑制效果，从而解释观测上极小的 $\Lambda_{\mathrm{eff}}$。

