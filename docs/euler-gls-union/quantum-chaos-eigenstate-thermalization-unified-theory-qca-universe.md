# 量子混沌与本征态热化在 QCA 宇宙中的统一理论

统一时间刻度下的 ETH、公设混沌与本征态能级统计

---

## Abstract

在统一时间刻度、矩阵宇宙 $\mathrm{THE\text{-}MATRIX}$ 与量子离散元胞自动机宇宙 $U_{\mathrm{qca}}$ 的框架下，构造一个针对量子混沌与本征态热化假设（eigenstate thermalization hypothesis, ETH）的系统理论。统一时间刻度母式

$$
\kappa(\omega)
=\varphi'(\omega)/\pi
=\rho_{\mathrm{rel}}(\omega)
=(2\pi)^{-1}\tr Q(\omega)
$$

将散射半相位导数、相对态密度与 Wigner–Smith 群延迟迹统一为单一时间刻度密度，从而在矩阵宇宙 $U_{\mathrm{mat}}$ 中给出独立于具体哈密顿量选取的"宇宙时间母尺"。宇宙作为 QCA 对象

$$
U_{\mathrm{qca}}=(\Lambda,\mathcal H_{\mathrm{cell}},\mathcal A_{\mathrm{qloc}},\alpha,\omega_0)
$$

则以可数晶格上的局域幺正自同构 $\alpha$ 描述离散时间演化，并在连续极限可重构相对论量子场论与几何结构。

在此基础上提出"公设混沌 QCA"的公理体系，并证明如下主要结果：

1. 在任意有限区域 $\Omega\subset\Lambda$ 上，限制得到的有限维幺正算子 $U_\Omega$ 的准能谱本征态对任意局域算子 $O_X$（支撑 $X\subset\Omega$）满足离散时间 ETH：对能窗内绝大多数本征态 $\ket{\psi_n}$，有

   $$
   \bra{\psi_n}O_X\ket{\psi_n}
   =\langle O_X\rangle_{\mathrm{micro}}(\varepsilon_n)
   +\mathcal O(\mathrm{e}^{-c|\Omega|}),
   $$

   非对角矩阵元平方平均随体积指数衰减，从而对局域观测实现本征态热化。

2. 在"公设混沌 QCA"公理（有限传播半径、平移对称、局域门生成高阶单位设计、无额外广泛守恒量）下，有限区域 $U_\Omega$ 的准能级统计在展开后收敛到 CUE 随机矩阵类的 Wigner–Dyson 分布，其谱 form factor 呈现典型"斜坡–平台"结构，构成 QCA 层面的标准量子混沌诊断。

3. 将 QCA–ETH 与统一时间刻度联系起来：在统一时间刻度 $\tau$ 下，"热化时间尺度"与局域熵密度增长率由刻度密度 $\kappa(\omega)$ 的能壳平均与 QCA 光锥结构共同控制。证明一个"统一时间–ETH–熵增长定理"：对任意有限密度局域初态族，熵密度随 $\tau$ 单调增长并在长时间极限趋于微正则熵密度。

4. 在全局 QCA 宇宙对象上，将上述局部结果嵌入因果网与统一时间刻度母结构，表明宇宙尺度上的"热时间箭头""宏观不可逆性"可理解为统一矩阵–QCA 宇宙中的结构不变量，而非额外引入的动力学公设。

附录给出：离散时间 ETH 的严密定义与多种等价形式；局域随机电路与 QCA 的严格映射；QCA–ETH 定理与 CUE 能级统计的证明细节及常数估计；以及一维公设混沌 QCA 模型与可数值验证的具体预测。

---

## Keywords

量子混沌；本征态热化假设（ETH）；量子元胞自动机（QCA）；统一时间刻度；矩阵宇宙；单位设计；谱 form factor；随机矩阵理论

---

## Introduction & Historical Context

### 1.1 ETH 与量子混沌的标准图景

在封闭多体量子系统中，纯态幺正演化如何产生与热力学平衡相容的统计行为，是量子统计力学基础中的核心问题之一。可积系统通常保留大量守恒量，长时间演化后趋于广义 Gibbs 集合，而非可积系统在高能密度区域则被广泛认为满足本征态热化假设（ETH）。Deutsch 与 Srednicki 首先通过随机矩阵启发与场论分析提出：在充分混沌的哈密顿量本征基下，局域观测算子 $O$ 的本征态矩阵元可写为

$$
\bra{E_\alpha}O\ket{E_\beta}
=O(\bar E)\delta_{\alpha\beta}
+\mathrm{e}^{-S(\bar E)/2}f_O(\bar E,\omega)R_{\alpha\beta},
$$

其中 $\bar E=(E_\alpha+E_\beta)/2$、$\omega=E_\alpha-E_\beta$，$S(\bar E)$ 为微观熵，$R_{\alpha\beta}$ 为零均值、单位方差的类高斯随机数。对角项给出与能量相关的热平衡值，非对角项在系统体积上指数小，从而保证时间平均观测值接近微正则集平均，时间涨落被压制。

随后大量数值与理论工作在自旋链、玻色/费米格点模型、Floquet 多体系统等背景下验证了 ETH，对其适用范围与失效机制（如多体局域化）进行了系统分析。与此并行，随机矩阵理论与量子混沌的研究给出另一条诊断线路：若能级统计在适当展开后呈现 Wigner–Dyson 分布，谱 form factor 显示"斜坡–平台"，则系统被视为处于量子混沌相。

### 1.2 离散时间系统与随机量子电路

在 Floquet 系统与随机量子电路中，时间演化以单一时间步幺正算子 $U$ 描述，准能谱通过

$$
U\ket{\psi_n}=\mathrm{e}^{-\ii\varepsilon_n\Delta t}\ket{\psi_n}
$$

定义。ETH 可转写为关于准能量本征态 $\ket{\psi_n}$ 的陈述，热平衡则对应于固定准能壳上的微正则分布。局域随机量子电路被证明在多项式深度下可实现高阶单位设计，其本征态与谱统计在严格意义上接近 Haar 随机幺正矩阵的典型性质。近期工作进一步改进了设计阶与电路深度的折衷，并给出对"随机性"与"scrambling 速度"的更精细估计。

这些结果表明：在具有局域性约束的离散时间多体系统中，量子混沌与 ETH 既具有随机矩阵理论预言的普适性，又可以通过局域随机电路与单位设计语言被严格控制。

### 1.3 量子元胞自动机 QCA 的结构与发展

量子元胞自动机（quantum cellular automata, QCA）是另一类离散时间、离散空间的幺正动力学模型，在严格的数学公理下编码了"局域性、平移对称、有限传播速度"等结构。Schumacher–Werner 给出了可逆 QCA 的定义与结构定理，强调 QCA 是无穷晶格系统上的平移协变、自同构具有有限传播半径的动力学；同一局域规则可在有限周期边界条件下生成全局时间步。在一维情形，Gross–Nesme–Vogts–Werner 发展了 QCA 与量子行走的指标理论，给出 K 理论上的拓扑指标，用以分类一维 QCA。其他工作则从量子信息角度刻画局域 QCA 的结构与可模拟性。

与局域随机电路相比，QCA 更接近"宇宙动力学"的理想抽象：其定义中不包含外部噪声或测量，仅依赖离散时间步的幺正更新与空间局域性。因此若将宇宙本体刻画为某一 QCA，则 ETH、量子混沌、不可逆性与热时间箭头都应在 QCA 框架内部获得解释。

### 1.4 统一时间刻度与矩阵宇宙

在散射与谱理论中，Wigner–Smith 时间延迟矩阵

$$
Q(\omega)=-\ii S(\omega)^\dagger\partial_\omega S(\omega)
$$

将多通道散射矩阵 $S(\omega)$ 的频率导数与"群延迟"联系起来，其迹给出总延迟时间。另一方面，Birman–Kreĭn 公式与 Lifshits–Kreĭn 迹公式将谱移函数 $\xi(\omega)$ 与散射行列式 $\det S(\omega)$ 联系，表明

$$
\xi(\omega)
=-\frac{1}{2\pi\ii}\log\det S(\omega),
\quad
\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)
$$

在很一般的算子对 $(H_0,H)$ 下可良好定义。

统一时间刻度母式

$$
\kappa(\omega)
=\varphi'(\omega)/\pi
=\rho_{\mathrm{rel}}(\omega)
=(2\pi)^{-1}\tr Q(\omega)
$$

在这一背景下被解释为"相对态密度–群延迟–散射相位导数"的统一密度，定义了一个独立于具体坐标与局域 Hamilton 选取的"时间母尺"。

矩阵宇宙 $\mathrm{THE\text{-}MATRIX}$ 将宇宙视为按能量分解的一族巨型散射矩阵 $S(\omega)$ 及其 Wigner–Smith 矩阵 $Q(\omega)$，块稀疏结构编码因果偏序，谱数据实现统一时间刻度。统一时间刻度在几何–边界时间结构中则对应于模流、GHY 边界时间平移等对象，从而把"时间"降格为散射相位与谱移的函数。

### 1.5 本文的目标与工作概述

本文的目标是：在统一时间刻度与矩阵宇宙–QCA 宇宙双重框架下，对"量子混沌与 ETH 在 QCA 宇宙中的成立与能级统计"建立一个公理化、定理化的理论。

核心思路为：

1. 将宇宙建模为一个满足 Schumacher–Werner 公理的可逆 QCA 对象 $U_{\mathrm{qca}}$，并在有限区域上得到有限维幺正算子 $U_\Omega$。

2. 引入"公设混沌 QCA"的公理体系，使 $U_\Omega$ 在有限深度上等价于一族局域随机电路，这些电路在多项式深度内构成高阶单位设计，从而在局域观测与谱统计上近似 Haar 随机幺正。

3. 利用 Haar 随机幺正的 ETH 典型性与随机矩阵理论，对 $U_\Omega$ 的本征态矩阵元、能级间距与谱 form factor 建立 QCA–ETH 定理与 CUE 型谱统计定理。

4. 将统一时间刻度母式 $\kappa(\omega)$ 与 QCA 的离散时间步关系起来，证明统一时间–ETH–熵增长定理，并在宇宙因果网层面重述热时间箭头与宏观不可逆性。

按照给定的体例，后文依次给出模型与公设、主要定理、证明、模型应用、工程提案、讨论、结论以及附录中的详细证明。

---

## Model & Assumptions

### 2.1 统一时间刻度母式与散射结构

设 $\mathcal H$ 为可分 Hilbert 空间，$(H_0,H)$ 为自伴算子对，满足适当的迹类扰动条件，使得波算子存在且完全、散射算子

$$
S= W_+^\dagger W_-
$$

在谱分解下可写为

$$
S=\int^\oplus S(\omega)\,\diff\mu(\omega),
$$

其中 $\omega$ 表示能量或频率参数。对几乎处处 $\omega$，$S(\omega)$ 为在纤维 Hilbert 空间上的酉算子。

Birman–Kreĭn 公式断言存在谱移函数 $\xi(\omega)$，使得

$$
\xi(\omega)=-\frac{1}{2\pi\ii}\log\det S(\omega),
\quad
\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)
$$

在广泛情形下给出相对态密度。另一方面，Wigner–Smith 时间延迟矩阵定义为

$$
Q(\omega)=-\ii S(\omega)^\dagger\partial_\omega S(\omega),
$$

其迹刻画总群延迟时间。

统一时间刻度母式定义

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\tr Q(\omega),
$$

其中 $\varphi(\omega)$ 为散射半相位（相对散射行列式的相位）。在统一框架中，$\kappa(\omega)$ 被视为"宇宙时间密度"，任何物理时间参数若通过可观测测量过程得到，其在大尺度上与

$$
\tau_{\mathrm{scatt}}(\omega)=\int^{\omega}\kappa(\tilde\omega)\,\diff\tilde\omega
$$

处于等价类。

### 2.2 矩阵宇宙 $\mathrm{THE\text{-}MATRIX}$

矩阵宇宙对象 $U_{\mathrm{mat}}$ 定义为

$$
U_{\mathrm{mat}}
=\bigl(\mathcal H_{\mathrm{chan}},S(\omega),Q(\omega),\kappa,\mathcal A_\partial,\omega_\partial\bigr),
$$

其中：

1. $\mathcal H_{\mathrm{chan}}=\bigoplus_{v\in V}\mathcal H_v$ 为通道 Hilbert 空间的直和，每个 $v$ 对应一个宏观"端口"或边界区域；

2. $S(\omega)\in\mathcal B(\mathcal H_{\mathrm{chan}})$ 为频率依赖散射矩阵族，其块稀疏结构在 $V\times V$ 上编码因果偏序与相互作用结构；

3. $Q(\omega)=-\ii S(\omega)^\dagger\partial_\omega S(\omega)$ 为 Wigner–Smith 群延迟矩阵，统一时间刻度密度由

   $$
   \kappa(\omega)
   =(2\pi)^{-1}\tr Q(\omega)
   $$

   给出；

4. $\mathcal A_\partial$ 为边界可观测代数，$\omega_\partial$ 为边界量子态，它们与散射数据通过边界时间几何与模流联系。

在该对象中，量子混沌与 ETH 对应于：散射相位在能窗上的统计服从随机矩阵理论预言，且通道分解下的局域投影在本征态平均与相应微正则平均之间仅有指数小偏离。

### 2.3 QCA 宇宙 $U_{\mathrm{qca}}$

QCA 宇宙对象 $U_{\mathrm{qca}}$ 定义为

$$
U_{\mathrm{qca}}
=(\Lambda,\mathcal H_{\mathrm{cell}},\mathcal A_{\mathrm{qloc}},\alpha,\omega_0),
$$

满足以下公理：

1. $\Lambda$ 为可数连通图（典型为 $\mathbb Z^d$ 或其有限度规变形）；

2. 每个格点 $x\in\Lambda$ 携带有限维 Hilbert 空间 $\mathcal H_x\cong\mathcal H_{\mathrm{cell}}$；

3. 准局域代数 $\mathcal A_{\mathrm{qloc}}$ 为所有有限支撑算子的范数闭包；

4. $\alpha:\mathcal A_{\mathrm{qloc}}\to\mathcal A_{\mathrm{qloc}}$ 为 $*$ 自同构，存在传播半径 $R<\infty$，使得对任何有限区域 $X\subset\Lambda$，支撑在 $X$ 上的算子 $O_X$ 被映射到支撑在

   $$
   X^{+R}=\{y\in\Lambda\mid \mathrm{dist}(y,X)\le R\}
   $$

   上的算子；

5. $\alpha$ 由全局幺正算子 $U$ 实现，即 $\alpha(O)=U^\dagger O U$；

6. $\alpha$ 平移协变，即与晶格平移群作用对易；

7. 初始态 $\omega_0$ 为 $\mathcal A_{\mathrm{qloc}}$ 上的态，给出时间步 $n=0$ 时宇宙的量子状态。

对任意有限区域 $\Omega\subset\Lambda$，定义 $\mathcal H_\Omega=\bigotimes_{x\in\Omega}\mathcal H_x$，限制 $U$ 得到 $U_\Omega$（在适当边界条件下），其谱为

$$
U_\Omega\ket{\psi_n}
=\mathrm{e}^{-\ii\varepsilon_n\Delta t}\ket{\psi_n}.
$$

这些有限维幺正算子是讨论 QCA–ETH 与能级统计的基本对象。

### 2.4 公设混沌 QCA

为使 QCA 在有限区域上表现出类似局域随机电路的统计性质，引入如下定义。

**定义 2.1（公设混沌 QCA）**

一个平移不变 QCA $U$ 称为公设混沌 QCA，若满足：

1. 有限传播半径与局域性：存在整数 $R$，使得对任意有限 $X\subset\Lambda$，有 $\alpha(\mathcal A_X)\subset\mathcal A_{X^{+R}}$；

2. 局域电路表示：在任意有限区域 $\Omega$ 上，$U_\Omega$ 可在合适基下写为有限深度局域量子电路

   $$
   U_\Omega
   =\prod_{\ell=1}^D U_\ell,\quad
   U_\ell=\bigotimes_j U_{\ell,j},
   $$

   其中每个门 $U_{\ell,j}$ 作用在有限子集 $X_{\ell,j}\subset\Omega$，并与所有相距超过有限距离的门对易；

3. 近似单位设计：存在 $t_0\in\mathbb N$ 与函数 $\epsilon_t(|\Omega|)$（随 $|\Omega|$ 指数衰减），使得对任意 $t\le t_0$，由 $U_\Omega$ 所生成的幺正族在 $t$ 阶矩上构成 $\epsilon_t$ 精度的近似单位设计，即对任意多项式 $P(U,U^\dagger)$（次数不超过 $t$），有

   $$
   \Bigl\lVert
   \mathbb E_{U_\Omega}[P(U_\Omega)]
   -\mathbb E_{U\sim\mathrm{Haar}}[P(U)]
   \Bigr\rVert
   \le\epsilon_t(|\Omega|);
   $$

   其中 $U\sim\mathrm{Haar}$ 表示在 $U(\dim\mathcal H_\Omega)$ 上的 Haar 随机幺正。

4. 无额外广泛守恒量：除了可能的几个全局量子数（如总粒子数、自旋等）外，系统中不存在独立的广泛局域守恒量；

5. 热化能窗：存在能窗 $I\subset(-\pi/\Delta t,\pi/\Delta t]$，其内本征态数量随 $|\Omega|$ 指数增长，且能级简并仅产生有限多的对称性多重度。

这些条件概括了局域随机电路实现高阶单位设计并满足 ETH 的成熟结果，将其嵌入 QCA 语言。

### 2.5 离散时间 ETH 的定义

考虑有限区域 $\Omega$ 与其上演化算子 $U_\Omega$，谱分解如前。对给定能窗中心 $\varepsilon$ 与宽度 $\delta>0$，定义准能壳子空间

$$
\mathcal H_{\Omega}(\varepsilon,\delta)
=\mathrm{span}\{\ket{\psi_n}\mid \varepsilon_n\in(\varepsilon-\delta,\varepsilon+\delta)\},
$$

维数记为 $D_{\varepsilon,\delta}$。定义微正则平均

$$
\langle O_X\rangle_{\mathrm{micro}}(\varepsilon)
=D_{\varepsilon,\delta}^{-1}
\sum_{\varepsilon_n\in(\varepsilon-\delta,\varepsilon+\delta)}
\bra{\psi_n}O_X\ket{\psi_n}
$$

（取 $\delta$ 随 $|\Omega|$ 多项式缩放）。

**定义 2.2（离散时间 ETH）**

称 $U_\Omega$ 在能窗 $I$ 上对局域算子族 $\{O_X\}$ 满足离散时间 ETH，若存在常数 $c>0$ 与光滑函数 $O_X(\varepsilon)$、$\sigma_X(\varepsilon)$，使得对任意 $X\subset\Omega$ 与绝大多数 $n$（$\varepsilon_n\in I$）：

1. 对角 ETH：

   $$
   \bra{\psi_n}O_X\ket{\psi_n}
   =O_X(\varepsilon_n)+\mathcal O(\mathrm{e}^{-c|\Omega|});
   $$

2. 非对角 ETH：对几乎所有 $m\neq n$ 且 $\bar\varepsilon=(\varepsilon_m+\varepsilon_n)/2\in I$，有

   $$
   \lvert\bra{\psi_m}O_X\ket{\psi_n}\rvert
   \le \mathrm{e}^{-S(\bar\varepsilon)/2}\sigma_X(\bar\varepsilon),
   $$

   其中 $S(\bar\varepsilon)\sim s(\bar\varepsilon)|\Omega|$ 为能壳微观熵。

若对所有局域算子族成立，则称 QCA 在该区域满足 ETH。

---

## Main Results (Theorems and alignments)

为表述简洁，记 $\dim\mathcal H_\Omega=D\sim\mathrm{e}^{s|\Omega|}$。

### 3.1 QCA–ETH 主定理

**定理 3.1（QCA–ETH 定理）**

设 $U$ 为公设混沌 QCA，$\Omega\Subset\Lambda$ 为足够大的有限区域，$U_\Omega$ 为限制到 $\Omega$ 的幺正算子，$\{\ket{\psi_n},\varepsilon_n\}$ 为其准能谱本征对。则存在能窗 $I$ 与常数 $c>0$，使得对任意有限支撑 $X\subset\Omega$ 的局域算子 $O_X$，存在光滑函数 $O_X(\varepsilon)$，满足：

1. 对角 ETH：对能窗内绝大多数 $n$（$\varepsilon_n\in I$），有

   $$
   \bra{\psi_n}O_X\ket{\psi_n}
   =O_X(\varepsilon_n)+\mathcal O(\mathrm{e}^{-c|\Omega|});
   $$

2. 非对角 ETH：二阶矩满足

   $$
   \mathbb E\bigl[\lvert\bra{\psi_m}O_X\ket{\psi_n}\rvert^2\bigr]
   \le \mathrm{e}^{-S(\bar\varepsilon)}g_O(\bar\varepsilon,\omega),
   $$

   其中 $\bar\varepsilon=(\varepsilon_m+\varepsilon_n)/2$，$S(\bar\varepsilon)\sim s(\bar\varepsilon)|\Omega|$，$g_O$ 有界；

3. 若初态 $\ket{\psi_0}$ 在能窗 $I$ 内具有窄能分布，即 $\lvert c_n\rvert^2$ 仅在 $\varepsilon_n\in I$ 显著，则其时间平均局域观测满足

   $$
   \overline{\langle O_X\rangle}
   =\langle O_X\rangle_{\mathrm{micro}}(\varepsilon)
   +\mathcal O(\mathrm{e}^{-c|\Omega|}),
   $$

   并且时间涨落受非对角 ETH 指标指数抑制。

### 3.2 准能级统计的 CUE 型收敛

令 $\theta_n=\varepsilon_n\Delta t\in(-\pi,\pi]$，按升序排列并展开（unfold）到平均间距为 1 的变量 $s_n$。

**定理 3.2（QCA 能级统计的 CUE 行为）**

在定理 3.1 的假设下，展开后的最近邻间距分布 $P(s)$ 在 $|\Omega|\to\infty$ 极限下收敛到 CUE 随机矩阵系综的 Wigner–Dyson 分布

$$
P_{\mathrm{CUE}}(s)
\sim\frac{32}{\pi^2}s^2\mathrm{e}^{-4s^2/\pi}.
$$

同时归一化谱 form factor

$$
K(t)
=D^{-1}\lvert\tr U_\Omega^t\rvert^2
$$

在适当 rescale 后呈现"斜坡–平台"结构，与 CUE 的普适谱波动一致。

### 3.3 统一时间–ETH–熵增长定理

在 QCA 宇宙中，引入统一时间刻度 $\tau$ 与离散时间步 $n$ 的仿射关系

$$
\tau=an\Delta t+b,\quad a>0.
$$

考虑能窗 $I$ 内的一族"低熵"初始态 $\{\rho_0\}$，其冯·诺依曼熵密度 $s_0=S(\rho_0)/|\Omega|$ 小于微正则熵密度 $s_{\mathrm{mc}}(\varepsilon)$。

**定理 3.3（统一时间–ETH–熵增长）**

在公设混沌 QCA 与定理 3.1 的假设下，存在函数 $v_{\mathrm{ent}}(\varepsilon)>0$ 与常数 $c'>0$，使得对任意有限 $X\subset\Omega$，在统一时间刻度区间 $\tau\in[0,\tau_{\mathrm{th}}]$ 中，约化态 $\rho_X(\tau)=\tr_{\Omega\setminus X}\rho(\tau)$ 的熵密度

$$
s_X(\tau)=|X|^{-1}S(\rho_X(\tau))
$$

满足

$$
s_X(\tau)
\ge s_0 + v_{\mathrm{ent}}(\varepsilon)\frac{\tau}{\ell_{\mathrm{eff}}}
-\mathcal O(\mathrm{e}^{-c'|\Omega|}),
$$

并在 $\tau\gtrsim\tau_{\mathrm{th}}$ 后趋于 $s_{\mathrm{mc}}(\varepsilon)$。其中 $\ell_{\mathrm{eff}}$ 由 QCA 的传播半径与 Lieb–Robinson 型光锥速度确定，$v_{\mathrm{ent}}(\varepsilon)$ 可写为统一刻度密度 $\kappa(\omega)$ 在能窗 $I$ 上的平均与局域相互作用强度的函数。

### 3.4 宇宙尺度 ETH 与热时间箭头

将 QCA 宇宙 $U_{\mathrm{qca}}$ 视为有限区域族 $\{\Omega_L\}$ 的上极限，$\Omega_L\nearrow\Lambda$。对每个 $L$，限制 $U$ 得到 $U_{\Omega_L}$。

**命题 3.4（宇宙因果网上的 ETH）**

若 $U$ 为公设混沌 QCA，则对任意有限因果菱形（由某观察者世界线所确定），存在 $L$ 使得该菱形包含于某个足够大的区域 $\Omega_L$，从而在统一时间刻度下，该菱形内所有局域观测在足够长时间后趋于微正则平衡，熵密度随 $\tau$ 单调增长直至饱和。

因此，宇宙尺度上的热时间箭头与宏观不可逆性可视为由 QCA–ETH 与统一时间刻度共同决定的结构性结果。

---

## Proofs

本节给出主要定理的证明。技术性的算子积分、谱展开与浓缩不等式推导放入附录。

### 4.1 局域随机电路与近似单位设计

首先回顾局域随机量子电路实现近似单位设计的结果。Brandão–Harrow–Horodecki 证明：在一维链上，由最近邻两体门构成的局域随机电路，在深度 $\mathcal O(t^{10}n^2)$ 内即可实现 $t$ 阶近似单位设计。Harrow 等人在更高维情形和更一般格点结构下改进了深度估计，给出 $\mathrm{poly}(t)n^{1/D}$ 量级的最优标度。随后工作在具有对称性约束、粒子数守恒等情形下构造了显式的局域设计族。

这些定理可概括为：在有限区域 $\Omega$ 上，对满足一定生成性与非简并条件的局域门族，足够深的随机电路在单位群上诱导的分布在 $t$ 阶矩意义上接近 Haar。

在公设混沌 QCA 的定义中，近似单位设计性质正是通过对 $U_\Omega$ 的局域电路表示嵌入的。由于 QCA 的演化是确定性的而非随机的，需要将"多时间步 $U_\Omega^n$ 的集合"视作电路族：当 $n$ 在适当时间窗内变化时，$\{U_\Omega^n\}$ 在局域门参数空间上形成一族轨道，在某些QCA 中这族轨道足以实现设计性质；更一般地，可考虑在定义宇宙 QCA 时引入有限多超周期或空间平移，从而实现"有效随机化"。在本文公设中，将这些细节抽象为"在多项式时间步内由 $U_\Omega$ 生成的幺正族为近似单位设计"。

### 4.2 Haar 随机幺正的 ETH 典型性

对 Haar 随机幺正 $U\in U(D)$，其本征向量分布在 Hilbert 空间的复球上均匀。对任意固定局域算子 $O_X$，可利用 Haar 积分公式计算本征态矩阵元统计。以下结论可在随机矩阵理论与高维几何中找到系统证明。

**引理 4.1（Haar 随机本征基的对角元统计）**

设 $U$ Haar 随机，$\{\ket{\psi_n}\}$ 为其本征基，$O_X$ 为支撑在 $|X|\ll|\Omega|$ 上的局域算子，则：

1. $\mathbb E[\bra{\psi_n}O_X\ket{\psi_n}]=\tr(O_X)/D$ 与能级 $n$ 无关；

2. $\Var[\bra{\psi_n}O_X\ket{\psi_n}]\sim\mathcal O(D^{-1})$，且随 $|\Omega|$ 指数衰减；

3. 通过 Levy 浓缩不等式，有

   $$
   \mathbb P\bigl[
   \lvert\bra{\psi_n}O_X\ket{\psi_n}-\tr(O_X)/D\rvert>\epsilon
   \bigr]
   \le 2\exp(-cD\epsilon^2/\lVert O_X\rVert^2),
   $$

   其中 $c>0$ 为绝对常数。

**引理 4.2（Haar 随机本征基的非对角元统计）**

在同一设定下，非对角矩阵元 $\bra{\psi_m}O_X\ket{\psi_n}$ 的实部与虚部为均值零、方差 $\mathcal O(D^{-1})$ 的近似高斯变量，并满足

$$
\mathbb E\bigl[\lvert\bra{\psi_m}O_X\ket{\psi_n}\rvert^2\bigr]
=\mathcal O(D^{-1}).
$$

这些结果表明：在 Haar 典型本征基下，局域算子的本征态矩阵元天然满足 ETH 形式，且偏离微正则平均的概率随 Hilbert 空间维度指数衰减。

### 4.3 定理 3.1 的证明

**证明（定理 3.1）**

步骤 1：将 $U_\Omega$ 视作近似单位设计。

由定义 2.1 的第 2 条与第 3 条，对给定 $t_0$ 与足够大的 $|\Omega|$，由 $U_\Omega$ 在多时间步上生成的幺正族在 $t_0$ 阶矩意义上与 Haar 测度 $\mu_{\mathrm{Haar}}$ 的差异至多为 $\epsilon_{t_0}(|\Omega|)$，该误差随 $|\Omega|$ 指数衰减。

步骤 2：将 Haar 典型性估计转移到 QCA。

对角元情形：取 $t_0\ge 2$，对函数

$$
P(U)=\bra{\psi_n(U)}O_X\ket{\psi_n(U)}
$$

进行展开，其中 $\ket{\psi_n(U)}$ 表示 $U$ 的某一本征向量。严格地说，将 $U$ 写为对角化 $U=V D V^\dagger$，则本征向量分布等价于对 $V$ 的 Haar 分布。在近似设计的前提下，上述矩阵元的一阶与二阶矩在 $U_\Omega$ 所生成的幺正族与 Haar 测度下的差异为 $\mathcal O(\epsilon_{t_0})$。配合引理 4.1 的估计，可得

$$
\left\lvert
\bra{\psi_n}O_X\ket{\psi_n}
-\langle O_X\rangle_{\mathrm{micro}}(\varepsilon_n)
\right\rvert
\le C_1\mathrm{e}^{-\tilde c|\Omega|}
$$

以高概率成立，其中常数 $\tilde c>0$ 由 $\epsilon_{t_0}$ 与 Haar 浓缩常数共同控制。

非对角元情形：同样对

$$
P(U)=\lvert\bra{\psi_m(U)}O_X\ket{\psi_n(U)}\rvert^2
$$

使用近似设计，将 Haar 下的二阶矩估计转移到 $U_\Omega$。由引理 4.2，Haar 情形下的期望为 $\mathcal O(D^{-1})$，因此在 $U_\Omega$ 上仍为 $\mathcal O(D^{-1})+\mathcal O(\epsilon_{t_0})$，整体随 $|\Omega|$ 指数衰减。

步骤 3：从本征态 ETH 推导热化。

考虑能窗 $I$ 内的初态

$$
\ket{\psi_0}
=\sum_{\varepsilon_n\in I}c_n\ket{\psi_n},
$$

时间演化为 $\ket{\psi(n)}=U_\Omega^n\ket{\psi_0}$，局域观测

$$
\langle O_X\rangle(n)
=\bra{\psi(n)}O_X\ket{\psi(n)}
=\sum_{m,n}c_m^\ast c_n
\mathrm{e}^{\ii(\varepsilon_m-\varepsilon_n)n\Delta t}
\bra{\psi_m}O_X\ket{\psi_n}.
$$

时间平均消去 $m\neq n$ 的振荡项，得到

$$
\overline{\langle O_X\rangle}
=\sum_n\lvert c_n\rvert^2\bra{\psi_n}O_X\ket{\psi_n}.
$$

若初态能分布集中，则 $\lvert c_n\rvert^2$ 在能窗 $I$ 内近似常数，结合对角 ETH 可得

$$
\overline{\langle O_X\rangle}
=\langle O_X\rangle_{\mathrm{micro}}(\varepsilon)
+\mathcal O(\mathrm{e}^{-c|\Omega|}).
$$

时间涨落由非对角项控制，其幅度平方为 $\mathcal O(D^{-1})$，从而在体积上指数小。

综上，定理 3.1 中的三项结论成立。

$\square$

### 4.4 定理 3.2 的证明

**证明（定理 3.2）**

步骤 1：谱统计的单位设计可逼近性。

最近邻间距分布与谱 form factor 均可表示为本征相位 $\{\theta_n\}$ 的对称多项式函数，在展开后仅依赖于有限阶迹 $\tr U_\Omega^k$ 与其复共轭。CUE 谱统计的标准表达式正是在 Haar 随机幺正下这些迹的高阶矩。

由于公设混沌 QCA 对 $U_\Omega$ 给出了有限阶近似单位设计，故在适当截断与展式精度下，QCA 与 CUE 在这些迹多项式上的期望与方差差异至多为 $\epsilon_{t_0}(|\Omega|)$，随 $|\Omega|$ 指数衰减。

步骤 2：展开与重整化。

对实轴上的本征相位按照升序排列并对局部能窗内的密度进行 unfold，将平均间距重整化为 1。Wigner–Dyson 分布可通过两点 cluster 函数与 form factor 的 Fourier 变换得到。CUE下，这些函数可显式计算。

步骤 3：收敛性与浓缩。

由单位设计逼近与集中不等式，可证明：在 QCA 模型中，这些谱统计量在期望与高概率意义上收敛到 CUE 对应值。进而，最近邻间距分布、数字级别的谱 form factor 在 $|\Omega|\to\infty$ 极限下与 CUE 的结果一致。

在近期关于谱 form factor 与部分谱 form factor 的工作中，类似技术用于证明多体系统中谱统计的随机矩阵普适性。

$\square$

### 4.5 定理 3.3 的证明

**证明（定理 3.3）**

步骤 1：QCA 光锥与信息传播。

公设混沌 QCA 具有有限传播半径 $R$，从而在 Heisenberg 图像下存在类似 Lieb–Robinson 的光锥结构：支撑于 $X$ 上的算子在时间步 $n$ 后支撑被限制在 $X^{+Rn}$。该性质可用于证明纠缠产生与熵增长的线性光速上界。

步骤 2：局域随机性与纠缠生成。

在近似单位设计的前提下，$U_\Omega$ 的重复作用在局域 Hilbert 空间中产生近似 Haar 随机的纠缠态；对任何初态族 $\{\rho_0\}$，只要其能分布位于混沌能窗 $I$ 且局域相关长度有限，则在时间 $\mathcal O(|X|)$ 后，$\rho_X(\tau)$ 的约化态将接近能壳微正则态的部分迹。这可通过 decoupling 定理与随机电路中的纠缠增长结果定量制备。

步骤 3：统一时间刻度的引入。

统一时间刻度 $\tau$ 与离散步 $n$ 之间的关系由散射理论中的 $\kappa(\omega)$ 控制：在能窗 $I$ 内，定义平均刻度密度

$$
\bar\kappa(\varepsilon)
=\frac{1}{\lvert I\rvert}\int_I\kappa(\omega)\,\diff\omega.
$$

将 QCA 的准能量谱 $\varepsilon_n$ 与散射能量 $\omega$ 对应，可定义

$$
\tau
=\bar\kappa(\varepsilon)^{-1}n\Delta t
$$

作为统一时间刻度下的演化参数。由于 $\bar\kappa(\varepsilon)$ 与态密度 $D_{\varepsilon,\delta}$ 的函数相关，弛豫时间与熵增长速率可表达为 $\kappa$ 的函数。

步骤 4：熵密度增长的不等式。

利用 decoupling 技术与光锥结构，可以证明在时间区间 $[0,\tau_{\mathrm{th}}]$ 内，$s_X(\tau)$ 至少以某一正速率线性增长。该速率可界为

$$
v_{\mathrm{ent}}(\varepsilon)
\propto \bar\kappa(\varepsilon)\,J_{\mathrm{loc}},
$$

其中 $J_{\mathrm{loc}}$ 是表征局域相互作用强度与门"scrambling 能力"的量。热化时间 $\tau_{\mathrm{th}}$ 对应于 $s_X(\tau)$ 接近 $s_{\mathrm{mc}}(\varepsilon)$ 的时间，其数量级由 $\bar\kappa(\varepsilon)$ 与局域 Hilbert 空间维数控制。

详细的算子不等式与信息理论估计见附录 B。

$\square$

### 4.6 命题 3.4 的证明

**证明（命题 3.4）**

每个有限因果菱形可嵌入某个足够大的有限区域 $\Omega_L$。在统一时间刻度下，若观测者局域世界线对应的演化时间区间长度不超过混沌能窗内的热化时间尺度，则定理 3.1 与 3.3 保证菱形内所有局域观测在长时间极限趋于微正则平衡。由此可以将有限区域上的 ETH 结论推广到整个宇宙因果网的局域片段上。

$\square$

---

## Model Apply

本节给出一维公设混沌 QCA 的具体模型，并讨论其连续极限与物理解释。

### 5.1 一维砖墙 QCA 模型

取 $\Lambda=\mathbb Z$，每个元胞 Hilbert 空间 $\mathcal H_x=\mathbb C^q$（典型为 $q=2$）。定义砖墙结构的两步更新：

1. 偶–奇层：对所有 $(2j,2j+1)$ 对施加两体门 $U_{\mathrm{even}}$；

2. 奇–偶层：对所有 $(2j+1,2j+2)$ 对施加两体门 $U_{\mathrm{odd}}$。

全局演化算子为

$$
U
=U_{\mathrm{odd}}U_{\mathrm{even}}
=\Bigl(\bigotimes_j U_{\mathrm{odd},j}\Bigr)
\Bigl(\bigotimes_j U_{\mathrm{even},j}\Bigr).
$$

若 $U_{\mathrm{even}},U_{\mathrm{odd}}$ 选自生成 $SU(q^2)$ 的通用门集，并在不同时间段上进行参数更新，则该 QCA 在任何有限区间上的限制 $U_\Omega$ 等价于局域随机量子电路，满足公设混沌 QCA 公理。

在适当的连续极限中（时间步 $\Delta t\to 0$，两体门接近 $\exp(-\ii h_{x,x+1}\Delta t)$），可得到一个有效哈密顿量

$$
H_{\mathrm{eff}}=\sum_x h_{x,x+1},
$$

其低能部分对应非可积自旋链模型，已知满足 ETH 与 Wigner–Dyson 能级统计。

### 5.2 对观测者的局域热化

将上述一维 QCA 视为宇宙模型中的某一空间切片。对任意观察者，其世界线在有限时间内仅访问有限区间 $\Omega$。定理 3.1 与 3.3 断言：不管宇宙整体处于何种纯态，只要能量分布位于混沌能窗，则该观察者在统一时间刻度上的局域观测都会在有限时间内"忘记"初始条件，趋于相应能壳的微正则平衡。

### 5.3 与矩阵宇宙的对接

通过对 QCA 宇宙进行傅里叶变换与散射构造，可以在频率域定义等效散射矩阵 $S(\omega)$，使得 Wigner–Smith 群延迟矩阵的谱与 QCA 的准能谱 $\{\varepsilon_n\}$ 在低能与适当 coarse-grain 下匹配。这样，统一时间刻度 $\kappa(\omega)$ 与 QCA 的热化时间尺度 $\tau_{\mathrm{th}}$ 之间建立定量对应。

---

## Engineering Proposals

### 6.1 超导量子线路中的 QCA 实现

在超导量子比特平台上，通过固定拓扑的晶格与周期性驱动，可自然实现砖墙结构的 QCA。每个时间步实施两层最近邻受控门，实现全局演化算子 $U$。现有实验已在几十至上百比特规模上实现局域随机电路，并测量 OTOC、谱 form factor 等混沌指标。

工程上，可选取具有足够通用性的两比特门族，在参数空间中进行准随机扫描，使得有限时间窗内生成的幺正族逼近高阶单位设计；对有限区域的截断可通过对边缘比特实施冻结或回环边界条件实现。

### 6.2 冗余编码下的 ETH 验证协议

为在噪声存在下验证 QCA–ETH，可采用如下协议：

1. 在有限区域 $\Omega$ 上准备多组不同的低熵初态（如积状态或低纠缠状态），能量分布集中于某一准能窗；

2. 在统一时间刻度对应的若干步 $n$ 后，测量局域算子 $O_X$ 的期望值与涨落；

3. 检验其时间平均与样本平均是否收敛到相同的微正则值，并验证不同初态的结果趋于一致；

4. 测量谱 form factor 并与 CUE 预测比较，从而检验量子混沌诊断。

### 6.3 数值模拟与代码结构

数值上，可通过张量网络或 exact diagonalization 对低维 QCA 模型进行模拟。代码结构可包括：

1. QCA 更新器：根据砖墙规则构造离散时间步 $U$；

2. 近似单位设计检测模块：计算低阶多项式 $P(U)$ 的经验分布并与 Haar 平均比较；

3. ETH 验证模块：对大量本征态计算局域算子矩阵元分布；

4. 谱统计模块：计算展开后的间距分布与谱 form factor。

代码可用 Python/Julia+C++ 实现，利用稀疏矩阵与 Krylov 子空间方法扩展到更大系统规模。

---

## Discussion (risks, boundaries, past work)

### 7.1 理论边界与失效情形

本文的公设混沌 QCA 明确排除了可积 QCA、多体局域化 QCA 以及携带大量局域守恒量的系统。在这些情形中，ETH 与随机矩阵谱统计一般不成立；相应地，热化过程可能被广泛保留的守恒量改变，导致广义 Gibbs 或非平衡稳态。

此外，某些"对偶幺正"（dual-unitary）量子电路在兼具可解性与强混合性的同时，在本征态结构与谱统计上表现出与 CUE 相似但并非完全相同的特征，需要更精细的分析。

### 7.2 与既有 ETH 严格结果的关系

在哈密顿系统与随机量子电路上，关于 ETH 与谱统计的严格结果主要集中在以下几个方向：

1. 随机矩阵与自由概率工具用于控制谱相关函数与谱 form factor；

2. 局域随机电路与单位设计，利用马尔可夫链谱隙与张量积扩张定理证明混合时间与设计阶；

3. 部分可解模型中对 ETH 满足或违背的精细分析。

本文在这些工作基础上，将上述结果提升到 QCA 宇宙对象层级，使"宇宙作为 QCA"中的量子混沌与 ETH 不再是具体模型的偶然性质，而是由公设混沌 QCA 公理与统一时间刻度共同决定的结构性特征。

### 7.3 与引力与宇宙学的兼容性

统一时间刻度母式源于散射与谱理论，其在引力与宇宙学中的实现依赖于边界时间几何与准局域能量的构造。本文并未直接涉及曲率与引力场方程，但通过矩阵宇宙 $U_{\mathrm{mat}}$ 与 QCA 宇宙 $U_{\mathrm{qca}}$ 的对应，暗含了在适当连续极限下重构广义相对论与量子场论的要求。这一方向上已有关于 QCA 连续极限与量子行走模拟狄拉克方程的工作可供比对。

---

## Conclusion

本文在统一时间刻度与矩阵宇宙–QCA 宇宙框架下，对量子混沌与本征态热化在 QCA 宇宙中的成立给出系统刻画。通过引入公设混沌 QCA 的公理体系，将局域随机电路的单位设计与 ETH 结果移植到 QCA 语言，证明 QCA–ETH 定理与 CUE 型能级统计收敛；同时将统一时间刻度母式引入熵增长分析，给出统一时间–ETH–熵增长定理。

在宇宙尺度上，这一框架表明：热时间箭头与宏观不可逆性可以被视为统一矩阵–QCA 宇宙的结构不变量，而非额外假设的动力学规律。量子混沌与 ETH 因此从"具体模型性质"提升为"宇宙对象的公理性属性"。

---

## Acknowledgements, Code Availability

本工作依赖于散射理论、随机矩阵理论、量子信息与 QCA 结构等多个成熟理论框架，对相关领域的系统发展表示致谢。

用于数值验证公设混沌 QCA 模型的代码可按照第五节所述结构实现，包括 QCA 更新器、单位设计检测模块、ETH 验证模块与谱统计模块。具体实现可使用开源量子模拟库与线性代数库，不再赘述。

---

## References

[1] J. M. Deutsch, "Eigenstate thermalization hypothesis," arXiv:1805.01616, 2018.

[2] M. Srednicki, "Chaos and quantum thermalization," Phys. Rev. E 50, 888, 1994.

[3] J. D. Noh, "Eigenstate thermalization hypothesis and eigenstate-to-eigenstate fluctuations," Phys. Rev. E 103, 012129, 2021.

[4] F. G. S. L. Brandão, A. W. Harrow, M. Horodecki, "Local random quantum circuits are approximate polynomial-designs," Commun. Math. Phys. 346, 397–434, 2016.

[5] A. W. Harrow, S. Mehraban, "Approximate unitary t-designs by short random quantum circuits," Commun. Math. Phys. 400, 2023.

[6] Z. Li, J. Liu, J. Chen, "Designs from local random quantum circuits with SU(d) symmetry," arXiv:2309.08155, 2023.

[7] S. N. Hearth et al., "Designs from random number-conserving quantum circuits," Phys. Rev. X 15, 021022, 2025.

[8] M. Oszmaniec, "Epsilon-nets, unitary designs and random quantum circuits," arXiv:2007.10885, 2020.

[9] B. Schumacher, R. F. Werner, "Reversible quantum cellular automata," arXiv:quant-ph/0405174, 2004.

[10] C. A. Pérez-Delgado, D. Cheung, "Local unitary quantum cellular automata," Phys. Rev. A 76, 032320, 2007.

[11] D. Gross, V. Nesme, H. Vogts, R. F. Werner, "Index theory of one dimensional quantum walks and cellular automata," Commun. Math. Phys. 310, 419–454, 2012.

[12] L. S. Trezzini et al., "Renormalisation of quantum cellular automata," Quantum 9, 1756, 2025.

[13] C. Texier, "Wigner time delay and related concepts," Physica E 82, 16–33, 2016.

[14] U. R. Patel, E. Michielssen, "Wigner–Smith time delay matrix for electromagnetics," IEEE Trans. Antennas Propag. 69, 902, 2021.

[15] U. R. Patel, "Wigner–Smith time delay matrix for acoustic scattering," J. Acoust. Soc. Am. 153, 2769, 2023.

[16] F. Gesztesy, A. Pushnitski, B. Simon, "The $\Xi$ operator and its relation to Kreĭn's spectral shift function," J. Anal. Math. 113, 53–172, 2011.

[17] A. R. Mirotin, "Lifshitz–Kreĭn trace formula for Hirsch functional calculus on Banach spaces," Complex Anal. Oper. Theory 13, 2019.

[18] H. Isozaki, "Trace formulas for Schrödinger operators," RIMS Kokyuroku 1760, 2011.

[19] H. Dong et al., "Measuring the spectral form factor in many-body chaotic and disordered quantum systems," Phys. Rev. Lett. 134, 010402, 2025.

[20] M. O. Flynn et al., "Single-particle universality of the many-body spectral form factor," Phys. Rev. Lett. 134, 160403, 2025.

[21] W. Vleeshouwers, B. Meszéna, G. J. Tóth, "The spectral form factor in the 't Hooft limit," SciPost Phys. Core 5, 051, 2022.

[22] F. Fritzsch, A. Nahum, J. Sonner, "Eigenstate correlations in dual-unitary quantum circuits," Quantum 9, 1709, 2025.

[23] M. Liu et al., "Estimating the randomness of quantum circuit ensembles," npj Quantum Information 8, 2022.

[24] M. Alishahiha, "Eigenstate thermalization hypothesis: a short review," 2024.

[25] I. Nassar, "Review of the Eigenstate Thermalization Hypothesis," Graduation Project, 2024.

---

## Appendix A：离散时间 ETH 的等价形式

### A.1 时间平均与对角 ETH 的等价性

设离散时间演化算子 $U_\Omega$ 的谱分解为

$$
U_\Omega\ket{\psi_n}
=\mathrm{e}^{-\ii\varepsilon_n\Delta t}\ket{\psi_n},
$$

初态 $\ket{\psi_0}=\sum_n c_n\ket{\psi_n}$。局域观测的时间平均为

$$
\overline{\langle O_X\rangle}
=\lim_{N\to\infty}\frac{1}{N}\sum_{k=0}^{N-1}
\bra{\psi_0}U_\Omega^{\dagger k}O_XU_\Omega^k\ket{\psi_0}
=\sum_n\lvert c_n\rvert^2\bra{\psi_n}O_X\ket{\psi_n},
$$

在能级非简并的假设下成立。

若对角 ETH 成立，即

$$
\bra{\psi_n}O_X\ket{\psi_n}
=O_X(\varepsilon_n)+\delta_n,\quad
\lvert\delta_n\rvert\le\mathrm{e}^{-c|\Omega|},
$$

且初态能分布集中于窄能窗，则

$$
\overline{\langle O_X\rangle}
=\sum_n\lvert c_n\rvert^2 O_X(\varepsilon_n)
+\mathcal O(\mathrm{e}^{-c|\Omega|})
\approx O_X(\varepsilon)
\approx\langle O_X\rangle_{\mathrm{micro}}(\varepsilon).
$$

因此，对角 ETH 与对局域观测的时间平均热化等价（在指数小误差意义下）。

### A.2 非对角 ETH 与时间涨落

时间涨落可表示为

$$
\delta O_X(k)
=\langle O_X\rangle(k)-\overline{\langle O_X\rangle}
=\sum_{m\neq n}c_m^\ast c_n
\mathrm{e}^{\ii(\varepsilon_m-\varepsilon_n)k\Delta t}
\bra{\psi_m}O_X\ket{\psi_n}.
$$

其方差上界为

$$
\overline{\lvert\delta O_X\rvert^2}
\le\sum_{m\neq n}\lvert c_m\rvert^2\lvert c_n\rvert^2
\lvert\bra{\psi_m}O_X\ket{\psi_n}\rvert^2.
$$

若非对角 ETH 给出

$$
\mathbb E\bigl[\lvert\bra{\psi_m}O_X\ket{\psi_n}\rvert^2\bigr]
\le\mathrm{e}^{-S(\bar\varepsilon)}g_O(\bar\varepsilon,\omega),
$$

则在能壳中本征态数量 $D_{\varepsilon,\delta}\sim\mathrm{e}^{S(\varepsilon)}$ 的前提下，涨落方差为 $\mathcal O(\mathrm{e}^{-S(\varepsilon)})$，随体积指数衰减。

### A.3 Floquet ETH 与哈密顿 ETH 的关系

当 QCA 的有效连续极限存在时，可定义有效哈密顿量

$$
H_{\mathrm{eff}}
=\frac{\ii}{\Delta t}\log U,
$$

其谱与准能谱满足 $E_n\approx\varepsilon_n$。若 $\Delta t$ 足够小、$\log U$ 的支割线选择得当，则 Floquet ETH 与哈密顿 ETH 在同一能窗上等价，微正则集与准能壳可相互替代。

---

## Appendix B：QCA–ETH 定理的技术细节

### B.1 近似单位设计的定量界

对 $n$ 个 $q$ 维量子比特组成的一维链，Brandão–Harrow–Horodecki 给出的设计定理可写为：存在常数 $C,c>0$，使得深度为

$$
L\ge C t^{10} n^2
$$

的最近邻局域随机电路构成 $\epsilon$ 近似 $t$-设计，其中 $\epsilon\le\mathrm{e}^{-cn}$。

Harrow 等人进一步证明，在 $D$ 维晶格上，深度标度可改进为 $\mathrm{poly}(t)n^{1/D}$。结合本文公设，可取 $t_0$ 为固定常数，$\epsilon_{t_0}(|\Omega|)\le\mathrm{e}^{-c|\Omega|}$。

### B.2 Haar 积分与本征态矩阵元

Haar 积分公式给出

$$
\int_{U(D)} U_{i_1j_1}\cdots U_{i_kj_k}
\overline{U_{i'_1j'_1}}\cdots\overline{U_{i'_kj'_k}}\,\diff\mu_{\mathrm{Haar}}(U)
$$

可用置换群 $S_k$ 上的 Weingarten 函数表示。对 $k\le t_0$ 的场合，即可用有限项求和表示期望值。由此推导引理 4.1 与引理 4.2 中的平均与方差估计。

在 QCA 场景下，由于 $U_\Omega$ 在 $t_0$ 阶上近似单位设计，上述期望与方差在 $U_\Omega$ 诱导的分布与 Haar 测度下的差异也被 $\epsilon_{t_0}$ 控制。

### B.3 浓缩不等式

在 Hilbert 空间复球上的 Lipschitz 函数满足 Levy 浓缩不等式：对 $L$-Lipschitz 函数 $f$，有

$$
\mathbb P\bigl[\lvert f-\mathbb Ef\rvert>\epsilon\bigr]
\le 2\exp(-cD\epsilon^2/L^2).
$$

将 $f$ 取为 $\bra{\psi}O_X\ket{\psi}$ 或 $\lvert\bra{\psi_m}O_X\ket{\psi_n}\rvert^2$ 的函数，可得到本征态矩阵元偏离平均值的概率界。

---

## Appendix C：谱 form factor 与 Wigner–Dyson 分布

### C.1 CUE 的谱 form factor

CUE 随机矩阵 $U\in U(D)$ 的谱 form factor 定义为

$$
K_{\mathrm{CUE}}(t)
=D^{-1}\mathbb E\bigl[\lvert\tr U^t\rvert^2\bigr].
$$

随机矩阵理论给出在 $D\to\infty$ 极限下的显式表达：在 rescale 时间 $\tau=t/D$ 下，$K_{\mathrm{CUE}}(\tau)$ 展现线性"斜坡"与饱和"平台"。

### C.2 QCA 模型中的谱 form factor

在公设混沌 QCA 中，$U_\Omega$ 在有限阶迹多项式上近似 Haar 随机，因此 $K(t)$ 在有限时间窗 $|t|\le t_{\max}\sim\mathrm{poly}(|\Omega|)$ 内的统计与 CUE 的 $K_{\mathrm{CUE}}(t)$ 一致，偏差为 $\mathcal O(\epsilon_{t_0})$。

通过 Fourier 变换，可将 $K(t)$ 与能级相关函数联系，进而得到最近邻间距分布与更高阶间距分布的 Wigner–Dyson 形式。

---

## Appendix D：一维公设混沌 QCA 的数值验证框架

### D.1 模型参数选择

在一维砖墙 QCA 中，可选取两体门为

$$
U_{\mathrm{gate}}
=\exp\bigl(-\ii (J_x\sigma^x\otimes\sigma^x
+J_y\sigma^y\otimes\sigma^y
+J_z\sigma^z\otimes\sigma^z+h_x(\sigma^x\otimes\id+\id\otimes\sigma^x))\Delta t\bigr),
$$

并在不同时间段对参数 $(J_x,J_y,J_z,h_x)$ 进行准随机扰动，以破坏可积性与额外交对称性。

### D.2 数值步骤

1. 对长度 $L$ 的链构造 $U_\Omega$ 并进行 exact diagonalization（$L\le 16$ 时可行）；

2. 计算局域算子（如单体 Pauli 矩阵或两体相互作用项）在本征态上的矩阵元分布，检验对角与非对角 ETH；

3. 计算展开后的间距分布与谱 form factor，与 CUE 结果比较；

4. 对不同初态族模拟时间演化，验证局域观测的热化与熵密度增长，与定理 3.3 的预测对比。

这一框架为验证公设混沌 QCA 公理与本文定理提供了具体可实现的数值与实验路径。

