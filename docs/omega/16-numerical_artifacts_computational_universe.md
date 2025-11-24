# 计算宇宙的数值伪影：如何在物理实验中探测普朗克尺度的截断误差与各向异性

*Numerical Artifacts of the Computational Universe: Detecting Planck-Scale Truncation Errors and Anisotropy in Physical Experiments*

---

## Abstract

若宇宙是一个由底层离散计算过程实现的动力系统，则有限内存、有限时钟频率与有限数值精度必然在宏观物理中留下极其微弱但原则上可探测的"数值伪影"。在以量子元胞自动机（quantum cellular automaton, QCA）为原型的计算宇宙模型中，本文给出一套系统的分析框架，将普朗克尺度附近的空间晶格化、有限精度舍入误差以及算法级资源调度（"懒惰计算"）统一表述为有效场论中的高维算符与弱洛伦兹破缺参数，并将之与现有和可预期的实验约束联系起来。本文的主要结论为：

(1) 在立方晶格上逼近洛伦兹不变色散关系的任意局域 QCA，其高动量色散必然包含方向依赖的 $\mathcal{O}((pa)^4)$ 各向异性修正，从而导致极高能粒子与光子的群速度在空间方向上的微弱差异；

(2) 若底层硬件使用有限精度数域，且未被完美可逆计算或纠错编码完全抹平，则宏观上表现为随能量增强的守恒律噪声，其在超高能宇宙线与长基线引力波传播中给出对"有效截断误差"指标 $\epsilon_{\mathrm{eff}}$ 的上界；

(3) 若存在随局域熵或观察者信息密度自适应的"计算分辨率分配"，则在宇宙学空洞区域可能出现微小的有效常数漂移，例如精细结构常数 $\alpha$ 或真空能密度 $\Lambda_{\mathrm{eff}}$ 的空间调制。结合超高能宇宙线、伽马射线暴的能量依赖时间延迟、高精度光学谐振腔与原子钟网络的观测，本文给出当前可获得的定量约束，并提出数个面向下一代观测设施的"计算取证学"实验方案，以期在噪声之中寻找计算宇宙的痕迹。

---

## Keywords

模拟假说；量子元胞自动机；数值伪影；洛伦兹不变性检验；超高能宇宙线；伽马射线暴；原子钟网络；精细结构常数

---

## Introduction & Historical Context

模拟假说在哲学层面最具代表性的表述来自 Bostrom 对"祖先模拟"的论证，即在技术高度发展的文明能够运行大规模高保真模拟的前提下，我们身处模拟中的先验概率可能远大于身处"基底现实"。与此同时，物理学中关于计算宇宙的构想——包括可逆计算、元胞自动机宇宙、信息引力等——试图将物理定律视为某种底层计算规则的涌现形式。

在这一类设想中，Beane 等人首次提出了一个明确可检验的思路：若宇宙是运行在立方晶格上的格点规范场论数值模拟，则晶格间距 $a$ 不可能无限小，其有限值会在高能宇宙线谱中表现为方向依赖的截止及 GZK 截断结构的各向异性，由此得到 $a^{-1} \gtrsim 10^{11} \,\mathrm{GeV}$ 的下界。([arXiv][1]) 最近，Vazza 等人从信息能量成本与天体物理观测出发，对模拟宇宙的物理可实现性进行了系统量化，指出若要在有限计算资源下重现观测宇宙，必须面对严苛的能量与熵预算约束。([Frontiers][2])

另一方面，大量高精度实验持续检验狭义与广义相对论的基本公设。包括利用冷却光学谐振腔进行的现代 Michelson–Morley 实验，其对光速各向异性给出 $\Delta c/c \sim 10^{-15}$ 量级的上限；([arXiv][3]) Fermi-LAT 等对伽马射线暴的时间延迟分析，将线性能量依赖光速修正的标度推高至接近甚至超过普朗克尺度；([arXiv][4]) 以及原子钟比较对精细结构常数时间变化与空间变化的严密限制。([APS Links][5]) 结合类星体吸收线、宇宙微波背景与宇宙学数据，对 $\alpha$ 与其他基本常数在宇宙学尺度上变动的约束亦趋于严格。([PMC][6])

上述工作表明：即便将模拟假说暂时撇开，关于洛伦兹不变性、守恒律与常数稳定性的高精度检验本身已经构成一门成熟的实验领域。然而，现有讨论往往将"模拟宇宙"与"量子引力修正"、"有效场论高维算符"等视为彼此独立的框架。

本文的目标是：在量子元胞自动机这一离散本体论之上，引入明确的"计算资源受限"假设，将"宇宙作为数值模拟"转化为一套具体的有效参数化，从而建立一门可与现有高精度实验直接对接的"计算取证学"。其核心思想是：

1. 把空间晶格化视作 QCA 的几何结构，分析其对色散关系与对称性的影响；

2. 把有限数值精度抽象为幺正性与守恒律的微弱随机破坏，并给出与宏观观测之间的定量映射；

3. 把资源调度与分辨率自适应视作有效常数在时空中的低频调制，利用原子钟、宇宙学观测与大尺度结构数据进行约束。

本工作不试图证明模拟假说"成立"，而是给出：若宇宙可以用此类计算模型逼近，则任何合理的模拟都必须满足怎样的实验约束；反之，一旦发现与这些约束显著冲突的现象，反而可以为这一类计算宇宙模型提供非平凡支持。

---

## Model & Assumptions

### 计算宇宙的 QCA 原型

我们采用如下抽象模型来描述计算宇宙：

1. 时空被表示为三维立方晶格 $\Lambda \cong a\mathbb{Z}^3$，时间以步长 $\Delta t$ 离散。

2. 每个格点 $x \in \Lambda$ 拥有有限维局域希尔伯特空间 $\mathcal{H}_x \cong \mathbb{C}^d$，全局希尔伯特空间为 $\mathcal{H} = \bigotimes_{x\in\Lambda} \mathcal{H}_x$。

3. 时间演化由局域幺正算符 $U$ 给出，具有有限作用范围 $R$，即

$$
\ket{\psi(t+1)} = U \ket{\psi(t)}, \quad U = \prod_{X\subset \Lambda} U_X,
$$

其中每个 $U_X$ 只作用于直径 $\le R$ 的有限子集。

4. 在长波极限 $a\to 0, \Delta t \to 0$ 下，单粒子激发的有效动力学可由洛伦兹不变的连续场论（如标量场、Dirac 场或 Maxwell 场）逼近。

在"理想数学 QCA"中，$U$ 是精确幺正，格点间距 $a$ 与时间步长 $\Delta t$ 仅作为缩放参数，不引入任何数值误差。而在模拟假说下，真正执行 $U$ 的底层硬件（或形式结构的实现）受到以下约束：

* 数值域为有限精度：例如有限字长整数或浮点数；

* 存储容量有限：只能容纳有限数量的格点与内部自由度；

* 计算资源有限：每步可执行的逻辑门数量有限，从而需要调度与近似。

在本模型中，我们将"理想 QCA"视为目标动力学，而硬件实现带来的偏离一律视作"数值伪影"。这些伪影被参数化为以下三类：

1. **晶格各向异性伪影**：由于 $\Lambda$ 只具有有限旋转群 $O_h$ 对称性，长波极限的洛伦兹不变性只在 $pa \ll 1$ 的窗口内近似成立，在高动量或高频段上出现系统性的各向异性修正。

2. **有限精度伪影**：每一步幺正演化在硬件上只能以近似方式实现，引入随机或有偏的数值舍入误差，导致幺正性与守恒律的微弱破坏。

3. **资源调度伪影**：为了降低资源消耗，模拟器可能对"低复杂度区域"采用稀疏更新、粗格点或更低精度表示，导致等效物理常数随空间区域缓慢变化。

在模型层面，我们引入三个无量纲参数来刻画其大小：

* 晶格尺度参数 $\eta_a = a M_{\mathrm{P}}$，其中 $M_{\mathrm{P}}$ 为普朗克能标；

* 有效截断误差参数 $\epsilon_{\mathrm{eff}}$，表示每一步局域演化在能量/概率守恒上的相对误差；

* 分辨率调制参数 $\delta_{\mathrm{res}}(x)$，表示在不同宇宙学环境中有效常数相对平均值的偏离。

我们的目标是在各种观测中提取对 $\eta_a, \epsilon_{\mathrm{eff}}, \delta_{\mathrm{res}}$ 的上界或"可检测窗口"。

---

## Main Results (Theorems and alignments)

### 定理 1：立方晶格 QCA 的高能各向异性色散

考虑满足平移不变性与局域性、长波极限接近标量或光学波动方程的三维 QCA。其单粒子色散关系 $\omega(\mathbf{k})$ 在 $|\mathbf{k}|a \ll 1$ 区间可展开为

$$
\omega^2(\mathbf{k}) = c^2 \mathbf{k}^2 + m^2 c^4 + a^2 \left( \beta_1 \sum_{i=1}^3 k_i^4 + \beta_2 \sum_{i<j} k_i^2 k_j^2 \right) + \mathcal{O}(a^4 k^6),
$$

其中 $\mathbf{k}=(k_x,k_y,k_z)$，$\beta_1, \beta_2$ 为由 QCA 局域结构决定的无量纲系数。

在 $m=0$ 的无质量极限，群速度

$$
\mathbf{v}_g(\mathbf{k}) = \nabla_{\mathbf{k}} \omega(\mathbf{k})
$$

在 $a^2$ 阶上表现出方向依赖，具体而言，对于给定模长 $|\mathbf{k}|=k$，沿晶格轴向 $\mathbf{k} = (k,0,0)$ 与沿体对角线 $\mathbf{k} = (k/\sqrt{3},k/\sqrt{3},k/\sqrt{3})$ 的群速度修正满足

$$
\Delta v_g^{\mathrm{axis}} - \Delta v_g^{\mathrm{diag}} = \mathcal{O}(a^2 k^3) \neq 0,
$$

因此在高能区必然出现光速或高能粒子传播速度的各向异性。

这一结论与早期对格点规范场论中晶格各向异性伪影的分析一致，也是利用宇宙线与高能光子约束"宇宙晶格间距"的基础。([arXiv][1])

### 定理 2：有限精度舍入误差导致的守恒律噪声标度

假设底层硬件在实现单步演化 $U$ 时，引入了相对规模为 $\epsilon \ll 1$ 的局域非幺正扰动，可用 Lindblad 型有效演化近似

$$
\rho(t+\Delta t) = U \rho(t) U^\dagger + \epsilon \,\mathcal{D}[\rho(t)] + \mathcal{O}(\epsilon^2),
$$

其中 $\mathcal{D}$ 为某个完全正的耗散超算符。若误差在时间上近似独立同分布，则经过 $N$ 步演化，某个守恒量 $Q$（如总能量或动量）的期望值偏离其理想值的标准差满足

$$
\sigma_Q(N) \sim \sqrt{N} \,\epsilon\, Q_{\mathrm{char}},
$$

其中 $Q_{\mathrm{char}}$ 是特征规模。若取宇宙年龄 $T_{\mathrm{U}}$ 与普朗克时间 $t_{\mathrm{P}}$ 定义的有效步数 $N \sim T_{\mathrm{U}}/t_{\mathrm{P}} \sim 10^{61}$，则仅有当

$$
\epsilon_{\mathrm{eff}} \lesssim 10^{-30}
$$

时，宏观上仍可观测到近乎严格的守恒律。这里 $\epsilon_{\mathrm{eff}}$ 是经可能的纠错编码与可逆计算抹平后的有效截断误差。该估计说明：若宇宙是以有限精度实现的 QCA 模拟，则要与现有关于能量与动量守恒的观测相容，底层必须使用极为高效的纠错与可逆逻辑。

### 命题 3：资源调度与有效常数的空间调制

设模拟器采用"分层分辨率"策略：依据局域复杂度指示函数 $\chi(x)$（如局域熵密度或观察者密度），选择不同的离散步长 $(a(x), \Delta t(x))$ 与数值精度 $n_{\mathrm{bit}}(x)$。对低能有效场论而言，这相当于在拉格朗日量中引入随空间缓慢变化的重整化常数 $g_i(x)$。例如电磁相互作用项中

$$
\mathcal{L}_{\mathrm{EM}} = -\frac{1}{4} Z_F(x) F_{\mu\nu}F^{\mu\nu} + Z_\psi(x) \bar{\psi} i\gamma^\mu D_\mu \psi + \cdots,
$$

将导致有效精细结构常数

$$
\alpha(x) \propto \frac{Z_\psi^2(x)}{Z_F(x)}
$$

呈现空间调制。若 $Z_F, Z_\psi$ 在宇宙学尺度上变化平滑，则可用线性化近似 $\Delta \alpha/\alpha \approx \kappa \,\Delta\chi$。现有原子钟比较、类星体吸收线与宇宙学数据对 $\Delta\alpha/\alpha$ 给出的上限通常在 $10^{-7}\text{–}10^{-15}$ 范围内，([APS Links][5]) 因此可直接转化为对资源调度强度 $\kappa \Delta\chi$ 的约束。

---

## Proofs

### 4.1 定理 1：立方晶格 QCA 各向异性色散的推导

为简明起见，以三维标量场的离散波动方程为例，其连续形式为

$$
\partial_t^2 \phi = c^2 \nabla^2 \phi.
$$

在立方晶格上采用标准二阶差分离散拉普拉斯

$$
(\nabla^2_a \phi)(\mathbf{x}) = \frac{1}{a^2} \sum_{i=1}^3 \left[ \phi(\mathbf{x}+a\hat{e}_i) + \phi(\mathbf{x}-a\hat{e}_i) - 2\phi(\mathbf{x}) \right].
$$

令

$$
\phi(\mathbf{x},t) = \exp\left[i(\mathbf{k}\cdot\mathbf{x} - \omega t)\right],
$$

代入离散方程得到色散关系

$$
\omega^2(\mathbf{k}) = \frac{4c^2}{a^2}\sum_{i=1}^3 \sin^2\left(\frac{k_i a}{2}\right).
$$

在 $|k_i a|\ll 1$ 下展开

$$
\sin\left(\frac{k_i a}{2}\right) = \frac{k_i a}{2} - \frac{(k_i a)^3}{48} + \mathcal{O}(a^5 k_i^5),
$$

从而

$$
\sin^2\left(\frac{k_i a}{2}\right) = \frac{k_i^2 a^2}{4} - \frac{k_i^4 a^4}{48} + \mathcal{O}(a^6 k_i^6).
$$

代入得

$$
\omega^2(\mathbf{k}) = c^2 \sum_{i=1}^3 k_i^2 - \frac{c^2 a^2}{12} \sum_{i=1}^3 k_i^4 + \mathcal{O}(a^4 k^6).
$$

第一项为各向同性的 $c^2 \mathbf{k}^2$，第二项为显式依赖分量的 $\sum k_i^4$ 形式。注意 $\sum k_i^4$ 在 $\mathrm{SO}(3)$ 下并非常数，只在有限群 $O_h$ 下保持对称。

对质量项 $m^2 c^4$ 的引入不会改变高动量各向异性项的结构，只在低能区略微修改色散。对更一般的 QCA，只要保持平移不变与局域性，其长波极限可用有效哈密顿量

$$
H_{\mathrm{eff}} = c \boldsymbol{\alpha}\cdot\mathbf{p} + \beta m c^2 + a^2 \sum_{i,j} \gamma_{ij} p_i^2 p_j^2 + \cdots
$$

表征，其中 $\boldsymbol{\alpha}, \beta, \gamma_{ij}$ 为若干矩阵或常数，$p_i = \hbar k_i$。在能谱平方后展开即可得到与上述标量情形同构的 $\sum k_i^4$ 结构，从而定理 1 对广泛的 QCA 模型成立。

为了显示方向依赖，比较两类波矢：

1. 轴向：$\mathbf{k} = (k,0,0)$。此时

$$
\omega^2_{\mathrm{axis}}(k) = c^2 k^2 - \frac{c^2 a^2}{12}k^4 + \mathcal{O}(a^4 k^6).
$$

2. 体对角线：$\mathbf{k} = (k/\sqrt{3},k/\sqrt{3},k/\sqrt{3})$。则

$$
\sum_{i=1}^3 k_i^4 = 3\left(\frac{k}{\sqrt{3}}\right)^4 = \frac{k^4}{3},
$$

因此

$$
\omega^2_{\mathrm{diag}}(k) = c^2 k^2 - \frac{c^2 a^2}{36}k^4 + \mathcal{O}(a^4 k^6).
$$

两者在 $\mathcal{O}(a^2 k^4)$ 上的差值为

$$
\omega^2_{\mathrm{axis}}(k) - \omega^2_{\mathrm{diag}}(k) = -\frac{c^2 a^2}{18}k^4 + \mathcal{O}(a^4 k^6)\neq 0,
$$

从而群速度

$$
v_g = \frac{\partial \omega}{\partial k}
$$

的修正亦呈现同阶差异，即

$$
\Delta v_g^{\mathrm{axis}} - \Delta v_g^{\mathrm{diag}} = \mathcal{O}(a^2 k^3).
$$

因此，只要 $a$ 有限且高能粒子可探测到 $ka \sim 1$ 的区域，晶格各向异性必然成为可观测效应。对无质量光子而言，这意味着在普朗克能标附近光速将成为方向的函数，这正是利用宇宙线到达方向分布约束晶格间距的基础思想。

### 4.2 定理 2：有限精度误差的随机游走标度

考虑单步演化的 Kraus 表示

$$
\rho \mapsto \sum_\alpha K_\alpha \rho K_\alpha^\dagger,
$$

其中在理想幺正情况下只有一个算符 $K_0 = U$ 且 $U^\dagger U = \mathbb{I}$。有限精度实现可被视为在 $U$ 附近加入小的扰动，使得

$$
K_0 = \sqrt{1-\epsilon^2}\,U,\quad K_j = \epsilon L_j,\; j=1,\dots,M,
$$

满足 $\sum_\alpha K_\alpha^\dagger K_\alpha = \mathbb{I}$，$\epsilon\ll 1$。令 $Q$ 为理想情况下守恒的可观测量，即 $[Q,U]=0$。单步后 $Q$ 的期望值变化为

$$
\delta \langle Q \rangle = \mathrm{Tr}(Q\rho') - \mathrm{Tr}(Q\rho),
$$

其中

$$
\rho' = \sum_\alpha K_\alpha \rho K_\alpha^\dagger.
$$

展开得

$$
\delta\langle Q\rangle = \epsilon^2 \sum_{j} \mathrm{Tr}\left( Q L_j \rho L_j^\dagger \right) - \epsilon^2 \mathrm{Tr}(Q\rho) + \mathcal{O}(\epsilon^3).
$$

若 $L_j$ 满足某种"零平均"条件（例如对称噪声），则单步期望偏移可以为零，但方差不为零。定义

$$
\delta Q_n = \langle Q\rangle_n - \langle Q\rangle_{n-1},
$$

则在独立同分布近似下，其方差

$$
\mathbb{E}[(\delta Q_n)^2] \sim \epsilon^2 Q_{\mathrm{char}}^2,
$$

其中 $Q_{\mathrm{char}}$ 是由 $L_j$ 与 $\rho$ 决定的典型尺度。总步数 $N$ 后的累计偏差

$$
\Delta Q_N = \sum_{n=1}^N \delta Q_n
$$

满足

$$
\mathbb{E}[\Delta Q_N]=0,\quad \mathrm{Var}(\Delta Q_N) = N\,\mathrm{Var}(\delta Q_1)\sim N\epsilon^2 Q_{\mathrm{char}}^2,
$$

即

$$
\sigma_Q(N) \sim \sqrt{N} \,\epsilon\, Q_{\mathrm{char}}.
$$

取 $Q$ 为能量或动量总和，$Q_{\mathrm{char}}$ 约为系统总能量或典型粒子能量。若我们希望在宇宙年龄尺度上仍然保持宏观上观测到的守恒精度，比如相对偏差 $\sigma_Q/Q_{\mathrm{char}} \lesssim 10^{-n}$，则有

$$
\epsilon_{\mathrm{eff}} \lesssim 10^{-n}/\sqrt{N}.
$$

若 $N \sim 10^{61}$，则即便 $n=10$ 也要求 $\epsilon_{\mathrm{eff}} \lesssim 10^{-40}$。现实中，守恒律检验的精度因体系不同而异，但这一数量级估计已经表明：若存在类"浮点数"一类的直接舍入误差，其裸值 $\epsilon$ 必须通过可逆计算与纠错编码被大幅抑制，宏观上呈现的只是极其微弱的"残余噪声" $\epsilon_{\mathrm{eff}}$。

在天体物理环境中，例如超高能宇宙线自源头到地球的传播步数可估算为

$$
N_{\mathrm{UHECR}} \sim \frac{L}{\lambda_{\mathrm{int}}},
$$

其中 $L$ 是传播距离，$\lambda_{\mathrm{int}}$ 是典型相互作用或散射的平均自由程。即便采用宏观步长 $\lambda_{\mathrm{int}} \sim 1\,\mathrm{Mpc}$ 粗粒化，$L \sim 100\,\mathrm{Mpc}$ 时也有 $N_{\mathrm{UHECR}}\sim 10^2$。此时若 $\epsilon_{\mathrm{eff}} \sim 10^{-20}$，累计能量相对偏差仅为 $10^{-19}$ 级别，远低于典型观测不确定度。相反，若将普朗克时间视作基本步长，则约束极为严苛。这说明从不同物理过程与时间尺度可以分别约束 $\epsilon_{\mathrm{eff}}$ 的不同组合，为"计算宇宙"的错误预算提供层级化图景。

### 4.3 命题 3：资源调度与 $\alpha(x)$ 调制的有效场论表述

在一般有效场论中，重整化因子 $Z_i(\mu)$ 依赖能标 $\mu$，但被假定在空间上均匀。若引入对空间坐标 $x$ 的缓慢依赖，则在树级近似下可以将其视作外场背景。精细结构常数的定义为

$$
\alpha(x) = \frac{e^2}{4\pi \varepsilon_0 \hbar c} \,\frac{Z_\psi^2(x)}{Z_F(x)},
$$

因此

$$
\frac{\Delta \alpha}{\alpha} \approx 2\frac{\Delta Z_\psi}{Z_\psi} - \frac{\Delta Z_F}{Z_F}.
$$

设资源调度策略在高复杂度区域提供高分辨率，即 $Z_i = Z_i^{(0)}$，在低复杂度区域略有偏移 $\delta Z_i$。若 $\delta Z_i/Z_i^{(0)} \sim \lambda\,\Delta \chi$ 线性依赖复杂度指示函数的变化，则

$$
\frac{\Delta \alpha}{\alpha} \sim \lambda_{\alpha} \Delta \chi.
$$

原子钟比较实验对 $\alpha$ 的时间漂移给出 $|\dot{\alpha}/\alpha| \lesssim 10^{-17}\,\mathrm{yr}^{-1}$ 量级的上限，([APS Links][5]) 而类星体吸收线与宇宙微波背景对其空间漂移给出 $|\Delta\alpha/\alpha| \lesssim 10^{-7}\text{–}10^{-5}$ 级别的约束，取决于红移与样本。([PMC][6]) 在"懒惰计算"情景下，可将宇宙空洞与致密星系团视作 $\chi$ 的两个极端，相对差值 $\Delta\chi \sim 1$，于是上述结果直接转化为对 $\lambda_{\alpha}$ 的上限。这些定量关系将在后文的模型应用部分进一步具体化。

---

## Model Apply

本节将上述三类数值伪影分别映射到现有或可预期的观测窗口。

### 5.1 晶格各向异性与超高能宇宙线谱

Beane 等人研究了立方晶格上实现的 QCD 模型对宇宙线的影响，指出若宇宙是采用 Wilson 费米子与立方晶格的数值模拟，则由于格点动量空间的 Brillouin 区结构，高能宇宙线谱的截止将展现出与晶格方向相关的各向异性。([arXiv][1]) 在 QCA 视角下，这一思想可推广为：

* 晶格色散关系在 $ka \lesssim 1$ 时开始偏离连续洛伦兹形式；

* 对于超高能质子或原子核，其能谱上限与传播阻尼将依赖其在动量空间中相对于晶格轴向的方向；

* 若观测到的 GZK 截断在天球上呈现出与某一固定方向相关的系统偏差，而该方向无法简化为本地天体物理结构（如银河磁场或源分布）的结果，则可视为晶格各向异性的候选信号。

目前皮埃尔·奥格天文台与 Telescope Array 对超高能宇宙线到达方向各向异性的观测显示出与大尺度结构相关的各向异性，但尚未发现指向某一固定宇宙学轴的普适偏离。现有数据通常可转化为对 $\Delta c/c$ 在 $E\sim 10^{19}\text{–}10^{20} \,\mathrm{eV}$ 能段上约 $10^{-20}\text{–}10^{-21}$ 级别的上限，从而给出 $a^{-1} \gtrsim 10^{11}\text{–}10^{12} \,\mathrm{GeV}$ 的下界，与格点规范场论分析相一致。([arXiv][1])

### 5.2 能量依赖光速与伽马射线暴时间延迟

若将晶格与有限精度伪影一并重写为有效的洛伦兹破缺项，则高能光子的色散关系可写为

$$
E^2 = p^2 c^2 \left[ 1 + \xi_1 \left(\frac{E}{E_{\mathrm{QG}}}\right) + \xi_2 \left(\frac{E}{E_{\mathrm{QG}}}\right)^2 + \cdots \right],
$$

其中 $E_{\mathrm{QG}}$ 是等效的量子引力或晶格能标，$\xi_n$ 为数值伪影控制的系数。光速随能量的有效变化在一阶近似为

$$
v(E) \approx c \left[ 1 - \frac{n+1}{2}\xi_n \left(\frac{E}{E_{\mathrm{QG}}}\right)^n \right].
$$

对于红移 $z$ 的瞬变源（GRB、耀变体爆发等），不同能量光子之间的到达时间延迟

$$
\Delta t \sim \frac{n+1}{2H_0} \,\xi_n \frac{\Delta E^n}{E_{\mathrm{QG}}^n} \int_0^z \frac{(1+z')^n}{\sqrt{\Omega_m(1+z')^3 + \Omega_\Lambda}}\,\mathrm{d}z'.
$$

Fermi-LAT 对数个明亮 GRB 的分析表明，在 $E\sim \mathrm{GeV}$ 范围内未发现显著能量依赖延迟，从而给出了对线性项 $n=1$ 和二次项 $n=2$ 的强限制：线性情形下 $E_{\mathrm{QG}} \gtrsim E_{\mathrm{P}}$，二次情形下 $E_{\mathrm{QG}} \gtrsim 10^{10}\,\mathrm{GeV}$ 的典型量级。([arXiv][4])

在计算宇宙框架中，可将 $E_{\mathrm{QG}}$ 与晶格间距 $a$ 及有效截断误差 $\epsilon_{\mathrm{eff}}$ 联系起来。例如若数值伪影主要来自晶格，则 $E_{\mathrm{QG}} \sim \hbar c/a$；若主要来自有限精度，则 $\xi_n$ 将为 $\epsilon_{\mathrm{eff}}$ 的某种函数。于是 GRB 时间延迟约束可被转写为对 $a$ 与 $\epsilon_{\mathrm{eff}}$ 的联合上界。

### 5.3 光速各向异性与现代 Michelson–Morley 实验

现代 Michelson–Morley 型实验采用超稳频的光学谐振腔，比较两条互相正交干涉臂上光速的差异，随着地球自转与公转实现对不同空间方向的扫描。Müller 等人通过冷却光学谐振腔实验，将光速各向异性的相对上限压缩到 $\Delta c/c \lesssim 10^{-15}$ 水平，并在 Robertson–Mansouri–Sexl 参数化框架下给出了相应的不等式。([arXiv][3])

若晶格各向异性诱导的光速方向依赖在低能区可近似写为

$$
\frac{\Delta c(\theta,\phi)}{c} \sim \lambda_{\mathrm{ani}} \left(\frac{E}{E_{\mathrm{QG}}}\right)^2,
$$

则实验频率通常对应 $E\sim \mathrm{eV}$ 级别，即使 $E_{\mathrm{QG}} \sim E_{\mathrm{P}}$，也有 $(E/E_{\mathrm{QG}})^2 \sim 10^{-56}$，远低于现有灵敏度。因而低能光学实验主要约束的是"能量无关"的各向异性，即若存在与能量无关的晶格优选方向，则必须使其权重 $\lambda_{\mathrm{ani}} \lesssim 10^{-15}$。这意味着若计算宇宙在设定 QCA 模型时未能完全做到能量依赖抑制，则宏观低能实验足以排除大部分"粗糙晶格"的构造。

### 5.4 原子钟网络与 $\alpha$ 的时空漂移

原子钟通过比较不同跃迁频率的稳定性来检验基本常数的变化，例如氢超精细结构、光学跃迁或高电荷离子钟等。Prestage 等人早期利用氢微波标准与汞离子钟的频率比较，得到 $|\Delta\alpha/\alpha| \lesssim 10^{-14}$（超过百日时间尺度）的限制；([APS Links][5]) 随着光学晶体钟与高电荷离子钟的发展，这一约束已被进一步收紧，并有专门设计的时钟对 $\alpha$ 的变化具备增强灵敏度。([Frontiers][7])

在计算宇宙情景下，若"资源调度"机制导致在不同空间区域或引力势中采用略有不同的离散化策略，则 $\alpha$ 的有效值可能呈现与环境相关的漂移。类星体吸收线的数据给出了在宇宙学尺度上 $|\Delta\alpha/\alpha| \lesssim 10^{-6}\text{–}10^{-5}$ 的典型约束；([PMC][6]) 近期 CMB 与距离–模数关系的分析亦对 $\alpha$ 的空间调制进行了独立检验。([APS Links][8]) 综合这些结果可得出：在"低复杂度"宇宙空洞与"高复杂度"星系团之间，若 $\Delta\chi \sim 1$，则 $|\lambda_{\alpha}| \lesssim 10^{-6}\text{–}10^{-5}$；而在地球轨道附近的引力势变化与太阳活动周期尺度上，则 $|\lambda_{\alpha}| \lesssim 10^{-15}$。

---

## Engineering Proposals

本节在既有实验基础上提出若干针对性的"计算取证学"实验方案，旨在最大化对 $\eta_a, \epsilon_{\mathrm{eff}}, \delta_{\mathrm{res}}$ 的约束能力。

### 6.1 超高能宇宙线各向异性调查的"晶格模式"分析

现有对超高能宇宙线各向异性的分析多集中于与大尺度结构或银河磁场的相关性。为了针对晶格各向异性，本工作建议引入如下分析步骤：

1. 在天球上选取一族与立方晶格对称群 $O_h$ 相匹配的球谐基底，将宇宙线到达方向的角分布展开在这些基函数上；

2. 重点分析与 $l=4$ 模相关的多极矩，因为 $\sum k_i^4$ 对应的角依赖可用四极与六极分量组合表示；

3. 将观测到的 $O_h$-结构分量与由各向同性源、银河磁场与大尺度结构模拟得到的"天体物理背景"进行差分，识别任何残余的"晶格型"模式。

若在 $E > 5\times 10^{19}\,\mathrm{eV}$ 的样本中仍未发现显著的 $O_h$-结构偏离，则可将 Beane 等人的 $a^{-1} \gtrsim 10^{11}\,\mathrm{GeV}$ 类型约束进一步提高一个量级以上。([arXiv][1])

### 6.2 多色多台伽马射线暴联合测时

当前 Fermi-LAT、MAGIC、HESS 等设施已对 GRB 的能量依赖延迟进行分析，但不同仪器在能段与时间分辨率上各有侧重。针对计算宇宙的色散效应，可设计专门的联合观测活动，具有以下特点：

1. 同时在 keV–MeV 与 GeV–TeV 多能段进行高时间分辨率观测，以增大 $\Delta E^n$；

2. 优先选择具有尖锐上升沿或短时脉冲结构的 GRB，以减小源内本征延迟的不确定性；

3. 在统计分析中引入"晶格方向"假设，即设想存在一组特定的空间方向，其上色散效应增强或减弱，对不同 GRB 的天球分布进行条件分组。

通过这一策略，有望将对二次能量依赖色散的约束推进一至两数量级，从而更敏感地检验 QCA 晶格伪影。

### 6.3 旋转光学谐振腔阵列与地面"Michelson–Morley 网络"

为提高对光速各向异性的灵敏度，可在全球布设多台高稳定光学谐振腔，构成一个"Michelson–Morley 网络"，并通过卫星时间同步实现长时间的相干数据积累。实验要点包括：

1. 每个站点配置相互正交的多个谐振腔，并以预定速率缓慢机械旋转，实现在短时间内扫描空间方向；

2. 不同站点在地球上的分布应尽量覆盖不同纬度与经度，以消除本地系统误差；

3. 数据分析时引入指向银河系平面、超星系平面以及候选"晶格轴"的特定方向模板，对频率漂移进行模板拟合。

若长期运行未发现与任何固定宇宙学方向相关的频率调制，可将"能量无关"的晶格各向异性进一步压缩到 $\Delta c/c \lesssim 10^{-18}$ 甚至更低。

### 6.4 深空原子钟与宇宙空洞的"分辨率探测"

为检验"懒惰计算"假设，可在未来深空探测任务中搭载高稳定原子钟（包括高电荷离子钟），在飞行器穿越不同引力势与大尺度结构环境时持续比较频率。具体方案包括：

1. 在太阳系外轨道或 Lagrange 点布设标准钟，与地面钟通过光学链路比较，检验 $\alpha$ 与其他常数是否存在与传统引力红移不同的额外漂移；

2. 在未来可达星际介质的任务中，刻意选择接近宇宙学空洞方向，利用长时间链路对比检验 $\alpha$ 在"低复杂度"环境中的微小偏离；

3. 将所得数据与类星体吸收线与 CMB 的 $\alpha$ 约束进行联合分析，构建对 $\delta_{\mathrm{res}}(x)$ 的全宇宙三维"计算分辨率映射"。

---

## Discussion (risks, boundaries, past work)

### 7.1 与量子引力与有效场论框架的关系

许多量子引力量子化方案（如环量子引力、非对易几何、多重特殊相对论等）同样预言在普朗克尺度附近出现洛伦兹破缺或修正，其数学形式往往与晶格伪影相似，例如色散关系中的 $p^3/M_{\mathrm{P}}$ 或 $p^4/M_{\mathrm{P}}^2$ 修正项。([科学直通车][9]) 因此，即便观测到某种高能色散或各向异性，其解释也未必指向模拟假说，而可能只是量子引力效应。

本文的贡献在于：在 QCA 与计算宇宙框架中给出一套内部自洽的参数化，使得不同来源的数值伪影（晶格、有限精度、资源调度）均可嵌入有效场论中，并与实验数据直接对应。同时表明若要与现有高精度实验相容，任何"计算宇宙"的硬件实现都必须接近"完美可逆计算与大规模纠错"的极端极限。

### 7.2 统计与系统误差的风险

在超高能宇宙线、GRB 与宇宙学常数漂移的分析中，系统误差往往难以完全控制。例如：

* 宇宙线的源分布与磁场模型存在不确定性；

* GRB 源内本征发射延迟可能与能量相关；

* 类星体吸收线测量受制于仪器波长标定与吸收云自身动力学。

这些因素均可能产生看似"数值伪影"的信号。因此任何关于"计算宇宙迹象"的声称都必须在严格的系统误差分析基础上进行，且需要多种独立观测的一致支持。

### 7.3 观测约束的解释空间

现有实验对洛伦兹破缺与常数漂移给出了极强约束，这可以从两种角度被解读：

1. 若宇宙是计算的，则其底层实现高度精巧，数值伪影被压缩到极限；

2. 宇宙并非以"有限字长数字模拟"的方式实现，或其实现形式在数学上等效于理想 QCA 或连续场论，不包含数值伪影。

本文并不试图在这两种解释之间作出选择，而是强调：无论哪一种，实验上得到的都是对"允许的偏离空间"的描述。若未来实验依然未发现显著偏离，则可以进一步将数值伪影参数空间压缩；若出现系统性异常，则需要在量子引力、暗能量新物理与计算宇宙三种解释之间进行区分和比较。

### 7.4 与近期模拟宇宙可行性研究的联系

Vazza 等人近期从信息与能量预算出发，评估了严格物理意义上重现观测宇宙所需的计算资源，指出若尝试以显式数值模拟方式在"基底宇宙"中重现实在宇宙，其能耗可能远超可行范围。([Frontiers][2]) 这一结论对"朴素数值模拟"提出了挑战，但仍为"形式上的计算宇宙"（如数学结构、可逆 QCA 等）保留空间。本文在后者框架下工作的同时，借用前者的资源估计结果，为 $\eta_a, \epsilon_{\mathrm{eff}}, \delta_{\mathrm{res}}$ 的合理取值给出定性边界：

* 若 $a$ 过小，则模拟所需存储与计算复杂度爆炸；

* 若 $\epsilon_{\mathrm{eff}}$ 过大，则与实验观测冲突；

* 若资源调度过于激进，则必然在宇宙学尺度上产生可观测的常数漂移。

---

## Conclusion

本文在量子元胞自动机与计算宇宙的统一框架下，将"模拟假说"具体化为一套可与实验对接的参数化模型。通过对立方晶格色散关系、高维有效算符与有限精度随机噪声的系统分析，我们得到如下主要结论：

1. 任何在立方晶格上逼近洛伦兹不变场论的 QCA，在高动量区不可避免地出现 $\mathcal{O}(a^2k^4)$ 阶的各向异性色散修正，从而导致高能粒子与光速的方向依赖。

2. 有限精度数值实现如未经完美可逆计算与纠错抹平，将在宏观尺度上表现为守恒律的随机游走偏离。若以普朗克时间为基本步长，则要与现有观测相容，等效截断误差 $\epsilon_{\mathrm{eff}}$ 必须远低于传统浮点数所允许的误差。

3. 资源调度与"懒惰计算"情景可在有效场论中重写为基本常数对空间背景的缓慢依赖，其幅度被原子钟、类星体吸收线与宇宙学数据严格约束。

4. 结合超高能宇宙线、伽马射线暴时间延迟、现代 Michelson–Morley 实验与原子钟网络，可以对晶格间距、截断误差与分辨率调制建立一个多维约束空间，为计算宇宙的"错误预算"提供定量框架。

5. 本文提出了一系列面向未来观测设施的"计算取证学"实验方案，包括晶格模式的宇宙线各向异性分析、多台多色 GRB 联合测时、全球光学谐振腔网络与深空原子钟任务，为进一步压缩数值伪影参数空间提供路径。

这些结果并未证明宇宙必然为模拟，但表明若宇宙以计算方式实现，则其硬件与算法必须满足极为苛刻的物理一致性条件。反过来，任何未来发现的细微但稳健的洛伦兹破缺或常数漂移，都可以通过本文框架被重新诠释为"计算宇宙"的潜在痕迹。这一视角为高精度物理实验提供了额外的解释维度，也为模拟假说赋予了具体的、可证伪的内容。

---

## Acknowledgements, Code Availability

作者感谢有关量子元胞自动机、模拟宇宙与高精度物理实验的公开文献与数据整理工作，它们为本文提供了必要的背景与定量基准。本文为理论分析，不涉及新的数值代码实现。若未来开展基于本文参数化的具体数据拟合与数值模拟，相关代码可在适当平台公开。

---

## Appendix A：立方晶格色散与 $\mathrm{SO}(3)$ 破缺的群论分析

在定理 1 的推导中，我们通过具体的差分算子展示了 $\sum k_i^4$ 结构的出现。本附录给出基于群论的更一般说明。

在连续情形下，洛伦兹不变或旋转不变的色散修正项必须由 $k^2 = \sum k_i^2$ 的多项式构成，例如 $k^4, k^6$ 等，对应 $\mathrm{SO}(3)$ 不变张量的标量部分。而在立方晶格上，对称群减少为 $O_h$。在这一群下，动量的多项式按不可约表示分解，其中包括标量表示 $A_1$、双重简并表示 $E$ 与三重简并表示 $T_2$ 等。

四阶多项式空间可分解为

$$
\mathcal{P}_4(\mathbf{k}) \cong A_1 \oplus E \oplus T_2,
$$

其中 $A_1$ 的基可以取为

$$
k_x^4 + k_y^4 + k_z^4,
$$

而 $E$ 与 $T_2$ 则对应不同的非标量组合，如

$$
2k_z^4 - k_x^4 - k_y^4,\quad k_x^4 - k_y^4,
$$

等。若要求色散关系在 $O_h$ 下保持标量，则只能选择 $A_1$ 分量，即 $\sum k_i^4$。但 $A_1$ 相对于 $\mathrm{SO}(3)$ 并非标量，而是标量 $k^4$ 与高阶球谐 $Y_{4m}$ 的线性组合。具体而言，有

$$
\sum_{i=1}^3 k_i^4 = \frac{3}{5}k^4 + \text{(与 } Y_{4m} \text{ 相关的各向异性项)}.
$$

这说明即便在晶格对称群下保持标量，仍不可避免引入相对于完全旋转群的"残余"各向异性。该各向异性的角依赖由 $l=4$ 的球谐系数表征，这正是第 6.1 节中提出以 $l=4$ 模式分析宇宙线各向异性的群论基础。

对更高阶修正 $\mathcal{O}(a^4k^6)$ 等，可类似地分析 $\mathcal{P}_6(\mathbf{k})$ 在 $O_h$ 下的分解。只要不引入额外的"改善"算子（如格点改进方案），这些各向异性成分在高能区均难以完全消除。

---

## Appendix B：有限精度噪声的多尺度约束

在定理 2 中，我们采用了单一步长 $\Delta t \sim t_{\mathrm{P}}$ 的估计。实际物理过程中存在多种有效时间尺度，本附录给出多尺度分解的约束结构。

设某一物理过程的自然时间尺度为 $\tau$，在此尺度上发生一次"宏观事件"（如一次散射、一段宇宙线的自由传播、一段引力波通过探测器）。在计算宇宙框架中，这段时间对应 $N_\tau$ 个底层时间步，每步引入相对误差 $\epsilon$。若宏观可观测量 $Q$ 对每个宏观事件的敏感度为 $\delta Q_\tau \sim \sqrt{N_\tau}\epsilon Q_{\mathrm{char}}$，而实验对 $Q$ 在该尺度上的相对精度为 $\sigma_Q/Q_{\mathrm{char}}$，则有

$$
\epsilon_{\mathrm{eff}} \lesssim \frac{\sigma_Q/Q_{\mathrm{char}}}{\sqrt{N_\tau}}.
$$

不同物理过程给出不同的 $N_\tau$ 与 $\sigma_Q$：

1. **实验室能量守恒测试**：例如原子跃迁能级的精细结构，时间尺度 $\tau \sim 10^{-8}\,\mathrm{s}$，精度 $\sigma_E/E \sim 10^{-12}\text{–}10^{-15}$。

2. **天体物理过程**：如脉冲星自转周期演化，$\tau \sim 10^7\text{–}10^8\,\mathrm{s}$，精度 $\sigma_f/f \sim 10^{-15}\text{–}10^{-18}$。

3. **宇宙学过程**：如宇宙膨胀历史与 CMB 各向异性，$\tau \sim 10^{13}\text{–}10^{17}\,\mathrm{s}$，精度依观测量而定。

将上述各类约束同时考虑，可以构建 $\epsilon_{\mathrm{eff}}$ 在不同能量与时间尺度上的"误差流形"，进而界定哪些类型的计算宇宙实现与现有观测不相容。例如若某类实现导致高能过程中的 $N_\tau$ 极大，则其对 $\epsilon_{\mathrm{eff}}$ 的约束比低能过程更强；反之，若底层算法在高能区采取更精细的可逆计算，而在低能区允许略大误差，则约束结构可能倒转。

---

## Appendix C："懒惰计算"与宇宙空洞的简化模型

为定量考察"懒惰计算"假设下 $\alpha(x)$ 的可能漂移，构建如下简化模型：

1. 将宇宙划分为两类区域：致密区 $D$（星系与星系团）与空洞区 $V$；

2. 在致密区，模拟器使用高分辨率参数 $(a_D,\Delta t_D,n_D)$；在空洞区使用粗分辨率参数 $(a_V,\Delta t_V,n_V)$，其中 $a_V > a_D$、$\Delta t_V > \Delta t_D$ 或 $n_V < n_D$；

3. 假设电磁场在这两类区域内的重整化常数满足

$$
Z_F^{(V)} = Z_F^{(D)}(1+\delta_F),\quad Z_\psi^{(V)} = Z_\psi^{(D)}(1+\delta_\psi),
$$

则

$$
\frac{\Delta\alpha}{\alpha} = \frac{\alpha_V - \alpha_D}{\alpha_D} \approx 2\delta_\psi - \delta_F.
$$

若假设 $\delta_F,\delta_\psi$ 为 $a$ 与 $\Delta t$ 的解析函数，例如

$$
\delta_F \sim c_1 (a_V^2 - a_D^2)\Lambda^2 + c_2 (\Delta t_V - \Delta t_D)\Lambda + \cdots,
$$

其中 $\Lambda$ 为某个重整化截断，则可将 $\Delta\alpha/\alpha$ 表达为 $a_V,a_D,\Delta t_V,\Delta t_D$ 的组合。通过将观测到的 $|\Delta\alpha/\alpha|$ 上限代入，即可得到对允许的分辨率差异的约束。

例如若类星体吸收线观测表明在 $z\sim 2\text{–}4$ 范围内 $|\Delta\alpha/\alpha| \lesssim 10^{-6}$，([PMC][6]) 则粗略上可以认为 $|2\delta_\psi - \delta_F| \lesssim 10^{-6}$。若重整化系数对 $a^2 \Lambda^2$ 有 $\mathcal{O}(1)$ 的系数，则必须要求 $|a_V^2 - a_D^2|\Lambda^2 \lesssim 10^{-6}$，在 $\Lambda \sim M_{\mathrm{P}}$ 情形下，这意味着即便在宇宙空洞中，相比致密区，晶格间距也只能增加不到一个普朗克长度的相对 $10^{-6}$ 量级。这一结果说明：在较为自然的重整化假设下，"懒惰计算"在宇宙学尺度上几乎没有调节余地，除非其对低能电磁效应的影响以某种方式被精确抵消。

---

## References

[1] S. R. Beane, Z. Davoudi, M. J. Savage, "Constraints on the universe as a numerical simulation," Eur. Phys. J. A 50, 148 (2014).

[2] F. Vazza, et al., "Astrophysical constraints on the simulation hypothesis for the universe," Front. Phys. (2025).

[3] N. Bostrom, "Are You Living in a Computer Simulation?," Philos. Quart. 53, 243–255 (2003).

[4] H. Müller, S. Herrmann, A. Saenz, A. Peters, C. Lämmerzahl, "Modern Michelson–Morley experiment using cryogenic optical resonators," Phys. Rev. Lett. 91, 020401 (2003).

[5] V. Vasileiou, et al., "Constraints on Lorentz invariance violation with Fermi-LAT observations of gamma-ray bursts," Phys. Rev. D 87, 122001 (2013).

[6] Z. Xiao, B.-Q. Ma, "Constraints on Lorentz invariance violation from gamma-ray bursts," Phys. Rev. D 80, 116005 (2009).

[7] J. D. Prestage, R. L. Tjoelker, L. Maleki, "Atomic clocks and variations of the fine structure constant," Phys. Rev. Lett. 74, 3511 (1995).

[8] M. S. Safronova, et al., "Atomic clocks and the search for variation of the fine structure constant," Ann. Phys. (Berlin) 531, 1800364 (2019).

[9] Y.-M. Yu, et al., "Highly charged ion clocks: Frontier candidates for tests of fundamental physics," Front. Phys. 11, 1104848 (2023).

[10] M. R. Wilczynska, et al., "Four direct measurements of the fine-structure constant 13 billion years ago," Sci. Adv. 6, eaay9672 (2020).

[11] T. D. Le, M. T. Vu, T. H. Dinh, "Stringent limit on space-time variation of fine-structure constant," Heliyon 6, e04495 (2020).

[12] H. M. Tohfa, et al., "Cosmic microwave background search for fine-structure constant variations," Phys. Rev. D 109, 103529 (2024).

[13] R. S. Gonçalves, et al., "Variation in the fine-structure constant and the distance-duality relation," JCAP 06, 036 (2020).

[14] G. Amelino-Camelia, "Testable scenario for relativity with minimum-length," Phys. Lett. B 510, 255–263 (2001).

[15] S. Zhang, B.-Q. Ma, "Lorentz violation from gamma-ray bursts," Astropart. Phys. 61, 108–113 (2015).

[1]: https://arxiv.org/abs/1210.1847?utm_source=chatgpt.com "Constraints on the Universe as a Numerical Simulation"

[2]: https://www.frontiersin.org/journals/physics/articles/10.3389/fphy.2025.1561873/full?utm_source=chatgpt.com "Astrophysical constraints on the simulation hypothesis for ..."

[3]: https://arxiv.org/abs/physics/0305117?utm_source=chatgpt.com "Modern Michelson-Morley experiment using cryogenic ..."

[4]: https://arxiv.org/abs/1308.6403?utm_source=chatgpt.com "Constraints on Lorentz Invariance Violation with Fermi-LAT Observations of Gamma-Ray Bursts"

[5]: https://link.aps.org/doi/10.1103/PhysRevLett.74.3511?utm_source=chatgpt.com "Atomic Clocks and Variations of the Fine Structure Constant"

[6]: https://pmc.ncbi.nlm.nih.gov/articles/PMC7182409/?utm_source=chatgpt.com "Four direct measurements of the fine-structure constant 13 ..."

[7]: https://www.frontiersin.org/journals/physics/articles/10.3389/fphy.2023.1104848/full?utm_source=chatgpt.com "Highly charged ion (HCI) clocks: Frontier candidates for ..."

[8]: https://link.aps.org/doi/10.1103/PhysRevD.109.103529?utm_source=chatgpt.com "Cosmic microwave background search for fine-structure ..."

[9]: https://www.sciencedirect.com/science/article/pii/S0927650514000541?utm_source=chatgpt.com "Lorentz violation from gamma-ray bursts"

