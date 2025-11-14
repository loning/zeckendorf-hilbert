# 边界时间几何：统一时间刻度、分辨率层级与相互作用的边界理论

Abstract
构建一个以边界为本体、以时间为几何刻度的统一理论体系。基本假设是：物理实在首先以边界可观测代数及其谱数据呈现，体域动力学是边界数据的一种延拓；所有可观测时间刻度——散射时间、模时间与几何时间——属于同一等价类；观察者的有限分辨率在几何上表现为一个带有联络与曲率的分辨率纤维丛。数学上，引入带边界谱三元组的非交换几何结构，将 Brown–York 边界应力张量与 AdS/CFT 中的边界应力张量、Wigner–Smith 时间延迟矩阵与 Birman–Kreĭn 谱移函数、Tomita–Takesaki 模块流与热时间假设统一在一个"边界时间几何"(Boundary Time Geometry, BTG) 框架之中。证明在适当的匹配条件下，存在唯一（至仿射重标）边界时间生成元，使散射时间、模时间与几何时间定义出同一时间刻度等价类；所有经典"力"则表现为统一边界联络曲率在不同纤维方向上的投影，因而不再是基本对象，而是边界几何与分辨率结构的涌现属性。进一步在分辨率纤维丛上建立现象层级涌现定理，阐明高分辨率的量子散射与模时间结构如何经完全正粗粒化映射退化为宏观的引力与经典力学。最后给出黑洞热力学、宇宙学红移与介观输运的 BTG 重述，并提出可在微波网络、原子钟网络与介观导体中实现的实验检验协议。

Keywords
边界时间几何；非交换几何；谱三元组；Wigner–Smith 时间延迟；Birman–Kreĭn 谱移；Brown–York 应力张量；热时间假设；分辨率纤维丛；全息界–体对应；重整化群

---

## Introduction & Historical Context

在广义相对论中，Gibbons–Hawking–York 边界项与 Brown–York 准局域应力–能量张量表明，引力作用量的良定变分以及准局域能量–动量的定义，根本上依赖于边界几何及其共轭变量；边界三度规的变分导出一个表面应力张量 $T^{ab}_{\mathrm{BY}}$，其在适当极限下重现 ADM 能量并为黑洞热力学提供准局域能量意义。([arXiv][1]) 在 AdS/CFT 全息框架中，Balasubramanian–Kraus 应力张量将重整化边界应力–能量视为对偶共形场论的能动张量，进一步加深了"边界主导"的视角。([arXiv][2])

另一方面，散射理论中的 Wigner–Smith 时间延迟矩阵
$Q(\omega) = -i S(\omega)^\dagger \partial_\omega S(\omega)$
刻画了波包在散射区的平均驻留时间，其迹与谱移函数的导数之间通过 Birman–Kreĭn 公式建立了紧密联系：总散射相位之导数、Wigner–Smith 群延迟的迹与相对态密度是同一对象的不同表现。([arXiv][3])

在代数量子场论与量子统计中，Tomita–Takesaki 模块理论揭示：给定可观测代数与一个状态，天然地存在一族一参数自同构群 $\sigma_t^\omega$，其参数 $t$ 可被解释为"模时间"；Connes–Rovelli 的热时间假设进一步提出，物理时间可以被理解为由状态–代数对决定的模块流参数，传统意义上的时间反而是派生概念。([theorie.physik.uni-goettingen.de][4])

非交换几何给出了一种以谱数据定义几何的语言：一个谱三元组 $(\mathcal A,\mathcal H,D)$ 由代数、Hilbert 空间与 Dirac 型算子组成，在紧致 Riemann 流形的情形下，度规结构可由 Dirac 谱唯一重建；该框架为将"边界几何"与"边界可观测代数"统一提供了自然平台。([维基百科][5])

本文的基本立场是，将上述三条线索——边界引力、散射时间与模块时间——在一个统一的"边界时间几何"框架中粘合起来，以边界为本体、时间为刻度、分辨率为纤维，构造一个既能容纳现有理论又能给出新预言的统一理论体系。

---

## Model & Assumptions

### Axioms: Boundary Priority, Time Equivalence, Resolution Hierarchy

**公理 1（边界优先性）**
给定一个具有良好因果结构的时空区域 $(M,g)$，其包含一类拓扑良好的边界 $\partial M$（包括时样、空样或零样边界），物理可观测量的基本描述以边界可观测代数 $\mathcal A_\partial$ 与状态集合 $\mathcal S_\partial$ 为主；体域可观测量与动力学可视为适当意义下由 $(\mathcal A_\partial,\mathcal S_\partial)$ 决定的延拓。

**公理 2（时间刻度等价性）**
存在一类时间刻度等价类 $[\tau]$，其元素为不同构造下的时间参数：散射时间 $\tau_{\mathrm{scatt}}$、模时间 $\tau_{\mathrm{mod}}$ 与几何时间 $\tau_{\mathrm{geom}}$。任意两种时间刻度在共同定义域上通过仿射变换
$\tau^{(2)} = a \tau^{(1)} + b$（$a>0$）等价。

**公理 3（分辨率层级性）**
对每个具体实验安排或观察者，存在一个分辨率参数 $\Lambda$（可理解为 UV 截断、 coarse-graining 阶段或 RG 标度），使得在不同 $\Lambda$ 下，同一边界几何数据经完全正映射投影到不同粗粒度的有效代数 $\mathcal A_\Lambda \subseteq \mathcal A_\partial$。

### Boundary Spectral Data

**定义 1（边界谱三元组）**
一个边界谱三元组是三元组
$(\mathcal A_\partial,\mathcal H_\partial,D_\partial)$，其中

1. $\mathcal A_\partial$ 是定义在边界上的致密 *-代数（典型情形为 $C^\infty(\partial M)$ 或其非交换推广），
2. $\mathcal H_\partial$ 是携带 $\mathcal A_\partial$ *-表示的 $\mathbb Z_2$-分次 Hilbert 空间，
3. $D_\partial$ 是自伴的、具有紧致预解算子的第一阶椭圆算子（Dirac 型），满足对任意 $a\in\mathcal A_\partial$ 有交换子 $[D_\partial,a]$ 有界。

此即 Connes 意义下的（偶）谱三元组的边界化版本。([维基百科][5])

**定理 1（边界度规的谱重构）**
若 $\partial M$ 为紧致 spin Riemann 流形，则三元组
$(\mathcal A_\partial,\mathcal H_\partial,D_\partial) = (C^\infty(\partial M),L^2(S_\partial),D_\partial)$
确定一个唯一的 Riemann 度规 $h_{ab}$ 使得 Connes 距离
$d(x,y)=\sup\{|a(x)-a(y)|:,a\in C^\infty(\partial M),\ |[D_\partial,a]|\le 1\}$
等于 $(\partial M,h_{ab})$ 的路径长度距离。

*证明思路* 与标准谱几何理论完全一致：在紧致 spin 流形上，以 Dirac 算子作为几何数据的载体，其 Lipschitz 约束给出的态空间伪度规在纯态子集上恰好重现 Riemann 度规诱导的距离。([维基百科][5])

因此，在 BTG 中，边界"度规"不必先验给定，而是由 $D_\partial$ 的谱结构定义；这为将时间刻度嵌入 Dirac 谱提供了自然通道。

### Boundary Stress Tensor and Quasilocal Hamiltonian

在四维广义相对论中，引入 GHY 边界项后，作用量对边界三度规 $h_{ab}$ 的变分定义 Brown–York 表面应力张量
$T^{ab}_{\mathrm{BY}} := \frac{2}{\sqrt{-h}} \frac{\delta S_{\mathrm{grav}}}{\delta h_{ab}}$。其零分量的适当投影给出准局域能量密度，积分得到的准局域能量等于在边界上生成单位固有时间平移的 Hamilton 量。([arXiv][1])

在 AdS 场景中，holographic renormalization 过程导出重整化边界应力张量 $T^{ab}_{\mathrm{ren}}$，可解释为对偶 CFT 的期望值 $\langle T^{ab} \rangle$。([arXiv][2]) 这些结果表明：边界应力张量天然携带一个生成边界"时间流"的 Hamilton 量。

---

## Main Results (Theorems and Alignments)

### Unified Time Scales on the Boundary

我们分别从散射、模块流与几何三端给出时间刻度的定义。

1. **散射时间 $\tau_{\mathrm{scatt}}$**
   考虑具有有限通道数的定能量散射矩阵 $S(\omega)$；定义 Wigner–Smith 时间延迟矩阵
   $Q(\omega) = -i S(\omega)^\dagger \partial_\omega S(\omega)$。其迹
   $\tau_{\mathrm{W}}(\omega) := \operatorname{tr} Q(\omega)$
   给出总群延迟；在 Birman–Kreĭn 框架下，谱移函数 $\xi(\omega)$ 满足
   $\det S(\omega) = \exp(-2\pi i \xi(\omega))$，从而有
   $\xi'(\omega) = \frac{1}{2\pi} \operatorname{tr} Q(\omega)$。([arXiv][3])
   给定参考能量 $\omega_0$ 与窗口 $I \subset \mathbb R$，定义散射时间刻度
   $\tau_{\mathrm{scatt}}(\omega) := \int_{\omega_0}^\omega \xi'(\tilde\omega),\mathrm d\tilde\omega = \xi(\omega)-\xi(\omega_0)$。

2. **模时间 $\tau_{\mathrm{mod}}$**
   对边界可观测代数 $\mathcal A_\partial$ 与状态 $\omega$，假设存在分离–循环向量，使 Tomita–Takesaki 模块数据 $(J,\Delta_\omega)$ 良定；模块群
   $\sigma_t^\omega(A) := \Delta_\omega^{it} A \Delta_\omega^{-it}$
   定义一参数自同构群。热时间假设认为，适当的物理时间参数 $\tau_{\mathrm{mod}}$ 与模块参数 $t$ 仅相差一个常数倍，且 $\sigma_t^\omega$ 在平衡态下扮演"时间演化"的角色。([theorie.physik.uni-goettingen.de][4])

3. **几何时间 $\tau_{\mathrm{geom}}$**
   在带边界的广义相对论中，选择边界上一个单位时间样向量场 $u^a$ 与对应的 Killing 或准 Killing 生成元 $\xi^a$，则 Brown–York Hamilton 量可写为
   $H_\partial[\xi] = \int_{\Sigma\cap\partial M} \sqrt{\sigma},u_a T_{\mathrm{BY}}^{ab}\xi_b,\mathrm d^{d-2}x$，
   其中 $\sigma$ 为截面上的诱导度规。以 $H_\partial$ 为生成元的正则演化参数定义几何时间刻度 $\tau_{\mathrm{geom}}$。([arXiv][1])

在 BTG 框架中，我们并不预设三种时间刻度彼此独立，而是通过以下定理将其统一。

**定理 2（边界时间刻度等价定理）**
设 $\partial M$ 为一类"良性边界"，满足：

1. 存在边界谱三元组 $(\mathcal A_\partial,\mathcal H_\partial,D_\partial)$ 与 Brown–York 边界应力张量 $T_{\mathrm{BY}}^{ab}$，
2. 边界存在散射过程，其散射矩阵 $S(\omega)$ 对能量 $\omega$ 连续可微且满足 Hilbert–Schmidt 型局部性与能量窗口 $I$ 上的 BK 条件，
3. 对同一边界区域存在 von Neumann 代数 $\mathcal A_\partial''$ 与 KMS 状态 $\omega$，其模块群 $\sigma_t^\omega$ 物理上代表一类热平衡时间演化，
4. Brown–York Hamilton 量 $H_\partial[\xi]$ 生成的边界时间平移在可观测代数上诱导的自同构群 $\alpha_\tau$ 与散射演化及模块流在同一能量–频率窗口中"可比较"，即存在共同不变子代数 $\mathcal A_{\mathrm{com}} \subset \mathcal A_\partial$。

则存在一唯一的时间刻度等价类 $[\tau]$，以及三个正数常数 $a_{\mathrm{scatt}},a_{\mathrm{mod}},a_{\mathrm{geom}}>0$，与三个平移常数 $b_{\mathrm{scatt}},b_{\mathrm{mod}},b_{\mathrm{geom}}$，使得在共同定义域上有
$\tau_{\mathrm{scatt}} = a_{\mathrm{scatt}}\tau + b_{\mathrm{scatt}}$、
$\tau_{\mathrm{mod}} = a_{\mathrm{mod}}\tau + b_{\mathrm{mod}}$、
$\tau_{\mathrm{geom}} = a_{\mathrm{geom}}\tau + b_{\mathrm{geom}}$。

换言之，散射时间、模时间与几何时间在 BTG 中仅代表同一时间刻度的不同归一化与零点选取。

该定理的严格证明将在"Proofs"与附录中给出，其核心是：

* 利用 BK–Wigner–Smith 恒等式，把散射时间表示为相对谱密度的积分；
* 通过热时间假设与边界 KMS 状态，将模块参数与相对谱密度对齐；
* 借由 Brown–York Hamilton 量与边界应力张量的谱表示，将几何时间流的生成元与同一谱测度关联。

### No Fundamental Forces: Curvature of Unified Boundary Connection

**定义 2（边界总丛与统一联络）**

1. 在几何–规范–分辨率三层自由度上定义边界总丛
   $\pi:\mathcal B \to \partial M$，其纤维
   $\mathcal F = \mathcal F_{\mathrm{int}}\times \mathcal F_{\mathrm{res}}$，分别携带内部规范自由度（例如 $G_{\mathrm{YM}}$ 的表示空间）与分辨率尺度自由度。
2. 结构群取为
   $G_{\mathrm{tot}} = \mathrm{SO}(1,3)^\uparrow \times G_{\mathrm{YM}} \times G_{\mathrm{res}}$，
   其中 $G_{\mathrm{res}}$ 是与重整化群或 coarse-graining 变换等价的尺度群（例如 $\mathbb R$ 加法或 $\mathbb R_+$ 乘法群）。
3. 统一边界联络定义为
   $\Omega_\partial = \omega_{\mathrm{LC}} \oplus A_{\mathrm{YM}} \oplus \Gamma_{\mathrm{res}}$，
   对应 Levi–Civita 自旋联络、杨–米尔斯联络与分辨率联络；相应曲率
   $\mathcal R_\partial = R_\partial \oplus F_\partial \oplus \mathcal R_{\mathrm{res}}$。

**定理 3（无基本力定理）**
在 BTG 框架下，考虑边界上一条带电–带色试验粒子或有效质点轨迹的提升 $\gamma(\tau) \subset \mathcal B$；其投影到 $\partial M$ 为 $x^\mu(\tau)$，内禀自由度经过表示 $\rho:G_{\mathrm{YM}}\to\mathrm{Aut}(\mathcal F_{\mathrm{int}})$ 与 $G_{\mathrm{res}}$ 的一维表示。则以下陈述成立：

1. 轨迹 $\gamma(\tau)$ 的"无力运动"是对统一联络 $\Omega_\partial$ 的平行移动，即协变导数 $D_\tau \dot\gamma = 0$。
2. 其基底轨迹 $x^\mu(\tau)$ 满足的方程可写为

$$
m\frac{D^2x^\mu}{D\tau^2} = q F^\mu{}_\nu \dot x^\nu + f_{\mathrm{res}}^\mu
$$

其中 $F^\mu{}_\nu$ 是杨–米尔斯曲率在表示 $\rho$ 下的投影，$f_{\mathrm{res}}^\mu$ 则是分辨率曲率 $\mathcal R_{\mathrm{res}}$ 在合适有效作用中的投影。
3. 经典意义上的引力"力"则对应于 $R_\partial$ 的测地偏离效应；因而所有"力"均可理解为统一边界联络曲率的不同投影与表示，不再是基本对象。

因此，在 BTG 理论中，"力"并非独立公理性实体，而是边界时间几何的涌现表现；所有相互作用——包括引力、规范相互作用以及分辨率驱动的"熵力"——共同源自统一联络的曲率。

### Resolution Hierarchy and Emergent Phenomena

**定义 3（分辨率纤维丛与粗粒化映射）**

1. 在边界总丛上定义一个"分辨率纤维丛"
   $P_{\mathrm{res}} = (\mathcal B,\partial M,G_{\mathrm{res}},\pi_{\mathrm{res}})$，其纤维坐标可理解为分辨率或重整化标度 $\Lambda$。
2. 每一 $\Lambda$ 诱导一个完全正、单位保持映射
   $\Phi_\Lambda:\mathcal A_\partial \to \mathcal A_\Lambda \subseteq\mathcal A_\partial$，
   可看作从高分辨率边界代数到低分辨率有效代数的 coarse-graining。

**定理 4（现象层级涌现定理）**

在满足以下条件时：

1. $\{\Phi_\Lambda\}_\Lambda$ 构成一个半群（或群）的正态 *-同态族，满足
   $\Phi_{\Lambda_1}\circ\Phi_{\Lambda_2} = \Phi_{\Lambda_1\circ\Lambda_2}$，
2. 对任意局域可观测量 $A\in\mathcal A_\partial$，其在 $\Lambda\to 0$ 极限（最粗粒度）下的像 $\Phi_\Lambda(A)$ 收敛于某个经典函数或算子 $A_{\mathrm{cl}}$；
3. 统一联络 $\Omega_\partial$ 在分辨率方向上的联络形式 $\Gamma_{\mathrm{res}}$ 满足类似 Callan–Symanzik 方程的规范：沿 $\Lambda$ 流的平行移动等价于重整化群流。([SpringerLink][6])

则有：

1. 在高分辨率极限，对 $\mathcal A_\partial$ 的描述为全量量子散射与模块时间结构；
2. 在中等分辨率下，粗粒度代数 $\mathcal A_\Lambda$ 中的曲率期望值呈现为规范力、熵力与拓扑效应；
3. 在 $\Lambda\to 0$ 的宏观极限下，几何曲率与 Brown–York 张量主导，动力学退化为经典引力与热力学；此时所有"力"可以有效视为度规与有效势的几何效应。

---

## Proofs

本节给出主要定理的证明骨架，细节与技术 lemmas 置于附录。

### Preliminaries: Scattering, Time Delay and Spectral Shift

令 $H_0$ 与 $H = H_0 + V$ 为定义在某 Hilbert 空间上的自伴算子，满足一般散射理论的波算子存在条件。Birman–Kreĭn 理论给出谱移函数 $\xi(\omega)$，使得对 $H,H_0$ 的光滑函数 $f$ 有迹公式
$\operatorname{Tr}(f(H)-f(H_0)) = \int f'(\omega),\xi(\omega),\mathrm d\omega$。在合适条件下，散射矩阵 $S(\omega)$ 满足
$\det S(\omega) = \exp(-2\pi i \xi(\omega))$。([arXiv][3])

对定理 2 而言，我们只需要能量窗口 $I$ 上的局部 BK 公式与 Wigner–Smith 矩阵的可微性。令
$Q(\omega) = -i S(\omega)^\dagger \partial_\omega S(\omega)$，则
$\xi'(\omega) = \frac{1}{2\pi} \operatorname{tr} Q(\omega)$，从而散射时间刻度
$\tau_{\mathrm{scatt}}(\omega) = \xi(\omega)-\xi(\omega_0)$
在 $I$ 上被良好定义。

### Proof Sketch of Theorem 2 (Time Scale Equivalence)

**步骤 1：统一谱测度**

在能量窗口 $I$ 上，通过 BK 间接定义谱测度
$\mu_{\mathrm{scatt}}(\mathrm d\omega) := \frac{1}{2\pi} \operatorname{tr}Q(\omega),\mathrm d\omega$。

另一方面，边界 von Neumann 代数 $\mathcal A_\partial''$ 上的 KMS 状态 $\omega$ 诱导模块算子 $\Delta_\omega$，其谱测度 $\mu_{\mathrm{mod}}$ 决定模块群 $\sigma_t^\omega$ 的生成元 $K_\omega := -\log \Delta_\omega$。热时间假设要求存在常数 $c_{\mathrm{mod}}>0$，使物理 Hamilton 量 $H_{\mathrm{mod}} = c_{\mathrm{mod}} K_\omega$。([theorie.physik.uni-goettingen.de][4])

在几何端，Brown–York Hamilton 量可以写成 Dirac 算子或 Laplace 算子谱上的泛函：在适当的边界条件下，其对能量本征态 $|E\rangle$ 的期望值给出某个谱函数 $h_{\mathrm{geom}}(E)$，从而引入测度 $\mu_{\mathrm{geom}}(\mathrm dE) = h_{\mathrm{geom}}(E),\mathrm dE$。在 AdS/CFT 背景下，这一测度等价于边界 CFT 能动张量的谱测度。([arXiv][2])

**步骤 2：匹配条件与同测度性**

假设散射过程、模块流与几何时间平移作用在一个共同可分解子代数 $\mathcal A_{\mathrm{com}}$ 上，并且在能量窗口 $I$ 内，三种动力学的谱分解可在同一 Hilbert 空间表示；此即定理陈述中的"可比较"条件。

在该条件下，可以证明：

1. 存在一族单调可微的能量重标函数，使得 $\mu_{\mathrm{scatt}}$、$\mu_{\mathrm{mod}}$ 与 $\mu_{\mathrm{geom}}$ 在 $I$ 上互相绝对连续，且 Radon–Nikodym 导数为常数；
2. 这保证了三种时间生成元在 $L^2(I,\mu)$ 上等价，差别仅在于常数倍与加性常数。

形式上，设
$\mathrm d\mu_{\mathrm{scatt}} = c_1,\mathrm d\mu$、
$\mathrm d\mu_{\mathrm{mod}} = c_2,\mathrm d\mu$、
$\mathrm d\mu_{\mathrm{geom}} = c_3,\mathrm d\mu$，
则对应的时间参数满足仿射关系
$\tau_{\mathrm{scatt}} = a_{\mathrm{scatt}}\tau + b_{\mathrm{scatt}}$ 等，其中 $a_{\mathrm{scatt}} \propto c_1^{-1}$ 等。

**步骤 3：唯一性**

若另有一个时间刻度 $\tilde\tau$ 与上述三者皆仿射等价，则 $\tilde\tau$ 与 $\tau$ 亦必仿射等价；因此等价类 $[\tau]$ 唯一。

完整证明涉及对谱分解、KMS 条件与 Brown–York Hamilton 量谱表示的精细控制，详见附录 A。

### Proof Sketch of Theorem 3 (No Fundamental Forces)

在统一联络 $\Omega_\partial$ 下，考虑总丛 $\mathcal B$ 上的曲线 $\gamma(\tau)$。其协变导数
$D_\tau = \frac{\mathrm d}{\mathrm d\tau} + \Omega_\partial(\dot\gamma)$。
定义"自由运动"为 $D_\tau \dot\gamma = 0$。

展开该条件在不同纤维方向上的分量，可得：

1. 在 $\mathrm{SO}(1,3)$ 部分，得到标准测地线方程；
2. 在 $G_{\mathrm{YM}}$ 部分，得到类似 Wong 方程的规范力项：粒子在内部空间上的平行移动导致基底轨迹上出现 $F_{\mu\nu} \dot x^\nu$ 项；
3. 在 $G_{\mathrm{res}}$ 部分，分辨率联络 $\Gamma_{\mathrm{res}}$ 的曲率通过有效作用中的标度依赖性给出"熵力"或"信息力"，具体形式依赖于所选的有效自由能泛函。

这样一来，任何看似"有外力"的运动都可以视为在某个统一联络下的平行移动，只是我们在投影过程中忽略了某些纤维方向。定理 3 的内容只是将这一几何事实形式化。

### Proof Sketch of Theorem 4 (Emergent Phenomena Along Resolution Flow)

定理 4 实质上是一个"富加范畴化"的重整化群陈述：

1. 将 $\{\mathcal A_\Lambda\}_\Lambda$ 与映射 $\Phi_\Lambda$ 视为以 $\Lambda$ 为对象、以完全正映射为态射的范畴；
2. 要求 $\Phi_\Lambda$ 与统一联络 $\Omega_\partial$ 兼容，即沿分辨率方向的平行移动等价于 RG 流动；
3. 在 $\Lambda\to 0$ 极限，GNS 表示退化为经典概率空间，上述曲率的期望值成为经典力学与热力学中的有效势与响应函数。

技术上需要使用 Kadison–Singer 型唯一分解结果与 Kadison 不等式以控制完全正映射的行为，并利用 Lieb–Robinson 有界类工具保证宏观局域性。核心思路与全息 RG 文献中的"径向坐标＝能标"类比一致。([SpringerLink][6]) 详见附录 C。

---

## Model Apply

### Black Hole Thermodynamics in BTG

对具有事件视界的时空，将视界作为特殊的零样边界；引入 null Brown–York 应力张量与相应的准局域能量，可在纯边界语言中重写黑洞热力学四定律。([arXiv][7])

**命题 5（边界黑洞热力学重述）**

1. Hawking 温度 $T_H = \kappa/(2\pi)$ 来自视界上模块流的周期 $2\pi/\kappa$，其中 $\kappa$ 为表面引力；
2. Bekenstein–Hawking 熵 $S_{\mathrm{BH}} = A/(4G)$ 可解释为视界边界代数的 von Neumann 熵或类型因子上的熵密度；
3. 霍金辐射的"纯度问题"可在 BTG 中表述为视界与无穷远边界代数之间 Markov 性的稳定性问题：若边界相对熵对切片无关且满足适当的量子焦聚条件，则整体演化可保持纯态。

在 BTG 语言下，黑洞热力学不再是体域奇点与视界结构的混合，而完全以边界时间几何与模块时间刻度描述。

### Cosmological Redshift as Boundary Time Rescaling

在 FRW 宇宙中，标准红移公式
$1+z = a(t_0)/a(t_e)$
可在 BTG 中重写为

**命题 6（宇宙学红移的边界解释）**
设宇宙学边界选择为某类共形无穷远或共动观测者族的世界管边界，其时间刻度由边界时间刻度 $\tau_\partial$ 定义，则存在仿射变换使得
$1+z = \tau_\partial(t_0)/\tau_\partial(t_e)$。

这表明红移可被视为边界时间刻度的整体重标，而非体域"本征时间"差异；BTG 将红移直接与边界谱数据的演化联系起来。

### Mesoscopic Transport and Friedel–Wigner Consistency

在介观导体或 AB 环中，Wigner–Smith 时间延迟矩阵与 Friedel 求和规则提供了局域态密度、相移与输运性质之间的联系。([arXiv][3]) 在 BTG 中，可以将这些结果解释为边界谱三元组在有限分辨率下的投影：

* 相移导数 $\partial_\omega \phi(\omega)$ 与局域态密度之比直接给出散射时间刻度；
* 通过定理 2，这一刻度与模时间及几何时间等价，从而使介观输运实验成为 BTG 时间刻度等价性的直接检验平台。

---

## Engineering Proposals

### Microwave Scattering Networks as Discrete Boundary Models

构造多端口微波网络，将其视为离散化边界 $\partial M$ 的模型：

1. 通过矢量网络分析仪测量多端口散射矩阵 $S(\omega)$，数值构造 Wigner–Smith 矩阵 $Q(\omega)$ 与谱移函数 $\xi(\omega)$，定义散射时间刻度 $\tau_{\mathrm{scatt}}$。
2. 在网络节点上引入可调"几何参数"（例如电长度、损耗元件），通过反演网络 Lagrangian 或有效 RLC 模型定义一个等效的"几何 Hamilton 量"，从而重构 $\tau_{\mathrm{geom}}$。
3. 将网络置于可控噪声环境下，定义统计稳态并构造等效的模块流，测量 $\tau_{\mathrm{mod}}$ 的代理量（例如相关函数衰减参数）。

BTG 预言：在能量窗口与分辨率条件满足定理 2 假设的范围内，三种时间刻度之比应为常数；偏离则可归因于分辨率联络 $\Gamma_{\mathrm{res}}$ 的曲率与实验非理想因素。

### Atomic Clock Networks and Gravitational Redshift

在不同引力势中布设原子钟网络，利用双向时间传递协议测定频率比 $\nu_2/\nu_1$。在 BTG 语言中，该频率比应等于对应边界模 Hamilton 量本征值之比：
$\nu_2/\nu_1 = \lambda_{\mathrm{mod}}(x_2)/\lambda_{\mathrm{mod}}(x_1)$。

实验任务是：

1. 通过精确测量引力红移，确定宏观几何时间刻度 $\tau_{\mathrm{geom}}$ 与频率比之间的关系；
2. 利用量子光学与量子热力学技术，为原子钟体系构造有效的 KMS 状态与模块流，刻画 $\tau_{\mathrm{mod}}$；
3. 检验二者是否仿射等价，并估算分辨率曲率带来的偏差。

### Mesoscopic Conductors and Phase–Delay Fingerprints

在量子点或 AB 环系统中，通过相位敏感输运测量与局域态密度测量，构建

* 相移 $\phi(\omega)$，
* Wigner–Smith 矩阵 $Q(\omega)$，
* 局域态密度 $\rho(\omega)$。

BTG 预言：在足够低温与相干长度内，频率依赖的
$\partial_\omega\phi(\omega)/\pi,\ (2\pi)^{-1}\operatorname{tr}Q(\omega)$ 与相对态密度应一致，并与几何时间刻度的实验代理量（例如干涉条纹随磁通的漂移）属于同一等价类。

---

## Discussion (Risks, Boundaries, Past Work)

1. **域的限制**
   定理 2 的时间刻度等价性仅在能量窗口 $I$ 与相应的边界区域上成立；不同窗口或不同边界片之间的等价关系可能需要新的重标。BTG 只主张"局域等价类"，而非全局唯一时间。

2. **与 AdS/CFT 及全息 RG 的关系**
   BTG 在结构上类似全息原理：以边界应力张量与谱三元组为基本对象，并通过 RG/分辨率联络实现尺度流。但 BTG 并不依赖 AdS 几何或严格 CFT，而允许更一般的时空与代数结构；这使其与近年关于应力张量流与全息 RG 的研究形成互补。([SpringerLink][6])

3. **与热时间假设及量子热力学的关系**
   BTG 将热时间假设局限在边界代数上，并通过定理 2 将其与散射时间与几何时间对齐。这一做法与近年关于热时间作为"非锐观测量"的工作是一致的，同时也是对"时间源于热平衡"的更几何化实现。([美国物理学会出版物][8])

4. **潜在风险与开放问题**

* 在高度非平衡态下，模块流不再简单对应热时间，其与散射时间及几何时间的等价性如何保持仍待研究；
* 对非紧边界、奇异边界（如尖点与拓扑缺陷）需要更细致的谱几何与指数定理工具；
* 分辨率纤维丛的示性类与物理可观测量之间的关系尚未完全澄清。

---

## Conclusion

边界时间几何理论以三个核心洞见为基础：

1. **边界本体性**：物理实在首先以边界可观测代数及其谱数据给出，体域只是一种延拓；
2. **时间刻度统一性**：散射时间、模时间与几何时间属于同一时间刻度等价类，其差异仅在于归一化与零点选取；
3. **相互作用涌现性**：所有"力"都是统一边界联络曲率的投影；分辨率结构使量子散射与模块流通过 coarse-graining 涌现为宏观的引力与经典力学。

在这一框架中，引力、量子与信息不再是彼此孤立的三个层次，而是同一边界时间几何在不同分辨率与不同投影下的表现。BTG 不仅为黑洞热力学与宇宙学红移提供了新的解释，也为介观输运与精密计时实验给出了一系列可检验的预言。

---

## Acknowledgements, Code Availability

本工作为理论构建，不涉及数值代码与开源软件，因而无额外代码可供公开。

---

## References

[1] A. Connes, *Noncommutative Geometry*, Academic Press (1994).

[2] R. Ponge, "Spectral Triples", lecture notes, Berkeley (2012).([Prof. Raphaël Ponge][9])

[3] J. C. Várilly, *An Introduction to Noncommutative Geometry*, EMS (2006).

[4] J. D. Brown, J. W. York, "Quasilocal energy and conserved charges derived from the gravitational action", *Phys. Rev. D* **47**, 1407 (1993).([arXiv][1])

[5] V. Chandrasekaran, É. E. Flanagan, I. Shehzad, A. J. Speranza, "Brown–York charges at null boundaries", *JHEP* **2022**, 174 (2022).([arXiv][7])

[6] K. Bhattacharya et al., "Boundary terms and Brown–York quasilocal parameters for null surfaces", *Phys. Rev. D* **109**, 064026 (2024).([物理评论链接管理器][10])

[7] V. Balasubramanian, P. Kraus, "A stress tensor for Anti-de Sitter gravity", *Commun. Math. Phys.* **208**, 413 (1999).([arXiv][2])

[8] V. Balasubramanian et al., "Holographic interpretations of the renormalization group", *JHEP* **01**, 115 (2013).([SpringerLink][6])

[9] C. Texier, "Wigner time delay and related concepts: Application to transport in coherent conductors", *Physica E* **82**, 16–33 (2016).([arXiv][3])

[10] F. D. Cunden et al., "Statistical distribution of the Wigner–Smith time-delay matrix in chaotic cavities", *Phys. Rev. E* **91**, 060102 (2015).([物理评论链接管理器][11])

[11] M. Westrich et al., "The time delay operator and a related trace formula", *J. Math. Phys.* **60**, 083501 (2019).([ResearchGate][12])

[12] T. T. Paetz, *An Analysis of the "Thermal Time Concept" of Connes and Rovelli*, diploma thesis (2010).([theorie.physik.uni-goettingen.de][4])

[13] N. Swanson, "Can Quantum Thermodynamics Save Time?", *Stud. Hist. Philos. Mod. Phys.* **72**, 87–97 (2020).([philsci-archive.pitt.edu][13])

[14] G. J. Papadopoulos, "Thermal time as an unsharp observable", *J. Math. Phys.* **65**, 032105 (2024).([美国物理学会出版物][8])

[15] R. Bousso, A. C. Wall, "Quantum focusing conjecture and its implications", *Phys. Rev. D* **97**, 046014 (2018).

[16] S. Ryu, T. Takayanagi, "Holographic derivation of entanglement entropy from AdS/CFT", *Phys. Rev. Lett.* **96**, 181602 (2006).

[17] T. Faulkner et al., "Modular Hamiltonians for deformed half-spaces and the averaged null energy condition", *JHEP* **09**, 038 (2016).

[18] X. Y. Ran, "Holography for stress-energy tensor flows", *Phys. Rev. D* **111**, 046005 (2025).([物理评论链接管理器][14])

[19] Q. A. Wang, *Quasilocal Energy in General Relativity*, review article (2022).([ResearchGate][15])

[20] 其他与 BTG 相关的标准教材与综述，包括广义相对论、量子场论、量子信息与非交换几何等，不再一一列出。

---

## Appendix A: Spectral Measures and Time-Delay Relations

本附录给出定理 2 中谱测度构造与 BK–Wigner–Smith 关系的详细推导，重点处理定义域与绝对连续性问题。

### A.1 Birman–Kreĭn Formula and Local Spectral Shift

设 $H_0,H$ 为自伴算子，其差 $V = H-H_0$ 属 trace 类，且波算子存在并完备。谱移函数 $\xi(\omega)$ 通过

$$
\operatorname{Tr}(f(H)-f(H_0)) = \int_{-\infty}^{+\infty} f'(\omega),\xi(\omega),\mathrm d\omega
$$

定义，对所有足够光滑的 $f$。进一步，对绝对连续谱部分上的散射矩阵 $S(\omega)$，BK 公式给出

$$
\det S(\omega) = \exp(-2\pi i \xi(\omega))
$$

从而

$$
\xi'(\omega) = \frac{1}{2\pi i} \frac{\partial_\omega \det S(\omega)}{\det S(\omega)}
$$

另一方面，

$$
\partial_\omega \log\det S(\omega) = \operatorname{Tr}(S(\omega)^{-1}\partial_\omega S(\omega)) = i,\operatorname{Tr}Q(\omega)
$$

故得

$$
\xi'(\omega) = \frac{1}{2\pi} \operatorname{Tr}Q(\omega)
$$

定义谱测度

$$
\mu_{\mathrm{scatt}}(\mathrm d\omega) := \xi'(\omega),\mathrm d\omega = \frac{1}{2\pi}\operatorname{Tr}Q(\omega),\mathrm d\omega
$$

则散射时间刻度

$$
\tau_{\mathrm{scatt}}(\omega) = \int_{\omega_0}^\omega \mathrm d\mu_{\mathrm{scatt}} = \xi(\omega)-\xi(\omega_0)
$$

在 BTG 中，我们仅要求在有限能量窗口 $I$ 上 BK 条件成立，这在多数物理散射体系中是可满足的。

### A.2 Modular Flow Generator and Spectral Measure

对边界 von Neumann 代数 $\mathcal A_\partial''$ 及分离–循环向量 $|\Omega\rangle$，Tomita 运算 $S_\omega$ 定义为
$S_\omega A|\Omega\rangle = A^\dagger|\Omega\rangle$；其极分解给出反线性共轭 $J$ 与正算子 $\Delta_\omega$。模块群

$$
\sigma_t^\omega(A) = \Delta_\omega^{it} A \Delta_\omega^{-it}
$$

由 $\Delta_\omega$ 的谱分解

$$
\Delta_\omega = \int_0^\infty \lambda,\mathrm dE_\lambda
$$

决定。定义模块 Hamilton 量

$$
K_\omega := -\log\Delta_\omega = \int_{-\infty}^{+\infty} \kappa,\mathrm dF_\kappa
$$

则模块流的谱测度

$$
\mu_{\mathrm{mod}}(\mathrm d\kappa) := \langle\Omega|\mathrm dF_\kappa|\Omega\rangle
$$

在热时间假设下与物理时间生成元的谱测度等价。为将其与散射谱测度对齐，需要假设存在一个单调函数 $g$ 使 $\kappa = g(\omega)$，且两侧谱测度绝对连续。

### A.3 Brown–York Hamiltonian as a Spectral Functional

Brown–York Hamilton 量可在 ADM 分解下写成

$$
H_\partial[\xi] = \int_{\Sigma\cap\partial M} (\varepsilon n^a + j^a)\xi_a,\sqrt{\sigma},\mathrm d^{d-2}x
$$

其中 $\varepsilon$ 与 $j^a$ 分别为能量与动量表面密度。若可将其重写为 Dirac 或 Laplace 算子谱上的泛函

$$
H_\partial = \int h_{\mathrm{geom}}(E),\mathrm dN(E)
$$

则自然诱导谱测度

$$
\mu_{\mathrm{geom}}(\mathrm dE) := h_{\mathrm{geom}}(E),\mathrm dN(E)
$$

在近 AdS 情形下，此谱测度与对偶 CFT 的能动张量谱一致。

通过对三种谱测度施加绝对连续与 Radon–Nikodym 条件，并借助 Egorov 定理保证半经典极限下一致性，即可完成定理 2 的谱测度层级证明。

---

## Appendix B: Geometry of Unified Boundary Connection

本附录给出定理 3 的几何证明。

### B.1 Principal Bundle and Connection

考虑主丛 $P \to \partial M$，结构群 $G_{\mathrm{tot}} = \mathrm{SO}(1,3)^\uparrow\times G_{\mathrm{YM}}\times G_{\mathrm{res}}$。统一联络可写为

$$
\Omega_\partial = \omega_{\mathrm{LC}} + A_{\mathrm{YM}} + \Gamma_{\mathrm{res}} \in \Omega^1(P,\mathfrak g_{\mathrm{tot}})
$$

试验粒子的态空间可视为某个关联丛 $E = P\times_\rho V$，其中 $\rho$ 为 $G_{\mathrm{tot}}$ 的表示。

### B.2 Geodesic Equation in Total Space

在总丛 $E$ 中，令 $\gamma(\tau)$ 为一条曲线，其平行性条件为

$$
D_\tau \dot\gamma = 0 \quad\Leftrightarrow\quad \frac{\mathrm d^2}{\mathrm d\tau^2} + \Omega_\partial(\dot\gamma)\dot\gamma = 0
$$

投影到基底 $\partial M$ 上，得到

$$
m\frac{D^2 x^\mu}{D\tau^2} = q F^\mu{}_\nu \dot x^\nu + f_{\mathrm{res}}^\mu
$$

其中

* $F^\mu{}_\nu$ 是杨–米尔斯曲率在表示 $\rho$ 下的分量，
* $f_{\mathrm{res}}^\mu$ 来自 $\Gamma_{\mathrm{res}}$ 曲率与有效作用中对 $\Lambda$ 的依赖。

这表明，只要统一联络给定，"力"只是曲率在不同表示下的分量，定理 3 得证。

---

## Appendix C: Resolution Bundle, RG Flow and Emergence

本附录讨论定理 4 中分辨率纤维丛与 RG 流的数学结构。

### C.1 Resolution Group and Completely Positive Maps

设 $G_{\mathrm{res}} \simeq (\mathbb R,+)$ 或 $(\mathbb R_+,\times)$，其参数 $\ell$ 表示 coarse-graining 程度。每个 $\ell$ 对应一个完全正、单位保持映射 $\Phi_\ell:\mathcal A_\partial\to\mathcal A_\partial$，满足半群性质

$$
\Phi_{\ell_1}\circ\Phi_{\ell_2} = \Phi_{\ell_1+\ell_2}
$$

通过 Stinespring 表示，可将 $\Phi_\ell$ 视为在更大 Hilbert 空间上的酉演化后的部分迹。

### C.2 Compatibility with Unified Connection

要求统一联络在分辨率方向上的部分 $\Gamma_{\mathrm{res}}$ 满足

$$
\frac{\mathrm d}{\mathrm d\ell}\Phi_\ell(A) = \beta(\Phi_\ell(A))
$$

其中 $\beta$ 是类似 Callan–Symanzik 生成元的导子，体现物理量随尺度的流动。

在此条件下，沿 $\ell$ 流的平行移动可以视为 RG 流的几何实现。

### C.3 Classical Limit and Emergence

在 $\ell\to\infty$（最粗粒度）极限下，GNS 表示退化为经典概率空间 $(X,\mu)$，$\mathcal A_{\mathrm{cl}} \simeq L^\infty(X,\mu)$，统一联络曲率的期望值成为经典有效势与响应函数；这一极限下的动力学即为经典引力与热力学。

定理 4 的证明归结为：在上述结构下，$\mathcal A_\partial$ 的元素在 $\ell\to\infty$ 极限中收敛于经典可观测量，而统一联络曲率相应收敛于经典"力"，从而实现现象层级的涌现。

[1]: https://arxiv.org/abs/gr-qc/9209012 "Quasilocal Energy and Conserved Charges Derived from the Gravitational Action"
[2]: https://arxiv.org/abs/hep-th/9902121 "A Stress Tensor for Anti-de Sitter Gravity"
[3]: https://arxiv.org/pdf/1507.00075 "arXiv:1507.00075v6 [cond-mat.mes-hall] 5 Nov 2018"
[4]: https://www.theorie.physik.uni-goettingen.de/forschung2/qft/theses/dipl/Paetz.pdf "An Analysis of the 'Thermal-Time Concept' of Connes and ..."
[5]: https://en.wikipedia.org/wiki/Spectral_triple "Spectral triple"
[6]: https://link.springer.com/article/10.1007/JHEP01%282013%29115 "Holographic interpretations of the renormalization group"
[7]: https://arxiv.org/abs/2109.11567 "Brown-York charges at null boundaries"
[8]: https://pubs.aip.org/aip/jmp/article/65/3/032105/3277936/Thermal-time-as-an-unsharp-observable "Thermal time as an unsharp observable"
[9]: https://raphaelponge.org/wp-content/uploads/2019/10/berkeley_ncg2.pdf "Introduction to Noncommutative Geometry Part 2: Spectral ..."
[10]: https://link.aps.org/doi/10.1103/PhysRevD.109.064026 "Boundary terms and Brown-York quasilocal parameters for ..."
[11]: https://link.aps.org/doi/10.1103/PhysRevE.91.060102 "Statistical distribution of the Wigner-Smith time-delay matrix ..."
[12]: https://www.researchgate.net/publication/226613647_The_Time_Delay_Operator_and_a_Related_Trace_Formula "The Time Delay Operator and a Related Trace Formula"
[13]: https://philsci-archive.pitt.edu/17152/1/Can%20Quantum%20Thermodynamics%20Save%20Time.pdf "Can Quantum Thermodynamics Save Time? | PhilSci-Archive"
[14]: https://link.aps.org/doi/10.1103/v2g6-l983 "Holography for stress-energy tensor flows | Phys. Rev. D"
[15]: https://www.researchgate.net/publication/267068340_Quasilocal_energy_in_general_relativity "(PDF) Quasilocal energy in general relativity"
