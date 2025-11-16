# 强 CP 问题与轴子在统一矩阵–QCA 宇宙中的拓扑–散射解

---

## Abstract

Quantum chromodynamics (QCD) in its most general form admits a topological $\theta$-term $\theta\, g_s^2(32\pi^2)^{-1} G_{\mu\nu}^a \tilde G^{a,\mu\nu}$, which violates $P$, $T$ and $CP$. After chiral field redefinitions, the physically observable strong $CP$ angle is $\bar\theta=\theta-\arg\det(Y_u Y_d)$, where $Y_u$ and $Y_d$ are the up- and down-type Yukawa matrices. Naturalness suggests $\bar\theta=\mathcal O(1)$, while neutron electric dipole moment (nEDM) bounds $|d_n|\lesssim 1.8\times 10^{-26}\,e\cdot\mathrm{cm}$ imply $|\bar\theta|\lesssim 10^{-10}$, constituting the strong $CP$ problem.

Peccei–Quinn (PQ) theory promotes $\bar\theta$ to a dynamical vacuum expectation value of an axion field. The axion potential is determined by the QCD topological susceptibility $\chi_{\mathrm{top}}$, with $m_a^2 f_a^2=\chi_{\mathrm{top}}$ and $V(a)\simeq \chi_{\mathrm{top}}[1-\cos(a/f_a-\bar\theta_0)]$. Lattice QCD and chiral effective theory now determine $\chi_{\mathrm{top}}(T)$ with high precision, fixing the QCD axion mass–coupling relation. However, in a broader unified description of the Universe, the origin and robustness of PQ symmetry against gravity, ultraviolet physics and global consistency conditions remain unclear.

Within the unified time-scale, boundary time geometry, matrix universe THE-MATRIX and quantum cellular automaton (QCA) universe framework, this work gives a topological–scattering solution of the strong $CP$ problem. The main ideas are:

1. Introduce a parameter space $X^\circ$ of all low-energy couplings (gauge couplings, $\theta$-angles, Yukawa phases, light scalar parameters) and an extended space $Y=M\times X^\circ$, where $M$ is spacetime. From the family of scattering matrices $S(\omega;\lambda)$ on a channel Hilbert space, construct a determinant line bundle $\mathcal L_{\mathrm{det}}\to Y$ and its square root $\mathcal L_{\mathrm{det}}^{1/2}$. The obstruction to a global smooth square root is encoded in a relative cohomology class $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$, which has the physical meaning of the global $\mathbb Z_2$ holonomy of the "square-root scattering determinant" $\sqrt{\det_p S}$ along parameter loops.

2. Using the previously developed Null–Modular double cover and restricted unitary bundle framework, one has an equivalence between: (i) local Einstein equations with appropriate quantum energy conditions, (ii) small causal diamond generalized entropy extremality and modular flow consistency, and (iii) vanishing of the obstruction class, $[K]=0$. Thus, in any Universe admitting a globally consistent boundary time geometry and semiclassical gravity, allowed physical sectors must satisfy $[K]=0$.

3. Embed QCD and its $\theta$-angle into this unified structure by identifying the QCD sector contribution $[K_{\mathrm{QCD}}]$ of $[K]$. The physical strong $CP$ angle $\bar\theta=\theta-\arg\det(Y_u Y_d)$ reappears as the phase holonomy of $\sqrt{\det_p S_{\mathrm{QCD}}}$ along loops in $X^\circ$. One shows that $[K_{\mathrm{QCD}}]=0$ is equivalent to the triviality (modulo $2\pi$) of all such holonomies; in particular, in any physically realized sector compatible with $[K]=0$ one has $\bar\theta_{\mathrm{eff}}\approx 0$ without requiring a vanishing quark mass.

4. In the matrix universe representation, the global Universe is a gigantic but structured unitary matrix whose block-sparse pattern encodes causal relations and whose spectral data encode the unified time-scale. In this picture, $\bar\theta$ is a "topological phase" of the QCD block of THE-MATRIX, and $[K]=0$ requires that the square-root determinant has trivial $\mathbb Z_2$ holonomy across all coupling loops. Strong $CP$ is then rephrased as the requirement that such topological scattering invariants vanish globally.

5. In the QCA universe layer, one constructs an $SU(3)$ gauge QCA with lattice topological charge $Q\in\mathbb Z$. The QCD $\theta$-term corresponds to a weight factor $\exp(\mathrm i\theta Q)$ in the discrete path-sum. By imposing a "topological–Null–Modular consistent QCA" condition that the total phase for all closed gauge-configuration histories be $2\pi\mathbb Z$, one obtains in the continuum limit a joint constraint on $\bar\theta$ and possible gravitational $\theta_G$-terms, thereby simultaneously suppressing strong and gravitational $CP$ violation.

6. The PQ axion is reinterpreted as a relative cohomology modulus of $[K]$. The axion field $a(x)/f_a$ parametrizes local rephasings of $\sqrt{\det_p S}$ along a $U(1)$ fiber of $\mathcal L_{\mathrm{det}}^{1/2}$. Its effective action reproduces the standard form $S[a]\sim\int[\tfrac12 f_a^2 (\partial a)^2+\chi_{\mathrm{top}}(1-\cos(a/f_a-\bar\theta_0))]\sqrt{-g}\,\mathrm d^4x$, where $\chi_{\mathrm{top}}$ is the QCD topological susceptibility determined from first-principles QCD. The global condition $[K]=0$ then enforces $\langle a\rangle/f_a=\bar\theta_0$ and $\bar\theta_{\mathrm{eff}}=0$, giving a unified topological–scattering reformulation of the PQ mechanism.

Appendices present standard QCD derivations of $\bar\theta$, the precise construction of $[K]$ from scattering theory, and explicit $SU(3)$ gauge QCA models with discrete topological charge and $\theta$-phase. The resulting picture treats strong $CP$ as a consistency constraint of the full matrix–QCA Universe rather than an independent fine-tuning of a low-energy parameter.

---

## Keywords

强 $CP$ 问题；QCD 轴子；Peccei–Quinn 机制；拓扑易感；散射行列式线丛；矩阵宇宙；量子元胞自动机；Null–Modular 双覆盖

---

## Introduction & Historical Context

### 强 $CP$ 问题的提出

四维 $SU(3)$ Yang–Mills 理论允许在拉氏量中加入拓扑项

$$
\mathcal L_\theta = \theta\,\frac{g_s^2}{32\pi^2} G_{\mu\nu}^a \tilde G^{a,\mu\nu},\quad
\tilde G^{a,\mu\nu}=\tfrac12\epsilon^{\mu\nu\rho\sigma}G^a_{\rho\sigma}.
$$

空间–时间积分将该项转化为拓扑电荷 $Q\in\mathbb Z$ 与角度 $\theta$ 的乘积，显式破坏 $P$、$T$ 与 $CP$。对含多代夸克的 QCD，引入 Yukawa 矩阵 $Y_u,Y_d$ 后，考虑手征重定义与异常效应，物理上可观测的强 $CP$ 角为

$$
\bar\theta = \theta - \arg \det(Y_u Y_d),
$$

其自然取值范围为 $[0,2\pi)$。

若没有额外对称或动力学机制，$\bar\theta$ 应为 $\mathcal O(1)$。然而 $\bar\theta\neq 0$ 将诱导中子电偶极矩 $d_n$，QCD 求和规则与手征有效理论给出

$$
d_n \simeq c_n \bar\theta\, e\cdot\mathrm{cm},\quad c_n\sim 10^{-16}.
$$

最新 nEDM 实验给出 $|d_n|<1.8\times 10^{-26}\,e\cdot\mathrm{cm}$ 的上界，从而

$$
|\bar\theta|\lesssim 10^{-10},
$$

即所谓强 $CP$ 问题：为何一个自然应为 $\mathcal O(1)$ 的角被微调到 $10^{-10}$ 量级。

### 传统解法与 QCD 轴子

强 $CP$ 问题的传统解法大致分为几类：

1. 上夸克质量为零：若 $m_u=0$，可通过手征旋转移除 $\bar\theta$。格点 QCD 已基本排除这一可能。

2. $P$ 或 $CP$ 为基本对称，在高能尺度自发破缺：真空选择 $\bar\theta=0$。这类模型需处理自发 $CP$ 破缺后诱导的 nEDM，并面临量子引力中离散对称的刻画问题。

3. Peccei–Quinn 机制：引入全局 $U(1)_{\mathrm{PQ}}$ 对称与标量场，其异常结构使得 QCD 真空能依赖于某个角场 $a/f_a$，并在真空能最小点自动调节 $\bar\theta_{\mathrm{eff}}=0$，对应的近似 Goldstone 模即 QCD 轴子。原始 PQ 模型已被实验排除，但 KSVZ、DFSZ 等"隐匿轴子"模型仍为主流方案。

在 PQ 框架下，轴子有效势由 QCD 拓扑易感系数 $\chi_{\mathrm{top}}$ 决定：

$$
V(a) \simeq \chi_{\mathrm{top}}\bigl[1-\cos(a/f_a - \bar\theta_0)\bigr],
\quad m_a^2 f_a^2 = \chi_{\mathrm{top}}.
$$

格点 QCD 与手征有效理论已经给出 $\chi_{\mathrm{top}}(T)$ 的高精度结果，从而精确定出 QCD 轴子质量与耦合常数的关系。

### 统一宇宙框架与问题重述

上述解法多在低能有效场论层面处理强 $CP$ 问题，而未将其嵌入包含引力、因果结构、边界时间几何与宇宙整体一致性的统一框架。另一方面，量子引力与黑洞热力学表明：全局对称在量子引力中可能被破坏，传统 PQ 机制中全局 $U(1)_{\mathrm{PQ}}$ 的稳定性存在疑问。

此前工作中引入了统一时间刻度、边界时间几何、矩阵宇宙 THE-MATRIX 与 QCA 宇宙的多层对象，将宇宙刻画为一个在散射、几何、模流、广义熵与因果偏序之间高度一致的单一结构。核心要点包括：

1. 统一时间刻度母式

   $$
   \kappa(\omega) = \frac{\varphi'(\omega)}{\pi}
   = \rho_{\mathrm{rel}}(\omega)
   = (2\pi)^{-1} \operatorname{tr} Q(\omega),
   $$

   将散射半相位导数、相对态密度与 Wigner–Smith 群延迟矩阵迹统一为单一时间密度。

2. 边界时间几何与 Null–Modular 双覆盖，将模流参数与散射相位在每个因果菱形边界上粘合，从而几何、熵与散射三者互相约束。

3. 矩阵宇宙 THE-MATRIX 与 QCA 宇宙刻画，将宇宙整个演化视为巨大 but 稀疏结构的酉矩阵或可逆 QCA，块结构编码因果偏序，谱数据实现时间刻度，反馈闭环承载 $\mathbb Z_2$ 拓扑。

在这一框架下，强 $CP$ 问题可以被重述为：在全宇宙的拓扑–散射不变量中，QCD 扇区贡献的那一部分为何被压制到近乎零。本文将展示，这一压制不再是"低能常数微调"，而是"统一宇宙拓扑–散射一致性"的强制结果。

---

## Model & Assumptions

本节给出本文所用统一宇宙结构、参数空间、散射行列式线丛与 QCD 扇区嵌入的模型与基本假设。

### 宇宙对象与参数空间

设宇宙的几何层由一个全局双曲洛伦兹流形 $(M,g)$ 描述，带有因果偏序与适当的边界结构（包括过去、未来无穷远与可能的黑洞视界等）。在此基础上，引入统一宇宙对象的若干层次：

* 几何层 $U_{\mathrm{geo}}$：$(M,g,\prec)$；

* 散射层 $U_{\mathrm{scat}}$：一族散射对与统一时间刻度 $\kappa(\omega)$；

* 边界层 $U_{\mathrm{BTG}}$：边界代数、模流与 Brown–York 准局域能量；

* 矩阵层 $U_{\mathrm{mat}}$：通道 Hilbert 空间上的散射矩阵宇宙 THE-MATRIX；

* QCA 层 $U_{\mathrm{QCA}}$：定义在可数晶格上的 SU(3) 规 QCA；

* 拓扑层 $U_{\mathrm{top}}$：相对上同调类 $[K]$ 与 Null–Modular 双覆盖。

为引入耦合参数，定义一个开参数空间 $X^\circ$，其坐标包括：

1. 规范耦合常数 $g_s,g,g'$ 等；

2. Yukawa 矩阵及 CKM/PMNS 相位的参数化；

3. QCD $\theta$-角、可能的引力 $\theta_G$ 角与其它拓扑项参数；

4. 轻标量（包括可能的轴子）与外部宏观参数。

定义扩展空间

$$
Y = M \times X^\circ,
$$

其边界 $\partial Y$ 包含时空边界与参数空间的可能边界。

### 散射矩阵族与行列式线丛

在适当的局域性与谱假设下，对每个参数点 $\lambda\in X^\circ$ 与能量 $\omega$，考虑一个散射对 $(H_0,H(\lambda))$ 及其波算子，得到通道 Hilbert 空间 $\mathcal H_{\mathrm{chan}}(\omega)$ 上的散射矩阵

$$
S(\omega;\lambda):\mathcal H_{\mathrm{chan}}(\omega)\to \mathcal H_{\mathrm{chan}}(\omega).
$$

假设 $S(\omega;\lambda)-\mathbf 1$ 为适当阶的迹类算子，使得修正行列式 $\det{}_p S(\omega;\lambda)$ 有定义并随 $(\omega,\lambda)$ 平滑变化（在谱隙与适当重正化下）。

由 $(\omega,\lambda)\in Y$ 向量丛 $\mathcal H_{\mathrm{chan}}$ 的这一族酉算子，可以构造一个复线丛 $\mathcal L_{\mathrm{det}}\to Y$，其纤维由形式上的"行列式"生成：

$$
\mathcal L_{\mathrm{det}}|_{(\omega,\lambda)}
\cong \mathbb C\cdot \det{}_p S(\omega;\lambda).
$$

局域上可以选取对数相位 $\phi(\omega,\lambda)$ 使得

$$
\det{}_p S(\omega;\lambda)=\exp\bigl(\mathrm i \phi(\omega,\lambda)\bigr).
$$

定义平方根线丛 $\mathcal L_{\mathrm{det}}^{1/2}$ 为形式上满足

$$
(\mathcal L_{\mathrm{det}}^{1/2})^{\otimes 2}
\simeq \mathcal L_{\mathrm{det}}.
$$

局部可以选取 $\sqrt{\det{}_p S} = \exp(\tfrac{\mathrm i}{2}\phi)$，但在全局上可能存在符号多值性。该多值性的 $\mathbb Z_2$ 扭结由相对上同调类

$$
[K]\in H^2(Y,\partial Y;\mathbb Z_2)
$$

刻画：$[K]=0$ 当且仅当存在在 $\partial Y$ 上平凡的全局平方根线丛。

这一构造可视作 Freed 等人关于行列式线丛与上同调障碍的散射版推广。

### Null–Modular 双覆盖与一致性条件

边界时间几何将每个小因果菱形 $D\subset M$ 的边界 $\partial D$ 装配上：

1. 边界可观测代数 $\mathcal A_\partial(D)$ 及其状态 $\omega_\partial(D)$；

2. 模流参数 $s\in\mathbb R$ 及模算子 $\Delta^{\mathrm i s}$；

3. 由散射矩阵 $S_D(\omega)$ 与 Wigner–Smith 群延迟 $Q_D(\omega)$ 给出的相位 $\varphi_D(\omega)$ 与时间刻度 $\kappa_D(\omega)$。

Null–Modular 双覆盖将模流参数与散射相位通过一个 $\mathbb Z_2$ 覆盖粘合，使得模流方向、时间箭头与相位单值性一致，避免"半圈反号"异常。此前工作表明，在局域 Einstein 方程、QNEC/QFC 与散射–模流一致性的假设下，下列条件等价：

1. 存在全局 Null–Modular 双覆盖，使得所有因果菱形的模流与散射相位在该覆盖上平滑对齐；

2. 每个因果菱形的广义熵极值条件与二阶相对熵非负等价于局域引力场方程；

3. 行列式平方根线丛的相对上同调类满足 $[K]=0$。

因此，对一个可接受的物理宇宙扇区而言，$[K]=0$ 并非任选，而是一致性要求。

### QCD 扇区与 $\bar\theta$ 的嵌入

在 QCD 扇区，考虑 SU(3) 规场 $A_\mu^a$ 与六味夸克 $\psi_f$，拉氏量包含

$$
\mathcal L_{\mathrm{QCD}} = -\tfrac14 G_{\mu\nu}^a G^{a,\mu\nu}
+ \bar\psi(i\gamma^\mu D_\mu)\psi
- (\bar u_L Y_u u_R + \bar d_L Y_d d_R + \mathrm{h.c.})
+ \theta \frac{g_s^2}{32\pi^2}G_{\mu\nu}^a \tilde G^{a,\mu\nu}.
$$

手征重定义与 Fujikawa 异常分析给出物理角

$$
\bar\theta = \theta - \arg\det(Y_u Y_d),
$$

在路径积分中出现在权因子 $\exp(\mathrm i\bar\theta Q)$ 中。

将 QCD 扇区视作矩阵宇宙 THE-MATRIX 的一个块，对每个参数 $\lambda$ 与能量 $\omega$ 有散射矩阵 $S_{\mathrm{QCD}}(\omega;\lambda)$。该族在参数空间上的行列式与平方根在 $[K]$ 中定义贡献 $[K_{\mathrm{QCD}}]$，其物理含义是：沿着参数空间中包含 $\bar\theta$ 变化的闭合回路，$\sqrt{\det_p S_{\mathrm{QCD}}}$ 是否发生不可消除的符号翻转。

### SU(3) 规 QCA 宇宙层

在 QCA 层构造 SU(3) 规 QCA：晶格顶点携带物质 Hilbert 空间，边携带规链接变量 $U_{x,\mu}\in SU(3)$，离散时间演化由局域规协变酉门 $U_{\mathrm{QCA}}$ 实现。离散拓扑电荷 $Q\in\mathbb Z$ 可通过格点上的 $\operatorname{Tr}(U_P \tilde U_P)$ 求和定义。

在这一设置中，QCD $\theta$-项对应于在离散路径和中加入相位因子

$$
\prod_n \exp\bigl(\mathrm i\theta Q_n\bigr),
$$

或在 Heisenberg 图像中写作 $U_{\mathrm{QCA}}(\theta)=\exp(\mathrm i\theta \hat Q) U_{\mathrm{QCA}}(0)$。拓扑–Null–Modular 一致性要求对任何闭合规构型回路，总相位为 $2\pi\mathbb Z$，这将在后文被用来约束 $\bar\theta$。

---

## Main Results (Theorems and Alignments)

本节将统一矩阵–QCA 宇宙框架下关于强 $CP$ 问题与轴子的主要结论形式化为若干定理与推论，证明置于附录。

### 定理 1（行列式平方根与相对上同调类）

在前述散射与参数空间假设下，散射矩阵族 $S(\omega;\lambda)$ 定义了一个复线丛 $\mathcal L_{\mathrm{det}}\to Y$，其纤维由修正行列式 $\det{}_p S(\omega;\lambda)$ 生成。存在一个自然的相对上同调类

$$
[K]\in H^2(Y,\partial Y;\mathbb Z_2),
$$

其满足：

1. $[K]=0$ 当且仅当存在在 $\partial Y$ 上平凡的平方根线丛 $\mathcal L_{\mathrm{det}}^{1/2}$，使得 $(\mathcal L_{\mathrm{det}}^{1/2})^{\otimes 2}\cong \mathcal L_{\mathrm{det}}$；

2. 对任意闭合参数回路 $\gamma\subset X^\circ$，$[K]$ 在映射圆柱 $M\times S^1_\gamma$ 上的评值给出 $\sqrt{\det_p S}$ 沿 $\gamma$ 的 $\mathbb Z_2$ holonomy：若 holonomy 为 $+1$，则该回路上平方根可平滑选择；若为 $-1$，则存在不可消除的符号翻转。

### 定理 2（Null–Modular 一致性与 $[K]=0$）

设宇宙满足如下条件：

1. $M$ 全局双曲，存在适当的边界时间几何结构与模流；

2. 小因果菱形上的广义熵极值与二阶相对熵非负成立，并与局域引力场方程等价；

3. 边界散射矩阵与模流在 Null–Modular 双覆盖上可局部对齐。

则以下命题等价：

1. 存在全局 Null–Modular 双覆盖，使得所有因果菱形上的模流与散射相位在该覆盖上平滑对齐，无 $\mathbb Z_2$ 异常；

2. 存在在 $\partial Y$ 上平凡的全局平方根线丛 $\mathcal L_{\mathrm{det}}^{1/2}$；

3. $[K]=0$。

从而，对任何物理上可接受的宇宙扇区，$[K]=0$ 是必要条件。

### 定理 3（QCD $\bar\theta$ 作为散射–拓扑 holonomy）

在 QCD 扇区，定义物理角

$$
\bar\theta(\lambda) = \theta(\lambda) - \arg\det\bigl(Y_u(\lambda) Y_d(\lambda)\bigr),
$$

并考虑参数空间中的闭合回路 $\gamma\subset X^\circ$。则：

1. $[K_{\mathrm{QCD}}]$ 在 $M\times S^1_\gamma$ 上的评值等于 $\exp(\mathrm i\Delta_\gamma\bar\theta/2)$ 的符号，其中 $\Delta_\gamma\bar\theta$ 为沿 $\gamma$ 的总相位变化（模 $2\pi$）；

2. 若对所有物理上可实现的回路 $\gamma$ 都有 $\Delta_\gamma\bar\theta\equiv 0\pmod{2\pi}$，则 $[K_{\mathrm{QCD}}]=0$；

3. 反之，若存在某条回路上 $\Delta_\gamma\bar\theta\equiv \pi\pmod{2\pi}$，则 $[K_{\mathrm{QCD}}]\neq 0$。

特别地，在局域参数邻域内，$[K_{\mathrm{QCD}}]=0$ 要求可选定规范使得 $\bar\theta_{\mathrm{eff}}\equiv 0\pmod{2\pi}$。

### 推论 3.1（统一宇宙中的强 $CP$ 抑制）

假设宇宙满足定理 2 的假设，且非 QCD 扇区在 $[K]$ 中的贡献已由独立一致性条件约束为零，则 $[K]=0\Rightarrow [K_{\mathrm{QCD}}]=0$。从而：

1. 物理上可实现的宇宙扇区必须满足 $\bar\theta_{\mathrm{eff}}\equiv 0\pmod{2\pi}$；

2. 实验上观测到的 $|\bar\theta|\lesssim 10^{-10}$ 被解读为对 $[K_{\mathrm{QCD}}]$ 可能残余的敏感上界，而自然预期为严格零。

### 定理 4（轴子作为 $[K]$ 的相对上同调模）

假设 $[K]$ 提升为整数系数类 $\tilde K\in H^2(Y,\partial Y;\mathbb Z)$。令轴子场的相位

$$
\phi(x) = \exp\bigl(\mathrm i a(x)/f_a\bigr)\in U(1),
$$

并通过耦合

$$
\mathcal L_{aG\tilde G} = \frac{a}{f_a}\frac{g_s^2}{32\pi^2}G_{\mu\nu}^a \tilde G^{a,\mu\nu}
$$

将其嵌入 QCD。则：

1. $\phi$ 的变化可视为平方根线丛 $\mathcal L_{\mathrm{det}}^{1/2}$ 的局域重标度，$\tilde K$ 即该 $U(1)$ 线丛的第一 Chern 类；

2. 在低能有效理论中，轴子势可写为

   $$
   V(a) \simeq \chi_{\mathrm{top}}\bigl[1-\cos(a/f_a-\bar\theta_0)\bigr]+\cdots,
   $$

   其中 $\chi_{\mathrm{top}}$ 为 QCD 拓扑易感系数，$\bar\theta_0$ 为 UV 标架下的裸角；

3. 若统一宇宙要求 $[K]=0$，则在全局上需有 $\langle a\rangle/f_a=\bar\theta_0$，从而 $\bar\theta_{\mathrm{eff}}=\bar\theta_0-\langle a\rangle/f_a=0$。

这给出 PQ 机制在统一拓扑–散射框架中的重解释：轴子是真正消除 $[K]$ 的相对上同调模，其真空选择由 $[K]=0$ 强制，而非额外自由。

### 定理 5（SU(3) 规 QCA 中的 $\theta$–扇区与 $[K_{\mathrm{QCD}}]$）

在 SU(3) 规 QCA 模型中，设每个时间步的演化算子为

$$
U_{\mathrm{QCA}}(\theta) = \exp\bigl(\mathrm i\theta \hat Q\bigr)\, U_{\mathrm{QCA}}(0),
$$

其中 $\hat Q$ 为离散拓扑电荷算符。考虑所有可能规构型路径组成的离散路径空间 $\mathcal C$。

1. 对于任意闭合路径 $\mathcal C$，总相位

   $$
   \Phi(\mathcal C) = \theta \sum_{n\in\mathcal C} Q_n
   $$

   的符号（模 $2\pi$）与 $[K_{\mathrm{QCD}}]$ 在对应映射圆柱上的评值一致；

2. 若要求对所有物理可实现的闭合路径 $\mathcal C$ 有 $\Phi(\mathcal C)\in 2\pi\mathbb Z$，则离散模型中的有效 $\bar\theta_{\mathrm{eff}}\equiv 0\pmod{2\pi}$；

3. 连续极限下，该条件逼迫 QCD 扇区的 $[K_{\mathrm{QCD}}]=0$，与定理 3–4 的结论兼容。

---

## Proofs

本节给出主定理的证明思路与关键步骤，技术细节与严格构造置于附录。

### 定理 1 的证明概要

行列式线丛与平方根的上同调障碍是成熟课题，可通过以下方式获得：

1. 对每个 $(\omega,\lambda)$ 固定一组正交标准通道基，$S(\omega;\lambda)$ 的谱可写为 $\{e^{\mathrm i\delta_j(\omega,\lambda)}\}_j$，定义局域半相位

   $$
   \phi(\omega,\lambda) = \sum_j \delta_j(\omega,\lambda).
   $$

2. 在参数空间的一个开覆盖 $\{U_\alpha\}$ 上，选取连续分支 $\phi_\alpha$，定义局域截面 $s_\alpha=\exp(\mathrm i\phi_\alpha)$ 作为 $\mathcal L_{\mathrm{det}}$ 的局域平凡化。

3. 在交集 $U_\alpha\cap U_\beta$ 上，过渡函数 $g_{\alpha\beta}=s_\alpha/s_\beta$ 取值于 $U(1)$，其射影平方根 $h_{\alpha\beta}=\sqrt{g_{\alpha\beta}}$ 构成 $\mathcal L_{\mathrm{det}}^{1/2}$ 的候选过渡函数。

4. $h_{\alpha\beta}$ 是否可以选取使得三角一致条件 $h_{\alpha\beta} h_{\beta\gamma} h_{\gamma\alpha}=1$ 成立，正由一个 $\mathbb Z_2$ 值 Čech 2-余圈决定，对应于 $H^2(Y;\mathbb Z_2)$ 中的一个类。

5. 加入边界条件要求 $\partial Y$ 上平方根平凡，则得到相对上同调 $H^2(Y,\partial Y;\mathbb Z_2)$ 中的类 $[K]$，其零化即为全局平方根存在的充要条件。

沿闭合回路 $\gamma$ 的 holonomy 则由 $\phi$ 的净变化 $\Delta_\gamma\phi$ 决定，其符号为 $\exp(\mathrm i\Delta_\gamma\phi/2)$，与 $[K]$ 在 $M\times S^1_\gamma$ 上的评值一致。

### 定理 2 的证明概要

Null–Modular 双覆盖将边界模流参数 $s$ 与散射相位 $\phi(\omega,\lambda)$ 联系起来，使得对每个因果菱形 $D$：

1. 模流生成的时间平移与由 $\kappa(\omega)$ 定义的散射时间刻度在边界上一致；

2. 广义熵的二阶变分与二阶相对熵非负条件等价于局域 Einstein 方程。

若 $[K]\neq 0$，则存在某些闭合参数回路上 $\sqrt{\det_p S}$ 的 holonomy 为 $-1$，意味着在 Null–Modular 双覆盖上无法连续选择散射相位与模流相位的相对符号，从而在某些因果菱形的边界拼接时出现"反号"跳跃。这会破坏广义熵–引力方程的统一变分原理。

反之，若 $[K]=0$，则可在整个 $Y$ 上选择平滑的 $\sqrt{\det_p S}$，并在边界上将其与模流参数一一对应，从而构造无异常的 Null–Modular 双覆盖。模流、广义熵与散射相位的一致性保证了小因果菱形上的变分原理与 Einstein 方程等价。这给出定理 2 所述的等价性。

### 定理 3 与推论 3.1 的证明概要

在 QCD 扇区，物理角

$$
\bar\theta = \theta - \arg\det(Y_u Y_d)
$$

出现在路径积分权重 $\exp(\mathrm i\bar\theta Q)$ 中，其对散射矩阵行列式相位的贡献可视为

$$
\det{}_p S_{\mathrm{QCD}} \sim \sum_Q P(Q)\exp(\mathrm i\bar\theta Q)\det S_Q,
$$

其中 $P(Q)$ 为拓扑扇区权重，$\det S_Q$ 为固定 $Q$ 下的散射行列式。

沿着参数空间中的闭合回路 $\gamma$ 变化 $\lambda$，$\bar\theta$ 可能发生整数倍 $2\pi$ 的绕行。由于拓扑电荷 $Q\in\mathbb Z$，总相位变化为

$$
\Delta_\gamma\Phi = \Delta_\gamma\bar\theta\cdot \langle Q\rangle_\gamma + \cdots,
$$

其中 $\langle Q\rangle_\gamma$ 为沿回路的有效拓扑权重。模 $2\pi$ 考虑时，若 $\Delta_\gamma\bar\theta\equiv 0\pmod{2\pi}$，则可在该回路上选择连续的平方根，不产生符号翻转；若 $\Delta_\gamma\bar\theta\equiv \pi\pmod{2\pi}$，则平方根必然翻转一次，对应 $[K_{\mathrm{QCD}}]\neq 0$。

因此，$[K_{\mathrm{QCD}}]=0$ 等价于所有物理可实现回路上 $\Delta_\gamma\bar\theta\equiv 0\pmod{2\pi}$。若假定非 QCD 扇区贡献已由其他一致性条件压制为零，则 $[K]=0\Rightarrow [K_{\mathrm{QCD}}]=0$，由此得到推论 3.1：$\bar\theta_{\mathrm{eff}}\equiv 0\pmod{2\pi}$。

### 定理 4 的证明概要

轴子场 $a(x)$ 的相位 $\phi(x)=\exp(\mathrm i a(x)/f_a)$ 可视为 $\mathcal L_{\mathrm{det}}^{1/2}$ 上的 $U(1)$ 纤维坐标。其耦合

$$
\frac{a}{f_a}\frac{g_s^2}{32\pi^2}G\tilde G
$$

在路径积分中引入权重 $\exp(\mathrm i aQ/f_a)$，可理解为对 $\sqrt{\det_p S}$ 的局域重标度。

在手征有效理论与格点 QCD 中，QCD 真空能对 $\theta$ 的依赖由

$$
E_0(\theta) = E_0(0) + \tfrac12\chi_{\mathrm{top}}\theta^2 + \mathcal O(\theta^4)
$$

刻画，推广到轴子耦合即得到

$$
V(a) \simeq \chi_{\mathrm{top}}\bigl[1-\cos(a/f_a - \bar\theta_0)\bigr],
$$

其中 $\bar\theta_0$ 为 UV 标架下的裸角。

若 $[K]=0$，则存在全局平方根线丛；在轴子存在时，这一条件等价于要求 $\phi$ 的绕行与 $\bar\theta$ 的绕行相互抵消，从而真空必须满足

$$
\frac{\langle a\rangle}{f_a} = \bar\theta_0,
\quad \bar\theta_{\mathrm{eff}} = \bar\theta_0 - \frac{\langle a\rangle}{f_a}=0.
$$

因此 PQ 机制被重解释为：通过引入轴子场，将整数类 $\tilde K$ 的代表提升到平凡，消除 $[K]$ 的 $\mathbb Z_2$ 投影。

### 定理 5 的证明概要

在 SU(3) 规 QCA 模型中，拓扑电荷算符 $\hat Q$ 对每个离散配置 $\{U_{x,\mu}\}$ 取整数值。引入相位 $\exp(\mathrm i\theta \hat Q)$ 后，一步时间演化算子为

$$
U_{\mathrm{QCA}}(\theta) = \exp(\mathrm i\theta \hat Q)U_{\mathrm{QCA}}(0).
$$

对闭合规构型路径 $\mathcal C$，总相位为

$$
\Phi(\mathcal C) = \theta \sum_{n\in\mathcal C} Q_n.
$$

若要求对所有物理可实现路径 $\mathcal C$ 有 $\Phi(\mathcal C)\in 2\pi\mathbb Z$，则有效 $\theta_{\mathrm{eff}}\equiv 0\pmod{2\pi}$。将该条件映射到连续极限与散射行列式线丛上，即得 $[K_{\mathrm{QCD}}]=0$，与定理 3–4 的条件一致。

---

## Model Apply

本节将统一拓扑–散射框架应用于强 $CP$ 问题的若干具体量，特别是 nEDM 上界、QCD 拓扑易感与轴子参数空间。

### nEDM 上界与 $[K_{\mathrm{QCD}}]$ 的约束

在无轴子情形，中子电偶极矩与 $\bar\theta$ 的关系可写为

$$
d_n \simeq c_n \bar\theta\, e\cdot\mathrm{cm},
\quad c_n\simeq (2\text{--}3)\times 10^{-16},
$$

结合 $|d_n|<1.8\times 10^{-26}\,e\cdot\mathrm{cm}$ 得到

$$
|\bar\theta|\lesssim 10^{-10}.
$$

在统一宇宙视角中，$\bar\theta$ 不再是自由常数，而是 $[K_{\mathrm{QCD}}]$ 在某一局域参数坐标中的表示。若 $[K_{\mathrm{QCD}}]=0$，则存在规范使得 $\bar\theta_{\mathrm{eff}}\equiv 0\pmod{2\pi}$，从而 nEDM 自然为零（仅留电弱 CKM 贡献）。nEDM 上界被解释为对可能偏离 $[K]=0$ 的极高灵敏度检验，而非对一个任意 UV 参数的微调。

更具体地，假设由于未知 UV 或引力效应，存在极小但非零的 $[K_{\mathrm{QCD}}]$ 残余，使得在某些参数回路上 $\Delta_\gamma\bar\theta\sim \epsilon\ll 1$。则 nEDM 上界给出 $\epsilon\lesssim 10^{-10}$。由于上同调类为离散量，这一"近似零"更自然地被解读为严格零，而实验仅验证了这一点在 $10^{-10}$ 精度上成立。

### QCD 拓扑易感与轴子参数

格点 QCD 与手征有效理论给出 $T=0$ 时的拓扑易感近似为 $\chi_{\mathrm{top}}(0)\sim (75\,\mathrm{MeV})^4$，并在 $T\gg T_c$ 时呈现接近稀薄瞬子气体的温度标度。

轴子质量由

$$
m_a^2 f_a^2 = \chi_{\mathrm{top}}(0)
$$

决定，给出常用近似

$$
m_a \simeq 5.7\,\mu\mathrm{eV}
\left(\frac{10^{12}\,\mathrm{GeV}}{f_a}\right).
$$

轴子暗物质的丰度则依赖于 $\chi_{\mathrm{top}}(T)$ 在 $T\sim\mathrm{GeV}$ 附近的行为。

在统一拓扑–散射框架中，$\chi_{\mathrm{top}}$ 是 QCD 模态在统一时间刻度 $\kappa(\omega)$ 上某个二阶谱矩的具体数值，而 $f_a$ 则与平方根行列式线丛 $\mathcal L_{\mathrm{det}}^{1/2}$ 的"惯性"有关。定理 4 表明，这些量不仅受 QCD 内部动力学约束，还必须与 $[K]=0$ 一致。特别地：

1. 过低的 $f_a$ 会使得轴子在早期宇宙中形成的大尺度拓扑缺陷在 Null–Modular 几何中引入不可接受的 holonomy，从而违背 $[K]=0$；

2. 过高的 $f_a$ 则可能导致轴子相位在宇宙尺度上无法充分均匀，从而在某些因果菱形上出现有效 $\bar\theta\neq 0$ 的区域，破坏局域熵–引力一致性。

因此，本框架为轴子参数空间施加了除传统宇宙学与实验约束之外的"拓扑–散射"约束。

### 引力 $\theta_G$ 项与统一约束

类比 QCD 的 $G\tilde G$，引力扇区可能包含 $R\tilde R$ 类型的拓扑项，其角度记为 $\theta_G$。在统一框架中，该项也贡献于 $[K]$，与 QCD 扇区共同决定总类 $[K]=[K_{\mathrm{grav}}]+[K_{\mathrm{QCD}}]+\cdots$。

要求 $[K]=0$ 则给出 $\theta_G$ 与 $\bar\theta$ 的联合约束，暗示强 $CP$ 问题与"引力 $CP$ 问题"并非独立，而是统一拓扑扇区选择的不同投影。

---

## Engineering Proposals

本节讨论若干与统一拓扑–散射框架直接相关的实验与工程方案，包括 nEDM、轴子探测与 QCA 模拟。

### 下一代 nEDM 实验

当前最佳 nEDM 上界来自 PSI 等设施，$|d_n|<1.8\times 10^{-26}\,e\cdot\mathrm{cm}$，未来装置（如 n2EDM@PSI 等）目标灵敏度可达 $10^{-27}\text{--}10^{-28}\,e\cdot\mathrm{cm}$。

在统一框架下，这类实验不仅约束 $\bar\theta$，还可被理解为对 $[K_{\mathrm{QCD}}]$ 残余的直接探测。若在未来灵敏度下仍未观测到 nEDM，则强烈支持 $[K_{\mathrm{QCD}}]=0$ 与 $[K]=0$ 的精确成立。

### 轴子搜索与参数空间

多种轴子暗物质与轴子–光子耦合实验（共振腔、谐振 LC、电磁共振、光学干涉等）正在探索 $m_a\sim\mu\mathrm{eV}\text{--}\mathrm{meV}$ 区间。结合格点 QCD 对 $\chi_{\mathrm{top}}(T)$ 的结果，这些实验可在 $f_a\sim 10^{10}\text{--}10^{13}\,\mathrm{GeV}$ 区间内强约束 QCD 轴子。

统一拓扑–散射框架给出的额外结构预言包括：

1. 某些 $f_a$ 区间可能因 $[K]=0$ 与 Null–Modular 几何的要求而被排除或偏好；

2. 若未来观测到轴子信号，其质量–耦合关系应与 $\chi_{\mathrm{top}}$ 的散射–谱诠释一致。

这些预言可通过系统比较轴子实验结果与统一框架中的参数相关性来检验。

### QCA 模拟与拓扑试验台

在近中期量子工程层面，可构造 SU(2) 或 SU(3) 规 QCA 的量子模拟，利用有限规模量子计算平台实现：

1. 在二维或三维离散晶格上构造规协变 QCA 更新门，定义离散拓扑电荷 $Q$；

2. 引入可调 $\theta$-相位 $\exp(\mathrm i\theta Q)$，并测量闭合路径下总相位 $\Phi(\mathcal C)$ 的分布；

3. 测试在何种条件下可通过引入类轴子自由度或调整边界条件消除 $\Phi(\mathcal C)$ 的 $\mathbb Z_2$ 残余，实现离散版的 $[K]=0$。

这类量子模拟为"拓扑–散射强 $CP$ 解"的关键结构提供了实验试验台。

### 引力与宇宙学信号

若引力扇区存在 $\theta_G R\tilde R$ 项，其效应可能表现在：引力波偏振的微小异常、宇宙微波背景偏振的奇异旋转或其他宇宙学观测。统一框架暗示，这些效应与 QCD 扇区的 $\bar\theta$ 不可独立调节，应共同满足 $[K]=0$。因此，未来高精度引力波与宇宙学实验可从另一个角度检验本理论结构。

---

## Discussion (risks, boundaries, past work)

本节讨论本框架与既有强 $CP$ 解法的关系、可能的局限与开放问题。

### 与传统强 $CP$ 解法的关系

统一拓扑–散射框架将 PQ 机制、离散 $CP$/$P$ 对称方案与其它解决方案纳入单一图景：

1. PQ 机制在本框架中被解释为"引入轴子场来提升并消除 $[K]$ 的整数 lift"，其真空选择由 $[K]=0$ 强制，而非额外假设；

2. 将 $CP$ 或 $P$ 视为量子引力允许的规约离散对称时，近期工作表明这类离散对称方案并不必然失效。在统一框架中，这可解读为对 $[K]$ 的离散对称约束的一种实现；

3. 上夸克质量为零的方案可视为参数空间 $X^\circ$ 上一超曲面的特例，在该超曲面上 $\bar\theta$ 可通过手征旋转完全移除；但格点 QCD 数值已强烈不支持 $m_u=0$，从而该方案不再被视为可行。

本框架强调：真正的"强 $CP$ 解"不应仅仅是某一 UV 模型的构造，而是整个宇宙拓扑–散射结构的一致性。

### 局限性与风险

尽管本框架在结构上统一了若干层次，但仍存在显著局限与风险：

1. 严格数学证明层面，行列式线丛 $\mathcal L_{\mathrm{det}}$ 的构造通常在欧氏或静态背景下更为清晰，将其推广到带宇宙学边界与动态几何的洛伦兹背景需要额外工作；

2. Null–Modular 双覆盖与 $[K]=0$ 与 Einstein 方程、QNEC/QFC 等价的证明依赖于此前系列工作，严格性与适用范围需要进一步澄清；

3. $[K]$ 为离散上同调类，其与连续参数 $\bar\theta$ 的关系在本文中通过 holonomy 与绕行数给出，严格刻画需使用 mapping torus 与谱流理论的数学框架；

4. 量子引力效应可能在 Planck 尺度引入额外拓扑项或破坏全局结构，改变 $[K]$ 的定义空间；

5. 若未来实验观察到 $\bar\theta$ 显著非零或 nEDM 超出目前上界的信号，则需要重新审视本框架中关于 $[K]=0$ 的假设。

### 与既有文献的联系

强 $CP$ 问题与 QCD 轴子的综述、格点 QCD 计算与精确 QCD 轴子性质的研究，为本框架提供了低能输入与可检验的数值基础。近期关于离散规约 $CP$/$P$ 对称在量子引力背景下的讨论，则从另一角度支持"强 $CP$ 解应与全局拓扑结构相关"的观点。

---

## Conclusion

本文在统一时间刻度、边界时间几何、矩阵宇宙 THE-MATRIX 与 QCA 宇宙的框架下，对强 $CP$ 问题与轴子给出了一个拓扑–散射统一解：

1. 散射矩阵族定义的行列式线丛的平方根存在性由相对上同调类 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$ 控制；

2. Null–Modular 双覆盖与广义熵–引力变分一致性要求 $[K]=0$，从而宇宙必须位于无 $\mathbb Z_2$ holonomy 的拓扑扇区；

3. QCD 的物理角 $\bar\theta$ 被重写为 QCD 扇区散射行列式平方根在参数空间回路上的 holonomy 坐标，$[K_{\mathrm{QCD}}]=0$ 等价于所有物理回路上 $\bar\theta_{\mathrm{eff}}\equiv 0\pmod{2\pi}$；

4. PQ 轴子被解释为 $[K]$ 的相对上同调模，其有效势由 QCD 拓扑易感 $\chi_{\mathrm{top}}$ 决定，真空值 $\langle a\rangle/f_a=\bar\theta_0$ 被 $[K]=0$ 条件固定，从而在统一框架内重现 PQ 机制；

5. SU(3) 规 QCA 宇宙中的 $\theta$–相位实现了 $[K_{\mathrm{QCD}}]$ 的离散版本，拓扑–Null–Modular 一致性在离散层面要求所有闭合路径总相位为 $2\pi\mathbb Z$，从而在连续极限下将 $\bar\theta$ 压制到零。

这一图景将强 $CP$ 问题从"单一参数的微调"提升为"宇宙拓扑–散射结构的全局一致性问题"，并为 nEDM 实验、轴子探测与量子模拟提供了新的结构性预言与约束。

---

## Acknowledgements, Code Availability

作者感谢关于强 $CP$ 问题、QCD 轴子、拓扑易感与行列式线丛等主题的大量既有工作为本研究提供的基础。本文所有推导为解析工作，未使用数值代码，代码可用性不适用。

---

## References

1. R. D. Peccei, H. R. Quinn, "CP Conservation in the Presence of Pseudoparticles", Phys. Rev. Lett. 38, 1440 (1977).

2. R. D. Peccei, H. R. Quinn, "Constraints Imposed by CP Conservation in the Presence of Pseudoparticles", Phys. Rev. D 16, 1791 (1977).

3. C. A. Baker et al., "Improved Experimental Limit on the Electric Dipole Moment of the Neutron", Phys. Rev. Lett. 97, 131801 (2006).

4. B. Lauss et al., "Search for the Electric Dipole Moment of the Neutron with Next-Generation Experiments" (n2EDM, PSI reports and white papers).

5. V. V. Flambaum et al., "Interpreting Electric Dipole Moments", Les Houches Lectures (2023).

6. G. Grilli di Cortona, E. Hardy, J. P. Vega, G. Villadoro, "The QCD Axion, Precisely", JHEP 01 (2016) 034.

7. M. Gorghetto, G. Villadoro, "Topological Susceptibility and QCD Axion Mass: QED and NNLO Corrections", JHEP 03 (2019) 033.

8. J. Frison et al., "Topological Susceptibility at High Temperature on the Lattice", JHEP 09 (2016) 021.

9. P. Petreczky et al., "The Topological Susceptibility in Finite Temperature QCD and Axion Cosmology", Phys. Rev. D 92, 094503 (2015).

10. R. D. Peccei, "Axions: Theory, Cosmology, and Experimental Searches", Lect. Notes Phys. 741, 3–17 (2008).

11. C. Vafa, E. Witten, "Parity Conservation in QCD", Phys. Rev. Lett. 53, 535 (1984).

12. Recent discussions on discrete gauged $(CP/P)$ symmetries and the strong $CP$ problem, e.g. "Clearing up the Strong CP Problem", arXiv:2510.18951 (2025).

13. Reviews on QCD axion cosmology and lattice inputs, e.g. D. J. E. Marsh, "Axion Cosmology", Phys. Rept. 643, 1–79 (2016).

---

## 附录 A：QCD $\theta$-项、物理 $\bar\theta$ 与 nEDM 的标准推导

### A.1 单味情形

考虑单味夸克 QCD，拉氏量为

$$
\mathcal L
= -\tfrac14 G_{\mu\nu}^a G^{a,\mu\nu}
+ \bar\psi(i\gamma^\mu D_\mu - m e^{\mathrm i\theta'\gamma_5})\psi
+ \theta\frac{g_s^2}{32\pi^2}G_{\mu\nu}^a \tilde G^{a,\mu\nu}.
$$

作手征变换

$$
\psi \to \exp(\mathrm i\alpha\gamma_5/2)\psi,
$$

质量项相位变为 $\theta'\to\theta'-\alpha$，同时 Fujikawa 方法表明路径积分度量引入相位 $\exp(\mathrm i\alpha Q)$，等效于 $\theta\to\theta+\alpha$。因此组合

$$
\bar\theta = \theta+\theta'
$$

在量子理论中不变。通过选择 $\alpha=-\theta'$ 可将质量项变成实数，但此时所有 $CP$ 破缺都集中到拓扑项中：

$$
\mathcal L_\theta = \bar\theta\frac{g_s^2}{32\pi^2}G_{\mu\nu}^a \tilde G^{a,\mu\nu}.
$$

### A.2 多味情形

对多味夸克，引入 Yukawa 矩阵 $Y_u,Y_d$，质量项为

$$
\mathcal L_m = -\bar u_L Y_u u_R - \bar d_L Y_d d_R + \mathrm{h.c.}
$$

在味空间施加酉变换可对角化质量矩阵，但这些变换一般具有手征分量，对 $\theta$-项产生偏移。将所有手征旋转的影响累积，最终得到物理强 $CP$ 角为

$$
\bar\theta = \theta - \arg\det(Y_u Y_d).
$$

若不存在额外对称，$\bar\theta$ 为自由参数，取值于 $[0,2\pi)$。

### A.3 nEDM 与 $\bar\theta$ 的关系

使用手征扰动理论与 QCD 求和规则，可以计算 $\bar\theta$-项对中子 EDM 的贡献，得到

$$
d_n(\bar\theta)
\simeq c_n \bar\theta\, e\cdot\mathrm{cm},
\quad c_n\simeq (2\text{--}3)\times10^{-16}.
$$

结合实验上界 $|d_n|<1.8\times 10^{-26}\,e\cdot\mathrm{cm}$，得

$$
|\bar\theta| \lesssim 10^{-10}.
$$

这构成强 $CP$ 问题的定量表述。

---

## 附录 B：相对上同调类 $[K]$ 与散射行列式线丛的构造

### B.1 Čech 上同调与线丛扭结

令 $\{U_\alpha\}$ 为 $Y$ 的一个良好开覆盖。在每个 $U_\alpha$ 上选取散射行列式的相位分支 $\phi_\alpha$，定义局域截面

$$
s_\alpha(\omega,\lambda) = \exp\bigl(\mathrm i\phi_\alpha(\omega,\lambda)\bigr)
\in \mathcal L_{\mathrm{det}}|_{U_\alpha}.
$$

在交集 $U_\alpha\cap U_\beta$ 上，过渡函数为

$$
g_{\alpha\beta} = \frac{s_\alpha}{s_\beta}:U_\alpha\cap U_\beta\to U(1).
$$

$\{g_{\alpha\beta}\}$ 满足 Čech 一致性条件 $g_{\alpha\beta}g_{\beta\gamma}g_{\gamma\alpha}=1$，定义了 $\mathcal L_{\mathrm{det}}$。

尝试构造平方根线丛时，在 $U_\alpha\cap U_\beta$ 上需要选取 $h_{\alpha\beta}\in U(1)$，使得 $h_{\alpha\beta}^2=g_{\alpha\beta}$。由于 $g_{\alpha\beta}$ 可能绕行 $U(1)$，$h_{\alpha\beta}$ 的选取一般仅在局部可能统一。三重交集上的一致性条件为

$$
h_{\alpha\beta} h_{\beta\gamma} h_{\gamma\alpha} = \varepsilon_{\alpha\beta\gamma},
\quad \varepsilon_{\alpha\beta\gamma}=\pm 1.
$$

$\{\varepsilon_{\alpha\beta\gamma}\}$ 构成一个取值于 $\mathbb Z_2$ 的 Čech 2-余圈，其共边界类对应 $H^2(Y;\mathbb Z_2)$ 中的一个元素，即 $\mathcal L_{\mathrm{det}}^{1/2}$ 的扭结度量。若存在 $\{k_{\alpha\beta}=\pm 1\}$，使得

$$
\varepsilon_{\alpha\beta\gamma} = k_{\alpha\beta}k_{\beta\gamma}k_{\gamma\alpha},
$$

则可重定义 $h'_{\alpha\beta}=k_{\alpha\beta}h_{\alpha\beta}$ 以满足严格一致条件，平方根线丛存在；否则不存在。

### B.2 相对上同调与边界条件

若要求在边界 $\partial Y$ 上平方根平凡，则需要在 $\partial Y$ 上选取一族截面使得所有 holonomy 为 $+1$。这相当于在 Čech 复杂中引入相对条件，得到相对上同调群 $H^2(Y,\partial Y;\mathbb Z_2)$，其中 $[K]$ 的零化是"存在在边界上平凡的全局平方根"的充要条件。

将闭合参数回路 $\gamma$ 看作 $Y$ 中的一个 1-循环，其与 $[K]$ 的配对给出该回路上平方根 holonomy 的符号。映射圆柱 $M\times S^1_\gamma$ 上 $[K]$ 的评值正是这一 holonomy 的拓扑刻画。

---

## 附录 C：SU(3) 规 QCA 的离散拓扑电荷与 $\theta$-相位

### C.1 模型构造

考虑四维超立方晶格 $\Lambda\subset\mathbb Z^4$。对每个时刻 $t$，空间晶格为三维切片，边携带规链接变量 $U_{x,\mu}\in SU(3)$，顶点携带物质 Hilbert 空间 $\mathcal H_x$。定义总 Hilbert 空间为

$$
\mathcal H = \bigotimes_{x\in\Lambda} \mathcal H_x \otimes
\bigotimes_{\text{edges}} L^2(SU(3)).
$$

离散时间演化由有限深度局域酉门 $U_{\mathrm{QCA}}$ 实现，满足：

1. 规协变性：$U_{\mathrm{QCA}}$ 与局域规变换 $\{g_x\}\in SU(3)$ 按自然方式变换；

2. 有限传播：一次更新仅影响有限邻域；

3. 必要时，连续极限下逼近 Wilson 格点 QCD 动力学。

离散拓扑电荷 $Q$ 可通过四维闭合超立方体上 plaquette 的有向乘积的迹定义：

$$
Q = \frac{1}{32\pi^2}\sum_x \epsilon^{\mu\nu\rho\sigma}
\operatorname{Tr}\bigl(U_{x,\mu\nu} U_{x,\rho\sigma}\bigr),
$$

其中 $U_{x,\mu\nu}$ 为围绕 plaquette 的链接乘积。适当规约后 $Q\in\mathbb Z$。

### C.2 $\theta$-相位与闭合路径

定义包含 $\theta$-相位的 QCA 更新算子为

$$
U_{\mathrm{QCA}}(\theta) = \exp\bigl(\mathrm i\theta \hat Q\bigr)\, U_{\mathrm{QCA}}(0),
$$

其中 $\hat Q$ 为对态依赖的拓扑电荷算符。在离散路径和视角下，每一条规构型路径 $\mathcal C$ 的振幅含有因子

$$
\exp\Bigl(\mathrm i\theta \sum_{n\in\mathcal C} Q_n\Bigr).
$$

若要求所有物理可实现的闭合路径 $\mathcal C$ 的总相位为 $2\pi\mathbb Z$，则有效 $\theta$ 必须调节到使得 $\theta Q_{\mathrm{tot}}\in 2\pi\mathbb Z$。连续极限下，这一条件对应于 $\bar\theta_{\mathrm{eff}}\equiv 0\pmod{2\pi}$，与 $[K_{\mathrm{QCD}}]=0$ 等价。

---

## 附录 D：QCD $\bar\theta$ 作为 holonomy 的详细证明

（略述关键步骤）

1. 将 QCD $\theta$-真空 $|\theta\rangle = \sum_Q e^{\mathrm i\theta Q}|Q\rangle$ 视为参数 $\theta$ 的截面，拓扑电荷 $Q$ 为 $\pi_3(SU(3))$ 元素的整数指标。

2. 对于含 Yukawa 相位的完整参数空间 $\lambda\in X^\circ$，$\bar\theta(\lambda)$ 是 $\theta$ 与 $\arg\det(Y_u Y_d)$ 的组合。沿闭合回路 $\gamma\subset X^\circ$，$\bar\theta$ 的总变化 $\Delta_\gamma\bar\theta$ 与映射圆柱 $M\times S^1_\gamma$ 上的混合 Chern–Simons 项相关。

3. 散射行列式 $\det{}_p S_{\mathrm{QCD}}(\omega;\lambda)$ 对 $\bar\theta$ 的依赖可以在瞬子背景下通过半经典展开得到，其相位随 $\bar\theta$ 绕行整数圈的次数给出一个谱流数，与拓扑电荷累积 $\langle Q\rangle_\gamma$ 相关。

4. 将谱流理论与行列式线丛的 Chern 类联系起来，可证明 $[K_{\mathrm{QCD}}]$ 的 $\mathbb Z_2$ 投影等于 $\exp(\mathrm i\Delta_\gamma\bar\theta/2)$ 的符号，这给出定理 3 的严格版本。

---

## 附录 E：Null–Modular 双覆盖与 $[K]$ 的等价性

（略述关键步骤）

1. 在每个小因果菱形 $D$ 的边界 $\partial D$ 上，存在一族模流生成元 $K_D$ 与散射相位密度 $\kappa_D(\omega)$，二者通过刻度同一式联系。

2. Null–Modular 双覆盖可视为在每个 $\partial D$ 上选择一条将模流参数与散射相位联系起来的"相位线"，其双值性由 $\mathbb Z_2$ 控制。

3. 若 $[K]\neq 0$，则在某些闭合参数–几何回路上，试图在所有 $\partial D$ 上一致选择相位线会遭遇不可消除的符号翻转，从而在拼接因果菱形时引入不兼容的模流反号，破坏广义熵–引力方程的统一变分。

4. 反之，$[K]=0$ 时可在整个 $Y$ 上选择一致的平方根相位，使所有 Null–Modular 双覆盖的局域补丁在 Čech 意义下无缝拼接。结合 QNEC/QFC 与 Brown–York 能量的已知结果，可证明这与 Einstein 方程的成立等价。

以上给出本文主文中定理 2 的严格上同调与模流意义下的证明框架。

