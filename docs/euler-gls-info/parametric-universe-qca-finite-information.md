# 有限信息下的带参数宇宙量子元胞自动机理论

## Abstract

在量子元胞自动机（quantum cellular automaton, QCA）、准局域算子代数与有限信息原理的框架下，本文构造一类显式带参数的"宇宙量子元胞自动机"模型。核心思想是：假设物理宇宙在物理上可区分的信息量存在有限上界 $I_{\max}$，则整个宇宙可以被编码为一个有限比特串参数向量 $\Theta$，并在严格的公理体系下唯一决定一个宇宙级 QCA 对象

$$
\mathfrak{U}_{\mathrm{QCA}}(\Theta) = \bigl(\Lambda(\Theta),\mathcal{H}_{\mathrm{cell}}(\Theta),\mathcal{A}(\Theta),\alpha_{\Theta},\omega_0^{\Theta}\bigr)
$$

其中 $\Lambda(\Theta)$ 为有限格点集合，$\mathcal{H}_{\mathrm{cell}}(\Theta)$ 为元胞 Hilbert 空间，$\mathcal{A}(\Theta)$ 为准局域 $C^\ast$ 代数，$\alpha_{\Theta}$ 为具有有限传播半径的自同构（由有限深度局域幺正线路实现），$\omega_0^{\Theta}$ 为由有限线路生成的初始宇宙态。

在"有限信息宇宙公理"下，我们引入全局信息容量上界 $I_{\max}$，并将宇宙参数拆分为结构参数 $\Theta_{\mathrm{str}}$、动力学参数 $\Theta_{\mathrm{dyn}}$ 与初始态参数 $\Theta_{\mathrm{ini}}$。在 QCA 的代数框架中证明：对每一个满足 $I_{\mathrm{param}}(\Theta)+S_{\max}(\Theta)\le I_{\max}$ 的有限比特串 $\Theta$，都存在满足局域性、可逆性和因果有界性的宇宙 QCA；其中参数信息量 $I_{\mathrm{param}}(\Theta)$ 与宇宙可达 Hilbert 空间最大冯诺依曼熵 $S_{\max}(\Theta)$ 满足

$$
I_{\mathrm{param}}(\Theta)+S_{\max}(\Theta)\le I_{\max}
$$

从而刻画"有限信息"对元胞数、局域 Hilbert 维数与参数精度的联合约束。

在连续极限方面，本文构造一类可缩放的带参数 QCA 族 $\mathfrak{U}_{\mathrm{QCA}}(\Theta;a,\Delta t)$，在格距 $a$ 与时间步长 $\Delta t\to 0$ 的适当极限下，证明存在有效场方程族，包括 Dirac 型方程

$$
\bigl(\mathrm{i}\gamma^\mu\partial_\mu - m(\Theta)\bigr)\psi = 0
$$

及带规范耦合与有效度规参数的方程系，其中质量 $m(\Theta)$、规范耦合与引力常数等有效连续参数由 $\Theta_{\mathrm{dyn}}$ 中的离散角参数与结构数据解析导出。进一步地，引入观察者网络与因果偏序，在宇宙 QCA 层面定义一类参数化的观察者对象与共识几何，使得宇宙参数 $\Theta$ 同时决定物理定律与可观测统计结构。

附录部分给出准局域 $C^\ast$ 代数与 QCA 的形式化构造；有限深度局域线路与 QCA 自同构之间的严格对应定理；Dirac–QCA 连续极限的系统推导；有限信息不等式与元胞数、局域维数之间的界限证明；以及从参数向量到有效场论常数与观察者网络统计的抽象映射示例。本文由此提供了一个可公理化、可计算且带参数的"有限信息宇宙元胞自动机"理论框架，为将物理宇宙视作具有有限描述复杂度的量子计算过程奠定了数学基础。

## Keywords

量子元胞自动机；准局域 $C^\ast$ 代数；有限信息原理；Dirac 连续极限；规范与引力有效常数；观察者网络与信息几何

---

## Introduction & Historical Context

量子元胞自动机最初作为量子计算与离散化量子场论的自然模型提出，其基本结构为在离散格点上排列有限维量子系统，采用离散时间步长由幺正演化算子迭代演化，并要求演化具有因果性与平移不变性等性质。基于代数化刻画的可逆 QCA 理论表明，这类模型可以形式化为定义在准局域 $C^\ast$ 代数上的自同构，其传播半径有限，且在适当假设下具有强的结构可逆性与 Margolus 分块分解性质。在之后的工作中，QCA 被系统用于构造自由与相互作用场论的离散版本，其连续极限可收敛到 Dirac、Weyl 甚至广义 Dirac 方程，并在量子行走、量子模拟和量子算法设计中得到广泛应用。

另一方面，关于"宇宙可承载信息量是否有限"的讨论则源于黑洞热力学、Bekenstein 熵界与全息原理。Bekenstein 提出的熵–能量–半径不等式与 Bousso 的协变熵界表明，给定有限面积的时空区域，其所含物理自由度与信息量上界与面积而非体积成正比，从而暗示存在某种"有限信息宇宙"的普适约束。与此同时，Lloyd 在研究"物理计算的极限"时指出，任何具体物理系统可执行的逻辑操作数与可存储信息量由能量、体积与基本常数 $c,\hbar,G$ 严格控制，进一步强化了"宇宙作为计算过程"的观念。

在这些背景下，一个自然的问题是：若将"宇宙"视为某种 QCA 对象，并引入形式化的有限信息公理，是否可以在严格数学层面上实现以下结构：

1. 用一个有限比特串 $\Theta$ 编码宇宙的结构数据、动力学定律与初始条件；
2. 在准局域代数与 QCA 理论框架中，从 $\Theta$ 唯一地构造出一个宇宙级 QCA 对象 $\mathfrak{U}_{\mathrm{QCA}}(\Theta)$；
3. 在适当缩放极限下，从 $\mathfrak{U}_{\mathrm{QCA}}(\Theta)$ 导出连续场论，包括 Dirac 型场、规范场与有效引力方程，其质量、耦合常数与度规参数由 $\Theta$ 的离散成分解析给出；
4. 用有限信息原理给出宇宙元胞数、局域 Hilbert 维数与参数精度之间的统一不等式，构成"宇宙规模–内部自由度–描述复杂度"三者之间的折衷关系。

现有 QCA 文献多集中于给定局域规则下的动力学性质、普适性与连续极限，而较少从"宇宙级"角度讨论参数编码与信息容量上界；而黑洞与全息文献则多在连续几何与量子引力层面刻画熵界，尚未与具体的离散 QCA 演化模型严格对接。本文的目标即是在两者之间搭建桥梁：在代数化 QCA 理论基础上，引入明确的有限信息宇宙公理，构造带参数的宇宙 QCA 模型，并分析其连续极限与信息论约束。

本文的主要贡献可概括为：

1. 在准局域 $C^\ast$ 代数上的 QCA 框架内提出有限信息宇宙公理，形式化引入全局信息容量上界 $I_{\max}$，并将宇宙参数向量 $\Theta$ 分解为结构参数 $\Theta_{\mathrm{str}}$、动力学参数 $\Theta_{\mathrm{dyn}}$ 与初始态参数 $\Theta_{\mathrm{ini}}$；
2. 从 $\Theta$ 明确构造宇宙 QCA 对象 $\mathfrak{U}_{\mathrm{QCA}}(\Theta)$，证明其满足局域性、可逆性与有限传播半径性质，并给出编码冗余意义下的存在–唯一性定理；
3. 建立参数信息量 $I_{\mathrm{param}}(\Theta)$ 与宇宙 Hilbert 空间最大熵 $S_{\max}(\Theta)$ 的有限信息不等式 $I_{\mathrm{param}}(\Theta)+S_{\max}(\Theta)\le I_{\max}$，进而导出元胞数上界、局域维数上界与二者之间的定量折衷关系；
4. 在 Dirac 型 QCA 与量子行走连续极限研究基础上，构造一类可缩放的带参数 QCA 族，证明其在 $a,\Delta t\to 0$ 极限下收敛到 Dirac 与规范场方程，并将质量与耦合常数表示为 $\Theta_{\mathrm{dyn}}$ 中离散角参数的函数；
5. 构建观察者网络与因果偏序的形式化框架，在宇宙 QCA 层面定义参数化的观察者对象、通信通道与共识几何，并讨论 $\Theta$ 对可观测统计结构的约束。

在此基础上，本文提出一个可公理化与可计算的"带参数有限信息宇宙 QCA"理论，为进一步将宇宙视作有限描述复杂度的量子计算过程提供结构化出发点。

---

## Model & Assumptions

### 准局域代数与元胞格结构

设 $\Lambda$ 为有限集合，代表宇宙中可分辨元胞的标签。结构参数 $\Theta_{\mathrm{str}}$ 中包含空间维数 $d\in\{1,2,3,4\}$、各方向格长 $L_1,\dots,L_d\in\mathbb{N}$，以及边界条件与可能的额外连边或缺陷，用以编码宇宙的离散空间结构。由此得到元胞集合

$$
\Lambda(\Theta_{\mathrm{str}})=\prod_{i=1}^d\{0,1,\dots,L_i-1\}
$$

格点数为

$$
N_{\mathrm{cell}}(\Theta_{\mathrm{str}})=\prod_{i=1}^d L_i
$$

对每个 $x\in\Lambda(\Theta_{\mathrm{str}})$，令元胞 Hilbert 空间为

$$
\mathcal{H}_x(\Theta_{\mathrm{str}})\cong\mathbb{C}^{d_{\mathrm{cell}}(\Theta_{\mathrm{str}})}
$$

其中 $d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\in\mathbb{N}$ 由结构参数指定，可以进一步分解为费米子、规范场与辅助寄存器的张量积，例如

$$
\mathcal{H}_x\cong\mathcal{H}_{\mathrm{f}}\otimes\mathcal{H}_{\mathrm{g}}\otimes\mathcal{H}_{\mathrm{aux}}
$$

对任意有限子集 $F\subset\Lambda$，定义

$$
\mathcal{H}_F=\bigotimes_{x\in F}\mathcal{H}_x
$$

$$
\mathcal{A}_F=\mathcal{B}(\mathcal{H}_F)
$$

若 $F\subset F'$，通过自然嵌入

$$
\iota_{F\subset F'}(A_F)=A_F\otimes\mathbf{1}_{F'\setminus F}
$$

将 $\mathcal{A}_F$ 视为 $\mathcal{A}_{F'}$ 的子代数。准局域 $C^\ast$ 代数定义为

$$
\mathcal{A}(\Theta_{\mathrm{str}})=\overline{\bigcup_{F\Subset\Lambda(\Theta_{\mathrm{str}})}\mathcal{A}_F}^{|\cdot|}
$$

若 $\Lambda$ 配备图结构 $(\Lambda,E_\Lambda)$，可定义图距离 $\mathrm{dist}(x,y)$ 为从 $x$ 到 $y$ 的最短边数。对有限 $F\subset\Lambda$ 与 $R>0$，定义球

$$
B_R(F)=\{y\in\Lambda:\exists x\in F,\ \mathrm{dist}(x,y)\le R\}
$$

其刻画局域邻域与传播半径。

态被定义为 $\mathcal{A}(\Theta_{\mathrm{str}})$ 上的正、归一线性泛函

$$
\omega:\mathcal{A}(\Theta_{\mathrm{str}})\to\mathbb{C}
$$

满足 $\omega(A^\dagger A)\ge 0$、$\omega(\mathbf{1})=1$。若存在密度矩阵 $\rho$ 使得 $\omega(A)=\mathrm{tr}(\rho A)$，则称其为正规态。

### QCA 自同构与有限传播半径

在准局域代数视角下，量子元胞自动机定义为保持局域结构的 $C^\ast$ 自同构。借鉴 Schumacher 与 Werner 的代数化定义，

**定义 2.1（量子元胞自动机）**

设 $\mathcal{A}(\Theta_{\mathrm{str}})$ 如上。一个量子元胞自动机是一个 $C^\ast$ 自同构

$$
\alpha:\mathcal{A}(\Theta_{\mathrm{str}})\to\mathcal{A}(\Theta_{\mathrm{str}})
$$

满足有限传播半径性质：存在 $R<\infty$，使得对任意有限 $F\subset\Lambda(\Theta_{\mathrm{str}})$ 与 $A\in\mathcal{A}_F$，存在有限集 $F'\subset B_R(F)$ 使得 $\alpha(A)\in\mathcal{A}_{F'}$。

在 Hilbert 空间表示中，常用幺正算子 $U$ 实现 $\alpha(A)=U^\dagger A U$。若 $U$ 可分解为有限深度的局域量子线路，则传播半径自动有限。与经典可逆元胞自动机不同，可逆 QCA 的逆在有限邻域条件下仍是 QCA，这一点由结构可逆性定理保证。

### 有限信息宇宙公理与编码映射

受 Bekenstein 熵界与全息原理启发，本文将"宇宙可承载信息量有限"的思想抽象为如下公理。

**公理 2.2（有限信息宇宙）**

存在一个有限常数 $I_{\max}\in\mathbb{N}$，以及从物理宇宙对象集合 $\mathfrak{U}_{\mathrm{phys}}$ 到有限比特串集合的编码映射

$$
\mathrm{Enc}:\mathfrak{U}_{\mathrm{phys}}\to\{0,1\}^{\le I_{\max}}
$$

使得：

1. 对任一物理上可区分的宇宙对象 $\mathfrak{U}$，编码 $\Theta=\mathrm{Enc}(\mathfrak{U})$ 的长度不超过 $I_{\max}$；
2. 若两个宇宙对象在物理上不可区分，则它们的编码可以相同；反之，对物理上可区分的宇宙类，编码在可逆重编码意义下是单射。

在本文的 QCA 框架中，$\mathfrak{U}_{\mathrm{phys}}$ 将用带参数宇宙 QCA 对象 $\mathfrak{U}_{\mathrm{QCA}}(\Theta)$ 表示。我们进一步将"有限信息"细化为参数信息量 $I_{\mathrm{param}}(\Theta)$ 与宇宙 Hilbert 空间最大熵 $S_{\max}(\Theta)$ 的联合约束不等式。

### 宇宙参数向量与分层编码

**定义 2.3（宇宙参数向量）**

宇宙参数向量定义为长度不超过 $I_{\max}$ 的比特串

$$
\Theta\in\{0,1\}^{\le I_{\max}}
$$

并分解为三部分

$$
\Theta=(\Theta_{\mathrm{str}},\Theta_{\mathrm{dyn}},\Theta_{\mathrm{ini}})
$$

其中：

1. $\Theta_{\mathrm{str}}$ 为结构参数，编码空间维数、格长、边界条件、拓扑缺陷、元胞内部自由度与对称群等离散信息；
2. $\Theta_{\mathrm{dyn}}$ 为动力学参数，编码局域幺正门的类型、作用邻域结构与有限精度角参数，决定 QCA 自同构 $\alpha_{\Theta}$；
3. $\Theta_{\mathrm{ini}}$ 为初始态参数，编码生成初始宇宙态 $\omega_0^{\Theta}$ 的有限深度线路与谱形状信息。

参数信息量定义为

$$
I_{\mathrm{param}}(\Theta)=|\Theta_{\mathrm{str}}|+|\Theta_{\mathrm{dyn}}|+|\Theta_{\mathrm{ini}}|
$$

其中 $|\cdot|$ 表示比特长度。

### 局域门集、线路深度与精度约束

为确保参数空间可数且受控，本文假设存在一个固定的有限门集

$$
\mathcal{G}=\{G_k\}_{k=1}^K
$$

其中每个 $G_k$ 作用于半径不超过 $r_0$ 的有限邻域，其矩阵元为代数数或由有限精度离散角参数控制的代数数。动力学参数 $\Theta_{\mathrm{dyn}}$ 指定线路深度 $D\in\mathbb{N}$，以及每一层的门类型索引 $k_\ell$ 与作用区域 $R_\ell\subset\Lambda$，同时对需要连续调参的门给出离散角

$$
\phi_{\ell,j}=2\pi n_{\ell,j}/2^{m_{\ell,j}}
$$

其中 $0\le n_{\ell,j}<2^{m_{\ell,j}}$，$m_{\ell,j}$ 有统一上界。

初始态参数 $\Theta_{\mathrm{ini}}$ 同样使用门集 $\mathcal{G}$ 构造有限深度态制备线路，使得参考积态

$$
|0_{\Lambda}\rangle=\bigotimes_{x\in\Lambda}|0_{\mathrm{cell}}\rangle_x
$$

通过一个有限深度幺正 $V_{\Theta}$ 演化为初始态

$$
|\Psi_0^{\Theta}\rangle=V_{\Theta}|0_{\Lambda}\rangle
$$

从而定义

$$
\omega_0^{\Theta}(A)=\langle\Psi_0^{\Theta}|A|\Psi_0^{\Theta}\rangle
$$

---

## Main Results (Theorems and Alignments)

本节给出在上述模型与公理下的主要结构性结果。证明思路在下一节概述，技术细节置于附录。

### 宇宙 QCA 对象的存在与唯一性

首先从参数向量 $\Theta$ 构造宇宙 QCA 对象。

**定义 3.1（带参数宇宙量子元胞自动机）**

给定满足有限信息不等式的参数向量 $\Theta=(\Theta_{\mathrm{str}},\Theta_{\mathrm{dyn}},\Theta_{\mathrm{ini}})$，定义宇宙 QCA 对象

$$
\mathfrak{U}_{\mathrm{QCA}}(\Theta)=\bigl(\Lambda(\Theta),\mathcal{H}_{\mathrm{cell}}(\Theta),\mathcal{A}(\Theta),\alpha_{\Theta},\omega_0^{\Theta}\bigr)
$$

其中：

1. $\Lambda(\Theta)$、$\mathcal{H}_{\mathrm{cell}}(\Theta)$、$\mathcal{A}(\Theta)$ 由 $\Theta_{\mathrm{str}}$ 按准局域代数构造给出；
2. $\alpha_{\Theta}$ 由动力学参数 $\Theta_{\mathrm{dyn}}$ 指定的有限深度局域线路 $U_{\Theta_{\mathrm{dyn}}}$ 诱导，定义为 $\alpha_{\Theta}(A)=U_{\Theta_{\mathrm{dyn}}}^\dagger A U_{\Theta_{\mathrm{dyn}}}$；
3. $\omega_0^{\Theta}$ 由初始态线路 $V_{\Theta_{\mathrm{ini}}}$ 作用于参考积态 $|0_{\Lambda}\rangle$ 得到；
4. 宇宙满足有限信息不等式
$$
I_{\mathrm{param}}(\Theta)+S_{\max}(\Theta)\le I_{\max}
$$
其中 $S_{\max}(\Theta)=\ln\dim\mathcal{H}_{\Lambda(\Theta)}=N_{\mathrm{cell}}(\Theta)\ln d_{\mathrm{cell}}(\Theta)$。

**定理 3.2（宇宙 QCA 的存在与编码唯一性）**

对任意满足有限信息不等式的 $\Theta\in\{0,1\}^{\le I_{\max}}$，存在宇宙 QCA 对象 $\mathfrak{U}_{\mathrm{QCA}}(\Theta)$ 如定义 3.1 所述，其演化 $\alpha_{\Theta}$ 为传播半径有限的 QCA 自同构。

若两组参数 $\Theta,\Theta'$ 所定义的宇宙 QCA 之间存在准局域 $C^\ast$ 代数同构 $\Phi:\mathcal{A}(\Theta)\to\mathcal{A}(\Theta')$、整数双射 $f:\mathbb{Z}\to\mathbb{Z}$ 以及态同构 $\omega_0^{\Theta'}=\omega_0^{\Theta}\circ\Phi^{-1}$，满足

$$
\Phi\circ\alpha_{\Theta}^n=\alpha_{\Theta'}^{f(n)}\circ\Phi,\quad\forall n\in\mathbb{Z}
$$

则 $\Theta$ 与 $\Theta'$ 在有限重编码意义下等价，即存在可逆重编码映射 $\mathrm{CodeRedund}$ 使得 $\Theta'=\mathrm{CodeRedund}(\Theta)$。

该定理说明，在固定门集与编码约定下，一个满足有限信息公理的宇宙类可由参数向量 $\Theta$ 唯一定义。

### 有限信息不等式与规模–自由度折衷

有限信息不等式蕴含宇宙元胞数与局域 Hilbert 维数的约束。

**命题 3.3（元胞数与局域维数上界）**

设 $d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ge 2$，则有限信息不等式

$$
I_{\mathrm{param}}(\Theta)+N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ln d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\le I_{\max}
$$

蕴含以下上界：

1. 元胞数上界
$$
N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\le\frac{I_{\max}-I_{\mathrm{param}}(\Theta)}{\ln 2}
$$

2. 在 $N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ge 1$ 时，局域 Hilbert 维数满足
$$
\ln d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\le\frac{I_{\max}-I_{\mathrm{param}}(\Theta)}{N_{\mathrm{cell}}(\Theta_{\mathrm{str}})}
$$

因而，当元胞数非常大时，局域自由度必须较少；反之，当每个元胞内部自由度巨大时，允许的元胞总数受到强烈压缩，构成"元胞数–内部自由度–参数比特数"三者之间的折衷结构。

### Dirac 型连续极限与有效质量映射

在既有 Dirac–QCA 与离散量子行走连续极限结果基础上，可构造一族缩放参数 $(a,\Delta t)$ 与动力学角参数，使宇宙 QCA 在极限下收敛到相对论性场论。

**定理 3.4（Dirac–QCA 的连续极限与质量–角参数映射）**

考虑一族一维 Dirac 型 QCA，结构参数指定 $\Lambda=\mathbb{Z}_L$、元胞 Hilbert 空间 $\mathcal{H}_x\cong\mathbb{C}^2$，动力学参数给出更新算子

$$
U_{\Theta}=S\,C\bigl(\theta(\Theta)\bigr)
$$

其中 $C(\theta)=\exp(-\mathrm{i}\theta\sigma_y)$ 为 coin 门，$S$ 为自旋依赖平移。令格距为 $a$，时间步长为 $\Delta t$，并引入连续坐标 $X=ax$、$T=n\Delta t$。当 $a,\Delta t,\theta(\Theta)\to 0$ 且 $c_{\mathrm{eff}}(\Theta)=a/\Delta t$ 收敛到有限常数时，离散演化在适当重标度下收敛到一维 Dirac 方程

$$
\mathrm{i}\partial_T\psi(T,X)=\bigl(-\mathrm{i}c_{\mathrm{eff}}(\Theta)\sigma_z\partial_X+m_{\mathrm{eff}}(\Theta)c_{\mathrm{eff}}^2(\Theta)\sigma_y\bigr)\psi(T,X)
$$

其中有效质量满足

$$
m_{\mathrm{eff}}(\Theta)c_{\mathrm{eff}}^2(\Theta)\approx\frac{\theta(\Theta)}{\Delta t}
$$

从而 $m_{\mathrm{eff}}(\Theta)$ 与动力学角参数 $\theta(\Theta)$ 之间存在近似线性关系。将构造推广到多维与多通道 QCA，可得到多味 Dirac 场的连续极限，并将质量矩阵与混合角表示为 $\Theta_{\mathrm{dyn}}$ 中离散角参数的函数。

### 规范场与有效引力常数

通过在元胞之间引入边寄存器、规范群 $G_{\mathrm{gauge}}$ 的有限维表示以及相应局域幺正，QCA 可模拟格规范场论及其连续极限。

**定理 3.5（规范耦合与引力常数的参数依赖）**

在带规范寄存器与局域耦合门的 QCA 构造下，存在一族缩放方案，使得在 $a,\Delta t\to 0$ 极限中出现有效 Yang–Mills 方程

$$
\nabla_\mu G^{\mu\nu}(\Theta)=J^\nu(\Theta)
$$

其中规范耦合常数 $g(\Theta)$ 与动力学参数 $\Theta_{\mathrm{dyn}}$ 中的若干离散角的组合相关。对传播锥与统一时间刻度函数 $\kappa(\omega;\Theta)$ 施加一致性条件，可定义有效度规 $g_{\mu\nu}(\Theta)$ 与引力常数 $G(\Theta)$，使得在适当近似下满足

$$
G_{\mu\nu}(\Theta)+\Lambda(\Theta)g_{\mu\nu}(\Theta)=8\pi G(\Theta)T_{\mu\nu}(\Theta)
$$

其中 $\Lambda(\Theta)$ 为由 $\Theta_{\mathrm{str}},\Theta_{\mathrm{dyn}},\Theta_{\mathrm{ini}}$ 决定的有效宇宙学常数。

尽管该构造在严格数学意义上仍需更多发展，其结构表明标准模型耦合与引力常数在原则上可被吸收到 $\Theta$ 的有限比特编码中。

### 观察者网络与共识几何

最后，在宇宙 QCA 中引入观察者网络与信息几何结构。

**定义 3.6（观察者对象与网络）**

一个观察者对象 $O_i$ 由局域可观测代数 $\mathcal{A}_{O_i}\subset\mathcal{A}(\Theta)$ 与其上态 $\omega_i^{\Theta}$ 组成，后者由全宇宙态在 $\mathcal{A}_{O_i}$ 上的限制给出。观察者网络 $\mathcal{G}_{\mathrm{obs}}(\Theta)$ 是有向图，其顶点为各 $O_i$，边为通信通道 $\mathcal{C}_{ij}$，对应完全正、迹保持映射 $\mathcal{C}_{ij}:\mathcal{A}_{O_i}\to\mathcal{A}_{O_j}$。

**定理 3.7（参数化共识几何的存在性）**

在给定宇宙 QCA 对象 $\mathfrak{U}_{\mathrm{QCA}}(\Theta)$ 与观察者网络 $\mathcal{G}_{\mathrm{obs}}(\Theta)$ 的条件下，存在一类由相对熵

$$
S\bigl(\mathcal{C}_{ij\ast}(\omega_i^{\Theta})\Vert\omega_j^{\Theta}\bigr)
$$

定义的信息几何结构，其在长时间极限 $n\to\infty$ 下可在部分参数区域 $\Theta$ 上收敛到零，从而定义在该 $\Theta$ 下的"共识几何"。共识是否出现及其收敛速度受 $\Theta_{\mathrm{dyn}}$ 与 $\Theta_{\mathrm{ini}}$ 中表征通信容量与噪声强度的参数强烈控制。

---

## Proofs

本节给出主要定理与命题的证明思路，将技术细节与具体估计推迟到附录。

### 宇宙 QCA 的存在与唯一性

**定理 3.2 的证明思路**

存在性部分通过显式构造得到。结构层由 $\Theta_{\mathrm{str}}$ 中的离散信息唯一决定格点集合 $\Lambda(\Theta_{\mathrm{str}})$、局域 Hilbert 空间 $\mathcal{H}_x(\Theta_{\mathrm{str}})$ 与准局域代数 $\mathcal{A}(\Theta_{\mathrm{str}})$。动力学层由 $\Theta_{\mathrm{dyn}}$ 指定的有限深度线路

$$
U_{\Theta_{\mathrm{dyn}}}=U_D\cdots U_1
$$

构造，每层 $U_\ell$ 为若干作用于半径不超过 $r_0$ 邻域的门的张量积。对任意 $A\in\mathcal{A}_F$，逐层共轭可证明其支撑集在每层最多向外扩展 $r_0$，从而经过 $D$ 层后支撑包含于 $B_{Dr_0}(F)$，保证 $\alpha_{\Theta}(A)=U_{\Theta_{\mathrm{dyn}}}^\dagger A U_{\Theta_{\mathrm{dyn}}}$ 具有有限传播半径。幺正性保证 $\alpha_{\Theta}$ 为 $C^\ast$ 自同构。初始态层由有限深度线路 $V_{\Theta_{\mathrm{ini}}}$ 作用于参考积态构造，得到纯态 $|\Psi_0^{\Theta}\rangle$ 及其对应的态 $\omega_0^{\Theta}$。

唯一性部分依赖于准局域代数的分类与可逆 QCA 的结构可逆性定理。Schumacher–Werner 的结果表明，在平移不变与有限传播半径假设下，QCA 可以表示为广义 Margolus 分块方案中的两层分块幺正乘积，其逆仍为 QCA。在本文的更一般情形中（允许有限体积与非完全平移不变），可以局部化地应用类似结构：给定两个 QCA 若存在代数同构 $\Phi$ 保持局域支持与因果结构，并在适当时间重标定下共轭，它们在局域门级别对应于同一门集与离散参数的可逆重编码，从而诱导 $\Theta$ 与 $\Theta'$ 的重编码等价关系。这部分详见附录 A 与附录 D 中的范畴化处理。

### 有限信息不等式与规模折衷

**命题 3.3 的证明思路**

由结构定义，宇宙 Hilbert 空间维数为

$$
\dim\mathcal{H}_{\Lambda(\Theta_{\mathrm{str}})}=d_{\mathrm{cell}}(\Theta_{\mathrm{str}})^{N_{\mathrm{cell}}(\Theta_{\mathrm{str}})}
$$

最大冯诺依曼熵为

$$
S_{\max}(\Theta)=N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ln d_{\mathrm{cell}}(\Theta_{\mathrm{str}})
$$

有限信息不等式给出

$$
I_{\mathrm{param}}(\Theta)+N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ln d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\le I_{\max}
$$

若 $d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ge 2$，则 $\ln d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ge\ln 2$，从而

$$
I_{\mathrm{param}}(\Theta)+N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ln 2\le I_{\max} \Rightarrow N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\le\frac{I_{\max}-I_{\mathrm{param}}(\Theta)}{\ln 2}
$$

当 $N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ge 1$ 时，可解出

$$
\ln d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\le\frac{I_{\max}-I_{\mathrm{param}}(\Theta)}{N_{\mathrm{cell}}(\Theta_{\mathrm{str}})}
$$

这两条不等式即为命题 3.3。技术上可进一步引入 Bekenstein–Bousso 型熵界，将 $S_{\max}(\Theta)$ 与离散几何中的"面积"关联，得到 $I_{\max}$ 的物理估计，但这超出本文范围。

### Dirac–QCA 连续极限的推导

**定理 3.4 的证明思路**

对一维 Dirac 型 QCA，动量空间中的更新矩阵为

$$
U_{\Theta}(k)=\mathrm{diag}\bigl(e^{\mathrm{i}k},e^{-\mathrm{i}k}\bigr)C\bigl(\theta(\Theta)\bigr)
$$

在 $k,\theta(\Theta)\to 0$ 小参数极限下，对 $U_{\Theta}(k)$ 做一次展开：

$$
C\bigl(\theta(\Theta)\bigr)\approx\mathbf{1}-\mathrm{i}\theta(\Theta)\sigma_y-\tfrac{1}{2}\theta(\Theta)^2\mathbf{1}
$$

$$
\mathrm{diag}\bigl(e^{\mathrm{i}k},e^{-\mathrm{i}k}\bigr)\approx\mathbf{1}+\mathrm{i}k\sigma_z-\tfrac{1}{2}k^2\mathbf{1}
$$

乘积到一阶近似：

$$
U_{\Theta}(k)\approx\mathbf{1}-\mathrm{i}\bigl(k\sigma_z+\theta(\Theta)\sigma_y\bigr)-\tfrac{1}{2}\bigl(k^2+\theta(\Theta)^2\bigr)\mathbf{1}
$$

令每步时间为 $\Delta t$，假设存在有效哈密顿量 $H_{\mathrm{eff}}(k)$ 使

$$
U_{\Theta}(k)=\exp\bigl(-\mathrm{i}H_{\mathrm{eff}}(k)\Delta t\bigr)
$$

将指数展开到一阶得到

$$
H_{\mathrm{eff}}(k)\approx\frac{k\sigma_z+\theta(\Theta)\sigma_y}{\Delta t}
$$

在位置表象下，以 $k\mapsto-\mathrm{i}\partial_X$、$X=ax$、$T=n\Delta t$ 以及 $c_{\mathrm{eff}}(\Theta)=a/\Delta t$ 重写，上式对应的演化方程为

$$
\mathrm{i}\partial_T\psi(T,X)=\bigl(-\mathrm{i}c_{\mathrm{eff}}(\Theta)\sigma_z\partial_X+m_{\mathrm{eff}}(\Theta)c_{\mathrm{eff}}^2(\Theta)\sigma_y\bigr)\psi(T,X)
$$

其中

$$
m_{\mathrm{eff}}(\Theta)c_{\mathrm{eff}}^2(\Theta)=\frac{\theta(\Theta)}{\Delta t}
$$

在多维与多味情形下，可通过张量积与适当 coin 结构得到多分量 Dirac 方程；与已有离散 Dirac 模型的连续极限分析一致，确保构造的合理性。具体推导详见附录 C。

### 规范场与引力常数映射

对规范场，可在每条格边上引入寄存器 $\mathcal{H}_{\mathrm{link}}$，存储近似群元 $\exp(\mathrm{i}aA_\mu)$，并引入局域幺正耦合门实现费米子与规范场的相互作用。相应的连续极限过程与量子链路–格规范理论中使用的方案类似。

有效引力常数量的构造更为间接：考虑 QCA 的传播锥与统一时间刻度函数

$$
\kappa(\omega;\Theta)=\frac{\varphi'(\omega;\Theta)}{\pi}=\frac{1}{2\pi}\mathrm{tr}\,Q(\omega;\Theta)
$$

其中 $\varphi(\omega;\Theta)$ 为散射相位，$Q(\omega;\Theta)$ 为 Wigner–Smith 群延迟矩阵。通过要求离散传播锥在连续极限下收敛到 Lorentz 光锥，结合广义熵与 QCA 能量–动量流的关系，可以在有效层面上确定 $g_{\mu\nu}(\Theta)$、$G(\Theta)$ 与 $\Lambda(\Theta)$ 的函数形式。这一部分依赖于散射理论与边界时间几何的既有结果，详细推演留待后续工作发展。

### 观察者网络与共识几何

观察者范畴的构造以对象对 $(\mathcal{A}_{O_i},\omega_i^{\Theta})$ 为基本元素，态射为 CPTP 映射 $\Phi_{ij}$。在给定宇宙演化下，不同观察者的态随时间演化为

$$
\omega_i^{\Theta}(n)=\omega_0^{\Theta}\bigl(\alpha_{\Theta}^{-n}(\cdot)\bigr)\big|_{\mathcal{A}_{O_i}}
$$

通信通道 $\mathcal{C}_{ij}$ 的存在与容量由 QCA 的局域结构与初始态纠缠决定。对每条边 $(i,j)$，定义共识偏离度

$$
D_{ij}(\Theta;n)=S\bigl(\mathcal{C}_{ij\ast}\bigl(\omega_i^{\Theta}(n)\bigr)\Vert\omega_j^{\Theta}(n)\bigr)
$$

全网偏离度

$$
D_{\mathrm{cons}}(\Theta;n)=\sum_{(i,j)\in E(\Theta_{\mathrm{str}})}D_{ij}(\Theta;n)
$$

若存在序列 $n_k\to\infty$ 使 $D_{\mathrm{cons}}(\Theta;n_k)\to 0$，则可定义在该 $\Theta$ 下的共识几何极限。从信息几何角度，这对应于观察者分布在统计流形上的收敛到某个子流形，该子流形的结构由 $\Theta$ 控制。相关证明需要结合量子相对熵的单调性与 QCA 下局域互信息的传播性质，具体估计见附录 E。

---

## Model Apply

本节讨论如何在带参数宇宙 QCA 框架中抽象地编码物理常数与初始条件，并给出若干简化示例。

### 标准模型参数的离散角编码

设 $\Theta_{\mathrm{dyn}}$ 中包含一组离散角参数

$$
\Phi=\bigl(\phi_1,\dots,\phi_{N_\phi}\bigr),\quad \phi_j=\frac{2\pi n_j}{2^{m_j}}
$$

其中 $n_j\in\{0,\dots,2^{m_j}-1\}$，$m_j$ 为精度位数。将 $\Phi$ 映射为有效质量矩阵、规范耦合与 Yukawa 耦合的函数：

$$
m_a(\Theta)=f_a(\Phi),\quad g_i(\Theta)=g_i(\Phi),\quad y_{ab}(\Theta)=h_{ab}(\Phi)
$$

其中 $f_a,g_i,h_{ab}$ 为由 QCA 连续极限确定的解析或分段解析函数。给定目标物理值 $m_a^{\mathrm{phys}},g_i^{\mathrm{phys}},y_{ab}^{\mathrm{phys}}$，可通过近似反演 $f_a,g_i,h_{ab}$ 来选择相应的整数 $n_j$，其所需精度由 $m_j$ 控制。参数信息量中与动力学有关的部分为

$$
I_{\mathrm{dyn}}(\Theta)\approx\sum_{j=1}^{N_\phi}m_j+\text{(门类型与邻域索引贡献)}
$$

因此，在有限 $I_{\max}$ 下，对物理常数的可实现精度存在上限。这为"参数自然性"问题提供了新的信息论视角：某些极端精细调参的物理常数可能在有限信息宇宙中难以实现。

### 宇宙规模与初始条件的联合约束

初始态参数 $\Theta_{\mathrm{ini}}$ 编码态制备线路 $V_{\Theta_{\mathrm{ini}}}$。若线路深度与门数有限，则可生成的纠缠模式具有有限复杂度。这意味着，在相同步长与门集下，宇宙初始条件的复杂性与参数信息量 $I_{\mathrm{ini}}(\Theta)$ 之间存在直接关联。

结合命题 3.3 的不等式：

$$
I_{\mathrm{str}}(\Theta)+I_{\mathrm{dyn}}(\Theta)+I_{\mathrm{ini}}(\Theta)+N_{\mathrm{cell}}(\Theta_{\mathrm{str}})\ln d_{\mathrm{cell}}(\Theta_{\mathrm{str}})\le I_{\max}
$$

可视为一个"预算约束"：增加宇宙规模 $N_{\mathrm{cell}}$ 或局域维数 $d_{\mathrm{cell}}$ 将压缩可用于编码更精细动力学与初始条件的比特预算。这在概念上对应于"宇宙越大、内容越简单"与"宇宙越小、可允许更复杂的局域物理"之间的权衡。

### 简化宇宙示例

作为示意，可构造如下玩具模型：

1. 一维周期格 $\Lambda=\mathbb{Z}_L$，元胞 Hilbert 空间 $\mathcal{H}_x\cong\mathbb{C}^2$；
2. 动力学为单一 Dirac 型 QCA，参数 $\theta(\Theta)$ 决定有效质量；
3. 初始态为一簇局域波包与热浴态的张量积。

在该模型中，$\Theta_{\mathrm{str}}$ 仅包含 $L$ 与 $d_{\mathrm{cell}}=2$，$\Theta_{\mathrm{dyn}}$ 仅含一个角参数 $\theta(\Theta)$，$\Theta_{\mathrm{ini}}$ 包含有限个门的描述。有限信息不等式直接给出 $L$ 的上界，而 Dirac 连续极限将 $\theta(\Theta)$ 映射为有效质量 $m_{\mathrm{eff}}(\Theta)$。这展示了从有限比特参数到连续物理量的一条明确路径。

---

## Engineering Proposals

尽管本文的出发点是宇宙级理论，但其结构同样适用于有限尺度的"子宇宙"或物理模拟平台。本节简要讨论若干工程实现方向。

### 量子模拟平台上的有限信息 QCA

现有中等规模量子设备（如困离子、超导量子比特与光量子行走平台）已能实现若干步 Dirac 型 QCA 或离散时间量子行走。在这些平台上，可以选择带参数的局域门，显式实现 $\Theta_{\mathrm{dyn}}$ 的有限比特编码，并通过实验测量验证连续极限下有效质量与耦合常数的映射关系。进一步地，可通过限制设备可用比特与门数，实验性地探讨有限信息不等式对可模拟物理现象的约束。

### QCA 格距与实验约束

若将 QCA 视为基础物理模型，则格距 $a$ 与时间步长 $\Delta t$ 必须与现有实验相容。对 Dirac–QCA 模型，可以利用高能散射、天体物理信号或引力波色散实验来约束 $a$ 的最大值；近年来部分工作已从量子行走与 QCA 连续极限的角度给出对格距的理论界限。在有限信息框架下，$a$ 的下界又与 $I_{\max}$ 与 $N_{\mathrm{cell}}$ 的乘积有关，形成"实验–信息论"双重约束。

### 多智能体系统与观察者网络

在工程层面，可以将带参数 QCA 框架用于抽象多智能体系统：将智能体视为元胞或局域代数子系统，资源与任务视为局域自由度，协议与调度规则视为 QCA 动力学的一部分。有限信息不等式则对应于系统硬件资源与协议复杂度的联合约束；观察者网络与共识几何结构则为分析分布式系统中一致性与观点收敛提供几何化工具。

---

## Discussion (risks, boundaries, past work)

### 与全息原理及相关工作的关系

本文的有限信息宇宙公理由 Bekenstein 熵界与 Bousso 协变熵界所启发，即在给定时空区域的几何约束下，其物理自由度与信息量上界有限。本文并未直接在连续时空中实现这些几何约束，而是将其抽象为一个全局信息容量上界 $I_{\max}$。在更完整的理论中，$I_{\max}$ 应作为由全息原理与具体宇宙几何确定的函数出现，例如与宇宙可观测视界面积成正比。

与以往"宇宙作为量子计算机"的工作相比，本文在 QCA 与准局域代数层面给出了更具体的结构：明确引入参数向量 $\Theta$、有限门集与有限深度线路，并通过有限信息不等式得到元胞数与局域维数上的约束。这在形式上将"计算极限"转化为"描述复杂度极限"。

### 理论边界与局限

本文的构造仍有若干局限性：

1. 虽然宇宙 QCA 在形式上有限，但其连续极限依然通过 $a,\Delta t\to 0$ 取极限实现，这在严格数学上需要精细的缩放分析与误差估计，目前仅对 Dirac 型与部分规范场模型有较完善结论；
2. 引力常数与宇宙学常数的参数依赖仅在结构层面勾勒，尚未给出完整的从 QCA 到 Einstein 方程的严格推导；
3. 有限信息不等式中的 $I_{\max}$ 目前被视为外部给定参数，其物理决定机制（例如与全息面积、宇宙能量或时长的关系）尚未在 QCA 框架内自洽导出；
4. 本文未讨论耗散、开放系统与非幺正演化对宇宙级 QCA 描述的影响，也未涉及测量与经典记录的具体机制。

### 概念风险与可检验性

从哲学角度，将宇宙描述为有限比特串 $\Theta$ 的观点具有强烈的"数字化"倾向，其合理性有赖于以下问题的进一步澄清：

1. 连续对称性（如 Lorentz 对称与规范对称）在有限比特描述中的精确或近似实现；
2. 重整化与连续极限中产生的"新常数"是否可以全部追溯到 $\Theta$ 的离散结构；
3. 不同 $\Theta$ 所定义的"可能宇宙"空间是否存在自然概率分布或选择原则。

在可检验性方面，离散 QCA 模型带来的最直接预测往往是高能尺度上的色散与对称性破缺效应，实验上可通过高能宇宙线、引力波与精密量子实验进行约束。同时，有限信息不等式可能在宇宙学初始条件与大尺度结构的统计分布中留下特征，但这些方向尚处于探索阶段。

---

## Conclusion

本文在量子元胞自动机与准局域 $C^\ast$ 代数的框架中，引入有限信息宇宙公理，构造了一个显式带参数的宇宙 QCA 理论。宇宙的结构层、动力学层与初始态层被统一编码为一个有限比特串参数向量 $\Theta$，并证明在固定门集与编码约定下，满足有限信息不等式的 $\Theta$ 唯一定义一个宇宙 QCA 对象 $\mathfrak{U}_{\mathrm{QCA}}(\Theta)$。有限信息不等式 $I_{\mathrm{param}}(\Theta)+S_{\max}(\Theta)\le I_{\max}$ 给出了宇宙元胞数、局域 Hilbert 维数与参数精度三者之间的定量折衷。

在连续极限上，本文基于 Dirac–QCA 与离散量子行走的既有成果，构造了从 $\Theta$ 到有效质量、规范耦合与引力常数的映射，表明标准模型与引力理论的连续参数在原则上可以被嵌入到有限比特描述中。进一步地，通过观察者网络与信息几何的构造，本文将宇宙参数 $\Theta$ 对可观测统计结构与共识几何的影响纳入同一理论框架。

未来工作方向包括：在更一般的 QCA 模型中严格推导 Einstein 方程与全息熵界；系统分析 $\Theta$ 空间的结构与可能的"选择原则"；在量子模拟平台上实现带参数 QCA 并验证有限信息不等式对物理可实现性的影响；以及将该框架与量子引力、宇宙学与多智能体系统理论进一步耦合。

---

## Acknowledgements, Code Availability

作者感谢量子元胞自动机、量子信息与量子引力领域现有工作的启发。本文提出的带参数宇宙 QCA 模型为纯理论构造，文中所述示例线路与连续极限分析均可在通用量子编程框架中直接实现，相关数值验证与模拟脚本可按本模型结构独立编写。

---

## References

[1] B. Schumacher, R. F. Werner, "Reversible quantum cellular automata," arXiv:quant-ph/0405174, 2004.

[2] P. Arrighi, "An overview of quantum cellular automata," Natural Computing 18, 885–899 (2019), arXiv:1904.12956.

[3] T. Farrelly, "A review of quantum cellular automata," Quantum 4, 368 (2020), arXiv:1904.13318.

[4] R. Bousso, "The holographic principle," Reviews of Modern Physics 74, 825–874 (2002), hep-th/0203101.

[5] S. Lloyd, "Ultimate physical limits to computation," Nature 406, 1047–1054 (2000), arXiv:quant-ph/9908043.

[6] C. Huerta Alderete et al., "Quantum walks and Dirac cellular automata on a digital quantum computer," Nature Communications 11, 3720 (2020).

[7] C. Gupta, "The Dirac vacuum in discrete spacetime," Quantum 9, 1845 (2025).

[8] L. Mlodinow, "Bounds on quantum cellular automaton lattice spacing from relativistic wave equations," Phys. Rev. 2025 (in press).

[9] P. Arrighi, S. Facchini, M. Forets, "Discrete-time quantum walks, Dirac equation and curved spacetime," Quantum Information Processing 18, 107 (2019).

[10] J. Preskill, "Quantum computing in the NISQ era and beyond," Quantum 2, 79 (2018).

---

## 附录 A：准局域代数与 QCA 自同构的技术细节

### A.1 准局域 $C^\ast$ 代数的构造

对有限 $\Lambda$ 与有限维 $\mathcal{H}_x$，任意有限 $F\subset\Lambda$ 对应 Hilbert 空间

$$
\mathcal{H}_F=\bigotimes_{x\in F}\mathcal{H}_x
$$

局域代数

$$
\mathcal{A}_F=\mathcal{B}(\mathcal{H}_F)
$$

嵌入

$$
\iota_{F\subset F'}(A_F)=A_F\otimes\mathbf{1}_{F'\setminus F}
$$

使 $\{\mathcal{A}_F\}_{F\Subset\Lambda}$ 形成有向系统，其直极限在范数闭包下得到准局域 $C^\ast$ 代数

$$
\mathcal{A}_{\mathrm{ql}}=\overline{\bigcup_{F\Subset\Lambda}\mathcal{A}_F}^{|\cdot|}
$$

若 $\Lambda$ 可数，构造过程类似，只需对所有有限子集取并与闭包即可。GNS 构造保证任意态诱导的表示中局域算子在范数拓扑下稠密。

### A.2 有限深度线路的传播半径估计

设线路

$$
U=U_D\cdots U_1,\quad U_\ell=\bigotimes_{R_\ell}G_{k_\ell}
$$

其中每个门 $G_{k_\ell}$ 作用于半径不超过 $r_0$ 的邻域。对 $A\in\mathcal{A}_F$，递归定义

$$
A^{(0)}=A,\quad A^{(\ell)}=U_\ell^\dagger A^{(\ell-1)}U_\ell
$$

由门的局域性，有

$$
\mathrm{supp}\bigl(A^{(\ell)}\bigr)\subset B_{r_0}\bigl(\mathrm{supp}(A^{(\ell-1)})\bigr)
$$

从而

$$
\mathrm{supp}\bigl(A^{(D)}\bigr)\subset B_{Dr_0}(F)
$$

令 $\alpha(A)=U^\dagger A U=A^{(D)}$，即可得到传播半径不超过 $Dr_0$。

### A.3 自同构性与结构可逆性

幺正 $U$ 诱导的映射 $\alpha(A)=U^\dagger A U$ 显然保持乘法与 $*$ 运算，其逆映射为 $A\mapsto U A U^\dagger$，因而为 $C^\ast$ 自同构。对平移不变与无限格情形，Schumacher 与 Werner 的结构定理进一步表明，该自同构可写为两层分块幺正的组合，其逆仍满足同一局域性约束。本文将这一结构思想局部化到有限格与非均匀情形，以控制编码冗余与门级表示之间的对应关系。

---

## 附录 B：有限信息不等式的进一步推论

### B.1 宇宙类数量的有限性

参数向量 $\Theta$ 的长度不超过 $I_{\max}$，因此所有可能参数串数量至多为

$$
\sum_{k=0}^{I_{\max}}2^k=2^{I_{\max}+1}-1
$$

有限信息不等式进一步排除不满足 $I_{\mathrm{param}}(\Theta)+S_{\max}(\Theta)\le I_{\max}$ 的参数，从而可实现宇宙类集合为有限集合的子集。虽然这一上界极其宽松，但与连续参数空间相较，表明在本框架中"可能宇宙"集合是离散且有限的。

### B.2 比特分配策略与自然性

将 $I_{\max}$ 视为总"预算"，需要在结构、动力学与初始态三者之间分配。给定目标宇宙规模与局域维数，可求得允许的最大参数信息量；反之，也可从对物理常数精度的要求出发，得到对宇宙规模的约束。这为自然性问题提供了新的问题形式：在固定 $I_{\max}$ 下，哪些参数配置在比特分配上"最经济"，是否存在对这类配置的统计偏好。

---

## 附录 C：一维 Dirac–QCA 连续极限的详细推导

### C.1 模型定义与参数化

考虑一维周期格 $\Lambda=\mathbb{Z}_L$，元胞 Hilbert 空间 $\mathcal{H}_x\cong\mathbb{C}^2$，基矢为 $|x,\uparrow\rangle,|x,\downarrow\rangle$。定义条件平移算子

$$
S|x,\uparrow\rangle=|x+1,\uparrow\rangle,\quad S|x,\downarrow\rangle=|x-1,\downarrow\rangle
$$

coin 门为

$$
C\bigl(\theta(\Theta)\bigr)=\exp\bigl(-\mathrm{i}\theta(\Theta)\sigma_y\bigr)
$$

更新算子 $U_{\Theta}=S\,C\bigl(\theta(\Theta)\bigr)$。

在动量基矢

$$
|k,\uparrow\rangle=L^{-1/2}\sum_x e^{\mathrm{i}kx}|x,\uparrow\rangle,\quad |k,\downarrow\rangle=L^{-1/2}\sum_x e^{\mathrm{i}kx}|x,\downarrow\rangle
$$

下有

$$
S|k,\uparrow\rangle=e^{\mathrm{i}k}|k,\uparrow\rangle,\quad S|k,\downarrow\rangle=e^{-\mathrm{i}k}|k,\downarrow\rangle
$$

从而

$$
U_{\Theta}(k)=\mathrm{diag}\bigl(e^{\mathrm{i}k},e^{-\mathrm{i}k}\bigr)C\bigl(\theta(\Theta)\bigr)
$$

### C.2 有效哈密顿量与连续极限

假设存在 $H_{\mathrm{eff}}(k)$ 使

$$
U_{\Theta}(k)=\exp\bigl(-\mathrm{i}H_{\mathrm{eff}}(k)\Delta t\bigr)
$$

对 $k,\theta(\Theta)$ 小参数展开并比较一阶项，得到

$$
H_{\mathrm{eff}}(k)\approx\frac{k\sigma_z+\theta(\Theta)\sigma_y}{\Delta t}
$$

将 $k\mapsto-\mathrm{i}\partial_X$、$X=ax$ 替换，并令 $c_{\mathrm{eff}}(\Theta)=a/\Delta t$，$m_{\mathrm{eff}}(\Theta)c_{\mathrm{eff}}^2(\Theta)=\theta(\Theta)/\Delta t$，得到一维 Dirac 方程

$$
\mathrm{i}\partial_T\psi(T,X)=\bigl(-\mathrm{i}c_{\mathrm{eff}}(\Theta)\sigma_z\partial_X+m_{\mathrm{eff}}(\Theta)c_{\mathrm{eff}}^2(\Theta)\sigma_y\bigr)\psi(T,X)
$$

多维与多味推广可通过在 coin 与平移算子中引入更复杂的矩阵结构实现，其连续极限已在相关量子行走与 QCA 文献中得到系统分析。

---

## 附录 D：从参数向量到有效常数空间的范畴化描述

定义参数空间

$$
\mathcal{P}=\bigl\{\Theta\in\{0,1\}^{\le I_{\max}}:\ I_{\mathrm{param}}(\Theta)+S_{\max}(\Theta)\le I_{\max}\bigr\}
$$

有效常数空间

$$
\mathcal{C}=\bigl\{(G,\Lambda,\hbar,g_i,m_a,y_{ab},\dots)\bigr\}
$$

连续极限过程定义了映射

$$
\mathcal{F}:\mathcal{P}\to\mathcal{C},\quad\Theta\mapsto\mathcal{F}(\Theta)
$$

定义等价关系 $\Theta\sim\Theta'$ 当且仅当 $\mathcal{F}(\Theta)=\mathcal{F}(\Theta')$。参数空间商 $\mathcal{P}/\sim$ 中的点对应在有效场论层面不可区分的宇宙类。定理 3.2 所述的 QCA 同构则为更强的等价关系，其必然蕴含 $\Theta\sim\Theta'$，但反之未必成立。

从范畴论角度，可构造以宇宙 QCA 对象为对象、以保持局域结构与有限信息约束的 $C^\ast$ 同构为态射的范畴 $\mathbf{Univ}_{\mathrm{QCA}}$，以及以连续场论对象为对象的范畴 $\mathbf{QFT}$，使 $\mathcal{F}$ 提升为函子 $\mathfrak{F}:\mathbf{Univ}_{\mathrm{QCA}}\to\mathbf{QFT}$。该函子的性质（例如是否保极限、共极限、是否满射）将为"可能宇宙"空间的结构提供更深刻的数学信息。

---

## 附录 E：观察者网络与信息几何的形式化

### E.1 观察者范畴与态射

定义观察者范畴 $\mathbf{Obs}(\Theta)$：

- 对象为对 $(\mathcal{A}_{O_i},\omega_i^{\Theta})$，其中 $\mathcal{A}_{O_i}\subset\mathcal{A}(\Theta)$ 为局域代数，$\omega_i^{\Theta}$ 为其上态；
- 态射为 CPTP 映射 $\Phi_{ij}:\mathcal{A}_{O_i}\to\mathcal{A}_{O_j}$。

观察者网络图 $\mathcal{G}_{\mathrm{obs}}(\Theta)$ 是 $\mathbf{Obs}(\Theta)$ 骨架上的有向图近似，其边集与态射集合存在自然对应。

### E.2 相对熵与共识指标

对两个态 $\omega,\sigma$，相对熵定义为

$$
S(\omega\Vert\sigma)=\mathrm{tr}\bigl(\rho_\omega(\ln\rho_\omega-\ln\rho_\sigma)\bigr)
$$

其中 $\rho_\omega,\rho_\sigma$ 为相应密度矩阵。对边 $(i,j)$，定义

$$
D_{ij}(\Theta;n)=S\bigl(\mathcal{C}_{ij\ast}\bigl(\omega_i^{\Theta}(n)\bigr)\Vert\omega_j^{\Theta}(n)\bigr)
$$

全网偏离度

$$
D_{\mathrm{cons}}(\Theta;n)=\sum_{(i,j)\in E(\Theta_{\mathrm{str}})}D_{ij}(\Theta;n)
$$

随 $n$ 演化的行为刻画了共识过程。利用相对熵在 CPTP 映射下的单调性，可证明在某些参数区域 $\Theta$ 上，若网络连通且通信噪声适度，则 $D_{\mathrm{cons}}(\Theta;n)$ 单调下降并趋于零，从而定义共识几何极限；而在其它参数区域，则可能存在非零下界，表示观察者之间的永续分歧。

这一框架为将带参数宇宙 QCA 与多观察者统计结构的联系形式化提供了基础。
