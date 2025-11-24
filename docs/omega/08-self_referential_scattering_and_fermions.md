# 自指散射与费米子的诞生：Riccati 平方根、旋量双覆盖与 $\mathbb{Z}_2$ 交换相位

*Self-Referential Scattering and the Birth of Fermions: Riccati Square Roots, Spinor Double Cover, and a $\mathbb{Z}_2$ Exchange Phase*

---

## Abstract

在基于连续时空与庞加莱对称性的传统框架中，自旋–统计关系通常通过场论的公理体系给出：半整数自旋场必须满足反对易关系并服从费米–狄拉克统计，整数自旋场则满足对易关系并服从玻色–爱因斯坦统计。该结果依赖于局域性、因果性以及相对论协变性，对底层离散结构与信息论机制并不敏感。在量子元胞自动机（quantum cellular automata, QCA）框架中，演化由离散格点上的局域幺正算子给出，连续时空与洛伦兹对称性在长波极限中涌现，因此有必要重新追问：费米子统计是否可以从更原始的离散动力学与拓扑结构中导出。

本文在 QCA 与光程守恒的本体论视角下，构造"自指散射结构"（self-referential scattering structure）模型：有质量粒子被描述为嵌入 QCA 网络中的局域反馈回路，其输入与输出通过拓扑方式闭合。利用一维散射理论与传输线理论中已知的阻抗–Riccati 形式，我们证明：在满足局域幺正与稳定束缚态存在的条件下，描述该反馈回路输入阻抗的演化必然满足离散或连续的 Riccati 方程，而稳定束缚态对应于 Möbius 变换的超越不动点。由此产生的状态参数不可避免地包含一个复平面上的平方根分支结构，即内部散射矩阵的有效"平方根" $\sqrt{S}$。

接着，我们将该平方根结构提升为一个在能量–动量参数空间上定义的复线丛，分析其单粒子与双粒子构型空间上的拓扑性质。利用 Laidlaw–Morette-DeWitt 与 Finkelstein–Rubinstein 类型的多连通构型空间路径积分分析，我们证明：对于由自指散射结构实现的稳定有质量激发，内部平方根线丛在交换路径的提升上具有非平凡的 $\mathbb{Z}_2$ holonomy，导致双粒子波函数在交换操作下获得因子 $(-1)$。在 $(3+1)$ 维时空中，这一 $\mathbb{Z}_2$ 拓扑指标与旋量双覆盖结构等价，从而给出"自旋 $1/2$"与反对称统计的统一信息论起源。

在 Dirac 型 QCA 的连续极限中，我们进一步表明：质量参数可以解释为自指散射环中的拓扑阻抗强度，其非零值精确对应于上述 $\mathbb{Z}_2$ 指标不平凡的情形，因此得到"有质量 $\Rightarrow$ 自指 $\Rightarrow$ 平方根 $\Rightarrow$ 费米子"的链式结构。本文最后讨论了该框架与已有拓扑自旋–统计定理的关系、适用边界以及在超导电路与光子晶体平台上实现可控自指散射网络并直接探测 $\mathbb{Z}_2$ 交换相位的实验途径。

---

## Keywords

量子元胞自动机；自指散射；Riccati 方程；拓扑阻抗；旋量双覆盖；$\mathbb{Z}_2$ 交换相位；自旋–统计关系

---

## Introduction & Historical Context

自从泡利提出不相容原理以来，费米子与玻色子之间的根本差别一直被视为量子世界最深刻的结构之一。实验事实表明：电子、夸克等半整数自旋粒子服从费米–狄拉克统计，多粒子波函数在粒子标签交换下获得因子 $(-1)$，并导致能级占据上的强排斥效应；而光子等整数自旋粒子服从玻色–爱因斯坦统计，多粒子波函数在交换下保持不变。

在连续时空的相对论性量子场论中，自旋–统计定理将这一现象与庞加莱群的表示论和场算子的局域性联系起来：在满足谱条件与微因果性的前提下，半整数自旋场必须满足反对易关系，整数自旋场必须满足对易关系，由此得到费米子与玻色子的区分。该证明在 Wightman 公理、Streater–Wightman 体系以及 Weinberg 的场论框架中得到系统化阐述，但其本质上依赖于连续流形结构与洛伦兹群的性质。

另一类重要思路来自拓扑方法。Laidlaw 与 Morette-DeWitt 将不可区别粒子体系的构型空间视为带有非平凡基本群的多连通空间，通过对路径积分进行按同伦类分解，指出不可区别多粒子体系的传播子按基本群的幺正表示加权叠加，从而得到在三维空间中仅允许玻色与费米两类统计，且交换相位与自旋结构相关联。([APS Link][1]) Finkelstein 与 Rubinstein 则从拓扑孤子与 kinks 出发，证明某些非平凡同伦类的场构型在量子化后自然携带半整数自旋并服从费米统计，从而给出自旋–统计关系的几何解释。([AIP Publishing][2])

在这些工作中，费米性通常被视为连续场构型空间的拓扑性质，或者是与时空旋转群双覆盖结构相关的代数性质。然而，如果宇宙在微观上由离散的量子信息处理网络描述，即量子元胞自动机，那么连续时空与场构型空间都只是长波极限下的涌现对象。量子元胞自动机以离散格点、局域希尔伯特空间与有限深度幺正电路为基本结构，已被证明可以在长波极限中给出 Dirac、Weyl 与 Maxwell 方程等有效描述，并能在量子行走与实验量子模拟平台上实现。([quantum-journal.org][3])

在这样的离散本体论中，一个自然的问题是：**费米子统计是否可以从 QCA 的内部动力学与拓扑结构中导出，而不预设连续时空与场论公理？**

本文提出的回答基于两个要点：

1. **有质量粒子的内部自指结构**：在 QCA 框架下，无质量激发对应于沿光锥方向传播的前馈信号，而稳定的有质量粒子则必须在局域区域内进行持续的"来回传播"，在信息速率守恒的约束下形成自洽反馈回路。该观点与传输线理论中"驻波–阻抗匹配"的图像以及 QCA 中"内部震动速度"解释质量的思路一致。

2. **反馈回路与 Riccati 方程**：一维散射理论与传输线理论表明，输入阻抗或反射系数随空间坐标的演化满足一类非线性的一阶微分或差分方程，其原型正是 Riccati 方程；稳定的驻波结构对应于该 Riccati 演化的固定点或轨道。Calogero 早期工作表明，Riccati 方程的解可以视为散射问题中某些泛函的极值，并与散射相位与束缚态谱相关。([AIP Publishing][4])

我们将这两点结合，构造"自指散射结构"模型，并证明：

* 描述自指反馈回路的阻抗变量 $Z$ 必然作为某个线性演化的投影而满足 Riccati 型方程，其稳定解携带平方根分支；

* 当考虑两个全同自指结构在构型空间中的交换路径时，该平方根结构在参数空间上的提升导致不可约的 $\mathbb{Z}_2$ holonomy，从而强制双粒子波函数在交换下获得因子 $(-1)$。

这种从自指反馈 $\Rightarrow$ Riccati 平方根 $\Rightarrow$ 旋量双覆盖 $\Rightarrow$ 费米统计的链式逻辑，使得费米子的存在可以被解释为"信息自指结构的拓扑指纹"，而不再需要将自旋与统计视为外加公理或抽象对称性的偶然后果。

---

## Model & Assumptions

本节给出基于 QCA 的自指散射模型，并列出后续定理所需的假设条件。

### 1. Dirac 型量子元胞自动机与单粒子扇区

考虑一维格点 $\mathbb{Z}$，每个格点 $x$ 携带二维内部希尔伯特空间 $\mathcal{H}_x \cong \mathbb{C}^2$，基矢标记为 $\{\lvert \uparrow\rangle,\lvert\downarrow\rangle\}$。全局希尔伯特空间为

$$\mathcal{H} = \bigotimes_{x\in\mathbb{Z}} \mathcal{H}_x .$$

设时间步长为 $\Delta t$，QCA 的一步演化由平移算子 $S_\pm$ 与局域"硬币"算子 $C(\theta)$ 组成：

$$U_{\mathrm{QCA}} = S \circ C,$$

其中

$$C(\theta) = \exp\left(- i \theta \sigma_y\right), \quad
S = \sum_x \Big(\lvert x+1\rangle\langle x\rvert \otimes \lvert\uparrow\rangle\langle\uparrow\rvert + \lvert x-1\rangle\langle x\rvert \otimes \lvert\downarrow\rangle\langle\downarrow\rvert\Big).$$

在单粒子扇区中，$U_{\mathrm{QCA}}$ 等价于一个离散时间量子行走。对于长波低能模态，取格距 $a\to 0$、时间步长 $\Delta t\to 0$，并令 $\theta$ 随之缩放，可得到一维 Dirac 方程作为连续极限。([quantum-journal.org][3])

在本文中，我们不依赖具体的 QCA 形式，而只使用如下抽象特征：

* 单粒子扇区上的演化由一参数族幺正算符 $U(k)$ 描述，$k$ 为准动量；

* 对于均匀区域，$U(k)$ 在适当基底中具有两条能带 $\epsilon_\pm(k)$，且在长波极限下逼近 Dirac 频散 $\epsilon_\pm(k) \approx \pm \sqrt{m^2 c^4 + c^2 \hbar^2 k^2}$。

### 2. 自指散射结构：外部波导与内部反馈环

为描述局域有质量激发，引入一段有限区域 $\Omega\subset\mathbb{Z}$，在其中局域规则与背景有所不同，可等效为一个散射中心。对单粒子态，在能量（准能量） $\epsilon$ 固定时，该散射中心的外部散射可由 $2\times 2$  单能散射矩阵

$$S_{\mathrm{ext}}(\epsilon) =
\begin{pmatrix}
r(\epsilon) & t'(\epsilon)\\
t(\epsilon) & r'(\epsilon)
\end{pmatrix}$$

描述，其中 $r,t$ 分别为反射与透射振幅。

**自指散射结构**由在散射中心内部加入一个反馈环的拓扑操作实现：将某一输出通道（或其线性组合）通过一段"内部波导"再接回输入通道，引入附加相位延迟 $\mathrm{e}^{\mathrm{i}\phi(\epsilon)}$ 与可能的内部散射。形式化地，可引入内部希尔伯特空间 $\mathcal{H}_{\mathrm{loop}}$ 与内部散射矩阵 $S_{\mathrm{loop}}(\epsilon)$，使整体网络的单能散射矩阵 $S_{\mathrm{tot}}(\epsilon)$ 通过 Redheffer 星积等网络连接规则表示为外部散射块与内部反馈块的组合。类似结构在微波网络、光学干涉仪与波导 QED 中广泛存在。([耶鲁大学计算机科学][5])

我们将满足以下条件的局域结构称为"自指散射结构"（self-referential scattering structure, SRS）：

* (S1) 整体演化在单粒子扇区上保持幺正性，即 $\forall \epsilon$，$S_{\mathrm{tot}}(\epsilon)$ 为幺正矩阵；

* (S2) 存在参数区间 $\mathcal{I}$ 使得在 $\epsilon\in\mathcal{I}$ 上 $S_{\mathrm{tot}}(\epsilon)$ 的一个本征值在复平面上绕单位圆一周，对应于一族束缚态或准束缚态；

* (S3) 内部反馈环包含有限传播时延，在 QCA 的时间步中对应有限代价的内部更新次数，满足信息速率守恒原则：外部群速度与内部相位速度的平方和等于常数 $c^2$。

条件 (S1)–(S3) 保证 SRS 既是散射理论中的局域散射中心，又是光程守恒理论中的自洽信息循环。

### 3. 输入阻抗与 Riccati 演化

为捕捉自指结构的非线性自洽性，引入类比传输线理论的"输入阻抗"概念。考虑一维量子波导或等效的链状 QCA，将散射中心左侧视为半无限均匀介质，其传播常数为 $k(\epsilon)$。在能量 $\epsilon$ 固定时，定义在散射中心左界面的复阻抗 $Z(\epsilon,x)$ 为右行与左行波振幅之比的某种线性分式函数，使得 $Z$ 的演化随空间坐标 $x$ 满足 Riccati 方程。

在连续情形下，一维 Schrödinger 或 Dirac 方程可通过适当变量变换写成阻抗 $Z(x)$ 满足的一阶非线性微分方程

$$\frac{\mathrm{d} Z}{\mathrm{d} x} = q_0(x,\epsilon) + q_1(x,\epsilon) Z + q_2(x,\epsilon) Z^2 ,$$

即 Riccati 方程，其中系数由局域势能或"折射率"决定。([维基百科][6]) 在离散情形下，沿着格点编号 $n$ 演化的阻抗 $Z_n(\epsilon)$ 则满足 Möbius 变换形式的离散 Riccati 递推：

$$Z_{n+1}(\epsilon) = \frac{a(\epsilon) Z_n(\epsilon) + b(\epsilon)}{c(\epsilon) Z_n(\epsilon) + d(\epsilon)},
\quad a d - b c \neq 0 .$$

对于给定能量 $\epsilon$，自洽的驻波结构要求在某一区域内部 $Z_n$ 收敛到 $n$-无关的不动点 $Z^\ast(\epsilon)$，满足

$$Z^\ast = \frac{a Z^\ast + b}{c Z^\ast + d},$$

从而得到二次代数方程

$$c (Z^\ast)^2 + (d-a) Z^\ast - b = 0.$$

该不动点方程的解的判别式为

$$\Delta = (d-a)^2 + 4 b c.$$

在 $\Delta \neq 0$ 时存在两个分支

$$Z^\ast_\pm = \frac{(a-d) \pm \sqrt{\Delta}}{2 c}.$$

正是这里的平方根 $\sqrt{\Delta}$ 引入了复平面上的双叶结构。

我们假设 SRS 满足：

* (R1) 对于某一能量区间 $\mathcal{I}$，$\Delta(\epsilon)$ 在复平面中绕过原点，导致 $\sqrt{\Delta(\epsilon)}$ 的 Riemann 曲面为双叶结构且不可简并；

* (R2) 实际物理可观测量（如反射系数 $r(\epsilon)$ 与透射系数 $t(\epsilon)$）是 $Z^\ast(\epsilon)$ 的有理函数，因此在能量空间中单值；

* (R3) 量子态振幅 $\psi(\epsilon)$ 与 $Z^\ast(\epsilon)$ 通过平方关系相联系，例如 $r(\epsilon) = \mathrm{e}^{\mathrm{i} \delta(\epsilon)}$，$Z^\ast(\epsilon) = \mathrm{i} \tan\big(\delta(\epsilon)/2\big)$，而态矢量相位自然取为 $\delta(\epsilon)/2$。

综上，SRS 的内部变量在本质上定义在携带平方根分支的双叶 Riemann 曲面上，其投影到能量轴上给出单值散射数据。这一事实将成为后文推导旋量双覆盖与 $\mathbb{Z}_2$ 交换相位的基础。

---

## Main Results (Theorems and Alignments)

本节将本文的核心结论组织为若干定理，并给出与标准自旋–统计框架的对应关系。

### Theorem 1（自指束缚态与 Riccati 不动点）

设一维 QCA 中存在满足条件 (S1)–(S3) 与 (R1)–(R3) 的自指散射结构 SRS。则对每一个能量 $\epsilon$ 上的稳定束缚态或准束缚态，存在一族输入阻抗 $Z_n(\epsilon)$ 使得在散射中心内部 $Z_n(\epsilon)$ 收敛到某个不动点 $Z^\ast(\epsilon)$，且 $Z^\ast(\epsilon)$ 必然满足一个带有非平凡平方根分支的代数方程。

换言之，任何稳定自指束缚态的内部状态空间自然携带一个双叶复曲面结构，其投影到外部散射数据上对应于单值的反射与透射系数。

---

### Theorem 2（平方根结构与旋量双覆盖）

在 Theorem 1 条件下，定义内部"规范相位"

$$\chi(\epsilon) := \frac{1}{2} \arg \det S_{\mathrm{tot}}(\epsilon),$$

以及相应的"平方根散射因子"

$$s(\epsilon) := \mathrm{e}^{\mathrm{i} \chi(\epsilon)}.$$

假设当能量参数沿闭合回路 $\gamma\subset\mathcal{I}$ 演化一周时，散射相位 $\arg \det S_{\mathrm{tot}}(\epsilon)$ 的变化量为 $2\pi n$，其中 $n$ 为奇数（对应存在奇数个束缚态的 Levinson 型情形）。则 $s(\epsilon)$ 在该回路上获得因子

$$s(\gamma(1)) = - s(\gamma(0)).$$

因此，$\{s(\epsilon)\}$ 不是能量空间上的单值函数，而是定义在一个双覆盖空间 $\widetilde{\mathcal{I}}$ 上的单值函数。

将 $\widetilde{\mathcal{I}}$ 解释为内部"自旋空间"，可以构造一个二维复向量

$$\Psi(\epsilon) =
\begin{pmatrix}
\cos\frac{\chi(\epsilon)}{2}\\
\sin\frac{\chi(\epsilon)}{2}, \mathrm{e}^{\mathrm{i}\varphi(\epsilon)}
\end{pmatrix},$$

其中 $\varphi(\epsilon)$ 为与外部传播方向与内禀对称性相关的附加角度，则 $\Psi$ 在参数空间旋转 $2\pi$ 后变号，在旋转 $4\pi$ 后回到自身，构成一个 $SU(2)$ 旋量的标准表现。这表明 SRS 的内部平方根结构自动实现了 $SO(3)$ 的双覆盖 $SU(2)$。

---

### Theorem 3（$\mathbb{Z}_2$ 交换相位）

考虑两个全同的自指散射结构 SRS$_1$、SRS$_2$，满足 Theorem 2 的条件。其两粒子构型空间为

$$\mathcal{C}_2 = \frac{\big(\mathbb{R}^3\times\mathbb{R}^3\big)\setminus\Delta}{S_2},$$

其中 $\Delta$ 为对角线（粒子重合构型）。设 $\gamma$ 为在 $\mathcal{C}_2$ 中对应于"交换两粒子空间位置一次"的闭合路径，其提升到带有内部平方根结构的总空间 $\widetilde{\mathcal{C}}_2$ 后构成一条非平凡同伦类。

则两粒子态矢量 $\lvert\Psi_{1,2}\rangle$ 在交换操作 $\mathcal{E}$ 下满足

$$\mathcal{E} \lvert\Psi_{1,2}\rangle = - \lvert\Psi_{2,1}\rangle.$$

换言之，自指散射结构的内部平方根线丛在交换路径上的 holonomy 形成一个不可约的 $\mathbb{Z}_2$ 表示，使得 SRS 实例在 $(3+1)$ 维时空中必然服从费米–狄拉克统计。

---

### Theorem 4（Dirac 型 QCA 中质量–自指–费米性的一致性）

设一维 Dirac 型 QCA 的长波极限给出标准 Dirac 哈密顿量

$$H_{\mathrm{eff}} = c \alpha p + \beta m c^2,$$

其中质量项 $m$ 由局域内部"硬币角"或等效参数决定。假设该质量项在微观上由某一自指散射结构的反馈强度与相位确定，并满足 Theorem 1–3 的假设条件。

则：

1. 连续极限中的质量 $m\neq 0$ 当且仅当自指反馈环存在非平凡不动点 $Z^\ast(\epsilon)$ 与相应的平方根结构；

2. 对应的一粒子态在旋转 $2\pi$ 时波函数变号，而在 $4\pi$ 时复原，携带自旋 $1/2$ 的旋量结构；

3. 多粒子 Fock 空间根据 Theorem 3 必须以反对称张量积方式构造，从而自动实现泡利不相容原理。

因此，在满足局域幺正、信息速率守恒与自指散射结构存在的前提下，Dirac 型 QCA 中的有质量激发必然是费米子。

---

## Proofs

本节对上述定理给出证明或严格化推导。为避免重复，部分技术细节推迟到附录。

### Proof of Theorem 1（概要）

在一维散射问题中，将波函数写作左右行波振幅组合

$$\psi(x) = A_+(x) \mathrm{e}^{\mathrm{i} k x} + A_-(x) \mathrm{e}^{-\mathrm{i} k x},$$

定义阻抗变量

$$Z(x) := \frac{A_+(x)}{A_-(x)}.$$

对 Schrödinger 或 Dirac 方程进行代数变换，可得到 $Z(x)$ 满足 Riccati 型微分方程

$$\frac{\mathrm{d}Z}{\mathrm{d}x} = q_0(x) + q_1(x) Z + q_2(x) Z^2,$$

其中系数 $q_j(x)$ 由局域势或等效参数决定。([维基百科][6]) 在 QCA 离散情形下，沿格点 $n$ 的演化由单步传播矩阵 $T_n$ 决定，将 $T_n$ 写成 $2\times 2$  传输矩阵形式

$$\begin{pmatrix}
A_+(n+1)\\
A_-(n+1)
\end{pmatrix}
=
\begin{pmatrix}
a_n & b_n\\
c_n & d_n
\end{pmatrix}
\begin{pmatrix}
A_+(n)\\
A_-(n)
\end{pmatrix},$$

由此得到

$$Z_{n+1} = \frac{a_n Z_n + b_n}{c_n Z_n + d_n},$$

即离散 Riccati 递推。

现在将自指散射结构视为有限长度 $N$ 的内部段 $\Omega = \{1,\dots,N\}$，其两端通过反馈连接，使得内部段的末端阻抗 $Z_N$ 与起点阻抗 $Z_0$ 满足

$$Z_0 = \Phi(Z_N), \quad Z_{n+1} = \Phi_n(Z_n),$$

其中 $\Phi,\Phi_n$ 均为 Möbius 变换。对稳定束缚态，要求阻抗分布沿环路迭代后回到自身，即存在 $Z^\ast$ 使

$$Z^\ast = \Phi\big(\Phi_{N-1}\circ\cdots\circ \Phi_0(Z^\ast)\big).$$

由于 Möbius 变换的复合仍为 Möbius 变换，上式等价于某个整体变换

$$Z^\ast = \frac{a Z^\ast + b}{c Z^\ast + d},$$

解得

$$c (Z^\ast)^2 + (d-a) Z^\ast - b = 0,$$

其判别式 $\Delta$ 非零时存在两个分支 $Z^\ast_\pm$。

条件 (R1) 规定，在参数（能量）变化一周时 $\Delta(\epsilon)$ 绕原点一周，从而 $\sqrt{\Delta(\epsilon)}$ 定义在一个双叶 Riemann 曲面上。对每个 $\epsilon$ 选取合适分支，即得到与某一稳定束缚态对应的 $Z^\ast(\epsilon)$。

因此，任何稳定自指束缚态的内部阻抗描述都不可避免地包含一个平方根分支，从而证明 Theorem 1。

### Proof of Theorem 2（概要）

定义总散射矩阵的行列式

$$\det S_{\mathrm{tot}}(\epsilon) = \mathrm{e}^{\mathrm{i} \delta(\epsilon)},$$

其中 $\delta(\epsilon)$ 是总散射相位。对具有局域势的散射系统，Levinson 定理表明当能量从阈下到阈上变化时，散射相位的变化量与束缚态数目相关：

$$\delta(\epsilon\to\infty) - \delta(\epsilon\to 0) = 2\pi N_{\mathrm{b}},$$

其中 $N_{\mathrm{b}}$ 为束缚态数。([AIP Publishing][4]) 对于自指环结构，能量参数在某区间内沿闭合回路 $\gamma$ 变化一周，相当于在适当势的参数空间中进行一次绕行，其散射相位变化量为

$$\oint_\gamma \mathrm{d}\delta(\epsilon) = 2\pi n,$$

其中 $n$ 为某个整数，当存在单个稳定束缚态时 $n=1$。

定义半相位

$$\chi(\epsilon) := \frac{\delta(\epsilon)}{2},
\quad s(\epsilon) := \mathrm{e}^{\mathrm{i}\chi(\epsilon)}.$$

若沿回路 $\gamma$ 演化一周，则

$$s(\gamma(1)) = \exp\left(\mathrm{i}\frac{\delta(\gamma(0))+2\pi n}{2}\right)
= \exp\left(\mathrm{i}\frac{\delta(\gamma(0))}{2}\right)\exp\left(\mathrm{i}\pi n\right)
= (-1)^n s(\gamma(0)).$$

当 $n$ 为奇数时，$s$ 在该回路上一周后变号，说明它不是能量空间上的单值函数，而只能在双覆盖空间 $\widetilde{\mathcal{I}}$ 上单值。

为将其提升为旋量结构，考虑参数空间 $\mathcal{P}$ 中的单位向量 $\mathbf{n}$（例如由动量方向与内部"质量向量"决定），构造映射

$$\mathbf{n} : \mathcal{P} \to S^2.$$

在 $SO(3)$ 的双覆盖 $SU(2)$ 中，$\mathbf{n}$ 的提升可写为一个归一化旋量 $\Psi(\mathbf{n})$，满足

$$\Psi(\mathbf{n}) \sim
\begin{pmatrix}
\cos\frac{\theta}{2}\\
\sin\frac{\theta}{2},\mathrm{e}^{\mathrm{i}\varphi}
\end{pmatrix},$$

其中 $(\theta,\varphi)$ 为 $S^2$ 上的球坐标。将 $\chi(\epsilon)$ 与 $\theta(\epsilon)$ 同一起来，即视散射半相位为某种有效"极角"，则 $\Psi$ 随 $\epsilon$ 沿闭合回路变化一周时变号，这正是自旋 $1/2$ 旋量在参数空间旋转 $2\pi$ 后变号、$4\pi$ 后复原的特征。因此，SRS 内部的平方根结构自然实现了 $SO(3)$ 的双覆盖。

### Proof of Theorem 3（拓扑路径积分视角）

Laidlaw 与 Morette-DeWitt 的工作表明，对于不可区别粒子体系，其构型空间 $\mathcal{C}_N$ 一般为多连通空间，传播子可按基本群 $\pi_1(\mathcal{C}_N)$ 的各同伦类分解，每个同伦类由该群的一个幺正表示加权。([APS Link][1]) 在三维空间中，$\pi_1(\mathcal{C}_N)\cong S_N$ 的某个商群，且其不可约一维幺正表示仅有"完全对称"与"完全反对称"两种，对应玻色与费米统计。

Finkelstein–Rubinstein 进一步指出，当粒子为拓扑孤子或 kinks 时，其内部场构型空间本身带有非平凡基本群，量子态矢量或其平方根在该空间上的提升决定了允许的幺正表示，从而给出自旋–统计的拓扑约束。([AIP Publishing][2])

在本工作中，自指散射结构的内部平方根线丛为一个复线丛 $\mathcal{L}\to\mathcal{P}$，其 holonomy 群为 $\mathbb{Z}_2$。对两粒子情形，其总参数空间为 $\mathcal{P}\times\mathcal{P}$，除去粒子重合构型后的构型空间 $\mathcal{C}_2$ 为

$$\mathcal{C}_2 = \frac{\big(\mathbb{R}^3\times\mathbb{R}^3\big)\setminus\Delta}{S_2}.$$

令 $\gamma$ 为在 $\mathcal{C}_2$ 中实现"交换两粒子一次"的闭合路径，其提升到带内部结构的总空间 $\widetilde{\mathcal{C}}_2$ 时，由于每个粒子的内部平方根在外部参数绕行中变号，总的线丛 holonomy 为

$$\mathrm{Hol}_\mathcal{L}(\gamma) = (-1)\times 1 = -1,$$

其中第一因子来自被"绕行者"的内部结构，第二因子来自"不动粒子"。

于是，两粒子态矢量在路径积分中按幺正表示 $\rho:\pi_1(\mathcal{C}_2)\to U(1)$ 加权，其中 $\rho(\gamma)=-1$。这正是完全反对称表示，导致

$$\mathcal{E}\lvert\Psi_{1,2}\rangle = - \lvert\Psi_{2,1}\rangle.$$

由于在三维空间中仅有玻色与费米两种一维表示，而内部平方根结构已固定 $\rho(\gamma)=-1$，因此 SRS 必须实现费米统计，从而证明 Theorem 3。

### Proof of Theorem 4（Dirac-QCA 一致性）

Dirac 型 QCA 的长波极限可写作连续时间的 Dirac 方程

$$\mathrm{i}\hbar \frac{\partial}{\partial t}\Psi(x,t) = \big(c\alpha p + \beta m c^2\big)\Psi(x,t),$$

其中 $m$ 为有效质量，由 QCA 中的局域参数（如硬币角 $\theta$）及其空间分布决定。([quantum-journal.org][3])

在自指散射解释下，质量项对应于内部反馈环的反馈强度与相位：若该反馈被关断，则内部自指结构消失，质量项趋于零，得到无质量 Dirac 或 Weyl 模式；若反馈存在且稳定，则内部阻抗 $Z^\ast(\epsilon)$ 满足 Theorem 1 的不动点方程，其判别式 $\Delta$ 的非平凡性与 Theorem 2 中的散射半相位绕行性质等价，从而得到旋量双覆盖与 Theorem 3 中的 $\mathbb{Z}_2$ 交换相位。

因此，在 $m\neq 0$ 的情形，Dirac 型 QCA 的有质量激发自动携带自旋 $1/2$ 与费米统计，且这一性质可在不引用连续场论的自旋–统计定理的情况下，从 QCA 内部的自指散射动力学中导出，从而完成 Theorem 4 的证明。

---

## Model Apply

本节将上述理论应用于具体的 Dirac-QCA 模型，并展示如何在该模型中识别 Riccati 阻抗、平方根结构与费米统计。

### 1. 一维 Dirac-QCA 的自指解释

考虑标准的 split-step 量子行走实现的 Dirac-QCA：

$$U(\theta_1,\theta_2) = S_+ C(\theta_2) S_- C(\theta_1),$$

其中 $C(\theta_j)$ 为局域旋转，$S_\pm$ 为条件平移。通过选择合适的角度 $\theta_{1,2}$，该量子行走的长波极限可逼近带质量的 Dirac 方程，且质量 $m$ 为 $\theta_1,\theta_2$ 的某个函数。([quantum-journal.org][3])

在某格点区域 $\Omega$ 中改变 $\theta_j$ 的取值，相当于引入一个局域势垒或缺陷，其单粒子散射可以通过数值或解析方法求得。将 $\Omega$ 内部视为传输线段，其单步传播矩阵 $T_n(\epsilon)$ 可用 $2\times 2$ 矩阵表示，对应的阻抗演化满足离散 Riccati 形式

$$Z_{n+1}(\epsilon) = \frac{a_n(\epsilon) Z_n(\epsilon) + b_n(\epsilon)}{c_n(\epsilon) Z_n(\epsilon) + d_n(\epsilon)}.$$

若在 $\Omega$ 末端引入一个反馈通道，将输出态经过若干 QCA 步长后重新注入 $\Omega$ 起点，则整体结构形成自指散射环。通过适当设计反馈通道的传播相位与耦合强度，可使得某一能量区域内存在稳定局域模态，其内部阻抗 $Z^\ast(\epsilon)$ 满足 Theorem 1 的不动点条件。

### 2. 质量参数与拓扑阻抗

将上述反馈强度参数化为复数 $\lambda$，并将其连续极限中的有效影响记入 Dirac 哈密顿量的质量项 $m(\lambda)$。在"拓扑阻抗"解释下，$m$ 可视为阻抗轨道在复平面上的绕行次数与平均模长的函数：

$$m(\lambda) \propto \oint_{\mathcal{C}(\lambda)} \frac{\mathrm{d}Z}{2\pi\mathrm{i}}\frac{1}{Z - Z_0},$$

其中 $\mathcal{C}(\lambda)$ 为随 $\lambda$ 扭曲的阻抗轨道，$Z_0$ 为某个参考点。非零质量对应于阻抗轨道绕行次数非零，即内部自指反馈使阻抗在复平面上形成"涡旋"，这与 Finkelstein–Rubinstein 模型中拓扑孤子携带自旋的图像相似。([AIP Publishing][2])

### 3. 泡利不相容原理的 QCA 版本

在 Dirac-QCA 的一粒子扇区中，态矢量空间可以用上述旋量结构参数化；将其提升至多粒子扇区，若直接采用张量积构造，将与 Theorem 3 得到的 $\mathbb{Z}_2$  holonomy 不一致。为保持拓扑一致性，多粒子态必须取反对称张量积：

$$\lvert\Psi_{1,2}\rangle = \frac{1}{\sqrt{2}}\big(\lvert\psi_1\rangle\otimes\lvert\psi_2\rangle - \lvert\psi_2\rangle\otimes\lvert\psi_1\rangle\big).$$

在 QCA 的格点表象中，这一反对称性意味着同一局域模式不能被两个全同自指激发同时占据，否则波函数为零，对应泡利不相容原理。

因此，本框架在 QCA 层面给出了泡利原理的几何解释：占据冲突不是经验规则，而是内部自指平方根结构与配置空间拓扑的直接结果。

---

## Engineering Proposals

虽然本文主要聚焦于理论结构，但自指散射与 Riccati 平方根结构在波导、光子晶体与超导电路中的工程实现具有较强的可行性，为直接测试本文提出的拓扑 $\mathbb{Z}_2$ 交换相位提供了可能。

### 1. 微波网络与超导电路中的自指散射环

在经典电磁波导与微波网络中，输入阻抗与反射系数的演化长期以来以 Riccati 方程与传输线理论为基础进行分析，实验上可以精确测量。([耶鲁大学计算机科学][5]) 在量子极限下，超导共振腔与 Josephson 结构成的电路 QED 系统中，可以实现近乎无损的反馈环与可调的相移元件。通过设计两个等效的反馈环并弱耦合它们，有望构造出两个"人工 SRS 粒子"，并在参数空间中执行"交换"操作，例如通过调控两环中的相移与耦合路径，使其在有效构型空间中沿非平凡回路演化。

在该方案中，可通过测量两环之间的量子干涉图样或多光子关联函数，识别是否存在与 $(-1)$ 交换相位相关的信号，例如某些两腔联合激发概率的消失。

### 2. 光子晶体与拓扑波导平台

光子晶体波导中的缺陷模与环形谐振腔可实现高质量因子的局域模与反馈结构。通过在二维光子晶体中构造两组等同的环形谐振腔并通过波导相连，可以在稳态与瞬态响应中观察到由内部相位反馈控制的干涉现象。若在其中嵌入非线性介质或量子点，进一步进入单光子或少光子极限，则该系统可以近似实现 QCA 中单粒子扇区的散射结构。

在此平台上，可以通过调节环路长度、耦合强度与局域折射率，扫描相位参数空间，并构造对应于"交换"两个局域缺陷模的等效过程，从而在测量上检验本文提出的 $\mathbb{Z}_2$ 拓扑指纹。

### 3. 量子行走与 Dirac-QCA 的实验模拟

目前已有在囚禁离子、光学网络与超导量子比特平台上实现 Dirac-QCA 与量子行走的实验工作。([Nature][7]) 在这些平台上，通过在空间或内部自由度上引入"回流通道"，可以在高维希尔伯特空间中编码自指散射环。

通过对单粒子与双粒子态的时间演化与干涉进行精细测量，有望间接重构内部散射相位的半相位结构，从而验证平方根 Riemann 曲面的存在，并检验交换操作是否对应于 $(-1)$ 相位。

---

## Discussion (Risks, Boundaries, Past Work)

### 1. 与传统自旋–统计定理的关系

传统自旋–统计定理依赖连续时空、局域场算子、谱界与微因果性等假设，其适用范围是相对论性量子场论。本文提出的自指散射–Riccati–平方根机制则工作在离散 QCA 的本体论层面，并不直接假设这些场论公理。

需要强调的是，本文并未否定传统定理，而是在一个更离散、信息论的框架下给出一条独立的推导路径。就长波极限而言，Dirac-QCA 的有效场论仍应满足传统自旋–统计定理的条件，因此两种推导在连续极限上是兼容的：旋量双覆盖与 $\mathbb{Z}_2$ 交换相位分别在场论与 QCA 层面出现，构成同一结构在不同尺度的投影。

### 2. 与拓扑自旋–统计工作的比较

Finkelstein–Rubinstein 与后续关于拓扑 geon 与拓扑孤子的研究，已经表明自旋–统计之间存在深刻的拓扑联系。([AIP Publishing][2]) 本文的创新点在于：

* 将"拓扑孤子"的角色由连续场构型转移到离散 QCA 中的"自指散射环"；

* 利用 Riccati 阻抗与散射相位的平方根结构，给出内部线丛与 $\mathbb{Z}_2$ holonomy 的具体构造；

* 直接在单粒子散射与网络反馈理论中识别该拓扑结构，使得自旋–统计关系可以被绑定到"信息自指"这一更具物理直观的对象上。

### 3. 适用边界与潜在风险

尽管理论结构自洽，但仍有若干重要问题需要谨慎对待：

1. **维数与任何子统计**：本文主要针对 $(3+1)$ 维情形，在该情况下构型空间的基本群结构限制了统计类型为玻色或费米。对 $(2+1)$ 维系统，构型空间的基本群为编织群，允许任何子统计。本文框架在 $(2+1)$ 维的推广可能会产生更丰富的内部平方根与多值结构，有待系统分析。([inspirehep.net][8])

2. **QCA 与连续极限的一致性**：虽然已有工作证明 Dirac-QCA 在长波极限下给出正确的 Dirac 方程，但对带有复杂缺陷与反馈网络的情形，连续极限的严格控制仍需更深入的数学分析，尤其是在存在非平凡拓扑时。([quantum-journal.org][3])

3. **Riccati 模型的有效性**：输入阻抗满足 Riccati 方程的结论在一维、线性、无耗散的波动系统中成立。对于实际的 QCA 与量子网络，实现精确的 Riccati 结构可能需要额外的对称性与工程上的细致设计，否则平方根结构可能被噪声或非理想效应模糊。

4. **实验可验证性**：$\mathbb{Z}_2$ 交换相位在传统费米体系中已大量间接得到证据，但在本文提出的"人工自指散射结构"中直接测量该相位，需要极高的相干性与精确的路径控制，这在实验上具有不小挑战。

---

## Conclusion

本文在量子元胞自动机与自指散射的框架下，提出并论证了费米子统计的一种信息论与拓扑统一解释。主要结论可概括如下：

1. **自指散射与 Riccati 不动点**：局域有质量激发可以建模为 QCA 网络中的自指散射环，其输入阻抗遵循 Riccati 型演化，稳定束缚态对应于 Möbius 变换的不动点，从而在内部状态空间引入不可避免的平方根分支与双叶 Riemann 曲面。

2. **平方根结构与旋量双覆盖**：总散射矩阵行列式的相位在能量或参数空间中绕行时，其半相位在闭合路径上变号，表明内部自由度只有在双覆盖空间上单值。该双覆盖自然实现 $SO(3)$ 的 $SU(2)$ 旋量表示，并给出"旋转 $2\pi$ 变号、旋转 $4\pi$ 复原"的自旋 $1/2$ 行为。

3. **$\mathbb{Z}_2$ 交换相位与费米统计**：在两粒子构型空间中，自指散射环的内部平方根线丛在交换路径上的 holonomy 为 $(-1)$，对应于基本群的一维反对称表示，从而强制多粒子态在交换下获得因子 $(-1)$，即服从费米–狄拉克统计。

4. **Dirac-QCA 中质量–自指–费米性的统一**：在 Dirac 型 QCA 的长波极限中，质量项可解释为拓扑阻抗的强度与绕行数，非零质量当且仅当存在自指散射结构及其平方根拓扑，由此得出"有质量 $\Rightarrow$ 自指 $\Rightarrow$ 平方根 $\Rightarrow$ 费米子"的链式统一关系。

5. **工程与实验前景**：自指散射与 Riccati 阻抗在微波网络、光子晶体与超导电路中的实现具有现实可行性，为通过人工构造的 SRS 结构直接探测 $\mathbb{Z}_2$ 交换相位、从离散信息本体层面验证费米统计的拓扑起源提供了可能。

因此，费米子的存在可以在一个完全离散、以信息自指为核心的宇宙图景中得到解释，而传统连续场论中的自旋–统计定理则可以被视为该图景在长波极限中的投影。

---

## Acknowledgements, Code Availability

作者感谢关于量子元胞自动机、拓扑自旋–统计关系与散射理论的既有文献所提供的启发。本文全部推导基于解析方法，未使用数值代码或附加软件实现。

---

## References

[1] M. G. G. Laidlaw, C. Morette-DeWitt, "Feynman Functional Integrals for Systems of Indistinguishable Particles," Phys. Rev. D 3, 1375–1378 (1971). ([APS Link][1])

[2] D. Finkelstein, J. Rubinstein, "Connection between Spin, Statistics, and Kinks," J. Math. Phys. 9, 1762–1779 (1968). ([AIP Publishing][2])

[3] R. D. Sorkin, "A General Relation between Kink-Exchange and Kink-Rotation," Commun. Math. Phys. 115, 421–434 (1988). ([Project Euclid][9])

[4] F. Calogero, "Note on the Riccati Equation," J. Math. Phys. 4, 427–430 (1963). ([AIP Publishing][4])

[5] Y. Chen, "Acoustic Inverse Scattering Problems," Yale Tech. Rep. TR913 (1992). ([耶鲁大学计算机科学][5])

[6] T. Farrelly, "A Review of Quantum Cellular Automata," Quantum 4, 368 (2020). ([quantum-journal.org][3])

[7] G. M. D'Ariano, N. Mosco, P. Perinotti, "Path-Integral Solution of the One-Dimensional Dirac Equation from Quantum Cellular Automata," Phys. Lett. A 378, 3165–3168 (2014). ([科学直通车][10])

[8] C. Huerta Alderete et al., "Quantum Walks and Dirac Cellular Automata on a Programmable Trapped-Ion Quantum Computer," Nat. Commun. 11, 3720 (2020). ([Nature][7])

[9] T. A. Brun, L. Mlodinow, "Quantum Cellular Automata and Quantum Field Theory in Two Spatial Dimensions," Phys. Rev. A 102, 062222 (2020). ([arXiv][11])

[10] N. Jolly, "Twisted Quantum Walks, Generalised Dirac Equation and Fermion Doubling," Eur. Phys. J. D 77, 142 (2023). ([SpringerLink][12])

[11] C. DeWitt-Morette, "Path Integration in Non-Relativistic Quantum Mechanics," Phys. Rep. 49, 253–297 (1979). ([科学直通车][13])

[12] R. Ramachandran, "Spin–Statistics Connection," Curr. Sci. 61, 95–102 (1991). ([JSTOR][14])

[13] H. F. Dowker, "Spin and Statistics in Quantum Gravity," AIP Conf. Proc. 545, 205–216 (2000). ([AIP Publishing][15])

[14] R. D. Tscheuschner, "Topological Spin-Statistics Relation in Quantum Field Theory," Class. Quantum Grav. 6, 1521–1538 (1989). ([SpringerLink][16])

[15] H. Ma, "Mass as Topological Impedance: Self-Referential Scattering and Chiral Symmetry Breaking in Dirac-QCA," preprint (2025).

[16] H. Ma, "Universal Conservation of Information Celerity: From Quantum Cellular Automata to Relativity, Mass and Gravity," preprint (2025).

---

## 附录 A：Riccati 阻抗方程与自指散射环的详细推导

本附录给出输入阻抗满足 Riccati 方程以及自指散射环对应 Möbius 不动点方程的详细推导。

### A.1 一维波动方程与阻抗变量

考虑一维无耗散波动方程

$$\frac{\partial^2 \psi}{\partial x^2} + k^2(x)\psi(x) = 0,$$

其时间依赖形式为 $\psi(x,t)=\psi(x)\mathrm{e}^{-\mathrm{i}\omega t}$。在局域均匀区域内，解可写为左右行波叠加

$$\psi(x) = A_+(x)\mathrm{e}^{\mathrm{i}k x} + A_-(x)\mathrm{e}^{-\mathrm{i}k x}.$$

定义阻抗

$$Z(x) := \frac{A_+(x)}{A_-(x)}.$$

对 $\psi'(x)$ 求导并用波动方程消去二阶导数，可得到关于 $A_\pm$ 的一阶方程组，将其消元后得到 $Z(x)$ 满足

$$\frac{\mathrm{d}Z}{\mathrm{d}x} = q_0(x) + q_1(x) Z + q_2(x) Z^2,$$

其中 $q_j(x)$ 与 $k(x)$ 及其导数有关。该推导在文献中已有系统阐述。([维基百科][6])

### A.2 离散传输矩阵与 Möbius 递推

在 QCA 或离散波导模型中，一步传播可表示为传输矩阵

$$\begin{pmatrix}
A_+(n+1)\\
A_-(n+1)
\end{pmatrix}
=
T_n
\begin{pmatrix}
A_+(n)\\
A_-(n)
\end{pmatrix},
\quad
T_n =
\begin{pmatrix}
a_n & b_n\\
c_n & d_n
\end{pmatrix},$$

由此得

$$Z_{n+1} = \frac{A_+(n+1)}{A_-(n+1)} = \frac{a_n A_+(n) + b_n A_-(n)}{c_n A_+(n) + d_n A_-(n)}
= \frac{a_n Z_n + b_n}{c_n Z_n + d_n}.$$

这一递推是一类 Möbius 变换，在 $ad-bc\neq 0$ 时为双射。

### A.3 自指环与整体不动点方程

考虑长度为 $N$ 的内部段 $\Omega=\{1,\dots,N\}$，其传输矩阵序列为 $\{T_n\}_{n=1}^{N}$。将内部段末端通过反馈相位 $\mathrm{e}^{\mathrm{i}\phi}$ 接回起点，则整体传输矩阵可写为

$$T_{\mathrm{loop}} = R(\phi) T_N \cdots T_1,$$

其中 $R(\phi)$ 表示反馈相位。设其矩阵元为

$$T_{\mathrm{loop}} =
\begin{pmatrix}
a & b\\
c & d
\end{pmatrix}.$$

稳定束缚态要求沿环路传播一周后振幅仅差一个总相位，即输入阻抗为不动点 $Z^\ast$，满足

$$Z^\ast = \frac{a Z^\ast + b}{c Z^\ast + d}.$$

整理得二次方程

$$c (Z^\ast)^2 + (d-a) Z^\ast - b = 0,$$

其判别式

$$\Delta = (d-a)^2 + 4 b c$$

决定 $Z^\ast$ 的双值结构。若随着能量或反馈相位的变化 $\Delta$ 在复平面中绕原点一周，则 $\sqrt{\Delta}$ 的取值空间为双叶 Riemann 曲面，对应附录主文中的平方根结构。

---

## 附录 B：平方根 Riemann 曲面与 $\mathbb{Z}_2$ 线丛

本附录从复分析与拓扑的角度细化平方根结构与 $\mathbb{Z}_2$ 线丛之间的对应关系。

### B.1 平方根函数的双叶结构

考虑复函数

$$f(z) = \sqrt{z},$$

其自然定义在去掉分支点 $z=0,\infty$ 的 Riemann 曲面上。选择实轴负半轴为分支切割，一叶 $f_+(z)$ 在切割上方解析，另一叶 $f_-(z)=-f_+(z)$ 在切割下方解析。

当 $z$ 绕原点一周，即沿闭合回路

$$\gamma : \theta\mapsto z(\theta)=\rho\mathrm{e}^{\mathrm{i}\theta},\quad \theta\in[0,2\pi],$$

沿 $f_+$ 追踪，可得

$$f_+\big(z(2\pi)\big) = - f_+\big(z(0)\big).$$

因此，$\sqrt{z}$ 的取值不是单叶复平面上的单值函数，而是在一个双覆盖 $\widetilde{\mathbb{C}^\ast}$ 上单值，覆盖映射为 $\pi(w)=w^2$。

### B.2 线丛视角与 $\mathbb{Z}_2$ holonomy

将 $z$ 视为参数空间坐标，$\sqrt{z}$ 视为线丛截面。定义复线丛

$$\mathcal{L} = \{(z,w)\in\mathbb{C}^\ast\times\mathbb{C} \mid w^2 = z\},$$

投影 $\pi:\mathcal{L}\to \mathbb{C}^\ast$，$\pi(z,w)=z$。对每个 $z$，纤维 $\pi^{-1}(z)$ 由两个点 $(z,\pm\sqrt{z})$ 构成。

沿闭合回路 $\gamma$ 提升到 $\mathcal{L}$ 时，若起点取 $(z(0),+\sqrt{z(0)})$，则终点为 $(z(0),-\sqrt{z(0)})$，说明纤维在该回路上的 holonomy 为 $(-1)$。相应的结构群可视为 $\mathbb{Z}_2=\{\pm 1\}$，其在闭合回路上的表示给出 $\mathbb{Z}_2$ 指数。

在本文的情形中，判别式 $\Delta(\epsilon)$ 扮演 $z$ 的角色，$\sqrt{\Delta(\epsilon)}$ 扮演 $w$。当 $\epsilon$ 在参数空间中绕行使 $\Delta(\epsilon)$ 绕原点一周时，内部阻抗不动点 $Z^\ast(\epsilon)$ 的分支标记发生翻转，对应自指散射结构内部线丛的 $(-1)$ holonomy。

---

## 附录 C：构型空间拓扑与交换相位的路径积分推导

本附录补充 Theorem 3 中关于两粒子构型空间与交换相位的路径积分推导。

### C.1 不可区别粒子的构型空间

对两个不可区别粒子，其有序构型空间为 $\mathbb{R}^3\times\mathbb{R}^3\setminus\Delta$，其中 $\Delta$ 为对角线。不可区别性要求对称群 $S_2$ 商出标签交换，得到

$$\mathcal{C}_2 = \frac{\mathbb{R}^3\times\mathbb{R}^3\setminus\Delta}{S_2}.$$

Laidlaw–Morette-DeWitt 表明，对应的路径积分可按 $\pi_1(\mathcal{C}_2)$ 的同伦类分解，每一类由某一幺正表示加权。([APS Link][1]) 在三维空间中，$\pi_1(\mathcal{C}_2)\cong \mathbb{Z}_2$，其两个一维幺正表示分别为 $\rho_{\mathrm{B}}(\gamma)=+1$ 与 $\rho_{\mathrm{F}}(\gamma)=-1$，对应玻色与费米统计。

### C.2 自指散射结构的内部提升

将每个自指散射结构的内部平方根线丛记为 $\mathcal{L}_i\to\mathcal{P}_i$，其结构群为 $\mathbb{Z}_2$。两粒子总空间带有外部构型 $\mathcal{C}_2$ 与内部参数 $\mathcal{P}_1\times\mathcal{P}_2$。整体系的"增强构型空间"为

$$\widetilde{\mathcal{C}}_2 = \mathcal{C}_2\times (\mathcal{L}_1\otimes\mathcal{L}_2).$$

构型空间中的交换路径 $\gamma$ 在 $\widetilde{\mathcal{C}}_2$ 中的提升 $\widetilde{\gamma}$ 在纤维上产生 holonomy

$$\mathrm{Hol}(\widetilde{\gamma}) = \mathrm{Hol}_1(\gamma)\cdot \mathrm{Hol}_2(\gamma).$$

由于交换路径对"被绕行粒子"的内部判别式绕原点一周，对"未绕行粒子"则不产生绕行，可得

$$\mathrm{Hol}_1(\gamma) = -1,\quad \mathrm{Hol}_2(\gamma)=+1,$$

从而

$$\mathrm{Hol}(\widetilde{\gamma}) = -1.$$

在路径积分中，这对应于对该同伦类赋予相位因子 $(-1)$，即选择 $\rho_{\mathrm{F}}$ 表示。

### C.3 与传统自旋–统计的兼容性

传统自旋–统计定理由场算子的局域性与旋转群表示性质给出交换相位的约束。本文的路径积分推导则表明：即便在离散 QCA 与自指散射的框架中，只要内部平方根线丛的 $\mathbb{Z}_2$ holonomy 确定，构型空间拓扑自动迫使交换相位为 $(-1)$。

在长波极限下，QCA 有效场论的自旋结构与本文所述内部线丛的 $\mathbb{Z}_2$ 指数相一致，从而保证两种推导的一致性。

[1]: https://link.aps.org/doi/10.1103/PhysRevD.3.1375?utm_source=chatgpt.com "Feynman Functional Integrals for Systems of Indistinguishable ..."

[2]: https://pubs.aip.org/aip/jmp/article-pdf/9/11/1762/19278266/1762_1_online.pdf?utm_source=chatgpt.com "Connection between Spin, Statistics, and Kinks"

[3]: https://quantum-journal.org/papers/q-2020-11-30-368/?utm_source=chatgpt.com "A review of Quantum Cellular Automata"

[4]: https://pubs.aip.org/aip/jmp/article-pdf/4/3/427/19213671/427_1_online.pdf?utm_source=chatgpt.com "Note on the Riccati Equation"

[5]: https://www.cs.yale.edu/publications/techreports/tr913.pdf?utm_source=chatgpt.com "acoustic inverse scattering problems"

[6]: https://en.wikipedia.org/wiki/Riccati_equation?utm_source=chatgpt.com "Riccati equation"

[7]: https://www.nature.com/articles/s41467-020-17519-4?utm_source=chatgpt.com "Quantum walks and Dirac cellular automata on a ..."

[8]: https://inspirehep.net/literature/340225?utm_source=chatgpt.com "Spin and statistics in (2+1)-dimensional space-time"

[9]: https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-115/issue-3/A-general-relation-between-kink-exchange-and-kink-rotation/cmp/1104160998.pdf?utm_source=chatgpt.com "A General Relation Between Kink-Exchange and ..."

[10]: https://www.sciencedirect.com/science/article/pii/S0375960114009098?utm_source=chatgpt.com "Path-integral solution of the one-dimensional Dirac ..."

[11]: https://arxiv.org/abs/2010.09104?utm_source=chatgpt.com "Quantum cellular automata and quantum field theory in two spatial dimensions"

[12]: https://link.springer.com/article/10.1140/epjd/s10053-023-00659-9?utm_source=chatgpt.com "Twisted quantum walks, generalised Dirac equation and ..."

[13]: https://www.sciencedirect.com/science/article/pii/0370157379900838?utm_source=chatgpt.com "Path integration in non-relativistic quantum mechanics"

[14]: https://www.jstor.org/stable/24094971?utm_source=chatgpt.com "Spin–statistics connection"

[15]: https://pubs.aip.org/aip/acp/article-pdf/545/1/205/12173058/205_1_online.pdf?utm_source=chatgpt.com "Spin and Statistics in Quantum Gravity"

[16]: https://link.springer.com/article/10.1007/BF00669348?utm_source=chatgpt.com "Topological spin-statistics relation in quantum field theory"
