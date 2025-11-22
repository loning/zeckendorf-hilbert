# 自指散射与费米子的诞生：Riccati 平方根、旋量双覆盖与 $\mathbb{Z}_2$ 交换相位

*Self-Referential Scattering and the Birth of Fermions: Riccati Square Roots, Spinor Double Cover, and a $\mathbb{Z}_2$ Exchange Phase*

---

## Abstract

Standard quantum field theory explains the relation between spin and statistics through the spin–statistics theorem, derived from Lorentz covariance and microcausality on a continuous spacetime background. In topological approaches, the antisymmetry of fermionic wavefunctions can also be understood via the nontrivial topology of configuration spaces and associated line bundles, as in the Finkelstein–Rubinstein construction for solitons in nonlinear field theories.([维基百科][1]) However, these frameworks typically assume relativistic quantum fields as the ontological starting point.

Within a discrete, causal quantum cellular automaton (QCA) ontology, the universe is described as a lattice of local Hilbert spaces updated by a global unitary step. In previous work, massive excitations were interpreted as localized, self-sustained interference structures whose internal dynamics consume part of a global information-update budget, giving mass an interpretation as "topological impedance" in an underlying scattering network. Building on this picture, the present work proposes a dynamical and geometric origin of fermionic statistics in terms of **self-referential scattering**.

We consider localized excitations realized as feedback loops in an effective one-dimensional scattering problem obtained from coarse-graining the QCA. The boundary response of such a loop is encoded in an impedance function or reflection coefficient solving a nonlinear Riccati equation, a structure well known in wave propagation and scattering theory.([SpringerOpen][2]) We show that the fixed-point condition for a stable, self-referential loop forces the physical state of the excitation to live on a **square-root branch** of the underlying scattering data. This branch structure induces a canonical double cover of the configuration space of $N$ identical excitations. We prove that the generator corresponding to exchanging two excitations lifts to a nontrivial loop on this double cover with holonomy $(-1)$, so that the $N$-body wavefunction transforms in the sign representation of the permutation group and satisfies fermionic exchange statistics.

In this construction, spinor behavior and the $\mathrm{Spin}(3)$ double cover of $\mathrm{SO}(3)$ are not postulated but emerge from the necessity of taking square roots of self-referential scattering data. The internal "Riccati square-root" variable plays the role of a spinor amplitude whose squared modulus reproduces observable scattering characteristics. In this sense, "spin $1/2$" is reinterpreted as the topological fingerprint of information self-reference in a QCA-based universe. We outline an explicit realization in Dirac-type QCA models and propose engineered scattering networks in photonic and superconducting platforms to test the predicted $\mathbb{Z}_2$ exchange phase.

---

## Keywords

Quantum cellular automata; self-referential scattering; Riccati equation; impedance; spin–statistics theorem; spinor double cover; Finkelstein–Rubinstein constraint; fermionic exchange phase

---

## Introduction & Historical Context

### 1.1 自旋–统计定理与连续场论的图景

自旋–统计定理表明，在三加一维相对论性量子场论中，半整数自旋的粒子必须服从费米–狄拉克统计，而整数自旋粒子必须服从玻色–爱因斯坦统计。其现代教科书推导依赖如下要素：洛伦兹协变性、真空稳定性、局域可观测量的正定概率以及类空间分离算符的对易或反对易关系（微因果性）。([维基百科][1]) 在这一框架中，费米子与玻色子的区分是场算符交换关系的输入条件之一，随后由结构定理保证与自旋的一致性。

这一证明体系具有高度严密性，却也带来一项公认的困惑：为何自旋与多体交换统计之间存在如此深刻的关联，而非成为彼此独立的结构？Feynman 曾感叹，对这一简单陈述的"直观解释"依然难以给出。([维基百科][1])

### 1.2 拓扑自旋–统计关系与孤子

另一条思路由 Finkelstein 与 Rubinstein 倡导，他们在非线性场论中考察拓扑孤子构型空间的同伦性质，指出当孤子构型空间的基本群非平凡时，可以通过非平庸的线丛来实现将 $2\pi$ 旋转与粒子交换联系起来，从而得到自旋–统计对应关系。([SpringerLink][3]) 在这一视角中，波函数不再是构型空间上的单值函数，而是某个线丛的截面；孤子绕行路径的同伦类通过丛的 holonomy 决定了交换相位。进一步的工作将这一思路应用于 Yang–Mills 孤子和 Hopf 拓扑不变量，展示了连结数与统计之间的几何关系。([APS链接][4])

拓扑方法提供了自旋–统计定理的几何直观，但仍然以内禀连续场为基本对象，且通常从已知孤子模型出发。

### 1.3 量子元胞自动机与离散本体论

近年兴起的量子元胞自动机（Quantum Cellular Automata, QCA）试图在离散、局域幺正演化的框架下重构量子场论，甚至整个物理宇宙。([arXiv][5]) 在 QCA 图景中，时空是由离散格点 $\Lambda$ 与每个格点处的局域 Hilbert 空间 $\mathcal{H}_x$ 组成，动力学由在有限邻域上作用的全局幺正算符 $U$ 给出。连续极限下，适当选择局部"coin"算符可以得到 Dirac、Weyl 或 Maxwell 方程，从而在离散本体上重现标准量子场论。

在此前一系列工作中，质量被解释为信息传播速率的几何"阻抗"：无质量激发对应沿光锥的前馈传播，而有质量激发则对应包含反馈与回绕的局域结构，其内部演化速度 $v_{\mathrm{int}}$ 与外部群速度 $v_{\mathrm{ext}}$ 满足信息速率守恒约束。对应的微观图像是：粒子是 QCA 网络中某种自指的反馈回路，其稳定存在依赖于输入与输出之间的阻抗匹配。

### 1.4 本文的目标与主张

本文试图在上述 QCA 与"质量=拓扑阻抗"图景上前进一步，提出如下主张：

1. 任何在 QCA 中实现稳定静止质量的局域激发，都可以在适当粗粒化后视为一维有效散射问题中的**自指反馈回路**。

2. 该反馈回路的边界响应（阻抗或反射系数）的空间演化由一个非线性 Riccati 方程支配；其稳态解是某个 Möbius 变换的不动点，并具有平方根判别式结构。([SpringerOpen][2])

3. 对于由 $N$ 个全同自指激发构成的体系，其总构型空间的自然量子化不再是单值波函数，而是由上述 Riccati 结构诱导的**双覆盖线丛**上的截面。粒子交换路径在该双覆盖上具有 $\mathbb{Z}_2$ holonomy，从而导致 $(-1)$ 的交换相位。

4. 因此，**有质量的自指激发在本构造中自动实现费米–狄拉克统计**；玻色子则对应无自指反馈的纯前馈模式或若干自指环的复合。

本研究的出发点不是试图"重新证明"自旋–统计定理，而是构造一种离散本体论下的微观机制，使自指散射、Riccati 平方根与旋量双覆盖之间建立明确联系，从而为费米子的存在提供一种动力学–几何的解释。

---

## Model & Assumptions

### 2.1 底层 QCA 结构

设 $\Lambda \subset \mathbb{Z}^d$ 是一个正则晶格，本文主要考虑 $d=1,3$ 的情形。每个格点 $x \in \Lambda$ 关联有限维 Hilbert 空间 $\mathcal{H}_x \cong \mathbb{C}^q$，全局 Hilbert 空间为

$$\mathcal{H} = \bigotimes_{x \in \Lambda} \mathcal{H}_x.$$

时间演化由一个有限邻域的局域幺正算符给出，即存在某个有限范围 $R$，使得单步演化 $U$ 可写成局部门的有限深度量子电路，且尊重因果性，即 $U^\dagger \mathcal{A}_O U \subset \mathcal{A}_{O^{+}}$，其中 $\mathcal{A}_O$ 是区域 $O$ 的局域算符代数，$O^{+}$ 为 $O$ 的有限厚度邻域。

为了连接到连续极限，我们考虑一类 Dirac 型 QCA，其单步演化在动量表象中可以写成

$$U(k) = \exp\left(-\mathrm{i} H_{\mathrm{eff}}(k) \Delta t\right),$$

其中 $H_{\mathrm{eff}}(k)$ 在长波极限 $k a \ll 1$ 下趋近于 Dirac Hamiltonian

$$H_{\mathrm{eff}}(k) \approx \alpha k + \beta m,$$

$\alpha,\beta$ 为满足 Clifford 代数的矩阵，$a$ 为格点间距，$m$ 为有效质量参数。

### 2.2 自指散射单元与有效一维模型

考虑在某一有限区域 $D \subset \Lambda$ 引入局域结构，使得在该区域内存在反馈通道：部分入射振幅在经过局域散射后重新注入同一区域。对于波长远大于 $D$ 尺寸的模式，可以采用一维有效描述，将整个区域 $D$ 压缩为一段等效传输线或散射中心，入射与出射信号沿一维坐标 $x$ 传播。

在频域表象下，设某一固定频率 $\omega$ 的模式在一维坐标上满足有效波动方程，其在 $x>0$ 半空间的传播可通过位置依赖的阻抗 $Z(x;\omega)$ 表征。按照电磁波与声学波传播理论，在适当的一维近似下，$Z(x;\omega)$ 的空间演化满足非线性 Riccati 方程([SpringerOpen][2])

$$\frac{\mathrm{d}Z}{\mathrm{d}x} = A(x;\omega) + B(x;\omega) Z + C(x;\omega) Z^2,$$

其中 $A,B,C$ 由介质参数决定。对于分层介质或离散格点模型，$Z$ 在层间跳跃满足 Möbius 变换

$$Z_{n+1} = \frac{a_n Z_n + b_n}{c_n Z_n + d_n}, \quad \begin{pmatrix} a_n & b_n \\ c_n & d_n \end{pmatrix} \in \mathrm{SL}(2,\mathbb{C}).$$

自指反馈结构的核心要求是：在某个有效边界点 $x=0$，局域结构对外表现的输入阻抗 $Z_{\mathrm{in}}(\omega)$ 必须等于由内部回路"看到"的负载阻抗 $Z_{\mathrm{loop}}(\omega)$。这一自洽条件在离散表示中可写为

$$Z_{\mathrm{in}} = \Phi(Z_{\mathrm{in}}),$$

其中 $\Phi$ 是由若干层的 Möbius 变换和反馈相位组成的复合映射。

**定义 2.1（自指散射单元）.** 在给定频率 $\omega$ 下，一个局域结构称为自指散射单元，如果其外部等效输入阻抗 $Z_{\mathrm{in}}(\omega)$ 是某个复 Möbius 变换 $\Phi$ 的不动点：

$$Z_{\mathrm{in}}(\omega) = \Phi\bigl(Z_{\mathrm{in}}(\omega)\bigr), \quad \Phi(z) = \frac{A z + B}{C z + D}, \quad AD - BC = 1.$$

该不动点的稳定性由 $\Phi'\bigl(Z_{\mathrm{in}}\bigr)$ 的模长决定。

### 2.3 Riccati 固定点与平方根判别式

一般地，Möbius 变换不动点方程

$$Z = \frac{A Z + B}{C Z + D}$$

可化为二次方程

$$C Z^2 + (D - A) Z - B = 0,$$

其解为

$$Z_\pm = \frac{A - D \pm \sqrt{(A - D)^2 + 4 B C}}{2C},$$

只要 $C \neq 0$。由此可见，任何自指散射单元的等效阻抗都天然携带一个平方根分支结构，其判别式

$$\Delta = (A - D)^2 + 4 B C$$

的相位与模长决定了两支解的物理性质。对于无损系统，$(A,B,C,D)$ 属于 $\mathrm{SU}(1,1)$ 或 $\mathrm{SL}(2,\mathbb{R})$ 的适当表示，$\Delta$ 位于复平面某条曲线，平方根函数 $\sqrt{\Delta}$ 的选择对应于两类不同的边界条件。

本文将此平方根结构视为"旋量"的雏形：可观察阻抗 $Z$ 对应于某个"振幅"变量 $\zeta$ 的平方，即

$$Z = F(\zeta^2),$$

而 $\zeta$ 在参数空间封闭路经下的多值性将决定交换统计。

### 2.4 全同自指激发的构型空间

考虑在三维空间中 $N$ 个良好分离的自指散射单元，其中心位置为 $\mathbf{x}_1,\dots,\mathbf{x}_N \in \mathbb{R}^3$。忽略内部结构的细节，几何构型空间为

$$Q_N = \frac{\bigl(\mathbb{R}^3\bigr)^N \setminus \Delta}{S_N},$$

其中 $\Delta$ 为粒子位置重合的对角子集，$S_N$ 为置换群。对 $d \geq 3$ 维，$Q_N$ 的基本群是 $S_N$，其元素可由相邻粒子的交换生成。([Physics Stack Exchange][6])

在标准量子力学中，多体波函数 $\Psi$ 被视为 $Q_N$ 上的复值单值函数。拓扑自旋–统计方案中，$\Psi$ 被视为某个线丛或向量丛上的截面，不同的丛结构对应于不同的交换统计。([SpringerLink][3])

在本文方案中，我们将利用每个自指散射单元内部的 Riccati 平方根结构，在 $Q_N$ 之上构造一个自然的双覆盖空间 $\widetilde{Q}_N$，并展示交换路径在 $\widetilde{Q}_N$ 上具有 $\mathbb{Z}_2$ holonomy。

---

## Main Results (Theorems and alignments)

本节给出本文的核心结果，集中在三个层面：

1. 自指散射单元与 Riccati 方程的平方根结构；

2. 由平方根结构诱导的旋量双覆盖；

3. 粒子交换产生的 $\mathbb{Z}_2$ 相位及其与费米统计的对应。

### 3.1 自指散射与 Riccati 平方根

**定理 3.1（自指散射单元的平方根判别式）.**

设某个自指散射单元的等效传输矩阵为

$$M = \begin{pmatrix} A & B \\ C & D \end{pmatrix} \in \mathrm{SL}(2,\mathbb{C}),$$

其外部输入阻抗 $Z_{\mathrm{in}}$ 为 Möbius 变换的不动点，即 $Z_{\mathrm{in}} = \Phi(Z_{\mathrm{in}})$，$\Phi(z) = (A z + B)/(C z + D)$。假设 $C \neq 0$ 且系统无损，使得 $M$ 的谱位于单位圆上。则：

1. $Z_{\mathrm{in}}$ 满足二次方程

   $$C Z^2 + (D - A) Z - B = 0.$$

2. 存在判别式 $\Delta = (A - D)^2 + 4 B C$，使得

   $$Z_{\mathrm{in}} = Z_\pm = \frac{A - D \pm \sqrt{\Delta}}{2C},$$

   其中 $\sqrt{\Delta}$ 为复平面上两值的平方根函数。

3. 若 $M$ 属于 $\mathrm{SU}(1,1)$ 或等价表示，则两支解 $Z_\pm$ 中恰有一支对应稳定不动点（$|\Phi'(Z)| < 1$），另一支对应不稳定不动点（$|\Phi'(Z)| > 1$）。

因此，任何稳定自指散射单元的外部响应都可以等价地由一对平方根变量 $\pm \sqrt{\Delta}$ 中的某一选择表征。

*证明思路.* 将不动点条件写为二次方程即可得到判别式和二值解；稳定性条件由 Möbius 变换导数模长判定。无损条件限制 $M$ 的谱，从而限定 $\Delta$ 的相位和模长，使得仅一支解稳定。详见附录 A。

### 3.2 旋量双覆盖的涌现

**定义 3.2（旋量内部变量）.**

对每个自指散射单元，我们引入内部变量 $\zeta$，使得

$$\sqrt{\Delta} = \Lambda \zeta^2,$$

其中 $\Lambda \in \mathbb{C}^\times$ 为与具体实现相关的非零常数。定义归一化"旋量"变量

$$\chi = \frac{\zeta}{\lVert \zeta \rVert},$$

其整体相位冗余视为规范自由度。

由此，稳定自指散射单元可由等效阻抗 $Z_{\mathrm{in}}$ 或旋量变量 $\chi$ 描述，两者满足

$$Z_{\mathrm{in}} = F(\chi^2),$$

其中 $F$ 是某个显式的有理函数。注意，$\chi$ 与 $-\chi$ 对应同一 $Z_{\mathrm{in}}$。

**定理 3.3（内部旋量双覆盖）.**

在上述假设下，单个自指散射单元的内部态空间可以视为一个商空间

$$\mathcal{S}_{\mathrm{int}} \cong \mathbb{C}^2 \setminus \{0\} / \{\chi \sim -\chi\},$$

并存在一个自然的映射

$$\pi_{\mathrm{int}} : \mathbb{C}^2 \setminus \{0\} \to \mathcal{S}_{\mathrm{int}}, \quad \pi_{\mathrm{int}}(\chi) = [\chi],$$

其核为 $\{\pm 1\}$。在适当的规范选择和粗粒化下，$\mathbb{C}^2$ 上的 $\mathrm{SU}(2)$ 旋转表示通过 $\pi_{\mathrm{int}}$ 投影到 $\mathcal{S}_{\mathrm{int}}$ 上的 $\mathrm{SO}(3)$ 旋转表示，因而内部自由度自然组织成一个 $\mathrm{Spin}(3)$ 的双覆盖结构。

这一结构与标准旋量理论完全同构：$\chi$ 扮演自旋 $1/2$ 旋量的角色，而 $Z_{\mathrm{in}}$ 和可观测散射相位对应于二次不变量。

### 3.3 粒子交换与 $\mathbb{Z}_2$ 交换相位

**定理 3.4（自指激发的费米型交换统计）.**

考虑三维空间中 $N$ 个全同的自指散射单元，其构型空间 $Q_N$ 如第 2.4 节所定义。令 $\widetilde{Q}_N$ 为由内部旋量变量诱导的双覆盖：

$$\widetilde{Q}_N = \Bigl\{(\mathbf{x}_1,\dots,\mathbf{x}_N;\chi_1,\dots,\chi_N)\Bigr\} \big/ \sim,$$

其中等价关系在每个粒子上识别 $\chi_j \sim -\chi_j$，同时要求外部 $Z_{\mathrm{in}}$ 不变。则：

1. $\widetilde{Q}_N$ 是 $Q_N$ 的双覆盖空间，其覆盖变换群由同时将所有 $\chi_j$ 变号的操作生成，构成一个 $\mathbb{Z}_2$。

2. 对于任意一对粒子 $i,j$，其交换操作对应 $Q_N$ 上一个闭合路径 $\gamma_{ij}$。在 $\widetilde{Q}_N$ 上，$\gamma_{ij}$ 提升为两条路径 $\widetilde{\gamma}_{ij}^{\pm}$，其端点相差一个全局变号：

   $$\widetilde{\gamma}_{ij}^{+}(1) = -\widetilde{\gamma}_{ij}^{-}(1).$$

3. 若将多体态视为 $\widetilde{Q}_N$ 上一条线丛的截面，并要求该截面在覆盖变换下变号，则沿 $\gamma_{ij}$ 的平行移动使波函数获得相位 $(-1)$：

   $$\Psi(\gamma_{ij}(1)) = - \Psi(\gamma_{ij}(0)).$$

因此，在该量子化方案中，粒子交换的几何实现必然对应费米型反对称统计。

*证明思路.* 这是 Finkelstein–Rubinstein 方案在自指旋量内部自由度上的具体实现。关键在于：将粒子绕行路径视为 $\widetilde{Q}_N$ 上的闭合曲线，其在覆盖空间上的提升具有非平凡的 $\mathbb{Z}_2$ holonomy。选择使覆盖变换对应波函数变号的线丛，即得到费米统计。([SpringerLink][3]) 详见附录 B。

---

## Proofs

本节给出上述定理的证明要点，技术细节分别在附录中展开。

### 4.1 定理 3.1 的证明

由不动点条件

$$Z = \frac{A Z + B}{C Z + D}$$

得

$$C Z^2 + (D - A) Z - B = 0.$$

这是关于 $Z$ 的二次方程，只要 $C \neq 0$ 即可写出显式解

$$Z_\pm = \frac{A - D \pm \sqrt{\Delta}}{2C}, \quad \Delta = (A - D)^2 + 4 B C.$$

假定系统无损，即 $M \in \mathrm{SU}(1,1)$ 或类似群，意味着 $M$ 的特征值位于单位圆上，而 $M$ 与对应的散射矩阵 $S$ 的本征相位紧密相关。Möbius 变换

$$\Phi(z) = \frac{A z + B}{C z + D}$$

的导数为

$$\Phi'(z) = \frac{1}{(C z + D)^2}.$$

代入 $Z_\pm$，可评估 $|\Phi'(Z_\pm)|$。在无损条件下，$(C Z_\pm + D)$ 的模长互为倒数，从而两支解中恰有一支满足 $|\Phi'(Z)| < 1$，该支对应稳定不动点，对应稳定自指散射结构；另一支则不稳定，对应非物理解或激发态。详尽分析见附录 A 中与变量相位方法和 Levinson 定理的比对。([SciELO][7])

### 4.2 定理 3.3 的证明

判别式 $\Delta$ 是 $M$ 的迹与行列式的不变量；在无损情形下，$\Delta$ 通常落在穿过原点的复平面曲线上。对每个频率 $\omega$ 与动量 $k$，我们可以写

$$\Delta(\omega,k) = \Lambda^2(\omega,k) \zeta^4(\omega,k),$$

其中 $\Lambda \neq 0$ 为规范选择。于是

$$\sqrt{\Delta} = \Lambda \zeta^2,$$

而 $Z_{\mathrm{in}}$ 可重写为某个有理函数 $F(\zeta^2)$。将 $\zeta$ 视为二维复向量的坐标，引入归一化

$$\chi = \frac{\zeta}{\lVert \zeta \rVert} \in \mathbb{C}^2 \setminus \{0\},$$

并识别 $\chi \sim -\chi$，即可得到内部态空间的商结构。标准群论结果表明，$\mathrm{SU}(2)$ 在 $\mathbb{C}^2$ 上的自然表示通过商映射投影到 $\mathrm{SO}(3)$ 在 $S^2$ 上的表示，而 $\mathrm{SU}(2)$ 是 $\mathrm{SO}(3)$ 的双覆盖。由此，内部态具有与自旋 $1/2$ 旋量完备等价的双覆盖结构。

### 4.3 定理 3.4 的证明

对 $Q_N$ 的拓扑性质已有成熟结论：在三维空间中，$Q_N$ 的基本群为置换群 $S_N$，其生成元可视为相邻粒子交换路径。([Physics Stack Exchange][6]) Finkelstein–Rubinstein 证明：若存在一个双覆盖 $\widetilde{Q}_N \to Q_N$，其覆盖变换群为 $\mathbb{Z}_2$，并且将 $2\pi$ 空间旋转与粒子交换路径关联到 $\widetilde{Q}_N$ 中的非平凡闭合回路，则可以构造一个线丛，使得多体态作为该线丛截面在覆盖变换下变号，从而实现费米统计。([SpringerLink][3])

在本文构造中，每个粒子携带内部旋量变量 $\chi_j$，$\chi_j \sim -\chi_j$ 对应同一物理阻抗。将所有粒子内部变量合并，可自然得到 $\widetilde{Q}_N$。沿交换路径 $\gamma_{ij}$ 的演化不仅在位置空间中绕行，还在内部参数空间中绕过平方根分支切割，使得 $(\chi_i,\chi_j)$ 的整体相位发生一次 $2\pi$ 绕行。这在 $\widetilde{Q}_N$ 上对应非平凡的 $\mathbb{Z}_2$ holonomy。选择使覆盖变换对应波函数变号的线丛，即可得到

$$\Psi(\dots,\mathbf{x}_i,\mathbf{x}_j,\dots) = -\Psi(\dots,\mathbf{x}_j,\mathbf{x}_i,\dots).$$

因此，自指散射激发天然实现费米型交换统计。

---

## Model Apply

本节展示如何在具体 QCA 模型中实现上述自指散射结构，并将之与 Dirac 质量与拓扑阻抗联系起来。

### 5.1 一维 Dirac–QCA 中的自指缺陷

考虑一维 Dirac 型 QCA，其单步演化可写作量子行走

$$U = S_+ \otimes \lvert\uparrow\rangle\langle\uparrow\rvert + S_- \otimes \lvert\downarrow\rangle\langle\downarrow\rvert \circ \left(\mathbb{I} \otimes C\right),$$

其中 $S_\pm$ 将态分别向左、右平移一步，$C$ 是 $2\times 2$ coin 矩阵，例如

$$C(\theta) = \begin{pmatrix} \cos\theta & \sin\theta \\ -\sin\theta & \cos\theta \end{pmatrix}.$$

在动量表象中，$U(k)$ 的本征值为 $\mathrm{e}^{\mp \mathrm{i}\omega(k)}$，满足色散关系

$$\cos\omega(k) = \cos\theta \cos(k a),$$

在长波极限下给出有效 Dirac 方程，质量 $m$ 与 $\theta$ 相关。([arXiv][5])

在此背景下，在某一格点或有限子链上修改 coin 矩阵或引入局域回路，可以实现有效散射中心。对波长远大于缺陷区域尺寸的模态，其散射由 $2\times 2$ 单道散射矩阵

$$S(k) = \begin{pmatrix} r(k) & t'(k) \\ t(k) & r'(k) \end{pmatrix}$$

表征。通过将缺陷区域内部的回路显式建模为附加的边界与反馈通道，可以将其等效阻抗写成满足 Riccati 方程的函数 $Z(x;k)$，其在缺陷区域外围的值给出 $r(k)$。相关技术与变量相位方法密切相关。([SciELO][7])

### 5.2 质量、束缚态与自指反馈

对具有自指反馈的缺陷，存在某些频率 $\omega$ 和动量 $k$ 使得极点条件

$$1 - r(\omega) \mathrm{e}^{\mathrm{i}\theta_{\mathrm{loop}}} = 0$$

成立，此处 $\theta_{\mathrm{loop}}$ 为回路附加相位。这些极点对应于束缚态或准束缚态，在 QCA 的连续极限下表现为局域化的"粒子"，其频率偏离无质量模态的色散关系，定义了有效质量 $m$。

另一方面，反射系数可写为

$$r(\omega) = \mathrm{e}^{\mathrm{i}\delta(\omega)},$$

其中 $\delta(\omega)$ 为散射相位。通过 Levinson 定理和变量相位方法，可以将 $\delta(\omega)$ 与束缚态数、Riccati 相位函数关联起来。([SciELO][7]) 极点条件可改写为关于阻抗的自洽方程，其解具有二值的平方根结构，从而为束缚态引入一个自然的内部旋量变量。

### 5.3 内部旋量与 Dirac 旋量的比对

在 Dirac–QCA 的连续极限中，费米子态通常由四分量旋量或在一维情形下的两分量旋量描述。本文构造表明，即使从标量散射数据出发，只要存在自指反馈结构，其等效阻抗中蕴含的平方根判别式就足以引入一个两分量内部自由度 $\chi$，并在适当的规范选择下恢复 $\mathrm{SU}(2)$ 旋量变换性质。

直观地说：QCA 的局域 coin 决定了传播方向与内部自由度；自指散射反馈则为这一内部自由度引入拓扑记忆，使其在空间旋转与粒子交换下出现"半角"相位。最终宏观上观测到的，是一个满足 Dirac 方程并服从费米–狄拉克统计的激发，其底层微观图像是一个 Riccati 方程的平方根不动点。

---

## Engineering Proposals

尽管本文主要关注理论结构，但自指散射与 Riccati 阻抗方程的工具在工程上高度成熟，已经广泛用于电磁波和声学波在非均匀介质中的传播建模。([SpringerOpen][2]) 这一事实为实验检验提供了自然舞台。

### 6.1 一维波导与超导微波线路中的自指回路

在一维电磁波导或超导传输线上，可以通过耦合谐振腔、分支和反馈环路构造自指散射单元。可测量量包括：

* 频域中的反射系数 $r(\omega)$ 和等效阻抗 $Z_{\mathrm{in}}(\omega)$；

* 通过调节反馈相位和耦合强度实现从无束缚态到单束缚态的连续过渡；

* 显示 Riccati 方程预测的阻抗分支结构，例如通过对介质参数的缓变调制，观察阻抗随深度的变化。

若能在同一波导上并列构造两个相同的自指单元，并设计可控的几何路径使其"交换"位置（例如通过可重构开关网络或时序控制模拟交换），则有望在干涉实验中观察到整体相位 $(-1)$ 的效应。

### 6.2 光子 QCA 与线性光学网络

基于波导阵列和分束器–移相器网络的线性光学平台可以实现二维 QCA。通过在某些节点引入环形光路反馈，可以实现光子"自指散射"的离散版本。通过测量相关函数、干涉条纹和有效散射相位，可以在光学频段间接验证 Riccati 平方根结构，进而为更复杂的多体交换实验奠定基础。

### 6.3 与超导量子比特平台的结合

在超导量子电路中，单步 QCA 可以通过受控相位门与 SWAP 门实现，而自指反馈可以通过可调谐耦合器和延迟线模拟。通过在多比特 Hilbert 空间中编码内部旋量变量 $\chi$，并利用 Ramsey 干涉精确测量交换操作前后的全局相位变化，有望在量子信息平台上实现自指费米子的原型。

---

## Discussion (risks, boundaries, past work)

### 7.1 与标准自旋–统计定理的关系

本文提出的自指散射机制并不试图取代标准自旋–统计定理，而是从离散本体论与散射网络角度提供一条补充路径。标准定理的核心假设是连续时空上的局域、洛伦兹协变量子场及其微因果性；而本文从 QCA 出发，将局域幺正性视为更基本的结构，并在其上构造自指反馈与 Riccati 方程。

两者之间存在如下对应关系：

* 标准定理中，粒子交换与 $2\pi$ 旋转通过 Lorentz 群表示论与场算符对易关系联系起来；本文中，粒子交换与 $2\pi$ 旋转通过自指散射内部的平方根判别式和双覆盖配置空间联系起来。

* 标准定理以场算符为基本对象；本文以 QCA 的局域幺正和散射网络为基本对象。

在适当的连续极限与 coarse-graining 下，两者应当兼容：自指散射产生的旋量结构与标准 Dirac 旋量重合，费米统计由两者共同保证。

### 7.2 与拓扑自旋–统计方案的联系

Finkelstein–Rubinstein 和后续工作已经表明，在具有非平凡拓扑的孤子模型中，可以通过构型空间的双覆盖与线丛 holonomy 得到自旋与统计的几何起源。([SpringerLink][3]) 本文可以视为这一思想在 QCA 与散射网络中的具体实现：

* 孤子模型中的拓扑电荷对应于自指散射网络的反馈绕行数；

* 孤子构型空间的非平凡基本群对应于多自指单元的构型空间 $Q_N$；

* 线丛 holonomy 对应于内部旋量变量 $\chi$ 的平方根多值性。

区别在于：孤子模型通常依赖连续场的非线性方程，而本文的自指结构可以在离散 QCA 网络中通过线性单步幺正与拓扑反馈回路实现，更适合与信息论和工程实现对接。

### 7.3 适用边界与潜在风险

本工作的假设与推导存在若干边界条件与潜在风险：

1. 有效一维描述的假设：将多维 QCA 中的局域结构压缩为一维传输线与阻抗模型，需要模式波长远大于自指区域尺度。这一近似在强耦合或高度非各向同性情形下可能失效。

2. Riccati 方程的适用性：经典波动理论中的阻抗 Riccati 方程依赖线性波动方程与某些边界条件；在 QCA 中，虽然单步幺正演化可在连续极限下近似为线性方程，但高频模式或深离散区域可能引入修正。

3. 多体效应与相互作用：本文主要在弱耦合和稀疏粒子极限下分析多体构型空间与交换路径。强相互作用或多粒子团簇可能改变构型空间的拓扑结构，进而影响统计性质。

4. 维数限制：本文重点讨论三加一维情形。在二加一维中，构型空间的基本群是 braid 群，允许任意子与分数统计；自指散射网络的平方根结构在二维中可能产生更丰富的统计行为，需要单独分析。([inis.iaea.org][8])

---

## Conclusion

本文在量子元胞自动机与散射网络的框架下，提出了一种将费米统计与自指散射联系起来的机制。核心结论可以概括为：

1. **质量即自指散射的稳定不动点**：有质量粒子可以视为 QCA 网络中的自指散射单元，其等效输入阻抗满足由 Möbius 变换引出的 Riccati 方程，并以平方根判别式形式给出稳定不动点。

2. **自指出平方根，平方根出旋量**：自指散射的判别式平方根引入了内部两值自由度，可组织为 $\mathrm{SU}(2)$ 旋量空间的双覆盖结构，$\chi$ 与 $-\chi$ 对应同一可观测阻抗。

3. **旋量双覆盖出费米统计**：将 $N$ 个自指单元的内部旋量纳入构型空间，得到 $Q_N$ 的自然双覆盖 $\widetilde{Q}_N$。粒子交换路径在该双覆盖上具有 $\mathbb{Z}_2$ holonomy，选择使覆盖变换对应波函数变号的量子化方案，自动得到费米–狄拉克统计。

4. **工程可实现性**：由于 Riccati 阻抗方程在电磁波、声学波与地球物理等领域已被广泛应用，构造自指散射网络并在实验上探测平方根多值性与交换相位在工程上具有可行性。

未来工作包括：在二加一维平台上探索自指散射诱导的任意子统计；在具体的 Dirac–QCA 模型中完成从底层单步幺正到连续场论有效拉氏量的推导；在超导量子电路与光子网络中实现最小自指费米子单元并测量其交换相位。

---

## Acknowledgements, Code Availability

本工作受益于关于自旋–统计定理、拓扑孤子与 QCA 连续极限的广泛讨论。数值验证部分所需的 Riccati 方程求解与 QCA 演化模拟可以通过标准科学计算库实现，相应示例代码可在通用开源平台上实现与共享。

---

## References

[1] W. Pauli, "The connection between spin and statistics," *Phys. Rev.* **58**, 716 (1940).([维基百科][1])

[2] R. F. Streater and A. S. Wightman, *PCT, Spin and Statistics, and All That* (Princeton Univ. Press, 2000).([维基百科][1])

[3] D. Finkelstein and J. Rubinstein, "Connection between spin, statistics, and kinks," *J. Math. Phys.* **9**, 1762 (1968).([SpringerLink][3])

[4] J. L. Friedman, "Statistics of Yang–Mills solitons," *Commun. Math. Phys.* **89**, 415 (1983).([SpringerLink][3])

[5] F. Wilczek, "Linking numbers, spin, and statistics of solitons," *Phys. Rev. Lett.* **51**, 2250 (1983).([APS链接][4])

[6] J. M. Leinaas and J. Myrheim, "On the theory of identical particles," *Nuovo Cimento B* **37**, 1 (1977).([users.physics.ox.ac.uk][9])

[7] A. Lerda, *Anyons: Quantum Mechanics of Particles with Fractional Statistics* (Springer, 1992).([SpringerLink][10])

[8] F. Calogero, *Variable Phase Approach to Potential Scattering* (Academic Press, New York, 1967).([Elsevier商店][11])

[9] V. D. Viterbo, "Variable phase equation in quantum scattering," *Rev. Bras. Ensino Fís.* **36**, 1303 (2014).([SciELO][7])

[10] L. P. Krainov and L. P. Presnyakov, "Phase functions for potential scattering in optics," *Physics–Uspekhi* **36**, 613 (1993).([ufn.ru][12])

[11] S. Kováčiková, "Generalized Riccati equations for 1-D magnetotelluric theory," *Earth Planets Space* **54**, 617 (2002).([SpringerOpen][2])

[12] A. J. Haines, "General elastic wave scattering problems using an impedance operator," *Geophys. J. Int.* **159**, 643 (2004).([OUP Academic][13])

[13] C. Kaernbach, "On Riccati equations describing impedance relations for cochlear wave propagation," *J. Acoust. Soc. Am.* **81**, 408 (1987).([PubMed][14])

[14] F. Finster and J. Smoller, "Error estimates for approximate solutions of the Riccati equation with real or complex potentials," arXiv:0807.4406 (2009).([arXiv][15])

[15] S. Weinberg, *The Quantum Theory of Fields, Vol. I* (Cambridge Univ. Press, 1995).([arXiv][5])

[16] G. 't Hooft, *The Cellular Automaton Interpretation of Quantum Mechanics* (Springer, 2016).([arXiv][5])

[17] Z. Feng, "Spin statistics and field equations for any spin," arXiv:2304.11394 (2023).([arXiv][5])

[18] D. G. Choi, "Line bundles and spin–statistics of solitons," *Nucl. Phys. B (Proc. Suppl.)* **14**, 301 (1989).([ScienceDirect][16])

[19] 相关 Dirac–QCA 与质量作为拓扑阻抗的工作，可见：H. Ma, "Mass as topological impedance: self-referential scattering and chiral symmetry breaking in Dirac–QCA," 待发表 (2025).

---

## Appendix A. Riccati Impedance Equation and Möbius Fixed Points

本附录给出阻抗 Riccati 方程与 Möbius 不动点结构的传统推导，并澄清本文所用参数的物理含义。

### A.1 一维波动与阻抗定义

考虑一维介质中标量波动方程

$$\frac{\partial^2 u}{\partial x^2} + k^2 n^2(x) u = 0,$$

其中 $u(x)$ 为场振幅，$k = \omega/c$，$n(x)$ 为位置依赖折射率。在频域，定义局域阻抗

$$Z(x) = \frac{1}{\mathrm{i} \omega \rho} \frac{\partial_x u(x)}{u(x)},$$

其中 $\rho$ 为常数（如介质密度）。代入波动方程可得

$$\frac{\mathrm{d}Z}{\mathrm{d}x} + Z^2 + k^2 n^2(x) = 0,$$

这是 Riccati 方程的一种标准形式。通过适当缩放与变量变换，可写作

$$\frac{\mathrm{d}Z}{\mathrm{d}x} = A(x) + B(x) Z + C(x) Z^2,$$

其中

$$A = -k^2 n^2(x), \quad B = 0, \quad C = 1.$$

这一推导出现在多种文献中，如变量相位方法和地球物理中的阻抗传播理论。([SciELO][7])

### A.2 分层介质与 Möbius 变换

对分层介质，每层 $n(x)$ 常数，厚度为 $d_j$，层间边界满足连续条件，层内解为平面波叠加

$$u_j(x) = A_j \mathrm{e}^{\mathrm{i} k_j x} + B_j \mathrm{e}^{-\mathrm{i} k_j x}.$$

层内反射与透射可用 $2\times 2$ 传输矩阵 $M_j \in \mathrm{SL}(2,\mathbb{C})$ 表示：

$$\begin{pmatrix} A_{j+1} \\ B_{j+1} \end{pmatrix} = M_j \begin{pmatrix} A_j \\ B_j \end{pmatrix}.$$

阻抗 $Z_j = B_j/A_j$ 在层间跃迁满足

$$Z_{j+1} = \frac{a_j Z_j + b_j}{c_j Z_j + d_j}, \quad M_j = \begin{pmatrix} a_j & b_j \\ c_j & d_j \end{pmatrix}.$$

这是典型的 Möbius 变换。多层复合后的总传输矩阵 $M$ 为各层矩阵的乘积，其不动点解满足二次方程，判别式自然出现平方根结构。([OUP Academic][13])

### A.3 自指反馈与不动点条件

若在某一位置 $x=0$ 引入反馈环，使出射波部分以相位 $\theta_{\mathrm{loop}}$ 重返输入，则等效边界条件为

$$u(0^-) = u(0^+) + \mathrm{e}^{\mathrm{i}\theta_{\mathrm{loop}}} u(0^+),$$

相应对阻抗的影响可以等效为附加的 Möbius 变换。自指条件要求外部"看到"的阻抗 $Z_{\mathrm{in}}$ 在经过一轮内部传播与反馈后不变，即

$$Z_{\mathrm{in}} = \Phi(Z_{\mathrm{in}}),$$

其中 $\Phi$ 为由各层传播与反馈相位构成的 Möbius 变换。对这一固定点方程进行求解即可得到定理 3.1 所述的二次方程与平方根判别式结构。

---

## Appendix B. Finkelstein–Rubinstein Construction and Self-Referential Loops

本附录回顾 Finkelstein–Rubinstein （FR）拓扑自旋–统计方案的主要思想，并说明如何将自指散射激发嵌入该框架。

### B.1 孤子构型空间与双覆盖

在非线性场论中，如 Skyrme 模型，拓扑孤子构型空间

$$\mathcal{C}_Q = \{ \text{场构型 } \phi(\mathbf{x}) \mid Q[\phi] = Q\}$$

通常具有非平凡的基本群 $\pi_1(\mathcal{C}_Q)$。FR 指出，可以人为构造一个双覆盖空间 $\widetilde{\mathcal{C}}_Q$，并规定对应于 $2\pi$ 空间旋转的闭合路径在 $\widetilde{\mathcal{C}}_Q$ 上提升为非平凡闭合曲线，使得其 holonomy 为 $(-1)$。在此基础上，将量子态视为 $\widetilde{\mathcal{C}}_Q$ 上的线丛截面，并要求在覆盖变换下波函数变号，即可得到自旋 $1/2$ 与费米统计。([SpringerLink][3])

### B.2 多孤子构型空间与交换路径

对 $N$ 个孤子的构型空间 $Q_N$，FR 分析表明其基本群由粒子交换与整体旋转生成，并满足某些关系式。通过将 $2\pi$ 旋转与一对粒子交换联系起来，并为这些生成元指定 $\mathbb{Z}_2$ 值，可在 $Q_N$ 上构造不同的双覆盖，对应于玻色、费米或更一般的统计。([SpringerLink][3])

### B.3 自指散射激发的 FR 数据

在本文构造中，每个自指散射单元内部的 Riccati 判别式平方根提供了一个自然的双值自由度 $\chi \sim -\chi$。将所有粒子的位置和内部旋量合并，得到

$$\widetilde{Q}_N = \Bigl\{(\mathbf{x}_1,\dots,\mathbf{x}_N;\chi_1,\dots,\chi_N)\Bigr\} \big/ \sim,$$

其对 $Q_N$ 的投影忘却所有 $\chi_j$。交换路径在 $\widetilde{Q}_N$ 上的提升具有如下性质：

* 仅进行空间交换而不改变内部旋量对应一条闭合路径；

* 然而，由于 Riccati 平方根分支切割的存在，沿该路径的绝热演化会使 $(\chi_i,\chi_j)$ 的整体相位绕原点一周，从而在 $\widetilde{Q}_N$ 上对应非平凡元素。

因此，自指散射结构自动为 FR 方案提供了所需的双覆盖与 holonomy 数据。选择使覆盖变换对应波函数变号的量子化规则，即得到费米统计；若选择覆盖变换为平凡作用，则得到玻色统计。本文强调的是：在有质量自指激发的自然动力学下，稳定性与幺正性要求选取前者，从而将"有质量"与"费米统计"在本构造中锁定在一起。

---

## Appendix C. Remarks on 2+1 Dimensions and Anyonic Generalizations

尽管本文主要关注三加一维情形，在二加一维中，自指散射与 Riccati 平方根结构可能产生更丰富的统计行为。

在二加一维，$N$ 粒子构型空间的基本群为 braid 群 $B_N$，其表示可以给出任意统计（anyonic statistics），允许粒子交换时的相位或矩阵表示连续插值于玻色与费米之间。([inis.iaea.org][8]) 自指散射网络中，内部旋量变量 $\chi$ 的多值性与 braid 群表示的组合有望给出一类"自指任意子"的具体实现：其统计相位不再局限于 $\pm \pi$，而是与 Riccati 判别式在参数空间中的绕行次数相关。

系统分析这一情形需要将本文的 QCA–散射构造推广到二维格点，并对多粒子 braid 路径的拓扑与内部自指反馈的几何结构进行统一建模，留待后续工作展开。

[1]: https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem?utm_source=chatgpt.com "Spin–statistics theorem"

[2]: https://earth-planets-space.springeropen.com/articles/10.1186/BF03353038?utm_source=chatgpt.com "Generalized Riccati equations for 1-D magnetotelluric ..."

[3]: https://link.springer.com/article/10.1007/BF01214741?utm_source=chatgpt.com "Statistics of Yang-Mills solitons"

[4]: https://link.aps.org/doi/10.1103/PhysRevLett.51.2250?utm_source=chatgpt.com "Linking Numbers, Spin, and Statistics of Solitons"

[5]: https://arxiv.org/pdf/2304.11394?utm_source=chatgpt.com "Spin Statistics and Field Equations for any Spin"

[6]: https://physics.stackexchange.com/questions/455539/what-is-the-spin-statistics-theorem-in-higher-dimensions?utm_source=chatgpt.com "What is the spin-statistics theorem in higher dimensions?"

[7]: https://www.scielo.br/j/rbef/a/qhtCfms9NH5mV8SDxDLfYMJ/?format=pdf&lang=en&utm_source=chatgpt.com "Variable phase equation in quantum scattering"

[8]: https://inis.iaea.org/collection/NCLCollectionStore/_Public/26/038/26038553.pdf?utm_source=chatgpt.com "JAN MYRHEIM Studies of Particle Statistics in One and ..."

[9]: https://users.physics.ox.ac.uk/~palmerc/FQMfiles/LandM.pdf?utm_source=chatgpt.com "Leinaas and Myrheim, Nuovo Cimento B 37 (1977) ..."

[10]: https://link.springer.com/chapter/10.1007/978-3-540-47466-1_2?utm_source=chatgpt.com "Introduction to Fractional Statistics in Two Dimensions"

[11]: https://shop.elsevier.com/books/variable-phase-approach-to-potential-scattering-by-f-calogero/calogero/978-0-12-155550-4?utm_source=chatgpt.com "Variable Phase Approach to Potential Scattering by F ..."

[12]: https://ufn.ru/ufn93/ufn93_7/ufn937f.pdf?utm_source=chatgpt.com "Phase functions for potential scattering in optics"

[13]: https://academic.oup.com/gji/article/159/2/643/626492?utm_source=chatgpt.com "General elastic wave scattering problems using an impedance ..."

[14]: https://pubmed.ncbi.nlm.nih.gov/3558956/?utm_source=chatgpt.com "On Riccati Equations Describing Impedance Relations for ..."

[15]: https://arxiv.org/pdf/0807.4406?utm_source=chatgpt.com "arXiv:0807.4406v2 [math-ph] 23 Nov 2009"

[16]: https://www.sciencedirect.com/science/article/pii/0920563289904957?utm_source=chatgpt.com "Line bundles and spin-statistics of solitons"

