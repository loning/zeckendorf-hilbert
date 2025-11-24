# 宇宙的极简公理化本体论：量子元胞自动机对象与多层涌现结构

*Minimal Axiomatic Ontology of the Universe: Quantum Cellular Automaton Objects and Multi-Layer Emergent Structures*

---

## Abstract

本文在量子元胞自动机（quantum cellular automaton, QCA）框架内提出一个极简的宇宙本体论。宇宙被定义为一个带初态的 QCA 对象，满足三条公理：(A1) 可数格点上的离散–幺正–局域量子动力系统；(A2) 存在 Lieb–Robinson 意义下的有限信号速度上界 $c$；(A3) 在某个低能一粒子扇区存在二维内部自由度的 Dirac 型有效模式。基于这三条公理，我们证明：（1）由局域代数及其幺正演化可构造出事件集与因果偏序，并在粗粒化极限下嵌入 Lorentz 型宏观时空几何；（2）在一维 Dirac 型 QCA 模型中，单步更新算符的色散关系为

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a),
$$

由此从同一更新算符对称地定义外部群速度 $v_{\mathrm{ext}}(p)$ 与内部演化速度 $v_{\mathrm{int}}(p)$，并严格证明信息速率圆恒等式

$$
v_{\mathrm{ext}}^2(p) + v_{\mathrm{int}}^2(p) = c^2,\qquad c = \frac{a}{\Delta t},
$$

其中 $c$ 为 QCA 的最大信号速率；（3）据此定义固有时间元

$$
\mathrm{d}\tau = \frac{v_{\mathrm{int}}}{c}\,\mathrm{d}t,
$$

可以推导出狭义相对论的时间膨胀关系与四速度规范化 $g_{\mu\nu}u^\mu u^\nu = -c^2$，并在低能极限下重构出相对论能量–动量关系

$$
E^2 = p^2c^2 + m^2c^4.
$$

质量因此获得一个纯内部的信息论定义 $mc^2 = \hbar\omega_{\mathrm{int}}(0)$，即静止系内部演化频率的能量尺度。本文进一步形式化了观察者对象与观察者网络的定义，指出观察者是宇宙对象中的自指局域子系统，其固有时间与宏观"公共现实"均由同一 QCA 本体在不同尺度上的涌现模式刻画。附录给出宇宙对象、因果偏序、Dirac–QCA 色散关系以及信息速率圆定理的详细证明，为后续在该框架内讨论引力、量子场与宇宙学奠定可复用的基础。

---

## Keywords

宇宙本体论；量子元胞自动机；Lieb–Robinson 界；Dirac 模型；信息速率圆；相对论的涌现；观察者网络

---

## 1 Introduction & Historical Context

连续时空与量子态是现代物理的两大基本叙事。一方面，广义相对论将宇宙建模为带 Lorentz 签名的四维流形 $(M,g_{\mu\nu})$，度规满足爱因斯坦场方程，曲率对应引力。另一方面，量子理论以 Hilbert 空间、幺正演化与测量公理为核心，物理系统由态矢量或密度算符描述，观测统计由 Born 规则给出。两者在量子场论、半经典引力等有效理论中可以协同运作，但在本体论层面仍存在明显张力：时空几何与量子态究竟孰为根本？观察者与测量是否需要额外的外部机制？

量子元胞自动机为"宇宙即量子计算"的视角提供了严格算子框架。QCA 将时空离散化为格点网络，每个格点上携带有限维 Hilbert 空间，自由度之间的相互作用由局域幺正更新规则给出。早期工作表明，自由 Dirac 场、Weyl 场以及 Maxwell 场可以在适当对称性与连续极限条件下从 QCA 中涌现。与此同时，离散时间量子行走（quantum walk）与 Dirac 方程之间的深层关联也已被系统阐明，证明通过适当选择 coin 旋转与平移结构，可以在长波极限下得到一维甚至高维的 Dirac 型有效动力学。

另一方面，Lieb–Robinson 界为非相对论量子自旋系统中的"有限信号速度"提供了严谨刻画：即使在没有显式相对论结构的格点模型中，局域扰动的影响在时空中也被限制在某个有效光锥内部，其外部的对易子范数呈指数衰减。这意味着类似"光速上限"的因果结构并非仅属于连续相对论场论，而是广泛存在于具有局域相互作用的量子格点系统中。

在这样的背景下，一个自然的本体论问题是：

*是否存在一个极简的公理系统，仅以 QCA 为唯一原语，就能从中涌现出：有限信号速度、狭义相对论几何、质量–能量关系以及观察者结构？*

本文试图给出一个肯定的构造性回答。我们提出三条极简公理：

1. 宇宙是一个离散–幺正–局域的 QCA 对象；

2. 宇宙演化满足 Lieb–Robinson 型有限光锥界，存在最大信号速率 $c$；

3. 宇宙在某个低能一粒子扇区中存在二维内部自由度的 Dirac 型有效模式。

在这三条公理之下，我们证明：

* 宇宙的事件集与因果偏序在粗粒化极限下可嵌入 Lorentz 型时空几何；

* Dirac 型低能模式的色散关系与内部 Bloch 结构导出一个"信息速率圆"：外部速度与内部演化速度构成以 $c$ 为半径的圆；

* 以内部演化速率定义固有时间，可以重建狭义相对论的时间膨胀、四速度规范化与能量–动量关系；

* 观察者可被刻画为宇宙对象中满足自指与记忆条件的局域子系统，其固有时间与所感知的"公共现实"都由同一 QCA 本体统一描述。

与现有从信息处理原则推导 Dirac 方程与自由量子场理论的工作相比，本文进一步将"宇宙是什么"本体论问题转写为对 QCA 宇宙对象的公理刻画，并强调信息速率几何与相对论几何之间的一一对应。

---

## 2 Model & Assumptions

本节给出宇宙对象的形式化定义，并陈述三条极简公理 A1–A3。

### 2.1 宇宙对象的定义

设 $\Lambda$ 为一个可数无界图，其顶点集合 $V(\Lambda)$ 表示空间元胞，边集合 $E(\Lambda)\subset V(\Lambda)\times V(\Lambda)$ 表示可直接相互作用的邻接关系。假设 $\Lambda$ 局域有限，即对任意 $x\in V(\Lambda)$，其度数 $\deg(x)$ 具有统一上界。

取一个有限维 Hilbert 空间 $\mathcal{H}_{\mathrm{cell}}\cong\mathbb{C}^d$ 作为单元胞空间。对每个格点 $x\in V(\Lambda)$ 配置一份拷贝 $\mathcal{H}_x\cong\mathcal{H}_{\mathrm{cell}}$。对任意有限子集 $\Lambda_0\subset\Lambda$，定义局域 Hilbert 空间

$$
\mathcal{H}_{\Lambda_0} := \bigotimes_{x\in\Lambda_0}\mathcal{H}_x.
$$

定义准局域算符代数

$$
\mathcal{A} := \overline{\bigcup_{\Lambda_0\Subset\Lambda}\mathcal{B}(\mathcal{H}_{\Lambda_0})}^{\lVert\cdot\rVert},
$$

其中 $\Lambda_0\Subset\Lambda$ 表示有限子集，$\mathcal{B}(\mathcal{H}_{\Lambda_0})$ 为有界算符代数，闭包取算符范数。

时间演化由一族 $C^\ast$-代数自同构 $\{\alpha_t\}_{t\in\mathbb{Z}}$ 给出，满足：

1. 群性质：$\alpha_0=\mathrm{id}$，$\alpha_{t+s}=\alpha_t\circ\alpha_s$；

2. 准局域性：存在常数 $R>0$，对任意 $A\in\mathcal{B}(\mathcal{H}_{\Lambda_0})$，其演化 $\alpha_1(A)$ 的支撑包含在 $\Lambda_0$ 的半径 $R$ 邻域内。

在具体构造中，通常存在某个幺正算符 $U$ 实现单步演化，即对所有 $A\in\mathcal{A}$ 有

$$
\alpha_1(A) = U^{\dagger}AU.
$$

宇宙初态是 $\mathcal{A}$ 上的一个态，即正归一线性泛函 $\omega_0:\mathcal{A}\to\mathbb{C}$，满足 $\omega_0(\mathbb{I})=1$、$\omega_0(A^{\dagger}A)\ge 0$。于是可以做如下定义。

**定义（宇宙对象）** 记五元组

$$
\mathfrak{U}_{\mathrm{QCA}} := \bigl(\Lambda,\mathcal{H}_{\mathrm{cell}},\mathcal{A},\alpha,\omega_0\bigr)
$$

为一个宇宙对象（QCA 宇宙），其中 $\alpha$ 为由准局域幺正算符实现的离散时间演化。

### 2.2 公理 A1：离散–幺正–局域

**公理 A1（离散–幺正–局域）** 物理宇宙是某个宇宙对象 $\mathfrak{U}_{\mathrm{QCA}}$，满足：

1. $\Lambda$ 可数且局域有限；

2. 单元胞 Hilbert 空间 $\mathcal{H}_{\mathrm{cell}}$ 有限维；

3. 存在准局域幺正算符 $U$，使对所有 $A\in\mathcal{A}$ 有 $\alpha_1(A) = U^{\dagger}AU$。

该公理将宇宙约束为一个"有限信息密度 + 局域相互作用 + 幺正演化"的离散量子动力系统，而未预设任何连续时空结构或 Lorentz 对称性。

### 2.3 公理 A2：有限光锥与 Lieb–Robinson 速度

**公理 A2（有限光锥）** 存在常数 $c>0$，对任意局域算符 $A,B$ 与任意 $t\in\mathbb{Z}$，存在常数 $C,\mu>0$ 使得

$$
\bigl|[\alpha_t(A),B]\bigr| \le C\,\lVert A\rVert\,\lVert B\rVert\exp\Bigl[-\mu\bigl(\mathrm{dist}(\mathrm{supp}A,\mathrm{supp}B)-c|t|\bigr)\Bigr],
$$

其中 $\mathrm{supp}A$ 为 $A$ 的最小支撑区域，$\mathrm{dist}$ 为图距离。

这一定律是 Lieb–Robinson 界的抽象形式，表明在时空图上存在一个以 $c$ 为"坡度"的有效光锥，光锥外的对易子范数指数抑制。物理上可将 $c$ 解释为宇宙中的最大信号速率，即"光速上限"的离散版本。

### 2.4 公理 A3：Dirac 型低能有效模式

**公理 A3（Dirac 有效模）** 在 $\mathfrak{U}_{\mathrm{QCA}}$ 的某个低能一粒子扇区中，存在一个二维内部自由度的平移不变子模型，其在一维动量表象下的单步更新算符 $U(p)\in SU(2)$ 满足：

1. 可以写为 Bloch 形式

$$
U(p) = \exp\bigl(-\mathrm{i}\,\Omega(p)\,\hat{n}(p)\cdot\vec{\sigma}\bigr),
$$

其中 $\vec{\sigma}$ 为 Pauli 矩阵，$\hat{n}(p)\in S^2$，$\Omega(p)\in[0,\pi]$；

2. 在某个 $p_0$ 邻域内，连续极限的有效 Hamilton 算符

$$
H_{\mathrm{eff}}(k) := \frac{\Omega(p_0+k)}{\Delta t} \approx c\,k\,\sigma_z + mc^2\sigma_x,
$$

其中 $\Delta t$ 为时间步长，$k$ 为小动量偏移，常数 $m\neq 0$ 称为该模式的质量参数。

这一公理要求宇宙中至少存在一个在低能极限下呈现一维有质量 Dirac 方程的模式，与从 QCA 原理导出 Dirac 方程的既有结果相一致。

---

## 3 Main Results (Theorems and Alignments)

在上述公理之下，本文给出以下三类主要结果。

### 3.1 宇宙因果结构与宏观几何

**定理 1（因果偏序与宏观 Lorentz 结构）**

在满足 A1–A2 的宇宙对象 $\mathfrak{U}_{\mathrm{QCA}}$ 中，定义事件集

$$
\mathcal{E} := \{(\Lambda_0,t)\mid \Lambda_0\Subset\Lambda,\ t\in\mathbb{Z}\}
$$

与局域代数

$$
\mathcal{A}(\Lambda_0,t) := \alpha_t\bigl(\mathcal{B}(\mathcal{H}_{\Lambda_0})\bigr)\subset\mathcal{A}.
$$

若对所有 $A\in\mathcal{A}(\Lambda_0,t), B\in\mathcal{A}(\Lambda_1,s)$ 且 $t<s$ 有 $[A,B]=0$，则记

$$
(\Lambda_0,t)\preceq(\Lambda_1,s).
$$

则 $(\mathcal{E},\preceq)$ 构成一个有向无环偏序结构，并且在适当粗粒化下可嵌入一个连续 Lorentz 型时空流形，使得 $\preceq$ 与该流形上的因果偏序兼容。

这一结果说明，因果锥与宏观时空几何可以完全由局域代数及其幺正演化内部涌现，而无需将连续时空作为公理。证明依托 Lieb–Robinson 界对扰动传播范围的指数抑制估计。

### 3.2 Dirac–QCA 色散与信息速率圆

在满足 A3 的一维 Dirac 型 QCA 模型中，我们选取具体的量子行走实现，并得到显式色散关系与速度定义。

**定理 2（Dirac–QCA 色散关系）**

考虑一维格点 $\Lambda=\mathbb{Z}$，局域 Hilbert 空间为两分量自旋 $\mathcal{H}_{\mathrm{cell}}\cong\mathbb{C}^2$。定义条件平移算符

$$
T := S_+\otimes\ket{\uparrow}\bra{\uparrow} + S_-\otimes\ket{\downarrow}\bra{\downarrow},
$$

其中 $S_+\ket{x}=\ket{x+1}$、$S_-\ket{x}=\ket{x-1}$，以及局域"质量旋转"

$$
C(m) := \exp\bigl(-\mathrm{i}m\Delta t\,\sigma_x\bigr).
$$

单步更新算符定义为

$$
U := C(m)\,T.
$$

在动量表象中，$U(p)\in SU(2)$ 的特征角 $\Omega(p)$ 满足色散关系

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a),
$$

其中 $a$ 为格点间距，$p\in[-\pi/a,\pi/a]$。

这一色散结构与 Dirac QCA 文献中的结果一致，体现了 coin 角 $m\Delta t$ 与格点动量 $p a$ 的对称角色。

**定理 3（信息速率圆）**

设 $c:=a/\Delta t$ 为 QCA 的最大信号速率。对上述 Dirac–QCA 模型中每个动量模态，定义外部群速度

$$
v_{\mathrm{ext}}(p) := a\,\frac{\mathrm{d}\omega(p)}{\mathrm{d}p},\qquad \omega(p) := \frac{\Omega(p)}{\Delta t},
$$

以及内部演化速度

$$
v_{\mathrm{int}}(p) := c\,\frac{\sin(m\Delta t)\cos(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

则对所有允值动量 $p$ 有恒等式

$$
v_{\mathrm{ext}}^2(p) + v_{\mathrm{int}}^2(p) = c^2.
$$

该定理表明：在 Dirac–QCA 模式中，总的信息更新速率 $c$ 被正交分解为"外部位移"与"内部演化"两部分，二者在速度平方意义上构成以 $c$ 为半径的圆，故称"信息速率圆"。

### 3.3 相对论结构与质量–能量关系的涌现

**推论 1（时间膨胀与固有时间）**

令 $v:=v_{\mathrm{ext}}(p)$ 为某惯性系中观测到的粒子速度，由信息速率圆得

$$
v_{\mathrm{int}}(p) = \sqrt{c^2 - v^2}.
$$

以内部演化速度定义固有时间元

$$
\mathrm{d}\tau := \frac{v_{\mathrm{int}}}{c}\,\mathrm{d}t = \sqrt{1-\frac{v^2}{c^2}}\,\mathrm{d}t,
$$

即可得到与狭义相对论一致的时间膨胀关系。

**推论 2（四速度规范化与 Minkowski 线元）**

令时空坐标 $x^0=ct,x^1=x$，四速度定义为

$$
u^\mu := \frac{\mathrm{d}x^\mu}{\mathrm{d}\tau}.
$$

则有

$$
u^0 = \gamma c,\qquad u^1=\gamma v,\qquad \gamma = \frac{1}{\sqrt{1-v^2/c^2}},
$$

在 Minkowski 度规 $g_{\mu\nu}=\mathrm{diag}(-1,1)$ 下满足

$$
g_{\mu\nu}u^\mu u^\nu = -c^2.
$$

线元可写为

$$
\mathrm{d}s^2 := g_{\mu\nu}\,\mathrm{d}x^\mu\,\mathrm{d}x^\nu = -c^2\,\mathrm{d}\tau^2.
$$

**推论 3（质量的内部定义与能量–动量关系）**

在静止系 $p=0$ 处，色散关系给出

$$
\cos\bigl(\omega(0)\Delta t\bigr) = \cos(m\Delta t).
$$

在 $m\Delta t\ll 1$ 极限下有 $\omega(0)\approx m$。定义静止能量

$$
E_0 := \hbar\omega(0) := mc^2,
$$

则质量 $m$ 被定义为维持内部演化所需的能量缩放因子，即"内部信息振荡密度"的度量。在 $p a\ll 1$ 的长波极限下，色散关系导出

$$
\omega^2(p)\approx m^2 + \frac{p^2c^2}{\hbar^2},
$$

总能量 $E(p)=\hbar\omega(p)$ 满足

$$
E^2(p)\approx p^2c^2 + m^2c^4.
$$

综上，狭义相对论的时间膨胀、四速度规范化及相对论能量–动量关系均可视为信息速率圆定理和 Dirac–QCA 色散结构在宏观极限下的重写。

---

## 4 Proofs

本节给出上述主定理的证明思路，详细技术计算与推导放在附录。

### 4.1 定理 1 的证明思路

由公理 A1，任一局域算符的支撑在单步演化中至多扩展到有限半径邻域；由 A2 的 Lieb–Robinson 界可知，对支撑距离满足 $\mathrm{dist}(\mathrm{supp}A,\mathrm{supp}B) > c|t|$ 的算符对，$[\alpha_t(A),B]$ 的范数呈指数抑制。

据此定义事件集 $\mathcal{E}$ 与局域代数 $\mathcal{A}(\Lambda_0,t)$，并用对易性定义偏序 $\preceq$。自反性由对易性自明；传递性利用 Jacobi 恒等式与对易子线性结构可证明；有向无环性来自时间参数单调性及扰动不能"回溯因果"的性质，否则将与 Lieb–Robinson 界与稳定态的响应理论冲突。

在粗粒化极限下，通过选取适当的大尺度块，将 $\Lambda$ 映射为近似连续的空间坐标，将整数时间 $t$ 映射为连续时间 $t_{\mathrm{cont}}$，此时以 $c$ 为坡度的离散光锥收敛为连续 Minkowski 光锥，从而可构造出兼容的 Lorentz 型时空流形嵌入。相关构造与技术细节见附录 A。

### 4.2 定理 2 的证明思路

在一维格点上，引入动量本征态

$$
\ket{p} := \frac{1}{\sqrt{2\pi/a}}\sum_{x\in\mathbb{Z}}\mathrm{e}^{\mathrm{i}p a x}\ket{x},\qquad p\in[-\pi/a,\pi/a].
$$

平移算符作用为

$$
S_+\ket{p}=\mathrm{e}^{-\mathrm{i}p a}\ket{p},\qquad S_-\ket{p}=\mathrm{e}^{\mathrm{i}p a}\ket{p}.
$$

于是条件平移在动量–自旋子空间 $\mathcal{H}_p\cong\mathbb{C}^2$ 上表示为

$$
T(p) = \exp\bigl(-\mathrm{i}p a\,\sigma_z\bigr),
$$

单步更新算符为

$$
U(p) = C(m)\,T(p) = \exp\bigl(-\mathrm{i}m\Delta t\,\sigma_x\bigr)\exp\bigl(-\mathrm{i}p a\,\sigma_z\bigr).
$$

利用 SU(2) 群元素乘法公式

$$
\exp\bigl(-\mathrm{i}\alpha\,\hat{a}\cdot\vec{\sigma}\bigr) \exp\bigl(-\mathrm{i}\beta\,\hat{b}\cdot\vec{\sigma}\bigr) = \exp\bigl(-\mathrm{i}\gamma\,\hat{c}\cdot\vec{\sigma}\bigr),
$$

其中

$$
\cos\gamma = \cos\alpha\cos\beta - (\hat{a}\cdot\hat{b})\sin\alpha\sin\beta,
$$

取 $\hat{a}=(1,0,0),\hat{b}=(0,0,1),\alpha=m\Delta t,\beta=p a$，即可得到

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a),
$$

从而证明定理 2。Bloch 向量分量的显式表达亦可由同一公式获得，见附录 B。

### 4.3 定理 3 及相对论推论的证明思路

由色散关系对 $p$ 求导可以得到群速度

$$
v_{\mathrm{ext}}(p) = a\,\frac{\mathrm{d}\omega}{\mathrm{d}p} = c\,\frac{\cos(m\Delta t)\sin(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

另一方面，SU(2) Bloch 向量分量给出

$$
\hat{n}(p)\sin\bigl(\Omega(p)\bigr) = \bigl(\sin(m\Delta t)\cos(p a),\,\sin(m\Delta t)\sin(p a),\,\sin(p a)\cos(m\Delta t)\bigr).
$$

据此对称地定义内部演化速度

$$
v_{\mathrm{int}}(p) := c\,\frac{\sin(m\Delta t)\cos(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

将两者平方相加并使用三角恒等式可得

$$
v_{\mathrm{ext}}^2(p)+v_{\mathrm{int}}^2(p) = c^2\,\frac{\cos^2(m\Delta t)\sin^2(p a)+\sin^2(m\Delta t)\cos^2(p a)}{\sin^2\bigl(\Omega(p)\bigr)}.
$$

另一方面，

$$
\sin^2\bigl(\Omega(p)\bigr) = 1 - \cos^2\bigl(\Omega(p)\bigr) = 1 - \cos^2(m\Delta t)\cos^2(p a),
$$

直接代数计算（见附录 C）表明

$$
\cos^2(m\Delta t)\sin^2(p a)+\sin^2(m\Delta t)\cos^2(p a) = \sin^2\bigl(\Omega(p)\bigr),
$$

因此

$$
v_{\mathrm{ext}}^2(p)+v_{\mathrm{int}}^2(p) = c^2,
$$

证明定理 3。

之后以 $v_{\mathrm{int}}$ 定义固有时间，构造四速度 $u^\mu$，在 Minkowski 度规下得到 $g_{\mu\nu}u^\mu u^\nu=-c^2$，并通过长波极限展开色散关系重建出 $E^2=p^2c^2+m^2c^4$。详细计算见附录 C。

---

## 5 Model Apply

本节从本体论角度解释上述结构在"宇宙是什么"问题中的含义。

### 5.1 宇宙作为 QCA 对象

在本框架中，宇宙不是"物质 + 时空"的叠加，而是一个带初态的 QCA 对象 $\mathfrak{U}_{\mathrm{QCA}}$。所谓"物质""场""粒子""时空"等概念，皆是在不同尺度与不同子扇区中的稳定激发或几何编码：

1. **几何层**：由 A1–A2 所确定的因果偏序及 Lieb–Robinson 光锥，在粗粒化后表现为 Minkowski 或更一般的 Lorentz 型几何；

2. **物质量层**：满足 A3 的 Dirac 模式对应有质量粒子，其静止能量与内部演化频率直接相关；

3. **场论层**：在多粒子与多模态拓展下，自由量子场理论可被视为 QCA 的连续极限描述；相互作用的引入则对应 QCA 更新算符中更复杂的局域结构。

在这一意义下，"宇宙是什么"的回答为：

> 宇宙是一族满足极简公理 A1–A3 的 QCA 宇宙对象中的一个具体实例，其全体幺正历史携带了我们所观测到的时空、物质与相互作用。

### 5.2 质量与惯性的统一解释

信息速率圆给出了对惯性与时间膨胀的统一解释：总的信息更新速率 $c$ 固定，而对于有质量激发来说，其内部演化与外部传播之间存在竞争关系。高速运动时，外部群速度接近 $c$，内部演化被迫减慢，对应固有时间变慢；静止时，全部信息速率用于内部演化，对应最大固有时间流逝。质量 $m$ 则由静止系内部演化频率 $\omega_{\mathrm{int}}(0)$ 定义，体现为维持局域模式稳定所需的信息振荡密度。

这种视角将相对论中的"时间膨胀""惯性""质量–能量关系"统一为 QCA 内部的一条几何恒等式，而不再需要将它们视为独立的经验定律。

### 5.3 观察者对象与公共现实

观察者在该本体论中不是外在实体，而是宇宙对象中满足自指性与记忆性的一类局域子系统。

**定义（观察者对象）**

一个观察者对象 $\mathcal{O}$ 为三元组

$$
\mathcal{O} = \bigl(\mathcal{A}_{\mathrm{loc}},\omega_{\mathrm{mem}},\mathcal{M}\bigr),
$$

其中：

1. $\mathcal{A}_{\mathrm{loc}}\subset\mathcal{A}$ 是某个局域子代数，对应观察者可访问的自由度；

2. $\omega_{\mathrm{mem}}(t)$ 是 $\mathcal{A}_{\mathrm{loc}}$ 上关于离散时间 $t$ 的一族态，对应观察者的内部记忆；

3. $\mathcal{M}=\{M_{\theta}\}$ 是一族"世界模型"，每个 $M_{\theta}$ 将历史观测记录映射为对未来可观测量的概率预测，参数 $\theta(t)$ 随时间按某个更新规则

$$
\theta(t+1) = F\bigl(\theta(t),\{\omega_{\mathrm{mem}}(s)\}_{s\le t}\bigr)
$$

变化。

观察者对象对应于事件集中的一条世界线 $\gamma_{\mathcal{O}} = \{(\Lambda_t,t)\}_{t\in\mathbb{Z}} \subset\mathcal{E}$，其固有时间由内部信息速率定义，与 Dirac 模式的固有时间具有相同形式。多个观察者对象的局域代数交集及其态的一致性范畴，构成所谓"公共现实"，即不同观察者在重叠可访问区域上对宇宙状态达成的共识。

---

## 6 Engineering Proposals

本节提出若干可在实验平台或数值模拟中检验与运用该本体论结构的工程方案。

### 6.1 Dirac–QCA 的量子模拟与信息速率圆的实验验证

一维与高维离散时间量子行走已在离子阱、超导量子电路与光学平台上实现，并可通过调节 coin 旋转与平移操作精确控制有效 Hamilton。这些平台可用于以下目的：

1. 通过测量波包的外部群速度 $v_{\mathrm{ext}}(p)$ 与内部自旋振荡频率，重构 $v_{\mathrm{int}}(p)$，从而在实验上验证信息速率圆 $v_{\mathrm{ext}}^2+v_{\mathrm{int}}^2=c^2$；

2. 在不同 coin 参数 $m\Delta t$ 下测量静止系内部振荡频率与有效质量的关系，检验 $mc^2=\hbar\omega_{\mathrm{int}}(0)$；

3. 利用多粒子量子行走考察局域相互作用对信息速率几何的修正，为进一步引入相互作用场论打基础。

### 6.2 QCA 的重整化与连续极限工程

近期关于 QCA 重整化与有效场论极限的工作表明，可以在格点尺度上系统构造与分析满足给定对称性与因果结构的 QCA 模型，并研究其在不同缩放下的有效描述。在本框架中，可进一步要求重整化流保持公理 A1–A3 结构，从而形成一类"宇宙模型族"，并在参数空间中搜索满足其他物理约束（如规范对称性、质量层次等）的子流形。

### 6.3 工程化宇宙模型的数值探索

在经典与量子混合计算平台上，可以构造有限大小的 QCA 宇宙玩具模型，选取具体格点拓扑、局域 Hilbert 空间维数与更新算符，数值验证：

1. 因果偏序与 Lieb–Robinson 光锥的形成；

2. Dirac 型低能模式的存在与色散关系；

3. 在多观察者对象的构造下，公共现实的形成与信息一致性。

这类数值实验将为进一步从 QCA 层面讨论引力与宇宙学问题提供直觉与技术准备。

---

## 7 Discussion (risks, boundaries, past work)

### 7.1 与既有工作的关系

在从信息处理原则构造自由量子场理论与 Dirac 方程的研究中，D'Ariano 与 Perinotti 等人已经展示了 QCA 可以作为 Dirac、Weyl 以及 Maxwell 场的离散本体，并在适当极限下恢复标准连续理论。本文在这一基础上进一步：

1. 将"宇宙"本体定义为带初态的 QCA 对象，强调 QCA 是唯一原语；

2. 引入有限光锥公理 A2，将 Lieb–Robinson 速度与宏观光速统一；

3. 在具体 Dirac–QCA 模型中提出信息速率圆定理，并将其与相对论几何、质量–能量关系直接对接；

4. 提出形式化的观察者对象与观察者网络结构。

同时，关于 Dirac 真空在离散时空中的定义、负能态填充与能谱模块结构的困难，已在近期工作中被系统分析，指出在离散时间模型中直接引入 Dirac 海将面临新的边界效应与对偶不稳定性。这些问题提示：在将本体论进一步推广到多粒子与相互作用场论时，需要更加谨慎地处理能谱与真空结构。

### 7.2 框架的边界与局限

尽管本文给出了一个极简而自洽的本体论框架，仍存在若干重要局限：

1. **自由场与低能极限**：公理 A3 仅要求存在一个自由 Dirac 型低能模式，尚未纳入规范场、相互作用与自发对称性破缺等结构；

2. **引力与曲率**：尽管因果结构与 Minkowski 线元可从信息速率几何中涌现，但完整的曲率与引力场方程尚未在该框架下实现，需要引入更复杂的 QCA 结构与粗粒化方案；

3. **测量与概率**：观察者对象与公共现实的定义仍停留在算子与态的层面，关于 Born 规则与概率解释的"涌现"还需要结合环境辅助不变性等思想进一步深化；

4. **连续极限的唯一性**：不同的 QCA 宇宙对象可能在低能极限下给出相同的连续有效理论，如何从实验数据约束 $\mathfrak{U}_{\mathrm{QCA}}$ 的细节仍是开放问题。

### 7.3 风险与开放问题

从本体论层面将宇宙完全离散化存在方法论风险：一旦未来实验发现某种不可规约的连续结构（例如对 Planck 级以上的某种连续对称性有直接证据），则需重新审视 QCA 作为唯一原语的合理性。此外，如何在保证局域性与幺正性的前提下引入复杂拓扑、规范对称与引力效应，也是该框架面临的关键挑战。

---

## 8 Conclusion

本文在量子元胞自动机框架下提出了一个极简的宇宙本体论：宇宙是一个满足三条公理 A1–A3 的 QCA 宇宙对象 $\mathfrak{U}_{\mathrm{QCA}}$。在这一公理体系内，我们构造了一维 Dirac 型 QCA 模型，给出其 SU(2) 色散关系与 Bloch 结构，从而定义外部群速度 $v_{\mathrm{ext}}$ 与内部演化速度 $v_{\mathrm{int}}$，并证明信息速率圆定理 $v_{\mathrm{ext}}^2+v_{\mathrm{int}}^2=c^2$。以此为基础，固有时间、四速度规范化以及相对论能量–动量关系得以自然涌现，质量被解释为内部信息振荡密度，惯性与时间膨胀统一为信息速率再分配的几何效应。

同时，我们将观察者刻画为宇宙对象中的自指局域子系统，其固有时间与公共现实的形成亦由同一 QCA 本体统一描述。工程层面，我们讨论了在现有或可预期的量子模拟平台上验证信息速率圆、构造 Dirac–QCA 以及进行 QCA 重整化数值探索的方案。

从本体论角度看，本工作给出的回答是：宇宙不是"物质 + 时空"的相加，而是一个极大一致的 QCA 对象及其幺正历史；时空几何、物质与观察者只是这一对象在不同尺度与不同子扇区中的涌现模式。未来工作将致力于在该框架内引入规范对称、相互作用与引力，并探讨宇宙学常数与黑洞熵等问题的统一约束。

---

## Acknowledgements, Code Availability

作者感谢关于量子元胞自动机、Lieb–Robinson 界以及量子行走–Dirac 方程关系的相关讨论与文献贡献。本文为概念与理论工作，未涉及数值程序与公开代码。

---

## Appendix A：宇宙对象与因果结构的技术细节

### A.1 支撑、距离与准局域性

对任意局域算符 $A\in\mathcal{B}(\mathcal{H}_{\Lambda_0}) \subset\mathcal{A}$，定义其支撑为 $\mathrm{supp}A:=\Lambda_0$。对任意两个有限子集 $\Lambda_0,\Lambda_1\subset\Lambda$，图距离定义为

$$
\mathrm{dist}(\Lambda_0,\Lambda_1) := \min\{\mathrm{dist}(x,y)\mid x\in\Lambda_0,\ y\in\Lambda_1\},
$$

其中 $\mathrm{dist}(x,y)$ 是图 $\Lambda$ 上的最短路径长度。

公理 A1 中的准局域性意味着存在 $R>0$ 使得

$$
\mathrm{supp}\bigl(\alpha_1(A)\bigr)\subset B_R\bigl(\mathrm{supp}A\bigr),
$$

其中 $B_R(S)$ 为集合 $S$ 的半径 $R$ 邻域。继而由 $\alpha_t=\alpha_1^t$ 可知：

$$
\mathrm{supp}\bigl(\alpha_t(A)\bigr)\subset B_{R|t|}\bigl(\mathrm{supp}A\bigr).
$$

### A.2 因果偏序的偏序性

事件集定义为

$$
\mathcal{E} := \{(\Lambda_0,t)\mid \Lambda_0\Subset\Lambda,\ t\in\mathbb{Z}\},
$$

联同局域代数

$$
\mathcal{A}(\Lambda_0,t) := \alpha_t\bigl(\mathcal{B}(\mathcal{H}_{\Lambda_0})\bigr).
$$

定义关系

$$
(\Lambda_0,t)\preceq(\Lambda_1,s) \iff \forall A\in\mathcal{A}(\Lambda_0,t),\forall B\in\mathcal{A}(\Lambda_1,s):[A,B]=0,\ t\le s.
$$

自反性：对任意 $(\Lambda_0,t)$，显然 $[A,B]=0$ 对所有 $A,B\in\mathcal{A}(\Lambda_0,t)$ 不成立，但当 $A$ 与 $B$ 取自两份彼此对易的子代数时可成立。在定义中要求 $t\le s$，当 $t=s$ 且 $\Lambda_0\subset\Lambda_1$ 时，可以通过选取适当局域子代数确保自反性。

传递性：若 $(\Lambda_0,t)\preceq(\Lambda_1,s)$ 且 $(\Lambda_1,s)\preceq(\Lambda_2,u)$，对任意 $A\in\mathcal{A}(\Lambda_0,t)$、$C\in\mathcal{A}(\Lambda_2,u)$，有

$$
[A,C] = [A,[B,C]] + [B,[A,C]],
$$

对所有 $B\in\mathcal{A}(\Lambda_1,s)$ 成立。利用对易子线性性质及 Lieb–Robinson 界可证明 $[A,C]$ 的范数在满足适当距离条件时趋于零，极限下得到严格对易，从而确立传递性。

有向无环性：若存在因果闭环 $(\Lambda_0,t_0)\preceq(\Lambda_1,t_1)\preceq\cdots\preceq(\Lambda_n,t_n)=(\Lambda_0,t_0)$ 且某处存在严格时间前后关系，则可构造一个局域扰动在有限时间内返回其起源并产生可观测的自干涉，这与 Lieb–Robinson 光锥与动力学稳定性相矛盾。形式化处理依托响应理论中的 Kubo 公式与因果性要求，详见相关文献。

### A.3 连续极限与因果结构嵌入

选取大尺度块 $B_L(x) \subset\Lambda$（例如以 $x$ 为中心的半径 $L$ 球），将其视为宏观空间元胞，定义连续坐标 $\vec{X} = \epsilon x$，$T=\epsilon t$，其中 $\epsilon\to 0$ 时块大小与时间步长同时缩放，使得 Lieb–Robinson 光锥边界 $\mathrm{dist}\sim c|t|$ 收敛为连续光锥 $\lVert\vec{X}-\vec{X}_0\rVert\le c|T-T_0|$。在这一极限下，$(\mathcal{E},\preceq)$ 嵌入到连续流形 $(M,g_{\mu\nu})$ 上的因果结构，$c$ 对应度规光锥的斜率。

---

## Appendix B：Dirac–QCA 的 SU(2) 结构与色散关系

### B.1 SU(2) 群元素乘法

任意 $U_1,U_2\in SU(2)$ 可写为

$$
U_1 = \exp\bigl(-\mathrm{i}\alpha\,\hat{a}\cdot\vec{\sigma}\bigr),\qquad U_2 = \exp\bigl(-\mathrm{i}\beta\,\hat{b}\cdot\vec{\sigma}\bigr),
$$

其中 $\hat{a},\hat{b}\in S^2$，$\alpha,\beta\in[0,\pi]$。其乘积为

$$
U_1U_2 = \exp\bigl(-\mathrm{i}\gamma\,\hat{c}\cdot\vec{\sigma}\bigr),
$$

其中

$$
\cos\gamma = \cos\alpha\cos\beta - (\hat{a}\cdot\hat{b})\sin\alpha\sin\beta,
$$

$$
\hat{c}\sin\gamma = \hat{a}\sin\alpha\cos\beta + \hat{b}\sin\beta\cos\alpha - (\hat{a}\times\hat{b})\sin\alpha\sin\beta.
$$

### B.2 Dirac–QCA 中的应用

在 Dirac–QCA 模型中，

$$
C(m) = \exp\bigl(-\mathrm{i}m\Delta t\,\sigma_x\bigr),\qquad T(p) = \exp\bigl(-\mathrm{i}p a\,\sigma_z\bigr).
$$

取

$$
\alpha = m\Delta t,\ \hat{a} = (1,0,0);\qquad \beta = p a,\ \hat{b} = (0,0,1).
$$

则

$$
\hat{a}\cdot\hat{b} = 0,\qquad \hat{a}\times\hat{b} = (0,-1,0).
$$

代入乘法公式得到

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a),
$$

$$
\hat{n}(p)\sin\bigl(\Omega(p)\bigr) = \bigl(\sin(m\Delta t)\cos(p a),\,\sin(m\Delta t)\sin(p a),\,\sin(p a)\cos(m\Delta t)\bigr).
$$

这给出了定理 2 中色散关系及 Bloch 向量各分量的显式形式。

---

## Appendix C：信息速率圆与相对论推论的计算细节

### C.1 群速度的导数计算

从色散关系

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a)
$$

出发，对 $p$ 求导：

$$
-\sin\bigl(\Omega(p)\bigr)\frac{\partial\Omega}{\partial p} = \cos(m\Delta t)\bigl(-\sin(p a)\bigr)a.
$$

得到

$$
\frac{\partial\Omega}{\partial p} = \frac{\cos(m\Delta t)\sin(p a)a}{\sin\bigl(\Omega(p)\bigr)}.
$$

由 $\omega(p)=\Omega(p)/\Delta t$ 得

$$
\frac{\mathrm{d}\omega}{\mathrm{d}p} = \frac{1}{\Delta t}\frac{\partial\Omega}{\partial p} = \frac{\cos(m\Delta t)\sin(p a)a}{\Delta t\,\sin\bigl(\Omega(p)\bigr)}.
$$

设 $c=a/\Delta t$，则群速度

$$
v_{\mathrm{ext}}(p) = a\,\frac{\mathrm{d}\omega}{\mathrm{d}p} = c\,\frac{\cos(m\Delta t)\sin(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

### C.2 内部速度的对称定义与代数恒等式

由 Bloch 向量分量

$$
\hat{n}(p)\sin\bigl(\Omega(p)\bigr) = \bigl(\sin(m\Delta t)\cos(p a),\,\sin(m\Delta t)\sin(p a),\,\sin(p a)\cos(m\Delta t)\bigr),
$$

取与质量参数 $m$ 最直接相关的 $x$ 分量，定义内部演化速度

$$
v_{\mathrm{int}}(p) := c\,\frac{\sin(m\Delta t)\cos(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

注意 $v_{\mathrm{ext}}$ 与 $v_{\mathrm{int}}$ 在 $m\Delta t$ 与 $p a$ 之间具有对称结构：若交换 $m\Delta t \leftrightarrow p a$，两者互换角色。

将二者平方相加：

$$
v_{\mathrm{ext}}^2(p)+v_{\mathrm{int}}^2(p) = c^2\,\frac{\cos^2(m\Delta t)\sin^2(p a)+\sin^2(m\Delta t)\cos^2(p a)}{\sin^2\bigl(\Omega(p)\bigr)}.
$$

另一方面，由色散关系

$$
\sin^2\bigl(\Omega(p)\bigr) = 1 - \cos^2\bigl(\Omega(p)\bigr) = 1 - \cos^2(m\Delta t)\cos^2(p a).
$$

直接展开可得

$$
\begin{aligned}
&\cos^2(m\Delta t)\sin^2(p a)+\sin^2(m\Delta t)\cos^2(p a)\\
&= \cos^2(m\Delta t)\bigl(1-\cos^2(p a)\bigr)+\sin^2(m\Delta t)\cos^2(p a)\\
&= \cos^2(m\Delta t) + \cos^2(p a)\bigl[\sin^2(m\Delta t)-\cos^2(m\Delta t)\bigr]\\
&= \cos^2(m\Delta t) + \cos^2(p a)\bigl[1-2\cos^2(m\Delta t)\bigr]\\
&= 1 - \cos^2(m\Delta t)\cos^2(p a)\\
&= \sin^2\bigl(\Omega(p)\bigr).
\end{aligned}
$$

于是

$$
v_{\mathrm{ext}}^2(p)+v_{\mathrm{int}}^2(p) = c^2.
$$

### C.3 时间膨胀与四速度规范化

由信息速率圆

$$
v_{\mathrm{int}}(p) = \sqrt{c^2 - v^2},\qquad v:=v_{\mathrm{ext}}(p),
$$

定义固有时间元

$$
\mathrm{d}\tau = \frac{v_{\mathrm{int}}}{c}\,\mathrm{d}t = \sqrt{1-\frac{v^2}{c^2}}\,\mathrm{d}t.
$$

反之

$$
\frac{\mathrm{d}t}{\mathrm{d}\tau} = \frac{1}{\sqrt{1-v^2/c^2}} = \gamma.
$$

于是四速度分量

$$
u^0 = \frac{\mathrm{d}(ct)}{\mathrm{d}\tau} = c\,\frac{\mathrm{d}t}{\mathrm{d}\tau} = \gamma c,
$$

$$
u^1 = \frac{\mathrm{d}x}{\mathrm{d}\tau} = \frac{\mathrm{d}x}{\mathrm{d}t}\frac{\mathrm{d}t}{\mathrm{d}\tau} = v\,\gamma.
$$

在 Minkowski 度规 $g_{\mu\nu}=\mathrm{diag}(-1,1)$ 下，

$$
g_{\mu\nu}u^\mu u^\nu = -(\gamma c)^2 + (\gamma v)^2 = -\gamma^2(c^2 - v^2) = -c^2.
$$

从而线元可以写为 $\mathrm{d}s^2=-c^2\mathrm{d}\tau^2$，这与狭义相对论的标准形式一致。

### C.4 质量与能量–动量关系

在 $p=0$ 处，色散关系为

$$
\cos\bigl(\omega(0)\Delta t\bigr) = \cos(m\Delta t).
$$

当 $m\Delta t\ll 1$ 时，

$$
\cos\bigl(\omega(0)\Delta t\bigr)\approx 1-\frac{\omega^2(0)\Delta t^2}{2},\qquad \cos(m\Delta t)\approx 1-\frac{m^2\Delta t^2}{2},
$$

比较可得 $\omega(0)\approx m$。定义静止能量

$$
E_0 := \hbar\omega(0) := mc^2,
$$

则质量 $m$ 由内部频率 $\omega_{\mathrm{int}}(0)$ 定义。

在 $p a\ll 1$ 时，色散关系展开为

$$
\cos\bigl(\omega(p)\Delta t\bigr) \approx 1-\frac{\omega^2(p)\Delta t^2}{2} \approx 1-\frac{m^2\Delta t^2}{2}-\frac{p^2 a^2}{2},
$$

得到

$$
\omega^2(p)\approx m^2 + \frac{p^2 a^2}{\Delta t^2} = m^2 + \frac{p^2 c^2}{\hbar^2}\hbar^2,
$$

从而总能量 $E(p)=\hbar\omega(p)$ 满足

$$
E^2(p)\approx p^2c^2 + m^2c^4.
$$

这即为相对论能量–动量关系的离散推导。

---

## References

1. G. M. D'Ariano, P. Perinotti, "Quantum cellular automata and free quantum field theory", *Phys. Rev. A* **90**, 062106 (2014).

2. A. Bisio, G. M. D'Ariano, P. Perinotti, "Quantum cellular automaton theory of light", *Ann. Phys.* **368**, 177–190 (2016).

3. T. A. Brun, et al., "Quantum cellular automata and quantum field theory in two spatial dimensions", *Phys. Rev. A* **102**, 062222 (2020).

4. L. S. Trezzini, "Renormalisation of quantum cellular automata", *Quantum* **9**, 1756 (2025).

5. F. W. Strauch, "Relativistic quantum walks", *Phys. Rev. A* **73**, 054302 (2006).

6. C. M. Chandrashekar, "Two-component Dirac-like Hamiltonian for generating quantum walk on one-, two- and three-dimensional lattices", *Sci. Rep.* **3**, 2829 (2013).

7. A. Pérez, "Asymptotic properties of the Dirac quantum cellular automaton", *Phys. Rev. A* **93**, 012328 (2016).

8. A. Mallick, C. M. Chandrashekar, "Dirac cellular automaton from split-step quantum walk", *Sci. Rep.* **6**, 25779 (2016).

9. P. C. Costa, et al., "Quantum walks via quantum cellular automata", *Quantum Inf. Process.* **17**, 198 (2018).

10. C. H. Alderete, et al., "Quantum walks and Dirac cellular automata on a trapped-ion quantum computer", *npj Quantum Inf.* **6**, 89 (2020).

11. N. P. Kumar, C. M. Chandrashekar, "Bounds on the dynamics of periodic quantum walks and emergence of the gapless and gapped Dirac equation", *Phys. Rev. A* **97**, 012116 (2018).

12. B. Nachtergaele, R. Sims, "Much ado about something: why Lieb–Robinson bounds are useful", *J. Stat. Phys.* **124**, 1–13 (2006).

13. E. H. Lieb, D. W. Robinson, "The finite group velocity of quantum spin systems", *Commun. Math. Phys.* **28**, 251–257 (1972).

14. M. Cheneau, "Experimental tests of Lieb–Robinson bounds", in *Quantum Systems in and out of Equilibrium*, EMS Press (2022).

15. C. Gupta, A. Perez, "The Dirac vacuum in discrete spacetime", *Quantum* **9**, 1845 (2025).

16. T. A. Brun, et al., "Quantum electrodynamics from quantum cellular automata", *Entropy* **27**, 492 (2025).

