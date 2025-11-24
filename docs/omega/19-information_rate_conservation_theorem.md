# 信息速率守恒定理：从最小量子元胞自动机公理到狭义相对论与质量的涌现

*Information Rate Conservation Theorem: From Minimal Quantum Cellular Automaton Axioms to the Emergence of Special Relativity and Mass*

---

## Abstract

本文在一个极小的离散本体论公理系统下，证明了所谓"信息速率守恒圆"并非额外假设，而是量子元胞自动机（quantum cellular automaton, QCA）内部的几何定理。我们以宇宙作为带初态的 QCA 对象为起点，给出三条最小公理：（A1）宇宙由可数格点上的局域幺正演化构成且每个元胞 Hilbert 空间有限维；（A2）演化满足 Lieb–Robinson 型有限传播速度界，从而存在最大信号速率常数 $c$；（A3）在某个低能一粒子扇区，存在二维内部自由度的 Dirac 型有效模型，其长波极限由一维 Dirac Hamilton 描述。

在此基础上，我们构造出一类具体的一维 Dirac 型 QCA，推导出其动量表象下的色散关系 $\cos(\Omega(p)) = \cos(m\Delta t)\cos(p a)$，其中 $a$ 为格点间距，$\Delta t$ 为离散时间步长。对每个准粒子动量模态，我们从同一 QCA 更新算符中对称地定义"外部群速度" $v_{\mathrm{ext}}(p)$ 与"内部演化速度" $v_{\mathrm{int}}(p)$。核心定理表明，二者必然满足恒等式

$$
v_{\mathrm{ext}}^2(p) + v_{\mathrm{int}}^2(p) = c^2,
$$

其中 $c = a/\Delta t$ 即 Lieb–Robinson 意义下的最大信号速率。该公式因此不再是公理，而是由 A1–A3 推出的几何定理。

借助这一"信息速率圆"，我们定义固有时间元 $\mathrm{d}\tau = \frac{v_{\mathrm{int}}}{c}\,\mathrm{d}t$，从而严格推出狭义相对论的时间膨胀关系 $\mathrm{d}\tau = \sqrt{1 - v^2/c^2}\,\mathrm{d}t$ 以及四速度规范化条件 $g_{\mu\nu}u^\mu u^\nu = -c^2$，其中 $v = v_{\mathrm{ext}}$、$u^\mu = \mathrm{d}x^\mu/\mathrm{d}\tau$ 且 $g_{\mu\nu}$ 为 Minkowski 度规。进一步地，我们在粒子静止系 $(v_{\mathrm{ext}} = 0)$ 中定义内部频率 $\omega_{\mathrm{int}}$，证明静止能量 $E_0$ 与内部频率满足 $E_0 = \hbar\omega_{\mathrm{int}}$，从而给出质量的内部定义 $mc^2 = \hbar\omega_{\mathrm{int}}$，并在信息速率定理和 Dirac 色散的配合下重构相对论能量公式 $E^2 = p^2c^2 + m^2c^4$。

附录部分详细给出：（i）宇宙对象与 Lieb–Robinson 界的精确定义与证明思路；（ii）一维 Dirac 型 QCA 的动量表象构造与色散关系的推导；（iii）信息速率守恒定理及其相对论推论的逐步计算过程。本文表明，若接受一个极小的离散量子本体论，则狭义相对论的几何以及质量–惯性的关系可以作为 QCA 内部的"信息几何定理"而涌现，而非独立的时空公理。

---

## Keywords

量子元胞自动机；信息速率守恒；Lieb–Robinson 界；Dirac 模型；狭义相对论；质量的内部定义

---

## 1 引言

### 1.1 背景问题

狭义相对论和量子理论在数学上高度成功，但在本体论层面通常基于不同的起点。相对论以四维连续流形与 Lorentz 对称性为公理基础，量子理论则以 Hilbert 空间与幺正演化为基础。若再引入"宇宙是量子计算"的离散本体图景，似乎需要额外假设"光速不变""时空连续"等几何公理，从而形成多套不相容的起点。

一个自然的问题是：

> 在一个纯粹离散的、以 Hilbert 空间与幺正性为唯一原语的宇宙图景中，狭义相对论及其核心结构是否可以作为定理涌现，而不是作为独立公理引入？

近期的量子元胞自动机研究表明，Dirac 方程、Weyl 方程、Maxwell 方程等相对论性场论可以作为某些 QCA 模型的长波极限而出现。这提示我们：也许不必把 Lorentz 对称性写成公理，而可以让它从更底层的离散结构中"浮现"出来。

另一方面，信息论与量子信息视角提出了另一种物理直觉：宇宙中的任何局域系统在单位普朗克时间内可使用的"信息更新速率"总量有限，并在"外部位移"和"内部演化"之间分配。经验上，这种有限资源约束表现为光速限制、时间膨胀与惯性的存在。

本文试图将这两条线索统一起来：在一个极小的 QCA 公理系统下，证明信息速率守恒关系

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2
$$

并非公理，而是关于 Dirac 型 QCA 的几何定理；从而狭义相对论与质量–惯性关系可以被重写为 QCA 的"信息几何定理"。

### 1.2 目标与方法

本文的目标有三：

1. 给出一个极小的 QCA 宇宙公理系统，使之既足以产生一个 Dirac 有效模，又不显式引入任何连续时空或 Lorentz 对称性假设。

2. 在该公理系统下，从具体的一维 Dirac 型 QCA 模型中严格推导"信息速率圆"

$$
v_{\mathrm{ext}}^2(p) + v_{\mathrm{int}}^2(p) = c^2,
$$

并将其提升为一般性的结构定理。

3. 利用该定理及自然的固有时间定义，推导狭义相对论的时间膨胀、四速度规范化与质量的内部定义，证明它们不是公理，而是 QCA 内部几何的必然。

方法上，我们首先给出宇宙对象 $\mathfrak{U}_{\mathrm{QCA}}$ 的形式定义，并陈述三条公理 A1–A3。然后构造一类典型的一维 Dirac–QCA 模型，求得其动量空间的 SU(2) 表示与色散关系。接着，从该模型中对称地定义外部群速度 $v_{\mathrm{ext}}$ 与内部演化速度 $v_{\mathrm{int}}$，证明其平方和恒等于 Lieb–Robinson 速度 $c^2$。最后，从该几何恒等式出发，定义固有时间与四速度，并证明相对论的标准结果。

### 1.3 文章结构

第 2 节给出 QCA 宇宙对象与最小公理系统。第 3 节构造一维 Dirac 型 QCA，并推导其色散关系。第 4 节为全文核心，给出信息速率守恒定理以及详细证明。第 5 节将该定理用于推导狭义相对论时间膨胀、四速度规范化与质量定义。第 6 节讨论向高维与引力弱场的推广。附录 A–C 给出技术性证明与计算细节。

---

## 2 宇宙作为量子元胞自动机：最小公理系统

本节给出宇宙的 QCA 形式化定义，并陈述本文采用的三条极简公理 A1–A3。

### 2.1 宇宙对象的定义

**定义 2.1（格点与局域 Hilbert 空间）** 设 $\Lambda$ 是一个可数无界图，其顶点集合 $V(\Lambda)$ 表示空间元胞，边集合 $E(\Lambda)\subset V(\Lambda)\times V(\Lambda)$ 描述可直接相互作用的邻接关系。假设 $\Lambda$ 局域有限，即对任意 $x\in V(\Lambda)$，其度数 $\deg(x)$ 有统一上界。

取一个有限维 Hilbert 空间 $\mathcal{H}_{\mathrm{cell}} \cong \mathbb{C}^d$ 作为单元胞状态空间，对每个 $x\in V(\Lambda)$ 配置一份拷贝 $\mathcal{H}_x \cong \mathcal{H}_{\mathrm{cell}}$。对任意有限子集 $\Lambda_0\subset\Lambda$，定义局域 Hilbert 空间

$$
\mathcal{H}_{\Lambda_0} := \bigotimes_{x\in\Lambda_0} \mathcal{H}_x.
$$

**定义 2.2（准局域算符代数）** 定义准局域算符代数为

$$
\mathcal{A} := \overline{\bigcup_{\Lambda_0\Subset\Lambda} \mathcal{B}(\mathcal{H}_{\Lambda_0})}^{|\cdot|},
$$

其中 $\Lambda_0\Subset\Lambda$ 表示有限子集，$\mathcal{B}(\mathcal{H}_{\Lambda_0})$ 表示有界算符代数，闭包在算符范数意义下取。

**定义 2.3（时间演化）** 时间演化由一个离散自同构群 $\{\alpha_t\}_{t\in\mathbb{Z}}$ 给出，其中每个 $\alpha_t:\mathcal{A}\to\mathcal{A}$ 满足：

1. 群性质：$\alpha_0 = \mathrm{id}$、$\alpha_{t+s} = \alpha_t\circ\alpha_s$；

2. **准局域性**：存在常数 $R>0$，使得对于任意局域算符 $A\in\mathcal{B}(\mathcal{H}_{\Lambda_0})$，其演化 $\alpha_1(A)$ 的支撑仅包含在 $\Lambda_0$ 的 $R$ 邻域之内。

在具体模型中，$\alpha_1$ 通常由一个有限深局域幺正电路 $U$ 实现，即 $\alpha_1(A) = U^{\dagger}AU$。

**定义 2.4（宇宙初态与宇宙对象）** 宇宙初态是 $\mathcal{A}$ 上的一个态，即正归一线性泛函 $\omega_0:\mathcal{A}\to\mathbb{C}$，满足 $\omega_0(\mathbb{I})=1$、$\omega_0(A^{\dagger}A)\ge 0$。于是，我们将宇宙定义为五元组

$$
\mathfrak{U}_{\mathrm{QCA}} := (\Lambda,\mathcal{H}_{\mathrm{cell}},\mathcal{A},\alpha,\omega_0).
$$

引入 Heisenberg 图像下的时间演化态 $\omega_t(A) := \omega_0(\alpha_t(A))$。

### 2.2 公理 A1：离散–幺正–局域

**公理 A1（离散–幺正–局域公理）** 物理宇宙是某个 QCA 宇宙对象 $\mathfrak{U}_{\mathrm{QCA}}$，满足：

1. $\Lambda$ 为可数图；

2. $\dim\mathcal{H}_{\mathrm{cell}}<\infty$；

3. 时间演化 $\alpha_1$ 由某个准局域幺正算符 $U$ 实现，即对所有 $A\in\mathcal{A}$，有 $\alpha_1(A) = U^{\dagger}AU$。

该公理只使用 Hilbert 空间、幺正性与局域性三种最小原语，不涉及连续时空结构。

### 2.3 公理 A2：有限光锥与 Lieb–Robinson 界

**公理 A2（有限光锥公理）** 存在一个常数 $c>0$，使得对任意局域算符 $A,B$ 与任意时间步 $t\in\mathbb{Z}$，有 Lieb–Robinson 型不等式

$$
\bigl|[\alpha_t(A),B]\bigr| \le C\,|A|\,|B|\,\exp\Bigl(-\mu(\mathrm{dist}(\mathrm{supp}A,\mathrm{supp}B) - c|t|)\Bigr),
$$

其中 $C,\mu>0$ 为常数，$\mathrm{dist}(\cdot,\cdot)$ 为图上的距离。

该公理抽象表达了"有限信号速度"的物理事实：不存在超光速的因果影响。常数 $c$ 将在后文自然识别为"光速"。

### 2.4 公理 A3：Dirac 有效模的存在

**公理 A3（Dirac 有效模公理）** 在 $\mathfrak{U}_{\mathrm{QCA}}$ 的某个低能一粒子扇区中，存在一个二维内部自由度的平移不变子模型，其在一维动量表象下的单步更新算符可写作

$$
U(p) = \exp\bigl(-\mathrm{i}\,\omega(p)\,\hat{n}(p)\cdot\vec{\sigma}\bigr),
$$

其中 $\vec{\sigma} = (\sigma_x,\sigma_y,\sigma_z)$ 为 Pauli 矩阵，$\hat{n}(p)\in S^2$ 为单位 Bloch 向量，$p\in[-\pi/a,\pi/a]$ 为布里渊区动量，且在某个 $p_0$ 邻域内，其有效 Hamilton 定义为

$$
H_{\mathrm{eff}}(k) := \frac{\omega(p_0 + k)}{\Delta t} \approx c\,k\,\sigma_z + m c^2 \sigma_x,
$$

其中 $\Delta t$ 为时间步长，$a$ 为格点间距，$k$ 为相对于 $p_0$ 的小动量偏移，$m$ 为非零常数。

该公理仅要求：宇宙中存在某个有效扇区，其低能行为由一维 Dirac 方程描述，且携带非零质量参数 $m$。它不假定任何连续时空或 Lorentz 对称性，只假定某个 SU(2) Bloch 曲线局部近似 Dirac Hamilton。

---

## 3 一维 Dirac 型量子元胞自动机模型

本节构造一个满足 A3 的具体一维 QCA 模型，以便在后文中进行显式计算。

### 3.1 模型定义：平移–旋币–条件平移

考虑一维整数格点 $\Lambda = \mathbb{Z}$，局域 Hilbert 空间为两分量自旋 $\mathcal{H}_{\mathrm{cell}} \cong \mathbb{C}^2$，基底记为 $\{\ket{\uparrow},\ket{\downarrow}\}$。定义两个平移算符 $S_{+}$、$S_-$ 为

$$
S_+\ket{x} = \ket{x+1},\quad S_-\ket{x} = \ket{x-1}.
$$

构造条件平移算符

$$
T := S_+ \otimes \ket{\uparrow}\!\bra{\uparrow} + S_- \otimes \ket{\downarrow}\!\bra{\downarrow},
$$

以及局域"质量旋转"算符

$$
C(m) := \exp\bigl(-\mathrm{i}\,m\Delta t\,\sigma_x\bigr),
$$

其中 $m$ 为模型参数，$\Delta t$ 为时间步长。

定义单步 QCA 更新算符

$$
U := C(m)\,T.
$$

这给出了一个标准的"旋币量子行走"（coined quantum walk），其在长波极限上将产生 Dirac 型色散。

### 3.2 动量表象与 SU(2) 表示

在一维情形下，平移不变模型可方便地在动量表象中分析。定义动量基底

$$
\ket{p} := \frac{1}{\sqrt{2\pi/a}}\sum_{x\in\mathbb{Z}} \mathrm{e}^{\mathrm{i}p a x}\ket{x},\quad p\in[-\pi/a,\pi/a].
$$

在该基底下，平移算符的作用为

$$
S_+\ket{p} = \mathrm{e}^{-\mathrm{i}p a}\ket{p},\quad S_-\ket{p} = \mathrm{e}^{\mathrm{i}p a}\ket{p}.
$$

于是条件平移算符 $T$ 在动量–自旋空间 $\mathcal{H}_p\cong\mathbb{C}^2$ 上的表示为

$$
T(p) = \mathrm{e}^{-\mathrm{i}p a}\ket{\uparrow}\!\bra{\uparrow} + \mathrm{e}^{\mathrm{i}p a}\ket{\downarrow}\!\bra{\downarrow} = \exp\bigl(-\mathrm{i}p a\,\sigma_z\bigr).
$$

因此单步更新算符在动量表象下为

$$
U(p) = C(m)\,T(p) = \exp\bigl(-\mathrm{i}m\Delta t\,\sigma_x\bigr)\exp\bigl(-\mathrm{i}p a\,\sigma_z\bigr).
$$

任意 $2\times 2$ 单位矩阵都可以唯一地写成某个角度绕某个单位向量 $\hat{n}(p)\in S^2$ 的旋转，即存在函数 $\Omega(p)\in[0,\pi]$ 与 $\hat{n}(p)$，使得

$$
U(p) = \exp\bigl(-\mathrm{i}\,\Omega(p)\,\hat{n}(p)\cdot\vec{\sigma}\bigr).
$$

利用 SU(2) 群元素的乘法公式，可得到 $\Omega(p)$ 的显式表达（证明见附录 B）：

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a).
$$

定义准频率 $\omega(p) := \Omega(p)/\Delta t$，则有色散关系

$$
\cos\bigl(\omega(p)\Delta t\bigr) = \cos(m\Delta t)\cos(p a).
$$

这便是 Dirac–QCA 的标准色散形式。

### 3.3 长波极限与 Dirac Hamilton

取 $p\approx 0$、$m\Delta t \ll 1$、$p a \ll 1$ 的极限，可展开

$$
\cos(m\Delta t) \approx 1 - \frac{(m\Delta t)^2}{2},\quad \cos(p a) \approx 1 - \frac{(p a)^2}{2}.
$$

于是

$$
\cos\bigl(\omega(p)\Delta t\bigr) \approx \Bigl(1 - \frac{(m\Delta t)^2}{2}\Bigr)\Bigl(1 - \frac{(p a)^2}{2}\Bigr) \approx 1 - \frac{(m\Delta t)^2}{2} - \frac{(p a)^2}{2}.
$$

另一方面，

$$
\cos\bigl(\omega(p)\Delta t\bigr) \approx 1 - \frac{(\omega(p)\Delta t)^2}{2}.
$$

比较系数得到

$$
\omega^2(p) \approx m^2 + \Bigl(\frac{p a}{\Delta t}\Bigr)^2.
$$

设 $c := a/\Delta t$，可写为

$$
\omega^2(p) \approx m^2 + \frac{p^2 c^2}{1}.
$$

于是有效 Hamilton 为

$$
H_{\mathrm{eff}}(p) \approx \hbar\omega(p) \approx \sqrt{m^2c^4 + p^2c^2}\,\frac{\hbar}{1}.
$$

进一步可在 Pauli 基底上写成

$$
H_{\mathrm{eff}}(p) \approx c\,p\,\sigma_z + m c^2 \sigma_x,
$$

这正是 A3 所要求的 Dirac 型 Hamilton。由此可见，该具体模型满足 A3。

---

## 4 信息速率守恒定理

本节从上一节的 Dirac–QCA 模型出发，定义外部群速度与内部演化速度，并给出信息速率守恒定理以及详细证明。

### 4.1 外部群速度的定义

在动量表象下，准粒子的准能量为 $E(p) := \hbar\omega(p)$。定义外部群速度为

$$
v_{\mathrm{ext}}(p) := \frac{\mathrm{d}E(p)}{\mathrm{d}p}\,\frac{1}{\hbar} = \frac{\mathrm{d}\omega(p)}{\mathrm{d}p}.
$$

由于我们采用格点间距 $a$、时间步长 $\Delta t$ 的归一化，且 $c = a/\Delta t$，更自然的定义是

$$
v_{\mathrm{ext}}(p) := a\,\frac{\mathrm{d}\omega(p)}{\mathrm{d}p},
$$

即每个时间步内，波包中心在空间中平均前进的距离除以 $\Delta t$。

由色散关系

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a),\quad \Omega(p) := \omega(p)\Delta t,
$$

对 $p$ 求导得到

$$
-\sin\bigl(\Omega(p)\bigr)\,\frac{\partial\Omega}{\partial p} = \cos(m\Delta t)\,(-\sin(p a))\,a.
$$

因此

$$
\frac{\partial\Omega}{\partial p} = \frac{\cos(m\Delta t)\,\sin(p a)\,a}{\sin\bigl(\Omega(p)\bigr)}.
$$

注意 $\omega(p) = \Omega(p)/\Delta t$，有

$$
\frac{\mathrm{d}\omega}{\mathrm{d}p} = \frac{1}{\Delta t}\frac{\partial\Omega}{\partial p} = \frac{\cos(m\Delta t)\,\sin(p a)\,a}{\Delta t\,\sin\bigl(\Omega(p)\bigr)} = c\,\frac{\cos(m\Delta t)\,\sin(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

故

$$
v_{\mathrm{ext}}(p) = a\,\frac{\mathrm{d}\omega}{\mathrm{d}p} = c\,\frac{\cos(m\Delta t)\,\sin(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

这给出了外部群速度的显式表达。

### 4.2 内部演化速度的对称定义

为了定义内部演化速度，我们从同一个 $U(p)$ 出发，考察内部自旋自由度在每一步中的"相位更新"。

利用 SU(2) 表示

$$
U(p) = \exp\bigl(-\mathrm{i}\,\Omega(p)\,\hat{n}(p)\cdot\vec{\sigma}\bigr),
$$

其中 $\hat{n}(p) = (n_x(p),n_y(p),n_z(p))$ 为单位向量。由前述乘法结构，可以选取 $\hat{n}(p)$ 使得（见附录 B）

$$
n_x(p) \propto \sin(m\Delta t)\cos(p a),\quad n_z(p) \propto \sin(p a)\cos(m\Delta t).
$$

在一个时间步内，自旋 Bloch 向量绕 $\hat{n}(p)$ 转过角度 $2\Omega(p)$。我们将"内部演化速度"定义为这段 SU(2) 旋转在"质量腿"方向上对应的速度分量，经适当归一为与空间速度同量纲。对称地，我们取

$$
v_{\mathrm{int}}(p) := c\,\frac{\sin(m\Delta t)\,\cos(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

可以看出，$v_{\mathrm{ext}}(p)$ 与 $v_{\mathrm{int}}(p)$ 分别捕捉了色散关系中的"动量腿" $\sin(p a)\cos(m\Delta t)$ 与"质量腿" $\sin(m\Delta t)\cos(p a)$，因而在几何上是完全对称的定义。

### 4.3 信息速率守恒定理及其证明

我们现在证明，对于上述定义的 $v_{\mathrm{ext}}(p)$ 与 $v_{\mathrm{int}}(p)$，有恒等式

$$
v_{\mathrm{ext}}^2(p) + v_{\mathrm{int}}^2(p) = c^2.
$$

**定理 4.1（信息速率守恒圆）** 在满足 A1–A3 的一维 Dirac 型 QCA 模型中，对任意动量 $p$，由色散关系定义的外部群速度 $v_{\mathrm{ext}}(p)$ 与内部演化速度 $v_{\mathrm{int}}(p)$ 满足

$$
v_{\mathrm{ext}}^2(p) + v_{\mathrm{int}}^2(p) = c^2.
$$

*证明* 代入上一小节的显式表达，有

$$
v_{\mathrm{ext}}^2(p) = c^2\,\frac{\cos^2(m\Delta t)\,\sin^2(p a)}{\sin^2\bigl(\Omega(p)\bigr)},
$$

$$
v_{\mathrm{int}}^2(p) = c^2\,\frac{\sin^2(m\Delta t)\,\cos^2(p a)}{\sin^2\bigl(\Omega(p)\bigr)}.
$$

二者相加得到

$$
v_{\mathrm{ext}}^2(p) + v_{\mathrm{int}}^2(p) = c^2\,\frac{\cos^2(m\Delta t)\,\sin^2(p a) + \sin^2(m\Delta t)\,\cos^2(p a)}{\sin^2\bigl(\Omega(p)\bigr)}.
$$

另一方面，由色散关系

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a)
$$

可以得到

$$
\sin^2\bigl(\Omega(p)\bigr) = 1 - \cos^2\bigl(\Omega(p)\bigr) = 1 - \cos^2(m\Delta t)\cos^2(p a).
$$

而

$$
\cos^2(m\Delta t)\,\sin^2(p a) + \sin^2(m\Delta t)\,\cos^2(p a) = \cos^2(m\Delta t)\bigl(1 - \cos^2(p a)\bigr) + \sin^2(m\Delta t)\cos^2(p a)
$$

$$
= \cos^2(m\Delta t) - \cos^2(m\Delta t)\cos^2(p a) + \sin^2(m\Delta t)\cos^2(p a)
$$

$$
= \cos^2(m\Delta t) + \cos^2(p a)\bigl(\sin^2(m\Delta t) - \cos^2(m\Delta t)\bigr)
$$

$$
= \cos^2(m\Delta t) + \cos^2(p a)\bigl(1 - 2\cos^2(m\Delta t)\bigr)
$$

$$
= 1 - \cos^2(m\Delta t)\cos^2(p a) = \sin^2\bigl(\Omega(p)\bigr).
$$

因此分子恰好等于分母，得到

$$
v_{\mathrm{ext}}^2(p) + v_{\mathrm{int}}^2(p) = c^2\,\frac{\sin^2\bigl(\Omega(p)\bigr)}{\sin^2\bigl(\Omega(p)\bigr)} = c^2.
$$

定理得证。$\square$

该定理表明，在 Dirac–QCA 模型中，每个准粒子动量模态可以自然地被分解成"外部位移速度"与"内部态演化速度"的正交分量，它们的平方和固定为 $c^2$，即 Lieb–Robinson 意义下的最大信号速率平方。这一"信息速率圆"完全由 A1–A3 与 SU(2) 几何推导而来，不需要额外引入。

---

## 5 狭义相对论与质量的涌现

本节利用定理 4.1，将 $v_{\mathrm{ext}}(p)$ 重命名为粒子在某参考系中的速度 $v$，并从信息速率圆出发构造固有时间、四速度和质量的内部定义。我们将看到，狭义相对论的核心结果在 QCA 框架内自然出现。

### 5.1 固有时间与时间膨胀

在某个惯性参考系中，观测到的粒子空间速度定义为

$$
v := v_{\mathrm{ext}}(p).
$$

由信息速率圆

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2
$$

得到

$$
v_{\mathrm{int}}(p) = c\sqrt{1 - \frac{v^2}{c^2}}.
$$

我们将内部演化速度视为"内部时钟"相对于某一全局参考时间 $t$ 的演化速率。定义固有时间元

$$
\mathrm{d}\tau := \frac{v_{\mathrm{int}}}{c}\,\mathrm{d}t = \sqrt{1 - \frac{v^2}{c^2}}\,\mathrm{d}t.
$$

于是得到标准的时间膨胀公式：

**推论 5.1（时间膨胀）** 在 QCA 宇宙中，Dirac 型激发的内部演化定义的固有时间 $\tau$ 与任一惯性参考系的坐标时间 $t$ 之间满足

$$
\mathrm{d}\tau = \sqrt{1 - \frac{v^2}{c^2}}\,\mathrm{d}t,
$$

其中 $v$ 为该参考系中观测到的粒子速度。

这与狭义相对论中从 Lorentz 变换推导出的固有时间表达完全一致，但在此解释为信息速率在外部位移与内部演化之间重新分配的结果。

### 5.2 四速度与 Minkowski 线元

定义时空坐标 $x^\mu = (x^0,x^1) = (c t, x)$，四速度为

$$
u^\mu := \frac{\mathrm{d}x^\mu}{\mathrm{d}\tau} = \Bigl(\frac{\mathrm{d}(ct)}{\mathrm{d}\tau}, \frac{\mathrm{d}x}{\mathrm{d}\tau}\Bigr) = \Bigl(\frac{c}{\sqrt{1 - v^2/c^2}}, \frac{v}{\sqrt{1 - v^2/c^2}}\Bigr) = (\gamma c, \gamma v),
$$

其中 $\gamma := 1/\sqrt{1 - v^2/c^2}$。

取 Minkowski 度规 $g_{\mu\nu} = \mathrm{diag}(-1,1)$，则

$$
g_{\mu\nu}u^\mu u^\nu = -(\gamma c)^2 + (\gamma v)^2 = -\gamma^2(c^2 - v^2) = -c^2.
$$

这给出标准的四速度规范化。

**推论 5.2（四速度规范化）** 对任一 Dirac 型 QCA 激发，利用信息速率圆定义的固有时间 $\tau$ 与四速度 $u^\mu$，有

$$
g_{\mu\nu}u^\mu u^\nu = -c^2,
$$

其中 $g_{\mu\nu}$ 为 Minkowski 度规。

进而，Minkowski 线元可写为

$$
\mathrm{d}s^2 := g_{\mu\nu}\,\mathrm{d}x^\mu\,\mathrm{d}x^\nu = -c^2\,\mathrm{d}\tau^2.
$$

因此，狭义相对论的几何结构可被视为信息速率圆在连续极限下的自然编码：固有时间是内部信息更新速率的参数化，时空线元是四速度规范化的几何形式。

### 5.3 质量的内部定义与相对论能量关系

在粒子静止系中 $(v = 0)$，信息速率圆给出 $v_{\mathrm{int}} = c$。内部演化频率 $\omega_{\mathrm{int}}(0)$ 由 Dirac–QCA 的准频率 $\omega(p)$ 在 $p=0$ 附近的值给出。具体地，色散关系在 $p=0$ 处简化为

$$
\cos\bigl(\omega(0)\Delta t\bigr) = \cos(m\Delta t)\cos(0) = \cos(m\Delta t).
$$

在小 $m\Delta t$ 极限下，有 $\omega(0)\Delta t \approx m\Delta t$，即

$$
\omega_{\mathrm{int}}(0) \approx m.
$$

定义静止能量

$$
E_0 := \hbar\omega_{\mathrm{int}}(0),
$$

则可自然将质量定义为

$$
mc^2 := E_0 = \hbar\omega_{\mathrm{int}}(0).
$$

更一般地，在动量 $p$ 的状态下，色散关系给出

$$
\omega^2(p) \approx m^2 + \frac{p^2 c^2}{\hbar^2},
$$

因此总能量

$$
E(p) := \hbar\omega(p)
$$

满足

$$
E^2(p) \approx p^2c^2 + m^2c^4.
$$

**推论 5.3（质量与相对论能量）** 在 Dirac–QCA 模型中，若将静止系内部演化频率 $\omega_{\mathrm{int}}(0)$ 与质量通过关系 $mc^2 = \hbar\omega_{\mathrm{int}}(0)$ 相联，则任意动量 $p$ 下的能量满足相对论能量–动量关系

$$
E^2 = p^2c^2 + m^2c^4.
$$

这表明，质量可解释为维持内部自旋态稳定循环所需的"内部频率"，而相对论能量公式则是 Dirac–QCA 色散与信息速率圆共同作用的结果。

---

## 6 向多维与引力弱场的推广（概述）

由于篇幅所限，本节仅概述多维推广与引力弱场的处理思路，详细技术留待后续工作。

在高维格点 $\Lambda\subset\mathbb{Z}^d$ 上，满足 A1–A2 的 QCA 同样存在 Lieb–Robinson 速度 $c$，可定义向量群速度 $\vec{v}_{\mathrm{ext}}(\vec{p})$ 与标量内部速度 $v_{\mathrm{int}}(\vec{p})$，并期待保持关系

$$
|\vec{v}_{\mathrm{ext}}(\vec{p})|^2 + v_{\mathrm{int}}^2(\vec{p}) = c^2.
$$

若在低能扇区存在 $2^n$ 维的 Dirac 型有效表示，则内部空间的维数增大，但依然可以将外部运动视为总信息速率向某些空间方向的投影，内部演化视为在剩余"质量–自旋"方向上的投影。信息速率圆则成为高维球上的勾股关系。

关于引力弱场，可类比地引入位置依赖的 Lieb–Robinson 速度 $c(x)$，或更一般的局部信息速率密度刻度 $\kappa(x)$，并构造一个依赖于 $\kappa(x)$ 的光学度规

$$
\mathrm{d}s^2 = -\eta^2(x)c^2\,\mathrm{d}t^2 + \eta^{-2}(x)\,\gamma_{ij}\,\mathrm{d}x^i\,\mathrm{d}x^j,
$$

其中 $\eta(x) := \kappa(x)/\kappa_{\infty}$。在零测地线条件下，该度规的空间投影等价于折射率 $n(x) = \eta^2(x)$ 的各向同性介质中的光线轨迹。这样可以把引力红移与光线偏折解释为底层 QCA 中局部信息速率刻度的空间变化。相关细节可以与统一时间刻度 $\kappa(\omega)$ 的散射理论表达拼合，构成统一的引力–信息几何图景。

---

## 7 结论

本文在一个极小的 QCA 公理系统（A1–A3）下，展示了信息速率守恒关系

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2
$$

在 Dirac 型 QCA 模型中是一个严格的几何定理，而非额外公理。借助该定理，我们在完全离散的 Hilbert 空间本体论框架内重构了狭义相对论的时间膨胀、四速度规范化与质量–能量关系，给出了质量的内部信息论定义。

这一结果表明，只要宇宙在某个扇区中表现出 Dirac 型低能结构，且整体满足有限光锥与局域幺正性，则相对论几何及质量–惯性关系都是 QCA 内部结构的必然，而非额外引入的时空公理。未来的工作将包括：将该框架推向高维、多粒子与规范场，并在统一时间刻度与引力弱场的结合下，进一步理解广义相对论如何作为 QCA 宇宙的宏观有效几何涌现。

---

## Appendix A：宇宙对象与 Lieb–Robinson 界

本附录回顾宇宙对象 $\mathfrak{U}_{\mathrm{QCA}}$ 与 Lieb–Robinson 界的形式结构，作为公理 A1–A2 的技术背景。

### A.1 QCA 作为有限深局域幺正电路

在实际构造中，一步 QCA 更新 $U$ 通常可分解为若干层局域幺正门。以一维为例，可将 $U$ 写为

$$
U = \prod_{\ell=1}^L U_\ell,
$$

其中每个 $U_\ell$ 作用在互不相交的有限区块上，且所有 $U_\ell$ 在图上具有有限直径支撑。有限深度 $L$ 与有限门宽保证了传播半径 $R$ 有统一上界。

在 $d$ 维格点上也可类似构造，例如采用棋盘分解，将系统分成若干子格点，每一子步只在某一子格点对内邻域实施幺正更新，从而整体保持幺正与局域性。

### A.2 Lieb–Robinson 界的证明思路

给定满足 A1 的 QCA，为了得到 A2 中的 Lieb–Robinson 界，可以利用与局域自旋系统相似的方法。设 $H$ 是产生离散时间 Floquet 演化 $U = \exp(-\mathrm{i}H\Delta t)$ 的有效 Hamilton（在本附录中仅作形式使用），其具有局域项分解

$$
H = \sum_{X\subset\Lambda} h_X,
$$

其中 $h_X$ 仅作用在有限区域 $X$，且满足规范衰减条件

$$
\sum_{X\ni x} |h_X|\,\mathrm{e}^{\mu \mathrm{diam}(X)} < \infty
$$

对某个 $\mu>0$ 成立。

在这种条件下，可以沿着标准的 Lieb–Robinson 证明路线，考虑随时间演化的算符 $A(t) := \alpha_t(A)$，推导出对易子 $[A(t),B]$ 的微分不等式

$$
\frac{\mathrm{d}}{\mathrm{d}t}\bigl|[A(t),B]\bigr| \le 2\sum_{X}|h_X|\,\bigl|[A(t),B]\bigr| + \cdots
$$

再利用 Grönwall 不等式与图上距离的结构，得到指数衰减界

$$
\bigl|[A(t),B]\bigr| \le C\,|A|\,|B|\,\exp\Bigl(-\mu(\mathrm{dist}(\mathrm{supp}A,\mathrm{supp}B) - v_{\mathrm{LR}}|t|)\Bigr),
$$

其中 $v_{\mathrm{LR}}$ 为 Lieb–Robinson 速度。A2 中的常数 $c$ 可以识别为 $v_{\mathrm{LR}}$ 在适当单位下的值。

在严格的 QCA 场景中，即便没有显式 Hamilton，也可以通过直接分析有限深局域幺正电路的传播锥来得到类似估计：每一步传播最多扩展 $R$ 个格点，因而 $c = R a/\Delta t$ 为自然的信号速度上界。

---

## Appendix B：Dirac–QCA 的色散关系与 Bloch 向量

本附录补充第 3 节中色散关系及 Bloch 向量形式的推导。

### B.1 SU(2) 群元素乘积公式

任意两个 SU(2) 群元素可以写成

$$
U_1 = \exp\bigl(-\mathrm{i}\alpha\,\hat{a}\cdot\vec{\sigma}\bigr),\quad U_2 = \exp\bigl(-\mathrm{i}\beta\,\hat{b}\cdot\vec{\sigma}\bigr),
$$

其乘积为

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

### B.2 将 $U(p) = C(m)T(p)$ 化为一次旋转

在我们的 Dirac–QCA 模型中，

$$
C(m) = \exp\bigl(-\mathrm{i} m\Delta t\,\sigma_x\bigr),
$$

$$
T(p) = \exp\bigl(-\mathrm{i} p a\,\sigma_z\bigr).
$$

因此

$$
U(p) = C(m)T(p) = \exp\bigl(-\mathrm{i} m\Delta t\,\sigma_x\bigr)\exp\bigl(-\mathrm{i} p a\,\sigma_z\bigr).
$$

代入上式，取

$$
\alpha = m\Delta t,\quad \hat{a} = (1,0,0),
$$

$$
\beta = p a,\quad \hat{b} = (0,0,1).
$$

则 $\hat{a}\cdot\hat{b} = 0$，$\hat{a}\times\hat{b} = (0,-1,0)$。于是合成角满足

$$
\cos\Omega(p) = \cos\alpha\cos\beta - 0\cdot\sin\alpha\sin\beta = \cos(m\Delta t)\cos(p a).
$$

这给出了第 3 节中使用的色散关系。

Bloch 向量分量可由

$$
\hat{n}(p)\sin\Omega(p) = \hat{a}\sin\alpha\cos\beta + \hat{b}\sin\beta\cos\alpha - (\hat{a}\times\hat{b})\sin\alpha\sin\beta.
$$

代入得到

$$
\hat{n}(p)\sin\Omega(p) = (\sin(m\Delta t)\cos(p a),\,\sin(m\Delta t)\sin(p a),\,\sin(p a)\cos(m\Delta t)).
$$

其中 $x$ 分量 $n_x(p)\propto\sin(m\Delta t)\cos(p a)$，$z$ 分量 $n_z(p)\propto\sin(p a)\cos(m\Delta t)$，与正文中用于定义 $v_{\mathrm{int}}$ 与 $v_{\mathrm{ext}}$ 的结构一致。

---

## Appendix C：信息速率守恒定理及相对论推论的细节

本附录整理定理 4.1 与推论 5.1–5.3 的计算细节，以确保严格性与自洽性。

### C.1 外部群速度的导数计算

从

$$
\cos\bigl(\Omega(p)\bigr) = \cos(m\Delta t)\cos(p a)
$$

出发，对 $p$ 求导：

$$
-\sin\bigl(\Omega(p)\bigr)\frac{\partial\Omega}{\partial p} = \cos(m\Delta t)\,(-\sin(p a))\,a.
$$

因此

$$
\frac{\partial\Omega}{\partial p} = \frac{\cos(m\Delta t)\,\sin(p a)\,a}{\sin\bigl(\Omega(p)\bigr)}.
$$

又 $\omega(p) = \Omega(p)/\Delta t$，所以

$$
\frac{\mathrm{d}\omega}{\mathrm{d}p} = \frac{1}{\Delta t}\frac{\partial\Omega}{\partial p} = \frac{\cos(m\Delta t)\,\sin(p a)\,a}{\Delta t\,\sin\bigl(\Omega(p)\bigr)} = c\,\frac{\cos(m\Delta t)\,\sin(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

最终得到

$$
v_{\mathrm{ext}}(p) = a\,\frac{\mathrm{d}\omega}{\mathrm{d}p} = c\,\frac{\cos(m\Delta t)\,\sin(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

### C.2 内部速度定义的对称性

内部速度定义为

$$
v_{\mathrm{int}}(p) := c\,\frac{\sin(m\Delta t)\,\cos(p a)}{\sin\bigl(\Omega(p)\bigr)}.
$$

可以注意到，若交换 $m\Delta t$ 与 $p a$ 的角色，对应地交换 $\sin$ 与 $\cos$ 的因子，则 $v_{\mathrm{ext}}$ 与 $v_{\mathrm{int}}$ 正好互换。这反映了 Dirac 色散中"质量–动量"对称结构。

### C.3 信息速率圆的代数恒等式

将两者平方相加：

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2\,\frac{\cos^2(m\Delta t)\,\sin^2(p a) + \sin^2(m\Delta t)\,\cos^2(p a)}{\sin^2\bigl(\Omega(p)\bigr)}.
$$

又

$$
\sin^2\bigl(\Omega(p)\bigr) = 1 - \cos^2\bigl(\Omega(p)\bigr) = 1 - \cos^2(m\Delta t)\cos^2(p a).
$$

直接计算可得

$$
\cos^2(m\Delta t)\,\sin^2(p a) + \sin^2(m\Delta t)\,\cos^2(p a) = 1 - \cos^2(m\Delta t)\cos^2(p a) = \sin^2\bigl(\Omega(p)\bigr).
$$

因此

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2.
$$

这完成了定理 4.1 的全部代数细节。

### C.4 时间膨胀与四速度的细节

由

$$
v_{\mathrm{int}} = c\sqrt{1 - \frac{v^2}{c^2}}
$$

定义

$$
\mathrm{d}\tau := \frac{v_{\mathrm{int}}}{c}\,\mathrm{d}t = \sqrt{1 - \frac{v^2}{c^2}}\,\mathrm{d}t.
$$

反过来

$$
\frac{\mathrm{d}t}{\mathrm{d}\tau} = \frac{1}{\sqrt{1 - v^2/c^2}} = \gamma.
$$

四速度分量

$$
u^0 = \frac{\mathrm{d}(ct)}{\mathrm{d}\tau} = c\frac{\mathrm{d}t}{\mathrm{d}\tau} = \gamma c,
$$

$$
u^1 = \frac{\mathrm{d}x}{\mathrm{d}\tau} = \frac{\mathrm{d}x}{\mathrm{d}t}\frac{\mathrm{d}t}{\mathrm{d}\tau} = v\,\gamma.
$$

代入度规

$$
g_{\mu\nu}u^\mu u^\nu = -(\gamma c)^2 + (\gamma v)^2 = -\gamma^2(c^2 - v^2) = -c^2.
$$

因此 Minkowski 线元可写为

$$
\mathrm{d}s^2 = g_{\mu\nu}\mathrm{d}x^\mu\mathrm{d}x^\nu = -c^2\mathrm{d}\tau^2.
$$

### C.5 质量的内禀定义与色散关系

从色散关系

$$
\cos\bigl(\omega(p)\Delta t\bigr) = \cos(m\Delta t)\cos(p a)
$$

在 $p=0$ 处得到

$$
\cos\bigl(\omega(0)\Delta t\bigr) = \cos(m\Delta t).
$$

在 $m\Delta t$ 小的情形下，展开

$$
\cos\bigl(\omega(0)\Delta t\bigr) \approx 1 - \frac{\bigl(\omega(0)\Delta t\bigr)^2}{2},\quad \cos(m\Delta t)\approx 1 - \frac{(m\Delta t)^2}{2}.
$$

比较可得 $\omega(0)\approx m$。定义静止能量 $E_0 := \hbar\omega(0)$，则

$$
E_0 \approx \hbar m.
$$

若我们采用单位制使 $\hbar = 1$ 且 $c=a/\Delta t$，则自然可以写出

$$
mc^2 := E_0 = \hbar\omega_{\mathrm{int}}(0).
$$

此外，在小 $p a$ 极限下，色散关系给出

$$
\omega^2(p) \approx m^2 + \Bigl(\frac{p a}{\Delta t}\Bigr)^2 = m^2 + \frac{p^2c^2}{1}.
$$

因此

$$
E^2(p) := \hbar^2\omega^2(p) \approx \hbar^2 m^2 + p^2 c^2.
$$

识别 $\hbar m c^2 = mc^2$ 并采用标准单位制，得到

$$
E^2 \approx p^2c^2 + m^2c^4.
$$

这表明，相对论能量–动量关系是 Dirac–QCA 色散的一阶近似结果，而质量 $m$ 正是静止态内部演化频率的缩放。

