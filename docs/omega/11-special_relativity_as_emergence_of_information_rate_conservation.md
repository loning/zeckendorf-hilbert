# 狭义相对论作为信息速率守恒的涌现：内部时间流逝与外部位移的正交分解

---

## Abstract

经典狭义相对论以光速不变与相对性原理为公理，采用闵可夫斯基时空作为先验几何舞台。在这一传统图像中，度规结构与洛伦兹因子被视为几何事实，其与信息流、计算能力之间的关系并不显式。另一方面，量子信息与凝聚态理论表明，物理系统普遍受限于有限的信息传播速度与有限的量子演化速度：局域量子格点系统满足 Lieb–Robinson 有限群速度界，从而定义出有效的"信号光速"；量子速度极限定理则给出纯态在射影希尔伯特空间中的最大演化速度，其由能量不确定度决定；信息物理极限分析进一步指出，每个物理器件存在由能量与自由度数量共同决定的最大计算速率。

本文在离散量子元胞自动机（quantum cellular automaton, QCA）本体论的框架下，提出一个以信息速率为核心的狭义相对论涌现方案。对任一局域激发，定义两类信息更新速率：其一是包络中心在格点上的外部群速度 $v_{\mathrm{ext}}$，刻画空间坐标的变化；其二是在内部希尔伯特空间射影空间中的 Fubini–Study 速度，经适当标度后记为内部速度 $v_{\mathrm{int}}$，刻画内部量子态演化的速率。本文提出**信息速率守恒公理**：存在普适常数 $c$，使得对任一时刻

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2},
$$

并以内部速度定义固有时间流逝率 $\mathrm d\tau / \mathrm dt = v_{\mathrm{int}}/c$。在此基础上，证明如下主结果：

(1) 由速率守恒与固有时间定义，可直接推出 $\mathrm d\tau = \mathrm dt/\gamma$，其中 $\gamma = (1 - v_{\mathrm{ext}}^{2}/c^{2})^{-1/2}$，即标准洛伦兹时间膨胀因子；

(2) 将信息速率圆重写成关于 $\mathrm dt$、$\mathrm d\mathbf x$、$\mathrm d\tau$ 的关系，可得到不变量线元 $\mathrm ds^{2} = -c^{2}\mathrm d\tau^{2} = -c^{2}\mathrm dt^{2} + \mathrm d\mathbf x^{2}$，从而恢复闵可夫斯基度规结构；

(3) 由固有时间与速度关系，构造四速度与四动量，得到标准的 $E = \gamma m c^{2}$ 与 $\mathbf p = \gamma m \mathbf v_{\mathrm{ext}}$ 以及不变关系 $E^{2} = p^{2}c^{2} + m^{2}c^{4}$；

(4) 在 Dirac–QCA 的一维模型中，内部 Zitterbewegung 型振荡频率 $\omega_{0}$ 与有效质量 $m$ 满足 $m c^{2} = \hbar \omega_{0}$，从而可将质量解释为维持粒子内部频率所需的最小信息速率，即一种信息论意义上的"阻抗"。

在该视角下，固有时间不再是预设的外在参数，而是内部量子状态在射影希尔伯特空间中行进的距离；有质量粒子的"不能被加速至光速"源于：当 $v_{\mathrm{ext}} \to c$ 时，内部速率 $v_{\mathrm{int}} \to 0$，维持同一内部结构所需能量趋于无穷。本文讨论了该框架与 QCA–相对论涌现文献、量子速度极限理论及 Lieb–Robinson 有限群速度之间的关系，分析了全局更新时间参数与多体纠缠等方面的局限，并提出若干基于 QCA 量子模拟及极端环境信息系统的可行工程检验思路。

---

## Keywords

信息速率守恒；量子元胞自动机；固有时间；洛伦兹因子；量子速度极限；Fubini–Study 度规；四动量

---

## Introduction & Historical Context

爱因斯坦在 1905 年提出狭义相对论，以下列两条公理为起点：

(1) 相对性原理：所有惯性系中的物理定律形式相同；

(2) 光速不变原理：真空中光传播速度 $c$ 在所有惯性系中相同。

闵可夫斯基随后将狭义相对论几何化，构造带 $(-+++)$ 签名的四维伪欧氏时空，并将自由粒子的运动视为时空中的测地线。洛伦兹变换在该时空中等价于保持线元 $\mathrm ds^{2} = -c^{2}\mathrm dt^{2} + \mathrm d\mathbf x^{2}$ 不变的线性变换群。该几何正式而成功，但其"为什么如此"的本体论问题长期悬而未决：为什么极限速度存在且为常数 $c$？为什么度规必然是闵可夫斯基型而非其他形式？

另一方面，量子信息与量子统计力学的发展揭示了一系列与速度和时间相关的普适约束。Lieb 与 Robinson 在研究量子自旋系统时证明了信息传播存在有限群速度界，局域算符的影响在空间中以有限"光锥"方式扩散，定义出所谓 Lieb–Robinson 速度。这一结果在非相对论晶格系统中给出了类光速上界，体现了局域性与有限信号速度之间的深刻联系。

在量子动力学中，Mandelstam–Tamm 与 Margolus–Levitin 等定理给出了量子速度极限：从一纯态演化到与之正交的态所需的最短时间由能量不确定度与平均能量下界所限定。Aharonov 与 Anandan 则在射影希尔伯特空间上引入 Fubini–Study 度规，将时间–能量不等式重述为量子态曲线长度与能量涨落之间的关系。

在信息物理极限的研究中，Lloyd 分析了由 $c$、$\hbar$ 与 $G$ 所决定的极限计算速率，指出任何物理系统可实现的计算步数与信息存储容量均由能量与自由度受限。这些工作共同表明：时间与速度不仅是几何量，更是信息传播与处理能力的反映。

量子元胞自动机为"宇宙即量子计算"的构想提供了离散且严格因果的动力学框架。局域幺正更新在格点上作用，天然具有有限传播速度；在适当连续极限下，一系列工作证明了 Dirac、Weyl 乃至 Maxwell 方程可由 QCA 的长波极限涌现。这些结果说明：相对论型场论可被视为底层离散信息处理过程的有效描述。

在此背景下，本文试图回答一个更为基础的问题：如果把 $c$ 解释为"单个局域激发每单位坐标时间所能使用的总信息更新速率"，狭义相对论的全部动力学是否可以从"信息速率守恒"这一约束出发涌现？具体而言，本文区分两种信息更新：

(1) 外部位移：激发在格点上的传播，以群速度 $v_{\mathrm{ext}}$ 表征；

(2) 内部演化：激发内部希尔伯特空间态在射影空间中的运动，以 Fubini–Study 速度经标度得到 $v_{\mathrm{int}}$。

本文提出的核心公理是：对任一激发，总信息速率向量 $(v_{\mathrm{ext}}, v_{\mathrm{int}})$ 的模长在普朗克尺度上受限于常数 $c$，并视为该激发可使用的信息速率预算。外部与内部演化是对同一预算的正交分配。接下来将证明，狭义相对论的时间膨胀、闵可夫斯基度规以及标准的能动量关系均可视为这一圆形预算约束的几何重写。

---

## Model & Assumptions

本节给出 QCA 背景、外部与内部速度的严格定义，并形式化信息速率守恒公理与固有时间的定义。

### QCA 背景与因果结构

考虑定义在 $d$ 维正则晶格 $\Lambda \subset \mathbb Z^{d}$ 上的量子元胞自动机。对每一格点 $x \in \Lambda$，关联有限维局域 Hilbert 空间 $\mathcal H_{x}$，全局 Hilbert 空间为

$$
\mathcal H = \bigotimes_{x \in \Lambda} \mathcal H_{x}.
$$

时间以整数步 $n \in \mathbb Z$ 标记，每一步由全局幺正算符 $U$ 实现，$U$ 可分解为有限深度局域幺正门阵列。局域性意味着：存在有限邻域 $N(r)$，使得每一步演化中，任一格点的算符只与其有限邻域上的算符发生耦合。

在此设定下，可定义局域算符 $A_{X}$ 在 $n$ 步演化后的支撑区域，其增长速度由 Lieb–Robinson 界控制：存在常数 $v_{\mathrm{LR}}>0$ 及衰减函数 $F$，使得空间上距 $X$ 足够远的区域 $Y$ 上的算符与 $A_{X}(n)$ 的对易子范数按指数或超多项式衰减。因此，信息在 QCA 中的传播速度存在上界，可在连续极限中识别为有效光速 $c$。

在本文中，将假设已经通过已知构造得到在长波极限下收敛于 Weyl/Dirac 方程的 QCA 演化。由此，外部群速度 $v_{\mathrm{ext}}$ 在有效连续极限中等同于相对论波包的群速度，但底层仍保留离散格点与全局更新步这一结构。

### 局域激发与外部速度

考虑 QCA 的单激发子空间 $\mathcal H_{\mathrm{1p}}$，其由单个粒子在晶格上的位置和内部自由度张成。设 $\ket{\psi_{p}}$ 为具有准动量 $p$ 的单激发本征模态，其有效色散关系为 $\omega(p)$。在此基础上构造窄带波包

$$
\ket{\Psi(t)} = \int \mathrm d p\, f(p - p_{0}) \mathrm e^{-\mathrm i \omega(p) t} \ket{\psi_{p}},
$$

其中 $f$ 为在 $p_{0}$ 附近急剧集中的权重函数。其包络中心位置 $\mathbf x(t)$ 的时间导数给出群速度

$$
v_{\mathrm{ext}}(p_{0}) = \left| \frac{\mathrm d\mathbf x}{\mathrm dt} \right|
= \left| \frac{\partial \omega(p)}{\partial p} \right|_{p = p_{0}}.
$$

由 QCA 的有限信号速度性质，$|v_{\mathrm{ext}}(p)| \le c$ 对所有 $p$ 成立。

在后文中，将把 $v_{\mathrm{ext}}$ 简记为 $v$，其物理含义为：每单位坐标时间内，粒子包络中心在空间上的平均位移速率。

### 内部 Hilbert 空间与 Fubini–Study 速度

每个激发携带有限维内部 Hilbert 空间 $\mathcal H_{\mathrm{int}}$ 中的量子态，用以表示自旋、味、内部振荡模式等。设 $\ket{\psi(t)} \in \mathcal H_{\mathrm{int}}$ 为在坐标时间 $t$ 的内部态，其在有效哈密顿量 $H$ 作用下演化：

$$
\mathrm i \hbar \frac{\mathrm d}{\mathrm dt} \ket{\psi(t)} = H \ket{\psi(t)}.
$$

内部态的物理等价类由射影 Hilbert 空间 $\mathbb{P}(\mathcal H_{\mathrm{int}})$ 表示，即去除整体相位的纯态轨道。射影空间自然配备 Fubini–Study 度规，其无穷小线元为

$$
\mathrm d s_{\mathrm{FS}}^{2}
= 4 \left( \langle \dot{\psi}(t) | \dot{\psi}(t) \rangle
- |\langle \psi(t) | \dot{\psi}(t) \rangle|^{2} \right)\mathrm dt^{2},
$$

对应的瞬时几何速度为

$$
v_{\mathrm{FS}}(t)
= \frac{\mathrm d s_{\mathrm{FS}}}{\mathrm dt}
= \frac{2 \Delta H(t)}{\hbar},
$$

其中 $\Delta H(t) = \sqrt{\langle H^{2} \rangle_{t} - \langle H \rangle_{t}^{2}}$ 为能量不确定度。

这一结果表明，内部态在射影空间中的演化速度由能量涨落控制，量子速度极限定理则给出在该速度下从初态演化到与之正交态的最短时间。

为了把这一几何速度与外部群速度 $v_{\mathrm{ext}}$ 置于同一量纲下，引入内部长度标度 $\ell_{\mathrm{int}}>0$，定义内部速度

$$
v_{\mathrm{int}}(t)
= \ell_{\mathrm{int}} v_{\mathrm{FS}}(t)
= \ell_{\mathrm{int}} \frac{2 \Delta H(t)}{\hbar}.
$$

$\ell_{\mathrm{int}}$ 可视为把 Fubini–Study 距离转化为空间"等效长度"的比例因子，其数值通过校准选择：在静止系中取某类"最大活跃"内部态，使其内部速度饱和至 $c$。定量而言，可在固定谱支撑的两能级系统上，选取同时饱和 Mandelstam–Tamm 与 Margolus–Levitin 量子速度极限的叠加态，并要求其在静止系中满足 $v_{\mathrm{int}} = c$，从而确定 $\ell_{\mathrm{int}}$。

在此归一下，对任一内部态有 $0 \le v_{\mathrm{int}} \le c$。

### 信息速率守恒公理

本文提出如下公理作为狭义相对论涌现的起点：

**公理 2.1（信息速率守恒）**

对 QCA 中任一局域激发及任一坐标时间 $t$，其外部群速度 $v_{\mathrm{ext}}(t)$ 与内部 Fubini–Study 速度经标度后的内部速度 $v_{\mathrm{int}}(t)$ 满足

$$
v_{\mathrm{ext}}^{2}(t) + v_{\mathrm{int}}^{2}(t) = c^{2},
$$

其中 $0 \le v_{\mathrm{ext}}(t) \le c$，$0 \le v_{\mathrm{int}}(t) \le c$。

该公理可以物理地理解为：每个激发在单位坐标时间内可用的总信息更新速率被上界 $c$ 限制，外部位移与内部演化只能在这一预算内做正交分配。之所以采用平方和形式，是为了得到与欧氏圆相对应的几何结构，从而引出闵可夫斯基度规的不变形式。

### 固有时间的内部定义

基于上述内部速度定义，固有时间 $\tau$ 定义为内部演化在信息长度意义上的累积量，即

$$
\frac{\mathrm d\tau}{\mathrm dt}
= \frac{v_{\mathrm{int}}(t)}{c}.
$$

当激发处于静止系时，若内部态选择为饱和量子速度极限的极值态，则 $v_{\mathrm{int}} = c$，从而 $\tau = t + \mathrm{const}$。

在一般运动状态下，外部速度增大将压缩内部速度 $v_{\mathrm{int}}$，从而使固有时间流逝变慢。这一定义在后文将被证明恰好重现狭义相对论中固有时间与坐标时间之间的洛伦兹关系。

---

## Main Results (Theorems and alignments)

在上述模型与公理基础上，本文得到以下主要结果。

### Theorem 3.1（洛伦兹时间膨胀的涌现）

设局域激发在某惯性系中的外部速度为 $v_{\mathrm{ext}}(t)$，内部速度为 $v_{\mathrm{int}}(t)$，满足信息速率守恒

$$
v_{\mathrm{ext}}^{2}(t) + v_{\mathrm{int}}^{2}(t) = c^{2},
$$

且固有时间 $\tau$ 定义为 $\mathrm d\tau / \mathrm dt = v_{\mathrm{int}}(t)/c$。则

$$
\frac{\mathrm d\tau}{\mathrm dt}
= \sqrt{1 - \frac{v_{\mathrm{ext}}^{2}(t)}{c^{2}}},
$$

即

$$
\mathrm d\tau = \frac{\mathrm dt}{\gamma(t)},
\quad
\gamma(t)
= \frac{1}{\sqrt{1 - v_{\mathrm{ext}}^{2}(t)/c^{2}}}.
$$

这就是标准狭义相对论中固有时间与坐标时间之间的洛伦兹时间膨胀公式。

### Theorem 3.2（闵可夫斯基线元作为信息速率恒等式）

在同一惯性系中，设激发的空间坐标为 $\mathbf x(t)$，满足

$$
\left| \frac{\mathrm d\mathbf x}{\mathrm dt} \right| = v_{\mathrm{ext}}(t).
$$

定义时空线元

$$
\mathrm ds^{2} = -c^{2}\mathrm dt^{2} + \mathrm d\mathbf x^{2}.
$$

则在信息速率守恒与固有时间定义下，有

$$
\mathrm ds^{2} = -c^{2}\mathrm d\tau^{2}.
$$

因此 $\mathrm ds^{2}$ 仅依赖于固有时间增量，是与具体惯性系无关的不变量，且其形式与闵可夫斯基度规一致。

### Theorem 3.3（四速度与四动量结构）

定义四坐标 $x^{\mu} = (c t, \mathbf x)$，固有时间 $\tau$ 如前，四速度

$$
U^{\mu} = \frac{\mathrm d x^{\mu}}{\mathrm d\tau}.
$$

令 $m>0$ 为激发的静止质量，四动量定义为

$$
P^{\mu} = m U^{\mu}.
$$

则有：

(1) 四速度分量为

$$
U^{0} = c \gamma,
\quad
\mathbf U = \gamma \mathbf v_{\mathrm{ext}},
\quad
\gamma = \frac{1}{\sqrt{1 - v_{\mathrm{ext}}^{2}/c^{2}}},
$$

且满足不变归一化条件

$$
U^{\mu} U_{\mu} = -c^{2}.
$$

(2) 四动量分量为

$$
P^{0} = \frac{E}{c} = m c \gamma,
\quad
\mathbf P = \mathbf p = m \gamma \mathbf v_{\mathrm{ext}},
$$

且满足不变质量壳条件

$$
P^{\mu} P_{\mu} = -m^{2} c^{2},
$$

从而

$$
E^{2} = p^{2}c^{2} + m^{2}c^{4}.
$$

### Theorem 3.4（质量作为内部频率与信息阻抗）

设一静止激发在其静止系中具有内部振荡角频率 $\omega_{0}$，其内部态随固有时间演化为 $\mathrm e^{-\mathrm i \omega_{0} \tau}\ket{\psi_{0}}$。定义静止质量为

$$
m c^{2} = \hbar \omega_{0}.
$$

在一般惯性系中，总能量 $E$ 由内部相位随坐标时间演化 $\mathrm e^{-\mathrm i E t/\hbar}$ 给出。若信息速率守恒与固有时间定义成立，则有：

(1) 总能量满足

$$
E = \gamma m c^{2},
$$

其中 $\gamma$ 为由 $v_{\mathrm{ext}}$ 确定的洛伦兹因子；

(2) 内部速度满足

$$
v_{\mathrm{int}} = \frac{c}{\gamma},
$$

从而能源亦可表示为

$$
E = m c^{2} \frac{c}{v_{\mathrm{int}}}.
$$

当 $v_{\mathrm{ext}} \to c$ 时，$v_{\mathrm{int}} \to 0$，$E \to \infty$。因此，质量可被解释为：在信息速率守恒约束下，为维持粒子内部振荡频率 $\omega_{0}$ 所需的最小信息阻抗，外部速度越高，为保持该内部结构而需投入的总能量越大。

---

## Proofs

本节给出上述定理的证明，技术细节在附录中补充。

### Theorem 3.1 的证明

由信息速率守恒

$$
v_{\mathrm{ext}}^{2}(t) + v_{\mathrm{int}}^{2}(t) = c^{2}
$$

对任一 $t$ 成立，可得

$$
v_{\mathrm{int}}(t)
= \sqrt{c^{2} - v_{\mathrm{ext}}^{2}(t)}.
$$

固有时间定义为

$$
\frac{\mathrm d\tau}{\mathrm dt}
= \frac{v_{\mathrm{int}}(t)}{c},
$$

代入上式得到

$$
\frac{\mathrm d\tau}{\mathrm dt}
= \frac{1}{c} \sqrt{c^{2} - v_{\mathrm{ext}}^{2}(t)}
= \sqrt{1 - \frac{v_{\mathrm{ext}}^{2}(t)}{c^{2}}}.
$$

定义

$$
\gamma(t) = \frac{1}{\sqrt{1 - v_{\mathrm{ext}}^{2}(t)/c^{2}}},
$$

即可写为

$$
\mathrm d\tau = \frac{\mathrm dt}{\gamma(t)},
$$

与狭义相对论中的时间膨胀关系完全一致。证毕。

### Theorem 3.2 的证明

在同一惯性系中，空间线元满足

$$
\mathrm d\mathbf x^{2} = v_{\mathrm{ext}}^{2}(t)\,\mathrm dt^{2}.
$$

由速率守恒，可写为

$$
v_{\mathrm{ext}}^{2}(t) = c^{2} - v_{\mathrm{int}}^{2}(t),
$$

于是时空线元

$$
\mathrm ds^{2}
= -c^{2}\mathrm dt^{2} + \mathrm d\mathbf x^{2}
= -c^{2}\mathrm dt^{2} + \left( c^{2} - v_{\mathrm{int}}^{2}(t) \right)\mathrm dt^{2}
= -v_{\mathrm{int}}^{2}(t)\,\mathrm dt^{2}.
$$

另一方面，固有时间定义给出

$$
\mathrm d\tau^{2}
= \left( \frac{v_{\mathrm{int}}(t)}{c} \right)^{2} \mathrm dt^{2}
\quad \Rightarrow \quad
v_{\mathrm{int}}^{2}(t)\,\mathrm dt^{2}
= c^{2}\mathrm d\tau^{2}.
$$

代回得到

$$
\mathrm ds^{2}
= -c^{2}\mathrm d\tau^{2}.
$$

因此线元只与固有时间相关，是 Lorentz 变换下的不变量，且形式与闵可夫斯基度规一致。证毕。

### Theorem 3.3 的证明

由 Theorem 3.1，

$$
\frac{\mathrm d\tau}{\mathrm dt}
= \sqrt{1 - \frac{v_{\mathrm{ext}}^{2}}{c^{2}}}
\quad \Rightarrow \quad
\frac{\mathrm dt}{\mathrm d\tau} = \gamma,
\quad
\gamma = \frac{1}{\sqrt{1 - v_{\mathrm{ext}}^{2}/c^{2}}}.
$$

四坐标定义为 $x^{\mu} = (c t, \mathbf x)$，四速度为

$$
U^{\mu}
= \frac{\mathrm d x^{\mu}}{\mathrm d\tau}
= \left( \frac{\mathrm d(c t)}{\mathrm d\tau},
\frac{\mathrm d\mathbf x}{\mathrm d\tau} \right)
= \left( c \frac{\mathrm dt}{\mathrm d\tau},
\frac{\mathrm d\mathbf x}{\mathrm dt} \frac{\mathrm dt}{\mathrm d\tau} \right)
= \left( c \gamma, \gamma \mathbf v_{\mathrm{ext}} \right).
$$

其模长

$$
U^{\mu} U_{\mu}
= - (U^{0})^{2} + \mathbf U^{2}
= -c^{2}\gamma^{2} + \gamma^{2} v_{\mathrm{ext}}^{2}
= -c^{2}\gamma^{2} \left( 1 - \frac{v_{\mathrm{ext}}^{2}}{c^{2}} \right)
= -c^{2}.
$$

这给出四速度的洛伦兹不变归一化。

四动量定义为 $P^{\mu} = m U^{\mu}$，于是

$$
P^{0} = m c \gamma,
\quad
\mathbf P = m \gamma \mathbf v_{\mathrm{ext}}.
$$

若将 $E = P^{0} c$、$\mathbf p = \mathbf P$，则

$$
E = \gamma m c^{2},
\quad
\mathbf p = \gamma m \mathbf v_{\mathrm{ext}}.
$$

计算不变量

$$
P^{\mu} P_{\mu}
= - (P^{0})^{2} + \mathbf P^{2}
= -m^{2} c^{2} \gamma^{2} + m^{2} v_{\mathrm{ext}}^{2} \gamma^{2}
= -m^{2} c^{2},
$$

得到

$$
E^{2} = p^{2} c^{2} + m^{2} c^{4}.
$$

证毕。

### Theorem 3.4 的证明

在静止系（$v_{\mathrm{ext}}=0$）中，设内部态随固有时间演化为

$$
\ket{\psi(\tau)} = \mathrm e^{-\mathrm i \omega_{0} \tau} \ket{\psi_{0}},
$$

其中 $\omega_{0}$ 为内部振荡频率。量子力学能量–频率关系给出

$$
E_{0} = \hbar \omega_{0}.
$$

定义静止质量 $m$ 满足

$$
m c^{2} = E_{0} = \hbar \omega_{0}.
$$

在一般惯性系中，坐标时间演化形式为

$$
\ket{\psi(t)} = \mathrm e^{-\mathrm i E t/\hbar} \ket{\psi_{0}'},
$$

其中 $E$ 为该系中测得的总能量。由固有时间与坐标时间关系

$$
\mathrm d\tau = \frac{\mathrm dt}{\gamma}
\quad \Rightarrow \quad
\frac{\mathrm d}{\mathrm d\tau}
= \frac{\mathrm d t}{\mathrm d\tau} \frac{\mathrm d}{\mathrm d t}
= \gamma \frac{\mathrm d}{\mathrm d t},
$$

内部态对固有时间的导数为

$$
\frac{\mathrm d}{\mathrm d\tau} \ket{\psi(\tau)}
= -\mathrm i \frac{E}{\hbar} \gamma \ket{\psi(\tau)}.
$$

将其与静止系情况下

$$
\frac{\mathrm d}{\mathrm d\tau} \ket{\psi(\tau)}
= -\mathrm i \omega_{0} \ket{\psi(\tau)}
$$

对应起来，可得

$$
E \gamma = \hbar \omega_{0}
= m c^{2},
$$

即

$$
E = \frac{m c^{2}}{\gamma}.
$$

注意这里的 $\gamma$ 定义为静止系相对于该惯性系的洛伦兹因子，因此若采用惯例把 $\gamma$ 视作"运动系相对于静止系"的因子，需要反向处理。更直接的做法是利用 Theorem 3.3 已得出的

$$
E = \gamma m c^{2},
$$

并结合内部速度表达式。

由信息速率守恒和 Theorem 3.1，有

$$
v_{\mathrm{int}}
= c \sqrt{1 - \frac{v_{\mathrm{ext}}^{2}}{c^{2}}}
= \frac{c}{\gamma}.
$$

因此可将总能量重写为

$$
E
= \gamma m c^{2}
= m c^{2} \frac{c}{v_{\mathrm{int}}}.
$$

当 $v_{\mathrm{ext}} \to c$ 时，$\gamma \to \infty$，$v_{\mathrm{int}} \to 0$，总能量发散。这表明：要在几乎完全冻结的内部时间流逝下维持原有内部结构，需要无穷大的能量投入。质量 $m$ 在这里可视为对内部振荡频率 $\omega_{0}$ 的信息阻抗：频率越高，为固定外部速度分量不崩塌该内部结构所需的信息速率越大，表现为更大的 $m$ 与更剧烈的能量增长。证毕。

---

## Model Apply

本节讨论上述结构在若干典型物理情形中的应用与诠释。

### 光子与静止粒子的两个极限

在信息速率平面 $(v_{\mathrm{ext}}, v_{\mathrm{int}})$ 上，信息速率守恒对应于半径为 $c$ 的四分之一圆。两种重要极限为：

1. **静止有质量粒子**：$v_{\mathrm{ext}} = 0$，$v_{\mathrm{int}} = c$。全部信息预算用于内部演化，固有时间与坐标时间一致，粒子内部"时钟"以最大速率运行。

2. **无质量粒子（理想光子）**：$v_{\mathrm{ext}} = c$，$v_{\mathrm{int}} = 0$。全部预算用于外部传播，内部演化速度为零，固有时间不流逝。这与光子沿 null 轨迹、固有时间恒为零的标准结果一致。

一般有质量粒子对应于四分之一圆上的中间点，随着 $v_{\mathrm{ext}}$ 增大，内部速度 $v_{\mathrm{int}}$ 减小，固有时间流逝减慢。

### 缪子寿命延长的几何诠释

宇宙线产生的高能缪子在穿越地球大气层时，其静止寿命约为 $\tau_{0} \approx 2.2\,\mu\mathrm s$，但在实验室系中观测到的平均寿命会随能量增大而显著延长。标准解释是洛伦兹时间膨胀：$\tau = \gamma \tau_{0}$。

在信息速率图像中，高速缪子的外部速度接近 $c$，内部速度为 $v_{\mathrm{int}} = c/\gamma \ll c$。设缪子衰变可以被视为内部状态在射影空间上达到某一临界距离 $L_{\mathrm{crit}}$ 时发生的跃迁，则静止系中达到该距离所需的固有时间为 $\tau_{0}$。在实验室系中，同一内部距离仍需固有时间 $\tau_{0}$，但固有时间与坐标时间关系为 $\mathrm d\tau = \mathrm dt/\gamma$，故达到该内部距离所需的坐标时间为 $\tau = \gamma \tau_{0}$，表现为寿命延长。

这说明，缪子寿命延长可理解为：缪子把信息预算的大部分分配给了外部高速位移，导致内部演化"变慢"，从而延后了衰变条件的达成。

### 相对论动量与动能的内部视角

Theorem 3.3 给出

$$
\mathbf p = \gamma m \mathbf v_{\mathrm{ext}},
\quad
E = \gamma m c^{2}.
$$

结合 $v_{\mathrm{int}} = c/\gamma$，可重写为

$$
\mathbf p
= m \frac{v_{\mathrm{ext}}}{v_{\mathrm{int}}} c,
\quad
E
= m c^{2} \frac{c}{v_{\mathrm{int}}}.
$$

这表明，在信息速率守恒框架下，动量与能量的增长可视为内部速度 $v_{\mathrm{int}}$ 被压缩的代价：对给定的外部速度 $v_{\mathrm{ext}}$，若内部速度降低，则为了维持相同的内部结构（尤其是保持频率 $\omega_{0}$ 不致退相干），系统必须投入更大的能量，表现为更大的动量与动能。

### QCA 中的 Dirac 粒子与内部振荡

在 Dirac–QCA 模型中，一维或三维的 Dirac 方程可由离散时间量子行走的连续极限获得，色散关系为

$$
E(p) = \pm \sqrt{(c p)^{2} + m^{2} c^{4}}.
$$

在静止动量 $p=0$ 附近，内部两个能带之间的干涉可产生高频 Zitterbewegung 振荡，其特征频率量级为 $2 m c^{2}/\hbar$。

在本文框架下，可将 $m c^{2} = \hbar \omega_{0}$ 中的 $\omega_{0}$ 理解为内部态在射影空间中的基本振荡频率。信息速率守恒要求外部速度越大，内部速度越小，内部振荡在坐标时间下观测到的速率越低；为了保持相同的内部相位演化，需要增加总能量 $E$，与 relativistic 质量–能量关系兼容。

---

## Engineering Proposals

尽管信息速率守恒公理在目前尚处理论层面，仍可据此提出若干具有工程意义的检验与应用方向。

### 相对论极限下的信息处理架构

Lloyd 的分析指出，给定能量与体积的物理系统，其最大计算步数与可处理信息量存在严格上界。若把某计算单元视为携带内部信息态与外部通信链路的"粒子"，则其总信息更新速率由能量预算限定，内部计算速率与外部通信速率需在该预算下平衡。

在接近相对论速度运行的航天器或卫星平台上，理论上可对"外部通信速率–内部运算速率–总能量"三者关系进行优化设计：

1. 由平台总能量与自由度估算理论上的最大信息步数上界；

2. 根据信道需求确定外部通信带宽与信号传播需求，对应外部速度分量；

3. 由信息速率圆约束，反推内部计算时钟频率的上界，从而给出在极端速度条件下硬件设计必须满足的稳健性余量。

在地面常规条件下，这种修正效应极微，但在未来极端航天任务或强引力环境下，信息速率视角提供了一个统一评估框架。

### QCA 量子模拟中的内部–外部分解测量

在超导线路、离子阱与冷原子系统中，已经实现了多种离散时间量子行走与 QCA 演化。可设计如下实验以探测内部与外部速度的耦合特性：

1. 在一维或二维平台上实现 Dirac–QCA，局域内部空间为两能级或多能级系统；

2. 制备在动量空间中不同中心 $p_{0}$ 的窄带波包，实现可控的外部群速度；

3. 在演化过程中同时测量：包络中心的位置期望值与内部 Bloch 向量在射影空间上的演化轨迹；

4. 利用 Fubini–Study 距离估计内部几何速度 $v_{\mathrm{FS}}(t)$，并拟合是否存在近似守恒关系

   $$
   v_{\mathrm{ext}}^{2} + \alpha^{2} v_{\mathrm{FS}}^{2} \approx c_{\mathrm{eff}}^{2},
   $$

   其中 $\alpha$ 为内部标度常数，$c_{\mathrm{eff}}$ 为该 QCA 的有效光速。

虽然实际系统存在耗散与噪声，严格守恒关系不必精确成立，但观察到近似的"速率圆"结构将为本文公理提供一个可观测的有效支持。

### 量子控制与量子速度极限中的统一视角

量子速度极限已广泛应用于量子控制与量子计量，给出任意目标变换的最短实现时间下限。在信息速率框架下，可将这些结果理解为内部速度 $v_{\mathrm{int}}$ 的约束，并在加入外部信号传播限制后构造"全栈"速度极限：

* 内部演化由 Fubini–Study 速度与量子速度极限限定；

* 外部控制信号与读出由局域性与 Lieb–Robinson 速度限定；

* 总信息速率预算由 $c$ 与系统总能量限定。

由此，在给定能量与空间布局的硬件平台上，可定义同时考虑内部演化与外部通信的最短控制时间下界，为高效量子控制算法的设计提供新的约束。

---

## Discussion (risks, boundaries, past work)

### 与 QCA–相对论涌现文献的关系

既有工作已经在 QCA 框架中从信息处理原则推导出 Dirac 方程与 Lorentz 对称性。D'Ariano 等人通过对称性、公设与离散性假设，构造了在长波极限下收敛于 Dirac 方程的量子行走，并分析了其色散关系与 Zitterbewegung 行为。

这些工作着重展示"如何从 QCA 得到相对论方程"；本文在其基础上提出的信息速率守恒则强调"为何存在 Minkowski 度规与洛伦兹因子"：一旦假定外部与内部两类信息更新被统一的预算 $c$ 约束，并用内部几何速度定义固有时间，狭义相对论的几何结构就成为这一预算约束的代数重写，而非独立的几何公理。

### 全局更新时间参数的本体地位

本文以 QCA 的离散步数 $n$ 或其连续极限 $t$ 作为坐标时间，并由此定义外部和内部速度。这看似引入了一个"特权时间参数"，与狭义相对论中不存在优先参考系的精神相冲突。

需要强调的是：在本框架中，$t$ 是底层离散动力学的标签，真正具有物理意义的是固有时间 $\tau$ 与线元 $\mathrm ds^{2} = -c^{2}\mathrm d\tau^{2}$。只要所有可观测量都可用 $\tau$ 与 $\mathrm ds^{2}$ 表达，并且不同观察者对 $t$ 的选择产生的预测在这些不变量上是一致的，那么底层是否存在"绝对栅格时间"在可观测层面就无法区分。严格证明这一点需要在 QCA–连续场论对应中展示：所有关联函数与散射幅最终只依赖 Lorentz 不变量，而与具体格点时间坐标无关，这超出本文范围，是未来工作的关键方向之一。

### 单粒子近似与多体纠缠的局限

本构架主要在单粒子（或少体可分）激发的层面上建立。实际物理系统中，多体纠缠与相互作用会显著影响信息传播与演化速度。Lieb–Robinson 界给出的是多体系统中算符支撑的传播速度，而量子速度极限在开放或多体系统中也存在非平凡的推广。

要将信息速率守恒推广到多体系统，需要：

1. 将"内部速度"推广到对某一局域子系统（或张量网络块）在射影空间中的演化速度；

2. 把外部速度定义为该子系统在全体系统中的支持区域演化速度；

3. 考虑纠缠熵与相关长度对可用信息预算的再分配。

这些问题牵涉到多体量子信息与张量网络几何，本文仅在单粒子层面建立了基本图像。

### 质量的拓扑–信息解释的边界

将质量解释为内部振荡频率或"信息阻抗"的想法与 Zitterbewegung 诠释、拓扑物态中的质量缺口以及 Higgs 机制存在交汇。要使之成为完整理论，需要满足至少三点：

1. 在线性 Dirac–QCA 模型中证明：内部振荡频率谱与有效连续质量参数之间具有稳定的一一对应关系；

2. 在包含规范场与自发对称性破缺的 QCA 模型中，说明质量的这一内部频率诠释如何与传统 Higgs 机制相容（例如质量由耦合常数与对称性破缺尺度共同决定，而内部频率为其在 QCA 场构态中的体现）；

3. 在引入引力的情形下，分析内部振荡频率如何对曲率与引力势能作出反应，从而与等效原理保持一致。

本文仅在狭义相对论与自由粒子层面给出信息–几何的一致性重述，并未触及上述全局问题。

### 与量子速度极限及信息引力方案的关系

本文内部速度 $v_{\mathrm{int}}$ 的定义直接采用 Fubini–Study 度规与量子速度极限的结果，因此与 Deffner 等人关于量子速度极限的综述以及 Hörnedal 等人的几何推广工作存在直接联系。在这些工作中，演化时间下界被等价地表述为能量涨落沿时间积分的下界；在本文中，这一积分被解释为固有时间的几何度量。

近年来，以纠缠熵、张量网络与相干信息为基础的"信息引力"方案试图将时空几何视为信息结构的涌现。本文的结果在更简化的狭义相对论背景下展示了：即便尚未引入曲率与全息结构，单纯的"信息速率圆"已经足以重构 Minkowski 度规。这提示了一条推广途径：在引力存在时，可考虑把信息速率守恒拓展为"信息体积守恒"或"时间刻度密度守恒"，从而在离散 QCA 本体中导出有效的曲率与爱因斯坦场方程，这将是后续工作的重点方向之一。

---

## Conclusion

本文在量子元胞自动机本体论与量子速度极限理论的背景下，引入了"信息速率守恒"的公理化框架，将每个局域激发的外部群速度与内部 Fubini–Study 几何速度视为同一信息预算的正交分量，满足

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}.
$$

以内部速度定义固有时间流逝率 $\mathrm d\tau / \mathrm dt = v_{\mathrm{int}}/c$ 后，可从该单一公理出发，严格导出：

1. 固有时间与坐标时间的关系 $\mathrm d\tau = \mathrm dt/\gamma$，即洛伦兹时间膨胀公式；

2. Minkowski 线元 $\mathrm ds^{2} = -c^{2}\mathrm d\tau^{2} = -c^{2}\mathrm dt^{2} + \mathrm d\mathbf x^{2}$ 作为信息速率圆的代数重写；

3. 四速度与四动量结构及其不变质量壳关系 $E^{2} = p^{2}c^{2} + m^{2}c^{4}$；

4. 质量作为内部振荡频率的体现，满足 $m c^{2} = \hbar \omega_{0}$，以及总能量 $E = m c^{2} c/v_{\mathrm{int}}$ 的信息阻抗诠释。

这一框架把狭义相对论从"先验几何"还原为"有限信息速率资源分配"的必然结果，为统一量子信息处理、量子速度极限与时空几何提供了一种简洁而具有约束力的视角。未来工作将致力于：在多体纠缠与相互作用存在时推广信息速率守恒；在包含规范场与引力的 QCA 模型中将其提升为"信息体积守恒"或"时间刻度密度守恒"；并通过 QCA 量子模拟与极端环境信息系统设计对该框架进行实验与工程层面的检验。

---

## Acknowledgements, Code Availability

作者感谢量子元胞自动机、量子速度极限与信息物理极限相关文献所提供的理论基础。本文所有推导均为解析推导，未使用数值仿真代码，因此不存在可公开的软件或代码仓库。

---

## 附录 A：Fubini–Study 度规与量子速度极限的推导

本附录回顾构建内部速度 $v_{\mathrm{int}}$ 所依赖的 Fubini–Study 度规与量子速度极限的基本公式，并说明内部速度上界 $v_{\mathrm{int}} \le c$ 的归一化逻辑。

### A.1 射影 Hilbert 空间与 Fubini–Study 距离

设 $\mathcal H$ 为有限维复 Hilbert 空间，纯态由归一化态矢 $\ket{\psi} \in \mathcal H$ 描述，其物理等价类由整体相位不变。射影 Hilbert 空间 $\mathbb{P}(\mathcal H)$ 上两纯态 $\ket{\psi}$、$\ket{\phi}$ 的 Fubini–Study 距离定义为

$$
\cos^{2} \frac{d_{\mathrm{FS}}(\psi, \phi)}{2}
= \frac{|\braket{\psi}{\phi}|^{2}}{\braket{\psi}{\psi}\,\braket{\phi}{\phi}}.
$$

当 $\ket{\psi} = \ket{\phi}$ 时，距离为零；当 $\ket{\psi}$ 与 $\ket{\phi}$ 正交时，距离为 $\pi$。

对光滑时间演化曲线 $\ket{\psi(t)}$，在 $t$ 和 $t + \mathrm dt$ 之间的无穷小距离可通过展开内积并取极限得到

$$
\mathrm d s_{\mathrm{FS}}^{2}
= 4 \left( \langle \dot{\psi}(t) | \dot{\psi}(t) \rangle
- |\langle \psi(t) | \dot{\psi}(t) \rangle|^{2} \right)\mathrm dt^{2}.
$$

### A.2 Schrödinger 演化下的几何速度

若态矢随时间无关哈密顿量 $H$ 演化，

$$
\ket{\dot{\psi}(t)}
= -\frac{\mathrm i}{\hbar} H \ket{\psi(t)},
$$

则

$$
\langle \dot{\psi} | \dot{\psi} \rangle
= \frac{1}{\hbar^{2}} \bra{\psi} H^{2} \ket{\psi},
\quad
\langle \psi | \dot{\psi} \rangle
= -\frac{\mathrm i}{\hbar} \bra{\psi} H \ket{\psi}.
$$

代入线元得

$$
\mathrm d s_{\mathrm{FS}}^{2}
= \frac{4}{\hbar^{2}}
\left( \bra{\psi} H^{2} \ket{\psi}
- \bra{\psi} H \ket{\psi}^{2} \right)\mathrm dt^{2}
= \frac{4 \Delta H^{2}}{\hbar^{2}} \mathrm dt^{2},
$$

其中

$$
\Delta H
= \sqrt{\bra{\psi} H^{2} \ket{\psi}
- \bra{\psi} H \ket{\psi}^{2}}
$$

为能量不确定度。因此几何速度为

$$
v_{\mathrm{FS}}
= \frac{\mathrm d s_{\mathrm{FS}}}{\mathrm dt}
= \frac{2 \Delta H}{\hbar}.
$$

这一结果表明，在给定能谱支撑下，能量不确定度越大，态在射影空间中移动越快。

### A.3 Mandelstam–Tamm 与 Margolus–Levitin 量子速度极限

Mandelstam–Tamm 速度极限考虑从初始纯态 $\ket{\psi_{0}}$ 演化到与之正交的纯态 $\ket{\psi_{\perp}}$ 所需的最短时间 $\tau_{\perp}$，证明其满足

$$
\tau_{\perp}
\ge \frac{\pi \hbar}{2 \Delta H}.
$$

Margolus–Levitin 速度极限则基于平均能量 $E = \bra{\psi} H \ket{\psi}$ 给出另一下界

$$
\tau_{\perp}
\ge \frac{\pi \hbar}{2 E}.
$$

两者共同给出最短时间的组合下界

$$
\tau_{\perp}
\ge \max\left( \frac{\pi \hbar}{2 \Delta H},
\frac{\pi \hbar}{2 E} \right).
$$

这些结果可视为时间–能量不确定关系的几何化表达：射影空间上两正交态之间的距离为 $\pi$，而几何速度上界为 $2 \Delta H/\hbar$，故最短时间必须不小于距离除以速度。

在多能级系统中，达到这种上界需要精心选择初始态，一般为能谱边缘两本征态的等幅叠加态。

### A.4 内部速度的归一与上界

本文定义内部速度

$$
v_{\mathrm{int}} = \ell_{\mathrm{int}} v_{\mathrm{FS}}
= \ell_{\mathrm{int}} \frac{2 \Delta H}{\hbar}.
$$

为固定 $\ell_{\mathrm{int}}$，可采用如下策略：

1. 选定某类物理上可实现的"极限内部态族"，例如在两能级系统中饱和 Mandelstam–Tamm 与 Margolus–Levitin 上界的叠加态，使其在静止系中代表"最大内部活跃度"；

2. 要求这些态在静止系中具有 $v_{\mathrm{int}} = c$；

3. 解得

   $$
   \ell_{\mathrm{int}}
   = \frac{c \hbar}{2 \Delta H_{\max}}.
   $$

   由于任一态的能量不确定度都不超过该支撑下的 $\Delta H_{\max}$，对所有态均有

   $$
   v_{\mathrm{int}} \le c.
   $$

   结合 QCA 的有限信号速度 $|v_{\mathrm{ext}}|\le c$，信息速率守恒公理要求物理态在二维速率平面内被限制在一个半径为 $c$ 的圆周上，从而自然引出后续闵可夫斯基几何的结构。

---

## 附录 B：由信息速率圆到闵可夫斯基度规的抽象推导

本附录在更抽象的设定下，给出由信息速率圆推导 Minkowski 度规的过程，凸显几何结构与代数恒等式之间的一致性。

### B.1 抽象信息速率平面

考虑二维实向量空间 $\mathbb R^{2}$，坐标记为 $(u_{1}, u_{2})$，代表两类信息速率。假设物理上允许的速率对被约束在半径为常数 $c>0$ 的圆周上，即

$$
u_{1}^{2} + u_{2}^{2} = c^{2}.
$$

引入参数 $\theta \in [0, \pi/2]$，令

$$
u_{1} = c \sin\theta,
\quad
u_{2} = c \cos\theta.
$$

将 $u_{1}$ 识别为外部速度 $v_{\mathrm{ext}}$，$u_{2}$ 识别为内部速度 $v_{\mathrm{int}}$。

假设存在坐标时间参数 $t$，外部位移满足

$$
\left| \frac{\mathrm d\mathbf x}{\mathrm dt} \right|
= v_{\mathrm{ext}}(t) = u_{1}(t) = c \sin\theta(t),
$$

并定义固有时间

$$
\frac{\mathrm d\tau}{\mathrm dt}
= \frac{v_{\mathrm{int}}(t)}{c}
= \frac{u_{2}(t)}{c}
= \cos\theta(t).
$$

### B.2 洛伦兹因子的几何关系

由定义

$$
\frac{\mathrm d\tau}{\mathrm dt} = \cos\theta(t)
\quad \Rightarrow \quad
\frac{\mathrm dt}{\mathrm d\tau}
= \frac{1}{\cos\theta(t)}
\equiv \gamma(t).
$$

另一方面，$v_{\mathrm{ext}} = c \sin\theta$，故

$$
\sin^{2}\theta
= \frac{v_{\mathrm{ext}}^{2}}{c^{2}},
\quad
\cos^{2}\theta
= 1 - \frac{v_{\mathrm{ext}}^{2}}{c^{2}},
$$

于是

$$
\gamma
= \frac{1}{\cos\theta}
= \frac{1}{\sqrt{1 - v_{\mathrm{ext}}^{2}/c^{2}}},
$$

正是洛伦兹因子。由此可见，只要存在一个信息速率圆与固有时间的上述定义，时间膨胀关系自动被恢复。

### B.3 Minkowski 线元的代数重写

定义时空线元

$$
\mathrm ds^{2}
= -c^{2}\mathrm dt^{2} + \mathrm d\mathbf x^{2}.
$$

由 $\mathrm d\mathbf x^{2} = v_{\mathrm{ext}}^{2}\mathrm dt^{2}$，有

$$
\mathrm ds^{2}
= -c^{2}\mathrm dt^{2} + v_{\mathrm{ext}}^{2}\mathrm dt^{2}
= -(c^{2} - v_{\mathrm{ext}}^{2})\mathrm dt^{2}.
$$

利用速率圆

$$
c^{2} - v_{\mathrm{ext}}^{2}
= v_{\mathrm{int}}^{2},
$$

得到

$$
\mathrm ds^{2}
= -v_{\mathrm{int}}^{2} \mathrm dt^{2}.
$$

另一方面，固有时间定义给出

$$
\mathrm d\tau
= \frac{v_{\mathrm{int}}}{c}\mathrm dt
\quad \Rightarrow \quad
v_{\mathrm{int}}^{2}\mathrm dt^{2}
= c^{2}\mathrm d\tau^{2}.
$$

故

$$
\mathrm ds^{2} = -c^{2}\mathrm d\tau^{2}.
$$

这一关系表明，Minkowski 线元的结构等价于信息速率圆与固有时间定义的组合结果。换言之，一旦承认"外部速度与内部速度在速率平面上构成半径为 $c$ 的圆"，Minkowski 度规便不再是额外假设，而是圆的代数重写。

---

## 附录 C：一维 Dirac–QCA 中质量与内部频率的关系

本附录以一维 Dirac–QCA 为例，说明内部振荡频率与质量参数之间的关系，从而为 Theorem 3.4 提供模型层面的支撑。

### C.1 一维 Dirac–QCA 的构造

考虑一维晶格 $\Lambda = a \mathbb Z$，格距为 $a$。每个格点携带两维内部 Hilbert 空间 $\mathcal H_{x} \cong \mathbb C^{2}$，可视为自旋–$\tfrac{1}{2}$ 自由度。定义移位算符

$$
(S_{+}\psi)_{x} = \psi_{x-1},
\quad
(S_{-}\psi)_{x} = \psi_{x+1}.
$$

构造如下一步演化算符

$$
U
= \exp\left( -\mathrm i \theta \sum_{x} \sigma_{x}^{y} \right)
\exp\left( -\mathrm i \frac{\pi}{2} \sum_{x} \sigma_{x}^{x} \right)
\left( S_{+} \otimes \ket{\uparrow}\bra{\uparrow}
+ S_{-} \otimes \ket{\downarrow}\bra{\downarrow} \right),
$$

其中 $\sigma^{x},\sigma^{y}$ 为 Pauli 矩阵，$\theta$ 为可调参数。对该 QCA 进行傅里叶变换，可在动量空间得到对角化形式

$$
U(p)
= \mathrm e^{-\mathrm i H_{\mathrm{eff}}(p)\Delta t/\hbar},
$$

对应的有效哈密顿量在小 $p$ 极限下收敛于一维 Dirac 哈密顿量

$$
H_{\mathrm{D}}(p)
= c p\, \sigma^{z} + m c^{2} \sigma^{x},
$$

其中 $c$ 与 $m$ 为由 $\theta$、$a$、$\Delta t$ 决定的参数。

### C.2 色散关系与内部振荡

对上述 Dirac 哈密顿量对角化得能谱

$$
E_{\pm}(p)
= \pm \sqrt{(c p)^{2} + m^{2} c^{4}}.
$$

在静止动量 $p=0$ 时，

$$
E_{\pm}(0)
= \pm m c^{2}.
$$

考虑由正、负能带本征态 $\ket{+}$、$\ket{-}$ 的等幅叠加构成的内部态

$$
\ket{\psi(0)}
= \frac{1}{\sqrt{2}}
\left( \ket{+} + \ket{-} \right).
$$

其时间演化为

$$
\ket{\psi(t)}
= \frac{1}{\sqrt{2}}
\left( \mathrm e^{-\mathrm i m c^{2} t/\hbar}\ket{+}
+ \mathrm e^{\mathrm i m c^{2} t/\hbar}\ket{-} \right).
$$

对合适的内部观测量（例如某一 Pauli 分量）的期望值，将出现频率为 $2 m c^{2}/\hbar$ 的振荡，这就是 Zitterbewegung 现象的离散版本。

在本文框架下，可将内部振荡的基本频率 $\omega_{0}$ 取为 $m c^{2}/\hbar$ 或 $2 m c^{2}/\hbar$ 中的一个常数倍；为了简洁起见，可定义

$$
m c^{2} = \hbar \omega_{0},
$$

将质量视为内部频率的线性函数。上述构造说明，这种关系在 Dirac–QCA 中具有明确的模型基础。

### C.3 内部速度与质量的对应

在静止动量 $p=0$ 的情况下，内部态以频率 $\omega_{0}$ 在射影空间中演化，Fubini–Study 速度为

$$
v_{\mathrm{FS}}
= \frac{2 \Delta H}{\hbar}.
$$

对两能级对称能谱 $E_{\pm} = \pm m c^{2}$ 的等幅叠加态，能量不确定度为

$$
\Delta H
= m c^{2},
$$

故

$$
v_{\mathrm{FS}}
= \frac{2 m c^{2}}{\hbar}
= 2 \omega_{0}.
$$

在本文选取的内部长度标度 $\ell_{\mathrm{int}}$ 下，要求静止系中饱和态满足 $v_{\mathrm{int}} = c$，即

$$
c
= \ell_{\mathrm{int}} v_{\mathrm{FS}}
= \ell_{\mathrm{int}} 2 \omega_{0}
\quad \Rightarrow \quad
\ell_{\mathrm{int}}
= \frac{c}{2 \omega_{0}}.
$$

从而对一般态有

$$
v_{\mathrm{int}}
= \ell_{\mathrm{int}} v_{\mathrm{FS}}
= \frac{c}{2 \omega_{0}} v_{\mathrm{FS}}.
$$

当考虑包含动量的情况时，能谱展开为 $E_{\pm}(p)$，内部振荡频率与能量不确定度随 $p$ 变化，内部速度 $v_{\mathrm{int}}$ 将低于 $c$。结合信息速率守恒与固有时间定义，即可得到随 $p$ 增大的外部速度压缩内部速度的效果，从而导出时间膨胀与能量增长关系。

因此，在 Dirac–QCA 模型中，质量 $m$ 与内部振荡频率 $\omega_{0}$ 之间存在线性对应，内部速度的归一与信息速率守恒公理在具体模型中具有明确的实现方式，为 Theorem 3.4 所采用的质量–频率关系提供了有力支持。

---

## References

[1] S. Lloyd, "Ultimate physical limits to computation", Nature 406, 1047–1054 (2000).

[2] J. Anandan, Y. Aharonov, "Geometry of quantum evolution", Phys. Rev. Lett. 65, 1697–1700 (1990).

[3] L. Mandelstam, I. Tamm, "The uncertainty relation between energy and time in non-relativistic quantum mechanics", J. Phys. (USSR) 9, 249–254 (1945).

[4] N. Margolus, L. B. Levitin, "The maximum speed of dynamical evolution", Physica D 120, 188–195 (1998).

[5] E. H. Lieb, D. W. Robinson, "The finite group velocity of quantum spin systems", Commun. Math. Phys. 28, 251–257 (1972).

[6] M. Cheneau et al., "Experimental tests of Lieb–Robinson bounds", arXiv:2206.15126 (2022).

[7] G. M. D'Ariano, N. Mosco, P. Perinotti, A. Tosini, "Discrete time Dirac quantum walk in 3+1 dimensions", Entropy 18, 228 (2016).

[8] L. Mlodinow, G. M. D'Ariano, P. Perinotti, "Discrete spacetime, quantum walks, and relativistic wave equations", Phys. Rev. A 97, 042131 (2018).

[9] S. Deffner, S. Campbell, "Quantum speed limits: from Heisenberg's uncertainty principle to optimal quantum control", J. Phys. A: Math. Theor. 50, 453001 (2017).

[10] N. Hörnedal, "Generalizations of the Mandelstam–Tamm quantum speed limit", Master's thesis, Stockholm University (2021).

[11] G. Ness et al., "Quantum speed limit for states with a bounded energy spectrum", Phys. Rev. Lett. 129, 140403 (2022).

[12] S. Deffner, "Quantum speed limits and the maximal rate of information production", Phys. Rev. Research 2, 013161 (2020).

[13] 相关 QCA 与 Dirac 方程涌现文献，见 G. M. D'Ariano 等系列论文及其后续综述文献。

