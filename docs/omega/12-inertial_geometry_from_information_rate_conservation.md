# 信息速率守恒下的惯性几何：质量、时间膨胀与能量–频率关系的微观统一

## Abstract

在传统表述中，狭义相对论中的时间膨胀与"相对论性质量"增加通常被视为两个独立的运动学效应，而量子力学通过普朗克关系 $E=\hbar \omega$ 将能量与频率直接对应。对于一粒有质量粒子，当其速度接近光速时，总能量快速增长，对应平面波相位频率 $\omega$ 的增长；但同一粒子的固有时间流逝却出现洛伦兹膨胀，内部时钟似乎"变慢"。这种"变慢的时钟对应更大的能量"的图像在直觉层面造成张力。本文在量子元胞自动机（quantum cellular automaton, QCA）与信息速率守恒（光程守恒）框架下，引入一个二维的"信息速率圆"：将总信息更新速率视为常数 $c$，并在"外部空间位移速度" $v_{\mathrm{ext}}$ 与"内部态演化速度" $v_{\mathrm{int}}$ 之间做正交分解，满足 $v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}$。在这一结构下，静止质量 $m_{0}$ 被刻画为静止系中内部量子态的康普顿频率 $\omega_{0}=m_{0}c^{2}/\hbar$，而运动状态对应在希尔伯特空间"内部演化"与"外部平移"两个频率分量之间的资源重分配。本文证明：平面物质波的总频率满足 $\omega_{\mathrm{tot}}=\gamma \omega_{0}$，内部"时钟频率"则随速度按 $\omega_{\mathrm{clock}}=\omega_{0}/\gamma$ 红移，而这两类频率都统一地嵌入能量–动量关系 $E^{2}=m_{0}^{2}c^{4}+p^{2}c^{2}$ 所诱导的频率恒等式 $\omega_{\mathrm{tot}}^{2}=\omega_{0}^{2}+\omega_{\mathrm{space}}^{2}$。在信息速率圆上，这对应于惯性几何的一条简单规则：当外部速度趋近 $c$ 时，内部演化速度 $v_{\mathrm{int}}\to 0$，相应的有效惯性阻抗 $m_{\mathrm{eff}}\propto v_{\mathrm{int}}^{-3}$ 发散。惯性因而被解释为"内部时间冻结极限下维持拓扑结构不崩塌所需的能量成本"。这一框架在不修改任何已验证相对论与量子力学预言的前提下，给出了 $E=m c^{2}$ 与 $E=\hbar \omega$ 之间几何与信息论意义上的统一。

## Keywords

信息速率守恒；量子元胞自动机；惯性几何；康普顿时钟；相对论时间膨胀；能量–频率对应；Fubini–Study 度规

---

## 1. Introduction & Historical Context

### 1.1 质量、时间与频率的表观矛盾

狭义相对论以能量–动量关系

$$
E^{2}=m_{0}^{2}c^{4}+p^{2}c^{2}
$$

为核心，将 $m_{0}$ 定义为洛伦兹不变量，而"相对论性质量" $\gamma m_{0}$ 主要作为早期教学中的便利概念，其物理内涵在现代文献中逐渐被弱化或废弃，转而强调不变量质量与四动量的协变描述。

另一方面，量子理论通过普朗克关系

$$
E = \hbar \omega
$$

将能量与频率直接对应。对于一自由粒子的平面波解 $\psi \sim \exp[\mathrm{i}(k x-\omega t)]$，总能量即由时间方向的相位频率 $\omega$ 决定。而 de Broglie 进一步提出：每一个具有静止质量 $m_{0}$ 的粒子在其静止系中都携带一个本征振荡频率

$$
\omega_{0}=\frac{m_{0}c^{2}}{\hbar},
$$

这在今天通常被称为康普顿频率或"内部时钟"。

由此产生一个看似矛盾的图像：

* 相对论预言：当粒子以速度 $v$ 运动时，其固有时间满足 $\mathrm{d}\tau = \mathrm{d}t/\gamma$，即内部时钟相对于实验室时间"走慢"。

* 量子波动图像下，总能量 $E=\gamma m_{0}c^{2}$ 对应的平面波相位频率 $\omega_{\mathrm{tot}}=E/\hbar=\gamma \omega_{0}$ 却随 $\gamma$ 增大，即"频率变快"。

若将"频率"简单理解为"粒子内部振动的节律"，那么"时间变慢"与"总频率变快"似乎互相矛盾。事实上，围绕 de Broglie 内部时钟、康普顿频率与物质波频率之间的关系，已有大量讨论与实验方案，包括"岩石是时钟"与原子干涉仪中对康普顿时钟的探测。

### 1.2 量子元胞自动机与离散相对论动力学

量子元胞自动机（QCA）将宇宙建模为在格点 $\Lambda\subset\mathbb{Z}^{d}$ 上作用的离散、局域且严格幺正的更新规则，其连续极限可涌现 Dirac、Weyl 与 Maxwell 等场方程。特别地，一维 Dirac 型 QCA 已被构造并证明其在长波极限下精确再现自由 Dirac 方程的演化算符与色散关系。

在 Feynman "棋盘模型"中，自旋–$1/2$ 费米子的传播被表示为在时空格点上以光速前进、在转向处按质量参数赋权的路径求和，该模型同样在连续极限下给出 Dirac 方程。这些工作表明：

1. 自由相对论粒子的动力学可以在离散、有限信息的框架中涌现；

2. 质量参数在离散模型中天然地与"转向率""内部翻转率"等局域结构联系在一起。

这为从信息与计算的角度理解惯性与质量提供了自然入口。

### 1.3 量子演化几何与内部"演化速度"

另外一条重要线索来自量子态空间几何。Anandan 与 Aharonov 指出：在射影希尔伯特空间 $\mathbb{P}(\mathcal{H})$ 上，量子态的演化可以用 Fubini–Study 度规测地长度描述，演化"速度"满足

$$
\frac{\mathrm{d}s}{\mathrm{d}t} = \frac{2}{\hbar}\Delta H,
$$

其中 $\Delta H$ 是能量不确定度。这类结果与量子速度极限（Mandelstam–Tamm 与 Margolus–Levitin 界）一起说明：在固定能量资源下，量子态的演化"速率"具有上界。

如果将"内部时间流逝"理解为"态在希尔伯特空间中演化的速率"，那么对于一个给定的自由粒子，其可用的演化"带宽"可以被视为有限资源。当这一资源更多地被用于改变空间位置（外部运动）时，用于内部相位/自旋/拓扑结构演化的份额必然减少。

### 1.4 本文的目标与贡献

本文在上述背景下引入"信息速率守恒"的概念：将一粒有质量粒子的全局演化视为在"外部位置自由度"与"内部态自由度"之间的信息速率分配，并假设存在一个普适上界 $c$，使得

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2},
$$

其中 $v_{\mathrm{ext}}$ 是外部群速度，$v_{\mathrm{int}}$ 则刻画内部量子态演化在 Fubini–Study 度规下的"速率"，两者共同构成一个二维"信息速率圆"。在此基础上，本文实现以下几点：

1. 给出一个从 QCA 与量子演化几何出发的惯性几何模型，将狭义相对论的时间膨胀视为信息速率在内外两个分量之间的再分配。

2. 证明对于 Dirac 型自由粒子，平面波的总频率、空间频率与静止康普顿频率之间满足 $\omega_{\mathrm{tot}}^{2}=\omega_{0}^{2}+\omega_{\mathrm{space}}^{2}$，并在信息速率圆上得到简洁的参数化关系 $\omega_{\mathrm{tot}}=\gamma \omega_{0}$，$\omega_{\mathrm{clock}}=\omega_{0}/\gamma$。

3. 从经典相对论力学出发，将纵向有效惯性质量 $m_{\mathrm{eff}}=\gamma^{3}m_{0}$ 重写为 $m_{\mathrm{eff}}\propto v_{\mathrm{int}}^{-3}$，从而将惯性解释为"内部时间冻结极限下的拓扑阻抗"。

4. 结合已有康普顿钟实验与物质波干涉实验，讨论如何在实验层面检验这种"惯性几何–信息速率"图像及其可能的修正项。

本文的立场是：不修改已检验的能量–动量关系与量子测量规则，而是在这些关系之上赋予一个统一的几何–信息论解释，使得"质量–频率–时间膨胀"三者合而为一。

---

## 2. Model & Assumptions

### 2.1 Dirac–QCA 有效模型与自由粒子扇区

考虑一维空间上的 Dirac 型量子元胞自动机，其格点集合为 $\Lambda=\Delta x\,\mathbb{Z}$，每一格点携带内部 Hilbert 空间 $\mathcal{H}_{\mathrm{cell}}\cong\mathbb{C}^{2}$，对应左右传播模或自旋上/下两个内部自由度。整体 Hilbert 空间为

$$
\mathcal{H}=\bigotimes_{n\in\Lambda}\mathcal{H}_{\mathrm{cell}}^{(n)}.
$$

演化由局域幺正算符 $U$ 给出，可视作"内部旋转"与"条件平移"的组合。已有研究表明，在满足齐次性、局域性与离散因果性的条件下，可以构造出这样一类 QCA，其在长波极限下的单粒子扇区上有效哈密顿量为

$$
H = c \alpha \hat{p} + \beta m_{0}c^{2},
$$

其中 $\hat{p}$ 是一维动量算符，$\alpha,\beta$ 为泡利矩阵，满足 $\alpha^{2}=\beta^{2}=\mathbb{I}$ 与反对易关系 $\{\alpha,\beta\}=0$。

这一哈密顿量在平面波基底 $\psi_{p}(x)\sim \exp(\mathrm{i}px/\hbar)$ 上的本征值为

$$
E(p)=\pm\sqrt{m_{0}^{2}c^{4}+p^{2}c^{2}},
$$

即标准的能量–动量色散关系。

因此，在后文的推导中，我们只需使用这一能量–动量关系与 QCA 的离散本体论作为概念背景，而无须依赖具体的元胞规则细节。

### 2.2 信息速率圆与"内–外"分解

我们引入如下基本公理。

**公理 1（信息速率守恒）.**

对任意自由粒子，在其一条世界线上，以某一外部参考时间 $t$ 参数化时，存在两个非负函数 $v_{\mathrm{ext}}(t)$ 与 $v_{\mathrm{int}}(t)$，分别记作"外部位移速率"与"内部态演化速率"，满足

$$
v_{\mathrm{ext}}^{2}(t)+v_{\mathrm{int}}^{2}(t)=c^{2}.
$$

其中：

* $v_{\mathrm{ext}}(t)$ 在连续极限下等同于粒子中心位置的群速度 $v(t)=\partial E/\partial p$；

* $v_{\mathrm{int}}(t)$ 刻画同一粒子在"内部自由度"方向上的量子态演化速率，其量纲为速度，通过一个固定的标度因子从 Fubini–Study 演化速度 $\mathrm{d}s/\mathrm{d}t$ 线性获得。

上述关系在几何上将 $(v_{\mathrm{ext}},v_{\mathrm{int}})$ 约束在半径为 $c$ 的二维圆上，故称"信息速率圆"。

为了与狭义相对论保持一致，我们将外部速度识别为

$$
v_{\mathrm{ext}}=v,
$$

并据此定义

$$
v_{\mathrm{int}}(v) := \sqrt{c^{2}-v^{2}} = c\sqrt{1-\beta^{2}},\quad \beta:=\frac{v}{c}.
$$

这一定义在静止系 $(v=0)$ 时给出 $v_{\mathrm{int}}=c$，即全部信息速率用于内部演化；而在极限 $v\to c$ 时，$v_{\mathrm{int}}\to 0$，对应"内部时间冻结"的极端情况。

### 2.3 时间膨胀与内部"时钟频率"

在狭义相对论中，固有时间 $\tau$ 与实验室时间 $t$ 之间满足

$$
\frac{\mathrm{d}\tau}{\mathrm{d}t}=\sqrt{1-\beta^{2}}=\frac{1}{\gamma},\quad \gamma:=\frac{1}{\sqrt{1-\beta^{2}}}.
$$

与上式比较，可以自然地将

$$
\frac{v_{\mathrm{int}}}{c} = \frac{\mathrm{d}\tau}{\mathrm{d}t}
$$

视为单位实验室时间内"内部时间"流逝的归一化速率。也就是说，内部速度 $v_{\mathrm{int}}$ 的大小等价于固有时间流逝速率的度量。

如果在静止系中粒子携带康普顿频率

$$
\omega_{0}=\frac{m_{0}c^{2}}{\hbar},
$$

则沿世界线的固有时间参数化下，其内部相位可写为

$$
\varphi(\tau)=\omega_{0}\tau.
$$

在实验室时间 $t$ 的视角下，可见到的"内部时钟频率"为

$$
\omega_{\mathrm{clock}}:=\frac{\mathrm{d}\varphi}{\mathrm{d}t}
=\omega_{0}\frac{\mathrm{d}\tau}{\mathrm{d}t}
=\omega_{0}\frac{v_{\mathrm{int}}}{c}
=\frac{\omega_{0}}{\gamma}.
$$

这正是时间膨胀的频率形式：运动粒子的内部时钟相对于实验室时间发生红移。

### 2.4 能量–频率关系与空间频率分量

另一方面，在动量本征态中，Dirac 粒子的平面波解具有相位

$$
\psi(x,t)\sim\exp\left[\frac{\mathrm{i}}{\hbar}\left(p x-E t\right)\right]
=\exp\left[\mathrm{i}\left(k x-\omega_{\mathrm{tot}}t\right)\right],
$$

其中

$$
k:=\frac{p}{\hbar},\qquad \omega_{\mathrm{tot}}:=\frac{E}{\hbar}.
$$

由能量–动量关系得

$$
\omega_{\mathrm{tot}}^{2}=\frac{E^{2}}{\hbar^{2}}
=\frac{m_{0}^{2}c^{4}+p^{2}c^{2}}{\hbar^{2}}
=\left(\frac{m_{0}c^{2}}{\hbar}\right)^{2}
+\left(\frac{pc}{\hbar}\right)^{2}
=\omega_{0}^{2}+\omega_{\mathrm{space}}^{2},
$$

其中

$$
\omega_{\mathrm{space}}:=c|k|=\frac{pc}{\hbar}
$$

可以被解释为"空间方向的频率分量"，对应波矢带来的空间振荡。

这一频率恒等式与信息速率圆之间存在紧密平行：$\omega_{0}$ 扮演"静止内部频率"的角色，对应 $v_{\mathrm{int}}$ 在静止时的取值；$\omega_{\mathrm{space}}$ 则对应外部动量与群速度。

在后文中，我们将展示如何在 QCA 的内部–外部自由度分解下，将 $\omega_{\mathrm{tot}}$、$\omega_{0}$、$\omega_{\mathrm{space}}$ 与 $v_{\mathrm{ext}}$、$v_{\mathrm{int}}$ 统一到一个"惯性几何"的框架中。

---

## 3. Main Results (Theorems and Alignments)

本节给出本文的主要定理与结构性结论。

### 3.1 惯性几何定理：时间膨胀的几何重写

**定理 3.1（惯性几何与时间膨胀）.**

在信息速率公理 1 成立的前提下，将外部速度定义为 $v_{\mathrm{ext}}=v$，内部速度定义为

$$
v_{\mathrm{int}}=\sqrt{c^{2}-v^{2}},
$$

则以下陈述等价：

1. 狭义相对论的时间膨胀公式

   $$
   \mathrm{d}\tau=\mathrm{d}t\sqrt{1-\frac{v^{2}}{c^{2}}},
   $$

   即 $\mathrm{d}\tau/\mathrm{d}t=v_{\mathrm{int}}/c$。

2. 粒子在二维"信息速率平面"上的速度向量

   $$
   \mathbf{u}=(v_{\mathrm{ext}},v_{\mathrm{int}})
   $$

   具有固定模长 $|\mathbf{u}|=c$。

换言之，时间膨胀可以被理解为：当物体在外部空间中的运动速度增加时，内部演化速度在一个半径为 $c$ 的圆上被迫减小。

### 3.2 频率几何定理：内部钟与总频率的协调

**定理 3.2（频率几何与能量–动量关系）.**

对于一自由 Dirac 粒子的平面波态，定义静止康普顿频率

$$
\omega_{0}=\frac{m_{0}c^{2}}{\hbar},
$$

总频率

$$
\omega_{\mathrm{tot}}=\frac{E}{\hbar},
$$

与空间频率

$$
\omega_{\mathrm{space}}=\frac{pc}{\hbar}.
$$

则有频率恒等式

$$
\omega_{\mathrm{tot}}^{2}=\omega_{0}^{2}+\omega_{\mathrm{space}}^{2}.
$$

进一步，若定义内部"时钟频率"

$$
\omega_{\mathrm{clock}}:=\frac{\omega_{0}}{\gamma}
=\omega_{0}\frac{v_{\mathrm{int}}}{c},
$$

则总频率与内部时钟频率之间满足

$$
\omega_{\mathrm{tot}}=\gamma \omega_{0}
=\frac{\omega_{0}^{2}}{\omega_{\mathrm{clock}}},
$$

即

$$
\omega_{\mathrm{clock}}\cdot \omega_{\mathrm{tot}}=\omega_{0}^{2}.
$$

这说明：

* 对于给定不变量 $\omega_{0}$，当内部时钟在实验室时间下变慢时（$\omega_{\mathrm{clock}}$ 减小），总频率 $\omega_{\mathrm{tot}}$ 必然增大；

* 频率的"变慢"与"变快"实则指向两个不同的投影：内部时钟与外部平面波相位。

### 3.3 惯性质量放大的信息几何表达

在相对论力学中，沿速度方向的加速度 $a_{\parallel}$ 与施加力 $F_{\parallel}$ 之间满足

$$
F_{\parallel}=m_{0}\gamma^{3}a_{\parallel},
$$

由此可以定义纵向有效惯性

$$
m_{\mathrm{eff}}^{\parallel}:=\gamma^{3}m_{0}.
$$

利用 $v_{\mathrm{int}}=c/\gamma$，可将其重写为

$$
m_{\mathrm{eff}}^{\parallel}
=m_{0}\left(\frac{c}{v_{\mathrm{int}}}\right)^{3}.
$$

**定理 3.3（惯性作为内部时间速率的逆立方）.**

在信息速率圆框架下，纵向有效惯性质量随内部演化速度 $v_{\mathrm{int}}$ 呈逆立方发散：

$$
m_{\mathrm{eff}}^{\parallel}\propto v_{\mathrm{int}}^{-3}.
$$

因此，当 $v\to c$ 时，$v_{\mathrm{int}}\to 0$，而 $m_{\mathrm{eff}}^{\parallel}\to\infty$。从信息论角度看，这对应于：在内部时间几乎冻结的极限，一个系统要维持自身拓扑与量子关联结构的稳定，其对外力的响应刚度趋于无穷。

### 3.4 能量–内部速率恒等式与 $E=\hbar\omega$ 的统一

由时间膨胀关系 $\mathrm{d}\tau/\mathrm{d}t=v_{\mathrm{int}}/c$ 与不变量 $m_{0}$ 出发，可定义一个与内部速率直接相关的能量量：

$$
E_{\mathrm{tot}}
:= m_{0}c^{2}\frac{\mathrm{d}t}{\mathrm{d}\tau}
= m_{0}c^{2}\frac{c}{v_{\mathrm{int}}}
=\frac{m_{0}c^{3}}{v_{\mathrm{int}}}.
$$

另一方面，由能量–动量关系，$E_{\mathrm{tot}}=\gamma m_{0}c^{2}= \hbar \omega_{\mathrm{tot}}$。

**定理 3.4（能量–内部速率恒等式）.**

在信息速率圆框架下，自由粒子的总能量既可以写为

$$
E_{\mathrm{tot}}=\gamma m_{0}c^{2},
$$

也可以写为

$$
E_{\mathrm{tot}}=\frac{m_{0}c^{3}}{v_{\mathrm{int}}},
$$

并兼容普朗克关系

$$
E_{\mathrm{tot}}=\hbar \omega_{\mathrm{tot}}.
$$

从而建立起

$$
\omega_{\mathrm{tot}}
=\frac{E_{\mathrm{tot}}}{\hbar}
=\frac{m_{0}c^{3}}{\hbar v_{\mathrm{int}}}
=\gamma \omega_{0}.
$$

这表明：

* $E=m c^{2}$ 与 $E=\hbar \omega$ 在本质上是同一恒等式在不同变量中的两种写法；

* 信息速率圆给出了一个在"能量–频率–内部时间速率"之间的三重统一。

这些定理的证明将在后文的 Proofs 与附录中给出。

---

## 4. Proofs

本节给出上述定理的主干推导，将更技术性的算符与几何论证移入附录。

### 4.1 定理 3.1 的证明：Minkowski 几何与圆形重参数化

四速度定义为

$$
u^{\mu}=\frac{\mathrm{d}x^{\mu}}{\mathrm{d}\tau}
=(\gamma c,\gamma v).
$$

其 Minkowski 范数满足

$$
u^{\mu}u_{\mu}
=-c^{2}\gamma^{2}+v^{2}\gamma^{2}
=-c^{2}.
$$

令

$$
v_{\mathrm{ext}}:=v,\qquad
v_{\mathrm{int}}:=c\sqrt{1-\frac{v^{2}}{c^{2}}}.
$$

则

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}
=v^{2}+c^{2}\left(1-\frac{v^{2}}{c^{2}}\right)
=c^{2}.
$$

另一方面，由时间膨胀

$$
\frac{\mathrm{d}\tau}{\mathrm{d}t}
=\sqrt{1-\frac{v^{2}}{c^{2}}}
=\frac{v_{\mathrm{int}}}{c},
$$

可见 $\mathrm{d}\tau/\mathrm{d}t$ 与 $v_{\mathrm{int}}$ 之间的关系正是信息速率圆的径向投影。因此，Minkowski 四速度恒等式与信息速率圆只是对同一约束的不同参数化。这即定理 3.1。

### 4.2 定理 3.2 的证明：频率的 Minkowski 几何

能量–动量关系

$$
E^{2}=m_{0}^{2}c^{4}+p^{2}c^{2}
$$

两侧除以 $\hbar^{2}$，得

$$
\left(\frac{E}{\hbar}\right)^{2}
=\left(\frac{m_{0}c^{2}}{\hbar}\right)^{2}
+\left(\frac{pc}{\hbar}\right)^{2}.
$$

令

$$
\omega_{\mathrm{tot}}:=\frac{E}{\hbar},\quad
\omega_{0}:=\frac{m_{0}c^{2}}{\hbar},\quad
\omega_{\mathrm{space}}:=\frac{pc}{\hbar},
$$

即得

$$
\omega_{\mathrm{tot}}^{2}
=\omega_{0}^{2}+\omega_{\mathrm{space}}^{2}.
$$

另一方面，速度可写为

$$
v = \frac{\partial E}{\partial p}
=\frac{pc^{2}}{E}
=\frac{\omega_{\mathrm{space}}c^{2}/c}{\omega_{\mathrm{tot}}}
=c\frac{\omega_{\mathrm{space}}}{\omega_{\mathrm{tot}}}.
$$

故 $\beta=v/c=\omega_{\mathrm{space}}/\omega_{\mathrm{tot}}$。由此得

$$
\gamma=\frac{1}{\sqrt{1-\beta^{2}}}
=\frac{\omega_{\mathrm{tot}}}{\omega_{0}},
$$

从而

$$
\omega_{\mathrm{tot}}=\gamma \omega_{0}.
$$

将时间膨胀写为 $\mathrm{d}\tau/\mathrm{d}t=1/\gamma$，内部时钟频率

$$
\omega_{\mathrm{clock}}=\omega_{0}\frac{\mathrm{d}\tau}{\mathrm{d}t}
=\frac{\omega_{0}}{\gamma}
$$

显然满足

$$
\omega_{\mathrm{clock}}\cdot \omega_{\mathrm{tot}}
=\left(\frac{\omega_{0}}{\gamma}\right)\cdot(\gamma \omega_{0})
=\omega_{0}^{2}.
$$

定理 3.2 由此得到。

### 4.3 定理 3.3 的证明：相对论动力学与内部速率重写

沿速度方向的相对论力学给出

$$
F_{\parallel}=\frac{\mathrm{d}}{\mathrm{d}t}(\gamma m_{0}v)
=m_{0}\gamma^{3}a_{\parallel},
$$

这是标准教科书结论。引入

$$
m_{\mathrm{eff}}^{\parallel}:=\gamma^{3}m_{0},
$$

则有

$$
F_{\parallel}=m_{\mathrm{eff}}^{\parallel}a_{\parallel}.
$$

利用

$$
v_{\mathrm{int}}
=c\sqrt{1-\frac{v^{2}}{c^{2}}}
=\frac{c}{\gamma},
$$

可得

$$
\gamma=\frac{c}{v_{\mathrm{int}}},\quad
\gamma^{3}=\left(\frac{c}{v_{\mathrm{int}}}\right)^{3},
$$

从而

$$
m_{\mathrm{eff}}^{\parallel}
=\gamma^{3}m_{0}
=m_{0}\left(\frac{c}{v_{\mathrm{int}}}\right)^{3}.
$$

当 $v\to c$ 时，$v_{\mathrm{int}}\to 0$，由上式直接看出 $m_{\mathrm{eff}}^{\parallel}$ 发散，即定理 3.3。

### 4.4 定理 3.4 的证明：能量–内部速率–频率的三重恒等

由时间膨胀

$$
\frac{\mathrm{d}t}{\mathrm{d}\tau}=\gamma
$$

与

$$
E_{\mathrm{tot}}=\gamma m_{0}c^{2}
$$

可视作

$$
E_{\mathrm{tot}}
= m_{0}c^{2}\frac{\mathrm{d}t}{\mathrm{d}\tau}.
$$

另一方面，由 $v_{\mathrm{int}}=c/\gamma$ 有

$$
\frac{\mathrm{d}t}{\mathrm{d}\tau}
=\frac{c}{v_{\mathrm{int}}},
$$

代入得到

$$
E_{\mathrm{tot}}
=m_{0}c^{2}\frac{c}{v_{\mathrm{int}}}
=\frac{m_{0}c^{3}}{v_{\mathrm{int}}}.
$$

再由普朗克关系

$$
E_{\mathrm{tot}}=\hbar \omega_{\mathrm{tot}},
$$

以及 $\omega_{0}=m_{0}c^{2}/\hbar$ 与 $\gamma=c/v_{\mathrm{int}}$，即可写成

$$
\omega_{\mathrm{tot}}
=\frac{E_{\mathrm{tot}}}{\hbar}
=\frac{m_{0}c^{3}}{\hbar v_{\mathrm{int}}}
=\frac{c}{v_{\mathrm{int}}}\frac{m_{0}c^{2}}{\hbar}
=\gamma \omega_{0},
$$

与定理 3.2 一致，从而完成能量–内部速率–频率三重恒等的闭环。

---

## 5. Model Apply

本节讨论信息速率圆与惯性几何在具体物理情景中的应用。

### 5.1 康普顿钟与物质波时钟实验的几何解读

近期一类重要实验利用原子干涉仪与频率梳，将物质波的康普顿频率视为时间标准，实现了"以质量计时"的方案，即所谓"康普顿频率钟"或"物质波钟"。这些实验表明，质量 $m$ 可以通过频率 $\omega_{0}=m c^{2}/\hbar$ 高精度测量，且该频率在不同速度下遵循相对论性时间膨胀修正。

在信息速率几何中：

* 静止原子对应 $v_{\mathrm{ext}}=0$，$v_{\mathrm{int}}=c$，内部时钟频率即 $\omega_{\mathrm{clock}}=\omega_{0}$；

* 当原子以速度 $v$ 运动时，内部时钟频率降为 $\omega_{\mathrm{clock}}=\omega_{0}/\gamma$，表现为干涉条纹相位随时间的变化变慢；

* 同时，物质波总频率 $\omega_{\mathrm{tot}}=\gamma \omega_{0}$ 增大，其空间频率 $\omega_{\mathrm{space}}=pc/\hbar$ 由动量决定。

干涉仪实际测量的相位差可以被视为 $\omega_{\mathrm{tot}}$ 与 $\omega_{\mathrm{clock}}$ 的适当组合，而信息速率圆提供了两者之间的几何约束，使得不同实验配置下的结果可以统一地投影到 $(v_{\mathrm{ext}},v_{\mathrm{int}})$ 平面中。

### 5.2 Dirac–QCA 中质量参数的几何意义

在一维 Dirac–QCA 模型中，局域更新可以写成"内部旋转"角度 $\theta$ 与条件平移的组合，而连续极限中的有效质量由 $\theta$ 决定，例如

$$
m_{0}c^{2} \propto \frac{\hbar}{\Delta t}\sin\theta.
$$

平面波模态的色散关系通常为

$$
\cos(\omega \Delta t)
=\cos\theta\cos(k\Delta x)+\cdots.
$$

在小 $k$ 极限下，这一色散收敛到

$$
\omega^{2}
\approx \left(\frac{m_{0}c^{2}}{\hbar}\right)^{2}
+c^{2}k^{2},
$$

即 $\omega_{\mathrm{tot}}^{2}=\omega_{0}^{2}+\omega_{\mathrm{space}}^{2}$。

在信息速率圆的语言中，$\theta$ 控制了内部旋转与外部位移之间的"耦合角"：

* 当 $\theta$ 接近 $0$ 时，质量趋近于零，模态主要以 $v_{\mathrm{ext}}\approx c$ 传播，$v_{\mathrm{int}}\approx 0$，对应近似无质量粒子；

* 当 $\theta$ 接近 $\pi/2$ 时，质量极大，模态在空间上几乎不传播，$v_{\mathrm{ext}}\approx 0$，$v_{\mathrm{int}}\approx c$，对应高度局域的重粒子；

* 中间情况则对应在信息速率圆上不同倾角的组合。

这给出了质量作为"信息速率分配规则"的几何解释：质量越大，系统越倾向于将资源用于内部演化而非外部传播。

### 5.3 相对论性质量图像的重新表述

传统"相对论性质量"语言将 $\gamma m_{0}$ 视为"运动质量"，虽在形式上方便，却容易引发"物体变重"的误解，并与现代强调不变量质量的习惯不符。

在信息速率几何中，可以用如下三元组替代"质量增加"的叙述：

1. 不变量质量 $m_{0}$ 是粒子身份的拓扑标记，对应静止康普顿频率 $\omega_{0}$；

2. 运动状态仅改变 $(v_{\mathrm{ext}},v_{\mathrm{int}})$ 在信息速率圆上的分配，使得内部时钟频率 $\omega_{\mathrm{clock}}=\omega_{0}v_{\mathrm{int}}/c$ 红移，总频率 $\omega_{\mathrm{tot}}=\gamma \omega_{0}$ 蓝移；

3. 有效惯性 $m_{\mathrm{eff}}^{\parallel}=\gamma^{3}m_{0}$ 则是外力–加速度关系的参数，其增长反映的是"内部时间速率变小后，系统对外扰动的响应刚度上升"。

这种表述避免了"质量真的变大"的直观误导，而强调惯性是内部时间几何的一种 emergent 特性。

---

## 6. Engineering Proposals

本节提出若干可以检验或利用信息速率几何的工程与实验方案。

### 6.1 物质波钟中分离测量 $\omega_{\mathrm{clock}}$ 与 $\omega_{\mathrm{tot}}$

原子干涉实验已经能够以极高精度测量与质量相关的康普顿频率以及与运动状态相关的相位偏移。在信息速率几何中，$\omega_{\mathrm{clock}}$ 与 $\omega_{\mathrm{tot}}$ 的乘积 $\omega_{\mathrm{clock}}\omega_{\mathrm{tot}}=\omega_{0}^{2}$ 是一个独特的预测：

* 通过比较静止与运动原子的干涉条纹漂移，可以提取 $\omega_{\mathrm{clock}}$ 的实验室时间频率；

* 利用能量–频率关系与动量控制，可以独立测定 $\omega_{\mathrm{tot}}$；

* 若能在同一实验平台上同时获得两者，并验证其乘积在不同速度下保持近似常数，即为对信息速率几何的一种间接支持。

任何偏离这一关系的系统性效应，都可能指向 QCA 离散结构的修正项或引力效应。

### 6.2 QCA 量子模拟中的信息速率断点

在可控量子平台（超导量子比特、囚禁离子、光格原子等）上实现 Dirac–QCA 或相关量子行走模型已成为量子模拟的一个方向。通过调节内部旋转角度与步长，可以扫描从近光速传播到高度局域的不同模式。

在信息速率几何下，可以设计以下实验：

1. 选取一族参数，使得有效群速度 $v_{\mathrm{ext}}$ 接近最大值，观测态矢在内部自由度上的演化速率（如 Bloch 球上的旋转频率）是否显著下降；

2. 在不同参数下测量同一初态演化至正交态所需最短时间，并与量子速度极限 $t_{\perp}\geq \pi\hbar/(2\Delta E)$ 对比，以检验"内部速率上界 $c$"与能量散度之间的标度关系；

3. 探索在接近"内部速率冻结"的极端参数处，是否出现数值上类似惯性放大的动力学行为。

这些实验可以在封闭系统中直接观察信息速率在内外自由度之间的分配，从而为本文的几何图像提供微观支撑。

### 6.3 高速束流中的"惯性几何"校准

在高能加速器中，带电粒子束团在接近光速时表现出典型的相对论性动力学，传统分析关注 $\gamma$ 因子的能量与动量标度。若在同一装置中引入精密的自旋进动或内部态干涉测量，则有机会同时测量：

* 对应 $\omega_{\mathrm{tot}}=\gamma \omega_{0}$ 的能量频率；

* 对应 $\omega_{\mathrm{clock}}=\omega_{0}/\gamma$ 的内部时钟频率（如通过拉比振荡周期或自旋回波）。

通过在不同 $\gamma$ 区间拟合这两类频率的标度关系，可以显式重建信息速率圆上的 $(v_{\mathrm{ext}},v_{\mathrm{int}})$ 曲线，检验其是否与 $v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}$ 一致，及在极高 $\gamma$ 区间是否出现偏离。

---

## 7. Discussion (risks, boundaries, past work)

### 7.1 与既有"内部时钟"与 Zitterbewegung 图像的关系

de Broglie 早期就提出"粒子携带内部时钟"的思想，将质量解释为内部振荡频率 $\omega_{0}=m c^{2}/\hbar$。这一图像在 Hestenes 等人的 Zitterbewegung 解释中得到深化，将 Dirac 电子视为带有内部旋转与螺旋轨道的结构体，质量与自旋源自内部周期运动。

本文的惯性几何框架在精神上与这些工作相近：

* 均将质量视为某种内部周期性的尺度；

* 均强调内部时间流逝与外部运动之间的深层联系。

不同之处在于：

1. 本文不对内部运动的具体空间轨迹作几何假设（如 helical 模型），而是通过 Fubini–Study 度规与量子速度极限，将内部"演化速度"抽象为态空间中的几何量；

2. 我们强调外部运动与内部演化之间的资源守恒关系 $v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}$，并将惯性发散解释为"内部时间速率趋零"的极限，而非特定力学模型中的不稳定行为。

因此，信息速率圆可以被视为对"内部时钟"思想的一种几何与信息论升级。

### 7.2 与"相对论性质量"争论的关系

现代教科书往往主张弃用"相对论性质量"，转而强调不变量质量与能量–动量四矢。然而，在教学与直观理解中，"高速运动阻力增加"仍然是一个极具感知性的事实。

信息速率几何在这场争论中的位置可以概括为：

* 数学上完全遵守不变量质量与四动量形式主义，不引入新质量参数；

* 概念上引入"有效惯性" $m_{\mathrm{eff}}^{\parallel}=\gamma^{3}m_{0}$ 作为外力–加速度关系中的系数，但明确指出它并非物体"本身的质量"，而是内部时间速率 $v_{\mathrm{int}}$ 的函数；

* 因此，所谓"变重"不过是"内部时间被挤压，导致响应刚度上升"的几何-信息现象。

这种视角在不改变任何实验预言的前提下，为"相对论性质量"的概念清理提供了一个新的折中方案。

### 7.3 QCA 与离散结构的可检验偏离

本文将信息速率圆公理化地引入，并以 Dirac–QCA 作为底层示意模型。真实宇宙是否在普朗克尺度上由 QCA 或其它离散结构支撑，目前尚无共识。

这一框架的保守版本仅被视为对现有连续理论的几何重写，在可检验尺度内不引入任何新预言；而其激进版本则允许在极高能或极短距上，信息速率圆出现微小偏离，例如

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}
=c^{2}\bigl(1+\varepsilon(p,\Lambda_{\mathrm{QCA}})\bigr),
$$

其中 $\Lambda_{\mathrm{QCA}}$ 是离散格点尺度，$\varepsilon$ 为随动量增加而增长的微小函数。这类偏离可能在超高能宇宙线、引力波传播或精密时钟实验中被放大。

本文未在具体模型中量化这些偏离，而是提供了一个可供嵌入的几何骨架，后续工作可结合具体 QCA 构造与实验约束加以填充。

### 7.4 边界与潜在风险

* 本文假设内部演化速率可以通过 Fubini–Study 度规与能量不确定度线性关联，并将其标度至 $c$。这一标度的唯一性与普适性尚需更精确的公理化讨论与实验校准。

* 频率与时间速率均为观测者依赖量，本文采用单一惯性系中的信息速率圆表述，尚未在一般协变框架下给出完整的张量化表述。

* 在强引力场或非惯性系中，时间膨胀与引力红移耦合，信息速率圆的推广应涉及有效光学度规与局域惯性系下的分解，这是更广义的"引力–信息几何"课题。

---

## 8. Conclusion

本文在量子元胞自动机与量子演化几何背景下，引入"信息速率守恒"这一结构，将一粒有质量粒子的演化视为在外部空间位移与内部态演化两个正交维度之间分配有限的信息更新速率。通过定义信息速率圆

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2},
$$

并将 $v_{\mathrm{ext}}$ 与群速度、$v_{\mathrm{int}}$ 与固有时间流逝速率关联，本文实现了以下统一：

1. 时间膨胀被重写为信息速率在内外两个分量之间的几何投影，Minkowski 四速度的超双曲结构对应到二维圆上的简单约束；

2. 静止康普顿频率 $\omega_{0}$、物质波总频率 $\omega_{\mathrm{tot}}$ 与空间频率 $\omega_{\mathrm{space}}$ 之间的关系 $\omega_{\mathrm{tot}}^{2}=\omega_{0}^{2}+\omega_{\mathrm{space}}^{2}$ 被解释为频率空间中的"惯性几何"，内部时钟频率 $\omega_{\mathrm{clock}}=\omega_{0}/\gamma$ 与总频率 $\omega_{\mathrm{tot}}=\gamma \omega_{0}$ 之间的互补性消解了"时间变慢却频率变快"的直觉矛盾；

3. 相对论动力学中的有效惯性 $m_{\mathrm{eff}}^{\parallel}=\gamma^{3}m_{0}$ 被重写为 $m_{\mathrm{eff}}^{\parallel}=m_{0}(c/v_{\mathrm{int}})^{3}$，从而将惯性发散解释为"内部时间冻结极限下维持拓扑结构的能量成本"；

4. 结合康普顿钟实验、物质波干涉与 QCA 量子模拟，提出了一系列可用于检验或利用惯性几何图像的工程方案。

在这一框架下，$E=m c^{2}$ 与 $E=\hbar \omega$ 不再是来自两个理论体系的独立公式，而是同一信息几何结构在不同变量下的投影。质量是康普顿频率的拓扑标签，时间膨胀是信息速率的再分配，惯性则是内部时间几何对外部扰动的响应刚度。

---

## Acknowledgements

作者感谢有关相对论质量、康普顿时钟与量子元胞自动机的公开文献与实验结果，为本文提供了必要的历史与技术背景。

## Code Availability

本文全部推导基于解析计算与标准相对论、量子力学工具，不依赖数值模拟代码。若需数值验证与符号推导，常用代数软件即可实现。

---

## References

1. L. de Broglie, *Recherches sur la théorie des quanta*, Ann. Phys. (1924).

2. A. Bisio, G. M. D'Ariano, A. Tosini, "Quantum field as a quantum cellular automaton: the Dirac free evolution in one dimension," *Ann. Phys.* **354**, 244–264 (2015).

3. R. P. Feynman, "The Feynman checkerboard," 见例如 GN Ord, "The Feynman chessboard model in 3+1 dimensions," *Front. Phys.* (2023).

4. "Energy–momentum relation," *Wikipedia*.

5. J. Anandan, Y. Aharonov, "Geometry of quantum evolution," *Phys. Rev. Lett.* **65**, 1697–1700 (1990).

6. "Quantum speed limit," *Wikipedia*.

7. S.-Y. Lan et al., "A Clock Directly Linking Time to a Particle's Mass," *Science* **339**, 554–557 (2013).

8. V. Venugopal, "de Broglie Wavelength and Frequency of Scattered Electrons in the Compton Effect," arXiv:1202.4572 (2012).

9. D. Hestenes, "Zitterbewegung Modeling," (2005); 以及 "Quantum mechanics of the electron particle clock," arXiv:1910.10478 (2019).

10. G. R. Osche et al., "Electron channeling resonance and de Broglie's internal clock," *Ann. Fond. Louis de Broglie* **36** (2011).

11. F. Hecht, "Einstein Never Approved of Relativistic Mass," *Phys. Teach.* **47**, 336–341 (2009).

12. P. M. Brown, "On the concept of mass in relativity," arXiv:0709.0687 (2007).

13. H. Müller, "Matter wave clocks," 相关讲座与综述。

14. Ma, H., "Universal Conservation of Information Celerity," preprint (2025).

---

## 附录 A：Dirac–QCA 哈密顿量与频率正交性的算符证明

本附录给出定理 3.2 中频率正交关系的算符形式证明，并展示其与 Dirac–QCA 有效哈密顿量之间的联系。

### A.1 Dirac 哈密顿量的平方与能量–动量关系

考虑一维 Dirac 型哈密顿量

$$
H = c \alpha \hat{p} + \beta m_{0}c^{2},
$$

其中 $\alpha,\beta$ 为 $2\times 2$ 泡利矩阵，满足

$$
\alpha^{2}=\beta^{2}=\mathbb{I},\qquad
\{\alpha,\beta\}=\alpha\beta+\beta\alpha=0.
$$

计算 $H^{2}$：

$$
\begin{aligned}
H^{2}
&= c^{2}\alpha \hat{p}\cdot\alpha \hat{p}
+ c\alpha \hat{p}\cdot\beta m_{0}c^{2}
+ \beta m_{0}c^{2}\cdot c \alpha \hat{p}
+ \beta^{2}m_{0}^{2}c^{4} \\
&= c^{2}\alpha^{2} \hat{p}^{2}
+ c m_{0}c^{2}\hat{p}\left(\alpha\beta+\beta\alpha\right)
+ \beta^{2}m_{0}^{2}c^{4}.
\end{aligned}
$$

利用 $\alpha^{2}=\beta^{2}=\mathbb{I}$ 与 $\{\alpha,\beta\}=0$，中间交叉项完全抵消，得到

$$
H^{2}
= c^{2}\hat{p}^{2}+m_{0}^{2}c^{4}.
$$

在动量本征态 $\hat{p}\psi_{p}=p\psi_{p}$ 上，$H^{2}\psi_{p}=E^{2}\psi_{p}$，由此得到

$$
E^{2}=c^{2}p^{2}+m_{0}^{2}c^{4},
$$

即标准能量–动量关系。这一推导在 Dirac–QCA 的连续极限中保持有效，因为 QCA 的一步演化算符 $U$ 满足 $U=\exp(-\mathrm{i}H\Delta t/\hbar)$ 的有效表示。

### A.2 频率正交关系

将上式两侧除以 $\hbar^{2}$，得

$$
\left(\frac{E}{\hbar}\right)^{2}
=\left(\frac{m_{0}c^{2}}{\hbar}\right)^{2}
+\left(\frac{pc}{\hbar}\right)^{2}.
$$

令

$$
\omega_{\mathrm{tot}}:=\frac{E}{\hbar},\quad
\omega_{0}:=\frac{m_{0}c^{2}}{\hbar},\quad
\omega_{\mathrm{space}}:=\frac{pc}{\hbar},
$$

即可得到

$$
\omega_{\mathrm{tot}}^{2}
=\omega_{0}^{2}+\omega_{\mathrm{space}}^{2},
$$

这正是频率空间中的"勾股关系"。它体现了哈密顿量中"质量项"与"动量项"在算符层面上的正交性：反对易关系保证了 $H^{2}$ 中不出现交叉项，从而保留了直角三角形的代数结构。

### A.3 与信息速率几何的对应

在信息速率圆中，$v_{\mathrm{ext}}$ 与 $v_{\mathrm{int}}$ 满足

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}.
$$

通过能量–动量关系，可以将速度与频率联系起来：

$$
v=c\frac{\omega_{\mathrm{space}}}{\omega_{\mathrm{tot}}},\quad
\gamma=\frac{\omega_{\mathrm{tot}}}{\omega_{0}},\quad
v_{\mathrm{int}}=c\sqrt{1-\frac{v^{2}}{c^{2}}}
=\frac{c}{\gamma}
=c\frac{\omega_{0}}{\omega_{\mathrm{tot}}}.
$$

因此

$$
\left(\frac{v_{\mathrm{ext}}}{c}\right)^{2}
=\left(\frac{\omega_{\mathrm{space}}}{\omega_{\mathrm{tot}}}\right)^{2},\quad
\left(\frac{v_{\mathrm{int}}}{c}\right)^{2}
=\left(\frac{\omega_{0}}{\omega_{\mathrm{tot}}}\right)^{2}.
$$

这说明，信息速率圆在速度空间中的几何结构，与频率空间中 $\omega_{0}$ 与 $\omega_{\mathrm{space}}$ 的正交关系完全平行，进一步支持了"惯性几何"作为统一描述的合理性。

---

## 附录 B：纵向有效惯性的详细推导

本附录对 $F_{\parallel}=m_{0}\gamma^{3}a_{\parallel}$ 的推导进行详细展开，并给出其在信息速率变量中的重写。

### B.1 相对论动量与加速度分解

相对论动量定义为

$$
\mathbf{p}=\gamma m_{0}\mathbf{v}.
$$

沿速度方向的加速度

$$
a_{\parallel}
:=\frac{\mathrm{d}v}{\mathrm{d}t},
$$

施加的力

$$
F_{\parallel}
:=\frac{\mathrm{d}p}{\mathrm{d}t}.
$$

计算

$$
\begin{aligned}
F_{\parallel}
&=\frac{\mathrm{d}}{\mathrm{d}t}(\gamma m_{0}v) \\
&= m_{0}\left(\gamma \frac{\mathrm{d}v}{\mathrm{d}t}
+v\frac{\mathrm{d}\gamma}{\mathrm{d}t}\right).
\end{aligned}
$$

由

$$
\gamma=\frac{1}{\sqrt{1-\beta^{2}}},\quad \beta=\frac{v}{c}
$$

得

$$
\frac{\mathrm{d}\gamma}{\mathrm{d}t}
=\frac{\mathrm{d}\gamma}{\mathrm{d}\beta}\frac{\mathrm{d}\beta}{\mathrm{d}t}
=\frac{\beta \gamma^{3}}{c}\frac{\mathrm{d}v}{\mathrm{d}t}
=\frac{\gamma^{3}v}{c^{2}}a_{\parallel}.
$$

代入

$$
F_{\parallel}
=m_{0}\left(\gamma a_{\parallel}
+v\frac{\gamma^{3}v}{c^{2}}a_{\parallel}\right)
=m_{0}\left(\gamma+\gamma^{3}\frac{v^{2}}{c^{2}}\right)a_{\parallel}.
$$

利用

$$
\gamma^{2}=\frac{1}{1-\beta^{2}}
\Rightarrow \gamma^{2}-1=\frac{\beta^{2}}{1-\beta^{2}}=\gamma^{2}\frac{v^{2}}{c^{2}},
$$

即

$$
\gamma^{2}\frac{v^{2}}{c^{2}}=\gamma^{2}-1,
$$

则

$$
\gamma+\gamma^{3}\frac{v^{2}}{c^{2}}
=\gamma+\gamma(\gamma^{2}-1)
=\gamma^{3}.
$$

于是

$$
F_{\parallel}=m_{0}\gamma^{3}a_{\parallel},
$$

这就是纵向有效惯性质量 $m_{\mathrm{eff}}^{\parallel}=\gamma^{3}m_{0}$ 的来源。

### B.2 用内部速率 $v_{\mathrm{int}}$ 重写

信息速率圆给出

$$
v_{\mathrm{int}}
=c\sqrt{1-\frac{v^{2}}{c^{2}}}
=\frac{c}{\gamma},
$$

故

$$
\gamma=\frac{c}{v_{\mathrm{int}}},\quad
\gamma^{3}=\left(\frac{c}{v_{\mathrm{int}}}\right)^{3}.
$$

从而

$$
m_{\mathrm{eff}}^{\parallel}
=\gamma^{3}m_{0}
=m_{0}\left(\frac{c}{v_{\mathrm{int}}}\right)^{3}.
$$

这显示了 $m_{\mathrm{eff}}^{\parallel}$ 对内部速率 $v_{\mathrm{int}}$ 的敏感依赖：当 $v_{\mathrm{int}}$ 因高外部速度而减小时，有效惯性以立方的方式快速增长。

在信息几何图像中，这意味着：

* 有效惯性大并不表示"物质增多"，而是表示内部时间流逝被压缩至极低速率，使得任何改变其外部运动状态的尝试都必须"撬动"一个内部几乎冻结的结构，因此显得极其困难。

---

## 附录 C：内部演化速度与 Fubini–Study 度规

本附录说明如何将内部速度 $v_{\mathrm{int}}$ 与量子态空间中的演化速度联系起来，并讨论其与量子速度极限之间的关系。

### C.1 Fubini–Study 演化速度

在射影 Hilbert 空间 $\mathbb{P}(\mathcal{H})$ 中，态矢 $|\psi(t)\rangle$ 的无关总体相位演化可由 Fubini–Study 线元

$$
\mathrm{d}s^{2}
=4\left(1-|\langle\psi(t)|\psi(t+\mathrm{d}t)\rangle|^{2}\right)
$$

刻画。Anandan–Aharonov 证明，对于由哈密顿量 $H$ 驱动的演化，演化"速度"满足

$$
\frac{\mathrm{d}s}{\mathrm{d}t}
=\frac{2}{\hbar}\Delta H,
$$

其中 $\Delta H=\sqrt{\langle H^{2}\rangle-\langle H\rangle^{2}}$ 为能量不确定度。这一关系说明：在给定能量色散资源下，态在 $\mathbb{P}(\mathcal{H})$ 中的几何演化速率受限。当系统接近量子速度极限时，其演化速度接近 $2\Delta H/\hbar$。

### C.2 内部速度的标度与饱和

对于自由 Dirac 粒子的单粒子扇区，可以将整体 Hilbert 空间拆分为"外部"（位置）与"内部"（自旋/粒子–反粒子）两部分自由度。在高对称情况下，可期望能量不确定度主要由内部结构决定，而群速度则与外部动量相关。

于是可以定义内部演化速度

$$
v_{\mathrm{int}}
:=\ell_{\mathrm{int}}\frac{\mathrm{d}s}{\mathrm{d}t}
=\ell_{\mathrm{int}}\frac{2}{\hbar}\Delta H_{\mathrm{int}},
$$

其中 $\ell_{\mathrm{int}}$ 为一固定长度标度，用以将无量纲的几何速度转化为具有速度量纲的量。选择 $\ell_{\mathrm{int}}$ 使得静止时

$$
v_{\mathrm{int}}(v=0)=c,
$$

即可在内部演化速度与信息速率圆中的 $v_{\mathrm{int}}$ 之间建立一一对应。在连续极限下，Dirac–QCA 自然提供了这样的长度与时间单位（格点间距与步长），因此可以将内部演化速度视为"每一步内部态变化所跨越的 Fubini–Study 距离"与步长之比。

当系统能量完全由静止质量贡献时，内部演化接近量子速度极限，$v_{\mathrm{int}}\approx c$；当系统的大部分能量转化为外部动量时，内部演化速度下降，$v_{\mathrm{int}}<c$，对应信息速率圆上的偏转。

### C.3 量子速度极限与信息速率上界

量子速度极限给出从一态演化到正交态所需的最短时间

$$
t_{\perp}\geq\max\left(\frac{\pi\hbar}{2\Delta E},\frac{\pi\hbar}{2\bar{E}}\right),
$$

其中 $\Delta E$ 与 $\bar{E}$ 分别为能量不确定度与平均能量。若将内部自由度视为主要负责态正交变化的子系统，则内部演化速度 $v_{\mathrm{int}}$ 的上界可视为量子速度极限的几何体现。

信息速率圆假定 $v_{\mathrm{int}}\leq c$ 为绝对上界，且在静止时饱和这一界。这一假设与量子速度极限概念在形式上相容：

* 静止粒子内部演化接近极快，能在最短时间内完成态的区分；

* 运动粒子将部分"速度预算"分配给外部位移，从而内部演化变慢，对应于更长的态正交时间。

这一图像为信息速率圆提供了一个自然的量子信息学背景，也指出了未来可以通过更精细的量子速度极限实验来进一步检验这一框架。

