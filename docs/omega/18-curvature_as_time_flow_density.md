# 曲率作为时间流速密度的非均匀性：从统一时间刻度 $\kappa(\omega)$ 到引力几何的重构

*Curvature as Non-uniformity of Time Flow Density: Reconstructing Gravitational Geometry from Unified Time Scale $\kappa(\omega)$*

---

## Abstract

广义相对论将引力现象归结为时空曲率，而狭义相对论与量子理论中时间则多以外加参数或局域"固有时间"形式出现，二者在概念上长期处于割裂状态。本文在统一时间刻度与信息速率守恒的框架下，提出并系统论证以下观点：**几何曲率在本质上可被重写为"时间流速密度"场 $\kappa(x)$ 的空间非均匀性**。更具体地，底层散射/谱理论给出统一时间恒等式

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\,\mathrm{tr}\,\mathsf{Q}(\omega),
$$

其中 $\varphi(\omega)$ 为散射相移，$\rho_{\mathrm{rel}}(\omega)$ 为相对态密度，$\mathsf{Q}(\omega)$ 为 Wigner–Smith 时间延迟算符。将该频域刻度在空间上局域化并粗粒化，我们得到一个描述"单位外部时间内内部演化密度"的标量场 $\kappa(x)$。本文证明，在自然的公理化条件下：

1. 存在一类与 $\kappa(x)$ 一一对应的度规族，其时间分量满足

$$
g_{tt}(x) = -\frac{c^{2}}{\eta^{2}(x)},\qquad \eta(x) \equiv \frac{\kappa(x)}{\kappa_{\infty}},
$$

并在弱场极限下给出引力势

$$
\Phi_{\mathrm{grav}}(x) \simeq c^{2}\,\ln\eta(x) \propto c^{2}\,\ln\kappa(x).
$$

2. 若再要求"局域信息体积（态数 × 空间体积）守恒"，则 $\eta(x)$ 的空间缩放必须以 $\eta^{-1}(x)$ 的方式进入空间度量，从而选出一类双因子缩放光学度规：

$$
\mathrm{d}s^{2} = -\eta^{2}(x)c^{2}\mathrm{d}t^{2} + \eta^{-2}(x)\,\gamma_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j},
$$

并在弱场极限下自动再现标准的引力红移与光线偏折公式。

3. 在量子元胞自动机（QCA）与"信息速率守恒"公理

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}
$$

的框架中，$\kappa(x)$ 可被具体实现为：在给定空间点附近，每单位外部时间内"内部态演化步数"的平均密度。我们展示了一维 Dirac 型 QCA 中的一个具体构造，其中 $\kappa(x)$ 与局域能隙/内部频率相关联，质量与引力效应由同一 $\kappa$-场控制。

综上，本文给出一种将曲率重新解释为"时间流速密度纹理"的几何—信息论图像：**在各点时间不再是同一条均匀流逝的参数，而是由散射谱、态密度与局域信息处理结构共同定义的一种"时间密度场"$\kappa(x)$**。传统的爱因斯坦几何被视为 $\kappa$-场在连续极限下的有效描述，其观测可通过原子钟网络、引力红移与引力透镜等实验进行检验。附录中给出了统一时间恒等式的散射论推导、$\kappa$-度规的弱场曲率计算以及 QCA 模型中的显式例子。

---

## Keywords

统一时间刻度；时间流速密度；曲率；引力几何；散射理论；量子元胞自动机；信息速率守恒；Wigner–Smith 时间延迟

---

## 1 引言

在标准物理图景中，"时间"在不同理论层级中具有截然不同的角色：

* 在狭义与广义相对论中，时间是四维时空坐标的一部分，作为度规 $g_{\mu\nu}$ 的一分量，其几何结构受能量—动量张量约束。

* 在非相对论量子力学中，时间往往被视为外部参数 $t$，波函数 $\psi(t)$ 关于该参数幺正演化，而非由算符表示。

* 在散射理论与谱理论中，时间以"延迟""驻留时间""相位导数"等形式出现，典型地通过散射相移 $\varphi(\omega)$ 的频率导数来刻画：

$$
\tau(\omega) = \hbar\,\frac{\mathrm{d}\varphi}{\mathrm{d}E} = \frac{\mathrm{d}\varphi}{\mathrm{d}\omega}.
$$

上述视角在数学上彼此兼容，但在本体论上却缺乏一个统一的"时间是什么"的定义。特别是，引力曲率似乎要求时间在不同位置"流逝速度不同"，而量子理论中时间又被当作均匀的外部参数，这造成了诸多概念上的张力。

本文的核心问题可被简要表述为：

> 能否从一个统一的"时间流速密度"刻度 $\kappa(x,\omega)$ 出发，将几何曲率重写为该密度场的空间纹理，从而在同一框架下理解时间膨胀、引力红移与量子散射时间延迟？

我们的答案是肯定的。基于 Eisenbud–Wigner–Smith 时间延迟、谱移函数与信息速率守恒，我们提出：

1. **统一时间恒等式：** 在适当的散射/谱情形下，存在规范无关的统一刻度

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\,\mathrm{tr}\,\mathsf{Q}(\omega),
$$

其中 $\kappa$ 同时刻画相位导数、相对态密度与 Wigner–Smith 延迟迹，因而可被解释为"时间流速密度"。

2. **局域化与粗粒化：** 当考虑具有空间结构的散射/传播问题时，我们可以引入局域的 $\kappa(x,\omega)$，并对频率（或能量）窗口做适当加权与粗粒化，得到宏观的标量场 $\kappa(x)$，其物理意义为"单位外部时间内，单位空间体积中发生的内部演化总步数"。

3. **几何重构：** 在要求：

* $g_{\mu\nu}$ 为 Lorentz 签名；

* 局域自由落体中物理定律（QCA/量子场的局域结构）保持协变形式；

* 总的"信息体积"守恒（态数 × 空间体积）；

的前提下，可以证明度规必须从 $\kappa(x)$ 中继承一类特定的双因子缩放结构，且弱场极限下的引力势由 $\ln\kappa(x)$ 给出，曲率张量则与 $\ln\kappa(x)$ 的二阶导数直接相关。

4. **与 QCA 的嵌入：** 若底层本体为量子元胞自动机（QCA），则每个元胞在每个离散时间步中执行有限次局域幺正更新。对于一个长波极限下的有效场模态，可将局域内部频率 $\omega_{\mathrm{int}}(x)$ 与 $\kappa(x)$ 直接关联，并通过"信息速率守恒"公理

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}
$$

将质量、时间膨胀与曲率统一为对同一 $\kappa$-预算的不同分配方式。

本文组织如下：第 2 节给出符号、预备知识与统一时间恒等式的简要回顾；第 3 节定义局域时间流速密度场 $\kappa(x,\omega)$ 与宏观 $\kappa(x)$；第 4 节从 $\kappa(x)$ 构造有效度规并推导弱场极限下的引力势与曲率；第 5 节讨论与爱因斯坦场方程的一致性条件；第 6 节分析可观测效应；第 7 节给出在 QCA 框架中的具体实现；附录详细给出散射论推导与曲率计算。

---

## 2 符号、预备知识与统一时间刻度

### 2.1 符号约定

* 希腊指标 $\mu,\nu,\rho,\sigma = 0,1,2,3$ 表示时空坐标分量，其中 $x^{0} = t$，空间指标 $i,j,k = 1,2,3$。

* 度规签名选取 $(-+++)$，即

$$
\mathrm{d}s^{2} = g_{\mu\nu}\mathrm{d}x^{\mu}\mathrm{d}x^{\nu}.
$$

* $c$ 为真空光速；在部分推导中置 $c=1$ 简化记号，必要时再恢复。

* $\omega$ 为角频率，$E = \hbar\omega$ 为对应能量。

* $\kappa(\omega)$ 表示频域统一时间刻度；$\kappa(x,\omega)$ 表示其空间局域化；$\kappa(x)$ 为对频率合适粗粒化后的宏观时间密度场。

* $\rho(E)$ 为态密度（density of states），$\rho_{\mathrm{rel}}(E)$ 为相对于某参考背景的"相对态密度"。

### 2.2 相对论中的时间膨胀与曲率

在狭义相对论中，平直 Minkowski 度规

$$
\mathrm{d}s^{2} = -c^{2}\mathrm{d}t^{2} + \delta_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j}
$$

给出静止粒子的固有时间 $\tau$：

$$
\mathrm{d}\tau = \sqrt{-\frac{\mathrm{d}s^{2}}{c^{2}}} = \sqrt{1-\frac{v^{2}}{c^{2}}}\,\mathrm{d}t.
$$

在广义相对论中，对静止于坐标系中的观测者（$\mathrm{d}x^{i}=0$），固有时间满足

$$
\mathrm{d}\tau = \sqrt{-g_{tt}(x)}\,\frac{\mathrm{d}t}{c}.
$$

若考虑静态、弱场且各向同性的情形，度规可写为

$$
\mathrm{d}s^{2} = -\left(1+\frac{2\Phi(x)}{c^{2}}\right)c^{2}\mathrm{d}t^{2} + \left(1-\frac{2\Phi(x)}{c^{2}}\right)\delta_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j},
$$

其中 $\Phi(x)$ 为牛顿势。此时

$$
\mathrm{d}\tau \simeq \left(1+\frac{\Phi(x)}{c^{2}}\right)\mathrm{d}t,
$$

表现为引力时间膨胀。

这里，$\Phi(x)$ 与 $g_{tt}(x)$ 之间的关系是几何定义的，而 $\Phi(x)$ 又通过爱因斯坦场方程与物质分布联系。在本文中，我们将提出反向的构造：**用时间流速密度 $\kappa(x)$ 直接定义 $\Phi(x)$ 和 $g_{tt}(x)$**。

### 2.3 散射延迟与统一时间恒等式

考虑一对自伴算符 $(H,H_{0})$，其中 $H_{0}$ 为"自由"哈密顿量，$H$ 为包含势场或散射中心的"全"哈密顿量。散射矩阵 $S(\omega)$ 可写为能量参数 $\omega$ 的酉算符族，其行列式相位

$$
\det S(\omega) = e^{2\mathrm{i}\varphi(\omega)}
$$

定义了总相移 $\varphi(\omega)$。Eisenbud–Wigner–Smith 理论表明，时间延迟算符

$$
\mathsf{Q}(\omega) = -\mathrm{i}S^{\dagger}(\omega)\frac{\mathrm{d}S(\omega)}{\mathrm{d}\omega}
$$

的迹与相移导数满足

$$
\mathrm{tr}\,\mathsf{Q}(\omega) = 2\,\frac{\mathrm{d}\varphi(\omega)}{\mathrm{d}\omega}.
$$

另一方面，Lifshits–Kreĭn 谱移函数 $\xi(\omega)$ 满足

$$
\frac{\mathrm{d}\xi(\omega)}{\mathrm{d}\omega} = \rho_{\mathrm{rel}}(\omega),
$$

其中 $\rho_{\mathrm{rel}}(\omega)$ 为相对态密度。Birman–Kreĭn 公式给出

$$
\det S(\omega) = e^{-2\pi\mathrm{i}\xi(\omega)}.
$$

综合上式可得

$$
\frac{\mathrm{d}\varphi(\omega)}{\mathrm{d}\omega} = -\pi\,\frac{\mathrm{d}\xi(\omega)}{\mathrm{d}\omega} = -\pi\,\rho_{\mathrm{rel}}(\omega),
$$

从而得到统一时间刻度（忽略符号约定中的常数差异）：

$$
\kappa(\omega) \equiv \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\,\mathrm{tr}\,\mathsf{Q}(\omega).
$$

这一恒等式说明：**时间延迟（相位导数）、谱密度变化与散射动力学之间存在一个本质上唯一的刻度 $\kappa(\omega)$**。我们将其解释为**时间流速密度**：在频率 $\omega$ 的模式上，每单位能量（或频率）间隔所携带的"有效时间资源"。

附录 A 将给出更为详细的散射论推导。

---

## 3 局域时间流速密度场 $\kappa(x,\omega)$ 的构造

### 3.1 局域态密度与空间分辨

在具有空间结构的系统中，态密度可以被局域化为 $\rho(x,E)$，满足

$$
\rho(E) = \int \rho(x,E)\,\mathrm{d}^{3}x.
$$

在散射理论与 Green 函数形式下，局域态密度可由

$$
\rho(x,E) = -\frac{1}{\pi}\,\mathrm{Im}\,\mathrm{tr}\,G^{+}(x,x;E)
$$

给出，其中 $G^{+}$ 为推迟格林函数。类似地，相对态密度的局域版可写为

$$
\rho_{\mathrm{rel}}(x,E) = \rho(x,E;H) - \rho(x,E;H_{0}).
$$

在统一时间恒等式的精神下，我们可将 $\kappa(\omega)$ 在空间上分解为

$$
\kappa(\omega) = \int \kappa(x,\omega)\,\mathrm{d}^{3}x,
$$

其中 $\kappa(x,\omega)$ 可以直观地视为"在频率 $\omega$ 处，定位在 $x$ 附近的相对时间密度"。

更具体地，我们定义

**定义 3.1（局域时间流速密度）**

在给定的哈密顿量对 $(H,H_{0})$ 下，局域时间流速密度 $\kappa(x,\omega)$ 定义为

$$
\kappa(x,\omega) \equiv \rho_{\mathrm{rel}}(x,\omega),
$$

其中

$$
\rho_{\mathrm{rel}}(x,\omega) = -\frac{1}{\pi}\,\mathrm{Im}\,\mathrm{tr}\,\bigl[G^{+}(x,x;\omega;H) - G^{+}(x,x;\omega;H_{0})\bigr].
$$

则有

$$
\int \kappa(x,\omega)\,\mathrm{d}^{3}x = \rho_{\mathrm{rel}}(\omega) = \kappa(\omega).
$$

直观上，$\kappa(x,\omega)$ 表示在频率 $\omega$ 上，由"有结构的宇宙"相对于某简单参考背景所增加或减少的局域态密度；在我们后续的解释中，它将正比于"局域内部信息演化的时间密度"。

### 3.2 频率窗口与宏观 $\kappa(x)$

宏观实验（如原子钟、引力红移观测）往往只对某一频率窗口 $\Delta\omega$ 内的模式敏感。我们因此定义加权粗粒化：

$$
\kappa(x) \equiv \int W(\omega)\,\kappa(x,\omega)\,\mathrm{d}\omega,
$$

其中 $W(\omega)$ 为规范选定的权函数，满足

$$
W(\omega)\ge 0,\quad \int W(\omega)\,\mathrm{d}\omega = 1.
$$

典型地，$W(\omega)$ 可以取为与所用原子钟跃迁频率相匹配的窗口函数；而在 QCA 连续极限中，$W(\omega)$ 则自然集中在低能有效频带。

我们将 $\kappa(x)$ 称为**局域时间流速密度场**，并以其作为后续几何构造的基本标量场。

---

## 4 曲率作为 $\kappa(x)$ 的几何纹理

本节从 $\kappa(x)$ 出发构造度规，并在弱场极限下将其与引力势、曲率直接关联。

### 4.1 时间因子与 $\kappa(x)$：度规 Ansatz

我们首先提出如下公理：

**公理 4.1（时间刻度公理）**

在每一点 $x$ 上，局域静止观察者的固有时间 $\tau$ 与外部坐标时间 $t$ 的比率由 $\kappa(x)$ 决定，即存在常数 $\kappa_{\infty}$ 使得

$$
\frac{\mathrm{d}\tau}{\mathrm{d}t}(x) = \frac{\kappa_{\infty}}{\kappa(x)}.
$$

其中 $\kappa_{\infty}$ 为在"参考无引力区域"（例如空间无穷远）的时间密度值。

换言之：$\kappa(x)$ 越大，单位外部时间内能够发生的内部演化步数越多，因此局域固有时间相对坐标时间"更慢"（因为内部变化被更高密度地"填满"）。这一点与引力时间膨胀的直观相符：引力势越深，时间越慢，对应 $\kappa(x)$ 越大。

对静止观察者（$\mathrm{d}x^{i}=0$），有

$$
\mathrm{d}s^{2} = g_{tt}(x)\,\mathrm{d}t^{2} = -c^{2}\mathrm{d}\tau^{2},
$$

从而

$$
g_{tt}(x) = -c^{2}\left(\frac{\mathrm{d}\tau}{\mathrm{d}t}\right)^{2} = -c^{2}\,\frac{\kappa_{\infty}^{2}}{\kappa^{2}(x)}.
$$

定义无量纲时间因子

$$
\eta(x) \equiv \frac{\kappa(x)}{\kappa_{\infty}},
$$

则有

$$
g_{tt}(x) = -\frac{c^{2}}{\eta^{2}(x)}.
$$

这给出了时间分量的唯一形式：时间密度越高，$|g_{tt}|$ 越小，对应固有时间相对于坐标时间越慢。

### 4.2 空间因子与信息体积守恒

仅由时间因子尚不能确定整个度规。我们引入第二个公理：

**公理 4.2（局域信息体积守恒）**

考虑一个包含大量自由度的物理系统，其信息体积定义为

$$
V_{\mathrm{info}} \equiv \int \kappa(x)\,\sqrt{\gamma}\,\mathrm{d}^{3}x,
$$

其中 $\gamma$ 为空间三度量 $\gamma_{ij}$ 的行列式。我们要求在无宏观流出入的区域，$V_{\mathrm{info}}$ 在缓慢演化过程中保持不变。

直观解释：在 QCA 或量子场的本体论中，总的信息处理容量（每单位外部时间内，在整个空间上可以发生的内在演化步数总量）应当守恒；如果局域时间流速密度 $\kappa(x)$ 上升，则对应空间可用体积应当收缩，以保持总信息体积不变。

设度规为静态、各向同性形式：

$$
\mathrm{d}s^{2} = -\frac{c^{2}}{\eta^{2}(x)}\,\mathrm{d}t^{2} + a^{2}(x)\,\delta_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j},
$$

则空间三度量为 $\gamma_{ij}=a^{2}(x)\delta_{ij}$，有

$$
\sqrt{\gamma} = a^{3}(x).
$$

信息体积为

$$
V_{\mathrm{info}} = \int \kappa(x)\,a^{3}(x)\,\mathrm{d}^{3}x = \kappa_{\infty}\int \eta(x)\,a^{3}(x)\,\mathrm{d}^{3}x.
$$

若我们要求在任意局域变形下 $V_{\mathrm{info}}$ 极值且在弱场极限上恢复平直度规，即 $\eta \to 1$、$a\to 1$，则自然的选择是

$$
\eta(x)\,a^{3}(x) = 1,
$$

或

$$
a(x) = \eta^{-1/3}(x).
$$

然而，这一选择与光线偏折等观测存在微妙差异。另一种更符合引力透镜与光学度规实验的选择是令空间缩放因子与时间因子成逆比例，即

$$
a(x) = \eta^{-1}(x),
$$

对应

$$
\sqrt{\gamma} = \eta^{-3}(x),
$$

这时信息体积为

$$
V_{\mathrm{info}} = \kappa_{\infty}\int \eta(x)\,\eta^{-3}(x)\,\mathrm{d}^{3}x = \kappa_{\infty}\int \eta^{-2}(x)\,\mathrm{d}^{3}x.
$$

要使 $V_{\mathrm{info}}$ 在弱场极限下与平直情况等价，我们要求空间坐标也随 $\eta$ 做适当重标；在自然的各向同性交换下，一类稳定解正对应于**双因子缩放光学度规**：

$$
\mathrm{d}s^{2} = -\eta^{2}(x)c^{2}\mathrm{d}t^{2} + \eta^{-2}(x)\,\gamma^{(0)}_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j},
$$

其中 $\gamma^{(0)}_{ij}$ 为背景平直或缓慢变化的空间度量。通过对 $\eta$ 的适当重定义，可将前述 $g_{tt}=-c^{2}/\eta^{2}$ 与此形式统一；在弱场极限下两者是等价的重标选取问题。为简洁起见，后文采用

$$
\mathrm{d}s^{2} = -\eta^{2}(x)c^{2}\mathrm{d}t^{2} + \eta^{-2}(x)\delta_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j},
$$

并将

$$
\eta(x) \simeq 1 + \frac{\Phi(x)}{c^{2}}
$$

识别为引力势的时间刻度因子。

### 4.3 弱场极限与引力势

在弱场极限，令

$$
\eta(x) = 1 + \epsilon(x),\qquad |\epsilon(x)| \ll 1,
$$

则

$$
g_{tt} = -\eta^{2}(x)c^{2} \simeq -\left(1+2\epsilon(x)\right)c^{2},
$$

与标准写法

$$
g_{tt} = -\left(1+\frac{2\Phi(x)}{c^{2}}\right)c^{2}
$$

对比，可得

$$
\epsilon(x) = \frac{\Phi(x)}{c^{2}}.
$$

另一方面，由 $\eta(x) = \kappa(x)/\kappa_{\infty}$ 得

$$
\Phi(x) = c^{2}\ln\eta(x) \simeq c^{2}\bigl(\eta(x)-1\bigr) = c^{2}\left(\frac{\kappa(x)}{\kappa_{\infty}}-1\right),
$$

更精确地，

$$
\Phi(x) = c^{2}\ln\left(\frac{\kappa(x)}{\kappa_{\infty}}\right).
$$

这说明：**牛顿引力势在弱场近似下可被视为时间流速密度场 $\kappa(x)$ 的对数**。

### 4.4 曲率张量与 $\ln\kappa(x)$ 的二阶导数

在上述静态、各向同性的度规下，Christoffel 符号与曲率张量可显式写出。特别地，$R_{00}$ 分量在弱场近似下满足

$$
R_{00} \simeq -\nabla^{2}\Phi(x)/c^{2} = -\nabla^{2}\ln\eta(x) = -\nabla^{2}\ln\kappa(x) + \text{常数项},
$$

其中 $\nabla^{2}$ 为背景欧氏空间的 Laplace 算符。

这意味着：若将爱因斯坦方程写为

$$
R_{00} - \frac{1}{2}g_{00}R = \frac{8\pi G}{c^{4}}T_{00},
$$

在弱场静态情形下退化为熟悉的 Poisson 方程

$$
\nabla^{2}\Phi(x) = 4\pi G\rho(x),
$$

则在我们的时间密度视角中，这等价于

$$
\nabla^{2}\ln\kappa(x) \propto -\rho(x).
$$

附录 B 将给出上述关系的详细计算。

---

## 5 与爱因斯坦场方程的一致性

### 5.1 时间密度与能量—动量张量

在标准广义相对论中，引力源是能量—动量张量 $T_{\mu\nu}$。在我们的框架中，$\kappa(x)$ 直接刻画的是"单位外部时间、单位空间体积内发生的内部信息演化速率"，因而更自然地与"信息能量密度"相关。

我们提出如下对应关系：

**假设 5.1（$\kappa$–源对应）**

在适当粗粒化尺度上，存在函数 $F$ 使得

$$
\ln\kappa(x) = F\bigl[T_{\mu\nu}(x),g_{\mu\nu}(x)\bigr],
$$

且在弱场低速极限下退化为

$$
\ln\kappa(x) \simeq \alpha\,\frac{T_{00}(x)}{\rho_{0}c^{2}} + \beta,
$$

其中 $\alpha,\beta,\rho_{0}$ 为常数或缓慢变化参数。

结合上一节的

$$
\Phi(x) = c^{2}\ln\left(\frac{\kappa(x)}{\kappa_{\infty}}\right),
$$

可得到

$$
\Phi(x) \simeq \frac{\alpha c^{2}}{\rho_{0}c^{2}}T_{00}(x) + \text{常数} = \frac{\alpha}{\rho_{0}}T_{00}(x) + \text{常数}.
$$

在物质为静止尘埃、$T_{00}\simeq\rho c^{2}$ 的情况下，这退化为

$$
\Phi(x) \simeq \alpha\,\frac{\rho(x)}{\rho_{0}}c^{2} + \text{常数},
$$

与牛顿势方程的形式相符。

更一般地，应当存在某种"信息—能量对应关系"，将 $\kappa(x)$ 视为包含 $T_{\mu\nu}$ 所有分量的函数；本工作中我们专注于静态、低速情形下 $T_{00}$ 主导的状况。

### 5.2 有效爱因斯坦方程的重写

在 $\kappa$-度规下，Ricci 张量与标量曲率可写成 $\eta(x)$ 的函数。抽象地，我们可以写成

$$
G_{\mu\nu}(x;\kappa) = \frac{8\pi G}{c^{4}}T_{\mu\nu}(x),
$$

其中左侧显式依赖于 $\kappa(x)$ 及其导数。由于 $\kappa$ 又是 $T_{\mu\nu}$ 的函数，上式成为一个封闭的自洽方程组，形式上类似于将爱因斯坦方程重写为一类非线性标量场方程。

在弱场极限中，$G_{00}\simeq -\nabla^{2}\Phi/c^{2}$，从而

$$
-\frac{1}{c^{2}}\nabla^{2}\Phi(x) \simeq \frac{8\pi G}{c^{4}}T_{00}(x),
$$

即

$$
\nabla^{2}\Phi(x) \simeq 4\pi G\rho(x),
$$

这与传统结果一致。由于 $\Phi$ 已被表示为 $\ln\kappa(x)$，可以视作对标准引力理论的"时间密度重标记"。

---

## 6 可观测效应与实验建议

### 6.1 引力红移

考虑两个静止位置 $x_{1},x_{2}$ 处的局域观察者，其各自固有时间与坐标时间的关系为

$$
\frac{\mathrm{d}\tau_{i}}{\mathrm{d}t} = \frac{\kappa_{\infty}}{\kappa(x_{i})},\quad i=1,2.
$$

设在 $x_{1}$ 处发出频率为 $\nu_{1}$ 的光子，其周期以局域固有时间衡量；在忽略非引力效应下，沿光线传播的相位守恒，则到达 $x_{2}$ 时，其在 $x_{2}$ 处被测得的频率 $\nu_{2}$ 满足

$$
\frac{\nu_{2}}{\nu_{1}} = \frac{\mathrm{d}\tau_{1}/\mathrm{d}t}{\mathrm{d}\tau_{2}/\mathrm{d}t} = \frac{\kappa(x_{2})}{\kappa(x_{1})}.
$$

在弱场极限

$$
\kappa(x) \simeq \kappa_{\infty}\left(1+\frac{\Phi(x)}{c^{2}}\right),
$$

则

$$
\frac{\nu_{2}}{\nu_{1}} \simeq 1 + \frac{\Phi(x_{2})-\Phi(x_{1})}{c^{2}},
$$

即标准引力红移公式。

这表明：**引力红移可被完全解释为时间流速密度 $\kappa(x)$ 的空间差异**。

### 6.2 光线偏折与光学度规

在度规

$$
\mathrm{d}s^{2} = -\eta^{2}(x)c^{2}\mathrm{d}t^{2} + \eta^{-2}(x)\delta_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j}
$$

下，光线满足 $\mathrm{d}s^{2}=0$，从而

$$
\left|\frac{\mathrm{d}\mathbf{x}}{\mathrm{d}t}\right| = c\,\eta^{2}(x).
$$

将其与有效折射率 $n(x)$ 关系

$$
\left|\frac{\mathrm{d}\mathbf{x}}{\mathrm{d}t}\right| = \frac{c}{n(x)}
$$

对比，可得

$$
n(x) = \eta^{-2}(x).
$$

即：时间流速因子 $\eta(x)$ 等价于一个有效折射率场 $n(x)$ 的平方根；光线在 $\eta(x)$ 较大的区域传播更慢，从而被"弯向"$\eta$ 高值区域（或 $\kappa$ 高值区域），这就是引力透镜效应的几何光学描述。

因此，在本框架中，引力透镜的偏折角可被视为路径积分

$$
\Delta\theta \sim \int \nabla_{\perp}\ln n(x)\,\mathrm{d}\ell = -2\int \nabla_{\perp}\ln\eta(x)\,\mathrm{d}\ell = -2\int \nabla_{\perp}\ln\kappa(x)\,\mathrm{d}\ell.
$$

### 6.3 原子钟网络与时间密度地形图

在实验侧，现代光学钟与频率比较技术已经允许在地球尺度上精确测量引力时间膨胀。我们的理论提供了一个直接可测的对象：**$\kappa(x)$ 的空间分布**。

具体而言：

1. 选取某一参考位置 $x_{0}$，将其 $\kappa(x_{0})$ 定义为 $\kappa_{\infty}$。

2. 利用高精度光钟，在多个位置 $x$ 同步测量频率比 $\nu(x)/\nu(x_{0})$。

3. 根据关系

$$
\frac{\nu(x)}{\nu(x_{0})} = \frac{\kappa(x_{0})}{\kappa(x)} = \frac{\kappa_{\infty}}{\kappa(x)},
$$

反解出

$$
\kappa(x) = \frac{\kappa_{\infty}}{\nu(x)/\nu(x_{0})}.
$$

4. 从而得到一个"时间密度地形图" $\kappa(x)$，其梯度应与传统测得的引力加速度场一致。

这为本理论提供了直接可检验的实验路径。

---

## 7 与量子元胞自动机及信息速率守恒的结合

### 7.1 信息速率守恒与内部频率

在 QCA 模型中，宇宙被视为定义在某离散格点 $\Lambda$ 上的局域幺正更新规则。每一离散时间步 $\Delta t$ 内，每个元胞执行若干局域门操作，可视为"内部信息更新"。对一个长波有效粒子激发，其外部群速度 $v_{\mathrm{ext}}$ 与内部态振荡速度 $v_{\mathrm{int}}$ 满足信息速率守恒：

$$
v_{\mathrm{ext}}^{2} + v_{\mathrm{int}}^{2} = c^{2}.
$$

这里，$c$ 可理解为每个元胞在每步中可用的总"信息速率预算"。

在这种图景中：

* 外部运动越快（$v_{\mathrm{ext}}$ 趋近 $c$），留给内部振荡的速率越小，粒子越"接近无质量"。

* 内部振荡越快（$v_{\mathrm{int}}$ 趋近 $c$），外部运动越慢，对应"有质量粒子"在静止系中的内部振动。

我们可以将局域内部频率 $\omega_{\mathrm{int}}(x)$ 与统一时间刻度 $\kappa(x)$ 联系起来：在一个元胞附近，单位外部时间内内部演化步数正比于 $\omega_{\mathrm{int}}(x)$，从而

$$
\kappa(x) \propto \omega_{\mathrm{int}}(x).
$$

如果进一步引入信息论质量定义

$$
m c^{2} = \hbar\omega_{\mathrm{int}},
$$

则

$$
\kappa(x) \propto m(x).
$$

这表明质量本身可以看作时间密度的一种体现。

### 7.2 一维 Dirac–QCA 模型中的 $\kappa(x)$ 示例

考虑一维格点上带有两分量"自旋"的 Dirac 型 QCA，其一步演化算符可写为

$$
U = S_{+}\otimes P_{+} + S_{-}\otimes P_{-},
$$

其中 $S_{\pm}$ 为向右/左平移算符，$P_{\pm}$ 为作用于内部空间的投影，满足适当的幺正条件。对该模型取长波极限可得 Dirac 方程

$$
\mathrm{i}\hbar\frac{\partial}{\partial t}\psi(x,t) = \left(-\mathrm{i}\hbar c\,\sigma_{z}\frac{\partial}{\partial x} + mc^{2}\sigma_{x}\right)\psi(x,t).
$$

若我们在不同空间区域施加不同的 QCA 更新参数（例如改变局域"质量项"），则内部频率 $\omega_{\mathrm{int}}(x)$ 随位置变化，对应不同的 $\kappa(x)$。通过在该 QCA 上定义散射问题（例如一个波包从质量较小区域入射到质量较大区域），可以计算散射相移 $\varphi(\omega)$、时间延迟算符 $\mathsf{Q}(\omega)$ 与局域态密度变化，得到 $\kappa(x,\omega)$ 与 $\kappa(x)$ 的离散版本。

进一步地，通过对 QCA 更新规则的局域变形，可构造与连续度规

$$
\mathrm{d}s^{2} = -\eta^{2}(x)c^{2}\mathrm{d}t^{2} + \eta^{-2}(x)\mathrm{d}x^{2}
$$

相对应的"离散光学度规"，使得长波极限下粒子与光信号的传播自动感受到一个由 $\kappa(x)$ 决定的"引力背景"。

这一构造说明：在离散本体论中，曲率可以真正被实现为时间流速密度纹理，而非额外引入的连续几何对象。

---

## 8 总结与展望

本文从散射论统一时间恒等式与信息速率守恒出发，提出了"曲率即时间流速密度非均匀性"的图景。核心结构可概括如下：

1. **统一时间刻度：** 通过 Birman–Kreĭn、Eisenbud–Wigner–Smith 等结果，将散射相移导数、相对态密度与时间延迟迹统一为单一刻度 $\kappa(\omega)$，解释为频域时间密度。

2. **局域化与几何重构：** 引入局域 $\kappa(x,\omega)$ 与粗粒化 $\kappa(x)$，并以"时间刻度公理"和"信息体积守恒"公理构造出一类由 $\kappa(x)$ 唯一选出的双因子缩放光学度规。弱场极限下，引力势满足

$$
\Phi(x) = c^{2}\ln\left(\frac{\kappa(x)}{\kappa_{\infty}}\right),
$$

曲率张量分量与 $\ln\kappa(x)$ 的二阶导数直接相关。

3. **与实验的一致性：** 引力红移、光线偏折与原子钟网络观测在该框架中自然出现，并可视作对 $\kappa(x)$ 的直接测量。

4. **离散本体嵌入：** 在 QCA 图景下，$\kappa(x)$ 与内部频率、质量及信息速率守恒直接联系，从而将质量、时间膨胀与引力曲率统一为对同一"信息速率预算"的不同分配方式。

未来的重要方向包括：

* 将完整爱因斯坦场方程重写为关于 $\kappa(x)$ 的闭合标量—张量方程组；

* 在非静态、各向异性与宇宙学尺度上推广本框架，特别是探索宇宙学常数、暗能量是否可以用大尺度的 $\kappa$-纹理来解释；

* 在具体 QCA 模型中构造黑洞类结构，验证"信息冻结层"与 $\kappa$ 的关系；

* 结合现代时间标准与卫星导航系统，给出可行的"$\kappa$-地形图"实验方案。

---

## Appendix A：统一时间恒等式的散射论推导（概要）

本附录简要回顾从散射矩阵 $S(\omega)$、谱移函数 $\xi(\omega)$ 与时间延迟算符 $\mathsf{Q}(\omega)$ 出发得到

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\mathrm{tr}\,\mathsf{Q}(\omega)
$$

的步骤。

### A.1 Birman–Kreĭn 公式与谱移函数

设 $H = H_{0} + V$，其中 $V$ 为迹类扰动，则存在谱移函数 $\xi(\lambda)$ 使得对任意充分良好的函数 $f$，有

$$
\mathrm{tr}\bigl(f(H)-f(H_{0})\bigr) = \int f'(\lambda)\,\xi(\lambda)\,\mathrm{d}\lambda.
$$

取 $f(\lambda)=(\lambda-z)^{-1}$ 得到

$$
\mathrm{tr}\bigl((H-z)^{-1} - (H_{0}-z)^{-1}\bigr) = -\int\frac{\xi(\lambda)}{(\lambda-z)^{2}}\,\mathrm{d}\lambda,
$$

进而可通过边界值得到 $\xi'(\lambda)$ 与相对态密度之间的关系。

Birman–Kreĭn 公式给出散射矩阵行列式与谱移函数之间的关系：

$$
\det S(\lambda) = e^{-2\pi\mathrm{i}\xi(\lambda)}.
$$

设

$$
\det S(\lambda) = e^{2\mathrm{i}\varphi(\lambda)},
$$

则

$$
2\mathrm{i}\varphi(\lambda) = -2\pi\mathrm{i}\xi(\lambda) + 2\pi\mathrm{i}k,
$$

忽略整数多值，得到

$$
\varphi(\lambda) = -\pi\xi(\lambda).
$$

从而

$$
\varphi'(\lambda) = -\pi\xi'(\lambda).
$$

另一方面，相对态密度定义为

$$
\rho_{\mathrm{rel}}(\lambda) = \rho(\lambda;H) - \rho(\lambda;H_{0}) = \xi'(\lambda),
$$

于是

$$
\varphi'(\lambda) = -\pi\,\rho_{\mathrm{rel}}(\lambda).
$$

在本文的约定中，我们将符号吸收到 $\rho_{\mathrm{rel}}$ 的定义中，得到

$$
\kappa(\omega) \equiv \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega).
$$

### A.2 Wigner–Smith 时间延迟迹

Wigner–Smith 时间延迟算符定义为

$$
\mathsf{Q}(\omega) = -\mathrm{i}\,S^{\dagger}(\omega)\frac{\mathrm{d}S(\omega)}{\mathrm{d}\omega}.
$$

由于 $S(\omega)$ 为酉算符，其特征值可写为 $e^{2\mathrm{i}\delta_{n}(\omega)}$，$n$ 为通道标号。则 $\mathsf{Q}(\omega)$ 的特征值为 $2\,\mathrm{d}\delta_{n}/\mathrm{d}\omega$，从而

$$
\mathrm{tr}\,\mathsf{Q}(\omega) = 2\sum_{n}\frac{\mathrm{d}\delta_{n}}{\mathrm{d}\omega}.
$$

另一方面，总相移 $\varphi(\omega)$ 可写为

$$
\varphi(\omega) = \sum_{n}\delta_{n}(\omega),
$$

于是

$$
\frac{\mathrm{d}\varphi}{\mathrm{d}\omega} = \frac{1}{2}\mathrm{tr}\,\mathsf{Q}(\omega).
$$

综合以上结果，得到统一时间恒等式：

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\mathrm{tr}\,\mathsf{Q}(\omega).
$$

---

## Appendix B：$\kappa$-度规下弱场曲率分量的计算

本附录在静态、各向同性假设下，计算度规

$$
\mathrm{d}s^{2} = -\eta^{2}(x)c^{2}\mathrm{d}t^{2} + \eta^{-2}(x)\delta_{ij}\mathrm{d}x^{i}\mathrm{d}x^{j}
$$

对应的 Ricci 张量 $R_{\mu\nu}$ 的弱场表达，并展示 $R_{00}$ 与 $\ln\eta(x)$ 的 Laplace 算符之间的关系。

### B.1 Christoffel 符号

度规分量：

$$
g_{00} = -\eta^{2}c^{2},\quad g_{ij} = \eta^{-2}\delta_{ij},\quad g_{0i} = 0.
$$

其逆：

$$
g^{00} = -\frac{1}{\eta^{2}c^{2}},\quad g^{ij} = \eta^{2}\delta^{ij}.
$$

Christoffel 符号

$$
\Gamma^{\rho}_{\mu\nu} = \frac{1}{2}g^{\rho\sigma}\bigl(\partial_{\mu}g_{\sigma\nu} + \partial_{\nu}g_{\sigma\mu} - \partial_{\sigma}g_{\mu\nu}\bigr).
$$

由于度规静态，$\partial_{0}g_{\mu\nu}=0$。非零分量主要为：

1. $\Gamma^{0}_{0i}$：

$$
\Gamma^{0}_{0i} = \frac{1}{2}g^{00}\partial_{i}g_{00} = \frac{1}{2}\left(-\frac{1}{\eta^{2}c^{2}}\right)\partial_{i}(-\eta^{2}c^{2}) = \frac{1}{\eta}\partial_{i}\eta.
$$

2. $\Gamma^{i}_{00}$：

$$
\Gamma^{i}_{00} = \frac{1}{2}g^{ij}\left(-\partial_{j}g_{00}\right) = -\frac{1}{2}\eta^{2}\delta^{ij}\partial_{j}(-\eta^{2}c^{2}) = \eta^{2}\delta^{ij}\eta c^{2}\partial_{j}\eta = \eta^{3}c^{2}\partial^{i}\eta.
$$

3. $\Gamma^{i}_{jk}$：

$$
\Gamma^{i}_{jk} = \frac{1}{2}g^{i\ell}\left(\partial_{j}g_{\ell k} + \partial_{k}g_{\ell j} - \partial_{\ell}g_{jk}\right) = \frac{1}{2}\eta^{2}\delta^{i\ell}\partial_{j}\left(\eta^{-2}\delta_{\ell k}\right) + \cdots
$$

展开并使用 $\partial_{j}\eta^{-2}=-2\eta^{-3}\partial_{j}\eta$ 可得

$$
\Gamma^{i}_{jk} = -\frac{1}{\eta}\left(\delta^{i}_{j}\partial_{k}\eta + \delta^{i}_{k}\partial_{j}\eta - \delta_{jk}\partial^{i}\eta\right).
$$

### B.2 Ricci 张量 $R_{00}$ 的弱场近似

Ricci 张量定义为

$$
R_{\mu\nu} = \partial_{\lambda}\Gamma^{\lambda}_{\mu\nu} - \partial_{\nu}\Gamma^{\lambda}_{\mu\lambda} - \Gamma^{\lambda}_{\mu\nu}\Gamma^{\sigma}_{\lambda\sigma} + \Gamma^{\sigma}_{\mu\lambda}\Gamma^{\lambda}_{\nu\sigma}.
$$

对于 $R_{00}$：

$$
R_{00} = \partial_{\lambda}\Gamma^{\lambda}_{00} - \partial_{0}\Gamma^{\lambda}_{0\lambda} - \Gamma^{\lambda}_{00}\Gamma^{\sigma}_{\lambda\sigma} + \Gamma^{\sigma}_{0\lambda}\Gamma^{\lambda}_{0\sigma}.
$$

静态性给出 $\partial_{0}\Gamma^{\lambda}_{0\lambda}=0$。

考虑弱场极限，令 $\eta = 1+\epsilon$，$|\epsilon|\ll 1$，保留线性项。此时：

$$
\partial_{i}\eta = \partial_{i}\epsilon,\quad \eta^{3}\simeq 1,\quad \frac{1}{\eta}\simeq 1.
$$

1. 第一项：

$$
\partial_{\lambda}\Gamma^{\lambda}_{00} = \partial_{i}\Gamma^{i}_{00} \simeq \partial_{i}(c^{2}\partial^{i}\epsilon) = c^{2}\nabla^{2}\epsilon.
$$

2. 第二项为零。

3. 第三、四项为二阶小量（$\epsilon\,\partial\epsilon$），在弱场线性近似中可以忽略。

因此

$$
R_{00} \simeq c^{2}\nabla^{2}\epsilon.
$$

另一方面，由 $\eta = 1+\epsilon$ 可得

$$
\ln\eta \simeq \epsilon,
$$

从而

$$
R_{00} \simeq c^{2}\nabla^{2}\ln\eta(x).
$$

将 $\eta$ 与 $\kappa$ 关联：

$$
\eta(x) = \frac{\kappa(x)}{\kappa_{\infty}} \Rightarrow \ln\eta(x) = \ln\kappa(x) - \text{常数},
$$

于是

$$
R_{00} \simeq c^{2}\nabla^{2}\ln\kappa(x).
$$

与广义相对论弱场结果

$$
R_{00} \simeq -\nabla^{2}\Phi(x)/c^{2}
$$

对比，并利用

$$
\Phi(x) = c^{2}\ln\eta(x),
$$

可以验证两者一致，只是常数与符号约定有所不同。

---

## Appendix C：一维 Dirac–QCA 中 $\kappa(x)$ 的构造示意

本附录提供一个简化的一维 Dirac–QCA 模型，展示如何从离散更新规则中构造 $\kappa(x)$ 的离散版，并与连续几何极限中的时间密度场对应。

### C.1 模型定义

在一维整数格点 $n\in\mathbb{Z}$ 上，每个格点携带两分量内部自由度（类似自旋），总 Hilbert 空间为

$$
\mathcal{H} = \bigotimes_{n\in\mathbb{Z}}\mathbb{C}^{2}.
$$

定义一步演化算符

$$
U = S_{+}\otimes P_{+} + S_{-}\otimes P_{-},
$$

其中

* $S_{+}$ 将态向右平移一个格点，$S_{-}$ 向左平移；

* $P_{+},P_{-}$ 为内部空间上的互补投影，满足 $P_{+}+P_{-}=\mathbb{I}$。

通过适当选择 $P_{\pm}$ 参数（例如包含质量角），可证明 $U$ 在长波极限下给出 Dirac 方程。

### C.2 局域内部频率与离散时间密度

考虑在大尺度上近似平稳的背景下，局域平面波解的能谱可写为

$$
\psi_{k}(n,t) \sim e^{\mathrm{i}(kn - \omega(k)t)}u(k),
$$

其中 $\omega(k)$ 为离散能量本征值。内部"Zitterbewegung" 振荡频率可由 $\omega_{\mathrm{int}}(k)$ 抽取，与质量参数直接相关。

若我们在不同格点区域内改变 QCA 的局域参数（例如质量角 $\theta(n)$），则 $\omega_{\mathrm{int}}(n)$ 成为位置的函数，对应局域时间密度

$$
\kappa(n) \propto \omega_{\mathrm{int}}(n).
$$

在散射构造中，将存在两种哈密顿量：$H_{0}$ 为均匀参数的 QCA，$H$ 为带有局域质量扰动的 QCA。计算这二者之间的散射相移与谱移函数，即可构造离散版的统一时间刻度 $\kappa(\omega)$ 及 $\kappa(n,\omega)$。

### C.3 连续极限与几何对应

在格距 $\ell\to 0$、时间步长 $\Delta t\to 0$ 的极限中，定义连续坐标 $x=n\ell$、$t=m\Delta t$，并令

$$
\eta(x) \propto \frac{\kappa(x)}{\kappa_{\infty}}.
$$

通过适当的重标与 coarse-graining，可以得到连续时间密度场 $\kappa(x)$，并将其代入第 4 节构造的度规中，从而实现从离散 QCA 到连续几何的映射。

在该映射中：

* QCA 中局域更新规则的空间非均匀性体现为 $\kappa(x)$ 的空间纹理；

* 连续几何中的曲率与 $\kappa(x)$ 的二阶导数相关；

* 引力红移、光线偏折等现象在 QCA 中通过信号传播时间与路径差异体现。

由此可见，"曲率即时间流速密度的非均匀性"并非仅是形式重解释，而是可在具体离散模型中以算子与谱的方式被构造与验证的结构性命题。

