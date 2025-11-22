# 基于局域信息体积守恒的光学度规与爱因斯坦场方程的熵力推导

**Optical Metric from Local Information Volume Conservation and the Entropic Derivation of Einstein Equations**

## Abstract

在量子元胞自动机（quantum cellular automaton, QCA）与信息本体论的视角下，时空几何应当被理解为底层离散量子网络的信息处理能力与连通结构的涌现表征。本文在这一框架中提出并形式化"局域信息体积守恒"原理：在从离散 QCA 到连续有效流形的粗粒化过程中，任何局域体积元内的"每单位坐标体积、每单位坐标时间所能承载的可分辨量子自由度总量"必须保持不变。该原理在静态、各向同性的情形下唯一选出一类双因子缩放的光学度规

$$
ds^2 = -n^{-2}(x) c^2 dt^2 + n^2(x)\delta_{ij} dx^i dx^j,
$$

其中 $n(x) \ge 1$ 可以解释为由局域信息处理负载（information processing load）诱导的有效折射率场。

在弱场极限中，取 $n(x) = 1 - \Phi(x)/c^2 + \mathcal O(\Phi^2/c^4)$，其中 $\Phi$ 为牛顿势，则所得线元展开为

$$
ds^2 = -(1+2\Phi/c^2)c^2dt^2 + (1-2\Phi/c^2)\delta_{ij}dx^i dx^j + \mathcal O(\Phi^2/c^4),
$$

恰好对应于参数化后牛顿（PPN）形式中 $\gamma = 1$ 的广义相对论弱场度规。由此可得光线偏折、Shapiro 延迟等观测量，其一阶偏折角系数为 $4GM/(bc^2)$，从而在标量场驱动的"折射率引力"框架下解决了爱因斯坦 1911 年标量引力理论中仅得到一半偏折角的历史困难。

进一步地，本文提出信息–引力变分原理（information–gravity variational principle, IGVP）：将几何作用量视为广义熵泛函的一部分，将局域信息处理负载视为纠缠熵密度的源项，在局域平衡的意义下对总"信息熵"泛函取变分。借助 Jacobson 关于"爱因斯坦方程作为状态方程"的思路，证明在光学度规可行的广义散射局域中，IGVP 的平衡条件等价于带有信息应力张量的爱因斯坦场方程。

本文由此在三个层面上建立了桥梁：（1）从 QCA 幺正演化与局域信息体积守恒出发，导出具有实验可检验内容的光学度规；（2）在弱场极限下与标准广义相对论的 PPN 结构完全对齐；（3）在熵力与信息几何的框架中，将爱因斯坦方程重释为"几何–信息平衡条件"，并给出若干可在数值 QCA 与类引力光学实验中检验的工程提案。

## Keywords

量子元胞自动机；光学度规；局域信息体积守恒；引力透镜；Shapiro 延迟；熵力；爱因斯坦方程；信息几何

---

## Introduction & Historical Context

广义相对论以带 Lorentz 签名的四维流形 $(M,g_{\mu\nu})$ 作为引力理论的基本舞台，引力被解释为时空几何的弯曲，而非作用于平直背景上的远程力。弱场极限下的观测检验（如水星近日点进动、光线经过太阳边缘的偏折、Shapiro 延迟等）对这一几何化引力叙事给出了高度精确的支持。

另一方面，以"It from Qubit"为代表的信息本体论观点认为，物理世界在最深层次上是由量子信息及其处理规则构成，连续时空、物质场以及测量结果均为某种底层离散信息结构的涌现属性。在这一脉络中，量子元胞自动机（QCA）被视为统一量子场与离散因果结构的一种自然模型：在离散格点上定义有限维局域 Hilbert 空间，通过有限邻域、空间齐次的幺正演化规则实现全局时间演化，进而在连续极限中涌现标准相对论性场方程。

早在 1911 年，爱因斯坦在讨论引力对光的影响时曾提出一种标量引力模型，将引力势 $\Phi$ 仅作为影响局域光速的标量场，并由此推导出光线经过太阳时的偏折角为 $2GM/(bc^2)$，即后来广义相对论正确结果的一半。这一误差可以追溯到模型中仅修改了度规的时间分量 $g_{00}$，忽略了空间分量 $g_{ij}$ 的弯曲贡献。完整的广义相对论在静态、弱场极限下给出的线元可写为

$$
ds^2 = -(1+2\Phi/c^2)c^2dt^2 + (1-2\gamma\Phi/c^2)(dx^2+dy^2+dz^2),
$$

其中 PPN 参数 $\gamma = 1$ 时才与实验相容。

在研究引力透镜与波传播的文献中，人们逐渐形成了"光学度规"（optical metric）的概念：对静态时空，可将零测地线的投影等价为三维 Riemann 流形上的测地线问题，其度规为 $\gamma_{ij} = -g_{00}^{-1}g_{ij}$，从而引入一个有效折射率 $N_{\text{eff}}(x)$，以研究弱引力场中的光线偏折与波传播。然而，这种光学度规通常是从已知的 $g_{\mu\nu}$ 出发的重写，而非从更底层的信息或计算结构导出的约束。

另一方面，Jacobson 的工作表明，若假定任意局域 Rindler 视界的熵与其面积成正比，并要求对所有局域视界都满足 Clausius 关系 $\delta Q = T dS$，则爱因斯坦场方程可以被解释为一种"状态方程"，在某种热力学极限下将能流与曲率联系起来。Verlinde 随后提出引力可以视为位置相关信息的熵力，从而在全息框架下导出牛顿引力定律及其相对论推广。虽然这些工作为"引力的熵力起源"提供了启发，但其原始表述通常假设了连续时空、局域热平衡以及全息屏等结构，并未直接与离散 QCA 框架和局域信息处理能力的约束相结合；同时，也面临诸多批评与修正建议。

本文的目标是在 QCA 视角下，将这几条线索统一起来：

1. 从 QCA 幺正性与局域信息处理密度出发，提出"局域信息体积守恒"原理；

2. 在静态、各向同性情形下证明：该原理唯一选出一类双因子缩放的光学度规 $ds^2 = -n^{-2}c^2dt^2 + n^2\delta_{ij}dx^i dx^j$，其中 $n(x)$ 由局域信息处理负载给出；

3. 在弱场极限下，证明这一度规与广义相对论 PPN 形式的线性化度规等价，从而给出正确的光线偏折与 Shapiro 延迟；

4. 在 Jacobson 与 Verlinde 的启发下，将几何作用量解释为信息–几何的熵泛函，提出信息–引力变分原理（IGVP），并证明其局域平衡条件等价于标准爱因斯坦场方程。

在此意义下，引力不再是"附加在 QCA 上的连续几何背景"，而是 QCA 网络在局域信息处理负载不均匀的情况下，为维持整体幺正性和信息体积守恒而被迫采用的一种有效光学几何。

---

## Model & Assumptions

本节构造从离散 QCA 到连续光学度规的建模框架，并给出明确的假设列表。

### 1. QCA 宇宙与局域信息处理密度

设底层宇宙由一 QCA 对象描述

$$
\mathfrak U_{\text{QCA}} = (\Lambda, \mathcal H_{\text{cell}}, U, \omega_0),
$$

其中：

* $\Lambda \subset \mathbb Z^3$ 为三维格点集合，格距为 $a$；

* 每个元胞携带有限维 Hilbert 空间 $\mathcal H_{\text{cell}} \cong \mathbb C^{d}$；

* 全局 Hilbert 空间为准局域张量积 $\mathcal H = \bigotimes_{x\in\Lambda} \mathcal H_{\text{cell}}$；

* 时间演化由具有有限传播半径 $R a$ 的幺正算符 $U$ 实现：

  $$
  \rho_{n+1} = U \rho_n U^\dagger,
  $$
  
  其中 $\rho_n$ 为第 $n$ 个离散时间步的全局态；

* $\omega_0$ 给定初始态或初始态族。

在给定截断尺度 $L \gg a$、$T \gg \Delta t$ 下，可对 QCA 作粗粒化，定义连续坐标 $x^\mu = (ct,\mathbf x)$，并引入有效场论描述。QCA 的幺正性保证了全系统希尔伯特空间维数和冯·诺伊曼熵的守恒，但局域上量子纠缠与信息处理负载可以高度非均匀。

定义无量纲的局域信息处理密度场

$$
\rho_{\text{info}}(x) \in [0,1),
$$

表示在单位坐标体积、单位坐标时间内，被内部自旋、局域纠缠、反馈回路等"内禀演化"消耗的计算预算占真空最大预算的比例。

对应地，引入局域信息拥塞因子

$$
n(x) = \frac{1}{1 - \alpha \rho_{\text{info}}(x)} \ge 1,
$$

其中 $\alpha \in (0,1)$ 为耦合常数，用于刻度规范。$n(x)=1$ 对应真空（无额外负载），$n(x)>1$ 对应高信息负载区域。

在 QCA 的连续极限中，自由光锥的最大群速度由格距与时间步长给出

$$
c = a/\Delta t.
$$

当局域信息负载增大时，外部信号传播可用预算减少，表现为有效传播速度减小，即 $v_{\text{ext}}(x) < c$。

### 2. 局域信息体积守恒与缩放因子

考虑一个小的四维坐标体积元

$$
\mathrm d^4x = \mathrm dt\,\mathrm d^3\mathbf x.
$$

在 QCA 粗粒化中，对应于某一有限元胞簇 $\Omega \subset \Lambda$ 在有限时间步内的演化。由于 QCA 的幺正性，$\Omega$ 内可分辨量子态的数目受局域 Hilbert 空间维数与纠缠结构约束，但在坐标重参数化下不应改变。

为刻画度规变形，引入时间与空间的局域缩放因子：

* 物理固有时间与坐标时间关系为

  $$
  \mathrm d\tau = \eta_t(x)\,\mathrm dt;
  $$

* 物理长度元与坐标长度元关系为

  $$
  \mathrm d\ell = \eta_x(x)\,|\mathrm d\mathbf x|.
  $$

则物理四体积元

$$
\mathrm dV_4^{\text{phys}} = \mathrm d\tau\,\mathrm d^3\ell = \eta_t(x)\,\eta_x^3(x)\,\mathrm dt\,\mathrm d^3\mathbf x.
$$

定义单位坐标体积、单位坐标时间内的"信息容量"为可分辨量子态的最大对数数目 $\mathcal C(x)$。在信息本体论下，假设 QCA 的局域结构在粗粒化中给出的 $\mathcal C(x)$ 与物理四体积元成正比，但受局域信息负载 $\rho_{\text{info}}(x)$ 抑制：

$$
\mathcal C(x) \propto \frac{\eta_t(x)\,\eta_x^3(x)}{n(x)}.
$$

这里 $n(x)$ 表征单位物理时间内可用的演化步数压缩。为了确保在纯坐标重参数化下局域信息容量不变，引入

**公理 1（局域信息体积守恒）**

在从 QCA 到连续流形的映射中，对于任意足够小的流形片段，局域信息容量满足

$$
\eta_t(x)\,\eta_x^3(x) \propto n(x),
$$

且在微扰弱场极限中退化为 Minkowski 值 $\eta_t = \eta_x = n = 1$。

在本文关注的静态、各向同性且弱场的情形下，实际观测约束主要来自于光线偏折与时间延迟，这些观测主要敏感于 $t$–$r$ 子空间中的度规结构。为此，我们进一步采用如下简化假设。

**假设 1（各向同性简化）**

在所考虑的尺度上，局域信息负载在空间上各向同性，即

$$
\eta_x(x) = \eta_s(x),
$$

$\eta_s$ 对三个空间方向统一缩放，且 $n(x)$ 仅依赖于势函数 $\Phi(x)$。

**假设 2（二维光锥保形性）**

要求任意径向光锥在 $(t,r)$ 二维子空间中的面积元保持共形不变，从而维持零测地线在 QCA 中的"因果预算"守恒。这等价于要求二维子度规的行列式在坐标变换下只受整体尺度因子影响。

在静态、球对称度规

$$
ds^2 = -A(r)c^2dt^2 + B(r)(dr^2 + r^2 d\Omega^2)
$$

的情形下，$(t,r)$ 子空间的度规行列式为

$$
\det g_{(t,r)} = -A(r)B(r).
$$

二维光锥保形性与局域信息体积守恒共同给出

**命题 1**

在上述设定下，$A(r)B(r) = 1$。

直观上，这是因为：若时间被因信息负载拉伸一个因子 $\eta_t$，则为了保持光锥面积与 QCA 中零测地线的"离散步数壳层"不变，径向方向必须缩放 $\eta_r = \eta_t^{-1}$，从而 $A \propto \eta_t^2$、$B \propto \eta_r^2$ 给出 $A B = \eta_t^2 \eta_r^2 = 1$。该结论将在附录 A 中给出更系统的 Liouville–型推导。

于是可取参数化

$$
A(r) = n^{-2}(r),\quad B(r) = n^2(r),
$$

得到一族光学度规

$$
ds^2 = -n^{-2}(r)c^2dt^2 + n^2(r)\left(dr^2 + r^2 d\Omega^2\right).
$$

这就是本文所说的"信息–光学度规"。

### 3. 信息折射率与牛顿势的匹配

为了在宏观尺度上恢复牛顿引力势，考虑慢速试验粒子在该度规中的测地线方程。设度规一般形式为

$$
ds^2 = -(1+2\Phi/c^2)c^2dt^2 + (1-2\gamma\Phi/c^2)\delta_{ij}dx^i dx^j,
$$

在 PPN 形式中 $\gamma = 1$ 对应一般相对论。弱场、慢速极限下，时间分量决定的色散关系给出有效势 $\Phi$，粒子加速度满足

$$
\mathrm d^2\mathbf x/\mathrm dt^2 \approx -\nabla\Phi.
$$

将信息–光学度规展开到一阶：

$$
n(x) = 1 + \epsilon(x),\quad |\epsilon|\ll 1,
$$

则

$$
n^{-2} = (1+\epsilon)^{-2} \approx 1 - 2\epsilon,\quad n^2 \approx 1 + 2\epsilon.
$$

因此线元变为

$$
ds^2 \approx -(1-2\epsilon)c^2dt^2 + (1+2\epsilon)\delta_{ij}dx^i dx^j.
$$

与 PPN 形式比较可见，当取

$$
\epsilon(x) = -\Phi(x)/c^2
$$

时，得到

$$
g_{00} = -(1+2\Phi/c^2),\quad g_{ij} = (1-2\Phi/c^2)\delta_{ij},
$$

即 $\gamma = 1$ 的广义相对论弱场度规。由此可定义

**定义 1（信息折射率）**

设牛顿势 $\Phi(x)$ 满足 $\nabla^2\Phi = 4\pi G\rho$，则信息拥塞因子定义为

$$
n(x) = 1 - \Phi(x)/c^2.
$$

在 $\Phi < 0$ 的引力势阱中有 $n(x) > 1$，对应局域信息负载较高、有效光速减小的区域。

---

## Main Results (Theorems and alignments)

在上述模型与假设下，本文的主要结果可概括为以下几个定理与推论。

### Theorem 1（局域信息体积守恒 ⇒ 光学度规）

在静态、球对称、弱场且可由 QCA 粗粒化得到的区域中，若满足：

1. 底层演化为局域幺正 QCA；

2. 局域信息体积守恒公理成立；

3. 各向同性简化与二维光锥保形性假设成立；

则连续极限中允许的度规必属于信息–光学度规族

$$
ds^2 = -n^{-2}(r)c^2dt^2 + n^2(r)(dr^2 + r^2d\Omega^2),
$$

其中 $n(r)\ge 1$ 为由局域信息处理密度确定的标量场。

此外，在弱场极限下，要求存在牛顿势 $\Phi(r)$ 使得慢速粒子运动满足 $\mathrm d^2\mathbf x/\mathrm dt^2 \approx -\nabla\Phi$ 则唯一确定

$$
n(r) = 1 - \Phi(r)/c^2 + \mathcal O(\Phi^2/c^4).
$$

### Theorem 2（信息–光学度规的 PPN 对齐）

在定理 1 的设定下，线元在 $|\Phi|/c^2 \ll 1$ 的极限中展开为

$$
ds^2 = -(1+2\Phi/c^2)c^2dt^2 + (1-2\Phi/c^2)(dr^2 + r^2d\Omega^2) + \mathcal O(\Phi^2/c^4).
$$

因此，在 PPN 记号下有

$$
\gamma = 1,
$$

从而自动给出：

1. 光线经过点质量 $M$ 周围、冲量参数为 $b$ 的弱场偏折角

   $$
   \Delta\theta = \frac{4GM}{bc^2} + \mathcal O\left(\frac{G^2M^2}{b^2c^4}\right);
   $$

2. Shapiro 延迟

   $$
   \Delta t_{\text{Shapiro}} \propto (1+\gamma)\frac{GM}{c^3}\ln\frac{4r_E r_R}{b^2}
   $$
   
   中 $1+\gamma = 2$，与标准广义相对论完全一致。

因此，在标量折射率场的框架下，若同时考虑时间分量与空间分量的协同缩放并满足 $A(r)B(r)=1$，即可自然避免传统标量引力理论中仅得到半数偏折角的历史困难。

### Theorem 3（信息–引力变分原理与爱因斯坦方程）

设总"信息熵"泛函定义为

$$
\mathcal S_{\text{tot}}[g,\Psi] = \mathcal S_{\text{geom}}[g] + \mathcal S_{\text{info}}[g,\Psi],
$$

其中：

* $\Psi$ 代表物质与信息自由度；

* 几何部分取 Jacobson–Iyer–Wald 类型的几何熵形式，即在适当归一化下

  $$
  \delta \mathcal S_{\text{geom}}[g] = \frac{1}{4G}\int_{\mathcal M} \sqrt{-g}\,(R_{\mu\nu} - \tfrac 12 R g_{\mu\nu})\,\delta g^{\mu\nu}\,\mathrm d^4x;
  $$

* 信息部分的变分定义信息应力张量

  $$
  T^{\text{info}}_{\mu\nu} = -\frac{2}{\sqrt{-g}}\frac{\delta \mathcal S_{\text{info}}}{\delta g^{\mu\nu}}.
  $$

若要求在所有局域观测者所见的 Rindler 小邻域上存在局域平衡，使得对任意紧支集的度规变分都有

$$
\delta \mathcal S_{\text{tot}} = 0,
$$

则该条件等价于

$$
R_{\mu\nu} - \tfrac 12 R g_{\mu\nu} = 8\pi G\,T^{\text{info}}_{\mu\nu}.
$$

在宏观极限下，若将 $T^{\text{info}}_{\mu\nu}$ 与标准能动张量 $T_{\mu\nu}$ 认同，则恢复通常形式的爱因斯坦场方程。

---

## Proofs

本节给出上述主要定理的证明思路，详细计算放置于附录。

### Proof of Theorem 1（概要）

1. **二维光锥与 Liouville 不变性**

   在 QCA 的几何光学极限下，考虑在 $(t,r)$ 子空间中的径向光线。对每一条离散光线，可视为在相空间 $(t,r;p_t,p_r)$ 上的 Hamilton 流，其 Liouville 定理保证相空间体积元 $\mathrm d t\,\mathrm d r\,\mathrm d p_t\,\mathrm d p_r$ 的不变性。粗粒化到连续度规后，要求零测地线在 $(t,r)$ 子空间上的面积元 $\sqrt{-\det g_{(t,r)}}\,\mathrm dt\,\mathrm dr$ 与对应的 QCA 步数壳层成正比，从而要求 $\det g_{(t,r)}$ 仅通过整体因子缩放。

   在静态、球对称度规

   $$
   ds^2 = -A(r)c^2dt^2 + B(r)dr^2 + \dots
   $$
   
   中，有 $\det g_{(t,r)} = -A(r)B(r)$。通过将 QCA 上的步数壳层与连续光锥面积元匹配，可证明 $A(r)B(r) = \text{const}$。在无穷远处 $r\to \infty$ 要求度规退化为 Minkowski（$A\to 1,B\to 1$），从而常数为 1，得到 $A(r)B(r)=1$。

2. **各向同性与缩放参数化**

   在空间三维各向同性假设下，将 $B(r)$ 统一赋给径向与角向部分，得到

   $$
   ds^2 = -A(r)c^2dt^2 + B(r)(dr^2 + r^2d\Omega^2).
   $$
   
   由 $A(r)B(r)=1$ 可对两个函数用单一标量 $n(r)$ 表示：

   $$
   A(r) = n^{-2}(r), B(r) = n^2(r).
   $$

3. **与牛顿势的匹配唯一性**

   将线元展开到一阶：

   $$
   n(r) = 1 + \epsilon(r) \Rightarrow A(r) \approx 1 - 2\epsilon(r), B(r) \approx 1+2\epsilon(r).
   $$
   
   慢速极限下的测地线方程可写成

   $$
   \mathrm d^2\mathbf x/\mathrm dt^2 = -\tfrac{c^2}{2}\nabla g_{00} + \mathcal O(v^2/c^2).
   $$
   
   代入 $g_{00}= -A(r) \approx -(1-2\epsilon)$，得到

   $$
   \mathrm d^2\mathbf x/\mathrm dt^2 \approx -\nabla(c^2\epsilon).
   $$
   
   为使之与牛顿定律 $\mathrm d^2\mathbf x/\mathrm dt^2 = -\nabla\Phi$ 一致，唯一可能是

   $$
   c^2\epsilon(r) = \Phi(r),
   $$
   
   即 $\epsilon(r) = \Phi(r)/c^2$。

   由 $\Phi < 0$ 的约定，为保持 $n\ge 1$，重定义 $\epsilon(r) = -\Phi(r)/c^2$，从而确定

   $$
   n(r) = 1 - \Phi(r)/c^2.
   $$

由此完成定理 1 的证明概要，完整的相空间推导见附录 A。

### Proof of Theorem 2（概要）

1. **PPN 形式展开**

   将

   $$
   n(r) = 1 - \Phi(r)/c^2
   $$
   
   代入信息–光学度规，展开到一阶得到

   $$
   g_{00} = -n^{-2} \approx -(1+2\Phi/c^2), \quad g_{ij} = n^2\delta_{ij} \approx (1-2\Phi/c^2)\delta_{ij}.
   $$
   
   与标准 PPN 记号比较，可读出 $\gamma = 1$。

2. **光学度规与有效折射率**

   对任一静态时空，三维光学度规定义为

   $$
   \gamma_{ij} = -g_{00}^{-1}g_{ij},
   $$
   
   零测地线在四维时空上的投影等价于该光学三维流形上的测地线。在信息–光学度规中有

   $$
   \gamma_{ij} = n^4(r)\delta_{ij}.
   $$
   
   因此光在三维空间中的有效折射率为

   $$
   N_{\text{eff}}(r) = n^2(r) = \left(1 - \Phi(r)/c^2\right)^2 \approx 1 - 2\Phi(r)/c^2.
   $$

3. **弱场光线偏折**

   采用几何光学近似，在平面内传播的光线偏折角可以写为

   $$
   \Delta\theta \approx \int_{-\infty}^{\infty} \frac{\partial}{\partial b}N_{\text{eff}}(r)\,\mathrm dl,
   $$
   
   其中 $b$ 为冲量参数，$\mathrm dl$ 为沿未扰动直线轨迹的路径元。对点质量 $M$ 有 $\Phi(r) = -GM/r$，从而

   $$
   N_{\text{eff}}(r) \approx 1 + \frac{2GM}{rc^2}.
   $$
   
   将 $r = \sqrt{b^2 + z^2}$ 代入并积分得到

   $$
   \Delta\theta = \frac{4GM}{bc^2},
   $$
   
   与广义相对论的标准结果一致。

   这一计算在附录 B 中给出详细步骤。

4. **Shapiro 延迟**

   Shapiro 延迟可由传播时间积分

   $$
   t = \int N_{\text{eff}}(r)\,\mathrm dl/c
   $$
   
   与平直空间中的传播时间之差给出，展开到一阶同样得到

   $$
   \Delta t_{\text{Shapiro}} \propto (1+\gamma)\frac{GM}{c^3}\ln(\dots),
   $$
   
   由于 $\gamma = 1$，与实验结果符合。

由此，定理 2 得证。

### Proof of Theorem 3（概要）

定理 3 实质上是在 QCA–信息本体论语义下，对 Jacobson"爱因斯坦方程即状态方程"结果的重述与推广。其证明可概括为以下步骤：

1. **局域视界与 QCA 信息流**

   对任意一点 $p \in M$，构造穿过 $p$ 的局域 Rindler 视界及其生成向量场。QCA 的因果结构保证存在与此视界对应的一族"离散光锥"，其上信息流入视界的能流 $\delta Q$ 可以用 QCA 局域能量–信息流密度描述。

2. **几何熵与 Noether 荷**

   对于任意满足 $f(R)$ 型拉格朗日密度的几何作用量，可以定义 Noether 荷与对应的几何熵密度。对爱因斯坦–Hilbert 作用量 $\mathcal L = R/(16\pi G)$ 来说，这一构造恢复 Bekenstein–Hawking 面积熵 $S_{\text{BH}} = A/(4G)$。

3. **信息熵与 Clausius 关系**

   将 QCA 中穿越视界的信息流解释为热流 $\delta Q$，将视界的几何熵与 QCA 在视界处可访问自由度的对数数目对应，则局域平衡条件可写为

   $$
   \delta Q = T\delta S_{\text{geom}} + T\delta S_{\text{info}},
   $$
   
   其中 $T$ 为加速观察者所见的 Unruh 温度。把 $\delta S_{\text{info}}$ 对 $\delta g^{\mu\nu}$ 的变分定义为信息应力张量 $T^{\text{info}}_{\mu\nu}$。

4. **对任意视界与任意变分的要求**

   若要求上述 Clausius 关系对穿过任意点的任意局域视界、以及所有紧支集的度规变分成立，则可以证明几何熵变分必须满足

   $$
   \delta \mathcal S_{\text{geom}} = \frac{1}{4G}\int (R_{\mu\nu} - \tfrac 12 R g_{\mu\nu})\delta g^{\mu\nu}\sqrt{-g}\,\mathrm d^4x,
   $$
   
   从而得到

   $$
   R_{\mu\nu} - \tfrac 12 R g_{\mu\nu} = 8\pi G T^{\text{info}}_{\mu\nu}.
   $$

因此，爱因斯坦场方程可以被解释为"几何熵与信息熵和谐极值"的条件。详细变分见附录 C。

---

## Model Apply

本节讨论信息–光学度规模型在若干物理背景中的具体应用。

### 1. 太阳系与弱场引力透镜

对太阳系尺度，可近似将太阳视为点质量 $M_\odot$，牛顿势为

$$
\Phi(r) = -GM_\odot/r.
$$

信息–光学度规给出

$$
n(r) = 1 + GM_\odot/(rc^2) + \mathcal O(G^2M_\odot^2/(r^2c^4)),
$$

光线偏折角

$$
\Delta\theta = 4GM_\odot/(bc^2),
$$

Shapiro 延迟

$$
\Delta t_{\text{Shapiro}} \sim 2GM_\odot/c^3\ln(\dots),
$$

与 Cassini 等实验的高精度测量相容，这一部分约束可直接转化为对 $n(r)$ 与 $\rho_{\text{info}}(r)$ 之间关系的实验界。

### 2. 星系尺度的引力透镜与暗物质剖面

在星系和星系团尺度，引力透镜观测提供了对暗物质质量分布的几何约束。在信息–光学度规框架下，光学折射率 $N_{\text{eff}} = n^2$ 由总势 $\Phi_{\text{tot}} = \Phi_{\text{baryon}} + \Phi_{\text{DM}}$ 决定。若暗物质的本体论被替换为"额外的信息负载"，则星系旋转曲线与透镜剖面之间的一致性条件可以被重写为对 $\rho_{\text{info}}(x)$ 场的反演问题。

这为将暗物质问题重新表述为"星系级信息处理预算如何分布"的反问题提供了途径，可以在数值模拟中通过不同形式的 $\rho_{\text{info}}$ 场来拟合观测数据。

### 3. QCA 模型中的连续极限与"弯曲"格点

在具体的 QCA 模型中，可以通过改变局域演化算符的参数，使某一区域的"计算步长"有效减小。例如，在一维 Dirac–QCA 中，质量项与格点间耦合决定了有效光速与传播带宽。在高质量或高纠缠密度区域，可以有效理解为 $n(x)$ 增大、$v_{\text{ext}}(x)$ 减小。

如果在大尺度上将这些局域参数视为连续场，则可将 QCA 上的"弯曲"格点结构通过信息–光学度规映射到连续时空几何，从而提供一种从 QCA 出发的"计算–几何"字典。

### 4. 随机图与 emergent metric

已有工作表明，在某些随机离散结构上，通过适当的连接规则与演化机制，可以在大尺度上涌现出有效的连续度规与曲率结构。在这些模型中，局域连通度与路径长度的统计特性可以通过信息–光学度规进一步翻译为 $n(x)$ 场与 $\rho_{\text{info}}(x)$ 的统计分布，从而将"随机图涌现几何"嵌入本文的信息–引力框架。

---

## Engineering Proposals

本文框架不仅具有概念意义，还自然导出一系列可在数值和实验层面检验的工程提案。

### 1. 数值 QCA 模拟中的"信息透镜"

在高维 QCA 模型上，预先设定空间上非均匀的局域更新规则，使得某一区域的有效传播速度减小，即构造出一个离散的 $n(x)$ 场。通过在 QCA 上注入波包并追踪其传播路径，可以数值测量：

* 波包偏折轨迹是否与信息–光学度规预测的测地线一致；

* 延迟时间是否满足 Shapiro 型对数修正；

* 多源–多透镜配置下的干涉图样是否与连续光学透镜模型一致。

这类模拟不需要真实引力场，而仅依赖于离散网络的可编程演化规则，可在量子模拟或经典离散网络上实现。

### 2. 光学或微波实验中的类引力透镜

在光学或微波频段，可以利用空间–时间可调谐的介质（如超材料、光子晶体或可编程介质）实现有效折射率分布 $N_{\text{eff}}(x)$。若介质的群速度随频率与位置变化可精确控制，则可在实验上实现：

* 对应于点质量或星系势阱的折射率剖面；

* 将"时间拉伸"通过色散关系与能量存储机制模拟，从而在有效介质中实现近似的信息–光学度规。

通过测量波前的偏折与传播时间，可以在"实验室引力光学"中直接检验信息–光学度规的预测。

### 3. 基于精密定时的天体测量

引力透镜和 Shapiro 延迟目前已在射电脉冲星、FRB 与雷达回波中得到高精度测量。本文框架暗示，当 $\rho_{\text{info}}(x)$ 在时间尺度上有显著变化时，$n(x,t)$ 亦随时间变化，从而引入额外的"信息时变透镜"效应。这在双星系统、AGN 或并合星系中的大尺度可变源上可能产生可观测信号，可设计对应的时域观测计划，对 $n(x,t)$ 的时间依赖性施加约束。

### 4. 量子信息处理系统中的"有效引力"

在大型量子计算平台（如二维超导量子芯片）上，局域门操作深度与纠缠熵分布决定了信息传播的"拥塞模式"。通过刻意在某一区域注入大量纠缠并测量探测量子比特的信号传播延迟，可以在人工系统中构造"信息引力透镜"的类比实验，验证"局域信息体积守恒"对传播锥的约束。

---

## Discussion (risks, boundaries, past work)

### 1. 与传统熵力引力方案的关系

Jacobson 的工作将爱因斯坦方程视为热力学状态方程，Verlinde 则进一步提出引力是位置相关信息的熵力，这些观点为"引力非基本而是涌现"的图景提供了重要线索。另一方面，关于熵力引力的批评指出：在具体模型中，熵力的类比并不总是严格成立，全息屏与试验粒子之间的关系也存在概念性困难。

本文与这些工作的差异在于：

* 以 QCA 与局域信息处理负载为基本对象，而非抽象全息屏；

* 利用局域信息体积守恒与光学度规构造，首先在弱场下重现广义相对论的 PPN 结构与实验检验结果；

* 将熵力视角收敛为 IGVP 中几何熵与信息熵的变分问题，从而在数学上与传统作用量形式兼容。

因此，可以将本文视为在"信息–几何–熵力"交汇处，对已有熵力方案的一个更加结构化、且与 QCA 本体相容的版本。

### 2. QCA 与 Lorentz 对称性的张力

离散格点结构天然破坏连续 Lorentz 对称性。QCA 模型必须在连续极限中"近似恢复"相对论对称性才能与现有粒子物理和引力实验相容。已有工作表明，在适当设计的 QCA 中，Dirac 与 Maxwell 方程可以在长波极限中涌现，Lorentz 不变性得到有效恢复，但在高能或短波极限中仍可能出现各向异性能量–动量关系。

本文的信息–光学度规假设默认了在考虑的尺度上可以采用连续、各向同性的度规描述，这在低能、弱场下是合理的。但在 Planck 级别或极高能宇宙射线传播中，QCA 微结构可能引入可观测的色散与各向异性修正，需要更精细的分析。

### 3. 信息折射率的反演与退化

在实际观测中，人们只能通过透镜成像与时间延迟反演出等效折射率 $N_{\text{eff}}(x)$，其分解为 $n(x)$ 与 $\rho_{\text{info}}(x)$ 之间并不唯一。例如，多种不同的 QCA 微观实现可能在连续极限中给出相同的 $n(x)$。因此，本文框架在本体论层面上依然存在"微观–宏观退化"，需要结合其他观测（如高阶相关函数、波包畸变等）来破缺退化。

### 4. 强场与非静态情形的推广

本文主要聚焦于静态、弱场、各向同性情形。对于黑洞附近强场区、并合双星或宇宙学膨胀背景，度规的一般形式远比信息–光学度规复杂。虽然可在局域静态近似下引入瞬时的 $n(x,t)$，但完整的强场推广需要：

* 在 QCA 中引入时间依赖的局域信息负载分布；

* 处理高度非局域的纠缠结构对 $n(x,t)$ 的影响；

* 将 IGVP 推广到非平衡态的广义熵流形式。

这些问题为未来工作留出了空间。

---

## Conclusion

本文在量子元胞自动机与信息本体论的框架下，提出并系统分析了"局域信息体积守恒"原理，并由此推导出一类双因子缩放的光学度规：

$$
ds^2 = -n^{-2}(x)c^2dt^2 + n^2(x)\delta_{ij}dx^i dx^j.
$$

在静态、球对称、弱场极限中，局域信息体积守恒与牛顿极限的要求唯一地将 $n(x)$ 与牛顿势 $\Phi(x)$ 关联为 $n(x) = 1 - \Phi(x)/c^2$。由此得到的度规展开为

$$
ds^2 = -(1+2\Phi/c^2)c^2dt^2 + (1-2\Phi/c^2)\delta_{ij}dx^i dx^j + \mathcal O(\Phi^2/c^4),
$$

与广义相对论在 PPN 框架中的弱场线元完全一致，从而自然给出正确的光线偏折与 Shapiro 延迟，并在标量折射率场的图景下解决了 1911 年标量引力理论的"半角困境"。

进一步地，本文构造了信息–引力变分原理（IGVP），将几何作用量解释为几何熵，将 QCA 局域信息负载引入信息熵泛函，并在 Jacobson 式局域热力学条件下证明了 IGVP 的极值条件等价于带有信息应力张量的爱因斯坦场方程。由此，在 QCA–信息–几何三者之间建立了一条从微观离散演化到宏观连续引力方程的统一链条。

最后，本文提出了若干数值与实验上的工程方案，用于在 QCA 模拟、光学类引力实验、精密天体测量以及大型量子信息处理平台中检验局域信息体积守恒与信息–光学度规的预测。这些工作为将"宇宙作为量子计算"与"引力作为信息几何"两种视角汇聚为可检验理论提供了具体路径。

---

## Acknowledgements, Code Availability

作者感谢关于量子元胞自动机、广义相对论弱场检验、引力透镜与熵力引力等方向的既有工作所构成的理论背景，尤其是关于从热力学与信息论推导爱因斯坦方程的诸多研究。本文的数值实现与 QCA 模拟方案可在通用张量网络与格点模拟平台上实现，具体代码结构可按照本文所述的局域信息负载场 $\rho_{\text{info}}(x)$ 与折射率场 $n(x)$ 的定义进行实现。

---

## References

[1] A. Einstein, "On the Influence of Gravitation on the Propagation of Light," Annalen der Physik 35, 1911.

[2] T. Jacobson, "Thermodynamics of Spacetime: The Einstein Equation of State," Physical Review Letters 75, 1260–1263 (1995).

[3] C. M. Will, "The Confrontation between General Relativity and Experiment," Living Reviews in Relativity 17, 4 (2014).

[4] J. Bodenner and C. M. Will, "Deflection of light to second order: A tool for illustrating principles of general relativity," American Journal of Physics 71, 770–773 (2003).

[5] G. W. Gibbons and M. C. Werner, "Applications of the Gauss–Bonnet Theorem to Gravitational Lensing," Classical and Quantum Gravity 25, 235009 (2008).

[6] E. P. Verlinde, "On the Origin of Gravity and the Laws of Newton," Journal of High Energy Physics 2011(4), 029 (2011).

[7] S. Gao, "Is Gravity an Entropic Force?" Entropy 13, 936–948 (2011).

[8] T. Faber and M. Visser, "Combining rotation curves and gravitational lensing: How to measure the equation of state of dark matter in the galactic halo," Monthly Notices of the Royal Astronomical Society 372, 136–150 (2006).

[9] I. Kleftogiannis, "Emergent spacetime from purely random structures," Physical Review Research 4, 033004 (2022).

[10] A. Kobakhidze, "Gravity is not an Entropic Force," Physical Review D 83, 021502 (2011).

[11] R. M. Wald, "Black Hole Entropy is Noether Charge," Physical Review D 48, R3427–R3431 (1993).

[12] G. 't Hooft, *The Cellular Automaton Interpretation of Quantum Mechanics*, Springer, 2016.

[13] P. Arrighi, S. Facchini, and M. Forets, "Discrete Lorentz covariance for quantum walks and quantum cellular automata," New Journal of Physics 16, 093007 (2014).

[14] T. A. Brun, H. A. Carteret, and A. Ambainis, "Quantum walks driven by many coins," Physical Review A 67, 052317 (2003).

[15] L. Fidkowski et al., "A Quantum Cellular Automaton Framework for Symmetry Protected Topological Phases," 2025.

[16] W. Javed et al., "Weak gravitational lensing in dark matter and plasma mediums for wormhole-like static aether solution," European Physical Journal C 82, 1044 (2022).

[17] R. K. Solanki, "Kottler Spacetime in Isotropic Static Coordinates," arXiv:2103.10002 (2021).

[18] J. Norton, "The historical foundation of Einstein's general theory of relativity," PhD Thesis, University of Pittsburgh (1981).

[19] A. Övgün, "Deflection angle of photon through dark matter by black holes in Einstein–Maxwell–dilaton gravity," Advances in High Energy Physics 2019, 1–9 (2019).

---

## Appendix A：局域信息体积守恒与 $A(r)B(r)=1$ 的 Liouville 型推导

考虑静态、球对称度规在 $(t,r)$ 子空间的限制：

$$
ds^2_{(t,r)} = -A(r)c^2dt^2 + B(r)dr^2.
$$

令共轭动量为

$$
p_t = g_{tt}\dot t = -A(r)c^2\dot t,\quad p_r = g_{rr}\dot r = B(r)\dot r,
$$

其中点表示对仿射参数 $\lambda$ 求导。零测地线满足 Hamiltonian 约束

$$
\mathcal H = \tfrac 12 g^{\mu\nu}p_\mu p_\nu = 0,
$$

在 $(t,r)$ 子空间上为

$$
\mathcal H = -\tfrac 12 A^{-1}(r)p_t^2/c^2 + \tfrac 12 B^{-1}(r)p_r^2 = 0.
$$

定义相空间体积元

$$
\mathrm d\Gamma = \mathrm dt\,\mathrm dr\,\mathrm dp_t\,\mathrm dp_r.
$$

Hamilton 方程保持 $\mathrm d\Gamma$ 不变，这是 Liouville 定理的内容。对零测地线壳层 $\mathcal H=0$，体积元可写为

$$
\mathrm d\Gamma|_{\mathcal H=0} = \mathrm dt\,\mathrm dr\,\mathrm dp_r\,\mathrm d\phi,
$$

其中 $\phi$ 为参数化壳层的角变量。由于 QCA 的幺正性要求在粗粒化映射中零测地线壳层对应的"步数密度"不变，故 $\sqrt{-\det g_{(t,r)}}\,\mathrm dt\,\mathrm dr$ 必须与 $\mathrm dt\,\mathrm dr$ 的比例因子保持常数。

具体地，

$$
\sqrt{-\det g_{(t,r)}} = \sqrt{A(r)B(r)}.
$$

若允许 $A(r)B(r)$ 随 $r$ 变化，则可通过坐标重定义 $t\to t'(t,r),r\to r'(r)$ 吸收部分变化，但零测地线壳层上的"步数壳层密度"将不再只依赖于局域信息负载，而掺入纯坐标自由度。为了保证"信息体积"只反映 QCA 中的物理负载而非坐标选择，要求 $A(r)B(r) = \text{const}$。

在无穷远处 $r\to\infty$ 要求度规趋于 Minkowski，即 $A(\infty)=B(\infty)=1$，因此常数必须为 1，得到

$$
A(r)B(r) = 1.
$$

结合各向同性假设，即可写为

$$
A(r) = n^{-2}(r),B(r)=n^2(r).
$$

---

## Appendix B：信息–光学度规下的光线偏折计算

考虑平面内的光线传播，选取平面 $\theta = \pi/2$，线元为

$$
ds^2 = -n^{-2}(r)c^2dt^2 + n^2(r)\left(dr^2 + r^2d\varphi^2\right).
$$

零测地线满足 $ds^2 = 0$，由 Killing 对称性有守恒量

$$
E = -g_{tt}\dot t = n^{-2}(r)c^2\dot t,\quad L = g_{\varphi\varphi}\dot\varphi = n^2(r)r^2\dot\varphi.
$$

其中 $E$ 与 $L$ 分别为"能量"与"角动量"。零测地线条件给出

$$
0 = -n^{-2}c^2\dot t^2 + n^2\dot r^2 + n^2r^2\dot\varphi^2.
$$

消去 $\dot t,\dot\varphi$ 得到径向方程

$$
\dot r^2 + \frac{L^2}{n^4r^2} = \frac{E^2}{c^2n^4}.
$$

定义冲量参数 $b = Lc/E$，并令 $u(\varphi) = 1/r(\varphi)$，可将径向方程化为

$$
\left(\frac{\mathrm du}{\mathrm d\varphi}\right)^2 + u^2 = \frac{1}{b^2}n^{-4}(r(u)).
$$

在弱场极限下，取

$$
n(r) = 1 - \Phi(r)/c^2,\quad \Phi(r) = -GM/r,
$$

则

$$
n^{-4}(r) \approx 1 - 4\Phi(r)/c^2 = 1 + 4GM/(rc^2).
$$

于是得到微扰方程

$$
\frac{\mathrm d^2u}{\mathrm d\varphi^2} + u = \frac{2GM}{c^2b^2}.
$$

其解为

$$
u(\varphi) = \frac{\sin\varphi}{b} + \frac{GM}{c^2b^2}(1+\cos\varphi) + \mathcal O(G^2M^2/(b^3c^4)).
$$

当 $\varphi$ 从 $-\pi/2 - \delta$ 变化到 $\pi/2 + \delta$ 时，光线由无穷远到无穷远，要求 $u(\varphi)\to 0$，解得偏折角

$$
\Delta\varphi = 2\delta = \frac{4GM}{bc^2}.
$$

这与标准广义相对论计算完全一致。

另一种更简洁的推导是直接在光学度规下使用近轴近似与积分形式

$$
\Delta\theta \approx \int_{-\infty}^{\infty}\nabla_\perp N_{\text{eff}}(r)\,\mathrm dl,
$$

这里 $N_{\text{eff}} = n^2 \approx 1 + 2GM/(rc^2)$，沿未扰动直线 $r=\sqrt{b^2+z^2}$ 积分同样给出 $4GM/(bc^2)$。

---

## Appendix C：信息–引力变分原理的变分计算

设几何熵泛函

$$
\mathcal S_{\text{geom}}[g] = \frac{1}{4G}\int_{\mathcal H} \mathrm d^2\Sigma\,\kappa,
$$

其中 $\mathcal H$ 为局域视界截面，$\kappa$ 为表面引力。Jacobson 与后续工作表明，相应的体积泛函变分可写为

$$
\delta \mathcal S_{\text{geom}} = \frac{1}{4G}\int_{\mathcal M}(R_{\mu\nu} - \tfrac 12R g_{\mu\nu})\delta g^{\mu\nu}\sqrt{-g}\,\mathrm d^4x.
$$

信息熵泛函取形式

$$
\mathcal S_{\text{info}}[g,\Psi] = \int_{\mathcal M} s_{\text{info}}(g,\Psi)\sqrt{-g}\,\mathrm d^4x,
$$

其中 $s_{\text{info}}$ 为局域信息熵密度，取决于度规与 QCA 中的物质–信息自由度。其变分为

$$
\delta \mathcal S_{\text{info}} = \int \left(\frac{\partial s_{\text{info}}}{\partial g^{\mu\nu}}\delta g^{\mu\nu} + \frac{\partial s_{\text{info}}}{\partial\Psi}\delta\Psi\right)\sqrt{-g}\,\mathrm d^4x + \int s_{\text{info}}\delta\sqrt{-g}\,\mathrm d^4x.
$$

利用

$$
\delta\sqrt{-g} = -\tfrac 12\sqrt{-g}g_{\mu\nu}\delta g^{\mu\nu},
$$

可整理为

$$
\delta \mathcal S_{\text{info}} = -\tfrac 12\int T^{\text{info}}_{\mu\nu}\delta g^{\mu\nu}\sqrt{-g}\,\mathrm d^4x + \int \frac{\partial s_{\text{info}}}{\partial\Psi}\delta\Psi\sqrt{-g}\,\mathrm d^4x,
$$

其中定义

$$
T^{\text{info}}_{\mu\nu} = -2\frac{\partial s_{\text{info}}}{\partial g^{\mu\nu}} + s_{\text{info}} g_{\mu\nu}.
$$

总熵变分为

$$
\delta \mathcal S_{\text{tot}} = \frac{1}{4G}\int (R_{\mu\nu} - \tfrac 12R g_{\mu\nu})\delta g^{\mu\nu}\sqrt{-g}\,\mathrm d^4x - \tfrac 12\int T^{\text{info}}_{\mu\nu}\delta g^{\mu\nu}\sqrt{-g}\,\mathrm d^4x + \dots.
$$

要求对任意紧支集的度规变分 $\delta g^{\mu\nu}$ 有 $\delta \mathcal S_{\text{tot}} = 0$ 且物质场满足各自的 Euler–Lagrange 方程，则必有

$$
R_{\mu\nu} - \tfrac 12R g_{\mu\nu} = 8\pi G\,T^{\text{info}}_{\mu\nu}.
$$

在宏观极限下，若将 $T^{\text{info}}_{\mu\nu}$ 与标准能动张量 $T_{\mu\nu}$ 认同，则恢复通常的爱因斯坦场方程。这一推导展示了 IGVP 与标准作用量形式之间的等价性，同时赋予几何熵与信息熵明确的信息–几何含义。

