# 离散视界上的全息熵：量子元胞自动机对黑洞信息悖论的幺正解

*Holographic Entropy from Discrete Causal Horizons: A Unitary Solution to the Black Hole Information Paradox in Quantum Cellular Automata*

---

## Abstract

黑洞信息悖论源于广义相对论中事件视界的因果隔离与量子理论全局幺正性之间的张力。半经典场论将黑洞视为具有温度 $T_H$ 与熵 $S_{\mathrm{BH}} = k_B A / (4 \ell_P^2)$ 的热力学系统，其中 $A$ 为视界面积，而霍金辐射在半经典极限下呈近似热谱，这意味着纯态坍缩形成的黑洞在完全蒸发后将演化为混合态，从而导致幺正性表观破坏。

本文在量子元胞自动机（quantum cellular automaton, QCA）的离散本体论与信息速率守恒 $v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2$ 的框架下，提出并分析一种黑洞的微观模型。核心思想是：视界不是几何上绝对的因果边界，而是 QCA 网络中信息外传速率 $v_{\mathrm{ext}}$ 被抑制、内部相位演化速率 $v_{\mathrm{int}}$ 饱和的临界层，记为"信息冻结层"。在这一离散视界上，跨越曲面的局域连接（Link）承担了内外区域之间的全部纠缠与信息通道。

在明确给出 QCA 宇宙模型、光学度规与离散视界的定义后，本文证明：

1. 对任意满足局域有限度数与普朗克尺度格距 $a \sim \ell_P$ 的 QCA 网络，视界上跨越曲面的连接数目 $N_{\mathrm{link}}$ 与面积满足 $N_{\mathrm{link}} \propto A / \ell_P^2$。

2. 若每条连接在黑洞平衡态时近似处于最大纠缠态，则对外部观测者的冯·诺依曼熵为

   $$
   S_{\mathrm{BH}} = \ln 2 \cdot N_{\mathrm{link}} \propto \frac{A}{\ell_P^2}.
   $$

3. 将连接视为 $\mathrm{SU}(2)$ 自旋网络的穿刺，采用环量子引力的面积谱 $A_j = 8 \pi \gamma \ell_P^2 \sqrt{j(j+1)}$ 与 $j = 1/2$，并取 Immirzi 参数 $\gamma = \ln 2 / (\pi \sqrt{3})$ 时，可恢复贝肯斯坦–霍金熵公式 $S_{\mathrm{BH}} = k_B A / (4 \ell_P^2)$，与既有黑洞熵计数结果保持一致。

进一步地，将黑洞与辐射视为有限维 Hilbert 空间上的纯态系统，并假设 QCA 演化为严格幺正的离散时间演化算符 $U$，本文利用 Page 定理与快速置乱假设，推导出辐射熵随时间的 Page 曲线：辐射纠缠熵在早期随时间单调增长，于黑洞与辐射可达 Hilbert 空间维数相当时达到峰值，随后随蒸发继续而下降至零，确保最终辐射态为纯态，从而在该框架下消解信息悖论。

本文将该 QCA 黑洞模型植入光学度规与信息体积守恒的统一方案之中，说明全息熵律可被视为 QCA 上离散视界的纠缠计数定理的连续极限外推。最后讨论了与环量子引力、AdS/CFT 及类比黑洞实验的关系，并给出若干可检验的观测与模拟建议，包括霍金辐射中非热相关性的搜索、类比黑洞平台上的纠缠结构测量等。

---

## Keywords

黑洞信息悖论；量子元胞自动机；全息原理；贝肯斯坦–霍金熵；纠缠熵；Page 曲线；环量子引力

---

## Introduction & Historical Context

黑洞热力学建立了几何面积与熵之间的精确联系。Bekenstein 首先提出，黑洞必须携带与视界面积成正比的熵，以保证广义第二定律在吞噬物质的过程中不被违反，并给出熵–面积关系的数量级估计。随后 Hawking 在曲率背景中的量子场论计算表明，静态黑洞应当以温度

$$
T_H = \frac{\hbar \kappa}{2 \pi k_B c}
$$

辐射，其中 $\kappa$ 为表面引力。这一结果与热力学第一、第二定律相结合，唯一确定了黑洞熵为

$$
S_{\mathrm{BH}} = \frac{k_B A}{4 \ell_P^2},
$$

其中 $\ell_P = \sqrt{G \hbar / c^3}$ 为普朗克长度。

半经典框架下，Hawking 辐射在无回波、无反射壁的情形中近似为黑体辐射，其密度矩阵对外部观察者而言为热混合态。如果黑洞源于初始纯态的坍缩，并最终完全蒸发，则半经典计算暗示纯态将不可逆地演化为混合态，违背量子理论的幺正性。这一张力被称为黑洞信息悖论。

围绕该悖论，已有多种候选解决方案：黑洞互补性强调不同观察者对事件的互补描述，防火墙方案提出在视界处存在剧烈高能壁以维护纠缠单调性，ER=EPR 设想视界两侧纠缠对由非平凡拓扑的 Einstein–Rosen 桥实现，而近年的"岛"公式与量子极值曲面方案则在半经典引力路径积分中恢复 Page 曲线。然而这些方案通常仍以内禀连续的时空流形为根基。

另一方面，量子元胞自动机与离散量子行走提供了描述量子场与相对论动力学的离散框架。在该框架中，宇宙被建模为在空间格点上作用的局域幺正更新规则，Dirac 与 Maxwell 等方程可以在长波极限下从 QCA 中涌现。这一思路自然引向一种离散本体论：在普朗克尺度，时空不再是光滑流形，而是由耦合的量子单元组成的网络。

在此类离散模型中，事件视界与奇点的几何概念需要被重新解释。若底层动力学为严格幺正的局域更新，则不存在数学意义上的"信息吸收端点"；任何表观不可逆性都应来自对系统部分自由度的忽略。另一方面，黑洞熵–面积律与全息原理提示，黑洞内部体积自由度在某种意义上被压缩到视界二维表面之上。

本文在此前提出的"信息速率守恒"与"光学度规"框架基础上，引入一个离散视界 QCA 模型，对黑洞熵与霍金辐射给出统一描述。核心步骤包括：

1. 在 QCA 中定义外部群速度 $v_{\mathrm{ext}}$ 与内部相位演化速度 $v_{\mathrm{int}}$，并采用母尺度恒等式 $v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2$ 作为信息速率守恒的公理化表达。

2. 通过局域信息处理密度 $\rho_{\mathrm{info}}$ 构造光学折射率场 $n(x)$，并将 $v_{\mathrm{ext}}$ 与 $n(x)$ 联系起来，从而定义离散视界为 $n(x)$ 超过某临界值时的等值面。

3. 证明跨越视界的离散连接数与面积成正比，并在最大纠缠假设下将黑洞熵识别为该连接集合的纠缠熵。

4. 将连接视为自旋网络穿刺，借助环量子引力的面积谱与 Immirzi 参数的既有结果恢复 $1/4$ 系数。

5. 在有限维 Hilbert 空间与快速置乱的假设下，利用 Page 定理分析辐射纠缠熵随时间的演化，得到符合幺正性要求的 Page 曲线，说明在该离散模型中信息悖论不再出现。

与现有连续框架最大的差异在于：本文从底层将黑洞视界建模为 QCA 网络中的"信息冻结层"，而非连续几何中的无厚度光滑曲面。黑洞熵不再是几何量的附属属性，而是离散网络中跨界纠缠通道数量的统计结果。

---

## Model & Assumptions

本节给出本文所用 QCA 宇宙模型、光学度规以及离散视界的严格定义，并列出关键假设。

### 2.1 QCA 宇宙与信息速率守恒

设空间由三维规则格点 $\Lambda \cong a \mathbb{Z}^3$ 组成，格距 $a$ 取为普朗克尺度数量级 $a \sim \ell_P$。每个格点 $x \in \Lambda$ 关联有限维 Hilbert 空间 $\mathcal{H}_x \cong \mathbb{C}^d$，全局 Hilbert 空间为张量积

$$
\mathcal{H} = \bigotimes_{x \in \Lambda} \mathcal{H}_x.
$$

离散时间步长为 $\Delta t$，QCA 的一次演化由幺正算符 $U: \mathcal{H} \to \mathcal{H}$ 实现，满足严格局域性：存在有限半径 $R$，使得任一本征局域算符 $O_x$ 的演化 $U^\dagger O_x U$ 仅支撑于以 $x$ 为中心、半径 $R$ 的有限邻域。该局域性定义了有限传播速度

$$
c = \frac{R a}{\Delta t},
$$

可与连续极限中的光速识别。

考虑在长波极限下描述为波包的局域激发，其在粗粒化坐标中的群速度记为 $v_{\mathrm{ext}}$，而内部自由度（"coin" 或内部自旋空间）中的相位旋进速率记为 $v_{\mathrm{int}}$。在此前工作中已证明，在 Dirac 型 QCA 中可构造一个信息速率向量 $(v_{\mathrm{ext}}, v_{\mathrm{int}})$ 满足

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2,
$$

并可通过 $\tau$ 作为内部相位演化参数恢复标准狭义相对论的固有时间与四速度规范化。本文将该关系作为信息速率守恒的公理化表述，并记作

**公理 2.1（信息速率守恒）** 对任一可辨别局域激发，外部传播速率 $v_{\mathrm{ext}}$ 与内部相位速率 $v_{\mathrm{int}}$ 满足

$$
v_{\mathrm{ext}}^2 + v_{\mathrm{int}}^2 = c^2.
$$

直观上，若 $v_{\mathrm{ext}}$ 接近 $c$，则激发近似无质量、在格点之间近光速传播；若 $v_{\mathrm{ext}}$ 接近 $0$，则激发几乎不在位置空间传播，而在内部 Hilbert 空间中以接近 $c$ 的速率作相位翻转与自指演化。

### 2.2 局域信息密度与光学折射率

定义每个格点的局域信息处理密度 $\rho_{\mathrm{info}}(x)$ 为单位时间内可在该元胞上实施的有效幺正自由度变化数目，归一化为无量纲量，并设存在上界 $\rho_{\max}$，对应元胞被局域最大纠缠填满的情形。

本文采用一类简单但足够表达引力红移的折射率模型，将有效折射率 $n(x)$ 定义为

$$
n(x) = \frac{1}{1 - \rho_{\mathrm{info}}(x) / \rho_{\max}},
$$

当 $\rho_{\mathrm{info}} \ll \rho_{\max}$ 时 $n(x) \approx 1$，当 $\rho_{\mathrm{info}} \to \rho_{\max}$ 时 $n(x) \to \infty$。光程守恒与标准光学度规理论表明，局域有效光速满足

$$
c_{\mathrm{eff}}(x) = \frac{c}{n(x)}.
$$

在 QCA 的长波连续极限下，可以构造一类光学度规

$$
\mathrm{d}s^2 = - \eta^2(x) c^2 \mathrm{d}t^2 + \eta^{-2}(x) \gamma_{ij}(x) \mathrm{d}x^i \mathrm{d}x^j,
$$

其中 $\eta(x)$ 与 $n(x)$ 等价，$\gamma_{ij}$ 为三维空间度规。此处我们只需保留 $c_{\mathrm{eff}}(x) = c/n(x)$ 这一关系，用以刻画外部群速度的抑制。

结合公理 2.1，可将局域外部群速度写为

$$
\lvert v_{\mathrm{ext}}(x) \rvert = \frac{c}{n(x)} = c \left(1 - \frac{\rho_{\mathrm{info}}(x)}{\rho_{\max}}\right).
$$

当 $\rho_{\mathrm{info}}(x) \to \rho_{\max}$ 时，$\lvert v_{\mathrm{ext}}(x) \rvert \to 0$，而 $v_{\mathrm{int}}(x) \to c$。

### 2.3 离散视界与信息冻结层

在上述设定下，给出本文的黑洞视界定义。

**定义 2.2（离散视界）** 设 $N_{\mathrm{crit}} > 1$ 为给定的临界折射率。离散视界 $\mathcal{H}$ 定义为连续极限中满足

$$
n(x) \geq N_{\mathrm{crit}}
$$

的等值闭合曲面族在格点上的近似离散化集合。

在 QCA 网络上，视界对应一层厚度约为一至数个格距的壳层区域

$$
\mathcal{H}_\Delta = \{ x \in \Lambda : N_{\mathrm{crit}} \leq n(x) < N_{\mathrm{crit}} + \delta \},
$$

其中 $\delta \ll N_{\mathrm{crit}}$。

**定义 2.3（信息冻结层）** 当 $n(x)$ 足够大，使得 $\lvert v_{\mathrm{ext}}(x) \rvert \ll c$ 而 $v_{\mathrm{int}}(x) \approx c$，称该壳层为信息冻结层。在此区域，激发的空间迁移几乎被阻塞，而内部 Hilbert 空间的相位与纠缠演化以接近 $c$ 的速率进行。

**假设 2.4（体积冻结与边界存储）** 对于满足

$$
n(x) \geq N_{\mathrm{crit}}
$$

的区域，QCA 的有效动力学满足：

1. 信息从外部区域沿径向传播至信息冻结层后，外向群速度趋近零，难以进一步向"内部体积"区传播。

2. 相反，冻结层内部的元胞可通过局域幺正耦合实现高频率的纠缠重排与能量–信息再分配。

因此，从外部观察者的角度看，黑洞内部体积自由度在动力学上"投影"为冻结层上的二维信息存储阵列。该假设与全息原理在定性上保持一致。

### 2.4 跨视界连接与 Hilbert 空间分解

将格点集合按照冻结层曲面 $\Sigma$ 分为外部区域 $\mathrm{Out}$、内部区域 $\mathrm{In}$ 与冻结层 $\mathcal{H}_\Delta$。外部与冻结层的 Hilbert 空间可写为

$$
\mathcal{H}_{\mathrm{out}} = \bigotimes_{x \in \mathrm{Out}} \mathcal{H}_x,\quad
\mathcal{H}_{\mathcal{H}} = \bigotimes_{x \in \mathcal{H}_\Delta} \mathcal{H}_x.
$$

考虑 QCA 的局域邻接图，将所有跨越冻结层的最近邻连接记为集合 $\mathcal{L}$，其中每条连接 $\ell \in \mathcal{L}$ 将一个外部格点与一个冻结层格点相连。

**定义 2.5（视界连接）** 视界连接集合 $\mathcal{L}$ 定义为所有满足：

1. 连接的一端属于 $\mathrm{Out}$，另一端属于 $\mathcal{H}_\Delta$。

2. 两端格点在邻接图中存在直接耦合项的边。

连接数目

$$
N_{\mathrm{link}} = \lvert \mathcal{L} \rvert
$$

将成为黑洞熵的关键计数对象。

在"冻结–边界存储"极限下，可将 Hilbert 空间的相关部分写作

$$
\mathcal{H}_{\mathcal{H}} \otimes \mathcal{H}_{\mathrm{out}} \cong \bigotimes_{\ell \in \mathcal{L}} \left( \mathcal{H}_{\ell}^{(\mathrm{in})} \otimes \mathcal{H}_{\ell}^{(\mathrm{out})} \right) \otimes \mathcal{H}_{\mathrm{rest}},
$$

其中 $\mathcal{H}_{\ell}^{(\mathrm{in})}$ 与 $\mathcal{H}_{\ell}^{(\mathrm{out})}$ 分别为连接两端的局域子空间，$\mathcal{H}_{\mathrm{rest}}$ 包含所有与跨界纠缠无关的自由度。

本文将主要关注 $\mathcal{L}$ 上的纠缠结构，并证明黑洞熵可由这些连接的纠缠冯·诺依曼熵给出。

---

## Main Results (Theorems and Alignments)

在上述模型与假设下，本文的核心结果可概括为以下四个定理。

**定理 3.1（离散视界上的全息存储）**

在局域度数有界、格距有限且满足信息速率守恒公理的 QCA 宇宙中，设存在一闭合冻结层 $\mathcal{H}_\Delta$ 定义黑洞视界，且内部区域的传播模式在动力学上被强烈抑制，则对于外部观察者可访问的算子代数，黑洞内部所有信息均可等价地编码到冻结层上的连接集合 $\mathcal{L}$ 所支撑的自由度中。

换言之，存在一同构

$$
\mathcal{H}_{\mathrm{BH}} \cong \bigotimes_{\ell \in \mathcal{L}} \mathcal{H}_{\ell}^{(\mathrm{in})} \otimes \mathcal{H}_{\mathrm{aux}},
$$

其中 $\mathcal{H}_{\mathrm{BH}}$ 为对外部可见的黑洞有效 Hilbert 空间，$\mathcal{H}_{\mathrm{aux}}$ 不与外部区域直接纠缠。

**定理 3.2（连接计数与面积律）**

设 QCA 网络在冻结层附近的连接图在大尺度上近似各向同性，并具有有限平均度数，则对足够大的视界曲面 $\Sigma$，跨越冻结层的连接数目满足

$$
N_{\mathrm{link}} = \eta \frac{A}{a^2} + o\left(\frac{A}{a^2}\right),
$$

其中 $A$ 为 $\Sigma$ 的连续极限表面积，$\eta$ 为只依赖于局域晶格结构的无量纲几何因子。

**定理 3.3（黑洞熵的纠缠起源）**

在定理 3.1 与 3.2 的条件下，若冻结层在平衡态时每条连接近似处于最大纠缠态，且连接之间的相关性在大尺度上可视为无序，则外部观察者所见黑洞的冯·诺依曼熵为

$$
S_{\mathrm{BH}} = k_B \ln 2 \cdot N_{\mathrm{link}} \approx k_B \eta \ln 2 \frac{A}{a^2}.
$$

将格距识别为普朗克长度 $a = \ell_P$ 并选取几何因子 $\eta$ 与环量子引力中 Immirzi 参数的标准值匹配，可恢复

$$
S_{\mathrm{BH}} = \frac{k_B A}{4 \ell_P^2}.
$$

**定理 3.4（幺正蒸发与 Page 曲线）**

设黑洞–辐射联合系统在任意时刻 $t$ 可由有限维 Hilbert 空间

$$
\mathcal{H}_{\mathrm{tot}} = \mathcal{H}_{\mathrm{BH}}(t) \otimes \mathcal{H}_{\mathrm{rad}}(t)
$$

上的纯态 $\lvert \Psi(t) \rangle$ 描述，并由 QCA 全局演化算符的幺正迭代给出。若内部动力学在冻结层上为快速置乱，并假设在每一阶段 $\lvert \Psi(t) \rangle$ 对于给定维数对 $(d_{\mathrm{BH}}(t), d_{\mathrm{rad}}(t))$ 接近 Haar 随机纯态，则辐射的冯·诺依曼熵近似满足

$$
S_{\mathrm{rad}}(t) \approx k_B \min\left( \ln d_{\mathrm{BH}}(t), \ln d_{\mathrm{rad}}(t) \right),
$$

从而随时间给出一条先升后降、最终回到零的 Page 曲线。黑洞完全蒸发时 $d_{\mathrm{BH}} \to 1$，辐射熵 $S_{\mathrm{rad}} \to 0$，联合系统始终处于纯态，从而信息悖论在该框架下不再出现。

上述定理的证明将在后续"Proofs"与附录中给出。

---

## Proofs

本节给出各定理的证明大纲，将技术细节与相关数学工具的完整推导放入附录。

### 4.1 定理 3.1 的证明：冻结层上的全息存储

证明思路基于 QCA 的局域性与因果结构。

1. **因果锥与可达性**

   对于外部区域的任一局域算符 $O_{\mathrm{out}}$，其在 QCA 演化下的 Heisenberg 像 $O_{\mathrm{out}}(t) = U^{-t} O_{\mathrm{out}} U^t$ 的支撑被限制在以该算符初始支撑为底的因果锥内。信息冻结层内的传播速度近乎零，意味着在有限时间尺度内，内部体积区域对外部观测算子的微扰贡献可以忽略，而冻结层上的自由度贡献主导。

2. **有效算子代数压缩**

   更精确地，考虑外部观察者可访问的算子代数 $\mathcal{A}_{\mathrm{out}}$。任何 $A \in \mathcal{A}_{\mathrm{out}}$ 的时间演化在 Heisenberg 图像中可写为

   $$
   A(t) = U^{-t} A U^t = A_{\mathcal{H}}(t) \otimes \mathbb{I}_{\mathrm{bulk}} + \text{小量},
   $$

   其中 $A_{\mathcal{H}}(t)$ 支撑在冻结层与外部区域，内部体积自由度的影响以小参数（由 $v_{\mathrm{ext}}/c$ 与演化时间共同控制）被抑制。

3. **Stinespring 结构与编码映射**

   在上述极限中，可以构造一 CPTP 映射，将内部体积 Hilbert 空间 $\mathcal{H}_{\mathrm{bulk}}$ 的自由度编码到冻结层上的辅助自由度 $\mathcal{H}_{\mathrm{aux}} \subset \mathcal{H}_{\mathcal{H}}$，使得对外部算子代数的期望值不变：

   $$
   \operatorname{tr}_{\mathrm{bulk}}\left( \rho_{\mathrm{BH}} A_{\mathrm{out}} \right)
   = \operatorname{tr}_{\mathrm{aux}}\left( \tilde{\rho}_{\mathcal{H}} A_{\mathrm{out}} \right).
   $$

   由 Stinespring 定理与算子代数同构，可证明存在 Hilbert 空间等价

   $$
   \mathcal{H}_{\mathrm{BH}} \cong \bigotimes_{\ell \in \mathcal{L}} \mathcal{H}_{\ell}^{(\mathrm{in})} \otimes \mathcal{H}_{\mathrm{aux}},
   $$

   从而得到定理 3.1 的结论。

详细构造见附录 A.1。

### 4.2 定理 3.2 的证明：连接数与面积的比例关系

该定理本质上是一个几何–组合论陈述，在具有有限度数与均匀性的格点网络上成立。

1. **局域各向同性假设**

   假设冻结层附近的连接图在足够大尺度上近似均匀各向同性，即每个格点的平均度数 $\deg(x)$ 在统计上为常数 $d_0$，且连接方向在球面上分布均匀。

2. **表面积离散化**

   将连续曲面 $\Sigma$ 在格点上的近似离散化视为所有距离曲面小于 $a/2$ 的格点集合。该集合的基数 $N_{\Sigma}$ 满足

   $$
   N_{\Sigma} = \zeta \frac{A}{a^2} + o\left(\frac{A}{a^2}\right),
   $$

   其中 $\zeta$ 为与晶格类型（立方、体心立方等）有关的常数。

3. **跨界连接计数**

   对每个在 $\Sigma$ 上的格点，统计指向内外两边的连接数。由于平均度数有限且无长程连接，跨界连接的总数与 $N_{\Sigma}$ 成正比，即

   $$
   N_{\mathrm{link}} = \eta N_{\Sigma} = \eta \zeta \frac{A}{a^2} + o\left(\frac{A}{a^2}\right).
   $$

   将 $\eta \zeta$ 归并为 $\eta$，得到定理 3.2 的表达式。

该论证与固体物理中的"表面原子数 $\propto$ 表面积"计算同源，详细推导见附录 A.2。

### 4.3 定理 3.3 的证明：纠缠熵与面积律

在定理 3.1 与 3.2 的基础上，将跨界连接视为携带纠缠的双系统子空间。

1. **单连接的熵贡献**

   假设每条连接 $\ell$ 上的 Hilbert 空间为 $\mathbb{C}^2 \otimes \mathbb{C}^2$，对应一对 qubit，自然纯态为 Bell 类最大纠缠态。对外部区域取偏迹，得到单个外部 qubit 的约化密度矩阵为

   $$
   \rho_{\ell}^{(\mathrm{out})} = \frac{1}{2} \mathbb{I}_2,
   $$

   其冯·诺依曼熵为

   $$
   S_{\ell} = - k_B \operatorname{tr}\left( \rho_{\ell}^{(\mathrm{out})} \ln \rho_{\ell}^{(\mathrm{out})} \right) = k_B \ln 2.
   $$

2. **多连接张量积与独立性**

   在冻结层处快速置乱的极限下，可以将不同连接上的纠缠近似视为统计独立，其联合态在外部观测下为张量积密度矩阵

   $$
   \rho_{\mathrm{out}} = \bigotimes_{\ell \in \mathcal{L}} \rho_{\ell}^{(\mathrm{out})},
   $$

   因此总熵为

   $$
   S_{\mathrm{BH}} = \sum_{\ell \in \mathcal{L}} S_{\ell} = k_B \ln 2 \cdot N_{\mathrm{link}}.
   $$

3. **与面积律的匹配**

   代入定理 3.2 的结果

   $$
   N_{\mathrm{link}} \approx \eta \frac{A}{a^2},
   $$

   得

   $$
   S_{\mathrm{BH}} \approx k_B \eta \ln 2 \frac{A}{a^2}.
   $$

   选择自然的格距 $a = \ell_P$，可将 $\eta$ 的具体数值通过更微观的自旋网络模型固定。

4. **与环量子引力面积谱的一致性**

   在环量子引力框架中，视界被自旋网络穿刺，面积本征值为

   $$
   A_j = 8 \pi \gamma \ell_P^2 \sqrt{j(j+1)},
   $$

   其中 $\gamma$ 为 Immirzi 参数。若将 QCA 的每条 qubit 连接识别为一个 $j = 1/2$ 的穿刺，则单穿刺面积

   $$
   A_{1/2} = 4 \pi \gamma \sqrt{3} \ell_P^2,
   $$

   自旋态空间维数为 $2j+1 = 2$，对应熵 $\ln 2$。通过计数穿刺数 $N = A / A_{1/2}$，总熵为

   $$
   S = N k_B \ln 2 = \frac{A}{4 \ell_P^2} k_B
   $$

   当且仅当

   $$
   \gamma = \frac{\ln 2}{\pi \sqrt{3}}.
   $$

   这一值与近年来基于环量子引力与 Landauer 原理的推导一致，表明本文 QCA 模型在熵–面积关系上与该类工作兼容。

以上完成定理 3.3 的证明。详细的自旋网络计数与 Immirzi 参数讨论见附录 B。

### 4.4 定理 3.4 的证明：幺正蒸发与 Page 曲线

该定理基于两个要素：QCA 的全局幺正性与关于 Haar 随机纯态的平均熵结果。

1. **有限维纯态与冯·诺依曼熵对称性**

   对任意纯态 $\lvert \Psi \rangle \in \mathcal{H}_{\mathrm{BH}} \otimes \mathcal{H}_{\mathrm{rad}}$，有

   $$
   S\left( \rho_{\mathrm{BH}} \right) = S\left( \rho_{\mathrm{rad}} \right),
   $$

   其中 $\rho_{\mathrm{BH}}$ 与 $\rho_{\mathrm{rad}}$ 为对另一子系统取偏迹后的约化态。QCA 的全局演化

   $$
   \lvert \Psi(t+1) \rangle = U \lvert \Psi(t) \rangle
   $$

   保证联合系统的纯态性质始终保持。

2. **Page 定理与平均熵**

   Page 计算表明，对 Hilbert 空间维数为 $d_{\mathrm{BH}} \leq d_{\mathrm{rad}}$ 的双系统，若从 Haar 测度选取随机纯态，则较小子系统的平均熵近似为

   $$
   \overline{S} \approx k_B \left( \ln d_{\mathrm{BH}} - \frac{d_{\mathrm{BH}}}{2 d_{\mathrm{rad}}} \right),
   $$

   当 $d_{\mathrm{rad}} \gg d_{\mathrm{BH}}$ 时接近最大值 $k_B \ln d_{\mathrm{BH}}$。

3. **快速置乱假设与典型态近似**

   由于冻结层上的局域幺正耦合高度非可积，可假设黑洞内部与视界之间的动力学为快速置乱，其特征时间 $t_*$ 满足

   $$
   t_* \sim \beta \ln S_{\mathrm{BH}},
   $$

   其中 $\beta$ 为与 Hawking 温度与 QCA 微观时间步长相关的常数。快速置乱系统的长时间演化典型态可被 Haar 随机纯态良好近似，Hayden–Preskill 协议与后续工作支持这一观点。

4. **维数演化与 Page 曲线**

   随蒸发进行，黑洞 Hilbert 空间的有效维数 $d_{\mathrm{BH}}(t)$ 随视界面积缩小而单调减小，而外部辐射子空间 $d_{\mathrm{rad}}(t)$ 单调增大。利用

   $$
   S_{\mathrm{rad}}(t) \approx k_B \min\left( \ln d_{\mathrm{BH}}(t), \ln d_{\mathrm{rad}}(t) \right),
   $$

   可见当 $d_{\mathrm{rad}} < d_{\mathrm{BH}}$ 时，辐射熵随时间增长；当 $d_{\mathrm{rad}} > d_{\mathrm{BH}}$ 时，辐射熵受限于较小子系统的维数，必须随 $d_{\mathrm{BH}}$ 的减小而下降，从而自动给出具有峰值的 Page 曲线。

5. **终态纯度与信息守恒**

   当黑洞完全蒸发时，$\dim \mathcal{H}_{\mathrm{BH}} = 1$，因此 $\rho_{\mathrm{BH}}$ 必为纯态，$S_{\mathrm{BH}} = 0$。由熵对称性必有 $S_{\mathrm{rad}} = 0$，说明所有信息最终以纯态形式编码于辐射之中。信息从未在 QCA 的幺正演化中丢失，只是在中间阶段以高度置乱的方式分布在大维数辐射 Hilbert 空间中。

上述逻辑完成定理 3.4 的证明。更精细的熵随时间函数形式可参照 Page 的数值计算与后续改进，附录 C 给出一类简单的参数化模型，并讨论 QCA 语境下的适用性。

---

## Model Apply

本节将上述普适性结果应用于简化的静态球对称黑洞模型，说明如何在 QCA 框架中构造离散视界、估计连接数，并对应到连续极限中的 Schwarzschild 几何。

### 5.1 静态球对称离散视界

考虑在 QCA 中嵌入一类近似球对称的高信息密度区域，其连续极限几何可被描述为 Schwarzschild 度规

$$
\mathrm{d}s^2 = -\left(1 - \frac{2GM}{r c^2}\right) c^2 \mathrm{d}t^2
+ \left(1 - \frac{2GM}{r c^2}\right)^{-1} \mathrm{d}r^2 + r^2 \mathrm{d}\Omega^2.
$$

在光学度规近似下，将折射率写为

$$
n(r) = \left(1 - \frac{2GM}{r c^2}\right)^{-1/2},
$$

其在 Schwarzschild 半径 $r_s = 2GM / c^2$ 处发散。在 QCA 模型中，$\rho_{\mathrm{info}}(r)$ 随 $r$ 减小时单调增加，并在某一半径 $r_h$ 附近逼近 $\rho_{\max}$。

以 $r = r_h$ 定义离散视界，对应的面积为

$$
A = 4 \pi r_h^2.
$$

在离散格上，视界附近的格点集合由所有满足 $\lvert \lVert x \rVert - r_h \rvert < a/2$ 的格点组成，其基数 $N_{\Sigma}$ 近似为

$$
N_{\Sigma} \approx \frac{A}{a^2}.
$$

### 5.2 连接计数与熵估计

采用定理 3.2 的结果，跨界连接数为

$$
N_{\mathrm{link}} \approx \eta \frac{A}{a^2} = \eta \frac{4 \pi r_h^2}{a^2}.
$$

对每个连接赋予 $k_B \ln 2$ 的纠缠熵，得到

$$
S_{\mathrm{BH}} \approx 4 \pi \eta k_B \ln 2 \frac{r_h^2}{a^2}.
$$

将 $a$ 识别为 $\ell_P$，调整 $\eta$ 使

$$
4 \pi \eta \ln 2 = \frac{1}{4},
$$

即可恢复

$$
S_{\mathrm{BH}} = \frac{k_B A}{4 \ell_P^2}.
$$

更精细地，将连接与 $\mathrm{SU}(2)$ 自旋网络穿刺对应，通过环量子引力的微观计数固定 Immirzi 参数，则无需将 $\eta$ 视为任意拟合参数，而是由自旋网络拓扑与统计权重决定。这一对应关系在附录 B 中展开。

### 5.3 QCA 中的温度与表面重力

在 QCA 模型中，冻结层上的内部相位频率 $\omega_{\mathrm{int}}$ 与外部观测到的有效温度相关。利用统一时间恒等式与局域态密度–散射相位导数的关系，可以将 Hawking 温度解释为冻结层模式的群延迟谱的特征尺度。该部分涉及统一时间刻度与散射时间延迟的工作，在此不展开，仅指出：

1. 冻结层上模式的群延迟矩阵 $\mathsf{Q}(\omega)$ 的迹决定局域时间刻度密度 $\kappa(\omega)$。

2. 对于近似热平衡的冻结层，Hawking 温度可由相应模态的谱布居与 $\kappa(\omega)$ 的关系确定，从而与表面重力 $\kappa$ 匹配。

这表明，黑洞温度也可以在 QCA 的频域散射描述中得到解释，并与几何表面重力保持一致。

---

## Engineering Proposals

尽管天体物理黑洞的 Hawking 辐射极其微弱，难以直接观测，但 QCA 黑洞模型仍然给出若干可在类比系统与数值模拟中检验的工程性预言。

### 6.1 类比黑洞平台上的非热相关性

类比黑洞实验（如 Bose–Einstein 凝聚体中的声学视界）已在实验上观测到近似热的 Hawking 辐射谱与视界两侧声子对的纠缠关联。在 QCA 模型中，冻结层上存在高度纠缠的离散连接，其向外泄漏的辐射应当携带可检测的非高斯相关与多体纠缠结构。

建议：

1. 在类比黑洞实验中，通过测量辐射模态的高阶相关函数与量子 Fisher 信息，检测偏离纯热分布的隐藏相关。

2. 利用量子断层成像与机器学习方法重建有效密度矩阵，检验是否存在与 QCA 模型预测一致的多体纠缠模式。

### 6.2 量子模拟与离散视界的实现

在离散时间量子行走与量子电路平台上，已经实现了 Dirac 型 QCA 的模拟，并观察到诸如 Zitterbewegung 等相对论效应。在可编程量子计算平台上，可以构造如下实验：

1. 设计一个二维或三维 QCA，中心区域布置高密度局域幺正门以模拟信息冻结层，外围为低密度区域。

2. 准备初始纯态波包坍缩到中心区域，记录外部"辐射"的量子态随离散时间的演化。

3. 在足够时间步后，对外部子系统做完全断层或影像测量，验证外部辐射是否从初期近似热态逐渐演化为纯态，并重构 Page 曲线。

这种方案为在有限比特数、可控噪声的条件下"模拟"黑洞 Page 曲线提供了具体路径，与近期关于可溯源 Page 曲线的模型研究形成呼应。

### 6.3 信息冻结层的光学模拟

在光学平台上，可通过空间折射率调制构造有效的"光学黑洞"，其折射率随半径变化导致光线偏折与捕获。为检验 QCA 光学度规的部分预言，可以：

1. 利用超材料构造具有强折射率梯度的介质，将折射率近似设计为 $n(r) = 1 / (1 - \rho_{\mathrm{eff}}(r)/\rho_{\max})$ 的形式。

2. 研究靠近"冻结层"区域波束的群速度减慢与反射–透射特性，验证信息速率守恒在类比系统中的体现。

虽然此类实验无法直接模拟量子纠缠结构，但可验证折射率–信息密度关系的部分宏观效应。

---

## Discussion (Risks, Boundaries, Past Work)

### 7.1 与既有黑洞熵理论的比较

本文给出的熵–面积推导与多类已有理论存在对应关系：

1. 与环量子引力：二者均将视界描述为由自旋网络穿刺构成的离散几何，并通过微观态计数恢复 $S_{\mathrm{BH}} = A/(4\ell_P^2)$。本文的 QCA 模型可视为在时间离散与因果局域性上为该图像提供动力学实现。

2. 与 AdS/CFT 与 Cardy 公式：在 AdS/CFT 框架中，黑洞熵由边界共形场论的态密度给出，Cardy 公式为二维情形提供了强有力工具。本文的"冻结层"可被视为某种离散化的边界理论，其连接自由度对应边界场论中的高能模式。

3. 与"脏黑洞"与 Wald 熵：对于广义引力理论，Wald 熵与 Noether 电荷为熵–面积关系的推广提供了系统性框架。在 QCA 模型中，若底层更新规则在有效连续极限中对应非 Einstein–Hilbert 拉格朗日量，则连接计数系数与 $\ell_P$ 的关系可能得到修正，对应 Wald 熵中附加项的离散图像。

### 7.2 信息悖论方案的相容性与差异

与其它信息悖论方案相比，本工作的特点在于：

1. 该模型从一开始就假定全局演化严格幺正，不允许任何非幺正"坍缩"或信息吸收。

2. 视界的"不可逾越性"只针对低能长波观察者，对于掌握完整 Hilbert 空间与 QCA 更新规则的"全知观察者"，不存在真正意义上的信息隔离。

3. 防火墙争论源于对视界外–内与外–辐射纠缠的张力。在 QCA 模型中，所有对外界可见的纠缠通道集中在有限厚度的冻结层上，其局域结构可能为同时满足平滑视界与幺正性的"中介层"。

这一图景与黑洞互补性、ER=EPR 与岛公式并不必然矛盾，而更像是它们在离散本体论上的一种提升：ER=EPR 所描述的非平凡拓扑与纠缠关系，可以在 QCA 网络拓扑与连接数的层面实现；岛公式中的"量子极值曲面"可以视为使某类信息测度极值化的最优冻结层。

### 7.3 模型边界与潜在风险

该框架依赖若干非平凡假设：

1. 底层宇宙的确可以在普朗克尺度被 QCA 宇宙模型良好描述，而非连续场论或其它离散结构。

2. 光学折射率与信息密度之间的函数关系在强引力场下仍然有效，其形式可能需要在更精细的 QCA–GR 对应中加以修正。

3. 快速置乱与 Haar 随机态近似在真实黑洞背景中是否成立仍是开放问题，尽管已有大量证据支持大型黑洞表现为高效信息扰动器。

此外，将连接视为独立的最大纠缠通道忽略了多体约束与长程相关的可能性；更精细的分析可能需要借助随机张量网络与纠缠网格（tensor network）的工具。

---

## Conclusion

本文在量子元胞自动机与光程守恒框架下，提出了一种离散视界模型，并对黑洞熵–面积律与信息悖论给出了统一描述。主要结论可概括如下：

1. 在满足信息速率守恒与局域度数有界的 QCA 宇宙中，黑洞视界可被定义为信息冻结层，即外部群速度 $v_{\mathrm{ext}}$ 接近零而内部相位速率 $v_{\mathrm{int}}$ 接近 $c$ 的临界壳层。

2. 跨越冻结层的连接集合 $\mathcal{L}$ 承担了内外区域之间的全部纠缠与信息通道，在外部可见算子代数上，黑洞内部信息可等价编码到这些连接自由度中，形成离散全息存储结构。

3. 在局域各向同性与最大纠缠假设下，跨界连接数 $N_{\mathrm{link}}$ 与面积满足 $N_{\mathrm{link}} \propto A / \ell_P^2$，每条连接贡献 $k_B \ln 2$ 的纠缠熵，从而得到 $S_{\mathrm{BH}} \propto A$。将连接与 $\mathrm{SU}(2)$ 自旋网络穿刺对应并采用环量子引力的面积谱与 Immirzi 参数的标准结果，可精确恢复贝肯斯坦–霍金熵公式。

4. 在有限维 Hilbert 空间与快速置乱假设下，QCA 的幺正演化确保黑洞–辐射联合系统始终处于纯态。利用 Page 的平均熵结果，可证明辐射熵随时间演化呈现先升后降的 Page 曲线，最终回到零，从而在该模型中信息悖论自然消失。

这一离散视界–QCA 图景表明：黑洞熵可以被严格理解为离散因果视界上的纠缠连接计数，而非连续几何的附带属性；霍金辐射则是冻结层上的高维纠缠态经由 QCA 散射机制向外泄漏的加密信息流。该框架为"时空源于量子信息"的观点提供了新的定量支撑，并为在可控量子系统中模拟与检验黑洞信息动力学提供了具体路径。

---

## Acknowledgements, Code Availability

作者感谢相关量子信息、量子引力与类比重力领域的研究共同体，为黑洞熵、Page 曲线与量子元胞自动机等课题提供的系统性成果。

本文主要为理论分析，所有推导在解析层面完成，未使用数值模拟代码。用于演示 QCA–黑洞玩具模型的量子电路与伪代码可在后续工作中给出。

---

## References

[1] J. D. Bekenstein, "Black holes and entropy," *Phys. Rev. D* **7**, 2333 (1973).

[2] S. W. Hawking, "Particle creation by black holes," *Commun. Math. Phys.* **43**, 199 (1975).

[3] J. M. Bardeen, B. Carter, S. W. Hawking, "The four laws of black hole mechanics," *Commun. Math. Phys.* **31**, 161 (1973).

[4] R. Bousso, "The holographic principle," *Rev. Mod. Phys.* **74**, 825 (2002).

[5] D. N. Page, "Average entropy of a subsystem," *Phys. Rev. Lett.* **71**, 1291 (1993).

[6] D. N. Page, "Time dependence of Hawking radiation entropy," *J. Cosmol. Astropart. Phys.* **09**, 028 (2013).

[7] P. Hayden, J. Preskill, "Black holes as mirrors: quantum information in random subsystems," *J. High Energy Phys.* **09**, 120 (2007).

[8] G. 't Hooft, "Dimensional reduction in quantum gravity," *Conf. Proc. C* **930308**, 284 (1993).

[9] L. Susskind, "The world as a hologram," *J. Math. Phys.* **36**, 6377 (1995).

[10] A. Ashtekar, J. Baez, A. Corichi, K. Krasnov, "Quantum geometry and black hole entropy," *Phys. Rev. Lett.* **80**, 904 (1998).

[11] K. Krasnov, "On the constant that fixes the area spectrum in canonical quantum gravity," *Class. Quantum Grav.* **15**, L47 (1998).

[12] A. Ghosh, A. Perez, "Black hole entropy and isolated horizons thermodynamics," *Phys. Rev. Lett.* **107**, 241301 (2011); and related works on LQG black hole entropy.

[13] E. M. C. Abreu et al., "On the role of Barrow's fractal entropy in loop quantum gravity," *Europhys. Lett.* **137**, 10003 (2022).

[14] J. Ananias Neto, R. Thibes, "Revisiting the Immirzi parameter: Landauer's principle and alternative entropy frameworks in loop quantum gravity," *Eur. Phys. J. C* **85**, 918 (2025).

[15] G. M. D'Ariano, "Quantum field as a quantum cellular automaton I: the Dirac free evolution in one dimension," *Phys. Lett. A* **376**, 697 (2012).

[16] A. Mallick, C. M. Chandrashekar, "Dirac cellular automaton from split-step quantum walk," *Sci. Rep.* **6**, 25779 (2016).

[17] T. A. Brun, M. C. Kimberley, "Quantum cellular automata and quantum field theory in two spatial dimensions," *Phys. Rev. A* **102**, 062222 (2020).

[18] C. Huerta Alderete et al., "Quantum walks and Dirac cellular automata on a programmable trapped-ion quantum computer," *Commun. Phys.* **3**, 89 (2020).

[19] P. Arrighi, S. Facchini, M. Forets, "Discrete Lorentz covariance for quantum walks and quantum cellular automata," *New J. Phys.* **16**, 093007 (2014).

[20] J. Steinhauer, "Observation of quantum Hawking radiation and its entanglement in an analogue black hole," *Nat. Phys.* **12**, 959 (2016); J. R. Muñoz de Nova et al., "Observation of thermal Hawking radiation and its temperature in an analogue black hole," *Nature* **569**, 688 (2019).

[21] W. G. Unruh, "Experimental black-hole evaporation?," *Phys. Rev. Lett.* **46**, 1351 (1981).

[22] M. Visser, "Dirty black holes: entropy versus area," *Phys. Rev. D* **48**, 583 (1993).

[23] I. Aref'eva et al., "Complete evaporation of black holes and Page curves," *Symmetry* **15**, 170 (2023).

[24] X. Wang, R. Li, J. Wang, "Page curves for a family of exactly solvable evaporating black holes," *Phys. Rev. D* **103**, 126026 (2021).

[25] M. Cadoni, E. Franzin, S. Mignemi, "Unitarity and Page curve for evaporation of 2D AdS black hole," *Phys. Rev. D* **105**, 024027 (2022).

（其他关于统一时间刻度、信息速率守恒、光学度规与 QCA 宇宙的相关工作（包括 Ma 等人的系列论文），作为本文 QCA 黑洞模型的直接理论背景。）

---

## Appendix A. QCA Formalism and Causal Compression

### A.1 外部算子代数与冻结层的等效编码

本附录给出定理 3.1 中 Hilbert 空间等价的更为详细的构造。

设 $\mathcal{A}_{\mathrm{out}}$ 为外部区域上有界算子代数，由支撑在 $\mathrm{Out}$ 区域的局域算子与其极限生成。考虑 QCA 的 Heisenberg 演化

$$
\Phi_t: \mathcal{A}_{\mathrm{out}} \to \mathcal{B}(\mathcal{H}),\quad \Phi_t(A) = U^{-t} A U^t.
$$

由于局域性，存在常数 $C$ 与速度 $v_c$（与 $c$ 同阶），使得 Lieb–Robinson 型不等式成立：对任意空间上距离 $\mathrm{dist}(\mathrm{supp} A, \mathrm{supp} B) > 0$ 的算子 $A,B$，有

$$
\lVert [\Phi_t(A), B] \rVert \leq C \lVert A \rVert \lVert B \rVert \exp\left( -\mu [\mathrm{dist}(\mathrm{supp} A, \mathrm{supp} B) - v_c t]_+ \right)
$$

其中 $[\cdot,\cdot]$ 为交换子，$[\cdot]_+$ 为正部分，$\mu>0$。

在冻结层内，外部群速度 $\lvert v_{\mathrm{ext}} \rvert$ 被抑制，使得从内部体积区域向外部传播的信号需要时间尺度远长于考虑的观测时间 $T$。因此在 $t \leq T$ 的时间窗中，可以将内部体积区域视为"因果静默"，对外部算子代数的影响可以通过一 CPTP 映射压缩到冻结层上的辅助自由度。

更具体地，固定时间窗 $[0,T]$，考虑演化后的算子族 $\Phi_t(\mathcal{A}_{\mathrm{out}})$。定义

$$
\mathcal{H}_{\mathrm{eff}} = \mathcal{H}_{\mathrm{out}} \otimes \mathcal{H}_{\mathcal{H}},
$$

以及投影

$$
P: \mathcal{H} \to \mathcal{H}_{\mathrm{eff}},
$$

将内部体积自由度迹掉。由于内部区域在时间 $T$ 内对外部的反馈被指数抑制，可证明存在一 CPTP 映射

$$
\mathcal{E}: \mathcal{B}(\mathcal{H}_{\mathrm{eff}}) \to \mathcal{B}(\mathcal{H}_{\mathrm{eff}})
$$

使得对任意 $A \in \mathcal{A}_{\mathrm{out}}$，有

$$
\left\lVert P \Phi_t(A) P - \mathcal{E}^t(P A P) \right\rVert \leq \epsilon(T),
$$

其中 $\epsilon(T)$ 随 $T$ 可控。

对外部观察者而言，在精度 $\epsilon(T)$ 内，内部体积可以等效为冻结层上的环境系统 $\mathcal{H}_{\mathrm{aux}}$，Stinespring 表示定理保证存在

$$
\mathcal{H}_{\mathrm{BH}} \cong \bigotimes_{\ell \in \mathcal{L}} \mathcal{H}_{\ell}^{(\mathrm{in})} \otimes \mathcal{H}_{\mathrm{aux}},
$$

对应定理 3.1 的陈述。

### A.2 连接计数的几何估计

在具有立方晶格结构的情形，冻结层邻近的格点可近似视为附着在连续曲面 $\Sigma$ 上的二维离散网格，格距为 $a$。

1. 将 $\Sigma$ 划分为面积元 $\Delta A = a^2$，每个面积元对应一个或若干格点。

2. 若晶格为简单立方，则每个格点平均有一条法向连接跨越曲面（指向内部或外部），以及若干切向连接。跨界连接主要来自于法向边。

3. 对于足够大的 $A$，边缘效应可忽略，跨界连接数近似为

   $$
   N_{\mathrm{link}} \approx \frac{A}{a^2}.
   $$

   更一般的晶格类型只改变前因子的几何常数。

该估计与固体物理中"表面原子数 $\sim A / a^2$" 的标准结果一致。

---

## Appendix B. Spin Network Picture and the 1/4 Coefficient

本附录将 QCA 连接模型与环量子引力自旋网络视界模型对接，说明为何在自然假设下可以恢复 $1/4$ 系数。

### B.1 面积谱与 Immirzi 参数

在环量子引力中，面积算符的本征值谱为

$$
A = 8 \pi \gamma \ell_P^2 \sum_i \sqrt{j_i (j_i + 1)},
$$

其中求和遍及所有穿刺视界的自旋网络边缘，$j_i$ 为对应的自旋量子数。

若假设在大面积极限下，主要贡献来自 $j = 1/2$ 的穿刺，则单穿刺贡献面积

$$
A_{1/2} = 4 \pi \gamma \sqrt{3} \ell_P^2.
$$

穿刺对应的内部边缘状态空间维数为

$$
\dim \mathcal{H}_{1/2} = 2j+1 = 2,
$$

因此每个穿刺可贡献熵 $k_B \ln 2$。

将总穿刺数记为

$$
N = \frac{A}{A_{1/2}} = \frac{A}{4 \pi \gamma \sqrt{3} \ell_P^2},
$$

总熵为

$$
S = N k_B \ln 2 = \frac{k_B \ln 2}{4 \pi \gamma \sqrt{3}} \frac{A}{\ell_P^2}.
$$

要求 $S = k_B A / (4 \ell_P^2)$ 给出

$$
\gamma = \frac{\ln 2}{\pi \sqrt{3}}.
$$

近期工作表明，这一数值可以通过 Landauer 原理与信息擦除成本独立得到，加强了其物理解释。

### B.2 QCA 连接与自旋穿刺的同一化

在本文的 QCA 模型中，每条连接 $\ell$ 上的 Hilbert 空间被取为 $\mathcal{H}_{\ell}^{(\mathrm{in})} \otimes \mathcal{H}_{\ell}^{(\mathrm{out})}$，其中每个因子为二能级系统。将

$$
\mathcal{H}_{\ell}^{(\mathrm{in})} \cong \mathcal{H}^{(j=1/2)}
$$

识别为自旋 $1/2$ 表象，则：

1. 每条连接对应视界上的一条自旋网络边缘穿刺，贡献面积 $A_{1/2}$。

2. 每条连接贡献一个比特的最大纠缠熵 $k_B \ln 2$。

因此视界上的 QCA 连接网络与环量子引力自旋网络模型在态计数上同构。黑洞熵–面积关系可视为同一计数问题在不同语言下的两种表述。

### B.3 非 $j=1/2$ 模式与修正项

在更一般的情形中，高自旋 $j>1/2$ 的穿刺与多体约束会带来对主导项的对数修正。已有研究表明，在环量子引力黑洞熵中出现 $-\alpha \ln A$ 型修正，其系数依微观模型而定。

在 QCA 连接模型中，这些修正可理解为：

1. 部分连接对应更高维局域 Hilbert 空间（多能级系统或多线重合）。

2. 冻结层内部存在全局约束（如总自旋、拓扑数守恒），导致可允许的纠缠配置数减少。

这些效应不会改变主导面积项 $A / (4 \ell_P^2)$，但会在亚主导阶给出对数或幂次修正，对应于不同量子引力方案的特征。

---

## Appendix C. Page Curve in a Finite-Dimensional QCA Toy Model

为具体展示 Page 曲线在 QCA 语境中的实现，考虑如下简单模型：

1. 取黑洞初始 Hilbert 空间维数为 $d_{\mathrm{BH}}(0) = 2^N$，对应 $N$ 条连接或 $N$ 个冻结层比特。

2. 每个离散时间步，从黑洞向辐射释放一个 qubit，通过某一随机幺正门与已辐射的 qubit 及剩余黑洞自由度充分纠缠。

### C.1 迭代过程

设第 $k$ 步后，黑洞剩余 qubit 数为 $N-k$，辐射 qubit 数为 $k$。在快速置乱假设下，联合态

$$
\lvert \Psi_k \rangle \in \left(\mathbb{C}^2\right)^{\otimes (N-k)} \otimes \left(\mathbb{C}^2\right)^{\otimes k}
$$

可近似视为 Haar 随机纯态。

由 Page 定理，若 $k \leq N/2$，则辐射熵近似为

$$
S_{\mathrm{rad}}(k) \approx k_B \left( k \ln 2 - \frac{1}{2} \right),
$$

而当 $k \geq N/2$ 时，较小子系统为黑洞，辐射熵变为

$$
S_{\mathrm{rad}}(k) \approx k_B \left( (N-k) \ln 2 - \frac{1}{2} \right).
$$

归一化后得到一条对称的 Page 曲线，在 $k = N/2$ 处达到峰值 $\approx k_B (N \ln 2 - 1/2)$，随后随 $k$ 增大而线性下降，终态 $k=N$ 时 $S_{\mathrm{rad}}(N) \approx 0$。

### C.2 与连续时间蒸发的对应

在连续时间模型中，黑洞质量 $M(t)$ 与视界面积 $A(t)$ 随 Hawking 辐射缓慢减小，辐射熵随时间的 Page 曲线可通过将 $k$ 视为释放的有效自由度数目并用连续参数 $t$ 插值得到。近期工作的数值模拟表明，在假定幺正蒸发与快速置乱的前提下，此类简化模型给出的 Page 曲线与更精致的引力–量子场论模型在定性上吻合。

### C.3 QCA 语境下的实现

在 QCA 中，可通过以下方式实现上述玩具模型：

1. 将冻结层的 $N$ 个元胞初始化为高度纠缠态，与外部环境分离。

2. 每个时间步，通过局域幺正门将一个冻结层元胞的自由度映射到外部辐射链路上，同时在冻结层内部施加足够深度的局域随机电路，实现快速置乱。

3. 在每个步长后，对外部辐射子系统进行完全断层，计算冯·诺依曼熵，得到离散版 Page 曲线。

该过程在任意可编程量子计算平台上均可实现，为检验"冻结层–连接–Page 曲线"三者之间的定量关系提供了可行路径。

---

## Appendix D. Remarks on Extensions and Open Problems

1. **旋转与带电黑洞**

   对 Kerr 与 Reissner–Nordström 黑洞，视界结构与温度–角动量–电荷关系更加复杂。QCA 模型可通过在冻结层引入角动量与荷流密度的各向异性来模拟这些效应，连接计数与熵–面积关系仍有望保持主导形式。

2. **多视界与内视界稳定性**

   在存在内视界的情形（如 Reissner–Nordström、Kerr–Newman），可构造多层冻结层，并分析其上连接网络的拓扑结构与信息传递。离散模型可能为"质量膨胀"与内视界不稳定性的微观机制提供新的视角。

3. **与岛公式的关系**

   近年的岛公式通过引入"量子极值曲面"重构辐射熵计算。QCA 中的冻结层可视为某类离散极值曲面，其位置由信息速率与纠缠结构共同决定。如何将二者的变分问题统一为一个离散–连续混合的极值问题，是后续值得深入研究的方向。

4. **观测约束与复杂性界**

   虽然信息在 QCA 中严格保存，但解码黑洞辐射中的信息可能需要指数大的电路复杂度。如何在本框架中引入复杂性几何与"可计算性"边界，将是连接信息悖论与计算复杂性理论的重要桥梁。


