# 因果结构的统一理论：时间刻度、偏序与广义熵

---

## Abstract

本文在单一数学框架中给出"什么是因果"的统一刻画。核心观点是：因果并非附加在时空或量子态之上的外在关系，而是由三类结构的兼容性共同定义的统一对象：

1. **几何偏序**：全局双曲洛伦兹流形上的光锥结构与小因果菱形的局域偏序；

2. **幺正演化与时间刻度**：由散射相位梯度、Wigner–Smith 群延迟与谱移函数构成的统一时间刻度；

3. **广义熵与信息单调性**：小因果菱形上广义熵极值及 QNEC/QFC 型不等式所刻画的时间箭头。

在谱与散射端，本文采用刻度同一式

$$
\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega),
$$

其中 $\varphi$ 为总散射半相位，$\rho_{\mathrm{rel}}$ 为相对态密度，$Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)$ 为 Wigner–Smith 群延迟算子。该等式源于 Birman–Kreĭn 公式与谱移函数理论，将"时间延迟"视为谱–相位几何的导数。

在代数量子场论与全息引力端，本文以 Tomita–Takesaki 模块流及 Null–Modular 双覆盖刻画因果钻石上的"模时间"，其生成元为应力–能量张量沿零边界的加权积分，并在重叠因果钻石链上满足 Markov 容斥律与强次可加性的饱和。在引力与几何端，引入 Gibbons–Hawking–York 边界项及其零类与角点推广保证变分良定，Brown–York 准局域应力张量成为沿边界"时间平移"的哈密顿生成元，几何时间由 Hamilton–Jacobi 关系确定。

本文建立以下统一命题：在满足局域量子能量条件、Hadamard 态与小因果菱形极限的半经典—全息窗口内，存在一类统一时间刻度等价类 $[\tau]$，使得：

* 几何因果偏序等价于存在严格递增的时间函数 $\tau\colon M\to\mathbb R$；

* 散射相位梯度与群延迟迹在该刻度下给出"可观测因果顺序"的读数；

* 小因果菱形上广义熵 $S_{\rm gen}$ 的极值与单调性在该刻度下与非线性爱因斯坦方程及其稳定性等价。

由此，因果可以被重述为：存在一套在几何、散射与熵三个侧面上自洽的偏序—时间刻度结构，并在拓扑上无异常。本文给出该结构的公理化定义，提出若干主定理，并在附录中给出与刻度同一式、信息几何变分原理及 Null–Modular 双覆盖相关的证明框架。

---

## Keywords

因果结构；时间刻度；偏序；广义熵；谱移函数；Wigner–Smith 群延迟；Birman–Kreĭn 公式；Tomita–Takesaki 模块流；Quantum Null Energy Condition；小因果菱形；Gibbons–Hawking–York 边界项；Brown–York 应力张量；Null–Modular 双覆盖；Markov 性；信息几何变分原理

---

## Introduction & Historical Context

经典广义相对论中，因果常以光锥与时间函数刻画。全球双曲洛伦兹流形上的稳定因果性等价于存在严格递增时间函数 $T\colon M\to\mathbb R$，使得若 $q\in J^+(p)$，则 $T(q)\ge T(p)$。这一结构保证了柯西问题的良定性与"无闭因果曲线"的条件。

在量子场论中，因果性通常表述为局域算符在类空间隔点处对易，即微因果性。Wightman 公理与代数量子场论框架在给定因果结构的情况下构造场的代数，但很少反向追问：是否可以仅从算子代数与态的结构中"恢复"因果偏序。

全息与信息论的发展引入了以熵与相对熵刻画因果的新视角。Jacobson 提出"纠缠平衡假说"：在固定体积的小测地球上，广义熵达到极值当且仅当局域满足爱因斯坦方程，从而在半经典窗口中建立了"引力场方程 = 小球纠缠极值条件"的对应。之后工作进一步结合 Ryu–Takayanagi 公式与相对熵，将广义熵的二阶变分与 Bulk 规范能量联系起来。

另一方面，散射理论与谱理论的长期发展给出了一整套精确的"相位—谱移—时间延迟"结构。Birman–Kreĭn 公式表明，对于一对自伴算子 $(H,H_0)$ 满足迹类扰动条件，存在谱移函数 $\xi(\omega)$，使得散射行列式的相位由 $\xi$ 决定；由此得到总散射相位的导数与谱移函数的导数、相对态密度、Wigner–Smith 群延迟迹之间的等价关系。这些结果说明，可以在频率域内建立"以相位梯度为密度"的时间刻度。

近年的一个重要进展是量子零能条件 QNEC 的证明。QNEC 将某点处沿零方向的应力–能量期望值与经过该点的割面广义熵在零方向上的二阶形变联系起来，是 ANEC 的局域量子化形式。Koeller–Leichenauer 及后续工作则显示，对半空间或由零平面切割出的区域，其模哈密顿量可以写成沿零方向的局域能流积分，从而建立了"局域模时间—能流—QNEC"的联系。

Casini–Huerta–Myers 对共形场论中球形区域的真空模哈密顿量进行了系统分析，利用共形变换将球形割面映射到 Rindler 楔的加速坐标系中，从而将模流几何化为 boost 生成元，并由此给出球形区域全息纠缠熵的推导。Casini–Teste–Torroba 则研究了零平面上一般区域的模哈密顿量，证明其在零平面上的局域性并建立了 Markov 性与强次可加性的饱和。

这些分散发展的结果指向一个更强的统一图景：

1. 在散射与谱端，时间可以理解为由相位梯度与群延迟刻度确定的参数；

2. 在代数与全息端，模时间由状态—代数对确定，并在几何上可实现为零边界上的加权能流；

3. 在引力与几何端，小因果菱形上广义熵的极值与单调性与局域引力场方程等价；

4. 在零平面与因果钻石链上，模哈密顿量的局域性与 Markov 性给出因果链上的信息结构。

本文的目标是将这些结构纳入单一公理体系，将"因果"定义为一个由偏序、统一时间刻度与广义熵单调性共同构成的对象，并给出三者之间的等价定理与拓扑约束。

---

## Model & Assumptions

本节给出本文使用的几何、散射、代数与熵结构，并列出统一因果理论所依赖的公理与假设。

### 几何背景与因果菱形

令 $(M,g)$ 为四维定向、时间定向的洛伦兹流形，度规签名取 $(-,+,+,+)$，满足：

* 全局双曲性：存在 Cauchy 片 $\Sigma \subset M$，每条非延拓类时或光状曲线与 $\Sigma$ 恰交一次；

* 稳定因果性：不存在闭因果曲线，且存在光滑时间函数 $T\colon M\to\mathbb R$ 严格沿所有将来定向类时曲线递增。

对任一点 $p\in M$，取足够小的本征尺度 $r\ll L_{\rm curv}(p)$，定义小因果菱形

$$
D_{p,r}=J^+(p^-)\cap J^-(p^+),
$$

其中 $p^\pm$ 为沿某参考类时方向本征时间 $\pm r$ 的点。$D_{p,r}$ 的边界由两族零测地生成的零超曲面 $\mathcal N_\pm$ 及其交线组成，构成局域因果几何的基本单元。

**公理 G（几何因果公理）**

1. $(M,g)$ 满足上述全局双曲性与稳定因果性；

2. 对任意 $p$ 与足够小 $r$，小因果菱形 $D_{p,r}$ 可在正规坐标下与 Minkowski 空间的因果菱形同胚，且曲率修正为 $O(r^2)$。

### 散射系统与谱移函数

在 Hilbert 空间 $\mathcal H$ 上考虑一对自伴算子 $(H,H_0)$，满足：

* $H$ 相对 $H_0$ 为迹类扰动，或其 resolvent 差为迹类；

* 存在波算子 $W_\pm$ 且完备，从而散射算子 $S=W_+^\dagger W_-$ 定义良好；

* 在绝对连续谱上，$S$ 纤维化为酉矩阵族 $S(\omega)$。

由谱移函数理论知，存在局部可积函数 $\xi(\omega)$，使得对足够光滑的测试函数 $f$，有

$$
\mathrm{tr}(f(H)-f(H_0))=\int_\mathbb R\xi(\omega)f'(\omega)\,{\rm d}\omega,
$$

且 Birman–Kreĭn 公式给出

$$
\det S(\omega)=\exp\bigl(-2\pi i\xi(\omega)\bigr).
$$

定义总散射相位

$$
\Phi(\omega)=\arg\det S(\omega),\qquad \varphi(\omega)=\tfrac12\Phi(\omega),
$$

相对态密度

$$
\rho_{\rm rel}(\omega)=-\xi'(\omega),
$$

以及 Wigner–Smith 群延迟算子

$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega),
$$

其迹 $\operatorname{tr}Q(\omega)$ 对应能量为 $\omega$ 的群延迟。

由上定义可得刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\rm rel}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

在适当正则性与能窗限制下成立。

**公理 S（散射刻度公理）**

1. 对考虑的能窗 $I\subset\mathbb R$，刻度同一式几乎处处成立；

2. $\rho_{\rm rel}(\omega)\ge 0$ 几乎处处，且 $\rho_{\rm rel}\not\equiv 0$；

3. $Q(\omega)$ 在 $I$ 上为正半定算子，且 $\operatorname{tr}Q(\omega)$ 局部可积。

在此基础上定义散射时间刻度：

**定义 2.1（散射时间刻度）**

相对于参考点 $\omega_0\in I$，定义

$$
\tau_{\rm scatt}(\omega)-\tau_{\rm scatt}(\omega_0)
=\int_{\omega_0}^{\omega}\rho_{\rm rel}(\tilde\omega)\,{\rm d}\tilde\omega
=\frac{1}{2\pi}\int_{\omega_0}^{\omega}\operatorname{tr}Q(\tilde\omega)\,{\rm d}\tilde\omega.
$$

由公理 S，$\tau_{\rm scatt}$ 在 $I$ 上严格递增。

### 边界代数、模块流与 Null–Modular 双覆盖

令 $\mathcal A_\partial$ 为适当边界上的可观测代数，$\omega$ 为其忠实正态态。Tomita–Takesaki 理论赋予对应的模算子 $\Delta_\omega$ 与模流

$$
\sigma_t^\omega(A)=\Delta_\omega^{it}A\Delta_\omega^{-it}.
$$

对 Minkowski 时空中球形区域或楔形区域的真空态，模流可几何化为相应因果钻石或楔形区域中的 Killing 流。

对因果钻石 $D(p,q)$，其边界可分解为两片零超曲面 $\mathcal N^\pm$，去除角点后得到两叶 $E^\pm$。在每一叶上引入仿射参数 $\lambda$ 与横向坐标 $x_\perp$，构成零边界的双覆盖

$$
\widetilde E_D=E^+\sqcup E^-.
$$

Casini–Teste–Torroba 等结果表明，在共形场论真空及其适当形变下，$D$ 的模哈密顿量可写为沿 $\widetilde E_D$ 的局域能流积分：

$$
K_D=2\pi\sum_{\sigma=\pm}\int_{E^\sigma}g_\sigma(\lambda,x_\perp)\,T_{\sigma\sigma}(\lambda,x_\perp)\,{\rm d}\lambda\,{\rm d}^{d-2}x_\perp,
$$

其中 $T_{\sigma\sigma}$ 为沿零方向的应力–能量张量分量，$g_\sigma$ 为由几何决定的权函数。

**公理 M（模流局域化公理）**

1. 对小因果菱形 $D_{p,r}$，在半经典—全息窗口内存在上述局域模哈密顿量表达；

2. 模时间参数 $t_{\rm mod}$ 与零方向仿射参数 $\lambda$ 单调同向。

### GHY 边界项、Brown–York 应力与几何时间

在具有共维一边界 $\partial M$ 的引力系统中，爱因斯坦–Hilbert 作用

$$
S_{\rm EH}=\frac{1}{16\pi G}\int_M R\sqrt{-g}\,{\rm d}^4x
$$

在变分时会产生边界上法向导数项。为保证在固定边界诱导度规 $h_{ab}$ 下变分良定，需要加入 Gibbons–Hawking–York 边界项

$$
S_{\rm GHY}=\frac{1}{8\pi G}\int_{\partial M}K\sqrt{|h|}\,{\rm d}^3x,
$$

以及对零类与角点的推广项。Brown–York 准局域应力张量定义为

$$
T^{ab}_{\rm BY}=\frac{2}{\sqrt{|h|}}\frac{\delta S}{\delta h_{ab}}
=\frac{1}{8\pi G}(K^{ab}-Kh^{ab})+\cdots,
$$

其中 $\cdots$ 表示零类与角点修正。对沿边界时间平移的 Killing 向量 $t^a$，相应哈密顿量为

$$
H_\partial=\int_\Sigma T^{ab}_{\rm BY}t_a n_b\,{\rm d}^{d-1}x,
$$

其中 $\Sigma$ 为边界上的空间切片，$n^a$ 为其法向。

几何时间 $\tau_{\rm geom}$ 可视为由 $H_\partial$ 生成的参量，并通过 Hamilton–Jacobi 关系与边界作用联系。

**公理 B（边界变分公理）**

1. 作用 $S=S_{\rm EH}+S_{\rm GHY}+\cdots$ 在固定边界几何数据下变分良定；

2. $T^{ab}_{\rm BY}$ 有界，且 $H_\partial$ 在选定的边界片族上定义良好；

3. 边界时间平移群 $\{\Phi_{\tau_{\rm geom}}\}$ 在半经典窗口内可与模流共形对齐。

### 广义熵与局域量子条件

对因果菱形 $D_{p,r}$ 内的割面 $\Sigma$，定义广义熵

$$
S_{\rm gen}(\Sigma)=\frac{A(\Sigma)}{4G\hbar}+S_{\rm out}(\Sigma),
$$

其中 $S_{\rm out}$ 为割面外侧量子场的冯·诺依曼熵。Jacobson 的"纠缠平衡"与后续工作表明，在适当约束下，小球或小因果菱形上 $S_{\rm gen}$ 的极值条件等价于局域爱因斯坦方程。

Quantum Null Energy Condition 给出沿零方向的局域不等式：

$$
\langle T_{kk}(x)\rangle_\psi\ge\frac{\hbar}{2\pi}\frac{{\rm d}^2S_{\rm out}}{{\rm d}\lambda^2}(x),
$$

其中 $k^a$ 为零向量，$\lambda$ 为其仿射参数。该不等式已在宽泛的 CFT 类中得到严格证明，并与局域模哈密顿量形变关系紧密相关。

**公理 E（广义熵—能量公理）**

1. 对每个小因果菱形 $D_{p,r}$，在固定合适"体积"或等效局域守恒量约束下，$S_{\rm gen}$ 在一个参考割面处取一阶极值；

2. 对所有零方向形变，$S_{\rm gen}$ 的二阶变分满足 QNEC/QFC 型不等式；

3. 相对熵对 Cauchy 片叶无关，且等价于 Iyer–Wald 正则能量。

### 拓扑与 $\mathbb Z_2$ 扇区假设

在具有自指散射网络或非平凡拓扑的系统中，散射半相位的平方根给出主 $\mathbb Z_2$ 丛，其 holonomy $\nu_{\sqrt S}(\gamma)\in\{\pm1\}$ 可视为环路上的拓扑指标。相应的体积分 BF 理论扇区类 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$ 描述可能存在的拓扑异常。

**公理 T（拓扑无异常公理）**

在小因果菱形极限及其拼合成的有限区域内，满足 $[K]=0$，等价地，对所有适当闭路 $\gamma$，有 $\nu_{\sqrt S}(\gamma)=+1$。

---

## Main Results (Theorems and Alignments)

在上述公理体系下，本文提出并论证以下主要结果。

### 定理 1（统一时间刻度等价类）

在公理 S、M 与 B 成立的半经典—全息窗口内，存在一类时间刻度等价类 $[\tau]$，满足：

1. 散射时间刻度 $\tau_{\rm scatt}$ 属于 $[\tau]$；

2. 模时间 $\tau_{\rm mod}$ 属于 $[\tau]$；

3. 几何时间 $\tau_{\rm geom}$ 属于 $[\tau]$。

更具体地，存在常数 $a>0,b\in\mathbb R$，使得在考虑的能窗与因果菱形族上，

$$
\tau_{\rm scatt}=a\tau_{\rm mod}+b,\qquad
\tau_{\rm geom}=c\tau_{\rm mod}+d,
$$

其中 $c>0,d\in\mathbb R$ 为常数。等价类 $[\tau]$ 由上述任一刻度代表，至仿射变换唯一。

### 定理 2（因果偏序的等价刻画）

在公理 G、S、M、E 成立的区域内，统一时间刻度等价类 $[\tau]$ 给出因果偏序的等价刻画：

对任意 $p,q\in M$，以下命题等价：

1. 几何因果性：$q\in J^+(p)$，即存在从 $p$ 到 $q$ 的未来定向非类空曲线；

2. 时间刻度单调性：存在 $\tau\in[\tau]$，使得对所有沿类时曲线 $\gamma$ 从 $p$ 到 $q$ 的连接，有 $\tau(p)\le\tau(q)$，且对某条连接曲线严格不等；

3. 广义熵单调性：对包含 $p,q$ 的每个足够小因果菱形链 $\{D_j\}$，广义熵 $S_{\rm gen}$ 沿零方向与 $\tau$ 同向单调不减，并在 $p\to q$ 的极限中给出非负"熵距离"。

从而，因果偏序可以等价地视为"统一时间刻度上的单调性"或"小因果菱形链上广义熵流的单调结构"。

### 定理 3（广义熵变分原理与局域引力方程）

在公理 G 与 E 成立、并假设物质场满足适当局域守恒条件与 Hadamard 态条件时，小因果菱形上的广义熵变分条件等价于局域爱因斯坦方程：

对任意 $p\in M$ 与足够小 $r$，若对所有零方向形变，在固定合适约束下 $S_{\rm gen}$ 在参考割面处一阶极值且二阶变分非负，则在 $p$ 处有

$$
G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab},
$$

其中 $G_{ab}$ 为爱因斯坦张量，$T_{ab}$ 为物质应力–能量张量，$\Lambda$ 为常数。

反之，若上述引力方程成立，且物质态满足洞察到的局域平衡条件，则小因果菱形上的广义熵满足公理 E 所要求的一阶极值与二阶非负性。

### 定理 4（Null–Modular 双覆盖、Markov 性与因果链）

在公理 G、M 与 E 成立的共形场论真空或其小形变中，对零平面上的区域族或其共形像的因果钻石族 $\{D_j\}$，模哈密顿量满足容斥结构

$$
K_{\cup_jD_j}=\sum_{k\ge1}(-1)^{k-1}\sum_{j_1<\cdots<j_k}
K_{D_{j_1}\cap\cdots\cap D_{j_k}},
$$

相应相对熵满足 Markov 性与强次可加性的饱和。由此得到：

1. 因果钻石链上的信息传播为"无额外记忆"的 Markov 过程；

2. 统一时间刻度 $\tau$ 在该链上与模时间一致，且与零方向仿射参数单调同向；

3. 小因果菱形链上的广义熵箭头与几何因果箭头一致。

### 定理 5（拓扑无异常与规范能量非负的等价性）

在公理 T 成立的情形下，小因果菱形拼合成的有限区域内，以下命题等价：

1. $\mathbb Z_2$–BF 体积分扇区类 $[K]=0$；

2. 对所有物理允许的闭路 $\gamma$，散射半相位平方根的 holonomy 满足 $\nu_{\sqrt S}(\gamma)=+1$；

3. 在满足引力场方程与局域量子条件的物质配置上，小因果菱形上的规范能量二阶变分非负。

反之，若存在 $[K]\neq 0$ 或 $\nu_{\sqrt S}(\gamma)=-1$ 的环路，则可构造出违反规范能量非负的配置，从而破坏广义熵单调性与因果箭头的一致性。

---

## Proofs

本节给出主定理的证明思路与关键步骤，技术细节放入附录。

### 定理 1 的证明思路（统一时间刻度等价类）

**步骤 1：散射时间刻度的存在与仿射唯一性**

由公理 S，刻度同一式在能窗 $I$ 内成立，且 $\rho_{\rm rel}(\omega)\ge 0$ 几乎处处，不恒为零。定义

$$
\tau_{\rm scatt}(\omega)-\tau_{\rm scatt}(\omega_0)
=\int_{\omega_0}^{\omega}\rho_{\rm rel}(\tilde\omega)\,{\rm d}\tilde\omega,
$$

可知 $\tau_{\rm scatt}$ 为严格递增连续函数。对任何另一满足相同刻度密度的函数 $\tilde\tau(\omega)$，其导数几乎处处满足

$$
\frac{{\rm d}\tilde\tau}{{\rm d}\omega}=c\,\rho_{\rm rel}(\omega),
$$

其中 $c>0$。积分得 $\tilde\tau=a\tau_{\rm scatt}+b$，即存在仿射唯一性。

若引入 Poisson 或其他正定窗函数构造窗口化刻度 $t_\Delta$，则在适当解析性条件下可证明 $t_\Delta$ 同样严格递增且至仿射唯一，形成能窗上的"散射时钟"。

相关技术可参见谱移函数与 Birman–Kreĭn 公式的标准证明，以及波迹不变量与散射相位导数之间的联系。

**步骤 2：模时间与散射时间的对齐**

Casini–Huerta–Myers 的结果表明，对共形场论中球形区域的真空态，其模哈密顿量与对应 Rindler 楔的 boost 生成元共形等价，从而模时间 $t_{\rm mod}$ 等同于沿加速轨迹的固有时间（至比例因子）。在全息情形下，模流对应于 Bulk 中某一 Killing 流，其参数与 Bulk 中的"几何时间"一致。

另一方面，散射系统可通过将边界模哈密顿量视为边界散射哈密顿量的函数，从而将其谱测度与散射相位导数—谱移函数联系起来。结合刻度同一式可得：模时间与散射时间刻度的导数差异仅为常数因子，从而两者为仿射等价。

Koeller–Leichenauer 及后续工作对零平面形变的局域模哈密顿量分析表明，模时间二阶形变直接与 $T_{kk}$ 相关，而 $T_{kk}$ 又由散射相位与群延迟控制，这为上述等价提供了局域谱–能流桥接。

**步骤 3：几何时间与模时间的对齐**

在具有 GHY 边界项的引力系统中，Brown–York 准局域能量可视为边界时间平移的哈密顿生成元。通过 Hamilton–Jacobi 关系，可以将边界几何时间与模时间对齐：模流的 KMS 性质与热时间假说说明，模时间刻度由态—代数对内禀决定，当该态为引力系统的"热真空"时，其模时间与边界 Killing 时间方向一致。结合全息对偶与 CHM 型构造，可以证明几何时间与模时间的差异仅为仿射变换。

综合步骤 1–3，得到统一时间刻度等价类 $[\tau]$ 的存在与仿射唯一性。

### 定理 2 的证明思路（因果偏序的等价刻画）

**(1) $\Rightarrow$ (2)：几何因果性蕴含时间刻度单调性**

由稳定因果性可知存在时间函数 $T\colon M\to\mathbb R$ 严格沿每条将来定向类时曲线递增。统一时间刻度等价类 $[\tau]$ 中的任何代表 $\tau$ 与 $T$ 之间存在严格单调函数 $f$，即 $\tau=f\circ T$。因此若 $q\in J^+(p)$，则沿任一从 $p$ 到 $q$ 的类时曲线有 $T(q)\ge T(p)$，故 $\tau(q)\ge\tau(p)$，并对至少一条曲线严格不等。

**(2) $\Rightarrow$ (1)：时间刻度单调性蕴含几何因果性**

若假设存在 $\tau\in[\tau]$，使得 $\tau(q)\ge\tau(p)$，却有 $q\notin J^+(p)$，则存在穿越 $p,q$ 的类时曲线与不穿越的 Cauchy 片构造，导致对某些路径上时间函数必须降低，违背 $\tau$ 沿类时曲线单调递增的性质，与公理 G 矛盾。标准的 Hawking–Ellis 理论给出"时间函数存在性与稳定因果性"的等价性，这里用 $\tau$ 替代 $T$ 重新表述。

**(1)+(2) $\Rightarrow$ (3)：几何因果性与时间刻度单调性蕴含广义熵单调性**

QNEC 给出沿零方向的局域不等式，将 $T_{kk}$ 与广义熵二阶形变联系起来；IGVP 与相对熵单调性则将 $T_{kk}$ 与几何的 $R_{kk}$ 与广义熵一阶极值条件联系起来。组合可得：在引力场方程成立且物质态满足 Hadamard 条件时，沿任何满足几何因果的零生成元，$S_{\rm gen}$ 在统一时间刻度 $\tau$ 的增加方向上二阶导数非负，从而 $S_{\rm gen}$ 单调不减。

在小因果菱形链上，对每个菱形的上下割面应用上述论证，并利用相对熵在 Cauchy 片上的片叶无关性，将局域单调性推广到整个链，得到 (3)。

**(3) $\Rightarrow$ (1)：广义熵单调性蕴含几何因果性**

若假设存在 $p,q$ 不满足几何因果性却满足 (3)，则可沿一条"时间回环"构造闭零曲线，使得一圈绕行后几何上回到原点，而 $S_{\rm gen}$ 的单调性迫使每圈增加非负熵，除非 $T_{kk}=0$ 且 $R_{kk}=0$，这与 QNEC 的严格性与引力场方程的局域非退化性矛盾。因此广义熵单调性排除了几何上的闭因果路径，恢复了几何因果性。

### 定理 3 的证明思路（IGVP 与爱因斯坦方程）

该定理的证明遵循 Jacobson"纠缠平衡"与后续全息推导的基本思路：

1. 在 $p$ 处选定 Riemann 正交坐标，使得度规在 $p$ 处为 Minkowski，Christoffel 符号消失，曲率贡献出现在二阶及更高阶；

2. 考虑包含 $p$ 的小因果菱形 $D_{p,r}$，其边界腰面附近面积在零方向上的二阶变分可用 Raychaudhuri 方程表示，其中包含 $R_{kk}$ 项；

3. 广义熵一阶变分 ${\rm d}S_{\rm gen}/{\rm d}\lambda$ 中，面积项提供 $R_{kk}$ 贡献，熵项通过局域第一定律与相对熵线性响应与 $T_{kk}$ 相关；

4. 要求在固定体积或等效约束下 ${\rm d}S_{\rm gen}/{\rm d}\lambda=0$，可得到 $R_{kk}=8\pi G\,T_{kk}$；

5. 二阶变分非负性利用 QNEC/QFC 及 Hollands–Wald 规范能量非负性给出，确保上述条件在所有零方向上稳定，从而通过 Bianchi 恒等式得到完整的 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。

反向推理则通过将给定的爱因斯坦方程代回面积与熵的变分表达式，验证广义熵极值与二阶非负性。

相关完整论证可见 Jacobson 的原始工作及随后利用相对熵与 holographic entanglement 的推导。

### 定理 4 与定理 5 的证明思路

定理 4 主要依赖 Casini–Teste–Torroba 对零平面区域模哈密顿量局域表达与 Markov 性的证明。其核心是：

1. 对零平面 $P$ 上的任意区域族 $\{A_j\}$，模哈密顿量 $K_{A_j}$ 具有沿零方向的局域表达；

2. 利用相对熵的张量积结构与模流性质，可证明模哈密顿量满足容斥公式；

3. 相应的相对熵满足强次可加性饱和，从而给出 Markov 条件；

4. 通过共形变换将零平面区域映射为因果钻石族，得到因果钻石链上的容斥—Markov 结构。

定理 5 则将 BF 体积分扇区的 $\mathbb Z_2$ 同调类 $[K]$ 与散射半相位平方根的 holonomy 及规范能量非负性联系起来。其关键是：若 $[K]\neq 0$，则存在某二维循环上 $\mathbb Z_2$ 曲率非零，可构造出沿该循环传播的场配置，使得模哈密顿量的二阶变分产生负规范能量，从而违反 QNEC/QFC。反之，若所有规范能量二阶变分非负，则可证明 $[K]=0$，消除拓扑异常。

---

## Model Apply

本节展示统一因果结构在几个典型情形中的应用。

### FRW 宇宙学中的时间与因果箭头

考虑平直 FRW 度规

$$
{\rm d}s^2=-{\rm d}t^2+a(t)^2({\rm d}r^2+r^2{\rm d}\Omega^2),
$$

其中 $a(t)$ 为尺度因子。观测到的红移 $1+z=a(t_0)/a(t_e)$ 可重写为发射与接收时刻的固有相位节奏比

$$
1+z=\frac{(\partial_t\phi)_e}{(\partial_t\phi)_0},
$$

其中 $\phi$ 为某标准谱线的相位。借助刻度同一式，可将 $(\partial_t\phi)$ 解释为统一时间刻度 $\tau$ 的变化率：${\rm d}\phi/{\rm d}\tau=\omega_{\rm phys}$。从而 FRW 中的红移成为统一时间刻度在宇宙学尺度上的重标，体现了"宇宙因果箭头"的宏观表现。

进一步，在含物质与辐射的 FRW 模型中，Friedmann 方程可视为将小因果菱形上的广义熵变分条件推广到共形时间切片上的平均形式，体现了"广义熵几何方程"的宇宙学版本。

### 黑洞视界与 Page 曲线

在黑洞蒸发过程中，可将靠近视界的小因果菱形沿视界拼合成链。统一因果结构的视角下：

* 视界附近的模哈密顿量局域化为沿零方向的能流积分；

* 广义熵箭头沿视界单调，使得外部观察者所见的 Page 曲线可理解为对一族因果菱形的 $S_{\rm gen}$ 聚合读数；

* QNEC 保证了沿视界的局域能流与熵二阶变分之间的约束，从而限制了可能的"超快蒸发"或"信息泄露"情形。

在全息框架中，这一描述与岛公式、量子极小面条件相容，体现了统一因果结构在视界—信息问题中的作用。

### 一维散射与信号处理

在一维势散射或微波网络中，Wigner–Smith 群延迟矩阵的迹可直接通过相位频率响应测量。统一因果结构框架下：

* 因果性要求群延迟非负，给出散射时间刻度的单调性；

* 小频率窗口内的 $\tau_{\rm scatt}$ 与几何时间及模时间等价；

* 对反馈散射网络，自指结构可能引入非平凡的 $\mathbb Z_2$ holonomy，其存在与否可通过频率闭路上的半相位跳变检测，与定理 5 的拓扑无异常条件直接关联。

这些可在微波电路、光子晶体与冷原子环路系统中实现，为检验统一时间刻度与因果箭头的实验路径提供具体方案。

---

## Engineering Proposals

统一因果结构虽然建立在半经典与全息理论层面，但其中多项刻度与不等式具有直接可测的工程含义。本节给出若干代表性提案。

### 时间刻度标定与跨平台校准

1. **微波网络群延迟计量**：构建在已知拓扑上的多端口散射网络，测量 $S(\omega)$ 与 $Q(\omega)$，通过刻度同一式重建 $\rho_{\rm rel}(\omega)$ 与 $\tau_{\rm scatt}(\omega)$，检验其单调性与正性，从而在实验上实现统一时间刻度的"散射端"标定；

2. **光学频梳与相位节奏**：利用光学频梳在不同平台（光纤、集成光子、冷原子）之间传递相位信息，将各平台的局部时间刻度嵌入统一的相位–频率刻度，构建跨平台的统一时间刻度网。

### 广义熵与能流的实验间接探测

1. **量子光学中 QNEC 的近似检验**：在有限模式的高维度光场中，通过对截断系统的熵–能量测量，构造"离散版 QNEC"，检验广义熵二阶形变与沿某有效零方向能流之间的不等式，从而对 QNEC 的某种有限维影像进行实验验证；

2. **冷原子系统中的局域模哈密顿量**：利用可控势阱与时间调制，在一维或二维冷原子系统中构造近似的因果菱形区域，通过测量子系统熵随局域形变的变化，重建模哈密顿量的局域部分，间接检验 Null–Modular 双覆盖的结构。

### 拓扑因果扇区与 $\mathbb Z_2$ 指标测量

在具有环路与反馈的散射网络中，通过测量闭路上的散射相位随参数变化的拓扑性质，可以提取 $\nu_{\sqrt S}(\gamma)$。实验上可以通过：

* 可调磁通的 Aharonov–Bohm 环路；

* 拓扑超导线端点的 Andreev 反射；

* 自指微波网络中的反馈环相位闭合条件，

来检测 $\mathbb Z_2$ holonomy 的存在，从而在实验上约束定理 5 中的拓扑无异常条件。

---

## Discussion (risks, boundaries, past work)

### 适用域与边界条件

统一因果结构的推导依赖多重前提：

* 半经典或全息窗口：引力场方程与 QFT 需在一类有效理论中可控；

* Hadamard 态与正则性：广义熵与 QNEC 的证明均依赖态的正则性；

* 小因果菱形极限：IGVP 的变分推导在 $r\to 0$ 极限下才严格成立。

因此，在强量子引力区域、非局域场论或具有严重超选扇区的体系中，上述结构可能失效或需改写。

### 与既有因果概念的关系

本文将因果重述为"偏序 + 统一时间刻度 + 广义熵单调性 + 拓扑无异常"的统一对象，与传统的几何因果理论、代数量子场论微因果性和全息因果楔结构相比：

* 在几何端，统一结构内含 Hawking–Ellis 因果层级；

* 在代数端，模流与局域代数的关系通过 Null–Modular 双覆盖得到精炼；

* 在全息端，广义熵与 Bulk 几何的对应被解释为因果箭头在边界与体域上的统一投影。

### 风险与开放问题

1. **QNEC 及其推广的稳健性**：虽然 QNEC 已在广泛的情形下被证明，但其在非共形场论或强耦合情形中的细节仍在研究；

2. **拓扑异常的物理实现**：定理 5 中的 $\mathbb Z_2$ 扇区在具体现实系统中的可实现性及其对因果的影响需要更细致的模型；

3. **离散因果网与连续极限**：将统一因果结构推广到因果集或离散网格，并分析连续极限下偏序与熵结构的稳定性，是进一步连接量子引力离散模型与连续广义相对论的关键问题。

关于这些问题的大量工作分布在 QFT、全息引力与算子代数的文献中，本文仅给出一个整合视角。

---

## Conclusion

本文在统一时间刻度、边界时间几何、Null–Modular 双覆盖及广义熵变分的基础上构建了一个围绕"因果"的统一理论框架。其核心结论可概括为：

1. 在半经典—全息窗口内，存在一类统一时间刻度等价类 $[\tau]$，将散射时间、模时间与几何时间粘合为单一刻度；

2. 几何偏序 $(M,\preceq)$ 与统一刻度上的单调性、以及小因果菱形链上的广义熵单调性三者等价，给出因果的三个互补刻画；

3. 小因果菱形上的广义熵变分原理与局域爱因斯坦方程等价，使引力场方程成为"熵在因果边界上的组织方式"的表达；

4. Null–Modular 双覆盖及 Markov 性保证因果钻石链上的信息传播具有局域性与无额外记忆结构；

5. $\mathbb Z_2$–BF 扇区的拓扑无异常与规范能量非负性等价，从而在拓扑层面约束因果结构的允许扇区。

在这一图景下，时空度规、散射矩阵、模流与广义熵不再是独立对象，而是同一因果结构在不同投影上的表现。时间则被理解为该结构上严格单调的刻度坐标，其箭头由广义熵单调性与拓扑无异常共同选定。

---

## Acknowledgements

作者感谢相关领域的研究工作为本文提供的基础，包括谱移函数与 Birman–Kreĭn 理论、量子零能条件与局域模哈密顿量、全息纠缠熵与引力场方程以及 Null–Modular 双覆盖与 Markov 性的系列研究。

---

## Code Availability

本文所有结果基于解析推导与现有数学物理定理，未使用专门数值代码。未来若开展基于散射网络与数值相对论的模拟，将另行公开相应代码实现。

---

## References

[1] M. Sh. Birman and M. G. Kreĭn, "On the theory of wave and scattering operators", Soviet Math. Dokl. 3, 740–744 (1962).

[2] K. B. Sinha, "Spectral shift function and trace formula", Proc. Indian Acad. Sci. (Math. Sci.) 104, 571–588 (1994).

[3] D. Borthwick, "The Birman–Kreĭn formula and scattering phase", arXiv:2110.06370 (2021).

[4] H. Casini, M. Huerta and R. C. Myers, "Towards a derivation of holographic entanglement entropy", JHEP 05, 036 (2011).

[5] T. Jacobson, "Entanglement Equilibrium and the Einstein Equation", Phys. Rev. Lett. 116, 201101 (2016).

[6] R. Bousso, Z. Fisher, S. Leichenauer and A. C. Wall, "Proof of the Quantum Null Energy Condition", Phys. Rev. D 93, 024017 (2016).

[7] S. Balakrishnan, T. Faulkner, Z. U. Khandker and H. Wang, "A general proof of the quantum null energy condition", JHEP 09, 020 (2019).

[8] J. Koeller and S. Leichenauer, "Local modular Hamiltonians from the quantum null energy condition", Phys. Rev. D 97, 065011 (2018).

[9] H. Casini, E. Teste and G. Torroba, "Modular Hamiltonians on the null plane and the Markov property of the vacuum state", J. Phys. A: Math. Theor. 50, 364001 (2017).

[10] G. Sárosi and T. Ugajin, "Modular Hamiltonians of excited states, OPE blocks and emergent bulk fields", JHEP 01, 012 (2018).

[11] A. Shahbazi-Moghaddam, "Aspects of Generalized Entropy and Quantum Null Energy Condition", PhD thesis, University of California, Berkeley (2020).

[12] E. Oh, I.-Y. Park and S.-J. Sin, "Complete Einstein equations from the generalized first law of entanglement", Phys. Rev. D 98, 026020 (2018).

---

## Appendices

### Appendix A：刻度同一式与统一时间刻度的构造

本附录给出刻度同一式的推导框架与统一时间刻度等价类存在—唯一性的技术细节。

#### A.1 谱移函数与 Birman–Kreĭn 公式

设 $(H,H_0)$ 为自伴算子对，满足差为迹类或 resolvent 差为迹类。由谱移函数理论，存在唯一（模常数）函数 $\xi(\omega)$，使得对任意 $f\in C_0^\infty(\mathbb R)$，有

$$
\mathrm{tr}(f(H)-f(H_0))=\int_\mathbb R\xi(\omega)f'(\omega)\,{\rm d}\omega.
$$

选择 $f(\lambda)=\chi_{(-\infty,\omega]}(\lambda)$ 的平滑近似，可将 $\xi(\omega)$ 解释为两个谱投影差的迹，即

$$
\xi(\omega)=\mathrm{tr}\bigl(E_H((-\infty,\omega])-E_{H_0}((-\infty,\omega])\bigr).
$$

Birman–Kreĭn 公式给出散射行列式与谱移函数之间的关系：

$$
\det S(\omega)=\exp\bigl(-2\pi i\xi(\omega)\bigr).
$$

取对数并微分得

$$
\partial_\omega\Phi(\omega)=\partial_\omega\arg\det S(\omega)=-2\pi\xi'(\omega),
$$

从而定义

$$
\rho_{\rm rel}(\omega)=-\xi'(\omega)=\frac{1}{2\pi}\Phi'(\omega).
$$

#### A.2 Wigner–Smith 群延迟迹

散射矩阵 $S(\omega)$ 在绝对连续谱上为酉算子族，其对频率的导数给出 Wigner–Smith 群延迟算子

$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega).
$$

由于 $S(\omega)$ 酉性，$Q(\omega)$ 自伴。将 $S(\omega)$ 分解为本征相位与本征向量，$S(\omega)=\sum_n e^{2i\delta_n(\omega)}\ket{n(\omega)}\bra{n(\omega)}$，则

$$
Q(\omega)=2\sum_n\frac{\partial\delta_n(\omega)}{\partial\omega}\ket{n(\omega)}\bra{n(\omega)}+\text{非对角项},
$$

从而

$$
\operatorname{tr}Q(\omega)=2\sum_n\frac{\partial\delta_n(\omega)}{\partial\omega}
=\partial_\omega\Phi(\omega).
$$

由此得到刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\rm rel}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

在非局域势或耗散散射情形，可利用修正行列式与自伴扩张理论对上述公式进行推广，其形式保持不变，只需对谱移函数进行重整化。

#### A.3 窗口化时钟与仿射唯一性

为抑制共振与高频尾部影响，引入正定窗函数 $h_\Delta$（例如 Poisson 核）

$$
h_\Delta(\omega)=\frac{\Delta}{\pi(\omega^2+\Delta^2)},
$$

定义卷积

$$
\Theta_\Delta(\omega)=(\rho_{\rm rel}*h_\Delta)(\omega)
=\int_\mathbb R\rho_{\rm rel}(\tilde\omega)h_\Delta(\omega-\tilde\omega)\,{\rm d}\tilde\omega.
$$

若 $\rho_{\rm rel}(\omega)\ge 0$ 且在考虑能窗内不恒为零，则 $\Theta_\Delta(\omega)>0$ 几乎处处。定义窗口化时间刻度

$$
t_\Delta(\omega)-t_\Delta(\omega_0)=\int_{\omega_0}^{\omega}\Theta_\Delta(\tilde\omega)\,{\rm d}\tilde\omega,
$$

则 $t_\Delta$ 严格递增连续。

对任一满足同一窗条件、且导数几乎处处与 $\Theta_\Delta$ 成比例的函数 $\tilde t_\Delta$，存在 $a>0,b\in\mathbb R$ 使 $\tilde t_\Delta=a t_\Delta+b$。从而在能窗 $I$ 上，"散射时钟"的刻度唯一至仿射变换。

### Appendix B：IGVP 与局域爱因斯坦方程的局部推导

#### B.1 小因果菱形几何与面积变分

在点 $p$ 的 Riemann 正交坐标中，度规展开为

$$
g_{\mu\nu}(x)=\eta_{\mu\nu}-\frac{1}{3}R_{\mu\alpha\nu\beta}(p)x^\alpha x^\beta+O(|x|^3).
$$

考虑以 $p$ 为中心、半径 $r$ 的小球或小因果菱形，其边界面积与体积的展开包含 $R_{\mu\nu}$ 贡献。例如 $d$-维小球体积有

$$
V(B_{p,r})=\frac{\Omega_{d-1}}{d}r^d\Bigl[1-\frac{R(p)}{6(d+2)}r^2+O(r^4)\Bigr].
$$

沿零向量 $k^a$ 生成的测地簇，膨胀量 $\theta$ 满足 Raychaudhuri 方程

$$
\frac{{\rm d}\theta}{{\rm d}\lambda}=-\frac{1}{2}\theta^2-\sigma_{ab}\sigma^{ab}-R_{ab}k^ak^b.
$$

在足够小 $r$ 与适当初始条件下，可将面积二阶变分表示为包含 $R_{kk}$ 的项加上 $\theta^2,\sigma^2$ 等非负贡献，在 $r\to 0$ 极限下，$R_{kk}$ 主导面积变分。

#### B.2 广义熵变分与局域第一定律

广义熵的一阶变分为

$$
\frac{{\rm d}S_{\rm gen}}{{\rm d}\lambda}
=\frac{1}{4G\hbar}\frac{{\rm d}A}{{\rm d}\lambda}
+\frac{{\rm d}S_{\rm out}}{{\rm d}\lambda}.
$$

相对熵 $S(\rho||\sigma)$ 对源态 $\rho$ 的一阶变分给出局域第一定律

$$
\delta S_{\rm out}=\delta\langle K_{\rm mod}\rangle,
$$

其中 $K_{\rm mod}$ 为参考态 $\sigma$ 的模哈密顿量。对球形区域或小因果菱形，可将 $K_{\rm mod}$ 局域化为应力–能量张量的积分，从而得到

$$
\frac{{\rm d}S_{\rm out}}{{\rm d}\lambda}
\propto\int T_{kk}\,{\rm d}\lambda\,{\rm d}^{d-2}x_\perp.
$$

要求在固定体积或等效约束下 ${\rm d}S_{\rm gen}/{\rm d}\lambda=0$，并令 $r\to 0$，利用面积变分中的 $R_{kk}$ 项与上述 $T_{kk}$ 项的比例关系，可以得到

$$
R_{kk}=8\pi G\,T_{kk}.
$$

对所有零方向成立，再结合 Bianchi 恒等式与能量–动量守恒，恢复完整爱因斯坦方程。

#### B.3 二阶变分与规范能量非负

广义熵相对参考态的二阶变分可写为规范能量

$$
\mathcal E=\delta^2S_{\rm rel},
$$

其非负性与 Hollands–Wald 规范能量非负性等价，并在 QNEC/QFC 结果中得到量化。规范能量非负性保证小因果菱形上的 IGVP 极值为稳定极值，从而确保局域爱因斯坦方程的稳定性与因果箭头的一致性。

### Appendix C：Null–Modular 双覆盖与 Markov 结构

#### C.1 零平面上的模哈密顿量

在 Minkowski 空间的零平面 $P$ 上，考虑由光状坐标 $(u,v,x_\perp)$ 描述的半空间，例如 $v\ge f(x_\perp)$。Casini–Teste–Torroba 给出真空态下的模哈密顿量局域表达：

$$
K_A=2\pi\int_{A}(\lambda-f(x_\perp))\,T_{vv}(\lambda,x_\perp)\,{\rm d}\lambda\,{\rm d}^{d-2}x_\perp,
$$

其中 $A$ 为零平面上的区域。该表达式说明模流沿零方向平移点，模时间与仿射参数 $\lambda$ 线性相关。

#### C.2 容斥性质与 Markov 性

对零平面上的区域族 $\{A_j\}$，利用应力–能量张量的线性叠加与模哈密顿量的定义，可证明

$$
K_{\cup_jA_j}=\sum_{k\ge1}(-1)^{k-1}\sum_{j_1<\cdots<j_k}
K_{A_{j_1}\cap\cdots\cap A_{j_k}}.
$$

相对熵 $S(\rho_A||\sigma_A)$ 在张量积结构下满足强次可加性，结合上述模哈密顿量容斥关系，可得对零平面区域族真空态满足 Markov 性，即条件互信息为零。这意味着沿零方向的因果链中，信息传播不携带额外记忆，仅依赖相邻段的信息。

#### C.3 共形映射到因果钻石族

通过共形变换，可将零平面区域族映射到 Minkowski 空间或更一般背景中的因果钻石族 $\{D_j\}$。共形不变性确保模哈密顿量的局域结构与容斥性质保留，从而在因果钻石链上建立 Markov 结构。统一时间刻度 $\tau$ 在该链上与零方向仿射参数单调同向，从而将因果箭头、模时间箭头与广义熵箭头统一。

