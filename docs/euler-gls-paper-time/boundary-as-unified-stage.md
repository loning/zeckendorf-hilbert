# 边界作为统一舞台：从时间翻译算子、Null–Modular 双覆盖到 GHY 边界项

---

**Abstract**
构造一个以边界为唯一基本舞台的统一框架，将三个成熟但通常分属不同语境的结构粘合为同一对象的三个投影：(i) 以 Birman–Kreĭn–Friedel–Wigner–Smith 体系为基础，由散射相位、谱移函数与 Wigner–Smith 时间延迟矩阵刻画的"时间翻译算子"；(ii) 以 Tomita–Takesaki 模理论与近年关于因果钻石/零平面模哈密顿量、Markov 性与 QNEC 的结果为基础的 Null–Modular 双覆盖与重叠因果钻石链；(iii) 以 Gibbons–Hawking–York (GHY) 边界项及其在含零类片与关节项的一般化为代表的引力边界作用与 Brown–York 准局域能量。本文在清晰列出适用域与假设的前提下，给出四个主结果：(1) 在满足迹类扰动条件的散射系统中，散射半相位导数、Kreĭn 谱移密度与 Wigner–Smith 延迟矩阵迹构成同一边界时间测度；(2) 在满足标准假设的相对论量子场论中，因果钻石与零平面上的模哈密顿量可以局域化为 Null–Modular 双覆盖上应力–能流的有权积分，并对重叠钻石族满足马尔可夫容斥律；(3) 在广义相对论的分段时空边界（含零类片与关节）上，加入 GHY 型边界/关节项后，作用量对固定诱导几何的变分良定，Brown–York 边界应力张量生成的边界时间平移构成第三种"边界时间"；(4) 在存在恰当匹配映射的情况下，这三种"边界时间"可统一为同一一参数自同构群的不同实现，从而将时间、代数和几何同时重述为边界数据的不同侧面。文末给出黑洞热力学、AdS/CFT 与散射网络实验中的统一刻度示例，并提出若干可在中尺度实验平台上检验的工程化方案。

---

**Keywords**
边界物理；时间翻译算子；Birman–Kreĭn 谱移；Wigner–Smith 时间延迟；Tomita–Takesaki 模理论；Null–Modular 双覆盖；马尔可夫性；Gibbons–Hawking–York 边界项；Brown–York 准局域能量；全息

---

## Introduction & Historical Context

### 1.1 从体域到边界的范式转移

相对论、量子场论与量子引力的发展呈现出明确的"由体到边"的趋势。量子散射理论以 $S$-矩阵为核心，直接在时空无穷远的辐射边界上编码动力学信息；Birman–Kreĭn 恒等式将散射行列式的相位与谱移函数联系起来，使"体积谱变化"可以由边界散射数据读出。([kurims.kyoto-u.ac.jp][1])

代数量子场论中，Tomita–Takesaki 模理论显示：给定局域代数与忠实态，模流 $\sigma_t^\omega$ 为该代数的典范一参数自同构群，其几何实现由 Bisognano–Wichmann 定理、球形区域与零平面模哈密顿量的局域表达得到清晰刻画。([arXiv][2])

广义相对论中，Einstein–Hilbert 体积项单独并不能给出对有边流形的良定变分原理，必须添加 Gibbons–Hawking–York 边界项；在存在零类片与关节的情形下，还必须引入相应的零边界与角点项方能保证作用量的可微性与 Hamilton–Jacobi 结构。([维基百科][3])

这些进展共同暗示：真正"可计算"的物理对象往往集中在边界，而体域更像边界数据的重建或演化结果。

### 1.2 三个表面不同的理论范式

本文关注的三个具体范式可简述如下。

(1) **散射端：时间作为边界翻译刻度**
设 $(H_0,H_0+V)$ 为一对自伴算子，$V$ 属于适当迹类，使得波算子与散射矩阵 $S(\omega)$ 良好定义并满足 Birman–Kreĭn 条件。此时存在谱移函数 $\xi(\omega)$，满足
$\det S(\omega)=\exp(-2\pi i \xi(\omega))$，
其导数 $\xi'(\omega)$ 与散射相位导数、Wigner–Smith 时间延迟矩阵 $Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)$ 的迹之间存在精确的迹公式关系。([kurims.kyoto-u.ac.jp][1])
这使得
$\varphi'(\omega)$、$\xi'(\omega)$、$\operatorname{tr}Q(\omega)$
可以共同刻画一类"边界时间测度"，从而把时间视为由边界谱数据生成的翻译参数。

(2) **代数–几何端：Null–Modular 双覆盖与重叠因果钻石链**
在 Minkowski 或 AdS 边界 CFT 中，对真空态限制到楔区、球形钻石或零平面区域，其模哈密顿量可以写成应力–能量张量在边界上的局域积分，并且在零平面上形成一族无限维 Lie 代数与 Markov 性。([arXiv][2])
对因果钻石 $D$ 引入由未来/过去零边界 $(E^+,E^-)$ 组成的 Null–Modular 双覆盖，其模哈密顿量 $K_D$ 可以写成

$$
K_D=2\pi\sum_{\sigma=\pm}\int_{E^\sigma} g_\sigma(\lambda,x_\perp)T_{\sigma\sigma}(\lambda,x_\perp),\mathrm d\lambda,\mathrm d^{d-2}x
$$

其中 $T_{\sigma\sigma}$ 为零方向分量。重叠钻石链的模哈密顿量满足容斥与马尔可夫拼接性质。

(3) **引力端：GHY 边界项、零类边界与 Brown–York 准局域能量**
在具有边界的时空流形 $\mathcal M$ 上，加入 GHY 边界项后

$$
S=S_{\mathrm{EH}}+S_{\mathrm{GHY}}
$$

才对固定诱导度规的变分良定；当边界包含零类片与关节时，还需补充零边界项与角点项。([维基百科][3])
对带边界区域进行 Hamilton–Jacobi 分析得到 Brown–York 边界应力张量

$$
T^{ab}_{\mathrm{BY}}=\frac{2}{\sqrt{-h}}\frac{\delta S}{\delta h_{ab}}
$$

其时间分量给出准局域能量与生成边界时间平移的哈密顿量。([arXiv][4])

这三条路线分别突出谱–散射、模–代数和几何–引力三个侧面，但它们都依赖于边界：散射由无穷远边界定义，模流在区域边界上局域化，引力作用的可微性由边界项决定。

### 1.3 本文的目标与主线

本文的目标是给出一个在数学上自洽且适用域明确的统一框架，将上述三个范式视为同一边界结构的三种投影。核心思想可概括为：

1. 以适当的"边界数据三元组"

$$
(\partial\mathcal M,\mathcal A_{\partial},\mu_{\partial})
$$

为基本对象，其中 $\partial\mathcal M$ 是几何边界，$\mathcal A_{\partial}$ 是其上可观测的代数或散射代数，$\mu_{\partial}$ 是由谱移或能流给出的时间刻度测度；

2. 将散射理论中的时间延迟、模理论中的模块流与引力中的 Brown–York 边界哈密顿量都重述为这个边界结构上的一参数自同构群的不同表示；

3. 在严格限定的条件下，证明这些表示彼此等价，从而将"时间–代数–几何"的三条主线压缩到统一的边界舞台上。

为此，下一节先给出抽象模型与假设，再在"Main Results"中给出四个主定理，随后提供证明骨架与附录中的技术细节，最后展示若干物理与工程应用。

---

## Model & Assumptions

本节构造一个同时容纳散射系统、代数 QFT 与引力边界的抽象模型，并明确各类结果的适用域。

### 2.1 抽象边界三元组

**定义 2.1（边界三元组）**
一个边界三元组是数据

$$
(\partial\mathcal M,\mathcal A_{\partial},\omega_{\partial})
$$

其中：

1. $\partial\mathcal M$ 是一个分段可微的三维流形，可分解为类时、类空与零类片以及它们的关节 $\mathcal C$；

2. $\mathcal A_{\partial}$ 是作用在 Hilbert 空间 $\mathcal H$ 上的 von Neumann 代数，包含边界可观测量（散射通道、边界场、准局域能量算子等）；

3. $\omega_{\partial}$ 是 $\mathcal A_{\partial}$ 上的忠实正常态，其 GNS 三元组记为 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$。

**公设 2.2（边界完备性）**
体域区域 $\mathcal M$ 的物理内容可由某个边界三元组 $(\partial\mathcal M,\mathcal A_{\partial},\omega_{\partial})$ 完全重建（在给定理论的适用范围内），即时间演化与响应算子均由边界一参数自同构群与态的演化确定。

这一公设在不同语境下具有不同的具体实现：散射理论中的波算子与 $S$-矩阵、AdS/CFT 中的边界 CFT 与体域几何、以及 Hamilton–Jacobi 视角下由边界数据重建体域解。([arXiv][2])

### 2.2 散射端的假设

**假设 S.1（迹类扰动与 BK 条件）**
在 Hilbert 空间 $\mathcal H_{\mathrm{scatt}}$ 上，$H_0$ 与 $H=H_0+V$ 为自伴算子，$V$ 属于 trace-class 或更强的理想，使得对几乎所有能量 $\omega$ 散射矩阵 $S(\omega)$ 存在，且 $S(\omega)-\mathbf 1\in\mathfrak S_1$。在这些假设下，Kreĭn 谱移函数 $\xi(\omega)$ 与 Birman–Kreĭn 恒等式

$$
\det S(\omega)=\exp(-2\pi i\xi(\omega))
$$

存在。([kurims.kyoto-u.ac.jp][1])

**假设 S.2（时间延迟矩阵与迹公式）**
Wigner–Smith 时间延迟算子定义为

$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)
$$

且 $Q(\omega)$ 为迹类算子，满足

$$
\operatorname{tr}Q(\omega)=2\pi\xi'(\omega)
$$

在适当意义下成立。([arXiv][5])

在这些条件下，可以定义"边界时间测度"

$$
\mathrm d\mu_{\partial}^{\mathrm{scatt}}(\omega):=\frac{1}{2\pi}\operatorname{tr}Q(\omega),\mathrm d\omega
$$

### 2.3 模理论与 Null–Modular 双覆盖的假设

**假设 M.1（标准模结构）**
$\mathcal A_{\partial}\subset\mathcal B(\mathcal H)$ 为因果区域 $O$ 的局域代数，$\omega$ 为真空态或 KMS 态，使得 $\Omega_\omega$ 在 $\mathcal A_{\partial}$ 上是循环且分离向量，从而存在 Tomita–Takesaki 模算符 $\Delta$ 与一参数模流

$$
\sigma_t^\omega(A)=\Delta^{it}A\Delta^{-it}
$$

**假设 M.2（几何模流）**
对楔区、球形因果钻石或零平面区域 $O$ 中的真空态，模流的几何作用为对应区域的洛伦兹变换或共形 Killing 流，其模哈密顿量 $K_O=-\log\Delta$ 可以写成应力–能量张量的局域积分。例如，对球形区域与零平面区域分别有

$$
K_O=2\pi\int_O\xi^\mu T_{\mu\nu}n^\nu,\mathrm d\Sigma
$$

与

$$
K_O=2\pi\int_{\mathcal N}g(\lambda,x_\perp)T_{\lambda\lambda},\mathrm d\lambda,\mathrm d^{d-2}x
$$

([arXiv][2])

**假设 M.3（Markov 性与容斥）**
对零平面上的区域族，其模哈密顿量满足 Casini–Teste–Torroba 所证明的 Markov 性：对沿零直线的嵌套或重叠区域，条件互信息饱和强次可加，并对应模哈密顿量的容斥恒等式。

在此基础上定义 Null–Modular 双覆盖：对因果钻石 $D$，其边界零超曲面分解为 $E^+\cup E^-$，并在二者上定义带权能流积分表示的模哈密顿量。

### 2.4 引力边界的假设

**假设 G.1（带边界/零边界的作用量）**
在四维 Lorentz 流形 $\mathcal M$ 上，引力作用量取标准形式

$$
S=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g}(R-2\Lambda),\mathrm d^4x + S_{\partial}
$$

其中

$$
S_{\partial}=S_{\mathrm{GHY}}^{\mathrm{tl/sp}}+S_{\mathcal N}^{\mathrm{null}}+S_{\mathcal C}^{\mathrm{corner}}
$$

分别为类时/类空片上的 GHY 边界项、零类片上的改进项以及关节上的角项。([维基百科][3])

**假设 G.2（变分良定性与 Brown–York 应力张量）**
在固定边界诱导度规（及零类边界的适当等价数据）的变分族上，$\delta S$ 仅含体积项，从而给出 Einstein 方程；对给定类时边界三维片 ${}^3B$，作用量关于边界度规的变分定义 Brown–York 边界应力张量

$$
T^{ab}_{\mathrm{BY}}=\frac{2}{\sqrt{-h}}\frac{\delta S}{\delta h_{ab}}
$$

其与边界 Killing 向量 $\xi^a$ 的收缩给出准局域能量与生成边界时间平移的哈密顿量。([arXiv][4])

在这些假设下，我们可以将 Brown–York 哈密顿量视为第三种"边界时间生成元"。

---

## Main Results (Theorems and alignments)

本节陈述本文的四个主结果，并指出它们在三条理论主线之间建立的对应关系。

### 3.1 定理 A：散射端的边界时间刻度同一式

**定理 A（BK–Wigner–Smith–时间刻度同一式）**
在假设 S.1–S.2 条件下，定义

* 总散射相位 $\Phi(\omega)=\arg\det S(\omega)$，半相位 $\varphi(\omega)=\frac{1}{2}\Phi(\omega)$；
* Kreĭn 谱移函数 $\xi(\omega)$，满足 $\det S(\omega)=\exp(-2\pi i\xi(\omega))$；
* Wigner–Smith 时间延迟算子 $Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)$。

则存在几乎处处有限的导数 $\xi'(\omega)$ 与 $\varphi'(\omega)$，使得

$$
\boxed{\ \frac{\varphi'(\omega)}{\pi}=\xi'(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)\ }
$$

几乎处处成立。

从而，测度

$$
\mathrm d\mu_{\partial}^{\mathrm{scatt}}(\omega):=\frac{1}{2\pi}\operatorname{tr}Q(\omega),\mathrm d\omega
$$

等价于谱移测度 $\mathrm d\xi(\omega)$ 与散射相位刻度 $\pi^{-1}\mathrm d\varphi(\omega)$，可视为统一的"边界时间刻度"。

这一定理综合了 Birman–Kreĭn 恒等式、Friedel 和谱移函数之间的关系以及 Eisenbud–Wigner–Smith 时间延迟的迹公式。([kurims.kyoto-u.ac.jp][1])

### 3.2 定理 B：Null–Modular 双覆盖上的模哈密顿量

**定义 3.1（Null–Modular 双覆盖）**
在 $d$ 维 Minkowski 时空中，考虑以点 $p,q$ 为顶点的因果钻石

$$
D(p,q)=J^+(p)\cap J^-(q)
$$

其边界由未来零超曲面 $\mathcal N^+$ 与过去零超曲面 $\mathcal N^-$ 组成。定义 Null–Modular 双覆盖

$$
\widetilde E_D:=E^+\sqcup E^-
$$

其中 $E^\pm$ 分别是 $\mathcal N^\pm$ 去除关节点后的两个光滑叶片，并在每个叶片上引入仿射参数 $\lambda$ 与横向坐标 $x_\perp$。

**定理 B（模哈密顿量的零测度局域化）**
在假设 M.1–M.2 条件下，对 Minkowski 真空态限制在因果钻石 $D$ 的局域代数 $\mathcal A(D)$，其模哈密顿量可以写成

$$
\boxed{\ K_D = 2\pi\sum_{\sigma=\pm}\int_{E^\sigma} g_\sigma(\lambda,x_\perp),T_{\sigma\sigma}(\lambda,x_\perp),\mathrm d\lambda,\mathrm d^{d-2}x\ }
$$

其中

1. $T_{++}=T_{vv}$、$T_{--}=T_{uu}$ 是沿两组零方向的应力–能量张量分量；
2. 权函数 $g_\sigma(\lambda,x_\perp)$ 仅由因果钻石的几何数据决定，并在端点处线性退化。

此外，对位于同一零平面上的重叠因果钻石族 $\{D_j\}$，其模哈密顿量满足容斥恒等式

$$
K_{\cup_jD_j}=\sum_{k\ge1}(-1)^{k-1}\sum_{j_1<\cdots<j_k}K_{D_{j_1}\cap\cdots\cap D_{j_k}}
$$

并且 Minkowski 真空态在这些区域上的限制满足 Markov 性，即对适当嵌套的 $A,B,C$ 有条件互信息

$$
I(A:C\mid B)=0
$$

与上述容斥恒等式等价。([SpringerLink][6])

定理 B 说明：模哈密顿量可以完全在零测度边界上局域化，Null–Modular 双覆盖为模流提供了纯边界化的几何实现。

### 3.3 定理 C：GHY–Brown–York 边界哈密顿量

**定理 C（引力作用的边界可微性与边界时间生成元）**
在假设 G.1–G.2 条件下，考虑带类时/类空/零类片及关节的时空区域 $\mathcal M$，总作用量

$$
S=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g}(R-2\Lambda),\mathrm d^4x+S_{\mathrm{GHY}}^{\mathrm{tl/sp}}+S_{\mathcal N}^{\mathrm{null}}+S_{\mathcal C}^{\mathrm{corner}}
$$

满足：

1. 对所有在边界上保持诱导几何（及零类边界上等效数据）固定的度规变分 $\delta g_{\mu\nu}$，总变分

$$
\delta S=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g},G_{\mu\nu},\delta g^{\mu\nu},\mathrm d^4x
$$

从而给出 Einstein 方程；([维基百科][3])

2. 对给定的类时边界 ${}^3B$ 与其上时间样 Killing 向量 $\xi^a$，Brown–York 边界应力张量

$$
T^{ab}_{\mathrm{BY}}=\frac{2}{\sqrt{-h}}\frac{\delta S}{\delta h_{ab}}
$$

定义的边界哈密顿量

$$
H_{\partial}^{\mathrm{grav}}[\xi]=\int_{B}\sqrt{\sigma},u_a,T^{ab}_{\mathrm{BY}},\xi_b,\mathrm d^2x
$$

生成沿 ${}^3B$ 上时间方向 $\xi^a$ 的准局域时间平移；当 ${}^3B$ 延伸至无穷远时，该哈密顿量收敛到 ADM 或 Bondi 质量。([arXiv][4])

因此，$H_{\partial}^{\mathrm{grav}}$ 可视为第三种边界时间生成元，与 Null–Modular 与散射端的生成元处于同一层级。

### 3.4 定理 D：边界三位一体（时间–代数–几何的统一）

为了陈述统一结果，引入以下抽象化。

**定义 3.2（统一边界时间生成元）**
给定边界三元组 $(\partial\mathcal M,\mathcal A_{\partial},\omega_{\partial})$，称自伴算子 $H_{\partial}$ 为统一边界时间生成元，如果

1. 在散射表示中，$H_{\partial}$ 的谱分解对能量变量 $\omega$ 的测度与 $\mathrm d\mu_{\partial}^{\mathrm{scatt}}(\omega)$ 等价；
2. 在代数表示中，模哈密顿量满足 $K_{\partial}=2\pi\beta^{-1}H_{\partial}$ 对某个正数 $\beta$ 成立，并产生 Tomita–Takesaki 模流；
3. 在几何表示中，Brown–York 哈密顿量可写为 $H_{\partial}^{\mathrm{grav}}[\xi]=\langle H_{\partial},J[\xi]\rangle$，其中 $J[\xi]$ 是与 Killing 向量 $\xi$ 相伴的边界电荷泛函。

**定理 D（边界三位一体原理）**
假设存在以下匹配结构：

1. 散射系统的入射/出射通道可以嵌入到某个 QFT 的边界代数 $\mathcal A_{\partial}$ 的可分子代数中，使得散射相位 $\varphi(\omega)$ 与模哈密顿量在渐近区域的谱相位一致；

2. QFT 的应力–能量张量期望值通过全息字典或半经典 Einstein 方程与 Brown–York 边界应力张量相联系；([arXiv][7])

3. 边界 Killing 时间与散射能量归一化常数满足热时间假设的归一化条件，即模流参数与物理时间相差一常数尺度。

在这些条件下，存在唯一（至全局仿射变换）统一边界时间生成元 $H_{\partial}$，使得

$$
\boxed{\ \text{散射时间延迟} \ \Longleftrightarrow\ \text{模流参数}\ \Longleftrightarrow\ \text{Brown–York 边界时间}\ }
$$

在共同域内等价。

更具体地说，存在正数常数 $c_1,c_2$ 使得

$$
\frac{\varphi'(\omega)}{\pi}=\xi'(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
$$

与

$$
K_D=2\pi\int T_{\sigma\sigma}g_\sigma
$$

$$
H_{\partial}^{\mathrm{grav}}[\xi]=\int \sqrt{\sigma},u_aT_{\mathrm{BY}}^{ab}\xi_b
$$

满足

$$
H_{\partial}=\int \omega,\mathrm d\mu_{\partial}^{\mathrm{scatt}}(\omega)
=c_1K_D+c_2^{-1}H_{\partial}^{\mathrm{grav}}
$$

在同一边界 Hilbert 空间的不同表示下给出同一一参数群 $\mathrm e^{-itH_{\partial}}$ 的三个实现。

定理 D 不声称在任意理论中都可自动构造这样的统一生成元，而是指出在上述匹配条件下，三条主线自然压缩到同一边界时间对象上。

---

## Proofs

本节给出主定理的证明骨架，更精细的技术细节与特殊情况放入附录。

### 4.1 定理 A 的证明骨架

Birman–Kreĭn 恒等式指出，在假设 S.1 条件下，存在谱移函数 $\xi(\omega)$ 使得

$$
\det S(\omega)=\exp(-2\pi i\xi(\omega))
$$

从而

$$
\Phi(\omega)=\arg\det S(\omega)=-2\pi\xi(\omega)
$$

半相位 $\varphi(\omega)=-\pi\xi(\omega)$。对光滑点求导得到

$$
\varphi'(\omega)=-\pi\xi'(\omega)
$$

([kurims.kyoto-u.ac.jp][1])

另一方面，Eisenbud–Wigner–Smith 时间延迟理论表明，在满足适度衰减与正则性条件的势散射系统中，可以将 Wigner–Smith 时间延迟算子定义为

$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)
$$

并证明其迹满足

$$
\operatorname{tr}Q(\omega)=-2,\partial_\omega\arg\det S(\omega)
$$

或等价地

$$
\operatorname{tr}Q(\omega)=2\pi,\xi'(\omega)
$$

([arXiv][5])

将两式合并即可得到

$$
\frac{\varphi'(\omega)}{\pi}=\xi'(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
$$

从而完成定理 A 的证明。严格处理需考虑 $\omega$ 上的例外零测度集合，详见附录 A。

### 4.2 定理 B 的证明骨架

Null–Modular 双覆盖表达式与 Markov 性的关键输入来自两类结果：

1. Casini–Huerta–Myers 与后续工作的球形区域模哈密顿量局域表达，可在共形映射下转化为零锥或零平面的情形：模哈密顿量为应力–能量张量沿零生成元的加权积分。([arXiv][2])

2. Faulkner–Leigh–Parrikar–Wang 对变形半空间的模哈密顿量讨论与 QNEC 的证明，表明零方向上的形变导致模哈密顿量的一阶修正正比于沿零平面的 $T_{--}$ 积分。([SpringerLink][6])

基于这些工作，Casini–Teste–Torroba 证明，对 Minkowski 真空态限制到未来地平线在零平面内的任意区域，其模哈密顿量可写成局域的零平面积分，并进一步证明模哈密顿量满足 Markov 性与容斥公式。

将因果钻石视作零锥截面，在几何上将其未来/过去零边界拆分为 $E^\pm$，并对两片分别引入仿射参数与权函数 $g_\pm$，即可得到定理 B 给出的 Null–Modular 双覆盖形式。容斥恒等式则来自模哈密顿量代数上的加减结构与相应区域的强次可加性饱和条件。

### 4.3 定理 C 的证明骨架

在不含零类片的情形，GHY 边界项必要性的经典推导可见于标准综述与教科书：计算 Einstein–Hilbert 作用量的变分，得到体积项与边界上的法向导数项；添加

$$
S_{\mathrm{GHY}}=\frac{\varepsilon}{8\pi G}\int_{\partial\mathcal M}\sqrt{|h|},K,\mathrm d^3x
$$

后，这一法向导数项被精确抵消，从而对固定诱导度规的变分族，$\delta S$ 仅含体积项。([维基百科][3])

当边界包含零类片与关节时，Lehner 等人利用 Cartan 标架形式给出了统一的边界与角点项表达，证明加入零类边界项

$$
S_{\mathcal N}\sim\int_{\mathcal N}\sqrt{\gamma}(\theta+\kappa),\mathrm d\lambda,\mathrm d^2x
$$

与适当角度项后，对保持零类几何数据的变分族，作用量同样可微。([物理评论链接管理器][8])

Brown–York 准局域能量则由 Hamilton–Jacobi 分析给出：对固定边界三维片 ${}^3B$，其历史上的作用量 $S[q_{ab}]$ 关于三维度规的变分定义表面应力张量，时间方向上的投影给出准局域能量密度，积分得到生成边界时间平移的哈密顿量。([arXiv][4])

这些标准结果直接导致定理 C 所述结论。

### 4.4 定理 D 的证明骨架

定理 D 的关键在于建立三种表示之间的匹配映射：

1. **散射–模理论的匹配**：在许多场景下，散射矩阵可以在代数 QFT 框架下用渐近场代数的自同构实现，每个能量通道对应于边界代数中的一族模式。将散射相位视作模谱移的边界极限，可以把 $\xi(\omega)$ 重述为模谱中的相位函数。([ResearchGate][9])

2. **模理论–引力的匹配**：AdS/CFT 与相对熵–模哈密顿量的全息关系表明，边界相对熵等于体域相对熵，模哈密顿量的引力对偶由极小面或广义熵函数给出；在小形变极限下，这一关系与 Iyer–Wald 正则能量和 Brown–York 准局域能量相一致。([arXiv][10])

3. **热时间归一化**：Bisognano–Wichmann 定理与热时间假设指出，真空态在楔区上的模流与加速时间平移几何同一，二者之间的比例常数由 Unruh 温度或卡西米尔条件确定。

在这些匹配下，可以将散射端的时间测度 $\mathrm d\mu_{\partial}^{\mathrm{scatt}}$、模端的模谱测度与引力端 Brown–York 哈密顿量视为同一边界谱测度的不同坐标表达，从而构造统一生成元 $H_{\partial}$。其唯一性（至仿射变换）来自谱测度的 Radon–Nikodym 唯一性与模流在外自同构群中的唯一类。

---

## Model Apply

本节展示统一边界框架在三个典型物理场景中的适用：黑洞热力学、AdS/CFT 与有限尺度散射网络。

### 5.1 黑洞热力学

对静态黑洞，事件视界是零类边界，表面引力 $\kappa$ 与 Hawking 温度 $T_{\mathrm H}=\kappa/(2\pi)$ 共同刻画其热性质。视界外侧的 QFT 真空态在楔区的模流等价于绕视界的欧几里得时间平移，其周期即为 $\beta_{\mathrm H}=1/T_{\mathrm H}$。([arXiv][2])

在统一边界框架中：

1. 散射端：考虑黑洞外的定能量散射，群延迟 $\operatorname{tr}Q(\omega)$ 的能量依赖编码了视界附近有效势垒与准正则模结构；

2. Null–Modular 端：视界本身可视作 Null–Modular 双覆盖的一部分，其模哈密顿量在零生成元上局域化，与 $T_{vv}$ 的积分成正比；

3. 引力端：对包围黑洞的边界二球，Brown–York 准局域能量在无穷远极限趋向 ADM 质量，而在靠近视界处则与 Bekenstein–Hawking 熵与温度的乘积形成 Legendre 结构。([arXiv][4])

统一生成元 $H_{\partial}$ 在三个端点给出相容的时间平移与热量–几何关系，从而将黑洞热力学重述为纯边界现象。

### 5.2 AdS/CFT 与时间的全息重构

在 AdS/CFT 对偶中，边界 CFT 的时间演化由哈密顿量 $H_{\mathrm CFT}$ 生成，其模哈密顿量与广义熵极值曲面共同决定体域的几何响应。Casini–Huerta–Myers 与 JLMS 类型的结果表明，球形区域的模哈密顿量引力对偶是某类顶帽黑洞的 Killing 生成元，其谱结构与 Brown–York 能量、Gibbons–Hawking–York 边界作用密切相关。([arXiv][2])

统一边界框架在此提供自然语言：

* 散射端：体域中高能过程的散射延迟对应边界 CFT 相关函数的相位结构；
* Null–Modular 端：边界 CFT 球形区域的模流通过 JLMS 对应体域的 Killing 流与极小面；
* 引力端：这些 Killing 流由 Brown–York 边界哈密顿量生成，其作用可由 GHY 项的 Hamilton–Jacobi 变分读出。

因此，"时间的全息重构"可理解为统一生成元 $H_{\partial}$ 在 CFT 与 AdS 两侧的两种表示。

### 5.3 有限尺度散射网络与实验可检性

在电磁散射与波动网络中，Wigner–Smith 时间延迟矩阵 $Q(\omega)$ 已被用于分析复杂媒质中的群延迟、模式聚焦与拓扑相位。([arXiv][5])

统一框架给出的实验路线是：

1. 在微波或光学网络中测量 $S(\omega)$，通过数值微分与谱分解获得 $Q(\omega)$ 与其迹，构造边界时间测度 $\mathrm d\mu_{\partial}^{\mathrm{scatt}}$；

2. 将网络视作离散化的"零平面"，通过对输入/输出端口的划分构造类钻石区域的有效模哈密顿量（可由二阶统计量或主模态分解近似）；

3. 利用有效介质或弯曲波导构造几何/拓扑类似的"引力边界"，通过能量存储与 Q 因子的变化定义类 Brown–York 准局域能量。

若三种读出在适当归一化下给出一致的时间刻度，则可视为统一边界时间生成元 $H_{\partial}$ 的实验指纹。

---

## Engineering Proposals

为将统一边界框架落地为可检的工程方案，这一节提出三类可在中尺度平台上实施的实验路线。

### 6.1 多端口散射网络中的边界时间测度

在多端口微波散射网络中，已可高精度测量随频率变化的 $S(\omega)$，并构造 Wigner–Smith 时间延迟矩阵 $Q(\omega)$。([arXiv][5])

工程步骤如下：

1. 设计若干具有不同"内域"结构的网络，但保持相同的端口几何与外部边界；
2. 对每个网络测量 $\operatorname{tr}Q(\omega)$，并通过频率积分获得"有效驻留时间"刻度；
3. 比较不同结构对 $\mathrm d\mu_{\partial}^{\mathrm{scatt}}$ 的影响，检验其是否只依赖于边界条件与谱移，而对内部细节具有鲁棒性。

这直接检验散射端的刻度同一式与边界时间的"外边界主导性"。

### 6.2 零平面模拟与 Null–Modular Markov 性

在量子比特链或冷原子 1+1 维系统中，可以构造近似的"零平面切割"：选择一族时空区域，其未来边界落在近似零线上，并测量对应子系统的模哈密顿量近似或条件互信息。

工程化提案：

1. 在可控多体系统中，对空间链的多个区段实施时间依赖的测量或局域耦合，实现对模哈密顿量的有效"模拟"；
2. 构造重叠区段的三元组 $(A,B,C)$，测量条件互信息 $I(A:C\mid B)$；
3. 检验在"零平面近似"极限下 $I(A:C\mid B)$ 的缩放是否接近 Markov 饱和，从而间接验证 Null–Modular 容斥结构。

### 6.3 准局域能量与几何边界的模拟

在类广义相对论的模拟平台（例如超流体、声学黑洞或折射率工程的光学媒质）中，可以定义有效度规体与边界界面。利用能量守恒与反射/透射系数，可以构造类 Brown–York 准局域能量的读出。([维基百科][3])

将这些读出与散射端的 $\mathrm d\mu_{\partial}^{\mathrm{scatt}}$ 以及 Null–Modular 结构相比较，可检验"几何边界"与"谱/模边界"的统一刻度是否在实验上可辨。

---

## Discussion (risks, boundaries, past work)

### 7.1 适用域与潜在风险

统一边界框架虽然在三个成熟理论的交集区域内是严谨的，但在以下几个方面存在清晰的适用边界：

1. **散射端的限制**：定理 A 在很大程度上依赖于迹类扰动与良好高能行为；对长程势、共振累积或强耦合非微扰体系，谱移函数与时间延迟迹公式的适用性需要重新审视。([kurims.kyoto-u.ac.jp][1])

2. **模理论端的限制**：Null–Modular 局域化与 Markov 性目前主要在共形场论与自由场模型中得到严格证明，对普遍的相互作用 QFT，特别是非局域或非洛伦兹不变理论，需要进一步推广。

3. **引力端的限制**：GHY 与 Brown–York 形式在经典 GR 及部分修正引力中已得到系统分析，但在全量子引力或泊松–路径积分层面的边界项定义仍然存在歧义，特别是在拓扑变化或奇点附近。([arXiv][11])

跨越这些边界时，统一时间生成元 $H_{\partial}$ 的存在性与唯一性需要额外假设或新的数学工具。

### 7.2 与既有工作的关系

本文所建框架可以视为若干成熟方向的"边界化重述"：

* 在散射理论侧，Birman–Kreĭn、谱移函数与 Wigner–Smith 时间延迟的关系长期用于谱理论与导电性质的研究；([kurims.kyoto-u.ac.jp][1])
* 在模理论侧，球形区域与零平面的模哈密顿量、ANEC/QNEC 与 Markov 性已成为相对论 QFT 与量子信息结合的核心主题；([arXiv][2])
* 在引力侧，GHY 边界项、Brown–York 准局域能量与全息熵/相对熵关系构成现代引力与全息的基础。([维基百科][3])

本文的贡献在于：把时间刻度统一视作边界谱测度，把模流与 Brown–York 哈密顿量视作同一生成元的不同表象，从而在概念上构造一个"边界三位一体"范式。

---

## Conclusion

本文提出并构建了一个以边界为唯一舞台的统一框架，将散射时间延迟、Null–Modular 模流与 GHY–Brown–York 引力边界项视为同一边界时间生成元 $H_{\partial}$ 的三种表示。

主要结论可以概括为：

1. 在迹类扰动的散射理论中，散射半相位导数、Kreĭn 谱移密度与 Wigner–Smith 延迟矩阵迹构成统一的边界时间测度；
2. 在代数量子场论中，因果钻石与零平面上的模哈密顿量可以完全局域化在 Null–Modular 双覆盖上，且对重叠钻石族满足 Markov 性与容斥律；
3. 在广义相对论中，包含 GHY、零边界与角点项的作用量对固定边界几何的变分良定，Brown–York 边界哈密顿量生成的时间平移构成几何意义上的边界时间；
4. 在存在合适匹配映射的情形下，可以构造统一的 $H_{\partial}$，使得散射时间延迟、模流参数与 Brown–York 边界时间在同一谱测度上等价，从而把"时间–代数–几何"同时重述为边界数据的不同侧面。

这一框架为诸多开放问题提供了新的角度，包括黑洞信息、宇宙学视界的时间刻度、以及可在中尺度平台上实现的边界物理实验。

---

## Acknowledgements, Code Availability

本工作属于理论构造与综述整合，未使用数值代码或数据分析程序，因此不存在可公开的代码。

---

## References

[1] H. Isozaki, "Trace Formulas for Schrödinger Operators," Kyoto University Preprint 2011. ([kurims.kyoto-u.ac.jp][1])

[2] M. Kohmoto, "The Spectral Shift Function and the Friedel Sum Rule," Ann. Henri Poincaré 14, 2013.

[3] S. Richard, "Time delay for an abstract quantum scattering process," arXiv:1103.3901.

[4] U. R. Patel, E. Michielssen, "Wigner–Smith Time Delay Matrix for Electromagnetics," arXiv:2005.03211. ([arXiv][5])

[5] H. Casini, M. Huerta, R. C. Myers, "Towards a derivation of holographic entanglement entropy," JHEP 1105 (2011) 036, arXiv:1102.0440. ([arXiv][2])

[6] T. Faulkner, R. G. Leigh, O. Parrikar, H. Wang, "Modular Hamiltonians for Deformed Half-Spaces and the Averaged Null Energy Condition," JHEP 09 (2016) 038, arXiv:1605.08072. ([SpringerLink][6])

[7] H. Casini, E. Teste, G. Torroba, "Modular Hamiltonians on the null plane and the Markov property of the vacuum state," J. Phys. A 50 (2017) 364001, arXiv:1703.10656.

[8] H. Casini, E. Teste, G. Torroba, "Markov property of the CFT vacuum and the a-theorem," Phys. Rev. Lett. 118, 261602 (2017), arXiv:1704.01870.

[9] S. J. Summers, "Tomita–Takesaki Modular Theory," math-ph/0511034.

[10] J. Mund, "The Bisognano–Wichmann Theorem for Massive Theories," Ann. Henri Poincaré 2 (2001) 907, hep-th/0101227.

[11] L. Lehner, R. C. Myers, E. Poisson, R. D. Sorkin, "Gravitational action with null boundaries," Phys. Rev. D 94, 084046 (2016), arXiv:1609.00207. ([arXiv][12])

[12] E. Dyer, K. Hinterbichler, "Boundary Terms, Variational Principles and Higher Derivative Modified Gravity," Phys. Rev. D 79, 024028 (2009), arXiv:0809.4033. ([物理评论链接管理器][13])

[13] J. D. Brown, J. W. York, "Quasilocal Energy and Conserved Charges Derived from the Gravitational Action," Phys. Rev. D 47, 1407 (1993), gr-qc/9209012. ([arXiv][4])

[14] G. Sárosi, et al., "Relative Entropy Equals Bulk Relative Entropy," JHEP 01 (2018) 012, arXiv:1706.10205. ([德国国家图书馆][14])

[15] D. D. Blanco, H. Casini, L. Y. Hung, R. C. Myers, 等关于模哈密顿量、相对熵与负能量束缚的一系列工作，见综述与引用条目。([arXiv][10])

[16] H. Casini, E. Teste, G. Torroba, "Mutual information superadditivity and unitarity bounds," JHEP 09 (2021) 046.

[17] H. Zhang, "The Birman–Krein Formula and Scattering Phase on Product Space," arXiv:2509.06372. ([arXiv][15])

[18] 其他关于谱移算子、模算子在零平面上的形式化、以及相对熵在有限域上界定的工作，见例如 V. Morinelli 等与 M. Schröfl 等的近期文献。([Department of Mathematics][16])

---

## Appendix A：散射谱移、相位与时间延迟的统一

本附录给出定理 A 的更详细证明与技术条件。

### A.1 Birman–Kreĭn 谱移与散射行列式

在假设 S.1 条件下，谱移函数 $\xi(\lambda)$ 可以通过 trace-class 扰动的谱分解定义：对任意紧支连续函数 $f$，有

$$
\operatorname{tr}(f(H)-f(H_0))=\int f'(\lambda),\xi(\lambda),\mathrm d\lambda
$$

以 $f(\lambda)=\chi_{(-\infty,E]}(\lambda)$ 近似可得到低能谱统计与 $\xi(E)$ 的关系。Birman–Kreĭn 恒等式进一步给出

$$
\det S(E)=\exp(-2\pi i\xi(E))
$$

其中右侧行列式为修正行列式，适用于 $S(E)-\mathbf 1\in\mathfrak S_1$ 的情形。([kurims.kyoto-u.ac.jp][1])

### A.2 Wigner–Smith 时间延迟迹公式

对能量依赖散射矩阵，定义

$$
Q(E)=-iS(E)^\dagger\partial_E S(E)
$$

可以证明 $Q(E)$ 自伴且非负，对短程势有

$$
\operatorname{tr}Q(E)=2\pi,\xi'(E)
$$

其证明可通过谱分解与散射相移展开完成。对多通道情况，采用偏波展开与通道求和，利用 $\det S(E)=\exp(i\sum_\ell (2\ell+1)\delta_\ell(E))$ 得到

$$
\partial_E\arg\det S(E)=\sum_\ell(2\ell+1)\partial_E\delta_\ell(E)
$$

与 $\operatorname{tr}Q(E)$ 的偏波展开项逐项匹配。([OSTI][17])

### A.3 半相位与统一刻度

定义半相位 $\varphi(E)=\tfrac12\arg\det S(E)$，则

$$
\varphi'(E)=\frac12\partial_E\arg\det S(E)=\pi,\xi'(E)=\frac{1}{2}\operatorname{tr}Q(E)/(2\pi)
$$

整理即得主文中的刻度同一式。

---

## Appendix B：零平面模哈密顿量与 Markov 性

### B.1 零平面上的模哈密顿量局域表达

对 Minkowski 真空态限制到未来地平线落在零平面上的区域，其模哈密顿量可以写成

$$
K=2\pi\int_{\mathcal N}g(\lambda,x_\perp),T_{\lambda\lambda}(\lambda,x_\perp),\mathrm d\lambda,\mathrm d^{d-2}x
$$

Casini–Teste–Torroba 给出两种证明：一种基于共形映射与球形区域模哈密顿量的已知形式，一种基于代数 QFT 的抽象 Tomita–Takesaki 结构。([arXiv][2])

### B.2 Markov 性与容斥公式

对零平面上由若干区域 $R_i$ 生成的 $\sigma$-代数，其模哈密顿量满足

$$
K_{\cup_iR_i}=\sum_{k\ge1}(-1)^{k-1}\sum_{i_1<\cdots<i_k}K_{R_{i_1}\cap\cdots\cap R_{i_k}}
$$

这一容斥结构等价于真空态在这些区域上的条件互信息满足

$$
I(A:C\mid B)=0
$$

的 Markov 性。Casini 等人证明这一性质导致强次可加性饱和与相对熵的强超加性，并与 CFT 中的单调流定理（$a$-定理）紧密相关。

---

## Appendix C：GHY 边界项、零类边界与 Brown–York 能量

### C.1 经典 GHY 变分计算

对 Einstein–Hilbert 作用量

$$
S_{\mathrm{EH}}=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g}R
$$

其变分包含体积项与边界上的 $\delta\Gamma$ 项，通过 Palatini 恒等式可写为

$$
\delta S_{\mathrm{EH}}=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g},G_{\mu\nu},\delta g^{\mu\nu}+\frac{1}{16\pi G}\int_{\partial\mathcal M}\sqrt{|h|},n_\mu v^\mu(\delta g,\partial\delta g)
$$

其中第二项无法仅通过固定 $g_{\mu\nu}$ 消去。添加

$$
S_{\mathrm{GHY}}=\frac{\varepsilon}{8\pi G}\int_{\partial\mathcal M}\sqrt{|h|}K
$$

后，其变分恰好抵消边界上的导数项，使得对固定诱导度规的变分族，作用量可微。([维基百科][3])

### C.2 零类边界与角点项

Lehner 等人给出包含零类边界的统一表达：对零超曲面 $\mathcal N$，其边界项

$$
S_{\mathcal N}=\frac{1}{8\pi G}\int_{\mathcal N}\sqrt{\gamma}(\theta+\kappa),\mathrm d\lambda,\mathrm d^2x
$$

涉及膨胀量 $\theta$ 与表面引力 $\kappa$；对不同类型边界相交的关节 $\mathcal C$，角点项

$$
S_{\mathcal C}=\frac{1}{8\pi G}\int_{\mathcal C}\sqrt{\sigma},\eta,\mathrm d^2x
$$

补偿法向方向的突变，从而保证总作用对保持适当边界数据固定的变分族可微。([物理评论链接管理器][8])

### C.3 Brown–York 应力张量与边界时间

对类时边界三维片 ${}^3B$，对作用量的变分定义

$$
T^{ab}_{\mathrm{BY}}=\frac{2}{\sqrt{-h}}\frac{\delta S}{\delta h_{ab}}=\frac{1}{8\pi G}(K^{ab}-Kh^{ab})+\cdots
$$

其中"$\cdots$" 表示可能的参考背景项。选择边界上的单位时间样向量 $u^a$ 与二维截面 $B$ 的法向量 $n^a$，准局域能量密度

$$
\varepsilon=T^{ab}_{\mathrm{BY}}u_an_b
$$

积分得到

$$
E_{\mathrm{BY}}=\int_B\sqrt{\sigma},\varepsilon,\mathrm d^2x
$$

它在 Hamilton–Jacobi 框架中等同于生成沿 $u^a$ 的边界时间平移的哈密顿量。([arXiv][4])

这说明引力边界上的时间平移可以完全用边界几何数据与 GHY/角点项重述，从而成为统一边界时间生成元 $H_{\partial}$ 的几何表示。

[1]: https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1760-03.pdf "TRACE FORMULAS FOR SCHRODINGER OPERATORS"
[2]: https://arxiv.org/pdf/1102.0440 "Towards a derivation of holographic entanglement entropy"
[3]: https://en.wikipedia.org/wiki/Gibbons%E2%80%93Hawking%E2%80%93York_boundary_term "Gibbons–Hawking–York boundary term"
[4]: https://arxiv.org/abs/gr-qc/9209012 "Quasilocal Energy and Conserved Charges Derived from the Gravitational Action"
[5]: https://arxiv.org/pdf/2005.03211 "Wigner-Smith Time Delay Matrix for Electromagnetics"
[6]: https://link.springer.com/article/10.1007/JHEP09%282016%29038 "Modular Hamiltonians for deformed half-spaces and the ..."
[7]: https://arxiv.org/abs/1102.0440 "Towards a derivation of holographic entanglement entropy"
[8]: https://link.aps.org/doi/10.1103/PhysRevD.94.084046 "Gravitational action with null boundaries | Phys. Rev. D"
[9]: https://www.researchgate.net/publication/247934289_The_Xi_Operator_and_its_Relation_to_Krein%27s_Spectral_Shift_Function "The Xi Operator and its Relation to Krein's Spectral Shift ..."
[10]: https://arxiv.org/abs/1305.3182 "[1305.3182] Relative Entropy and Holography"
[11]: https://arxiv.org/pdf/0809.4033 "Boundary Terms, Variational Principles and Higher ..."
[12]: https://arxiv.org/abs/1609.00207 "[1609.00207] Gravitational action with null boundaries"
[13]: https://link.aps.org/doi/10.1103/PhysRevD.79.024028 "Boundary terms, variational principles, and higher derivative ..."
[14]: https://d-nb.info/1153657546/34 "JHEP01(2018)012"
[15]: https://arxiv.org/html/2509.06372v1 "the Birman Krein Formula and scattering phase on product ..."
[16]: https://web.ma.utexas.edu/mp_arc/e/99-30.latex "The Spectral Shift Operator"
[17]: https://www.osti.gov/servlets/purl/1903614 "Eisenbud–Wigner–Smith time delay in atom–laser ..."
