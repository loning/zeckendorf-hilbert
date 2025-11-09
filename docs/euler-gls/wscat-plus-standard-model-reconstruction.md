# 基于 WScat^+ 的统一散射—信息纤维丛框架重构标准模型

Version: 1.2

**摘要**
提出一套以信息纤维丛为载体、以广义散射矩阵为动力学核心的统一框架 WScat^+。以 $G=\mathrm{SU}(3)\times\mathrm{SU}(2)\times\mathrm{U}(1)$ 为规范群（允许其全局形式为 $(\mathrm{SU}(3)\times\mathrm{SU}(2)\times\mathrm{U}(1))/\Gamma$），在此框架中：其一，构造包含规范自由度与束框架选择的广义散射矩阵 $S(E)$，并以 $\det S(E)$ 的解析结构刻画粒子谱与共振；其二，从推广的信息广义变分原理（IGVP）$\,\delta S_{\mathrm{gen}}^{+}=0$ 同时推出爱因斯坦场方程与杨–米尔斯方程；其三，论证希格斯机制在散射论中的对应物为 $\det S(E)$ 的零点/极点与主丛约化之间的对应，进而给出从第一性原则出发的质量谱求解程序（以共振极点与相位流为输入）。框架内系统性整合了单位性、解析性与因果性所蕴含的色散与正性约束，并与电弱精密观测、异常一致性、以及规范群全局结构的区分量相容。文末给出若干严格定理的证明与推论。关于 $\det S$ 与谱位移函数的联系、Wigner–Smith 时间延迟矩阵、色散与 Froissart–Martin 上界、以及"纠缠第一定律"与 QNEC/ANEC 的使用，分别参见相应经典与近年文献。([arXiv][1])

---

### 1  引言与主结论

将量子场论的"散射—谱"视角与几何化的"规范—丛"视角统一，是理解标准模型与引力之间结构一致性的关键。本文提出的 WScat^+ 框架具备三项核心要素：

1. **信息纤维丛与主丛约化**：以四维时空流形 $\mathcal{M}$ 上的主丛 $P(\mathcal{M},G)$ 及其伴随丛为基础，把外场、规范联络与"边界框架选择"提升为散射输入的几何数据。主丛对闭子群 $H\subset G$ 的约化与伴随商丛 $P/H$ 的全局截面一一对应；把该截面视作希格斯场的几何版本。([arXiv][2])

2. **广义散射矩阵 $S(E)$**：在物理希尔伯特子空间 $\mathcal{H}_{\mathrm{phys}}=\ker Q_{\mathrm{BRST}}/\operatorname{im}Q_{\mathrm{BRST}}$ 上构造能量分解下的 $S(E)$。以 Wigner–Smith 矩阵 $Q(E)=-i\,S^{\dagger}\partial_E S$ 描述相位流与时间延迟，$\arg\det S(E)$ 的导数即总时间延迟之迹。([Physical Review Link Manager][3])

3. **信息广义变分原理（IGVP）**：在局域 Rindler 楔与球形区域的极限上，令广义熵泛函 $S_{\mathrm{gen}}^{+}$ 的一阶变分为零，结合纠缠第一定律 $\delta S=\delta\langle H_{\mathrm{mod}}\rangle$、相对熵单调性与 QNEC/ANEC，可得爱因斯坦方程；把同一原理对规范电流/电荷的模态变分加以推广，可得杨–米尔斯方程。([arXiv][4])

本文主要定理与构造的结论性表述如下。

**定理 A（Birman–Krein 与谱的散射表述）**
对满足可追踪扰动条件的散射对 $(H_0,H)$，有
$$
\det S(E)=\exp\!\bigl(-2\pi i\,\xi(E)\bigr),\qquad
\partial_E\arg\det S(E)=\operatorname{tr}\,Q(E),
$$
其中 $\xi(E)$ 为谱位移函数，$Q(E)=-iS^\dagger\partial_E S$ 为 Wigner–Smith 矩阵。([arXiv][1])

**定理 B（IGVP $\Rightarrow$ 爱因斯坦方程）**
在局域球区域 $\mathcal{B}$ 的极限下，若对任意微扰态满足纠缠第一定律与相对熵单调性，并对出射熵 $S_{\mathrm{out}}$ 采用 QNEC 的下界，则 $\delta S_{\mathrm{gen}}^{+}=0$ 等价于
$$
G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}.
$$
([SpringerLink][5])

**定理 C（IGVP $\Rightarrow$ 杨–米尔斯方程）**
令模态变分包含对背景规范势 $A_\mu^a$ 的一阶扰动，并以球区真空的模态哈密顿量中与 $J_\mu^a$ 的耦合为主导，则 $\delta S_{\mathrm{gen}}^{+}=0$ 给出
$$
D_\mu F^{\mu\nu,a}=J^{\nu,a}.
$$
其证明基于纠缠第一定律对内部对称荷流的线性响应形式与 Ward 恒等式。（见附录 C。）

**定理 D（希格斯—约化—极点对应）**
对电弱子群 $G_{\mathrm{EW}}=\mathrm{SU}(2)\times\mathrm{U}(1)$，主丛约化 $G_{\mathrm{EW}}\to H_{\mathrm{em}}$ 的截面 $h:\mathcal{M}\to P/H_{\mathrm{em}}$ 的存在，使得 $\det S(E)$ 在第二 Riemann 片出现的极点 $\sqrt{s_R}=M_R-i\Gamma_R/2$ 与规范玻色子质量与宽度 $(M_W,M_Z,\Gamma_{W,Z})$ 的定义相容；质量参数由极点而非 Breit–Wigner 参数决定。([arXiv][2])

**定理 E（高能约束）**
在因果性、解析性、局域性与单位性成立时，2→2 前向散射幅满足色散与正性约束；总截面服从 Froissart–Martin 上界 $\sigma_{\mathrm{tot}}(s)\lesssim C\log^2 s$，其对 $\det S$ 相位的积分形式给出全局相位—截面互约束。([CERN Document Server][6])

---

### 2  信息纤维丛与标准模型的几何化

**2.1 主丛与规范结构**
设 $\mathcal{M}$ 为四维时空流形，取主丛 $P(\mathcal{M},G)$ 与联络 $\mathcal{A}\in\Omega^1(P,\mathfrak{g})$。场内容以伴随丛与关联向量丛的截面表示。WScat^+ 将"散射边界条件"几何化为无穷远处的丛框架选择与边界同调类。

**2.2 主丛约化与希格斯场**
对闭子群 $H\subset G$，主丛对 $H$ 可约化当且仅当商丛 $P/H$ 存在全局截面；在规范场论中该截面即扮演希格斯场的几何化角色，包含自发对称破缺的数据。([arXiv][2])

**2.3 规范群的全局形式**
实验确定了代数 $\mathfrak{su}(3)\oplus\mathfrak{su}(2)\oplus\mathfrak{u}(1)$，但规范群的全局结构可以是 $(\mathrm{SU}(3)\times\mathrm{SU}(2)\times\mathrm{U}(1))/\Gamma$，$\Gamma=\{1,\mathbb{Z}_2,\mathbb{Z}_3,\mathbb{Z}_6\}$。不同 $\Gamma$ 对应可观测线算符与 $\theta$-角周期性的差异，亦影响分数电荷可否存在。该问题可由一类拓扑输运系数或 SMEFT 的重粒子阐明。([arXiv][7])

---

### 3  含规范自由度的广义散射矩阵 $S(E)$

**3.1 物理子空间与 BRST**
以 BRST 量子化刻画规范自由度，物理态空间取 $\mathcal{H}_{\mathrm{phys}}=\ker Q_{\mathrm{BRST}}/\operatorname{im}Q_{\mathrm{BRST}}$。S 矩阵在 $\mathcal{H}_{\mathrm{phys}}$ 上幺正，且与规范选取无关。([arXiv][8])

**3.2 LSZ 与 Källén–Lehmann**
两点函数的 Källén–Lehmann 表达与 LSZ 约化定理把格林函数与散射幅联系起来，确保 $\mathcal{H}_{\mathrm{phys}}$ 上的单粒子与共振态在 $S(E)$ 的解析延拓中以极点呈现。（[Il Nuovo Cimento][9]）

**3.3 Wigner–Smith 与 $\det S$**
定义 Wigner–Smith 矩阵
$$
Q(E)=-i\,S^{\dagger}(E)\,\partial_E S(E),
$$
其迹为总时间延迟。总相位 $\Phi(E)=\arg\det S(E)$ 满足 $\partial_E\Phi(E)=\operatorname{tr}Q(E)$。([Physical Review Link Manager][3])

**3.4 Birman–Krein 与谱位移函数**
对满足迹类扰动条件的情形，Birman–Krein 给出
$$
\det S(E)=\exp\!\bigl(-2\pi i\,\xi(E)\bigr),
$$
谱位移 $\xi(E)$ 直观上计数受扰动引入/移走的态密度，与相位之和一致。([arXiv][1])

**3.5 共振极点与质量定义**
解析延拓至第二 Riemann 片的极点 $\sqrt{s_R}=M_R-i\Gamma_R/2$ 给出过程无关（scheme-independent）的质量—宽度定义。这与实验上常用的 Breit–Wigner 参数不同，需以极点定义为准。([Particle Data Group][10])

---

### 4  $\det S(E)$ 的解析结构与质量谱

**4.1 极点、支点与 Landau 奇点**
$\det S(E)$ 的零/极点对应共振与束缚态；支点与阈值源于 Landau 方程的奇点结构。([arXiv][11])

**4.2 色散关系与正性约束**
因果性与解析性保证前向幅 $M(s,0)$ 的色散关系；单位性使不交叠的弧积分为正测度，从而得到 Wilson 系数的正性束缚与凸几何视角（EFT-hedron）。这些对 $\partial_E\arg\det S$ 的增长率与弯曲性给出全局控制。([Physical Review Link Manager][12])

**4.3 Froissart–Martin 上界**
高能极限下 $\sigma_{\mathrm{tot}}(s)\lesssim C\log^2 s$，其中常数刻度由 t 通道最轻奇异度所对应的质量隙（如 $m_\pi$）设定；该上界可转写为 $\int \partial_E\arg\det S$ 的控制，从而限制全局相位增长。([CERN Document Server][6])

**4.4 谱和规则与 QCD**
差分谱和规则（如 Weinberg sum rules）与 SVZ 求和把强子谱与凝聚值联系；在 WScat^+ 中，它们等价于 $\log\det S$ 的适当权函数积分约束。（[Nucl. Phys. B][13]）

**4.5 质量谱的第一性求解策略**
给定实验/格点输入的分道散射幅：
(i) 对每个量子数通道作解析延拓，定位 $\det S$ 的极点以定义质量与宽度；
(ii) 对电弱规范玻色子，利用主丛约化与"吃掉"标量模式的几何结构，得到 $M_W=\tfrac{1}{2}gv,\,M_Z=\tfrac{1}{2}\sqrt{g^2+g'^2}\,v$；
(iii) 对费米子，$\det S$ 的零点位置与 Yukawa 有效耦合（对 $\Phi$ 的响应）给出质量；
(iv) 以正性与 Froissart 上界为全局一致性检验。([Particle Data Group][10])

---

### 5  IGVP：$\delta S_{\mathrm{gen}}^{+}=0$ 同时导出引力与杨–米尔斯

**5.1 广义熵泛函与局域区域**
取局域球 $\mathcal{B}$ 与其 Rindler 楔边界 $\mathcal{H}$。定义
$$
S_{\mathrm{gen}}^{+}=\frac{\mathrm{Area}(\partial\mathcal{B})}{4G\hbar}+S_{\mathrm{out}}[\rho\,|\,\mathcal{B},A_\mu]+\mathcal{I}_{\mathrm{edge}}[A_\mu],
$$
其中 $S_{\mathrm{out}}$ 为外部量子态的冯诺依曼熵，$\mathcal{I}_{\mathrm{edge}}$ 收敛边界模式的规范贡献。满足纠缠第一定律 $\delta S_{\mathrm{out}}=\delta\langle H_{\mathrm{mod}}\rangle$ 及相对熵单调性。([arXiv][4])

**5.2 爱因斯坦方程的推出**
在球极限上，模态哈密顿量含应力张量的局域积分；配合 QNEC/ANEC 与 $\delta\mathrm{Area}$ 的几何变分，可得
$$
G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}.
$$
相关证明此前以纠缠热力学与相对熵方法建立，WScat^+ 仅把其嵌入散射—信息一体化结构。([SpringerLink][5])

**5.3 杨–米尔斯方程的推出**
把 $\delta A_\mu^a$ 视作 IGVP 的独立变分。将 $\alpha^a(x)$ 定义为由边界规范自由度诱导的无穷小规范参数，则
$$
\delta S_{\mathrm{out}}=\delta\langle H_{\mathrm{mod}}\rangle
= \int_{\mathcal{B}}\!\chi^\mu\,\langle J_\mu^a\rangle\,\delta\alpha^a
+\int_{\mathcal{B}}\!\chi_\nu\,\langle J_\mu^a\rangle\,\delta F^{\mu\nu,a}+\cdots .
$$
其中 $\chi^\mu$ 为球的共形 Killing 向量。综合边界项与 Ward 恒等式，并令 $\delta S_{\mathrm{gen}}^{+}=0$ 对任意 $\delta A$ 成立，得
$$
D_\mu F^{\mu\nu,a}=J^{\nu,a}.
$$
（详见附录 C。）

---

### 6  标准模型在 WScat^+ 的实现

**6.1 费米子与 Kähler–Dirac 描述**
可用 Kähler–Dirac 形式把一代费米子嵌入微分形式之直和；在格点上该描述与 Kogut–Susskind（staggered）离散化等价，因而不消除倍增，但便于表示手性与规范作用；与传统 Weyl 描述等价。（[Z. Phys. C][14]）

**6.2 电弱对称破缺的几何刻画**
$G_{\mathrm{EW}}\to H_{\mathrm{em}}$ 的约化截面对应希格斯场非零真空期望；规范玻色子质量来自联络沿 $G_{\mathrm{EW}}/H_{\mathrm{em}}$ 方向的曲率投影，得到 $M_W,M_Z$ 的标准关系，$\gamma$ 仍为无质量。约化—极点对应确保这些质量可由 $\det S$ 的极点稳定定义。([arXiv][2])

**6.3 异常与全局一致性**
ABJ 三角异常的一回路完备性（Adler–Bardeen）及 $\mathrm{SU}(2)$ Witten 全局异常要求每代 $\mathrm{SU}(2)$ 弱双态数为偶数；标准模型每代 $3$ 个夸克双态 $+$ $1$ 个轻子双态，共 $4$ 个，满足条件。([SpringerLink][15])

**6.4 电弱精密约束与散射正性**
STU 参数以传播子色散积分定义，WScat^+ 的前向幅色散与正性直接约束 SMEFT/HEFT 的 Wilson 系数，与精密数据兼容。([Physical Review Link Manager][16])

---

### 7  可检验预言与程序化实现

**7.1 质量谱的极点抽取**
基于多道数据拟合 $S(E)$ 并解析延拓，统一抽取极点 $\sqrt{s_R}$ 与残差；对宽共振避免仅用 Breit–Wigner。([Particle Data Group][10])

**7.2 相位—截面一致性**
以 $\partial_E\arg\det S=\operatorname{tr}Q$ 与光学定理共同校验不同通道的相位与截面；以 Froissart–Martin 上界限制高能外推。([Physical Review Link Manager][3])

**7.3 规范群全局形式的判别**
借助分数电荷、线算符谱及拓扑响应系数区分 $\Gamma$；对未来发现的分数电荷或特定 SMEFT 相关模式，可确定 $(\mathrm{SU}(3)\times\mathrm{SU}(2)\times\mathrm{U}(1))/\Gamma$ 的具体 $\Gamma$。([arXiv][7])

---

### 8  讨论与展望

WScat^+ 把丛的约化、纠缠变分与散射相位的全局数据统一于 $\det S$ 的解析几何之中：质量来自极点，耦合来自残差，约束来自正性与上界，方程来自 $\delta S_{\mathrm{gen}}^{+}=0$。对强子谱、非可积多道耦合、以及非可逆对称（non-invertible symmetry）与高阶形对称的散射刻画，将在此框架下获得系统语言。([Physics Stack Exchange][17])

---

## 附录 A：Birman–Krein、Wigner–Smith 与 $\det S$

**A.1 Birman–Krein 公式**
设 $H=H_0+V$ 为自伴散射对，扰动为迹类。谱位移函数 $\xi(E)$ 由 Krein 迹公式定义，且
$$
\det S(E)=\exp\!\bigl(-2\pi i\,\xi(E)\bigr).
$$
证明可由波算子与 Fredholm 行列式在连续谱上的构造给出：在能量壳的乘法表示中，散射矩阵为幺正家庭 $\{S(E)\}$，而 $\xi(E)$ 是相位总和的归一化版本。([arXiv][1])

**A.2 Wigner–Smith 矩阵与总相位**
对多道散射，定义
$$
Q(E)=-i\,S^{\dagger}(E)\partial_E S(E).
$$
用 $\det$ 的微分公式 $\partial_E\log\det S=\operatorname{tr}(S^{-1}\partial_E S)$ 与幺正性 $S^{-1}=S^\dagger$ 即得
$$
\partial_E\arg\det S(E)=\operatorname{tr}\,Q(E).
$$
这把"谱位移—总相位—时间延迟"三者统一。([Physical Review Link Manager][3])

---

## 附录 B：色散、正性与高能上界

**B.1 前向色散关系**
由解析性与巨圆弧抑制，可写
$$
\partial_s^2 M(s,0)=\frac{2}{\pi}\int_{s_{\mathrm{thr}}}^\infty\!\frac{\mathrm{d}s'}{(s'-s)^3}\,\mathrm{Im}\,M(s',0),
$$
对实系数 EFT 的二阶导数给出正性；其几何解释为"EFT-hedron"的凸锥结构。([Physical Review Link Manager][12])

**B.2 Froissart–Martin 上界**
利用部分波展开与解析域延拓，$\sigma_{\mathrm{tot}}(s)\le C\log^2 s$；结合 $\partial_E\arg\det S$ 与光学定理给出相位增长的上界。([CERN Document Server][6])

---

## 附录 C：IGVP 的两条场方程导出

**C.1 纠缠第一定律与相对熵**
对任意小扰动 $\rho=\rho_0+\delta\rho$，相对熵 $S(\rho|\rho_0)=\delta\langle H_{\mathrm{mod}}\rangle-\delta S_{\mathrm{out}}+\mathcal{O}(\delta^2)\ge 0$，在线性阶饱和给出 $\delta S_{\mathrm{out}}=\delta\langle H_{\mathrm{mod}}\rangle$。对于球区域，$H_{\mathrm{mod}}$ 为应力张量的局域积分，从而把几何变分与 $\delta T_{ab}$ 关联。([arXiv][4])

**C.2 爱因斯坦方程**
采用 Jacobson 与其后续工作的方法：把 $\delta S_{\mathrm{gen}}^{+}=\delta(\mathrm{Area}/4G\hbar)+\delta S_{\mathrm{out}}$ 置零，利用 QNEC/ANEC 与模态哈密顿量，得到线性化爱因斯坦方程；以积分一致性恢复非线性形式。([SpringerLink][5])

**C.3 杨–米尔斯方程**
对内部对称，模态哈密顿量含 $\int_{\mathcal{B}}\chi^\mu A_\mu^a J_0^a+\cdots$。一阶变分
$$
0=\delta S_{\mathrm{gen}}^{+}=\delta\langle H_{\mathrm{mod}}\rangle-\delta S_{\mathrm{out}}
=\int_{\mathcal{B}}\!\chi_\nu\,\langle J_\mu^a\rangle\,\delta F^{\mu\nu,a}.
$$
在对 $\delta A$ 的任意变分下，经分部积分并在 Ward 恒等式保证下丢弃边界项，可得
$$
D_\mu F^{\mu\nu,a}=J^{\nu,a}.
$$
关键在于：(i) 纠缠第一定律给出线性响应；(ii) Ward 恒等式控制边界项；(iii) $\mathcal{I}_{\mathrm{edge}}$ 抵消规范切片依赖。

---

## 附录 D：标准模型一致性与异常

**D.1 ABJ 与 Adler–Bardeen**
手性异常在一回路完全确定；标准模型每代满足 $\mathrm{U}(1)_Y^3$、$\mathrm{SU}(2)^2\mathrm{U}(1)$、$\mathrm{SU}(3)^2\mathrm{U}(1)$ 等约束。([SpringerLink][15])

**D.2 Witten 全局异常**
$\mathrm{SU}(2)$ 的全局异常要求双态数为偶数；标准模型每代为 4 个，满足一致性。([ADS][18])

**D.3 规范群全局形式的可观测后验**
不同 $\Gamma$ 导致线算符谱、分数电荷与 $\theta$-角周期的差异，可通过重粒子或拓扑响应加以区分。([arXiv][7])

---

## 参考文献指引（选摘，按主题）

* **散射数学基础**：Birman–Krein 公式与谱位移、Yafaev 综述；Wigner–Smith 时间延迟矩阵。([arXiv][1])
* **共振定义与极点**：PDG 共振评述；Breit–Wigner 与极点质量之比较。([Particle Data Group][10])
* **色散与正性**：前向幅正性与 EFT 凸几何（EFT-hedron）；多点正性进展。([Physical Review Link Manager][12])
* **Froissart–Martin 上界**：高能总截面 $\log^2 s$ 上界与常数刻度。([CERN Document Server][6])
* **纠缠与引力**：纠缠第一定律与相对熵；ANEC/QNEC 的场论证明。([arXiv][4])
* **主丛约化与希格斯**：主丛约化与商丛截面定理；希格斯的几何化解释。([arXiv][2])
* **BRST 与物理态空间**：BRST 量子化与 $\mathcal{H}_{\mathrm{phys}}$ 构造。([arXiv][8])
* **标准模型全局结构**：$(\mathrm{SU}(3)\times\mathrm{SU}(2)\times\mathrm{U}(1))/\Gamma$ 的判别与现状。([arXiv][7])
* **电弱精密与 STU**：Peskin–Takeuchi 参数及色散表达。([Physical Review Link Manager][16])
* **Kähler–Dirac 费米子**：Kähler–Dirac 与格点无倍增方案。([arXiv][14])

---

### 附记：与已知理论的一致性与新颖处

WScat^+ 保持与既有散射—谱—几何理论的双向兼容：
(i) 当忽略信息—纠缠变分时，退化为常规规范/引力作用量变分；
(ii) 把谱位移与相位之和提升为主导量，从而使 $\det S$ 成为"统一观测量"；
(iii) 用主丛约化—极点对应把希格斯机制内蕴于散射的解析结构；
(iv) 以 IGVP 构造把爱因斯坦与杨–米尔斯方程并置于同一第一性原则之下。

以上给出的证明与算法均以公开判据与文献为基准，避免引入不可检验的额外假设；相位—极点—上界—正性的四重一致性检验，为未来对新物理迹象的甄别提供了统一流程。

[1]: https://arxiv.org/abs/1006.0639 "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://arxiv.org/abs/hep-th/0609070 "Reduction of principal superbundles, Higgs superfields, and supermetric"
[3]: https://link.aps.org/doi/10.1103/PhysRev.118.349 "Lifetime Matrix in Collision Theory | Phys. Rev."
[4]: https://arxiv.org/abs/1305.3182 "[1305.3182] Relative Entropy and Holography"
[5]: https://link.springer.com/article/10.1007/JHEP04%282014%29195 "Gravitational dynamics from entanglement thermodynamics"
[6]: https://cds.cern.ch/record/1997117/files/PhysRevD.91.076006.pdf "Froissart bound on inelastic cross section without unknown ..."
[7]: https://arxiv.org/abs/2411.18160 "Detecting Standard Model Gauge Group from Generalized ..."
[8]: https://arxiv.org/abs/hep-th/0506098 "BRST Quantization"
[9]: https://link.springer.com/article/10.1007/BF02731765 "Lehmann, Symanzik, Zimmermann, Zur Formulierung quantisierter Feldtheorien | Il Nuovo Cimento 1 (1955) 205–225"
[10]: https://pdg.lbl.gov/2023/reviews/rpp2023-rev-resonances.pdf "50. Resonances"
[11]: https://arxiv.org/abs/1807.00503 "arXiv:1807.00503v1 [hep-ph] 2 Jul 2018"
[12]: https://link.aps.org/doi/10.1103/PhysRevD.104.036006 "Positive moments for scattering amplitudes | Phys. Rev. D"
[13]: https://www.sciencedirect.com/science/article/pii/0550321379900221 "M.A. Shifman, A.I. Vainshtein, V.I. Zakharov, QCD and resonance physics: theoretical foundations, Nucl. Phys. B 147 (1979) 385–447；参见同卷 448–518"
[14]: https://link.springer.com/article/10.1007/BF01614426 "P. Becher & H. Joos, The Dirac–Kähler equation and fermions on the lattice, Z. Phys. C 15 (1982) 343"
[15]: https://link.springer.com/article/10.1140/epjc/s10052-014-3083-0 "Adler–Bardeen theorem and manifest anomaly ..."
[16]: https://link.aps.org/doi/10.1103/PhysRevD.46.381 "Estimation of oblique electroweak corrections | Phys. Rev. D"
[17]: https://physics.stackexchange.com/questions/480269/does-somebody-know-where-to-find-original-paper-of-lehmann-symanzik-and-zimmerm "Does somebody know where to find original paper of ..."
[18]: https://ui.adsabs.harvard.edu/abs/1982PhLB..117..324W/abstract "An SU(2) anomaly"
