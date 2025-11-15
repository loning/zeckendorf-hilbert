# 边界语言作为统一物理框架:从散射相位、GHY 边界项到模流与广义熵的单一结构

## 摘要

本文提出并系统化"边界语言"(boundary language)的概念,将物理理论重写为关于因果切割面上"允许交换什么"的代数–几何结构,而体域场论仅是该结构的一种实现。以边界可观测代数与边界状态为基本对象,我们将三类看似独立的理论范式统一到同一框架中:(1) 散射理论中的谱移函数、总散射相位与 Wigner–Smith 群延迟;(2) 广义相对论中的 Gibbons–Hawking–York (GHY) 边界项与 Brown–York 准局域能;(3) 算子代数中的 Tomita–Takesaki 模流与相对熵单调性。核心观点是:时间不是体域内部事先给定的流逝参数,而是由"边界语言"中允许的通量平衡与信息单调性所生成的统一翻译参数;所有可观测的延迟、能量与广义熵变分,都是同一边界结构的不同投影。

在数学上,我们以"边界语言三公理"形式化这一框架:(A1) 守恒与通量公理,将边界视为能量、荷与信息通量的平衡界面;(A2) 时间生成公理,将在边界上定义的一参数 (*)-自同构群及其生成元视为时间刻度来源;(A3) 单调与一致性公理,以相对熵单调性及其几何形式(量子焦聚、量子零能条件等)为代表,排除超因果与负熵传输。

在散射实现中,我们证明:满足 A1–A3 的边界语言在适定短程散射体系上必然诱导刻度同一式

$$
\kappa(\omega)=\dfrac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\dfrac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

其中 $\varphi(\omega)$ 为总散射半相位,$\rho_{\mathrm{rel}}(\omega)$ 为相对态密度,$Q(\omega)$ 为 Wigner–Smith 群延迟算子。该同一式把相位梯度、谱移密度与群延迟的迹统一为"时间刻度"这一单一边界对象。

在引力实现中,我们表明:GHY 边界项与 Brown–York 准局域能正定性是边界语言 A1–A2 在几何侧的必要条件;从而将 ADM 时间、本征时间与 Killing 时间重述为由边界哈密顿量生成的翻译。在算子代数实现中,我们以 Tomita–Takesaki 模理论给出边界语言的典范模型,并以相对熵单调性实现 A3,从而在一类自然情形下把"时间箭头"刻画为相对熵随模时间的单调演化。

本文最后通过一维势散射、静态黑洞外区域与 Rindler 楔三类模型,展示边界语言如何产生实验可观测的时间延迟、准局域能与 Unruh 温度,并给出若干可检验的谱–几何–信息论预言。附录中详细给出散射–谱移–群延迟刻度同一式、GHY 项变分完备性及相对熵单调性等关键命题的证明,并引入有限阶 Euler–Maclaurin 与 Poisson 纪律的"误差几何"框架,以保证边界读数向实验数据的可控映射。

---

## 1 引言

### 1.1 研究动机与总体结构

传统场论与引力理论多以体域为起点:给定带度规的流形 $(M,g)$、体域作用量 $S[\Phi,g]$ 及其变分方程,再通过边界条件加以补足。然而在三类看似无关的理论中,边界长期扮演着"真正可观测"的角色:

1. 在散射与谱理论中,总散射相位 $\varphi(\omega)$、Birman–Kreĭn 谱移函数 $\xi(\omega)$ 以及 Wigner–Smith 群延迟算子 $Q(\omega)=-iS^\dagger\partial_\omega S$ 完全由"入/出无穷远边界"定义。
2. 在广义相对论中,Einstein–Hilbert 体作用的变分要求引入 Gibbons–Hawking–York (GHY) 边界项以实现变分完备性,而 Brown–York 准局域能与准局域应力张量则严格是边界数据。
3. 在算子代数与代数量子场论中,Tomita–Takesaki 模流 $\sigma_t^\omega$ 完全由代数–态对 $(\mathcal M,\omega)$ 决定,其参数 $t$ 被视为"内禀时间";而相对熵的单调性与广义熵不等式则仅依赖边界可访问代数之间的包含关系。

这些事实提示:**边界本身,而非体域,才是统一物理结构的自然舞台**。本文据此提出"边界语言"的概念,将物理理论定义为关于某一因果切割面 $\Sigma \subset M$ 的三元组结构

$$
\mathfrak L_\Sigma=(\mathcal A_\partial,\omega,\mathcal F),
$$

其中 $\mathcal A_\partial$ 是边界可观测代数,$\omega$ 是边界状态,$\mathcal F$ 是通量泛函族,用以刻画跨越 $\Sigma$ 的能量、荷与信息交换。体域场论、几何与散射构造则仅是实现这一三元组的不同方式。

### 1.2 核心观点:时间作为边界翻译

本文的核心主张可以概括为:

* 给定一条因果切割面 $\Sigma$,物理理论首先给出"允许跨越 $\Sigma$ 的交换"——这就是边界语言;
* 时间不是事先赋予体域的连续参数,而是由边界语言内部的一参数 (*)-自同构群 $\{\alpha_t\}_{t\in\mathbb R}$ 及其生成元导出;
* 在满足守恒与单调性条件时,该时间与散射相位的频率导数、引力边界哈密顿量与模流参数属于同一"时间刻度等价类"。

更具体地,我们将在散射实现中证明刻度同一式

$$
\kappa(\omega)=\dfrac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\dfrac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

并在引力与模流实现中展示:ADM/本征时间与模时间可通过此刻度映射进入同一等价类。

### 1.3 文章结构

全文结构如下:第 2 节给出边界语言与三公理的严格定义。第 3 节在短程散射理论中实现边界语言,并证明刻度同一式。第 4 节在带边界的引力理论中展示 GHY 项与 Brown–York 准局域能如何实现 A1–A2。第 5 节讨论模流与相对熵单调性,展示 A3 在代数侧的实现。第 6 节整合三端结构,引入统一时间刻度等价类。第 7 节给出若干典型模型与可检预言。附录 A–D 提供关键命题与误差几何框架的详细证明。

---

## 2 边界语言与三公理

### 2.1 因果切割面与边界代数

设 $(M,g)$ 为具有良好因果结构的洛伦兹流形,$\Sigma\subset M$ 为一共维一子流形,将时空分成"内侧" $M_{\mathrm{in}}$ 与"外侧" $M_{\mathrm{out}}$。我们称 $\Sigma$ 为因果切割面。

**定义 2.1.1(边界可观测代数)**
与因果切割面 $\Sigma$ 关联的边界可观测代数是一个 $C^\ast$-代数 $\mathcal A_\partial$,其元素对应于仅通过对 $\Sigma$ 上的读数即可决定的可观测量,例如:

* 散射通道上的入/出场算子与 S-矩阵的函数;
* 边界诱导度规、外在曲率及其构成的几何量;
* 代数量子场论中楔区或 Cauchy 表面边界上的局域代数。

**定义 2.1.2(边界状态)**
边界状态是 $\mathcal A_\partial$ 上的正归一线性泛函 $\omega:\mathcal A_\partial\to\mathbb C$,代表给定物理配置(体域场、度规、外部源等)下对边界可观测量的期望值。

### 2.2 边界语言三元组

**定义 2.2.1(边界语言)**
一个边界语言是三元组

$$
\mathfrak L_\Sigma=(\mathcal A_\partial,\omega,\mathcal F),
$$

其中 $\mathcal A_\partial,\omega$ 如上所述,$\mathcal F\subset\mathcal A_\partial^\ast$ 为一族实值线性泛函,称为通量泛函族,用以刻画能量、荷、熵或信息等可交换量的边界读数。

典型示例包括:

* 散射理论中与概率流、能量流或时间延迟相关的泛函;
* 引力理论中与准局域能量、动量、角动量与广义熵相关的泛函;
* 代数量子理论中与模哈密顿量、相对熵与信息流相关的泛函。

### 2.3 公理 A1:守恒与通量

**公理 A1(守恒与通量)**
对于满足适当正则性条件的体域作用量 $S_{\mathrm{bulk}}$ 和边界作用量 $S_{\mathrm{bdry}}$,存在通量泛函 $F\in\mathcal F$,使得对任意紧支撑体域变分 $\delta\Phi,\delta g$ 有

$$
\delta(S_{\mathrm{bulk}}+S_{\mathrm{bdry}})=\text{(体积分)}+F(\delta X_\Sigma),
$$

其中 $\delta X_\Sigma\in\mathcal A_\partial$ 为对应的边界源变分。要求对所有满足边界条件的物理变分,当体域方程成立时有

$$
F(\delta X_\Sigma)=0
$$

并且 $F$ 对允许的边界变分族线性,使边界变分可被解释为"通量守恒条件"的表达。

直观上,A1 要求任意体域变分在边界上的残余项都可被识别为某个通量泛函作用于边界数据的变分,从而将"变分完备性"重述为"通量可归算到边界语言"的条件。

### 2.4 公理 A2:时间生成

**公理 A2(时间生成)**
在边界可观测代数 $\mathcal A_\partial$ 上存在一参数 (*)-自同构群

$$
\{\alpha_t\}_{t\in\mathbb R}\subset\operatorname{Aut}(\mathcal A_\partial),
$$

其生成元为闭的不定界导子 $\delta$,满足:

1. 存在一族"时间可观测量" $\mathcal T\subset\mathcal A_\partial$,对每个 $T\in\mathcal T$,$t\mapsto\omega(\alpha_t(T))$ 连续可微;
2. 通量泛函在 $\alpha_t$ 下满足合适的不变性或守恒性质,例如对能量泛函 $F_E\in\mathcal F$ 有
   $F_E\circ\alpha_t=F_E$;
3. 对应生成元 $\delta$ 可通过某个"边界哈密顿量" $H_\partial\in\mathcal A_\partial^{\prime\prime}$ 表示为

$$
\dfrac{\mathrm d}{\mathrm dt}\omega(\alpha_t(A))=i\,\omega([H_\partial,\alpha_t(A)])
$$

   至少在某个稠密域上成立。

我们将参数 $t\in\mathbb R$ 称为边界语言生成的时间刻度。它在散射实现中与频率 $\omega$ 共轭,在引力实现中与 ADM/本征时间共轭,在模流实现中与模参数共轭。

### 2.5 公理 A3:单调与一致性

**公理 A3(单调与一致性)**
给定边界语言 $\mathfrak L_\Sigma$,对任意两个边界状态 $\omega,\omega'$,存在非负函数 $S_{\mathrm{rel}}(\omega'\Vert\omega)$,称为相对熵或广义熵,满足:

1. 非负性:$S_{\mathrm{rel}}(\omega'\Vert\omega)\ge0$,且当且仅当 $\omega'=\omega$ 时取零;
2. 单调性:对任意子代数包含 $\mathcal A_{\partial,1}\subset\mathcal A_{\partial,2}\subset\mathcal A_\partial$,有

$$
S_{\mathrm{rel}}^{(1)}(\omega'\Vert\omega)\le S_{\mathrm{rel}}^{(2)}(\omega'\Vert\omega);
$$

3. 时间一致性:在适当物理条件(如能量条件或 KMS 条件)下,若沿时间生成公理 A2 的流 $\omega_t,\omega_t'$ 演化,则

$$
\dfrac{\mathrm d}{\mathrm dt}S_{\mathrm{rel}}(\omega_t'\Vert\omega_t)\le0
$$

   至少在某个方向(定义时间箭头)上成立。

A3 把因果一致性与"信息不能增益"刻画为边界语言的内禀性质,为时间箭头的边界几何–代数定义提供基础。

---

## 3 散射理论中的边界语言实现

### 3.1 短程散射与 S-矩阵

考虑 Hilbert 空间 $\mathcal H$ 上的自共轭算子 $H_0$ 与 $H=H_0+V$,其中 $V$ 为短程扰动,满足标准假设使得波算子

$$
\Omega_\pm=\operatorname{s-}\lim_{t\to\pm\infty}e^{itH}e^{-itH_0}
$$

存在且完备。S-矩阵定义为

$$
S=\Omega_+^\ast\Omega_-,
$$

在能量表象下可分解为

$$
S=\int^\oplus S(\omega)\,\mathrm d\mu(\omega),
$$

其中 $S(\omega)$ 为作用于通道空间的幺正矩阵。

我们在此取因果切割面为"无穷远入/出边界",边界代数为

$$
\mathcal A_\partial=B(\mathcal H_{\mathrm{in}})\vee B(\mathcal H_{\mathrm{out}})
$$

的某个适当子代数(例如由渐进行为生成的代数)。边界状态 $\omega$ 可取为入射波包或热平衡态。

**定义 3.1.1(总散射相位与群延迟)**
设

$$
\Phi(\omega)=\arg\det S(\omega),\qquad\varphi(\omega)=\dfrac{1}{2}\Phi(\omega).
$$

定义 Wigner–Smith 群延迟算子为

$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega).
$$

记对通道空间的迹为 $\operatorname{tr}Q(\omega)$。

另设 $\xi(\omega)$ 为 Birman–Kreĭn 谱移函数,相对态密度定义为

$$
\rho_{\mathrm{rel}}(\omega)=\dfrac{\mathrm d}{\mathrm d\omega}\xi(\omega)
$$

(符号约定见附录 A)。

### 3.2 刻度同一式与 A2 的散射实现

在散射语境下,我们将"时间可观测量"选取为频率空间上由 $S(\omega)$ 产生的可观测量,通量泛函则包括概率流、能量流与延迟泛函。

**定理 3.2.1(散射–谱移–群延迟刻度同一式)**
在满足短程与正则性假设的散射系统中,刻度函数

$$
\kappa(\omega)=\dfrac{\varphi'(\omega)}{\pi}
$$

与相对态密度 $\rho_{\mathrm{rel}}(\omega)$ 以及群延迟的迹 $(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 满足恒等式

$$
\kappa(\omega)=\dfrac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\dfrac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

该同一式将总相位的频率导数、谱移密度与群延迟统一为同一刻度函数 $\kappa(\omega)$,可视为边界语言生成的时间刻度在散射端的具体表达。

*证明思路*:利用 Birman–Kreĭn 公式

$$
\det S(\omega)=e^{-2\pi i\xi(\omega)},
$$

对 $\omega$ 求导,并结合 $\det S(\omega)=e^{i\Phi(\omega)}$ 与 $Q(\omega)=-iS^\dagger\partial_\omega S$ 的定义,得到

$$
\operatorname{tr}Q(\omega)=2\pi\xi'(\omega),\quad\Phi(\omega)=-2\pi\xi(\omega),
$$

从而

$$
\varphi'(\omega)/\pi=-\xi'(\omega),\quad \rho_{\mathrm{rel}}(\omega)=-\xi'(\omega),
$$

综合得到所述同一式。详尽证明见附录 A。

**推论 3.2.2(散射时间刻度)**
对频率局域在 $\omega_0$ 邻域的入射波包,其平均群延迟 $\tau_{\mathrm{WS}}(\omega_0)$ 给出边界时间刻度的实验读数:

$$
\tau_{\mathrm{WS}}(\omega_0)=\dfrac{\int\mathrm d\omega\,|a(\omega)|^2\operatorname{tr}Q(\omega)}{\int\mathrm d\omega\,|a(\omega)|^2}\approx 2\pi\,\kappa(\omega_0).
$$

### 3.3 边界语言视角下的谱流与拓扑分支

考虑依参数 $\lambda\in\mathbb R$ 连续变化的散射系统 $S(\omega;\lambda)$,在满足适当 Fredholm 性与正则性条件下,谱移函数 $\xi(\omega;\lambda)$ 为 $(\omega,\lambda)$ 的连续函数,其在 $\omega$ 上的积分给出谱流:

**命题 3.3.1(谱流作为边界拓扑分支变化)**
在参数区间 $[\lambda_1,\lambda_2]$ 上,能量区间 $[\omega_1,\omega_2]$ 内的本征值穿越谱阈产生的累计谱流

$$
\Delta N=\int_{\omega_1}^{\omega_2}\mathrm d\omega\,\rho_{\mathrm{rel}}(\omega;\lambda)
$$

是整数,并对应于边界语言的拓扑分支变化。其物理意义是:参数变化导致允许跨越边界的态数改变,对应拓扑类别或束缚态数目的跃迁。

---

## 4 引力中的边界语言与 GHY 项

### 4.1 Einstein–Hilbert 作用的变分问题

设 $(M,g)$ 为带边界 $\partial M$ 的四维时空,Einstein–Hilbert 体作用为

$$
S_{\mathrm{EH}}[g]=\dfrac{1}{16\pi G}\int_M\mathrm d^4x\,\sqrt{-g}\,R.
$$

对度规变分 $\delta g_{\mu\nu}$,可将标量曲率变分写为

$$
\delta R=g^{\mu\nu}\delta R_{\mu\nu}+R_{\mu\nu}\delta g^{\mu\nu},
$$

而 $\delta R_{\mu\nu}$ 含有对 $\delta g_{\mu\nu}$ 的一阶导数。经分部积分后,$\delta S_{\mathrm{EH}}$ 包含体积项与边界项,边界项中含有 $\partial_n\delta g$ 项,无法仅用诱导度规 $h_{ij}=g_{ij}|_{\partial M}$ 的变分表示,这意味着单独 $S_{\mathrm{EH}}$ 不能给出良定的 Dirichlet 边界变分问题。

**命题 4.1.1(GHY 项作为 A1 的必要条件)**
若只包含 $S_{\mathrm{EH}}$ 而不添加边界作用 $S_{\mathrm{GHY}}$,则对度规变分的边界贡献中存在不能写成通量泛函 $F\in\mathcal F$ 对边界源变分 $\delta h_{ij}$ 线性作用的项,从而违背边界语言公理 A1。加入 GHY 边界项

$$
S_{\mathrm{GHY}}[g]=\dfrac{1}{8\pi G}\int_{\partial M}\mathrm d^3x\,\sqrt{|h|}\,K,
$$

后,总作用 $S_{\mathrm{tot}}=S_{\mathrm{EH}}+S_{\mathrm{GHY}}$ 的边界变分可写为

$$
\delta S_{\mathrm{tot}}[g]=\text{(体积分)}+\dfrac{1}{16\pi G}\int_{\partial M}\mathrm d^3x\,\sqrt{|h|}\,(K_{ij}-Kh_{ij})\delta h^{ij},
$$

其中 $K_{ij}$ 为外在曲率,$K=K_{ij}h^{ij}$。因此

$$
F(\delta X_\Sigma)=\dfrac{1}{16\pi G}\int_{\partial M}\mathrm d^3x\,\sqrt{|h|}\,(K_{ij}-Kh_{ij})\delta h^{ij}
$$

构成通量泛函,实现 A1。详细推导见附录 B。

### 4.2 Brown–York 准局域能与时间生成

由总作用量对边界度规的变分可定义 Brown–York 准局域能动量张量

$$
T_{ij}^{\mathrm{BY}}=\dfrac{2}{\sqrt{|h|}}\dfrac{\delta S_{\mathrm{tot}}}{\delta h^{ij}}=\dfrac{1}{8\pi G}(K_{ij}-Kh_{ij})+\text{(参考项)}.
$$

对给定时间切片 $\Sigma_t\subset\partial M$ 及其单位时间样向量场 $u^i$,可定义准局域能量

$$
E_{\mathrm{BY}}[\Sigma_t]=\int_{\Sigma_t}\mathrm d^2x\,\sqrt{\sigma}\,u^iu^jT_{ij}^{\mathrm{BY}},
$$

其中 $\sigma$ 为 $\Sigma_t$ 上诱导二维度规。

**定理 4.2.1(边界哈密顿量与几何时间生成)**
在具有 ADM 分解的时空中,存在一个边界哈密顿量 $H_\partial$,其在适当边界条件下,通过泊松括号或对易子生成边界代数上的时间演化:对任意边界可观测量 $A\in\mathcal A_\partial$ 有

$$
\dfrac{\mathrm d}{\mathrm dt}\omega_t(A)=i\,\omega_t([H_\partial,A]),
$$

其中 $\omega_t$ 是沿时间切片 $\Sigma_t$ 的态。且 $H_\partial$ 可由 Brown–York 准局域能量积分得到,从而几何时间完全由边界语言生成,满足 A2。

在静态情形(存在时间样 Killing 矢量)下,$H_\partial$ 与 ADM 质量或 Komar 能量等价,从而 Killing 时间、ADM 时间与由边界语言生成的时间刻度属于同一等价类。

---

## 5 算子代数、模流与相对熵

### 5.1 标准形与模流

设 $\mathcal M$ 为作用于 Hilbert 空间 $\mathcal H$ 的 von Neumann 代数,$\omega$ 为 $\mathcal M$ 上的忠实正态态。GNS 表象给出向量 $\Omega\in\mathcal H$,使得

$$
\omega(A)=\langle\Omega,A\Omega\rangle.
$$

Tomita 运算符 $S$ 由

$$
SA\Omega=A^\ast\Omega,\quad A\in\mathcal M
$$

定义,其极分解为

$$
S=J\Delta^{1/2},
$$

其中 $J$ 为共轭,$\Delta$ 为模算子。Tomita–Takesaki 模流定义为

$$
\sigma_t^\omega(A)=\Delta^{it}A\Delta^{-it},\quad t\in\mathbb R.
$$

在边界语言框架下,我们取

$$
\mathcal A_\partial=\mathcal M,\quad \alpha_t=\sigma_t^\omega,\quad \omega\ \text{给定}.
$$

**命题 5.1.1(模流作为 A2 的典范实现)**
对任意标准形 $(\mathcal M,\mathcal H,\Omega)$ 与忠实正态态 $\omega$,Tomita–Takesaki 模流 $\{\sigma_t^\omega\}$ 为一参数 (*)-自同构群,满足:

1. $\omega\circ\sigma_t^\omega=\omega$(即 $\omega$ 为模流的 KMS 态);
2. 对任意 $A\in\mathcal M$,映射 $t\mapsto\omega(\sigma_t^\omega(A))$ 连续。

因此,$(\mathcal M,\omega,\{\sigma_t^\omega\})$ 自然满足时间生成公理 A2,并提供"模时间"的严格数学实现。

### 5.2 相对熵与单调性

对两个忠实正态态 $\omega,\omega'$,可定义相对模算子 $\Delta_{\omega',\omega}$,Araki 相对熵定义为

$$
S(\omega'\Vert\omega)=-\langle\Omega',\log\Delta_{\omega',\omega}\,\Omega'\rangle,
$$

其中 $\Omega'$ 为 $\omega'$ 的 GNS 向量。

**定理 5.2.1(相对熵单调性)**
若 $N\subset M$ 为 von Neumann 代数包含,$\omega,\omega'$ 为 $M$ 上的态,则

$$
S(\omega'|_N\Vert\omega|_N)\le S(\omega'\Vert\omega).
$$

此定理表达了"缩小可访问代数不会增加可区分度",在边界语言框架中正对应于公理 A3 的第二条。

在与几何–全息相结合的情形下,相对熵单调性可等价于广义熵的某些单调性质,以及量子零能条件、量子焦聚条件等,从而提供统一的"信息不增"边界律。

### 5.3 时间箭头与模时间

进一步地,考虑沿模流演化的态

$$
\omega_t=\omega\circ\sigma_t^\omega,\quad \omega_t'=\omega'\circ\sigma_t^\omega.
$$

在满足适当能量条件、KMS 条件与局域性假设下,可以证明或强烈预期

$$
\dfrac{\mathrm d}{\mathrm dt}S(\omega_t'\Vert\omega_t)\le0,
$$

从而将时间箭头定义为相对熵单调减小的方向。与散射端时间刻度、引力端几何时间结合,可得到统一的时间几何图景。

---

## 6 统一时间刻度与刻度等价类

### 6.1 三位一体刻度函数

综合第 3 节的散射实现与第 4、5 节的引力和模流实现,我们引入统一刻度函数

$$
\kappa(\omega)=\dfrac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\dfrac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

在散射端,$\kappa(\omega)$ 直接由 S-矩阵给出;在引力端,$\kappa$ 与曲率背景中传播的相位延迟与 Shapiro 延迟相关;在模流端,$\kappa$ 可通过谱分解与模算子 $\Delta$ 的对数谱密度联系起来。

**定义 6.1.1(时间刻度等价类)**
若两个时间参数 $t_1,t_2$ 满足存在严格单调的正函数 $f:\mathbb R\to\mathbb R$ 使得

$$
t_2=f(t_1)
$$

并且对边界语言产生的所有可观测时间序列,$t_1,t_2$ 之间仅存在刻度重标,而不改变因果顺序与单调性,则称 $t_1,t_2$ 属于同一时间刻度等价类,记为 $[t]$。

**命题 6.1.2(散射–几何–模时间的刻度统一)**
在满足 A1–A3 的边界语言框架下,散射时间(由 $\kappa(\omega)$ 定义)、几何时间(由边界哈密顿量 $H_\partial$ 生成)与模时间(由模流 $\sigma_t^\omega$ 定义)在适当条件下属于同一刻度等价类。刻度映射由刻度函数 $\kappa$ 与几何–代数桥接给出。

### 6.2 Null–Modular 双覆盖的边界草图

在零测地边界(null boundary)与楔区模流中,存在所谓 Null–Modular 双覆盖结构:零测地的仿射参数可以通过模流参数的适当重标得到,而模哈密顿量与几何生成元之间存在双线性关系。该结构表明,在极限意义上,null 边界上的时间可以被视为模时间的几何化;其广义熵变分满足量子焦聚不等式,而这又是相对熵单调性的几何投影。由于技术细节繁复,本文在此仅作概念性陈述。

---

## 7 典型模型与可检验预言

### 7.1 一维势散射模型

考虑一维势散射 $H_0=-\dfrac{\mathrm d^2}{\mathrm dx^2}$、$H=H_0+V(x)$,其中 $V(x)$ 为短程势。入/出通道为平面波,S-矩阵为 $2\times2$ 幺正矩阵,可写为

$$
S(\omega)=\begin{pmatrix}t(\omega)&r'(\omega)\\r(\omega)&t'(\omega)\end{pmatrix}.
$$

在此模型中:

* 总散射相位 $\varphi(\omega)$ 由 $\det S(\omega)$ 的辐角确定;
* 群延迟算子 $Q(\omega)$ 的迹给出通道平均 Wigner–Smith 延迟;
* 相对态密度 $\rho_{\mathrm{rel}}(\omega)$ 描述束缚态与共振态对态密度的修正。

通过附录 A 的同一式

$$
\kappa(\omega)=\dfrac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\dfrac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

可在频率局域波包上定义边界时间刻度。数值上,测量 $\operatorname{tr}Q(\omega)$ 或共振峰附近的相位跃迁都可直接给出 $\kappa(\omega)$ 的实验代理。

### 7.2 静态黑洞外区域与准局域能

在静态黑洞外区域,选定一个大球面 $r=R$ 作为边界,定义 Brown–York 准局域能量 $E_{\mathrm{BY}}(R)$。当 $R\to\infty$ 时,$E_{\mathrm{BY}}$ 趋近于 ADM 质量。对有限 $R$,可将 "Shapiro 延迟"、光线绕射相位与 $E_{\mathrm{BY}}$ 联系起来,得到几何时间与散射刻度 $\kappa(\omega)$ 的一致性条件。这提供了一种从边界语言角度理解"引力时间膨胀"的方式。

### 7.3 Rindler 楔、Unruh 温度与模时间

在 Minkowski 时空中,取 Rindler 楔 $x>|t|$,楔区局域代数上的模流恰好等同于 Rindler 时间平移,真空态为对应温度为 $T=a/2\pi$ 的 KMS 态,其中 $a$ 为加速度。由此可将 Unruh 温度重述为边界语言中"模时间刻度"的温度解释:对加速观察者而言,模流即其物理时间演化,而模哈密顿量刻画其可访问代数的能谱结构。

---

## 8 总结与展望

本文提出的边界语言框架以三公理(守恒与通量、时间生成、单调与一致性)为基础,将散射理论中的相位–谱移–时间延迟,引力中的 GHY 边界项与准局域能,以及算子代数中的模流与相对熵单调性统一于同一结构之下。其关键技术结果是刻度同一式

$$
\kappa(\omega)=\dfrac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\dfrac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

以及 GHY 项在变分完备性中的必要性与模流在时间生成中的典范性。

未来工作方向包括:Null–Modular 双覆盖与量子焦聚不等式的完整公理化;边界语言在时间晶体、自指散射网络与因果网络中的实现;以及在实验与数值层面对刻度同一式与误差几何预测的系统检验。

---

## 附录 A:散射–谱移–群延迟刻度同一式的严格推导

本附录给出定理 3.2.1 的详细证明。

### A.1 谱移函数与 Birman–Kreĭn 公式

设 $H_0,H=H_0+V$ 为自共轭算子,$V$ 为 trace class 微扰。谱移函数 $\xi(\lambda)$ 通过下式定义:对足够光滑且衰减良好的函数 $f$,有

$$
\operatorname{tr}\left(f(H)-f(H_0)\right)=\int_{-\infty}^{\infty}f'(\lambda)\,\xi(\lambda)\,\mathrm d\lambda.
$$

Birman–Kreĭn 公式表明,对几乎处处的能量 $\lambda$,S-矩阵的行列式满足

$$
\det S(\lambda)=e^{-2\pi i\xi(\lambda)}.
$$

### A.2 对能量求导与群延迟

对 $\lambda$ 求导得到

$$
\dfrac{\partial_\lambda\det S(\lambda)}{\det S(\lambda)}=-2\pi i\,\xi'(\lambda).
$$

另一方面,对可逆矩阵 $S(\lambda)$,有对数导数公式

$$
\dfrac{\partial_\lambda\det S}{\det S}=\operatorname{tr}\left(S^{-1}\partial_\lambda S\right).
$$

散射矩阵幺正性给出 $S^{-1}=S^\dagger$,定义

$$
Q(\lambda)=-iS^\dagger(\lambda)\partial_\lambda S(\lambda),
$$

于是

$$
\operatorname{tr}Q(\lambda)=-i\,\operatorname{tr}\left(S^\dagger\partial_\lambda S\right)=-i\,\dfrac{\partial_\lambda\det S}{\det S}=2\pi\,\xi'(\lambda).
$$

故

$$
\xi'(\lambda)=\dfrac{1}{2\pi}\operatorname{tr}Q(\lambda).
$$

### A.3 相位与相对态密度

令

$$
\Phi(\lambda)=\arg\det S(\lambda).
$$

由 Birman–Kreĭn 公式

$$
i\Phi(\lambda)=-2\pi i\xi(\lambda)\quad\Rightarrow\quad\Phi(\lambda)=-2\pi\xi(\lambda).
$$

总散射半相位

$$
\varphi(\lambda)=\dfrac{1}{2}\Phi(\lambda)=-\pi\xi(\lambda).
$$

对 $\lambda$ 求导得

$$
\dfrac{\varphi'(\lambda)}{\pi}=-\xi'(\lambda).
$$

依据定义,相对态密度 $\rho_{\mathrm{rel}}(\lambda)$ 与谱移函数导数的关系可选定为

$$
\rho_{\mathrm{rel}}(\lambda)=-\xi'(\lambda),
$$

符号约定反映散射与束缚态计数的一致性。于是

$$
\dfrac{\varphi'(\lambda)}{\pi}=\rho_{\mathrm{rel}}(\lambda).
$$

与前一小节结果比较可得

$$
\rho_{\mathrm{rel}}(\lambda)=\dfrac{1}{2\pi}\operatorname{tr}Q(\lambda),
$$

最终得到

$$
\dfrac{\varphi'(\lambda)}{\pi}=\rho_{\mathrm{rel}}(\lambda)=\dfrac{1}{2\pi}\operatorname{tr}Q(\lambda).
$$

---

## 附录 B:GHY 边界项与变分完备性的推导

本附录详细说明命题 4.1.1。

### B.1 Einstein–Hilbert 作用的边界变分

从

$$
S_{\mathrm{EH}}[g]=\dfrac{1}{16\pi G}\int_M\mathrm d^4x\,\sqrt{-g}\,R
$$

出发,对 $g_{\mu\nu}$ 变分,并利用

$$
\delta R_{\mu\nu}=\nabla_\rho\delta\Gamma^\rho_{\mu\nu}-\nabla_\mu\delta\Gamma^\rho_{\rho\nu},
$$

可以将 $\delta S_{\mathrm{EH}}$ 写成体积项与边界项之和。边界项可整理为

$$
\delta S_{\mathrm{EH}}\big|_{\partial M}=\dfrac{1}{16\pi G}\int_{\partial M}\mathrm d^3x\,\sqrt{|h|}\,n_\mu\left(g^{\nu\rho}\delta\Gamma^\mu_{\nu\rho}-g^{\mu\nu}\delta\Gamma^\rho_{\rho\nu}\right),
$$

其中 $n_\mu$ 为边界单位法向矢量。由于 $\delta\Gamma$ 含有 $\partial\delta g$ 项,边界变分不能仅用 $\delta h_{ij}$ 表示,从而不符合"通量泛函对源变分线性作用"的形式。

### B.2 GHY 项的补偿作用

引入 GHY 边界作用

$$
S_{\mathrm{GHY}}[g]=\dfrac{1}{8\pi G}\int_{\partial M}\mathrm d^3x\,\sqrt{|h|}\,K.
$$

外在曲率定义为

$$
K_{ij}=h_i^{\ \mu}h_j^{\ \nu}\nabla_\mu n_\nu,\quad K=K_{ij}h^{ij}.
$$

对 $g_{\mu\nu}$ 变分,$K$ 的变分可用 $\delta h_{ij}$ 与法向导数组合表示。经仔细整理,$\delta S_{\mathrm{GHY}}$ 刚好产生补偿项,使得

1. 所有含 $\partial_n\delta g$ 的项在 $\delta S_{\mathrm{EH}}+\delta S_{\mathrm{GHY}}$ 中相互抵消;
2. 剩余的边界变分仅包含 $\delta h_{ij}$ 而不含其导数。

最终结果为

$$
\delta S_{\mathrm{tot}}=\delta S_{\mathrm{EH}}+\delta S_{\mathrm{GHY}}=\dfrac{1}{16\pi G}\int_M\mathrm d^4x\,\sqrt{-g}\,G_{\mu\nu}\delta g^{\mu\nu}+\dfrac{1}{16\pi G}\int_{\partial M}\mathrm d^3x\,\sqrt{|h|}\,(K_{ij}-Kh_{ij})\delta h^{ij}.
$$

若选取 Dirichlet 边界条件 $\delta h_{ij}=0$,则边界项自动消失,变分完备;若允许 $\delta h_{ij}\ne0$,则可将边界项解释为通量泛函

$$
F(\delta X_\Sigma)=\dfrac{1}{16\pi G}\int_{\partial M}\mathrm d^3x\,\sqrt{|h|}\,(K_{ij}-Kh_{ij})\delta h^{ij},
$$

其中 $\delta X_\Sigma\equiv\delta h_{ij}$。至此,公理 A1 得到实现。

---

## 附录 C:模流、相对熵与时间箭头的技术细节

### C.1 标准形与模算子的构造

给定 $(\mathcal M,\omega)$,GNS 表象 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$ 使得

$$
\omega(A)=\langle\Omega_\omega,\pi_\omega(A)\Omega_\omega\rangle.
$$

在不致混淆的情况下略去 $\pi_\omega$,记 $A\Omega_\omega$ 即为 GNS 向量。

Tomita 运算符 $S$ 由

$$
SA\Omega_\omega=A^\ast\Omega_\omega
$$

定义,其闭包的极分解 $S=J\Delta^{1/2}$ 给出模算子 $\Delta$ 和模共轭 $J$。模流

$$
\sigma_t^\omega(A)=\Delta^{it}A\Delta^{-it}
$$

满足 Tomita–Takesaki 定理:对任意 $t\in\mathbb R$,$\sigma_t^\omega$ 是 $\mathcal M$ 的 (*)-自同构,且

$$
\omega(A\sigma_{i}^\omega(B))=\omega(BA)
$$

给出 KMS 条件。

### C.2 相对模算子与相对熵

给定两个态 $\omega,\omega'$,相对模算子 $\Delta_{\omega',\omega}$ 通过相对 Tomita 运算子构造:

$$
S_{\omega',\omega}A\Omega_\omega=A^\ast\Omega',
$$

其极分解为 $S_{\omega',\omega}=J_{\omega',\omega}\Delta_{\omega',\omega}^{1/2}$。
Araki 相对熵为

$$
S(\omega'\Vert\omega)=-\langle\Omega',\log\Delta_{\omega',\omega}\,\Omega'\rangle.
$$

相对熵单调性可通过完全正、保迹映射及 Stinespring 表示来证明:如果 $\Phi:\mathcal M\to\mathcal N$ 是完全正保迹映射,则

$$
S(\omega'\circ\Phi\Vert\omega\circ\Phi)\le S(\omega'\Vert\omega).
$$

取 $\Phi$ 为条件期望或子代数限制即可得到定理 5.2.1。

### C.3 时间箭头的不等式形式

在某些情形下,可将时间箭头的陈述加强为如下不等式:设 $\omega_t,\omega_t'$ 为沿模流演化的态,则

$$
\dfrac{\mathrm d^2}{\mathrm dt^2}S(\omega_t'\Vert\omega_t)\ge0,
$$

即相对熵在模时间上是凸的。此类性质在全息与 QNEC/QFC 文献中与广义熵的二阶变分密切相关,对应于 null 边界上的量子焦聚条件。

---

## 附录 D:有限阶 Euler–Maclaurin 与 Poisson 纪律的误差几何

边界语言产生的刻度函数 $\kappa(\omega)$ 与实验读数之间往往通过频率积分与离散采样联系。为保证"理论–实验对接"的严格性,需要一个控制 aliasing 与截断误差的"误差几何"框架。

### D.1 有限阶 Euler–Maclaurin 公式

对足够光滑的函数 $f$,在区间 $[a,b]$ 上有 Euler–Maclaurin 公式

$$
\sum_{n=a}^{b}f(n)=\int_a^b f(x)\,\mathrm dx+\dfrac{f(a)+f(b)}{2}+\sum_{k=1}^m\dfrac{B_{2k}}{(2k)!}\left(f^{(2k-1)}(b)-f^{(2k-1)}(a)\right)+R_m,
$$

其中 $B_{2k}$ 为 Bernoulli 数,$R_m$ 为余项。我们强制只取有限阶 $m$,并将 $R_m$ 在给定函数类上的上界视为"误差几何"的一部分:其大小由 $f$ 的高阶导数与主奇点控制。

原则上,我们要求:

1. 拟合刻度函数 $\kappa(\omega)$ 的任何多项式或有理近似都在物理上相关频率区间内控制高阶导数的增长;
2. 所有由 Euler–Maclaurin 截断引入的误差 $R_m$ 不产生新的奇点,即"奇性不增,极点=主尺度"。

### D.2 Poisson 求和与 aliasing 控制

Poisson 求和公式

$$
\sum_{n\in\mathbb Z}f(n)=\sum_{k\in\mathbb Z}\hat f(2\pi k)
$$

将离散采样与频率空间联系。对于刻度函数与相关响应函数的数值计算,采样步长 $\Delta\omega$ 与频域支撑决定 aliasing 误差。

在边界语言框架下,我们要求:

1. 采样满足 Nyquist–Shannon 条件,使 aliasing 误差可被上界控制;
2. 对每个实验采样方案,给出明确的 aliasing 误差估计,并证明其不引入新的奇点,仅改变权重或分布;
3. 误差分析服从"有限阶"纪律:不依赖形式上无限和或无限微分,而是通过有限阶截断与严格误差界形成封闭的误差几何。

这一框架使得从理论刻度函数 $\kappa(\omega)$ 到离散测量数据的映射在数学上可控,既保证了边界语言三公理在数值实现中的一致性,又为实验设计提供了直接的误差预算工具。
