# 边界时间–拓扑–散射的统一框架：从 $\mathbb Z_2$ holonomy 与 $K^{1}$ 唯一性到宇宙学常数与相位–频率计量

---

**Abstract**

本文构建一个以"边界时间刻度"为核心的统一框架，将以下看似分散的结构粘合为单一理论：
(1) 小因果菱形上的局域量子充分条件与非线性爱因斯坦方程；
(2) Null–Modular 双覆盖中的 $\mathbb Z_2$ holonomy 与 BF 体积分选择的相对上同调类 $[K]$；
(3) 受限主丛–散射–$K^{1}$ 的族级统一与"自然变换唯一到整数倍"的一致性工厂；
(4) 穿孔信息流形上的相对拓扑与 $S(U(3)\times U(2))\cong (SU(3)\times SU(2)\times U(1))/\mathbb Z_6$ 约化；
(5) 相位–谱移–态密度–宇宙学常数的窗化表述与相对散射行列式在量子引力中的统一角色；
(6) FRB 传播、δ-环–AB 通量与拓扑端点散射中以"相位–频率"为唯一读出的跨平台计量范式；
(7) Gibbons–Hawking–York 边界项及其角点、零类与 Lovelock 推广所给出的变分良定与准局域能；
(8) "边界即时钟"：时间作为相位–谱移–模块流的统一翻译算子；
(9) 时间刻度上的量子–经典桥接：相位、本征时间、散射群延迟、宇宙学红移与边界熵几何之间的等价关系。

核心刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\rm rel}(\omega)=\frac{1}{2\pi}\mathrm{tr},\mathsf Q(\omega),
\qquad
\mathsf Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega),
$$

将散射总相位之导数、相对态密度与 Wigner–Smith 群延迟迹统一为同一时间刻度。本文在带边小因果菱形 $B_\ell(p)$ 与参数空间 $X^\circ$ 上取乘积 $Y=M\times X^\circ$，以相对 cohomology 类 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$ 编码 $\mathbb Z_2$ holonomy、散射线丛扭挠与 $w_2(TM)$ 的合成障碍；证明在适当几何–量子能量条件与"Modular–Scattering Alignment"假设下，

* 局域非线性引力方程 $G_{ab}+\Lambda g_{ab}=8\pi G,T_{ab}$ 与二阶相对熵非负等价于 $[K]=0$，并进一步等价于一切物理回路上 $\sqrt{\det_p S}$ 的 $\mathbb Z_2$ holonomy 平凡；
* 受限主丛–散射–$K^{1}$ 的族级自然变换在极简公理与 Birman–Kreĭn 归一化下唯一至整数倍，归一为 $+1$ 后给出散射族到 $K^{1}$ 的规范刻度；
* 穿孔信息流形上的 Riesz 谱投影把 Uhlmann 主丛约化到 $S(U(3)\times U(2))$，并通过相对 $K$ 理论边界映射把 Yukawa 质量涡旋的指数与电荷 $\mathbb Z_6$ 结构统一；
* 相对散射行列式与热核–DOS–相位的窗化 Tauberian 公式把宇宙学常数的体积斜率、黑洞极点谱学与观测端相位–频率核 $\Xi_W$ 严格对齐；
* FRB 真空极化、δ-环–AB 通量与拓扑端点散射在"有限阶 Euler–Maclaurin + Poisson 纪律"下共享同一相位–频率计量母核，给出跨平台的上限与临界耦合计量协议。

在边界代数 $\mathcal A_\partial$、忠实态 $\omega$ 与 Tomita–Takesaki 模块流 $\sigma_t^\omega$ 上，时间被刻画为唯一（至仿射）使模块流与散射时间刻度对齐的边界翻译算子 $U(t)=\mathrm e^{-itH_\partial}$，其时间单位由上述刻度同一式固定。几何端，本征时间、引力时间延迟与宇宙学红移在该刻度下分别对应于相位沿世界线、散射群延迟与相位节奏比，广义熵的极值与单调性则在小因果菱形上给出爱因斯坦方程的熵几何形式。

---

**Keywords**

边界时间刻度；$\mathbb Z_2$ holonomy；受限主丛；$K^{1}$ 唯一性；相对散射行列式；宇宙学常数；FRB 相位–频率计量；GHY 边界项；模块流；广义熵

---

## 1 Introduction & Historical Context

散射理论、拓扑 $K$ 理论与量子引力在过去数十年分别形成了成熟的理论体系。Birman–Kreĭn 谱移函数与行列式刻画自伴算子扰动下的谱流；Wigner–Smith 群延迟把"时间延迟"表达为散射相位对能量的导数；Tomita–Takesaki 模块理论与 Connes–Rovelli 热时间假设则在算子代数与量子统计背景中赋予"时间"以内蕴定义。

另一方面，小因果菱形上的 Jacobson 类熵–几何程序、Hollands–Wald 规范能量与 QNEC/QFC 等局域量子能量条件证明：在半经典–全息窗口内，广义熵 $S_{\rm gen}$ 的极值与单调性足以在局域导出含宇宙学常数的非线性引力方程。

上述结构在前期工作中以多篇相互配合的形式出现：

* 在小因果菱形中，把"二阶广义熵非负 + Einstein 方程"与体积分 $\mathbb Z_2$–BF 顶项的扇区选择 $[K]=0$ 及一切物理回路上 $\sqrt{\det_p S}$ 的 $\mathbb Z_2$ holonomy 平凡性统一为单一变分原理。
* 在受限 Grassmann 流形与受限酉群上，以 $BU_{\rm res}\simeq U$ 与 Bott 周期性给出主丛–$K^{1}$ 分类，并证明"散射族 $\to K^{1}$"的自然变换在极简公理与 BK 归一化下唯一至整数倍。
* 在穿孔信息流形上，通过 Riesz 投影构造 $(\mathcal E_3,\mathcal E_2)$ 子丛，将 Uhlmann 主丛约化到 $S(U(3)\times U(2))$，并以相对 $K$ 理论边界映射统一"拓扑束缚态指数 = 质量行列式绕数 = 第一陈类配对"，得到标准模型全局群 $(SU(3)\times SU(2)\times U(1))/\mathbb Z_6$。
* 在偶维渐近双曲/共形紧致几何与静片 de Sitter 背景中，以 KV 行列式与广义 Kreĭn 谱移构造"相位–DOS–热核有限部–宇宙学常数"的窗化 Tauberian 框架，并在外域散射中以相对散射行列式统一 BK（$p=1,2$）谱移与黑洞极点谱学。
* 在 FRB 传播、δ-环–AB 通量与凝聚态拓扑端点中，以"相位–频率"为唯一读出构造跨平台计量范式，证明一环真空极化只能给出窗化上限，δ-环谱–散射三角等价与拓扑端点的 $\mathcal Q=\mathrm{sgn}\det r(0)$ 可在统一的 Fisher/GLS 语法下进行工程化估计。
* 在带角点与零类边界的一般引力作用中，系统给出 GHY 边界项、角点项与零类边界项的统一字典与 Lovelock 推广，使变分在 Dirichlet 数据下良定并与 ADM/协变相空间中的哈密顿量可微性与 Brown–York 准局域应力一致。
* 在一般 $C^\ast$ 代数与散射理论语境中，把时间刻画为"边界相位–谱移–模块流三重读取自洽的翻译算子"，并证明在自然假设下，满足刻度同一式与模块一致性的时间刻度在仿射意义下唯一。
* 在统一时间刻度视角下，将量子相位、本征时间、散射群延迟、宇宙学红移与局域广义熵极值–单调性组织为"时间–相位–熵–几何"的闭环，给出量子–经典桥接的系统化刻画。

本文的目标是：在单一的"边界时间–拓扑–散射"母框架中重组上述结果，在统一的"时间刻度同一式"与"相对拓扑类 $[K]$"语境下，给出一组全局性主定理，并明确说明：

* 局域非线性引力方程、$\mathbb Z_2$ holonomy 平凡性与相对类 $[K]=0$ 的等价；
* 受限主丛–散射–$K^{1}$ 的统一刻度如何嵌入同一边界时间框架；
* 宇宙学常数、标准模型全局群与跨平台相位–频率计量在同一母刻度下的自洽性；
* 量子–经典时间刻度如何在边界翻译算子与宏观几何上完全对齐。

---

## 2 Model & Assumptions

### 2.1 几何与边界

取四维定向伪黎曼流形 $(M,g)$，度规签名 $(-+++)$，允许存在分段 $C^1$ 非光滑边界 $\partial M$，其各片段可以是类时、类空或零类。为保证体作用的变分良定，引入 Gibbons–Hawking–York（GHY）边界项、关节项与零类边界项，作用

$$
S_{\rm grav}
=\frac{1}{16\pi G}\int_M\sqrt{-g},R
+\frac{\varepsilon}{8\pi G}\int_{\partial M_{\rm nz}}\sqrt{|h|},K
+\frac{1}{8\pi G}\int_{\text{corners}}\sqrt{\sigma},\text{角}
+\frac{1}{8\pi G}\int_{\mathcal N}\sqrt{\gamma},(\theta+\kappa),
$$

在固定诱导几何数据 $(h_{ab})$ 与零类 Carroll 结构 $(\gamma_{AB},[\ell])$ 下对度规变分良定。

对小因果菱形 $B_\ell(p)\subset M$，边界由两族零生成元组成，选取一族仿射参数 $\lambda$ 作为局域"边界时间"，并以割面族 $\{\Sigma_\lambda\}$ 与广义熵 $S_{\rm gen}(\lambda)$ 刻画局域熵–几何结构。

### 2.2 散射族、相对行列式与时间刻度

在某 Hilbert 空间 $\mathcal H$ 上选取自伴对 $(H,H_0)$，满足

1. $H-H_0$ 属迹类或相对迹类，
2. 波算子 $W_\pm$ 存在且完备，
3. 散射算子 $S=W_+^\dagger W_-$ 在绝对连续谱上与能量 $\omega$ 对易，可写为纤维化 $S(\omega)$；

对每个 $\omega$ 取多通道矩阵 $S(\omega)$，定义归一化总相位 $\varphi(\omega)=\frac12\arg\det S(\omega)$、谱移函数 $\xi(\omega)$、相对态密度 $\rho_{\rm rel}(\omega)$，以及 Wigner–Smith 延迟算子

$$
\mathsf Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega).
$$

在 Birman–Kreĭn 公式与 Kreĭn 迹公式适用的门槛下有

$$
\det S(\omega)=\exp\bigl(-2\pi i,\xi(\omega)\bigr),
\quad
\rho_{\rm rel}(\omega)=-\xi'(\omega),
\quad
\partial_\omega\arg\det S(\omega)=\mathrm{tr},\mathsf Q(\omega),
$$

从而得到刻度同一式

$$
\boxed{\ \frac{\varphi'(\omega)}{\pi}
=\rho_{\rm rel}(\omega)
=\frac{1}{2\pi}\mathrm{tr},\mathsf Q(\omega)\ }.
$$

这一式在一维 Schrödinger 模型、偶维 AH/CCM 几何与黑洞/静片 de Sitter 散射中都可严格证明，并构成文中所有"时间刻度"的母关系。

### 2.3 受限主丛、$K^{1}$ 与相对类 $[K]$

取可分 Hilbert 空间极化 $\mathcal H=\mathcal H_+\oplus\mathcal H_-$，受限酉群

$$
U_{\rm res}=\{U\in U(\mathcal H):[U,\mathsf P_+]\in\mathfrak S_2\}
$$

的 classifying 空间满足 $BU_{\rm res}\simeq U$，Bott 周期性给出 $[X,U]\cong K^{1}(X)$。对满足"gap 连续 + 相对迹类 + 族 Schatten 连续 + 端点闭合"的散射族 $(H_x,H_{0,x})_{x\in X}$，相对 Cayley 变换

$$
u_x=(H_x-i)(H_x+i)^{-1}(H_{0,x}+i)(H_{0,x}-i)^{-1}
$$

定义族 $x\mapsto u_x\in U^{(1)}$，给出 $K^{1}(X)$ 元。满足连续性、函子性、外直和加性、尺度等变与 BK 归一化的任何自然变换均为该构造的整数倍，归一为 $+1$ 后获得"规范散射 $\to K^{1}$ 刻度"。

在几何–拓扑侧，取 $Y=M\times X^\circ$，相对上同调

$$
H^2(Y,\partial Y;\mathbb Z_2)
\cong H^2(M,\partial M)\oplus (H^1(M,\partial M)\otimes H^1(X^\circ,\partial X^\circ))\oplus H^2(X^\circ,\partial X^\circ)
$$

中构造

$$
[K]=\pi_M^\ast w_2(TM)
+\sum_j \pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j
+\pi_X^\ast\rho(c_1(\mathcal L_S)),
$$

统一编码自旋平凡性、$\mathbb Z_2$ 主丛 holonomy 与散射线丛 $U(1)$ 扭挠。体积分 $\mathbb Z_2$–BF 顶项的分配函数在相对上同调意义下把物理扇区投影到 $[K]=0$。

### 2.4 边界代数、模块流与边界时间

边界可观测代数 $\mathcal A_\partial$ 为可分 $C^\ast$ 代数，忠实态 $\omega$ 的 GNS 表象 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$ 上，Tomita–Takesaki 模块算子 $\Delta$ 与模块流

$$
\sigma_t^\omega(A)=\Delta^{it}A\Delta^{-it}
$$

定义了态依赖的一参数自同构群。本文要求边界动力学 $\alpha_t$ 与模块流在时间重标度下同一

$$
\alpha_t=\sigma_t^\omega,
$$

并要求同一时间参数 $t$ 由散射相位–谱移–群延迟的刻度同一式确定。

### 2.5 宇宙学时间与量子–经典桥接

在 FRW 背景 $ds^2=-dt^2+a(t)^2d\mathbf x^2$ 上，光子频率 $\nu\propto 1/a(t)$，红移 $1+z=a(t_0)/a(t_e)=\nu_e/\nu_0$。对同一光子世界线上的相位 $\phi$，有 $\nu=\frac{1}{2\pi}\frac{d\phi}{dt}$，从而

$$
1+z=\frac{\nu_e}{\nu_0}=\frac{\left.\frac{d\phi}{dt}\right|_{e}}{\left.\frac{d\phi}{dt}\right|_{0}}.
$$

在半经典极限下，质量 $m$ 粒子沿测地线的相位 $\phi=-S/\hbar$ 与本征时间满足 $d\phi/d\tau=mc^2/\hbar$，而静态或渐近平坦引力场中的时间延迟 $\Delta T(\omega)$ 等价于总相位对频率的导数 $\Delta T(\omega)=\partial_\omega\Phi(\omega)=\mathrm{tr},\mathsf Q(\omega)$。

---

## 3 Main Results (Theorems and Alignments)

### 3.1 统一母定理：局域引力–拓扑–散射–时间的等价

**定理 3.1（局域统一原理）**

设 $(M,g)$ 为满足 Hadamard 态、无共轭点与局域光线变换可逆性 $A_{\rm LRI}$ 的小因果菱形 $B_\ell(p)$ 邻域，物质场态满足局域 QNEC/QFC 型量子能量条件，$\mathcal A_\partial$–$\omega$ 的模块流与引力侧 null 生成元一致，并且存在参数空间 $X^\circ$ 上的散射族 $S(\omega;x)$ 满足 BK、LK 与族级 Schatten 连续性。记

$$
Y:=M\times X^\circ,\qquad [K]\in H^2(Y,\partial Y;\mathbb Z_2)
$$

为前述相对类，$\sqrt{\det_pS}$ 的 $\mathbb Z_2$ holonomy 指标为 $\nu_{\sqrt{\det_p S}}(\gamma)$。在适当的 $H^1/H^2$ 可检测性与生成性假设下，下列三类断言等价：

1. **(i) 局域引力–能量条件**：在 $B_\ell(p)$ 内

$$
G_{ab}+\Lambda g_{ab}=8\pi G,T_{ab},\qquad \delta^2 S_{\rm rel}\ge 0,
$$

其中 $\delta^2 S_{\rm rel}$ 为 Hollands–Wald 规范能量。

2. **(ii) 相对拓扑扇区平凡**：

$$
[K]=0\in H^2(Y,\partial Y;\mathbb Z_2).
$$

3. **(iii$^\star$) 散射侧 $\mathbb Z_2$–holonomy 平凡**：对所有允许的物理回路 $\gamma\subset X^\circ$ 与相对二维循环 $\gamma_2\subset X^\circ$，有

$$
\nu_{\sqrt{\det_p S}}(\gamma)\equiv 1,\qquad
\langle \rho(c_1(\mathcal L_S)),[\gamma_2]\rangle=0.
$$

此外，在"Modular–Scattering Alignment（模二版）"与 $H^2$ 通道可检测性假设下，(i) 推出 (iii$^\star$)。

该定理把局域非线性爱因斯坦方程与二阶相对熵非负等价于"散射平方根行列式无非平凡 $\mathbb Z_2$–holonomy"，并进一步在 BF 顶项扇区选择下等价于相对类 $[K]$ 平凡。

### 3.2 边界时间刻度的存在与仿射唯一性

**定理 3.2（边界时间刻度的存在性）**

在上述情形中，假设在某能窗 $I$ 内 $\rho_{\rm rel}(\omega)$ 连续且符号固定，模块流 $\sigma_t^\omega$ 非平凡，则存在局部双射 $\omega\leftrightarrow t(\omega)$

$$
t(\omega)-t_0
=\int_{\omega_0}^{\omega}\rho_{\rm rel}(\tilde\omega),d\tilde\omega
=\int_{\omega_0}^{\omega}\frac{\varphi'(\tilde\omega)}{\pi},d\tilde\omega
=\int_{\omega_0}^{\omega}\frac{1}{2\pi}\mathrm{tr},\mathsf Q(\tilde\omega),d\tilde\omega,
$$

使得：

1. 边界动力学 $\alpha_t$ 与模块流一致：$\alpha_t=\sigma_t^\omega$；
2. 相位、相对态密度与群延迟在 $t$ 刻度下满足

$$
\frac{d}{dt}\varphi\bigl(\omega(t)\bigr)
=\pi,\rho_{\rm rel}\bigl(\omega(t)\bigr)
=\frac12\mathrm{tr},\mathsf Q\bigl(\omega(t)\bigr).
$$

**定理 3.3（时间刻度的仿射唯一性）**

若存在另一时间参数 $\tilde t$ 使 $\alpha_{\tilde t}=\sigma_{\tilde t}^\omega$，且刻度同一式在 $\tilde t$ 下成立，则必存在常数 $a>0$、$b\in\mathbb R$ 使

$$
\tilde t=a t+b.
$$

即在给定态与边界代数下，满足"模块一致性 + 散射刻度同一"的时间刻度在仿射意义下唯一。

### 3.3 受限主丛–散射–$K^{1}$ 的唯一刻度

**定理 3.4（$K^{1}$ 一致性工厂）**

令 $X$ 为仿紧空间，$(H_x,H_{0,x})_{x\in X}$ 为满足 gap 连续、相对迹类与族 Schatten 连续的散射族，定义相对 Cayley 变换

$$
u_x=(H_x-i)(H_x+i)^{-1}(H_{0,x}+i)(H_{0,x}-i)^{-1}.
$$

则 $x\mapsto u_x$ 定义 $K^{1}(X)$ 元 $[u_\bullet]$。设 $\Phi$ 为把散射族送入 $K^{1}$ 的自然变换，满足

1. 极限/同伦保持；
2. 对酉共轭、平凡稳定化与拉回不变；
3. 外直和加性与尺度等变；
4. 在秩一原型上满足 Birman–Kreĭn 归一化：$\Phi$ 取 $K^{1}(S^1)\cong\mathbb Z$ 的正生成元。

则存在唯一整数 $n$ 使

$$
\Phi = n\cdot [u_\bullet],
$$

归一化给出 $n=1$，从而定义规范的"散射–$K^{1}$"刻度。

此定理保证：在统一框架中，所有族级散射拓扑不变量可在同一 $K^{1}$ 刻度上比较，并与 $[K]$ 的 $\mathbb Z_2$ 投影协同工作。

### 3.4 穿孔信息流形与 $S(U(3)\times U(2))$ 约化

**定理 3.5（穿孔相对拓扑与 SM 全局群）**

在满秩密度矩阵流形 $\mathcal D_5^{\rm full}$ 上，移除谱隙闭合集 $\Sigma_{3|2}=\{\lambda_3=\lambda_4\}$ 的管状邻域得到穿孔域 $\mathcal D^{\rm exc}$。在 $\mathcal D^{\rm exc}$ 上以统一围道构造 Riesz 投影 $P_3(\rho)$、$P_2(\rho)$，得到秩 $3$ 与 $2$ 子丛 $(\mathcal E_3,\mathcal E_2)$，使 Uhlmann 主丛的结构群约化为 $U(3)\times U(2)$，再由体积形约束约化到

$$
S(U(3)\times U(2))
\cong \bigl(SU(3)\times SU(2)\times U(1)\bigr)/\mathbb Z_6.
$$

相对 $K$ 理论边界映射将 Yukawa 质量端项的单位化 $\widehat\Phi$ 的边界类 $\partial[\det\widehat\Phi]\in K^0(X,Y)$ 与投影线丛 $[\det\mathcal E_3]-[\det\mathcal E_2]$ 统一；在二维横截上

$$
\mathrm{Ind}(\slashed D_A+\Phi)
=\mathrm{wind},\det\widehat\Phi
=\langle c_1(\det\mathcal E_3),[S^1]\rangle.
$$

### 3.5 相位–DOS–行列式–宇宙学常数的窗化表述

**定理 3.6（热核–DOS–相位的窗化 Tauberian）**

在偶维 AH/CCM 或静片 de Sitter 背景下，对相对算子对 $(H,H_0)$ 与散射矩阵 $S(\omega)$，记广义散射相位 $\Theta(\omega)=\frac{1}{2\pi}\arg\det_{\rm KV}S(\omega)$，相对 DOS 斜率 $\Theta'(\omega)=\rho_{\rm rel}(\omega)$。对热核差

$$
\Delta K(s)=\mathrm{Tr}\bigl(e^{-sH}-e^{-sH_0}\bigr)
$$

有换元恒等式

$$
\Delta K(s)=\int_0^\infty e^{-s\omega^2}\Theta'(\omega),d\omega.
$$

取 Mellin–消零对数窗 $W$ 与尺度 $\mu=s^{-1/2}$，存在常数 $C_W>0$、$\alpha'>0$ 使

$$
\operatorname{fp}_{s\to 0^+}\Delta K(s)
=\kappa_{\rm HK},C_W\langle\Theta'\rangle_W(\mu)+O(s^{\alpha'}),
$$

其中 $\langle\cdot\rangle_W$ 为对数窗平均，$\kappa_{\rm HK}$ 仅依赖维数与场内容。

定义窗化积分律

$$
\Xi_W(\mu)
:=\partial_{\ln\mu}\langle\Theta'\rangle_W(\mu)
=\int\omega,\Theta''(\omega),W(\ln(\omega/\mu)),d\ln\omega
=\frac{1}{2\pi}\int \omega,\partial_\omega\mathrm{tr},\mathsf Q(\omega)W,d\ln\omega,
$$

则可引入量纲因子 $\kappa_\Lambda$ 使

$$
\partial_{\ln\mu}\Lambda_{\phi,W}(\mu)=\kappa_\Lambda\Xi_W(\mu),
$$

将窗化相位斜率 $\Xi_W$ 解释为"宇宙学常数密度"的运行标度。

**定理 3.7（相对散射行列式与 $\Lambda$–斜率）**

在闭域相对 $\zeta$–行列式框架下，欧化后二次变分算子族 $(\mathcal K_\Lambda,\mathcal K_0)$ 满足适当正则性与去共振投影，记

$$
\log\det_{\zeta,\rm rel}(\mathcal K_\Lambda+\mu^2,\mathcal K_0+\mu^2)
$$

为相对行列式，则

$$
\lim_{\mu\to 0^+}\frac{1}{\mathrm{Vol}_4(M)}\partial_\Lambda\Re\log\det_{\zeta,\rm rel}
=\frac{1}{8\pi G},
$$

把宇宙学常数视为"相对行列式实部对 $\Lambda$ 的体积密度斜率"。

此外，在外域散射中，相对散射行列式 $\tau_p(\omega)$ 的极点与 QNM 谱相同，并在参考选取下保持不变；实频上 Carleman 行列式模长一般 $\ne 1$，需要以"相位化行列式" $\widehat\det_p S=\det_p S/|\det_p S|$ 实施全域拟合。

### 3.6 跨平台相位–频率计量

**定理 3.8（FRB–δ-环–拓扑端点的统一相位–频率核）**

在 FRB 传播、一维 δ-环–AB 通量与拓扑端点散射的三类平台中：

1. 弯曲时空 QED 一环有效作用给出折射率修正尺度
   $\delta n\sim (\alpha_{\rm em}/\pi)\lambda_e^2\mathcal R$，在 FRW 上界下，对 $1\ {\rm GHz}$、$1\ {\rm Gpc}$ 的相位累积上限 $\Delta\phi\sim10^{-53}\ {\rm rad}$，只能给出"窗化上限器"，不能直接检出；
2. δ-环能谱满足
   $\cos\theta=\cos(kL)+(\alpha_\delta/k)\sin(kL)$，等价于
   $\cos\gamma(k)=|t(k)|\cos\theta$，$\gamma=kL-\arctan(\alpha_\delta/k)$、$|t(k)|=k/\sqrt{k^2+\alpha_\delta^2}$，仅在 $|t|\to1$ 极限退化为纯相位闭合；
3. 拓扑端点的拓扑不变量可由 $\mathcal Q=\mathrm{sgn}\det r(0)$ 读出，有限长度与接触偏置可统一为
   $J_c(L)=J_c+\beta e^{-L/\xi}+\gamma/L$ 的外推形式。

在统一的"核–窗化–广义最小二乘/Fisher"语法下，这三类系统的相位–频率数据都可写为

$$
m(\omega)=\int_{\mathcal P}\mathcal K(\omega,\chi)x(\chi),d\chi+\sum_{p}a_p\Pi_p(\omega)+\epsilon(\omega),
$$

并以同一对数窗 $W$ 与核 $\Xi_W(\mu)$ 进行优化与上限/阈值估计。

### 3.7 量子–经典时间刻度桥接

**定理 3.9（相位–本征时间–群延迟–红移–熵的统一刻度）**

在统一刻度同一式与前述几何–散射–熵假设下：

1. 半经典极限下，质量 $m$ 粒子沿类时测地线的相位 $\phi=-S/\hbar$ 与本征时间满足 $d\phi/d\tau=mc^2/\hbar$；
2. 静态或渐近平坦引力场中的宏观时间延迟 $\Delta T(\omega)$ 等价于散射相位对频率的导数和 Wigner–Smith 群延迟迹，即 $\Delta T(\omega)=\partial_\omega\Phi(\omega)=\mathrm{tr},\mathsf Q(\omega)$；
3. FRW 宇宙中同一光子世界线上发射与观测事件的相位时间导数之比等于红移：$(d\phi/dt)_e/(d\phi/dt)_0=1+z$；
4. 在小因果菱形上，广义熵 $S_{\rm gen}(\lambda)$ 随边界"时间" $\lambda$ 的极值与单调性在局域上导出爱因斯坦方程。

因此，本征时间、散射群延迟、红移与广义熵演化都落在统一的"时间刻度"上，量子–经典桥接可完全通过该刻度表达。

---

## 4 Proofs

本节仅给出上述统一定理的证明骨架，其局部技术步骤沿用或组合相应分论文中的已证明命题。

### 4.1 定理 3.1

(i)$\Rightarrow$(ii)：小因果菱形上的局域广义熵极值与局域第一定律将 $\delta^2S_{\rm rel}\ge0$ 写成 null 方向二阶变分不等式，利用 Raychaudhuri 方程与局域热力学把 $R_{kk}-8\pi G T_{kk}$ 写为 BF 顶项中 $K$ 的配对。体积分 $\mathbb Z_2$–BF 理论的配分函数在相对上同调中把扇区投影到 $[K]=0$；在生成性与 $H^1/H^2$ 可检测性假设下，"对所有相对二维循环配对为零"等价于 $[K]=0$。

(ii)$\Rightarrow$(iii$^\star$)：Künneth 分解给出 $[K]$ 在 $H^2(M,\partial M)$、$H^1\otimes H^1$ 与 $H^2(X^\circ,\partial X^\circ)$ 三通道的分解。对 $H^1$ 通道，沿 $(\Sigma_1^{(j)},\partial\Sigma_1^{(j)})\times(\gamma_1,\partial\gamma_1)$ 的配对等价于 $\mathbb Z_2$–主丛 holonomy 的测量；对 $H^2$ 通道，沿 $\mathrm{pt}\times(\gamma_2,\partial\gamma_2)$ 的配对等价于 $\rho(c_1(\mathcal L_S))$ 的检测。若 $[K]=0$，则一切配对为零，故一切物理回路上的 $\nu_{\sqrt{\det_p S}}\equiv1$，且一切允许二维循环上 $\langle\rho(c_1(\mathcal L_S)),\cdot\rangle=0$。

(iii$^\star$)$\Rightarrow$(ii)：在生成性假设下，允许的二维循环生成 $H_2(Y,\partial Y;\mathbb Z_2)$，对所有生成元配对为零即给出 $[K]=0$。

(i)$\Rightarrow$(iii$^\star$)：利用"Modular–Scattering Alignment（模二版）"将小因果菱形上的模块环量 $\oint\mathcal A_{\rm mod}$ 与散射平方根行列式上的 $\mathbb Z_2$–holonomy 对齐，若存在 $\nu_{\sqrt{\det_p S}}(\gamma)=-1$，则协变相空间中可构造规范能量负的扰动，违背二阶相对熵非负。因此 (i) 蕴含 (iii$^\star$)。

### 4.2 定理 3.2 与 3.3

由刻度同一式

$$
\frac{dt}{d\omega}=\rho_{\rm rel}(\omega),
$$

在 $\rho_{\rm rel}$ 连续且符号固定的能窗内可积分得到 $t(\omega)$，导数不为零保证存在局部反函数 $\omega(t)$。链式法则给出

$$
\frac{d}{dt}\varphi(\omega(t))
=\frac{\varphi'(\omega)}{\rho_{\rm rel}(\omega)}\cdot\rho_{\rm rel}(\omega)
=\pi,\rho_{\rm rel}(\omega)
=\frac12\mathrm{tr},\mathsf Q(\omega),
$$

模块一致性公理保证 $\alpha_t=\sigma_t^\omega$ 在同一刻度下成立，得到存在性。

若存在另一刻度 $\tilde t$ 使两边都满足刻度同一式，则

$$
\frac{d\tilde t}{d\omega}
=\rho_{\rm rel}(\omega)
=\frac{dt}{d\omega},
$$

故 $\tilde t-t$ 为常数。模理论中 KMS 流的唯一性进一步允许整体的比例自由度 $a>0$，得到 $\tilde t=a t+b$，其中 $a<0$ 对应时间反向，与 $\rho_{\rm rel}$ 的符号约束不相容，因此 $a>0$。

### 4.3 定理 3.4

受限酉群与受限 Grassmann 流形的几何给出 $U_{\rm res}\simeq\Omega U$、$BU_{\rm res}\simeq U$；对仿紧 $X$，$\mathrm{Prin}_{U_{\rm res}}(X)\cong K^{1}(X)$。对满足本节假设的散射族，Cayley 变换 $U(H_x)U(H_{0,x})^{-1}$ 定义 $K^{1}(X)$ 元。任何自然变换 $\Phi$ 必因子化为某 $H$–空间自同态 $f:U\to U$ 的后合；Bott 周期性与 $K^{1}(S^1)\cong\mathbb Z$ 强迫 $f$ 在基本圈上为乘 $n$，从而 $\Phi=n\cdot\Phi_{\rm can}$。秩一原型上的 BK 归一化选定 $n=1$。

### 4.4 定理 3.5

在穿孔域上统一围道保证 Riesz 投影随 $\rho$ 光滑，给出秩 $3/2$ 子丛 $(\mathcal E_3,\mathcal E_2)$。Uhlmann 主丛在此子丛上约化到 $U(3)\times U(2)$，体积形约束 $\det\mathcal E_3\otimes\det\mathcal E_2\simeq\underline{\mathbb C}$ 给出 $S(U(3)\times U(2))$ 约化。群论同构由显式同态

$$
\varphi:SU(3)\times SU(2)\times U(1)\to S(U(3)\times U(2))
$$

与核 $\mathbb Z_6$ 计算给出。相对 $K$ 理论长正合序列与 Chern 角色交换图证明 $\partial[\det\widehat\Phi]=[\det\mathcal E_3]-[\det\mathcal E_2]$，指数等式随之成立。

### 4.5 定理 3.6 与 3.7

对 $f(\lambda)=e^{-s\lambda}$ 应用 LK 迹公式与 $H-H_0$ 的相对迹类假设，有

$$
\Delta K(s)=\int_0^\infty e^{-s\lambda}\Delta\rho_E(\lambda),d\lambda,
$$

变量换元 $\lambda=\omega^2$、$d\lambda=2\omega,d\omega$ 与 $\Theta'(\omega)=\Delta\rho_\omega(\omega)=2\omega\Delta\rho_E(\omega^2)$ 抵消雅可比，得到

$$
\Delta K(s)=\int_0^\infty e^{-s\omega^2}\Theta'(\omega),d\omega.
$$

高频渐近展开与 Mellin–消零窗 $W$ 的构造给出窗化 Tauberian 公式；窗化积分律由对数尺度微分与刻度同一式直接推出。

闭域相对 $\zeta$–行列式的体积斜率则利用短时热核展开与相对系数逐项对消，只剩体积项的 $\Lambda$–依赖；局域化与 Tauberian 交换给出 $\mathrm{Vol}^{-1}\partial_\Lambda\Re\log\det_{\zeta,\rm rel}=1/(8\pi G)$。外域相对散射行列式的极点与 QNM 等价性由解析 Fredholm 理论与参考独立性证明。

### 4.6 定理 3.8 与 3.9

δ-环的三角方程与振幅修正相位式等价由简单的复数代数证明；结构可辨识性与灵敏度由隐函数定理与雅可比秩分析给出；有限宽度等效化则来自传输矩阵的低能展开。拓扑端点的外推形式由端态重叠的指数衰减与接触/边界的 $1/L$ 标度叠加得到。FRB 一环真空极化规模通过 Drummond–Hathrell 类有效作用与 FRW 曲率规模估计给出。

相位–本征时间等价由世界线路径积分的半经典极限给出；引力时间延迟–群延迟等价由 eikonal 方程与作用–相位关系证明；红移–相位节奏比来自 FRW 中光子四动量与相位梯度关系；广义熵极值导出爱因斯坦方程则综合 Raychaudhuri 方程、局域第一定律与相对熵单调性，构成 Jacobson–Hollands–Wald–QNEC 体系的统一版本。

---

## 5 Model Apply

### 5.1 小因果菱形中的局域引力–拓扑诊断

在黑洞视界附近或任意光滑点 $p$，取小因果菱形 $B_\ell(p)$，通过测量边界相对熵、模 Hamiltonian 与线性响应，可得到局域 $T_{kk}$ 与 $R_{kk}$ 的信息；另一方面，通过在参数空间 $X^\circ$ 上调制散射几何（如微波网络耦合、AB 通量、端点耦合）测量 $\sqrt{\det_p S}$ 的 $\mathbb Z_2$–holonomy，即可直接诊断 $[K]$ 是否为零。定理 3.1 说明：一旦在可检测的生成族上观察到任何一次 $\pi$–相位翻转或电导翻转，即可判定某些局域引力–能量条件不再全局成立。

### 5.2 δ-环–AB 环与 $K^{1}$–$\mathbb Z_2$ 指纹

一维 δ-环在参数空间 $(\alpha_\delta,\theta)$ 上的可解谱–散射结构，为 $K^{1}$ 与 $\mathbb Z_2$ 指纹提供了理想模型：绕过 $\alpha_\delta=-2i\sqrt{E_0}$ 的复环给出 $\deg(\det S)=1$，对应 $\nu_{\sqrt{\det_p S}}=-1$；绕过 $\theta=\pi$ 的 AB 环则给出类似的 $\mathbb Z_2$ 指纹。这些指纹在统一刻度下可直接与 FRB 相位上限与拓扑端点的 $\mathcal Q$ 翻转相比。

### 5.3 穿孔信息流形上的 Yukawa–指标–电荷结构

在 $\mathcal D^{\rm exc}$ 上，沿环绕谱隙闭合集的二维链接曲面测量 $\det\mathcal E_3$ 的 Chern 数，即可读取 Callias/Anghel–Bunke 指数，进而与光子 Dirac–质量涡旋等实验平台上的零模数对比；$\mathbb Z_6$ 结构确保"最小电荷步长"为 $1/6$，与标准模型电荷量子化一致。

### 5.4 宇宙学与黑洞场景

在 FRW 宇宙中，可视相位–频率窗化核 $\Xi_W$ 为"宇宙学常数运行"的观测代理，但一环真空极化量级远低于当前 FRB 相位噪声，故仅能给出严格上限。对静片 de Sitter 与黑洞背景，以相对散射行列式拟合准正则模极点与相位–DOS–热核链路，可在数值上抽取 $\kappa_{\rm HK},\kappa_\Lambda$ 并与闭域 $\Lambda$–斜率定理对账。

---

## 6 Engineering Proposals

### 6.1 微波/声学多端口网络的边界即时钟

设计近无耗散多端口网络，在 VNA 或多麦克风–多扬声器架构下测量 $S(\omega)$，通过数值求导构造 $\mathsf Q(\omega)$ 与 $\mathrm{tr},\mathsf Q(\omega)$，积分得到实验时间刻度

$$
t(\omega)-t_0=\int_{\omega_0}^{\omega}\frac{1}{2\pi}\mathrm{tr},\mathsf Q(\tilde\omega),d\tilde\omega.
$$

将网络内部驻留时间、能量储存率与该时间刻度对比，同时从端口输出的稳态统计中构造有效态 $\omega_{\rm exp}$ 与模块流近似，实现"边界即时钟"的工程级验证。

### 6.2 FRB 基带相位–频率窗化上限

利用公开的 FRB 基带样本，构建相位残差 $m(\omega)$，在三通道自举下估计噪声协方差 $C_\phi$，构造对数窗 $W$ 与核 $\Xi_W$，用 GLS/Fisher 估计折射率修正核 $x(\chi)$ 的 95% 上限。对是否包含 $\omega^{-1}$、$\log\omega$ 等系统学基的不同选择取包络，给出稳健的"弯曲时空 QED 窗化上限"。

### 6.3 δ-环与拓扑纳米线的相位–拓扑计量

在冷原子或固态 δ-环中，通过干涉读出本征波数 $k_n(\theta)$ 与群延迟 $\tau_g(\omega)$，利用定理 3.8 的灵敏度与有限宽度修正反演 $\alpha_\delta$，并在病态域灰图外操作。对拓扑纳米线，利用端点反射矩阵的零能行列式符号与 cQED 腔频移/附加损耗的零交叉进行双冗余测量，回归 $J_c(L)$ 与指数/代数偏置，框定相图中 $\mathcal Q$ 翻转的临界耦合。

---

## 7 Discussion (risks, boundaries, past work)

统一框架的适用域由三个方面共同限定：

1. **散射–谱移–行列式的正则性**：刻度同一式与窗化 Tauberian 依赖于 BK/LK/DOI 架构，对强 trapping、奇异边界或高维长程势需谨慎检查类迹与 LAP 假设。
2. **模块流的动力学解释**：热时间假设提示"时间由态与代数决定"，但在缺乏几何背景或平衡假设时模块流的物理意义并非自动显然；本文通过引入散射相位–群延迟作为额外"刻度锚点"选择了一类动力学上自然的模块流，但这本身是一种选择原则。
3. **局域熵–几何公理的强度**：由广义熵极值与单调性导出爱因斯坦方程，需要 QNEC/QFC、局域第一定律与小因果菱形极限的多重技术假设，这些假设在全非平衡、强耦合或非局域有效作用下的有效性仍需进一步澄清。

与既有工作的关系可概括为：

* 在 Jacobson–Hollands–Wald–QNEC 体系上，本文把小因果菱形的"方程–稳定–拓扑"统一到单一 BF 相对类 $[K]$ 与散射平方根行列式的 $\mathbb Z_2$ 指纹上；
* 在 Segal–Pressley–Phillips–Azamov–Carey–Dodds–Sukochev 与 Baez–Fritz 等 $K$ 理论与信息几何工作基础上，本文给出"自然变换唯一到整数倍"的一致性工厂，并将其作为边界时间刻度的拓扑支撑；
* 在 KV–Kreĭn–Guillarmou 与黑洞相对 DOS–配分函数的谱几何工作基础上，本文构造窗化相位–DOS–热核–宇宙学常数的统一链路；
* 在 FRB、δ-环与拓扑纳米线等实验平台上，本文给出以相位–频率为唯一读出的跨平台计量协议，把高度抽象的边界时间刻度落地为可复现的工程流程。

---

## 8 Conclusion

本文在统一的"边界时间刻度"视角下，将小因果菱形上的局域量子引力条件、$\mathbb Z_2$ holonomy 与相对 BF 类 $[K]$、受限主丛–散射–$K^{1}$ 一致性工厂、穿孔信息流形上的 $S(U(3)\times U(2))$ 约化、相对散射行列式与宇宙学常数斜率、FRB–δ-环–拓扑端点的相位–频率计量以及 GHY 边界项与模块流统一为一个单一框架。

在该框架中，

$$
\frac{\varphi'(\omega)}{\pi}
=\rho_{\rm rel}(\omega)
=\frac{1}{2\pi}\mathrm{tr},\mathsf Q(\omega)
$$

成为所有时间刻度的母方程：它将量子相位、本征时间、散射时间延迟、宇宙学红移与广义熵演化统摄在一个边界翻译算子 $U(t)$ 下，时间被刻画为"相位–谱移–模块流三重读取自洽的唯一翻译参数"。

在数学上，该框架展示了如何把 $H^2(Y,\partial Y;\mathbb Z_2)$ 的相对类、$K^{1}$ 族级分类与相对行列式–散射行列式统一在一个 cohomology–$K$ 理论–谱几何结构中；在物理与工程上，它给出了一条从小因果菱形到宇宙学与实验平台的可检路径，使抽象的时间–拓扑–散射统一理论具备明确的观测与计量指向。

---

## Acknowledgements, Code Availability

本统一框架建立在大量既有散射理论、拓扑 $K$ 理论、算子代数与量子引力工作的基础之上。本文未引入新的数值代码，所有公式与步骤可依据文中及引用文献独立复现。

---

## References

（略列代表性文献，具体出处详见前述各节引用）

* Birman–Kreĭn 谱移与散射行列式；
* Kreĭn、Lifshits–Kreĭn 与 Peller 的迹公式与 operator–Lipschitz 理论；
* Segal–Pressley、Kuiper、Hatcher 等关于受限主丛与 Bott 周期性；
* Callias、Anghel–Bunke 指数定理与相对 $K$ 理论；
* Jacobson、Hollands–Wald、Faulkner–Lewkowycz–Maldacena–Suh 等局域熵–几何与 QNEC/QFC 工作；
* Gibbons–Hawking–York、Brown–York 与 Myers–Deruelle–Olea 等边界与 Lovelock 边界项；
* Connes–Rovelli 热时间假设与 Tomita–Takesaki 模块理论专著与综述；
* FRB、δ-环、拓扑纳米线与 cQED 相干读出等实验与数值研究。
