## ——窗化群延迟、红移与光速的公理化理论、接口纲要与非渐近误差闭合(完整版)

**Version: 3.14** (Critical Revision: ℏ Factor Correction & Reviewer-Requested Enhancements)

## 摘要

在"宇宙 = 广义光结构(Generalized Light Structure, GLS)""观察者 = 滤镜链(windowed compression → CP 通道 → POVM → 阈值计数)""因果 = 类光锥偏序"的**双层并行框架**中,建立以
$$
\boxed{\ \frac{\varphi'(E)}{2\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad \mathsf Q(E)=-i\,S(E)^\dagger \tfrac{dS}{dE}(E)\ }
$$
为母刻度(相位导数—相对态密度—Wigner–Smith 群延迟迹)的公理化理论。核心结果:(i)以**窗化群延迟读数** $T_\gamma[w_R,h]$ 提供时间的操作化刻度（**注意：$T_\gamma$ 是 $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 的带内线性读数，并非前沿时间 $t_*$；窄带/共振下可取负值；二者仅在§3.4的高频平台极限下一致**），并证明其串并联可加、规范协变/相对不变(当 $U,V$ 与能量无关或 $\det U\cdot\det V\equiv1$ 时保持不变);在**单通道**($N=1$)真空纯延迟 $S(\omega)=e^{-i\omega L/c}$ 且归一化 $\int (w_R*\check h)=2\pi$ 的情形,窗化群延迟读数给出 $T_\gamma=L/c$(可用以**标定** $c$);Nyquist 条件仅保证该读数的离散实现**无别名误差**,两者层级不同;(ii)以谱缩放刻画**红移**并证明与时间的互易标度律;(iii)以真空**前沿**规范光速 $c$,给出任意物理通道的**前沿下界**与**无超锥传播**;(iv)**在 §4 的前提 (i)、(ii′)、(iii)、(iv) 内**(LTI+Hardy 因果、局域与被动性、加强版高频真空极限)给出**高频标定桥接**(§3.4):任意固定形状归一窗的蓝移极限 $\lim_{E_0\to\infty}T_\gamma= t_*$,从而把因果前沿 $t_*$ 作为 $T_\gamma$ 的**可操作极限刻度**;并提出**因果前沿层($t_*$)与操作化群延迟层($T_\gamma$)的双层并行框架**,给出从 GLS 到因果流形的接口骨架;(v)在同一账本中统一**波/粒二象性**与双缝的窗化互补不等式 $D^2+V^2\le 1$;(vi)阐明"分辨率提升 = 宇宙膨胀(红移放大)"的严格对偶,并给出 Nyquist–Poisson–Euler–Maclaurin(NPE)**有限阶**误差闭合与工程化处方。理论全程采用算子—测度—函数语言(Toeplitz/Berezin 压缩 $K_{w,h}$,读数 = 对谱测度的线性泛函),在全局幺正公设下将一切时间/密度读数统一由 $\mathsf Q=-iS^\dagger S'$ 定义,实验性非幺正均通过幺正扩张 $\widehat S$ 回推母刻度。

---

## Notation & Axioms / Conventions

### 单位与常数规范

默认采用 $\hbar=1$(必要时亦可取 $c=1$)。若 $c$ 未取为 1,则需按 $L/c$ 恢复光程量纲。

**主变量约定与量纲互换**：**全文以 $\omega$（角频率）为主自变量**。在 $\hbar=1$ 下，$E$ 与 $\omega$ 数值相等。恢复 SI 单位时：

- **$\omega$ 变量**：$\mathsf Q_\omega(\omega)=-iS^\dagger(\omega)\tfrac{dS}{d\omega}(\omega)$，量纲为**时间**；
- **$E$ 变量**：$\mathsf Q_E(E)=-iS^\dagger(E)\tfrac{dS}{dE}(E)$，且
$$
\boxed{\ \mathsf Q_E(E)=\frac{1}{\hbar}\,\mathsf Q_\omega(\omega),\quad E=\hbar\omega\ }.
$$

**量纲与读数**：
- 以 $\omega$ 为自变量时，$(2\pi)^{-1}\operatorname{tr}\mathsf Q_\omega$ 的量纲为**时间**，读数 $T$ 直接为秒；
- 以 $E$ 为自变量时，$(2\pi)^{-1}\operatorname{tr}\mathsf Q_E$ 的量纲为 $1/\text{能量}$，相应物理时间为
$$
\boxed{\ T_{\rm phys}=\hbar\,T_E\ }.
$$
且有**测度不变式**
$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\omega\,d\omega
\;=\;
\frac{1}{2\pi}\operatorname{tr}\mathsf Q_E\,dE.
$$

本文算例与主证明默认采用 $\omega$ 变量，并按"傅里叶规范"统一常数因子（$\int(w_R*\check h)=2\pi$）。

**术语对齐**:本文中"时间"如无特别说明,指因果时间 $t_*$;$T_\gamma[w_R,h]$ 称为窗化群延迟读数或操作化时间刻度。

**Standing Assumption A (母刻度语境)**:本文采用**有限维幺正散射矩阵**的代数语境。假设在工作带内 $S(E)\in C^1\cap\mathsf{U}(N)$（$N$ 为有限通道数）。**母刻度关系**
$$
\boxed{\ \rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\ }
$$
在此语境下作为**等价定义**成立：定义 $\xi(E):=-\tfrac{1}{2\pi i}\log\det S(E)$（取主值分支），则 $\rho_{\rm rel}(E)=-\xi'(E)$；反之，由 $\mathsf Q(E)=-iS^\dagger(E)S'(E)$ 的迹与行列式导数的关系 $\operatorname{tr}(A^{-1}A')=(\log\det A)'$ 即得上述等式。此定义无需诉诸无限维谱移函数理论的相对可追踪等抽象假设，直接在 $\mathsf{U}(N)$ 的李群微分几何中成立。

> **注**：若需处理无限维算子或连续谱，可采用Birman–Kreĭn谱移函数定理的完整版本（需相对可追踪等标准假设），届时上述关系升格为定理。本文聚焦可实现器件网络，故统一采用有限维语境。

### 卡片 I（刻度同一｜全局幺正公设）

**公设（全局幺正）**：宇宙视作封闭系统;存在以能量 $E$ 为坐标的绝对连续谱区间,在本工作带内散射矩阵 $S(E)\in C^1\cap\mathsf U(N)$ 幺正。根据Standing Assumption A，母刻度关系
$$
\rho_{\rm rel}(E):=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad \mathsf Q(E)=-i\,S^\dagger(E)S'(E)
$$
等价于相位导数定义 $\rho_{\rm rel}(E)=-\xi'(E)$，其中 $\xi(E):=-\tfrac{1}{2\pi i}\log\det S(E)$（主值分支）。
我们据此**定义**相位测度 $\mu_\varphi$:令
$$
 d\mu_\varphi^{\rm ac}(E):=\rho_{\rm rel}(E)\,dE,
$$
等价写作
$$
\boxed{\,\frac{\varphi'(E)}{2\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\xi'(E)\,}.
$$
此处 $\varphi$ 为实现该密度的相位函数,其符号仅随 $\rho_{\rm rel}$ 而定。**需要强调：除特殊情形外,$\rho_{\rm rel}$ 可取正可取负,故 $\mu_\varphi$ 一般为符号测度（signed measure），并不对应任何物理态的能谱测度。**

**处方（开放子系统的幺正扩张规约）**：任何实验性损耗/增益均视作对环境自由度的迹出;理论分析统一通过幺正扩张 $\widehat S(E)$ 处理,并以 $\mathsf Q(\widehat S)=-i\widehat S^\dagger\widehat S'$ 评估全部时间/密度读数。实际读数对可访问通道 $\mathcal C$ 采用块迹/压缩,**可验证等价式**为
$$
T_{\mathcal C}[w_R,h]=-\int (w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\big(P_{\mathcal C}\,(-i\widehat S^\dagger \widehat S')\,P_{\mathcal C}\big)\,dE,
$$
或用 Toeplitz/Berezin 压缩 $\operatorname{Tr}(K_{w,h}\cdot)$ 实现,仅计算可观测子空间。

**扩张依赖性与规约（关键）**：$\widehat S$ 的幺正扩张不唯一，环境子空间的能量依赖基变换会改变可见块的读数。为保证读数的可比性与可复现性，**必须采用以下两条规约之一**：

**(A) 高频规约扩张**：规定采用满足以下条件的幺正扩张类 $\{\widehat S\}$：
  - 前沿因子化后的剩余部分 $\widehat S_0(\omega)=e^{i\omega t_*}\widehat S(\omega)$ 在高频极限下一致趋于单位矩阵：$\lim_{|\omega|\to\infty}\widehat S_0(\omega)=I$；
  - 可见–环境交叉块在高频上一致趋零：$\lim_{|\omega|\to\infty}\|P_{\mathcal C}\widehat S_0(\omega)P_{\mathcal C}^\perp\|=0$。

  在此规约下，高频平台法（§3.4）的极限 $\lim_{E_0\to\infty}T_{\mathcal C}[w_R(\cdot-E_0),h]=t_*$ 对所有满足规约的扩张一致成立，从而 $t_*$ 具有不变量意义。

**(B) 相对量为主报**（**工程强烈推荐**）：对无法保证扩张类一致性的实验，或无法验证级联兼容性（Assumption B）或规范协变拓扑项的场景，规定**主报相对量**
$$
\boxed{\ T_{\rm rel}:=T_{\mathcal C}[w_R,h;S]-T_{\mathcal C}[w_R,h;S_{\rm ref}]\ },
$$
其中 $S_{\rm ref}$ 为标准参考通道（如校准用纯延迟或真空链路）。**相对量自动消除**：
- 环境规约依赖（扩张路径的非唯一性）；
- 规范协变中的拓扑项（净绕数偏置，§3.2）；
- 级联可加性的环境旁路耦合误差（§3.2 Assumption B；若两链对同一参考均可测）。

**特别适用于跨器件/跨实验对比，无需验证交叉块范数或绕数分支。** 报告时需声明 $S_{\rm ref}$ 的选取及其前沿时间 $t_*({\rm ref})$。

**明确约定**：下文涉及开放子系统的 $T_{\mathcal C}[w_R,h]$ 绝对量时，默认已采用规约(A)或在同一扩张类内对比；**跨扩张类的绝对量对比无物理意义**。实验报告中建议优先使用 $T_{\rm rel}$。

**$\mathsf Q$ vs $\widetilde{\mathsf Q}$**:本文不引入 $\widetilde{\mathsf Q}:=-iS^{-1}S'$。两者在幺正 $S$ 时有 $\operatorname{tr}\mathsf Q=\operatorname{tr}\widetilde{\mathsf Q}$,但在"子系统可见"的非幺正有效描述下,$\mathsf Q$ 的**幺正扩张路径**更自然地对接块迹/压缩。

**警示**：对开放子系统的有效散射矩阵 $S_{\mathcal C}$ 通常非幺正,直接代入 $-iS_{\mathcal C}^{-1}S_{\mathcal C}'$ 不可取；本文一律通过幺正扩张 $\widehat S$ 与块迹/Toeplitz 压缩计算可访问时标。

### 卡片 II(有限阶 EM 与带限正则性)

一切离散—连续换算与窗化读数遵循 NPE 三分解
$$
\varepsilon_{\rm total}=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$

**正则性前提（严格带限保证）**：本文的严格带限场景要求 $\widehat w,\widehat h\in C_c^{M+1}(\mathbb R)$（紧支撑、$M+1$ 阶连续可微，$M$ 为 Euler–Maclaurin 所用阶数），使得：
- $\widehat h$ 为紧支撑有界乘子，$\mathrm{supp}\,\widehat h\subset[-\Omega_h,\Omega_h]$；
- $\widehat w$ 同理，$\mathrm{supp}\,\widehat w\subset[-\Omega_w,\Omega_w]$。

在此前提下，卷积 $\widehat g=\widehat h\cdot\widehat{\rho_{\rm rel}}$ 的支撑被 $\widehat h$ 截断，从而 $f(E)=w_R(E)[h\!\star\!\rho_{\rm rel}](E)$ 属于 Paley–Wiener 类 $\mathsf{PW}_B\cap L^1$（$B=\Omega_h+\Omega_w/R$）。

零心母窗 $w_R(E)=w(E/R)$ 的频域支撑为 $\mathrm{supp}\,\widehat{w_R}\subset[-\Omega_w/R,\Omega_w/R]$（其中 $\Omega_w$ 为母窗 $w$ 的带宽）。平移窗 $w_R(E-E_c)$ 仅改变相位，支撑宽度不变。因此若采样间隔
$$
\Delta\le \frac{\pi}{\Omega_h+\Omega_w/R},
$$
则 $\varepsilon_{\rm alias}=0$（Nyquist–Shannon，**精确等式**）。

**近带限回退**：若仅为近带限（如高斯窗、指数衰减窗），$\varepsilon_{\rm alias}$ 保留为可估上界的残差项，必须回退到附录B的NPE三分解估计；$\varepsilon_{\rm EM}$ 由**有限阶** Euler–Maclaurin(端点伯努利层与显式余项)控制;$\varepsilon_{\rm tail}$ 由窗外衰减控制。

**工程常用窗的适用性警示**：工程常用的 **Kaiser、Blackman–Harris** 等窗在本文变量规范下（能量域/时间域有紧支撑）其**傅里叶像通常不满足频域严格带限**（存在旁瓣衰减），属于**近带限**场景。此类窗应按**附录B的NPE三分解估计误差**（$\varepsilon_{\rm alias},\varepsilon_{\rm EM},\varepsilon_{\rm tail}$），而非套用严格带限的精确等式 $\varepsilon_{\rm alias}=0$。

**误差尺度提示**：在近带限常用窗核下，误差主尺度**通常**受最靠近实轴的奇性控制（参见附录B的上界模板）。此提示为经验性指导，非无条件定理。([维基百科][2])

### 记号约定

约定 $(h\star f)(E):=(h*f)(E)$,其中 $\check h(E):=h(-E)$,星号表示对能量变量的卷积。

**零心母窗约定**：窗族采用**零心母窗** $w_R(E)=w(E/R)$（$w$ 以原点为中心），其中 $w$ 为偶函数且 $w\in L^1\cap C^M$（$M$ 为 Euler–Maclaurin 所用阶数）。**需要平移时显式标注**：如 $w_R(E-E_c)$ 表示窗心位于 $E_c$ 的窗函数。核 $h$ 亦取 $h\in L^1\cap C^M$,具体归一方式在上下文另行说明。

> **记号澄清**：采用零心母窗避免"二次平移"歧义。例如，§3.4的平移窗族定义为 $F_{E_c}(\omega):=(w_R*\check h)(\omega-E_c)$，其中 $w_R(E)=w(E/R)$ 不含预设平移，$E_c$ 为扫描中心频率。

**傅里叶规范**: $\widehat f(\omega):=\displaystyle\int_{\mathbb R} f(E)\,e^{-i\omega E}\,dE$, $f(E)=\displaystyle\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\omega)\,e^{i\omega E}\,d\omega$。在此规范下,Nyquist 条件 $\Delta\le \pi/(\Omega_h+\Omega_w/R)$ 与附录 B 的 Poisson 公式中 $2\pi$ 因子与相位约定一致。

$S(E)\in\mathsf U(N)$:多通道散射矩阵,$\mathsf Q=-iS^\dagger S'$。$\quad$ $\rho_{\rm rel}=-\xi'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q$。$\quad$ 窗—核:零心母窗 $w_R(E)=w(E/R)$,前端核 $h$。$\quad$ 压缩 $K_{w,h}$:Toeplitz/Berezin 型。**引理 0.1(刻度同一的迹—谱移关系)** 由 $\det S(E)=e^{-2\pi i\xi(E)}$ 与 $\mathsf Q=-iS^\dagger S'$ 可得 $\tfrac{d}{dE}\log\det S(E)=-2\pi i\,\xi'(E)$ 和 $\operatorname{tr}\mathsf Q(E)=-i\,\tfrac{d}{dE}\log\det S(E)$,从而 $(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)=-\xi'(E)$。([arXiv][1])

---

## 1. GLS 与滤镜链

### 1.1 对象层

**定义 1.1(GLS)** 设
$$
\mathfrak U=(\mathcal H,\ S(E),\ \mu_\varphi,\ \mathcal W),
$$
其中 $d\mu_\varphi^{\rm ac}=(\varphi'/(2\pi))\,dE$,$\mathcal W$ 为可实施窗—核字典。任意态 $\rho$ 的窗化读数为
$$
\mathrm{Obs}(w_R,h;\rho)=\operatorname{Tr}(K_{w,h}\rho)
=\!\int_{\mathbb R}\! w_R(E)\,[\,h\!\star\!\rho_\rho\,](E)\,dE\;+\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$
其中 $\rho_\rho(E):=\dfrac{d\mu_\rho^{\rm ac}}{dE}$ 为态 $\rho$ 相对于 Lebesgue 测度 $dE$ 的能谱密度;而 $\rho_{\rm rel}(E):=-\xi'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$ 属于通道/散射数据。

**层级警示（态层 vs 通道层）**：
本节 $\mathrm{Obs}(w_R,h;\rho)$ 是对**态测度** $\mu_\rho$ 的窗化读数,依赖输入态 $\rho$。第 §3.1 定义的 $T_\gamma[w_R,h]$ 则是对**母测度** $\mu_\varphi$(密度 $\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$)的窗化读数,仅依赖通道 $S$。二者**处于不同层**：除非另行声明,$\mathrm{Obs}(w_R,h;\rho)\neq T_\gamma[w_R,h]$。特别地,$\rho_{\rm rel}$ 一般为符号密度,并非任何物理态的能谱密度,因而通常不存在"参考态"使 $d\mu_\rho^{\rm ac}=\rho_{\rm rel}\,dE$。

### 1.2 操作语法:滤镜链

**定义 1.2(滤镜链)** 一次观测流程
$$
\boxed{\ \mathcal O=\mathcal M_{\rm th}\circ \{M_i\}\circ \Phi\circ K_{w,h}\ }
$$
以 $K_{w,h}$ 定位带宽与几何,$\Phi$ 表示耦合/退相干(CP),$\{M_i\}$ 为 POVM 读出基,$\mathcal M_{\rm th}$ 将通量阈值化为 clicks。Born 概率与最小 KL 投影一致化见 §10。([Google 图书][4])

---

## 2. 因果流形的内生

### 2.1 上半平面解析性(Hardy) ⇒ 单向支撑与偏序

取上半平面 Cauchy 变换
$$
m(z)=\int_{\mathbb R}\frac{d\mu_\varphi(E)}{E-z},
$$
其中 $\mu_\varphi$ 由卡片 I 定义。为应用 Paley–Wiener/Titchmarsh 与 Kramers–Kronig,本稿在 §2–§4 假设 $\mu_\varphi$ 绝对连续,且 $\rho_{\rm rel}\in L^2(\mathbb R)$,于是
$$
m(z)=\int_{\mathbb R}\frac{d\mu_\varphi(E)}{E-z}\in H^2(\mathbb C^+).
$$
若实验性非幺正引入的奇异贡献不可忽略,统一并入幺正扩张 $\widehat S$ 的环境自由度而不计入 $\mu_\varphi$ 的奇异部分。在 LTI 与因果假设下,Paley–Wiener/Titchmarsh 与 Kramers–Kronig–Hilbert 关系推出时域冲激响应 $g(t)$ 的单向支撑(规范后 $t\ge 0$)及实/虚部的 Hilbert 共轭。**本文关于"解析性 $\Rightarrow$ 单向支撑"的结论仅针对各链的频域传递算子** $T_\gamma(\omega)$（或 $S(\omega)$ 的矩阵元）**在 $\mathbb C^+$ 的 Hardy 解析性**；**$m(z)$ 是相位测度的 Cauchy 变换，仅用于描述 $\log\det S$ 的相位—测度关系，不可误作系统传函再用 Hardy 理论推因果性**。

**定义 2.1(可达预序)** 设链集合 $\Gamma(x,y):=\{\gamma:x\to y\}$。定义前沿时间与几何量
$$
t_*(\gamma):=\inf\{\,t:\,g_\gamma(t;L)\neq 0\,\},\qquad
\tau(x,y):=\inf_{\gamma\in\Gamma(x,y)} t_*(\gamma),\qquad
L_*(x,y):=\inf_{\gamma\in\Gamma(x,y)} L(\gamma).
$$
约定:当 $\Gamma(x,y)=\varnothing$ 时,$\tau(x,y)$ 与 $L_*(x,y)$ 记为 $+\infty$,且关系 $x\preceq y$ **不成立**。据此定义可达预序
$$
\boxed{\ x\preceq y\;\Longleftrightarrow\;\Gamma(x,y)\neq\varnothing\ }.
$$

**约定(恒等链)** 对每个 $x$,$\Gamma(x,x)$ 包含恒等链 $e_x$,规定 $L(e_x)=0$,$g_{e_x}(t;0)=\delta(t)$,故 $t_*(e_x)=0$。于是 $\tau(x,x)=0=L_*(x,x)/c$,自反性由定义立即得到。

**假设(无闭因果回路)**:不存在 $x\neq y$ 使得 $x\preceq y$ 且 $y\preceq x$。

**命题 2.2(偏序性)** 在"无闭因果回路"条件下,$\preceq$ 为偏序。

*证明*:自反性来自恒等链 $e_x$,即 $\Gamma(x,x)\ni e_x$ 非空;传递性由链拼接给出:若 $\Gamma(x,y)\neq\varnothing$ 且 $\Gamma(y,z)\neq\varnothing$,则存在拼接链 $\gamma=\gamma_{z\leftarrow y}\circ\gamma_{y\leftarrow x}\in\Gamma(x,z)$,故 $\Gamma(x,z)\neq\varnothing$;反对称性由"无闭因果回路"给出。□

窗化群延迟读数 $T_\gamma[w_R,h]$ 是相位导数的频域加权读数,没有与前沿时间 $t_*(\gamma)$ 的一般大小比较关系。

### 2.2 相位奇性 ⇒ 最短到达与因果边界

de Branges 相位的跳变/极点(Hermite–Biehler 零点、散射相移突变)对应到达奇性(驻相/等时集),为光锥边缘提供可检峰值标记。([普渡大学数学系][6])

---

## 3. 操作化时间刻度:窗化群延迟读数

### 3.1 定义

下述 $T_\gamma[w_R,h]$ 为相位导数的带内读数,用作时间刻度的操作化读数,并非前沿时间 $t_*$。

**通道层定义（channel-only）**：
$T_\gamma[w_R,h]$ 定义为对母测度 $\mu_\varphi$ 的线性配对,因此是 $S$ 的泛函,与输入态无关；实验上通过测量 $S$(或其相位导数)或 §3.4 的高频平台法加以标定。

**定义 3.1(窗化群延迟读数)** 对因果可达的传播—读出链 $\gamma$ 与窗—核 $(w_R,h)$,定义
$$
\boxed{\ T_\gamma[w_R,h]\;:=\;-\int_{\mathbb R} (w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\gamma(E)\,dE\ },\qquad \check h(E):=h(-E),
$$
并约定 $(h\star f)(E)=(h*f)(E)$（$\star$即卷积）。等价地,
$$
T_\gamma[w_R,h]=-\int_{\mathbb R} w_R(E)\,[\,h\!\star\!\rho_{\rm rel}\,](E)\,dE.
$$
（等价性来自 $\int (f*g)h=\int f\,(g^{\vee}*h)$ 与 $(h^{\vee})^{\vee}=h$ 的卷积对偶恒等式。）

**符号约定**：定义中的负号采用**工程/因果号记** $S(\omega)=e^{-i\omega\tau}$（正延迟 $\tau>0$），使得 $\mathsf Q=-iS^\dagger S'=-\tau<0$，从而 $T_\gamma=+\tau>0$ 直接对应物理飞行时间。这与母刻度 $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 的符号测度性质相容。

此量在母刻度上实现"带内时间"的可实现读数。**本文默认采用 $\int_{\mathbb R}(w_R*\check h)=2\pi$ 的归一化,以便在**单通道**($N=1$)真空纯延迟链路 $S(\omega)=e^{-i\omega L/c}$ 上直接读出 $T_\gamma=L/c$**；多通道时可取每模平均 $T_\gamma/N$。

**关于符号测度与负读数（关键警示）**：$(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 为相位导数的带内密度，非态密度，因而一般为**符号测度**（signed measure）。由此得到的窗化读数 $T_\gamma[w_R,h]$ **在窄带/共振下可取负值**，反映带内相位斜率与色散特性，并**不**定义因果时间。**本文不主张 $T_\gamma\ge t_*$ 的一般不等式**；二者无普适大小关系。**因果与无信号**由**前沿** $t_*$ 与类光锥偏序决定（§4）。在§3.4的前提下，蓝移极限给出 $T_\gamma\to t_*$，故 $t_*$ 是 $T_\gamma$ 的可操作极限刻度而非其逐频带下界。

**归一化处方($2\pi$)**：
$$
\int_{\mathbb R}(w_R*\check h)=\Big(\int_{\mathbb R}w_R\Big)\Big(\int_{\mathbb R}h\Big)=2\pi.
$$
鉴于 $\int w_R=R\!\int w$,可取 $\int h=2\pi/(R\!\int w)$(或对 $w_R,h$ 同时作幅度重标),从而对任意 $R$ 与窗形均保持 $\int(w_R*\check h)=2\pi$。**该 $2\pi$ 与本文"傅里叶规范"（见"记号约定"一节）保持一致**，在不同傅里叶约定下需相应调整常数因子。

**为何采用 $2\pi$？** 这一归一化使得在**单通道真空纯延迟** $S(\omega)=e^{-i\omega L/c}$ 时
$$
-\frac{1}{2\pi}\int (w_R*\check h)(E)\,\operatorname{tr}\mathsf Q(E)\,dE=-\frac{1}{2\pi}\int (w_R*\check h)(E)\cdot \Big(-\frac{L}{c}\Big)\,dE = \frac{L}{c},
$$
从而把 $T_\gamma$ 标定到几何量 $L/c$（或 $\hbar L/(\hbar c)$）。任何其它归一化只差一个**已知常数因子**,但 $2\pi$ 最便于跨实验对比。

**统一记号（同一窗算子,对不同测度配对）**：
记 $\mathcal T_{w_R,h}[\mu]:=\int_{\mathbb R} (w_R*\check h)(E)\,d\mu(E)$。则 $T_\gamma[w_R,h]=\mathcal T_{w_R,h}[\mu_\varphi]$(通道层),$\mathrm{Obs}(w_R,h;\rho)=\mathcal T_{w_R,h}[\mu_\rho]$(态层)。本文关于可加性、规范协变、HF 桥接、红移标度律等主命题均指 $\mathcal T_{w_R,h}[\mu_\varphi]$。

**警示（多通道平台值）**：**在多通道系统**（$N>1$）中，$T_\gamma$ 的高频平台值为 $Nt_*$（总时延），而**每模平均** $\overline T_\gamma$ 的平台值为 $t_*$（几何前沿）。**跨实验对比或标定几何前沿时，推荐使用** $\overline T_\gamma$。详见§3.4。

**多通道 N 不变定义**：为便于多通道器件网络直接套用,可采用每模平均的并行刻度
$$
\boxed{\ \overline T_\gamma[w_R,h]\;:=\;-\int_{\mathbb R} (w_R*\check h)(E)\,\frac{1}{2\pi}\,\frac{1}{N}\operatorname{tr}\mathsf Q_\gamma(E)\,dE\ },\qquad \int_{\mathbb R}(w_R*\check h)=2\pi.
$$
其中 $N$ 指**可访问子空间的维度** $N_{\rm eff}:=\mathrm{rank}\,P_{\mathcal C}$；若读全通道则 $N=N_{\rm phys}$。在单通道($N=1$)下 $\overline T_\gamma=T_\gamma$；对应的前沿分解与平台极限为
$$
\overline T_\gamma=t_*-\frac{1}{2\pi}\int_{\mathbb R}(w_R*\check h)(E)\,\frac{1}{N}\operatorname{tr}\mathsf Q_0(E)\,dE,\qquad
\lim_{E_0\to\infty}\overline T_\gamma=t_*.
$$

**一致口径提示**：**若关注几何前沿**而非总时延,推荐直接使用 $\overline T_\gamma$；无论通道数 $N$ 为何值,**平台极限统一为 $t_*$**（而非 $Nt_*$）。

窗化群延迟读数与前沿时间 $t_*$ 的桥接见 §3.4。后续关于采样与 NPE 的一切公式均作用于被积函数
$$
f(E):=w_R(E)\big[h\!\star\!\rho_{\rm rel}\big](E),
$$
并以该 $f$ 为误差估计的唯一对象。([chaosbook.org][7])

### 3.2 串并联可加、规范协变

**定理 3.2(可加性,幺正散射)** 设在 $w_R$ 的带内 $S_j^\dagger(E)S_j(E)=I\ (j=1,2)$。若 $\gamma=\gamma_2\circ\gamma_1$,则
$$
\operatorname{tr}\mathsf Q_{\gamma_2\circ\gamma_1}
=\operatorname{tr}\mathsf Q_{\gamma_2}+\operatorname{tr}\mathsf Q_{\gamma_1},\qquad
T_{\gamma_2\circ\gamma_1}[w_R,h]=T_{\gamma_2}[w_R,h]+T_{\gamma_1}[w_R,h].
$$
*证明*:由 $(S_2S_1)'=S_2'S_1+S_2S_1'$ 得 $\mathsf Q(S_2S_1)=S_1^\dagger\mathsf Q(S_2)S_1+\mathsf Q(S_1)$;取迹用循环不变性即得第一式;代入定义得第二式。

*备注(幺正版)*:由**卡片 I(刻度同一｜全局幺正公设)**可知任意串/并联网络可视为单一幺正扩张 $\widehat S$ 的块构造,故 $\operatorname{tr}\mathsf Q$ 与 $T_\gamma[w_R,h]$ 的可加性在幺正框架内直接成立,无需其他替代处方。

**Assumption B (级联兼容性，开放子系统的可加性前提)**：对**开放子系统**的块压缩情形，"先串接再压缩"是否等于"先压缩再相加"取决于环境自由度的耦合结构。具体要求：

设两链的幺正扩张为 $\widehat S_1, \widehat S_2$，可见投影为 $P_{\mathcal C}$。若级联 $\gamma=\gamma_2\circ\gamma_1$ 对应 $\widehat S=\widehat S_2\widehat S_1$，则块压缩的可加性
$$
T_{\mathcal C}[\gamma_2\circ\gamma_1]=T_{\mathcal C}[\gamma_2]+T_{\mathcal C}[\gamma_1]
$$
**成立的充分条件**是：可见投影与环境块满足**无寄生旁路的可交换性**，即
$$
P_{\mathcal C}\,\widehat S_2\,(I-P_{\mathcal C})\approx 0,\qquad
(I-P_{\mathcal C})\,\widehat S_1\,P_{\mathcal C}\approx 0,
$$
（在窗支撑频带内近似为零）。此条件保证环境自由度不在两链间建立"旁路耦合"，从而块迹满足乘法性。

*证明提纲*：在级联兼容性下，
$$
\operatorname{tr}\big(P_{\mathcal C}\widehat{\mathsf Q}\,P_{\mathcal C}\big)
\approx \operatorname{tr}\big(P_{\mathcal C}\widehat{\mathsf Q}_2\,P_{\mathcal C}\big)
+\operatorname{tr}\big(P_{\mathcal C}\widehat{\mathsf Q}_1\,P_{\mathcal C}\big),
$$
其中近似误差由交叉块的范数上界控制。

**可操作误差界（实验可验证）**：
$$
\big|T_{\mathcal C}[\gamma_2\!\circ\!\gamma_1]-T_{\mathcal C}[\gamma_2]-T_{\mathcal C}[\gamma_1]\big|
\ \le\ C\,\sup_{\omega\in{\rm supp}(w_R*\check h)}\Big(|P_{\mathcal C}\widehat S_2P_{\mathcal C}^\perp|+|P_{\mathcal C}^\perp\widehat S_1P_{\mathcal C}|\Big),
$$
其中 $C$ 仅依赖窗-核面积与带宽常数（$C\sim \int|w_R*\check h|\cdot\mathrm{diam}(\mathrm{supp})$）。

若不满足该条件或无法验证交叉块范数，**强烈建议统一使用相对读数** $T_{\rm rel}$（卡片I方案B），自动消除环境依赖项与规范项。([chaosbook.org][7])

**命题 3.3(规范协变与相对不变)** 设能量依赖基变换 $S\mapsto U(E)SV(E)$,则
$$
\operatorname{tr}\mathsf Q(USV)=\operatorname{tr}\mathsf Q(S)-i\,\operatorname{tr}(U^\dagger U')-i\,\operatorname{tr}(V'V^\dagger).
$$
*推导要点(算子级)*:
$$
\mathsf Q(USV)=V^\dagger\mathsf Q(S)V-i\,V^\dagger S^\dagger\big(U^\dagger U'\big)SV-i\,V^\dagger V'.
$$
取迹并利用循环不变性即可得到上述恒等式。规范项对时间读数的影响为
$$
\Delta T=-\int (w_R*\check h)(E)\,\frac{1}{2\pi}\Big(\partial_E\arg\det U+\partial_E\arg\det V\Big)\,dE.
$$

**相对不变的充要条件**：$\Delta T=0$（即 $\operatorname{tr}\mathsf Q$ 在窗化读数层面保持不变）当且仅当
$$
\boxed{\ \partial_E\big(\arg\det U(E)+\arg\det V(E)\big)\equiv 0\ \text{在}\ \mathrm{supp}(w_R*\check h)\ \text{上}\ }.
$$
特别地，当 $U,V$ 与能量无关，或 $\det U(E)\det V(E)\equiv 1$（恒定模幺正），上述条件自动满足。

**拓扑项：净绕数校正**：若 $\arg\det U$ 或 $\arg\det V$ 存在分支切换（如 $2\pi$ 相位跳变），定义**窗内净绕数**
$$
w_{\rm net}:=\frac{1}{2\pi}\int_{\mathrm{supp}(w_R*\check h)}\partial_E\arg\det U\,dE\in\mathbb Z,
$$
（$\arg\det V$ 的绕数类似定义）。此时 $\Delta T$ 包含拓扑整数偏置，**不应解释为物理延迟**。

**数值实现与报告规约（强制要求）**：
- 选择连续分支计算 $\arg\det U$；若遇跳变，**必须报告净绕数** $w_{\rm net}$ 并**在主报的绝对时标中剔除拓扑偏置** $w_{\rm net}\cdot\frac{1}{N}\int(w_R*\check h)$；
- **跨实验/跨器件对比一律采用相对读数**：
$$
T_{\rm rel}(\gamma):=T_\gamma[w_R,h;S]-T_\gamma[w_R,h;S_{\rm ref}],
$$
其中 $S_{\rm ref}$ 为标准参考（如校准用纯延迟）。**相对量自动消除规范项与拓扑偏置**，无需手动扣除 $w_{\rm net}$。
消除规范项。**若只能辨识到等价类 $S\sim USV$,则以相对读数 $T_{\rm rel}$ 为物理量;对应地,$\rho_{\rm rel}$ 与 $\mu_\varphi$ 也只在此等价类下定义到加性常数。**([普渡大学数学系][6])

**命题 3.4(能量重参数化协变性)** 令 $E=E(\varepsilon)$ 为单调 $C^1$ 同胚,记 $S_\varepsilon(\varepsilon):=S(E(\varepsilon))$。则
$$
\mathsf Q_\varepsilon(\varepsilon)=-iS_\varepsilon^\dagger \frac{dS_\varepsilon}{d\varepsilon}
=E'(\varepsilon)\,\mathsf Q_E(E(\varepsilon)),\qquad
\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\varepsilon(\varepsilon)\,d\varepsilon
=\frac{1}{2\pi}\operatorname{tr}\mathsf Q_E(E)\,dE.
$$
于是母刻度与由其诱导的窗化读数在能量坐标重参数化下不变；相应地,$(w_R,h)$ 需作雅可比一致的幅度重标以保持 $\int(w_R*\check h)=2\pi$。

**Nyquist条件在重参数化下的缩放**：若原 $E$ 变量下的带宽为 $B$（满足 $\Delta_E\le\pi/B$），在新变量 $\varepsilon$ 下等间隔采样时，Nyquist条件变为
$$
\boxed{\ \Delta_\varepsilon\le \frac{\pi}{B\cdot\sup_{\rm supp}E'(\varepsilon)}\ },
$$
其中 $\sup$ 取于窗支撑的 $\varepsilon$ 区间。**保守选择**：若 $E'(\varepsilon)$ 变化剧烈，取 $\inf_{\rm supp}E'(\varepsilon)$ 作为缩放因子以确保整个支撑内无别名：
$$
\Delta_\varepsilon\le \frac{\pi}{B\cdot\inf_{\rm supp}E'(\varepsilon)}.
$$
这确保重参数化后的离散实现仍满足卡片II的无别名条件。

### 3.3 非渐近误差闭合(NPE)

**命题 3.5(离散实现；精确与近似的分立表述)** 设 $f(E):=w_R(E)\,[\,h\!\star\!\rho_{\rm rel}\,](E)$,采样点 $E_n=E_0+n\Delta$。

**(A) 严格带限 + Nyquist 条件(精确等式)**:若 $\widehat w,\widehat h$ 严格带限且 $f\in\mathsf{PW}_B\cap L^1$，其中 $B:=\Omega_h+\Omega_w/R$,并满足
$$
\Delta\le \frac{\pi}{B},
$$
则当 $\widehat f$ 紧支撑于 $[-B,B]$ 且 $f\in L^1\cap L^2$ 时,Poisson 求和与积分可交换,由此得
$$
\boxed{\ T_\gamma[w_R,h]=\int_{\mathbb R} f(E)\,dE=\Delta\sum_{n\in\mathbb Z} f(E_n)\ }.
$$
此时 $\varepsilon_{\rm alias}=\varepsilon_{\rm EM}=\varepsilon_{\rm tail}=0$。**关键提醒：严格带限+Nyquist条件下(A)式是精确等式，无需引入任何误差项；只有在近带限或数值截断时才需要(B)的三分解。**

**(B) 近带限/数值截断(NPE 三分解)**:若 $f$ 仅近似带限或实现上将无穷和截断为 $|n|\le N$,则
$$
T_\gamma[w_R,h]=\Delta\sum_{|n|\le N} f(E_n)+\varepsilon_{\rm tail}+\varepsilon_{\rm alias}+\varepsilon_{\rm EM},
$$
其中
$$
\varepsilon_{\rm tail}:=\Delta\sum_{|n|>N} f(E_n),\qquad |\varepsilon_{\rm alias}|\le\sum_{k\ne 0}\Big|\widehat f\big(\cdot+2\pi k/\Delta\big)\Big|_{L^1},
$$
而 $\varepsilon_{\rm EM}$ 仅在以有限阶 Euler–Maclaurin 近似无穷和(或对近带限 $f$ 的修正积分)时出现,其上界参见附录 B。*说明*: 本命题将理论上的等式 (A) 与工程实践的 NPE 分解 (B) 严格区分,避免在无 alias 的情形下引入不存在的 EM/尾项。**再次强调:严格带限 + Nyquist 时 $\varepsilon_{\rm alias}=\varepsilon_{\rm EM}=\varepsilon_{\rm tail}=0$;只有在近带限或数值截断时才引入三分解,避免在无 alias 情况下误加 EM 校正**。([chaosbook.org][7])

### 3.4 前沿–群延迟桥梁(HF 平台一致性/标定法)

本节**在 §4 的前提 (i)、(ii′)、(iii)、(iv) 内**(LTI+Hardy 因果、局域与被动性、加强版高频真空极限),在不改变本文双层框架的前提下,给出一个**可操作、非渐近可控/渐近一致**的桥接:

> **在 §4 假设下前沿 $t_*$ 存在且唯一**，下述极限提供 $T_\gamma$ 与 $t_*$ 的**一致性检验**，并据此实现**平台法标定**：**在高频真空极限下,任意固定形状的归一窗族沿频率平移,窗化群延迟读数收敛到前沿时间 $t_*$。**

> 并给出有限频带下的简单"夹逼"上界,从而把 $t_*$ 的测度回推为 $T_\gamma$ 的**可实现标定极限**。

#### 3.4.1 前沿因子化(Front factorization)

在 §4 的前提 (i)–(iv) 下(LTI + Hardy 因果、被动、局域有限传播、高频真空极限),对任一链 $\gamma$ 存在常数 $t_*(\gamma)\ge 0$ 与**剩余散射子**
$$
S_0(\omega):=e^{i\omega\,t_*(\gamma)}\,S(\omega),
$$
使得 $S_0$ 的时域冲激响应 $g_0(t)$ 满足**零前沿**支撑 $g_0(t)=0$(对 $t<0$)。于是
$$
\mathsf Q(\omega)\;=\;-iS^\dagger S' \;=\;-t_*(\gamma)\,\mathsf I\;+\;\mathsf Q_0(\omega),\qquad
\mathsf Q_0:=-iS_0^\dagger S_0'.
$$
取迹并代入本文母刻度（含定义3.1的负号）,在归一化 $\int (w_R*\check h)=2\pi$ 下得到**分解恒等式**
$$
\boxed{\quad T_\gamma[w_R,h]\;=\;t_*(\gamma)\,\operatorname{tr}\mathsf I\;-\;\underbrace{\int_{\mathbb R}(w_R*\check h)(\omega)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_0(\omega)\,d\omega}_{\displaystyle \ \ :=:\ \varepsilon_{\rm rem}(w_R,h)}\quad}
$$
其中"余项" $\varepsilon_{\rm rem}$ 完全由零前沿剩余散射 $S_0$ 决定。**在单通道**($N=1$)下,$\operatorname{tr}\mathsf I=1$,故 $T_\gamma=t_*-\varepsilon_{\rm rem}$。

> **直观**:把"几何最短自由飞行"($t_*$)作为全局相位斜率抽取出来,$T_\gamma$ 就是"**前沿 $t_*$ − 零前沿散射的带内相位平均**"。

#### 3.4.2 高频标定极限(桥接主命题)

设一族**平移窗** $F_{E_0}(\omega):=(w_R*\check h)(\omega-E_0)$(形状固定、仅平移),并保持本文 Nyquist 无别名与 $\int F_{E_0}=2\pi$。令 $F_{E_0}$ 的支撑宽度 $\mathrm{diam}(\mathrm{supp}\,F_{E_0})\le W<\infty$ 与 $E_0$ 无关。

**实现建议（非负窗推荐）**：**推荐选用非负窗—核族**使 $F_{E_0}\ge 0$（如Kaiser窗、Blackman–Harris窗等），从而 $T_\gamma-t_*$ 可严格解释为对 $\frac{1}{2\pi}\operatorname{tr}\mathsf Q_0$ 的带内平均，夹逼界直接给出物理意义明确的误差上界。**若窗不是严格带限，请同步给出附录B的alias与EM余项上界。**若 $F_{E_0}$ 允许取负（如卷积后出现振荡或采用正弦窗），需同时报告 $\frac{1}{2\pi}\int |F_{E_0}|$ 作为保守上界的归一因子；此时夹逼界仍成立但解释需谨慎。

**可检前提（实验应用）**：只要在所扫频段的上沿，实测 $|\operatorname{tr}\mathsf Q(\omega)+t_* N|$ 随 $\omega$ **单调衰减并可被统一上界**，则平台误差可由 §3.4.3 的夹逼式直接上界。形式上，这对应于 §4 的前提 (i)、(ii′)、(iii)、(iv)，其中前提 (ii′) 假设 $S_0'(\omega)$ 在大频率上一致有界且趋零（等价地 $\operatorname{tr}\mathsf Q_0(\omega)=-i\operatorname{tr}(S_0^\dagger S_0')\to0$），由此得
$$
\sup_{\omega\in\mathrm{supp}\,F_{E_0}}\big|\operatorname{tr}\mathsf Q_0(\omega)\big|\to 0.
$$
该条件在被动、Hardy、局域、高频真空极限之下成立。于是:

**定理 3.6(HF 桥接)** 对任意固定形状的归一窗族 $F_{E_0}$,**在单通道**($N=1$)下有
$$
\boxed{\qquad \lim_{E_0\to+\infty} T_\gamma[w_R(\cdot-E_0),h]\;=\;t_*(\gamma)\qquad}
$$
且**有限频带夹逼**:
$$
\big|\,T_\gamma[w_R(\cdot-E_0),h]-t_*(\gamma)\,\big|\ \le\
\sup_{\omega\in\mathrm{supp}\,F_{E_0}}\ \big|\operatorname{tr}\mathsf Q_0(\omega)\big|\ \xrightarrow[E_0\to\infty]{}\ 0.
$$

*证明要点*:由 3.4.1 的分解,$T_\gamma=t_*\,\operatorname{tr}\mathsf I-\int F_{E_0}\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_0$；在单通道下 $\operatorname{tr}\mathsf I=1$。对 $E_0$ 足够大,$\operatorname{tr}\mathsf Q_0$ 在 ${\rm supp}\,F_{E_0}$ 上一致趋零,余项被该一致上界控制,极限即得。□

**命题 3.6'(多通道几何前沿极限)** 对**多通道**($N\ge1$)系统，采用每模平均刻度 $\overline T_\gamma[w_R,h]:=-\int (w_R*\check h)(E)\,\frac{1}{2\pi}\,\frac{1}{N}\operatorname{tr}\mathsf Q_\gamma(E)\,dE$（定义见 §3.1），有
$$
\boxed{\qquad \lim_{E_0\to+\infty} \overline T_\gamma[w_R(\cdot-E_0),h]\;=\;t_*(\gamma)\qquad}
$$
且**有限频带夹逼**:
$$
\big|\,\overline T_\gamma[w_R(\cdot-E_0),h]-t_*(\gamma)\,\big|\ \le\
\sup_{\omega\in\mathrm{supp}\,F_{E_0}}\ \Big|\frac{1}{N}\operatorname{tr}\mathsf Q_0(\omega)\Big|\ \xrightarrow[E_0\to\infty]{}\ 0.
$$

*证明要点*:由3.4.1分解，$\mathsf Q=-t_*\mathsf I+\mathsf Q_0$，故
$$
\overline T_\gamma=-\int F_{E_0}\,\frac{1}{2\pi}\,\frac{1}{N}\operatorname{tr}\mathsf Q\,dE
=t_*-\int F_{E_0}\,\frac{1}{2\pi}\,\frac{1}{N}\operatorname{tr}\mathsf Q_0\,dE.
$$
高频极限下 $\operatorname{tr}\mathsf Q_0/N$ 在窗支撑内一致趋零，余项被夹逼界控制。□

> **操作含义**:把**同一窗形**沿频率"蓝移"扫描(保持带限与归一),所测 $T_\gamma$ 曲线（单通道）或 $\overline T_\gamma$ 曲线（多通道几何前沿）在高频端**平台值**统一为 $t_*$。该程序只用到本文已设定的带限/Nyquist与高频真空极限,无需新增假设。

> **刻度选择提示**：对**几何前沿时间**的实验标定，多通道系统推荐直接使用 $\overline T_\gamma$ 作为测量量，其平台极限自然给出 $t_*$；若使用 $T_\gamma$（总通道时延），则平台值为 $Nt_*$，需除以通道数 $N$ 才能恢复几何前沿。

#### 3.4.3 有限带宽下的直接界(工程可用)

对任意有限中心频率 $E_0$,由 3.4.2 的夹逼可直接报出**系统误差上界**:
$$
t_*(\gamma)-\Delta_-(E_0)\ \le\ T_\gamma[w_R(\cdot-E_0),h]\ \le\ t_*(\gamma)+\Delta_+(E_0),
$$
$$
\Delta_\pm(E_0)\ :=\ \sup_{\omega\in\mathrm{supp}\,F_{E_0}}\big|\operatorname{tr}\mathsf Q_0(\omega)\big|.
$$

**派生界（Lipschitz 估计）**：若 $F_{E_0}\ge 0,\ \int F_{E_0}=2\pi$，且 $|\partial_\omega \operatorname{tr}\mathsf Q_0(\omega)|\le L$ 于窗支撑，则对任意 $\omega_0\in\mathrm{supp}\,F_{E_0}$ 有
$$
\big|T_\gamma-t_*\big|
=\Big|\int \frac{F_{E_0}(\omega)}{2\pi}\,\operatorname{tr}\mathsf Q_0(\omega)\,d\omega\Big|
\le \big|\operatorname{tr}\mathsf Q_0(\omega_0)\big|
   +\frac{L}{2}\,\mathrm{diam}\big(\mathrm{supp}\,F_{E_0}\big).
$$
从而
$$
\big|T_\gamma-t_*\big|
\le \min_{\omega_0\in\mathrm{supp}\,F_{E_0}}
    \big|\operatorname{tr}\mathsf Q_0(\omega_0)\big|
  + \frac{L}{2}\,\mathrm{diam}\big(\mathrm{supp}\,F_{E_0}\big).
$$
**特别地**，若已知窗支撑内存在 $\omega_*$ 使 $\operatorname{tr}\mathsf Q_0(\omega_*)=0$（例如将窗中心选在高频零交叉附近），则可简化为
$$
\big|T_\gamma-t_*\big|\le \frac{L}{2}\,\mathrm{diam}\big(\mathrm{supp}\,F_{E_0}\big).
$$
这将**平台到达速率与窗宽直接挂钩**,便于实验选带宽。

当仅有"近带限"实现时,把 $\Delta_\pm$ 与 §3.3 的 NPE 误差三分解($\varepsilon_{\rm alias},\varepsilon_{\rm EM},\varepsilon_{\rm tail}$)**相加**即可形成**可审计的总误差预算**。

> **注意**:本界不声称 $T_\gamma\ge t_*$;在强共振、窄带情况下,$\operatorname{tr}\mathsf Q$ 在带内可出现**负值**,从而 $T_\gamma<t_*$ 甚至为负,但**高频平台极限**仍等于 $t_*$。

### 3.5 实验实现要点（极简）

本节给出窗化群延迟读数与HF平台标定的实验实施路径。

**微波/射频波段**：使用矢量网络分析仪（VNA）直接测量散射矩阵 $S(\omega)$。对获得的相位谱 $\arg S(\omega)$ 进行展宽与解缠，**数值微分时建议采用正则化方法**（如Savitzky–Golay滤波微分、样条拟合后求导、或Tikhonov正则化）以抑制噪声放大；直接差分会显著放大高频噪声。结合 $\mathsf Q=-iS^\dagger S'$ 计算 $\operatorname{tr}\mathsf Q(\omega)$，窗化读数按定义3.1积分即可。

**光学频段**：
- **频域方法**：频率梳或白光干涉获取相位-频率响应，转换为群延迟谱；
- **时域方法**：泵浦-探测测量瞬态响应，时变镜（ITO/ENZ，§12.5）与频域响应的映射由定理6.2的谱缩放律给出。

**HF平台标定**：固定窗形 $(w_R,h)$ 沿频率 $E_0$ 扫描，绘制 $T_\gamma(E_0)$ 曲线，高频段平台值即为 $t_*$ 的标定量；依§3.4.3的夹逼界 $\Delta_\pm(E_0)$ 评估系统误差。

**误差预算示例**：设观测带宽 $B=\Omega_h+\Omega_w/R=10$ GHz，采样间隔 $\Delta=0.05$ GHz（满足Nyquist $\Delta\le \pi/B\approx 0.16$ GHz），窗—核取 $M=4$ 阶可微。依§3.3命题3.5，此时 $\varepsilon_{\rm alias}=0$（严格带限），$\varepsilon_{\rm EM}$ 由附录B的4阶EM余项给出（$\sim B^{-4}$量级），$\varepsilon_{\rm tail}$ 由支撑外衰减控制。总误差 $\varepsilon_{\rm total}=\varepsilon_{\rm EM}+\varepsilon_{\rm tail}+\Delta_\pm(E_0)$ 可审计且非渐近有界。

---

**前提**:以下关于前沿与无超锥传播的命题建立在:

(i) **LTI + 因果 + 上半平面解析性(Hardy)**:频域响应的上半平面解析性与 Hardy 边值保证 Kramers–Kronig–Hilbert 关系;**若进一步假设被动性**,则可归入 Herglotz 类;

(ii′) **高频真空极限(加强版，一致收敛条件)**:存在前沿 $t_*$ 使 $S_0(\omega):=e^{i\omega t_*}S(\omega)\to I$ 且 $S_0'(\omega)\to 0$(在$|\omega|\to\infty$时)。**精确要求**：
- **全局有界性**：存在 $M<\infty$ 使 $|\operatorname{tr}\mathsf Q_0(\omega)|\le M$ 对所有 $\omega\in\mathbb R$ 成立；
- **一致趋零**：对任意固定有限窗宽 $W<\infty$，有
$$
\lim_{E_0\to\infty}\sup_{|\omega-E_0|\le W}\left|\operatorname{tr}\mathsf Q_0(\omega)\right|=0.
$$

这保证了高频平台法（定理3.6）的余项可被一致控制。**物理实现**：被动、Hardy、局域、且在高频 远离共振的系统自然满足此条件（$S_0'\sim O(\omega^{-2})$ 即足够）。

(iii) **局域性/有限传播速度**:链由满足双曲型局域动力学的元件组成,其格林函数(或冲激响应)存在有限波前;

(iv) **被动性**:无主动增益导致的超前响应。

**可核查清单（实验验证前沿下界的充分条件）**：对任意器件链 $\gamma$，若满足以下条件，则定理4.2的前沿下界 $t_*(\gamma)\ge L/c$ 成立：

1. **LTI**：系统线性时不变，频域描述为 $S(\omega)$；
2. **因果支撑**：冲激响应 $g(t)$ 在 $t<0$ 时恒为零，且 $g\in L^1(\mathbb R^+)$（可积）；
3. **高频衰减速率**：前沿因子化后的 $S_0(\omega)=e^{i\omega t_*}S(\omega)$ 满足 $\|S_0(\omega)-I\|=O(|\omega|^{-1})$ 或更快（$|\omega|\to\infty$）；
4. **元件波前速度**：链中各元件的局部波前速度不超过§4.1规范的光速 $c$（在真空度规下）；
5. **无超前增益**：无主动放大导致的非因果响应或超前峰。

**操作判据**：实验上可通过以下方式验证：
- 测量 $|S(\omega)|$ 与 $\arg S(\omega)$，用Kramers–Kronig关系交叉验证因果性；
- 检查高频段 $|S(\omega)|$ 的衰减速率（谱分析仪扫频）；
- 对时域脉冲响应测量，确认 $t<L/c$ 时无信号到达。

**结论**：满足上述清单即保证前沿下界 $t_*\ge L/c$ 成立，从而可依此构造类光锥与偏序结构（§4.2）。

## 4. 光速与类光锥:前沿定标与无超锥传播

### 4.1 光速的前沿规范

**定义 4.1(光速 $c$)** 真空冲激响应 $g_0(t;L)$ 的最早非零到达 $t_{\rm front}(L)$ 给出
$$
c:=\lim_{L\to\infty}\frac{L}{t_{\rm front}(L)}\quad\text{（若极限存在）}.
$$
**稳健版本**：若上述极限不存在（如 $t_{\rm front}(L)$ 在某些尺度振荡），改用
$$
c_{\rm min}:=\liminf_{L\to\infty}\frac{L}{t_{\rm front}(L)},\qquad
c_{\rm max}:=\limsup_{L\to\infty}\frac{L}{t_{\rm front}(L)},
$$
并据此给出前沿速度的上下界 $c_{\rm min}\le v_{\rm front}\le c_{\rm max}$。本文§4.2的前沿下界采用 $c_{\rm max}$（最保守界），不作等式判断。
其中 $L$ 表示在**真空度规**下两点间的**光程(测地长度)**,其定义独立于介质;介质的色散与吸收效应仅体现于系统响应而不改变前沿下界的几何基准。该 $L$ 亦用于 §4.2 中 $t_*(\gamma)\ge L/c$ 的判定基准。前沿速度与因果一致(Sommerfeld–Brillouin 先驱)。([互联网档案馆][8])

### 4.2 无超锥传播——前沿读数

**定理 4.2(前沿下界)** 在上述前提下,任意链 $\gamma$ 的输出冲激响应 $g_\gamma(t;L)$ 在 $t<L/c$ 恒为 0,因而
$$
t_*(\gamma)\ \ge\ L/c,
$$
且等号当且仅当链的高频传播子在真空极限下沿测地达到。据此可定义类光锥边界与未来锥
$$
\partial J^+(x):=\{\,y\in J^+(x):\ \tau(x,y)=L_*(x,y)/c\,\},\qquad
J^+(x):=\{\,y:x\preceq y\,\}=\{\,y:\Gamma(x,y)\neq\varnothing\,\}.
$$
其中 $\tau(x,y)=\inf_{\gamma\in\Gamma(x,y)} t_*(\gamma)\ge L_*(x,y)/c$ 由前沿下界保证。*注*:窗化群延迟读数 $T_\gamma[w_R,h]$ 仍非前沿时间,窄带/共振下可取负,二者无普适比较不等式;二者的桥接见 §3.4。([Wolfram MathWorld][5])

本文一切因果与无信号结论仅以 $t_*$ 与类光锥偏序为准绳;$T_\gamma$ 仅作为可测读数,不参与偏序的定义。

---

## 5. 波—粒统一与"不同画面"的来源

### 5.1 同源二读数:期望与计数

同一 $K_{w,h}$ 诱导
$$
\text{(波)}\ \ \mathrm{Obs}(w_R,h)=\operatorname{Tr}(K_{w,h}\rho),\qquad
\text{(粒)}\ \ \mathbb E N_{w,h}=\operatorname{Tr}\big(K_{w,h}\,\Phi(\rho)\big)=\operatorname{Tr}\big(\Phi^\dagger(K_{w,h})\,\rho\big).
$$
其中 $\Phi^\dagger$ 为 $\Phi$ 的 Heisenberg 伴随。二者时间标度均由 $T_\gamma[w_R,h]$ 计量;$\Phi,\{M_i\},\mathcal M_{\rm th}$ 仅改变统计外观,不改母刻度。**此处 $T_\gamma$ 指通道层读数（channel-only functional）；态层窗化读数 $\mathrm{Obs}(w_R,h;\rho)$ 与 $T_\gamma$ 处于不同层（前者依赖态 $\rho$），不可混用**。([Google 图书][4])

### 5.2 双缝的窗化互补律

设路径投影 $P_1,P_2$,which-way 退相干 $\mathcal D_\eta(\rho)=(1-\eta)\rho+\eta\sum_j P_j\rho P_j$。屏上窗—核 $(w_R,h)$ 的强度
$$
I(\eta)\ \propto\ \sum_{j}\langle K_{w,h}P_j\psi,P_j\psi\rangle
+2(1-\eta)\,\Re\langle K_{w,h}P_1\psi,P_2\psi\rangle.
$$
**定理 5.2(窗化互补不等式)** 能见度 $V$ 与可辨度 $D$(Helstrom 距离)满足 $D^2+V^2\le 1$,等号在纯态与理想区分/理想相干极限取到。([物理评论链接管理器][9])

*证明提纲*:以 CPTP 收缩性与 Cauchy–Schwarz 控制交叉块范数;将二分类最小错判界(Helstrom)嵌入窗化场景,复现 Englert 不等式。([物理评论链接管理器][10])

### 5.3 延迟擦除(Delayed-Choice Quantum Eraser, DCQE)

**设置** 设双缝路径投影 $P_1,P_2$。引入"信号—闲置(idler)"分裂 $\mathcal H=\mathcal H_s\otimes\mathcal H_i$,以幺正纠缠器
$$
U_{\rm ent}:\ P_j\otimes\lvert0\rangle_i\ \mapsto\ P_j\otimes\lvert I_j\rangle_i,\qquad \langle I_1\mid I_2\rangle=0,\ j=1,2,
$$
实现 which-way 打标。屏上读数由同一窗—核 $K:=K_{w,h}$ 给出,闲置端选择在两类测量基之间切换:

(i) which-way 基 $\{\Pi_{I_1},\Pi_{I_2}\}$;(ii) 擦除基 $\{\Pi_{E_\pm}\}$,其中
$$
\lvert E_\pm\rangle=\tfrac{1}{\sqrt2}\big(\lvert I_1\rangle \pm e^{i\phi}\lvert I_2\rangle\big),\quad \Pi_{E_\pm}=\lvert E_\pm\rangle\langle E_\pm\rvert.
$$

**定义(符合—条件强度)** 记源态 $\rho_s$ 与总态 $\rho_{si}=U_{\rm ent}(\rho_s\otimes\lvert0\rangle\langle0\rvert)U_{\rm ent}^\dagger$。对闲置端结果 $\alpha\in\{I_1,I_2,E_+,E_-\}$,定义
$$
I_\alpha(w_R,h):=\operatorname{Tr}\Big[(K\otimes \Pi_\alpha)\,\rho_{si}\Big].
$$

**命题 5.3(无条件=无干涉;擦除=条件条纹)**

(1) 无条件边缘强度与退相干等价:
$$
I_{\rm uncond}(w_R,h):=\sum_{j=1}^2 I_{I_j}(w_R,h)=\operatorname{Tr}\Big(K\,\sum_{j=1}^2 P_j\rho_s P_j\Big),
$$
其交叉项消失,故屏上不显干涉。

(2) 擦除基下的条件符合显现互补相位:
$$
I_\pm(w_R,h)=\sum_{j=1}^2 \operatorname{Tr}\big(K\,P_j\rho_s P_j\big)\ \pm\ 2\,\Re\Big(e^{i\phi}\operatorname{Tr}(K\,P_1\rho_s P_2)\Big),
$$
两图样相位相反,能见度在纯态与理想稳定窗下取到互补上界。

**定理 5.4(无信号与无条件群延迟不变)** 设闲置端采用任意完备仪式 $\{\mathcal I_a^i\}$(包含 which-way 或擦除作特别情形),则

(i) 屏上无条件分布不依赖闲置选择与测量先后:
$$
\sum_a I_a(w_R,h)=\operatorname{Tr}\big(K\,\operatorname{Tr}_i\rho_{si}\big),\qquad \sum_a \mathcal I_a^i=\Phi_i\ \text{为 CPTP};
$$

(ii) **信号端的无条件（边缘）窗化群延迟读数**不随闲置端完备仪式而变:
$$
\boxed{\ T_{\rm sig}^{\rm (marg)}[w_R,h]=-\int (w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_{\rm sig}(E)\,dE\ }.
$$

*证明要点*:完备性与偏迹给出 $\sum_a(\mathrm{Id}_s\otimes\mathcal I_a^i)(\rho_{si})=(\mathrm{Id}_s\otimes\Phi_i)(\rho_{si})$,取 $\operatorname{Tr}_i$ 得无条件不变;不变性来自 $\sum_a\mathcal I_a^i=\Phi_i$ 与 $\operatorname{Tr}_i$ 的边缘保持;$\mathsf Q_{\rm sig}$ 由信号散射子决定,与闲置的本地测量基无关,故边缘群延迟读数不变。

**关键警示（无信号仅对无条件量）**：**本命题的无信号性与群延迟不变性仅对无条件（边缘）量成立**。对按结果 $a$ 条件化后的读数 $T_{\rm sig|a}$，一般会随闲置端选择而变化（这正是"which-way信息"与"干涉能见度"互补性的体现）。因果性与无信号由 $t_*$ 与类光锥偏序保证（§7），与 $T_\gamma$ 的条件/无条件区分无关。

*备注(延迟与类空间分离)*:当屏与闲置读出区域类空间分离时,由 §7 的窗化微因果律,$[K[U_x],\mathbf 1\otimes\Pi_\alpha[U_y]]=0$,因而"延迟选择"不引入任何超因果效应;仅在符合(条件化)层面重排样本,边缘统计与群延迟读数保持不变。其无信号与时间顺序独立的根源来自由 $t_*$ 决定的偏序结构,而非 $T_\gamma$。

---

## 6. 红移:谱缩放与时间互易

### 6.1 定义

**定义 6.1(红移)** 对源—受体,母刻度上
$$
1+z=\frac{E_{\rm src}}{E_{\rm obs}}=\frac{\nu_{\rm src}}{\nu_{\rm obs}}.
$$
**宇宙学语境**:当 $1+z>1$ 时 $E_{\rm obs}<E_{\rm src}$,此记号与天体物理学标准一致。

### 6.2 互易标度律

**假设(谱均匀缩放)**:存在 $z>-1$ 使 $S_{\rm obs}(E)=S_{\rm src}((1+z)E)$,并保证 $S,\ S'$ 在缩放域内可测可积;同时假设源端窗/核满足卡片 II 的带限与采样前提。

**定理 6.2** 若谱缩放 $E\mapsto E/(1+z)$,则对任意链 $\gamma$ 与窗—核 $(w_R,h)$,
$$
\boxed{\ 
T_\gamma^{\rm obs}[w_R,h]
=\frac{1}{1+z}\,T_\gamma\!\big[w_R^{\langle 1/(1+z)\rangle},\,h^{\langle 1/(1+z)\rangle}\big],\quad
w_R^{\langle a\rangle}(E):=w_R(aE),\ \ h^{\langle a\rangle}(E):=h(aE).
\ }
$$
等价地,
$$
T_\gamma^{\rm obs}[w_R,h]
=-\int_{\mathbb R}(w_R*\check h)\!\Big(\frac{E}{1+z}\Big)\,
\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\gamma(E)\,dE.
$$
**带限与采样协变**:若 $\widehat w,\widehat h$ 严格带限,则 $w_R^{\langle a\rangle},h^{\langle a\rangle}$ 仍严格带限,Nyquist 纪律随缩放变为 $\Delta\le \pi/\big(a(\Omega_h+\Omega_w/R)\big)$,故卡片 II 的前提在该模型下保持有效。为保持母刻度校准,**对缩放后的窗—核做幅度重标**使 $\displaystyle \int_{\mathbb R}\big(w_R^{\langle a\rangle}*\check h^{\langle a\rangle}\big)=2\pi$。下文默认该归一已执行；若未重标，则 $T$ 需乘以相应的面积因子修正。

**缩放后的 $2\pi$ 保持重标**：若 $f^{\langle a\rangle}(E):=f(aE)$,则 $\int (w_R^{\langle a\rangle}*\check h^{\langle a\rangle})=\tfrac{1}{a^2}\int (w_R*\check h)$。需保持 $\int=2\pi$ 时,可采用：

**(i) 双边对称重标**（本文默认）：取
$$
\widetilde w_R^{\langle a\rangle}:=a\,w_R^{\langle a\rangle},\qquad
\widetilde h^{\langle a\rangle}:=a\,h^{\langle a\rangle},
$$
则 $\int (\widetilde w_R^{\langle a\rangle}*\widetilde{\check h}^{\langle a\rangle})=2\pi$。

**(ii) 单边重标**：若仅对 $w_R^{\langle a\rangle}$（或 $h^{\langle a\rangle}$）做单边幅度重标,则需乘以 $a^2$ 才能把 $\int (w_R^{\langle a\rangle}*\check h^{\langle a\rangle})$ 恢复到 $2\pi$。

**红移情况的等价表述**：设 $a=\frac{1}{1+z}$。

- **未做归一重标**（原始缩放）：
$$
T_\gamma^{\rm obs}[w_R,h]
=\int (w_R*\check h)\!\Big(\frac{E}{1+z}\Big)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE
=\frac{1}{1+z}\,T_\gamma\!\big[w_R^{\langle \frac{1}{1+z}\rangle},\,h^{\langle \frac{1}{1+z}\rangle}\big].
$$

- **采用对称归一重标**（使缩放后仍满足 $\int=2\pi$）：
$$
\boxed{\
T_\gamma^{\rm obs}[w_R,h]=(1+z)\,T_\gamma\!\big[\widetilde w_R^{\langle \frac{1}{1+z}\rangle},\,\widetilde h^{\langle \frac{1}{1+z}\rangle}\big].
\ }
$$
**示例**：若 $\int(w_R*\check h)=2\pi$，缩放后取 $\widetilde w_R^{\langle a\rangle}=a\,w_R(a\cdot)$，$\widetilde h^{\langle a\rangle}=a\,h(a\cdot)$ 以保持面积 $\int(\widetilde w_R^{\langle a\rangle}*\widetilde{\check h}^{\langle a\rangle})=2\pi$ 不变。

*证明要点*:$\operatorname{tr}\mathsf Q_{\rm obs}(E)=(1+z)\,\operatorname{tr}\mathsf Q\big((1+z)E\big)$；$(\widetilde w_R^{\langle a\rangle}*\widetilde{\check h}^{\langle a\rangle})(E)=a\,(w_R*\check h)(aE)$。

**Nyquist缩放规律（再次强调）**：谱缩放 $E\mapsto E/(1+z)$ 下，窗—核缩放为 $w_R^{\langle a\rangle}(E)=w_R(aE),\ h^{\langle a\rangle}(E)=h(aE)$（$a=1/(1+z)$），其频域支撑缩放为 $\mathrm{supp}\,\widehat w_R^{\langle a\rangle}\subset[-\Omega_w/(aR),\Omega_w/(aR)]$，故Nyquist条件变为
$$
\Delta\le \frac{\pi}{\Omega_h/a+\Omega_w/(aR)}=\frac{\pi\cdot a}{\Omega_h+\Omega_w/R}=(1+z)^{-1}\cdot\frac{\pi}{\Omega_h+\Omega_w/R}.
$$
**总结**：红移使采样间隔需求放宽 $(1+z)$ 倍（蓝移则收紧），与时间互易标度律一致。

---

## 7. 窗化微因果与滤镜链的因果适配

### 7.1 类空间分离与交换

**局域化约定(本节)** 在因果流形 $(\mathcal M,\preceq)$ 上,对任意开集 $U\subset\mathcal M$ 记 $P_U$ 为 $U$ 上的局域投影/截断算符,定义局域窗—核
$$
K_{w,h}[U]:=P_U K_{w,h} P_U,
$$
使得 $\mathrm{supp}\,K_{w,h}[U]\subset U$。称 $U_x,U_y$ 类空间分离当且仅当 $U_x\cap J^\pm(U_y)=\varnothing$。以下所有陈述均针对局域算子 $K_{w,h}[U]$。

**定义 7.1(类空间分离)** 两局域窗—核支撑域 $U_x,U_y$ 互不落入对方的前/后向锥内。
**命题 7.2(窗化微因果律)** 设 $K_{w_x,h_x}[U_x],K_{w_y,h_y}[U_y]$ 属于满足微因果(例如 Wightman/Haag–Kastler)条件的局域代数网,且其支撑区域类空间分离,则
$$
[K_{w_x,h_x}[U_x],K_{w_y,h_y}[U_y]]=0.
$$
若进一步假设相关 CP/POVM 操作的 Heisenberg 伴随将各自算子代数保持在 $K_{w_x,h_x}[U_x]$、$K_{w_y,h_y}[U_y]$ 生成的局域子代数内,且支撑继续类空间分离,则有 $\mathcal O_y\circ \mathcal O_x=\mathcal O_x\circ \mathcal O_y$。该陈述与 QFT 微因果 $[\mathscr O(x),\mathscr O(y)]=0$ 同型。([ncatlab.org][11])

### 7.2 因果适配与组合律

**定义 7.3(因果适配)** 沿世界线 $\gamma$ 的滤镜族 $\{\mathcal O_t\}$ 若其支撑包含于 $J^-(\gamma(t))$ 且仅作用于 $K_{w_t,h_t}$ 生成的子代数,则称因果适配。
**命题 7.4(组合律)** 分段滤镜满足
$$
\mathcal O_{[t_0,t_n]}=\mathcal O_{[t_{n-1},t_n]}\circ\cdots\circ \mathcal O_{[t_0,t_1]},
$$
相邻类空间分离段可交换,否则按时间序组合。

### 7.3 延迟选择的无信号与时间顺序独立

**命题 7.5(无信号)** 对任意信号—闲置总态 $\rho_{si}$ 与任意闲置端完备仪式 $\{\mathcal I_a^i\}$($\sum_a\mathcal I_a^i=\Phi_i$ 为 CPTP),有
$$
\operatorname{Tr}_i\Big[(\mathrm{Id}_s\otimes\sum_a\mathcal I_a^i)(\rho_{si})\Big]=\operatorname{Tr}_i(\rho_{si}),
$$
故任意屏上局域窗—核 $K_{w,h}[U_x]$ 的无条件读数不依赖闲置端的测量基、是否擦除、以及先后顺序。

**命题 7.6(时间顺序独立)** 若屏域 $U_x$ 与闲置域 $U_y$ 类空间分离,则对任何 $K_{w,h}[U_x]$ 与闲置端投影 $\Pi_\alpha[U_y]$ 有
$$
[K_{w,h}[U_x],\mathbf 1\otimes\Pi_\alpha[U_y]]=0,
$$
从而无论"先测屏后擦除"或"先擦除后测屏",无条件分布一致;条件符合仅改变样本分组,不改变边缘。与 §5.3 的定理 5.4 保持一致。其无信号性与时间顺序独立源于偏序结构,而非 $T_\gamma$。

---

## 8. 接口纲要:GLS → 因果流形(构造骨架与开放问题)

### 8.1 范畴

$\mathbf{WScat}$:对象为 $(S,\mu_\varphi,\mathcal W)$,态射为保持卡片 I/II 的滤镜链;
$\mathbf{Cau}$:对象为因果流形 $(\mathcal M,\preceq)$,其中 $\preceq$ 为由 §2.1 的可达预序在无闭因果回路假设下得到的偏序(或一般情形下的商偏序);态射为保持类光锥与该偏序的映射。

### 8.2 构造骨架与限制

**纲要 8.1(GLS → 因果流形的接口构造)** 存在**以 $t_*$ 为参数的接口图式**
$$
\mathfrak F_{t_*}:\mathbf{WScat}\to\mathbf{Cau},
$$
*构造要点*:$\mathfrak F_{t_*}$ 以前沿集/最早到达集(由 $t_*(\cdot)$ 确定)与相位奇性生成偏序与锥;$\operatorname{tr}\mathsf Q$ 仅用于读数层面的刻度与标定(Nyquist 极限与 $c$ 等值)。$t_*$ 可由 §3.4 的 HF 标定从 $T_\gamma$ **实验性确定**,再作为外参输入接口,从而闭合双层框架的往返使用。

**开放问题**:反向函子 $\mathfrak G:\mathbf{Cau}\to\mathbf{WScat}$ 的构造与自然同构 $\mathfrak F_{t_*}\circ\mathfrak G\simeq \mathrm{Id}_{\mathbf{Cau}}$、$\mathfrak G\circ\mathfrak F_{t_*}\simeq \mathrm{Id}_{\mathbf{WScat}}$ 的**存在性与自然性验证为后续工作**。目前仅给出接口纲要骨架,不对双层等价性作承诺。

---

## 9. 分辨率—红移对偶与尺度重整

令带限偶窗 $w\in\mathsf{PW}_\Omega$,采用零心母窗
$$
w_R(E)=w(E/R),
$$
需要中心定位于 $E_c$ 时使用 $w_R(E-E_c)$。分辨率提升 $R\mapsto\lambda R$($\lambda>1$)对应于红移放大 $E\mapsto E/(1+z)$,两者在 Nyquist 纪律下完全对偶。在该对偶框架下,别名关断,EM 端点误差与尾项随 $R$ 的演化按可计算律缩放,并与谱缩放协变。([维基百科][2])

---

## 10. Born 概率 = 最小 KL 投影;指针基 = 谱极小

在可实现读数字典上,Born 概率等价于参考分布到线性约束族的 **I-投影(最小 KL)**;信息几何的投影与广义毕达哥拉斯定理为运算学基座。稳定读出基对应 $K_{w,h}$ 的谱极小方向(或其函数演算),从而"偏振/指针"成为谱几何对象。**此等价建立在可实现读数字典诱导的线性约束族上;更广场景的证明与可检条件另文给出**。([Stern School of Business][12])

---

## 11. 与 RCA/EBOC 的接口(离散—连续统一)

### 11.1 轨迹—相位嵌入与群延迟速度

将可逆元胞自动机(RCA)轨迹的局部块以稳定窗族嵌入 de Branges–Kreĭn 相位几何,定义"轨迹—相位度量" $d_{\rm TP}$。RCA 的前沿斜率对应 GLS 群延迟导出的有效速度,窗化读数统一离散—连续时间刻度。([普渡大学数学系][6])

### 11.2 EBOC 解释

EBOC 的"静态块"在 GLS 中表现为全局可逆散射网络;观察者为其中移动的滤镜链。"不完备 = 非停机"的对译可表述为:有限窗重构误差的尾项熵通量不可积/不衰,关联 §3 的 NPE 尾项控制。

---

## 12. 范式与算例

### 12.1 相位器计时

**算例（$\omega$ 变量，$\hbar=1$）**：单通道 $S(\omega)=e^{2i\delta(\omega)}$ 时 $\operatorname{tr}\mathsf Q(\omega)=2\delta'(\omega)$。取窄带等效窗 $G(\omega)\approx(w_R*\check h)(\omega)$,并用盒函数近似
$$
G_{\Delta\omega}(\omega)=\frac{2\pi}{\Delta\omega}\,\mathbf 1_{[\omega_0-\Delta\omega/2,\,\omega_0+\Delta\omega/2]}(\omega),
\quad \int G_{\Delta\omega}=2\pi.
$$
则根据定义3.1（含负号）
$$
\begin{aligned}
T &\approx -\int G_{\Delta\omega}(\omega)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega)\,d\omega
=-\int G_{\Delta\omega}(\omega)\,\frac{\delta'(\omega)}{\pi}\,d\omega \\
&=-\frac{2\pi}{\pi\,\Delta\omega}\Big[\delta\!\big(\omega_0+\tfrac{\Delta\omega}{2}\big)-\delta\!\big(\omega_0-\tfrac{\Delta\omega}{2}\big)\Big]
\xrightarrow{\ \Delta\omega\to 0\ }\ -2\,\delta'(\omega_0).
\end{aligned}
$$
在纯延迟 $S(\omega)=e^{-i\omega L/c}$（工程号记）下,$2\delta(\omega)=-\omega L/c$,故 $\delta'(\omega)=-\tfrac{L}{2c}$,于是 $T\approx -2\delta'(\omega_0)=\tfrac{L}{c}$。

**量纲说明**：若以 $E$ 变量书写，则 $\delta'(E)=\delta'(\omega)/\hbar$（在 $\hbar=1$ 下数值相等）。**归一化约定**：因采用 $h\approx\delta$（此处 $\int h=1$）,按 §3.1 归一化处方取 $\int w_R=2\pi$,从而 $G\approx w_R$ 仍满足 $\int G=2\pi$。若 $\int w_R\neq2\pi$,需整体乘以 $\dfrac{\int w_R}{2\pi}$ 的校正因子。（**此处 $G\ge0,\ \int G=2\pi$,因此等价于对 $-\delta'(\omega)/\pi$ 的带内平均。**）(Wigner 相位导数计时)([chaosbook.org][13])

### 12.2 双缝—偏振(交叉项调谐)

按 $\eta$ 调节 which-way 强度,能见度 $V$ 单调降、可辨度 $D$ 单调升,且 $D^2+V^2\le 1$;交叉项仅在两窗未来锥交集内存活。([物理评论链接管理器][10])

### 12.3 红移时钟

以 $(\nu_{\rm src},\nu_{\rm obs})$ 对齐母刻度后,$1+z=\nu_{\rm src}/\nu_{\rm obs}$。由 §6.2 的精确换元,
$$
T_{\rm obs}[w_R,h]
=-\int_{\mathbb R}(w_R*\check h)\!\Big(\frac{E}{1+z}\Big)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE
=\frac{1}{1+z}\,T_{\rm src}\!\big[w_R^{\langle 1/(1+z)\rangle},\,h^{\langle 1/(1+z)\rangle}\big].
$$

### 12.4 双缝延迟擦除(DCQE)

取远场近似下的两缝振幅 $\psi_{1,2}(x)$,屏上选择位置窗—核 $K_{w,h}$($w_R$ 定位于像面区段,$h$ 取近 $\delta$ 核以读出强度)。设源态 $\rho_s$ 为纯态 $\lvert\psi_s\rangle\langle\psi_s\rvert$,$\lvert\psi_s\rangle=\tfrac{1}{\sqrt2}(\lvert1\rangle+e^{i\theta}\lvert2\rangle)$。则

* **无条件**:$I_{\rm uncond}(x)\propto |\psi_1(x)|^2+|\psi_2(x)|^2$。

* **擦除符合**:
$$
I_\pm(x)\ \propto\ |\psi_1(x)|^2+|\psi_2(x)|^2\ \pm\ 2\,\big|\psi_1(x)\psi_2(x)\big|\cos\big(\Delta k\cdot x+\theta+\phi\big).
$$
两图样相位相反,叠加回到无条件分布。

* **无条件群延迟一致性**:信号端的边缘群延迟读数
$$
T_{\rm sig}^{\rm (marg)}[w_R,h]=-\int (w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_{\rm sig}(E)\,dE
$$
与闲置端擦除选择无关;当 $w_R,h$ 满足卡片 II 的带限与 Nyquist 条件时,NPE 误差闭合同步成立。

### 12.5 时间域双缝:超快时变镜(ITO/ENZ)

采用接近 ENZ 区的 ITO 薄膜构成可切换"时间镜",以两次超短泵浦在时刻 $t_1,t_2$ 使反射率快速跃迁,相当于对入射探测脉冲施加两道"时间狭缝"。随间隔 $\Delta t=t_2-t_1$ 调谐,反射谱出现清晰干涉条纹,周期满足 $\Delta\omega \simeq 2\pi/\Delta t$。([Nature][17])

将时间域双缝视作对反射通道的瞬时调制,其对频域的等效作用为乘以
$$
M(\omega)=r_1+r_2e^{-i\omega\Delta t},
$$
其中 $r_{1,2}$ 为两次开启的复幅度。反射谱强度
$$
I_{\rm ref}(\omega)\ \propto\ \big|M(\omega)\big|^2\,I_{\rm in}(\omega)
=\Big(|r_1|^2+|r_2|^2+2|r_1r_2|\cos[\omega\Delta t+\phi]\Big)\,I_{\rm in}(\omega),
$$
$\phi=\arg r_2-\arg r_1$。这与空间双缝在角谱上的条纹完全同构,只是"空间位移 $\leftrightarrow$ 时间延迟"对换成"角频率条纹",§6 的谱缩放—时间互易直接适用。

以等效散射子 $S_{\rm eff}(\omega)=M(\omega)\,S_0(\omega)$ 表示时变镜对静态通道 $S_0$ 的调制。

**相位增量与幺正扩张**：若 $M(\omega)$ 为全通（$|M|\equiv 1$），或在幺正扩张 $\widehat S_{\rm eff}$ 上对应全通因子 $U_M(\omega)$，则相位读数增量由
$$
\delta\left(\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\right)
=\tfrac{1}{2\pi}\tfrac{d}{d\omega}\arg U_M(\omega)
$$
给出条纹相位对 $\omega$ 的导数。一般 $|M|\neq 1$ 的幅度项进入环境迹块,需以 $\mathsf Q(\widehat S_{\rm eff})=-i\,\widehat S_{\rm eff}^\dagger \widehat S_{\rm eff}'$ 评估（遵循卡片 I 的幺正扩张处方）。窗化群延迟读数 $T[w_R,h]=-\int_{\mathbb R}(w_R*\check h)(\omega)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_{\rm eff}(\omega)\,d\omega$ 自然分解为"静态背景 + 时间狭缝相位项",在母刻度上精确对接操作化时间刻度的定义(见 §3.1)。互补律 $D^2+V^2\le 1$(§5)与无信号结论(§5.3、§7.3)保持不变;§4 的前沿下界 $t_*\ge L/c$ 不受开合时序影响,条纹遵循 §3.3 的 NPE 有限阶误差闭合。([Nature][17])

---

## 附录 A:窗化互补 $D^2+V^2\le 1$ 的证明

记 $K=K_{w,h}$。定义两路径的非归一化条件态
$$
\tilde\rho_1:=P_1 K\rho K P_1,\qquad \tilde\rho_2:=P_2 K\rho K P_2,
$$
并归一化
$$
\rho_1:=\frac{\tilde\rho_1}{\operatorname{Tr}\tilde\rho_1},\qquad \rho_2:=\frac{\tilde\rho_2}{\operatorname{Tr}\tilde\rho_2}.
$$
设 $\Pi$ 为二分类最优 POVM,则 Helstrom 距离 $D=\tfrac12|\rho_1-\rho_2|_1$ 给出最小错判界。交叉可见度 $V$ 由 $K$ 的非对角块归一量诱导。以 CPTP 收缩性与 Cauchy–Schwarz 得
$$
D^2+V^2\le 1,
$$
等号在纯态与理想区分/理想相干下取到。([Google 图书][4])

---

## 附录 B:NPE 三分解的上界模板

采用零心母窗 $w_R(E)=w(E/R)$，中心定位于 $E_c$ 时记为 $w_R(E-E_c)$。以下一切导数与积分均相对于 $E$ 而非移相变量计算。*记号统一*:本节出现的 $(w_R h)$ 指函数乘积而非卷积;令
$$
g(E):=(h\!\star\!\rho_{\rm rel})(E),\qquad f(E):=w_R(E-E_c)\,g(E),
$$
后续所有误差界均针对 $f$ 给出（其中 $E_c$ 为窗中心位置）。

*Poisson 基式*:对上述 $f$ 有
$$
\int_{\mathbb R} f(E)\,dE=\Delta\sum_{n\in\mathbb Z} f(E_0+n\Delta)-\sum_{k\ne 0}e^{i(2\pi k/\Delta)E_0}\widehat f\Big(\tfrac{2\pi k}{\Delta}\Big).
$$
若 $\mathrm{supp}\,\widehat f\subset(-2\pi/\Delta,2\pi/\Delta)$,第二项为零(无 alias),积分与无限采样和精确相等。仅当 $f$ 近带限或在实现中截断无穷和时,才引入本文 NPE 的 $\varepsilon_{\rm alias},\varepsilon_{\rm tail}$,以及采用有限阶 Euler–Maclaurin 时的 $\varepsilon_{\rm EM}$。

**Poisson 别名(一般近带限)**:设 $\widehat f(\omega)$ 为 $f$ 的傅里叶变换,则
$$
|\varepsilon_{\rm alias}|\ \le\ \sum_{k\ne 0}\Big|\widehat f\big(\cdot+2\pi k/\Delta\big)\Big|_{L^1},
\qquad \widehat f=\widehat{w_R}\ast\Big(\widehat{h}\cdot\widehat{\rho_{\rm rel}}\Big).
$$
工程估算可使用
$$
|\varepsilon_{\rm alias}|\ \le\ \Bigg(\sum_{k\ne 0}\Big|\widehat{w_R}\big(\cdot+2\pi k/\Delta\big)\Big|_{L^1}\Bigg)\,\Big|\widehat{h}\cdot\widehat{\rho_{\rm rel}}\Big|_{L^\infty},
$$
若 $g$ 再次严格带限,上述求和可有限截断并令别名项为零。

**EM 阶数选择(处方)**:给定目标误差阈值 $\varepsilon_{\rm tol}$,取最小 $M$ 使
$$
\sum_{m=1}^{M}\frac{|B_{2m}|}{(2m)!}\Big|f^{(2m-1)}\Big|_{L^1}\ \le\ \tfrac12\,\varepsilon_{\rm tol},
$$
同时选取 Euler–Maclaurin 余项界 $|R_{2M}|\le \tfrac12\,\varepsilon_{\rm tol}$。这样 $|\varepsilon_{\rm EM}|$ 可控制在既定容差内。

**有限阶 EM**:令取到 $2M$ 阶,则
$$
|\varepsilon_{\rm EM}|\ \le\ \sum_{m=1}^{M}\frac{|B_{2m}|}{(2m)!}\,\Big|f^{(2m-1)}\Big|_{L^1}\;+\;|R_{2M}|,
$$
其中 $R_{2M}$ 为 DLMF 形式余项(可用周期化伯努利函数显式表示并估界)。

**尾项**:若 $w_R(E-E_c)$ 在 $|E-E_c|>\Lambda R$ 上 $L^1$ 可控（即母窗 $w$ 在 $|x|>\Lambda$ 外可控）,且 $|g|_{L^\infty}$ 有界,则
$$
|\varepsilon_{\rm tail}|\ \le\ \Big|w_R(E-E_c)\mathbf 1_{|E-E_c|>\Lambda R}\Big|_{L^1}\,|g|_{L^\infty}
=\Big|w\mathbf 1_{|x|>\Lambda}\Big|_{L^1}\cdot R\,|g|_{L^\infty}.
$$
尺度变换 $R\mapsto\lambda R$ 与谱缩放 $E\mapsto E/(1+z)$ 下,上述上界按傅里叶—采样对偶协变。([维基百科][2])

---

## 附录 C:接口纲要的范畴论骨架

对象:$\mathbf{WScat}$ 的态射为保持卡片 I/II 的滤镜链;$\mathbf{Cau}$ 的态射为保持类光锥与偏序的映射。
$\mathfrak F_{t_*}:\mathbf{WScat}\to\mathbf{Cau}$:**以 $t_*$ 为参数的接口图式**;以前沿集/最早到达集(由 $t_*(\cdot)$ 确定)构造偏序与锥;$\operatorname{tr}\mathsf Q$ 仅用于读数刻度与 $c$ 的等值标定。$t_*$ 可由 §3.4 的 HF 标定从 $T_\gamma$ **实验性确定**,再作为外参输入接口,从而闭合双层框架的往返使用。
反向函子 $\mathfrak G:\mathbf{Cau}\to\mathbf{WScat}$ 与自然同构的存在性为开放问题。

---

## 附录 D:Toeplitz/Berezin 压缩与 de Branges 背景

Toeplitz/Berezin 框架为窗化读数提供算子化实施路径;de Branges 空间提供相位 $\varphi$ 及其导数的全纯—测度对应,从而与谱移—群延迟刻度同一无缝对接。Toeplitz 压缩技术见 [6],Berezin 符号与变换见 [16],de Branges 空间见 [5]。

---

## 参考文献(选)

1. A. Pushnitski, *An integer-valued version of the Birman–Kreĭn formula*, 2010:给出 $\det S(E)=e^{-2\pi i\xi(E)}$ 与相关刻度同一的严式化基准。([arXiv][1])
2. F. T. Smith, *Lifetime Matrix in Collision Theory*, Phys. Rev. 118 (1960):提出 $\mathsf Q=-iS^\dagger S'$ 的群延迟矩阵与其物理解释。([chaosbook.org][7])
3. B.-G. Englert, *Fringe Visibility and Which-Way Information: An Inequality*, PRL 77 (1996):双缝互补不等式 $D^2+V^2\le1$。([物理评论链接管理器][10])
4. C. W. Helstrom, *Quantum Detection and Estimation Theory*, Academic Press (1976):最小错判测度与 Helstrom 界。([Google 图书][4])
5. L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice–Hall (1968):de Branges 相位/空间及 Hermite–Biehler 背景。([普渡大学数学系][6])
6. A. Böttcher, B. Silbermann, *Analysis of Toeplitz Operators*, Springer (1990/2006):Toeplitz 框架与压缩算子技术。
7. DLMF(NIST),§2.10 Euler–Maclaurin、相关余项与误差估计;并见 §24.2 伯努利函数。([dlmf.nist.gov][15])
8. Nyquist–Shannon 采样定理与别名机理(百科/教材性综述)。([维基百科][2])
9. E. C. Titchmarsh, Paley–Wiener/Titchmarsh 定理(因果—解析性与 Hilbert 变换);Kramers–Kronig 关系物理阐释。([Wolfram MathWorld][5])
10. L. Brillouin, *Wave Propagation and Group Velocity*, Academic Press (1960):先驱/前沿速度与因果讨论的经典来源。([互联网档案馆][8])
11. Berezin 协变/逆协变符号与 Berezin 变换(Toeplitz/Berezin 量化)。([SpringerLink][16])
12. R. Tirole *et al.*, *Double-slit time diffraction at optical frequencies*, Nature Phys. 19, 999–1002 (2023):ITO 近 ENZ 区时变镜实现时间域双缝干涉,展示频谱条纹与上升时间接近一个光学周期的证据。([Nature][17])
13. D. Castelvecchi, *Light waves squeezed through 'slits in time'*, Nature News (2023):Nature 新闻对时间域双缝实验的权威解读,引用指出镜面切换可能达 1 fs 量级。([Nature][18])
14. S. Vezzoli *et al.*, *Saturable Time-Varying Mirror Based on an Epsilon-Near-Zero Material*, Phys. Rev. Applied 18, 054067 (2022):ITO–Au 可饱和时变镜的先导工作,实现十倍反射调制与亚 30 fs 级响应。([物理评论链接管理器][19])

---

### 结论要点

* 三位一体刻度 $\varphi'/(2\pi)=\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 统一了相位—密度—群延迟;
* 窗化群延迟读数提供时间的操作化刻度,具可加与**规范协变(相对不变)**,并在 NPE 纪律下**非渐近闭合**;
* 以真空**前沿**规范 $c$ 得到**无超锥传播**与到达时间下界;
* **高频标定桥接**(§3.4):任意固定形状归一窗的蓝移极限 $\lim_{E_0\to\infty}T_\gamma= t_*$,把因果前沿 $t_*$ 作为 $T_\gamma$ 的**可操作极限刻度**;
* **红移—时间**满足**互易标度律**;**分辨率提升**与**红移放大**严格对偶;
* 双缝的窗化互补律 $D^2+V^2\le1$ 与 which-way 调谐在同一母刻度下统一;
* 建立**因果前沿层($t_*$)与操作化群延迟层($T_\gamma$)的双层并行框架**;给出从 GLS 到因果流形的接口纲要;$t_*$ 由 §3.4 的 HF 标定从 $T_\gamma$ 实验确定,反向函子与自然同构存在性为开放问题。

[1]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://en.wikipedia.org/wiki/Nyquist%E2%80%93Shannon_sampling_theorem?utm_source=chatgpt.com "Nyquist–Shannon sampling theorem"
[4]: https://books.google.com/books/about/Quantum_Detection_and_Estimation_Theory.html?id=Ne3iT_QLcsMC&utm_source=chatgpt.com "Quantum Detection and Estimation Theory"
[5]: https://mathworld.wolfram.com/TitchmarshTheorem.html?utm_source=chatgpt.com "Titchmarsh Theorem -- from Wolfram MathWorld"
[6]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[7]: https://chaosbook.org/library/SmithDelay60.pdf?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory"
[8]: https://archive.org/details/wavepropagationg00bril_0?utm_source=chatgpt.com "Wave propagation and group velocity : Brillouin, Léon, 1889"
[9]: https://link.aps.org/pdf/10.1103/PhysRevLett.77.2154?utm_source=chatgpt.com "Fringe Visibility and Which-Way Information: An Inequality"
[10]: https://link.aps.org/doi/10.1103/PhysRevLett.77.2154?utm_source=chatgpt.com "Fringe Visibility and Which-Way Information: An Inequality"
[11]: https://ncatlab.org/nlab/show/Wightman%2Baxioms?utm_source=chatgpt.com "Wightman axioms in nLab"
[12]: https://pages.stern.nyu.edu/~dbackus/BCZ/entropy/Csiszar_geometry_AP_75.pdf?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions and ..."
[13]: https://chaosbook.org/library/WignerDelay55.pdf?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering ..."
[15]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[16]: https://link.springer.com/chapter/10.1007/978-1-4612-0255-4_12?utm_source=chatgpt.com "Berezin-Toeplitz Quantization"
[17]: https://www.nature.com/articles/s41567-023-01993-w "Double-slit time diffraction at optical frequencies | Nature Physics"
[18]: https://www.nature.com/articles/d41586-023-00968-4 "Light waves squeezed through 'slits in time'"
[19]: https://link.aps.org/doi/10.1103/PhysRevApplied.18.054067?utm_source=chatgpt.com "Saturable Time-Varying Mirror Based on an Epsilon-Near-Zero Material"
