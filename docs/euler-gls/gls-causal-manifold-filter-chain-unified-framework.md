# GLS—因果流形—滤镜链统一框架

## ——窗化群延迟、红移与光速的公理化理论、互构纲要与非渐近误差闭合(完整版)

**Version: 3.11**

## 摘要

在"宇宙 = 广义光结构(Generalized Light Structure, GLS)""观察者 = 滤镜链(windowed compression → CP 通道 → POVM → 阈值计数)""因果 = 类光锥偏序"的统一语境中,建立以
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad \mathsf Q(E)=-i\,S(E)^\dagger \tfrac{dS}{dE}(E)\ }
$$
为母刻度(相位导数—相对态密度—Wigner–Smith 群延迟迹)的公理化理论。核心结果:(i)以**窗化群延迟读数**提供时间的操作化刻度,并证明其串并联可加、规范协变/相对不变(当 $U,V$ 与能量无关或 $\det U\cdot\det V\equiv1$ 时保持不变);在真空链路上,其 Nyquist 极限与前沿速度标定 $c$ 等值;(ii)以谱缩放刻画**红移**并证明与时间的互易标度律;(iii)以真空**前沿**规范光速 $c$,给出任意物理通道的**前沿下界**与**无超锥传播**;(iv)提出"GLS ↔ 因果流形"的**互构纲要**,给出构造骨架与一致性条件,**严格证明及自然性验证另文呈现**;(v)在同一账本中统一**波/粒二象性**与双缝的窗化互补不等式 $D^2+V^2\le 1$;(vi)阐明"分辨率提升 = 宇宙膨胀(红移放大)"的严格对偶,并给出 Nyquist–Poisson–Euler–Maclaurin(NPE)**有限阶**误差闭合与工程化处方。理论全程采用算子—测度—函数语言(Toeplitz/Berezin 压缩 $K_{w,h}$,读数 = 对谱测度的线性泛函),在全局幺正公设下将一切时间/密度读数统一由 $\mathsf Q=-iS^\dagger S'$ 定义,实验性非幺正均通过幺正扩张 $\widehat S$ 回推母刻度。

---

## Notation & Axioms / Conventions

### 单位与常数规范

默认采用 $\hbar=1$(必要时亦可取 $c=1$)。若恢复 SI 单位,所有由 $\operatorname{tr}\mathsf Q$ 导出的时间读数需乘以 $\hbar$,即 $T_{\rm phys}=\hbar\,T$;相应地,若 $c$ 未取为 1,则需按 $L/c$ 恢复光程量纲。

**术语对齐**:本文中"时间"如无特别说明,指因果时间 $t_*$;$T_\gamma[w_R,h]$ 称为窗化群延迟读数或操作化时间刻度。

### 卡片 I（刻度同一｜全局幺正公设）

**公设（全局幺正）**：宇宙视作封闭系统;存在以能量 $E$ 为坐标的绝对连续谱区间,在本工作带内散射矩阵 $S(E)\in C^1\cap\mathsf U(N)$ 幺正。由 Birman–Kreĭn 公式
$$
\det S(E)=e^{-2\pi i\xi(E)},\qquad \mathsf Q(E)=-i\,S^\dagger(E)S'(E),
$$
**推出**
$$
\rho_{\rm rel}(E):=-\xi'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E).
$$
我们据此**定义**相位测度 $\mu_\varphi$:令
$$
 d\mu_\varphi^{\rm ac}(E):=\rho_{\rm rel}(E)\,dE,
$$
等价写作
$$
\boxed{\,\frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\xi'(E)\,}.
$$
此处 $\varphi$ 为实现该密度的相位函数,其符号仅随 $\rho_{\rm rel}$ 而定。

**处方**：任何实验性损耗/增益均视作对环境自由度的迹出;理论分析统一通过幺正扩张 $\widehat S(E)$ 处理,并以 $\mathsf Q(\widehat S)=-i\widehat S^\dagger\widehat S'$ 评估全部时间/密度读数。本文不引入 $\widetilde{\mathsf Q}:=-iS^{-1}S'$。

### 卡片 II(有限阶 EM 与极点 = 主尺度)

一切离散—连续换算与窗化读数遵循 NPE 三分解
$$
\varepsilon_{\rm total}=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$
若 $h,w$ **严格带限**,其频域支撑满足 $\mathrm{supp}\,\widehat h\subset[-\Omega_h,\Omega_h]$、$\mathrm{supp}\,\widehat w\subset[-\Omega_w,\Omega_w]$。当采用窗族 $w_R(E)=w((E-E_0)/R)$ 时,$\mathrm{supp}\,\widehat{w_R}\subset[-\Omega_w/R,\Omega_w/R]$。因此若采样间隔
$$
\Delta\le \frac{\pi}{\Omega_h+\Omega_w/R},
$$
则 $\varepsilon_{\rm alias}=0$(Nyquist–Shannon);近似带限/有效带宽场景下,$\varepsilon_{\rm alias}$ 保留为可估上界的残差项。$\varepsilon_{\rm EM}$ 由**有限阶** Euler–Maclaurin(端点伯努利层与显式余项)控制;$\varepsilon_{\rm tail}$ 由窗外衰减控制。奇性不增,极点决定主尺度。([维基百科][2])

### 记号约定

约定 $(h\star f)(E):=(h*f)(E)$,其中 $\check h(E):=h(-E)$,星号表示对能量变量的卷积。窗族取 $w_R(E)=w((E-E_0)/R)$,默认 $w$ 为偶函数且属于 $L^1\cap C^M$ 以支撑所用 Euler–Maclaurin 阶数;核 $h$ 亦取 $h\in L^1\cap C^M$,具体归一方式在上下文另行说明。

**傅里叶规范**: $\widehat f(\omega):=\displaystyle\int_{\mathbb R} f(E)\,e^{-i\omega E}\,dE$, $f(E)=\displaystyle\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\omega)\,e^{i\omega E}\,d\omega$。在此规范下,Nyquist 条件 $\Delta\le \pi/(\Omega_h+\Omega_w/R)$ 与附录 B 的 Poisson 公式中 $2\pi$ 因子与相位约定一致。

$S(E)\in\mathsf U(N)$:多通道散射矩阵,$\mathsf Q=-iS^\dagger S'$。$\quad$ $\rho_{\rm rel}=-\xi'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q$。$\quad$ 窗—核:偶窗 $w_R(E)=w((E-E_0)/R)$,前端核 $h$。$\quad$ 压缩 $K_{w,h}$:Toeplitz/Berezin 型。**引理 0.1(刻度同一的迹—谱移关系)** 由 $\det S(E)=e^{-2\pi i\xi(E)}$ 与 $\mathsf Q=-iS^\dagger S'$ 可得 $\tfrac{d}{dE}\log\det S(E)=-2\pi i\,\xi'(E)$ 和 $\operatorname{tr}\mathsf Q(E)=-i\,\tfrac{d}{dE}\log\det S(E)$,从而 $(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)=-\xi'(E)$。([SpringerLink][3])

---

## 1. GLS 与滤镜链

### 1.1 对象层

**定义 1.1(GLS)** 设
$$
\mathfrak U=(\mathcal H,\ S(E),\ \mu_\varphi,\ \mathcal W),
$$
其中 $d\mu_\varphi^{\rm ac}=(\varphi'/\pi)\,dE$,$\mathcal W$ 为可实施窗—核字典。任意态 $\rho$ 的窗化读数为
$$
\mathrm{Obs}(w_R,h;\rho)=\operatorname{Tr}(K_{w,h}\rho)
=\!\int_{\mathbb R}\! w_R(E)\,[\,h\!\star\!\rho_\rho\,](E)\,dE\;+\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$
其中 $\rho_\rho(E):=\dfrac{d\mu_\rho^{\rm ac}}{dE}$ 为态 $\rho$ 相对于 Lebesgue 测度 $dE$ 的能谱密度;而 $\rho_{\rm rel}(E):=-\xi'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$ 属于通道/散射数据。仅当选取参考态 $\rho_{\rm ref}$ 满足 $d\mu_{\rho_{\rm ref}}^{\rm ac}=\rho_{\rm rel}(E)\,dE$ 时,才可以在公式中以 $\rho_{\rm rel}$ 替换 $\rho_\rho$;其余情形必须显式区分二者。

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
若实验性非幺正引入的奇异贡献不可忽略,统一并入幺正扩张 $\widehat S$ 的环境自由度而不计入 $\mu_\varphi$ 的奇异部分。在 LTI 与因果假设下,Paley–Wiener/Titchmarsh 与 Kramers–Kronig–Hilbert 关系推出时域冲激响应 $g(t)$ 的单向支撑(规范后 $t\ge 0$)及实/虚部的 Hilbert 共轭。

**定义 2.1(前沿时间可达预序)** 设链集合 $\Gamma(x,y):=\{\gamma:x\to y\}$。若 $\Gamma(x,y)\neq\varnothing$,定义
$$
t_*(\gamma):=\inf\{\,t:\,g_\gamma(t;L)\neq 0\,\},\qquad
\tau(x,y):=\inf_{\gamma\in\Gamma(x,y)} t_*(\gamma),\qquad
L_*(x,y):=\inf_{\gamma\in\Gamma(x,y)} L(\gamma).
$$
约定:当 $\Gamma(x,y)=\varnothing$ 时,$\tau(x,y)$ 与 $L_*(x,y)$ 记为 $+\infty$,且关系 $x\preceq y$ **不成立**。据此定义可达预序
$$
x\preceq y\;\Longleftrightarrow\;\Gamma(x,y)\neq\varnothing\ \text{且}\ \tau(x,y)\ge \frac{L_*(x,y)}{c}.
$$
(**充分条件**:若 **$\Gamma(x,y)\neq\varnothing$** 且对所有 $\gamma:x\to y$ 均有 $t_*(\gamma)\ge L(\gamma)/c$,则 $x\preceq y$。*注*:反向蕴含一般不成立,除非满足 §4 的补强前提并且极小链同时实现 $\tau$ 与 $L_*$。)

**约定(恒等链)** 对每个 $x$,$\Gamma(x,x)$ 包含恒等链 $e_x$,规定 $L(e_x)=0$,$g_{e_x}(t;0)=\delta(t)$,故 $t_*(e_x)=0$。于是 $\tau(x,x)=0=L_*(x,x)/c$,自反性由定义立即得到。

**假设(无闭因果回路)**:不存在 $x\neq y$ 使得 $x\preceq y$ 且 $y\preceq x$。定义类光锥边界
$$
\partial J^+(x):=\{\,y\in J^+(x):\ \tau(x,y)=L_*(x,y)/c\,\},\qquad
J^+(x):=\{\,y:\Gamma(x,y)\neq\varnothing,\ x\preceq y\,\}.
$$
**命题 2.2(偏序性,依赖前沿下界)** 在**前沿下界假设**(即对任意链 $\gamma$ 均有 $t_*(\gamma)\ge L(\gamma)/c$;该假设由 §4 的前提 (i)–(iv) 可推出,见定理 4.2)与"无闭因果回路"条件下,$\preceq$ 为偏序。

*证明*:自反性来自恒等链 $e_x$;设 $x\preceq y$ 与 $y\preceq z$,取任意拼接链 $\gamma=\gamma_{z\leftarrow y}\circ\gamma_{y\leftarrow x}$。由卷积支撑的 Minkowski 和性质,有
$$
t_*(\gamma)\ \ge\ t_*(\gamma_{z\leftarrow y})+t_*(\gamma_{y\leftarrow x})\ (\text{边界不抵消时取等}),
$$
再由前沿下界得到
$$
t_*(\gamma)\ \ge\ \frac{L(\gamma_{z\leftarrow y})+L(\gamma_{y\leftarrow x})}{c}\ \ge\ \frac{L_*(x,z)}{c}.
$$
因此对全体链取下确界得 $\tau(x,z)\ge L_*(x,z)/c$,从而 $x\preceq z$;反对称性由"无闭因果回路"给出。□

窗化群延迟读数 $T_\gamma[w_R,h]$ 是相位导数的频域加权读数,没有与前沿时间 $t_*(\gamma)$ 的一般大小比较关系。

### 2.2 相位奇性 ⇒ 最短到达与因果边界

de Branges 相位的跳变/极点(Hermite–Biehler 零点、散射相移突变)对应到达奇性(驻相/等时集),为光锥边缘提供可检峰值标记。([普渡大学数学系][6])

---

## 3. 操作化时间刻度:窗化群延迟读数

### 3.1 定义

下述 $T_\gamma[w_R,h]$ 为相位导数的带内读数,用作时间刻度的操作化读数,并非前沿时间 $t_*$。

**定义 3.1(窗化群延迟读数)** 对因果可达的传播—读出链 $\gamma$ 与窗—核 $(w_R,h)$,定义
$$
\boxed{\ T_\gamma[w_R,h]\;:=\;\int_{\mathbb R} (w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\gamma(E)\,dE\ },\qquad \check h(E):=h(-E),
$$
并约定 $(h\star f)(E)=(h*f)(E)$。等价地,
$$
T_\gamma[w_R,h]=\int_{\mathbb R} w_R(E)\,[\,h\!\star\!\rho_{\rm rel}\,](E)\,dE.
$$
此量在母刻度上实现"带内时间"的可实现读数。后续关于采样与 NPE 的一切公式均作用于被积函数
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
*证明*:由 $(S_2S_1)'=S_2'S_1+S_2S_1'$ 得 $\mathsf Q(S_2S_1)=S_1^\dagger\mathsf Q(S_2)S_1+\mathsf Q(S_1)$;取迹用循环不变性即得第一式;代入定义得第二式。*备注(幺正版)*:由**卡片 I(刻度同一｜全局幺正公设)**可知任意串/并联网络可视为单一幺正扩张 $\widehat S$ 的块构造,故 $\operatorname{tr}\mathsf Q$ 与 $T_\gamma[w_R,h]$ 的可加性在幺正框架内直接成立,无需其他替代处方。([chaosbook.org][7])

**命题 3.3(规范协变与相对不变)** 设能量依赖基变换 $S\mapsto U(E)SV(E)$,则
$$
\operatorname{tr}\mathsf Q(USV)=\operatorname{tr}\mathsf Q(S)-i\,\operatorname{tr}(U^\dagger U')-i\,\operatorname{tr}(V'V^\dagger).
$$
*推导要点(算子级)*:
$$
\mathsf Q(USV)=V^\dagger\mathsf Q(S)V-i\,V^\dagger S^\dagger\big(U^\dagger U'\big)SV-i\,V^\dagger V'.
$$
取迹并利用循环不变性即可得到上述恒等式。当 $U,V$ 与能量无关或 $\det U(E)\det V(E)\equiv1$ 时,附加项消失,故 $\operatorname{tr}\mathsf Q$ 保持不变。一般情形采用相对读数
$$
T_{\rm rel}(\gamma):=T_\gamma[w_R,h;S]-T_\gamma[w_R,h;S_{\rm ref}],
$$
以消除规范项。([普渡大学数学系][6])

### 3.3 非渐近误差闭合(NPE)

**命题 3.4(离散实现；精确与近似的分立表述)** 设 $f(E):=w_R(E)\,[\,h\!\star\!\rho_{\rm rel}\,](E)$,采样点 $E_n=E_0+n\Delta$。

**(A) 严格带限 + Nyquist 条件(精确等式)**:若 $\widehat w,\widehat h$ 严格带限且 $f\in\mathsf{PW}_B\cap L^1$，其中 $B:=\Omega_h+\Omega_w/R$,并满足
$$
\Delta\le \frac{\pi}{B},
$$
则由 Poisson 求和得
$$
\boxed{\ T_\gamma[w_R,h]=\int_{\mathbb R} f(E)\,dE=\Delta\sum_{n\in\mathbb Z} f(E_n)\ }.
$$
此时 $\varepsilon_{\rm alias}=\varepsilon_{\rm EM}=\varepsilon_{\rm tail}=0$。

**(B) 近带限/数值截断(NPE 三分解)**:若 $f$ 仅近似带限或实现上将无穷和截断为 $|n|\le N$,则
$$
T_\gamma[w_R,h]=\Delta\sum_{|n|\le N} f(E_n)+\varepsilon_{\rm tail}+\varepsilon_{\rm alias}+\varepsilon_{\rm EM},
$$
其中
$$
\varepsilon_{\rm tail}:=\Delta\sum_{|n|>N} f(E_n),\qquad |\varepsilon_{\rm alias}|\le\sum_{k\ne 0}\Big|\widehat f\big(\cdot+2\pi k/\Delta\big)\Big|_{L^1},
$$
而 $\varepsilon_{\rm EM}$ 仅在以有限阶 Euler–Maclaurin 近似无穷和(或对近带限 $f$ 的修正积分)时出现,其上界参见附录 B。*说明*: 本命题将理论上的等式 (A) 与工程实践的 NPE 分解 (B) 严格区分,避免在无 alias 的情形下引入不存在的 EM/尾项。([chaosbook.org][7])

---

**前提**:以下关于前沿与无超锥传播的命题建立在:

(i) **LTI + 因果 + 上半平面解析性(Hardy)**:频域响应的上半平面解析性与 Hardy 边值保证 Kramers–Kronig–Hilbert 关系;**若进一步假设被动性**,则可归入 Herglotz 类;

(ii) **高频真空极限**:对任一传播段 $T(\omega;L)$,有 $\lim_{|\omega|\to\infty}T(\omega;L)\,e^{-i\omega L/c}=1$(或等价地 $\lim_{|\omega|\to\infty}n(\omega)=1$);

(iii) **局域性/有限传播速度**:链由满足双曲型局域动力学的元件组成,其格林函数(或冲激响应)存在有限波前;

(iv) **被动性**:无主动增益导致的超前响应。

## 4. 光速与类光锥:前沿定标与无超锥传播

### 4.1 光速的前沿规范

**定义 4.1(光速 $c$)** 真空冲激响应 $g_0(t;L)$ 的最早非零到达 $t_{\rm front}(L)$ 给出
$$
c:=\lim_{L\to\infty}\frac{L}{t_{\rm front}(L)}\quad(\text{或取上确界作规范常数}).
$$
其中 $L$ 表示在**真空度规**下两点间的**光程(测地长度)**,其定义独立于介质;介质的色散与吸收效应仅体现于系统响应而不改变前沿下界的几何基准。该 $L$ 亦用于 §4.2 中 $t_*(\gamma)\ge L/c$ 的判定基准。前沿速度与因果一致(Sommerfeld–Brillouin 先驱)。([互联网档案馆][8])

### 4.2 无超锥传播——前沿读数

**定理 4.2(前沿下界)** 在上述前提下,任意链 $\gamma$ 的输出冲激响应 $g_\gamma(t;L)$ 在 $t<L/c$ 恒为 0,因而
$$
t_*(\gamma)\ \ge\ L/c,
$$
且等号当且仅当链的高频传播子在真空极限下沿测地达到。*注*:窗化群延迟读数 $T_\gamma[w_R,h]$ 仍非前沿时间,窄带/共振下可取负,二者无普适比较不等式。([Wolfram MathWorld][5])

本文一切因果与无信号结论仅以 $t_*$ 与类光锥偏序为准绳;$T_\gamma$ 仅作为可测读数,不参与偏序的定义。

---

## 5. 波—粒统一与"不同画面"的来源

### 5.1 同源二读数:期望与计数

同一 $K_{w,h}$ 诱导
$$
\text{(波)}\ \ \mathrm{Obs}(w_R,h)=\operatorname{Tr}(K_{w,h}\rho),\qquad
\text{(粒)}\ \ \mathbb E N_{w,h}=\operatorname{Tr}\big(K_{w,h}\,\Phi(\rho)\big)=\operatorname{Tr}\big(\Phi^\dagger(K_{w,h})\,\rho\big).
$$
其中 $\Phi^\dagger$ 为 $\Phi$ 的 Heisenberg 伴随。二者时间标度均由 $T_\gamma[w_R,h]$ 计量;$\Phi,\{M_i\},\mathcal M_{\rm th}$ 仅改变统计外观,不改母刻度。([Google 图书][4])

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

**定理 5.4(无信号与群延迟不变)** 设闲置端采用任意完备仪式 $\{\mathcal I_a^i\}$(包含 which-way 或擦除作特别情形),则

(i) 屏上无条件分布不依赖闲置选择与测量先后:
$$
\sum_a I_a(w_R,h)=\operatorname{Tr}\big(K\,\operatorname{Tr}_i\rho_{si}\big),\qquad \sum_a \mathcal I_a^i=\Phi_i\ \text{为 CPTP};
$$

(ii) 信号通道的窗化群延迟读数与擦除选择无关:
$$
T_{\rm sig}[w_R,h\mid \{\mathcal I_a^i\}]=\int (w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_{\rm sig}(E)\,dE=T_{\rm sig}[w_R,h].
$$

*证明要点*:完备性与偏迹给出 $\sum_a(\mathrm{Id}_s\otimes\mathcal I_a^i)(\rho_{si})=(\mathrm{Id}_s\otimes\Phi_i)(\rho_{si})$,取 $\operatorname{Tr}_i$ 得无条件不变;$\mathsf Q_{\rm sig}$ 由信号散射子决定,与闲置的本地测量基无关,故 $T_{\rm sig}$ 不变。

*备注(延迟与类空间分离)*:当屏与闲置读出区域类空间分离时,由 §7 的窗化微因果律,$[K[U_x],\mathbf 1\otimes\Pi_\alpha[U_y]]=0$,因而"延迟选择"不引入任何超因果效应;仅在符合(条件化)层面重排样本,边缘统计与群延迟读数保持不变。其无信号与时间顺序独立的根源来自由 $t_*$ 决定的偏序结构,而非 $T_\gamma$。

---

## 6. 红移:谱缩放与时间互易

### 6.1 定义

**定义 6.1(红移)** 对源—受体,母刻度上
$$
1+z=\frac{E_{\rm src}}{E_{\rm obs}}=\frac{\nu_{\rm src}}{\nu_{\rm obs}}.
$$

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
=\int_{\mathbb R}(w_R*\check h)\!\Big(\frac{E}{1+z}\Big)\,
\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\gamma(E)\,dE.
$$
**带限与采样协变**:若 $\widehat w,\widehat h$ 严格带限,则 $w_R^{\langle a\rangle},h^{\langle a\rangle}$ 仍严格带限,Nyquist 纪律随缩放变为 $\Delta\le \pi/\big(a(\Omega_h+\Omega_w/R)\big)$,故卡片 II 的前提在该模型下保持有效。

*证明要点*:$\operatorname{tr}\mathsf Q_{\rm obs}(E)=(1+z)\,\operatorname{tr}\mathsf Q\big((1+z)E\big)$,以及$(f*g)\big(aE\big)=a\,\big(f^{\langle a\rangle}*g^{\langle a\rangle}\big)(E)$。

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

## 8. 互构纲要:GLS ↔ 因果流形(构造骨架)

### 8.1 范畴

$\mathbf{WScat}$:对象为 $(S,\mu_\varphi,\mathcal W)$,态射为保持卡片 I/II 的滤镜链;
$\mathbf{Cau}$:对象为因果流形 $(\mathcal M,\preceq)$,其中 $\preceq$ 为由 §2.1 的可达预序在无闭因果回路假设下得到的偏序(或一般情形下的商偏序);态射为保持类光锥与该偏序的映射。

### 8.2 构造与结论

**纲要 8.1(GLS ↔ 因果流形的互构骨架)** 存在构造性的函子
$$
\mathfrak F:\mathbf{WScat}\to\mathbf{Cau},\qquad \mathfrak G:\mathbf{Cau}\to\mathbf{WScat},
$$
并预期存在自然同构 $\mathfrak F\circ\mathfrak G\simeq \mathrm{Id}_{\mathbf{Cau}}、\mathfrak G\circ\mathfrak F\simeq \mathrm{Id}_{\mathbf{WScat}}$。本稿仅给出构造骨架,严格证明与自然性验证将另文阐述。*构造要点*:$\mathfrak F$ 以前沿集/最早到达集(由 $t_*(\cdot)$ 确定)与相位奇性生成偏序与锥;$\operatorname{tr}\mathsf Q$ 仅用于读数层面的刻度与标定(Nyquist 极限与 $c$ 等值);$\mathfrak G$ 以固有时间/光锥参数化构造带限窗—核并施以 Berezin 压缩,使 $\varphi'/\pi=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 与 NPE 闭合同步成立。([SpringerLink][3])

---

## 9. 分辨率—红移对偶与尺度重整

令带限偶窗 $w\in\mathsf{PW}_\Omega$,统一取
$$
w_R(E)=w\!\big((E-E_0)/R\big).
$$
分辨率提升 $R\mapsto\lambda R$($\lambda>1$)对应于红移放大 $E\mapsto E/(1+z)$,两者在 Nyquist 纪律下完全对偶。在该对偶框架下,别名关断,EM 端点误差与尾项随 $R$ 的演化按可计算律缩放,并与谱缩放协变。([维基百科][2])

---

## 10. Born 概率 = 最小 KL 投影;指针基 = 谱极小

在可实现读数字典上,Born 概率等价于参考分布到线性约束族的 **I-投影(最小 KL)**;信息几何的投影与广义毕达哥拉斯定理为运算学基座。稳定读出基对应 $K_{w,h}$ 的谱极小方向(或其函数演算),从而"偏振/指针"成为谱几何对象。([Stern School of Business][12])

---

## 11. 与 RCA/EBOC 的接口(离散—连续统一)

### 11.1 轨迹—相位嵌入与群延迟速度

将可逆元胞自动机(RCA)轨迹的局部块以稳定窗族嵌入 de Branges–Kreĭn 相位几何,定义"轨迹—相位度量" $d_{\rm TP}$。RCA 的前沿斜率对应 GLS 群延迟导出的有效速度,窗化读数统一离散—连续时间刻度。([普渡大学数学系][6])

### 11.2 EBOC 解释

EBOC 的"静态块"在 GLS 中表现为全局可逆散射网络;观察者为其中移动的滤镜链。"不完备 = 非停机"的对译可表述为:有限窗重构误差的尾项熵通量不可积/不衰,关联 §3 的 NPE 尾项控制。

---

## 12. 范式与算例

### 12.1 相位器计时

单通道 $S(E)=e^{2i\delta(E)}$ 时 $\operatorname{tr}\mathsf Q(E)=2\delta'(E)$。窄带窗近似:
$$
T\approx \int w_R(E)\frac{\delta'(E)}{\pi}\,dE
\approx \frac{1}{\pi}\Big[\delta\!\big(E_0+\tfrac{\Delta E}{2}\big)-\delta\!\big(E_0-\tfrac{\Delta E}{2}\big)\Big].
$$
(Wigner 相位导数计时)([chaosbook.org][13])

### 12.2 双缝—偏振(交叉项调谐)

按 $\eta$ 调节 which-way 强度,能见度 $V$ 单调降、可辨度 $D$ 单调升,且 $D^2+V^2\le 1$;交叉项仅在两窗未来锥交集内存活。([物理评论链接管理器][10])

### 12.3 红移时钟

以 $(\nu_{\rm src},\nu_{\rm obs})$ 对齐母刻度后,$1+z=\nu_{\rm src}/\nu_{\rm obs}$。由 §6.2 的精确换元,
$$
T_{\rm obs}[w_R,h]
=\int_{\mathbb R}(w_R*\check h)\!\Big(\frac{E}{1+z}\Big)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE
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

* **群延迟一致性**:对任何 $\alpha\in\{\pm, I_1,I_2\}$,
$$
T_{\rm sig}[w_R,h\mid \alpha]=\int (w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_{\rm sig}(E)\,dE,
$$
与擦除选择无关;当 $w_R,h$ 满足卡片 II 的带限与 Nyquist 条件时,NPE 误差闭合同步成立。

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

以等效散射子 $S_{\rm eff}(\omega)=M(\omega)\,S_0(\omega)$ 表示时变镜对静态通道 $S_0$ 的调制,相位读数增量由
$$
\delta\left(\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\right)
=\tfrac{1}{2\pi}\tfrac{d}{d\omega}\arg M(\omega),
$$
给出条纹相位对 $\omega$ 的导数。窗化群延迟读数 $T[w_R,h]=\int_{\mathbb R}(w_R*\check h)(\omega)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_{\rm eff}(\omega)\,d\omega$ 自然分解为"静态背景 + 时间狭缝相位项",在母刻度上精确对接操作化时间刻度的定义(见 §3.1)。互补律 $D^2+V^2\le 1$(§5)与无信号结论(§5.3、§7.3)保持不变;§4 的前沿下界 $t_*\ge L/c$ 不受开合时序影响,条纹遵循 §3.3 的 NPE 有限阶误差闭合。([Nature][17])

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

取偶窗 $w_R(E)=w((E-E_0)/R)$,其中 $E_0$ 为中心频率。以下一切导数与积分均相对于 $E$ 而非移相变量计算。*记号统一*:本节出现的 $(w_R h)$ 指函数乘积而非卷积;令
$$
g(E):=(h\!\star\!\rho_{\rm rel})(E),\qquad f(E):=w_R(E)\,g(E),
$$
后续所有误差界均针对 $f$ 给出。

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

**尾项**:若 $w_R$ 在 $|E-E_0|>\Lambda R$ 上 $L^1$ 可控,且 $|g|_{L^\infty}$ 有界,则
$$
|\varepsilon_{\rm tail}|\ \le\ \Big|w_R\mathbf 1_{|E-E_0|>\Lambda R}\Big|_{L^1}\,|g|_{L^\infty}.
$$
尺度变换 $R\mapsto\lambda R$ 与谱缩放 $E\mapsto E/(1+z)$ 下,上述上界按傅里叶—采样对偶协变。([维基百科][2])

---

## 附录 C:互构纲要的范畴论骨架

对象:$\mathbf{WScat}$ 的态射为保持卡片 I/II 的滤镜链;$\mathbf{Cau}$ 的态射为保持类光锥与偏序的映射。
$\mathfrak F$:以前沿集/最早到达集构造偏序与锥;$\operatorname{tr}\mathsf Q$ 仅用于读数刻度与 $c$ 的等值标定。
$\mathfrak G$:以固有时间构造带限窗—核并施以 Berezin 压缩,使刻度同一与 NPE 闭合同步成立。([SpringerLink][3])

---

## 附录 D:Toeplitz/Berezin 压缩与 de Branges 背景

Toeplitz/Berezin 框架为窗化读数提供算子化实施路径;de Branges 空间提供相位 $\varphi$ 及其导数的全纯—测度对应,从而与谱移—群延迟刻度同一无缝对接。([SpringerLink][3])

---

## 参考文献(选)

1. A. Pushnitski, *An integer-valued version of the Birman–Kreĭn formula*, 2010:给出 $\det S(E)=e^{-2\pi i\xi(E)}$ 与相关刻度同一的严式化基准。([arXiv][1])
2. F. T. Smith, *Lifetime Matrix in Collision Theory*, Phys. Rev. 118 (1960):提出 $\mathsf Q=-iS^\dagger S'$ 的群延迟矩阵与其物理解释。([chaosbook.org][7])
3. B.-G. Englert, *Fringe Visibility and Which-Way Information: An Inequality*, PRL 77 (1996):双缝互补不等式 $D^2+V^2\le1$。([物理评论链接管理器][10])
4. C. W. Helstrom, *Quantum Detection and Estimation Theory*, Academic Press (1976):最小错判测度与 Helstrom 界。([Google 图书][4])
5. L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice–Hall (1968):de Branges 相位/空间及 Hermite–Biehler 背景。([普渡大学数学系][6])
6. A. Böttcher, B. Silbermann, *Analysis of Toeplitz Operators*, Springer (2006):Toeplitz 框架与压缩算子技术。([SpringerLink][14])
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

* 三位一体刻度 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 统一了相位—密度—群延迟;
* 窗化群延迟读数提供时间的操作化刻度,具可加与**规范协变(相对不变)**,并在 NPE 纪律下**非渐近闭合**;
* 以真空**前沿**规范 $c$ 得到**无超锥传播**与到达时间下界;
* **红移—时间**满足**互易标度律**;**分辨率提升**与**红移放大**严格对偶;
* 双缝的窗化互补律 $D^2+V^2\le1$ 与 which-way 调谐在同一母刻度下统一;
* 提出 **GLS ↔ 因果流形** 的互构纲要,保留自然同构的严格证明与验证为后续工作。

[1]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://en.wikipedia.org/wiki/Nyquist%E2%80%93Shannon_sampling_theorem?utm_source=chatgpt.com "Nyquist–Shannon sampling theorem"
[3]: https://link.springer.com/book/10.1007/978-3-662-02652-6?utm_source=chatgpt.com "Analysis of Toeplitz Operators"
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
[14]: https://link.springer.com/book/10.1007/3-540-32436-4?utm_source=chatgpt.com "Analysis of Toeplitz Operators"
[15]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[16]: https://link.springer.com/chapter/10.1007/978-1-4612-0255-4_12?utm_source=chatgpt.com "Berezin-Toeplitz Quantization"
[17]: https://www.nature.com/articles/s41567-023-01993-w "Double-slit time diffraction at optical frequencies | Nature Physics"
[18]: https://www.nature.com/articles/d41586-023-00968-4 "Light waves squeezed through 'slits in time'"
[19]: https://link.aps.org/doi/10.1103/PhysRevApplied.18.054067?utm_source=chatgpt.com "Saturable Time-Varying Mirror Based on an Epsilon-Near-Zero Material"
