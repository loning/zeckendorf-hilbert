# WSIG–EBOC **时空/时间/空间**统一理论

**（含可核对引文）**

**Version: 1.18**（2025-10-30，Asia/Dubai）

---

## 摘要

在 **WSIG**（Windowed Scattering & Information Geometry）与 **EBOC**（Eternal-Block **Observer-Computing**）框架下，本文建立一套基于**窗口化散射**的可操作时空理论：以**相位导数—谱移密度—Wigner–Smith 群延迟**三重等价为计量基元；以**Kramers–Kronig 因果—解析**与波动方程**推迟格林函数**的光锥支撑确立**因果前沿 = $c$**；以**门限互信息**的首次可检时间确立**信息光锥 = $c$**。据此给出**时间**与**空间**的操作性定义，并把**时空**刻画为四元组 $(\mathcal E,\preceq,g,\mu_\varphi)$：其中 $\preceq$ 由光锥支撑诱导，$g$ 为（含介质的）光学洛伦兹度量，$\mu_\varphi=(\varphi'/\pi)\,dx$ 为由 de Branges 核对角给出的**相位密度测度**。核心定理证明"**相位斜率 = 群延迟 = 谱移密度 = SI 实现**"四等价，并在 **Nyquist–Poisson–Euler–Maclaurin（NPE）** 误差账本下给出**非渐近**可检上界。理论兼容**可逆元胞自动机（RCA）**之 CHL 定理的离散光锥，并与采样/插值/帧的密度阈值（Landau、Wexler–Raz、Balian–Low）建立同构。

---

## 0. 记号与预备

* 散射矩阵 $S(E)\in U(N)$。**Wigner–Smith 延迟矩阵**定义为 $Q(E):=-\,i\,S(E)^\dagger \tfrac{dS}{dE}(E)$，其迹 $\mathrm{tr}\,Q(E)$ 的量纲为 $1/\text{能量}$；物理**群延迟**取 $\tau_{\mathrm{WS}}(E):=\hbar\,\mathrm{tr}\,Q(E)$，量纲为时间。该定义可追溯至 Smith 对"寿命矩阵"的刻画。标准文献将 Wigner–Smith 延迟定义为"相位对能量的导数"并与 $\mathrm{tr}\,Q$ 对应，$\tau=\hbar\,\mathrm{tr}Q$ 具时间量纲。([物理评论链接管理器][1])

* **Birman–Kreĭn（BK）公式**：若 $\det S(E)=e^{-2\pi i\,\xi(E)}$，则 $\mathrm{tr}\,Q(E)=-2\pi\,\xi'(E)$。([arXiv][2])

* **KK—因果**：严格因果 $\Leftrightarrow$ 频响上半平面解析 $\Leftrightarrow$ Kramers–Kronig 色散关系（Toll）。([物理评论链接管理器][3])

* **推迟格林函数**：对三维**标量**波动方程 $\square G_{\rm ret}=\delta$，有显式式 $G_{\rm ret}(t,\mathbf r)=\delta\!\bigl(t-|\mathbf r|/c\bigr)/(4\pi|\mathbf r|)$，支撑恰在 $t=r/c$。对 **Maxwell** 方程，时域格林函数为**dyadic（张量）**核，由对该标量核的张量—微分算子作用（含 $\delta$ 及其导数）构成，支撑同样仅在光锥上。([维基百科][4])

* **光学度量（Gordon）**：各向同性介质可等效为**光学度量** $g^{\rm opt}_{\mu\nu}$。在被动线性介质且高频极限 $n(\omega)\to 1$ 的常见情形下，**信号前沿速度等于真空光速 $c$**（Sommerfeld–Brillouin）；更一般地，以高频极限定义的**前沿光学度量** $g^{\rm front}$ 给出最早可达时间 $t_{\min}=d_{\rm front}/c$，而群速可与 $c$ 不同。现代综述与推广见 Leonhardt–Philbin 及后续工作。([arXiv][5])

* **快/慢光与信息速度**：实验与信息论定义表明**可检测信息速度不超 $c$**。([PubMed][6])

* **NPE 误差账本**：Nyquist 采样定理与别名条件（Shannon/Nyquist）；Poisson 求和公式（NIST DLMF §1.8(iv)）；Euler–Maclaurin 有界余项（DLMF §2.10）。([webusers.imj-prg.fr][7])

* **de Branges 核对角**：对 Hermite–Biehler 函数 $\mathcal{E}$ 的空间 $\mathcal H(\mathcal{E})$，有 $K(x,x)=\tfrac{1}{\pi}\,\varphi'(x)\,|\mathcal{E}(x)|^{2}$，其中 $\varphi$ 为相位函数。

* **Weyl–Heisenberg 表示与唯一性**：Stone–von Neumann 定理与相干/时频框架之基础可参见 Folland。([PagePlace][8])

* **窗化卷积与平均记号**：取能量窗 $w_R\in L^{1}(\mathbb R)$ 与单位积分核 $h\in L^{1}(\mathbb R)$。归一规范
$$
\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,dE=1,\qquad \int_{\mathbb R} h(\nu)\,d\nu=1.
$$
定义卷积与窗化平均
$$
[h\star f](E):=\int_{\mathbb R} h(\nu)\,f(E-\nu)\,d\nu,\qquad
\big\langle f\big\rangle_{w,h}:=\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,[h\star f](E)\,dE.
$$
在真空纯延迟链路 $S_L(E)=e^{iEL/(\hbar c)}$ 下，由 $\operatorname{tr}Q_L\equiv L/(\hbar c)$ 与上式归一规范，得 $\hbar\langle \operatorname{tr}Q_L\rangle_{w,h}=L/c$（见 §4）。

* **分布与广义函数记号**：$\delta(\cdot)$ 为 Dirac $\delta$ 分布；$\Theta(t)$ 为 Heaviside 阶跃函数，$\Theta(t)=0\ (t<0)$、$\Theta(t)=1\ (t>0)$（取 $\Theta(0)=\tfrac{1}{2}$ 不影响本文结果）。因此 §5 的表示式中 $\Theta\bigl(t-d_{\rm front}(x,y)/c\bigr)\,g(t;x,y)$ 描述**前沿之后**的尾项响应。

* **散射背景与能量表象**：设 $\mathcal H$ 为希尔伯特空间，$H_0,H$ 为其上自伴算子（自由/全哈密顿量）。假设波算子 $W_\pm:=s\text{-}\lim_{t\to\pm\infty} e^{itH}e^{-itH_0}$ 存在且完备，则散射算子 $\mathsf S:=W_+^*W_-$ 在能量表象纤维化为 $S(E)\in U(N)$。Wigner–Smith 延迟矩阵定义为 $Q(E):=-\,i\,S(E)^\dagger\partial_E S(E)$，与正文 §0 的记号一致。

* **迹记号**：本文统一用 $\operatorname{tr}$ 表示有限维矩阵迹（如 $S(E)\in U(N)$），$\operatorname{Tr}$ 保留给希尔伯特空间上的迹类算子（如 §6 的 $T_{w_R}$）。

---

## 1. 公理（WSIG–EBOC 时空）

令
$$
\mathbb S=\bigl(\mathcal E,\ \preceq,\ g,\ \mu_\varphi;\ H,H_0,S(\cdot);\ \mathcal W,\mathcal H\bigr).
$$

**层级说明**：本文称 $(\mathcal E,\preceq,g,\mu_\varphi)$ 为**时空四元组**（本体层），而 $(H,H_0,S(\cdot);\mathcal W,\mathcal H)$ 为**实现资料**（实现层，用以给出窗化散射读数与证明链），两者不可混淆。

称 $\mathbb S$ 为**WSIG–EBOC 时空**，若：

**(A1) 事件与因果序**：$\mathcal E$ 为事件集；若波动方程的 $G_{\rm ret}$ 对差向量 $(e_2-e_1)$ 有支撑，则置 $e_1\preceq e_2$。离散系统取 RCA 邻域传播界（见 §9）。([维基百科][4])

**(A2) 表象与可观测性**：$\mathcal H$ 为希尔伯特空间；$(U_\tau,V_\sigma)$ 为 Weyl–Heisenberg 射影酉表示，支持窗化读数。([PagePlace][8])

**(A3) 相位—密度—延迟字典**：存在窗 $\mathcal W$ 使 $\partial_E\arg\det S=\mathrm{tr}\,Q=-2\pi\,\xi'(E)$ 的窗化读数成立。([arXiv][2])

**(A4) 因果—解析一致**：严格因果 $\iff$ KK 色散。([物理评论链接管理器][3])

**(A5) 前沿—信息一致**：以**前沿光学光程**度量 $D_{\rm front}$ 归一化后，信息速度的上确界同为 $c$，即
$$
c_{\rm info}:=\lim_{\delta\downarrow0}\sup\frac{D_{\rm front}}{T_\delta}=c,\quad
D_{\rm front}=\begin{cases}L,&\text{真空},\\ d_{\rm front}(x,y),&\text{介质/不均匀/有界域}.\end{cases}
$$
([维基百科][4])

**(A6) 采样—误差闭合**：读数误差按 NPE 三分解给出非渐近上界。([webusers.imj-prg.fr][7])

**(A7) SI 对齐**：$c$ 取 SI 固定值；"以延迟计长"与"以时定长"互逆实现（§4、§8）。

**(A8) 相位密度几何**：de Branges 核对角 $K(x,x)=\tfrac{1}{\pi}\,\varphi'(x)\,|\mathcal{E}(x)|^{2}$ 诱导 $\mu_\varphi:=(\varphi'/\pi)\,dx$ 作为窗化刻度。

---

## 2. 操作性定义：时间与空间

**定义 2.1（时间）** 取窗 $w_R$ 与单位积分核 $h$。对链路散射 $S(E)$，定义**窗口化群延迟读数**
$$
\mathsf T[w_R,h]:=\hbar\,\frac{1}{2\pi}\int_\mathbb R w_R(E)\,\bigl[h\star \mathrm{tr}\,Q\bigr](E)\,dE,
$$
其中 $Q:=-iS^\dagger \tfrac{dS}{dE}$，$\mathrm{tr}\,Q$ 与 $\partial_E\arg\det S$ 及 $-2\pi\xi'(E)$ 等价。([物理评论链接管理器][1])

**归一规范**：约定 $(2\pi)^{-1}\!\int_{\mathbb R}\! w_R(E)\,dE=1$，且 $\int_{\mathbb R}\! h(E)\,dE=1$（单位积分核），据此在真空纯延迟链路上有 $\mathsf T=L/c$。验证：在 $S_L(E)=e^{iEL/(\hbar c)}$ 下有 $\mathrm{tr}\,Q=L/(\hbar c)$ 常数，代入上式并用上述归一条件立得 $\mathsf T=L/c$；与定理 4.1 保持一致。

在真空长度 $L$ 的链路上，定义的**时间坐标差**满足 $\Delta t=L/c$。

**定义 2.2（空间）** 真空中以**雷达距**定义空间距离：$d(A,B):=\tfrac{c}{2}\,\mathsf T_{\rm roundtrip}(A\to B\to A)$。

在介质/不均匀/有界域中，定义**波前（front）光程** $d_{\rm front}(A,B)$：取材料**高频极限**折射率 $n_\infty(\mathbf x)=\lim_{\omega\to\infty}n(\mathbf x,\omega)$，据此构造 Gordon **前沿**光学度量 $g^{\rm front}$ 的零测地线长度并令 $d_{\rm front}$ 为其极小值，则**最早可达时间** $t_{\min}(A,B)=d_{\rm front}(A,B)/c$。均匀各向同性且 $n_\infty\equiv 1$ 时，$d_{\rm front}(A,B)=|A-B|$，故 $t_{\min}=|A-B|/c$。([arXiv][9])

**群折射率**：对各向同性被动介质，定义
$$
n_g(\mathbf x,\omega):=n(\mathbf x,\omega)+\omega\,\partial_\omega n(\mathbf x,\omega)
=\frac{c}{v_g(\mathbf x,\omega)},
$$
其中 $v_g$ 为群速度。于是群时间 $t_g=\int_\gamma n_g\,ds/c$，相位时间 $t_\phi=\int_\gamma n\,ds/c$。**一般地不保证 $t_g$ 或 $t_\phi$ 与 $t_{\min}$ 的大小关系**（在异常色散与增益/损耗情况下可出现 $t_g<t_{\min}$ 或 $t_\phi<t_{\min}$）；普适且与因果一致的仅是
$$
t_{\min}=\frac{d_{\rm front}}{c},\qquad T_{\rm info}\ge t_{\min},
$$
其中 $T_{\rm info}$ 为任意**可检信息**的首次到达时间（见 §5）。

**往返时间**：
$$
\mathsf T_{\mathrm{roundtrip}}(A\to B\to A;\,w_R,h)
:=\mathsf T[w_R,h;\,A\to B]+\mathsf T[w_R,h;\,B\to A].
$$
若链路与读数协议互易（双向对称），则 $d(A,B)=\tfrac{c}{2}\,\mathsf T_{\mathrm{roundtrip}}(A\to B\to A)$。

**前沿假设（F）**：介质为被动线性、各向同性，且高频折射率存在有限极限
$$
n_\infty(\mathbf x):=\lim_{\omega\to\infty}n(\mathbf x,\omega)\in[1,\infty),
$$
据此定义前沿光学度量 $g^{\rm front}$ 与 $d_{\rm front}$。若极限难以验证，取
$$
n_\infty(\mathbf x):=\limsup_{\omega\to\infty}n(\mathbf x,\omega)
$$
亦可保证 $t_{\min}=d_{\rm front}/c$ 的上界与"前沿 = $c$"结论成立。

**定义 2.3（同时切片）** 选参考世界线与往返协议，令 $\Sigma_t:=\{e\in\mathcal E:\ \mathsf T_{\rm roundtrip}=2t\}$，其三维度量由雷达距或 $g^{\rm front}$ 诱导。

---

## 3. 时空的结构化定义

**定义 3.1（WSIG–EBOC 时空）** 若存在窗化散射读数使：

(1) **度量—读数一致**：真空链路 $L$ 上 $\mathsf T=L/c$；介质零测地线（以 $g^{\rm front}$ 度量）与前沿一致；

(2) **三重字典**：$\partial_E\arg\det S=\mathrm{tr}\,Q=-2\pi\xi'(E)$；

(3) **NPE 可检**：误差别名/Poisson/EM 余项有全局上界；

(4) **信息—因果一致**：首次可检互信息时间 $T_\delta(L)$ 使 $\lim_{\delta\downarrow0}\sup L/T_\delta(L)=c$；

则四元组 $(\mathcal E,\preceq,g,\mu_\varphi)$ 为一**时空**。([arXiv][2])

---

## 4. 主等价定理（相位—延迟—谱移—SI）

**定理 4.1**（四等价） 设真空链路 $L$ 的散射 $S_L(E)=\exp\!\bigl(i E L/(\hbar c)\bigr)$。则
$$
\mathsf T[w_R,h;L]
=\hbar\,\big\langle \partial_E\arg\det S_L\big\rangle_{w,h}
=\hbar\,\big\langle \mathrm{tr}\,Q_L\big\rangle_{w,h}
=-\,\hbar\,2\pi\,\big\langle \xi'(E)\big\rangle_{w,h}
=\frac{L}{c},
$$
且在 Nyquist 带宽极限下所得 $c=\lim L/\mathsf T$ 与窗/核无关，并与 SI 数值一致。

**证明**：

**假设（单模纯延迟链路）**：取单通道 $S_L(E)=\exp\!\bigl(iE L/(\hbar c)\bigr)$。窗 $w_R\in L^1(\mathbb R)$、核 $h\in L^1(\mathbb R)$ 满足归一规范
$$
\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,dE=1,\qquad \int_{\mathbb R} h(E)\,dE=1.
$$

**引理 1（对数导数 = Wigner–Smith）**：对可微酉矩阵（此处为标量）$S$，有
$$
\partial_E\arg\det S(E)=\operatorname{Im}\,\partial_E\log\det S(E)
=\operatorname{Im}\,\operatorname{tr}\!\big(S^\dagger(E)\,\partial_E S(E)\big)
=-\,i\,\operatorname{tr}\!\big(S^\dagger(E)\,\partial_E S(E)\big)
=\operatorname{tr}Q(E),
$$
其中 $Q(E):=-\,i\,S^\dagger(E)\,\partial_E S(E)$。在标量 $S_L$ 下，$\operatorname{tr}Q_L(E)=-iS_L^*(E)\partial_E S_L(E)=L/(\hbar c)$（常数）。

**引理 2（Birman–Kreĭn）**：若 $\det S(E)=e^{-2\pi i\,\xi(E)}$，则
$$
\operatorname{tr}Q(E)=-2\pi\,\xi'(E).
$$
据此在 $S_L$ 下得 $\xi'(E)=-\,\frac{1}{2\pi}\,\frac{L}{\hbar c}$。

**主证明**：定义窗化读数
$$
\mathsf T[w_R,h;L]
=\hbar\,\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,\bigl[h\star \operatorname{tr}Q_L\bigr](E)\,dE.
$$
因 $\operatorname{tr}Q_L\equiv L/(\hbar c)$ 为常数，卷积与积分交换并用两条归一，得
$$
\mathsf T[w_R,h;L]
=\hbar\cdot\frac{1}{2\pi}\cdot\frac{L}{\hbar c}\!\int w_R(E)\,dE\cdot\!\int h(\nu)\,d\nu
=\frac{L}{c}.
$$
再结合引理 1–2，于被积函数恒定之事实，立得
$$
\mathsf T
=\hbar\,\big\langle \partial_E\arg\det S_L\big\rangle_{w,h}
=\hbar\,\big\langle \operatorname{tr}Q_L\big\rangle_{w,h}
=-\,\hbar\cdot 2\pi\,\big\langle \xi'(E)\big\rangle_{w,h}
=\frac{L}{c}.
$$

**误差闭合说明（NPE）**：Nyquist/Poisson/Euler–Maclaurin 三项在"常数被积"情形下分别为 0：别名项为 0，Poisson 周期化项为 0，EM 余项因高阶导数为 0 而为 0。故极限与窗/核无关，且与 SI 数值一致。$\square$

---

## 5. 因果前沿与信息光锥

**定理 5.1（因果前沿 = $c$）** 线性且严格因果（可时变）信道的最早非零响应时间满足
$$
t_{\min}=\frac{D_{\rm front}}{c},\qquad
D_{\rm front}=\begin{cases}L,&\text{真空},\\ d_{\rm front}(x,y),&\text{介质/不均匀/有界域}.\end{cases}
$$
真空情形即 $t_{\min}(L)=L/c$。

**证明**：设系统线性且严格因果（可时变）。令源信号 $x$ 支持于 $t\ge 0$。输出
$$
y(t)=\int_{\mathbb R} G_{\rm ret}(t,\tau;x,y)\,x(\tau)\,d\tau,\quad
\text{其中 }G_{\rm ret}(t,\tau;x,y)=0\ \text{当}\ t-\tau< D_{\rm front}/c.
$$
**注**：在真空/线性时不变（LTI）情形，$G_{\rm ret}(t,\tau;x,y)=G_{\rm ret}(t-\tau,L)$，上式化为卷积。

**真空、均匀、无耗 3D 标量波动方程：**
$$
G_{\rm ret}(t,r)=\frac{\delta(t-r/c)}{4\pi r},
$$
支撑**仅在** $t=r/c$（Huygens 原理）。**Maxwell 电磁场**：时域格林函数为**dyadic（张量）**核，由对 $\delta(t-r/c)/(4\pi r)$ 的张量—微分算子作用（含 $\delta$ 及其导数）构成，其**支撑同样仅在光锥**上，故最早非零响应时间同为 $t_{\min}=L/c$。

**一般介质/不均匀/有界域：** 令 $d_{\rm front}(x,y)$ 为由高频极限折射率 $n_\infty=\lim_{\omega\to\infty}n(\omega)$ 确定的 Gordon **前沿**光学度量下的测地光程（即波前速度 $v_{\rm wf}=\lim_{\omega\to\infty}v_{\rm ph}(\omega)$ 决定的光程）。则
$$
G_{\rm ret}^{\rm med}(t;x,y)=A(x,y)\,\delta\!\Big(t-\frac{d_{\rm front}(x,y)}{c}\Big)+\Theta\!\Big(t-\frac{d_{\rm front}(x,y)}{c}\Big)\,g(t;x,y),
$$
其中 $A(x,y)$ 为由介质/几何决定的前沿振幅，$g$ 在 $t\ge d_{\rm front}/c$ 局部可积，且**不改变传播前沿 = $c$**（与先驱波及因果性一致）。真空均匀 3D 为特例：$d_{\rm front}(x,y)=|x-y|$、$A(x,y)=\frac{1}{4\pi|x-y|}$、尾项 $g\equiv 0$。

因此在真空情形下，当 $t<L/c$ 时，对任意 $\tau\ge 0$，有 $t-\tau<L/c\Rightarrow G_{\rm ret}(t-\tau,L)=0$，从而 $y(t)=0$。取 $x=\delta$ 可见 $y(t)=\delta(t-L/c)/(4\pi L)$，故最早非零响应恰在 $t=L/c$。这在频域与 KK 等价：严格因果 $\Leftrightarrow$ 上半平面解析；由移位定理，最小支撑端点即传播前沿 $L/c$。$\square$

**定理 5.2（信息光锥 = $c$）** 设接收端在 $\Delta t$ 前仅含与发送独立的噪声，无预共享携信变量。记门限互信息的首次可检时间 $T_\delta$。定义前沿距离 $D_{\rm front}$（真空取 $L$，介质取 $d_{\rm front}(x,y)$）。则 $c_{\rm info}:=\lim_{\delta\downarrow0}\sup\dfrac{D_{\rm front}}{T_\delta}=c$。

**证明**：设输入过程 $X$ 支持于 $t\ge 0$，噪声 $N$ 与 $X$ 独立，接收端观测
$$
Y_t := \{Y(s): 0\le s\le t\},\qquad Y(t)=\int_{\mathbb R} G_{\rm ret}(t,\tau;x,y)\,X(\tau)\,d\tau+N(t).
$$
**注**：真空/线性时不变（LTI）情形下 $G_{\rm ret}(t,\tau;x,y)=G_{\rm ret}(t-\tau;|x-y|)$，可写为 $Y=G_{\rm ret}\!*\!X+N$。

**(1) 零互信息（前沿之前）**：若在**真空** $t<L/c$（或在**介质/不均匀/有界域** $t<d_{\rm front}(x,y)/c$），则 $Y(s)=N(s)$，故 $I(X;Y_t)=0$。

**(2) 正互信息与门限时间（前沿之后）**：任取 $\varepsilon>0$，令
$$
t_\varepsilon=\begin{cases}L/c+\varepsilon,&\text{真空},\\ d_{\rm front}(x,y)/c+\varepsilon,&\text{介质/不均匀/有界域}. \end{cases}
$$
取标量试探 $X_\alpha(\tau)=\alpha\,\psi(\tau)$（$\psi$ 为单位能量的短时脉冲）。则
$$
Z_\varepsilon:=\int_0^{t_\varepsilon}G_{\rm ret}(t_\varepsilon,\tau;x,y)\,\psi(\tau)\,d\tau.
$$
**非零（前沿之后）**：真空情形取**连续且 $\psi(0)\neq 0$** 的单位能量短脉冲，则对**任意小** $\varepsilon>0$ 有
$$
Z_\varepsilon=\frac{\psi(\varepsilon)}{4\pi L}\neq 0.
$$
介质/不均匀/有界域情形，由 §5 给出的 $G_{\rm ret}^{\rm med}$ 之前沿项 $A(x,y)\delta\!\big(t-d_{\rm front}/c\big)$ 与尾项在 $t\ge d_{\rm front}/c$ 的支撑，同样给出 $Z_\varepsilon\neq 0$。引入等概符号 $S\in\{\pm1\}$，设输入波形 $X_S(\tau):=S\,\alpha\,\psi(\tau)$。则
$$
Y(t_\varepsilon)=S\,\alpha\,Z_\varepsilon+N(t_\varepsilon).
$$
**噪声模型**：令 $N(t_\varepsilon)\sim\mathcal N(0,\sigma^{2})$，与 $X$ 独立。记 $X:=S\,\alpha$，取 $\mathrm{SNR}:=\alpha^{2}|Z_\varepsilon|^{2}/\sigma^{2}$。当 $\mathrm{SNR}\to0$（以 nats 计），由 I–MMSE 小 SNR 斜率得
$$
I\bigl(X;Y(t_\varepsilon)\bigr)=\tfrac{1}{2}\,\mathrm{SNR}+o(\mathrm{SNR})=\frac{\alpha^{2}|Z_\varepsilon|^{2}}{2\sigma^{2}}+o(\alpha^{2}).
$$
又因 $Y(t_\varepsilon)$ 为 $Y_{[0,t_\varepsilon]}$ 的可测函数，故
$$
I\bigl(X;Y_{[0,t_\varepsilon]}\bigr)\ge I\bigl(X;Y(t_\varepsilon)\bigr).
$$
因此对任意小的 $\delta>0$，可取充分小的 $\alpha$ 使 $I\bigl(X;Y(t_\varepsilon)\bigr)\ge\delta$，继而 $I\bigl(X;Y_{[0,t_\varepsilon]}\bigr)\ge\delta$。定义 $T_\delta:=\inf\{t:I(X;Y_{[0,t]})\ge\delta\}$，便得 $T_\delta\le t_\varepsilon$。因此
$$
\forall \varepsilon>0,\ \exists \delta(\varepsilon)\downarrow 0:\quad T_\delta\le t_\varepsilon,
$$
由是
$$
c_{\rm info}:=\lim_{\delta\downarrow0}\sup\frac{D_{\rm front}}{T_\delta}=c,\qquad
D_{\rm front}=\begin{cases}L,&\text{真空},\\ d_{\rm front}(x,y),&\text{介质/不均匀/有界域}.\end{cases}
$$
$\square$

---

## 6. 相位密度几何与迹公式

**命题 6.1** 在 de Branges 空间 $\mathcal H(\mathcal{E})$ 上，几乎处处 $K(x,x)=\tfrac{1}{\pi}\,\varphi'(x)\,|\mathcal{E}(x)|^{2}$。因此**相位密度** $\rho(x):=\varphi'(x)/\pi$ 给出自然测度。令再生核正交投影 $\Pi$，并取 $T_{w_R}:=M_{\sqrt{w_R}}\Pi M_{\sqrt{w_R}}$。**若** $w_R\ge0$ 且 $w_R\in L^{1}\cap L^\infty(d\mu_\varphi)$（或以 $w_R^{(n)}\uparrow w_R$ 之单调截断极限理解），**则** $T_{w_R}$ 为迹类，并且
$$
\mathrm{Tr}(T_{w_R})=\int_{\mathbb R} w_R(x)\,\rho(x)\,dx.
$$
该恒等式为"相位—密度—延迟"在 RKHS 的实现。

**证明**：设 $\mathcal{E}$ 为 Hermite–Biehler 函数，$\mathcal{E}^\#(z):=\overline{\mathcal{E}(\overline z)}$。de Branges 空间 $\mathcal H(\mathcal{E})$ 的再生核为
$$
K(z,w)=\frac{\overline{\mathcal{E}(w)}\,\mathcal{E}(z)-\overline{\mathcal{E}^\#(w)}\,\mathcal{E}^\#(z)}{2\pi i\,(\overline w-z)}.
$$
取 $w=z=x\in\mathbb R$，用洛必达法则并记 $\mathcal{E}(x)=|\mathcal{E}(x)|e^{-i\varphi(x)}$ 得
$$
K(x,x)=\frac{1}{2\pi i}\Big(\overline{\mathcal{E}(x)}\mathcal{E}'(x)-\overline{\mathcal{E}'(x)}\mathcal{E}(x)\Big)
=\frac{1}{\pi}\,\varphi'(x)\,|\mathcal{E}(x)|^{2}.
$$
于是对角密度 $\rho(x):=\varphi'(x)/\pi$ 自然诱导测度 $\mu_\varphi=\rho(x)\,dx$，并由再生性质给出窗口迹公式。$\square$

---

## 7. 采样/插值/帧：密度阈值与障碍

* **Landau 必要密度**（Paley–Wiener 特例）：采样/插值序必须满足端密度阈值。([Project Euclid][10])
* **Wexler–Raz 双正交关系**：刻画 Gabor 框架的对偶窗—格参数关系及其推广。([sites.math.duke.edu][11])
* **Balian–Low 障碍**：临界密度下单窗无法同时时—频紧局域；可作框架/多窗规避。([Scispace][12])

---

## 8. NPE 误差账本（非渐近上界）

**误差分解与尾项定义**：约定时间读数的非理想项分解为 $\varepsilon_{\rm alias}$（别名/欠采样）、$\varepsilon_{\rm EM}$（Euler–Maclaurin 有限阶余项）与 $\varepsilon_{\rm tail}$（窗/核的有限支持或非紧支撑尾项）。取 $R>0$ 使 $w_R$ 的主要支撑包含于 $[-R,R]$。定义
$$
\varepsilon_{\rm tail}:=\hbar\,\frac{1}{2\pi}\int_{|E|>R} w_R(E)\,[h\star \mathrm{tr}Q](E)\,dE.
$$
若 $\int_{|E|>R}|w_R(E)|\,dE\le \epsilon$、$h\in L^{1}$，并且记 $\Omega_E:=\operatorname{supp}(w_R)\oplus \operatorname{supp}(h)$，且 $\mathrm{tr}\,Q\in L^\infty(\Omega_E)$，则
$$
|\varepsilon_{\rm tail}|\le \frac{\hbar}{2\pi}\,\epsilon\,\|h\|_{L^{1}}\,\operatorname*{ess\,sup}_{E\in \Omega_E}|\mathrm{tr}\,Q(E)|.
$$
在真空纯延迟链路中，$\mathrm{tr}Q_L$ 为常数，故三项误差（别名/EM/尾项）皆为 0（见 §4）。

* **Nyquist（别名）**：若 $\widehat f$ 带限于 $(-\pi/\Delta E,\pi/\Delta E)$，则别名为 0；否则可用频谱抽样上界量化。([webusers.imj-prg.fr][7])
* **Poisson 求和**：把离散采样与周期化严格联结，用于评估别名项。([dlmf.nist.gov][13])
* **Euler–Maclaurin（有限阶）**：余项满足 $|R_{p}|\le \frac{2\zeta(p)}{(2\pi)^p}\int|f^{(p)}|$，给出端点/尾项的可检上界。([dlmf.nist.gov][14])

综上，时间读数满足 $\mathsf T=\tfrac{L}{c}+\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}$，三误差在规程内可控并收敛。

---

## 9. 离散时空与 CHL 光锥

设格点间距为 $a$、离散时间步长为 $\Delta t$。半径 $r$ 的 RCA 在 $t$ 步的影响域为 $\pm r t$，等效"离散光锥"，其离散"光速"定义为
$$
c_{\rm disc}=\frac{r\,a}{\Delta t}.
$$
**Curtis–Hedlund–Lyndon 定理**刻画了"连续且与移位可换 $\Leftrightarrow$ 滑动块码"，并保证可逆性时逆演化亦为 CA，从而实现可逆因果传播。([SpringerLink][15])

---

## 10. 与相对论/场论的相容性

* **洛伦兹协变**：$G_{\rm ret}$ 的光锥支撑等价于 Minkowski 光锥。([维基百科][4])
* **微因果/无超信号性**：快/慢光体系中"信息速度 $\le c$"与量子场的类空对易一致。([PubMed][6])
* **介质几何**：Gordon 光学度量把折射/流速吸收入度量，不改变前沿 $=c$。([arXiv][9])

---

## 11. 结论性定义（汇总）

* **时间**：在给定窗—核与读数协议下，时间是**窗口化群延迟坐标**，即 $t\equiv \hbar\int \tfrac{w_R}{2\pi}\,[h\!\star\!\mathrm{tr}\,Q]\,dE$。
* **空间**：通过等时往返读数选定的**同时切片 $\Sigma_t$** 及其三维度量。真空中由雷达距定义；介质情形以**前沿光学度量** $g^{\rm front}$（高频极限 $n_\infty=\lim_{\omega\to\infty}n(\omega)$ 决定）的零测地线定义 $d_{\rm front}$，最早可达时间 $t_{\min}=d_{\rm front}/c$，前沿 $=c$ 与因果一致。
* **时空**：四元组 $(\mathcal E,\preceq,g,\mu_\varphi)$，其中 $\preceq$ 来自 $G_{\rm ret}$ 光锥支撑，$g$ 为（光学）洛伦兹度量，$\mu_\varphi=(\varphi'/\pi)\,dx$ 为相位密度刻度；在 NPE 账本下可检、可校准，并与 SI 互逆实现。

---

## 12. 实施规程（简述）

1. 选几何已知的真空链路 $L$；2) 宽带激励，测得 $\hat\tau=\mathsf T[w_R,h;L]$；3) 检验 Nyquist（带限/反混叠）、估计 Poisson/EM 余项；4) 取 $\hat c=L/\hat\tau$，与频率链/干涉计长度链交叉校准闭环。([webusers.imj-prg.fr][7])

---

## 13. 证明脉络与外部索引

* $\partial_E\arg\det S=\mathrm{tr}\,Q$ 与 BK 恒等式：([arXiv][2])
* KK—因果等价与前沿光锥：([物理评论链接管理器][3])
* 信息光锥与门限互信息：([PubMed][6])
* NPE 三分解的非渐近上界：([webusers.imj-prg.fr][7])
* de Branges 核对角与相位密度：标准 de Branges 空间理论
* Weyl–Heisenberg/Stone–von Neumann：([PagePlace][8])
* CHL 定理与离散光锥：([SpringerLink][15])

---

## 参考文献（书目信息，按主题）

**散射与群延迟**：F. T. Smith, "Lifetime Matrix in Collision Theory," *Phys. Rev.* 118 (1960) 349–356；A. Pushnitski, "The Birman–Krein formula…" (2010, arXiv:1006.0639)；M. S. Birman & D. R. Yafaev, "The spectral shift function…" *Alg. Anal.* 4 (1992) 1–20.

**因果—色散—前沿**：J. S. Toll, "Causality and the Dispersion Relation," *Phys. Rev.* 104 (1956) 1760–1770；L. Brillouin, *Wave Propagation and Group Velocity*, Academic Press (1960)。

**光学度量**：W. Gordon, "Zur Lichtfortpflanzung nach der Relativitätstheorie," *Ann. Phys.* 377 (1923) 421–456；U. Leonhardt & T. G. Philbin, "General Relativity in Electrical Engineering" (2006)。

**信息速度**：M. D. Stenner, D. J. Gauthier, M. A. Neifeld, "The speed of information in a 'fast-light' optical medium," *Nature* 425 (2003) 695–698；A. H. Dorrah, M. Mojahedi, *Phys. Rev. A* 90 (2014) 033822。

**采样—Poisson—EM**：C. E. Shannon, "Communication in the Presence of Noise," *Proc. IRE* 37 (1949)；H. Nyquist, "Certain Topics in Telegraph Transmission Theory," (1928)；NIST DLMF §1.8（Poisson）、§2.10（Euler–Maclaurin）。

**de Branges 空间**：L. de Branges, *Hilbert Spaces of Entire Functions*, 1968；J. Antezana, J. Marzo, J.-F. Olsen, "Zeros of random functions generated with de Branges kernels," *IMRN* (2017)。

**Gabor/帧/密度**：H. J. Landau, "Necessary density conditions...," *Acta Math.* 117 (1967) 37–52；I. Daubechies 等, "Gabor Time-Frequency Lattices and the Wexler–Raz Identity," *JFAA* 1 (1995)；C. Heil, *A Basis Theory Primer*, Birkhäuser (2011)。

**Weyl–Heisenberg 与唯一性**：G. B. Folland, *Harmonic Analysis in Phase Space*, Princeton (1989)。

**RCA 与 CHL**：G. A. Hedlund, "Endomorphisms and automorphisms of the shift dynamical system," *Math. Systems Theory* 3 (1969) 320–375。

---

### 结语（定理）

**定理（统一刻度定理）**：以**窗口化群延迟的 Nyquist 极限**定义的 $c$ 在真空链路上**唯一**确定，且与

(A) 相位斜率/谱移密度、(B) 因果前沿（KK & 光锥）、(C) 信息光锥（门限互信息）、(D) SI 实现

两两等价。因此：**时间**即**窗化群延迟坐标**；**空间**即**等时往返切片及其度量**；**时空**即**因果序 +（光学）度量 + 相位密度测度**的可测结构。上述等价与可检性由 §4–§8 之证明与文献支撑。

**证明**：设真空链路 $L$。由定理 4.1，窗化群延迟读数给出 $\mathsf T=L/c$。由定理 5.1，最早非零响应时间 $t_{\min}(L)=L/c$，故"相位斜率/群延迟"与"因果前沿"一致。由定理 5.2，门限互信息的首次可检时间 $T_\delta(L)\to L/c$（$\delta\downarrow 0$），于是"信息光锥"与前沿一致。SI 中 $c$ 为固定常数，长度—时间互逆实现（现稿 §2、§12 的往返/雷达规程）即给出 $\hat c=L/\hat\tau$ 与频率链/干涉计长度链的闭环一致性。因此四者（A）相位斜率/谱移密度，（B）因果前沿，（C）信息光锥，（D）SI 实现，两两等价。$\square$

---

[1]: https://link.aps.org/doi/10.1103/PhysRev.118.349?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory | Phys. Rev."
[2]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[3]: https://link.aps.org/doi/10.1103/PhysRev.104.1760?utm_source=chatgpt.com "Causality and the Dispersion Relation: Logical Foundations"
[4]: https://en.wikipedia.org/wiki/Green%27s_function?utm_source=chatgpt.com "Green's function"
[5]: https://arxiv.org/abs/cond-mat/0607418?utm_source=chatgpt.com "General Relativity in Electrical Engineering"
[6]: https://pubmed.ncbi.nlm.nih.gov/14562097/?utm_source=chatgpt.com "The speed of information in a 'fast-light' optical medium"
[7]: https://webusers.imj-prg.fr/~antoine.chambert-loir/enseignement/2020-21/shannon/shannon1949.pdf?utm_source=chatgpt.com "Communication In The Presence Of Noise"
[8]: https://api.pageplace.de/preview/DT0400.9781400882427_A26692119/preview-9781400882427_A26692119.pdf?utm_source=chatgpt.com "harmonic analysis in phase space"
[9]: https://arxiv.org/pdf/cond-mat/0607418?utm_source=chatgpt.com "General Relativity in Electrical Engineering"
[10]: https://projecteuclid.org/journals/acta-mathematica/volume-117/issue-none/Necessary-density-conditions-for-sampling-and-interpolation-of-certain-entire/10.1007/BF02395039.full?utm_source=chatgpt.com "Necessary density conditions for sampling and ..."
[11]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[12]: https://scispace.com/pdf/differentiation-and-the-balian-low-theorem-2u9h20ri25.pdf?utm_source=chatgpt.com "Differentiation and the Balian-Low Theorem"
[13]: https://dlmf.nist.gov/1.8?utm_source=chatgpt.com "1.8 Fourier Series"
[14]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[15]: https://link.springer.com/article/10.1007/BF01691062?utm_source=chatgpt.com "Endomorphisms and automorphisms of the shift dynamical ..."
