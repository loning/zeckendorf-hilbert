# WSIG–EBOC **时空/时间/空间**统一理论

**（含可核对引文）**

**Version: 1.38**（2025-11-02，Asia/Dubai）

---

## 摘要

在 **WSIG**（Windowed Scattering & Information Geometry）与 **EBOC**（Eternal-Block **Observer-Computing**）框架下，本文建立一套基于**窗口化散射**的可操作时空理论：以**相位导数—谱移密度—Wigner–Smith 群延迟**三重等价为计量基元；以**Kramers–Kronig 因果—解析（稳定 LTI 限定）**与波动方程**推迟格林函数**（时域支撑，适用于 LTV）的光锥支撑，给出**以前沿光学度量计的上界：因果前沿不超 $c$**；并在**3D 真空纯传播/前沿奇性 $K\neq0$/链路含Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量）** 时取等号。以**门限互信息**的首次可检时间确立**信息光锥上界**：在真空或静态介质（LTI）下，$c_{\rm info}:=\lim_{\delta\downarrow0}\sup D_{\rm front}/T_\delta\le c$，**且当且仅当**满足**前沿可检**（§5）时取等号 $c_{\rm info}=c$；LTV 仅得 $T_\delta\ge t_{\min}$。据此给出**时间**与**空间**的操作性定义，并把**时空**刻画为四元组 $(\mathcal E,\preceq,g,\mu_\varphi)$：其中 $\preceq$ 由光锥支撑诱导，$g$ 为（含介质的）光学洛伦兹度量，$\mu_\varphi=(\varphi'/\pi)\,dx$ 为由 de Branges 核对角给出的**相位密度测度**。核心定理证明"**相位斜率 = 群延迟 = 谱移密度 = SI 实现**"四等价，并在 **Nyquist–Poisson–Euler–Maclaurin（NPE）** 误差账本下给出**非渐近**可检上界。理论兼容**可逆元胞自动机（RCA）**之 CHL 定理的离散光锥，并与采样/插值/帧的密度阈值（Landau、Wexler–Raz、Balian–Low）建立同构。

---

## 0. 记号与预备

* 散射矩阵 $S(E)\in U(N)$。**Wigner–Smith 延迟矩阵**定义为 $Q(E):=-\,i\,S(E)^\dagger \tfrac{dS}{dE}(E)$，其迹 $\mathrm{tr}\,Q(E)$ 的量纲为 $1/\text{能量}$；物理**群延迟**取 $\tau_{\mathrm{WS}}(E):=\hbar\,\mathrm{tr}\,Q(E)$，量纲为时间。该定义可追溯至 Smith 对"寿命矩阵"的刻画。标准文献将 Wigner–Smith 延迟定义为"相位对能量的导数"并与 $\mathrm{tr}\,Q$ 对应，$\tau=\hbar\,\mathrm{tr}Q$ 具时间量纲。([物理评论链接管理器][1])

* **Birman–Kreĭn（BK）公式**：若 $\det S(E)=e^{-2\pi i\,\xi(E)}$，则 $\mathrm{tr}\,Q(E)=-2\pi\,\xi'(E)$。([arXiv][2])

* **KK—因果（LTI 限定）**：在**稳定 LTI**系统（脉冲响应 $h_{\rm sys}(t)$）上，严格因果 $\Rightarrow$ 频响在上半平面解析；并且在 $h_{\rm sys}\in L^1(\mathbb R)$、$H(\omega)$ 多项式增长受控、无上半平面极点等**附加条件**下，实部与虚部满足 Kramers–Kronig 色散，且可反推严格因果（解析 $\Rightarrow$ 因果）。**LTV/非平稳**情形不适用该频域等价，本文仅采用 $G_{\rm ret}$ 的时域支撑性表述（见 §5）。([物理评论链接管理器][3])

* **推迟格林函数**：在三维**真空无界域**，标量波动方程 $\square G_{\rm ret}=\delta$ 的解为 $G_{\rm ret}(t,\mathbf r)=\delta(t-|\mathbf r|/c)/(4\pi|\mathbf r|)$，支撑恰在 $t=r/c$；**Maxwell** 的时域 **dyadic** 核由该标量核经张量—微分算子得到（含 $\delta$ 及其导数），支撑同样**仅在光锥上**。**在有界域/介质/色散**下，一般会出现**先驱/尾场**，详见 §5 的分解式。([维基百科][4])

* **光学度量（Gordon）**：前沿时间**满足**
$$
t_{\min}\ge \frac{d_{\rm front}}{c},
$$
其中 $d_{\rm front}$ 由高频极限折射率 $n_\infty$ 的 **3D 费马度量**定义。**在 3D 真空纯传播**或**前沿含奇性 $K\neq0$**、或**链路含Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量）** 时取等号。许多被动介质在高频满足"真空化" $n(\mathbf x,\omega)\to1$（故 $n_\infty=1$），于是 $d_{\rm front}=|A-B|$；此时**实验坐标下**仅能无条件断言 $t_{\min}\ge |A-B|/c$，并**仅在**上述**等号条件**成立时才**恢复**"前沿速度 $=c$"。（群速与 $c$ 可异——Sommerfeld–Brillouin 先驱）现代综述与推广见 Leonhardt–Philbin 及后续工作。([arXiv][5])

* **快/慢光与信息速度**：实验与信息论定义表明**可检测信息速度不超 $c$**。([PubMed][6])

* **NPE 误差账本**：Nyquist 采样定理与别名条件（Shannon/Nyquist）；Poisson 求和公式（NIST DLMF §1.8(iv)）；Euler–Maclaurin 有界余项（DLMF §2.10）。([webusers.imj-prg.fr][7])

* **de Branges 核对角**：对 Hermite–Biehler 函数 $\mathcal{E}$ 的空间 $\mathcal H(\mathcal{E})$，有 $K(x,x)=\tfrac{1}{\pi}\,\varphi'(x)\,|\mathcal{E}(x)|^{2}$，其中 $\varphi$ 为相位函数。**（记号统一）**本文以 $E$ 表示能量（亦作实频变量）；在 de Branges 章节用 $x$ 表示同一实轴变量并与 $E$ 等同，记作 $x\equiv E$。因此 $\mu_\varphi=(\varphi'(E)/\pi)\,dE$，并与 §2 中 $w_R(E)$ 的归一规范 $\tfrac{1}{2\pi}\!\int w_R(E)\,dE=1$ 一致。

* **Weyl–Heisenberg 表示与唯一性**：Stone–von Neumann 定理与相干/时频框架之基础可参见 Folland。([PagePlace][8])

* **窗化卷积与平均记号**：取能量窗 $w_R\in L^{1}(\mathbb R)$ 与**单位积分核** $\eta\in L^{1}(\mathbb R)$。归一规范
$$
\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,dE=1,\qquad \int_{\mathbb R} \eta(\nu)\,d\nu=1.
$$
定义卷积与窗化平均
$$
[\eta\star f](E):=\int_{\mathbb R} \eta(\nu)\,f(E-\nu)\,d\nu,\qquad
\big\langle f\big\rangle_{w,\eta}:=\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,[\eta\star f](E)\,dE.
$$
在真空纯延迟链路 $S_L(E)=e^{iEL/(\hbar c)}$ 下，由 $\operatorname{tr}Q_L\equiv L/(\hbar c)$ 与上式归一规范，得 $\hbar\langle \operatorname{tr}Q_L\rangle_{w,\eta}=L/c$（见 §4）。**（符号说明）**本文以 $\eta$ 表示**单位积分核**（用于窗化读数），以 $h_{\rm sys}(t)$ 表示**系统脉冲响应**（LTI 滤波器），$t_h:=\inf\{t:\,h_{\rm sys}(t)\neq 0\}$ 为其起始时延。

* **分布与广义函数记号**：$\delta(\cdot)$ 为 Dirac $\delta$ 分布；$\Theta(t)$ 为 Heaviside 阶跃函数，$\Theta(t)=0\ (t<0)$、$\Theta(t)=1\ (t>0)$（取 $\Theta(0)=\tfrac{1}{2}$ 不影响本文结果）。

* **前沿分解（定义）**：在真空或静态介质（LTI）并满足前沿假设（F）下，推迟格林函数可在分布意义上写成
$$
G_{\rm ret}(t;x,y)=K(x,y)\,\delta\!\Big(t-\tfrac{d_{\rm front}(x,y)}{c}\Big)+\Theta\!\Big(t-\tfrac{d_{\rm front}(x,y)}{c}\Big)\,g(t;x,y),
$$
其中 $K(x,y)$ 称为**前沿系数**（描述可传播奇性的强度），$g$ 为**尾项核**（局部可积）。据此，本文各处"前沿含奇性 $K\neq0$"即指 $K(x,y)\neq0$；此时在 $t=d_{\rm front}(x,y)/c$ 存在分布型非零响应，从而满足文中各"取等号条件"。

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

**(A4) 因果—解析一致**：在**稳定 LTI**情形，严格因果 $\Rightarrow$ 频响在上半平面解析；并且在 $h_{\rm sys}\in L^1(\mathbb R)$、$H(\omega)$ 多项式增长受控、无上半平面极点等**附加条件**下，实部与虚部满足 Kramers–Kronig 色散，且可反推严格因果（解析 $\Rightarrow$ 因果）。**LTV/非平稳**情形不使用该频域等价，仅采用 $G_{\rm ret}(t,\tau)$ 的时域支撑表述（见 §5）。**在时不变/静态介质**下，**仅断言**
$$
t_{\min}\ge \frac{D_{\rm front}}{c},\qquad
D_{\rm front}=\begin{cases}L,&\text{真空},\\ d_{\rm front}(x,y),&\text{介质/不均匀/有界域}.\end{cases}
$$
当**传播核**在前沿含奇性 $K\neq0$（如3D真空）或链路含**Dirac直通分量** $h_{\rm sys}(t)=\kappa\delta(t)+h_{\rm sc}(t)$（$\kappa\neq0$）时可取等号；若与严格因果 LTI 滤波器（脉冲响应 $h_{\rm sys}(t)$，起始时延 $t_h:=\inf\{t:\,h_{\rm sys}(t)\neq 0\}$）串联，则
$$
t_{\min}\ \ge\ \frac{D_{\rm front}}{c}+t_h,
$$
且仅当前述"前沿奇性/Dirac直通"成立并**无前沿处系统性抵消**时，方有
$$
t_{\min}=\frac{D_{\rm front}}{c}+t_h.
$$
([物理评论链接管理器][3])

**(A5) 前沿—信息一致**：在**真空或静态介质（LTI）**下，门限互信息的首次可检时间 $T_\delta$ 满足
$$
c_{\rm info}:=\lim_{\delta\downarrow0}\sup\frac{D}{T_\delta}\ \le\ c,
$$
其中 $D$ 为所用归一化的**前沿光程**。并且当且仅当满足**前沿可检**时取等 $c_{\rm info}=c$；此处"前沿可检"指：$G_{\rm ret}$ 在 $t=D/c$ 处有奇性 $K\neq0$，或测链含**Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量）**，或存在 $t_n\downarrow D/c$ 与单位能量短脉冲 $\psi$ 使 $\int G_{\rm ret}(t_n,\tau;x,y)\psi(\tau)\,d\tau\neq0$。**(i) 链路归一化（$t_h=0$）**：$D=D_{\rm front}$。**(ii) 系统归一化（$t_h>0$）**：$D=D_{\rm sys}:=D_{\rm front}+c\,t_h$。**（LTV 补充）**：对时变系统，仅断言 $T_\delta\ge t_{\min}$（由 $G_{\rm ret}(t,\tau)$ 的时域支撑定义）。([维基百科][4])

**(A6) 采样—误差闭合**：读数误差按 NPE 三分解给出非渐近上界。([webusers.imj-prg.fr][7])

**(A7) SI 对齐**：$c$ 取 SI 固定值；"以延迟计长"与"以时定长"互逆实现（§4、§12）。

**(A8) 相位密度几何**：de Branges 核对角 $K(x,x)=\tfrac{1}{\pi}\,\varphi'(x)\,|\mathcal{E}(x)|^{2}$ 诱导 $\mu_\varphi:=(\varphi'/\pi)\,dx$ 作为窗化刻度。

---

## 2. 操作性定义：时间与空间

**定义 2.1（时间）** 取窗 $w_R$ 与单位积分核 $\eta$。对链路散射 $S(E)$，定义**窗口化群延迟读数**
$$
\mathsf T[w_R,\eta]:=\hbar\,\frac{1}{2\pi}\int_\mathbb R w_R(E)\,\bigl[\eta\star \mathrm{tr}\,Q\bigr](E)\,dE,
$$
其中 $Q:=-iS^\dagger \tfrac{dS}{dE}$，$\mathrm{tr}\,Q$ 与 $\partial_E\arg\det S$ 及 $-2\pi\xi'(E)$ 等价。([物理评论链接管理器][1])

**归一规范**：约定 $(2\pi)^{-1}\!\int_{\mathbb R}\! w_R(E)\,dE=1$，且 $\int_{\mathbb R}\! \eta(E)\,dE=1$（单位积分核），据此在真空纯延迟链路上有 $\mathsf T=L/c$。验证：在 $S_L(E)=e^{iEL/(\hbar c)}$ 下有 $\mathrm{tr}\,Q=L/(\hbar c)$ 常数，代入上式并用上述归一条件立得 $\mathsf T=L/c$；与定理 4.1 保持一致。

在真空长度 $L$ 的链路上，定义的**时间坐标差**满足 $\Delta t=L/c$。

**定义 2.2（空间）** 真空中以**雷达距**定义空间距离：$d(A,B):=\tfrac{c}{2}\,\mathsf T_{\rm roundtrip}(A\to B\to A)$。

在介质/不均匀/有界域中，取高频极限折射率 $n_\infty(\mathbf x)=\lim_{\omega\to\infty}n(\mathbf x,\omega)$。定义 3D **费马（光学）度量**
$$
ds_{\rm front}=n_\infty(\mathbf x)\,|d\mathbf x|,
$$
并据此定义**前沿光程**
$$
d_{\rm front}(A,B):=\inf_{\gamma:A\to B}\int_\gamma n_\infty(\mathbf x)\,ds,
$$
则**最早可达时间**满足
$$
t_{\min}(A,B)\ge \frac{d_{\rm front}(A,B)}{c}.
$$
当（i）3D真空纯传播，或（ii）介质前沿存在奇性 $K\neq0$，或（iii）测链含Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量）时，取等号。在各向同性且 $n_\infty\equiv1$ 时，$d_{\rm front}=|A-B|$。上述与 4D Gordon 光学度量的零测地线描述在高频极限下等价，但用于计时以 3D 光程表述更为直接。([arXiv][9])

**群折射率**：对各向同性被动介质，定义
$$
n_g(\mathbf x,\omega):=n(\mathbf x,\omega)+\omega\,\partial_\omega n(\mathbf x,\omega)
=\frac{c}{v_g(\mathbf x,\omega)},
$$
其中 $v_g$ 为群速度。于是群时间 $t_g=\int_\gamma n_g\,ds/c$，相位时间 $t_\phi=\int_\gamma n\,ds/c$。**一般地不保证 $t_g$ 或 $t_\phi$ 与 $t_{\min}$ 的大小关系**（在异常色散与增益/损耗情况下可出现 $t_g<t_{\min}$ 或 $t_\phi<t_{\min}$）。**普适且与因果一致的仅是**
$$
t_{\min}\ge \frac{d_{\rm front}}{c},\qquad T_{\rm info}\ge t_{\min},
$$
且**仅当**（i）3D 真空纯传播，或（ii）介质前沿存在奇性 $K\neq0$，或（iii）测链含Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量）时，才有 $t_{\min}=d_{\rm front}/c$。其中 $T_{\rm info}$ 为任意**可检信息**的首次到达时间（见 §5）。

**往返时间**：
$$
\mathsf T_{\mathrm{roundtrip}}(A\to B\to A;\,w_R,\eta)
:=\mathsf T[w_R,\eta;\,A\to B]+\mathsf T[w_R,\eta;\,B\to A].
$$
若链路与读数协议互易（双向对称），则 $d(A,B)=\tfrac{c}{2}\,\mathsf T_{\mathrm{roundtrip}}(A\to B\to A)$。

**前沿假设（F）**：介质为被动线性、各向同性，且高频折射率存在有限极限
$$
n_\infty(\mathbf x):=\lim_{\omega\to\infty}n(\mathbf x,\omega)\in[1,\infty).
$$
据此定义前沿光学度量 $g^{\rm front}$ 与前沿光程 $d_{\rm front}$。若只能给出 $n_\infty$ 的上下界函数 $1\le \underline n_\infty(\mathbf x)\le n_\infty(\mathbf x)\le \overline n_\infty(\mathbf x)<\infty$，则对应的前沿光程满足 $\underline d_{\rm front}\le d_{\rm front}\le \overline d_{\rm front}$。**一般地仅能无条件断言**
$$
\boxed{\ t_{\min}(A,B)\ \ge\ \frac{\underline d_{\rm front}(A,B)}{c}\ },
$$
而
$$
t_{\min}(A,B)\ \le\ \frac{\overline d_{\rm front}(A,B)}{c}
$$
**仅在附加条件下成立**：当（i）3D 真空纯传播，或（ii）介质前沿存在奇性 $K\neq0$，或（iii）测链含Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量）时有 $t_{\min}=d_{\rm front}/c$，联立 $d_{\rm front}\le \overline d_{\rm front}$ 得到上界；若与严格因果 LTI 滤波器串联且起始时延有上界 $t_h$，则
$$
t_{\min}\ \ge\ \frac{d_{\rm front}}{c}+t_h,
$$
并且仅当前述等号条件满足且无前沿抵消时，方有 $t_{\min}=\frac{d_{\rm front}}{c}+t_h\le \frac{\overline d_{\rm front}}{c}+t_h$。
本稿其他处对"等号何时成立"的口径与 §5 保持一致。**仅当**被动因果介质满足高频真空化（典型模型下 $n(\mathbf x,\omega)\to1$）时，实验坐标中才**恢复** $t_{\min}=|A-B|/c$ 与"波前速度 $=c$"；一般介质则保持 $t_{\min}\ge d_{\rm front}/c$ 的陈述。

**定义 2.3（同时切片）** 选参考世界线与往返协议，令 $\Sigma_t:=\{e\in\mathcal E:\ \mathsf T_{\rm roundtrip}=2t\}$，其三维度量由雷达距或 $g^{\rm front}$ 诱导。

---

## 3. 时空的结构化定义

**定义 3.1（WSIG–EBOC 时空）** 若存在窗化散射读数使：

(1) **度量—读数一致**：真空链路 $L$ 上 $\mathsf T=L/c$；介质**前沿光程**与前沿一致，即 $d_{\rm front}$ 为 **3D 费马（光学）度量** $ds_{\rm front}=n_\infty|\mathrm dx|$ 的**测地光程极小值**；

(2) **三重字典**：$\partial_E\arg\det S=\mathrm{tr}\,Q=-2\pi\xi'(E)$；

(3) **NPE 可检**：误差别名/Poisson/EM 余项有全局上界；

(4) **信息—因果一致（真空或静态介质〔LTI〕）**：首次可检互信息时间 $T_\delta$ 满足
$$
c_{\rm info}:=\lim_{\delta\downarrow0}\sup\frac{D_{\rm front}}{T_\delta}\ \le\ c,
$$
**且仅当**满足**前沿可检**（见 A5、§5）时取等 $c_{\rm info}=c$。**（串联滤波补充）**：若测链含严格因果 LTI 滤波器且起始时延 $t_h>0$，则以上 $D_{\rm front}$ **全部替换为** $D_{\rm sys}:=D_{\rm front}+c t_h$。**（LTV 补充）**：对时变系统，仅断言 $T_\delta\ge t_{\min}$（由 $G_{\rm ret}(t,\tau)$ 的时域支撑定义）。

则四元组 $(\mathcal E,\preceq,g,\mu_\varphi)$ 为一**时空**。([arXiv][2])

---

## 4. 主等价定理（相位—延迟—谱移—SI）

**定理 4.1**（四等价） 设真空链路 $L$ 的散射 $S_L(E)=\exp\!\bigl(i E L/(\hbar c)\bigr)$。则
$$
\mathsf T[w_R,\eta;L]
=\hbar\,\big\langle \partial_E\arg\det S_L\big\rangle_{w,\eta}
=\hbar\,\big\langle \mathrm{tr}\,Q_L\big\rangle_{w,\eta}
=-\,\hbar\,2\pi\,\big\langle \xi'(E)\big\rangle_{w,\eta}
=\frac{L}{c},
$$
且在 Nyquist 带宽极限下所得 $c=\lim L/\mathsf T$ 与窗/核无关，并与 SI 数值一致。

**证明**：

**假设（单模纯延迟链路）**：取单通道 $S_L(E)=\exp\!\bigl(iE L/(\hbar c)\bigr)$。窗 $w_R\in L^1(\mathbb R)$、核 $\eta\in L^1(\mathbb R)$ 满足归一规范
$$
\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,dE=1,\qquad \int_{\mathbb R} \eta(E)\,dE=1.
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
\mathsf T[w_R,\eta;L]
=\hbar\,\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,\bigl[\eta\star \operatorname{tr}Q_L\bigr](E)\,dE.
$$
因 $\operatorname{tr}Q_L\equiv L/(\hbar c)$ 为常数，卷积与积分交换并用两条归一，得
$$
\mathsf T[w_R,\eta;L]
=\hbar\cdot\frac{1}{2\pi}\cdot\frac{L}{\hbar c}\!\int w_R(E)\,dE\cdot\!\int \eta(\nu)\,d\nu
=\frac{L}{c}.
$$
再结合引理 1–2，于被积函数恒定之事实，立得
$$
\mathsf T
=\hbar\,\big\langle \partial_E\arg\det S_L\big\rangle_{w,\eta}
=\hbar\,\big\langle \operatorname{tr}Q_L\big\rangle_{w,\eta}
=-\,\hbar\cdot 2\pi\,\big\langle \xi'(E)\big\rangle_{w,\eta}
=\frac{L}{c}.
$$

**误差闭合说明（NPE）**：Nyquist/Poisson/Euler–Maclaurin 三项在"常数被积"情形下分别为 0：别名项为 0，Poisson 周期化项为 0，EM 余项因高阶导数为 0 而为 0。故极限与窗/核无关，且与 SI 数值一致。$\square$

---

## 5. 因果前沿与信息光锥

**定理 5.1（因果前沿不超 $c$；等号条件）** 线性且严格因果、**时不变（静态介质）**信道的最早非零响应时间满足
$$
t_{\min}\ge \frac{D_{\rm front}}{c},\qquad
D_{\rm front}=\begin{cases}L,&\text{真空},\\ d_{\rm front}(x,y),&\text{介质/不均匀/有界域}.\end{cases}
$$
且在**3D真空自由空间纯传播**时 $t_{\min}=L/c$；对一般介质/有界域，若前沿含奇性 $K\neq0$ 或链路含Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量），亦有 $t_{\min}=d_{\rm front}/c$；若与严格因果LTI滤波器串联，则 $t_{\min}\ge D_{\rm front}/c+t_h$（等号需前沿可检且无抵消）。

**（LTV 备注）**：对线性**时变**系统，仅以 $G_{\rm ret}(t,\tau)$ 的**时域支撑**表述前沿；本文不以静态 $d_{\rm front}$ 代表时变介质的前沿。

**证明**：设系统线性且严格因果、时不变（静态介质）。由因果性，
$$
G_{\rm ret}(t,\tau;x,y)=0\quad\text{当}\quad t<\tau.
$$
令源信号 $x$ 支持于 $t\ge0$，则
$$
y(t)=\int_{\mathbb R}G_{\rm ret}(t,\tau;x,y)\,x(\tau)\,d\tau,\qquad y(t)=0\ (t<0).
$$

**真空、均匀、无耗 3D 标量波动方程：**
$$
G_{\rm ret}(t,r)=\frac{\delta(t-r/c)}{4\pi r},
$$
支撑仅在 $t=r/c$，故对链路长度 $L$ 有 $t_{\min}(L)=L/c$。**Maxwell** 情形由 dyadic 核对上式施以张量—微分算子（含 $\delta$ 及其导数），支撑同样仅在光锥上，结论不变。

**一般介质/不均匀/有界域（以下确界口径）**：在**前沿假设（F）**下，$n_\infty(\mathbf x)$ 存在且有限，由高频几何光学的前沿传播界得
$$
\operatorname{supp}_t G_{\rm ret}^{\rm med}(t,\tau;x,y)\ \subseteq\ [\,\tau+d_{\rm front}(x,y)/c,\ \infty).
$$
因此当 $t<d_{\rm front}(x,y)/c$ 时响应为零。若前沿含奇性 $K\neq0$ 或链路含Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量），则在 $t=d_{\rm front}(x,y)/c$ 处存在分布型非零响应，从而
$$
t_{\min}= \tfrac{d_{\rm front}(x,y)}{c};
$$
否则仅能断言
$$
\boxed{\ t_{\min}\ \boldsymbol{\ge}\ \tfrac{d_{\rm front}(x,y)}{c}\ },
$$
且通常严格大于。若与严格因果 LTI 滤波器串联且起始时延 $t_h>0$，则
$$
t_{\min}\ \ge\ \tfrac{d_{\rm front}(x,y)}{c}+t_h,
$$
并且**仅当**前沿含奇性 $K\neq0$ 或链路具有Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量），且不存在前沿处抵消时，方可取等号。

因此在真空情形下，当 $t<L/c$ 时，对任意 $\tau\ge 0$，有 $t-\tau<L/c\Rightarrow G_{\rm ret}(t-\tau,L)=0$，从而 $y(t)=0$。**取单位能量短脉冲族** $x_\eta=\psi_\eta$（$\psi_\eta\to\delta$ 为近似恒等核），则
$$
y_\eta(t)=\big(G_{\rm ret}*\psi_\eta\big)(t)=\frac{\psi_\eta(t-L/c)}{4\pi L},
$$
从而 $\lim_{\eta\downarrow 0}y_\eta(t)=\delta(t-L/c)/(4\pi L)$，最早非零响应仍在 $t=L/c$。该论证与"可检读数"口径一致。

**（LTI 情形）**：因果 $\Leftrightarrow$ 上半平面解析（稳定 LTI）。在**纯延迟链路** $G(t)=\delta(t-L/c)$ **或**串联严格因果滤波器且具有**Dirac直通分量（即脉冲响应含 $\delta(t)$ 分量）**时，**最小支撑端点**为 $L/c$。对**一般 LTI** 系统（脉冲响应 $h_{\rm sys}(t)$），最早非零响应时间由其支撑给出
$$
t_{\min}=\inf\{t:\,h_{\rm sys}(t)\neq 0\},\qquad
t_{\min}=L/c+t_h\ \ (\text{若与纯延迟串联}).
$$
其中 $t_h:=\inf\{t:\,h_{\rm sys}(t)\neq 0\}$ 为系统起始时延。

**（LTV 情形）**：上述频域等价一般不成立，应直接以 $G_{\rm ret}(t,\tau)$ 的支撑性质陈述和证明前沿。$\square$

**定理 5.2（信息光锥；上界与等号条件）** 在真空或静态介质（LTI）下，门限互信息的首次可检时间 $T_\delta$ 满足
$$
c_{\rm info}:=\lim_{\delta\downarrow0}\sup\frac{D}{T_\delta}\ \le\ c,
$$
其中 $D$ 为所用归一化的**前沿光程**。**且当且仅当**满足**前沿可检**时取等 $c_{\rm info}=c$。

**(i) 链路归一化（$t_h=0$）**：$D=D_{\rm front}$；若满足**前沿可检**（定义同 A5），则 $c_{\rm info}=c$。

**(ii) 系统归一化（串联严格因果 LTI，$t_h>0$）**：$D=D_{\rm sys}:=D_{\rm front}+c\,t_h$；若满足**前沿可检**，则 $c_{\rm info}=c$。

**（LTV 补充）**：对线性时变系统，仅断言 $T_\delta\ge t_{\min}$。

**证明**：设输入过程 $X$ 支持于 $t\ge 0$，噪声 $N$ 与 $X$ 独立，接收端观测
$$
Y_t := \{Y(s): 0\le s\le t\},\qquad Y(t)=\int_{\mathbb R} G_{\rm ret}(t,\tau;x,y)\,X(\tau)\,d\tau+N(t).
$$
**注**：真空/线性时不变（LTI）情形下 $G_{\rm ret}(t,\tau;x,y)=G_{\rm ret}(t-\tau;|x-y|)$，可写为 $Y=G_{\rm ret}\!*\!X+N$。

**(1) 零互信息（前沿之前）**：对情形 (i)，若在**真空** $t<L/c$（或在**介质/不均匀/有界域** $t<d_{\rm front}(x,y)/c$），则 $Y(s)=N(s)$，故 $I(X;Y_t)=0$。对情形 (ii)，前沿改为 $D_{\rm sys}/c$。

**(2) 前沿之后（情形 i 的完整证明；情形 ii 仅需替换 $D_{\rm front}\to D_{\rm sys}$）**：

若满足**前沿可检**（情形 i）或系统含串联滤波（情形 ii），则对任意小 $\varepsilon>0$，令
$$
t_\varepsilon:=\tfrac{D_{\rm front}}{c}+\varepsilon\quad\text{（情形 i）},\qquad
t_\varepsilon:=\tfrac{D_{\rm sys}}{c}+\varepsilon\quad\text{（情形 ii）},
$$
取标量试探 $X_\alpha(\tau)=\alpha\,\psi(\tau)$（$\psi$ 为单位能量的短时脉冲），有
$$
Z_\varepsilon:=\int_0^{t_\varepsilon}G_{\rm ret}(t_\varepsilon,\tau;x,y)\,\psi(\tau)\,d\tau\neq0.
$$
**真空情形**（情形 i）：取**连续且 $\psi(0)\neq 0$** 的单位能量短脉冲，则 $Z_\varepsilon=\psi(\varepsilon)/(4\pi L)\neq 0$。**介质情形**（情形 i）：由前沿奇性 $K\neq0$ 或尾项在 $t\ge d_{\rm front}/c$ 的支撑给出 $Z_\varepsilon\neq 0$。**串联滤波情形**（情形 ii）：系统响应在 $t\ge D_{\rm sys}/c$ 可检。

引入等概符号 $S\in\{\pm1\}$，设 $X_S(\tau):=S\,\alpha\,\psi(\tau)$，则 $Y(t_\varepsilon)=S\,\alpha\,Z_\varepsilon+N(t_\varepsilon)$。令 $N(t_\varepsilon)\sim\mathcal N(0,\sigma^{2})$，记 $X:=S\,\alpha$，取 $\mathrm{SNR}:=\alpha^{2}|Z_\varepsilon|^{2}/\sigma^{2}$。由 I–MMSE 小 SNR 斜率得
$$
I\bigl(X;Y(t_\varepsilon)\bigr)=\tfrac{1}{2}\,\mathrm{SNR}+o(\mathrm{SNR})=\frac{\alpha^{2}|Z_\varepsilon|^{2}}{2\sigma^{2}}+o(\alpha^{2}).
$$
因 $Y(t_\varepsilon)$ 为 $Y_{[0,t_\varepsilon]}$ 的可测函数，故 $I\bigl(X;Y_{[0,t_\varepsilon]}\bigr)\ge I\bigl(X;Y(t_\varepsilon)\bigr)$。对任意小 $\delta>0$，可取充分小 $\alpha$ 使 $I\bigl(X;Y_{[0,t_\varepsilon]}\bigr)\ge\delta$，便得 $T_\delta\le t_\varepsilon$。因此 $\forall \varepsilon>0,\ \exists \delta(\varepsilon)\downarrow 0:\,T_\delta\le t_\varepsilon$，由是情形 (i) 给出 $c_{\rm info}=c$，情形 (ii) 同样给出 $c_{\rm info}=c$。

$\square$

**注**：情形 (ii) 的证明与情形 (i) 完全相同，仅需把 $D_{\rm front}$ 替换为 $D_{\rm sys}=D_{\rm front}+c t_h$，从而消除 §5.1 中 $t_{\min}\ge D_{\rm front}/c+t_h$ 与信息光锥速度的矛盾。

---

## 6. 相位密度几何与迹公式

**命题 6.1** 在 de Branges 空间 $\mathcal H(\mathcal{E})$ 上，几乎处处 $K(x,x)=\tfrac{1}{\pi}\,\varphi'(x)\,|\mathcal{E}(x)|^{2}$。因此**相位密度** $\rho(x):=\varphi'(x)/\pi$ 给出自然测度。令再生核正交投影 $\Pi$，并取 $T_{w_\varphi}:=M_{\sqrt{w_\varphi}}\Pi M_{\sqrt{w_\varphi}}$。**若** $w_\varphi\ge0$ 且 $w_\varphi\in L^{1}\cap L^\infty(d\mu_\varphi)$（或以 $w_\varphi^{(n)}\uparrow w_\varphi$ 之单调截断极限理解），**则** $T_{w_\varphi}$ 为迹类，并且
$$
\mathrm{Tr}(T_{w_\varphi})=\int_{\mathbb R} w_\varphi(E)\,\rho(E)\,dE,\qquad \rho(E)=\frac{\varphi'(E)}{\pi}.
$$
这里的积分变量 $E$ 与 §2 的能量变量一致。该恒等式为"相位—密度—延迟"在 RKHS 的实现。

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
\varepsilon_{\rm tail}:=\hbar\,\frac{1}{2\pi}\int_{|E|>R} w_R(E)\,[\eta\star \mathrm{tr}Q](E)\,dE.
$$
若 $\int_{|E|>R}|w_R(E)|\,dE\le \epsilon$、$\eta\in L^{1}$，并且记 $\Omega_E:=\operatorname{supp}(w_R)\oplus \operatorname{supp}(\eta)$，且 $\mathrm{tr}\,Q\in L^\infty(\Omega_E)$，则
$$
|\varepsilon_{\rm tail}|\le \frac{\hbar}{2\pi}\,\epsilon\,\|\eta\|_{L^{1}}\,\operatorname*{ess\,sup}_{E\in \Omega_E}|\mathrm{tr}\,Q(E)|.
$$
在真空纯延迟链路中，$\mathrm{tr}Q_L$ 为常数，故三项误差（别名/EM/尾项）皆为 0（见 §4）。

* **Nyquist（别名）**：若 $\widehat f$ 带限于 $(-\pi/\Delta E,\pi/\Delta E)$，则别名为 0；否则可用频谱抽样上界量化。([webusers.imj-prg.fr][7])
* **Poisson 求和**：把离散采样与周期化严格联结，用于评估别名项。([dlmf.nist.gov][13])
* **Euler–Maclaurin（有限阶）**：余项满足 $|R_{p}|\le \frac{2\zeta(p)}{(2\pi)^p}\int|f^{(p)}|$，给出端点/尾项的可检上界。([dlmf.nist.gov][14])

**（真空纯延迟校准链路）**：综上，时间读数满足
$$
\mathsf T=\tfrac{L}{c}+\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$
三误差在规程内可控并收敛。

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
* **介质几何**：Gordon 光学度量把折射/流速吸收入度量，因而**在前沿光学度量中**按定义始终有"前沿 $=c$"。**实验坐标**下仅能保证 $t_{\min}\ge d_{\rm front}/c$；且**仅当**满足 §5 的**等号条件**（真空纯传播/前沿奇性/含Dirac直通分量，或再加严格因果 LTI 滤波器已知 $t_h$）时，方可恢复"前沿 $=c$"。若并且 $n_\infty\equiv1$，则 $d_{\rm front}=|A-B|$（此时是否取等仍取决于前述条件）。([arXiv][9])

---

## 11. 结论性定义（汇总）

* **时间**：在给定窗—核与读数协议下，时间是**窗口化群延迟坐标**，即 $t\equiv \hbar\int \tfrac{w_R}{2\pi}\,[\eta\!\star\!\mathrm{tr}\,Q]\,dE$。
* **空间**：通过等时往返读数选定的**同时切片 $\Sigma_t$** 及其三维度量。真空中由雷达距定义；介质情形以**前沿光学度量**诱导的 **3D 费马度量** $ds_{\rm front}=n_\infty(\mathbf x)|\mathrm dx|$ 的**测地光程极小值**定义 $d_{\rm front}$（高频极限 $n_\infty=\lim_{\omega\to\infty}n(\mathbf x,\omega)$ 决定），最早可达时间满足 $t_{\min}\ge d_{\rm front}/c$；**仅当**（i）3D 真空纯传播，或（ii）介质前沿存在奇性 $K(x,y)\neq0$，或（iii）测链含Dirac直通分量（即 $h_{\rm sys}(t)$ 含 $\delta(t)$ 分量）时，方有 $t_{\min}=d_{\rm front}/c$。**在前沿光学度量下**波前速度按定义为 $c$；**实验坐标**下：若 $n_\infty\equiv1$，则 $d_{\rm front}=|A-B|$ 且无条件仅得 $t_{\min}\ge |A-B|/c$；**仅在** §5 的等号条件（或外接严格因果 LTI 滤波器使 $t_h>0$ 时改以 $D_{\rm sys}$ 计）下，方可**恢复**"前沿速度 $=c$"的结论。
* **时空**：四元组 $(\mathcal E,\preceq,g,\mu_\varphi)$，其中 $\preceq$ 来自 $G_{\rm ret}$ 光锥支撑，$g$ 为（光学）洛伦兹度量，$\mu_\varphi=(\varphi'/\pi)\,dx$ 为相位密度刻度；在 NPE 账本下可检、可校准，并与 SI 互逆实现。

---

## 12. 实施规程（简述）

1. 选几何已知的真空链路 $L$；2) 宽带激励，测得 $\hat\tau=\mathsf T[w_R,\eta;L]$；3) 检验 Nyquist（带限/反混叠）、估计 Poisson/EM 余项；4) 取 $\hat c=L/\hat\tau$，与频率链/干涉计长度链交叉校准闭环。([webusers.imj-prg.fr][7])

---

## 13. 证明脉络与外部索引

* $\partial_E\arg\det S=\mathrm{tr}\,Q$ 与 BK 恒等式：([arXiv][2])
* KK—因果等价（稳定 LTI 限定）与前沿光锥：([物理评论链接管理器][3])
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

**证明**：设真空链路 $L$。由定理 4.1，窗化群延迟读数给出 $\mathsf T=L/c$。由定理 5.1，最早非零响应时间 $t_{\min}(L)=L/c$，故"相位斜率/群延迟"与"因果前沿"一致。由定理 5.2，真空链路因 $G_{\rm ret}(t,r)=\delta(t-r/c)/(4\pi r)$ 含前沿奇性（$\delta$ 分布）而满足**前沿可检**条件，故门限互信息的首次可检时间 $T_\delta(L)\to L/c$（$\delta\downarrow 0$），于是"信息光锥"与前沿一致。SI 中 $c$ 为固定常数，长度—时间互逆实现（§2、§12 的往返/雷达规程）即给出 $\hat c=L/\hat\tau$ 与频率链/干涉计长度链的闭环一致性。因此四者（A）相位斜率/谱移密度，（B）因果前沿，（C）信息光锥，（D）SI 实现，两两等价。$\square$

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
