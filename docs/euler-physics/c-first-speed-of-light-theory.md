# $(c)$-FIRST：光速常数的窗口化群延迟表述、等价层、误差账本与完整证明（全文）

**Version: 1.24**（2025-10-31，Asia/Dubai）

**作者**：Auric（EBOC / WSIG / S-series）

**关键词**：光速常数；因果前沿；Wigner–Smith 延迟；Birman–Kreĭn 公式；谱移函数；Kramers–Kronig（因果—解析）；微因果；信息光锥；Nyquist–Poisson–Euler–Maclaurin 误差账本；SI 计量基准

**MSC**：81U05；47A40；94A15；78A40；83A05

---

## 0.0 立场声明

本文不对光速常数 $c$ 作任何重新定义或数值调整。$c$ 的常数地位与数值属于既定理论与度量学体系之内容。本文仅提供一种**窗口化群延迟**视角下对 $c$ 的**新表述**：在严格指明的理想模型与条件下，相关群延迟量与路径长度之比呈现为 $c$ 的等价刻画。这一表述是数学—物理结构的重述，而非对常数的重定标。

---

## 0.1 误差 = 解析余项（用语与符号约定）

本文中**误差**一词严格指**数学逼近的解析余项**，与实验测量误差或统计不确定度无关。典型情形包括（但不限于）：
$$
\mathsf{Err}=\underbrace{\mathsf{err}_{\mathrm{alias}}}_{\text{采样与混叠项}}+\underbrace{\mathsf{err}_{\mathrm{EM}}^{(N)}}_{\text{Euler–Maclaurin 有限阶余项}}+\underbrace{\mathsf{err}_{\mathrm{tail}}}_{\text{窗/频带外尾项}}.
$$
上式各项均为**确定性**（可上界/可控制）量；若无特别说明，本文所有"误差""误差账本"均作如上**解析意义**理解。

---

## 0.2 记号与单位

设能量变量为 $E=\hbar \omega$，散射矩阵 $S(E)\in\mathrm U(N)$ 可对能量求导。**Wigner–Smith 延迟矩阵**定义为 $Q(E):=-\,i\,S(E)^\dagger\,\frac{dS}{dE}(E)$；它是厄米矩阵，**总群延迟**记为 $\tau_{\mathrm{WS}}(E):=\hbar\,\operatorname{tr}Q(E)$（单位：秒）。**Smith（1960）原始"寿命矩阵"将 $\hbar$ 并入矩阵定义，记 $Q_{\text{Smith}}:=-\,i\,\hbar\,S^\dagger \frac{dS}{dE}$；本文采用不含 $\hbar$ 的 $Q$ 约定，并以 $\tau_{\mathrm{WS}}=\hbar\,\operatorname{tr}Q$ 表示总群延迟，二者仅差一个 $\hbar$ 因子（量纲与 §13.1 一致）。**这一构造在电磁、声学等多域广泛使用。([APS链接][1])

本文默认单模链路（$N=1$；多端口情形见第 11 节），并对观测采用带宽随 $R\uparrow$ 增长的窗 $w_R$（归一化 $\int_{\mathbb R} w_R(E)\,dE=2\pi$）与前端核 $h$ 的卷积，**其中 $h\in L^1(\mathbb R)$ 且归一化为 $\int_{\mathbb R} h(E)\,dE=1$**，因此对任意常值 $C_0$ 有 $h\!\star\! C_0=C_0$（避免与下文的光速常数 $c$ 混淆）。SI 与计量对齐采用"固定 $c$"的定义：$\,c=299\,792\,458\,\mathrm{m\,s^{-1}}$ 为**精确常数**，米用 $l=c\,\Delta t$ 实现。([BIPM][2])

---

## 1. 主表述（WSIG）与要证目标

### 1.1 窗口化群延迟读数（定义）

**窗口化群延迟读数**定义为
$$
\mathsf T[w_R,h;L]\ :=\ \frac{\hbar}{2\pi}\int_{\mathbb R} w_R(E)\,\bigl[h\!\star\!\operatorname{tr}Q_L\bigr](E)\,dE,
$$
上式诱导记号：$\ \displaystyle \langle f\rangle_{w,h}:=\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,[h\!\star\! f](E)\,dE,$，于是 $\ \mathsf T=\hbar\,\langle \operatorname{tr}Q_L\rangle_{w,h}$。其中 $L$ 是端点的欧氏几何距。

### 1.2 表述（光速的窗口化群延迟基线）

在自由空间（真空、均匀、无界、无耗散）的理想模型下，对长度 $L$ 的真空链路与任意满足 $\int_{\mathbb R}w_R(E)\,dE=2\pi$ 与 $\int_{\mathbb R}h(E)\,dE=1$ 的窗口/前端核对 $(w_R,h)$，窗口化群延迟读数满足
$$
\boxed{\quad \mathsf T[w_R,h;L]=\frac{L}{c}\quad}
$$
为便于后文引用，可记 $\bar{\tau}_{\mathrm{vac}}[w_R,h;L]:=\mathsf T[w_R,h;L]$。该表述仅为对既定常数 $c$ 的结构性重述，不涉及对 $c$ 的重定义或数值调整。

### 1.3 要证目标

**本文主线**：证明上式表述之 $c$ 与下列四类结构**互为等价**：

* （A）**相位斜率 / 谱移密度**：$\ \partial_E\arg\det S=\operatorname{tr}Q=-2\pi\,\xi'(E)$（BK 公式），故 $\mathsf T=\hbar\langle \partial_E\arg\det S\rangle$。([arXiv][3])
* （B）**因果前沿**：严格因果 $\Leftrightarrow$ 频响上半平面解析（KK），3D 推迟格林函数支撑在光锥 $t=r/c$ 上，故**最早非零响应速度**为 $c$。([APS链接][4])
* （C）**信息光锥（在假设 7.0 下）**：互信息首次可检阈值速度的上确界等于 $c$。([APS链接][5])
* （D）**SI 实现互逆**："以时定长"（SI）与"以延迟计长"（本文）互为实现。([BIPM][2])

此外给出**Nyquist–Poisson–Euler–Maclaurin（NPE）**非渐近误差账本，实现工程可检。([fab.cba.mit.edu][6])

---

## 2. 基本性质与引理

### 引理 2.1（$Q$ 的厄米性与相位导数恒等式）

若 $S(E)$ 幺正可微，则 $Q(E)=-\,i\,S^\dagger S'$ 厄米，且
$$
\partial_E\arg\det S(E)=\operatorname{tr}Q(E).
$$

**证明**：由 $S^\dagger S=I$ 得 $(S^\dagger)'\,S+S^\dagger S'=0\Rightarrow (S^\dagger)'\,S=-S^\dagger S'$。故
$$
Q^\dagger= i (S^\dagger)' S= - i S^\dagger S'=Q.
$$
又 $\partial_E\ln\det S=\operatorname{tr}(S^{-1}S')=\operatorname{tr}(S^\dagger S')=i\,\operatorname{tr}Q$，取虚部即得 $\partial_E\arg\det S=\operatorname{tr}Q$。—证毕。

（与 Smith 的"寿命矩阵"在 $\hbar$ 因子上一致；参见 §0 的约定说明。）([APS链接][1])

### 引理 2.2（BK 公式与谱移导数）

取 Birman–Kreĭn 约定 $\det S(E)=\exp\{-\,2\pi i\,\xi(E)\}$，则
$$
\operatorname{tr}Q(E)=-\,2\pi\,\xi'(E).
$$

**证明**：对上式取导：$\partial_E\ln\det S=-2\pi i\,\xi'$。又 $\partial_E\ln\det S=i\,\operatorname{tr}Q$，合并得 $\operatorname{tr}Q=-2\pi\,\xi'$。—证毕。([arXiv][3])

> **注**：文献亦见不同号约定；本文一律采用上式带"−"号的 BK 约定。([arXiv][3])

---

## 3. 真空链路的 $S$ 与 $\operatorname{tr}Q$

对理想真空链路长度 $L$，平面波传播相位为 $\phi(E)=E\,L/(\hbar c)$；因无耦合、无增益/损耗，故
$$
S_L(E)=e^{\,i\phi(E)}\in \mathrm U(1),\qquad \Rightarrow\quad Q_L(E)=\frac{d\phi}{dE}=\frac{L}{\hbar c},
$$
为**与能量无关的常数**。据此
$$
\mathsf T[w_R,h;L]=\frac{\hbar}{2\pi}\!\int w_R(E)\,[h\!\star\!Q_L](E)\,dE
=\frac{\hbar}{2\pi}\!\int w_R(E)\,Q_L\,dE
=\frac{\hbar}{2\pi}\cdot 2\pi\cdot \frac{L}{\hbar c}=\frac{L}{c}.
$$

因此若忽略采样与带宽截断误差，则主表述直接给出 $c=L/\mathsf T$。下面用 NPE 误差账本严格控制有限带宽与离散观测误差（第 8 节）。关于 $Q$、$\tau_{\mathrm{WS}}$ 的物理与测量见 Smith 原文与当代综述。([APS链接][1])

---

## 4. 主表述的**存在—唯一**与窗/核无关性（完整证明）

**命题 4.1**：在真空链路上，窗口化群延迟读数 $\mathsf T[w_R,h;L]=L/c$ 的关系存在且唯一，与窗 $w_R$ 与前端核 $h$ 的具体形状无关。

**证明**：

1. **常值结构**：由第 3 节，$\operatorname{tr}Q_L(E)\equiv L/(\hbar c)$。卷积 $h\!\star\!\operatorname{tr}Q_L$ 与加窗平均均不改变常值。

2. **Nyquist（别名项）**：若被测与窗—核的总频谱在**能量的共轭变量** $\tau$（单位：$\mathrm{J}^{-1}$）上**严格带限**，即 $\widehat f(\tau)$ 支撑于 $|\tau|<\tau_{\max}$，则 Poisson 求和给出**无混叠的充要条件**
$$
\boxed{\ \frac{2\pi}{\Delta E}>2\,\tau_{\max}\ \Longleftrightarrow\ \Delta E<\frac{\pi}{\tau_{\max}}\ }.
$$
在该条件下频谱重复项不重叠，从而 $\varepsilon_{\mathrm{alias}}=0$。若仅具"有效带宽"（存在带外尾项，非严格带限），则一般 $\varepsilon_{\mathrm{alias}}\neq0$，其量级由带外能量与 $\Delta E$ 给出，应按 §8.1 的上界并入误差账本。([fab.cba.mit.edu][6])

3. **Poisson—EM（端点与尾项）**：为应用 Euler–Maclaurin 上界，取整数 $m\ge 1$，并假设 $g(E):=w_R(E)\,[h\!\star\!\operatorname{tr}Q_L](E)\in C^{2m}[a,b]$ 且 $g^{(2m)}$ 可积；在真空链路下因 $h\!\star\!\operatorname{tr}Q_L$ 为常值，选择 $w_R\in C^{2m}_c$ 即可满足该条件。设能量步长为 $\Delta E$，节点 $E_n=a+n\,\Delta E$。则**求和公式**的 Euler–Maclaurin 余项满足
$$
\bigl|R_{2m}\bigr|
\ \le\ \frac{2\,\zeta(2m)}{(2\pi)^{2m}}\,(\Delta E)^{2m-1}
\int_{a}^{b}\!\bigl|g^{(2m)}(E)\bigr|\,dE
\ \le\ \frac{2\,\zeta(2m)}{(2\pi)^{2m}}\,(\Delta E)^{2m-1}(b-a)\,
\sup_{E\in[a,b]}\bigl|g^{(2m)}(E)\bigr|.
$$
将其与**梯形积分**联系起来（两边乘以 $\Delta E$ 并整理），得到对 $\displaystyle \int_a^b g(E)\,dE$ 的**梯形法**误差上界为 $O\!\bigl((\Delta E)^{2m}\bigr)$。因此在**固定带宽**下，端点/尾项误差随 $m\uparrow$ 或 $\Delta E\downarrow$ 按 $(\Delta E)^{2m}$ 收敛（$m=1$ 时即 $O((\Delta E)^2)$），与 §8.2 的严格推导保持一致。—证毕。([carmamaths.org][7])

4. **极限与唯一性（理论项）**：综合 1)–3)，在真空链路下
$$
\mathsf T[w_R,h;L]
=\frac{\hbar}{2\pi}\!\int_{\mathbb R} w_R(E)\,[h\!\star\!\operatorname{tr}Q_L](E)\,dE
=\frac{L}{c}.
$$
因此 $\lim_{\text{带宽}\uparrow}\mathsf T=L/c$ 存在且与 $w_R,h$ 无关，从而窗口化群延迟表述给出 $c=L/\mathsf T$ 的唯一关系。

**与实测值的区分**：有限采样与有限带宽下，观测量
$$
\mathrm{Obs}
=\mathsf T[w_R,h;L]
+\varepsilon_{\mathrm{alias}}+\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}},
$$
其中各 $\varepsilon$ 的上界如 §8 所述，随带宽↑、步长↓、阶数↑ 而收敛至 0。—证毕。

---

## 5. 等价层（一）：相位—谱移—延迟（完整证明）

**定理 5.1**：取 BK 约定 $\det S(E)=\exp\{-2\pi i\,\xi(E)\}$，则几乎处处
$$
\boxed{\ \operatorname{tr}Q(E)=\partial_E\arg\det S(E)=-\,2\pi\,\xi'(E)\ }.
$$

**证明**：已于引理 2.1–2.2 逐步给出：$\partial_E\arg\det S=\operatorname{tr}Q$，而 BK 给 $\partial_E\ln\det S=-2\pi i\,\xi'$。二式相合即得。—证毕。([arXiv][3])

**推论 5.2**：窗口化平均下
$$
\mathsf T[w_R,h;L]=\hbar\,\Big\langle \partial_E\arg\det S_L \Big\rangle_{w,h}
=\,-\,\hbar\,2\pi\,\langle \xi'(E)\rangle_{w,h}.
$$

真空链路 $S_L(E)=e^{iEL/(\hbar c)}\Rightarrow \partial_E\arg\det S_L=L/(\hbar c)$，故 $\mathsf T=L/c$。—证毕。

> 注：更一般的障碍散射、波迹与 BK 的联系可见 Borthwick 的系统论述。([arXiv][8])

---

## 6. 等价层（二）：因果前沿 = $c$（完整证明）

### 6.1 KK—因果等价（Toll）

为避免与 §1.1 的能量域前端核 $h(E)$ 混淆，本节将**时域脉冲响应**记为 $\kappa(t)$，其频率（复频）响应记为
$$
K(z):=\int_{0}^{\infty}\kappa(t)\,e^{izt}\,dt,\qquad \Im z>0.
$$

**定理 6.1（Toll）**：稳定线性时不变系统的严格因果性（$\kappa(t)=0,\ t<0$）与其频率响应 $K(\omega)$ 的上半平面解析性及 **Kramers–Kronig** 色散关系逻辑等价。([APS链接][4])

**证明要点**：

(i) 若 $\operatorname{supp}\kappa\subset[0,\infty)$，则 $K(z)$ 在 $\Im z>0$ 全纯，边界值满足 Hilbert 变换，得 KK 关系；

(ii) 反向由 Paley–Wiener–Titchmarsh 定理：若 $K$ 可在上半平面解析并满足适当增长条件，逆变换得 $\kappa(t)$ 支持于非负半轴。因此**严格因果 $\Leftrightarrow$ KK**。—证毕。([APS链接][4])

### 6.2 光锥前沿（仅适用于自由空间）

对三维**标量**波动方程，在**自由空间（真空、均匀、无界、无耗散）**模型下，推迟格林函数为
$$
G_{\mathrm{ret}}(t,\mathbf r)=\frac{\delta\!\bigl(t-|\mathbf r|/c\bigr)}{4\pi|\mathbf r|},
$$
其支撑严格位于**光锥** $t=r/c$。对于 **Maxwell** 方程，在同样条件下，时域 **dyadic（张量）**格林函数可由标量核 $\delta(t-r/c)/(4\pi r)$ 经张量微分算子生成，因而为**分布级**的 $\delta$ 及其导数在 $t=r/c$ 上的组合；据此**最早非零前沿**为 $t=r/c$。

**适用限制**：在存在色散/耗散或边界的介质中通常出现 $t>r/c$ 的尾项；但在无超信号性的理论中**前沿不早于** $r/c$。—证毕。([solar.physics.montana.edu][9]; dyadic 结构见 [ETH Zürich][15])

### 6.3 快/慢光与前驱

色散介质可出现 $v_g>c$ 或负群速，但信息/前沿速度不超过 $c$。Sommerfeld–Brillouin 前驱解析式与实验（Stenner–Gauthier–Neifeld；Macke–Ségard）均证实"可检信息最早不早于真空同程"。([PubMed][10])

---

## 7. 等价层（三）：信息光锥（在下述通信模型假设下的证明）

**假设 7.0（通信模型，允许预共享资源）**：信道为严格因果的真空 LTI 链路；允许发送端与接收端**预共享**经典随机数或量子纠缠；在时间窗口 $\Delta t$ 内，若 $\Delta t<L/c$ 则**不存在**任何跨区通信（无超信号性）。

定义"首次可检互信息时间"
$$
T_\delta(L):=\inf\Bigl\{\Delta t\ge0:\ \exists\ \text{协议使}\ I(X;Y_{\Delta t})\ge\delta\Bigr\},\qquad
\boxed{\ c_{\mathrm{info}}:=\limsup_{\delta\downarrow0}\ \sup_{L>0}\frac{L}{T_\delta(L)}\ }.
$$

**定理 7.1（信息光锥）**：在假设 7.0 下，有 $c_{\mathrm{info}}=c$。

**证明**：

**上界**：由无超信号性与微因果，$\Delta t<L/c$ 时，接收端观测 $Y_{\Delta t}$ 不能携带发送端输入 $X$ 的信息，故 $I(X;Y_{\Delta t})=0$，从而 $\sup_{L} L/T_\delta(L)\le c\ \forall\delta>0\Rightarrow \limsup_{\delta\downarrow0}\le c$。

**下界**：真空链路上第 3–5 节给出 $\mathsf T=L/c$。设接收端做能量或相干阈值检验（考虑信道+探测器总噪声），则当 $\Delta t=L/c+\varepsilon$ 且满足宽带—门限准则时，窗口积累的信噪随带宽/时间线性增长，存在阈值 $\delta(\varepsilon)\downarrow0$ 使 $I\ge\delta(\varepsilon)$。Dorrah–Mojahedi 用"可检测信息速度"以 SNR 阈值在总噪声模型下形式化了该事实。对任意 $\varepsilon>0$ 存在 $\delta(\varepsilon)\downarrow0$ 使 $\sup_{L}\frac{L}{T_{\delta(\varepsilon)}(L)}\ge c-\varepsilon\Rightarrow \liminf_{\delta\downarrow0}\ge c$。

**收束**：由上界与构造性下界并用，$\limsup_{\delta\downarrow0}=\liminf_{\delta\downarrow0}=c$ 因而极限存在且等于 $c$，即 $c_{\mathrm{info}}=c$。—证毕。([APS链接][5])

> 注：量子场论视角下，"无超信号性 $\Rightarrow$ 微因果"的当代证明为上界提供了独立逻辑支撑。([arXiv][11])

---

## 8. NPE 误差账本（非渐近上界与证明）

令**理论（连续）聚合量**
$$
\mathsf T:=\frac{\hbar}{2\pi}\!\int_{\mathbb R} w_R(E)\,[h\!\star\!\operatorname{tr}Q](E)\,dE.
$$

令 $g(E):=w_R(E)\,[h\!\star\!\operatorname{tr}Q](E)$，取等距能量网格 $E_n=a+n\,\Delta E$（$n=0,\dots,N$，$b=a+N\,\Delta E$）。定义**梯形法**的离散估计量
$$
\mathrm{Obs}:=\frac{\hbar}{2\pi}\,\Delta E\left[\frac{g(E_0)+g(E_N)}{2}+\sum_{n=1}^{N-1} g(E_n)\right],
$$
与连续量 $\displaystyle \mathsf T=\frac{\hbar}{2\pi}\int_{a}^{b}\!g(E)\,dE$ 对应。其偏差由 $\varepsilon_{\text{alias}}$、$\varepsilon_{\text{EM}}$ 与 $\varepsilon_{\text{tail}}$ 构成，详见下文。

由有限采样与有限带宽/阶数，
$$
\mathrm{Obs}=\mathsf T+\varepsilon_{\text{alias}}+\varepsilon_{\text{EM}}+\varepsilon_{\text{tail}}
=\frac{L}{c}+\varepsilon_{\text{alias}}+\varepsilon_{\text{EM}}+\varepsilon_{\text{tail}},
$$
其中第二个等号在真空链路下由 $\mathsf T=L/c$（见 §3–§4）给出。

### 8.1 Nyquist 与 Poisson（变量与单位已显式化）

设能量域 Fourier 对为
$$
\widehat f(\tau):=\int_{\mathbb R} f(E)\,e^{-i\tau E}\,dE,\qquad [\tau]=\mathrm{J}^{-1}.
$$

则对任意步长 $\Delta E>0$ 与偏移 $a\in\mathbb R$，Poisson 求和为
$$
\boxed{\
\sum_{n\in\mathbb Z} f\!\bigl(a+n\,\Delta E\bigr)
=\frac{1}{\Delta E}\sum_{k\in\mathbb Z}
\widehat f\!\Bigl(\frac{2\pi k}{\Delta E}\Bigr)\,
e^{\,i\,\frac{2\pi k a}{\Delta E}}
\ }.
$$

**无混叠（alias-free）充要条件**：若 $\widehat f(\tau)=0$ 当 $|\tau|\ge \pi/\Delta E$，则所有 $k\neq 0$ 项为零，别名项消失。

**别名误差上界（非严格带限时；针对梯形估计量）**：
$$
\boxed{\
\bigl|\varepsilon_{\mathrm{alias}}^{\text{trap}}\bigr|
\le \sum_{k\neq 0}
\left|\widehat f\!\Bigl(\frac{2\pi k}{\Delta E}\Bigr)\right|
\ }.
$$
此处把 Poisson 周期化后的 $\Delta E\sum f$ 与 $\int f$ 之差写为 $k\neq0$ 频谱重复的和；有限区间的端点/权重误差由 §8.2 的 EM 上界单独计入，不在此项重复记账。

与频率域的**等价换元**：令 $\omega:=E/\hbar,\ \Delta\omega:=\Delta E/\hbar,\ g(\omega):=f(\hbar\omega),\ \widehat g(t):=\!\int g(\omega)e^{-i\omega t}d\omega$（此时 $t=\hbar\tau$），则
$$
\sum_{n} g\!\bigl(\omega_0+n\,\Delta\omega\bigr)
=\frac{1}{\Delta\omega}\sum_{k\in\mathbb Z}\widehat g\!\bigl(k\,T_s\bigr)\,
e^{\,i\,k\,T_s\,\omega_0},\qquad T_s:=\frac{2\pi}{\Delta\omega}\ \text{（时间采样周期）}.
$$

**无混叠条件**在 $(\omega,t)$ 变量下等价为
$$
\boxed{\ T_s>2\,t_{\max}\ \Longleftrightarrow\ \Delta\omega<\frac{\pi}{t_{\max}}\ },
$$
其中 $t_{\max}$ 为 $\widehat g(t)$ 的支持上界；在能量域对应为
$$
\boxed{\ \Delta E<\frac{\pi\,\hbar}{t_{\max}}\ }.
$$

在本文应用中可取 $f(E)=w_R(E)\,[h\!\star\!\operatorname{tr}Q](E)$。上述单位与变量的显式化保证 §4 与 §8 的 NPE 误差账本在**能量采样**与**频率采样**两种实现之间严格一致、可检且无歧义。—证毕。([math.columbia.edu][12])

### 8.2 Euler–Maclaurin（端点与尾项）

对光滑 $g$ 与整数 $m\ge1$，**步长 $\Delta E$** 的 Euler–Maclaurin 给出
$$
\sum_{n=0}^{N} g(E_n)=\frac{1}{\Delta E}\int_{a}^{b}\!g(x)\,dx+\frac{g(a)+g(b)}{2}
+\sum_{k=1}^{m}\frac{B_{2k}}{(2k)!}\,(\Delta E)^{2k-1}\!\Bigl(g^{(2k-1)}(b)-g^{(2k-1)}(a)\Bigr)+R_{2m},
$$
其中 $E_n=a+n\,\Delta E,\ N=(b-a)/\Delta E$。余项满足可用上界
$$
\bigl|R_{2m}\bigr|
\ \le\ \frac{2\,\zeta(2m)}{(2\pi)^{2m}}\,(\Delta E)^{2m-1}
\int_{a}^{b}\!\bigl|g^{(2m)}(x)\bigr|\,dx
\ \le\ \frac{2\,\zeta(2m)}{(2\pi)^{2m}}\,(\Delta E)^{2m-1}(b-a)\,
\sup_{x\in[a,b]}\bigl|g^{(2m)}(x)\bigr|.
$$
**针对梯形积分的误差阶**：将上式两边乘以 $\Delta E$ 并整理得
$$
\underbrace{\Delta E\left[\frac{g(a)+g(b)}{2}+\sum_{n=1}^{N-1} g(E_n)\right]}_{\text{梯形法}}
=\int_a^b g(x)\,dx
+\sum_{k=1}^{m}\frac{B_{2k}}{(2k)!}\,(\Delta E)^{2k}\!\Bigl[g^{(2k-1)}(b)-g^{(2k-1)}(a)\Bigr]
+\Delta E\,R_{2m}.
$$
由 $|R_{2m}|\le \dfrac{2\zeta(2m)}{(2\pi)^{2m}}(\Delta E)^{2m-1}\!\int_a^b |g^{(2m)}|$，得到
$$
\bigl|\mathrm{Obs}-\mathsf T\bigr|
\le \frac{\hbar}{2\pi}\left[
\sum_{k=1}^{m}\frac{|B_{2k}|}{(2k)!}\,(\Delta E)^{2k}\cdot\bigl|g^{(2k-1)}(b)-g^{(2k-1)}(a)\bigr|
+\frac{2\zeta(2m)}{(2\pi)^{2m}}\,(\Delta E)^{2m}\!\int_a^b |g^{(2m)}(x)|\,dx
\right].
$$
因此在**固定带宽**下，端点/尾项误差随 $m\uparrow$ 或 $\Delta E\downarrow$ 按 **$(\Delta E)^{2m}$** 收敛（$m=1$ 时即 $O((\Delta E)^2)$）。取 $g=w_R\,[h\!\star\!\operatorname{tr}Q]$ 即得 $\varepsilon_{\text{EM}}$ 的显式上界。—证毕。([carmamaths.org][7])

### 8.3 尾项（有限带宽截断）

若 $w_R$ 的频域窗在带外具有至多代数/指数衰减，$h\!\star\!\operatorname{tr}Q$ 连续且有界，则
$$
\bigl|\varepsilon_{\text{tail}}\bigr|\le |h\!\star\!\operatorname{tr}Q|_\infty\cdot \int_{|E|>\Omega_R} |w_R(E)|\,dE\to0
$$
（$\Omega_R\!\uparrow$）。—证毕。

---

## 9. 工程实现：以延迟计长 & 与 SI 交叉校准（规约与可检性）

**规约**：

(i) 选几何已知的真空链路 $L$；(ii) 宽带激励，测得 $\hat\tau=\mathsf T[w_R,h;L]$；(iii) 计算 $\hat c=L/\hat\tau$，并随带宽验证"别名=0、端点/尾项收敛"；(iv) 以铯频率链与干涉计长度链交叉校准，闭环至 SI "以时定长"的 **Mise en pratique**。([BIPM][2])

**介质与"快光"注意**：群速异常不影响信息/前沿速度上界；检测阈值下的信息速度 $\le c$ 的理论与实验证据详见文献。([PubMed][10])

---

## 10. 结论定理（四等价与唯一性）

**定理 10.1**：光速常数 $c$ 可由窗口化群延迟表述**唯一**刻画；且与

$(\mathrm A)$ 相位斜率/谱移密度、$(\mathrm B)$ 因果前沿、$(\mathrm C)$ 信息光锥（在假设 7.0 下）、$(\mathrm D)$ SI 实现

**两两等价**。—证毕（综上第 3–9 节）。

---

## 11. 多端口一般化与离散实现（RCA 光锥）

### 11.1 多端口一般化与基线校准条件

若 $S(E)\in\mathrm U(N)$，令"平均延迟"$\ \bar\tau(E):=\hbar\,\frac{1}{N}\operatorname{tr}Q(E)$。**对无耦合且各通道等长的 $N$ 端口真空链路，有 $S(E)=e^{iEL/(\hbar c)}I_N$，从而 $Q(E)=\frac{L}{\hbar c}I_N$**，各本征延迟皆为 $L/c$，故 $\bar\tau(E)=L/c$。

**多端口分解与恢复条件**：令 $S(E)\in \mathrm U(N)$ 表示 $N$ 端口散射矩阵，作分解
$$
S(E)=e^{\,i E L/(\hbar c)}\,U(E),\qquad U(E)\in \mathrm U(N).
$$
则 Wigner–Smith 算子 $Q(E)=-i\,S^\dagger(E)S'(E)$ 的迹满足
$$
\operatorname{tr}Q(E)=\frac{N L}{\hbar c}-i\,\operatorname{tr}\!\bigl(U^\dagger(E)\,U'(E)\bigr),\qquad
\bar{\tau}(E)=\frac{L}{c}-\frac{i\hbar}{N}\operatorname{tr}\!\bigl(U^\dagger(E)\,U'(E)\bigr).
$$

**基线校准**：若存在参考链路使 $\operatorname{tr}(U^\dagger U')$ 在被测与参考两链路间相同（或可精确建模并扣除），则窗口化平均恢复 $\bar{\tau}=L/c$。对于单一 S-参数 $S_{mn}$，仅在"直达真空通道、无额外色散耦合且端口等长"的条件下有 $\hbar\,\partial_E\arg S_{mn}=L/c$；否则亦需按上法相消/校准（参见第 9 节）。—证毕。([APS链接][1])

### 11.2 离散等价（RCA 光锥与 CHL）

半径 $r$ 的一维可逆元胞自动机（RCA）中，$t$ 步后每个元胞仅受初态 $\pm r t$ 邻域影响（归纳法可证），形成**离散光锥**，取栅距 $a$、步长 $\Delta t$ 得离散"光速" $c_{\mathrm{disc}}=r\,a/\Delta t$。CHL 定理刻画"连续＋移位共变"的滑动块码与 CA 的等价性。进一步，若该滑动块码为**双射**且其逆亦为滑动块码，则得到**可逆** CA，从而在离散因果结构下实现可逆的传播光锥。—证毕。([维基百科][13])

---

## 12. 与相对论/场论的相容性（要点证明）

* **洛伦兹协变**：标量波动方程与 Maxwell 方程的推迟格林函数支撑均在 $t=r/c$（第 6.2 节），保证"光锥前沿= $c$" 与协变性一致。—证毕。([solar.physics.montana.edu][9])
* **微因果**：Soulas 证明"无超信号性 $\Rightarrow$ 微因果"；结合 6.1–6.2，所得前沿与信息光锥一致。—证毕。([arXiv][11])

---

## 13. 补充证明细节

### 13.1 $Q$ 的物理量纲与真空常值

由 $Q=-iS^\dagger \tfrac{dS}{dE}$ 得 $[Q]=E^{-1}$，故 $\tau_{\mathrm{WS}}=\hbar\,\operatorname{tr}Q$ 具时间量纲。真空链路 $S_L(E)=e^{i E L/(\hbar c)}\Rightarrow \operatorname{tr}Q_L=L/(\hbar c)$ 为常值，保证 $\mathsf T=L/c$。—证毕。([APS链接][1])

### 13.2 KK—因果的严格化（记号统一）

与 §1.1 的能量域核 $h(E)$ 区分，本节统一使用 $\kappa(t)$ 表示**时域脉冲响应**，$K(z)$ 表示其频率响应。给定 $\kappa\in L^{2}(\mathbb R)$ 且 $\operatorname{supp}\kappa\subset[0,\infty)$，则 $K(z)$ 为上半平面全纯函数，边界值 $K(\omega)$ 的实部与虚部由 Hilbert 变换互定，即 KK 关系；反向由 Paley–Wiener–Titchmarsh 定理推出 $\kappa(t)=0$（$t<0$）。—证毕。([APS链接][4])

### 13.3 光锥支撑的直接校验（自由空间）

对**标量**波动方程，在**自由空间（真空、均匀、无界、无耗散）**下，将 $G_{\mathrm{ret}}(t,\mathbf r)=\delta(t-r/c)/(4\pi r)$ 代入波算符 $(\frac{1}{c^2}\partial_t^2-\nabla^2)$ 的分布意义计算，可得 $(\frac{1}{c^2}\partial_t^2-\nabla^2)G_{\mathrm{ret}}=\delta(t)\delta(\mathbf r)$；支撑仅在 $t=r/c$。对 **Maxwell** 方程，在同样条件下，其 dyadic 格林函数为**分布级**的 $\delta$ 及其导数在光锥上的组合，**支撑同样仅在光锥上**，故前沿速度结论相同。在色散/耗散或有边界介质中此结论不成立。—证毕。([solar.physics.montana.edu][9]; [ETH Zürich][15])

### 13.4 信息阈值与误差指数

对二元假设检验（存在/不存在微弱信号），在独立样本数随观测时间/带宽线性增长时，最优误差指数为 KL 散度（Chernoff–Stein）；Dorrah–Mojahedi 在含总噪声模型下跟踪"可检测信息速度"，与本表述一致。—证毕。([APS链接][5])

---

## 14. 最终陈述

以"窗口化群延迟"表述之 $c$，在真空链路上给出 $L/\mathsf T$ 的唯一值；该值与**相位斜率/谱移密度**、**因果前沿**与**信息光锥**三线并证，且与 **SI** 的固定数值完全一致。工程上，NPE 误差账本提供非渐近、可操作的精度控制与校准路径。([BIPM][2])

---

## 参考文献

**1.** F. T. Smith, "Lifetime Matrix in Collision Theory," *Phys. Rev.* **118** (1960) 349–356。
**2.** BIPM，《SI 手册》（第九版，v3.02）。
**3.** A. Pushnitski, "The Birman–Krein formula," *arXiv:1006.0639*（2010）。
**4.** J. S. Toll, "Causality and the Dispersion Relation: Logical Foundations," *Phys. Rev.* **104** (1956) 1760–1770。
**5.** A. H. Dorrah, M. Mojahedi, "Velocity of detectable information in faster-than-light pulses," *Phys. Rev. A* **90** (2014) 033822。
**6.** C. E. Shannon, "Communication in the Presence of Noise," *Proc. IRE* **37** (1949) 10–21。（脚注链接为教学版 PDF）
**7.** D. H. Bailey, J. M. Borwein, "Effective Error Bounds in Euler–Maclaurin-Based Quadrature Schemes"（2005/2006）。
**8.** D. Borthwick, *Scattering by Obstacles*（arXiv:2110.06370，2022 版）。
**9.** *PH519 Lecture Notes*, "The Wave Equation Green's Function"（2020，教学讲义 PDF）。
**10.** M. D. Stenner, D. J. Gauthier, M. A. Neifeld, "The speed of information in a 'fast-light' optical medium," *Nature* **425** (2003) 695–698。
**11.** A. Soulas, "No-signalling implies microcausality in QFT," *arXiv:2309.07715*（2025 版）。
**12.** P. Woit, "Notes on the Poisson Summation Formula"（2020，讲义）。
**13.** Curtis–Hedlund–Lyndon theorem（CHL 定理）条目与综述（维基）。
**14.** BIPM，"SI 基本单位：米（metre）"页面。
**15.** ETH Zürich, "Radiation" lecture notes, Ch. 6（时域 dyadic 格林函数）。

---

### 附：关键出处与段落对应（选摘）

* SI "以时定长"与固定 $c$ 的表述与数值：BIPM 官方页面与 SI 手册。([BIPM][14])
* Wigner–Smith 定义与跨域应用：Smith 1960；JASA 近作（声学版）。([APS链接][1])
* Birman–Kreĭn 与 $\det S$ 的谱移表述与导数关系：Pushnitski（2010）；Borthwick（2021/2022）。([arXiv][3])
* KK—因果等价：Toll 1956。([APS链接][4])
* 3D 推迟格林函数的光锥支撑：标量波动方程讲义；Maxwell dyadic 格林函数。([solar.physics.montana.edu][9]; [ETH Zürich][15])
* 快/慢光与信息速度：Stenner–Gauthier–Neifeld（2003）；Dorrah–Mojahedi（2014）；前驱分析（2012）。([PubMed][10])
* NPE 误差账本的三支：Shannon（Nyquist）、Poisson（Woit 讲义）、EM（Bailey–Borwein）。([fab.cba.mit.edu][6])
* CHL 定理与离散光锥：维基条目与 CA 专著。([维基百科][13])

（全文完）

---

[1]: https://link.aps.org/doi/10.1103/PhysRev.118.349?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory | Phys. Rev."
[2]: https://www.bipm.org/documents/20126/41483022/SI-Brochure-9-EN.pdf?utm_source=chatgpt.com "SI Brochure - 9th ed./version 3.02"
[3]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[4]: https://link.aps.org/doi/10.1103/PhysRev.104.1760?utm_source=chatgpt.com "Causality and the Dispersion Relation: Logical Foundations"
[5]: https://link.aps.org/doi/10.1103/PhysRevA.90.033822?utm_source=chatgpt.com "Velocity of detectable information in faster-than-light pulses"
[6]: https://fab.cba.mit.edu/classes/S62.12/docs/Shannon_noise.pdf?utm_source=chatgpt.com "Communication in the Presence of Noise*"
[7]: https://carmamaths.org/resources/jon/em.pdf?utm_source=chatgpt.com "Effective Error Bounds in Euler-Maclaurin-Based Quadrature ..."
[8]: https://arxiv.org/pdf/2110.06370?utm_source=chatgpt.com "arXiv:2110.06370v3 [math.SP] 15 Aug 2022"
[9]: https://solar.physics.montana.edu/dana/ph519/rad_GF.pdf?utm_source=chatgpt.com "The Wave Equation Green's Function (DWL 4/22/20)"
[10]: https://pubmed.ncbi.nlm.nih.gov/14562097/?utm_source=chatgpt.com "The speed of information in a 'fast-light' optical medium"
[11]: https://arxiv.org/pdf/2309.07715?utm_source=chatgpt.com "A proof that no-signalling implies microcausality in ..."
[12]: https://www.math.columbia.edu/~woit/fourier-analysis/theta-zeta.pdf?utm_source=chatgpt.com "Notes on the Poisson Summation Formula, Theta Functions ..."
[13]: https://en.wikipedia.org/wiki/Curtis%E2%80%93Hedlund%E2%80%93Lyndon_theorem?utm_source=chatgpt.com "Curtis–Hedlund–Lyndon theorem"
[14]: https://www.bipm.org/en/si-base-units/metre?utm_source=chatgpt.com "SI base unit: metre (m)"
[15]: https://ethz.ch/content/dam/ethz/special-interest/itet/photonics-dam/documents/lectures/EandM/Radiation.pdf?utm_source=chatgpt.com "Chapter 6 Radiation - ETH Zürich"
