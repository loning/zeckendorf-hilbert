# S26. 相位密度与稳定性：de Branges–Mellin 框架下的采样—插值—帧障碍

**—— 相位导数测度、Landau 型必要/充分准则、Balian–Low 类不可能性与小扰动稳定**

## 摘要（定性）

在 de Branges–Mellin 框架中，以相位导数 $\varphi'(x)$ 诱导的"相位密度"作为几何刻度，建立采样与插值序列的必要—充分密度准则；证明对由相位网格作小相位扰动得到的序列存在 Riesz 基/框架的稳定半径；在 Weyl–Heisenberg（Mellin）单窗矩形格情形，结合密度定理（**仅在临界密度 $\alpha\beta=1$ 时**帧必为 Riesz 基）与 Balian–Low 定理（临界密度下紧局域窗不可能生成 Riesz 基/正交基），给出紧局域性的障碍。上述结论在"有限阶" Euler–Maclaurin（EM）与 Nyquist–Poisson–EM 三分解纪律下保持工作条带内的奇性集合不增与极阶不升，并与窗/核最优化的带限投影—卷积结构协同。全文定性陈述，避免对数值常数的最优化诉求。

---

## 0. 设定与相位密度

**前提（统一声明）**：令 $E\in HB$ 且**在实轴无零点**，$\varphi$ 为其相位（随 $x\in\mathbb R$ 单调且实解析）。则**几乎处处**

$$
E(x)=|E(x)|\,e^{-i\varphi(x)},\qquad
E^\sharp(z):=\overline{E(\bar z)}.
$$

记

$$
U(x):=\frac{E^\sharp(x)}{E(x)}=e^{2i\varphi(x)}\ \ \text{(a.e. }x\in\mathbb R),\qquad
\Theta(z):=\frac{E^\sharp(z)}{E(z)}\ \ \text{（上半平面内函数，实轴边界值 a.e. 为 }U\text{）}.
$$

再生核对角恒等式（后文"相位密度刻度"与迹恒等的唯一锚点）：

$$
\boxed{K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2>0\ \ \text{(a.e.)}}
$$

其中 $K$ 为 $\mathcal H(E)$ 的再生核。本文仅依赖上述 de Branges 核对角公式，并据此定义参考密度 $\rho(x):=\varphi'(x)/\pi$。归一化再生核 $\kappa_x:=K(\cdot,x)/\sqrt{K(x,x)}$ 满足

$$
\boxed{\langle \kappa_x,\kappa_y\rangle=\frac{\sin(\varphi(x)-\varphi(y))}{(x-y)\sqrt{\varphi'(x)\varphi'(y)}}\ \ (x\neq y),\quad \langle \kappa_x,\kappa_x\rangle=1}
$$

上式及相位函数的用法见 Marzo–Nitzan–Olsen (J. Anal. Math. **117** (2012) 365–395)；核对角公式 $K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)$ 与归一化核的内积公式亦可见 Antezana–Marzo–Olsen (Int. Math. Res. Not. IMRN **2016** (16) 5117–5144; arXiv:1504.01769)。**本文所有结论仅依赖恒等成立的核—相位公式**

$$
K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2>0,
$$

因而**不依赖**对 $\Im m$ 的规范化选择。

**相位密度测度与 Beurling 密度.** 本文核心刻度为 de Branges 核对角恒等式

$$
K(x,x)=\frac{1}{\pi}\varphi'(x)|E(x)|^2>0\ \ \text{(a.e.)}
$$

与由此诱导的相位测度 $\varphi'(x)\,dx$。定义**参考密度（相位密度）** $\rho(x):=\varphi'(x)/\pi$。**关于与 Weyl–Titchmarsh $m$-函数的对齐**：在与 canonical system 匹配的规范下，可对齐 $\Im m(x+i0)=\pi\rho(x)$ 且 $\rho=\varphi'/\pi$；但**本文后续结论仅依赖核—相位恒等式 $K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)$ 本身，不依赖于 $\Im m$ 的具体规范化与 $m$ 函数/谱密度的对齐**（参见 Eckhardt 2024 与 Romanov–Eckhardt–Kostenko 等对 canonical system 规范化的讨论）。

对区间 $I\subset\mathbb R$，定义**相位测度**累计量（注意：$\Phi$ 为大写，与相位函数 $\varphi$（小写）区分）

$$
\Phi(I):=\int_I \varphi'(x)\,dx,
$$

并对离散序列 $\Lambda=\{x_n\}\subset\mathbb R$ 定义

$$
D_\varphi^-(\Lambda):=\liminf_{R\to\infty}\ \inf_{x_0\in\mathbb R}\
\frac{\#\big(\Lambda\cap[x_0-R,x_0+R]\big)}{\Phi([x_0-R,x_0+R])/\pi},
$$

$$
D_\varphi^+(\Lambda):=\limsup_{R\to\infty}\ \sup_{x_0\in\mathbb R}\
\frac{\#\big(\Lambda\cap[x_0-R,x_0+R]\big)}{\Phi([x_0-R,x_0+R])/\pi}.
$$

当 $\varphi'\equiv T$（Paley–Wiener 情形）时，$D_\varphi^\pm$ 退化为经典 Beurling 密度与带宽 $T$ 的比值，从而与 Landau 密度阈值一致。

**窗与迹前提.** 取 $w_R\ge0$ 有界且紧支撑（或 $w_R\in L^1(\varphi'(x)\,dx)$），由于

$$
\int_{\mathbb R} w_R(x)\,\frac{K(x,x)}{|E(x)|^{2}}\,dx
=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx<\infty,
$$

故压缩乘子 $P_{\mathcal H(E)}M_{w_R}P_{\mathcal H(E)}$ 为正且迹类，并有

$$
\operatorname{Tr}\big(M_{w_R}\big|_{\mathcal H(E)}\big)
=\int_{\mathbb R} w_R(x)\,\frac{K(x,x)}{|E(x)|^{2}}\,dx
=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx.
$$

在窗化/加权截断后，误差分量分解为：（i）本征带限主项，（ii）泊松求和产生的混叠项（**Nyquist 条件—实现策略说明**：本文取 Fourier 规范 $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$；在此规范下，带限 $\Omega$ 的 Nyquist 阈值为 $\Delta\le\pi/\Omega$（端点在强零假设下可取等号）。例如在 Paley–Wiener 空间 $PW_T$ 中（带宽为 $T$，频带 $[-T,T]$），临界采样步长为 $\pi/T$；在相位坐标下混叠频带不交叠时混叠项为零。若用 $e^{2\pi i\beta t}$ 归一，则阈值写作 $\alpha\beta=1$；此处为窗化—泊松—EM 的实现策略说明，不参与定理的必要前提），（iii）边界/余项（用**有限阶** Euler–Maclaurin 控制，仅取到 $2N$ 阶导数的余项型估计，见 NIST DLMF §2.10(i)，参式 2.10.20 及相关条目；Poisson 求和见 DLMF §1.8(iv)，参式 1.8.14–1.8.16）。

*术语说明（Nyquist–Poisson–EM 三分解）.* 本文所用"Nyquist–Poisson–EM 三分解"仅作为**换序组织**：主项=带限投影项；混叠项=Poisson 求和项（在理想带限且采样间隔满足 Nyquist 阈值 $\Delta\le\pi/\Omega$ 时为 0，其中 $\Omega$ 为带宽）；余项=有限阶 Euler–Maclaurin 边界校正。本文仅把它作为记叙性划分，不增加任何新的分析假设。

*适用性注解.* 下述有限阶 EM 与 Poisson–EM 分解仅用于估计窗化截断误差；我们不引入全局型整函数阶次最优化，且只在需要时假定被积对象具有限个可控导数。

在所用窗 $w_R$ 满足（紧支或指数衰减、偶、$|w_R|_\infty\le C$）且仅作**有限阶** EM 与 Nyquist–Poisson–EM 换序时，换序所致误差层为整/全纯，**因此在工作条带内不引入新奇点且极阶不升**。

**结构性假设（全篇默认前提）.** 默认 $\varphi'(x)\,dx$ 为 **（局部）doubling** 测度（满足 MNO 要求的 doubling 条件），即

$$
\exists C\ge1,\ \forall I,\ \int_{2I}\varphi'(x)\,dx\le C\int_I\varphi'(x)\,dx.
$$

**在本文设定下，该假设蕴含**对应模型空间 $K_\Theta$ 由 **one-component（一分量）** 内函数生成（Marzo–Nitzan–Olsen 2012）；**本假设仅用于 §1–§2 的 Landau 型密度判据**，据此可套用 Marzo–Nitzan–Olsen (2012) 的采样/插值密度刻画。**§3 的 Clark 基纯原子性对亚纯内函数恒成立，不需该假设；"至多一个例外角"对应正交核基性质，而非测度性质。相关命题处将回引本前提。**

*说明.* 我们仅用到"$\varphi'(x)\,dx$ 为（局部）doubling $\Rightarrow$ 模型空间 one-component"这一**充分条件**并据此调用 Marzo–Nitzan–Olsen (2012) 的密度结论；更细的等价刻画需附加额外结构假设，**本文不主张其双向充要性**。

**规范锚点（全文统一）**：

- **规范提示（重要）**：**本文核心结论仅依赖核—相位恒等式 $K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)$，不依赖与 $m$-函数/谱密度的对齐。** *如需引入谱密度/ $m$ 函数*，在**trace-normalized** Hamiltonian 规范下有 $\Im m(x+i0)=\pi\,\rho(x)$ 与 $\rho=\varphi'/\pi$；本篇主定理不以此为假设。
- **内函数与相位网格**：$\Theta=\dfrac{E^\sharp}{E}=e^{2i\varphi}$（a.e.），$X_\theta=\{x:\Theta(x)=e^{2i\theta}\}=\{x:\varphi(x)=\theta+\pi n\}$（**相位步长 = $\pi$**）。
- **核对角**：$K(x,x)=\dfrac{|E(x)|^2}{\pi}\varphi'(x)>0$（a.e.）。
- **相位尺度与密度**：$\Phi(I)=\int_I\varphi'(x)\,dx$，$D_\varphi^\pm(\Lambda)=\lim_{R\to\infty} \frac{\#(\Lambda\cap I)}{\Phi(I)/\pi}$。
- **窗口与迹**（充分条件）：$w_R\ge0$ 有界且紧支撑（或 $w_R\in L^1(\varphi'\,dx)$）$\Rightarrow$ $M_{w_R}|_{\mathcal H(E)}$ 为正且迹类，$\operatorname{Tr}(M_{w_R})=\frac{1}{\pi}\int w_R\,\varphi'$。
- **标准数值测度**：令 $d\nu(x):=\frac{K(x,x)}{|E(x)|^2}\,dx=\frac{\varphi'(x)}{\pi}\,dx$。

---

## 1. 采样与相位密度：Landau 型必要条件

记标准化再生核 $\kappa_x:=K(\cdot,x)/\sqrt{K(x,x)}$。称 $\Lambda$ 为**采样序列**，若存在常数 $A,B>0$ 使

$$
A\,\|F\|_{\mathcal H(E)}^2\ \le\ \sum_{x_n\in\Lambda}\frac{|F(x_n)|^2}{K(x_n,x_n)}\ \le\ B\,\|F\|_{\mathcal H(E)}^2,
\qquad \forall\,F\in\mathcal H(E).
$$

**统一窗化假设（本节及后续全文）**：以下均取 $w_R\in L^\infty\cap L^1(\varphi'(x)\,dx)$，紧支撑或指数衰减，且 $\|w_R\|_\infty\le 1$；从而

$$
\int_{\mathbb R}w_R(x)\,\frac{K(x,x)}{|E(x)|^{2}}\,dx=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx<\infty,
$$

保证 $M_{w_R}|_{\mathcal H(E)}$ 为正算子且具有有限迹。此处 $M_{w_R}$ 记乘子在 $\mathcal H(E)$ 上的压缩（Toeplitz）算子 $P_{\mathcal H(E)}M_{w_R}P_{\mathcal H(E)}$。此后不再重复上述假设。

### 引理 1.1（窗化迹恒等）

设 $w_R\ge0$ 且 $w_R\in L^1(\varphi'(x)\,dx)\cap L^\infty$。则压缩乘子 $M_{w_R}$ 在 $\mathcal H(E)$ 上为正且迹类，且

$$
\operatorname{Tr}\!\left(M_{w_R}\big|_{\mathcal H(E)}\right)
=\int_{\mathbb R} w_R(x)\,\frac{K(x,x)}{|E(x)|^{2}}\,dx
=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx.
$$

上式第一个等号直接来自再生核恒等式 $\sum_n|e_n(x)|^2=K(x,x)$，第二个等号用核对角公式 $K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)$ 代换。

*注记（易检充分条件）.* 作为便利性检查，若另知 $\sup_{x\in\operatorname{supp}w_R}\frac{K(x,x)}{|E(x)|^2}<\infty$，亦可直接验证迹类性；但在上述条件下该界自动有限。

*证明.* 取 $w_R\in L^1(\varphi'dx)\cap L^\infty$ 并由正性单调逼近 $C_c$ 情形，可由 $\sum_n\langle M_{w_R}e_n,e_n\rangle=\int w_R K/|E|^{2}dx$ 得到迹类与迹值的充要性。在上述条件下（$w_R\ge0$，$w_R\in L^1\cap L^\infty$，核满足标准 de Branges 界），$M_{w_R}$ 为迹类。取任一正交基 $\{e_n\}$，记其有限截断族 $\{e_1,\ldots,e_N\}$ 的秩—$N$ 投影为 $\Pi_N$，则 $\Pi_N\uparrow I$（SOT）。由 $M_{w_R}\ge0$ 且 $M_{w_R}$ 迹类，得 $M_{w_R}^{1/2}\Pi_N M_{w_R}^{1/2}\uparrow M_{w_R}$ 为**非降**迹类序列；据**单调收敛定理**与 $\|M_{w_R}\|$ 的**主控**，可逐项取迹并与求和交换。由 $\langle f,g\rangle_{\mathcal H(E)}=\int f\bar g\,|E|^{-2}dx$ 和再生核恒等式 $\sum_n |e_n(x)|^2=K(x,x)$ 得
$$
\operatorname{Tr}(M_{w_R})=\sum_n\langle M_{w_R}e_n,e_n\rangle=\int w_R \sum_n|e_n|^2 |E|^{-2}dx=\int w_R K(x,x)|E|^{-2}dx,
$$
再用 $K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)$ 即得。$\square$

**注记（Berezin 变换与迹公式）.** 对任意有界乘子 $M_{w}$，函数 $\widetilde w(x):=\langle M_{w}\kappa_x,\kappa_x\rangle$ 为 $w$ 的 Berezin 变换；一般有 $\widetilde w(x)\neq w(x)$。本文所用的迹恒等式与密度估计仅涉及 Berezin 符号 $\widetilde w$ 在 $\Lambda$ 上的求和，作为对 $w$ 的积分的近似，无需 $\widetilde w\equiv w$。具体而言：压缩乘子 $M_{w_R}$ 的迹
$$
\operatorname{Tr}(M_{w_R})=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx
$$
仅依赖于原窗函数 $w_R$，而密度估计中出现的求和 $\sum_{x_n}\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle$ 涉及 Berezin 变换值 $\widetilde w_R(x_n)$；通过迹不等式与窗的平移—缩放即可将其转化为区间计数估计。注意 $\widetilde w\le\|w\|_\infty$。若 $M_w$ 为正迹类且以 $d\nu(x)=\frac{\varphi'(x)}{\pi}\,dx$ 计算（见 §0 规范锚点），则有
$$
\int_{\mathbb R}\widetilde w(x)\,d\nu(x)=\operatorname{Tr}(M_w);
$$
此等式仅用于迹与求和的比较，不要求 $\widetilde w\equiv w$。

下文所有"单位质量窗"均指相对于相位测度 $\varphi'(x)\,dx$ 归一：$\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx=1$，且 $\operatorname{diam}(\operatorname{supp}w_R)\asymp R$；此时 $\operatorname{Tr}(M_{w_R})=1$。

### 定理 1.2（采样的相位密度下界；前提：$\varphi'(x)\,dx$ 为（局部）doubling）

若 $\Lambda$ 为采样序列，则 $D_\varphi^-(\Lambda)\ge 1$，即采样序列的相位密度必须不低于相位测度的自然密度阈值。

*证明（修订版）.* 取 $w_R\ge0$ 为**相位测度** $\varphi'(x)\,dx$ 下的近单位族：$\frac{1}{\pi}\int_{\mathbb R} w_R\,\varphi'(x)\,dx=1$，支撑直径按 $\Phi$ 规模趋向无穷，且 $\|w_R\|_\infty\le1$。则压缩乘子 $M_{w_R}$ 在 $\mathcal H(E)$ 上为正且迹类，并有

$$
\operatorname{Tr}(M_{w_R}|_{\mathcal H(E)})=\frac{1}{\pi}\int_{\mathbb R} w_R\,\varphi'(x)\,dx=1.
$$

设 $T_\Lambda=\sum_{x_n}|\kappa_{x_n}\rangle\langle\kappa_{x_n}|$，采样下界等价于 $A I\le T_\Lambda$。于是

$$
\operatorname{Tr}(M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2})
\ge A\,\operatorname{Tr}(M_{w_R})
=\frac{A}{\pi}\int_{\mathbb R} w_R\,\varphi'(x)\,dx.
$$

另一方面

$$
\operatorname{Tr}(M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2})
=\sum_{x_n}\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle.
$$

*严格化换序说明.* 记 $\Lambda_R=\Lambda\cap I_R$ 为有限子集，令 $T_{\Lambda_R}=\sum_{x_n\in\Lambda_R}|\kappa_{x_n}\rangle\langle\kappa_{x_n}|$。由于 $M_{w_R}\ge0$ 且 $M_{w_R}\big|_{\mathcal H(E)}$ 为迹类，$\{T_{\Lambda_R}\}$ 单调递增并在强算子拓扑下 $T_{\Lambda_R}\uparrow T_\Lambda$。于是

$$
\operatorname{Tr}\!\left(M_{w_R}^{1/2}T_{\Lambda_R}M_{w_R}^{1/2}\right)
=\sum_{x_n\in\Lambda_R}\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle
\uparrow\ \operatorname{Tr}\!\left(M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2}\right),
$$

其中极限与求和次序可由单调收敛（正算子）或以帧上界作主导收敛控制。因 $\{\kappa_{x_n}\}$ 的 Bessel（采样上界）性质保证 $T_\Lambda$ 有界，而 $M_{w_R}$ 为正迹类，故积算子 $M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2}$ 为迹类，且可按标准 Berezin 变换论证逐项求迹。

**迹不等式转区间计数**：取**近似指标窗** $w_{R,I}$（使 $\frac{1}{\pi}\int w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$）作为区间 $I$ 的近似指标，则上述迹不等式给出序列计数的下界估计。此处把 $\sum\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle$ 与 $\#(\Lambda\cap I)$ 比较，需配合序列的 Bessel/Riesz 性与窗族的统一界控制。

*构造示例.* 可取 $w_{R,I}$ 为平滑顶帽（或 Fejér 型窗）：支撑在 $I$ 附近，$\operatorname{diam}(\operatorname{supp}w_{R,I})\asymp|I|$，并经归一化使 $\frac{1}{\pi}\int w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$。

这里仅**调用** MNO（2012）在"$\varphi'(x)\,dx$ 为 doubling"$\Rightarrow$"模型空间 one-component"之**充分性**以应用其 Landau 型密度判据，**不主张**该性质在我文设定下的双向等价。令 $R\to\infty$ 并对区间中心平移平均，在相位导数 $\varphi'(x)\,dx$ 为（局部）doubling 的假设下（回引 §0 结构性假设），配合引理 1.1 与 **Marzo–Nitzan–Olsen (2012)** 的 Landau 型密度定理（J. Anal. Math. **117** (2012) 365–395，Thm 1），得 $D_\varphi^-(\Lambda)\ge 1$。详细的误差控制与余项一致性估计见 MNO 原文。$\square$

---

## 2. Riesz 序列与相位密度：插值的上界

称 $\Lambda$ 为（标准化核）**Riesz 序列**，若 $\{\kappa_{x_n}\}_{x_n\in\Lambda}$ 在 $\mathcal H(E)$ 内为 Riesz 系列，即存在 $A',B'>0$ 使

$$
A'\sum |c_n|^2\ \le\ \left\|\sum c_n\,\kappa_{x_n}\right\|_{\mathcal H(E)}^2\ \le\ B'\sum |c_n|^2.
$$

记 $\Pi_\Lambda$ 为 $\operatorname{span}\{\kappa_{x_n}\}$ 的正交投影。

### 定理 2.1（插值的相位密度上界；前提：$\varphi'(x)\,dx$ 为（局部）doubling）

若 $\Lambda$ 为 Riesz 序列（因而为插值序列），则 $D_\varphi^+(\Lambda)\le 1$，即插值序列的相位密度必须不超过相位测度的自然密度阈值。

*证明（修订版）.* 取 $w_R\ge0$ 为**相位测度** $\varphi'(x)\,dx$ 下的近单位族：$\frac{1}{\pi}\int_{\mathbb R} w_R\,\varphi'(x)\,dx=1$，支撑直径按 $\Phi$ 规模趋向无穷，且 $\|w_R\|_\infty\le1$。Riesz 性给出 $A'\Pi_\Lambda\le T_\Lambda\le B'\Pi_\Lambda$。于是

$$
\sum_{x_n}\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle
=\operatorname{Tr}(M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2})
\le B'\,\operatorname{Tr}(M_{w_R}^{1/2}\Pi_\Lambda M_{w_R}^{1/2})
\le B'\,\operatorname{Tr}(M_{w_R}).
$$

*严格化换序说明.* 与定理 1.2 同理，记 $\Lambda_R=\Lambda\cap I_R$ 为有限子集，由 $M_{w_R}\ge0$ 的正性与 $T_{\Lambda_R}\uparrow T_\Lambda$ 的单调收敛性，配合 Riesz 序列的帧界控制，迹与求和互换可由单调收敛定理保证。因 $\{\kappa_{x_n}\}$ 的 Riesz 性质保证 $T_\Lambda$ 有界，而 $M_{w_R}$ 为正迹类，故积算子 $M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2}$ 为迹类，且可按标准 Berezin 变换论证逐项求迹。

**迹不等式转区间计数**：同定理 1.2，取**近似指标窗** $w_{R,I}$（使 $\frac{1}{\pi}\int w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$）作为区间 $I$ 的近似指标，则上述迹不等式给出序列计数的上界估计。此处把 $\sum\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle$ 与 $\#(\Lambda\cap I)$ 比较，需配合序列的 Bessel/Riesz 性与窗族的统一界控制。

*构造示例.* 同定理 1.2，可取 $w_{R,I}$ 为平滑顶帽（或 Fejér 型窗）：支撑在 $I$ 附近，$\operatorname{diam}(\operatorname{supp}w_{R,I})\asymp|I|$，并经归一化使 $\frac{1}{\pi}\int w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$。

这里仅**调用** MNO（2012）在"$\varphi'(x)\,dx$ 为 doubling"$\Rightarrow$"模型空间 one-component"之**充分性**以应用其 Landau 型密度判据，**不主张**该性质在我文设定下的双向等价。配合引理 1.1 与 **Marzo–Nitzan–Olsen (2012)** 的插值密度结论（J. Anal. Math. **117** (2012) 365–395，Thm 2），在相位导数 $\varphi'(x)\,dx$ 为（局部）doubling 的假设下，令 $R\to\infty$ 并对区间中心平移平均得 $D_\varphi^+(\Lambda)\le 1$。详细的误差控制与余项一致性估计见 MNO 原文。$\square$

---

## 3. 相位网格与 Clark 基：充分性模板

对任意 $\theta\in\mathbb R$，定义"相位网格"（**相位步长为 $\pi$**）

$$
\boxed{X_\theta:=\{x\in\mathbb R:\ U(x)=e^{2i\theta}\}=\{x:\ \varphi(x)=\theta+\pi n,\ n\in\mathbb Z\}.}
$$

**定理 3.1（Clark 基的相位密度刻画）.** 设 $\Theta=E^\sharp/E$ 为**亚纯内函数**。则：

（i）对**所有** $\alpha\in\mathbb T$，Clark 测度 $\sigma_\alpha$ 为**纯原子**（支撑为 $\{x:\Theta(x)=\alpha\}$ 的离散集）（Makarov–Poltoratski）；

（ii）对**除至多一个角** $\alpha=e^{2i\theta}\in\mathbb T$ 外，$\{k^\Theta_{x}\}_{\Theta(x)=\alpha}$ 构成 $K_\Theta$ 的**正交核基**（de Branges Thm.22；Antezana–Marzo–Olsen Lemma 1.2）。

经等距同构 $f\mapsto Ef:\ K_\Theta\to\mathcal H(E)$ 回到 $\mathcal H(E)$，得到相位网格 $X_\theta=\{x:\varphi(x)=\theta+\pi n,\ n\in\mathbb Z\}$（**相位步长 = $\pi$**）上的正交核基（除至多一个角外；若出现例外角需按 Theorem 22 判据另行核查），且

$$
D_\varphi^\pm(X_\theta)=1.
$$

**说明.** 在实轴上 $\Theta(x)=\dfrac{E^\sharp(x)}{E(x)}=e^{2i\varphi(x)}$（a.e.），故相位网格 $X_\theta=\{x:\varphi(x)=\theta+\pi n,\ n\in\mathbb Z\}$（**相位步长 = $\pi$**）。对**亚纯内函数** $\Theta$，对**所有** $\alpha=e^{2i\theta}\in\mathbb T$，Clark 测度 $\sigma_\alpha$ 为**纯原子**；其支撑为 $\{\Theta=\alpha\}=\{x:e^{2i\varphi(x)}=e^{2i\theta}\}=\{x:\varphi(x)=\theta+\pi n\}$ 的离散解。对**除至多一个角** $\alpha$ 外，$\{k^\Theta_x\}_{\Theta(x)=\alpha}$ 为 $K_\Theta$ 的正交核基；经 $F\mapsto F/E$ 等距同构回到 $\mathcal H(E)$，得到相位网格 $X_\theta$（**相位步长 = $\pi$**）上的正交核基（除至多一个角需另查），且 $D_\varphi^\pm(X_\theta)=1$（Baranov, Ann. Inst. Fourier **55**(7) (2005) 2399–2422）。**等距同构**为 $F\mapsto F/E:\ \mathcal H(E)\to K_\Theta$ 与其逆 $f\mapsto E f:\ K_\Theta\to\mathcal H(E)$。

**前提说明**：§1–§2 的密度判据需**全局 doubling ⇒ one-component**（回引 §0），本定理中 Clark 测度的**纯原子性**对亚纯内函数恒成立，不需该假设；"至多一个例外角"对应的是正交核基性质，而非测度性质。

对 meromorphic $\Theta$，$\{\kappa_{x_n}\}_{\varphi(x_n)=\theta+\pi n}$ 在 $K_\Theta$ 中对**所有** $\theta\in[0,\pi)$ **除至多一个值外**为正交核基（该例外角由 $\Theta-e^{2i\theta}\in L^2$ 刻画，参见 Baranov, arXiv:2206.02175 (2022) §2 对 de Branges Theorem 22 的现代复述）。

**例外角的存在性**：对 $\alpha=e^{2i\theta}\in\mathbb T$，令 $\varphi(\omega_n)=\theta+\pi n$。则对**除至多一个** $\theta$ 外，$\{\kappa_{\omega_n}\}$ 为 $\mathcal H(E)$ 的正交核基；若存在例外角 $\theta_{\mathrm{exc}}$，则由条件 $e^{i\theta_{\mathrm{exc}} z}E(z)-e^{-i\theta_{\mathrm{exc}} z}E^\sharp(z)\in\mathcal H(E)$ 刻画（见 de Branges, *Hilbert Spaces of Entire Functions*, Theorem 22, p.55；Baranov (arXiv:2206.02175, 2022, §2) 对 Theorem 22 的现代复述；Antezana–Marzo–Olsen, Theorem 1.1）。该例外角由上述条件唯一确定。在例外角处，对应核族仍为离散序列但需单独核查其正交性/归一化。（另见 Baranov (Ann. Inst. Fourier **55**(7) (2005) 2399–2422) 定理与说明；Makarov–Poltoratski 综述。）

---

## 4. 小扰动稳定与 Kadec 型定理

设 $\{x_n^{(0)}\}$ 为某 $\theta$ 的相位网格的递增枚举（$\varphi(x_n^{(0)})=\theta+n\pi$），令 $\Lambda=\{x_n\}$ 与之逐点对应。定义**相位分离量**（在相位坐标下的 Carleson 式分离）

$$
\Delta_\varphi:=\inf_{m\neq n}|\varphi(x_m)-\varphi(x_n)|>0,
$$

并记**相位偏差**

$$
\delta:=\sup_n\big|\varphi(x_n)-\varphi(x_n^{(0)})\big|.
$$

### 定理 4.1（Kadec–Bari 型稳定）

存在 $\delta_0>0$ 使得若 $\delta<\delta_0$ 且 $\Delta_\varphi>0$，则 $\{\kappa_{x_n}\}$ 与 $\{\kappa_{x_n^{(0)}}\}$ 等价，因而为 Riesz 基；框界常数仅依赖于 $\delta$ 与 $\Delta_\varphi$。

**归一说明与常数 $\delta_0$ 的确定：**

本文统一采用以下归一设定：

1. 固定 $\Theta(x)=e^{2i\varphi(x)}$，**相位步长为 $\pi$**；
2. 在 Paley–Wiener 空间 $PW_\pi$ 中，取 $\varphi'(x)\equiv \pi$，从而 $\varphi(x)=\pi x$（适当选零点）；
3. 于是相位偏差条件 $\sup_n|\varphi(x_n)-(\theta+n\pi)|<\delta_0$ 等价于 $\sup_n|\lambda_n-n|<\delta_0/\pi$（其中 $\lambda_n=x_n$）。

对应经典 Kadec (1/4) 定理（在 $L^2(0,2\pi)$ 归一下），要求 $\sup_n|\lambda_n-n|<1/4$，因此**在 Paley–Wiener 情形可取 $\delta_0=\pi/4$**。具体而言，

$$
\varphi(x)=\pi x\ \Rightarrow\ \sup_n|\varphi(x_n)-(\theta+n\pi)|<\tfrac{\pi}{4}\ \Longleftrightarrow\ \sup_n\big|x_n-\big(\tfrac{\theta}{\pi}+n\big)\big|<\tfrac14.
$$

从而 $\sup_n|\varphi(x_n)-(\theta+n\pi)|<\pi/4$ 与 $L^2(-\pi,\pi)$ 语境的 Kadec 1/4 **完全等价**。

对**一般 de Branges 空间**：$\delta_0$ 依赖于相位测度的 doubling 常数、one-component（一分量）性与相关 Carleson/伪双曲控制。对应 Baranov (2005) 在模型空间中核基/框架的小扰动稳定性结果；**具体数值需由 doubling 与 one-component 常数确定，本文不追求其最优数值**。

**说明（Kadec 1/4 与稳定性背景）**：在 Paley–Wiener 空间 $PW_\pi$ 中，Kadec 定理断言若 $\sup_n|\lambda_n-n|<1/4$，则 $\{e^{i\lambda_n t}\}$ 为 $L^2(-\pi,\pi)$ 的 Riesz 基，常数 $1/4$ 尖锐。通过相位坐标化，这与本文的相位偏差条件 $\sup_n|\varphi(x_n)-(\theta+n\pi)|<\pi/4$ **等价**（并非更强命题）；此几何化理解与经典 Kadec 1/4 定理等价，见 Vellucci 等综述/证明变体（Ricerche Mat. **64** (2015) 147–180）。一般 de Branges 空间中，相应的伪双曲/Carleson 型控制对应 Baranov (Ann. Inst. Fourier **55**(7) (2005) 2399–2422) 在模型空间中核基/框架的小扰动稳定性结果。

*证明.* 以 $\varphi$ 为坐标考察 Gram 矩阵 $G=(\langle \kappa_{x_m},\kappa_{x_n}\rangle)$。当 $\delta=0$ 时得到 Clark 构型的对角情形；小相位偏差使 $G$ 成为"对角 + 小范数偏差"的可逆紧扰动。由 Bari 定理与 Neumann 级数即得。本稳定性仅依赖 Gram 矩阵的'对角+小扰动'结构与 Bari–Neumann 论证，与窗化无关；见 Baranov (2005) 对模型空间核基/框架的小扰动稳定性结果。$\square$

**注记（$\delta_0$ 的依赖性）**：上述临界值 $\delta_0$ 依赖于相位测度的 doubling 常数与 one-component 性质中的相关控制常数；**本文采定性陈述，不追求 $\delta_0$ 的尖锐数值**。

**注记**：小相位偏差的 Riesz/框架稳定与模型空间中核基的"对角+小扰动"框架一致，可参见 Baranov（AIF 2005）。

---

## 5. Weyl–Mellin 格点与 Balian–Low 类不可能性

在带权 Mellin–Hilbert 空间 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$ 上，考虑 Weyl–Heisenberg 酉对

$$
(U_\tau f)(x)=x^{i\tau}f(x),\qquad (V_\sigma f)(x)=e^{\sigma a/2}f(e^\sigma x),
$$

满足 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$。其 Stone 生成元

$$
A=\log x,\qquad B=-i\left(x\partial_x+\tfrac a2\right)
$$

在共同核心上满足 $[A,B]=iI$。取对数坐标 $t=\log x$ 的 $L^2$-等距变换 $(\mathcal U f)(t)=e^{a t/2} f(e^t)$，则 $(U_\tau,V_\sigma)$ 化为 $\mathbb R$ 上的标准调制 $e^{i\tau t}$ 与平移 $T_\sigma$，即在 $t=\log x$ 变量下**与标准 Gabor 系统完全等价**。

**归一化说明**：本文采用 $\mathrm{e}^{i\tau t}$ 规范，因此临界密度为 $\tau_0\sigma_0=2\pi$；这与 Gabor 文献常用的 $\mathrm{e}^{2\pi i\beta t}$ 规范下的 $\alpha\beta=1$ **完全等价**。对**单窗 + 矩形格点**，由 Wexler–Raz 双正交关系与密度定理得：若 $\mathcal G(g;\Gamma)$ 成帧，则 $\alpha\beta\le 1$；若在 $\alpha\beta=1$ 时仍成帧，则必为 Riesz 基（若还是 Parseval 紧框架，则为正交基）；欠采样（$\alpha\beta>1$）不存在 Riesz 基；临界情形受 Balian–Low 障碍约束。

**下文默认：单窗、矩形（可分）格点 $\Gamma=\{(m\tau_0,n\sigma_0)\}$ 与标准 Gabor 归一。** 给定格点 $\Gamma$，记

$$
\mathcal G(g;\Gamma):=\{\,U_{m\tau_0}V_{n\sigma_0}g:\ (m,n)\in\mathbb Z^2\,\}.
$$

**规范换元**：取 $t=\log x$ 与 $\tau=2\pi\beta$、$\sigma=\alpha$，则"$\tau_0\sigma_0=2\pi$"$\Longleftrightarrow$"$\alpha\beta=1$"。

### 定理 5.1（Balian–Low 类不可能性：临界密度）

**（适用范围：单窗 + 可分（矩形）格点）**

若 $\tau_0\sigma_0=2\pi$（临界密度，或用 $e^{2\pi i\beta t}$ 归一化时 $\alpha\beta=1$），且 $\mathcal G(g;\Gamma)$ 为 Riesz 基或 Parseval 紧框架（tight frame），则必有

$$
A g\notin L^2(\mathbb R_+,x^{a-1}dx)\quad\text{或}\quad B g\notin L^2(\mathbb R_+,x^{a-1}dx).
$$

**最小可检核表述**：当格点满足临界密度且窗 $g\in L^2(\mathbb R_+,x^{a-1}dx)$ 具有有限位置二阶矩（$\int(\log x)^2|g(x)|^2 x^{a-1}dx<\infty$）或有限 Mellin 导数二阶矩（$\int|x\partial_x g+\tfrac a2 g|^2 x^{a-1}dx<\infty$）时，Gabor/Mellin–Gabor 系统不能同时为 Riesz 基/正交基（Balian–Low 定理）。

**注记与适用范围：**

1. **时—频局域化与二阶矩对应**：在对数坐标 $t=\log x$ 域，$A=\log x$ 与 $B=-i(x\partial_x+\frac a2)$ 对应于位置与动量。具体而言：
   - $A g\in L^2(\mathbb R_+,x^{a-1}dx)$ 等价于 $\int(\log x)^2|g(x)|^2 x^{a-1}dx<\infty$（对数坐标下的位置二阶矩有限）；
   - $B g\in L^2(\mathbb R_+,x^{a-1}dx)$ 等价于 $\int|x\partial_x g+\tfrac a2 g|^2 x^{a-1}dx<\infty$（Mellin 导数/动量二阶矩有限）。
   
   本定理断言即为经典时—频不确定性原理（$tg$ 与 $\widehat g'$ 的二阶矩不可同时有限）在 Gabor 基情形下的 Mellin 版本。

2. **两步化表述（密度定理 + Balian–Low）**：在**单窗 + 可分（矩形）格点**且**临界密度**（$\tau_0\sigma_0=2\pi$，或用 $e^{2\pi i\beta t}$ 归一化时 $\alpha\beta=1$）下：
   
   **步骤 (i)：密度三分律**（Heil, J. Fourier Anal. Appl. **13** (2007) 113–166；Wexler–Raz 对偶原理）
   - 单窗矩形格 Gabor 系统若成帧，必须格点密度 $\alpha\beta\le 1$；
   - 在 $\alpha\beta=1$（临界密度）时，若成帧则必为**非冗余**，即 **Riesz 基**；
   - 若进一步为 **Parseval 紧框架**（tight frame，frame bound=1），则由线性代数事实（tight Riesz 基 ⇔ ONB）得到**正交基**。
   
   **步骤 (ii)：Balian–Low 定理**（Heil–Powell, J. Math. Phys. **47** (2006) 113506；Daubechies 1992）
   - 若在 $\alpha\beta=1$ 下得到 Riesz 基/正交基，则窗 $g$ 不可能同时具有良好时—频二阶矩局域（即"紧局域"）：至少其一有限时即发生不可能性，必有 $Ag\notin L^2$ 或 $Bg\notin L^2$。
   
   **结论**：在临界密度 $\alpha\beta=1$ 下，单窗矩形格的框架（由步骤 (i) 必为 Riesz 基）受步骤 (ii) 约束，窗无法同时时—频紧局域。

3. **例外情形**：对于非分离格点或多窗系统，临界密度下存在其他路线，不受本定理约束。

*证明思路.* 在对数模型中等价于 $\mathbb R$ 上的调制—平移临界情形。若同时 $Ag,Bg\in L^2$（分别对应时域与"频域"二阶矩有限），则可构造二阶矩有限的双正交对；结合 Wexler–Raz 双正交关系与 CCR，得到与"每个基本胞元一自由度"的密度事实矛盾，故断言成立。详见 Heil–Powell（J. Math. Phys. **47** (2006) 113506）对 Riesz 基情形的标准处理；Daubechies（*Ten Lectures on Wavelets*, SIAM, 1992）对时—频局域化的经典论述。$\square$

*与经典 BLT 的对应.* 通过 $(\mathcal U f)(t)=e^{a t/2}f(e^t)$ 等距变换，有 $A\leftrightarrow t$（乘子）、$B\leftrightarrow -i\partial_t$；故"$Ag$ 或 $Bg$ 不在 $L^2$"等价于"$tg\notin L^2$ 或 $\partial_t g\notin L^2$"。这与矩形格点临界密度下 Gabor Riesz 基/（完全）帧的 Balian–Low 定理一致：若形成基/帧，则窗不可能同时具备良好的时—频二阶矩局域性。

---

## 6. 窗化误差纪律与主导项稳定性

在窗化实现下，误差分量分解为：（i）本征带限主项，（ii）泊松求和的混叠项（Nyquist 条件下为零；见 §0 规范锚点，本文采 $\widehat f(\xi)=\int f e^{-ix\xi}dx$ 规范，对应阈值 $\Delta\le\pi/\Omega$），（iii）边界/余项（**有限阶** Euler–Maclaurin 控制）。我们仅采用**有限阶** Euler–Maclaurin（见 NIST DLMF §2.10(i)，参式 2.10.20 及相关条目），并与 Poisson 求和/Nyquist 条件（见 DLMF §1.8(iv)，参式 1.8.14–1.8.16）结合控制边界层与别名项。**Nyquist–Poisson–EM 三分解仅作为实现性的换序组织，不参与定理假设**。

**与本文结论的匹配**：在窗 $w_R\in C_c^\infty(\mathbb R)$（紧支光滑，或指数衰减）且核函数满足标准 de Branges 增长估计（充分条件：对任意紧区间 $I$，$\sup_{x\in I}K(x,x)/|E(x)|^2<\infty$）的条件下，本文所用的**有限阶** Euler–Maclaurin 与 Nyquist–Poisson–EM 三分解仅影响**边界误差阶**，不改变 §1–§2 所用的**主导密度项**与 §4 的**可逆性**判据。**该性质仅作为工程化换序纪律的结论使用**，不涉及本文密度/基性定理的证明核心。具体而言：

- §1–§2 的密度估计在全局 doubling 假设下通过 Landau 型判据直接成立；窗化迹恒等（引理 1.1）的主导项 $\frac{1}{\pi}\int w_R\varphi'(x)\,dx$ 精确，边界层贡献受控；
- §4 的 Gram 矩阵可逆性与 Kadec–Bari 稳定性基于相位分离与小扰动控制，与窗化无关；
- **在仅取有限阶 EM 截断、核满足上述增长估计**的前提下，带限投影与卷积核在频域的操作对奇性集合与极阶的影响受控，在工作条带内不引入新奇点且极阶不升。

（EM 配方与伯努利多项式见 NIST DLMF §2.10(i)，参式 2.10.20 及相关条目；Poisson 求和见 DLMF §1.8(iv)，参式 1.8.14–1.8.16。）

---

## 7. 与前序理论的接口

### 7.1 S15：Weyl–Heisenberg 协变与窗函数诱导的内积

- S26 的 §5 采用 $(U_\tau,V_\sigma)$ 的 Weyl 关系与 $[A,B]=iI$，直接推广 S15 的酉表示框架；
- Balian–Low 不可能性对应 S15 中紧局域窗在临界密度下的 Riesz 基障碍。

### 7.2 S16：de Branges 规范系统与辛结构

- S26 的核心刻度 $\varphi'(x)=\pi K(x,x)/|E(x)|^2$ 即 S16 的相位—再生核公式；
- Clark 基模板对应 S16 中辛流沿相位坐标的自然采样。

### 7.3 S17：散射—酉性与相位—行列式公式

- 相位密度 $\rho(x)=\pi^{-1}\varphi'(x)$ 与 S17 的谱密度 $\rho_{\mathrm{rel}}(E)$ 联结；
- §3 的相位网格 $X_\theta$ 对应 S17 中散射相位的等间隔采样。

### 7.4 S18：窗不等式与半范数测度化

- 定理 1.2 与 2.1 的密度估计采用 S18 的窗化迹不等式框架；
- 引理 1.1 的窗化迹恒等对应 S18 的半范数测度化。

### 7.5 S19：光谱图与非回溯—邻接关系

- 离散序列的 Beurling 密度对应 S19 中图谱的局部密度；
- Riesz 序列的框界对应 S19 的非回溯算子谱分布。

### 7.6 S20：BN 投影、KL 代价与 Bregman 敏感度

- §4 的小扰动稳定性分析可调用 S20 的 Bregman 几何框架；
- Gram 矩阵的可逆性对应 S20 的 Hessian $\nabla^2\Lambda$ 的正定性。

### 7.7 S21：连续谱阈值与奇性稳定性

- §6 的"极点 = 主尺度"保持即 S21 的奇性非增定理在相位密度框架下的推广；
- 有限阶 EM 的端点层不引入新奇点，与 S21 的 Bregman–KL 敏感度链一致。

### 7.8 S22：窗/核最优化与变分原理

- §1–§2 的密度估计依赖 S22 的带限偶窗变分原理；
- 窗化迹恒等（引理 1.1）对应 S22 的频域核型 Euler–Lagrange 方程。

### 7.9 S23：多窗协同优化与 Pareto 前沿

- §4 的 Kadec 型稳定对应 S23 的多窗族小扰动稳定性；
- 相位密度阈值为 S23 的 Pareto 前沿提供必要边界。

### 7.10 S24：紧框架与对偶窗

- 定理 1.2 的采样下界对应 S24 的帧界判据；
- §3 的 Clark 基对应 S24 的 Parseval 紧帧充要条件。

### 7.11 S25：非平稳 Weyl–Mellin 框架

- §5 的格点密度阈值 $\tau_0\sigma_0=2\pi$（或 $\alpha\beta=1$）对应 S25 的"无混叠"条件；
- Balian–Low 不可能性为 S25 的非平稳 tight 框架提供临界密度边界；
- §4 的小扰动稳定对应 S25 定理 4.2 的轻微非均匀步长稳定性。

---

## 8. 失效边界

1. **无限阶 EM**：将 EM 当无穷级使用会引入伪奇性并破坏"极阶不升"，从而无法保障密度估计与稳定性。
2. **非 HB/相位不正**：若失去 $\varphi'(x)=\pi K(x,x)/|E(x)|^2>0$ 的正性，则相位密度刻度失效，应退回一般 Carleson 型测度框架。
3. **相位非分离**：相位坐标上不分离使 Gram 矩阵不可逆，小扰动定理不适用。

---

## 9. 可检清单（最小充分条件）

1. **相位刻度**：验证核—相位恒等式
$$
K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2>0,
$$
并计算 $\Phi(I)=\int_I\varphi'(x)\,dx$。**（重要）本文核心结论仅依赖上式，不依赖与 $m$-函数/谱密度的对齐。** 若需使用 $m$-函数，则**在与 canonical system 匹配的规范下**可对齐 $\Im m(x+i0)=\pi\rho(x)$ 且 $\rho(x)=\varphi'(x)/\pi$；但本文核心结论不依赖该等式。

2. **采样下界**：对非负偶窗 $w_R$，检查

$$
\sum_{x_n\in\Lambda}\!\big\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\big\rangle\ \gtrsim\ \frac1\pi\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx,
$$

令 $R\to\infty$ 与平移平均，得 $D_\varphi^-(\Lambda)\ge1$。

3. **插值上界**：对非负偶窗 $w_R$，检查

$$
\sum_{x_n\in\Lambda}\!\big\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\big\rangle\ \lesssim\ \frac1\pi\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx,
$$

同理得 $D_\varphi^+(\Lambda)\le1$。

4. **相位网格充分性**：在 $\Theta=E^\sharp/E$ 为亚纯内函数下，对**所有** $\alpha\in\mathbb T$，Clark 测度 $\sigma_\alpha$ 为纯原子（支撑离散）；对**除至多一个角** $\alpha$ 外，$\{\kappa_x\}_{x\in X_\theta}$ 为正交核基（除至多一个角外；若出现例外角需按 Theorem 22 判据另行核查），且 $D_\varphi^\pm(X_\theta)=1$（相位步长 $\pi$）。（doubling ⇒ one-component 前提仅用于 §1–§2 密度判据。）

5. **小扰动稳定**：若 $\sup_n|\varphi(x_n)-(\theta+n\pi)|\le\delta<\delta_0$ 且相位分离常数 $\Delta_\varphi>0$，用 Bari–Neumann 法得 Riesz 基稳定。

6. **Balian–Low**：在 $\tau_0\sigma_0=2\pi$ 且**单窗 + 矩形格点**下，若 $Ag,Bg\in L^2$ 则与 Wexler–Raz/CCR 矛盾，从而不可；非临界密度或多窗/非分离格按注释分情形。

7. **窗化纪律**：所有离散—连续换序仅用**有限阶** EM；Nyquist–Poisson–EM 三分解仅作为实现性的换序组织，不参与定理假设。在窗 $w_R\in C_c^\infty$ 且核满足标准增长估计下，**在仅取有限阶 EM 截断**的前提下，有限阶 EM 截断边界贡献可控，在工作条带内不引入新极点或提高极点阶数；在理想带限且采样间隔满足 Nyquist 阈值（$\Delta\le\pi/\Omega$，见 §0 规范说明）时别名项为 0。

---

## 参考文献（选）

* L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice-Hall, 1968（HB 空间、相位与再生核；Theorem 22 关于例外角的经典结论）。
* B. Eckhardt, *Scattering theory for canonical systems and applications to the spectral problem for Jacobi operators*, Invent. Math. (2024); DOI:10.1007/s00222-024-01287-9（canonical system、trace-normalized Hamiltonian 与 m 函数/谱测度关系的现代处理，含归一化讨论）。
* D. V. Romanov, A. Eckhardt, A. Kostenko 等，*Canonical systems and de Branges spaces*, arXiv:1408.6022（canonical system 与 de Branges 空间的规范化概览）。
* J. Antezana, J. Marzo, J.-F. Olsen, *Zeros of Random Functions Generated with de Branges Kernels*, Int. Math. Res. Not. IMRN **2016** (16) 5117–5144; arXiv:1504.01769; DOI:10.1093/imrn/rnv188（$K(x,x)=\pi^{-1}\varphi'(x)|E(x)|^2$ 的随机函数应用与相位函数的用法）。
* J. Marzo, S. Nitzan, J.-F. Olsen, *Sampling and interpolation in de Branges spaces with doubling phase*, J. Anal. Math. **117** (2012) 365–395; arXiv:1103.0566; DOI:10.1007/s11854-012-0026-2（**doubling 相位下的 Landau 型密度阈值，本文定理 1.2 与 2.1 所依赖的核心文献**）。
* K. Seip, *Interpolation and Sampling in Spaces of Analytic Functions*, Amer. Math. Soc., 2004（Beurling 密度与 Landau 型定理）。
* N. Makarov, A. Poltoratski, *Meromorphic Inner Functions, Toeplitz Kernels and the Uncertainty Principle*, Prog. Math. **vol. 322**, Birkhäuser, 2013（Clark 基与模型空间）。
* A. Baranov, *Cauchy–de Branges spaces, geometry of their reproducing kernels and multiplication operators*, arXiv:2206.02175 (2022)（Theorem 22 的现代复述与 Cauchy–de Branges 空间的几何）。
* A. Baranov, *Stability of bases and frames of reproducing kernels in model spaces*, Ann. Inst. Fourier **55**(7) (2005) 2399–2422; DOI:10.5802/aif.2165（模型空间核基的小扰动稳定，§4 所用）。
* S. Axler, *Berezin Transform and Invariant Subspaces*, Adv. Math. **63** (1987) 1–38（Berezin 变换与再生核关系）。
* I. Daubechies, *Ten Lectures on Wavelets*, SIAM, 1992（Balian–Low 定理与时—频局域化的经典论述）。
* C. Heil, D. Powell, *Gabor Schauder bases and the Balian-Low theorem*, J. Math. Phys. **47** (2006) 113506; DOI:10.1063/1.2393151（**BLT 的 Riesz 基情形标准处理，§5 证明所引**）。
* C. Heil, *History and Evolution of the Density Theorem for Gabor Frames*, J. Fourier Anal. Appl. **13** (2007) 113–166; DOI:10.1007/s00041-006-6073-2（**Gabor 密度定理史述、Wexler–Raz 对偶性与临界密度处 Parseval→ONB 的两步论证，§5 注记 2 所引**）。
* J. Wexler, S. Raz, *Discrete Gabor expansions*, Signal Process. **21** (1990) 207–220（Wexler–Raz 双正交关系）；另见 P. L. Søndergaard, *Gabor frames by sampling and periodization*, Adv. Comput. Math. **27** (2007) 355–373（含 LTFAT 讲义中的 Wexler–Raz 公式快速引用）。
* P. Vellucci, A. M. Bersani, *A simple pointview for Kadec-1/4 theorem in the complex case*, Ricerche Mat. **64** (2015) 147–180（Kadec 1/4 定理的综述与证明变体）。
* K. Gröchenig, *Foundations of Time–Frequency Analysis*, Birkhäuser, 2001（Weyl–Heisenberg 系统与 Kadec 定理）。
* A. Beurling, P. Malliavin, *On Fourier transforms of measures with compact support*, Acta Math. **107** (1962) 291–309（Beurling 密度）。
* N. Nikolski, *Operators, Functions, and Systems: An Easy Reading*, vol. 1, Amer. Math. Soc., 2002（Riesz 基与小扰动）。
* NIST DLMF, §2.10（Euler–Maclaurin 配方）；§1.8(iv)（Poisson 求和）。

---

**结语**

以相位导数 $\varphi'$ 为核心刻度，本文在 de Branges–Mellin 框架中统一了采样—插值密度阈值、相位网格的充分模板、小扰动稳定半径与 Mellin–Weyl 格点下的 Balian–Low 类不可能性；并在严格的"有限阶" EM 与 Nyquist–Poisson–EM 纪律下确保窗化实现对奇性与极阶的控制。由此，S15–S25 的窗/核优化与帧构造获得密度—稳定层面的边界与可检准则，也为后续非齐次/多通道相位密度与自适应窗的算子化设计提供坚实基础。该框架与 S15–S25（Weyl–Heisenberg、de Branges 规范系统、散射—酉性、窗不等式、光谱图、BN 投影、连续谱阈值、窗/核最优、多窗协同、紧框架与非平稳框架）接口一致，将相位密度作为统一刻度，建立采样—插值—帧的必要/充分准则与稳定性边界。
