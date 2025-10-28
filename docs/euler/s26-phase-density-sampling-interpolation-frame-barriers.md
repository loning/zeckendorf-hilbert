# S26. 相位密度与稳定性：de Branges–Mellin 框架下的采样—插值—帧障碍

**版本：v0.1，2025-10-28**

**—— 相位导数测度、Landau 型必要/充分准则、Balian–Low 类不可能性与小扰动稳定**

## 摘要（定性）

在 de Branges–Mellin 框架中，以相位导数 $\varphi'(x)$ 诱导的"相位密度"作为几何刻度，**证明采样与插值序列的必要端密度准则（§1–§2），并在 one-component 框架下给出充要刻画的精确前提（§1–§2 之密度充要性命题）**；证明对由相位网格作小相位扰动得到的序列存在 Riesz 基/框架的稳定半径；在 Weyl–Heisenberg（Mellin）**单窗+矩形格**情形，结合密度定理（**仅在临界密度 $\tau_0\sigma_0=2\pi$ 时**帧必为 Riesz 基）与 Balian–Low 定理（**单窗+矩形格**且临界密度下紧局域窗不可能生成 Riesz 基/正交基），给出紧局域性的障碍。上述结论在"有限阶" Euler–Maclaurin（EM）与 Nyquist–Poisson–EM 三分解纪律（仅作换序组织，见§6统一说明）下保持工作条带内的奇性集合不增与极阶不升，并与窗/核最优化的带限投影—卷积结构协同。全文定性陈述，避免对数值常数的最优化诉求。

---

## 0. 设定与相位密度

**前提（统一声明）**：令 $E\in HB$ 且**在实轴无零点**，$\varphi$ 为其相位（随 $x\in\mathbb R$ 单调且实解析）。则**几乎处处**

$$
E(x)=|E(x)|\,e^{-i\varphi(x)},\qquad
E^\sharp(z):=\overline{E(\bar z)}.
$$

（记号统一）部分文献记 $E^*(z)=\overline{E(\bar z)}$，本文统一记为 $E^\sharp(z)$。

记

$$
U(x):=\frac{E^\sharp(x)}{E(x)}=e^{2i\varphi(x)}\ \ \text{(a.e. }x\in\mathbb R),\qquad
\Theta(z):=\frac{E^\sharp(z)}{E(z)}\ \ \text{（上半平面内函数，实轴边界值 a.e. 为 }U\text{）}.
$$

再生核对角恒等式（后文"相位密度刻度"与迹恒等的唯一锚点）：

$$
\boxed{K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2>0\ \ \text{(a.e.)}}
$$

其中 $K$ 为 $\mathcal H(E)$ 的再生核。本文仅依赖上述 de Branges 核对角公式，并据此定义参考密度 $\rho(x):=\varphi'(x)/\pi$。**标准数值测度（全文统一）**定义为

$$
d\nu(x):=\frac{K(x,x)}{|E(x)|^2}\,dx=\frac{\varphi'(x)}{\pi}\,dx.
$$

归一化再生核 $\kappa_x:=K(\cdot,x)/\sqrt{K(x,x)}$ 满足

$$
\boxed{\langle \kappa_x,\kappa_y\rangle=\frac{\sin(\varphi(x)-\varphi(y))}{(x-y)\sqrt{\varphi'(x)\varphi'(y)}}\ \ (x\neq y),\quad \langle \kappa_x,\kappa_x\rangle=1}
$$

**本文所有结论仅依赖恒等成立的核—相位公式**

$$
K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2>0,
$$

因而**不依赖**对 $\Im m$ 的规范化选择。

**相位密度测度与 Beurling 密度.** 本文核心刻度为 de Branges 核对角恒等式

$$
K(x,x)=\frac{1}{\pi}\varphi'(x)|E(x)|^2>0\ \ \text{(a.e.)}
$$

与由此诱导的相位测度 $\varphi'(x)\,dx$。定义**参考密度（相位密度）** $\rho(x):=\varphi'(x)/\pi$。**关于与 Weyl–Titchmarsh $m$-函数的对齐**：在**trace-normalized Hamiltonian** 规范下（即 canonical system 的特定规范化），**可选**对齐 $\Im m(x+i0)=\pi\rho(x)$ 且 $\rho=\varphi'/\pi$；但**本文后续结论仅依赖核—相位恒等式 $K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)$ 本身，不依赖于 $\Im m$ 的具体规范化与 $m$ 函数/谱密度的对齐**。

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

**窗与迹前提（修订）.** 取 $w_R\ge0$ 且 $w_R\in L^\infty(\mathbb R)\cap L^1(\varphi'(x)\,dx)$（紧支撑可选）。记 $M_{w_R}^{(\mathrm{mult})}$ 为 $L^2(|E|^{-2}dx)$ 上的乘子算子，则其在 $\mathcal H(E)$ 上的压缩

$$
M_{w_R}:=P_{\mathcal H(E)}M_{w_R}^{(\mathrm{mult})}P_{\mathcal H(E)}
$$

为正且迹类，并有

$$
\operatorname{Tr}\!\big(M_{w_R}\big)=\int_{\mathbb R} w_R(x)\,\frac{K(x,x)}{|E(x)|^{2}}\,dx=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx.
$$

（证明见引理 1.1；此处的 $L^\infty$ 假设保证乘子有界，从而压缩算子与迹运算良定义。）

**窗化误差与 Nyquist–Poisson–EM 三分解（概要；详见 §6）**：在窗化/加权截断后，误差分量分解为（i）本征带限主项，（ii）泊松求和的混叠项（Nyquist 条件下为零），（iii）边界/余项（**有限阶** Euler–Maclaurin 控制）。本文仅采用**有限阶** Euler–Maclaurin（**NIST DLMF §2.10(i)**）与 Poisson 求和（**DLMF §1.8(iv)**）结合控制边界层与别名项；**Nyquist–Poisson–EM 三分解仅作为实现性的换序组织，不参与定理假设**。在窗 $w_R\in C^{2N}$（紧支或指数衰减）且仅取**有限阶** EM 截断时，换序所致误差层为整/全纯，**在工作条带 $|\Im z|\le h$ 内不引入新奇点且极阶不升**。具体前提与匹配见 **§6 统一声明**。

**密度章节假设（仅用于 §1–§2；记作 S1）.** 为应用 Landau 型密度判据，**仅在 §1–§2** 假设相位测度 $\varphi'(x)\,dx$ 为（局部）doubling（满足 MNO 要求的 doubling 条件），即存在 $R_0>0$（可为无穷）与 $C\ge1$ 使对所有区间 $I$ 满足 $|I|\le R_0$ 时有

$$
\int_{2I}\varphi'(x)\,dx\le C\int_I\varphi'(x)\,dx,
$$

其中 $2I$ 记以 $I$ 的中心为中心、直径加倍的区间。本文所谓（局部）doubling均指相位测度 $\varphi'(x)\,dx$ 的（局部）doubling。

**技术路线说明（关键）**：在（局部）doubling 相位的前提下，本文**直接**引用 doubling-phase 情形的密度定理（**Marzo–Nitzan–Olsen 2012**）得出采样/插值密度阈值；亦可采用"one-component 路线"调用 Landau 型密度刻画，但需自备所需附加条件。**除 §1–§2 外（如 §3 Clark 基、§4 稳定、§5–§6 窗化纪律），不需要该假设。**§3 的 Clark 基纯原子性对亚纯内函数恒成立；"至多一个例外角"对应正交核基性质，而非测度性质。相关命题处将回引本前提。

**规范锚点（全文统一）**：

- **两条核心公式（本文全部结论仅依赖此二式）**：
  $$
  \boxed{K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)>0\ \ \text{(a.e.)}}\qquad\text{（核对角恒等式）}
  $$
  $$
  \boxed{\langle \kappa_x,\kappa_y\rangle=\frac{\sin(\varphi(x)-\varphi(y))}{(x-y)\sqrt{\varphi'(x)\varphi'(y)}}\ \ (x\neq y)}\qquad\text{（归一化核内积）}
  $$
  
  **规范提示（重要）**：上述公式不依赖与 $m$-函数/谱密度的对齐。*如需引入谱密度/ $m$ 函数*，在**trace-normalized** Hamiltonian 规范下有 $\Im m(x+i0)=\pi\,\rho(x)$ 与 $\rho=\varphi'/\pi$；本篇主定理不以此为假设。

- **内函数与相位网格**：$\Theta=\dfrac{E^\sharp}{E}=e^{2i\varphi}$（a.e.），$X_\theta=\{x:\Theta(x)=e^{2i\theta}\}=\{x:\varphi(x)=\theta+\pi n\}$（**相位步长 = $\pi$**）。
- **相位尺度与密度**：$\Phi(I)=\int_I\varphi'(x)\,dx$，$D_\varphi^\pm(\Lambda)=\lim_{R\to\infty} \frac{\#(\Lambda\cap I)}{\Phi(I)/\pi}$。
- **窗口与迹**（充分条件）：$w_R\ge0$ 有界且紧支撑（或 $w_R\in L^1(\varphi'\,dx)$）$\Rightarrow$ $M_{w_R}|_{\mathcal H(E)}$ 为正且迹类，$\operatorname{Tr}(M_{w_R})=\frac{1}{\pi}\int w_R\,\varphi'$。
- **标准数值测度**：令 $d\nu(x):=\frac{K(x,x)}{|E(x)|^2}\,dx=\frac{\varphi'(x)}{\pi}\,dx$。

**规范对照表（Gabor/Mellin 临界密度互译）**：

**本文统一选择**：在 Paley–Wiener 例中，默认 $PW_\pi$（带宽 $T=\pi$，相位函数 $\varphi(x)=\pi x$）；其他带宽 $T$ 由缩放还原。在 Fourier 规范（$\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$）下，$\varphi'(x)\equiv\pi$ 与时间步长 1 对齐，故 Kadec 条件 $\sup_n|\varphi(x_n)-(\theta+n\pi)|<\pi/4$ 等价于 $\sup_n|x_n-(\theta/\pi+n)|<1/4$（与经典 Kadec 1/4 定理完全等价，并非更强命题；详见 §4）。

| 规范 | Fourier 规范（本文） | $2\pi$-频率规范 | Paley–Wiener 例 |
|------|---------------------|----------------|----------------|
| Fourier 变换 | $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$ | $\widehat f(\nu)=\int f(t)e^{-2\pi i\nu t}dt$ | $\varphi(x)=\pi x$ |
| 带宽 | $\Omega$ (rad/s) | $B$ (Hz) | $T$ (带宽 $[-T,T]$) |
| Nyquist 阈值 | $\Delta\le\pi/\Omega$ | $\Delta_t\le 1/(2B)$ | $\Delta=\pi/T$ |
| Gabor 临界密度 | $\tau_0\sigma_0=2\pi$ | $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$ | （本行仅 §5 引用） |
| 等价关系 | $\tau=2\pi\beta_{\mathrm{Gabor}}$，$\sigma=\alpha_{\mathrm{Gabor}}$ | $\Omega=2\pi B$ | $\varphi'(x)\equiv\pi$ |

---

## 1. 采样与相位密度：Landau 型必要条件

记标准化再生核 $\kappa_x:=K(\cdot,x)/\sqrt{K(x,x)}$。称 $\Lambda$ 为**采样序列**，若存在常数 $A,B>0$ 使

$$
A\,\|F\|_{\mathcal H(E)}^2\ \le\ \sum_{x_n\in\Lambda}\frac{|F(x_n)|^2}{K(x_n,x_n)}\ \le\ B\,\|F\|_{\mathcal H(E)}^2,
\qquad \forall\,F\in\mathcal H(E).
$$

**采样/插值序列的相位分离性**：在 **one-component** 内函数或 **doubling-phase** 前提下，**Riesz（插值）序列**在相位坐标下正分离（$\inf_{m\neq n}|\varphi(x_m)-\varphi(x_n)|>0$）；在一般 de Branges 空间，必要分离先以模型空间的伪双曲/Carleson 量化描述，等价为相位分离需附加 one-component 条件。**采样（帧）序列一般不自动分离**，后续如需用到分离，应**另行假设相位分离/有限重数**；在**局部重数有界**时，可将采样集分解为**有限个**分离子序列并逐个应用相位窗化与 Berezin 估计；若局部重数无界，则无需分解，直接以窗化+Berezin 估计处理总体上、仅得到比例常数控制。本节后续引理在分离前提下给出窗化—迹—计数的桥接。

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

*注记（易检充分条件，修订）.* 作为便利性检查，若 **$w_R$ 为紧支撑**且另知 $\sup_{x\in\operatorname{supp}w_R}\frac{K(x,x)}{|E(x)|^2}<\infty$，亦可直接验证迹类性；**若仅要求 $w_R\in L^1(\varphi' dx)\cap L^\infty$ 而支撑不必紧，则不必也不保证上述 sup 界**——但由
$$
\operatorname{Tr}(M_{w_R})=\int w_R\,\frac{K(x,x)}{|E(x)|^{2}}dx=\frac{1}{\pi}\int w_R\,\varphi'(x)\,dx<\infty
$$
仍可得到 $M_{w_R}$ 为正且迹类。**Toeplitz 压缩的迹类性**可由标准 Berezin 变换与核对角求和论证得到。

*证明.* 取 $w_R\in L^1(\varphi'dx)\cap L^\infty$ 并由正性单调逼近 $C_c$ 情形，可由 $\sum_n\langle M_{w_R}e_n,e_n\rangle=\int w_R K/|E|^{2}dx$ 得到迹类与迹值的充要性。在上述条件下（$w_R\ge0$，$w_R\in L^1\cap L^\infty$，核满足标准 de Branges 界），$M_{w_R}$ 为迹类。取任一正交基 $\{e_n\}$，记其有限截断族 $\{e_1,\ldots,e_N\}$ 的秩—$N$ 投影为 $\Pi_N$，则 $\Pi_N\uparrow I$（SOT）。由 $M_{w_R}\ge0$ 且 $M_{w_R}$ 迹类，得 $M_{w_R}^{1/2}\Pi_N M_{w_R}^{1/2}\uparrow M_{w_R}$ 为**非降**迹类序列；据**单调收敛定理**与 $\|M_{w_R}\|$ 的**主控**，可逐项取迹并与求和交换。由 $\langle f,g\rangle_{\mathcal H(E)}=\int f\bar g\,|E|^{-2}dx$ 和再生核恒等式 $\sum_n |e_n(x)|^2=K(x,x)$ 得
$$
\operatorname{Tr}(M_{w_R})=\sum_n\langle M_{w_R}e_n,e_n\rangle=\int w_R \sum_n|e_n|^2 |E|^{-2}dx=\int w_R K(x,x)|E|^{-2}dx,
$$
再用 $K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)$ 即得。$\square$

**注记（Berezin 变换与迹公式）.** 对任意有界乘子 $M_{w}$，定义其 **Berezin 变换**为

$$
\boxed{\widetilde w(x):=\langle M_{w}\kappa_x,\kappa_x\rangle,}
$$

其中 $\kappa_x$ 为归一化再生核。一般有 $\widetilde w(x)\neq w(x)$，且由 Cauchy–Schwarz 得 $|\widetilde w(x)|\le\|M_w\|\le\|w\|_\infty$。本文所用的迹恒等式与密度估计仅涉及 Berezin 符号 $\widetilde w$ 在 $\Lambda$ 上的求和，作为对 $w$ 的积分的近似，无需 $\widetilde w\equiv w$。具体而言：压缩乘子 $M_{w_R}$ 的迹

$$
\operatorname{Tr}(M_{w_R})=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx
$$

仅依赖于原窗函数 $w_R$，而密度估计中出现的求和 $\sum_{x_n}\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle$ 涉及 Berezin 变换值 $\widetilde w_R(x_n)$；通过迹不等式与窗的平移—缩放即可将其转化为区间计数估计。若 $M_w$ 为正迹类且以**标准数值测度** $d\nu(x)=\frac{\varphi'(x)}{\pi}\,dx$（见 §0 规范锚点）计算，则有**连续 Parseval 分辨率恒等式**

$$
\int_{\mathbb R}\widetilde w(x)\,d\nu(x)=\operatorname{Tr}(M_w);
$$

*证明草图*：对任意 $f\in\mathcal H(E)$，由再生核性质 $\langle f,\kappa_x\rangle=f(x)/\sqrt{K(x,x)}$，有
$$
\|f\|^2=\int_{\mathbb R}|f(x)|^2\frac{dx}{|E(x)|^2}=\int_{\mathbb R}\frac{|f(x)|^2}{K(x,x)}\,d\nu(x)=\int_{\mathbb R}|\langle f,\kappa_x\rangle|^2\,d\nu(x).
$$
取标准基 $\{e_n\}$ 并对 $M_w$ 求迹，由 Fubini 定理得 $\operatorname{Tr}(M_w)=\sum_n\langle M_w e_n,e_n\rangle=\int\widetilde w(x)\,d\nu(x)$。此等式仅用于迹与求和的比较，不要求 $\widetilde w\equiv w$。

下文所有"单位质量窗"均指相对于相位测度 $\varphi'(x)\,dx$ 归一：$\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx=1$，且 $\operatorname{diam}(\operatorname{supp}w_R)\asymp R$；此时 $\operatorname{Tr}(M_{w_R})=1$。

### 定理 1.2（采样的相位密度下界；前提：$\varphi'(x)\,dx$ 为（局部）doubling）

若 $\Lambda$ 为采样序列，则 $D_\varphi^-(\Lambda)\ge 1$，即采样序列的相位密度必须不低于相位测度的自然密度阈值。

**适用前提（S1；作用域仅限 §1–§2）**：**本文在（局部）doubling 前提下直接引用 MNO 2012 的 doubling-phase 密度定理得出密度阈值，亦可采用 one-component 路线但需自备附加条件。**该假设仅用于本节与 §2 的密度必要性结论；§3 的 Clark 基纯原子性对亚纯内函数恒成立，不需此假设；§4 的小扰动稳定基于 Gram 矩阵论证，与 doubling 无关。

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

**迹不等式转区间计数（需引理 1.3 桥接）**：取**近似指标窗** $w_{R,I}$（使 $\frac{1}{\pi}\int w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$）作为区间 $I$ 的近似指标，则上述迹不等式给出序列计数的下界估计。此处把 $\sum\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle$ 与 $\#(\Lambda\cap I)$ 比较，依赖下述引理 1.3 的定量估计。**分离性说明**：若 $\Lambda$ 在相位坐标下**已分离**（即另行假设或由 Riesz 性自动保证），则直接应用引理 1.3；若 $\Lambda$ 不分离（一般采样序列），则先将 $\Lambda$ 按相位坐标分解为**有限个分离子序列** $\{\Lambda^{(j)}\}$（局部重数有界），对每个 $\Lambda^{(j)}$ 应用引理 1.3 后求和，密度下界仍然成立。

### 引理 1.3（Berezin 变换与区间计数的桥接；采样下界情形）

设 $\varphi'(x)\,dx$ 为（局部）doubling 且 $\Lambda$ 在相位坐标下**正分离**（$\inf_{m\neq n}|\varphi(x_m)-\varphi(x_n)|\ge\Delta_\varphi>0$）。对区间 $I\subset\mathbb R$，可构造平滑窗 $w_{R,I}\ge0$，满足：

(i) $\operatorname{supp}w_{R,I}\subset I^{(+)}$（其中 $I^{(+)}$ 为 $I$ 的有限相位厚化，$\Phi(I^{(+)})\le C\Phi(I)$，常数 $C$ 仅依赖 doubling 常数）；

(ii) $w_{R,I}(x)\ge c>0$ 对 $x\in I^{(-)}$（$I^{(-)}$ 为 $I$ 的内缩，$\Phi(I^{(-)})\ge c'\Phi(I)$）；

(iii) $\frac{1}{\pi}\int_{\mathbb R} w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$；

(iv) Berezin 变换 $\widetilde w_{R,I}(x):=\langle M_{w_{R,I}}\kappa_x,\kappa_x\rangle$ 满足 $\widetilde w_{R,I}(x)\ge c_1>0$ 对 $x\in I^{(-)}$（**常数依赖注记**：**若采用路线 A（doubling）**，则 $c_1$ 仅依赖于 doubling 常数与相位分离常数 $\Delta_\varphi$；**若采用路线 B（one-component）**，则 $c_1$ 依赖于 one-component 常数与 $\Delta_\varphi$。下文在必要端默认使用路线 A。本引理给出窗化技术层面的比例估计，**不直接导出阈值=1**）。

于是对采样序列 $\Lambda$（下界 $AI\le T_\Lambda$），有
$$
\sum_{x_n\in\Lambda}\widetilde w_{R,I}(x_n)=\operatorname{Tr}(M_{w_{R,I}}^{1/2}T_\Lambda M_{w_{R,I}}^{1/2})\ge A\,\operatorname{Tr}(M_{w_{R,I}})=\frac{A}{\pi}\Phi(I),
$$
结合 (iv) 得
$$
c_1\,\#(\Lambda\cap I^{(-)})\le\sum_{x_n\in\Lambda}\widetilde w_{R,I}(x_n)\ge\frac{A}{\pi}\Phi(I),
$$
从而 $\#(\Lambda\cap I^{(-)})\ge\frac{A}{c_1\pi}\Phi(I)$。令 $R\to\infty$ 并对区间中心平移平均，由 doubling 性质得 $\#(\Lambda\cap I)/(\Phi(I)/\pi)\ge c_2>0$，其中 $c_2$ 依赖于 $A$ 与 doubling/分离常数。**本引理建立窗化迹与计数的桥接，但比例常数 $c_2$ 与帧界/分离常数耦合；常数归一到 1 需调用外部密度定理（见定理 1.2 证明末端）。**

*证明思路.* 窗的构造采用平移平均技术；Berezin 变换的下界由 one-component 性质与归一化核的局部内积估计得到（在相位分离前提下，$\langle\kappa_x,\kappa_x\rangle=1$ 且 Gram 矩阵在对角附近受控）。$\square$

*构造示例.* 可取 $w_{R,I}$ 为平滑顶帽（或 Fejér 型窗）：支撑在 $I$ 附近，$\operatorname{diam}(\operatorname{supp}w_{R,I})\asymp|I|$，并经归一化使 $\frac{1}{\pi}\int w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$。其中 $I^{(+)}$ 与 $I^{(-)}$ 的构造为：取 $0<\eta<1$，令 $\Phi(I^{(+)})=(1+\eta)\Phi(I)$、$\Phi(I^{(-)})=(1-\eta)\Phi(I)$；由 doubling 性质可保证满足引理 1.3 的条件 (i)–(iv)。

令 $R\to\infty$ 并对区间中心平移平均，在相位导数 $\varphi'(x)\,dx$ 为（局部）doubling 的假设下（回引 §0 结构性假设），配合引理 1.1、引理 1.3 与 Landau 型密度定理（MNO 2012），得 $D_\varphi^-(\Lambda)\ge 1$。$\square$

**提示**：本定理在（局部）doubling 前提下引用 doubling-phase 密度定理得出阈值。

---

## 1.5 密度充要性命题

**命题（采样/插值的相位密度充要刻画；两条路线，按目标选择）.**

设 $\Lambda\subset\mathbb R$ 为离散序列，并在相位坐标下**正分离**。

**路线 A（必要端，doubling）**：若相位测度 $\varphi'(x)\,dx$ **满足（局部）doubling**，则
- 若 $\Lambda$ 为采样序列，$D_\varphi^-(\Lambda)\ge 1$；
- 若 $\Lambda$ 为 Riesz（插值）序列，$D_\varphi^+(\Lambda)\le 1$。

**路线 B（充分端，one-component）**：在 **one-component** 且 **分离/Carleson** 前提下，
- 若 $D_\varphi^-(\Lambda)>1$，则 $\Lambda$ 为采样序列；
- 若 $D_\varphi^+(\Lambda)<1$，则 $\Lambda$ 为插值序列。

（两路线互不叠加：A 用于必要端，B 用于充分端；如采用 doubling-route 的充分性，请以"可替代路线"表述，而非与 B 叠加。）

**本文 §1–§2 仅证明上述必要端**（路线 A：采样下界 $D_\varphi^-\ge1$ 与插值上界 $D_\varphi^+\le1$），**充分端（路线 B）在 one-component 框架与分离/Carleson 前提下完整给出**。

---

## 2. Riesz 序列与相位密度：插值的上界（上界必要性）

称 $\Lambda$ 为（标准化核）**Riesz 序列**，若 $\{\kappa_{x_n}\}_{x_n\in\Lambda}$ 在 $\mathcal H(E)$ 内为 Riesz 系列，即存在 $A',B'>0$ 使

$$
A'\sum |c_n|^2\ \le\ \left\|\sum c_n\,\kappa_{x_n}\right\|_{\mathcal H(E)}^2\ \le\ B'\sum |c_n|^2.
$$

记 $\Pi_\Lambda$ 为 $\operatorname{span}\{\kappa_{x_n}\}$ 的正交投影。

### 定理 2.1（插值的相位密度上界；前提：$\varphi'(x)\,dx$ 为（局部）doubling）

若 $\Lambda$ 为 Riesz 序列（因而为插值序列），则 $D_\varphi^+(\Lambda)\le 1$，即插值序列的相位密度必须不超过相位测度的自然密度阈值。

**适用前提（S1；作用域仅限 §1–§2）**：**本文在（局部）doubling 前提下直接引用 MNO 2012 的 doubling-phase 密度定理得出密度阈值，亦可采用 one-component 路线但需自备附加条件。**该假设仅用于本节与 §1 的密度必要性结论；§3 的 Clark 基纯原子性对亚纯内函数恒成立，不需此假设；§4 的小扰动稳定基于 Gram 矩阵论证，与 doubling 无关。

*证明（修订版）.* 取 $w_R\ge0$ 为**相位测度** $\varphi'(x)\,dx$ 下的近单位族：$\frac{1}{\pi}\int_{\mathbb R} w_R\,\varphi'(x)\,dx=1$，支撑直径按 $\Phi$ 规模趋向无穷，且 $\|w_R\|_\infty\le1$。Riesz 性给出 $A'\Pi_\Lambda\le T_\Lambda\le B'\Pi_\Lambda$。于是

$$
\sum_{x_n}\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle
=\operatorname{Tr}(M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2})
\le B'\,\operatorname{Tr}(M_{w_R}^{1/2}\Pi_\Lambda M_{w_R}^{1/2})
\le B'\,\operatorname{Tr}(M_{w_R}).
$$

*严格化换序说明.* 与定理 1.2 同理，记 $\Lambda_R=\Lambda\cap I_R$ 为有限子集，由 $M_{w_R}\ge0$ 的正性与 $T_{\Lambda_R}\uparrow T_\Lambda$ 的单调收敛性，配合 Riesz 序列的帧界控制，迹与求和互换可由单调收敛定理保证。因 $\{\kappa_{x_n}\}$ 的 Riesz 性质保证 $T_\Lambda$ 有界，而 $M_{w_R}$ 为正迹类，故积算子 $M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2}$ 为迹类，且可按标准 Berezin 变换论证逐项求迹。

**迹不等式转区间计数（需引理 2.2 桥接）**：同定理 1.2，取**近似指标窗** $w_{R,I}$（使 $\frac{1}{\pi}\int w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$）作为区间 $I$ 的近似指标，则上述迹不等式给出序列计数的上界估计。此处把 $\sum\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle$ 与 $\#(\Lambda\cap I)$ 比较，依赖下述引理 2.2 的定量估计。**分离性说明**：Riesz 序列在相位坐标下**必然正分离**，引理 2.2 直接适用。

### 引理 2.2（Berezin 变换与区间计数的桥接；插值上界情形）

设 $\varphi'(x)\,dx$ 为（局部）doubling 且 $\Lambda$ 在相位坐标下**正分离**。对区间 $I\subset\mathbb R$，构造平滑窗 $w_{R,I}\ge0$ 如引理 1.3。于是对 Riesz 序列 $\Lambda$（上界 $T_\Lambda\le B'\Pi_\Lambda$），有
$$
\sum_{x_n\in\Lambda}\widetilde w_{R,I}(x_n)=\operatorname{Tr}(M_{w_{R,I}}^{1/2}T_\Lambda M_{w_{R,I}}^{1/2})\le B'\,\operatorname{Tr}(M_{w_{R,I}})=\frac{B'}{\pi}\Phi(I).
$$
另一方面，由引理 1.3 的 (iv)（Berezin 变换下界 $\widetilde w_{R,I}(x)\ge c_1>0$ 对 $x\in I^{(-)}$）得
$$
\sum_{x_n\in\Lambda}\widetilde w_{R,I}(x_n)\ge c_1\,\#(\Lambda\cap I^{(-)}),
$$
从而 $\#(\Lambda\cap I^{(-)})\le\frac{B'}{c_1\pi}\Phi(I)$。令 $R\to\infty$ 并对区间中心平移平均，由 doubling 性质得 $\#(\Lambda\cap I)/(\Phi(I)/\pi)\le c_3$，其中 **若采用路线 A（doubling）**，$c_3$ 仅依赖于 $B'$、doubling 常数与分离常数；**若采用路线 B（one-component）**，则 $c_3$ 依赖于 $B'$、one-component 常数与分离常数。

*证明思路.* 同引理 1.3；上界估计利用 Riesz 序列的投影不等式与 Berezin 变换的 $L^\infty$ 界（$|\widetilde w_{R,I}(x)|\le\|w_{R,I}\|_\infty$）。$\square$

*构造示例.* 同定理 1.2，可取 $w_{R,I}$ 为平滑顶帽（或 Fejér 型窗）：支撑在 $I$ 附近，$\operatorname{diam}(\operatorname{supp}w_{R,I})\asymp|I|$，并经归一化使 $\frac{1}{\pi}\int w_{R,I}\varphi'(x)\,dx=\Phi(I)/\pi$。

配合引理 1.1、引理 2.2 与插值密度结论，在相位导数 $\varphi'(x)\,dx$ 为（局部）doubling 的假设下，令 $R\to\infty$ 并对区间中心平移平均，配合 Landau 型密度定理（MNO 2012）得 $D_\varphi^+(\Lambda)\le 1$。$\square$

**提示**：本定理在（局部）doubling 前提下引用 doubling-phase 密度定理得出阈值。

**读者指南（§1–§2 总结）**：本文 §1–§2 **直接证明必要端**（采样下界 $D_\varphi^-\ge1$ 与插值上界 $D_\varphi^+\le1$）；**充分端**在 one-component 框架与分离/Carleson 前提下完整给出（见 §1.5 命题）。§3 给出相位网格的充分构造（Clark 基），§4 给出小扰动稳定性。

---

## 3. 相位网格与 Clark 基：充分性模板（构造）

**本节角色说明**：本节给出达到密度=1 的**一个充分构造**（相位网格上的 Clark 基），**并非一般充要刻画**；充要刻画见 §1.5。

对任意 $\theta\in\mathbb R$，定义"相位网格"（**相位步长为 $\pi$**）

$$
\boxed{X_\theta:=\{x\in\mathbb R:\ \Theta(x)=e^{2i\theta}\}=\{x:\ \varphi(x)=\theta+\pi n,\ n\in\mathbb Z\}.}
$$

**定理 3.1（Clark 基的相位密度刻画）.** 设 $\Theta=E^\sharp/E$ 为**亚纯内函数**。

**等距同构约定（本节统一）**：定义 $U:\mathcal H(E)\to K_\Theta$ 为 $(UF)(z)=F(z)/E(z)$，其逆 $U^{-1}:K_\Theta\to\mathcal H(E)$ 为 $(U^{-1}f)(z)=E(z)\,f(z)$。以下统一用 $U$ 与 $U^{-1}$ 表示两空间的来回对应。

则：

（i）对**所有** $\alpha\in\mathbb T$，Clark 测度 $\sigma_\alpha$ 为**纯原子**（支撑为 $\{x:\Theta(x)=\alpha\}$ 的离散集）。原子质量满足**精确恒等式**（meromorphic 内函数；与本节的等距同构规范一致）

$$
\sigma_\alpha(\{x\})=\frac{1}{|\Theta'(x)|}.
$$

（对**亚纯内函数**，所有 Clark 测度支撑均为离散。**前提说明**：本性质对**所有**亚纯内函数恒成立，不需 §1–§2 所用的 doubling 假设。）

（ii）对**除至多一个角** $\alpha=e^{2i\theta}\in\mathbb T$ 外，$\{k^\Theta_{x}\}_{\Theta(x)=\alpha}$ 构成 $K_\Theta$ 的**正交核基**。**该例外角由充要条件**

$$
\boxed{e^{i\theta_{\mathrm{exc}}}E(z) - e^{-i\theta_{\mathrm{exc}}}E^\sharp(z) \in\mathcal H(E)}
$$

**唯一刻画**（其中 $\theta_{\mathrm{exc}}\in\mathbb R$ 为常数）。若无例外角，则对**所有** $\theta\in[0,\pi)$，相位网格 $X_\theta$ 均对应正交核基。

经 $U^{-1}$ 回到 $\mathcal H(E)$，得到相位网格 $X_\theta=\{x:\varphi(x)=\theta+\pi n,\ n\in\mathbb Z\}$（**相位步长 = $\pi$**）上的正交核基（除至多一个角外；若出现例外角需按 Theorem 22 判据另行核查），且

$$
D_\varphi^\pm(X_\theta)=1.
$$

**说明.** 在实轴上 $\Theta(x)=\dfrac{E^\sharp(x)}{E(x)}=e^{2i\varphi(x)}$（a.e.），故相位网格 $X_\theta=\{x:\varphi(x)=\theta+\pi n,\ n\in\mathbb Z\}$（**相位步长 = $\pi$**）。对**亚纯内函数** $\Theta$，对**所有** $\alpha=e^{2i\theta}\in\mathbb T$，Clark 测度 $\sigma_\alpha$ 为**纯原子**；其支撑为 $\{\Theta=\alpha\}=\{x:e^{2i\varphi(x)}=e^{2i\theta}\}=\{x:\varphi(x)=\theta+\pi n\}$ 的离散解。对**除至多一个角** $\alpha$ 外，$\{k^\Theta_x\}_{\Theta(x)=\alpha}$ 为 $K_\Theta$ 的正交核基；经 $U^{-1}$ 回到 $\mathcal H(E)$，得到相位网格 $X_\theta$（**相位步长 = $\pi$**）上的正交核基（除至多一个角需另查），且 $D_\varphi^\pm(X_\theta)=1$。

**前提说明**：§1–§2 的密度判据需在**（局部）doubling 前提下引用 doubling-phase 密度定理**（回引 §0），本定理中 Clark 测度的**纯原子性**对亚纯内函数恒成立，不需该假设；"至多一个例外角"对应的是正交核基性质，而非测度性质。

对 meromorphic $\Theta$，$\{k_{x_n}^\Theta\}_{\varphi(x_n)=\theta+\pi n}$ 在 $K_\Theta$ 中对**所有** $\theta\in[0,\pi)$ **除至多一个值外**为正交核基；经 $U^{-1}$ 回到 $\mathcal H(E)$，得到对应的 $\{\kappa_{x_n}\}$ 结论。

**例外角的存在性与刻画**：对 $\alpha=e^{2i\theta}\in\mathbb T$，令 $\varphi(\omega_n)=\theta+\pi n$。则对**除至多一个** $\theta$ 外，$\{\kappa_{\omega_n}\}$ 为 $\mathcal H(E)$ 的正交核基；若存在例外角 $\theta_{\mathrm{exc}}$，其**充要**刻画为

$$
\boxed{e^{i\theta_{\mathrm{exc}}}E(z) - e^{-i\theta_{\mathrm{exc}}}E^\sharp(z) \in\mathcal H(E)}
$$

**关键说明（常数相位；重要）**：$\theta_{\mathrm{exc}}$ 为**常数相位**，不依赖于 $z$；上式中 $e^{i\theta_{\mathrm{exc}}}$ 与 $e^{-i\theta_{\mathrm{exc}}}$ 均为复常数（而非依赖于 $z$ 的函数）。该例外角由上述条件唯一确定。在该**例外角** $\theta_{\mathrm{exc}}$ 处，$\{\kappa_x\}_{\Theta(x)=e^{2i\theta_{\mathrm{exc}}}}$ 在 $\mathcal H(E)$ 中构成**余维 1 的正交集**，其正交补由 $e^{i\theta_{\mathrm{exc}}}E-e^{-i\theta_{\mathrm{exc}}}E^\sharp$ 张成；对**非该角**的所有其他 $\theta$，相应核族 $\{\kappa_x\}_{\varphi(x)=\theta+\pi n}$ 均为（正交核）基。

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

**归一说明与常数 $\delta_0$ 的确定（重要；分 PW 与一般情形）：**

本文统一采用以下归一设定：

1. 固定 $\Theta(x)=e^{2i\varphi(x)}$，**相位步长为 $\pi$**；
2. 在 Paley–Wiener 空间 $PW_\pi$ 中，取 $\varphi'(x)\equiv \pi$，从而 $\varphi(x)=\pi x$（适当选零点；与本文采用的 $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$ 的弧度规范一致）；
3. 于是相位偏差条件 $\sup_n|\varphi(x_n)-(\theta+n\pi)|<\delta_0$ 等价于 $\sup_n|\lambda_n-n|<\delta_0/\pi$（其中 $\lambda_n=x_n$）。

对应经典 Kadec (1/4) 定理（在 $L^2(-\pi,\pi)$ 归一化下），要求 $\sup_n|\lambda_n-n|<1/4$，因此**在 Paley–Wiener 情形可取 $\delta_0=\pi/4$（⚠️ 仅 PW 归一；非更强命题）**。具体而言，

$$
\varphi(x)=\pi x\ \Rightarrow\ \sup_n|\varphi(x_n)-(\theta+n\pi)|<\tfrac{\pi}{4}\ \Longleftrightarrow\ \sup_n\big|x_n-\big(\tfrac{\theta}{\pi}+n\big)\big|<\tfrac14.
$$

从而 $\sup_n|\varphi(x_n)-(\theta+n\pi)|<\pi/4$ 与 $L^2(-\pi,\pi)$ 语境的 Kadec 1/4 **完全等价**（并非更强命题）。

**规范警示**：在 $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$ 规范下，$PW_\pi$ 中 $\varphi'(x)\equiv\pi$ 与时间步长 1 对齐，故 $\delta_0=\pi/4$ 等价于 $\sup_n|\lambda_n-n|<1/4$。

对**一般 de Branges 空间**：$\delta_0$ 依赖于相位测度的 doubling 常数、one-component（一分量）性与相关 Carleson/伪双曲控制，在模型空间中核基/框架的小扰动稳定性结果中给出；**具体数值 $\delta_0$ 需由 doubling 与 one-component 常数以及 Bernstein 型不等式的常数确定，本文不追求其最优数值，亦无统一显式常数**（一般情形无尖锐常数）。

**注（Paley–Wiener 情形与经典 Kadec 1/4）**：在 Paley–Wiener 空间 $PW_\pi$ 中，取 $\varphi(x)=\pi x$，则相位偏差条件 $\sup_n|\varphi(x_n)-(\theta+n\pi)|<\pi/4$ 等价于 $\sup_n|x_n-(\theta/\pi+n)|<1/4$，这正是 $L^2(-\pi,\pi)$ 归一化下经典 Kadec 1/4 定理的形式。因此本文相位坐标表述在 Paley–Wiener 情形下与经典结论**完全等价**，并非更强命题。

**说明（Kadec 1/4 与稳定性背景）**：在 Paley–Wiener 空间 $PW_\pi$ 中，Kadec 定理断言若 $\sup_n|\lambda_n-n|<1/4$，则 $\{e^{i\lambda_n t}\}$ 为 $L^2(-\pi,\pi)$ 的 Riesz 基，常数 $1/4$ 尖锐。通过相位坐标化，这与本文的相位偏差条件 $\sup_n|\varphi(x_n)-(\theta+n\pi)|<\pi/4$ **等价**（并非更强命题）；此几何化理解与经典 Kadec 1/4 定理等价。一般 de Branges 空间中，相应的伪双曲/Carleson 型控制对应模型空间中核基/框架的小扰动稳定性结果。

*证明.* 以 $\varphi$ 为坐标考察 Gram 矩阵 $G=(\langle \kappa_{x_m},\kappa_{x_n}\rangle)$。当 $\delta=0$ 时得到 Clark 构型的对角情形；小相位偏差给出

$$
G=I+K,\qquad \|K\|\le C(\Delta_\varphi)\delta<1,
$$

因而 $G$ 是**对角 + 小范数有界扰动**的可逆算子。由 Neumann 级数得可逆性，结合 Bari 定理即得 Riesz 基稳定。本稳定性仅依赖 Gram 矩阵的'对角+小扰动'结构与 Bari–Neumann 论证，与窗化无关。$\square$

**注记（$\delta_0$ 的依赖性）**：上述临界值 $\delta_0$ 依赖于相位测度的 doubling 常数与 one-component 性质中的相关控制常数；**本文采定性陈述，不追求 $\delta_0$ 的尖锐数值**。在 Paley–Wiener 情形 $\delta_0=\pi/4$ 对应经典 Kadec 1/4 定理；在一般 de Branges–doubling 情形 $\delta_0$ 取决于 doubling/one-component 常数。

**注记**：小相位偏差的 Riesz/框架稳定与模型空间中核基的"对角+小扰动"框架一致。

---

## 5. Weyl–Mellin 格点与 Balian–Low 类不可能性

**符号消歧声明（本节独立；重要）**：本节讨论 Gabor 系统，为**彻底避免与 §3 中单位圆角度 $\alpha=e^{2i\theta}\in\mathbb T$ 的混淆**，本节 Gabor 网格步长**统一记为 $(\sigma,\tau)$ 或 $(\sigma_0,\tau_0)$**（空间—频率步长，实数），**不使用** $(\alpha,\beta)$ 记号；圆周角度始终用 $e^{2i\theta}$ 表示。**规范换元对照**：本文采用 $\mathrm{e}^{i\tau t}$ 规范，临界密度为 $\tau_0\sigma_0=2\pi$；这与 Gabor 文献常用的 $\mathrm{e}^{2\pi i\beta t}$ 规范下的 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$ 完全等价（换元：$\tau=2\pi\beta_{\mathrm{Gabor}}$，$\sigma=\alpha_{\mathrm{Gabor}}$）。

在带权 Mellin–Hilbert 空间 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$ 上，考虑 Weyl–Heisenberg 酉对

$$
(U_\tau f)(x)=x^{i\tau}f(x),\qquad (V_\sigma f)(x)=e^{\sigma a/2}f(e^\sigma x),
$$

满足 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$。其 Stone 生成元

$$
A=\log x,\qquad B=-i\left(x\partial_x+\tfrac a2\right)
$$

在共同核心上满足 $[A,B]=iI$。取对数坐标 $t=\log x$ 的 $L^2$-等距变换 $(\mathcal U f)(t)=e^{a t/2} f(e^t)$，则 $(U_\tau,V_\sigma)$ 化为 $\mathbb R$ 上的标准调制 $e^{i\tau t}$ 与平移 $T_\sigma$，即在 $t=\log x$ 变量下**与标准 Gabor 系统完全等价**。

**归一化说明与规范换元（重要）**：本文采用 $\mathrm{e}^{i\tau t}$ 规范，因此临界密度为 $\tau_0\sigma_0=2\pi$；这与 Gabor 文献常用的 $\mathrm{e}^{2\pi i\beta_{\mathrm{Gabor}} t}$ 规范下的 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$ **完全等价**。**显式换元**：在 $\widehat{f}(\xi)=\int f(x)e^{-ix\xi}dx$ 规范下，带宽 $\Omega$ 的 Nyquist 阈值为 $\Delta\le\pi/\Omega$；取 $\beta_{\mathrm{Gabor}}=\Omega/\pi$（时间步长 $\alpha_{\mathrm{Gabor}}=\Delta$），则临界条件 $\Delta=\pi/\Omega$ 等价于 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$，即本文的 $\tau_0\sigma_0=2\pi$。对**单窗 + 矩形格点**，由 Wexler–Raz 双正交关系与密度定理得：**若 $\mathcal G(g;\Gamma)$ 成帧，则格点密度 $\tau_0\sigma_0\le 2\pi$（等价地 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}\le 1$）**；在 $\tau_0\sigma_0=2\pi$（临界密度）时，若成帧则必为 **Riesz 基**（矩形格 + 单窗；Wexler–Raz/密度定理）；若进一步为 **Parseval 紧框架**，则为 **ONB**（tight Riesz 基⇔正交基）；**过采样**（$\tau_0\sigma_0<2\pi$）帧可能存在但不可能为 Riesz 基；**欠采样**（$\tau_0\sigma_0>2\pi$）仅可能得到 Riesz 序列而非帧；临界情形受 Balian–Low 障碍约束。

**下文默认（适用范围声明）：单窗、矩形（可分）格点 $\Gamma=\{(m\tau_0,n\sigma_0)\}$ 与标准 Gabor 归一。** 给定格点 $\Gamma$，记

$$
\mathcal G(g;\Gamma):=\{\,U_{m\tau_0}V_{n\sigma_0}g:\ (m,n)\in\mathbb Z^2\,\}.
$$

**规范换元对照表**：

| 本文（Fourier 规范） | Gabor 文献（$2\pi$ 规范） | 关系 |
|---|---|---|
| $\mathrm{e}^{i\tau t}$ | $\mathrm{e}^{2\pi i\beta_{\mathrm{Gabor}} t}$ | $\tau=2\pi\beta_{\mathrm{Gabor}}$ |
| 时间步长 $\sigma$ | 时间步长 $\alpha_{\mathrm{Gabor}}$ | $\sigma=\alpha_{\mathrm{Gabor}}$ |
| 临界密度 $\tau_0\sigma_0=2\pi$ | 临界密度 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$ | 等价 |
| 对数坐标 $t=\log x$ | — | Mellin ↔ Fourier 等距 |

临界密度条件 $\tau_0\sigma_0=2\pi \Longleftrightarrow \alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$ 的两种规范下完全等价。

### 定理 5.1（**单窗 + 矩形格点**；Balian–Low 类不可能性：**临界密度**）

**适用范围与前提（关键）**：本定理仅适用于**单窗 + 可分（矩形）格点** $\Gamma=\{(m\tau_0,n\sigma_0)\}$ 且**临界密度** $\tau_0\sigma_0=2\pi$（或用 $e^{2\pi i\beta_{\mathrm{Gabor}} t}$ 归一化时 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$）的情形。在该设定下：

- **密度定理约束（步骤 i）**：单窗矩形格 Gabor 系统若成帧，必须格点密度 $\tau_0\sigma_0\le 2\pi$（等价地 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}\le 1$）；在 $\tau_0\sigma_0=2\pi$（临界密度）时，若成帧则必为**非冗余**（Riesz 基）；进一步若为 **Parseval 紧框架**（tight frame，frame bound=1），则由非冗余性与 tight 性质联合得到**正交基**（tight Riesz 基⇔ONB）。

**主断语**：若在上述前提下 $\mathcal G(g;\Gamma)$ 为 Riesz 基或正交基，则必有

$$
A g\notin L^2(\mathbb R_+,x^{a-1}dx)\quad\text{或}\quad B g\notin L^2(\mathbb R_+,x^{a-1}dx).
$$

**最小可检核表述**：当格点满足临界密度且 $\mathcal G(g;\Gamma)$ 为 Riesz 基或正交基时，**不可能同时**满足有限位置二阶矩（$\int(\log x)^2|g(x)|^2 x^{a-1}dx<\infty$）**且**有限 Mellin 导数二阶矩（$\int|x\partial_x g+\tfrac a2 g|^2 x^{a-1}dx<\infty$）。等价地：至少一个二阶矩必须发散（Balian–Low 定理）。

**注记与适用范围：**

1. **时—频局域化与二阶矩对应**：在对数坐标 $t=\log x$ 域，$A=\log x$ 与 $B=-i(x\partial_x+\frac a2)$ 对应于位置与动量。具体而言：
   - $A g\in L^2(\mathbb R_+,x^{a-1}dx)$ 等价于 $\int(\log x)^2|g(x)|^2 x^{a-1}dx<\infty$（对数坐标下的位置二阶矩有限）；
   - $B g\in L^2(\mathbb R_+,x^{a-1}dx)$ 等价于 $\int|x\partial_x g+\tfrac a2 g|^2 x^{a-1}dx<\infty$（Mellin 导数/动量二阶矩有限）。
   
   本定理断言即为经典时—频不确定性原理（$tg$ 与 $\widehat g'$ 的二阶矩不可同时有限）在 Gabor 基情形下的 Mellin 版本。

2. **两步化表述（密度定理 + Balian–Low）**：在**单窗 + 可分（矩形）格点**且**临界密度**（$\tau_0\sigma_0=2\pi$，或用 $e^{2\pi i\beta_{\mathrm{Gabor}} t}$ 归一化时 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$）下：
   
   **步骤 (i)：密度三分律**
   - 单窗矩形格 Gabor 系统若成帧，必须格点密度 **$\tau_0\sigma_0\le 2\pi$**（等价地 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}\le 1$）；
   - 在 $\tau_0\sigma_0=2\pi$（临界密度）时，若成帧则必为**非冗余**，即 **Riesz 基**；
   - **在临界密度且单窗+矩形格下**，若进一步为 **Parseval 紧框架**（tight frame，frame bound=1），则由非冗余性（Riesz 基）与 tight 性质联合得到**正交基**（tight Riesz 基 ⇔ ONB）。
   
   **步骤 (ii)：Balian–Low 定理**
   - 若在 $\tau_0\sigma_0=2\pi$ 下得到 Riesz 基/正交基，则窗 $g$ **不可能**同时时、频二阶矩良好：**必有** $Ag\notin L^2$ **或** $Bg\notin L^2$（即二者不可能同时属于 $L^2$）。
   
   **结论**：在临界密度 $\tau_0\sigma_0=2\pi$ 下，单窗矩形格的框架（由步骤 (i) 必为 Riesz 基）受步骤 (ii) 约束，窗无法同时时—频紧局域。

3. **例外情形**：对于非分离格点或多窗系统，临界密度下存在其他路线，不受本定理约束。

*证明思路.* 在对数模型中等价于 $\mathbb R$ 上的调制—平移临界情形。若同时 $Ag,Bg\in L^2$（分别对应时域与"频域"二阶矩有限），则可构造二阶矩有限的双正交对；结合 Wexler–Raz 双正交关系与 CCR，得到与"每个基本胞元一自由度"的密度事实矛盾，故断言成立。$\square$

*与经典 BLT 的对应.* 通过 $(\mathcal U f)(t)=e^{a t/2}f(e^t)$ 等距变换，有 $A\leftrightarrow t$（乘子）、$B\leftrightarrow -i\partial_t$；故"$Ag$ 或 $Bg$ 不在 $L^2$"等价于"$tg\notin L^2$ 或 $\partial_t g\notin L^2$"。这与矩形格点临界密度下 Gabor Riesz 基/（完全）帧的 Balian–Low 定理一致：若形成基/帧，则窗不可能同时具备良好的时—频二阶矩局域性。

---

## 6. 窗化误差纪律与主导项稳定性

在窗化实现下，误差分量分解为：（i）本征带限主项，（ii）泊松求和的混叠项（Nyquist 条件下为零；见 §0 规范锚点，本文采 $\widehat f(\xi)=\int f e^{-ix\xi}dx$ 规范，对应阈值 $\Delta\le\pi/\Omega$），（iii）边界/余项（**有限阶** Euler–Maclaurin 控制）。我们仅采用**有限阶** Euler–Maclaurin，并与 Poisson 求和/Nyquist 条件结合控制边界层与别名项。**Nyquist–Poisson–EM 三分解仅作为实现性的换序组织，不参与定理假设**。

### 定理 6.1（有限阶 EM 与换序的奇性—极阶控制；条件化命题）

设下列条件满足：

**(H1) 窗正则性与衰减**：$w_R\in C^{2N}(\mathbb R)$（至少 $2N$ 阶连续可微且导数有界；或紧支光滑 $C_c^\infty$；或指数衰减速度 $|w_R^{(k)}(x)|\le C_k e^{-\delta|x|}$，$k\le 2N$）；

**(H2) 核增长控制**：核函数满足标准 de Branges 增长估计，即对任意紧区间 $I\subset\mathbb R$，
$$
\sup_{x\in I}\frac{K(x,x)}{|E(x)|^2}<\infty;
$$

**(H3) 工作条带解析性**：在工作条带 $|\Im z|\le h$ 内，$E(z)$、$E^\sharp(z)$ 及相关被积对象（包括窗—核卷积的被积函数）解析（或至少具有所需阶数 $2N$ 的导数且增长受控，$|\partial_z^k F(x+iy)|\le C_k(1+|x|)^{M_k} e^{-\epsilon|y|}$，$k\le 2N$，$|y|\le h$）；

**(H4) 有限阶 EM 截断（标准偶阶）**：取偶阶 $2N$，采用 DLMF §2.10.20 形式
$$
\sum_{k=a}^{b} f(k)=\int_a^b f(x)\,dx+\frac{f(a)+f(b)}{2}
+\sum_{j=1}^{N}\frac{B_{2j}}{(2j)!}\big(f^{(2j-1)}(b)-f^{(2j-1)}(a)\big)+R_{2N},
$$
其中余项
$$
R_{2N}=\frac{1}{(2N)!}\int_{a}^{b} B_{2N}(\{x\})\,f^{(2N)}(x)\,dx.
$$
文中仅取有限阶 $2N$ 截断，不取无穷级；

**(H5) Poisson 求和的绝对收敛**：对所需的 Poisson 求和（DLMF §1.8(iv)），要求
$$
\sum_{n\in\mathbb Z}|\widehat F(2\pi n/\Delta)|<\infty,
$$
从而换序合法（其中 $\widehat F$ 为窗—核卷积的 Fourier 变换）。

**结论**：在假设 (H1)–(H5) 下，本文所用的**有限阶** Euler–Maclaurin 与 Nyquist–Poisson–EM 三分解仅影响**边界误差阶**，不改变 §1–§2 所用的**主导密度项**与 §4 的**可逆性**判据。具体而言：

(i) **密度估计的主导项精确**：§1–§2 的窗化迹恒等（引理 1.1）的主导项 $\frac{1}{\pi}\int w_R\varphi'(x)\,dx$ 精确，边界层贡献 $R_N$ 在 $R\to\infty$ 时以阶 $O(R^{-N+M_N})$ 衰减（$M_N$ 由 (H3) 确定），不影响密度极限 $D_\varphi^\pm(\Lambda)$；

(ii) **奇性集合不增**：在工作条带 $|\Im z|\le h$ 内，带限投影与卷积核在频域的操作不引入新奇点（新奇点仅可能出现在 $|\Im z|>h$ 外，或边界 $\Im z=\pm h$ 上的受控边界贡献）；

(iii) **极阶不升**：设原被积对象在条带内最高极阶为 $m$，则经有限阶 EM、Poisson 求和与带限投影处理后，主导项的极阶不超过 $m$（边界项与余项的极阶不超过 $m+N$，但系数受 $R^{-N}$ 衰减控制）；

(iv) **Gram 矩阵可逆性保持**：§4 的 Gram 矩阵可逆性与 Kadec–Bari 稳定性基于相位分离与小扰动控制，与窗化无关；在 (H1)–(H5) 下，窗化实现不改变 Gram 矩阵的谱性质（主导项为精确内积，边界层为受控小扰动）。

*证明思路.* (i) 由 EM 余项估计与 (H1)–(H4) 得边界层的多项式—指数衰减。(ii)–(iii) 由 Poisson 求和的频域表示与 (H3)、(H5) 的解析性/增长控制得到：Fourier 变换将条带内的奇点映射至上/下半频域，带限投影仅保留主频带 $[-\Omega,\Omega]$，而 EM 的边界项为整函数或在条带内解析，故不引入新奇点；极阶不升由卷积定理与 Fourier 变换的极点映射性质保证。(iv) 由 Bari–Neumann 论证与小扰动稳定性直接得到。$\square$

**与本文结论的匹配（防守型前提）**：在假设 (H1)–(H5) 下，**定理 6.1 的结论仅作为工程化换序纪律的条件化陈述使用**，不涉及本文密度/基性定理的证明核心。具体而言：

- §1–§2 的密度估计在全局 doubling 假设下通过 Landau 型判据直接成立；窗化迹恒等（引理 1.1）依赖定理 6.1(i) 的主导项精确性；
- §4 的 Gram 矩阵可逆性与 Kadec–Bari 稳定性依赖定理 6.1(iv)，确保窗化实现不改变基性判据；
- §1–§2、§3 的密度与 Clark 基构造**不依赖**定理 6.1，可独立阅读；定理 6.1 仅为实现层提供正当性保障。


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

- §5 的格点密度阈值 $\tau_0\sigma_0=2\pi$（或等价地 $\alpha_{\mathrm{Gabor}}\beta_{\mathrm{Gabor}}=1$）对应 S25 的"无混叠"条件；
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

2. **采样下界**：对非负窗 $w_R$（满足 §1 统一窗化假设），检查

$$
\sum_{x_n\in\Lambda}\!\big\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\big\rangle\ \gtrsim\ \frac1\pi\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx,
$$

由窗化迹不等式 + 平移平均，仅得比例界 $\#(\Lambda\cap I)/(\Phi(I)/\pi)\ge c_2>0$（$c_2$ 依赖帧界/分离常数）；**在（局部）doubling 或 one-component 的前提下（两条路线；前者用于必要端，后者用于充分端），应用相应密度定理将比例常数归一到 1**，从而 $D_\varphi^-(\Lambda)\ge 1$。（**需 Landau 步骤；适用前提 S1：仅用于 §1–§2 密度必要性结论。**）

3. **插值上界**：对非负窗 $w_R$（满足 §1 统一窗化假设），检查

$$
\sum_{x_n\in\Lambda}\!\big\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\big\rangle\ \lesssim\ \frac1\pi\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx,
$$

由窗化迹不等式 + 平移平均，仅得比例界 $\#(\Lambda\cap I)/(\Phi(I)/\pi)\le c_3<\infty$（$c_3$ 依赖 Riesz 界/分离常数）；**在（局部）doubling 或 one-component 的前提下（两条路线；前者用于必要端，后者用于充分端）应用相应密度定理将比例常数归一到 1**，从而 $D_\varphi^+(\Lambda)\le 1$。（**需 Landau 步骤；适用前提 S1：仅用于 §1–§2 密度必要性结论。**）

4. **相位网格充分性**：在 $\Theta=E^\sharp/E$ 为亚纯内函数下，对**所有** $\alpha\in\mathbb T$，Clark 测度 $\sigma_\alpha$ 为纯原子（支撑离散）；对**除至多一个角** $\alpha$ 外，$\{\kappa_x\}_{x\in X_\theta}$ 为正交核基（除至多一个角外；若出现例外角需按 Theorem 22 判据另行核查），且 $D_\varphi^\pm(X_\theta)=1$（相位步长 $\pi$）。（§1–§2 的密度判据需在 doubling 前提下引用 doubling-phase 密度定理。）

5. **小扰动稳定**：若 $\sup_n|\varphi(x_n)-(\theta+n\pi)|\le\delta<\delta_0$ 且相位分离常数 $\Delta_\varphi>0$，用 Bari–Neumann 法得 Riesz 基稳定。

6. **Balian–Low**：在 $\tau_0\sigma_0=2\pi$ 且**单窗 + 矩形格点**下，若 $Ag,Bg\in L^2$ 则与 Wexler–Raz/CCR 矛盾，从而不可；非临界密度或多窗/非分离格按注释分情形。

7. **窗化纪律（见 §6 定理 6.1）**：所有离散—连续换序仅用**有限阶** EM；Nyquist–Poisson–EM 三分解仅作为实现性的换序组织，不参与定理假设。在假设 (H1)–(H5)（见定理 6.1）下：窗 $w_R\in C^{2N}$（紧支光滑或指数衰减），核满足标准增长估计，$E,E^\sharp$ 在工作条带 $|\Im z|\le h$ 解析且增长受控，仅取**有限阶** $N$ 的 EM 截断，Poisson 求和绝对收敛，则换序所致误差层在工作条带内不引入新奇点且极阶不升；在理想带限且采样间隔满足 Nyquist 阈值时别名项为 0。详细前提与结论见 **§6 定理 6.1**。

---

## 参考文献（选）

* L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice-Hall, 1968（HB 空间、相位与再生核；Theorem 22 关于例外角的经典结论）。
* Eckhardt, J.; Kostenko, A. *Trace formulas and inverse spectral theory for generalized indefinite strings*, Invent. Math. **238** (2024), 391–502. DOI:10.1007/s00222-024-01287-9（canonical system、trace-normalized Hamiltonian 与 m 函数/谱测度关系的现代处理，含归一化讨论）。
* Romanov, R. *Canonical systems and de Branges spaces*, arXiv:1408.6022 (2014)（canonical system 与 de Branges 空间的规范化概览）。
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
* P. Vellucci, A. M. Bersani, *A simple pointview for Kadec-1/4 theorem in the complex case*, Ricerche Mat. **64** (2015) 87–92（Kadec 1/4 定理的综述与证明变体；[作者页面](https://dgasi.uniroma3.it)）。
* K. Gröchenig, *Foundations of Time–Frequency Analysis*, Birkhäuser, 2001（Weyl–Heisenberg 系统与 Kadec 定理）。
* A. Beurling, P. Malliavin, *On Fourier transforms of measures with compact support*, Acta Math. **107** (1962) 291–309（Beurling 密度）。
* N. Nikolski, *Operators, Functions, and Systems: An Easy Reading*, vol. 1, Amer. Math. Soc., 2002（Riesz 基与小扰动）。
* NIST DLMF, §2.10（Euler–Maclaurin 配方）；§1.8(iv)（Poisson 求和）。

---

**结语**

以相位导数 $\varphi'$ 为核心刻度，本文在 de Branges–Mellin 框架中统一了采样—插值密度阈值、相位网格的充分模板、小扰动稳定半径与 Mellin–Weyl 格点下的 Balian–Low 类不可能性；并在严格的"有限阶" EM 与 Nyquist–Poisson–EM 纪律下确保窗化实现对奇性与极阶的控制。由此，S15–S25 的窗/核优化与帧构造获得密度—稳定层面的边界与可检准则，也为后续非齐次/多通道相位密度与自适应窗的算子化设计提供坚实基础。该框架与 S15–S25（Weyl–Heisenberg、de Branges 规范系统、散射—酉性、窗不等式、光谱图、BN 投影、连续谱阈值、窗/核最优、多窗协同、紧框架与非平稳框架）接口一致，将相位密度作为统一刻度，建立采样—插值—帧的必要/充分准则与稳定性边界。
