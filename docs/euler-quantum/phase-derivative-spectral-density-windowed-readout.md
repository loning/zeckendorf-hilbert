# 相位导数即谱密度：量子测量的窗口化读数理论与非渐近误差闭合

**Phase-Derivative Equals Spectral Density: A Windowed Readout Theory of Quantum Measurement with Non-Asymptotic Error Closure**

**作者**：Auric
**版本**：v1.0（可复现方法学首稿）
**关键词**：Weyl–Titchmarsh 函数、Herglotz 测度、局域态密度（LDOS）、散射相位、窗化迹（windowed trace）、Nyquist–Poisson–Euler–Maclaurin（三分解误差）、隧穿/延迟时间、指针基

---

## 摘要

在 de Branges–Krein 规范系统与 Herglotz–Weyl 词典下，建立单通道散射中**相位导数与相对谱密度**的等价：对几乎处处的能量 $E$,

$$
\boxed{\ \varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)=\pi\bigl(\rho_m(E)-\rho_{m_0}(E)\bigr)\ },
$$

其中 $m,m_0$ 分别为待测算子与参照算子的 Weyl–Titchmarsh 函数，$\rho_m,\rho_{m_0}$ 为其 Herglotz–Weyl 边界虚部密度。由此导出**窗口化读数方程**：

$$
\mathrm{Obs}(R,\Delta,M,T)
=\int_{\mathbb R} w_R(E)\,\bigl[h\!\star\!\rho_\star\bigr](E)\,dE
+\varepsilon_{\mathrm{alias}}+\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}},
$$

其中 $w_R$ 为能量窗、$h$ 为带限前端核、$\rho_\star$ 按场景为 $\rho_m$ 或 $\rho_{\mathrm{rel}}$。在 Nyquist–Poisson–EM 纪律下可实现**别名关断/压阈**与**非渐近误差闭合**。该框架把"延迟/隧穿时间""负延迟"与"指针基"统一为**窗—核—采样—误差账本**的可设计问题。

---

## 0. 记号与规范

**能量与上半平面**：$E\in\mathbb R$，$\mathbb C_+=\{z:\Im z>0\}$。

**Weyl–Titchmarsh 与密度**：若 $m:\mathbb C_+\to\mathbb C_+$ 为 Herglotz（Nevanlinna）函数（半直线自伴算子或规范系统的 Weyl 函数），则

$$
\Im m(E+i0)=\pi\,\rho_m(E)\qquad(\rho_m\ge 0\ \text{a.e.}) .
$$

给定参照算子 $H_0$，定义**相对（谱移）密度**

$$
\rho_{\mathrm{rel}}(E):=\xi'(E),
$$

其中 $\xi$ 为谱移函数（SSF）。

**说明**：当 $(H,H_0)$ 源自同一边界三元组/半直线设定且端口 Weyl–Titchmarsh 函数 $m,m_0$ 存在时，在 a.e. $E$ 上有等价式 $\xi'(E)=\rho_m(E)-\rho_{m_0}(E)$（见定理 2.1）。凡与散射相位直接对应者，统一采用 $\rho_{\mathrm{rel}}$。

**散射相位**：单通道 $S(E)=e^{2i\varphi(E)}$。Wigner–Smith 矩阵 $\mathsf Q(E)$ 的定义见下文"单位约定"。

**傅里叶对（非角频率）**：

$$
\widehat f(\nu)=\int_{\mathbb R} f(E)\,e^{-2\pi i\nu E}\,dE,\qquad
f(E)=\int_{\mathbb R}\widehat f(\nu)\,e^{2\pi i\nu E}\,d\nu .
$$

若 $\operatorname{supp}\widehat h\subset[-\mathcal B_h,\mathcal B_h]$、$\operatorname{supp}\widehat w_R\subset[-\mathcal B_w(R),\mathcal B_w(R)]$，则 $\widehat w_R(\nu)=R\,\widehat w(R\nu)$、$\mathcal B_w(R)=\mathcal B_w^0/R$，并记角频率 $\Omega=2\pi\mathcal B$。

**单位约定（统一）**：本文**统一**采用 Wigner–Smith 矩阵（对能量 $E$ 求导）

$$
\boxed{\ \mathsf Q(E):=-i\,S(E)^\dagger \frac{dS}{dE}\ },\qquad
\boxed{\ \tau_{\mathrm{WS}}(E):=\hbar\,\operatorname{tr}\mathsf Q(E)\ }.
$$

则 a.e. $E$ 有

$$
\boxed{\ \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\xi'(E)\ },\qquad \text{单通道： }\operatorname{tr}\mathsf Q(E)=2\,\varphi'(E).
$$

单通道时 $\tau_{\mathrm{WS}}(E)=2\hbar\,\varphi'(E)=2\pi\hbar\,\rho_{\mathrm{rel}}(E)$。

**a.e. 范围声明**：凡含 $S'(E)$、$\varphi'(E)$、$\xi'(E)$ 或边界值 $\Im m(E+i0)$ 的等式，均在**几乎处处**能量上成立。盒装等式右上角的"a.e."标注提醒读者在共振点/不可导点按测度零处理。

**符号约定备注**：若采用他书的 $\det S=e^{-2\pi i\xi}$ 负号约定，同时置换 $\varphi\mapsto-\varphi$ 可保持 $\varphi'=\pi\rho_{\mathrm{rel}}$ 不变（详见附录 A）。

**参考**：Wigner (1955); Smith (1960) 定义与性质；Birman–Kreĭn 公式见 Yafaev (1992/2010) 与 Pushnitski (2006)，据此得 $\operatorname{tr}\mathsf Q$ 与 $\xi'$ 的关系。

**LDOS 约定**："LDOS"指端口/边界意义下的 m-测度密度及其相对版（$\rho_m$ 或 $\rho_{\mathrm{rel}}$）。单/多通道时本文以 $\rho_{\mathrm{rel}}:=\xi'(E)$ 为准；在可由端口 m-函数实现的情形，它与边界 m-测度差一致；否则以 $\xi'$ 的定义为主。当读者只关心**非负主项**时，应选用 $\rho_m$ 而非 $\rho_{\mathrm{rel}}$（见推论 2.2 与 §4）。

---

## 1. 引言

现实仪器受限于**有限带宽**与**有限时间**。因此，任何读数必然包含**谱平滑**与**窗化采样**两步。本文用严格的谱论—采样复合框架给出可实现的读数方程：**测得量 = 窗口加权的 LDOS + 三分解误差（别名/伯努利层/尾项）**，并在 Nyquist–Poisson–EM 纪律下实现**非渐近闭合**。核心事实是

$$
\varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E),
$$

从而延迟/隧穿时间、负延迟与指针基问题均可在同一窗化—误差账本下分析与设计。

**操作备注（$\rho_m$ 与 $\rho_{\mathrm{rel}}$ 的选择）**：若需**非负主项**与"能量计数"解释，请选 $\rho_m$；与相位导数/Friedel 关系配对时选 $\rho_{\mathrm{rel}}$（其符号不定）。两者在窗—核—误差账本中可互换，但物理解读不同（见推论 2.2 与 §4）。

---

## 2. 相位—密度词典（相对版）

> **符号约定前置**：本文固定采用 Birman–Kreĭn 正号约定 $\det S(E)=e^{+2\pi i\,\xi(E)}$；若读者沿用负号流派（$\det S=e^{-2\pi i\xi}$），同时令 $S\mapsto S^{-1}$（或 $\varphi\mapsto -\varphi$）可恢复相同物理结论 $\varphi'=\pi\rho_{\mathrm{rel}}$（详见附录 A）。

### 定理 2.1（相位导数 = SSF 导数；迹类假设）

在单通道散射且**满足**：
(i) $(H-i)^{-1}-(H_0-i)^{-1}\in\mathfrak S_1$（迹类）且波算子存在；
(ii) $S(E)$ 在 a.e. $E$ 可微；
(iii) 采用固定的 BK 号记 $\det S(E)=e^{+2\pi i\,\xi(E)}$；
则 a.e. $E$ 上

$$
\boxed{\ \varphi'(E)=\pi\,\xi'(E)\ }.
$$

若再假设 $(H,H_0)$ 源自同一边界三元组/半直线情形且存在对应 Weyl–Titchmarsh $m,m_0$，则 a.e. $E$ 上

$$
\boxed{\ \xi'(E)=\rho_m(E)-\rho_{m_0}(E)\ },
$$

因而 $\varphi'(E)=\pi(\rho_m-\rho_{m_0})=\pi\,\rho_{\mathrm{rel}}(E)$，其中 $\rho_{\mathrm{rel}}:=\xi'$。

**证明**（分三步）：

**(I) Birman–Kreĭn（BK）与相位导数—SSF 的导数关系。**
在 $(H,H_0)$ 的波算子存在且 $(H-i)^{-1}-(H_0-i)^{-1}$ 为迹类的假设下，SSF $\xi(E)$ 存在并满足 Kreĭn 迹公式

$$
\operatorname{Tr}\bigl(f(H)-f(H_0)\bigr)=\int_{\mathbb R} f'(E)\,\xi(E)\,dE,
$$

以及 **BK 公式**

$$
\det S(E)=\exp\{+2\pi i\,\xi(E)\}\quad(\text{a.e. }E).
$$

对单通道 $S(E)=e^{2i\varphi(E)}$，取 $\log$ 并对 $E$ 求导，得

$$
\frac{d}{dE}\log\det S(E)=2i\,\varphi'(E)=2\pi i\,\xi'(E)\quad\Longrightarrow\quad \varphi'(E)=\pi\,\xi'(E).
$$

（这里用到 a.e. 处 $\arg\det S$ 可选取连续支，且 $S$ 可微：散射相位在 a.e. 能量上可微。）

**(II) SSF 导数与 m-测度之差。**
规范系统/半直线情形中，Weyl–Titchmarsh 函数 $m$ 为 Herglotz 函数，其 Herglotz 表示的绝对连续部分满足

$$
\Im m(E+i0)=\pi\,\rho_m(E),\qquad \Im m_0(E+i0)=\pi\,\rho_{m_0}(E)\quad(\text{a.e. }E).
$$

由 Kreĭn 迹公式的分布微分与边界值理论，得到

$$
\xi'(E)=\rho_m(E)-\rho_{m_0}(E)=\rho_{\mathrm{rel}}(E)\quad(\text{a.e. }E).
$$

直观而言，$\xi'$ 即相对于参照 $H_0$ 的**边界谱密度差**。

**(III) 合并即得结论。**
由 (I) 与 (II) 立刻得到 $\varphi'(E)=\pi\xi'(E)=\pi\rho_{\mathrm{rel}}(E)$。证毕。

**a.e. 说明**：以上等式于 $E$ 的**几乎处处**成立（a.e.），在离散共振点或不可导点按测度零处理。

### 推论 2.2（$\rho_m$-版非负性）

若 $h\ge 0$、$w_R\ge 0$ 且主项采用 $\rho_m$，则

$$
\int_{\mathbb R} w_R(E)\,\bigl[h\!\star\!\rho_m\bigr](E)\,dE\ \ge\ 0 .
$$

**说明**：当 $h\ge 0$、$\rho_m\ge 0$ 时，卷积 $h\!\star\!\rho_m\ge 0$（卷积保非负性），故窗口积分非负。若换用符号不定的 $\rho_{\mathrm{rel}}$，该非负性不再保证。

---

## 3. 窗化迹与三分解误差

### 定理 3.0（窗口化读数方程）

令 $w_R$ 为能量窗，$h$ 为带限前端核，$\rho_\star\in\{\rho_m,\rho_{\mathrm{rel}}\}$。定义

$$
g(E):=w_R(E)\cdot (h\!\star\!\rho_\star)(E),\qquad
\mathcal S:=\int_{\mathbb R}g(E)\,dE .
$$

将连续读数以步长 $\Delta$ 采样、在 $[-T,T]$ 截断并以 EM 校正至 $2M$ 阶，得到

$$
\boxed{\ \mathrm{Obs}(R,\Delta,M,T)
=\mathcal S+\varepsilon_{\mathrm{alias}}+\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}}\ },
$$

其中 $\varepsilon_{\mathrm{alias}}$ 来自 Poisson 求和的带外复制（命题 3.1），$\varepsilon_{\mathrm{EM}}$ 与 $\varepsilon_{\mathrm{tail}}$ 分别由定理 3.3 的余项与截断给出。当 **(h,w_R) 严格带限**且 $\Delta\le \dfrac{1}{2(\mathcal B_h+\mathcal B_w(R))}$ 时，$\varepsilon_{\mathrm{alias}}=0$；对**近带限**核/窗，$\varepsilon_{\mathrm{alias}}$ 由 §3.1 的指数/高斯尾界**随 $\Delta$** 连续逼近 0。

**证明**：
（i）**离散化**：将 $\mathbb R$ 分割为长度 $\Delta$ 的小区间并截至 $[-T,T]$，得

$$
\mathcal S=\Delta\!\!\sum_{|n|\le T/\Delta}\! g(n\Delta)+\text{EM 校正}+\int_{|E|>T}\! g(E)\,dE .
$$

（ii）**Poisson/别名项**：用命题 3.1 将无限和改写为 $\sum_k \widehat g(k/\Delta)$，与 $\widehat g(0)=\int g$ 的差即为 $\varepsilon_{\mathrm{alias}}$。当 $\Delta\le 1/\bigl(2(\mathcal B_h+\mathcal B_w(R))\bigr)$ 时别名项为零。
（iii）**EM 与尾项**：定理 3.3 与 $w_R$ 的尾衰减给出 $\varepsilon_{\mathrm{EM}},\varepsilon_{\mathrm{tail}}$ 的上界。三项相加即得陈述。证毕。

---

下述各小节给出三分解误差的具体控制。

### 3.1 Poisson 求和与别名控制

#### 命题 3.1（Poisson 求和与 Nyquist 关断）

设 $g$ 可积且 $\widehat g$ 连续（数值实现时取带外快速衰减）；一般情形下式子也可在**温和分布**（tempered distributions）框架下解释。采用非角频率傅里叶对 $\widehat g(\nu)=\int g(E)e^{-2\pi i\nu E}dE$。则

$$
\boxed{\ \Delta\sum_{n\in\mathbb Z} g(n\Delta)=\sum_{k\in\mathbb Z}\widehat g\!\left(\frac{k}{\Delta}\right)\ }.
$$

若 $\operatorname{supp}\widehat g\subset[-B,B]$ 而采样步长满足 $\Delta\le \frac{1}{2B}$，则右侧仅 $k=0$ 项存活，别名误差 $\varepsilon_{\mathrm{alias}}=0$。

**证明**：记狄拉克梳 $\mathrm{III}_\Delta(E)=\sum_{n\in\mathbb Z}\delta(E-n\Delta)$。有

$$
\Delta\sum_{n}g(n\Delta)=\int_{\mathbb R}g(E)\,\underbrace{\Delta\,\mathrm{III}_\Delta(E)}_{=:P_\Delta(E)}\,dE.
$$

对偶性给出 $\widehat{\mathrm{III}_\Delta}(\nu)=\Delta^{-1}\sum_{k\in\mathbb Z}\delta(\nu-k/\Delta)$，故 $\widehat{P_\Delta}(\nu)=\sum_{k}\delta(\nu-k/\Delta)$。Plancherel/Parseval 与卷积—乘积关系推出

$$
\Delta\sum_{n}g(n\Delta)=\int \widehat g(\nu)\,\widehat{P_\Delta}(\nu)\,d\nu
=\sum_{k\in\mathbb Z}\widehat g\!\left(\frac{k}{\Delta}\right).
$$

若 $\operatorname{supp}\widehat g\subset[-B,B]$，当 $\Delta\le(2B)^{-1}$ 时，所有 $k\neq 0$ 的采样点 $k/\Delta$ 都落在带外，因而 $\widehat g(k/\Delta)=0$。证毕。

**应用于窗—核复合**：当 $g=w_R\cdot(h\!\star\!\rho_\star)$ 时，卷积—乘积与支撑给出：$\widehat{h\!\star\!\rho_\star}=\widehat h\cdot\widehat{\rho_\star}$，故 $\operatorname{supp}\widehat{(h\!\star\!\rho_\star)}\subset[-\mathcal B_h,\mathcal B_h]$；再由 $\widehat g=\widehat w_R*\widehat{(h\!\star\!\rho_\star)}$，得

$$
\operatorname{supp}\widehat g\subset\bigl[-(\mathcal B_h+\mathcal B_w(R)),\,\mathcal B_h+\mathcal B_w(R)\bigr].
$$

从而 Nyquist 条件为

$$
\boxed{\ \Delta\ \le\ \frac{1}{2\bigl(\mathcal B_h+\mathcal B_w(R)\bigr)}\ =\ \frac{\pi}{\Omega_h+\Omega_w(R)}\ }.
$$

**可检性备注**：当 $\widehat h$ 或 $\widehat w_R$ 仅**近**带限（而非紧支撑）时，应把 Nyquist 理解为**近似关断阈**，$|\varepsilon_{\mathrm{alias}}|$ 由下文命题 3.2 的闭式上界报告，并随 $\Delta$ 线性衰减。严格带限时别名可完全关断（$\varepsilon_{\mathrm{alias}}=0$）。

#### 命题 3.2（近带限别名上界）

在命题 3.1 的设定下，若 $\widehat g$ 带外快速衰减（非紧支），则

$$
\varepsilon_{\mathrm{alias}}=\sum_{k\neq 0}\widehat g\!\left(\frac{k}{\Delta}\right),\qquad
\bigl|\varepsilon_{\mathrm{alias}}\bigr|\ \le\ \sum_{k\neq 0}\Bigl|\widehat g\!\left(\frac{k}{\Delta}\right)\Bigr|.
$$

进一步，若 $|\widehat g(\nu)|\le C e^{-\alpha|\nu|}$（指数尾）或 $|\widehat g(\nu)|\le C e^{-\alpha\nu^2}$（高斯尾），则

$$
\bigl|\varepsilon_{\mathrm{alias}}\bigr|\le \frac{2C\,\Delta}{\alpha}\quad\text{或}\quad
\bigl|\varepsilon_{\mathrm{alias}}\bigr|\le C\sqrt{\frac{\pi}{\alpha}}\,\Delta .
$$

**证明**：由 Poisson 求和式，别名误差即去掉 $k=0$ 后的离散尾和，首个不等式显然。
（a）**指数尾**：$|\widehat g(k/\Delta)|\le C e^{-\alpha|k|/\Delta}$。故

$$
\sum_{k\neq 0}\left|\widehat g\!\left(\frac{k}{\Delta}\right)\right|
=2\sum_{k=1}^\infty C e^{-\alpha k/\Delta}
\le 2C\int_0^\infty e^{-\alpha x/\Delta}\,dx = \frac{2C\,\Delta}{\alpha}.
$$

（b）**高斯尾**：$|\widehat g(k/\Delta)|\le C e^{-\alpha k^2/\Delta^2}$。用积分比较 $\sum_{k=1}^\infty e^{-\beta k^2}\le \tfrac{1}{2}\bigl(\sqrt{\tfrac{\pi}{\beta}}-1\bigr)\le \sqrt{\tfrac{\pi}{4\beta}}$（$\beta>0$），取 $\beta=\alpha/\Delta^2$ 得到陈述的不等式。证毕。

**注（收敛性与上界）**：上述指数/高斯尾上界给出**可用 $\mathcal O(\Delta)$ 上界**报告（保守）；实际别名项对指数/高斯尾常呈**超指数**收敛（$\sim e^{-\alpha/\Delta}$ 或 $\sim e^{-\alpha/\Delta^2}$）。数值实现可用更紧的 Jacobi $\vartheta$-和或 Poisson-外推界，但不影响本框架的非渐近闭合。

### 3.2 Euler–Maclaurin（EM）伯努利层与尾项

#### 定理 3.3（Euler–Maclaurin 偶阶公式及余项上界）

设 $g\in C^{2M}([-T,T])$（或分段 $C^{2M}$ 且端点可控）。记 $N:=\lfloor T/\Delta\rfloor$。则

$$
\begin{aligned}
\int_{-T}^{T}\!g(E)\,dE
&=\Delta\!\!\sum_{|n|\le N}\! g(n\Delta)
-\frac{\Delta}{2}\,\bigl(g(T)+g(-T)\bigr)\\
&\quad-\sum_{k=1}^{M-1}\frac{B_{2k}}{(2k)!}\,\Delta^{2k}
\Bigl(g^{(2k-1)}(T)-g^{(2k-1)}(-T)\Bigr)
-R_{2M},
\end{aligned}
$$

其中余项满足

$$
\boxed{\ |R_{2M}|\ \le\ \frac{2\,\zeta(2M)}{(2\pi)^{2M}}\,\Delta^{2M}\int_{-T}^{T}\!\left|g^{(2M)}(x)\right|dx\ }.
$$

**证明**：取分段线性插值并用**周期伯努利函数** $B_{2M}(\{x/\Delta\})$ 的 Fourier 展开推导 EM 公式（标准方法）。余项可写作

$$
R_{2M}=\frac{\Delta^{2M}}{(2M)!}\int_{-T}^{T} B_{2M}(\{x/\Delta\})\,g^{(2M)}(x)\,dx .
$$

由 Fourier 展开 $B_{2M}(t)=-\dfrac{(2M)!}{(2\pi i)^{2M}}\sum_{n\neq0}\dfrac{e^{2\pi i n t}}{n^{2M}}$ 得 $|B_{2M}(t)|\le \dfrac{2(2M)!}{(2\pi)^{2M}}\zeta(2M)$ 对一切 $t$。从而

$$
|R_{2M}|
\le \frac{\Delta^{2M}}{(2M)!}\cdot \frac{2(2M)!}{(2\pi)^{2M}}\zeta(2M)\int_{-T}^T |g^{(2M)}(x)|\,dx
= \boxed{\ \frac{2\,\zeta(2M)}{(2\pi)^{2M}}\,\Delta^{2M}\int_{-T}^{T}\!|g^{(2M)}(x)|\,dx\ }.
$$

证毕。

**常数来源**：伯努利多项式 Fourier 展开 + 经典界 $|B_{2M}(t)|\le \frac{2(2M)!}{(2\pi)^{2M}}\zeta(2M)$，见标准参考文献（DLMF、Euler–Maclaurin 公式条目）。

**奇/偶情形注记**：对偶阶 $2M$ 取法，伯努利项只含偶阶 $B_{2k}$；对奇函数 $g$ 且对称区间 $[-T,T]$ 时，端点项与奇阶导数项在对称端点处相消（见附录 B 自检基准）。

**尾项控制**：定义

$$
\varepsilon_{\mathrm{EM}}(M):=|R_{2M}|,\qquad
\varepsilon_{\mathrm{tail}}(R):=\int_{|E|>T}\!|g(E)|\,dE .
$$

若 $w_R(E)\le C\,e^{-\kappa |E|/R}$（指数尾），则 $\varepsilon_{\mathrm{tail}}(R)\le \dfrac{2CR}{\kappa}\,|h\!\star\!\rho_\star|_\infty\,e^{-\kappa T/R}$。

**严格带限窗的尾项**：若在**频域采用三角谱窗（非周期 Fourier 对偶）**，则时域窗 $w_R$ 为 $\operatorname{sinc}^2$ 形（$\mathcal F\{\mathrm{tri}\}=\mathrm{sinc}^2$），**严格带限**且尾项呈多项式衰减（$\sim |E|^{-2}$），需按所选窗的已知大 $|E|$ 渐近给出具体界。

### 3.3 非渐近误差闭合

**一般情形（含近带限）**：

$$
\boxed{\ \bigl|\mathcal S-\mathcal S_{\Delta,M,T}\bigr|\ \le\ \varepsilon_{\mathrm{alias}}(\Delta)+\varepsilon_{\mathrm{EM}}(M)+\varepsilon_{\mathrm{tail}}(R)\ },
$$

其中 $\varepsilon_{\mathrm{alias}}(\Delta)$ 取 §3.1 的闭式上界（指数尾或高斯尾）。

**严格带限 + Nyquist**：

$$
\boxed{\ \bigl|\mathcal S-\mathcal S_{\Delta,M,T}\bigr|\ \le\ \varepsilon_{\mathrm{EM}}(M)+\varepsilon_{\mathrm{tail}}(R)\ }.
$$

从而读数的系统误差**逐项可控且可报告**。

**操作提示**：
1. 先验验证 Nyquist 条件 $\Delta\le 1/\bigl(2(\mathcal B_h+\mathcal B_w(R))\bigr)$；
2. 报告 $\varepsilon_{\mathrm{alias}}$ 的**显式数值上界**（按指数尾或高斯尾选用 §3.1 的闭式）；
3. 再提升 $M,T$ 以压低 $\varepsilon_{\mathrm{EM}},\varepsilon_{\mathrm{tail}}$。

---

## 4. 物理诠释：延迟、隧穿与"负延迟"

在**幺正**体系中，Wigner–Smith 矩阵
$\mathsf Q(E)=-i\,S(E)^\dagger \tfrac{d}{dE}S(E)$（Wigner 1955, Smith 1960）为 Hermitian（自伴），故其固有延迟（特征值）为**实数**但**不必非负**；并且

$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)
$$

的符号一般不定。

**密度选择提醒**：若需要"非负主项"及能量计数解释，请选 $\rho_m$；与相位导数/Friedel 关系配对时选 $\rho_{\mathrm{rel}}$（其可取负）。见推论 2.2。

**次幺正（有损/增益）体系**：延迟可为复数，需要在相应广义框架下解释。可参见近年来对**亚幺正散射**延迟的推广（Chen et al., 2021 等）。

**数值解读纪律**：在别名未关断或 EM/尾项未压低到目标阈值前，数值读数的正负号不应作物理解读。按 §3 的纪律（先 Nyquist 控制，再提 $M,T$ 或改善窗衰减）将数值误差压至阈值后，方可对"负延迟"作物理解读。

---

## 5. 指针基的窗化判据

令 $\mathcal B$ 为候选谱基，$\rho_{\mathcal B,\star}$ 为其在端口处的 LDOS（$\rho_m$ 或 $\rho_{\mathrm{rel}}$）。定义窗口化信噪比

$$
\mathsf{SNR}(\mathcal B;h,w_R,\Delta,M)\ \approx
\frac{\displaystyle\int_{\mathbb R} w_R(E)\,(h\!\star\!\rho_{\mathcal B,\star})(E)\,dE}
{\sqrt{\varepsilon_{\mathrm{alias}}^2+\varepsilon_{\mathrm{EM}}^2+\varepsilon_{\mathrm{tail}}^2}} .
$$

**说明**：此处 $\approx$ 表示把统计噪声忽略到系统误差可控阈值以下的工程近似；$\mathsf{SNR}$ 用于基的相对比较而非严格概率意义。

当满足 Nyquist 条件且 **(h,w_R) 严格带限**时，$\varepsilon_{\mathrm{alias}}=0$；对**近带限**核/窗，$\varepsilon_{\mathrm{alias}}$ 随 $\Delta$ **连续**逼近 0（§3.1 给出 $\mathcal O(\Delta)$ 上界），从而 $\mathsf{SNR}$ 将出现**显著提升**。使 $\mathsf{SNR}$ 极大的谱基即为**指针基**。

---

## 6. 多通道扩展

### 定理 6.1（多通道迹公式）

在**幺正**多通道散射 $S(E)\in\mathrm U(N)$ 下，定义 Wigner–Smith 矩阵

$$
\mathsf Q(E)=-i\,S(E)^\dagger \frac{d}{dE}S(E).
$$

则 $\mathsf Q(E)$ 为 Hermitian（自伴），其特征值（固有延迟）**可正可负**；并且 a.e. $E$,

$$
\boxed{\ \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\xi'(E)\ }.
$$

**证明**：矩阵初等微分恒等式给出

$$
\frac{d}{dE}\log\det S(E)=\operatorname{tr}\bigl(S(E)^{-1}S'(E)\bigr)=\operatorname{tr}\bigl(S(E)^\dagger S'(E)\bigr).
$$

据此

$$
\operatorname{tr}\mathsf Q(E)=-i\,\operatorname{tr}\bigl(S^\dagger S'\bigr)=-i\,\frac{d}{dE}\log\det S(E).
$$

由 BK（多通道情形同样成立）$\det S(E)=e^{+2\pi i\,\xi(E)}$，于是

$$
\operatorname{tr}\mathsf Q(E)
=-i\cdot 2\pi i\,\xi'(E)=2\pi\,\xi'(E)=2\pi\,\rho_{\mathrm{rel}}(E).
$$

两边同除以 $2\pi$ 即得。证毕。

**a.e. 说明**：以上等式于 $E$ 的**几乎处处**成立（a.e.），在离散共振点或不可导点按测度零处理。

**Hermitian 性与固有延迟**：由 $S^\dagger S=I$ 得 $(S^\dagger S)'=S'^\dagger S+S^\dagger S'=0$，故 $\mathsf Q^\dagger=i\,S'^\dagger S=-i\,S^\dagger S'=\mathsf Q$。特征值为实但可正可负。

**次幺正情形**：在**次幺正**体系（有损/增益）中，延迟可为复数，本文窗化与 Nyquist–Poisson–EM 闭合仍按迹/实部进行；读数解释需结合具体通道模型。

**符号对照**：本文采用 $\det S(E)=e^{+2\pi i\,\xi(E)}$ 正号约定，与 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\xi'$ 同号一致。不同作者的 BK 号记可能相反（见附录 A），读者需对照文献时注意符号对应。

---

## 7. 可复现实验协议（最小版）

**输入**：$(\mathcal B_h,\ \mathcal B_w^0,\ R,\ \Delta,\ M,\ T)$。
**选择**：非负、带限或带外快速衰减核 $h$（BL/Gauss-BL/Exp-BL）；**逐点非负窗** $w_R$：
  - **高斯**：指数尾，逐点非负；
  - **DPSS/PSWF**：**第 0 模态在区间内无零点**（可全正归一）；高阶本征函数出现振荡并非逐点非负（PSWF 第 $n$ 阶在 $(-1,1)$ 内恰有 $n$ 个零点）；DPSS/PSWF 为**近**带限（能量集中）而**非真带限**；
  - **频域三角谱窗（非周期对偶）**：时域为 $\operatorname{sinc}^2$ 形（$\mathcal F\{\mathrm{tri}\}=\mathrm{sinc}^2$），**严格带限**且尾项呈多项式衰减。
**纪律**：$\Delta\le 1/\bigl(2(\mathcal B_h+\mathcal B_w(R))\bigr)$；$M\ge 2$；$T$ 使 $\varepsilon_{\mathrm{tail}}$ 达到目标阈值。
**报告**：输出

$$
\Bigl(\mathrm{Obs},\ \varepsilon_{\mathrm{alias}},\ \varepsilon_{\mathrm{EM}},\ \varepsilon_{\mathrm{tail}}\Bigr),
$$

及主项占比与"非负性合规"（注明采用 $\rho_m$ 还是 $\rho_{\mathrm{rel}}$）。
**压力测试**：自大步长（不合规）逐步减小至合规，记录读数符号/台阶点，验证"**别名主导 $\to$ 去别名后主项稳定**"。

---

## 8. 结论

本文给出

$$
\textbf{相位导数 = $\pi$×相对谱密度}\quad\Longrightarrow\quad
\textbf{测得 = 窗口加权 LDOS + （别名/伯努利层/尾项）}
$$

的严格而可复现的量化框架，并在 Nyquist–Poisson–EM 纪律下实现**非渐近闭合**。该框架将延迟/隧穿、负延迟与指针性统一为**窗—核—采样—误差**的工程化问题，为后续把 Born 二次律表述为"几何投影 = 信息投影（KL/Bregman）"提供可检路径。

---

## 附录 A：符号约定与文献对照

**Birman–Kreĭn 公式约定**：本文固定采用

$$
\det S(E)=e^{+2\pi i\,\xi(E)}\quad(\text{a.e. }E),
$$

配合单通道 $S(E)=e^{2i\varphi(E)}$，得 $\varphi'=\pi\xi'$。该选择与部分教材的 $\det S=e^{-2\pi i\xi}$ 约定相差一个全局负号，但只要同时调整 $S=e^{-2i\varphi}$，物理结论 $\varphi'=\pi\rho_{\mathrm{rel}}$ 保持不变。本文采用正号约定以确保与多通道迹公式 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$ 及 Friedel 关系的同号一致性。

**定理 2.1、定理 6.1 的完整证明**见正文 §2 与 §6。

---

## 附录 B：误差上界速查表

**EM 余项**（定理 3.3）：若 $g\in C^{2M}([-T,T])$ 且 $\int_{-T}^{T}|g^{(2M)}(x)|\,dx\le G_{2M}$，则

$$
\boxed{\ \varepsilon_{\mathrm{EM}}(M)\ \le\ \frac{2\,\zeta(2M)}{(2\pi)^{2M}}\,\Delta^{2M}\,G_{2M}\ }.
$$

**尾项**：若 $w_R(E)\le C\,e^{-\kappa |E|/R}$，则

$$
\varepsilon_{\mathrm{tail}}(R)\ \le\ \frac{2CR}{\kappa}\,|h\!\star\!\rho_\star|_\infty\,e^{-\kappa T/R}.
$$

**别名误差**（命题 3.2）：指数尾 $|\widehat g(\nu)|\le C e^{-\alpha|\nu|}$ 时，$|\varepsilon_{\mathrm{alias}}|\le \dfrac{2C\,\Delta}{\alpha}$；高斯尾 $|\widehat g(\nu)|\le C e^{-\alpha\nu^2}$ 时，$|\varepsilon_{\mathrm{alias}}|\le C\sqrt{\tfrac{\pi}{\alpha}}\,\Delta$。

**自检基准**（定理 3.3 符号验证）：取常函数 $g\equiv c$，则左端 $\int_{-T}^{T}g=2Tc$；右端：求和项 $\Delta\sum_{|n|\le N}c\approx (2N+1)\Delta c \approx 2Tc+\Delta c$；端点修正 $-\frac{\Delta}{2}(c+c)=-\Delta c$；伯努利层与余项均为零。总和 $\approx 2Tc+\Delta c - \Delta c = 2Tc$ ✓。取线性 $g(E)=aE$（奇函数）时，求和与端点项均为零，伯努利奇阶项亦为零（奇导数在对称端点相消），验证通过。

---

## 附录 C：实现清单（可移植）

* FFT 卷积实现 $h\!\star\!\rho_\star$；
* 带限/近带限窗 $w_R$ 乘法；
* 均匀采样 $\Delta$ 与 EM 偶阶校正（含端点梯形项）；
* 误差账本：$\varepsilon_{\mathrm{alias}}/\varepsilon_{\mathrm{EM}}/\varepsilon_{\mathrm{tail}}$ 与主项占比；
* 明确采用 $\rho_m$ 还是 $\rho_{\mathrm{rel}}$，以避免解读混淆。

---

## 参考文献（选）

1. M. Sh. Birman & M. G. Kreĭn, *On the Theory of Wave and Scattering Operators*, Sov. Math. Dokl. **3** (1962).
2. D. R. Yafaev, *Mathematical Scattering Theory: General Theory*, AMS, 1992/2010.
3. B. Simon, *Spectral Analysis of Rank One Perturbations and Applications*, Proc. Symp. Pure Math. **65** (1999).
4. A. Pushnitski, *The Birman–Kreĭn Formula for Unitary Operators*, St. Petersburg Math. J. **17** (2006).
5. E. P. Wigner, *Lower Limit for the Energy Derivative of the Scattering Phase Shift*, Phys. Rev. **98** (1955)；F. T. Smith, *Lifetime Matrix in Collision Theory*, Phys. Rev. **118** (1960).
6. C. A. A. de Carvalho & H. M. Nussenzveig, *Time Delay*, Phys. Rep. **364** (2002).
7. J. Behrndt, F. Gesztesy, H. Holden & R. Nichols, *Spectral Shift Functions and Dirichlet-to-Neumann Maps*, Math. Ann. **371** (2018).
8. Bo-Wen Chen et al., *Generalization of Wigner Time Delay to Subunitary Scattering Systems*, Phys. Rev. E **103** (2021).
9. D. Slepian & H. O. Pollak, *Prolate Spheroidal Wave Functions, I*, Bell Syst. Tech. J. **40** (1961).
10. L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice-Hall, 1968；R. Romanov, *Canonical Systems and de Branges Spaces*, 综述。
11. E. M. Stein & R. Shakarchi, *Fourier Analysis*, Princeton, 2003（Poisson 求和与采样定理）。
12. T. M. Apostol, *Introduction to Analytic Number Theory*（Euler–Maclaurin 与伯努利数上界）。
13. DLMF（Digital Library of Mathematical Functions），§24.8，伯努利多项式与余项常数。
