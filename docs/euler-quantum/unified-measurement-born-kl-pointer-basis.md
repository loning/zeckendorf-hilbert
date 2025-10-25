# 窗口化读数统一测量：Born 概率 = 最小 KL，指针基 = 最小能量本征基

（含非渐近误差闭合与窗/核最优）

**作者**：
**单位**：
**日期**：2025-10-25

---

## 摘要（定性）

本文在**镜像核—de Branges–Kreĭn 规范系统—信息几何**的统一框架下，提出并严格证明三条主定理：

1. **窗口化读数定理**：任何可实现的量子测量读数均等价于"能量窗 $w_R$ 与前端核 $h$"对（相对或绝对）**局域态密度**（LDOS）的加权；当采用**离散采样—有限截断**的现实流程时，误差可按 **Nyquist（别名）–Poisson（采样）–Euler–Maclaurin（EM，求和—积分差）**三项**非渐近闭合**，且在**带限 + Nyquist 条件**下别名项严格为零。该结论立足于 Weyl–Titchmarsh $m$-函数的 Herglotz 性与边界值词典（$\Im m(E+i0)=\pi\rho(E)$）及其与规范系统的等价表述。
2. **Born 概率 = 最小 KL（信息投影）**：当读数字典与**对数-配分势** $\Lambda(\rho)=\log\!\sum_j w_j e^{\langle\beta_j,\rho\rangle}$ 对齐时，**单位响应的最小能量投影**与**线性矩约束下的最小 Kullback–Leibler（KL）散度**等价；softmax 概率正是最小-KL 投影的权，且当 $\tau\!\downarrow\!0$（或等价地 $\beta=1/\tau\!\uparrow\!\infty$）时经 $\Gamma$-极限收敛为硬投影（Hilbert 正交）。等价使用 **Fenchel–Legendre 对偶 / Bregman–KL 恒等式 / Csiszár 的 I-projection**。
3. **指针基 = 最小能量/信息投影的本征基**：有限字典下，最小能量 mollifier 的系数向量为 $\beta^\star=\dfrac{G^{-1}c}{c^\ast G^{-1}c}$；在 Gram 谱分解 $G=U\Lambda U^\ast$ 中，$\beta^\star$ 沿 $\{u_k\}$ 以 $\lambda_k^{-1}$ 加权展开，因而**对 $\beta^\star$ 贡献最强的方向**由

$$
\arg\max_k\ \frac{|\langle u_k,c\rangle|^2}{\lambda_k}
$$

实现；小特征值趋势放大该方向，但是否主导取决于同时具有足够大的投影 $|\langle u_k,c\rangle|$。软版的信息 Hessian $\nabla^2\Lambda$ 的谱基与之同构。

在散射侧，借由 **Birman–Kreĭn** 与 **Wigner–Smith** 的标准构造，单通道下相位导数与（相对）谱密度满足

$$
\varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)=\pi\,\xi'(E),\qquad
\mathsf Q(E)=-i\,S(E)^\dagger\frac{dS}{dE},
$$

进而 $\tfrac1{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$。这把"负延迟"解释为**参照选择**与**相对计数**的结果，而非因果违反。

**关键词**：窗口化读数；Weyl–Titchmarsh；谱移函数；Wigner–Smith 时间延迟；de Branges 空间；BN—Bregman；最小 KL；PSWF；Nyquist–Poisson–EM；非渐近误差。

---

## 0. 记号与背景

* **能量与上半平面**：$E\in\mathbb R$，$\mathbb C_+=\{z:\Im z>0\}$。
* **Weyl–Titchmarsh 与 LDOS**：若 $m:\mathbb C_+\!\to\!\mathbb C_+$ 为 Herglotz–Nevanlinna 函数且其测度部分在 $E$ 处具密度 $\rho_m(E)$，则 a.e.

$$
\Im m(E+i0)=\pi\rho_m(E).
$$

此处的 $\pi$ 来自 **Stieltjes 反演**的标准常数，与傅里叶变换规范无涉。本文采用傅里叶规范 $\widehat f(\xi)=\int f(t)e^{-it\xi}\,dt$。
* **散射相位与谱移**：本文固定 Birman–Kreĭn 的"正号"约定

$$
\det S(E)=e^{+2\pi i\,\xi(E)},\qquad \xi'(E)=\rho_{\mathrm{rel}}(E).
$$

定义**相对（谱移）密度** $\rho_{\mathrm{rel}}(E):=\xi'(E)$（a.e.）。说明：当 $(H,H_0)$ 源自同一边界三元组/半直线设定且端口 Weyl–Titchmarsh 函数 $m,m_0$ 存在时，在 a.e. $E$ 上有等价式 $\xi'(E)=\rho_m(E)-\rho_{m_0}(E)$。单通道 $S(E)=e^{2i\varphi(E)}$ 下，$\varphi'(E)=\pi\,\xi'(E)=\pi\,\rho_{\mathrm{rel}}(E)$（a.e.）。如改用"负号"约定 $\det S=e^{-2\pi i\,\xi}$，需同时置换 $\varphi\mapsto-\varphi$ 才保持该链式等价。
* **de Branges—规范系统**：完成函数 $E$ 与内函数 $U=E^\sharp/E$ 生成的 Hilbert 空间 $\mathcal H(E)$ 等价于一阶辛型规范系统；Weyl 函数即 $m$。
* **信息势与 Fisher 几何**：$\Lambda(\rho)=\log\sum_j w_j e^{\langle\beta_j,\rho\rangle}$，$p_j(\rho)=\dfrac{w_j e^{\langle\beta_j,\rho\rangle}}{\sum_\ell w_\ell e^{\langle\beta_\ell,\rho\rangle}}$，$\nabla^2\Lambda=\mathrm{Cov}_{p(\rho)}(\beta)$。

---

## 1. 主定理 I：窗口化读数与非渐近误差闭合

### 定理 1.1（窗口化读数；Nyquist–Poisson–EM 三分解）

取偶窗 $w_R(x)=w(x/R)$ 与前端核 $h\in L^1\cap L^2$。**LDOS 选择**：若需要非负主项与能量计数解释，取 $\rho_\star=\rho_m$；与相位导数/Friedel–BK 对应时，取 $\rho_\star=\rho_{\mathrm{rel}}=\xi'$（可取负）。对绝对或相对 LDOS $\rho_\star\in\{\rho_m,\rho_{\mathrm{rel}}\}$ 定义读数

$$
\mathrm{Obs}_{\Delta,T}:=\Delta\!\!\sum_{|n|\le M}\! w_R(E_n)\,[h\!\star\!\rho_\star](E_n),\quad E_n=n\Delta,\ T=M\Delta.
$$

则

$$
\mathrm{Obs}_{\Delta,T}
=\int_{\mathbb R} w_R(E)\,[h\!\star\!\rho_\star](E)\,dE
+\varepsilon_{\mathrm{alias}}+\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}},
$$

其中
（i）$\varepsilon_{\mathrm{alias}}$：由 **Poisson 求和**导致的频谱回折（aliasing）；
（ii）$\varepsilon_{\mathrm{EM}}$：**有限阶 Euler–Maclaurin** 求和公式之余项；
（iii）$\varepsilon_{\mathrm{tail}}$：窗外截断尾项。

若 $\widehat w_R$ 与 $\widehat h$ 分别带限于 $[-\Omega_w,\Omega_w]$、$[-\Omega_h,\Omega_h]$。被采样函数 $F(E)=w_R(E)\,[h\!\star\!\rho](E)$ 为**时域乘积**，由卷积定理其频谱 $\widehat F=\widehat w_R\ast(\widehat h\,\widehat\rho)$ 的支集**包含于** $[-(\Omega_w+\Omega_h),\,\Omega_w+\Omega_h]$（Minkowski 和上界），因而 $\Omega_{\mathrm{eff}}\le \Omega_w+\Omega_h$。在别名分析中，可把 $\Omega_w+\Omega_h$ 作为**充分**上界使用。**充分条件：**当采样满足

$$
\boxed{\ \Delta \le \frac{\pi}{\Omega_w+\Omega_h}\ }
$$

时，Poisson 公式中除 $k=0$ 外的折叠项全为零，故 $\varepsilon_{\mathrm{alias}}=0$（Nyquist 关断）。$\varepsilon_{\mathrm{EM}}$ 由有限阶伯努利层显式控制；$\varepsilon_{\mathrm{tail}}$ 由窗外 $L^2$ 能量给出。

**注（有效带宽，对采样变量 $E$）**：别名分析针对 $F(E)=w_R(E)\,[h\!\star\!\rho](E)$ 的**时域乘积**；其频域为**卷积** $\widehat w_R\ast\widehat h\,\widehat\rho$，故谱宽不超过 $\Omega_w+\Omega_h$（Minkowski 和上界，通常作**充分上界**使用）。这与先卷积成核 $w_R\!\star h$ 再与 $\rho$ 卷积的**连续积分**层面不同，后者涉及 $\widehat{w_R\!\star h}=\widehat w_R\,\widehat h$ 的谱宽 $\min(\Omega_w,\Omega_h)$，但那不是被采样的对象。若采样间隔 $\Delta\le \pi/(\Omega_w+\Omega_h)$，则 Poisson 折叠项除 $k=0$ 外全消失，别名误差为零；近带限时误差由出带能量与采样率共同上界。

**注（边界情形）**：**只要** $\mathrm{supp}\,\widehat F\subset(-\pi/\Delta,\pi/\Delta)$ 或在端点处为零时，$\varepsilon_{\mathrm{alias}}=0$；若仅"近带限"或端点不为零，别名随"出带能量"与采样率显式上界。

**注（近带限情形）**：当 $\widehat{w_R}$、$\widehat{h}$ 仅**近似带限**（现实中常见）时，$\varepsilon_{\mathrm{alias}}$ 由出带能量与采样率共同决定，可用 Poisson 项的非零 $k$ 尾和给出上界；理想"$\varepsilon_{\mathrm{alias}}=0$"需**严格带限 + Nyquist** 同时满足。

**证明要点.**
（a）谱侧：由 Herglotz 表示与谱定理，$[h\!\star\!\rho_\star](E)=\int h(E-E')\,d\mu_\star(E')$，$\Im m(E+i0)=\pi\rho_m(E)$，得卷积加权形式。
（b）别名（Poisson 求和，**按本文角频率规范** $\widehat f(\xi)=\int f(t)e^{-i\xi t}dt$）：$\Delta\sum_{n}F(n\Delta)=\sum_k\widehat F\!\bigl(\tfrac{2\pi k}{\Delta}\bigr)$；若 $\mathrm{supp}\,\widehat F\subset(-\pi/\Delta,\pi/\Delta)$，则仅 $k=0$ 留下。此处 $\xi$ 为**角**频率，采样点为 $2\pi k/\Delta$。
（c）EM 余项：采用到 $2p$ 阶 Euler–Maclaurin 需 $F$ 具足够阶可积导数，余项按 NIST DLMF §24.11 给出上界；有限阶 EM 不引入新奇点，仅改变端点解析数据。

### 推论 1.2（PSWF 能量浓聚与强制性）

对任意**带限函数** $f\in\mathsf{PW}_\Omega$，其在有限区间 $[-T,T]$ 的能量比例满足

$$
\int_{-T}^{T}|f|^2\le \lambda_0\,|f|_{L^2(\mathbb R)}^2,\qquad \Rightarrow\quad
|\,\mathbf 1_{|t|>T} f\,|_{L^2}^2 \ge (1-\lambda_0)\,|f|_{L^2}^2,
$$

其中 $\lambda_0\in(0,1)$ 为有限区间 Fourier 限制算子的**最大特征值**（PSWF/DPSS 第 0 阶）。据此可得误差泛函的强制性。

**注（PSWF 零点性质与能量浓聚）**：PSWF 第 $n$ 阶函数在区间 $(-1,1)$ 内恰有 $n$ 个零点（Slepian–Pollak 1961），因此**仅第 0 阶**可在有限区间内保持单符号（不变号）；高阶函数呈振荡。PSWF/DPSS 的能量浓聚与零点性质见 Slepian–Pollak–Landau 系列与后续综述，本文仅调用最基本结论。

---

## 2. 主定理 II：Born 概率 = 最小 KL 信息投影

设字典 $\{\phi_j\}\subset\mathcal H$，评估向量 $k_{s_0}$。几何侧的**最小能量 mollifier**为

$$
\min_{M\in\mathscr B}|M|^2\quad\text{s.t.}\quad \langle M,k_{s_0}\rangle=1,
$$

有限字典写 $M^\star=\sum_j\beta_j^\star\phi_j$，$\beta^\star=\dfrac{G^{-1}c}{c^\ast G^{-1}c}$，$G_{ij}=\langle\phi_i,\phi_j\rangle$，$c_j=\langle\phi_j,k_{s_0}\rangle$。

**对齐假设**：存在线性算子 $\mathcal T:\mathcal H\to\mathbb R^d$ 与自然参数族，使 $\langle M,k_{s_0}\rangle=1$ 等价为 $\mathbb E_q[\beta]=u_0$。在此**字典—约束—势函数**三者对齐下，信息与几何问题互可转写。

### 引理 2.1（Bregman–KL 恒等式）

令 $\Lambda(\rho)=\log\sum_j w_j e^{\langle\beta_j,\rho\rangle}$，$p_j(\rho)=\dfrac{w_j e^{\langle\beta_j,\rho\rangle}}{\sum_\ell w_\ell e^{\langle\beta_\ell,\rho\rangle}}$。则

$$
B_\Lambda(\rho'\mid\rho)
=\Lambda(\rho')-\Lambda(\rho)-\langle\nabla\Lambda(\rho),\rho'-\rho\rangle
=\mathrm{KL}\!\big(p(\rho)\,|\,p(\rho')\big).
$$

**标准事实**：log-partition $\Lambda$ 的 Bregman 散度即对应该指数族上的 KL 散度，且线性矩约束下的最小-KL（I-projection）给出 softmax 权。参见 Banerjee et al. (2005)、Csiszár (1975)。

### 定理 2.2（几何最小能量 $\Longleftrightarrow$ 最小 KL（I-projection））

在上述对齐下，

$$
\boxed{\
\min_{M}|M|^2\ \text{s.t.}\ \langle M,k_{s_0}\rangle=1
\ \Longleftrightarrow
\min_{q\in\Delta}\{\mathrm{KL}(q|\pi):\ \mathbb E_q[\beta]=u_0\}\ }.
$$

（**在该对齐假设下**）极小解满足 $\nabla\Lambda(\rho^\star)=u_0$，其权 $p(\rho^\star)$ 为 I-projection；当 $\tau\!\downarrow\!0$（或等价地 $\beta=1/\tau\!\uparrow\!\infty$）时，经 $\Gamma$-极限收敛到硬正交投影。

### 推论 2.3（Born 概率的 softmax 实现）

测量概率权即

$$
p_j(\rho^\star)=\frac{w_j e^{\langle\beta_j,\rho^\star\rangle}}{\sum_\ell w_\ell e^{\langle\beta_\ell,\rho^\star\rangle}},
$$

它是满足矩约束的**最小-KL**分布（I-projection），soft $\to$ hard 极限对应几何正交投影（Born）。

---

## 3. 主定理 III：指针基的谱刻画

设 $G=U\Lambda U^\ast$（$\Lambda=\mathrm{diag}(\lambda_k)$）。有

$$
\beta^\star\ \propto\ U\Lambda^{-1}U^\ast c=\sum_k\frac{\langle u_k,c\rangle}{\lambda_k}\,u_k,\qquad
|M^\star|^{-2}=c^\ast G^{-1}c=\max_{|y|=1}\frac{|c^\ast y|^2}{y^\ast G y}.
$$

默认字典线性无关且 $G\succ0$；若仅半正定，则在 $\mathrm{ran}(G)$ 上取 Moore–Penrose 逆并把 $\beta^\star$ 解释为最小范数解。

**（i）本征基与主导方向**：$\beta^\star=\sum_k \frac{\langle u_k,c\rangle}{\lambda_k}u_k$。因子 $1/\lambda_k$ 使小特征值方向被放大，但**是否主导**取决于**同时**具有足够大的投影 $|\langle u_k,c\rangle|$；对 $\beta^\star$ 贡献**最强**的方向由

$$
\arg\max_k\ \frac{|\langle u_k,c\rangle|^2}{\lambda_k}
$$

实现（Rayleigh 商）。

**（ii）信息几何对应（条件式）**：在"字典—约束—势函数"**等距对齐**（$\mathcal T$ 同构且保持二次型）时，$\nabla^2\Lambda(\rho^\star)$ 的特征方向与 $G$ 的谱向量 $\{u_k\}$ **一一对应**；一般情形仅能保证"对应关系"而非同构。此条件下，主导方向仍由上式控制。

---

## 4. 相位—密度、Wigner–Smith 时间延迟与"负延迟"的参照依赖

**先决条件（标准）**：$(H,H_0)$ 满足适当迹类/局部可积条件以保证 $S(E)$ 与 $\xi(E)$ 的 a.e. 可导，并满足 Birman–Kreĭn 公式；单通道时 $S=e^{2i\varphi}$ 给出 $\operatorname{tr}\mathsf Q=2\varphi'$，从而 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$ a.e.（Wigner 1955；Smith 1960；后续综述/推广见下文参考）。

**号记与单位**：固定 $\hbar=1$。采用 Birman–Kreĭn 的"**正号**"约定

$$
\det S(E)=e^{+2\pi i\,\xi(E)},\qquad
\Rightarrow\quad \varphi'(E)=\pi\,\xi'(E)=\pi\,\rho_{\mathrm{rel}}(E)\quad\text{(a.e.)},\quad
\mathsf Q(E)=-i\,S^\dagger\frac{dS}{dE},\ \ \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)\quad\text{(a.e.)}.
$$

如改用"负号"约定 $\det S=e^{-2\pi i\,\xi}$，需同时置换 $\varphi\mapsto-\varphi$ 才保持等式结构一致。

**参考**：Wigner–Smith 时间延迟矩阵的定义与性质见 Wigner (1955) 与 Smith (1960)；Birman–Kreĭn 公式及其与谱移函数 $\xi$ 的关系见 Yafaev (1992/2010) 与 Pushnitski (2010)，据此得 $\operatorname{tr}\mathsf Q$ 与 $\xi'$ 的关系。

### 定理 4.1（相位导数 =（相对）谱密度）

在迹类假设与 a.e. 可微下，

$$
\boxed{\ \varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)=\pi\,\xi'(E)\ }\quad\text{(a.e.)}.
$$

证明：由 $\det S(E)=e^{+2\pi i \xi(E)}$ 与 $S(E)=e^{2i\varphi(E)}$ 得 $\varphi'(E)=\pi\,\xi'(E)$；再由定义 $\rho_{\mathrm{rel}}:=\xi'$ 即得。

### 命题 4.2（Wigner–Smith 与 LDOS）

$\mathsf Q(E)=-iS^\dagger \tfrac{dS}{dE}$ 为 Hermitian（厄米）；单通道时

$$
\operatorname{tr}\mathsf Q(E)=2\,\varphi'(E)\quad\text{(a.e.)},
$$

于是

$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)\quad\text{(a.e.)}.
$$

"负延迟"来自**相对计数**与参照 $H_0$ 的选择，并不意味着因果违背。

**注（幺正性与复延迟）**：恒等式 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$ 在**幺正散射**下成立；有损/增益（次幺正）体系需用复延迟推广（Chen 等 2021）。$\mathsf Q$ 的本征值（proper delay）一般可正可负，其 Hermitian 性仅保证实谱；多通道与色散系统中出现的负值与整体因果不等式并行。

---

## 5. 窗/核最优化：强式 Euler–Lagrange、KKT 与 $\Gamma$-极限

在带限偶子空间 $\mathsf{PW}^{\mathrm{even}}_{\Omega}$ 上，定义（$K$ 为最高偶阶索引，与 §1 的采样记号 $M$ 无关）

$$
\mathcal J(w)=\sum_{j=1}^{K-1}\gamma_j\,|w_R^{(2j)}|_{L^2}^2+\lambda\,|\mathbf 1_{|t|>T}w_R|_{L^2}^2,\qquad \text{s.t.}\ w(0)=1.
$$

其一阶必要条件（频域强式）为

$$
\chi_{[-\Omega/R,\Omega/R]}(\xi)\Big(\sum_{j=1}^{K-1}\gamma_j\,\xi^{4j}\,\widehat{w_R^\star}(\xi)
+\tfrac{\lambda}{2\pi}\,(\widehat{\mathbf 1_{|t|>T}}\!\ast\!\widehat{w_R^\star})(\xi)\Big)=\eta\,\chi_{[-\Omega/R,\Omega/R]}(\xi),
$$

其中 $\widehat{\mathbf 1_{|t|>T}}=2\pi\delta-\tfrac{2\sin(T\xi)}{\xi}$（在 $\mathcal S'$ 中理解），$\eta$ 为拉格朗日乘子。

**说明（约束来源）**：约束 $w(0)=1$ 由反演公式 $w(0)=\frac{1}{2\pi}\int \widehat w(\xi)\,d\xi$ 给出，故其变分项在频域为**常数**，合并到右端的 $\eta$ 中。指数窗情形宜在时域求解以避免分布阶假设，且仍保持"极点 = 主尺度"。

**BN–Bregman 软化与 $\Gamma$-极限**：考虑 $\mathcal J(w)+\tau\,\Lambda^\ast(\mathcal Tw)$（$\tau>0$），可得唯一极小元；$\tau\downarrow0$ 时极小值与极小序列 $\Gamma$-收敛至硬约束问题。

---

## 6. 奇性保持、阈值与零点稳定半径

采用**有限阶** EM 与偶窗/核，工作条带内的奇性集合不增、极阶不升；其原因是 EM 余项可写为边界高阶导数与伯努利多项式的**解析**组合，因而不引入新奇点。具体而言，有限阶 Euler–Maclaurin 的余项可写成 $f^{(p)}$ 与周期化伯努利函数 $P_p$ 的卷积积分，因而只改变端点处的解析数据，不引入新奇点。阈值可由 $\varphi'=\pi\rho_{\mathrm{rel}}$ 的退化点识别，并用 Rouché 定理得到零点位置的稳定半径（细节从略）。

---

## 7. 实验/数值协议（可复现纲要）

**器件**：单通道势垒/量子点/微波波导。
**步骤**：
(1) **校准参照**：确定 $(H_0,H)$，由传输/反射数据经 Weyl $m$-函数或等效反演估计 $\rho_m,\rho_{m_0}$。
(2) **窗/核求解**：在 $\mathsf{PW}^{\mathrm{even}}_{\Omega}$ 或指数族内按 §5 强式方程求 $w_R^\star$。
(3) **采样账本**：记录 $(\Delta,M,T)$ 与 Nyquist 条件 $\Delta\le \pi/(\Omega_w+\Omega_h)$；EM 取有限阶并给出上界。
(4) **读数映射**：以定理 1.1 将数据还原为 $w_R$ 与 $h$ 对 $\rho_\star$ 的加权；分别对 $\rho_{\mathrm{rel}}$ 与 $\rho_m$ 读取，比较延迟符号的参照依赖。
(5) **指针/概率**：构造字典与 $G,c$，计算 $\beta^\star$、Rayleigh 商；soft 层用 $\Lambda$ 得到 $p(\rho^\star)$（Born 权）。

---

## 8. 与既有理论的关系与澄清

* **操作—信息等价**：本文并非"从零公设导出 Born"，而是给出**在真实窗/核/采样流程下**的**最小-KL ↔ Hilbert 投影**等价；hard 极限对应正交投影（Born）。
* **Wigner–Smith 与 DOS**：$\operatorname{tr}\mathsf Q/2\pi=\rho_{\mathrm{rel}}$ 来自相位—谱移—LDOS 之链；"负延迟"属相对计数效应。
* **PSWF 与最优能量集中**：带限窗的内/外能量分配由 PSWF 谱控制，支撑强制性与最优窗存在性。

---

## 9. 与 S15–S23 及量子读数理论的接口

* **S15（Weyl–Heisenberg 酉表示）**：窗族 $U_\tau V_\sigma w$ 的协变性保证读数算符在相位—尺度群下的对称性；等距性使信息势 $\Lambda$ 在群平均下保持。
* **S16（de Branges–Krein 规范系统）**：我们只用到 $m$ 为 Herglotz–Nevanlinna 函数并与某个规范系统/HB 生成函数 $E$ 对应这一事实；**不**假设 $m=-E'/E$ 的特殊形态（该式**仅在特殊情形**可成立）。传递矩阵 $M(t,z)$ 的 $J$-酉性保证 $\Im m>0$，从而 $\rho_m\ge 0$。
* **S17（散射算子与功能方程）**：定理 4.1 的 $\varphi'=\pi\rho_{\mathrm{rel}}$ 即 S17 散射相位导数判据；通道特征值等价给出 $\det S=c_0U$ 的相位—密度词典。
* **S18（轨道—谱窗化不等式）**：定理 1.1 的三分解误差与 S18 §3.3 统一非渐近上界对齐；Nyquist 条件下别名归零对应 S18 带限 Paley–Wiener 假设。
* **S19（谱图与 Ihara ζ）**：离散图的非回溯算子给出"离散相位导数 = 离散谱密度"；本文 Poisson 求和在离散设定下退化为有限和，误差仅剩 EM 层与截断。
* **S20（BN 投影—KL 代价—灵敏度）**：定理 2.2 的最小-KL ↔ 最小能量等价直接调用 S20 §2 的 Bregman–KL 恒等式；软化与 $\Gamma$-极限对应 S20 §3。
* **S21（连续谱阈值与奇性稳定性）**：本文 $\varphi'=\pi\rho_{\mathrm{rel}}$ 对应 S21 §0.2 相位—密度同一式（0.1）；阈值判据 $\varphi'=0\Leftrightarrow\rho_{\mathrm{rel}}=0$ 给出窗化读数的奇点检测。
* **S22（窗/核最优化）**：§5 的频域强式方程对应 S22 式（2.2）；BN–Bregman 软化与 $\Gamma$-极限继承 S22 定理 5.1。
* **S23（多窗/多核协同优化）**：本文单窗最优可推广至 S23 向量窗与帧算子层面；指针基判据（定理 III）对应 S23 §5 的双帧结构与 Wexler–Raz 双正交。
* **量子读数理论（phase-derivative-spectral-density-windowed-readout.md）**：本文定理 1.1 即该文 §3 的窗化迹与三分解误差；定理 4.1 对应该文定理 2.1 的相位—密度词典；本文进一步给出 Born 概率与指针基的信息几何刻画。

---

## 10. 结论

本文把量子测量统一为**窗口化读数**问题，并得到：

* **Born 概率** = **最小-KL 信息投影**（soft）；
* **指针基** = **最小能量/信息投影本征基**，其主导方向由 $\arg\max_k \frac{|\langle u_k,c\rangle|^2}{\lambda_k}$ 给出（soft/hard 一致，经 $\Gamma$-极限）；
* **延迟/隧穿** = **（相对）LDOS** 的读数；"负延迟"来自参照与相对计数；
* **实现路线**：PSWF/带限窗 + Nyquist–Poisson–EM + 变分最优，形成**非渐近、可复现**的误差闭合与设计准则。

---

## 参考文献（选）

* de Branges, **Hilbert Spaces of Entire Functions**（Purdue 公开本）。
* Wigner, **Lower Limit for the Energy Derivative of the Scattering Phase Shift**, Phys. Rev. 98, 145 (1955).
* Smith, **Lifetime Matrix in Collision Theory**, Phys. Rev. 118, 349 (1960).
* Yafaev, **Mathematical Scattering Theory** (AMS, 1992/2010).
* Pushnitski, **The spectral shift function and the invariance principle**, J. Funct. Anal. 183, 269 (2001); arXiv:math/9911182.
* Behrndt–Gesztesy–Nakamura, **Spectral shift functions and Dirichlet-to-Neumann maps**, Math. Ann. 371, 1255 (2018); arXiv:1609.08292.
* Slepian–Pollak–Landau, **Prolate Spheroidal Wave Functions**, Bell Syst. Tech. J. (1961–1964)。
* Chen et al., **Generalization of Wigner time delay to subunitary scattering systems**, Phys. Rev. E 103, L050203 (2021).
* Banerjee et al., **Clustering with Bregman Divergences**, JMLR 6, 1705 (2005)。
* Csiszár, **I-divergence geometry of probability distributions**, Ann. Probab. 3, 146 (1975)。
* Amari–Nagaoka, **Methods of Information Geometry**（AMS MMONO-191）。
* NIST DLMF §24.11：Euler–Maclaurin 余项。

---

## 附录：关键式索引（便于检索）

* **Poisson 求和（本规范 $\widehat f(\xi)=\int f(t)e^{-it\xi}dt$）**：$\Delta\sum_{n}F(n\Delta)=\sum_k\widehat F\bigl(\tfrac{2\pi k}{\Delta}\bigr)$。
* **Herglotz 边界值（与 FT 规范无关）**：$\Im m(E+i0)=\pi\rho(E)$（a.e.）。
* **相位—密度—谱移**：$\varphi'=\pi\rho_{\mathrm{rel}}=\pi\xi'$（a.e.，在标准迹类/可微条件下）。
* **时间延迟密度**：$\tfrac1{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$（a.e.，幺正散射下）。
* **窗化读数**：$\mathrm{Obs}_{\Delta,T}=\int w_R\,(h\!\star\!\rho_\star)+\varepsilon_{\mathrm{alias}}+\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}}$。
* **Nyquist 无别名**：$\Delta\le \pi/(\Omega_w+\Omega_h)$（针对采样变量 $E$ 上的 $F=w_R\cdot(h\!\star\!\rho)$，和宽）。
* **Bregman–KL（log-partition）**：$B_\Lambda(\rho'\mid\rho)=\mathrm{KL}(p(\rho)\,|\,p(\rho'))$。
* **最小能量解与主导方向**：$\beta^\star=\dfrac{G^{-1}c}{c^\ast G^{-1}c}$，$\arg\max_k \frac{|\langle u_k,c\rangle|^2}{\lambda_k}$。
* **PSWF 能量浓聚与零点**：第 $n$ 阶在 $(-1,1)$ 恰有 $n$ 个零点；$\lambda_0$ 控制区间内能量上界。
* **带限最优窗强式**：见 §5 频域方程。

（全文完）
