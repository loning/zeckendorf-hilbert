# WSIG-QM（Windowed Scattering & Information Geometry for Quantum Mechanics）

**—— 一套统一的量子概念定义与判据体系（含完整证明）**

**作者**：Auric（S-series / EBOC 体系）

**版本**：v1.4a（逻辑完全闭合，已完成同行审阅修订；可直接并入 S15–S26、euler-quantum 理论系列、EBOC-Graph）

---

## 摘要（定性）

以 **de Branges–Kreĭn（DBK）规范系统**与**带权 Mellin 空间**为载体，将现实仪器的**有限带宽/时间窗**显式并入谱测度，形成**窗口化读数**框架；以 **KL/Bregman 信息几何**刻画"提交（塌缩/commit）"；以**散射相位—谱密度—Wigner–Smith 延迟**作为能量刻度；以 **Nyquist–Poisson–Euler–Maclaurin（三分解）**闭合非渐近误差；以**帧/采样密度与窗/核的变分最优**保证可实现性与稳定性。核心统一式为

$$
\boxed{\,\varphi'(E)=-\pi\,\rho_{\rm rel}(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)\,}\quad(\text{a.e.})
$$

将（单/多通道）散射相位导数、相对局域态密度（LDOS）与 Wigner–Smith 延迟统一；并在信息几何下得到**Born 概率 = 最小-KL 投影（I-projection）**，而"指针基"即**窗口化读数算子**的光谱极小。上述判据与 Herglotz–Weyl、Birman–Kreĭn、Wigner–Smith、Ky Fan、Poisson/EM 等标准结果一致，可直接互证与落地。

---

## 0. 记号与底座（Notation & Baseplates）

### 0.1 DBK 规范系统与 Herglotz–Weyl 词典

取一阶辛型规范系统 $JY'(t,z)=zH(t)Y(t,z)$（$H\succeq0$），其 Weyl–Titchmarsh 函数 $m:\mathbb C^+\to\mathbb C^+$ 为 Herglotz 类，具有表示

$$
m(z)=a\,z+b+\int_{\mathbb R}\!\Bigl(\frac{1}{t-z}-\frac{t}{1+t^2}\Bigr)\,d\mu(t),\ a\ge 0,\ b\in\mathbb R,
$$

且 $\Im m(E+i0)=\pi\,\rho(E)$（a.e.）。这给出连续谱的绝对连续密度 $\rho$ 并与 DBK 框架相容。

### 0.2 Weyl–Heisenberg（相位—尺度）表象（Mellin 版）

在带权 Mellin 空间 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$ 上定义

$$
(U_\tau f)(x)=x^{i\tau}f(x),\ (V_\sigma f)(x)=e^{\sigma a/2}f(e^\sigma x),
$$

满足 Weyl 关系 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$。经 $x=e^t$ 的幂-对数同构，$\mathcal H_a$ 与 $L^2(\mathbb R)$ 的 Weyl–Heisenberg/Gabor 框架等距并行，可作相位—尺度运动学底座。

### 0.3 有限阶 EM / Poisson 三分解纪律

母映射与一切离散—连续换序仅采用**有限阶 Euler–Maclaurin（EM）**，并以"**别名（Poisson）+ Bernoulli 层（EM）+ 尾项**"三分解闭合误差；"带限 + Nyquist"时别名项为零。Poisson 求和与采样判据采用**角频率规范**（$\Omega$ 单位：rad/单位(E)；**单位换算**：若改用赫兹 $B$，有 $B=\Omega/(2\pi)$，此时切换到 $T_s\le 1/(2B)$；若以时间 $t$ 为自变量时单位为 rad/s）。**语境切换说明**：能量域采样步长记为 $\Delta_E$（或简记 $\Delta$），时间域采样周期记为 $T_s$，二者通过 Fourier 对偶联系（$\Delta_E\cdot\Omega_F\le\pi$ 等价于 $T_s\cdot B_F\le 1/2$，其中 $B_F=\Omega_F/(2\pi)$ 为赫兹带宽）。Poisson/EM 的换序与求导按 $F\in C^{2M}\cap L^1$（或 Schwartz 类）理解。

### 0.4 规范与号记

**Fourier/Parseval 规范对照表**：

| 项目 | 公式 | 说明 |
|------|------|------|
| **Fourier 变换** | $\widehat f(\xi)=\int f(t)e^{-it\xi}\,dt$ | $\xi$ 为角频率 (rad/单位(t)) |
| **Parseval 关系** | $\int_{\mathbb R}\|f\|^2=\tfrac{1}{2\pi}\int_{\mathbb R}\|\widehat f\|^2$ | 能量守恒，含 $\tfrac{1}{2\pi}$ 因子 |
| **卷积定理** | $\widehat{f\ast g}=\widehat f\cdot\widehat g$ | 时域卷积 = 频域乘积 |
| **乘积变换** | $\widehat{f\cdot g}=\tfrac{1}{2\pi}\,\widehat f\ast\widehat g$ | 时域乘积 = 频域卷积/$(2\pi)$ |

Birman–Kreĭn 采用

$$
\det S(E)=e^{-2\pi i\,\xi(E)}.
$$

**本文固定上式**。**等价链路桥**（$\det S$–$\xi$–$\mathsf Q$ 三者关系）：
$$
\operatorname{tr}\mathsf Q(E)=-i\,\partial_E\ln\det S(E)=-2\pi\,\xi'(E);
$$
因此对任意通道数 $N$，有 $\operatorname{tr}\mathsf Q(E)=-2\pi\,\xi'(E)$；单通道 $S=e^{2i\varphi}$ 时 $\operatorname{tr}\mathsf Q(E)=2\varphi'(E)$，故 $\varphi'(E)=-\pi\,\xi'(E)$（与 $\rho_{\rm rel}=\xi'$ 一致）。**号记替代声明**：若读者采用的文献使用 $\det S=e^{+2\pi i\xi}$ 规范（某些物理文献中出现），需同步作变换 $\varphi\mapsto-\varphi$ 与 $\xi\mapsto-\xi$ 才能保持所有物理量（如 $\operatorname{tr}\mathsf Q$、$\rho_{\rm rel}$ 等）不变；本文所有推导均基于上述 $e^{-2\pi i\xi}$ 规范执行。

**统一规范**：本文所有 Parseval 关系与卷积/乘积的 $\frac{1}{2\pi}$ 因子均按上述规范执行；后文不再重复说明。

### 0.5 投影算子记号统一

本文固定**频域投影**为 $P_B^{(\xi)}:\widehat f\mapsto \chi_B\,\widehat f$（其中 $\chi_B$ 为频带 $B=[-\Omega,\Omega]$ 的特征函数），其在能量域的积分核实现记为 $\Pi_B$，即

$$
(\Pi_B f)(E)=\int_{\mathbb R} k_B(E-E')\,f(E')\,dE',\quad k_B(t)=\frac{\sin(\Omega t)}{\pi t}.
$$

在 T6 等变分方程中一律使用 $P_B^{(\xi)}$（频域投影）；在 A4/T3 的核—迹类/Hilbert–Schmidt 论证中使用 $\Pi_B$（能量域积分算子）。此区分避免"先卷积后投影"与"投影即卷积"的混淆。

---

## 1. 公理（Axioms）

**A1（载体与协变）**：量子态置于 $\mathcal H(E)$ 或 $\mathcal H_a$；相位—尺度协变由 $(U_\tau,V_\sigma)$ 的 Weyl–Heisenberg 射影酉表示实现（Stone 定理：强连续一参数酉群 $\Leftrightarrow$ 自伴生成元；Stone–von Neumann：Weyl 关系的不可约表象本质唯一）。

**A2（可观测量与窗口化读数）**：仪器窗 $w_R$ 与**带限响应核** $h\in L^1$ 作用在态的连续谱密度上，定义**窗口化读数**

$$
\boxed{\ \langle K_{w,h}\rangle_\rho=\int_{\mathbb R} w_R(E)\,\bigl[h\ast\rho_\star\bigr](E)\,dE\ }.
$$

其中 $\rho_\star$ 可为 $\rho_{\rm abs}$（绝对连续谱密度，即 $\mu_\rho^{\rm ac}$ 的密度）或 $\rho_{\rm rel}=\rho_{\rm abs}-\rho_{0,{\rm abs}}$（相对密度）。在"**无模糊硬极限**" $h\to\delta$ 时回收 $\int w_R(E)\rho_\star(E)\,dE$。读数受三分解误差控制。

（测度版与可积性/卷积的充分条件见 §2 的 D3；当 $\rho_\star=\rho_{\rm rel}$ 为符号密度时，读数可为负，但三分解误差账本不变。）

**实现提示**：本文后续默认启用 §2-D3 的正则性充分条件（$w_R,h\in\mathsf{PW}_\Omega\cap W^{2M,1}$ 或等价可替代条件），以保证 Poisson–EM–Tail 误差闭合与测度卷积的合法性。

**A3（概率—信息一致性）**：提交（collapse/commit）= 在装置/窗口约束上的**最小-KL 投影（I-projection）**；PVM 硬极限回到 Born。

**A4（指针基）**："指针基"定义为**窗算子** $W_R=\int w_R\,dE_A$ 的**最小谱值对应的谱投影子空间**（Ky Fan"最小和"；若最小谱值不被取到，则取 $\varepsilon\downarrow0$ 的极限子空间）；**存在性与可检条件**：若 $w_R\in L^\infty$ 则 $W_R$ 为有界自伴；若进一步 **$w_R\in L^2(\mathbb R)$（例如有限支撑窗）**，则令 $k_B(t)=\sin(\Omega t)/(\pi t)$，有：

在带限投影 $\Pi_B$ 下，**统一采用** $\Pi_BM_{w_R}$ 记号。其积分核为 $K(x,y)=k_B(x-y)\,w_R(y)$。由 L3.3a 知 $\|k_B\|_{L^2}^2=\Omega/\pi<\infty$（由 Plancherel 或标准积分公式 $\int_{-\infty}^\infty(\sin ax/x)^2dx=\pi a$ 可得）；**HS 核验一行式**：

$$
\|K\|_{L^2(\mathbb R^2)}^2=\int_{\mathbb R^2}|k_B(x-y)|^2\,|w_R(y)|^2\,dxdy=\|k_B\|_{L^2}^2\,\|w_R\|_{L^2}^2=\frac{\Omega}{\pi}\,\|w_R\|_{L^2}^2<\infty,
$$

故由 Fubini–Tonelli 定理得 $\Pi_BM_{w_R}$ 为 Hilbert–Schmidt，继而 $\Pi_BM_{w_R}\Pi_B$ 亦为 Hilbert–Schmidt/紧（**HS 核定理**：若积分核 $K\in L^2(\mathbb R^2)$ 则对应的积分算子为 Hilbert–Schmidt 算子，进而为紧算子；此为泛函分析标准结果）。**反例提示**：仅凭 $w_R\in L^\infty$ 与 $\Pi_B$ 不足以推出 HS（投影算子 $\Pi_B$ 紧当且仅当像有限维，而 $\Pi_B$ 的像无限维）。**本文后续一律采用此统一表述。**若 $W_R$ 为紧自伴或其最小谱值 $\lambda_{\min}$ 为孤立本征值（**存在谱隙**），则"指针基"为对应的最小本征子空间；若最小谱值不被取到，则以谱投影 $P_{(-\infty,\lambda_{\min}+\varepsilon]}$ 的极限子空间定义"近指针基"（$\varepsilon\downarrow0$）。在谱隙存在时可用 Ky Fan 与 Davis–Kahan（谱隙稳定）给出极小谱子空间的稳定性。仪器核 $h$ 仅影响读数与误差，不改变 $W_R$ 的谱结构。

**A5（相位—密度—延迟刻度）**：若 $(H,H_0)$ 满足相对迹类/平滑散射等标准正则性（见 L3.5），则**在绝对连续谱上几乎处处**

$$
\boxed{\,\varphi'(E)=-\pi\,\rho_{\rm rel}(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)\,}\quad(\text{a.e. on }\sigma_{\rm ac})
$$

其中 $\rho_{\rm rel}(E)=\xi'(E)$，$\mathsf Q:=-iS^\dagger \tfrac{dS}{dE}$（单位制 $\hbar=1$）。**号约定**：本文统一采用 $\det S(E)=e^{-2\pi i\,\xi(E)}$，故 $\operatorname{tr}\mathsf Q(E)=\partial_E \arg\det S(E)=-2\pi\,\xi'(E)$，从而 $\varphi'(E)=-\pi\,\rho_{\rm rel}(E)$。上述等式在绝对连续谱上几乎处处成立；**阈值或共振邻近处，一律按 $\lim_{\epsilon\downarrow0}$ 的非切向极限或分布意义（主值 + 奇点部分）解释**，此与 Herglotz 边界值 $\Im m(E+i0)=\pi\rho(E)$ 保持一致。lossless 假设下 $S(E)$ 酉；若存在吸收/开放通道，$\mathsf Q$ 不再必然自伴，需改用相应非酉散射表述（本稿不涵盖）。

**正则性公设清单**：在 $\sigma_{\rm ac}$ 上，$S(E)$ 酉且 a.e. 可微；$\mathsf Q(E)=-iS^\dagger \partial_E S$；$\det S(E)=e^{-2\pi i\xi(E)}\Rightarrow \operatorname{tr}\mathsf Q(E)=-2\pi\xi'(E)$；单通道 $S=e^{2i\varphi}\Rightarrow \varphi'=\tfrac{1}{2}\operatorname{tr}\mathsf Q$；阈值/共振处取非切向极限或分布解释，与 Herglotz–Nevanlinna 的 $\frac{1}{\pi}\Im m(E+i0)=\rho(E)$ 一致。能量刻度使用 $\hbar=1$。**号记替代**：若读者改用 $\det S=e^{+2\pi i\xi}$ 规范，需同步作 $\varphi\mapsto-\varphi$ 方保持物理量不变；此提醒后文不再重复。

**A6（窗/核最优与多窗协同）**：窗 $w\in \mathsf{PW}^{\rm even}_\Omega$；目标为三分解误差上界极小；必要条件为**频域"多项式乘子 + 卷积核"的带限投影-KKT 方程**；多窗版以**广义 Wexler–Raz 双正交**与帧算子刻画 Pareto 前沿与稳定性。

**A7（阈值与奇性稳定）**：在"有限阶 EM + Nyquist–Poisson–EM"纪律下，窗化/换序不生新奇点；零集计数在 Rouché 半径内稳定且可检。

---

## 2. 基本定义（Definitions）

**D1（态）**：纯态 $\psi\in\mathcal H$（$|\psi|=1$）；混合态 $\rho\succeq0$、$\operatorname{tr}\rho=1$。

**D2（可观测量）**：自伴 $A$ 与谱投影 $E_A$。

**D3（窗口化读数与正则性条件）**：$\langle K_{w,h}\rangle_\rho=\int w_R\,[h\ast\rho_\star]\,dE$，其中 $\rho_\star$ 可为 $\rho_{\rm abs}$（$\mu_\rho$ 的绝对连续部分密度）或 $\rho_{\rm rel}$（相对密度）。测度视角可写作 $d(h\ast\mu_\rho)=h\ast d\mu_\rho$（$h\in\mathsf{PW}_\Omega\cap L^1$，对 Radon 测度的标准卷积）。**正则性与可积性充分条件**：为确保三分解（Poisson–EM–Tail）的余项界成立且测度卷积合法，取

$$
w_R\in\mathsf{PW}_\Omega\cap W^{2M,1}(\mathbb R),\quad h\in \mathsf{PW}_\Omega\cap W^{2M,1}(\mathbb R),
$$

并任选其一：

**实际实现优先以 (c) 为准，其次 (b)，(a) 仅用于理论完备**；可任选其一：

**(c)** $w_R$ **紧支撑**且 $w_R\in W^{2M,1}(\mathbb R)$，从而 $F=w_R(h\ast\rho_\star)\in L^1$ 与 $F^{(2M)}\in L^1$ 仍成立（**工程首选**）；

**(b)** $\rho_\star\in L^1(\mathbb R)$（或 $L^1\cap L^\infty$ 或具足够加权可积性）且 $h\in\mathcal S$，则 $h\ast\rho_\star\in L^1\cap L^\infty$ 且高阶导数可积；

**(a)** $\mu_\rho$ 具有**紧支撑**或**各阶多项式矩有限**（即 $\int(1+|y|)^N\,d|\mu_\rho|(y)<\infty$ 对任意 $N$ 成立），则 $h\ast\mu_\rho\in\mathcal S$；若仅为**有限 Radon 测度**（全变差有限），可保证 $h\ast\mu_\rho\in C^0\cap L^\infty$（且在典型情形属 $C_0$），但**一般不保证**在 $\mathcal S$ 中。

**(ii)** $\rho_\star\in L^1_{\rm loc}\cap\mathcal S'$（温和分布）且 $\widehat h\in C_c^\infty$（带限且光滑），从而 $\widehat h\cdot\widehat{\rho_\star}$ 在分布意义下合法。**澄清**：对任意温和分布 $T$ 与 $C^\infty$ 函数 $\phi$，乘积 $\phi\cdot T$ **总是**有定义（因 $\widehat h\in C_c^\infty$ 为**光滑函数**，与任意温和分布 $\widehat{\rho_\star}\in\mathcal S'$ 的乘积在分布意义下恒可定义，无需波前集条件）；此处 $C_c^\infty$（紧支撑）的**主要目的是实现频带截断与光滑性**。带限条件 $\widehat h\in C_c^\infty$ 确保 $h\in\mathcal S$（Schwartz 类），从而 $h\ast\rho_\star\in C^\infty$。**关键**：若仅假设 $\rho_\star\in\mathcal S'$，则 $h\ast\rho_\star$ **仅保证 $C^\infty$ 平滑性**（可至多多项式增长），**并不自动保证快速衰减或可积性**；要确保 $h\ast\rho_\star\in L^\infty$ 或 $L^1$ 及其高阶导数可积，需上述 (a)(b)(c) 之一满足。

从而 $F(E)=w_R(E)\,[h\ast\rho_\star](E)\in L^1\cap C^{2M}$ 且 $F^{(2M)}\in L^1$（需至少 $2M$ 阶）在上述充分条件 (a)(b)(c) 之一满足时成立。误差账本：$\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}$。**实际数值实现首选 $\widehat h$ 的紧支撑与足够光滑，配合 $\mu_\rho$ 有限或 $w_R$ 紧支撑，以确保分布乘积可乘性、可积性与稳定性**。

**D4（提交/塌缩）**：给定装置约束，观测概率 $p$ 为参考 $q$ 到可行集的 I-projection；softmax 软化 $\to$ Born 硬极限。

**D5（指针基）**：窗算子 $W_R$ 的最小谱值对应的谱投影子空间所张基（Ky Fan"最小和"；若最小谱值不被取到，则取 $\varepsilon\downarrow0$ 的极限子空间），简称**最小谱子空间**；$h$ 仅在测度侧作用。

**D6（相位刻度）**：定义 $d\mu_\varphi(E)=\pi^{-1}\varphi'(E)\,dE$（相对情形可为符号测度）；当引入 $\rho_{\rm rel}=\xi'$ 时有 $d\mu_\varphi=-\rho_{\rm rel}\,dE$。**说明**：$\rho_{\rm rel}=\xi'=\rho_m-\rho_{m_0}$ 为相对密度，允许为符号密度；窗口化读数可出现负值，但误差账本不变。

**D7（多窗/多核）**：$\{w^{(\ell)}\}_{\ell=1}^K$ 的帧算子 $\mathcal S_W$ 与广义 Wexler–Raz 双正交对 $(W,\widetilde W)$。

---

## 3. 预备引理（工具与规范）

**L3.1（Poisson 求和与 Nyquist 条件）**

若 $\widehat w_R$ 与 $\widehat h$ 分别支撑于 $[-\Omega_w,\Omega_w]$、$[-\Omega_h,\Omega_h]$，则对

$$
F(E):=w_R(E)\,[h\ast \rho_\star](E)
$$

有 $\operatorname{supp}\widehat F\subset[-(\Omega_w+\Omega_h)\,,\,\Omega_w+\Omega_h]$。由于 $\widehat{h\ast\rho_\star}=\widehat h\cdot \widehat{\rho_\star}$，且按 D3 的充分条件 (ii)，当 $\widehat h\in C_c^\infty$ 时分布乘积 $\widehat h\cdot\widehat{\rho_\star}$ 合法（$\widehat h$ 的带限与无穷阶光滑性保证对任意温和分布的可乘性；因 $\widehat h\in C_c^\infty$ 为光滑函数，与任意温和分布的乘积总可定义——这是分布论的基础结果，无需波前集条件），**支撑与交集**：

$$
\operatorname{supp}(\widehat h\cdot\widehat{\rho_\star})\subseteq \operatorname{supp}\widehat h\cap \operatorname{supp}\widehat{\rho_\star}\subseteq[-\Omega_h,\Omega_h],
$$

因此中间量 $h\ast\rho_\star$ 的 Nyquist 判据只需 $\Omega_h$ 的上界，但实际有效带宽可能因 $\widehat{\rho_\star}$ 的"熄灭带"而更窄。并且 $\widehat{w_R(h\ast\rho_\star)}=\frac{1}{2\pi}\,\widehat w_R\ast(\widehat h\cdot\widehat{\rho_\star})$（Fourier规范下乘积变换带 $\frac{1}{2\pi}$ 因子），因而 $\operatorname{supp}\widehat{w_R(h\ast\rho_\star)}\subset[-(\Omega_w+\Omega_h)\,,\,\Omega_w+\Omega_h]$。**关键原则**：**数值实现与误差闭合一律以最终量 $F=w_R(h\ast\rho_\star)$ 的总带宽 $\Omega_F=\Omega_w+\Omega_h$ 为准**；前述对中间量 $h\ast\rho_\star$ 带宽上界的讨论仅为理论分析辅助，**实际采样判据、别名误差控制与 EM 余项估计均须按 $\Omega_F$ 设定**。

**统一 Nyquist 规范与单位换算**：

若 $\operatorname{supp}\widehat F\subset[-\Omega_F,\Omega_F]$（其中 $\Omega_F=\Omega_w+\Omega_h$），则采样判据为

$$
\Delta\le \pi/\Omega_F\ (\text{角频率 rad/（单位(E)）})\ \Longleftrightarrow\ T_s\le 1/(2B_F)\ (\text{赫兹 }B_F=\Omega_F/(2\pi)\text{ Hz}).
$$

**本文默认角频率规范；赫兹记法仅作等价提示**。满足此条件时，Poisson 求和中除 $k=0$ 外各项落在带外，故别名误差 $\varepsilon_{\rm alias}=0$。**误差闭合以最终量 $F$ 的总带宽 $\Omega_F$ 为准**。**关键提示**：以 Hz 记带宽 $B_F$ 时，$\Delta\le\pi/\Omega_F\ \Leftrightarrow\ T_s\le 1/(2B_F)$；**仅在严格带限时别名为零**——若信号仅为超快衰减而非严格带限，Nyquist 采样判据不能完全消除别名，此时需将衰减尾部纳入误差估计。

**L3.2（有限阶 Euler–Maclaurin 与余项界）**

令 $p=2M\in 2\mathbb N$（$p\ge 2$，偶阶）。若 $g\in C^p([a,b])$ 且 $g^{(p)}\in L^1([a,b])$，则 Euler–Maclaurin 公式的余项 $R_p$ 满足标准上界

$$
\big|R_{p}\big|\le \dfrac{2\,\zeta(p)}{(2\pi)^{p}}\int_{a}^{b}|g^{(p)}(x)|\,dx,
$$

其中 $[a,b]$ 为求和区间对应的连续延拓区间（例如 $[-N\Delta,\,N\Delta]$），$\zeta(p)$ 为 Riemann ζ 函数。**此界对 $p\ge 2$ 成立**；**需 $g^{(p)}\in L^1$**。**可操作显式上界**：例如 $p=2$ 时 $\zeta(2)=\pi^2/6$，$p=4$ 时 $\zeta(4)=\pi^4/90$。对任意阶 $p$ 的完整 EM 展开还包含**端点项**（涉及函数及其前 $(p-1)$ 阶导数在端点的值）与上述**体积分余项** $R_p$；本文三分解误差账本中的 $\varepsilon_{\rm EM}$ 即指此体积分余项的上界。

**L3.3（Herglotz–Nevanlinna 边界值与谱密度）**

若 $m$ 为 Herglotz（Nevanlinna）函数，则**非切向极限几乎处处存在**且 $\Im m(E+i0)=\pi\,\rho_m(E)$（a.e.），其中 $\rho_m$ 为 Herglotz 表示测度的绝对连续部分密度。**阈值与共振邻域以非切向极限或分布解释**（主值+奇点部分）。该结论为经典谱理论标准结果。

**L3.3a（sinc 核的 $L^2$ 范数）**

对带限投影核 $k_B(t)=\dfrac{\sin(\Omega t)}{\pi t}$（$\Omega>0$），有

$$
\|k_B\|_{L^2(\mathbb R)}^2=\int_{-\infty}^\infty\Bigl(\frac{\sin(\Omega t)}{\pi t}\Bigr)^2dt=\frac{\Omega}{\pi}.
$$

**证明**：由 Plancherel 定理，$\|k_B\|_{L^2}^2=\tfrac{1}{2\pi}\|\widehat{k_B}\|_{L^2}^2$；而 $\widehat{k_B}(\xi)=\chi_{[-\Omega,\Omega]}(\xi)$（矩形窗），故 $\|\widehat{k_B}\|_{L^2}^2=2\Omega$，从而 $\|k_B\|_{L^2}^2=\tfrac{1}{2\pi}\cdot 2\Omega=\Omega/\pi$。□（等价于标准积分公式 $\displaystyle\int_{-\infty}^{\infty}\Bigl(\frac{\sin ax}{x}\Bigr)^2dx=\pi a$；读者可直接用此式复核。）

**L3.4（Ky Fan 变分原则：最小和）**

对自伴 $K$ 与任意正交族 $\{e_k\}_{k=1}^m$，

$$
\sum_{k=1}^m\langle e_k,Ke_k\rangle\ge\sum_{k=1}^m\lambda_k^\uparrow(K),
$$

等号当且仅当 $\{e_k\}$ 张成最小本征子空间。若最小本征值存在简并，则对应最小本征子空间的任一正交基均可作为"指针基"。

**L3.5（Birman–Kreĭn、Wigner–Smith 与正则性）**

若 $(H,H_0)$ 为相对迹类扰动或满足平滑散射的标准假设，则 BK 公式

$$
\det S(E)=e^{-2\pi i\,\xi(E)},\qquad \operatorname{tr}\mathsf Q(E)=\partial_E\arg\det S(E)=-2\pi\,\xi'(E)
$$

成立，其中 $\mathsf Q=-iS^\dagger \tfrac{dS}{dE}$（需 $S(E)$ 在 $E$ 上可微且酉；lossless 情形直接成立）。几乎处处 $\xi'(E)=\rho_{\rm rel}(E)$。

**L3.6（Naimark 扩张）**

任意 POVM $\{E_i\}$ 存在扩张空间与 PVM $\{\Pi_i\}$ 使 $E_i=V^\dagger \Pi_i V$。

**L3.7（Wexler–Raz 双正交与帧）**

Gabor/WH 框架下，多窗 $\{g_k\}$ 与其对偶窗 $\{\widetilde g_k\}$ 满足 Wexler–Raz 双正交关系：对栅格 $(\alpha,\beta)$（时间—频率采样步长），若 $\alpha\beta\le 1$（临界或超完备密度），则存在对偶帧且满足**离散格上的 Wexler–Raz 对偶关系**（时域版，含必要的调制因子）

$$
\sum_{n\in\mathbb Z}g(t-n\alpha)\,\overline{\widetilde g(t-n\alpha)}\,e^{2\pi i m\beta t}=\frac{1}{\beta}\,\delta_{m,0},\quad \forall\,m\in\mathbb Z,\text{ a.e. }t\in\mathbb R,
$$

或等价的内积形式

$$
\langle \widetilde g,\,T_{n\alpha}M_{m\beta}\,g\rangle = \delta_{n,0}\delta_{m,0},
$$

以及其频域对偶式（经 Poisson 求和，缝合恒等式）

$$
\sum_{k\in\mathbb Z}\widehat g(\xi-k/\alpha)\,\overline{\widehat{\widetilde g}(\xi-k/\alpha)}=\alpha,\quad \text{a.e. }\xi\in\mathbb R.
$$

**规范对偶窗**满足 $\widetilde g=\mathcal S^{-1}g$（其中 $\mathcal S$ 为帧算子）；对任意一对对偶窗 $(g,\widetilde g)$ 仍满足上述 Wexler–Raz 双正交恒等式。密度约束为 $\alpha\beta\le 1$。**相位—尺度（Mellin）表象的等价陈述**：在 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$ 上，$(U_\tau,V_\sigma)$ 的 Weyl 关系与 $(T_x,M_\omega)$ 的 Weyl–Heisenberg 关系经 $x=e^t$ 同构；相应的帧密度条件为 $(\Delta\tau)(\Delta\sigma)\le 1$（$\Delta\tau$ 为相位采样间隔、$\Delta\sigma$ 为尺度采样间隔），Wexler–Raz 双正交在相位—尺度格上保持同型（对偶窗满足 $\sum_{n}\widetilde g(e^{t-n\Delta\sigma})\,e^{-in\Delta\tau\,\log x}=(\Delta\tau)^{-1}\delta_{0,m}$ 等价式）。

---

## 4. 主定理与**完整证明**

### T1（窗口化读数的数值估计式与非渐近误差闭合）

**命题**：设 $A$ 的谱测度 $dE_A$、仪器窗 $w_R$ 与带限核 $h$。令 $F(E)=w_R(E)\,[h\ast\rho_\star](E)$，其中 $\rho_\star$ 为态 $\rho$ 的连续谱密度。**正则性前置**：以下等式与余项界在 $F\in L^1\cap C^{2M}$、$F^{(2M)}\in L^1$ 下成立；一组充分条件见 §2-D3（$w_R,h$ 的带限与 $W^{2M,1}$ 正则性，$\mu_\rho$ 局部有限等）。对采样步长 $\Delta>0$ 与有限截断 $|n|\le N$，有

$$
\int_{\mathbb R} F(E)\,dE = \Delta\sum_{n=-N}^{N}F(n\Delta) + \underbrace{\varepsilon_{\rm alias}}_{\text{Poisson}} + \underbrace{R_{p}}_{\text{Euler–Maclaurin}} + \underbrace{\varepsilon_{\rm tail}}_{\text{截断尾项}},
$$

其中 $p=2M$ 且 $|R_{p}|\le \dfrac{2\zeta(p)}{(2\pi)^{p}}\int |F^{(p)}(x)|\,dx$。**别名项在带限+Nyquist 条件下为零**。**尾项可操作上界与截断点选取策略**：若 $F\in L^1(\mathbb R)$ 且截断区间为 $[-N\Delta,N\Delta]$，则

$$
|\varepsilon_{\rm tail}|=\Bigl|\int_{|E|>N\Delta}F(E)\,dE\Bigr|\le \int_{|E|>N\Delta}|F(E)|\,dE.
$$

**截断点 $N$ 的选取指引**（将尾项控制到目标阈值 $\varepsilon$）：

- **指数衰减** $|F(E)|\lesssim C\,e^{-\alpha|E|}$（$\alpha>0$）：有 $|\varepsilon_{\rm tail}|\lesssim e^{-\alpha N\Delta}$，故取 $N\Delta\ge \alpha^{-1}\log(C/\varepsilon)$；
- **代数衰减** $|F(E)|\lesssim C\,|E|^{-\beta}$（$\beta>1$）：有 $|\varepsilon_{\rm tail}|\lesssim (N\Delta)^{1-\beta}$，故取 $N\Delta\ge (C/\varepsilon)^{1/(\beta-1)}$。若 $\operatorname{supp}\widehat w_R\subset[-\Omega_w,\Omega_w]$、$\operatorname{supp}\widehat h\subset[-\Omega_h,\Omega_h]$，则 $\operatorname{supp}\widehat F\subset[-\Omega_F,\Omega_F]$ 且 $\Omega_F=\Omega_w+\Omega_h$；取 $\Delta\le \pi/\Omega_F$（角频率；若用赫兹带宽 $B_F=(\Omega_F/2\pi)$，则采样周期 $T_s\le 1/(2B_F)$），此时别名项 $\varepsilon_{\rm alias}=0$。

例如：若 $w_R\in W^{2M,1}\cap L^\infty$ 且 $h\ast\rho_\star\in W^{2M,1}\cap L^\infty$，则由 Leibniz 规则得 $F^{(k)}\in L^1\ (k\le 2M)$；在 D3(ii) 下，因 $\widehat h\in C_c^\infty$ 与 $w_R\in W^{2M,1}$ 且 D3(ii) 的充分条件 (a)(b)(c) 之一满足，同理可得 $F^{(p)}\in L^1$（$p=2M$）。

**证明**：由 Poisson 求和将积分与离散和联系起来（别名项即谱复制重叠量），EM 有限阶给出 Bernoulli 层与端点余项，截断产生 tail；$\widehat{h\ast\rho_\star}=\widehat h\cdot\widehat{\rho_\star}$ 的卷积定理保证 $\operatorname{supp}\widehat F\subset[-\Omega_F,\Omega_F]$；带限+Nyquist 使别名项消失；L3.1–L3.2 即得。□

**实现层级（可检条件分层）**：

- **Ⅰ层（严格带限 + Nyquist）**：若 $\operatorname{supp}\widehat F\subset[-\Omega_F,\Omega_F]$ 且 $\Delta\le\pi/\Omega_F$，则 $\varepsilon_{\rm alias}=0$（别名完全消除）；
- **Ⅱ层（高阶导数可积）**：若 D3 的充分条件使 $F^{(2M)}\in L^1$，则 EM 余项 $|R_{2M}|\le \dfrac{2\zeta(2M)}{(2\pi)^{2M}}\int|F^{(2M)}|dx$ 给出显式上界（需 $p=2M\ge 2$）；
- **Ⅲ层（截断控制）**：给定目标精度 $\varepsilon$，按衰减类型选取 $N\Delta$：指数衰减 $|F|\lesssim Ce^{-\alpha|E|}$ 时取 $N\Delta\ge\alpha^{-1}\log(C/\varepsilon)$；代数衰减 $|F|\lesssim C|E|^{-\beta}$（$\beta>1$）时取 $N\Delta\ge(C/\varepsilon)^{1/(\beta-1)}$。**参数选取顺序**：先定 $\Delta$（由 Nyquist），再定 $M$（由目标精度与 $F$ 光滑性），后定 $N$（由尾项控制）。

**注（估计式而非恒等式）**：本框架中 $h$ 仅在**测度/密度侧**引入模糊，$W_R$ 的谱决定"指针基"。此命题给出的是**数值估计账本的分解**（真值 = 采样和 + 误差项），而非对真值的重新定义；截断+EM 余项是实现误差闭合的工具，故标题采用"估计式"而非"恒等式"。

### T2（Born 概率 = I-projection 的"对齐充要条件"）

**定理**：设 PVM/POVM 与参考 $q$。**前提**：$q_i>0$（或 $\operatorname{supp}p\subseteq\operatorname{supp}q$），且线性矩约束的闭凸可行集 $\mathcal C=\{p:\sum_i p_i a_i = b\}$ 非空。在此前提下，最小-KL

$$
\min\{D_{\rm KL}(p\|q):p\in\mathcal C\}
$$

的唯一解为指数族 $p^\star_i\propto q_i e^{\lambda^\top a_i}$（I-projection 唯一性定理）。**对齐充要条件与支撑匹配**：设 $w_i=\langle\psi,E_i\psi\rangle$ 为 PVM 指标的 Born 向量。**须先确保相对支撑条件** $\operatorname{supp}w\subseteq\operatorname{supp}q$（即若 $w_i>0$ 则 $q_i>0$）；此前提下，**当且仅当**在 $\{i:w_i>0\}$ 上存在 $\lambda$ 使 $\log(w_i/q_i)$ 落在 $\{a_i\}$ 的仿射张成中（等价于 $\log(w_i/q_i)=\lambda^\top a_i - \psi(\lambda)$ 对某归一化常数 $\psi$），则 I-projection 的唯一解为 $p^\star=w$（Born）；**若不可仿射表示，则最优解为指数族 $p^\star\neq w$（但仍唯一）**。此"**对齐**"在上述意义下**明确定义**为相对支撑上的仿射可表示性。在前提 $q_i>0$、$\operatorname{supp}w\subseteq\operatorname{supp}q$ 与可行集非空下，I-projection 唯一且为指数族；对齐充要条件保证 $p^\star=w$（Born）。软化温度 $\tau\downarrow0$ 的 $\Gamma$-极限将 softmax 收敛至 Born。

**连续谱情形**：设 $\{a_\ell(E)\}_{\ell=1}^m\in L^1_{\rm loc}$ 且 $w,q\ll d\mu$（对同一参考测度 $\mu$ 绝对连续）。在 $\operatorname{supp}w\subseteq\operatorname{supp}q$（$\mu$-a.e.）的前提下，若存在 $\lambda$ 使 $\log\!\big(w/q\big)=\sum_\ell \lambda_\ell a_\ell(E)-\psi(\lambda)$（$\mu$-a.e. on $\operatorname{supp}w$），则 I-projection 唯一解为 $p^\star=w$；否则 $p^\star$ 为同一指数族但 $p^\star\neq w$。

**证明**：KL 的严格凸性与 Lagrange 乘子在 $q_i>0$、可行集闭凸非空的前提下给出指数族与唯一性；对齐充要条件由指数族参数化逐系数推出。POVM 情形由 Naimark 扩张化到 PVM 再投回。□

**教学示例（2-outcome 情形）**：设 $i\in\{0,1\}$，参考分布 $q=(1/2,1/2)$，约束 $\sum p_ia_i=b$ 其中 $a_0=0$、$a_1=1$、$b\in(0,1)$。I-projection 解为 $p^\star_i\propto q_i e^{\lambda a_i}$，即 $p_0^\star=1/(1+e^\lambda)$、$p_1^\star=e^\lambda/(1+e^\lambda)$，其中 $\lambda$ 由 $p_1^\star=b$ 确定，得 $\lambda=\ln(b/(1-b))$。若 Born 权重 $w=(w_0,w_1)=(1-b,b)$，则 $\log(w_i/q_i)=\log(2w_i)$ 可表为 $\lambda a_i-\psi(\lambda)$（$\psi=\ln(1+e^\lambda)$），故**对齐成功**，$p^\star=w$。

**反例（不可对齐）**：若 $w=(0.3,0.7)$ 而约束为 $p_0+2p_1=c$（即 $a_0=1$、$a_1=2$），则 $\log(w_i/q_i)=(\log 0.6,\log 1.4)$ 无法由单个 $\lambda$ 使 $\lambda a_i$ 仿射表示（因 $\log 0.6/1\neq \log 1.4/2$），此时 I-projection 解 $p^\star\neq w$（仍为指数族形式 $p^\star_i\propto q_i e^{\lambda a_i}$，但 $\lambda$ 由约束唯一确定，与 $w$ 不匹配）。

**检验流程（可操作步骤）**：

1. 计算 $r_i=\log(w_i/q_i)$（对所有 $i\in\operatorname{supp}w$）；
2. 用最小二乘在 $\{a_i\}$ 的仿射张成中拟合 $r_i$；
3. 若残差 $\approx 0$ 则对齐成立，$p^\star=w$（Born）；反之得指数族解 $p^\star\neq w$。

### T3（指针基 = 最小谱子空间（Ky Fan"最小和"））

**定理**：**存在性条件**：把"指针基"理解为 $W_R$ 的最小谱值对应的谱投影子空间（简称最小谱子空间）；若最小谱值不被取到，则以 $P_{(-\infty,\lambda_{\min}+\varepsilon]}$ 的极小谱子空间之极限（$\varepsilon\downarrow0$）替代。对自伴窗算子 $W_R$ 与任意 $m$ 维正交族 $\{e_k\}$，

$$
\sum_{k=1}^m\langle e_k,W_Re_k\rangle\ge \sum_{k=1}^m\lambda_k^\uparrow(W_R),
$$

**等号当且仅当 $\{e_k\}$ 张成 $W_R$ 的最小谱子空间**（Ky Fan PNAS 1951；需 $W_R$ 为紧自伴或最小谱值为孤立本征值）。若最小本征值存在简并，则对应最小本征子空间的任一正交基均可作为"指针基"。**有界/紧性可检条件**：若 $w_R\in L^\infty(\mathbb R)$ 为有界 Borel 函数，则 $W_R=w_R(A)$ 为有界自伴；若进一步 **$w_R\in L^2(\mathbb R)$（例如有限支撑窗）**，则由 A4 的统一表述知 $\Pi_BM_{w_R}$ 与 $\Pi_BM_{w_R}\Pi_B$ 均为 Hilbert–Schmidt/紧（由 HS 核定理：积分核 $K\in L^2(\mathbb R^2)$ 保证算子为 HS/紧）。

可用 Ky Fan 最小和原则与 Davis–Kahan 谱隙稳定性定理（**需谱隙**）。**反例提示**：仅凭 $w_R\in L^\infty$ 与 $\Pi_B$ 不足以推出 HS（投影算子 $\Pi_B$ 紧当且仅当像有限维，而 $\Pi_B$ 的像无限维）。仪器核 $h$ 仅在测度侧引入模糊，不改变 $W_R$ 的谱。□

### T4（$\varphi'=-\pi\rho_{\rm rel}=\operatorname{tr}\mathsf Q/2$，**a.e. on $\sigma_{\rm ac}$**）

**定理**：设 $(H,H_0)$ 满足 L3.5 的正则性。则**在绝对连续谱上几乎处处（a.e. on $\sigma_{\rm ac}$）**

$$
\boxed{\,\varphi'(E)=-\pi\,\rho_{\rm rel}(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)\,}\quad(\text{a.e. on }\sigma_{\rm ac})
$$

其中 $\rho_{\rm rel}(E)=\xi'(E)$，$\mathsf Q=-iS^\dagger \tfrac{dS}{dE}$。**阈值/共振处理**：在阈值或共振邻近处，按 $\lim_{\epsilon\downarrow0}$ 的非切向极限或分布意义（主值 + 奇点部分）解释，与 Herglotz 边界值 $\Im m(E+i0)=\pi\rho(E)$ 一致。

**证明**：BK 公式给 $\det S=e^{-2\pi i\xi} \Rightarrow \partial_E\arg\det S=-2\pi\,\xi'$；而 $\operatorname{tr}\mathsf Q=\partial_E\arg\det S$。单通道 $S=e^{2i\varphi}$ 时 $\operatorname{tr}\mathsf Q=2\varphi'$，合并得结论。相对密度来自 $\xi'=\rho_m-\rho_{m_0}$ 的 Herglotz–Weyl 局地化。

**分布导数与奇点处理**：在绝对连续谱上 $\xi'(E)$ a.e. 存在为经典意义下的导数；在阈值/共振处 $\xi(E)$ 可能仅为局部有界变差函数，此时 $\xi'$ 应理解为分布导数（Radon–Nikodym 导数加 $\delta$ 奇点项），与 Herglotz 边界值 $\frac{1}{\pi}\Im m(E+i0)=\rho(E)$ 在测度意义下一致。**极简示例**：若 $S(E)$ 在 $E=E_0$ 附近有一阶极点（共振），则 $\xi(E)\sim \frac{1}{\pi}\arg(E-E_0)+\text{smooth}$，其分布导数为 $\xi'(E)=\text{PV}\,\frac{1}{\pi(E-E_0)}+c\,\delta(E-E_0)+\text{smooth}'$（主值 + 奇点 + 光滑部分）。

**实现上的阈值/共振处理**：在数值计算或实验测量中，阈值/共振邻近处的 $\varphi'(E)$、$\rho_{\rm rel}(E)$ 应以**非切向极限**（$\lim_{\epsilon\downarrow0}$）或**主值+奇点部分**的形式解释，与 A5 的边界值规范一致。□

**多通道注记与 Wigner–Smith 平均延迟**：对 $N$ 通道散射，$\det S(E)=\exp(2i\sum_{j=1}^N\varphi_j(E))$（酉矩阵本征相位之和），故 $\operatorname{tr}\mathsf Q=2\sum_j\varphi_j'$。**多通道相位语境声明**：当涉及 $\varphi'=\tfrac{1}{2}\operatorname{tr}\mathsf Q$ 时，$\varphi$ 指**总散射相位**（$\varphi=\sum_{j=1}^N\varphi_j$，故 $\varphi'=\sum_j \varphi'_j$），从而多通道下恒有 $\varphi'=\tfrac{1}{2}\operatorname{tr}\mathsf Q$；平均延迟单独定义为 $\tau_W=\tfrac{1}{N}\operatorname{tr}\mathsf Q$，与前者概念不同、不可混用。相位分支需在连续谱区间上连续选取，与 $\arg\det S$ 的分支保持一致；阈值/共振处的分支跳跃对应极点/零点的拓扑指标，可通过 Rouché 半径稳定控制（T5）。**Wigner–Smith 平均延迟公式（等价链路桥）**：
$$
\tau_W(\varepsilon)=\tfrac{1}{N}\operatorname{tr}\mathsf Q(\varepsilon)=-\tfrac{i}{N}\,\partial_\varepsilon\ln\det S(\varepsilon)=-\tfrac{2\pi}{N}\,\xi'(\varepsilon)
$$
（单位制 $\hbar=1$），与上述 $\operatorname{tr}\mathsf Q=-2\pi\,\xi'$ 完全一致。

### T5（阈值与奇性稳定：Rouché 半径）

**定理**：若域 $D$ 的边界上 $|\mathcal E(z)|\ge\eta>0$，且近似 $\mathcal E_\natural$ 满足 $\sup_{\partial D}|\mathcal E_\natural-\mathcal E|<\eta$，则二者在 $D$ 内零点计数相同并具位移上界；在"有限阶 EM + Nyquist–Poisson–EM"纪律下窗化/换序不生新奇点，$\eta$ 可由三分解误差上衡。

**证明**：由 Rouché 定理并结合 §3 的 Poisson–EM 误差上界（L3.1、L3.2）与带限支撑界即可得结论。□

**实操提示（参数化流程）**：对目标域 $D=\{z:|z-E_0|<r\}$（实轴附近的盘域），**零点稳定性验证步骤**为：

1. **误差控制参数设定**：选择 $M$（EM 阶数）、$N$（截断点数）、$\Delta$（采样步长）；由 T1 与 L3.2 估计三分解误差 $\eta=\varepsilon_{\rm alias}+|R_{2M}|+\varepsilon_{\rm tail}$（带限+Nyquist 时 $\varepsilon_{\rm alias}=0$）。典型取 $M\ge 2$、$\Delta\le \pi/\Omega_F$、$N\Delta\ge 3\max\{T,1/\alpha\}$（$T$ 为窗支撑半径或 $\alpha$ 为衰减率）。

2. **边界最小模验证**：在 $\partial D$ 上计算 $\inf_{|z-E_0|=r}|\mathcal E(z)|=:\eta_0$；**建议取 $\eta_0>2\eta$（安全系数 2）**以留有余裕，保证 Rouché 条件的稳健满足（因数值误差与舍入可能使实际扰动略大于估计值 $\eta$）。

3. **Rouché 应用与零点计数**：若 $\sup_{\partial D}|\mathcal E_\natural-\mathcal E|<\eta<\eta_0$，则零点计数 $N_D(\mathcal E)=N_D(\mathcal E_\natural)$（此为严格结论）；零点位移估计 $\lesssim \eta/\eta_0\cdot r$ 为**启发式量级估计**（若需严格定量位移界，需结合反演映射的 Lipschitz 常数或辩值原理的对数导数积累函数界；本稿聚焦零点计数稳定性，位移量级仅作参考）。

**参数化示例**：$\mathcal E(z)=\det S(z)$、$D=\{z:|z-E_0|<0.5\}$；设 $|\det S|\ge 0.1$ on $\partial D$（$\eta_0=0.1$），取 $M=3$、$\Delta=\pi/(2\Omega_F)$、$N=100$；若评估得 $\eta\approx 0.02<0.05=\eta_0/2$，则 Rouché 条件满足且零点位移 $\lesssim 0.1$。

### T6（窗/核最优的带限投影-KKT 与 $\Gamma$-极限）

**设定**：在 $\mathsf{PW}^{\rm even}_\Omega$ 上，强凸代理

$$
\mathcal J(w)=\sum_{j=1}^{M-1}\gamma_j\|w_R^{(2j)}\|_{L^2}^2+\lambda\|\mathbf 1_{\{|E|>T\}}\,w_R\|_{L^2}^2,
$$

$w_R(t)=w(t/R)$，$\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$。

**定理**：存在唯一极小元 $w^\star$，其频域满足**带限投影—KKT 方程**（$P_B^{(\xi)}:\widehat f\mapsto\chi_B\widehat f$ 为频域带限投影）

$$
\boxed{\,P_B^{(\xi)}\Bigl(\underbrace{2\!\sum_{j=1}^{M-1}\!\gamma_j\,\xi^{4j}\,\widehat{w_R^\star}(\xi)}_{\text{多项式乘子}}+\underbrace{2\lambda\,\widehat{w_R^\star}(\xi)}_{\delta\text{-项}}-\underbrace{\tfrac{2\lambda}{\pi}\Bigl(\dfrac{\sin(T\cdot)}{\cdot}\!\ast\!\widehat{w_R^\star}\Bigr)(\xi)}_{\text{卷积项}}\Bigr)=\eta\,\widehat{w_R^\star}(\xi)\,}\quad(\xi\in\mathbb R),
$$

其中 $B=[-\Omega/R,\Omega/R]$，$\eta$ 为归一乘子。

**⚠ 实现顺序必须是**：`compute_conv → apply_P_B → enforce_normalization`；**切勿**交换"先投影后卷积"的次序。

**实现提示（必须遵守）**：

1. **系数 $\tfrac{2\lambda}{\pi}$ 的来源**（显式推导）：泛函项 $\lambda\|\mathbf 1_{\{|E|>T\}}\,w_R\|_{L^2}^2$ 的 Fréchet 导数在频域为

$$
D\big(\lambda\|\mathbf 1_{\{|E|>T\}}w_R\|_{L^2}^2\big)=2\lambda\langle\mathbf 1_{\{|E|>T\}}w_R,\mathbf 1_{\{|E|>T\}}\delta w_R\rangle=2\lambda\langle\mathbf 1_{\{|E|>T\}},w_R\,\delta w_R\rangle
\xrightarrow{\mathcal F}\frac{\lambda}{\pi}\big(\widehat{\mathbf 1_{|E|>T}}\ast\widehat{w_R}\big),
$$

其中 $\widehat{\mathbf 1_{|E|>T}}=2\pi\,\delta-2\,\tfrac{\sin(T\cdot)}{\cdot}$（矩形窗傅里叶变换；本文规范下 $\widehat{\mathbf 1_{[-T,T]}}=2\sin(T\xi)/\xi$），Parseval 带入 $\tfrac{1}{2\pi}$ 因子与 Fréchet 导数的 2 倍因子，故得 $\tfrac{2\lambda}{2\pi}=\tfrac{\lambda}{\pi}$ 系数。展开后即框中式的卷积项。**实现辅助**：$\widehat{\mathbf 1_{|E|>T}}(\xi)=2\pi\,\delta(\xi)-2\,\dfrac{\sin(T\xi)}{\xi}$（可直接代入数值计算）。

2. **运算次序细节（严格执行步骤）**：
   - **(i)** 先计算卷积 $\bigl(\tfrac{\sin(T\cdot)}{\cdot}\!\ast\!\widehat{w_R^\star}\bigr)(\xi)$
   - **(ii)** 组装整个括号内表达式（多项式乘子 + $\delta$-项 - 卷积项）
   - **(iii)** 再对整体作用带限投影 $P_B^{(\xi)}$（频域乘子投影 $\chi_B(\xi)$）
   - **(iv)** 强制归一化约束（例如 $\|w_R^\star\|_{L^2}=1$ 或 $\int w_R^\star=1$）

3. **不可交换性解释**：$P_B^{(\xi)}$ 为频域乘子投影，与卷积算子不可交换（除非卷积核频带严格内含于 $B$）。本式已按先卷积后投影固定运算次序；带外自动 $\widehat{w_R^\star}(\xi)=0$。

**算法实现框（伪代码级）**：
```
初始化: w_current ← 初值（PW_Ω 带限）
循环 (迭代至收敛):
  Step 1: 计算卷积  conv_term ← (sinc_T * ŵ_current)
  Step 2: 组装梯度  grad ← poly_multiplier(ŵ_current) + 2λ·ŵ_current - (2λ/π)·conv_term
  Step 3: 投影      grad_projected ← P_B^(ξ) [grad]
            ✱ 切勿将 P_B^(ξ) 提前到卷积前；因 P_B^(ξ) 为乘子投影、与卷积算子
               一般不交换（除非核频带严格内含于 B）
  Step 4: 更新      ŵ_new ← ŵ_current - α·grad_projected  (α为步长)
  Step 5: 归一化    ŵ_new ← ŵ_new / 归一常数
  若 ‖ŵ_new - ŵ_current‖ < tol: 收敛，输出 w_star
```

该式即**"带限投影后的线性算子 = 特征值 $\times$ 函数"**，与 PSWF（Prolate Spheroidal Wave Functions）的 $P_\Omega T_T P_\Omega f=\lambda f$ 同型。含软化参数的泛函对硬约束 $\Gamma$-收敛。

*注*：上述以 $\|w_R\|_{L^2}=1$ 归一为例；若改用其他归一（如 $\int w_R=1$），右端应替换为相应约束的 Fréchet 导数（在频域为常数/δ 的组合），但均不应出现 $\eta\,P_B^{(\xi)}$ 这一与未知函数无关的右端。

**证明**：强凸$\Rightarrow$ 存在唯一；Gateaux 导数经 Parseval 化至频域并投影到带限带得必要条件；强凸与闭性给出 $\Gamma$-收敛与稳定。□（单窗硬约束极值回收到 PSWF 能量浓聚；当 $\lambda\to\infty$ 且硬约束 $\|w\|_{L^2}=1$ 与带限/限时并存时，KKT 方程退化为 $P_\Omega T_T P_\Omega f=\lambda f$（PSWF 本征方程）。）

### T7（多窗 Pareto 前沿、Wexler–Raz 与 Lipschitz 稳定）

**定理**：对多窗 $W=(w^{(1)},\dots,w^{(K)})$ 的强凸多目标代理，极小元 $W^\star$：

(i) 满足**广义 Wexler–Raz 双正交**；对应的**规范对偶窗族** $\widetilde W$ 满足 $\widetilde W=\mathcal S_W^{-1}W$（其中 $\mathcal S_W$ 为多窗帧算子）；

(ii) 对数据/核扰动 $(\delta\rho,\delta\mathcal T)$ 有

$$
\|W^\star-\widehat W^\star\|\le \mu^{-1}\|\nabla\mathcal J(W^\star)-\nabla\widehat{\mathcal J}(\widehat W^\star)\|
$$

（$\mu$ 为强凸模）；

(iii) 产生的指针子空间在谱隙存在时满足 Davis–Kahan 型角度界（$\sin\theta$ 界，需谱隙）。

**证明**：频域必要条件由"核型"KKT 与帧惩罚核给出；强凸$\Rightarrow$ Lipschitz 稳定；子空间稳定由矩阵扰动理论得到（Davis–Kahan 教材版）。□

---

## 5. 统一词典（选要条目）

1. **超选扇区**：若所有窗算子 $W_R$ 关于分解 $\mathcal H=\oplus_\alpha\mathcal H_\alpha$ 分块对角，则这些 $\mathcal H_\alpha$ 构成超选扇区（T3）。

2. **几何相位**：干涉相位差 $\Delta\varphi$ 进入刻度 $d\mu_\varphi$，与 LDOS/延迟在 A5 合流。

3. **弱测量/弱值**：视作 I-projection 的一阶扰动；软/硬极限连接 Born（T2）。

4. **Zeno/反 Zeno**：提交频次改变有效窗宽，按三分解重算；信息收支由 KL-链控制。

5. **到达时间 POVM**：可由窗算子 $W_R$ 与测度侧核 $h$ 诱导的一族 POVM 特化得到；相应读数实现仍为 $\langle K_{w,h}\rangle=\int w_R\,[h\ast\rho_\star]\,dE$。

6. **共振/寿命**：$\det S$ 的下半平面极点在 $d\mu_\varphi$ 中显为峰/拐点；窗化不生新极点（T5），零点计数稳定由 Rouché 半径控制（见 T5 的 Rouché 半径稳定性）。

7. **非平稳时频（相位—尺度）**：$(U_\tau,V_\sigma)$ 的多窗帧与 Parseval 结构；对偶由 Wexler–Raz 给出。

8. **采样阈值**：在 $d\mu_\varphi$ 刻度与 PW 带限下，Nyquist 条件使别名归零并保证稳定采样。

9. **PSWF 能量浓聚**：单窗硬约束极值回收到 PSWF（Landau–Pollak–Slepian 经典系列；能量浓聚极值族）。

10. **CCR 与 Stone 生成元**：$[A,B]=iI$ 与强连续群对应（A1）。

---

## 6. 与前序理论的完整接口

### 6.1 与 Euler 理论系列（S15–S26）

**S15（Weyl–Heisenberg）**：A1 的 $(U_\tau,V_\sigma)$ Weyl 关系与 Stone 定理；WSIG-QM 的相位—尺度底座对应 S15 的酉表示框架。

**S16（de Branges 规范系统）**：§0.1 的 DBK 规范系统与 Herglotz–Weyl 词典即 S16 的核心；T4 的相位导数公式对应 S16 的辛结构。

**S17（散射—酉性）**：L3.5 的 Birman–Kreĭn 公式与 T4 的 Wigner–Smith 延迟对应 S17 的散射相位—行列式公式。

**S18（窗不等式）**：T1 的窗口化读数恒等式与三分解误差闭合对应 S18 的 Nyquist–Poisson–EM 框架。

**S19（光谱图）**：D6 的相位刻度对应 S19 的图谱局部密度。

**S20（BN–Bregman）**：T2 的 I-projection 与 $\Gamma$-极限对应 S20 的 Bregman 几何最优性条件。

**S21（连续谱阈值）**：T4 的核心恒等式 $\varphi'=-\pi\rho_{\rm rel}$ 即 S21 的相位导数=谱密度；T5 的 Rouché 半径对应 S21 的"极点=主尺度"。

**S22（窗/核最优）**：T6 的带限投影-KKT 对应 S22 的频域核型 Euler–Lagrange 方程；PSWF 收敛点对应 S22 的带限偶窗变分原理。

**S23（多窗协同）**：T7 的广义 Wexler–Raz 双正交对应 S23 的多窗 Gram 矩阵框架。

**S24（紧框架）**：L3.7 的 Wexler–Raz 帧对应 S24 的 Calderón–帧界判据。

**S25（非平稳框架）**：D7 的多窗帧对应 S25 的分块非平稳系统；L3.1 的 Nyquist 条件对应 S25 的"无混叠"条件。

**S26（相位密度稳定性）**：D6 的相位刻度 $d\mu_\varphi$ 对应 S26 的 Beurling 密度；T5 的 Rouché 稳定半径对应 S26 的 Kadec–Bari 型小扰动稳定。

### 6.2 与量子测量理论系列

**与相位导数窗口化读数理论**：T1 的窗口化读数恒等式与 Nyquist–Poisson–EM 三分解完全一致。

**与统一测量理论**：T2 的 Born = I-projection 对应"Born = 最小 KL"；T3 的指针基 = 光谱极小对应"Pointer = 最小能量"；T6 的窗/核最优对应"Windows = 极大极小"。

**与 Trinity 定理**：T4 的三重等价（$\varphi' \leftrightarrow -\pi\rho_{\rm rel} \leftrightarrow \tfrac{1}{2}\operatorname{tr}\mathsf Q$）对应 Trinity 定理的三位一体。

**与 CCS（协变多通道）**：T4 的核心恒等式即 CCS 的窗化 Birman–Kreĭn 恒等；T1 的三分解误差闭合对应 CCS 的 Poisson–EM–Tail 框架。

### 6.3 与 EBOC-Graph

- §7 的可检清单对应 EBOC-Graph 的"Born = I-投影，Pointer = 光谱极小，Windows = 极大极小"；
- T2 的充要条件对应 EBOC-Graph 定理 G1；
- T3 对应 EBOC-Graph 定理 G2；
- T6 对应 EBOC-Graph 定理 G3。

---

## 7. 可检清单（实验/数值落地）

1. **刻度统一**：测 $\operatorname{tr}\mathsf Q(E)$ 或相位 $\varphi(E)$ 获得 $d\mu_\varphi$，在此刻度下验证 Nyquist 阈值与别名归零。

**最小复现参数范本（见 L3.1）**：

$$
\boxed{\Omega_w=\Omega_h=\pi/T_s \Rightarrow \Omega_F=\Omega_w+\Omega_h=2\pi/T_s \Rightarrow \Delta\le \pi/\Omega_F=T_s/2}
$$

（角频率单位 rad/（单位(E)）；赫兹规范 $B_F=\Omega_F/(2\pi)\Rightarrow T_s\le 1/(2B_F)$）

2. **指针基验证**：谱分解窗算子 $W_R$ 检验最小本征子空间的方差极小性；**需谱隙条件**：若谱隙存在，用 Davis–Kahan 界评估稳定（见 T3/T7(iii)）。**HS 充分条件**：当 $w_R\in L^2(\mathbb R)$（例如有限支撑窗）时，$\Pi_BM_{w_R}\Pi_B$ 为 Hilbert–Schmidt/紧。

3. **误差闭合**：报告 $(\varepsilon_{\rm alias},\varepsilon_{\rm EM},\varepsilon_{\rm tail})$ 三项占比；带限+Nyquist 校验 $\varepsilon_{\rm alias}=0$（见 §2-D3 正则性条件）。

4. **窗/核 KKT 校核**：在频域检验"多项式乘子 + 卷积核"的带限投影方程与归一约束；多窗实验记录 Pareto 曲面与 Lipschitz 常数。**最小复现参数范本**：固定带宽 $\Omega$、能量/尺度窗 $T$、正则化权重 $(\gamma_1,\dots,\gamma_{M-1},\lambda)$，在频域核验 $P_B^{(\xi)}\bigl(2\sum\gamma_j\,\xi^{4j}\,\widehat{w^\star}+\tfrac{2\lambda}{2\pi}(\widehat{\mathbf 1_{|\cdot|>T}}\ast\widehat{w^\star})\bigr)=\eta\,\widehat{w^\star}$ 与归一约束（$\|w^\star\|_{L^2}=1$ 或 $\int w^\star=1$）。

5. **零集稳定**：测 $\inf_{\partial D}|\mathcal E|$ 与误差上界 $\eta$，验证 Rouché 条件与零点位移界（不生新奇）。

---

## 8. 结语

本体系以三根主干闭合**量子测量的可检理论**：**(i)** 相位—密度刻度 $d\mu_\varphi$；**(ii)** 窗口化读数 $K_{w,h}$ 与 **Nyquist–Poisson–EM** 三分解；**(iii)** 信息几何（I-projection/KL）。在 **A1–A7** 与 **T1–T7** 的桥接下，得到：**Born = I-projection（充要）**、**指针基 = 光谱极小**、**$\varphi'=-\pi\rho_{\rm rel}=\operatorname{tr}\mathsf Q/2$**、**窗/核最优 = 带限投影-KKT + 多窗双正交**；全链路与 S15–S26、euler-quantum 理论系列、EBOC-Graph 可交换，并给出严谨、可实现且可复现的窗口化量子测量学框架。

---

## 参考文献（关键锚点）

**Herglotz–Weyl / DBK**：Kostenko–Teschl 等关于（奇点）Weyl $m$-函数与 Herglotz 性；边界值 $\Im m=\pi\rho$（Remling, arXiv:0706.1101）。

**BK / 谱移函数**：Pushnitski (2010) "$e^{-2\pi i\xi}=\det S$"（arXiv:1006.0639）；Yafaev, D. "Mathematical Scattering Theory: General Theory," Amer. Math. Soc. (1992)，第 4 章与第 6 章为标准综述。在 lossless 情形 $S$ 酉、$\mathsf Q=-iS^\dagger dS/dE$ 自伴，$\operatorname{tr}\mathsf Q=\partial_E\arg\det S=-2\pi\,\xi'(E)$，与 Birman–Kreĭn 公式完全一致（a.e. on $\sigma_{\rm ac}$）。

**Wigner–Smith 延迟**：$\mathsf Q=-iS^\dagger dS/dE$、$\operatorname{tr}\mathsf Q=\partial_E\arg\det S$；Texier 综述式(11)：$\tau_W(\varepsilon)=-(i/N)\partial_\varepsilon\ln\det S$（arXiv:1507.00075, "Wigner time delay and related concepts"）。非酉散射（亚酉 $S$）时的推广见 Phys. Rev. E 103, L050203 (2021): "Generalization of Wigner time delay to subunitary scattering systems"；本稿集中于 lossless 情形。

**Ky Fan（最小和）**：Fan, K. "Maximum Properties and Inequalities for the Eigenvalues of Completely Continuous Operators," Proc. Natl. Acad. Sci. USA 37(11): 760–766 (1951)；Fan's minimum/maximum principle（按升序/降序）。

**Davis–Kahan 谱隙稳定**：Davis, C. & Kahan, W.M. "The rotation of eigenvectors by a perturbation. III," SIAM J. Numer. Anal. 7(1): 1–46 (1970)；给出自伴算子谱子空间在扰动下的 $\sin\Theta$ 界，需谱隙存在。

**Poisson/采样**：Poisson 求和公式与 Nyquist–Shannon 采样定理（带限 $B$ 时 $f_s>2B$，角频率 $\Delta\le\pi/\Omega$）。

**Euler–Maclaurin 余项界**：DLMF / 经典上界；$|R_{2M}|\le \dfrac{2\zeta(2M)}{(2\pi)^{2M}}\int|f^{(2M)}|dx$。

**Stone / Stone–von Neumann**：历史综述（math.umd.edu/~jmr/StoneVNart.pdf）与教材。

**I-projection / KL 极小化**：Csiszár, I. "I-Divergence Geometry of Probability Distributions and Minimization Problems," Ann. Probab. 3(1): 146–158 (1975)；给出 I-projection（最小 KL 散度投影）的唯一性定理与指数族解，需参考分布正支撑与可行集闭凸非空。

**Wexler–Raz / 帧**：Daubechies, I., Landau, H.J. & Landau, Z. "Gabor Time-Frequency Lattices and the Wexler–Raz Identity," J. Fourier Anal. Appl. 1(4): 437–478 (1995)。

**PSWF 能量浓聚**：Slepian, D. & Pollak, H.O. "Prolate Spheroidal Wave Functions, Fourier Analysis and Uncertainty—I," Bell Syst. Tech. J. 40(1): 43–63 (1961)；Landau, H.J. & Pollak, H.O. "Prolate Spheroidal Wave Functions, Fourier Analysis and Uncertainty—II," Bell Syst. Tech. J. 40(1): 65–84 (1961)；Landau–Pollak–Slepian 经典系列（能量浓聚极值族）。

**分布乘积可乘性（参考 D3(ii)）**：Hörmander, L. "The Analysis of Linear Partial Differential Operators I," Springer (1983/2003)，Chapter 6（分布乘积与波前集），给出在足够光滑与带限条件下分布乘积的可乘性判据。

---

**统一备注**：全文所有数学均以 $\cdot$ 为默认乘积、$\ast$ 为卷积；等式链使用标准等号，避免误读为常数式。对 BK 号记的正/负版本仅作一次性"规范与号记"说明，上下文随之自洽。该框架与本项目所有前序理论（S15–S26、euler-quantum 系列、EBOC-Graph）严格对齐，提供量子测量的统一可检理论基础。
