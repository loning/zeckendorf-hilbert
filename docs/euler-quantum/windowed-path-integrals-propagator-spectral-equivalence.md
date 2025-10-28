# 窗口化路径积分：从传播子到"窗—核"谱读数的严格等价

**Windowed Path Integrals: A Spectral "Window–Kernel" Formulation of Propagators**

Version: 0.8.1 · 2025-10-28

## 摘要

在 **de Branges–Kreĭn（DBK）规范系统**与 **Weyl–Heisenberg（含对数/Mellin）**表象所组成的 WSIG-QM 框架下，本文以**谱定理 + 解析傅里叶对偶**为主线，给出**路径积分 = 传播子核**的严格数学刻画，并证明一个**窗化路径积分定理**：任何可实现的路径积分型观测都等价于能量域的"窗—核—密度"卷积；其时间域正是传播子时间迹（或带态权的核）在同一窗/核下的傅里叶对偶。数值实现方面，离散化误差**非渐近**地闭合为"**别名（Poisson）+ 伯努利层（Euler–Maclaurin）+ 截断**"三分解；在**带限 + Nyquist**条件下别名项严格为 0。相位刻度方面，绝对连续谱上几乎处处成立

$$
\varphi'(E)=\dfrac{1}{2}\operatorname{tr}\mathsf Q(E),\qquad
\rho_{\rm rel}(E)=\dfrac{s_{\rm BK}}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\varphi(E)=s_{\rm BK}\,\pi\,\xi(E)\pmod{\pi},
$$

其中 $\mathsf Q(E)=-i\,S^\dagger(E)\, \dfrac{dS}{dE}(E)$ 为 Wigner–Smith 延迟矩阵，$\rho_{\rm rel}=\xi'$ 为谱移密度，$s_{\rm BK}$ 为 BK 号记版本参数（本文采用 $s_{\rm BK}=+1$）；这由 Birman–Kreĭn 公式与相对散射延迟的一致化给出，从而把路径权重的作用量相位与**可测的能量刻度**闭合统一。信息几何侧，**Born 概率 = 最小-KL（I-投影）**给出 log-sum-exp 软势的凸对偶语义；**窗/核**的单窗与多窗协同可表述为强凸/稀疏最优化并与帧—对偶窗理论对接。以上均锚定标准判据：谱定理与 Stone 定理、Birman–Kreĭn 公式、Wigner–Smith 延迟、Poisson 求和与 Euler–Maclaurin 公式、Nyquist–Shannon 采样、Wexler–Raz 双正交与"painless"展开等。

---

## 0. 记号与规范

**（0.1）Fourier 规范.** 取

$$
\widehat f(\xi)=\int_{\mathbb R} f(x)\,e^{-ix\xi}\,dx,\qquad
f(x)=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\xi)\,e^{ix\xi}\,d\xi,
$$

并用 Parseval（零频等式与 Plancherel 并用）：$\displaystyle \int f\,\overline g=\frac{1}{2\pi}\int \widehat f\,\overline{\widehat g}$。

**速查卡：** 本规范下，$\widehat{e^{+iEt_0}}(\xi)=2\pi\delta(\xi-t_0)$，$\widehat{e^{-iEt_0}}(\xi)=2\pi\delta(\xi+t_0)$；缩放 $w_R(E)=w(E/R)$ 给出 $\widehat w_R(\xi)=R\,\widehat w(R\xi)$（幅值因子 $R$，支撑缩至 $1/R$ 倍）。角频率 $\Omega$ 对应时间带宽 $\Omega$（本文统一取此规范，与某些文献的 $2\pi$ 放置不同）。

> **单位/规范提示（统一）.** 在能量—时间对偶中，记 $E$ 的傅里叶对偶变量为 $\xi$；在 $\hbar=1$ 下 $\xi=t$（单位：time），恢复 $\hbar$ 时 $\xi=t/\hbar$。本文所谓"带宽 $\Omega$"统一指 **$\xi$-域半宽**（即 $|\xi|\le \Omega$ 的支撑/近支撑）。因此能量侧 $\widehat w_R,\widehat h$ 的半宽分别为 $\Omega_w/R,\Omega_h$，其和 $\Omega_g=\Omega_w/R+\Omega_h$ 亦为 **$\xi$-域半宽**。若以物理时间表述，在 $\hbar=1$ 约定下有 $T_g=\Omega_g^{-1}$；恢复 $\hbar$ 时应取 $T_g=\hbar/\Omega_g$。文中一切 Nyquist 判据均以 $\xi=t/\hbar$ 为准。Nyquist 判据见 §3 与附录 A。

**（0.2）量纲与常数.** 统一取 $\hbar=1$；恢复时以 $t\mapsto t/\hbar$ 替换。

**（0.3）谱与传播子.** $H$ 为自伴算子，$E_H$ 为其谱测度。对任意**迹类算子** $\rho\in\mathfrak S_1(\mathcal H)$（其中**态权**指 $\rho\ge 0$，**可观测权**指符号有限且 $\operatorname{Tr}\rho=0$ 的迹类算子），定义

$$
K_\rho(t):=\operatorname{Tr}\big(\rho\,e^{-iHt}\big)=\int_{\mathbb R} e^{-iEt}\,d\nu_\rho(E),\quad
\nu_\rho(B):=\operatorname{Tr}\big(\rho\,E_H(B)\big).
$$

在此假设下，$K_\rho(t)$ 良定义且为连续有界函数。

若 $\nu_\rho$ 的绝对连续部分具有密度 $\rho_{\rm abs}(E)$，则其贡献满足（分布意义）$\widehat{\rho_{\rm abs}}(t)=\int_{\mathbb R} e^{-iEt}\rho_{\rm abs}(E)\,dE$。一般地，$K_\rho(t)=\widehat{\rho_{\rm abs}}(t)+\widehat{\nu_{\rm sing}}(t)$；当且仅当 $\nu_\rho$ 纯绝对连续时，才有 $K_\rho=\widehat{\rho_{\rm abs}}$。这来自谱定理与 Stone 定理对 $e^{-itH}$ 的刻画。

**泛化记号.** 对一般谱密度/测度 $\rho_\star$（可为 $\rho_{\rm abs}$、$\rho_{\rm rel}$ 或其他），记 $K_{\rho_\star}(t):=\widehat{\rho_\star}(t)=\int_{\mathbb R} e^{-iEt}\,d\rho_\star(E)$。当 $\rho_\star$ 来自某迹类 $\rho$ 的谱测度 $\nu_\rho$ 时，$K_{\rho_\star}(t)=K_\rho(t):=\operatorname{Tr}(\rho e^{-iHt})$；一般地仍取 Stieltjes/分布意义。

**（0.4）窗与核.** 取**偶窗** $w_R(E)=w(E/R)$，其中 $w\in \mathsf{PW}^{\rm even}_\Omega$（带宽 $\Omega$ 的 Paley–Wiener 偶函数类，此处取 $L^2$ Paley–Wiener：紧支撑傅里叶变换的 $L^2$ 函数），则 $\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$ 亦为偶函数且支撑在 $[-\Omega/R,\Omega/R]$。**注：** "支撑缩放（$\Omega/R$）"与"幅值因子（$R$）"需区分——例如 $R=2$ 时支撑变为原来的 $1/2$，而峰值变为原来的 $2$ 倍，使 $\|\widehat w_R\|_{L^1}$ 保持不变。**缩放不变速查：** 由 $\widehat w_R(\xi)=R\,\widehat w(R\xi)$ 得

$$
\|\widehat w_R\|_{L^1}=\int_{\mathbb R}|\widehat w_R(\xi)|\,d\xi=\int_{\mathbb R}R\,|\widehat w(R\xi)|\,d\xi=\|\widehat w\|_{L^1},
$$

$$
\int_{\mathbb R}|\xi|^k\,|\widehat w_R(\xi)|\,d\xi=R\int_{\mathbb R}|\xi|^k\,|\widehat w(R\xi)|\,d\xi
=R\int_{\mathbb R}\left|\frac{\eta}{R}\right|^k\,|\widehat w(\eta)|\,\frac{d\eta}{R}
=R^{-k}\int_{\mathbb R}|\eta|^k\,|\widehat w(\eta)|\,d\eta\le \left(\frac{\Omega}{R}\right)^k\|\widehat w\|_{L^1}.
$$

测试核 $h\in W^{2M,1}(\mathbb R)\cap L^1(\mathbb R)$（无偶性要求，必要时可带限），保证卷积与换序。

**函数空间提示.** 本文在定理 2.1 与假设 A 中要求 $w\in L^\infty$ 以保证卷积—乘积交换与估计。在本文的 Paley–Wiener 设定（$\operatorname{supp}\widehat w\subset[-\Omega,\Omega]$）下，$w$ 连续且有界，并有 $\|w\|_{L^\infty}\le \tfrac{1}{2\pi}\|\widehat w\|_{L^1}\le \tfrac{\sqrt{2\Omega}}{2\pi}\|\widehat w\|_{L^2}$，因此 $w\in L^\infty$ 自动成立。

**函数空间提示（更正）.** 在一维情形，按本文对 Sobolev 空间的约定（$W^{m,1}(\mathbb R)\subset L^1(\mathbb R)$），有嵌入
$$W^{1,1}(\mathbb R)\hookrightarrow C_0(\mathbb R)\cap L^\infty(\mathbb R).$$
因此对任意 $M\ge 1$，若 $h\in W^{2M,1}(\mathbb R)$，则 $h\in C_0(\mathbb R)\cap L^\infty(\mathbb R)$ 成立，可用于卷积与换序的有界性估计。另一方面，**定理 2.1 的恒等式本身**最低仅需 $h\in L^1(\mathbb R)$；更高阶的 $W^{2M,1}$ 假设仅服务于 §3 的 EM 误差估计。

**（0.5）相位—密度—延迟刻度.** 设对参照 $H_0$ 的散射矩阵为 $S(E)$（单/多通道）。本文固定 Birman–Kreĭn 号记

$$
\det S(E)=e^{+2\pi i\,\xi(E)}\quad (\text{a.e. }E),
$$

并引入 Wigner–Smith 延迟矩阵。**量纲与 $\hbar$ 统一：** 定义

$$
\mathsf Q_\hbar(E):=-i\,\hbar\,S^\dagger(E)\,\partial_E S(E),\qquad
\mathsf Q(E):=\frac{1}{\hbar}\,\mathsf Q_\hbar(E)=-i\,S^\dagger(E)\,\partial_E S(E).
$$

则对任意 a.e. 可微的散射能量 $E$，

$$
\operatorname{tr}\mathsf Q_\hbar(E)=2\,\hbar\,\varphi'(E)=2\pi\hbar\,\xi'(E),\qquad
\rho_{\rm rel}(E)=\xi'(E)=\frac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q_\hbar(E).
$$

在全文中取 $\hbar=1$，默认 $\mathsf Q=\mathsf Q_\hbar/\hbar$，从而

$$
\xi'(E)=\dfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\rho_{\rm rel}(E):=\xi'(E)=\dfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\quad\text{(谱移密度)}.
$$

定义总相位 $\displaystyle \varphi(E):=\tfrac12\,\arg\det S(E)$，其中选取与 BK 号记一致的**连续支路**，并将 $\xi$ 规范为在参考能区（例如阈下或选定参考能量 $E_\ast$）归零，使得 $\xi(E)$ 的绝对值可物理测量。则

$$
\varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E),\qquad
\varphi(E)=s_{\rm BK}\,\pi\,\xi(E)\ \pmod{\pi},
$$

其中 $s_{\rm BK}=+1$ 对应本文版本 I 号记（$\det S=e^{+2\pi i\xi}$）。由此

$$
\rho_{\rm rel}(E)=\xi'(E)=\frac{s_{\rm BK}}{2\pi}\operatorname{tr}\mathsf Q(E).
$$

**归一化与支路选择.** 令谱移函数取标准归一化 $\xi(E)\to 0$ 当 $E\to-\infty$，并选择连续支路使 $\arg\det S(E)$ 满足 $\arg\det S(-\infty)=0$。在此归一化下，BK 版本 I（$\det S=e^{+2\pi i\xi}$）给出**函数级**等式
$$\varphi(E)=\pi\,\xi(E),\qquad \varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E).$$
若采用一般号记 $s_{\rm BK}\in\{+1,-1\}$，则 $\varphi(E)=s_{\rm BK}\,\pi\,\xi(E)$，导数关系不变。

**统一不变量说明：** $\varphi'(E)=\tfrac12\operatorname{tr}\mathsf Q(E)$ 为两号记版本的共同不变量（与 $s_{\rm BK}$ 无关），而 $\rho_{\rm rel}(E)$ 的符号依赖由 $s_{\rm BK}$ 决定。详见定理 4.1 对双版本号的详细说明。

**适用条件：** 上述关系在 §4.1 的散射正则性条件下（例如相对迹类或 Hilbert–Schmidt 条件，使 $S(E)$ a.e. 可微且 BK 公式适用）a.e. 成立，并统一了作用量相位与谱移密度的刻度。详见 §4.1 与附录 A。

---

## 1. 路径积分与谱—窗/核字典

位置本征基下的传播子核

$$
K(x_f,t;x_i,0)=\langle x_f|e^{-iHt}|x_i\rangle
=\int_{\mathbb R} e^{-iEt}\,d\mu_{x_f,x_i}(E),
$$

其中 $\mu_{x_f,x_i}$ 为对应的谱 Stieltjes 测度。形式的费曼路径积分正是对该核的另一种表述（在严格化框架下与核一致）。因此，当选择"窗" $w_R(E)=e^{-iEt_0}$ 与"核" $h=\delta$（广义函数意义）时，时间传播子 $K(x_f,t_0;x_i,0)$ 就是能量侧窗化读数的特例；$h\neq\delta$ 则对应能量平滑，时间域为乘以 $\widehat h$。

在 WSIG-QM 语境中，这等价于：**可测的所有路径积分型观测 = 能量侧"窗—核—密度"读数**；时间侧为传播子时间迹/核在同窗/核下的傅里叶对偶。

---

## 2. **窗化路径积分定理：能量—时间双表**

设 $H$ 自伴，$E_H$ 其谱测度；$\rho_\star$ 表示欲读数的谱密度（可取 $\rho_{\rm abs}$ 或相对密度 $\rho_{\rm rel}$）。令 $w_R\in \mathsf{PW}^{\rm even}_\Omega$，$h\in W^{2M,1}\cap L^1$。

**Assumption A（换序与可积性前提）.** 为使定理 2.1 的傅里叶对偶与换序严格成立，假设：
- **（A1）谱密度规整性：** $\rho_\star$ 为有限符号 Borel 测度（即 $|\rho_\star|(\mathbb R)<\infty$）；当 $\rho_\star$ 有绝对连续部分时其密度属 $L^1_{\rm loc}(\mathbb R)$。
- **（A2）窗函数规整性：** $w_R\in L^\infty(\mathbb R)\cap C^{2M}(\mathbb R)$ 且为偶函数，属 Paley–Wiener 类 $\mathsf{PW}^{\rm even}_\Omega$（带限于角频率 $\Omega$），从而其傅里叶变换 $\widehat w_R$ 紧支撑于 $[-\Omega/R,\Omega/R]$（角频率规范）。
- **（A3）核函数规整性：** $h\in W^{2M,1}(\mathbb R)\cap L^1(\mathbb R)$（无偶性要求），保证 $h\!\ast\!\rho_\star$ 在分布意义下良定义且 $\widehat h\in L^\infty(\mathbb R)$。**充分条件链：** 由 Sobolev 嵌入，$h\in W^{2M,1}(\mathbb R)$ 蕴含 $h\in C_0(\mathbb R)\cap L^\infty(\mathbb R)$（对 $2M\ge 1$ 时），从而 $\|h\!\ast\!\rho_\star\|_{L^\infty}\le \|h\|_{L^\infty}\,|\rho_\star|(\mathbb R)$，保证定理 2.1 证明中的有界性与可积性。**时间侧 EM 附加要求：** 若在时间侧使用 $2M$ 阶 EM 修正（见 A6），需额外保证 $\widehat h\in C^{2M}(\mathbb R)$。充分条件为 $h$ 满足矩条件 $\int_{\mathbb R}|x|^k\,|h(x)|\,dx<\infty$（$0\le k\le 2M$），此时 $\widehat h^{(k)}(t)=\int_{\mathbb R}(-ix)^k h(x)\,e^{-ixt}\,dx$ 对所有 $0\le k\le 2M$ 一致收敛且 $\|\widehat h^{(k)}\|_{L^\infty}\le \int_{\mathbb R}|x|^k\,|h(x)|\,dx$。
- **（A4）Fubini/Tonelli 可交换（修订）.** 上述条件下，$h\!\ast\!\rho_\star\in L^1(\mathbb R)$，且 $w_R\cdot(h\!\ast\!\rho_\star)\in L^1(\mathbb R)$（亦可视为对 Lebesgue 测度的绝对连续有限测度）。因此分布型 Parseval/Plancherel 恒等式与 Fubini–Tonelli 换序成立。
- **（A5）Stieltjes/分布对偶：** 当 $\rho_\star=\nu_\rho$ 为谱测度时，$K_{\rho_\star}(t)=\operatorname{Tr}(\rho e^{-iHt})$ 由 Stone 定理保证为连续有界函数；点谱+绝对连续谱分拆时各部分分别以 Stieltjes 意义处理。
- **（A6）时间侧 EM 光滑性（可选）：** 若在时间侧使用 $2M$ 阶 Euler–Maclaurin 修正，需额外假设 $G_t=\tfrac{1}{2\pi}\widehat w_R(-t)\,\widehat h(t)\,K_{\rho_\star}(t)\in C^{2M}([-T,T])$。**充分条件（三因子闭合）：** 
  - **(i) 窗函数：** 若 $w_R\in L^1(\mathbb R)$ 且满足矩条件 $\int_{\mathbb R}|E|^k|w_R(E)|\,dE<\infty$（$0\le k\le 2M$），则 $\widehat w_R\in C^{2M}(\mathbb R)$ 且

$$
\widehat w_R^{(k)}(t)=\int_{\mathbb R}(-iE)^k w_R(E)\,e^{-iEt}\,dE,\qquad
\|\widehat w_R^{(k)}\|_{L^\infty}\le \int_{\mathbb R}|E|^k|w_R(E)|\,dE.
$$

**注意：** $w_R\in\mathsf{PW}^{\rm even}_\Omega$（即 $\operatorname{supp}\widehat w_R\subset[-\Omega/R,\Omega/R]$）仅保证 $w_R$ 在能量域解析与有界，**不足以**推出时间域 $\widehat w_R$ 的 $C^{2M}$ 光滑性；后者需由能量侧矩条件给出。由 (i)(ii)(iii) 合用可闭合 $G_t^{(2M)}$ 的有界性。
  - **(ii) 核函数：** $h$ 满足矩条件 $\int_{\mathbb R}|x|^k\,|h(x)|\,dx<\infty$（$0\le k\le 2M$），从而 $\widehat h\in C^{2M}(\mathbb R)$ 且 $\|\widehat h^{(k)}\|_{L^\infty}\le \int_{\mathbb R}|x|^k\,|h(x)|\,dx$（见 A3 中时间侧 EM 附加要求）。
  - **(iii) 谱密度：** 对**整体现代谱测度** $\rho_\star$ 施加到 $2M$ 阶的统一矩条件：

$$\int_{\mathbb R}|E|^k\,d|\rho_\star|(E)<\infty,\qquad 0\le k\le 2M,$$

其中 $|\rho_\star|$ 为测度 $\rho_\star$ 的全变差（覆盖绝对连续、点谱、奇异连续三部分）。于是 $K_{\rho_\star}^{(k)}(t)=\int_{\mathbb R}(-iE)^k e^{-iEt}\,d\rho_\star(E)$ 对所有 $0\le k\le 2M$ 一致收敛且有界（$|K_{\rho_\star}^{(k)}(t)|\le \int_{\mathbb R}|E|^k\,d|\rho_\star|(E)$），从而 $K_{\rho_\star}\in C^{2M}(\mathbb R)$。综合 (i)(ii)(iii)，由 Leibniz 规则得 $G_t^{(2M)}$ 存在且有界，EM 余项上界 $\lesssim \dfrac{1}{(2M)!}\,\max\limits_{|t|\le T}\big|G_t^{(2M)}(t)\big|\,\Delta_t^{2M}$ 合法。**纯绝对连续特例：** 当 $\rho_\star$ 为绝对连续密度 $\rho_{\rm abs}(E)$ 时，矩条件退化为 $\int_{\mathbb R}|E|^k\,|\rho_{\rm abs}(E)|\,dE<\infty$（$0\le k\le 2M$）。**点谱/奇异连续：** 需分别保证 $\sum_n |p_n|\,|E_n|^k<\infty$ 与相应奇异连续部分的矩可积；否则建议在时间侧跳过 EM 或改用能量侧方案（§3(ii)）。推荐优先使用能量侧采样。
- **（A7）能量侧 EM 光滑性（修订，统一充分条件）.** 为在能量侧使用 $2M$ 阶 Euler–Maclaurin，需 $G_E:=w_R\cdot(h\!\ast\!\rho_\star)\in C^{2M}(\mathbb R)$。给出如下**分情形充分条件**：
  **(i)** $w_R\in C^{2M}(\mathbb R)$；
  **(ii-A)**（**一般测度，函数连续有界**）若 $h^{(k)}\in C_b(\mathbb R)\cap L^1(\mathbb R)$（$0\le k\le 2M$），则对任意**有限符号测度** $\rho_\star$ 有
$$
(h^{(k)}\!\ast\!\rho_\star)\in C_b(\mathbb R),\qquad
\big\|(h^{(k)}\!\ast\!\rho_\star)\big\|_{L^\infty}\le \|h^{(k)}\|_{L^\infty}\,|\rho_\star|(\mathbb R).
$$
  **备注（必要区分）**：若仅有 $h^{(k)}\in L^1\cap L^\infty$ 而缺少连续性，则一般只能推出 $(h^{(k)}\!\ast\!\rho_\star)\in L^\infty$，**不能**保证其连续（例如 $\rho_\star=\delta_0$）。此时应改用（ii-B）的绝对连续密度情形，或按（ii-C）对点谱部分分段处理/显式求和。
  **(ii-B)**（**$L^p$ 密度情形**）若仅有 $h^{(k)}\in L^1(\mathbb R)$（$0\le k\le 2M$），则需附加 $\rho_\star$ 具 **$L^p$ 密度** $v\in L^p(\mathbb R)$（某个 $1\le p<\infty$；如仅在 $[-E_{\rm max},E_{\rm max}]$ 内施行 EM，可取 $v\in L^p_{\rm loc}$ 并据截断窗作局部化）。于是
$$
(h^{(k)}\!\ast\!v)\in C_0(\mathbb R)\cap L^\infty(\mathbb R),\qquad
\|h^{(k)}\!\ast\!v\|_{L^\infty}\le \|h^{(k)}\|_{L^1}\,\|v\|_{L^p}.
$$
  **(ii-C)** 若 $\rho_\star$ 含点质量，则按离散和式处理或要求 $h^{(k)}\in L^\infty$ 以确保有界性；此时可采用分段 EM 或直接显式求和以绕开连续可微要求。
  在上述任一情形下，$G_E\in C^{2M}(\mathbb R)$ 成立，$2M$ 阶 EM 余项可由 $\max_{|E|\le E_{\max}}|G_E^{(2M)}(E)|$ 控制。

### 定理 2.1（窗—核对偶）

设 $w\in L^\infty(\mathbb R)\cap C^{2M}(\mathbb R)$，$h\in W^{2M,1}(\mathbb R)\cap L^1(\mathbb R)$，$\rho_\star$ 为有限符号 Borel 测度，则

$$
\boxed{\;
\int_{\mathbb R} w(E)\,\bigl[h\!\ast\!\rho_\star\bigr](E)\,dE
=\frac{1}{2\pi}\int_{\mathbb R}\widehat w(-t)\,\widehat h(t)\,K_{\rho_\star}(t)\,dt\;},
$$

其中 $K_{\rho_\star}(t)=\widehat{\rho_\star}(t)$；当 $\rho_\star=\nu_\rho$ 时与 $K_\rho(t):=\operatorname{Tr}(\rho e^{-iHt})$ 一致。若 $w$ 为偶函数（如带宽窗 $w_R(E)=w(E/R)$），则上式右端的 $\widehat w(-t)$ 可写为 $\widehat w(t)$。

> **正则性分级说明：** 定理 2.1 的恒等式本身仅需 $w\in L^\infty$、$h\in L^1$（换序按 A1–A4 保证），而 $C^{2M}$/$(W^{2M,1})$ 的高阶光滑性仅用于 §3 的 EM 误差估计；若仅使用定理本身而无需 $\mathcal O(\Delta^{2M})$ 精度的 EM 修正，可将正则性要求降为 $w\in L^\infty$、$h\in L^1$。

**证明.** 记 $g(E)=w(E)\,(h\!\ast\!\rho_\star)(E)$。由假设 A1–A3，$h\in W^{2M,1}\cap L^1$，故 $\|h\!\ast\!\rho_\star\|_{L^1}\le \|h\|_{L^1}\,|\rho_\star|(\mathbb R)$，从而 $g:=w\cdot(h\!\ast\!\rho_\star)\in L^1(\mathbb R)$（因 $w\in L^\infty$）。据此可直接应用 Fubini–Tonelli 与 Parseval 得到结论；无需用到 $\|h\!\ast\!\rho_\star\|_{L^\infty}$ 上界。由 Parseval，$\int g=\widehat g(0)$。再由卷积—乘积对偶

$$
\widehat g(\xi)=\frac{1}{2\pi}\int_{\mathbb R}\widehat w(\tau)\,\widehat h(\xi-\tau)\,\widehat{\rho_\star}(\xi-\tau)\,d\tau.
$$

取 $\xi=0$，变元 $t=-\tau$ 得

$$
\widehat g(0)=\frac{1}{2\pi}\int_{\mathbb R}\widehat w(-t)\,\widehat h(t)\,\widehat{\rho_\star}(t)\,dt.
$$

又由记号 0.3，$\widehat{\rho_\star}(t)=K_{\rho_\star}(t)$（Stieltjes/分布意义），即得所述。换序由 $w\in L^\infty\cap C^{2M}$、$h\in W^{2M,1}$ 及 $\rho_\star$ 的 **Lebesgue 三分解**（点谱 $+\ $绝对连续 $+\ $奇异连续）下的可积性估计保证：对点谱部分采用显式和式、对绝对连续部分采用 $L^1$ 积分、对奇异连续部分以有限测度的全变差作界，从而 Fubini–Tonelli 与零频 Parseval 恒等式得以适用。□

> **诠释.** 左端是**能量侧**"窗—核—密度"读数；右端是**时间侧**传播子时间迹在相同窗/核下的乘积积分。这就是"**路径积分核（传播子）↔ 能量窗化谱读数**"的精确傅里叶对偶，依赖的仅是谱定理与 Plancherel（Stone 定理确保 $e^{-itH}$ 的一参单位群）。

> **通式与偶窗.** 定理陈述的通式 $\widehat w(-t)$ 适用于任意窗函数；当 $w$ 为偶函数时简化为 $\widehat w(t)$。对点时刻传播子等非偶窗情形（如 $w(E)=e^{\pm iEt_0}$），采用推论 2.2 的分布版本，号记细节见附录 B.2。

### 推论 2.2（分布版本/点窗与 $\delta$ 核，修订）

令 $w\in\mathcal S'(\mathbb R)$ 且其傅里叶变换 $\widehat w$ 为**有界有限测度**（容许 $\widehat w=2\pi\,\delta(\cdot\pm t_0)$）；令 $\rho_\star$ 为**有限符号 Borel 测度**；令 $h\in\mathcal S'(\mathbb R)$ 且可由 $h_\epsilon\in W^{2M,1}\cap L^1$ 逼近。则定理 2.1 的恒等式

$$
\int_{\mathbb R} w(E)\,(h\!\ast\!\rho_\star)(E)\,dE
=\frac{1}{2\pi}\int_{\mathbb R}\widehat w(-t)\,\widehat h(t)\,K_{\rho_\star}(t)\,dt
$$

在 $\mathcal S'$ 配对意义下成立（与定理 2.1 保持相同的通式记号 $\widehat w(-t)$；当 $w$ 为偶函数时可简化为 $\widehat w(t)$）。此时 $K_{\rho_\star}(t)=\widehat{\rho_\star}(t)\in C_b(\mathbb R)$，与 $\widehat h\in L^\infty$ 的乘积良定义；本文不将该乘法泛化至任意分布乘子。

**点时刻传播子特例（双版本对照）.** 取 $h=\delta$（从而 $\widehat h\equiv 1$），在本文傅里叶规范 $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$ 下：

| 窗函数 $w(E)$ | $\widehat w(\xi)$ | $\widehat w(-t)$ | 右端结果 | 左端谱表示 |
|-------------|-----------------|-----------------|---------|-----------|
| $e^{+iEt_0}$ | $2\pi\delta(\xi-t_0)$ | $2\pi\delta(t+t_0)$ | $K_{\rho_\star}(-t_0)$ | $\int e^{+iEt_0}d\rho_\star(E)$ |
| $e^{-iEt_0}$ | $2\pi\delta(\xi+t_0)$ | $2\pi\delta(t-t_0)$ | $K_{\rho_\star}(t_0)$ | $\int e^{-iEt_0}d\rho_\star(E)$ |

两侧恒等式逐步相等，与 §0.1 速查卡完全对齐。物理上常用第二行（$w=e^{-iEt_0}$）得正时刻传播子 $K_{\rho_\star}(t_0)$。

---

## 3. 离散化与**Nyquist–Poisson–EM**三分解（非渐近闭合）

在数值实现中，对（2.1）任一侧取等距采样步长 $\Delta$，窗口截断至 $[-T,T]$，并以 $2M$ 阶 Euler–Maclaurin（EM）修正求和—积分差，则总体误差可**一次性**分解为

$$
\boxed{\ \text{error}=\underbrace{\text{alias}}_{\text{Poisson}}\ +\
\underbrace{\text{Bernoulli layer}}_{\text{EM 余项}}\ +\
\underbrace{\text{tail}}_{\text{截断}}\ }.
$$

**侧别统一与别名判据.** 为避免变量混用，定义
- **时间侧函数**：$G_t(t):=\dfrac{1}{2\pi}\,\widehat w_R(-t)\,\widehat h(t)\,K_{\rho_\star}(t)$。（当 $w_R$ 为偶函数时可简化为 $\widehat w_R(t)$。）
- **能量侧函数**：$G_E(E):=w_R(E)\,(h\!\ast\!\rho_\star)(E)$。

**（i）时间侧采样（近带限与上界）.** 若在时间侧采样 $G_t$（步长 $\Delta_t$），由定义 $G_t(t)=\dfrac{1}{2\pi}\widehat w_R(-t)\widehat h(t)K_{\rho_\star}(t)$ 与本文傅里叶规范 $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$，逐步计算得 $\mathcal F[\widehat w_R(-t)]=2\pi w_R$、$\mathcal F[\widehat h]=2\pi h^\sharp$、$\mathcal F[K_{\rho_\star}]=2\pi\rho_\star^\sharp$（其中 $f^\sharp(E):=f(-E)$ 为反射）。对 Borel 测度 $\mu$ 定义反射 $\mu^\sharp(B):=\mu(-B)$（$-B:=\{-x: x\in B\}$）。于是 $\mathcal F[K_{\rho_\star}]=2\pi\rho_\star^\sharp$ 合法，且与函数情形的反射记号一致。由 $K_{\rho_\star}(t)=\displaystyle\int_{\mathbb R}e^{-iEt}\,d\rho_\star(E)$，对 $t$ 取傅里叶变换得
$$\mathcal F[K_{\rho_\star}](\xi)=\int_{\mathbb R}\left[\int_{\mathbb R}e^{-iEt}\,d\rho_\star(E)\right]\,e^{-it\xi}\,dt=2\pi\int_{\mathbb R}\delta(\xi+E)\,d\rho_\star(E)=2\pi\,\rho_\star^\sharp(\xi),$$
其中 $\mu^\sharp(B):=\mu(-B)$。由乘积—卷积律与前因子 $1/(2\pi)$，得

$$
\widehat G_t(\xi)=\bigl(w_R\ast h^\sharp\ast\rho_\star^\sharp\bigr)(\xi).
$$

散射谱 $\rho_\star$ 通常非紧支撑，故 $\widehat G_t$ 一般支撑在 $\mathbb R$ 上。**严格带限情形（别名=0）需额外假设**：存在 $\Omega_G$ 使 $\operatorname{supp}\widehat G_t\subset[-\Omega_G,\Omega_G]$（即 $w_R\ast h^\sharp\ast\rho_\star^\sharp$ 带限），此时

$$
\boxed{\ \Delta_t\ \le\ \frac{\pi}{\Omega_G}\ \Rightarrow\ \text{alias}=0\ }.
$$

一般**近带限**情形下，别名上界由出带能量控制：

$$
\|\text{alias}\|\ \lesssim\ \big\|\widehat G_t\big\|_{L^1(|\xi|>\pi/\Delta_t)}.
$$

EM 余项（需 $G_t\in C^{2M}$，见假设 A6）：$\lesssim \dfrac{1}{(2M)!}\,\max\limits_{|t|\le T}\big|G_t^{(2M)}(t)\big|\,\Delta_t^{2M}$；截断尾项 $\lesssim \|G_t\|_{L^1(|t|>T)}$。

**（ii）能量侧采样（推荐）.** 若在能量侧采样 $G_E$（步长 $\Delta_E$），其傅里叶变换 $\widehat G_E(\xi)=\dfrac{1}{2\pi}\widehat w_R(\xi)\ast\bigl(\widehat h(\xi)\cdot K_{\rho_\star}(\xi)\bigr)$。**带宽判据（Minkowski 和）：** 当 $\widehat w_R$ 与 $\widehat h$ 均为紧支撑时，有

$$
\operatorname{supp}\widehat G_E\ \subset\ \operatorname{supp}\widehat w_R+\operatorname{supp}\widehat h,
$$

与 $K_{\rho_\star}$ 是否紧支撑无关（被乘子局域化）。具体地，若 $\operatorname{supp}_\xi\widehat w_R\subset[-\tfrac{\Omega_w}{R},\tfrac{\Omega_w}{R}]$ 且 $\operatorname{supp}_\xi\widehat h\subset[-\Omega_h,\Omega_h]$，则 $\operatorname{supp}_\xi\widehat G_E\subset[-(\tfrac{\Omega_w}{R}+\Omega_h),\ \tfrac{\Omega_w}{R}+\Omega_h]$，其中 $\boxed{\ \Omega_g=\tfrac{\Omega_w}{R}+\Omega_h\ }$ 为 **$\xi$-域半宽**。则 $\widehat G_E$ 严格带限于 $[-\Omega_g,\Omega_g]$，从而

$$
\boxed{\ \Delta_E\ \le\ \frac{\pi}{\Omega_g}\ \Rightarrow\ \text{alias}=0\ }.
$$

EM 余项（需假设 A7 保证 $G_E\in C^{2M}$）：$\lesssim \dfrac{1}{(2M)!}\,\max\limits_{|E|\le E_{\rm max}}\big|G_E^{(2M)}(E)\big|\,\Delta_E^{2M}$；截断尾项 $\lesssim \|G_E\|_{L^1(|E|>E_{\rm max})}$。**解析 $\Rightarrow$ 指数收敛（限定条件版）：** 当 $G_E$ 在实轴邻近的水平条带 $\{E+i\eta:|\eta|<\eta_0\}$ 内解析且满足条带内一致衰减（如 $|G_E(E+i\eta)|\lesssim (1+|E|)^{-\alpha}$ 对某 $\alpha>1$）或可周期化延拓时，梯形规则呈几何（指数）收敛 $\lesssim e^{-c/\Delta_E}$（$c$ 依赖于解析条带宽度与衰减速率）；详见 Trefethen–Weideman（SIAM Rev. 2014）关于周期/解析情形的梯形规则指数收敛定理。非周期或无条带解析时需退回代数阶估计。**点谱情形注意：** 若 $\rho_\star$ 含点质量（如谐振子点谱 $\sum_n p_n\delta(E-E_n)$），则 $G_E$ 仅为分段光滑；此时需改用分段 EM 或直接对离散谱求和 $\sum_n p_n w_R(E_n)h(E_n)$，绕过连续微分要求（见假设 A7 中降级处理说明）。

**实践建议.** 优先在**能量侧**采样 $G_E=w_R\cdot(h\ast\rho_\star)$，因其窗/核带限时自动满足 Nyquist 条件。**光滑性注意：** 若使用 $2M$ 阶 EM 修正，需验证假设 A7 的充分条件（$\rho_\star$ 具 $L^1_{\rm loc}$ 密度且 $h\in C^{2M}$）；对含点谱情形，改用分段处理或直接对离散谱求和。时间侧采样需额外验证 $\rho_\star$ 的矩条件（见假设 A6）或施加低通预滤波。

**近带限工作定义.** 对给定容差 $\varepsilon>0$，定义 $\varepsilon$-带限半宽

$$
\Omega_\varepsilon(G):=\inf\big\{\Omega:\ \|\widehat G\|_{L^1(|\xi|>\Omega)}\le \varepsilon\big\},
$$

从而别名上界可用此量表达：$\|\text{alias}\|\lesssim \|\widehat G\|_{L^1(|\xi|>\pi/\Delta)}$；而截断尾项上界由窗外被积函数控制：$\|\text{tail}\|\lesssim \|G\|_{L^1(|x|>T)}$。

**误差账本实施清单（数值实现者速查）：**

| 输入参数 | 符号 | 典型值/单位 |
|---------|------|------------|
| 窗带宽（角频率） | $\Omega_w$ | rad/time |
| 核带宽（角频率） | $\Omega_h$ | rad/time |
| 采样步长（时间侧） | $\Delta_t$ | time |
| 采样步长（能量侧） | $\Delta_E$ | energy |
| 截断半宽 | $T$ | time 或 energy |
| EM 阶数 | $2M$ | 偶数，≥2 |
| 容差 | $\varepsilon$ | 近带限定义用 |

| 输出/判据 | 表达式 | 注释 |
|---------|--------|------|
| **别名=0 条件（时间侧）** | $\Delta_t \le \pi/\Omega_G$ | 仅在 $\widehat G_t$ 严格带限时成立 |
| **别名=0 条件（能量侧）** | $\Delta_E \le \pi/\Omega_g$ | $\Omega_g$ 为 $\widehat G_E$ 半宽（推荐） |
| **别名上界（近带限）** | $\lesssim \|\widehat G\|_{L^1(|\xi|>\pi/\Delta)}$ | 出带能量；见上文 $\Omega_\varepsilon(G)$ 定义 |
| **EM 余项上界** | $\lesssim \frac{1}{(2M)!} \max\limits_{|x|\le T} |G^{(2M)}(x)| \cdot \Delta^{2M}$ | Bernoulli 层；能量侧需 A7，时间侧需 A6；点谱需降级处理 |
| **EM 指数收敛（解析 ⇒ 几何）** | $\lesssim e^{-c/\Delta}$ | 梯形规则 |
| **截断尾项上界** | $\lesssim \|G\|_{L^1(|x|>T)}$ 或 $\lesssim e^{-cT}$（解析） | 窗外能量 |


---

## 4. 相位—密度—延迟的统一刻度

### 定理 4.1（BK + Wigner–Smith）

设 $(H,H_0)$ 满足常规散射正则性（例如 $V\in L^1(\langle x\rangle,dx)$ 或相应相对迹类/Hilbert–Schmidt 条件，使谱移函数与 $S(E)$ 的可微性、BK 公式适用），使得 a.e. $E$ 上 $S(E)$ 存在并酉。

**BK 号记双版本约定（与主流文献对照）.**  
**版本 I（本文采用）：** $\det S(E)=e^{+2\pi i\xi(E)}$，$\mathsf Q(E):=-i\,S^\dagger(E)\,\partial_E S(E)$（取 $\hbar=1$），从而 $\xi'(E)=\dfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$。  
**版本 II（Pushnitski, Sobolev 等主流）：** $\det S(E)=e^{-2\pi i\xi(E)}$，$\mathsf Q(E):=-i\,S^\dagger(E)\,\partial_E S(E)$（定义相同），从而 $\xi'(E)=-\dfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$。  
**互换规则（统一表述）.** 记 $s_{\rm BK}\in\{+1,-1\}$ 使 $\det S(E)=e^{s_{\rm BK}\,2\pi i\,\xi(E)}$。定义

$$
\varphi(E):=\tfrac12\,\arg\det S(E)\quad\Rightarrow\quad 
\varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E).
$$

则

$$
\rho_{\rm rel}(E):=\xi'(E)=\frac{s_{\rm BK}}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\varphi(E)\equiv s_{\rm BK}\,\pi\,\xi(E)\ \ (\mathrm{mod}\ \pi\mathbb Z),
$$

因而

$$
\boxed{\ \varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E)=s_{\rm BK}\,\pi\,\rho_{\rm rel}(E)\ }.
$$

其中 $s_{\rm BK}=+1$ 对应本文主文"版本 I"，$s_{\rm BK}=-1$ 对应"版本 II"。（$\varphi'$ 为两版本共同不变量。）

**证明（要点）.** 由 BK 公式 $\det S(E)=e^{s_{\rm BK}\,2\pi i\xi(E)}$（a.e.）取对数并微分，得 $\dfrac{d}{dE}\log\det S(E)=\operatorname{tr}(S^{-1}S')=s_{\rm BK}\,2\pi i\,\xi'(E)$。又因 $S$ 酉，$S^{-1}=S^\dagger$，于是 $\operatorname{tr}(-iS^\dagger S')=s_{\rm BK}\,2\pi\,\xi'(E)$，即 $\operatorname{tr}\mathsf Q(E)=s_{\rm BK}\,2\pi\,\xi'(E)$。定义 $\varphi(E):=\tfrac12\,\arg\det S(E)$（可取连续分支锚定），则 $\varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E)$，且有 $\varphi(E)\equiv s_{\rm BK}\,\pi\xi(E)\pmod{\pi\mathbb Z}$。□


> **物理含义.** $\operatorname{tr}\mathsf Q(E)$ 为总群延迟，其与谱移导数一致即是 Friedel-型"密度—相位"规则的抽象版本。上述 $\rho(E)=(2\pi\hbar)^{-1}\operatorname{Tr}\mathsf Q(E)$ 在凝聚态、介观物理与电磁波散射中广泛用作能级密度的直接度量。

**与窗化读数的联系.** 对良态散射对 $(H,H_0)$，有 $\rho_{\rm rel}(E)=\xi'(E)=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$，故 $K_{\rho_{\rm rel}}(t)=\widehat{\rho_{\rm rel}}(t)$ 可理解为 $\tfrac{1}{2\pi}\widehat{\operatorname{tr}\mathsf Q}(t)$ 的分布版本；这在定理 2.1 中将相对散射读数与 BK/Wigner–Smith 刻度统一对接。

---

## 5. Born = I-投影与信息几何

**（解释性命题/信息几何语义）** 下述"Born = 最小-KL（I-投影）"用于本框架的概率更新语义，并非量子力学 Born 规则公理的标准表述，而是将窗化读数后的概率条件化/更新过程置于信息几何框架下的重述；在闭凸矩约束 $\mathcal C$ 与下半连续条件下存在唯一极小解。

**适用场景：** 当窗化读数（定理 2.1）给出能量谱的条件化分布后，若需将其更新为满足额外线性矩约束 $\mathcal C$ 的最优分布，可表为对参考 $q$ 的最小-KL 投影（I-投影）：

$$
p^\star=\arg\min_{p\in\mathcal C}\mathrm{KL}(p|q),
$$

则解属于指数族，势函数为 $\log\sum_j e^{\langle\lambda, T_j\rangle}$（log-sum-exp）。这与 Fenchel–Legendre 对偶一致，温度 $\tau\downarrow 0$ 的极限在 $\Gamma$-收敛下给出"硬投影/最小能量"。此"Born = 最小-KL"的等价在信息几何中由 Csiszár 的 I-投影与 Bregman-KL 关系奠基。**注意：** 本节非路径积分的必要组成部分，仅为与 WSIG-QM 公理 A4/定理 T2 的概念接口。

---

## 6. 窗/核设计与多窗协同（最优化—帧—对偶窗）

**（6.1）单窗强凸最优.** 在带限偶子空间上以"带外能量 + 高阶导能量"作目标，得到唯一极小窗；频域满足带限投影的 KKT 条件。

**（6.2）多窗/多核与帧稳定.** 用加权多目标描述帕累托前沿；令 $\{g_m\}$ 为多窗族，帧算子 $Sf=\sum_m \langle f,g_m\rangle g_m$，存在对偶窗族 $\{\tilde g_m\}$ 使 $\sum_m \langle f,g_m\rangle \tilde g_m = f$。Wexler–Raz 双正交给出 Gabor/WH 系的必要充分条件；"painless"非正交展开提供可实现的稳定构造。

---

## 7. 轨道展开与迹公式接口（半经典视角）

抽象迹公式把"谱和 + 轨道和"置于同一测试核 $h$ 下；窗化后奇性集合与阶保持，数值误差依旧遵循本论文的"别名 + EM + 截断"账本。（具体 Selberg/Gutzwiller 版略。）

---

## 8. 例：自由粒子与谐振子（纲要）

* **自由粒子**：LDOS 的密度 $\rho_{\rm abs}(E)$ 与 $K_{\rho_{\rm abs}}(t)$ 由傅里叶互为对偶；取 $w_R(E)=e^{-iEt_0}$、$h=\delta$ 恢复 $K_{\rho_{\rm abs}}(t_0)$。
* **谐振子**：点谱 $\nu_\rho=\sum_n p_n\delta(E-E_n)$ 时，$K_{\rho}(t)=\sum_n p_n e^{-iE_n t}$，（2.1）以 Stieltjes 形式依然成立。

---

## 9. 与 WSIG-QM / UMS / EBOC 的接口

**9.1 与 WSIG-QM 的接口。**
- WSIG-QM 的公理 A2（有限窗口读数）直接对应本文定理 2.1 的能量侧"窗—核—密度"读数。
- WSIG-QM 的公理 A5（相位—密度—延迟刻度）与本文定理 4.1 采用完全一致的 BK 号记与 Wigner–Smith 定义。
- WSIG-QM 的定理 T1（窗口化读数恒等式与非渐近误差闭合）与本文第 3 节的 Nyquist–Poisson–EM 三分解共享同一误差账本。
- WSIG-QM 的定理 T2（Born = I-projection）与本文第 5 节的信息几何投影在概念与证明结构上完全对齐。

**9.2 与 UMS 的接口。**
- UMS 的核心统一式 $\rho_{\rm rel}\,dE = \xi'\,dE = \tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\,dE$ 与 $\varphi'=\tfrac{1}{2}\operatorname{tr}\mathsf Q=\pi\,\rho_{\rm rel}$ 与本文 0.5 及定理 4.1 采用相同刻度。
- UMS 的公理 A2（有限窗口读数）与本文定理 2.1 在传播子语境下完全等价。
- UMS 的定理 4.1–4.3（Nyquist–Poisson–EM 有限阶闭合）为本文第 3 节的路径积分离散化提供理论支撑。

**9.3 与 EBOC-Graph 的接口。**
- EBOC-Graph 的定理 G4（非渐近误差闭合）与本文第 3 节的三分解在离散谱/图信号情形下共享框架。
- 路径积分在图/格点系统上的离散化可沿用本文的 Nyquist–Poisson–EM 账本，将连续能量谱替换为图拉普拉斯谱。

**9.4 与 S15–S26 的接口。**
- S15–S17 的 Herglotz 表示与规范系统为传播子核的谱密度 $\rho_{\rm abs}$ 提供解析结构。
- S24–S26 的纤维 Gram、Wexler–Raz 双正交与 Balian–Low 不可能性为本文第 6 节的多窗设计提供具体判据。
- S21–S23 的相位—尺度协变与有限阶 EM 纪律直接支撑本文的误差闭合框架。

**9.5 与 CCS（协变多通道）的接口。**
- CCS 的窗化 Birman–Kreĭn 恒等式与本文定理 4.1 在多通道散射情形下完全一致。
- CCS 的 Nyquist–Poisson–EM 三分解为本文第 3 节的路径积分离散化提供多通道推广。

**9.6 保持"极点 = 主尺度"的有限阶 EM 纪律。**
- 本文在所有离散—连续换序中均采用**有限阶** EM，确保传播子的极点（共振/束缚态能量）始终为"主尺度"标记。
- 与 WSIG-QM、UMS、S15–S26 保持一致：EM 余项仅作有界扰动，不引入新奇点。

---

## 10. 结论

**一语以蔽之**：

$$
\boxed{\ \text{路径积分 = 传播子核}\ \Longleftrightarrow
\text{能量侧"窗—核—密度"读数}\ \stackrel{\mathcal F}{\leftrightarrow}
\text{时间侧窗化传播子迹}\ },
$$

并在 **BK/延迟/相位密度**统一刻度与 **Nyquist–Poisson–EM** 误差学下，得到**严格对偶 + 可计算闭合**的表述。

---

### 附录 A：规范切换与 $\hbar$ 恢复

* 若取对称 Fourier 规范 $\widehat f=(2\pi)^{-1/2}\int f e^{-ix\xi}$，则定理 2.1 右端无 $1/(2\pi)$ 因子（自动吸收进规范）。
* 恢复 $\hbar$：以 $\xi=t/\hbar$ 改写 $\widehat w_R,\widehat h,K_{\rho_\star}$ 的自变量并配套雅可比；按 §0.5 中 $\mathsf Q_\hbar$ 的定义，含 $\hbar$ 的版本无关关系式为 $\operatorname{tr}\mathsf Q_\hbar(E)=2\,\hbar\,\varphi'(E)$；在版本 I 号记（$\det S=e^{+2\pi i\xi}$）下有 $\varphi\equiv\pi\xi\pmod{\pi\mathbb Z}$（可在 $E_\ast$ 处锚定分支），从而 $\operatorname{tr}\mathsf Q_\hbar(E)=2\pi\hbar\,\xi'(E)$。
* **Nyquist 速查式（恢复 $\hbar$）：** 设 $\Omega_g$ 为能量侧 $\widehat G_E$ 的 **$\xi$-域半宽**（$\xi=t/\hbar$）。则
$$
\boxed{\ \Delta_E\le \frac{\pi}{\Omega_g}\ }\ .
$$
等价地，以**物理时间半宽**
$$
T_g:=\frac{\hbar}{\Omega_g}
$$
表示，则
$$
\boxed{\ \Delta_E\le \frac{\pi\,\hbar}{T_g}\ }\ ,
$$
二者完全一致；当 $\hbar=1$ 时退化为 $\Delta_E\le \pi/\Omega_g$。时间侧同理：若 $\Omega_G$ 为 $G_t$ 的频域半宽，则 $\Delta_t\le \pi/\Omega_G$。取 $\hbar=1$ 时回到正文 §3 公式。

> **单位再提示（与 §0.1 对齐）：** 上述 $\Omega_g,\Omega_G$ 均为 $\xi=t/\hbar$ 域的半宽（$\hbar=1$ 时单位：1/time）；若需以普通频率 $f$（Hz）表述，则以 $\Omega=2\pi f/\hbar$ 替换。
* **BK 号记版本切换：** 正文采用版本 I：$\det S=e^{+2\pi i\xi}$；主流文献采用版本 II：$\det S=e^{-2\pi i\xi}$。两版本下 $\xi'$ 与 $\operatorname{tr}\mathsf Q_\hbar$（或 $\operatorname{tr}\mathsf Q$）同时变号，**统一不变量**为相位导数：

$$
\boxed{\ \varphi'(E)=\tfrac{1}{2\hbar}\operatorname{tr}\mathsf Q_\hbar(E)\ }\quad(\text{两版本一致}),
$$

而谱移密度则带版本依赖的符号：

$$
\boxed{\ \rho_{\rm rel}(E)=\xi'(E)=\pm\,\tfrac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q_\hbar(E)\ },
$$

其中"$+$"对应版本 I（$\det S=e^{+2\pi i\xi}$，$\varphi\equiv\pi\xi\pmod{\pi\mathbb Z}$），"$-$"对应版本 II（$\det S=e^{-2\pi i\xi}$，$\varphi\equiv-\pi\xi\pmod{\pi\mathbb Z}$）。可在参考能量 $E_\ast$ 处锚定常数项以固定分支。定理 4.1 对两种号记的详细说明见正文。

---

### 附录 B：路径积分与传播子核的等价性补充

**B.1 Feynman–Kac 公式与谱表示。**
对势 $V$ 满足适当增长条件的薛定谔算子 $H=-\tfrac{1}{2}\Delta+V$，传播子核

$$
K(x_f,t;x_i,0)=\langle x_f|e^{-iHt}|x_i\rangle
$$

可经 Trotter 乘积公式与 Feynman–Kac 公式（虚时情形）得到严格版本；实时路径积分的严格化需视势函数满足的条件而定。关键点：
- 谱定理给出 $e^{-iHt}=\int e^{-iEt}\,dE_H(E)$。
- 传播子核为 $\langle x_f|e^{-iHt}|x_i\rangle$ 在位置表象下的矩阵元。
- Feynman–Kac 给出路径积分表述（形式）；严格版本需 Wiener 测度或格点近似。

**B.2 窗化为 $w_R(E)=e^{+iEt_0}$ 与 $h=\delta$ 的极限。**
在本文采用的傅里叶规范 $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$ 下，取 $w_R(E)=e^{+iEt_0}$ 则 $\widehat w_R(\xi)=2\pi\delta(\xi-t_0)$，故定理 2.1 通式中的 $\widehat w_R(-t)=2\pi\delta(t+t_0)$。若 $h=\delta$，则 $\widehat h(t)=1$。代入定理 2.1 右端：

$$
\frac{1}{2\pi}\int_{\mathbb R} 2\pi\delta(t+t_0)\cdot 1\cdot K_{\rho_\star}(t)\,dt = K_{\rho_\star}(-t_0).
$$

左端按谱表示 $\int_{\mathbb R} e^{+iEt_0}\,d\rho_\star(E) = K_{\rho_\star}(-t_0)$，两侧**逐步等式一致**。若需右端直接给出 $K_{\rho_\star}(t_0)$（对应正时刻传播子），则改用窗函数 $w_R(E)=e^{-iEt_0}$（此时 $\widehat w_R(-t)=2\pi\delta(t-t_0)$），与 0.1 的速查卡完全对齐。物理上两种写法等价，均为定理 2.1 在点窗下的特例。

**B.3 能量平滑（$h\neq\delta$）的物理解释。**
- 若 $h$ 为带限函数，对应能量域平滑/滤波；时间域为 $\widehat h(t)$ 的乘子。
- 例：取 $h$ 为高斯，则对应能量不确定度展宽；Wigner–Weyl 时频分析中等价于相空间局域化。

---

### 附录 C：Wexler–Raz 双正交与"painless"展开简要

**C.1 Wexler–Raz 双正交（更正）。**
设 $\{M_{mb}T_{na}g\}_{m,n\in\mathbb Z}$ 与 $\{M_{mb}T_{na}\tilde g\}_{m,n\in\mathbb Z}$ 为 $(a,b)$ 格点上一对 Gabor 系。它们互为**对偶帧**的**充要条件**是：在**伴随晶格**
$$
\Lambda^\circ=\Big\{\Big(\frac{m}{a},\frac{n}{b}\Big):\ m,n\in\mathbb Z\Big\}
$$
上满足二维采样正交
$$
\boxed{\ \frac{1}{ab}\Big\langle \tilde g,\,M_{\frac{m}{a}}T_{\frac{n}{b}}\,g\Big\rangle=\delta_{m,0}\delta_{n,0},\quad \forall\,m,n\in\mathbb Z\ }.
$$
（等价写法 $\langle g,\,M_{\frac{m}{a}}T_{\frac{n}{b}}\tilde g\rangle=ab\,\delta_{m,0}\delta_{n,0}$ 仅系内积对易与常数归一互换。）
原"沿轴求和"条件仅在附加周期化/收敛前提下可由 Poisson 求和化简得到，**不应作为一般判据**。

**C.2 "Painless"非正交展开（修订）。**
推荐在**过采样**情形 $ab<1$（冗余度 $>1$）构造"painless"**紧框架**（$A=B$）；此时可给出显式对偶窗且数值稳定。**在临界密度 $ab=1$** 下，除非采用非良好局域的退化窗，一般**无法**得到良好局域的紧框架（受 Balian–Low 不可能性限制），因此不作普遍性断言。

**C.3 与本文窗/核设计的联系。**
- 多窗/多核协同（§6.2）可视为多个 Gabor 系的并；帕累托前沿对应加权多目标最优化。
- Wexler–Raz 条件确保对偶窗存在，从而定理 2.1 的多窗版本可逐窗叠加并保持数值稳定性。

---

## 参考锚点（精选）

* **谱定理、Stone 定理与传播子核的谱表示：** Teschl《Mathematical Methods in Quantum Mechanics》（AMS Graduate Studies in Mathematics）；Reed–Simon《Methods of Modern Mathematical Physics》Vol. I。
* **路径积分与传播子：** Feynman–Hibbs《Quantum Mechanics and Path Integrals》；Simon《Functional Integration and Quantum Physics》（Academic Press）；Glimm–Jaffe《Quantum Physics: A Functional Integral Point of View》；Littlejohn《The Propagator and the Path Integral》讲义。
* **Birman–Kreĭn 公式与谱移函数：** Pushnitski（Acta Math. 2008），Yafaev《Mathematical Scattering Theory》；Sobolev 综述（arXiv:1006.0639）。
* **Wigner–Smith 延迟矩阵：** Wigner（Phys. Rev. 1955）、Smith（Phys. Rev. 1960）原始论文；多通道情形见 Shimamura（J. Phys. B 2006）；综述见 Martin（Phys. Rev. A 1992）。
* **Friedel 规则与谱移—电荷关系：** Kohmoto–Koma–Nakamura（Phys. Rev. B 1999）。
* **采样、Poisson 与 Nyquist：** Shannon（1949）经典；Nyquist–Shannon 采样定理见 Marks《Introduction to Shannon Sampling and Interpolation Theory》（Springer）；Poisson 求和与近似采样见 Butzer–Gessinger（Arch. Math. 1997）、Candès 讲义（Stanford Math 262）。
* **Euler–Maclaurin 公式与指数收敛梯形规则：** Atkinson《An Introduction to Numerical Analysis》（Wiley）；解析/周期情形指数（几何）收敛见 Trefethen–Weideman《The Exponentially Convergent Trapezoidal Rule》（SIAM Review 2014, Vol. 56, No. 3, pp. 385–458）——此为解析函数上梯形规则指数收敛的权威综述。
* **帧与对偶窗、Wexler–Raz 与"painless"展开：** Daubechies, Landau, Landau（J. Fourier Anal. Appl. 1995）；Daubechies–Grossmann–Meyer（J. Math. Phys. 1986）；Christensen《An Introduction to Frames and Riesz Bases》（Birkhäuser）；Gröchenig《Foundations of Time-Frequency Analysis》（Birkhäuser）；Casazza 等综述。
* **I-投影与信息几何：** Csiszár《I-Divergence Geometry of Probability Distributions and Minimization Problems》（Ann. Probab. 1975）；Amari–Nagaoka《Methods of Information Geometry》（AMS）。

（全文所用外部结论均为标准判据；涉及可能随规范变化的常数/符号已在相应处固定或注明依赖。）
