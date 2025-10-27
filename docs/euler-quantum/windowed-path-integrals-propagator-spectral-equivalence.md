# 窗口化路径积分：从传播子到"窗—核"谱读数的严格等价

**Windowed Path Integrals: A Spectral "Window–Kernel" Formulation of Propagators**

## 摘要

在 **de Branges–Kreĭn（DBK）规范系统**与 **Weyl–Heisenberg（含对数/Mellin）**表象所组成的 WSIG-QM 框架下，本文以**谱定理 + 解析傅里叶对偶**为主线，给出**路径积分 = 传播子核**的严格数学刻画，并证明一个**窗化路径积分定理**：任何可实现的路径积分型观测都等价于能量域的"窗—核—密度"卷积；其时间域正是传播子时间迹（或带态权的核）在同一窗/核下的傅里叶对偶。数值实现方面，离散化误差**非渐近**地闭合为"**别名（Poisson）+ 伯努利层（Euler–Maclaurin）+ 截断**"三分解；在**带限 + Nyquist**条件下别名项严格为 0。相位刻度方面，绝对连续谱上几乎处处成立

$$
\varphi'(E)=\dfrac{1}{2}\operatorname{tr}\mathsf Q(E),\qquad
\rho_{\rm rel}(E)=\dfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\varphi(E)=\pi\,\xi(E),
$$

其中 $\mathsf Q(E)=-i\,S^\dagger(E)\, \dfrac{dS}{dE}(E)$ 为 Wigner–Smith 延迟矩阵，$\rho_{\rm rel}=\xi'$ 为谱移密度；这由 Birman–Kreĭn 公式与相对散射延迟的一致化给出，从而把路径权重的作用量相位与**可测的能量刻度**闭合统一。信息几何侧，**Born 概率 = 最小-KL（I-投影）**给出 log-sum-exp 软势的凸对偶语义；**窗/核**的单窗与多窗协同可表述为强凸/稀疏最优化并与帧—对偶窗理论对接。以上均锚定标准判据：谱定理与 Stone 定理、Birman–Kreĭn 公式、Wigner–Smith 延迟、Poisson 求和与 Euler–Maclaurin 公式、Nyquist–Shannon 采样、Wexler–Raz 双正交与"painless"展开等。

---

## 0. 记号与规范

**（0.1）Fourier 规范.** 取

$$
\widehat f(\xi)=\int_{\mathbb R} f(x)\,e^{-ix\xi}\,dx,\qquad
f(x)=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\xi)\,e^{ix\xi}\,d\xi,
$$

并用 Parseval（零频等式与 Plancherel 并用）：$\displaystyle \int f\,\overline g=\frac{1}{2\pi}\int \widehat f\,\overline{\widehat g}$。

**速查卡：** 本规范下，$\widehat{e^{+iEt_0}}(\xi)=2\pi\delta(\xi-t_0)$，$\widehat{e^{-iEt_0}}(\xi)=2\pi\delta(\xi+t_0)$；缩放 $w_R(E)=w(E/R)$ 给出 $\widehat w_R(\xi)=R\,\widehat w(R\xi)$（幅值因子 $R$，支撑缩至 $1/R$ 倍）。角频率 $\Omega$ 对应时间带宽 $\Omega$（本文统一取此规范，与某些文献的 $2\pi$ 放置不同）。

**（0.2）量纲与常数.** 统一取 $\hbar=1$；恢复时以 $t\mapsto t/\hbar$ 替换。

**（0.3）谱与传播子.** $H$ 为自伴算子，$E_H$ 为其谱测度。对任意迹类态权 $\rho\ge 0$（或迹为 0 的可观测权），定义

$$
K_\rho(t):=\operatorname{Tr}\big(\rho\,e^{-iHt}\big)=\int_{\mathbb R} e^{-iEt}\,d\nu_\rho(E),\quad
\nu_\rho(B):=\operatorname{Tr}\big(\rho\,E_H(B)\big).
$$

若 $\nu_\rho$ 的绝对连续部分具有密度 $\rho_{\rm abs}(E)$，则其贡献满足（分布意义）$\widehat{\rho_{\rm abs}}(t)=\int_{\mathbb R} e^{-iEt}\rho_{\rm abs}(E)\,dE$。一般地，$K_\rho(t)=\widehat{\rho_{\rm abs}}(t)+\widehat{\nu_{\rm sing}}(t)$；当且仅当 $\nu_\rho$ 纯绝对连续时，才有 $K_\rho=\widehat{\rho_{\rm abs}}$。这来自谱定理与 Stone 定理对 $e^{-itH}$ 的刻画。

**泛化记号.** 对一般谱密度/测度 $\rho_\star$（可为 $\rho_{\rm abs}$、$\rho_{\rm rel}$ 或其他），记 $K_{\rho_\star}(t):=\widehat{\rho_\star}(t)=\int_{\mathbb R} e^{-iEt}\,d\rho_\star(E)$。当 $\rho_\star$ 来自某迹类 $\rho$ 的谱测度 $\nu_\rho$ 时，$K_{\rho_\star}(t)=K_\rho(t):=\operatorname{Tr}(\rho e^{-iHt})$；一般地仍取 Stieltjes/分布意义。

**（0.4）窗与核.** 取**偶窗** $w_R(E)=w(E/R)$，其中 $w\in \mathsf{PW}^{\rm even}_\Omega$（带宽 $\Omega$ 的 Paley–Wiener 偶函数类），则 $\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$ 亦为偶函数且支撑在 $[-\Omega/R,\Omega/R]$。**注：** "支撑缩放（$\Omega/R$）"与"幅值因子（$R$）"需区分——例如 $R=2$ 时支撑变为原来的 $1/2$，而峰值变为原来的 $2$ 倍，使 $L^1$ 范数保持。前端核 $h\in W^{2M,1}(\mathbb R)\cap L^1(\mathbb R)$（无偶性要求，必要时可带限），保证卷积与换序。

**（0.5）相位—密度—延迟刻度.** 设对参照 $H_0$ 的散射矩阵为 $S(E)$（单/多通道）。本文固定 Birman–Kreĭn 号记

$$
\det S(E)=e^{+2\pi i\,\xi(E)}\quad (\text{a.e. }E),
$$

并引入 Wigner–Smith 延迟矩阵 $\mathsf Q(E):=-i\,S^\dagger(E)\,S'(E)$。由 BK 公式对数导数可得

$$
\xi'(E)=\dfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\rho_{\rm rel}(E):=\xi'(E)=\dfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\quad\text{(谱移密度)}.
$$

记总相位 $\varphi(E):=\pi\,\xi(E)$，则

$$
\varphi'(E)=\pi\,\xi'(E)=\dfrac{1}{2}\operatorname{tr}\mathsf Q(E)=\pi\,\rho_{\rm rel}(E).
$$

**适用条件：** 上述关系在 §4.1 的散射正则性条件下（例如相对迹类或 Hilbert–Schmidt 条件，使 $S(E)$ a.e. 可微且 BK 公式适用）a.e. 成立，并统一了作用量相位与谱移密度的刻度。恢复 $\hbar$ 时有 $2\hbar\,\delta'(E)=\operatorname{tr}\mathsf Q(E)$，其中 $\det S=e^{2i\delta}$。详见 §4.1 与附录 A。

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
- **（A3）核函数规整性：** $h\in W^{2M,1}(\mathbb R)\cap L^1(\mathbb R)$（无偶性要求），保证 $h\!\ast\!\rho_\star$ 在分布意义下良定义且 $\widehat h\in L^\infty(\mathbb R)$。
- **（A4）Fubini/Tonelli 可交换：** 上述条件下，卷积 $h\!\ast\!\rho_\star$ 与乘积 $w_R\cdot(h\!\ast\!\rho_\star)$ 为有界测度，从而分布型 Parseval/Plancherel 恒等式与 Fubini–Tonelli 换序成立。
- **（A5）Stieltjes/分布对偶：** 当 $\rho_\star=\nu_\rho$ 为谱测度时，$K_{\rho_\star}(t)=\operatorname{Tr}(\rho e^{-iHt})$ 由 Stone 定理保证为连续有界函数；点谱+绝对连续谱分拆时各部分分别以 Stieltjes 意义处理。

### 定理 2.1（窗—核对偶）

$$
\boxed{\;
\int_{\mathbb R} w_R(E)\,\bigl[h\!\ast\!\rho_\star\bigr](E)\,dE
=\frac{1}{2\pi}\int_{\mathbb R}\widehat w_R(t)\,\widehat h(t)\,K_{\rho_\star}(t)\,dt\;},
$$

其中 $K_{\rho_\star}(t)=\widehat{\rho_\star}(t)$；当 $\rho_\star=\nu_\rho$ 时与 $K_\rho(t):=\operatorname{Tr}(\rho e^{-iHt})$ 一致。当 $w_R(E)=e^{+iEt_0}$（从而 $\widehat w_R(t)=2\pi\delta(t-t_0)$）、$h=\delta$ 时，右端化为 $K_{\rho_\star}(t_0)$（详见附录 B.2 对傅里叶规范的讨论）。

**证明.** 记 $g(E)=w_R(E)\,(h\!\ast\!\rho_\star)(E)$。由 Parseval，$\int g=\widehat g(0)$。再由卷积—乘积对偶

$$
\widehat g(\xi)=\frac{1}{2\pi}\int_{\mathbb R}\widehat w_R(\tau)\,\widehat h(\xi-\tau)\,\widehat{\rho_\star}(\xi-\tau)\,d\tau.
$$

取 $\xi=0$，变元 $t=-\tau$ 得

$$
\widehat g(0)=\frac{1}{2\pi}\int_{\mathbb R}\widehat w_R(-t)\,\widehat h(t)\,\widehat{\rho_\star}(t)\,dt.
$$

因 $w_R$ 为偶函数（0.4），其傅里叶变换 $\widehat w_R$ 亦偶，从而 $\widehat w_R(-t)=\widehat w_R(t)$。又由记号 0.3，$\widehat{\rho_\star}(t)=K_{\rho_\star}(t)$（Stieltjes/分布意义），即得所述。此处采用分布型 Parseval/Plancherel；假设 $\rho_\star$ 为有限 Borel 测度，$h\in L^1(\mathbb R)$ 使 $h\!\ast\!\rho_\star$ 有界且（广义）可积，从而 Fubini/Tonelli 与换序成立。换序由 $w_R\in L^\infty\cap C^{2M}$、$h\in W^{2M,1}$ 及 $\rho_\star$ 在 Fubini/Tonelli 意义下的可积性（对紧支撑与绝对连续部分分解处理）保证。□

> **诠释.** 左端是**能量侧**"窗—核—密度"读数；右端是**时间侧**传播子时间迹在相同窗/核下的乘积积分。这就是"**路径积分核（传播子）↔ 能量窗化谱读数**"的精确傅里叶对偶，依赖的仅是谱定理与 Plancherel（Stone 定理确保 $e^{-itH}$ 的一参单位群）。

> **偶窗假设与去偶化.** 本定理陈述采用偶窗 $w_R$（从而 $\widehat w_R(-t)=\widehat w_R(t)$）以简化证明中的符号；对非偶窗（例如恢复点时刻传播子时取 $w_R(E)=e^{\pm iEt_0}$）或需去偶化处理的情形，见附录 B.2 对傅里叶规范与号记的讨论——结论保持，仅需配合规范调整。

> **提示.** 当需恢复点时刻传播子 $K_{\rho_\star}(t_0)$ 时，取 $w_R(E)=e^{\pm iEt_0}$ 与 $h=\delta$ 的极限，见附录 B.2。

---

## 3. 离散化与**Nyquist–Poisson–EM**三分解（非渐近闭合）

在数值实现中，对（2.1）任一侧取等距采样步长 $\Delta$，窗口截断至 $[-T,T]$，并以 $2M$ 阶 Euler–Maclaurin（EM）修正求和—积分差，则总体误差可**一次性**分解为

$$
\boxed{\ \text{error}=\underbrace{\text{alias}}_{\text{Poisson}}\ +\
\underbrace{\text{Bernoulli layer}}_{\text{EM 余项}}\ +\
\underbrace{\text{tail}}_{\text{截断}}\ }.
$$

**别名=0 判据（Nyquist 条件）：** 记 $g(E):=w_R(E)\,(h\!\ast\!\rho_\star)(E)$ 为能量侧被采样的量。若 $\widehat w_R$ 与 $\widehat h$ **严格带限**于 $[-\Omega_w,\Omega_w]$ 与 $[-\Omega_h,\Omega_h]$（角频率规范），则由傅里叶卷积—乘积对偶 $\widehat g=\frac{1}{2\pi}\,\widehat w_R\ast\big(\widehat h\cdot\widehat{\rho_\star}\big)$ 及支撑卷积规则知：
- 若 $\widehat h$ 带限于 $[-\Omega_h,\Omega_h]$，则 $\operatorname{supp}(\widehat h\cdot\widehat{\rho_\star})\subseteq [-\Omega_h,\Omega_h]$（无论 $\widehat{\rho_\star}$ 是否带限）；
- 进而 $\operatorname{supp}\widehat g\subseteq \operatorname{supp}\widehat w_R + \operatorname{supp}\widehat h\subseteq [-(\Omega_w+\Omega_h),\Omega_w+\Omega_h]$。

**因此，当且仅当 $g(E)$ 的角频域支撑在 $[-(\Omega_w+\Omega_h),\Omega_w+\Omega_h]$ 内时，** 若等距采样步长（时间侧）满足

$$
\Delta\ \le\ \frac{\pi}{\Omega_w+\Omega_h},
$$

则由 Nyquist–Shannon 采样定理，**别名项严格为 0**（Poisson 求和之非零模项消失）。近带限情形，别名由出带能量与 $\Delta$ 的显式上界控制。EM 层只依赖有限阶导数，尾项由窗外 $L^1/L^2$ 能量给界。EM 层取自 Euler–Maclaurin 公式的带余项版本；对解析/周期情形，梯形规则呈指数收敛。

**误差账本实施清单（数值实现者速查）：**

| 输入参数 | 符号 | 典型值/单位 |
|---------|------|------------|
| 窗带宽（角频率） | $\Omega_w$ | rad/time |
| 核带宽（角频率） | $\Omega_h$ | rad/time |
| 采样步长（时间侧） | $\Delta$ | time |
| 截断半宽 | $T$ | time |
| EM 阶数 | $2M$ | 偶数，≥2 |

| 输出/判据 | 表达式 | 注释 |
|---------|--------|------|
| **别名=0 条件** | $\Delta \le \pi/(\Omega_w+\Omega_h)$ | 严格带限时成立 |
| **别名上界（近带限）** | $\lesssim \|\widehat g\|_{L^1(|\xi|>\pi/\Delta)}$ | 出带能量 |
| **EM 余项上界** | $\lesssim \frac{1}{(2M)!} \max\limits_{|t|\le T} |g^{(2M)}(t)| \cdot \Delta^{2M}$ | Bernoulli 层 |
| **截断尾项上界** | $\lesssim \|\widehat g\|_{L^1(|t|>T)}$ 或 $\lesssim e^{-cT}$（解析） | 窗外能量 |

**注.** Poisson 求和与近似采样、Parseval 分解之间的等价与互推，参见 Butzer–Gessinger 等综述。

---

## 4. 相位—密度—延迟的统一刻度

### 定理 4.1（BK + Wigner–Smith）

设 $(H,H_0)$ 满足常规散射正则性（例如 $V\in L^1(\langle x\rangle,dx)$ 或相应相对迹类/Hilbert–Schmidt 条件，使谱移函数与 $S(E)$ 的可微性、BK 公式适用；参见 Yafaev 或 Sobolev 对散射理论的综述），使得 a.e. $E$ 上 $S(E)$ 存在并酉。若取 BK 号记 $\det S(E)=e^{2\pi i\xi(E)}$，并记 $\varphi(E):=\pi\,\xi(E)$（即 $\det S=e^{2i\varphi}$），则

$$
\xi'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E),\qquad
\mathsf Q(E):=-i\,S^\dagger(E)\,S'(E),
$$

从而

$$
\boxed{\ \varphi'(E)=\frac{1}{2}\operatorname{tr}\mathsf Q(E)=\pi\,\rho_{\rm rel}(E)\ },\qquad
\rho_{\rm rel}(E):=\xi'(E).
$$

**证明（要点）.** 由 BK 公式 $\det S(E)=e^{2\pi i\xi(E)}$（a.e.）取对数并微分，得 $\dfrac{d}{dE}\log\det S(E)=\operatorname{tr}(S^{-1}S')=2\pi i\,\xi'(E)$。又因 $S$ 酉，$S^{-1}=S^\dagger$，于是 $\operatorname{tr}(-iS^\dagger S')=2\pi\,\xi'(E)$，即 $\operatorname{tr}\mathsf Q(E)=2\pi\,\xi'(E)$。定义 $\varphi(E):=\pi\,\xi(E)$，则 $\varphi'(E)=\pi\,\xi'(E)=\dfrac{1}{2}\operatorname{tr}\mathsf Q(E)$，即得结论。

**号记对照.** 若取 $\det S(E)=e^{-2\pi i\xi(E)}$（部分文献的选择），则 $\xi'(E)$ 与 $\operatorname{tr}\mathsf Q(E)$ 共同变号，最终比例 $\varphi'=\tfrac{1}{2}\operatorname{tr}\mathsf Q=\pi\rho_{\rm rel}$ 保持不变。□

**权威锚点：**
- **BK 公式：** Pushnitski（Acta Math. 2008），Yafaev《Mathematical Scattering Theory》，Sobolev 综述（arXiv:1006.0639）。
- **Wigner–Smith 延迟矩阵：** Wigner（Phys. Rev. 1955）、Smith（Phys. Rev. 1960）原始论文；多通道情形见 Shimamura（J. Phys. B 2006）。

> **物理含义.** $\operatorname{tr}\mathsf Q(E)$ 为总群延迟，其与谱移导数一致即是 Friedel-型"密度—相位"规则的抽象版本。

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

**（6.2）多窗/多核与帧稳定.** 用加权多目标描述帕累托前沿；令 $\{g_m\}$ 为多窗族，帧算子 $Sf=\sum_m \langle f,g_m\rangle g_m$，存在对偶窗族 $\{\tilde g_m\}$ 使 $\sum_m \langle f,g_m\rangle \tilde g_m = f$。Wexler–Raz 双正交给出 Gabor/WH 系的必要充分条件；"painless"非正交展开提供可实现的稳定构造（参考 Daubechies–Landau、Daubechies–Grossmann–Meyer、Gröchenig 等）。

**（6.3）参考教材.** Christensen《An Introduction to Frames and Riesz Bases》对帧与对偶窗有系统陈述；Casazza 等给出 WH 帧的收敛与稳定分析。

**权威锚点：**
- **Wexler–Raz 双正交：** Daubechies, Landau, Landau（J. Fourier Anal. Appl. 1995）；原始 Janssen（Signal Processing 1998）。
- **Painless 展开：** Daubechies–Grossmann–Meyer（J. Math. Phys. 1986）；综述见 Gröchenig《Foundations of Time-Frequency Analysis》（Birkhäuser）。

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

* 若取对称 Fourier 规范 $\widehat f=(2\pi)^{-1/2}\int f e^{-ix\xi}$，则（2.1）右端无 $1/(2\pi)$ 因子。
* 恢复 $\hbar$：以 $\xi=t/\hbar$ 改写 $\widehat w_R,\widehat h,K_{\rho_\star}$ 的自变量并配套雅可比。
* BK 号记改为 $\det S=e^{-2\pi i\xi}$ 时，$\xi'$ 与 $\operatorname{tr}\mathsf Q$ 共同变号；相应地 $\varphi'=\tfrac{1}{2}\operatorname{tr}\mathsf Q$ 与 $\rho_{\rm rel}=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q$ 的比例关系 $\varphi'=\pi\,\rho_{\rm rel}$ 保持不变，等式结构不变。

---

### 附录 B：路径积分与传播子核的等价性补充

**B.1 Feynman–Kac 公式与谱表示。**
对势 $V$ 满足适当增长条件的薛定谔算子 $H=-\tfrac{1}{2}\Delta+V$，传播子核

$$
K(x_f,t;x_i,0)=\langle x_f|e^{-iHt}|x_i\rangle
$$

可经 Trotter 乘积公式与 Feynman–Kac 公式（虚时情形）得到严格版本；实时路径积分的严格化需视势函数满足的条件而定（参见 Simon《Functional Integration and Quantum Physics》或 Glimm–Jaffe《Quantum Physics: A Functional Integral Point of View》）。关键点：
- 谱定理给出 $e^{-iHt}=\int e^{-iEt}\,dE_H(E)$。
- 传播子核为 $\langle x_f|e^{-iHt}|x_i\rangle$ 在位置表象下的矩阵元。
- Feynman–Kac 给出路径积分表述（形式）；严格版本需 Wiener 测度或格点近似。

**B.2 窗化为 $w_R(E)=e^{+iEt_0}$ 与 $h=\delta$ 的极限。**
在本文采用的傅里叶规范 $\widehat f(\xi)=\int f(x)e^{-ix\xi}dx$ 下，取 $w_R(E)=e^{+iEt_0}$ 则 $\widehat w_R(t)=2\pi\delta(t-t_0)$；若 $h=\delta$，则 $\widehat h(t)=1$。代入定理 2.1 右端：

$$
\frac{1}{2\pi}\int_{\mathbb R} 2\pi\delta(t-t_0)\cdot 1\cdot K_{\rho_\star}(t)\,dt = K_{\rho_\star}(t_0).
$$

左端则为 $\int e^{+iEt_0}\rho_\star(E)\,dE = K_{\rho_\star}(-t_0)$（谱表示下的复共轭形式）。因传播子满足 $K_{\rho_\star}(-t)=\overline{K_{\rho_\star}(t)}$（当 $\rho_\star$ 为正测度或 $\rho_\star=\nu_\rho$ 且 $\rho=\rho^\dagger$ 时成立），故可通过取共轭或重新定义窗函数为 $w_R(E)=e^{-iEt_0}$（此时 $\widehat w_R(t)=2\pi\delta(t+t_0)$，需配合偶性调整变号）来恢复标准传播子形式 $K_{\rho_\star}(t_0)$。这一细节与傅里叶规范的选取密切相关；物理上两种写法等价。

**B.3 能量平滑（$h\neq\delta$）的物理解释。**
- 若 $h$ 为带限函数，对应能量域平滑/滤波；时间域为 $\widehat h(t)$ 的乘子。
- 例：取 $h$ 为高斯，则对应能量不确定度展宽；Wigner–Weyl 时频分析中等价于相空间局域化。

---

### 附录 C：Wexler–Raz 双正交与"painless"展开简要

**C.1 Wexler–Raz 恒等式。**
对 Gabor 系 $\{g_{m,n}(x)=e^{2\pi imx}g(x-na)\}$ 与对偶窗 $\{\tilde g_{m,n}\}$，Wexler–Raz 给出：

$$
\sum_{n\in\mathbb Z}\langle g,\,e^{2\pi imx}\,\tilde g(\cdot-na)\rangle = \frac{1}{a}\,\delta_{m,0}.
$$

此为 Gabor 帧的双正交必要充分条件；推广到 Weyl–Heisenberg 群的射影表示。

**C.2 "Painless"非正交展开。**
Daubechies–Grossmann–Meyer 构造：取 $a=1/b$（时频参数），选择窗使 Gabor 系为紧框架（$A=B$），则存在显式对偶窗且数值稳定。参见 Christensen 教材第 7 章与 Casazza 等综述。

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
* **Euler–Maclaurin 公式与指数收敛梯形规则：** Atkinson《An Introduction to Numerical Analysis》（Wiley）；解析/周期情形指数收敛见 Trefethen《Approximation Theory and Approximation Practice》（SIAM）。
* **帧与对偶窗、Wexler–Raz 与"painless"展开：** Daubechies, Landau, Landau（J. Fourier Anal. Appl. 1995）；Daubechies–Grossmann–Meyer（J. Math. Phys. 1986）；Christensen《An Introduction to Frames and Riesz Bases》（Birkhäuser）；Gröchenig《Foundations of Time-Frequency Analysis》（Birkhäuser）；Casazza 等综述。
* **I-投影与信息几何：** Csiszár《I-Divergence Geometry of Probability Distributions and Minimization Problems》（Ann. Probab. 1975）；Amari–Nagaoka《Methods of Information Geometry》（AMS）。

（全文所用外部结论均为标准判据；涉及可能随规范变化的常数/符号已在相应处固定或注明依赖。）
