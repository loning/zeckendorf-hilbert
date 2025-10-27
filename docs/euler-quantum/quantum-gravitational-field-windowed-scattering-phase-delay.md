# 量子引力场：以窗化散射相位—延迟—谱移为刻度的统一理论

*Quantum Gravitational Field as a Windowed Scattering Phase–Delay–Spectral-Shift Measure*

---

## 摘要

本文提出一套**完全以可观测量刻度**的量子引力场理论：对给定时空几何 $g$ 与参考几何 $g_0$，以其定能散射矩阵 $S_g(E)$ 的能量导数所定义的 **Wigner–Smith 延迟算子** $Q_g(E)=-i\,S_g(E)^\dagger \partial_E S_g(E)$ 为核心，定义**相对态密度**（relative density of states, rDOS）

$$
\rho_{\mathrm{rel},g}(E)\;=\;\frac{1}{2\pi i}\,\mathrm{tr}\!\big(S_g^\dagger \partial_E S_g\big)\;=\;\frac{1}{2\pi}\,\mathrm{tr}\,Q_g(E).
$$

在满足 Birman–Kreĭn（BK）公式 $\det S_g(E)=\exp[-2\pi i\,\xi_g(E)]$ 的一般散射框架下，有 $\rho_{\mathrm{rel},g}(E)=-\xi_g'(E)$，其中 $\xi_g$ 为 Kreĭn 谱移函数；这统一了**相位—延迟—谱移**三者的刻度关系，并与 Friedel/Smith 关系一致。注：本文中 $Q=-iS^\dagger\partial_E S$ 的自然单位为能量$^{-1}$，物理时间延迟为 $\hbar Q$。我们以**窗化观测**实现实验分辨率内的可测读数：选取满足 Wexler–Raz 双正交与 Gabor 帧必要密度（$\Delta E\,\Delta t/(2\pi\hbar)\le 1$）的窗—对偶核 $(w,\tilde w)$，定义

$$
\mathcal N_{w}[g;E_0]\;=\;\int_{\mathbb R} w(E-E_0)\,\rho_{\mathrm{rel},g}(E)\,dE,
$$

并给出**窗化 BK 恒等式**与**非渐近误差三分解**（混叠/Poisson＋伯努利层/Euler–Maclaurin＋截断）。在渐近平直/双曲流形的几何散射、定常弱场的 Shapiro 引力时延、及含吸收（如黑洞外区）的非幺正散射中，我们证明：(**不变性**) 对微分同胚/幺正等价不变；(**可加性**) 级联散射的 rDOS 可加；(**半经典极限**) 窗化 rDOS 由周期测地流长度谱控制，并在低频极限回到经典驻留时间与 Shapiro 时延。本文并给出面向数值的可复现实验流程与与既有量子引力/S-matrix/几何散射文献的接口。

---

## 关键词

Wigner–Smith 延迟；Krein 谱移；Birman–Kreĭn 公式；Friedel/Smith 关系；窗化观测；Gabor/Weyl–Heisenberg 框架；Landau 采样密度；流形散射；Shapiro 延迟

---

## 1. 引言（以可观测量刻度）

散射相位与能量导数给出 DOS 的事实自 Beth–Uhlenbeck 与 Friedel 以来已广泛确立；在现代散射理论中，这由 BK 公式严格化为

$$
\det S(E)=e^{-2\pi i\,\xi(E)},\qquad
\xi'(E)=-\tfrac{1}{2\pi i}\mathrm{tr}\!\big(S^\dagger \partial_E S\big),
$$

因而 $\rho_{\mathrm{rel}}(E)=\frac{1}{2\pi i}\mathrm{tr}(S^\dagger \partial_E S)=-\xi'(E)$。这同时等价于以 Wigner–Smith 延迟算子 $Q=-iS^\dagger \partial_E S$ 计量的驻留时间总和。上述等价在数学物理中具有标准而严密的表述（BK 与谱移函数理论），在物理上与 Friedel/Smith 关系吻合。

几何散射方面，对渐近平直/长程度量/双曲几何之拉普拉斯–Beltrami（或 Klein–Gordon）算子存在完备的能量壳散射矩阵与微局部结构；散射矩阵在能量纤维上是与无穷远测地流相关的 Fourier 积分算子，这为将 DOS 的几何来源解释为**谱流**提供了严格基础。

本文主张：**量子引力场**可操作地定义为**窗化的相对 DOS**，即 $\rho_{\mathrm{rel},g}(E)$ 及其在仪器分辨率内的读数 $\mathcal N_w[g;E_0]$。该定义基于可观测的散射矩阵 $S_g(E)$，通过 $\arg\det S$ 的能量导数或 Wigner–Smith 延迟算子 $Q$ 的迹计量，天然具备：(i) 微分同胚/幺正等价下不变；(ii) 级联散射的可加性；(iii) 半经典极限与波迹/测地谱的 Poisson 关系；(iv) 非幺正散射（吸收）的复延迟推广。

---

## 2. 设定与记号

### 2.1 几何与算子

设 $(M,g)$ 为带一个或多个非紧端的光滑流形，满足渐近 Euclid（或渐近双曲/长程）条件；令 $H_g=-\Delta_g$（或含合适短/长程势的自伴变体）。取参考几何 $(M,g_0)$ 与 $H_{g_0}$。假设成对 $(H_g,H_{g_0})$ 满足**相对迹类**条件，即存在 $z\in\rho(H_{g_0})$ 使

$$
(H_g-H_{g_0})(H_{g_0}-z)^{-1}\in\mathfrak{S}_1,
$$

其中 $\mathfrak{S}_1$ 为迹类算子理想。在此条件下，谱移函数 $\xi_g(E)$ 与能量壳散射矩阵 $S_g(E)$ 良定，且 BK 公式 $\det S_g(E)=e^{-2\pi i\xi_g(E)}$ 成立。

### 2.2 以 rDOS 定义量子引力场

$$
\boxed{\;\rho_{\mathrm{rel},g}(E)\;=\;\frac{1}{2\pi i}\,\mathrm{tr}\!\big(S_g^\dagger \partial_E S_g\big)\;=\;\frac{1}{2\pi}\,\mathrm{tr}\,Q_g(E)\;=\;-\xi_g'(E);}
$$

其中 $Q_g(E)=-iS_g^\dagger \partial_E S_g$ 为**能量导相延迟算子**（自然单位为能量$^{-1}$，物理时间延迟为 $\hbar Q_g$）。此定义等价于能量分辨的总驻留时间密度，亦即"几何相对 DOS"。

### 2.3 窗化观测与对偶窗

**Fourier 规范声明**：本文固定能量—时间 Fourier 对偶为

$$
\widehat{f}(t)=\frac{1}{2\pi\hbar}\int_{\mathbb R} f(E)\,e^{-iEt/\hbar}\,dE,\qquad
f(E)=\int_{\mathbb R}\widehat{f}(t)\,e^{iEt/\hbar}\,dt;
$$

凡涉及 $\widehat{w}$、Poisson 求和与 Gabor 密度的常数/相位，均以此规范计量。

取 $w\in\mathcal S(\mathbb R)\cap L^1$ 为能量窗（无量纲归一化），$\tilde w$ 为其 Gabor 对偶。在能量—时间 $(E,t)$ 表示中，取调制算子 $M_\tau f(E)=e^{i\tau E/\hbar}f(E)$。采用**规范化内积** $\langle f,g\rangle_{E}=\frac{1}{2\pi\hbar}\int_{\mathbb R}\overline{f(E)}g(E)\,dE$（带度量因子 $1/(2\pi\hbar)$，确保归一化常数无量纲）。

对窗对 $(w,\tilde w)$ 与格点步长 $(\Delta E,\Delta t)$，**Wexler–Raz 双正交**（无求和版本）为

$$
\Big\langle \tilde w,\, M_{m\Delta t}\,T_{n\Delta E}\,w\Big\rangle_{E}
=\frac{\Delta E\,\Delta t}{2\pi\hbar}\,\delta_{m0}\,\delta_{n0}.
$$

窗化读数定义为

$$
\mathcal N_{w}[g;E_0]=\int_{\mathbb R} w(E-E_0)\,\rho_{\mathrm{rel},g}(E)\,dE.
$$

Gabor 帧的**必要密度**条件为 $\Delta E\,\Delta t/(2\pi\hbar)\le 1$（帧的必要条件）；**Riesz 基**情形取等号（$=1$）并受 Balian–Low 限制。

---

## 3. 主定理（刻度与不变性）

### 定理 3.1（相位—DOS—延迟恒等式）

在 2.1 的假设下，

$$
\rho_{\mathrm{rel},g}(E)=\frac{1}{2\pi i}\,\mathrm{tr}\!\big(S_g^\dagger \partial_E S_g\big)
=\frac{1}{2\pi}\,\mathrm{tr}\,Q_g(E)=-\xi_g'(E).
$$

**证明（要点）**：BK 公式给出 $\log\det S_g(E)=-2\pi i\,\xi_g(E)$。微分并用 $\partial_E\log\det S=\mathrm{tr}(S^{-1}\partial_E S)=\mathrm{tr}(S^\dagger\partial_E S)$（幺正时 $S^{-1}=S^\dagger$），即
$\mathrm{tr}(S^\dagger \partial_E S)=-2\pi i\,\xi_g'(E)$，得第一与第三等号；再由 $Q=-iS^\dagger \partial_E S$ 得中间等号。∎

### 定理 3.2（窗化 BK 恒等式，幺正情形）

对任意 $h\in C_c^\infty(\mathbb R)$，

$$
\int h(E)\,\rho_{\mathrm{rel},g}(E)\,dE
= -\frac{1}{2\pi i}\int h(E)\,\partial_E\log\det S_g(E)\,dE
= \frac{1}{2\pi}\int h'(E)\,\arg\det S_g(E)\,dE.
$$

**证明**：由定理 3.1 与分部积分，端点由紧支撑保证消失。此处 $\log\det S$ 取连续解卷绕的 $\arg\det S$ 分支；阈值/束缚态处的跳变以分布意义计入窗化积分。∎

### 定理 3.3（级联可加性）

若相对于同一参考 $g_0$，有能量壳级联 $S_{g_2\circ g_1}(E)=S_{g_2}(E)S_{g_1}(E)$，则

$$
\rho_{\mathrm{rel},g_2\circ g_1}=\rho_{\mathrm{rel},g_2}+\rho_{\mathrm{rel},g_1}.
$$

**证明**：$\log\det(S_2S_1)=\log\det S_2+\log\det S_1+2\pi i\,k(E)$，其中 $k(E)$ 为**分段常数整数**（对应行列式的分支选择）。对 $E$ 微分后 $k'(E)=0$（作为分布，除非在相位跃迁/束缚态阈值处可能出现 $\delta$-型跃变）。在窗化 BK 恒等式（定理 3.2，幺正情形）中，分部积分使端点/跃变项由窗函数紧支撑消去或合并到 $h'$ 中；套用定理 3.2 即得。∎

### 定理 3.4（微分同胚/幺正不变性）

若 $g'=\phi^*g$ 为**保持渐近结构/散射边界接触结构**的微分同胚拖曳，则存在幺正 $U$ 使 $S_{g'}(E)=U^\dagger S_g(E)U$。因此 $\mathrm{tr}\,Q$ 与 $\rho_{\mathrm{rel}}$ 不变。

**证明**：在渐近平直/双曲流形上，散射矩阵是与无穷远测地流相关的 Fourier 积分算子（FIO），几何散射的函子性保证：当 $\phi$ 保持散射结构时，波算子/散射矩阵在能量纤维上以幺正（微局部）共轭方式变换；迹不变性即得。∎

---

## 4. 几何散射、半经典极限与波迹

### 4.1 几何散射的能量纤维结构

**假设（FIO 结构）**：在渐近平直流形上，散射度量 $g$ 与参考度量 $g_0$ 的差为**短程扰动**，满足以下条件：

(i) **衰减率**：度量扰动 $|g-g_0|+r|\partial(g-g_0)| = O(r^{-\rho})$，$\rho>1$；

(ii) **正则性**：度量及势属 $C^\infty$ 且高阶导数满足配套衰减；

(iii) **无陷波/无束缚连续谱**：确保散射算子的 Fredholm 性质。若存在陷波，以 $0$-trace 正则化处理（Melrose–Zworski 框架）；

(iv) **辐射边界条件**：在无穷远处波场满足 Sommerfeld 出射条件。

在此假设下，散射矩阵 $S_g(E)$ 是与无穷远处测地流在时间 $\pi$（对应半波群 $e^{-i\pi\sqrt{\Delta}}$）的典范变换相关的 Fourier 积分算子（FIO）；此结构与 Melrose–Zworski、Christiansen–Joshi、Hassell–Vasy 等结果一致。该 FIO 结构保证了散射矩阵在能量纤维上的微局部性质与几何不变性。

### 4.2 波迹与周期测地流（Poisson 关系）

在双曲/凸余紧背景下，波群的正则化迹（$0$-trace）满足 Poisson/Selberg-型公式：闭合测地的长度谱控制波迹奇点位置与权重；因此窗化的 $\rho_{\mathrm{rel}}$ 在半经典极限 $\hbar\to 0$ 由周期测地贡献主导。

### 定理 4.1（半经典窗化极限）

假设流形为**双曲/凸余紧背景**或渐近平直流形且周期测地轨道为**清洁交会（clean）/非退化**。取 $w$ 为尺度 $\sigma$ 的平滑窗，令 $\widehat{w}$ 支撑于 $|t|\lesssim \sigma^{-1}$。当 $\hbar\to 0$ 且 $\sigma$ 与几何注入半径/弛豫时间匹配时，

$$
\mathcal N_{w}[g;E_0]\;=\;\sum_{\gamma\in\mathcal P}\,A_\gamma(E_0)\,\widehat{w}(T_\gamma)\,e^{i S_\gamma(E_0)/\hbar}\;+\;o(1),
$$

其中 $\mathcal P$ 为周期测地族，$T_\gamma$ 其周期，$S_\gamma$ 为经典作用量，$A_\gamma$ 含稳定子与 monodromy 的标准因子。

**证明（要点）**：在上述几何假设下，波群的正则化迹（**0-trace**）满足 Poisson/Selberg-型公式：奇性支撑位于长度谱 $\{T_\gamma\}$。结合定理 3.2 与波迹公式，把 $\arg\det S$ 的能量导数转化到时间域后，以平稳相位法得到；正则化与非退化条件保证级数收敛与余项估计。该陈述在几何假设"清洁/非退化周期测地"与"凸余紧/渐近平直"下严格成立，完整证明见 Melrose–Zworski 散射微积分框架、Duistermaat–Guillemin 波迹公式、Colin de Verdière 之波迹综述及 Borthwick、Guillarmou–Naud 双曲流形专论。∎

### 4.3 宏观极限与 Shapiro 延迟

定常弱场中，$\mathcal N_{w}$ 的低频极限回到 Shapiro 引力时延；具体地，$\partial_E\arg\det S$ 以平均群时延表示，等价于经典传播时间的引力增量。在参数化后牛顿（PPN）框架下，对单程近轴近似，Shapiro 时延公式为

$$
\Delta t \;\approx\; (1+\gamma)\frac{GM}{c^3}\log\frac{4r_1 r_2}{b^2},
$$

其中 $b$ 为最近逼近距（冲量参数），$r_1,r_2$ 为初/末位置的径向距离，$\gamma$ 为 PPN 参数（广义相对论中 $\gamma=1$）。Cassini 实验（Bertotti et al. 2003, Nature **425**, 374）通过雷达回波精确测量了日面掠射引力时延，得到 $\gamma=1+(2.1\pm2.3)\times10^{-5}$，验证了广义相对论至 $10^{-5}$ 量级；此结果与本文窗化 rDOS 的低频极限相吻合。完整的参考时校准与 PPN 系数计量见 Ashby (2010, NIST Special Publication 1198)。

---

## 5. 非幺正散射与复时间延迟

在存在吸收/泄露（如黑洞外区、耗散开口系统）时，$S_g(E)$ 非幺正，$S^{-1}\neq S^\dagger$。此时**复时间延迟**定义为

$$
\tau(E)=-\frac{i}{N}\,\partial_E\log\det S_g(E)\in\mathbb C,
$$

等价地可写为 $\tau(E)=\frac{1}{N}\,\mathrm{tr}(S_g^{-1}\partial_E S_g)$。其实部 $\mathrm{Re}\,\tau=\frac{1}{N}\partial_E\arg\det S$ 对应相位导数与驻留时间，虚部 $\mathrm{Im}\,\tau=\frac{1}{N}\partial_E\log|\det S|$ 刻画吸收度。当 $S$ 为次幺正时，$\rho_{\mathrm{rel}}^{(\mathrm{eff})}=\frac{1}{2\pi}\partial_E\arg\det S$ 仅刻画"相位"部分；$\mathrm{Im}\,\tau$ 刻画吸收强度，与 $S$-矩阵极点/共振及**相干完美吸收**（CPA）条件直接相关。**CPA 条件**要求 $\det S(E_0)=0$（Chong et al. 2010, Phys. Rev. Lett. **105**, 053901），此时共振能量 $E_0$ 处 $\mathrm{Re}\,\tau$ 与 $\mathrm{Im}\,\tau$ 的峰—峰对齐指示共振零—极互补。rDOS $\nu(E)=\tfrac{1}{2\pi}\mathrm{tr}\,Q(E)$ 与 $S$-矩阵极点/零点的统计分布存在定量联系，在随机矩阵理论与开口腔体系统中已有系统性结果（Brouwer–Beenakker 1997; Cunden et al. 2015; Chen et al. 2021）。

相应地，定义**有效 rDOS** 为

$$
\rho_{\mathrm{rel},g}^{(\mathrm{eff})}(E)=\frac{1}{2\pi}\,\partial_E\arg\det S_g(E)=\frac{1}{2\pi}\,\mathrm{Im}\,\partial_E\log\det S_g(E),
$$

在幺正极限 $S^\dagger S=I$ 时，$|\det S|=1$ 且上式退化为定理 3.1。注：此处复延迟 $\tau$ 的自然单位为能量$^{-1}$，物理时间延迟为 $\hbar\tau$。

---

## 6. 窗化采样与误差的非渐近闭合

### 6.1 采样可实现性：Wexler–Raz 与采样密度

选择 $(\Delta E,\Delta t)$ 与窗对 $(w,\tilde w)$ 使 Gabor 系形成帧/基，并满足 Wexler–Raz 双正交。对**能量窗化后的光滑带限近似**，可用 Landau 必要密度（Paley–Wiener 类）估计采样下界；对一般 Gabor 帧，**必要密度条件** $\Delta E\,\Delta t/(2\pi\hbar)\le 1$。**Riesz 基**情形取等号 $\Delta E\,\Delta t/(2\pi\hbar)=1$ 并受 Balian–Low 约束（时—频同时集中不可能）；稠密帧情形 $\Delta E\,\Delta t/(2\pi\hbar)<1$ 较稳健且数值上更实用。完整密度理论参见 Daubechies (1992) 与 Gröchenig (2001)。这给出从离散能量网格对 $\rho_{\mathrm{rel}}$ 进行稳定估计的充分—必要准则。

### 6.2 误差三分解：混叠＋伯努利层＋截断

令采样步长为 $\Delta E$，截断到有限窗 $I=[E_{\min},E_{\max}]$。对平滑 $f=\rho_{\mathrm{rel}}\!*w$ 应用 Poisson 求和（在 §2.3 固定的 Fourier 规范下）：

$$
\sum_{n\in\mathbb Z} f(E_0+n\Delta E)
= \frac{1}{\Delta E}\sum_{k\in\mathbb Z}
e^{\,i2\pi k E_0/\Delta E}\,
\widehat{f}\!\left(\frac{2\pi\hbar k}{\Delta E}\right)
\quad\text{（Poisson）},
$$

其中 $\widehat{f}(t)=\frac{1}{2\pi\hbar}\int f(E)e^{-iEt/\hbar}\,dE$。非零 $k$ 项即**混叠**；对有限求和/积分差，Euler–Maclaurin（EM）给出**伯努利层**显式余项（适用条件：$f^{(2m)}\in L^\infty$、端点可导，以 $B_{2m}$ 与边界高阶导数表出至 $2m$ 阶）；截断带来第三类误差。三者相加即总误差的**非渐近闭合**。

---

## 7. 物理后果与可检验预测

1. **相位台阶与束缚态计数（Levinson/Friedel–Kreĭn 型）**：$\arg\det S$ 对 $E$ 的累计跳变与低能相移之和及束缚态数目相关；Friedel–Kreĭn 关系给出 $\Delta_E[\arg\det S/(2\pi)] = n_{\text{bound}} + \text{修正项}$，其中 $n_{\text{bound}}$ 为束缚态数。故 $\int^E \rho_{\mathrm{rel}}\,dE'$ 呈整数级跃迁，与拓扑相位联系紧密。关于计数式与谱移函数/相位台阶的联系及常见修正项（半束缚态、简并、多通道情形），见 Martin (2006, J. Phys. A: Math. Gen. **39**, R625) 之 Levinson 定理拓扑综述及 Kreĭn 原始结果。
2. **共振与延迟峰值**：Breit–Wigner 近似下，$\mathrm{tr}\,Q(E)$ 在 $E_0$ 处出现峰值，半高宽 $\Gamma$ 与寿命由 $\mathrm{Re}\,\tau$ 定量关联；在非幺正系统中，$\mathrm{Im}\,\tau$ 还指示极点分布与 CPA 条件。
3. **引力透镜/脉冲时延**：多路径干涉在 $\mathcal N_w[g;E]$ 中留下能量依赖的相位—延迟纹理；对 FRB/脉冲星的多频测量可直接估计窗化 rDOS 的纹理。

---

## 8. 数学证明与技术细节

### 8.1 BK 公式与谱移函数

在相对迹类假设下（或适当的相对可追性/光滑假设），谱移函数 $\xi_g$ 由

$$
\mathrm{tr}\big(\varphi(H_g)-\varphi(H_{g_0})\big)=\int_{\mathbb R}\varphi'(E)\,\xi_g(E)\,dE,\qquad \forall \varphi\in C_c^\infty(\mathbb R),
$$

唯一决定。对能量壳散射矩阵 $S_g(E)$ 成立 BK 公式 $\det S_g(E)=e^{-2\pi i\xi_g(E)}$，且 $\xi_g$ 的绝对连续部分满足定理 3.1。

### 8.2 流形散射与能量纤维

渐近平直/长程背景下，散射理论与散射微积分保证 $S_g(E)$ 的良定、幺正性（无吸收时）及其与无穷远测地流的 FIO 关联；这使定理 4.1 的半经典陈述可由波迹–长度谱公式导出。

### 8.3 Wigner–Smith 延迟的算子表达

多通道情形 $Q(E)=-iS^\dagger \partial_E S$ 自然推广；在电磁/声学等波动系统亦成立并可转写为能量密度积分的体/边表示。具体地，**局域 DOS 表示**（Lloyd/Friedel–Kreĭn 关系）给出

$$
\mathrm{tr}\,Q(E) = 2\pi\,\partial_E N(E),\qquad N(E)=\int_{\Omega}\mathrm{LDOS}(E,\mathbf{r})\,d\mathbf{r},
$$

其中 LDOS（局域态密度）可由散射格林函数 $G(E,\mathbf{r},\mathbf{r}')$ 虚部给出；这便于数值实现与材料色散/损耗处理。详见 Akkermans–Montambaux (2007, §5.2) 与 arXiv:cond-mat/0112225（图散射 Friedel 求和规则）。

### 8.4 非幺正推广与统计性质

对次幺正 $S$，定义复延迟 $\tau$ 并建立与 $S$-矩阵极点分布的统计联系；在随机矩阵理论与开口腔体实验中，$\mathrm{Re}\,\tau$ 的分布与零点—极点统计存在定量关系（Brouwer 1997, Phys. Rev. Lett. **78**, 4737; Cunden et al. 2015; Chen et al. 2021），可用于推断共振寿命与吸收通道结构。

### 8.5 窗化采样与误差界

Wexler–Raz 身份刻画对偶窗；Landau 密度给出必要下界。Poisson 求和与 EM 余项一起构成误差的**非渐近闭合**：对 $2m$ 阶光滑窗，EM 余项界与 $|f^{(2m)}|_\infty$ 成正比，混叠项由 $\widehat f$ 在频域栅点的衰减控制。

---

## 9. 数值实现（可复现流程）

**输入**：几何/折射率模型 $g$ 与参考 $g_0$，窗 $w$ 与对偶 $\tilde w$，采样步长 $\Delta E$。

1. **定能散射求解**：在能量网格 $\{E_j\}$ 上求 $S_g(E_j)$（几何散射坐标或 PML 处理辐射条件）。
2. **能量导数**：若求解器支持复能量，用**复步差分**（complex-step derivative）计算 $\partial_E S_g(E_j)\approx [S_g(E_j+i\epsilon)-S_g(E_j-i\epsilon)]/(2i\epsilon)$，得 $Q_g(E_j)=-iS_g^\dagger \partial_E S_g$；复步差分避免消去误差，精度高且数值稳定。若仅支持实能量点，采用**中心差分** $\partial_E S_g(E_j)\approx [S_g(E_j+\delta)-S_g(E_j-\delta)]/(2\delta)$。对于 rDOS，也可直接计算 $\arg\det S_g(E_j)$：先对 $\det S$ 执行**相位解卷绕**（unwrapping）以避免 $2\pi$ 跳变，再用数值导数得 $\partial_E\arg\det S$；**建议同时计算** $\rho_{\mathrm{rel}}=\tfrac{1}{2\pi}\mathrm{tr}\,Q$ 与 $\rho_{\mathrm{rel}}=\tfrac{1}{2\pi}\partial_E\arg\det S$ 并**交叉校核**以排除数值噪声。
3. **rDOS 与窗化**：$\rho_{\mathrm{rel}}(E_j)=\tfrac{1}{2\pi}\mathrm{tr}\,Q_g(E_j)$ 或 $\rho_{\mathrm{rel}}(E_j)=\tfrac{1}{2\pi}\partial_E\arg\det S_g(E_j)$；执行离散卷积 $\mathcal N_w[g;E_k]=\sum_j w(E_k-E_j)\rho_{\mathrm{rel}}(E_j)\Delta E$。
4. **采样与误差控制**：选 $\Delta E$ 小于窗主瓣带宽的 $1/5\sim 1/10$ 以满足 Nyquist 判据；检查 Gabor 帧密度 $\Delta E\,\Delta t/(2\pi\hbar)\le 1$；以 $|\widehat f(2\pi\hbar k/\Delta E)|$ 估计混叠（§6.2 Poisson 公式）；用 $2m$ 阶 EM 余项界（取 $2m=4$ 为保守选择）与边界修正量化截断误差。

---

## 10. 与现有量子引力/信息框架的接口

* **S-matrix 取向**：本文以 $S(E)$ 为原始对象，强调定能、低能与弯曲背景的一致可观测刻度，兼容 S-matrix 与天球全息的可观测性立场。
* **宏观极限**：$\mathcal N_w$ 的低频极限回到 Shapiro 时延/经典驻留时间；半经典区由测地谱控制。
* **信息论单调性**：窗化/粗粒化视为 CPTP/正保持映射下统计区分度的降低；量子相对熵的**数据处理不等式**保证任何后端读出与通道噪声只会降低可判别度，从而使本刻度**保守**（单调）且具有比较意义。

---

## 11. 与 WSIG-QM / UMS / S-series 的接口

**11.1 与 WSIG-QM 的接口。**
- WSIG-QM 的公理 A5（相位—密度—延迟刻度）与本文定理 3.1 采用完全一致的 BK 号记与 Wigner–Smith 定义：$\rho_{\mathrm{rel}}(E)=\tfrac{1}{2\pi}\mathrm{tr}\mathsf Q(E)$，$\varphi'(E)=\pi\rho_{\mathrm{rel}}(E)=\tfrac{1}{2}\mathrm{tr}\mathsf Q(E)$。
- WSIG-QM 的公理 A2（有限窗口读数）直接对应本文 2.3 的窗化观测 $\mathcal N_w[g;E_0]$。
- WSIG-QM 的定理 T1（窗口化读数恒等式与非渐近误差闭合）与本文 6.2 的误差三分解共享 Nyquist–Poisson–EM 框架。
- 本文的量子引力场定义 $\rho_{\mathrm{rel},g}$ 可视为 WSIG-QM 在几何散射语境下的具体实现。

**11.2 与 UMS 的接口。**
- UMS 的核心统一式 $d\mu_\varphi = \tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\,dE = \rho_{\mathrm{rel}}\,dE = \tfrac{\varphi'}{\pi}\,dE$ 与本文定理 3.1 完全一致。
- 本文的窗化 BK 恒等式（定理 3.2）为 UMS 的谱—窗化字典提供几何散射情形的具体表述。
- UMS 的公理 A7（通道—单调—容量）与本文 §10 的信息论单调性（DPI）共享数据处理不等式框架。

**11.3 与窗口化路径积分理论的接口。**
- 窗口化路径积分理论的核心定理 2.1（窗—核对偶）可在几何散射语境下改写为：$\mathcal N_w[g;E_0] = \tfrac{1}{2\pi}\int \widehat w(t)\,\mathrm{tr}(e^{-iH_g t})\,dt$。
- 本文的定理 3.2（窗化 BK 恒等式）为路径积分理论的能量—时间对偶提供几何化表述。
- 两理论共享 Nyquist–Poisson–EM 误差闭合框架。

**11.4 与 S15–S26 的接口。**
- S15–S17 的 Herglotz 表示与规范系统为本文的谱移函数 $\xi_g(E)$ 提供解析结构。
- S24–S26 的 Wexler–Raz 双正交、Landau 必要密度与 Balian–Low 不可能性为本文 2.3 与 6.1 的窗化采样提供具体判据。
- S21–S23 的有限阶 EM 纪律直接支撑本文 6.2 的误差闭合框架。

**11.5 与 CCS（协变多通道）的接口。**
- CCS 的窗化 Birman–Kreĭn 恒等式与本文定理 3.2 在多通道散射情形下完全一致。
- CCS 的 Wigner–Smith 群延迟矩阵定义与本文 2.2 采用相同约定。
- 本文的非幺正推广（§5）可视为 CCS 在含吸收散射情形下的几何化版本。

**11.6 与 EBOC-Graph 的接口。**
- EBOC-Graph 的定理 G4（非渐近误差闭合）与本文 6.2 的三分解在离散谱/图信号情形下共享框架。
- 本文的几何散射可在图/格点系统上离散化，将连续能量谱替换为图拉普拉斯谱，与 EBOC-Graph 的图谱滤波统一。

**11.7 保持"极点 = 主尺度"的有限阶 EM 纪律。**
- 本文在所有离散—连续换序中均采用**有限阶** EM（§6.2），确保散射极点（共振/束缚态能量）始终为"主尺度"标记。
- 与 WSIG-QM、UMS、S15–S26 保持一致：EM 余项仅作有界扰动，不引入新奇点。

---

## 结论

以 $\rho_{\mathrm{rel},g}(E)=\frac{1}{2\pi}\mathrm{tr}\,Q_g(E)=-\xi_g'(E)$ 为核心的**窗化相对 DOS** 及其仪器分辨率读数 $\mathcal N_w[g;E_0]$，为量子引力场提供了**完全基于可观测量、操作性、比较性与重正化-无关**的刻度：

(1) 与 Birman–Kreĭn、Wigner–Smith、Friedel/Smith 的标准散射理论判据严格一致；

(2) 在几何散射框架中具备良好存在性、微分同胚/幺正等价不变性，并以 FIO 结构与无穷远测地流对接；

(3) 级联散射的可加性（定理 3.3），分支处理清晰；

(4) 半经典极限与波迹/测地长度谱的 Poisson 公式吻合，宏观极限回到 Shapiro 引力时延；

(5) 可经 Gabor 窗化采样在实验上直接读出，并有明确的非渐近误差预算（Poisson 混叠 + EM 伯努利层 + 截断）；

(6) 可自然推广到非幺正/吸收场景（复时间延迟 $\tau=-\frac{i}{N}\partial_E\log\det S$），并与 CPA 条件及共振极点统计对接。

该框架以**相位—延迟—谱移**为唯一主线，将经典-量子与几何-信息的刻度统一到一个可验证、可数值实现且可与天文/实验数据直接对接的体系中。

---

### 参考要点与依据（按主题摘引）

* **BK 公式与谱移函数**：$\det S=e^{-2\pi i\xi}$、$\xi'(E)=-\tfrac{1}{2\pi i}\mathrm{tr}(S^\dagger S')$ 的数学物理严格化与相对迹类条件。
* **Wigner–Smith 延迟**：$Q=-iS^\dagger \partial_E S$ 的定义、物理解释与多物理场推广（电磁/声学、含色散与损耗）。
* **几何散射**：渐近平直/长程情形的散射微积分与 $S(E)$ 的 FIO 结构。
* **波迹与长度谱/Poisson**：双曲背景与 $0$-trace 的 Poisson-/Selberg-型公式。
* **非幺正/复延迟与极点统计**：复延迟的理论与实验、极点计数联系。
* **Wexler–Raz 与 Landau 采样下界**：窗对的双正交与必要密度。
* **Poisson 求和与 Euler–Maclaurin**：误差三分解的基础与非渐近界。
* **Shapiro 引力时延（宏观极限）**：历史测试与公式来源。
* **Levinson-型结论**：相位台阶/束缚态计数之拓扑化综述。
* **数据处理不等式/相对熵单调性**：粗粒化/通道下可判别度单调降低之严密依据。

---

## 附录 A：窗化 BK 恒等式的细化证明

取 $h\in C_c^\infty$。在幺正情形，由定理 3.1，

$$
\int h\,\rho_{\mathrm{rel}}\,dE
= -\frac{1}{2\pi i}\int h\,\partial_E\log\det S\,dE
= \frac{1}{2\pi i}\int h'\,\log\det S\,dE.
$$

将 $\log\det S$ 分解为实部 $\log|\det S|$ 与虚部 $i\arg\det S$；幺正时 $|\det S|=1$，得到

$$
\int h\,\rho_{\mathrm{rel}}\,dE = \frac{1}{2\pi}\int h'\,\arg\det S\,dE.
$$

对非幺正情形，定义有效 rDOS 为 $\rho_{\mathrm{rel}}^{(\mathrm{eff})}=\tfrac{1}{2\pi}\partial_E\arg\det S=\tfrac{1}{2\pi}\mathrm{Im}\,\partial_E\log\det S$，仅保留相位导数部分，吸收率部分由 $\mathrm{Im}\,\tau=\tfrac{1}{N}\partial_E\log|\det S|$ 单独刻画。

## 附录 B：误差三分解的显式上界

令 $f=\rho_{\mathrm{rel}}\!*w$ 且 $f^{(2m)}\in L^\infty$、端点可导。对有限求和 $\sum_{n=a}^{b} f(E_0+n\Delta E)$ 与 $\Delta E\int_a^b f(x)\,dx$ 的差，**Euler–Maclaurin 公式**（到 $2m$ 阶）给出

$$
\Delta E\sum_{n=a}^{b} f(E_0+n\Delta E) - \int_{E_0+a\Delta E}^{E_0+b\Delta E} f(x)\,dx
=\sum_{j=1}^{m}\frac{B_{2j}}{(2j)!}(\Delta E)^{2j}\big(f^{(2j-1)}(b)-f^{(2j-1)}(a)\big)
+R_{2m},
$$

其中 $B_{2j}$ 为伯努利数，$|R_{2m}|\le C_m\,|f^{(2m)}|_\infty\,(\Delta E)^{2m}(b-a)$，常数 $C_m$ 可由伯努利周期多项式的 $L^1$ 范数界出。混叠项由 $\frac{1}{\Delta E}\sum_{k\neq0}|\widehat f(2\pi\hbar k/\Delta E)|$ 控制（§6.2 Poisson 公式）；截断项按窗衰减指数界定。

## 附录 C：非幺正情形的 rDOS 与复延迟

定义 $\rho_{\mathrm{rel}}^{(\mathrm{eff})}=\tfrac{1}{2\pi}\,\partial_E\arg\det S$。对非幺正 $S$，复时间延迟 $\tau=-\frac{i}{N}\partial_E\log\det S$ 分为实部（相位导数，对应驻留时间）与虚部（吸收率导数）。$\mathrm{Re}\,\tau$ 的分布统计与 $S$-矩阵零点—极点结构存在定量联系，在随机矩阵理论与开口腔体中已有系统性实验验证（Brouwer 1997; Cunden et al. 2015）。

**CPA 条件与双洛伦兹形**：在共振能量 $E_0$ 附近，当 $\det S(E_0)=0$（相干完美吸收），$\tau(E)$ 展现**双洛伦兹**结构：$\mathrm{Re}\,\tau$ 在 $E_0$ 处峰值（Breit–Wigner 型），$\mathrm{Im}\,\tau$ 在同一位置呈现吸收极大；此时 $S$-矩阵在复平面的零点与极点互补。

**复现实验指引**：对 $\det S(E)$ 的幅相同测，$\mathrm{Re}\,\tau$ 与 $\mathrm{Im}\,\tau$ 的峰-峰对齐指示 CPA/共振零极互补。数值上可通过测量 $S(E)$ 的幅相并以复步差分求 $\partial_E S$ 得到，或直接对 $\arg\det S$ 解卷绕后差分；二者可交叉校核稳健性。

---

## 附录 D：符号对照与单位

**核心量定义**：

| 符号 | 定义 | 物理意义 | 单位 |
|------|------|----------|------|
| $S_g(E)$ | 能量壳散射矩阵 | 几何 $g$ 的定能散射算子 | 无量纲 |
| $Q_g(E)$ | $-iS_g^\dagger \partial_E S_g$ | 能量导相延迟算子（物理时间延迟为 $\hbar Q_g$） | 能量$^{-1}$ |
| $\xi_g(E)$ | 谱移函数，$\det S_g=e^{-2\pi i\xi_g}$ | 相对累积态密度（BK） | 无量纲 |
| $\rho_{\mathrm{rel},g}(E)$ | $\tfrac{1}{2\pi i}\mathrm{tr}(S^\dagger\partial_E S)=-\xi_g'$ | 相对态密度 | 能量$^{-1}$ |
| $\tau(E)$ | $-\tfrac{i}{N}\partial_E\log\det S$ | 平均复延迟（物理时间延迟为 $\hbar\tau$） | 能量$^{-1}$ |
| $\mathcal N_w[g;E_0]$ | $\int w(E-E_0)\rho_{\mathrm{rel},g}(E)\,dE$ | 窗化读数 | 无量纲 |
| $(w,\tilde w)$ | 窗-对偶核对 | Wexler–Raz 双正交（规范化内积下） | 无量纲 |
| $\Delta E,\Delta t$ | 采样步长/窗宽 | Gabor 格点尺度 | 能量, 时间 |

**单位与规范注记**：
- 物理时间延迟为 $\hbar Q_g(E)$ 与 $\hbar\tau(E)$，单位为时间；本文 $Q_g$ 与 $\tau$ 的自然单位为能量$^{-1}$。
- 窗-对偶核对 $(w,\tilde w)$ 满足能量—时间版本的 Wexler–Raz 双正交（§2.3 规范化内积 $\langle\cdot,\cdot\rangle_E$ 下，度量因子 $1/(2\pi\hbar)$ 确保归一化常数无量纲）。
- Fourier 规范固定为 $\widehat{f}(t)=\frac{1}{2\pi\hbar}\int f(E)e^{-iEt/\hbar}\,dE$（§2.3），所有相位因子与 Gabor 密度以此计量。

**关键恒等式**（幺正情形）：

$$
\rho_{\mathrm{rel}}(E) = \frac{1}{2\pi i}\mathrm{tr}(S^\dagger\partial_E S) = \frac{1}{2\pi}\mathrm{tr}\,Q = -\xi'(E) = \frac{1}{2\pi}\partial_E\arg\det S.
$$

**非幺正情形**：

$$
\rho_{\mathrm{rel}}^{(\mathrm{eff})}(E) = \frac{1}{2\pi}\,\partial_E\arg\det S = \frac{1}{2\pi}\,\mathrm{Im}\,\partial_E\log\det S,\qquad
\tau = -\frac{i}{N}\partial_E\log\det S = \frac{1}{N}\mathrm{tr}(S^{-1}\partial_E S).
$$

**Gabor 密度条件**：$\Delta E\,\Delta t/(2\pi\hbar)\le 1$ 为必要密度。

---

**注**：文中所有记号与号记遵循数学物理主流约定（例如 BK 取 $\det S=e^{-2\pi i\xi}$），以避免号差混淆。所有公式均在相应引用的适用条件下成立。
