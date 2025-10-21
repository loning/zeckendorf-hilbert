# S15. Weyl–Heisenberg 酉系统与完成功能方程的算子等价

—— 带权 Mellin–Hilbert 空间中的群表示、生成元、Weyl 关系与镜像

**作者**：Auric
**日期**：2025-10-21

---

## 摘要（定性）

在带权 Mellin–Hilbert 空间 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}\,dx)$ 中构造两族一参数酉算子：相位模群 $U_\tau f=x^{i\tau}f$ 与尺度伸缩群 $V_\sigma f=e^{\sigma a/2}f(e^\sigma\!\cdot)$。证明它们强连续、给出自伴生成元与公共核心，并建立标准 Weyl 关系 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$，从而得到 Weyl–Heisenberg（$\mathbb R^2$ 的中心扩张）之射影酉表示；在对数坐标模型中，该系统等价于 $L^2(\mathbb R)$ 上的"调制—平移"Weyl 对。Mellin 侧呈现为"垂线平移—权乘"的谱图像并可对角化。构造满足自反性的再生核 Hilbert 空间（RKHS）后，完成功能方程 $\Xi(a-s)=\varepsilon\Xi(s)$ 与镜像算子 $Jf(x)=x^{-a}f(1/x)$ 的本征关系 $JF=\varepsilon F$ 严格等价。全流程仅使用**有限阶** Euler–Maclaurin（EM）与**方向亚纯化**：窗化/卷积/换序仅叠加整/全纯层，**极点唯由主尺度产生**；增长由支持函数上界与 $\Gamma/\pi$ 正规化配平；数值离散化误差统一由 Nyquist–Poisson–EM 三分解给出非渐近可计算上界。

---

## 0. 记号与基础框架

### 0.1 完成函数与中心轴

设 Dirichlet 级数

$$
L(s)=\sum_{n\ge1}\frac{a_n}{n^s},\qquad s\in\mathbb C,
$$

其完成函数

$$
\Xi(s)=Q^{s/2}r(s)L(s),\qquad r(a-s)=r(s),\qquad \Xi(a-s)=\varepsilon\,\Xi(s),\ |\varepsilon|=1,
$$

称 $\Re s=\tfrac a2$ 为中心轴。

### 0.2 带权 Mellin–Hilbert 空间与 Mellin 变换

$$
\mathcal H_a:=L^2(\mathbb R_+,x^{a-1}\,dx),\quad
\langle f,g\rangle_a=\int_0^\infty f(x)\overline{g(x)}\,x^{a-1}\,dx.
$$

Mellin 变换

$$
\mathcal M_a[f](s):=\int_0^\infty f(x)\,x^{\,s}\frac{dx}{x},
$$

在 $\Re s=\frac a2$ 上满足 Plancherel–Mellin 等距：

$$
|f|_{\mathcal H_a}^2=\frac1{2\pi}\int_{\mathbb R}\big|\mathcal M_a[f]\big(\tfrac a2+i\tau\big)\big|^2\,d\tau .
$$

令对数等距

$$
(Tf)(t):=e^{\frac a2 t}f(e^t),\qquad t=\log x,
$$

则 $T:\mathcal H_a\to L^2(\mathbb R,dt)$ 为酉，该归一由 $T$ 与 Fourier 变换的标准配对唯一确定。

### 0.3 镜像算子

定义 $Jf(x):=x^{-a}f(1/x)$。则 $J$ 在 $\mathcal H_a$ 上酉且 $J^2=\mathrm{Id}$。在 $t$-模型中，

$$
(TJT^{-1}g)(t)=g(-t).
$$

### 0.4 解析纪律与增长—误差

所有离散—连续换序仅使用**有限阶** EM（伯努利层与余项关于复参全纯/整）；沿方向切片的拉普拉斯–Stieltjes 变换在工作竖条内亚纯，其极点位置与阶数由指数–多项式律唯一决定。方向增长由 Newton 支持函数上界控制；垂线增长由 $\Gamma/\pi$ 正规化配平。数值误差按**别名/Poisson + 有限阶 EM 伯努利层 + 截断尾项**三部分统一核算。

---

## 1. 两族一参数酉群与 Weyl 关系

### 定义 1.1（相位与尺度的酉作用）

对 $\tau,\sigma\in\mathbb R$：

$$
(U_\tau f)(x):=x^{i\tau}f(x),\qquad
(V_\sigma f)(x):=e^{\frac{\sigma a}{2}}\,f(e^\sigma x).
$$

### 定理 1.2（强连续与酉性）

$\{U_\tau\}_{\tau\in\mathbb R}$、$\{V_\sigma\}_{\sigma\in\mathbb R}$ 为强连续一参数酉群，且

$$
|U_\tau f|_a=|f|_a,\qquad |V_\sigma f|_a=|f|_a.
$$

**证明** $U_\tau$ 的酉性由权函数 $x^{a-1}$ 对乘子 $x^{i\tau}$ 的不变性显然。对 $V_\sigma$，变换因子与前置归一精确抵消：

$$
|V_\sigma f|_a^2=\int_0^\infty |e^{\frac{\sigma a}{2}}f(e^\sigma x)|^2 x^{a-1}\,dx
=e^{\sigma a}\int_0^\infty|f(y)|^2 (ye^{-\sigma})^{a-1}\,e^{-\sigma}dy=|f|_a^2.
$$

强连续性通过等距 $T$ 获得：$(TU_\tau T^{-1})g(t)=e^{i\tau t}g(t)$ 与 $(TV_\sigma T^{-1})g(t)=g(t+\sigma)$ 为 $L^2(\mathbb R)$ 的教材级强连续群，因而 $\{U_\tau\},\{V_\sigma\}$ 强连续。∎

### 命题 1.3（Weyl 关系）

$$
V_\sigma U_\tau=e^{i\tau\sigma}\,U_\tau V_\sigma .
$$

**证明** 逐点计算：

$$
(V_\sigma U_\tau f)(x)=e^{\frac{\sigma a}{2}}(e^\sigma x)^{i\tau}f(e^\sigma x)=e^{i\tau\sigma}(U_\tau V_\sigma f)(x).
$$

∎

**注 1.4（对数模型）** 通过 $T$，得到

$$
(TU_\tau T^{-1}g)(t)=e^{i\tau t}g(t),\qquad (TV_\sigma T^{-1}g)(t)=g(t+\sigma),
$$

即 $L^2(\mathbb R)$ 上标准"调制—平移"Weyl 对。

---

## 2. Stone 生成元、公共核心与 CCR

### 定理 2.1（生成元与本质自伴性）

存在在 $C_c^\infty(\mathbb R_+)$ 上定义的算子

$$
Af=\log(x)\,f,\qquad
Bf=-i\Big(x\frac{d}{dx}+\frac a2\Big)f,
$$

它们在该共同核心上**本质自伴**，其闭包 $\overline A,\overline B$ 为自伴生成元，并满足

$$
U_\tau=e^{i\tau\,\overline A},\qquad V_\sigma=e^{i\sigma\,\overline B}.
$$

闭包的自然域为

$$
\mathsf D(\overline A)=\{f\in\mathcal H_a:\ \log(\cdot)\,f\in\mathcal H_a\},
$$

$$
\mathsf D(\overline B)=\{f\in\mathcal H_a:\ f\in AC_{\mathrm{loc}}(\mathbb R_+),\ x f'(x)\in\mathcal H_a\}.
$$

公共核心可取 $C_c^\infty(\mathbb R_+)$；其 $t$-模型下的自然核心为 $C_c^\infty(\mathbb R)$（亦可改用 $\mathcal S(\mathbb R)$ 作为核心，二者均足够）。在 $T$-模型中对应 $\widehat A=t$、$\widehat B=-i\partial_t$ 的本质自伴性，其中 $\mathsf D(\widehat{\overline B})=H^1(\mathbb R)$。

**证明** 由 Stone 定理与酉等距 $T$ 把 $(A,B)$ 传递到 $(t,-i\partial_t)$ 获得自伴闭包与核心性。∎

### 命题 2.2（对易关系）

在公共核心 $C_c^\infty(\mathbb R_+)$ 上，

$$
[A,B]=iI.
$$

**证明** 直接计算如常，化简得 $([A,B]f)(x)=i f(x)$。所有对易计算均在该公共核心上进行，再以本质自伴性延拓到闭包 $\overline A,\overline B$。∎

### 推论 2.3（指数式 Weyl 等价）

由命题 1.3 得

$$
e^{i\sigma\,\overline B}e^{i\tau\,\overline A}=e^{i\tau\sigma}\,e^{i\tau\,\overline A}e^{i\sigma\,\overline B},
$$

与核心上 $[A,B]=iI$ 的正规 Weyl 表示等价。对无界算子，先在共同核心上应用 Campbell–Baker–Hausdorff，再以稠密延拓完成；在**正则表示**假设下二者等价。

---

## 3. Mellin 侧的作用、对角化与共轭

### 命题 3.1（Mellin 侧的平移—乘子）

对适定 $f$ 与 $s$：

$$
\mathcal M_a[U_\tau f](s)=\mathcal M_a[f](s+i\tau),\qquad
\mathcal M_a[V_\sigma f](s)=e^{-\sigma\,(s-\frac a2)}\,\mathcal M_a[f](s).
$$

**证明** 第一式由 $U_\tau$ 的乘子性显然。第二式代入定义并以 $y=e^\sigma x$ 代换得 $\mathcal M_a[V_\sigma f](s)=e^{\frac{\sigma a}{2}}\int_0^\infty f(y)\,y^s e^{-\sigma s}\frac{dy}{y}=e^{-\sigma(s-\frac a2)}\mathcal M_a[f](s)$。对一般 $s$ 的陈述按解析延拓理解。∎

### 命题 3.2（镜像对生成元的共轭）

$J$ 为 $\mathcal H_a$ 上酉对合，且

$$
J\,\overline A\,J=-\overline A,\qquad J\,\overline B\,J=-\overline B,\qquad J\,U_\tau\,J=U_{-\tau},\qquad J\,V_\sigma\,J=V_{-\sigma}.
$$

**证明** 在 $t$-模型中 $TJT^{-1}g(t)=g(-t)$ 为标准奇偶算子 $P$，该等式等价于 $PtP=-t$ 与 $P(-i\partial_t)P=+i\partial_t$；故对乘子 $t$ 与导数 $-i\partial_t$ 皆取负；回推即得（对闭包 $\overline A,\overline B$ 的共轭关系由稠密延拓建立）。∎

---

## 4. 自反核 RKHS 与完成功能方程的算子等价

### 4.1 自反核与评估向量

取核 $K$ 使得 $(f,g)\mapsto\langle f, K\ast g\rangle_a$ 正定，其中 $\ast$ 为 Mellin 卷积（乘法卷积）

$$
(K\ast g)(x)=\int_0^\infty K\!\left(\frac{x}{y}\right)g(y)\,\frac{dy}{y},
$$

且其 Mellin 变换满足

$$
\mathcal M_a[K](a-s)=\mathcal M_a[K](s)\quad(\text{自反性});
$$

则由 Moore–Aronszajn 定理在 $\mathcal H_a$ 上诱导再生核 Hilbert 空间 $\mathcal H(K)$。记 $k_s\in\mathcal H(K)$ 为评估向量，满足

$$
F\in\mathcal H(K)\ \Rightarrow\ \Xi(s):=\langle F,k_s\rangle_a,\qquad k_{a-s}=Jk_s,
$$

且 $s\mapsto k_s$ 在中心轴邻域连续。评估向量 $k_s$ 的选择唯一到常数相位；本文选取与 $J$ 对齐的规范，使 $k_{a-s}=Jk_s$ 成立。

### 定理 4.2（完成功能方程 $\Longleftrightarrow$ 镜像本征）

$$
\Xi(a-s)=\varepsilon\,\Xi(s)\quad\Longleftrightarrow\quad JF=\varepsilon F.
$$

**证明** 由 $k_{a-s}=Jk_s$ 得

$$
\Xi(a-s)=\langle F,k_{a-s}\rangle_a=\langle F,Jk_s\rangle_a=\langle JF,k_s\rangle_a.
$$

若 $JF=\varepsilon F$，则 $\Xi(a-s)=\varepsilon\Xi(s)$；反之，$\langle (JF-\varepsilon F),k_s\rangle_a\equiv0$ 对所有 $s$ 成立，由再生性得 $JF=\varepsilon F$。∎

---

## 5. 解析纪律：有限阶 EM 与方向亚纯化

### 定理 5.1（窗化/卷积的奇性保持）

取偶窗/核 $\psi$（紧支或指数衰减）并以**有限阶** EM 进行离散—连续桥接，定义

$$
\Xi_\psi(s):=\langle F\!\ast\!\psi,\ k_s\rangle_a.
$$

则 $\Xi_\psi$ 与 $\Xi$ 在同一工作竖条内具有相同的极点集合与阶数；所有 EM 端点伯努利层与余项关于 $s$ 为整/全纯，故**极点仅来自主尺度**。

**证明** 带参 EM 的有限阶伯努利层在复参数上全纯，余项整/全纯；方向亚纯化断言沿切片的拉普拉斯–Stieltjes 变换的极点由指数率与多项式阶唯一决定。∎

### 命题 5.2（增长控制）

沿 $\rho=\rho_\perp+s\mathbf v$ 的切片，增长由 Newton 支持函数 $H_{\mathrm{New}(F)}(\mathbf v)$ 上界；完成功能方程与 $\Gamma/\pi$ 正规化共同在中心轴提供对称的垂线衰减。∎

---

## 6. 非渐近离散化：Nyquist–Poisson–EM 三分解

### 定理 6.1（采样—积分的统一误差界）

设 $g\in C^{2M}\cap L^1$，$\widehat g,g^{(2M)}\in L^1$。对步长 $\Delta>0$ 与截断 $T>0$，有

$$
\Big|\ \int_{\mathbb R} g(s)\,ds\ -\ \Delta\!\!\sum_{|k|\le \lfloor T/\Delta\rfloor}\! g(k\Delta)\ \Big|
\ \le
\underbrace{\sum_{m\ne0}\big|\widehat g(2\pi m/\Delta)\big|}_{\text{别名/Poisson}}
+\underbrace{\sum_{j=1}^{M-1} c_j\,\Delta^{2j}\,|g^{(2j)}|_{L^1}}_{\text{有限阶 EM 伯努利层}}
+\underbrace{\int_{|s|>T}\! |g(s)|\,ds}_{\text{截断尾项}}.
$$

若 $g$ 带限且 $\Delta\le\pi/\Omega$，别名项为零。

**证明** 由 Poisson 求和公式、带参有限阶 EM 与尾项估计直接叠加。∎

**注 6.2** 当 $g$ 来自 $\Xi$ 或 $\Xi_\psi$ 的窗化 integrand，定理 5.1 保障误差层不改变奇性集合；增长常数由命题 5.2 控制。

---

## 7. Weyl–Heisenberg 中心扩张的射影酉表示

### 定义 7.1（Weyl 系统）

令

$$
W(\tau,\sigma):=U_\tau V_\sigma,\qquad (\tau,\sigma)\in\mathbb R^2.
$$

由命题 1.3，

$$
W(\tau,\sigma)\,W(\tau',\sigma')=e^{\,i\tau'\sigma}\,W(\tau+\tau',\sigma+\sigma').
$$

因此 $(\tau,\sigma)\mapsto W(\tau,\sigma)$ 为 $\mathbb R^2$ 的射影酉表示，其 2-余因子

$$
c\big((\tau,\sigma),(\tau',\sigma')\big)=e^{\,i\tau'\sigma}
$$

确定 Weyl–Heisenberg 的中心扩张；由 Stone–von Neumann 定理在不可约与正则性条件下惟一化。本表示在 $L^2(\mathbb R)$（通过 $T$）为**不可约且正则**的 Schrödinger 型表示，故满足该定理的惟一性前提。亦可采用对称规范 $W_{\mathrm{sym}}(\tau,\sigma)=e^{i\tau\sigma/2}U_\tau V_\sigma$，二者酉等价并给出同一 Weyl–Heisenberg 中心扩张。

---

## 8. 例示

**(1) Riemann $\xi$**：取 $a=1$，$\Xi(s)=\tfrac12 s(s-1)\pi^{-s/2}\Gamma(\tfrac s2)\zeta(s)$。构造自反核 $K$ 使 $\mathcal M_1[K](1-s)=\mathcal M_1[K](s)$，则 $\Xi(1-s)=\Xi(s)$ 当且仅当 $JF=F$。

**(2) Dirichlet $L(s,\chi)$**：若 $\chi$ 非实，$\varepsilon$ 为 Gauss 因子相位，则 $JF=\varepsilon F$ 与 $\Xi(a-s,\chi)=\varepsilon\,\Xi(s,\chi)$ 等价。

---

## 9. 可检清单（最小充分条件）

1. **群与生成元**：$\{U_\tau\},\{V_\sigma\}$ 强连续、酉；$A=\log x$、$B=-i(x\partial_x+\tfrac a2)$ 在共同核心 $C_c^\infty(\mathbb R_+)$ 上本质自伴，其闭包 $\overline A,\overline B$ 为自伴生成元；在核心上 $[A,B]=iI$。
2. **Mellin 侧**：$\mathcal M_a[U_\tau]=(\cdot)\circ(\cdot+i\tau)$、$\mathcal M_a[V_\sigma]=e^{-\sigma(s-\frac a2)}\cdot$；中心轴应用 Plancherel–Mellin。
3. **镜像等价**：选自反核 $K$，构造 $k_s$ 且 $k_{a-s}=Jk_s$，并令 $\Xi(s)=\langle F,k_s\rangle_a$；验证 $JF=\varepsilon F\iff \Xi(a-s)=\varepsilon\Xi(s)$。
4. **解析纪律**：窗化/换序仅用**有限阶** EM；伯努利层与余项关于 $s$ 全纯/整，**极点=主尺度**。
5. **增长与误差**：支持函数上界与 $\Gamma/\pi$ 正规化控制增长；数值误差按 Nyquist–Poisson–EM 三分解给出显式常数。

---

## 10. 与既有篇章的接口

**S0–S1（母映射与解析域）**：本篇的 $\mathcal H_a$ 与 Mellin 归一由 S0–S1 的"相位—尺度母映射/可积条带"设定统一固定；$T$-模型把母映射的对数坐标化落实为标准 Fourier 架构，为 §0.2 的 Plancherel–Mellin 判据提供规范。

**S2（加法镜像与零集几何）**：S2 的"加法镜像 $\theta\mapsto-\theta$"在本篇由 $J$ 具体实现为 $t\mapsto -t$（对数坐标），从而把零集关于中心轴的几何对称转写为 $JF=\varepsilon F$ 的本征条件；S2 的横截模板决定 §5 中方向切片的合法性。

**S3（自反核与 Mellin 镜像）**：S3 的自反核构造在 §4 处升格为 RKHS 语言；公式 $k_{a-s}=Jk_s$ 是 S3 镜像对称在再生核层面的精确实现，并与 $\Xi(s)=\langle F,k_s\rangle_a$ 组合为功能方程的算子等价。

**S4（有限阶 Euler–Maclaurin）**：S4 的"有限阶 EM—伯努利层—整/全纯"纪律在 §5 成为奇性保持的核心工具；本篇所有离散—连续换序仅调用有限阶 EM，从而保证"极点=主尺度"。

**S5（方向亚纯化与极点定位）**：S5 的方向拉普拉斯–Stieltjes 模板支撑 §5 对窗化对象的极点不变性证明：极点位置与阶由主尺度的指数率与多项式阶唯一确定，窗/卷积只叠加整/全纯层。

**S6（信息量刻度与凸对偶）**：S6 的信息势 $\mathcal L$（及其对偶 $\mathcal L^\ast$）与 Bregman/KL 对偶为窗权与谱投影的参数化提供统一语义；在 §5–§6 的误差预算中，采用 S6 的"有效模态质心/协方差"刻度衡量窗化的能量分配与带宽。

**S7（$L$-函数接口模板）**：S7 的 $Q$（conductor）与 $\Gamma/\pi$ 正规化统一了本篇 §0.1 的完成函数记号；其中心轴 $a$ 与 $\varepsilon$ 相位直接进入 §4 的本征关系，确保群表示语言与 $L$-函数语法一致。

**S8（离散一致逼近与差分湮灭）**：S8 的 Nyquist–Poisson–EM 三分解在 §6 作为非渐近误差学的标准形，Poisson 别名/伯努利层/截断尾项三者给出实际计算的可检上界；差分湮灭可与 §3 的垂线平移协同用于序列重构。

**S9（Pretentious—几乎周期—指数和）**：S9 的 Pretentious 距离刻画竖向平移窗下的相干/非相干区；本篇 $U_\tau$ 的"垂线平移"在 Mellin 侧与 Pretentious 词典直接对齐，可把 §7 的 Weyl 变换用于构造放大器/共振器的群表示版本。

**S10（Amoeba 几何与增长）**：S10 的 Ronkin/支持函数上界提供 §5.2 的增长控制，使 Weyl–Heisenberg 作用下的方向增长在 Newton 多面体几何上可视化与可估。

**S11（迹公式接口）**：S11 的核—变换—窗三件套在本篇被解释为 Weyl 系统下的"调制—平移—伸缩"的算子化语义；特别地，Kuznetsov/Selberg 的核选择可在 §1–§3 的框架中解读为对 $\mathcal H_a$ 的受控谱投影。

**S12（近似功能方程、mollifier 与共振）**：S12 的软窗 AFE 与谱最优 mollifier 在本篇以 $U_\tau,V_\sigma$ 的射影系统获得算子实现；$\Gamma/\pi$ 正规与 EM 纪律保证 AFE 的非渐近误差闭合。

**S13（大值与 $\Omega$-下界）**：S13 的放大器/共振器可在 §7 的 Weyl 系统中表述为对 $W(\tau,\sigma)$ 的有限线性叠加与谱半径控制；Pretentious/非 Pretentious 区的阈值机制与本篇的平移—伸缩对齐。

**S14（de Branges / Beurling–Nyman 界面）**：S14 的 RKHS 与 BN 子空间在本篇 §4 直接调用；功能方程 $\Leftrightarrow$ 镜像本征 $JF=\varepsilon F$ 是 S14 的内积评估—镜像对称的算子化精炼；最小能量投影可在 Weyl 系统下视作不变子空间的正交分解。

**前瞻（S16–S18）**：S16 之 de Branges–Krein 规范系统将以 $(\overline A,\overline B,J)$ 作为基本三元组；S17 拟把散射—功能方程算子化置于 affine（平移+伸缩）表象，以与迹公式/散射矩阵并行；S18 将在 Weyl/affine 双表象下建立轨道—谱窗化不等式与稳定性准则。

---

## 11. 结语

在 $\mathcal H_a$ 中构造之 $U_\tau$—$V_\sigma$ Weyl 对给出 Weyl–Heisenberg 的射影酉表示；Mellin 侧呈"垂线平移—权乘"，镜像算子在 RKHS 框架下把完成功能方程等价为本征关系 $JF=\varepsilon F$。以**有限阶** EM 与方向亚纯化为纪律，可确保奇性与增长结构稳定、可检；以 Nyquist–Poisson–EM 的非渐近误差学支撑有限窗计算。该算子骨架与 S0–S14 各篇形成严密接口，并为后续 de Branges–Krein 规范系统（S16）、散射—功能方程的算子化（S17）与轨道—谱窗化不等式（S18）提供统一、稳固的基础。

---

## 附录 A：公开判据（摘录）

* **Stone 定理**：强连续一参数酉群 $\{e^{itH}\}$ 的生成元 $H$ 自伴且唯一；若在稠密域上定义的对称算子本质自伴，则其闭包即为该生成元。
* **Stone–von Neumann 定理**：满足 CCR 的不可约正则 Weyl 表示在酉等价意义下唯一。
* **Plancherel–Mellin 判据**：$Tf(t)=e^{\frac a2 t}f(e^t)$ 把 $\mathcal H_a$ 酉等距到 $L^2(\mathbb R)$，中心轴 Mellin 为 Fourier。
* **有限阶 Euler–Maclaurin（带参）**：有限阶伯努利层关于外部复参全纯，余项整/全纯。
* **方向亚纯化**：沿方向的拉普拉斯–Stieltjes 变换在可积竖条内亚纯，其极点位置与阶数由指数率与多项式次数控制。
