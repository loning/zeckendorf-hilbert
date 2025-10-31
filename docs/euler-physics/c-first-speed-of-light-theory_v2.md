# 基于Wigner-Smith延迟的光速测量：窗口化群延迟方法的理论基础与非渐近误差闭合（在SI 2019固定 $c$ 前提下的长度校准与一致性检验）

**Version: 2.0**（2025-10-31）

**作者**：Auric（EBOC / WSIG / S-series）

**关键词**：长度校准；Wigner–Smith 延迟；窗口化群延迟；Birman–Kreĭn 公式；谱移函数；Kramers–Kronig 关系；因果前沿；信息光锥；Nyquist–Poisson–Euler–Maclaurin 误差账本；SI 计量基准

**MSC**：81U05；47A40；94A15；78A40；83A05

---

## 摘要

本文提出并验证了一种基于Wigner-Smith（WS）延迟矩阵的长度校准方法（在SI 2019固定 $c$ 前提下）。在SI 2019框架下，光速常数 $c = 299\,792\,458$ m/s 为精确定义常数，用于实现长度单位"米"。本文证明：在该框架内，通过窗口化群延迟读数 $\mathsf{T}[w_R,h;L]$ 可实现"以延迟定长"的计量路径，该路径与SI的"以时定长"互为实现，且与相位斜率/谱移密度、因果前沿、信息光锥三种物理图像在理论上保持一致。

核心贡献在于：(1) 证明WSIG（窗口化散射积分格林函数）框架在理想真空链路上精确恢复理论值 $\mathsf{T} = L/c$；(2) 建立Nyquist–Poisson–Euler–Maclaurin（NPE）三支非渐近误差账本，为实际测量（离散采样、有限带宽）提供可计算的误差上界；(3) 论证该测量方法与散射理论（BK公式）、因果律（KK关系）、信息论（可检测信息速度）的内在一致性。

本文不试图"定义"光速（其值已由SI固定），而是为基于WS延迟的长度校准提供从理论到实践的完整闭环：理论验证 → 一致性论证 → 误差控制 → 计量实现。

---

## 0. 记号与单位

设能量变量为 $E=\hbar \omega$，散射矩阵 $S(E)\in\mathrm U(N)$ 可对能量求导。**Wigner–Smith 延迟矩阵**定义为 $Q(E):=-\,i\,S(E)^\dagger\,\frac{dS}{dE}(E)$；它是厄米矩阵，**总群延迟**记为 $\tau_{\mathrm{WS}}(E):=\hbar\,\operatorname{tr}Q(E)$（单位：秒）。**Smith（1960）原始"寿命矩阵"将 $\hbar$ 并入矩阵定义，记 $Q_{\text{Smith}}:=-\,i\,\hbar\,S^\dagger \frac{dS}{dE}$；本文采用不含 $\hbar$ 的 $Q$ 约定，并以 $\tau_{\mathrm{WS}}=\hbar\,\operatorname{tr}Q$ 表示总群延迟，二者仅差一个 $\hbar$ 因子（量纲见 §13.1）**。这一构造在电磁、声学等多域广泛使用。^[1]

本文默认单模链路（$N=1$；多端口情形见第 11 节），并对观测采用带宽随 $R\uparrow$ 增长的窗 $w_R$（归一化 $\int_{\mathbb R} w_R(E)\,dE=2\pi$）与前端核 $h$ 的卷积，**其中 $h\in L^1(\mathbb R)$ 且归一化为 $\int_{\mathbb R} h(E)\,dE=1$**，因此对任意常值 $C_0$ 有 $h\!\star\! C_0=C_0$。

**SI 2019 约定**：光速常数 $c=299\,792\,458\,\mathrm{m\,s^{-1}}$ 为**精确定义常数**（exact by definition），米通过 $l=c\,\Delta t$ 从时间基准实现。^[2] 本文在此框架内工作，不试图"测量"或"定义" $c$，而是验证基于WS延迟的计量方法与SI实现的一致性。

---

## 1. 引言与框架定位

### 1.1 研究背景

光速常数 $c$ 是现代物理学的基石之一。在SI 2019体系中，$c$ 被固定为精确数值 $299\,792\,458$ m/s，用于从时间基准（铯-133超精细跃迁频率）定义长度单位"米"。这一"以时定长"的实现路径已被干涉法、腔共振法等多种技术验证。

本文提出并验证一种基于**Wigner-Smith（WS）延迟矩阵**的替代路径。WS延迟矩阵源于散射理论，定量描述波包在散射区域的群延迟。对于真空中的电磁传播，我们证明：窗口化的WS延迟读数 $\mathsf{T}$ 在理论上精确给出 $\mathsf{T} = L/c$，其中 $L$ 是几何距离。

### 1.2 本文目标与定位

**本文不试图"定义"光速**——其值已由SI固定。我们的目标是：

1. **理论验证**：证明在SI框架下，WSIG（窗口化散射积分）方法在理想条件下精确恢复理论值 $\mathsf{T} = L/c$；
2. **一致性论证**：论证该结果与散射理论（相位斜率/谱移密度）、因果律（KK关系）、信息论（可检测信息速度）的内在一致性；
3. **误差控制**：建立NPE（Nyquist–Poisson–Euler–Maclaurin）三支非渐近误差账本，为实际测量提供可计算的误差上界；
4. **计量实现**：说明"以延迟定长"与SI的"以时定长"如何互为实现。

### 1.3 主要贡献

**贡献1（理论）**：在真空链路上，证明窗口化群延迟读数
$$
\mathsf T[w_R,h;L]\ =\ \frac{\hbar}{2\pi}\int_{\mathbb R} w_R(E)\,\bigl[h\!\star\!\operatorname{tr}Q_L\bigr](E)\,dE
$$
在理想条件（连续、无限带宽、扁平端点窗函数）下**精确等于** $L/c$，且与窗函数 $w_R$ 和核 $h$ 的具体形状无关（§3-§4）。

**贡献2（一致性）**：证明上述结果与以下物理图像**互为一致**：
- **(A) 相位斜率/谱移密度**：$\operatorname{tr}Q = \partial_E\arg\det S = -2\pi\,\xi'(E)$（Birman-Kreĭn公式，§5）
- **(B) 因果前沿**：Kramers-Kronig关系 + 光锥支撑 → 前沿速度为 $c$（§6）
- **(C) 信息光锥**：在经典因果线性信道且无预共享的条件下，可检测信息速度的上界为 $c$（§7，依赖假设7.0）

**贡献3（误差账本）**：提供NPE三支非渐近误差上界（§8）：
- **Nyquist/别名项** $\varepsilon_{\text{alias}}$：频谱重复导致的混叠误差
- **Euler-Maclaurin项** $\varepsilon_{\text{EM}}$：离散采样的端点/尾项误差（包含扁平端点条件的精确分析）
- **截断项** $\varepsilon_{\text{tail}}$：有限带宽的截断误差

**贡献4（计量实现）**：说明如何通过交叉校准（铯频率链、干涉计长度链）实现"以延迟定长"与SI的"以时定长"的闭环（§9）。

### 1.4 与现有文献的关系

- **WS延迟矩阵**：源于Smith（1960）的碰撞散射理论^[1]，后推广到电磁学、声学等多个领域。
- **Birman-Kreĭn公式**：连接散射矩阵相位与谱移函数^[3]。
- **Kramers-Kronig关系**：Toll（1956）证明其与因果性的逻辑等价^[4]。
- **信息光锥**：Dorrah-Mojahedi（2014）研究快/慢光中的"可检测信息速度"^[5]。
- **NPE误差分析**：Shannon（Nyquist采样）、Woit（Poisson求和）、Bailey-Borwein（EM公式）^[6,7]。

本文的创新在于：将上述工具统一到WSIG框架下，并**首次**建立从理论到实践的完整误差闭环。

### 1.5 符号说明与极限约定

在§3的理想真空场景，$\operatorname{tr}Q_L$ 为常数，故 $\mathsf T[w_R,h;L]=L/c$ 与带宽 $R$ 无关。我们在主要公式中写"$\lim_{\text{带宽}\uparrow}$"是为统一涵盖有限带宽/采样的工程实现（§8-§9）：在理想情形该极限平凡存在，在实际测量中则由NPE账本控制误差收敛。

---

## 2. Wigner-Smith延迟矩阵的基本性质

### 2.1 定义与厄米性

**引理 2.1**：若 $S(E)$ 幺正可微，则 $Q(E)=-\,i\,S^\dagger S'$ 厄米，且
$$
\partial_E\arg\det S(E)=\operatorname{tr}Q(E).
$$

**证明**：由 $S^\dagger S=I$ 得 $(S^\dagger)'\,S+S^\dagger S'=0\Rightarrow (S^\dagger)'\,S=-S^\dagger S'$。故
$$
Q^\dagger= i (S^\dagger)' S= - i S^\dagger S'=Q.
$$
又因 $|\det S|=1$（幺正性），$\partial_E\ln\det S$ 为纯虚数。具体地，
$$
\partial_E\ln\det S=\operatorname{tr}(S^{-1}S')=\operatorname{tr}(S^\dagger S')=i\,\operatorname{tr}Q,
$$
取虚部即得 $\partial_E\arg\det S=\operatorname{tr}Q$。证毕。□

> **注**：与Smith的"寿命矩阵"在 $\hbar$ 因子上一致（§0）。

### 2.2 Birman-Kreĭn公式与谱移导数

**引理 2.2**：取Birman-Kreĭn约定 $\det S(E)=\exp\{-\,2\pi i\,\xi(E)\}$，则
$$
\operatorname{tr}Q(E)=-\,2\pi\,\xi'(E).
$$

**证明**：对 $\ln\det S = -2\pi i\,\xi$ 求导：$\partial_E\ln\det S=-2\pi i\,\xi'$。又 $\partial_E\ln\det S=i\,\operatorname{tr}Q$，合并得 $\operatorname{tr}Q=-2\pi\,\xi'$。证毕。□^[3]

> **注**：文献亦见不同号约定；本文一律采用上式带"−"号的BK约定。

---

## 2.3 与SI 2019计量框架的关系

### 2.3.1 SI体系中的光速地位

在国际单位制（SI）2019修订版中，光速 $c$ 被固定为**定义常数**：
$$
c = 299\,792\,458\ \text{m·s}^{-1}\quad\text{（exact）}.
$$
这意味着：
1. **$c$ 的数值在SI中为定义常数、无不确定度；实验只能作为一致性/闭环校准的检验，而非对 $c$ 的参数估计**；
2. **米由光速定义**：1米定义为"光在真空中 $1/299\,792\,458$ 秒内传播的距离"；
3. **时间基准为铯-133**：秒由铯-133超精细跃迁频率 $\Delta\nu_{\text{Cs}} = 9\,192\,631\,770$ Hz 定义。

因此，SI框架的计量逻辑是：
$$
\boxed{\text{时间（铯钟）}\ \xrightarrow{c\ \text{（定义）}}\ \text{长度（米）}}.
$$

### 2.3.2 本文方法的定位：长度校准而非光速测量

在SI框架下，本文的WSIG方法**不是测量光速**（光速已被固定），而是提供一种**长度校准**（length calibration）路径：

**传统SI实现**（"以时定长"）：
1. 铯钟提供时间基准 $\Delta t$
2. 通过固定的 $c$ 计算长度：$L = c \cdot \Delta t$
3. 用干涉法或其他方法验证该长度

**本文方法**（"以延迟定长"）：
1. 铯钟提供时间基准 $\Delta t$
2. 测量WS延迟 $\tau_{\text{WS}}$ （群延迟）
3. 通过固定的 $c$ 计算长度：$L = c \cdot \tau_{\text{WS}}$
4. 本文证明：在理想真空链路上，$\tau_{\text{WS}} = \mathsf{T} = L/c$，即该方法与SI实现**自洽**

### 2.3.3 互为实现的含义

"以时定长"与"以延迟定长"**互为实现**是指：
- 二者都依赖铯钟时间基准和固定的 $c$
- 二者都用于从时间基准校准长度
- 本文证明：在理想条件下，两种方法给出**相同的长度值** $L$
- 这是**一致性验证**，而非"两种独立定义"

### 2.3.4 为何不与SI矛盾

如果本文声称"定义光速"，那将与SI框架矛盾（因为 $c$ 已被固定）。但本文的实际内容是：
- **假设** $c = 299\,792\,458$ m/s（SI值）
- **推导** 真空链路的散射矩阵 $S_L(E) = e^{iEL/(\hbar c)}$
- **计算** WS延迟 $Q_L = L/(\hbar c)$
- **验证** 窗口化读数 $\mathsf{T} = L/c$
- **结论** 基于WS延迟的长度校准与SI一致

这是**在已知 $c$ 的前提下的一致性验证**，不构成循环论证，也不与SI矛盾。

### 2.3.5 计量学价值

本文方法的计量学价值在于：
1. **提供新的长度校准路径**：基于散射理论的WS延迟
2. **跨领域可移植性**：WS延迟在电磁、声学、量子散射等多个领域有统一形式
3. **误差可控性**：NPE账本提供非渐近误差上界，便于工程实现
4. **与SI互补**：可用于交叉校准，增强计量体系的鲁棒性

---

## 3. 真空链路的理论预言

本节在**SI固定 $c$ 的前提下**，推导理想真空链路的散射矩阵与WS延迟。

### 3.1 真空中的散射矩阵

在SI固定 $c = 299\,792\,458$ m/s 的框架下，真空中的电磁波满足色散关系
$$
\omega = c k,\quad\text{即}\quad E = \hbar c k,
$$
其中 $k$ 是波数。对于长度为 $L$ 的真空链路，平面波传播的相位为
$$
\phi(E) = k L = \frac{E L}{\hbar c}.
$$

由于真空无色散、无耦合、无增益/损耗，单模散射矩阵为纯相位：
$$
S_L(E) = e^{i\phi(E)} = e^{iEL/(\hbar c)} \in \mathrm{U}(1).
$$

这是在**已知 $c$** 的前提下建立的理论模型，不是"定义" $c$。

### 3.2 WS延迟的计算

由定义 $Q_L(E) = -i S_L^\dagger \frac{dS_L}{dE}$，计算得
$$
Q_L(E) = -i e^{-i\phi(E)} \cdot \frac{d}{dE}\bigl(e^{i\phi(E)}\bigr)
= -i e^{-i\phi} \cdot i \frac{d\phi}{dE} \cdot e^{i\phi}
= \frac{d\phi}{dE}
= \frac{L}{\hbar c}.
$$

**关键性质**：$Q_L(E)$ 是**与能量无关的常数**，反映真空的非色散性质。

总群延迟为
$$
\tau_{\mathrm{WS}}(E) = \hbar\,Q_L(E) = \frac{L}{c}.
$$

### 3.3 窗口化读数

窗口化群延迟读数定义为
$$
\mathsf T[w_R,h;L]\ :=\ \frac{\hbar}{2\pi}\int_{\mathbb R} w_R(E)\,\bigl[h\!\star\!\operatorname{tr}Q_L\bigr](E)\,dE.
$$

由于 $\operatorname{tr}Q_L = Q_L = L/(\hbar c)$ 为常数，卷积不改变常值：
$$
h\!\star\!\operatorname{tr}Q_L = \int_{\mathbb R} h(E-E')\,\frac{L}{\hbar c}\,dE' = \frac{L}{\hbar c}\int_{\mathbb R} h(E-E')\,dE' = \frac{L}{\hbar c}.
$$
（因为 $\int h = 1$）

因此
$$
\mathsf T = \frac{\hbar}{2\pi}\int_{\mathbb R} w_R(E)\,\frac{L}{\hbar c}\,dE
= \frac{L}{c}\cdot\frac{1}{2\pi}\int_{\mathbb R} w_R(E)\,dE
= \frac{L}{c}.
$$
（因为 $\int w_R = 2\pi$）

**结论**：在理想真空链路上，窗口化读数**精确等于** $L/c$，与窗函数 $w_R$ 和核 $h$ 的具体形状无关（只要满足归一化条件）。

---

## 4. 窗口化群延迟读数的收敛性与误差控制

### 4.1 理想情形的精确性

**定理 4.1**：在真空链路上，若窗 $w_R$ 和核 $h$ 满足归一化条件，则
$$
\mathsf T[w_R,h;L] = \frac{L}{c}\quad\text{（精确）}.
$$

**证明**：已在§3.3给出。关键在于 $\operatorname{tr}Q_L$ 为常数。证毕。□

### 4.2 有限采样与带宽的误差

实际测量中，由于：
1. **离散采样**：能量点离散化，步长为 $\Delta E$
2. **有限带宽**：窗函数 $w_R$ 仅在有限区间 $[a, b]$ 非零
3. **端点效应**：离散积分的端点权重误差

观测量
$$
\mathrm{Obs} = \mathsf T + \varepsilon_{\text{alias}} + \varepsilon_{\text{EM}} + \varepsilon_{\text{tail}},
$$
其中各误差项将在§8详细分析。

### 4.3 Euler-Maclaurin端点条件（技术修正）

为控制离散积分的端点误差，我们引入**扁平端点条件**。

令 $g(E) := w_R(E)\,[h\!\star\!\operatorname{tr}Q_L](E)$。取整数 $m\ge1$，并假设 $g(E) \in C^{2m}[a,b]$，**且 $g$ 在端点"扁平"**：
$$
g^{(j)}(a)=g^{(j)}(b)=0\quad\text{对}\quad j=0,1,\dots,2m-1.
$$

**在真空链路下** $h\!\star\!\operatorname{tr}Q_L$ 为常值，**因此只需选择 $w_R$ 为具有扁平端点的 $C_c^{2m}$ "凸台函数"（bump function）**即可满足该条件。

此时所有伯努利边界项消失，**梯形估计量**与 $\int g$ 之差仅余Euler-Maclaurin余项 $R_{2m}$，给出
$$
\bigl|\varepsilon_{\mathrm{EM}}\bigr|
\le \frac{2\,\zeta(2m)}{(2\pi)^{2m}}\,(\Delta E)^{2m}(b-a)\,
\sup_{E\in[a,b]}\bigl|g^{(2m)}(E)\bigr|.
$$

**若未满足扁平端点条件**，则按**保守版**上界处理：
$$
\bigl|\varepsilon_{\mathrm{EM}}\bigr|\le C_2(\Delta E)^2+\cdots,
$$
其中首项由 $\tfrac{|B_2|}{2!}(\Delta E)^2\bigl|g'(b)-g'(a)\bigr|$ 控制。^[7]

### 4.4 极限存在性与唯一性

**命题 4.2**：在真空链路上，极限
$$
\lim_{\substack{\text{带宽}\uparrow\\\Delta E\downarrow}}\mathrm{Obs} = \frac{L}{c}
$$
存在且唯一，收敛速度由NPE账本（§8）控制。

**证明要点**：
1. 理论值 $\mathsf{T} = L/c$ 精确（定理4.1）
2. Nyquist条件下别名项 $\varepsilon_{\text{alias}} = 0$（§8.1）
3. 扁平端点下 $\varepsilon_{\text{EM}} = O((\Delta E)^{2m})$（§8.2）
4. 有限带宽下 $\varepsilon_{\text{tail}} \to 0$ 当 $\Omega_R \to \infty$（§8.3）

因此 $\mathrm{Obs} \to \mathsf{T} = L/c$。证毕。□

---

## 5. 一致性验证（一）：相位斜率与谱移密度

本节论证：WSIG方法与散射理论的相位/谱移表述**互为一致**。

**定理 5.1**：取Birman-Kreĭn约定 $\det S(E)=\exp\{-2\pi i\,\xi(E)\}$，则几乎处处
$$
\boxed{\ \operatorname{tr}Q(E)=\partial_E\arg\det S(E)=-\,2\pi\,\xi'(E)\ }.
$$

**证明**：已于引理2.1-2.2给出。证毕。□^[3]

**推论 5.2**：窗口化平均下
$$
\mathsf T[w_R,h;L]=\hbar\,\Big\langle \partial_E\arg\det S_L \Big\rangle_{w,h}
=\,-\,\hbar\,2\pi\,\langle \xi'(E)\rangle_{w,h}.
$$

真空链路 $S_L(E)=e^{iEL/(\hbar c)}\Rightarrow \partial_E\arg\det S_L=L/(\hbar c)$，故 $\mathsf T=L/c$。证毕。□

**一致性说明**：
- WS延迟 $\operatorname{tr}Q$ 与相位斜率 $\partial_E\arg\det S$ 是**同一物理量的不同数学表述**（恒等关系）
- Birman-Kreĭn公式将其连接到谱移函数 $\xi(E)$
- 在真空链路上，所有表述都给出 $\mathsf{T} = L/c$

> **注**：更一般的障碍散射、波迹与BK的联系见Borthwick的系统论述。^[8]

---

## 6. 一致性验证（二）：因果前沿

本节论证：WSIG方法与因果律要求的前沿速度**互为一致**。

### 6.1 Kramers-Kronig关系与因果性

**定理 6.1（Toll）**：稳定线性时不变系统的**严格因果性**（$h(t)=0,\ t<0$）与其频率响应 $H(\omega)$ 的**上半平面解析性**与**Kramers-Kronig色散关系**逻辑等价。^[4]

**证明要点**：
(i) 若 $h$ 支持于 $[0,\infty)$，则 $H(z)=\int_0^\infty h(t)e^{izt}dt$ 在 $\Im z>0$ 全纯，边界值满足Hilbert变换，得KK关系；

(ii) 反向由Paley-Wiener-Titchmarsh定理：若 $H$ 可在上半平面解析并满足适当增长条件，逆变换得 $h(t)$ 支持于非负半轴。

因此**严格因果 $\Leftrightarrow$ KK关系**。证毕。□^[4]

### 6.2 光锥前沿与支撑性质（技术修正）

对三维**标量**波动方程
$$
\left(\frac{1}{c^2}\partial_t^2 - \nabla^2\right)G_{\mathrm{ret}}(t,\mathbf r) = \delta(t)\delta(\mathbf r),
$$
满足因果性（$t<0$ 时 $G=0$）与辐射边界条件的**唯一解**为
$$
G_{\mathrm{ret}}(t,\mathbf r)=\frac{\delta\!\bigl(t-|\mathbf r|/c\bigr)}{4\pi|\mathbf r|}.
$$

其支撑（分布意义下）位于**光锥** $t=r/c$ 上。

对于**Maxwell方程**，时域dyadic格林函数可由对 $\delta(t-r/c)/(4\pi r)$ 的张量-微分算子作用构成，包含 $\delta$ 及其导数，**其奇异支撑同样在光锥上**。^[9,15] 因此**分布意义下**的最早非零响应（奇异支撑）出现在 $t=L/c$ 的光锥上，前沿速度为 $c$。

**一致性说明**：
- 因果律（KK关系）要求前沿速度不超过Maxwell方程的特征速度 $c$
- 光锥支撑给出最早响应时间 $t = L/c$
- 结合§3，WSIG方法给出 $\mathsf{T} = L/c$
- **三者一致**：都给出相同的"延迟=距离/速度"关系

### 6.3 快/慢光与前驱

色散介质可出现 $v_g>c$ 或负群速，但信息/前沿速度不超过 $c$。Sommerfeld-Brillouin前驱解析式与实验（Stenner-Gauthier-Neifeld；Macke-Ségard）均证实"可检测信息最早不早于真空同程"。^[10]

---

## 7. 条件性结果：信息光锥（在通信模型假设下）

本节论证：在特定通信模型假设下，WSIG方法与信息论的"可检测信息速度"**互为一致**。

**假设 7.0（通信模型）**：信道为严格因果的LTI真空链路；接收端在时刻 $\Delta t$ 之前仅基于局域操作与本地噪声（包含经典与量子噪声）生成观测，且这些噪声与发送端输入 $X$ 独立。**并且在单次试验内，不允许接收端持有与发送端输入 $X$ 相关的预共享经典随机量或量子纠缠。**

定义"首次可检互信息时间"
$$
T_\delta(L):=\inf\bigl\{\Delta t\ge0:\ \exists\ \text{协议使}\ I(X;Y_{\Delta t})\ge\delta\bigr\},\quad
c_{\mathrm{info}}:=\lim_{\delta\downarrow0}\sup_{L>0}\frac{L}{T_\delta(L)}.
$$

**定理 7.1（在假设7.0下）**：$c_{\mathrm{info}}=c$。

**证明**：

**上界**：在假设7.0下，若 $\Delta t<L/c$，由§6.2的光锥支撑与独立噪声/局域性条件，$Y_{\Delta t}$ 与 $X$ 独立，故 $I(X;Y_{\Delta t})=0$，从而 $\sup L/T_\delta(L)\le c$。

**下界**：真空链路上§3-§5给出 $\mathsf T=L/c$。设接收端做能量或相干阈值检验（考虑信道+探测器总噪声），则当 $\Delta t=L/c+\varepsilon$ 时，窗口积累的信噪比随带宽/时间线性增长，存在阈值 $\delta(\varepsilon)\downarrow0$ 使 $I\ge\delta(\varepsilon)$。令 $\varepsilon,\delta\downarrow0$，得 $\sup L/T_\delta(L)\ge c$。

合并即 $c_{\mathrm{info}}=c$。证毕。□^[5]

**适用性说明**：

定理7.1的结论**强依赖于假设7.0**，特别是"无与 $X$ 相关的预共享资源"条件。在以下情形中，该定理**不适用**：
- 量子纠缠辅助的通信协议（entanglement-assisted）或任何与 $X$ 相关的预共享资源
- 非线性或时变信道

在这些情形中，"可检测信息速度"的定义需要重新审视。但**无信号定理保证任何此类方案均不能实现超光速信息传输**，因而**前沿/信息速度仍不超过 $c$**。预共享资源可能影响容量或一次检测所需资源，但不改变因果前沿。

> **注**：量子场论视角下，"无超信号性 $\Rightarrow$ 微因果"的当代证明为上界提供了独立逻辑支撑。^[11]

---

## 8. NPE误差账本：非渐近上界与证明

本节建立Nyquist-Poisson-Euler-Maclaurin（NPE）三支非渐近误差上界。

令**理论（连续）聚合量**
$$
\mathsf T:=\frac{\hbar}{2\pi}\!\int_{\mathbb R} w_R(E)\,[h\!\star\!\operatorname{tr}Q](E)\,dE.
$$

令 $g(E):=w_R(E)\,[h\!\star\!\operatorname{tr}Q](E)$，取等距能量网格 $E_n=a+n\,\Delta E$（$n=0,\dots,N$，$b=a+N\,\Delta E$）。定义**梯形法**的离散估计量
$$
\mathrm{Obs}:=\frac{\hbar}{2\pi}\,\Delta E\left[\frac{g(E_0)+g(E_N)}{2}+\sum_{n=1}^{N-1} g(E_n)\right],
$$

由有限采样与有限带宽，
$$
\mathrm{Obs}=\mathsf T+\varepsilon_{\text{alias}}+\varepsilon_{\text{EM}}+\varepsilon_{\text{tail}}
=\frac{L}{c}+\varepsilon_{\text{alias}}+\varepsilon_{\text{EM}}+\varepsilon_{\text{tail}}.
$$

### 8.1 Nyquist与Poisson（变量与单位显式化）

设能量域Fourier对为
$$
\widehat f(\tau):=\int_{\mathbb R} f(E)\,e^{-i\tau E}\,dE,\qquad [\tau]=\mathrm{J}^{-1}.
$$

则对任意步长 $\Delta E>0$ 与偏移 $a\in\mathbb R$，Poisson求和为
$$
\boxed{\
\sum_{n\in\mathbb Z} f\!\bigl(a+n\,\Delta E\bigr)
=\frac{1}{\Delta E}\sum_{k\in\mathbb Z}
\widehat f\!\Bigl(\frac{2\pi k}{\Delta E}\Bigr)\,
e^{\,i\,\frac{2\pi k a}{\Delta E}}
\ }.
$$

**无混叠（alias-free）充要条件**：若 $\widehat f(\tau)=0$ 当 $|\tau|\ge \pi/\Delta E$，则所有 $k\neq 0$ 项为零，别名项消失。

**别名误差上界（非严格带限时）**：
$$
\boxed{\
\bigl|\varepsilon_{\mathrm{alias}}\bigr|
\le \sum_{k\neq 0}
\left|\widehat f\!\Bigl(\frac{2\pi k}{\Delta E}\Bigr)\right|
\ }.
$$

该上界针对**无限等距采样的周期化误差**；有限区间的端点/权重误差已在§8.2以EM独立计入（不重复记账）。

与频率域的**等价换元**：令 $\omega:=E/\hbar,\ \Delta\omega:=\Delta E/\hbar$，则无混叠条件在 $(\omega,t)$ 变量下等价为
$$
\boxed{\ \Delta\omega<\frac{\pi}{t_{\max}}\ },
$$
其中 $t_{\max}$ 为时域支持上界；在能量域对应为
$$
\boxed{\ \Delta E<\frac{\pi\,\hbar}{t_{\max}}\ }.
$$

^[12]

### 8.2 Euler-Maclaurin（端点与尾项，技术修正）

对光滑 $g$ 与整数 $m\ge1$，**步长 $\Delta E$** 的Euler-Maclaurin给出
$$
\sum_{n=0}^{N} g(E_n)=\frac{1}{\Delta E}\int_{a}^{b}\!g(x)\,dx+\frac{g(a)+g(b)}{2}
+\sum_{k=1}^{m}\frac{B_{2k}}{(2k)!}\,(\Delta E)^{2k-1}\!\Bigl(g^{(2k-1)}(b)-g^{(2k-1)}(a)\Bigr)+R_{2m},
$$
其中 $E_n=a+n\,\Delta E,\ N=(b-a)/\Delta E$。余项满足可用上界
$$
\bigl|R_{2m}\bigr|
\ \le\ \frac{2\,\zeta(2m)}{(2\pi)^{2m}}\,(\Delta E)^{2m-1}
\int_{a}^{b}\!\bigl|g^{(2m)}(x)\bigr|\,dx.
$$

**针对梯形积分的误差阶**：将上式两边乘以 $\Delta E$ 并整理得
$$
\underbrace{\Delta E\left[\frac{g(a)+g(b)}{2}+\sum_{n=1}^{N-1} g(E_n)\right]}_{\text{梯形法}}
=\int_a^b g(x)\,dx
+\sum_{k=1}^{m}\frac{B_{2k}}{(2k)!}\,(\Delta E)^{2k}\!\Bigl[g^{(2k-1)}(b)-g^{(2k-1)}(a)\Bigr]
+\Delta E\,R_{2m}.
$$

**若 $g$ 在端点扁平**（$g^{(j)}(a)=g^{(j)}(b)=0$ 对 $j=0,1,\dots,2m-1$），则所有伯努利项消失，得到
$$
\bigl|\mathrm{Obs}-\mathsf T\bigr|
\le \frac{\hbar}{2\pi}\cdot\frac{2\zeta(2m)}{(2\pi)^{2m}}\,(\Delta E)^{2m}\!\int_a^b |g^{(2m)}(x)|\,dx
=O\bigl((\Delta E)^{2m}\bigr).
$$

**否则主导项为 $O((\Delta E)^2)$**，更高阶项并入上界：
$$
\bigl|\mathrm{Obs}-\mathsf T\bigr|
\le \frac{\hbar}{2\pi}\left[\frac{|B_2|}{2!}\,(\Delta E)^{2}\cdot\bigl|g'(b)-g'(a)\bigr|+\cdots\right].
$$

^[7]

### 8.3 尾项（有限带宽截断）

若 $w_R$ 的频域窗在带外具有至多代数/指数衰减，$h\!\star\!\operatorname{tr}Q$ 连续且有界，则
$$
\bigl|\varepsilon_{\text{tail}}\bigr|\le |h\!\star\!\operatorname{tr}Q|_\infty\cdot \int_{|E|>\Omega_R} |w_R(E)|\,dE\to0
$$
（$\Omega_R\!\uparrow$）。证毕。□

### 8.4 系统误差（新增）

实际测量中还需考虑：
$$
\varepsilon_{\text{sys}} = \varepsilon_{\text{detector}} + \varepsilon_{\text{geometry}} + \varepsilon_{\text{environment}} + \varepsilon_{\text{quantum}},
$$
其中：
- $\varepsilon_{\text{detector}}$：探测器时间分辨率（典型值 ~ps级）
- $\varepsilon_{\text{geometry}}$：长度 $L$ 的测量不确定度（干涉法 ~nm级）
- $\varepsilon_{\text{environment}}$：温度、压力、重力红移等效应
- $\varepsilon_{\text{quantum}}$：**当实验灵敏度达到相关量级时**，才需考虑真空涨落/Casimir等二阶效应；否则可忽略于系统误差预算之外

这些项的量级估计和控制方法需根据具体实验装置确定。

---

## 9. 工程实现：以延迟计长 & 与SI交叉校准

**规约**：

(i) 选几何已知的真空链路 $L$；

(ii) 宽带激励，测得 $\hat\tau=\mathsf T[w_R,h;L]$；

(iii) 计算 $\hat c=L/\hat\tau$**仅作为一致性诊断量**，**不作为对 $c$ 的估计**；**报告残差** $r_c:=\hat c/c-1$ **作为一致性指标**；**计量应用为用已知 $c$ 计算** $\hat L=c\,\hat\tau$ **并与几何/干涉链路交叉校准**；并随带宽验证"别名=0、端点/尾项收敛"；

(iv) 以铯频率链与干涉计长度链交叉校准，闭环至SI"以时定长"的**Mise en pratique**。^[2]

**交叉校准的含义**：
- 用铯钟确定时间基准
- 用干涉法（基于固定 $c$）确定几何长度 $L$
- 测量WS延迟 $\tau_{\text{WS}}$
- 验证 $c \cdot \tau_{\text{WS}} \approx L$（在误差范围内）
- 这是**一致性检验**，而非独立测量 $c$

**介质与"快光"注意**：群速异常不影响信息/前沿速度上界；检测阈值下的信息速度 $\le c$ 的理论与实验证据详见文献。^[10]

---

## 10. 结论定理：不同表述的自洽性与计量应用

**定理 10.1**：在SI固定 $c = 299\,792\,458$ m/s的框架下，基于窗口化群延迟的WSIG方法满足：

(1) **理论自洽**：在理想真空链路上，$\mathsf{T}[w_R,h;L] = L/c$（精确）；

(2) **与散射理论一致**：$\mathsf{T} = \hbar\langle\operatorname{tr}Q\rangle = \hbar\langle\partial_E\arg\det S\rangle = -2\pi\hbar\langle\xi'\rangle$；

(3) **与因果律一致**：因果前沿速度（光锥支撑）为 $c$，与 $L/\mathsf{T}$ 一致；

(4) **与信息论条件性一致**：在假设7.0下，可检测信息速度的上界为 $c$；

(5) **误差可控**：NPE三支误差（别名、端点、截断）具有非渐近上界，随采样密度/带宽收敛；

(6) **与SI互补**："以延迟定长"与"以时定长"互为实现，可用于交叉校准。

证毕（综上§3-§9）。□

**计量学意义**：
- 提供基于散射理论的新计量路径
- 跨领域可移植（WS延迟在多个物理领域有统一形式）
- 误差可控且可工程实现
- 与SI框架互补，增强计量体系鲁棒性

---

## 11. 多端口一般化与离散实现

### 11.1 多端口一般化（技术修正）

若 $S(E)\in\mathrm U(N)$，令"平均延迟"$\ \bar\tau(E):=\hbar\,\frac{1}{N}\operatorname{tr}Q(E)$。

**对无耦合且各通道等长的 $N$ 端口真空链路**，有 $S(E)=e^{iEL/(\hbar c)}I_N$，从而 $Q(E)=\frac{L}{\hbar c}I_N$，各本征延迟皆为 $L/c$，故$\bar\tau(E)=L/c$。

**若存在端口耦合或几何长度差异**，则 $\operatorname{tr}Q(E)$ 含装置相位（耦合器/混合器等）的能量导数贡献。此时需进行基线相消/参考链路扣除：

令 $\Delta\!\operatorname{tr}Q:=\operatorname{tr}Q_{\text{被测}}-\operatorname{tr}Q_{\text{参考}}$。

**参考与被测应为同构（几何与器件同型、仅差路径长度）或其装置相位的能量依赖可由模型统一扣除**，否则 $\Delta\!\operatorname{tr}Q$ 不再等于 $L/c$。

对于单一S-参数 $S_{mn}$，仅在"直达真空通道、无额外色散耦合且端口等长"的条件下有 $\hbar\,\partial_E\arg S_{mn}=L/c$；否则亦需按上法相消/校准（参见§9）。^[1]

### 11.2 离散等价（RCA光锥与CHL）

半径 $r$ 的一维可逆元胞自动机（RCA）中，$t$ 步后每个元胞仅受初态 $\pm r t$ 邻域影响（归纳法可证），形成**离散光锥**，取栅距 $a$、步长 $\Delta t$ 得离散"光速" $c_{\mathrm{disc}}=r\,a/\Delta t$。

Curtis-Hedlund-Lyndon（CHL）定理刻画"连续+移位共变"的滑动块码与CA的等价性。进一步，若该滑动块码为**双射**且其逆亦为滑动块码，则得到**可逆**CA，从而在离散因果结构下实现可逆的传播光锥。^[13]

---

## 12. 与相对论/场论的相容性

* **洛伦兹协变**：标量波动方程与Maxwell方程的推迟格林函数支撑均在 $t=r/c$（§6.2），保证"光锥前沿= $c$"与协变性一致。^[9]

* **微因果**：Soulas证明"无超信号性 $\Rightarrow$ 微因果"；结合§6.1-§6.2，所得前沿与信息光锥一致。^[11]

---

## 13. 补充证明细节

### 13.1 $Q$ 的物理量纲与真空常值

由 $Q=-iS^\dagger \tfrac{dS}{dE}$ 得 $[Q]=E^{-1}$，故 $\tau_{\mathrm{WS}}=\hbar\,\operatorname{tr}Q$ 具时间量纲。

真空链路 $S_L(E)=e^{i E L/(\hbar c)}\Rightarrow \operatorname{tr}Q_L=L/(\hbar c)$ 为常值，保证 $\mathsf T=L/c$。^[1]

### 13.2 KK-因果的严格化

给定 $h\in L^2(\mathbb R)$ 支持 $[0,\infty)$，则 $H(z)$ 为上半平面全纯函数，边界值 $H(\omega)$ 的实/虚部由Hilbert变换互定，即KK关系；反向由Paley-Wiener-Titchmarsh保证 $H$ 的解析与增长条件推出 $h(t)=0$（$t<0$）。^[4]

### 13.3 光锥支撑的直接校验

对**标量**波动方程，将 $G_{\mathrm{ret}}(t,\mathbf r)=\delta(t-r/c)/(4\pi r)$ 代入波算符 $(\frac{1}{c^2}\partial_t^2-\nabla^2)$ 的分布意义计算，可得 $(\frac{1}{c^2}\partial_t^2-\nabla^2)G_{\mathrm{ret}}=\delta(t)\delta(\mathbf r)$；支撑仅在 $t=r/c$。

对**Maxwell**方程，其dyadic格林函数虽需张量-微分算子构造，但**支撑同样仅在光锥上**，故前沿速度结论相同。^[9,15]

### 13.4 信息阈值与误差指数

对二元假设检验（存在/不存在微弱信号），在独立样本数随观测时间/带宽线性增长时，最优误差指数为KL散度（Chernoff-Stein）；Dorrah-Mojahedi在含总噪声模型下跟踪"可检测信息速度"，与本定义一致。^[5]

---

## 14. 最终陈述

在SI固定 $c = 299\,792\,458$ m/s的框架下，基于Wigner-Smith延迟的窗口化群延迟方法：

1. **理论上**在理想真空链路精确恢复 $\mathsf{T} = L/c$；
2. **与散射理论、因果律、信息论（条件性）保持一致**；
3. **提供NPE三支非渐近误差账本**，为工程实现提供可计算的误差控制；
4. **与SI的"以时定长"互为实现**，可用于交叉校准与长度计量。

本文为基于WS延迟的长度计量提供了从理论验证到实践误差控制的完整闭环，展示了散射理论在精密计量中的应用潜力。

---

## 参考文献

[1] F. T. Smith, "Lifetime Matrix in Collision Theory," *Phys. Rev.* **118** (1960) 349–356.
[2] BIPM，《SI手册》（第九版，v3.02）; "SI base unit: metre (m)".
[3] A. Pushnitski, "The Birman–Krein formula," *arXiv:1006.0639* (2010).
[4] J. S. Toll, "Causality and the Dispersion Relation: Logical Foundations," *Phys. Rev.* **104** (1956) 1760–1770.
[5] A. H. Dorrah, M. Mojahedi, "Velocity of detectable information in faster-than-light pulses," *Phys. Rev. A* **90** (2014) 033822.
[6] C. E. Shannon, "Communication in the Presence of Noise," *Proc. IRE* **37** (1949) 10–21.
[7] D. H. Bailey, J. M. Borwein, "Effective Error Bounds in Euler–Maclaurin-Based Quadrature Schemes" (2005/2006).
[8] D. Borthwick, *Scattering by Obstacles* (arXiv:2110.06370, 2022).
[9] *PH519 Lecture Notes*, "The Wave Equation Green's Function" (2020).
[10] M. D. Stenner, D. J. Gauthier, M. A. Neifeld, "The speed of information in a 'fast-light' optical medium," *Nature* **425** (2003) 695–698.
[11] A. Soulas, "No-signalling implies microcausality in QFT," *arXiv:2309.07715* (2025).
[12] P. Woit, "Notes on the Poisson Summation Formula" (2020).
[13] Curtis–Hedlund–Lyndon theorem（CHL定理）条目与综述（维基）.
[14] BIPM，"SI 基本单位：米（metre）"页面.
[15] ETH Zürich, "Radiation" lecture notes, Ch. 6（时域dyadic格林函数）.

---

**（全文完）**
