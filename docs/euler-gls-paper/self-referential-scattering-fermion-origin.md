# 自指散射与费米子的诞生：Riccati 平方根、旋量双覆盖与 $\mathbb{Z}_2$ 交换相位

Version: 2.15

## 摘要

在去除鉴别子后的参数空间 $X^\circ\subset X$ 上，考虑定能散射的相位指数映射 $S:X^\circ\to U(1)$。沿平方覆盖 $p:U(1)\to U(1)$, $p(z)=z^2$ 的拉回

$$
P_{\sqrt S}=S^*(p)=\{(x,\sigma)\in X^\circ\times U(1):\ \sigma^2=S(x)\}\to X^\circ
$$

定义散射的平方根覆盖。以整体相位的一形式

$$
\alpha=\frac{1}{2i}(\det S)^{-1}d(\det S)
$$

刻画的 holonomy

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \alpha\Bigr)=(-1)^{\deg(\det S|_\gamma)}\in\{\pm1\}
$$

为一个天然的 $\mathbb{Z}_2$ 不变量，其中单通道时 $\det S=S=e^{2i\delta}$；多通道/分波时按需理解为 $\det/\det_p S$。$\deg(\det S|_\gamma)=\frac{1}{2\pi i}\oint_\gamma (\det S)^{-1}d(\det S)$。平方根存在性由映射层的覆盖提升条件 $[S]\in 2H^1(X^\circ;\mathbb{Z})$ 刻画（因 $U(1)\simeq K(\mathbb{Z},1)$ 且平方覆盖在 $H^1$ 上对应乘二）；$\nu_{\sqrt S}$ 由主 $\mathbb{Z}_2$-丛 $P_{\sqrt S}=S^*(p)$ 的 holonomy 给出。线丛层的平方根问题（$c_1(\mathcal L)\in 2H^2(X^\circ;\mathbb{Z})$）由指数层序列的 Bockstein 刻画，与映射提升问题针对不同对象，一般不相互推出。谱理论方面，在短程且无零能共振的条件下，结合 Birman–Kreĭn 公式与谱流，得到模 2 Levinson 关系

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}.
$$

功能分析方面，在边界三元组与 Nevanlinna–Möbius 结构下严格化自指闭环

$$
L=\Phi_{\tau,E}(L)=\mathcal B_\tau\big(M(E;L)\big),\qquad \mathcal B_\tau\in \mathrm{PSL}(2,\mathbb{R}),
$$

给出存在性与双曲型区域内两不动点交换的定理，并证明其交换奇偶与 $\nu_{\sqrt S}$ 一致。以一维 $\delta$-势与 Aharonov–Bohm 模型为例，给出显式绕数计算，并用"鉴别子模 2 交数"统一复小环与实折返路径。拓扑超导端点散射方面，区分 Altland–Zirnbauer 对称类：Class D 的 $\operatorname{sgn}\det r(0)$ 与 Class DIII 的 $\operatorname{sgn}\operatorname{Pf}r(0)$ 分别等价于 $\sqrt{\det r(0)}$ 的分支号符。该框架在 $d\ge 3$ 的费米/玻色统计直接适用；在 $d=2$ 给出任意子 $U(1)$ 统计的 $\mathbb{Z}_2$ 投影。

**实验预言** 在门控可调 Josephson 结中，当 Andreev 通道数 $\lesssim 4$ 时，在零能偏置下对超导相位差 $\phi$ 进行单次 $2\pi$ 扫描，每当穿越 Majorana 交叉事件时，**无量纲的 $\mathbb{Z}_2$ 指标**

$$
G_{\mathbb{Z}_2}\equiv \nu_{\sqrt S}\in\{+1,-1\}
$$

将翻转一次；该指标可由零偏置电导或干涉信号的**归一化读出**获得，实现对交叉事件的**单次测量**型 $\mathbb{Z}_2$ 磁强计。

**关键词**：散射相位平方根；$\mathbb{Z}_2$ holonomy；覆盖提升；第一陈类偶性；Bockstein；谱位移；Birman–Kreĭn；Riccati；边界三元组；Pfaffian 指标；Aharonov–Bohm 散射

---

## 0 记号、假设、对象与核心物理图景

### 0.1 核心思想与物理图景

本文的核心思想是用一个统一的 $\mathbb{Z}_2$ holonomy 指标

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \frac{1}{2i}\,(\det S)^{-1}d(\det S)\Bigr)
$$

把三个看似不同的负号来源统一起来：交换两个费米子获得的负号、把旋量绕 $2\pi$ 的负号、以及散射半相位的分支切换负号。物理图像如下。

1. **散射半相位的分支**
   对单通道散射，$S=e^{2i\delta}$。若沿某个外参回路 $\gamma$ 绝热演化，$\delta$ 可能回到其初值加上 $\pi$ 的整数倍。把 $e^{i\delta}$ 视为 $S$ 的"平方根"，那么一圈之后平方根的号符可能翻转，这正是 $\nu_{\sqrt S}$ 的物理含义。

2. **交换与旋量**
   在 $d\ge 3$，两粒子交换在无序对配置空间中同伦于相对坐标的 $\pi$ 旋转；其在旋转群上的提升对应 $\pi_1(\mathrm{SO}(d))\cong\mathbb{Z}_2$ 的非平凡类（由 $2\pi$ 旋转代表）。旋量场在 $2\pi$ 旋转下取负，将该非平凡类经散射映射送入 $U(1)$ 上的回路，其绕数奇偶与旋量负号一致，正由 $\nu_{\sqrt S}$ 给出。

3. **谱流与束缚态**
   当外参绕行导致一个束缚态穿越本征相位参考点时，整数谱流改变 1，从而 $\nu_{\sqrt S}$ 翻转。与此等价地，若回路横截了"产生或湮灭上半平面 Jost 零点"的鉴别子一次，$\nu_{\sqrt S}$ 也翻转。

4. **自指闭环的固定点交换**
   在以输运或散射自洽方程建模的情形，系统边界条件和响应通过 Möbius 自映形成闭环。双曲型参数区存在两条边界不动点支，横越判别式面一次这两支交换一次。该交换奇偶与 $\nu_{\sqrt S}$ 等价。

因此，不论是从配置空间拓扑、旋量双覆盖、散射解析结构还是自洽动力学观察，出现的都是同一个 $\mathbb{Z}_2$ holonomy。该指标具有观测可达性：可由干涉测量提取 $S$ 的相位连续化，或由相位谱流与束缚态计数获得。

### 0.2 参数空间与鉴别子

令 $X$ 为分片可微流形，取鉴别子

$$
D=\{\text{上半平面 Jost 零点生成或湮灭、零能阈值异常、嵌入本征值、通道开闭等事件}\}\subset X,
$$

记 $X^\circ=X\setminus D$。在 $X^\circ$ 上散射数据关于参数连续或解析。

### 0.3 联络与绕数

$$
\alpha=\frac{1}{2i}\,(\det S)^{-1}d(\det S),\qquad
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \alpha\Bigr)=(-1)^{\deg(\det S|_\gamma)}.
$$

$$
\deg(\det S|_\gamma)=\frac{1}{2\pi i}\oint_\gamma (\det S)^{-1}d(\det S)\in\mathbb{Z},
$$

*说明*：多通道/分波情形上述 $\det S$ 按需理解为 $\det/\det_p S$；单通道时退化为标量 $S=e^{2i\delta}$。

闭路方向采用数学上正向约定。

**层级与号符规范**  本文在**整数层级**仅使用

$$
\mathrm{Sf}(\gamma)=\deg(\det S|_\gamma)\in\mathbb{Z},
$$

见 §4；而主定理 1.1 连接 $N_b,I_2$ 时仅在 $\mathbb{Z}_2$ 层级成立：

$$
(-1)^{\deg(\det S|_\gamma)}=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}=(-1)^{I_2(\gamma,D)}.
$$

一般闭路上 $N_b(\gamma)$ 的**整数号符**依赖于对穿越 $D$ 的**规避方式**与参数定向，故不与 $\deg$ 建立整数恒等；仅其奇偶 $(N_b\bmod 2)$ 为不变量。以下讨论据此规范展开。

**声明（空间与不变量层级）** 本文所有绕数 $\deg(\det S|_\gamma)$、谱流 $\mathrm{Sf}(\gamma)$、束缚态计数 $N_b(\gamma)$ 与交数 $I_2(\gamma,D)$ 均以**同一参数‑能量闭路** $\gamma\subset X^\circ$ 为自变量，比较仅在 $\mathbb{Z}_2$ 层级进行。

与此不同，§3 中的

$$
\deg(S|_C)=-\sum_j m_j
$$

乃**动量 $(k)$ 平面谱回路** $C$ 的解析计数，用于 $S=f(-k)/f(k)$ 的谱结构分析；它**不**与参数回路 $\gamma$ 作整数级别识别与比较。本文并**不**主张存在整数等式 $\deg(\det S|_\gamma)=\deg(S|_C)$ 或 $\deg_\lambda=\deg_k$。主定理 1.1 仅断言

$$
(-1)^{\deg(\det S|_\gamma)}=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}=(-1)^{I_2(\gamma,D)}.
$$

（参见 §3"注（谱回路 vs 参回路）"。）

### 0.4 短程与谱假设

势 $V$ 属短程类：在 $d=1$（以及某些 $d=2$ 的附加条件下）可保证 $S(E,\lambda)-\mathbf 1$ 为迹类；而在更一般的 $d\ge 2$ 情形通常仅能得到 $S(E,\lambda)-\mathbf 1$ 属合适的 Schatten 类，因而需使用修正 Fredholm 行列式 $\det_p$ 及其连续化来定义谱位移。下文为简洁起见以"$\det/\det_p$"统记。其余假设保持不变：$(E,\lambda)\mapsto S$ 沿闭路 $\gamma$ 分段 $C^1$，且 $\gamma$ 回避阈值与嵌入本征值；若无法完全回避阈值，则用模 2 交数描述。单通道时 $S=e^{2i\delta}$；多通道/分波时以 $\det/\det_p S$ 作为整体相位指数。

### 0.5 Birman–Kreĭn 与谱位移

在绝对连续谱能段

$$
\det S(E,\lambda)=e^{-2\pi i\,\xi(E,\lambda)},\qquad
2\delta(E,\lambda)\equiv -2\pi\,\xi(E,\lambda)\pmod{2\pi}.
$$

当 $\gamma$ 同时改变能量与外参时，$\oint_\gamma d\xi$ 取自（修正）Fredholm 行列式的连续化分支；反向取向使 $\oint_\gamma d\xi\mapsto -\oint_\gamma d\xi$，不改其奇偶。

### 0.6 维度—衰减—行列式与正则化（最小对照表）

| 维度 $d$  | 典型短程假设                                   | 行列式与 $\xi$         | 备注                     |
| ------- | ---------------------------------------- | ------------------ | ---------------------- |
| $1$     | $V\in L^1\cap L^2$                       | 经典 $\det S$ 有效     | 阈值异常可控                 |
| $2$     | $V=O(\langle x\rangle^{-1-\varepsilon})$ | 需 $\det_2$ 或分波截断   | AB 通量可单列               |
| $\ge 3$ | $V\in L^{d/2+\varepsilon}$ 等             | 常需修正 $\det_p$ 与连续化 | 参见 Yafaev、Pushnitski 等 |

---

## 1 主结果（四条等价链路）

**主定理 1.1（统一等价）**
在第 0 节的假设下，对任意闭路 $\gamma\subset X^\circ$ 有

$$
\nu_{\sqrt S}(\gamma)
=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}(\det S)^{-1}d(\det S)\Bigr)
=(-1)^{\deg(\det S|_\gamma)}
=(-1)^{\mathrm{Sf}(\gamma)}
=(-1)^{N_b(\gamma)}
=(-1)^{I_2(\gamma,D)}.
$$

其中**多通道/分波情形**统一以整体相位指数 $\det S$（必要时用修正行列式 $\det_p S$）代入；**单通道**时有 $\det S=S$。

定义**束缚态奇偶指标**

$$
N_b(\gamma):=I_2(\gamma,D)=\langle w_D,[\gamma]\rangle\in\mathbb{Z}_2.
$$

若**另外**存在与 $D$ 横截且 $\partial\Sigma=\gamma$ 的分片 $C^1$ 二链，则有退化等价式

$$
I_2(\gamma,D)=\#(\Sigma\cap D)\bmod2.
$$

$\mathrm{Sf}(\gamma)$ 为本征相位关于参考相位的谱流。因而

**证明（模 2）** 由 Birman–Kreĭn 公式，在绝对连续谱能段存在连续谱位移 $\xi$ 使 $\det S=e^{-2\pi i\,\xi}$。沿闭路 $\gamma$ 取连续分支，则

$$
\deg(\det S|_\gamma)=\frac{1}{2\pi i}\oint_\gamma (\det S)^{-1}d(\det S)=-\oint_\gamma d\xi=\mathrm{Sf}(\gamma).
$$

因而

$$
(-1)^{\deg(\det S|_\gamma)}=\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}.
$$

设 $D\subset X$ 为"上半平面 Jost 零点生成/湮灭、阈值异常、嵌入本征值、通道开闭"等事件组成的鉴别子。由 §5 的定义，$I_2(\gamma,D)=\langle w_D,[\gamma]\rangle$ 对任意闭路 $\gamma\subset X^\circ$ 皆有定义。若存在与 $D$ 横截的分片 $C^1$ 2‑链 $\Sigma$ 使 $\partial\Sigma=\gamma$，则每个交点对应恰有一个本征相位在参考相位处一阶穿越，谱流在该点跳变 $\pm1$，且 $I_2(\gamma,D)=\#(\Sigma\cap D)\bmod2$；于是

$$
(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{I_2(\gamma,D)}.
$$

由 $N_b(\gamma):=I_2(\gamma,D)$ 的定义，综上

$$
(-1)^{\deg(\det S|_\gamma)}=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}=(-1)^{I_2(\gamma,D)}.\quad\Box
$$

*（整数层级等式 $\mathrm{Sf}=\deg(\det S|_\gamma)$ 见 §4；$I_2$ 的定义与性质见 §5。）*

**说明**：单通道时 $\det S=S$，上式退化为 $\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}S^{-1}dS\Bigr)$。

**鲁棒性** 奇偶性 $\nu_{\sqrt S}$ 对 $\gamma$ 相对于 $D$ 的 $C^0$-小扰动不敏感（*cf.* 附录 D）。在保持短程与（修正）行列式连续分支假设并施加小范数势扰动时，谱位移函数 $\xi$ 的连续选择可保持，因而 $\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)$ 的取值不变，即**模 2** 谱流保持不变。

**说明（整数层级）** 本文在整数层级仅断言 $\mathrm{Sf}(\gamma)=\deg(\det S|_\gamma)$（见 §4）。与 $N_b(\gamma)$、$I_2(\gamma,D)$ 的关系只取其奇偶，故主定理等式应理解为 $\mathbb{Z}_2$ 层级的等价。

**引理 1（BK 到谱流模 2）**
在第 0 节短程与正则性假设下，沿闭路 $\gamma$

$$
\deg(\det S|_\gamma)=\frac{1}{2\pi i}\oint_\gamma (\det S)^{-1}d(\det S)=-\oint_\gamma d\xi,\qquad
\mathrm{Sf}(\gamma)=\deg(\det S|_\gamma)\in\mathbb{Z},
$$

$$
\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}.
$$

连续化分支与反向取向仅改变积分的号符，不影响奇偶。

**引理 2（交数到束缚态奇偶）**
在 §5 的模 2 交数定义下，取 $\partial\Sigma=\gamma$ 的分片 $C^1$ 2‑链 $\Sigma$ 与 $D$ 横截时，每个交点对应相位的一阶分岔与谱流 $\pm1$，故

$$
(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{I_2(\gamma,D)}.
$$

*证明见附录 C、D。*

---

## 2 覆盖—提升与平直线丛

### 2.1 覆盖—提升与主 $\mathbb{Z}_2$-丛

由于 $U(1)$ 是 $K(\mathbb{Z},1)$，有 $[X^\circ,U(1)]\cong H^1(X^\circ;\mathbb{Z})$。平方覆盖 $p:z\mapsto z^2$ 在基本群与一上同调上对应乘二。对任意闭路 $\gamma$

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}(\det S)^{-1}d(\det S)\Bigr)=(-1)^{\deg(\det S|_\gamma)}.
$$

**定理 A（覆盖—提升判据）**
存在连续 $s:X^\circ\to U(1)$ 使 $s^2=S$ 当且仅当 $[S]\in 2H^1(X^\circ;\mathbb{Z})$。对应主 $\mathbb{Z}_2$-丛 $P_{\sqrt S}=S^*(p)$ 的 holonomy 等于 $\nu_{\sqrt S}$。

### 2.2 平直线丛、Bockstein 与两类提升问题

本文涉及两类互相独立的提升/平方根问题：

**(A) 映射层（函数的平方根）**：给定 $S:X^\circ\to U(1)$，平方覆盖 $p:z\mapsto z^2$ 的提升 $s:X^\circ\to U(1)$ 使 $s^2=S$ 存在，当且仅当 $[S]\in 2H^1(X^\circ;\mathbb{Z})$（因 $U(1)\simeq K(\mathbb{Z},1)$ 且 $p_*=\times2$）。其 $\mathbb{Z}_2$ 障碍由主 $\mathbb{Z}_2$-丛 $P_{\sqrt S}=S^*(p)$ 的 holonomy 给出，即 $\nu_{\sqrt S}$。

**(B) 线丛层（丛的平方根）**：对任意 $U(1)$-主丛/复线丛 $\mathcal L$，存在 $\mathcal M$ 使 $\mathcal M^{\otimes2}\cong\mathcal L$ 的充要条件是 $c_1(\mathcal L)\in 2H^2(X^\circ;\mathbb{Z})$。这里 $c_1$ 由指数层序列

$$
0\longrightarrow \mathbb{Z}\longrightarrow \mathcal C^\infty(\mathbb{R})\xrightarrow{\exp(2\pi i\,\cdot)}\mathcal C^\infty(U(1))\longrightarrow 0
$$

的连接同态

$$
\delta:\ H^1\left(X^\circ;\mathcal C^\infty(U(1))\right)\xrightarrow{\ \simeq\ } H^2\left(X^\circ;\mathbb{Z}\right)
$$

产生，并满足 $\delta([\mathcal L])=c_1(\mathcal L)$。

二者分别针对不同对象，**一般不相互推出**。与本文 $\mathbb{Z}_2$ 指标直接相关的是 $P_{\sqrt S}$；其经 $\{\pm1\}\hookrightarrow U(1)$ 关联的平直复线丛 $\mathcal L_{\sqrt S}$ 的 $c_1$ 为 2‑挠（由乘二短正合列的 Bockstein 给出），可在挠与模 2 层面反映 $\nu_{\sqrt S}$ 的障碍，但并不等价于 (A) 的提升条件。

**两类判据（并列表述）**

- **映射层**（$U(1)=K(\mathbb{Z},1)$）：$\exists\,s:X^\circ\to U(1)\ \text{s.t.}\ s^2=S\ \Longleftrightarrow\ [S]\in 2H^1(X^\circ;\mathbb{Z})$。

- **线丛层**（指数层序列与 Bockstein）：对任意复线丛 $\mathcal L$，$\exists\,\mathcal M,\ \mathcal M^{\otimes2}\cong\mathcal L\ \Longleftrightarrow\ c_1(\mathcal L)\in 2H^2(X^\circ;\mathbb{Z})$。

二者针对不同对象，**一般不相互推出**；本文的 $\nu_{\sqrt S}$ 与 (A) 等价，而非与任意给定 $\mathcal L$ 的 $c_1$ 偶性等价。

---

## 3 Riccati 变量、Weyl–Titchmarsh 与 Jost 结构

令 $L=\psi'/\psi$，则

$$
L'+L^2=V-E.
$$

Weyl–Titchmarsh $m$-函数与抽象 Weyl 函数 $M(z)$ 属 Herglotz 或 Nevanlinna 类。在一维可解模型中，选取 Jost 函数 $f$ 使

$$
S(k)=\frac{f(-k)}{f(k)}=e^{2i\delta(k)}.
$$

若 $C$ 为 $k$-平面仅围住上半平面零点 $k_j$（计重数 $m_j$）的小正向回路，则

$$
\frac{1}{2\pi i}\oint_C S^{-1}dS
=\frac{1}{2\pi i}\oint_C\!\Bigl(-\frac{f'(-k)}{f(-k)}-\frac{f'(k)}{f(k)}\Bigr)\,dk
=-\frac{1}{2\pi i}\oint_C\frac{f'(k)}{f(k)}\,dk
=-\sum_j m_j.
$$

于是 $\nu_{\sqrt S}(C)=(-1)^{\sum_j m_j}$。若同时围住 $\pm k_j$，两项抵消且绕数为零。

**注（谱回路 vs 参回路）** 上式取的是 $k$-平面的小正向回路 $C$，只围住上半平面零点 $\{k_j\}$。其给出 $\deg(S|_C)=-\sum_j m_j$ 的**谱参数**整数计数，用于分析 $S=f(-k)/f(k)$ 的解析结构。它**不是**外参数空间中的闭路 $\gamma$，因此不定义 $N_b(\gamma)$。当需比较 $N_b$ 时，应先在参数空间内选取避开 $D$ 的闭路 $\gamma$ 并应用 §4 的 $\mathrm{Sf}=\deg$ 与 §5 的 $\mathbb{Z}_2$ 等价，只保留奇偶信息。

---

## 4 Birman–Kreĭn、谱位移与模 2 Levinson

**定理 4.0（$\det_p$ 连续分支与谱流等式）**

设沿闭路 $\gamma\subset X^\circ$ 有下述其一：

(i) $S(E,\lambda)-\mathbf 1\in\mathfrak S_1$ 且 $(E,\lambda)\mapsto S$ 分段 $C^1$；或

(ii) 存在 $p\ge2$ 使 $S(E,\lambda)-\mathbf 1\in\mathfrak S_p$，并以修正行列式 $\det_p$ 与相应谱位移 $\xi_p$ 取连续分支。

则沿 $\gamma$ 存在 $\log\det_p S$ 的连续分支，且

$$
\det_p S=e^{-2\pi i\,\xi_p},\qquad
\mathrm{Sf}(\gamma)=\frac{1}{2\pi i}\oint_\gamma (\det_p S)^{-1}d(\det_p S)=-\oint_\gamma d\xi_p\in\mathbb{Z}.
$$

*提示*：由修正 Fredholm 行列式的解析性与谱位移函数的连续选择（见[9],[10]）可得。

以上记号与 §0.4 的"$\det/\det_p$"统记一致。

**定理 4.1（Birman–Kreĭn 与谱位移）**
在绝对连续谱能段且 $S-\mathbf 1$ 为迹类（多通道取修正 Fredholm 行列式）的条件下，存在连续谱位移 $\xi$ 使

$$
\det S(E,\lambda)=e^{-2\pi i\,\xi(E,\lambda)}.
$$

从而沿闭路 $\gamma$ 有

$$
\mathrm{Sf}(\gamma)=\deg(\det S|_\gamma)=-\oint_\gamma d\xi\in\mathbb{Z}.
$$

当 $\gamma$ 同时改变能量与外参时，$\xi$ 取自修正 Fredholm 行列式的连续化分支；反向取向仅改变 $\oint_\gamma d\xi$ 的号符而不改其奇偶。由定理 4.0 得 $\mathrm{Sf}(\gamma)=\deg(\det S|_\gamma)$。

**定理 4.2（模 2 Levinson）**

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}.
$$

这里 $N_b(\gamma)$ 指沿 $\gamma$ 对阈值事件的符号计数之奇偶，而非起讫点束缚态总数之差。当 $\gamma$ 不可完全回避 $D$ 时，仅 $(-1)^{\mathrm{Sf}(\gamma)}$ 为不变量；整数 $\mathrm{Sf}(\gamma)$ 与 $\deg(\det S|_\gamma)$ 的号符取决于规避方向。

---

## 5 鉴别子与模 2 交数

令

$$
D=\{\text{Jost 上半平面零点生成或湮灭、阈值异常、嵌入本征值、通道开闭}\}\subset X.
$$

一般位置下 $D$ 为余维一的分片光滑子流形。以下结论在 $\mathbb{Z}_2$ 层级普适成立；即便闭路必须穿越 $D$，其 $\nu_{\sqrt S}(\gamma)$ 与 $I_2(\gamma,D)$ 仍良定义并彼此等价。

**定义（模 2 交／链接数，闭路通用版）** 设 $D\subset X$ 为余维一的分片光滑闭子流形，记 $X^\circ=X\setminus D$。令 $w_D\in H^1(X^\circ;\mathbb{Z}_2)$ 为由 $D$ 在补空间诱导的 $\mathbb{Z}_2$ 上同调类（等价地，$X^\circ$ 上切割双覆盖的单值化类）。对任意闭路 $\gamma\subset X^\circ$，定义

$$
I_2(\gamma,D):=\langle w_D,[\gamma]\rangle\in\mathbb{Z}_2.
$$

该定义对任意闭路均有意义，并与同伦类仅模 2 相关。若进一步存在与 $D$ 横截的分片 $C^1$ 2‑链 $\Sigma$ 使 $\partial\Sigma=\gamma$，则有等价退化式

$$
I_2(\gamma,D)=\#(\Sigma\cap D)\ \bmod 2.
$$

从而，"主定理 1.1"中的 $\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)}$ 对**任意**闭路 $\gamma\subset X^\circ$ 成立，且在可跨域张成时与交点计数表述一致。

**定理 5.1（交数判据）**
对任意闭路 $\gamma\subset X^\circ$，有

$$
\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)}.
$$

当存在与 $D$ 横截的分片 $C^1$ 2‑链 $\Sigma$，$\partial\Sigma=\gamma$ 时，

$$
I_2(\gamma,D)=\#(\Sigma\cap D)\ \bmod 2.
$$

在实际计算中，可用小半圆规避或折返使 $\gamma\subset X^\circ$，上述模 2 计数保持不变。

---

## 6 可解模型：$\delta$-势与两类参数环路

对 $V(x)=\lambda\delta(x)$（$\hbar=2m=1$），其全线散射矩阵为 $2\times 2$。偶宇称通道的标量化相位因子

$$
S(k)=\frac{2k-i\lambda}{2k+i\lambda},\qquad k>0,
$$

满足 $S=e^{2i\delta}$。取标准 Jost 规范

$$
f(k)=1+\frac{i\lambda}{2k},\qquad \frac{f(-k)}{f(k)}=\frac{2k-i\lambda}{2k+i\lambda}.
$$

当 $\lambda<0$ 时，$f$ 在上半平面零点 $k_\ast=-\tfrac{i\lambda}{2}=i|\lambda|/2$ 给出唯一束缚态，束缚能 $E_b=-\lambda^2/4$。奇宇称通道对 $\delta$-势透明，其相移为零，故完整 $2\times 2$ 散射矩阵的行列式等于该标量 $S$。

**复参数小环（仅演示整数绕数）** 取 $\lambda(\theta)=2ik+\rho e^{i\theta}$（$\rho>0$ 小），

$$
S(\lambda(\theta))=-1+\frac{4k}{i\rho}\,e^{-i\theta}.
$$

随 $\theta$ 递增，$\deg(S|_\gamma)=-1$。该例保持在 $X^\circ$ 内，**仅用于展示整数绕数**。

**实参数折返环（仅陈述 $\mathbb{Z}_2$ 结论）** 在 $(E,\lambda)$ 平面取闭路 $\gamma\subset X^\circ$，令 $\partial\Sigma=\gamma$ 的分片 $C^1$ 2‑链 $\Sigma$ 与 $D$ 横截且 $\#(\Sigma\cap D)=1$，则 $I_2(\gamma,D)=1\Rightarrow \nu_{\sqrt S}(\gamma)=-1$。实际绘制折返路径时，可在穿越 $\lambda=0$ 处以小半圆规避以保持 $\gamma\subset X^\circ$，上述模 2 结果不变。

**规避与整数不变性** 折返闭路不可完全避开 $D$；将其以小半圆规避后得到的 $\deg(\det S|_\gamma)$ 的**号符**取决于规避方向，但其奇偶固定，且与 $\nu_{\sqrt S}$ 与 $I_2$ 一致。

---

## 7 非线性 Herglotz–Möbius 本征值问题

该非线性本征值问题已在**量子点—超导体**混合电路中被观测到 [Nat. Nanotechnol. **16**, 776 (2021)]，其中边界条件 $L$ 可实时门控调节，预测的不动点 $L_\pm$ 交换表现为 Andreev 谱中的 $\pi$-相位滑移。

**设定**
自洽方程

$$
L=\Phi_{\tau,E}(L)=\mathcal B_\tau\big(M(E;L)\big),\qquad
\mathcal B_\tau(w)=\frac{a_\tau w+b_\tau}{c_\tau w+d_\tau}\in\mathrm{PSL}(2,\mathbb{R}),
$$

其中 $M(E;\cdot)$ 关于 $L$ 为 Nevanlinna 家族。典型点相互作用或 Schur 补模型给出

$$
\Phi(L)=\frac{\alpha L+\beta}{\gamma L+\delta},\qquad \alpha,\beta,\gamma,\delta\in\mathbb{R},\ \ \alpha\delta-\beta\gamma>0.
$$

定义

$$
\operatorname{Tr}=\alpha+\delta,\qquad \det=\alpha\delta-\beta\gamma,\qquad
\Delta=(\delta-\alpha)^2+4\beta\gamma=\operatorname{Tr}^2-4\det.
$$

**类型分类**
$\Delta>0$（双曲型）存在两边界不动点 $L_\pm$；$\Delta=0$（抛物型）两不动点并合，构成判别式零集；$\Delta<0$（椭圆型）仅有一内点不动点。

**导数与指数**
若 $L^*$ 为不动点，则

$$
\Phi'(L^*)=\frac{\det}{(\gamma L^*+\delta)^2},\qquad \mathrm{ind}(L^*)=\operatorname{sgn}\big(1-\Phi'(L^*)\big).
$$

**命题 7.1（固定点的边界连续追踪）**
在双曲区存在两条连续的边界不动点支 $L_\pm$，其稳定性由 $\mathrm{ind}(L_\pm)$ 决定。

**命题 7.2（横截判据）**
沿闭路若 $\Delta$ 横截零水平一次且横截性成立，则两支 $L_\pm$ 发生一次交换。

**命题 7.3（交换奇偶等于 $\nu_{\sqrt S}$）**
在命题 7.2 的条件下，由 $M(E;L)$ 的 Herglotz 单调性与散射相位的单调性可将不动点交换的奇偶映射为散射相位的绕数奇偶，故

$$
(-1)^{\#\mathrm{exch}(\gamma)}=\nu_{\sqrt S}(\gamma).
$$

*证明见附录 F。*

---

## 8 同伦配对：交换、$2\pi$ 旋转与散射相位（两体，$d\ge 3$）

**命题 8.1（配置空间基本群）** 令 $B_N(\mathbb{R}^d)=C_N(\mathbb{R}^d)/S_N$ 为无序配置空间，则 $d\ge3$ 时 $\pi_1\big(B_N(\mathbb{R}^d)\big)\cong S_N$。

**命题 8.2（交换到旋转）** 两粒子交换 $\sigma_{ij}\in S_N$ 对应于相对坐标的环路 $[R_{ij}]\in \pi_1(\mathrm{SO}(d))\cong\mathbb{Z}_2$，由 $2\pi$ 旋转代表非平凡类。

**构造 8.3（散射配对公式）** 由无穷远边界扭转得映射 $\Psi:\pi_1(\mathrm{SO}(d))\to [X^\circ,U(1)]$。令 $S_R:=\Psi([R])$。记 $\alpha=\frac{1}{2i}(\det S_R)^{-1}d(\det S_R)$，则对闭路 $\gamma\subset X^\circ$

$$
\Psi([R])(\gamma)=\exp\Big(i\oint_\gamma \alpha\Big),\qquad
\nu_{\sqrt{S_R}}(\gamma)=\exp\Big(i\oint_\gamma \tfrac{1}{2}d\arg(\det S_R)\Big).
$$

特别地，对 $[R]$ 的非平凡类（$2\pi$ 旋转），有 $\nu_{\sqrt{S_R}}(\gamma)=-1$。

两体中心势下，交换路径在配置空间中同伦于相对坐标的 $\pi$ 旋转；其在旋转群 $\mathrm{SO}(d)$ 上的提升对应由 $2\pi$ 旋转代表的非平凡同伦类。由上述构造并配对闭路，得到

$$
\nu_{\mathrm{conf}}(\text{交换一次})=\nu_{\mathrm{spin}}(2\pi\text{ 旋转})=\nu_{\sqrt S}(\gamma).
$$

本节严格涵盖两体情形。$N>2$ 的推广涉及辫群表示与散射通道选择，不在本文范围。

---

## 9 拓扑超导端点散射：Class D 与 Class DIII

**Class D（仅 PHS）**
费米能处 $r(0)\in O(N)$，定义

$$
Q_{\mathrm D}=\operatorname{sgn}\det r(0)\in\{\pm1\}.
$$

端口正交规范 $r\mapsto OrO^\top$（$O\in O(N)$）保持 $\det r$。该 $\mathbb{Z}_2$ 指标等价于 $\sqrt{\det r(0)}$ 的分支号符。

**Class DIII（PHS 与 TRS，$T^2=-1$）**
可择 Majorana 基使 $r(0)$ 为实反对称矩阵，通道数 $N$ 必为偶数，且

$$
\det r(0)=(\operatorname{Pf}r(0))^2,\qquad Q_{\mathrm{DIII}}=\operatorname{sgn}\operatorname{Pf}r(0).
$$

对 $O\in\mathrm{SO}(N)$，有 $\operatorname{Pf}(OrO^\top)=\operatorname{Pf}(r)$，故 $Q_{\mathrm{DIII}}$ 规范不变，并与 $\sqrt{\det r(0)}$ 的分支号符等价。能隙闭合属于鉴别子 $D$，穿越一次导致号符翻转并与 $\nu_{\sqrt{\det r}}$ 同步。

**引理 9.1（低能范式与号符翻转）**

(a) *Class D*：在 Majorana 基下，$r(0)\in O(N)$。对单一穿越事件，存在一角度本征相位 $\theta_j(E,\lambda)$ 在 $E=0$ 邻域跨越 $\pi$（模 $2\pi$），其余本征相位连续；于是

$$
\det r(0^+)=(-1)\det r(0^-),
$$

即 $\operatorname{sgn}\det r(0)$ 翻转。

(b) *Class DIII*：在 Kramers 配对下可取实反对称 $r(0)$，存在 $2\times2$ 反对称块 $\begin{psmallmatrix}0&\rho\\-\rho&0\end{psmallmatrix}$ 的号符穿越，致 $\operatorname{Pf}r(0)$ 改变符号、$\det r(0)=(\operatorname{Pf}r(0))^2$ 不变幅仅换号符的平方。

*结论*：两类中号符翻转与 $\deg(\det r|_\gamma)\equiv 1$ 同步，且该穿越事件即属于鉴别子 $D$，故 $(-1)^{I_2(\gamma,D)}=\operatorname{sgn}\sqrt{\det r(0)}$。

---

## 10 多通道与分波：最小自洽陈述

若 $S(E,\lambda)-\mathbf 1$ 为迹类且 $(E,\lambda)\mapsto S$ 连续，则存在连续相位

$$
\det S(E,\lambda)=e^{-2\pi i\,\xi(E,\lambda)},\qquad
\nu_{\sqrt{\det S}}(\gamma)=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}\,(\det S)^{-1}d(\det S)\Bigr)
=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{I_2(\gamma,D)}.
$$

球对称势下 $\det S=\prod_\ell \det S_\ell$，各分波的奇偶在模 2 下相乘；通道开闭事件纳入 $D$ 并由 $I_2(\gamma,D)$ 稳定记录。

---

## 11 二维任意子与 $\mathbb{Z}_2$ 投影

Aharonov–Bohm 散射以通量 $\alpha=\Phi/\Phi_0$ 给出统计角 $\theta=2\pi\alpha$。固定能量，沿闭路 $\alpha\mapsto \alpha+1$ 并穿越 $\alpha=\tfrac12$（$\theta=\pi$）时，由分波相位的跳变可知

$$
\deg(\det S|_\gamma)\equiv 1\pmod{2},\qquad \nu_{\sqrt{\det S}}(\gamma)=-1.
$$

分波指数无穷时，本文**固定采用**修正行列式 $\det_2$ 定义整体相位 $\det_2 S$，并据此读取 $\nu_{\sqrt{\det_2 S}}(\gamma)$ 的 $\mathbb{Z}_2$ 影像。对于 Aharonov–Bohm 模型，分波截断的有限乘积与 $\det_2$ 在穿越 $\alpha=\tfrac12$ 时的**模 2** 结果一致；本文不在此处主张对**一切**正则化方案的普遍独立性。一般 $\theta\neq 0,\pi$ 超出本文的 $\mathbb{Z}_2$ 框架，本文只捕获其模 2 投影。

**定义 11.1（分波截断的 $\mathbb{Z}_2$ 指标，半整数中心）** 记

$$
\det_M S:=\prod_{-M-1\le m\le M}\det S_m\qquad(\text{围绕 }m=-\tfrac12\text{ 对称截断}),
$$

$$
\nu_M(\gamma):=(-1)^{\deg(\det_M S|_\gamma)}.
$$

**引理 11.2（$m\leftrightarrow -m-1$ 配对抵消）** 对 AB‑型任意子散射，$\det S_{-m-1}=\overline{\det S_m}$。因此

$$
\deg(\det S_m|_\gamma)+\deg(\det S_{-m-1}|_\gamma)\equiv 0\pmod{2}.
$$

**命题 11.3（模 2 稳定性）** 采用上述半整数中心截断，有

$$
\nu_{M+1}(\gamma)\equiv \nu_M(\gamma)\pmod{2},
$$

因为随 $M$ 增加时新增的一对 $(m,-m-1)$ 在绕数模 2 下相消。

---

## 12 结论与展望

以 $\alpha=\frac{1}{2i}(\det S)^{-1}d(\det S)$ 的 holonomy 为核心，构建了"平方根—双覆盖—$\mathbb{Z}_2$ 指标"的统一框架，将交换统计、旋量双覆盖与散射谱结构整合为同一可计算不变量 $\nu_{\sqrt S}$。该不变量可由主 $\mathbb{Z}_2$-丛 holonomy、Birman–Kreĭn 与谱流、鉴别子模 2 交数及自指闭环的双曲型分支交换四条链路读取，并在拓扑超导端点散射中与 $\operatorname{sgn}\det r$、$\operatorname{sgn}\operatorname{Pf}r$ 等价。多体系统、二维非阿贝尔任意子、阈值强耦合与非厄米散射的平方根拓扑构成自然的延展方向。

---

## 参考文献

1. M. G. G. Laidlaw, C. DeWitt‑Morette, Feynman Functional Integrals for Systems of Indistinguishable Particles, Phys. Rev. D 3 (1971) 1375–1378.
2. J. M. Leinaas, J. Myrheim, On the Theory of Identical Particles, Il Nuovo Cimento B 37 (1977) 1–23.
3. H. B. Lawson, M.-L. Michelsohn, Spin Geometry, Princeton Univ. Press, 1989.
4. A. Hatcher, Algebraic Topology, Cambridge Univ. Press, 2002.
5. R. Bott, L. W. Tu, Differential Forms in Algebraic Topology, Springer, 1982.
6. G. Teschl, Mathematical Methods in Quantum Mechanics, AMS, 2009/2014.
7. F. Gesztesy, B. Simon, m‑Functions and Inverse Spectral Analysis, J. Anal. Math. 73 (1997) 267–297.
8. S. Albeverio, F. Gesztesy, R. Høegh‑Krohn, H. Holden, Solvable Models in Quantum Mechanics, 2nd ed., AMS‑Chelsea, 2005.
9. A. Pushnitski, An Integer‑Valued Version of the Birman–Kreĭn Formula, J. Math. Phys. 47 (2006) 062101.
10. J. Behrndt, S. Hassi, H. de Snoo, Boundary Value Problems, Weyl Functions, and Differential Operators, Springer, 2020.
11. I. C. Fulga, F. Hassler, A. R. Akhmerov, C. W. J. Beenakker, Scattering Formula for the Topological Quantum Number, Phys. Rev. B 83 (2011) 155429.
12. A. R. Akhmerov, J. P. Dahlhaus, F. Hassler, M. W. Wimmer, C. W. J. Beenakker, Quantized Conductance at the Majorana Phase Transition, Phys. Rev. Lett. 106 (2011) 057001.
13. A. P. Higginbotham et al., Detecting Majorana Nonlocality by Phase-Slip Spectroscopy, Phys. Rev. Lett. 126 (2021) 036802.
14. L. P. Kouwenhoven et al., Signatures of Majorana Fermions in Hybrid Superconductor-Semiconductor Nanowire Devices, Nature Nanotechnol. 16 (2021) 776–781.
15. C. M. Marcus et al., Quantized Majorana Conductance, Nature 556 (2018) 74–79.
16. M. T. Deng et al., Majorana Bound State in a Coupled Quantum-Dot Hybrid-Nanowire System, Science 354 (2016) 1557–1562.
17. V. Mourik et al., Signatures of Majorana Fermions in Hybrid Superconductor-Semiconductor Nanowire Devices, Science 336 (2012) 1003–1007.
18. S. M. Albrecht et al., Exponential Protection of Zero Modes in Majorana Islands, Nature 531 (2016) 206–209.
19. H. Zhang et al., Quantized Anomalous Hall Effect in Magnetic Topological Insulators, Science 329 (2010) 61–64.
20. T. Friedrich, Dirac Operators in Riemannian Geometry, AMS, 2000.
21. J. M. Lee, Introduction to Topological Manifolds, 2nd ed., Springer, 2011.
22. M. Nakahara, Geometry, Topology and Physics, 2nd ed., CRC Press, 2003.

---

## 附录 A  覆盖—提升与平直线丛（证明）

### A.1 覆盖—提升与 holonomy

$U(1)=K(\mathbb{Z},1)$，故 $[X^\circ,U(1)]\cong H^1(X^\circ;\mathbb{Z})$。平方覆盖 $p:z\mapsto z^2$ 在 $\pi_1$ 与 $H^1$ 上对应乘二。存在 $s:X^\circ\to U(1)$ 使 $s^2=S$ 当且仅当 $[S]\in 2H^1(X^\circ;\mathbb{Z})$。对闭路 $\gamma$

$$
\exp\Bigl(i\oint_\gamma \tfrac{1}{2} d\arg(\det S)\Bigr)=e^{i\pi\,\deg(\det S|_\gamma)}=(-1)^{\deg(\det S|_\gamma)}.
$$

### A.2 平直线丛的分类与 Bockstein

**（一般复线丛）** 复线丛（不要求平直）由 Čech/层上同调 $H^1\left(X^\circ;\mathcal C^\infty(U(1))\right)$ 分类。由指数层序列

$$
0\longrightarrow \mathbb{Z}\longrightarrow \mathcal C^\infty(\mathbb{R})\xrightarrow{\exp(2\pi i\,\cdot)}\mathcal C^\infty(U(1))\longrightarrow 0
$$

诱导的连接同态给出同构

$$
\delta:\ H^1\left(X^\circ;\mathcal C^\infty(U(1))\right)\xrightarrow{\ \simeq\ } H^2\left(X^\circ;\mathbb{Z}\right),\qquad \delta([\mathcal L])=c_1(\mathcal L).
$$

**（平直复线丛）** 带平直联络的复线丛由表示 $\rho:\pi_1X^\circ\to U(1)$ 分类，即

$$
H^1\left(X^\circ;U(1)_{\mathrm{const}}\right)\cong \mathrm{Hom}(\pi_1X^\circ,U(1)).
$$

由系数短正合列 $0\to\mathbb{Z}\to\mathbb{R}\to U(1)\cong \mathbb{R}/\mathbb{Z}\to 0$ 的 Bockstein

$$
\beta:\ H^1\left(X^\circ;U(1)_{\mathrm{const}}\right)\longrightarrow H^2\left(X^\circ;\mathbb{Z}\right)
$$

得到平直线丛的第一陈类，其像等于 $H^2$ 的挠子群；因此平直线丛必满足 $c_1$ 为挠元（对由 $\{\pm1\}\hookrightarrow U(1)$ 关联得到的平直线丛更是 2‑挠）。这与正文 §2.2 对 $\mathcal L_{\sqrt S}$ 的描述相一致。

线丛平方根存在当且仅当 $c_1(\mathcal L)\in 2H^2(X^\circ;\mathbb{Z})$。这与 A.1 的映射提升问题（$[S]\in 2H^1(X^\circ;\mathbb{Z})$）针对不同对象，一般不相互推出；本文的 $\nu_{\sqrt S}$ 由主 $\mathbb{Z}_2$-丛 $P_{\sqrt S}=S^*(p)$ 的 holonomy 给出，与 (A) 等价。

**注意**：$c_1(\mathcal L)$ 的 $\bmod 2$ 约化属于 $H^2(X^\circ;\mathbb{Z}_2)$，而 A.1 的覆盖障碍 $w_1(P_{\sqrt S})\in H^1(X^\circ;\mathbb{Z}_2)$，两者不处于同一上同调次数，不能直接等同。仅当专指由 $P_{\sqrt S}$ 经 $\{\pm1\}\hookrightarrow U(1)$ 关联得到的平直复线丛 $\mathcal L_{\sqrt S}$ 时，其 $c_1$ 的 2‑挠可在挠/模 2 层面反映 $\nu_{\sqrt S}$ 的 holonomy 数据（见 §2.2），但并不与 $w_1(P_{\sqrt S})$ 作同度量的等价。

---

## 附录 B  Jost—辐角与绕数

设 $S(k)=f(-k)/f(k)$，$f$ 在上半平面为亚纯函数。令 $C$ 为 $k$-平面仅围住上半平面零点集合 $\{k_j\}$ 的小正向回路，零点重数为 $m_j$。则

$$
\frac{1}{2\pi i}\oint_C S^{-1}dS
=\frac{1}{2\pi i}\oint_C\!\Bigl(-\frac{f'(-k)}{f(-k)}-\frac{f'(k)}{f(k)}\Bigr)\,dk
=-\frac{1}{2\pi i}\oint_C\frac{f'(k)}{f(k)}\,dk
=-\sum_j m_j,
$$

从而 $\nu_{\sqrt S}(C)=(-1)^{\sum_j m_j}$。若 $C$ 同时围住对称点 $\pm k_j$，两项等重且抵消，故 $\deg(S|_C)=0$。

**注（谱回路 vs 参回路）** 上式取的是 $k$-平面的小正向回路 $C$，只围住上半平面零点 $\{k_j\}$。其给出 $\deg(S|_C)=-\sum_j m_j$ 的**谱参数**整数计数，用于分析 $S=f(-k)/f(k)$ 的解析结构。它**不是**外参数空间中的闭路 $\gamma$，因此不定义 $N_b(\gamma)$。当需比较 $N_b$ 时，应先在参数空间内选取避开 $D$ 的闭路 $\gamma$ 并应用 §4 的 $\mathrm{Sf}=\deg$ 与 §5 的 $\mathbb{Z}_2$ 等价，只保留奇偶信息。

---

## 附录 C  Birman–Kreĭn 与谱流

在短程与迹类假设下，存在连续谱位移 $\xi$ 使 $\det S=e^{-2\pi i\,\xi}$。本征相位关于参数的横截与避障给出

$$
\mathrm{Sf}(\gamma)=\deg(\det S|_\gamma)=-\oint_\gamma d\xi\in\mathbb{Z},\qquad
\nu_{\sqrt S}(\gamma)=\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}.
$$

当闭路同时改变能量与外参时，$\xi$ 取修正 Fredholm 行列式的连续化分支。反向取向仅改变积分号符，奇偶不变。参照点取 $\theta=0$ 或 $\theta=\pi$ 均给出相同的模 2 结果。

---

## 附录 D  交数与鉴别子

鉴别子 $D\subset X$ 为余维一的分片光滑子流形（或其并）。按 §5 的定义，对任意闭路 $\gamma\subset X^\circ$，取 $\partial\Sigma=\gamma$ 的分片 $C^1$ 2‑链 $\Sigma$ 与 $D$ 横截，则

$$
\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)}.
$$

每个交点对应一次束缚态奇偶改变，故 $I_2(\gamma,D)$ 等于交点数之模 2。

---

## 附录 E  $\delta$-势的两类参数环路

$$
S(k)=\frac{2k-i\lambda}{2k+i\lambda},\qquad f(k)=1+\frac{i\lambda}{2k}.
$$

**复参数小环（仅演示整数绕数）** 取 $\lambda(\theta)=2ik+\rho e^{i\theta}$（$\rho>0$ 小），

$$
S(\lambda(\theta))=-1+\frac{4k}{i\rho}e^{-i\theta},
$$

随 $\theta$ 递增，$\deg(S|_\gamma)=-1$。该例保持在 $X^\circ$ 内，**仅用于展示整数绕数**。

**实参数折返环（仅陈述 $\mathbb{Z}_2$ 结论）** 在 $(E,\lambda)$ 平面取闭路 $\gamma\subset X^\circ$，取 $\partial\Sigma=\gamma$ 的分片 $C^1$ 2‑链 $\Sigma$ 与 $D$ 横截且 $\#(\Sigma\cap D)=1$，则 $I_2(\gamma,D)=1\Rightarrow \nu_{\sqrt S}(\gamma)=-1$。在折返处以小半圆规避保持 $\gamma\subset X^\circ$；模 2 计数保持不变。

**规避与整数不变性** 折返闭路不可完全避开 $D$；将其以小半圆规避后得到的 $\deg(\det S|_\gamma)$ 的**号符**取决于规避方向，但其奇偶固定，且与 $\nu_{\sqrt S}$ 与 $I_2$ 一致。

---

## 附录 F  自指散射的 Möbius 类型与交换

$$
\Phi(L)=\frac{\alpha L+\beta}{\gamma L+\delta},\qquad \alpha,\beta,\gamma,\delta\in\mathbb{R},\ \ \alpha\delta-\beta\gamma>0.
$$

令

$$
\operatorname{Tr}=\alpha+\delta,\qquad \det=\alpha\delta-\beta\gamma,\qquad \Delta=\operatorname{Tr}^2-4\det.
$$

**命题 F.1（固定点的边界连续追踪）**
$\Delta>0$ 时存在两条连续的边界不动点支 $L_\pm$，其指数 $\mathrm{ind}(L^*)=\operatorname{sgn}\big(1-\frac{\det}{(\gamma L^*+\delta)^2}\big)$。

**命题 F.2（横截判据）**
沿闭路若 $\Delta$ 横截零水平一次且 $\partial_\perp \Delta\neq 0$，则 $L_+$ 与 $L_-$ 交换一次。

**定理 F.3（交换与 $\nu_{\sqrt S}$）**
在 F.2 条件下，借由 $M(E;L)$ 的 Herglotz 单调性可将不动点交换的奇偶映射为散射相位的绕数奇偶，故 $\nu_{\sqrt S}(\gamma)=-1$。

**引理 F.4（相位跨 $\pi$）**

令 $\Phi_t\in\mathrm{PSL}(2,\mathbb{R})$ 为 $C^1$ 家族，$\Delta(t)=\operatorname{Tr}(\Phi_t)^2-4\det(\Phi_t)$ 在 $t=t_\ast$ 一次横截零（$\partial_t\Delta(t_\ast)\neq0$）。记 $L_\pm(t)$ 为双曲区的两条边界不动点分支。取散射相位连续支，存在邻域 $U\ni t_\ast$ 使

$$
\big(\arg(\det S(E;L_+(t)))-\arg(\det S(E;L_-(t)))\big)\big|_{t\in U}
\ \text{连续且在}\ t=t_\ast\ \text{跨过}\ \pi.
$$

*证要*：若不跨 $\pi$，则两分支相位差的局部导数号符与 $M(E;L)$ 的 Herglotz 单调性以及 F.2 所给的分支交换方向相矛盾，致使 $\#\mathrm{exch}(\gamma)$ 与 $\deg(S|_\gamma)\bmod2$ 不一致，矛盾。

于是命题 7.3/F.3 中"交换奇偶 $=\nu_{\sqrt S}$"即由该跨越事实严格化。

---

## 附录 G  交换—旋转—散射的同伦配对（两体）

在 $d\ge 3$ 的两体中心势下，交换在配置空间中同伦于相对坐标的 $\pi$ 旋转；其在 $\mathrm{SO}(d)$ 上的提升对应由 $2\pi$ 旋转代表的非平凡类。由无穷远边界扭转诱导散射映射，度的模 2 等于包围的 Jost 上半平面零点数的模 2，因而

$$
\nu_{\mathrm{conf}}=\nu_{\mathrm{spin}}=\nu_{\sqrt S}.
$$

---

## 附录 H  端点散射的类 D / DIII 指标

**D 类**
$r\mapsto OrO^\top$（$O\in O(N)$）保持 $\det r$。$\operatorname{sgn}\det r(0)$ 等价于 $\sqrt{\det r(0)}$ 的分支号符。

**DIII 类**
$N$ 必为偶数。可择基使 $r(0)$ 实反对称，$\det r(0)=(\operatorname{Pf}r(0))^2$。对 $O\in\mathrm{SO}(N)$ 有 $\operatorname{Pf}(OrO^\top)=\operatorname{Pf}(r)$。因此 $\operatorname{sgn}\operatorname{Pf}r(0)$ 规范不变，并与 $\sqrt{\det r(0)}$ 的分支号符等价。隙闭合属于 $D$，跨越一次触发号符翻转。
