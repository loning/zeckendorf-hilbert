# 自指散射与费米子的诞生：Riccati 平方根、旋量双覆盖与 $\mathbb{Z}_2$ 交换相位

Version: 1.3

## 摘要

在去除鉴别子后的参数空间 $X^\circ\subset X$ 上，考虑定能散射的相位指数映射 $S:X^\circ\to U(1)$。沿平方覆盖 $p:U(1)\to U(1)$, $p(z)=z^2$ 的拉回

$$
P_{\sqrt S}=S^*(p)=\{(x,\sigma)\in X^\circ\times U(1):\ \sigma^2=S(x)\}\to X^\circ
$$

定义散射的平方根覆盖。以 Maurer–Cartan 一形式

$$
\alpha=\frac{1}{2i}\,S^{-1}dS
$$

刻画的 holonomy

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \alpha\Bigr)=(-1)^{\deg(S|_\gamma)}\in\{\pm1\}
$$

为一个天然的 $\mathbb{Z}_2$ 不变量，其中 $\deg(S|_\gamma)=\frac{1}{2\pi i}\oint_\gamma S^{-1}dS$。平方根存在与 $\nu_{\sqrt S}$ 可在两层拓扑判据中刻画并保持一致：其一是映射层的覆盖提升条件 $[S]\in 2H^1(X^\circ;\mathbb{Z})$；其二是线丛层的陈类偶性 $c_1(\mathcal L_S)\in 2H^2(X^\circ;\mathbb{Z})$，其中 $\mathcal L_S$ 为由 $S$ 对应的平直复线丛且 $c_1(\mathcal L_S)$ 是指数短正合列的 Bockstein 像。谱理论方面，在短程且无零能共振的条件下，结合 Birman–Kreĭn 公式与谱流，得到模 2 Levinson 关系

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}.
$$

功能分析方面，在边界三元组与 Nevanlinna–Möbius 结构下严格化自指闭环

$$
L=\Phi_{\tau,E}(L)=\mathcal B_\tau\big(M(E;L)\big),\qquad \mathcal B_\tau\in \mathrm{PSL}(2,\mathbb{R}),
$$

给出存在性与双曲型区域内两不动点交换的定理，并证明其交换奇偶与 $\nu_{\sqrt S}$ 一致。以一维 $\delta$-势与 Aharonov–Bohm 模型为例，给出显式绕数计算，并用"鉴别子模 2 交数"统一复小环与实折返路径。拓扑超导端点散射方面，区分 Altland–Zirnbauer 对称类：Class D 的 $\operatorname{sgn}\det r(0)$ 与 Class DIII 的 $\operatorname{sgn}\operatorname{Pf}r(0)$ 分别等价于 $\sqrt{\det r(0)}$ 的分支号符。该框架在 $d\ge 3$ 的费米/玻色统计直接适用；在 $d=2$ 给出任意子 $U(1)$ 统计的 $\mathbb{Z}_2$ 投影。

**关键词**：散射相位平方根；$\mathbb{Z}_2$ holonomy；覆盖提升；第一陈类偶性；Bockstein；谱位移；Birman–Kreĭn；Riccati；边界三元组；Pfaffian 指标；Aharonov–Bohm 散射

---

## 0 记号、假设、对象与核心物理图景

### 0.1 核心思想与物理图景

本文的核心思想是用一个统一的 $\mathbb{Z}_2$ holonomy 指标

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \frac{1}{2i}\,S^{-1}dS\Bigr)
$$

把三个看似不同的负号来源统一起来：交换两个费米子获得的负号、把旋量绕 $2\pi$ 的负号、以及散射半相位的分支切换负号。物理图像如下。

1. **散射半相位的分支**
   对单通道散射，$S=e^{2i\delta}$。若沿某个外参回路 $\gamma$ 绝热演化，$\delta$ 可能回到其初值加上 $\pi$ 的整数倍。把 $e^{i\delta}$ 视为 $S$ 的"平方根"，那么一圈之后平方根的号符可能翻转，这正是 $\nu_{\sqrt S}$ 的物理含义。

2. **交换与旋量**
   在三维及更高维，两粒子交换路径同伦于相对坐标的 $2\pi$ 旋转。旋量场在 $2\pi$ 旋转下取负，把这一路径以散射映射送入 $U(1)$ 上的回路，其绕数奇偶就给出与旋量负号一致的 $\nu_{\sqrt S}$。

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

### 0.3 holonomy 口径与绕数

$$
\alpha=\frac{1}{2i}\,S^{-1}dS,\qquad
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \alpha\Bigr)=(-1)^{\deg(S|_\gamma)},
$$

$$
\deg(S|_\gamma)=\frac{1}{2\pi i}\oint_\gamma S^{-1}dS\in\mathbb{Z},
$$

闭路方向采用数学上正向约定。

### 0.4 短程与谱假设

势 $V$ 属短程类，使 $S(E,\lambda)-\mathbf 1$ 为迹类；多通道取修正 Fredholm 行列式。假定 $(E,\lambda)\mapsto S$ 在闭路 $\gamma$ 上分段 $C^1$，且 $\gamma$ 远离阈值与嵌入本征值。若无法完全回避阈值，则以模 2 交数描述。单通道时 $S=e^{2i\delta}$；多通道时以 $\det S$ 作为整体相位指数。

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
=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}S^{-1}dS\Bigr)
=(-1)^{\deg(S|_\gamma)}
=(-1)^{\mathrm{Sf}(\gamma)}
=(-1)^{N_b(\gamma)}
=(-1)^{I_2(\gamma,D)}.
$$

其中 $\mathrm{Sf}(\gamma)$ 为本征相位关于参考相位的谱流，$N_b(\gamma)$ 为沿闭路 $\gamma$ 束缚态穿越连续谱阈值的符号计数（出生计 $+1$、湮灭计 $-1$），其奇偶与 $\mathrm{Sf}(\gamma)$ 等价，$I_2(\gamma,D)$ 为 $\gamma$ 与鉴别子 $D$ 的模 2 交数。

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
当 $\gamma$ 与 $D$ 横截时，每个横截点对应相位的一阶分岔与谱流 $\pm1$，故

$$
(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{I_2(\gamma,D)}.
$$

*证明见附录 C、D。*

---

## 2 覆盖—提升与平直线丛

### 2.1 覆盖—提升与主 $\mathbb{Z}_2$-丛

由于 $U(1)$ 是 $K(\mathbb{Z},1)$，有 $[X^\circ,U(1)]\cong H^1(X^\circ;\mathbb{Z})$。平方覆盖 $p:z\mapsto z^2$ 在基本群与一上同调上对应乘二。对任意闭路 $\gamma$

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}S^{-1}dS\Bigr)=(-1)^{\deg(S|_\gamma)}.
$$

**定理 A（覆盖—提升判据）**
存在连续 $s:X^\circ\to U(1)$ 使 $s^2=S$ 当且仅当 $[S]\in 2H^1(X^\circ;\mathbb{Z})$。对应主 $\mathbb{Z}_2$-丛 $P_{\sqrt S}=S^*(p)$ 的 holonomy 等于 $\nu_{\sqrt S}$。

### 2.2 平直线丛、Bockstein 与陈类偶性

带平直联络的复线丛同构类由

$$
H^1(X^\circ;U(1))\cong \mathrm{Hom}(\pi_1X^\circ,U(1))
$$

分类。指数短正合列

$$
0\longrightarrow \mathbb{Z}\longrightarrow \mathbb{R}\longrightarrow U(1)\longrightarrow 0
$$

诱导 Bockstein 态射 $\beta:H^1(X^\circ;U(1))\to H^2(X^\circ;\mathbb{Z})$，并有 $\beta([\mathcal L_S])=c_1(\mathcal L_S)$。平方根线丛存在当且仅当 $c_1(\mathcal L_S)\in 2H^2(X^\circ;\mathbb{Z})$。复线丛的底层实二维丛天然可定向，故 $w_1(\mathcal L_S)=0$ 与平方根存在性无关。

**两层判据的相容性（并列表述）**

- **映射层**（$U(1)=K(\mathbb{Z},1)$）：存在连续 $s$ 使 $s^2=S$ $\Leftrightarrow$ $[S]\in 2H^1(X^\circ;\mathbb{Z})$。

- **线丛层**（平直联络）：指数短正合列 $0\to\mathbb{Z}\to\mathbb{R}\to U(1)\to 0$ 诱导 Bockstein $\beta:H^1(X^\circ;U(1))\to H^2(X^\circ;\mathbb{Z})$，且 $\beta([\mathcal L_S])=c_1(\mathcal L_S)$。平方根线丛存在 $\Leftrightarrow$ $c_1(\mathcal L_S)\in 2H^2(X^\circ;\mathbb{Z})$。

二者在模 2 层面的障碍与 $\nu_{\sqrt S}(\gamma)=(-1)^{\deg(S|_\gamma)}$ 一致。

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
=\sum_j\left(\frac{1}{2\pi i}\oint_C \frac{f'(-k)}{f(-k)}(-dk)-\frac{1}{2\pi i}\oint_C \frac{f'(k)}{f(k)}\,dk\right)
=-\sum_j m_j,
$$

于是 $\nu_{\sqrt S}(C)=(-1)^{\sum_j m_j}$。若同时围住 $\pm k_j$，两项抵消且绕数为零。

---

## 4 Birman–Kreĭn、谱位移与模 2 Levinson

**定理 4.1（Birman–Kreĭn 与谱位移）**
在绝对连续谱能段且 $S-\mathbf 1$ 为迹类（多通道取修正 Fredholm 行列式）的条件下，存在连续谱位移 $\xi$ 使

$$
\det S(E,\lambda)=e^{-2\pi i\,\xi(E,\lambda)}.
$$

从而沿闭路 $\gamma$ 有

$$
\mathrm{Sf}(\gamma)=\deg(\det S|_\gamma)=-\oint_\gamma d\xi\in\mathbb{Z}.
$$

当 $\gamma$ 同时改变能量与外参时，$\xi$ 取自修正 Fredholm 行列式的连续化分支；反向取向仅改变 $\oint_\gamma d\xi$ 的号符而不改其奇偶。

**定理 4.2（模 2 Levinson）**

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}.
$$

这里 $N_b(\gamma)$ 指沿 $\gamma$ 对阈值事件的符号计数之奇偶，而非起讫点束缚态总数之差。

---

## 5 鉴别子与模 2 交数

令

$$
D=\{\text{Jost 上半平面零点生成或湮灭、阈值异常、嵌入本征值、通道开闭}\}\subset X.
$$

一般位置下 $D$ 为余维一的分片光滑子流形。定义模 2 交数 $I_2(\gamma,D)$。

**定理 5.1（交数判据）**
当 $\gamma$ 与 $D$ 横截时，

$$
\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)}.
$$

不可完全回避阈值时，可采用小半圆切除或折返以获得等价的模 2 结果。

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

**复参数小环（绕极点）**
取 $\lambda(\theta)=2ik+\rho e^{i\theta}$（$\rho>0$ 小）。有

$$
S(\lambda(\theta))=-1+\frac{4k}{i\rho}\,e^{-i\theta}.
$$

随 $\theta$ 递增，$e^{-i\theta}$ 在单位圆顺时针一周，故 $\deg(S|_\gamma)=-1$，$\nu_{\sqrt S}=-1$。

**实参数折返环**
在 $(E,\lambda)$ 平面以穿越 $\lambda=0$ 并返回的折返闭路横截鉴别子一次，$I_2(\gamma,D)=1\Rightarrow \nu_{\sqrt S}=-1$。

---

## 7 自指散射：Nevanlinna–Möbius 结构与交换

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
$\Delta>0$（双曲型）存在两边界不动点 $L_\pm$；$\Delta=0$（抛物型）两不动点并合，构成判别子；$\Delta<0$（椭圆型）仅有一内点不动点。

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

两体中心势下，配置空间的交换路径与相对坐标的 $2\pi$ 旋转同伦。由无穷远边界扭转构造散射诱导映射 $\Psi:\pi_1(\mathrm{SO}(d))\to [X^\circ,U(1)]$ 并配对闭路，得到

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

Aharonov–Bohm 散射以通量 $\alpha=\Phi/\Phi_0$ 给出统计角 $\theta=2\pi\alpha$。固定能量，沿闭路 $\alpha\mapsto \alpha+1$ 时穿越 $\alpha=\tfrac12$（$\theta=\pi$），有 $\deg(\det S|_\gamma)=1$，故 $\nu_{\sqrt{\det S}}=-1$。一般 $\theta\neq 0,\pi$ 超出本文的 $\mathbb{Z}_2$ 框架，本文只捕获其模 2 投影。分波数目无穷时采用分波截断的有限乘积极限或修正行列式 $\det_2$ 正则化，所给 $\mathbb{Z}_2$ 结果与正则化选择无关。

---

## 12 结论与展望

以 $\alpha=\frac{1}{2i}S^{-1}dS$ 的 holonomy 为核心，构建了"平方根—双覆盖—$\mathbb{Z}_2$ 指标"的统一框架，将交换统计、旋量双覆盖与散射谱结构整合为同一可计算不变量 $\nu_{\sqrt S}$。该不变量可由主 $\mathbb{Z}_2$-丛 holonomy、Birman–Kreĭn 与谱流、鉴别子模 2 交数及自指闭环的双曲型分支交换四条链路读取，并在拓扑超导端点散射中与 $\operatorname{sgn}\det r$、$\operatorname{sgn}\operatorname{Pf}r$ 等价。多体系统、二维非阿贝尔任意子、阈值强耦合与非厄米散射的平方根拓扑构成自然的延展方向。

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
13. T. Friedrich, Dirac Operators in Riemannian Geometry, AMS, 2000.
14. J. M. Lee, Introduction to Topological Manifolds, 2nd ed., Springer, 2011.
15. M. Nakahara, Geometry, Topology and Physics, 2nd ed., CRC Press, 2003.

---

## 附录 A  覆盖—提升与平直线丛（证明）

### A.1 覆盖—提升与 holonomy

$U(1)=K(\mathbb{Z},1)$，故 $[X^\circ,U(1)]\cong H^1(X^\circ;\mathbb{Z})$。平方覆盖 $p:z\mapsto z^2$ 在 $\pi_1$ 与 $H^1$ 上对应乘二。存在 $s:X^\circ\to U(1)$ 使 $s^2=S$ 当且仅当 $[S]\in 2H^1(X^\circ;\mathbb{Z})$。对闭路 $\gamma$

$$
\exp\Bigl(i\oint_\gamma \tfrac{1}{2} d\arg S\Bigr)=e^{i\pi\,\deg(S|_\gamma)}=(-1)^{\deg(S|_\gamma)}.
$$

### A.2 平直线丛的分类与 Bockstein

带平直联络的复线丛由 $H^1(X^\circ;U(1))\cong \mathrm{Hom}(\pi_1X^\circ,U(1))$ 分类。指数短正合列

$$
0\longrightarrow \mathbb{Z}\longrightarrow \mathbb{R}\longrightarrow U(1)\longrightarrow 0
$$

诱导 Bockstein 态射 $\beta:H^1(X^\circ;U(1))\to H^2(X^\circ;\mathbb{Z})$，并有 $\beta([\mathcal L_S])=c_1(\mathcal L_S)$。平方根线丛存在当且仅当 $c_1(\mathcal L_S)\in 2H^2(X^\circ;\mathbb{Z})$。其模 2 约化与 A.1 的覆盖障碍一致。

---

## 附录 B  Jost—辐角与绕数

设 $S(k)=f(-k)/f(k)$，$f$ 在上半平面为亚纯函数。令 $C$ 为 $k$-平面仅围住上半平面零点集合 $\{k_j\}$ 的小正向回路，零点重数为 $m_j$。则

$$
\frac{1}{2\pi i}\oint_C S^{-1}dS
=\sum_j\left(\frac{1}{2\pi i}\oint_C \frac{f'(-k)}{f(-k)}(-dk)-\frac{1}{2\pi i}\oint_C \frac{f'(k)}{f(k)}\,dk\right)
=-\sum_j m_j,
$$

从而 $\nu_{\sqrt S}(C)=(-1)^{\sum_j m_j}$。若 $C$ 同时围住对称点 $\pm k_j$，两项等重且抵消，故 $\deg(S|_C)=0$。

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

鉴别子 $D\subset X$ 为余维一的分片光滑子流形（或其并），由上半平面 Jost 零点生成或湮灭、阈值异常、嵌入本征值、通道开闭等事件组成。当 $\gamma$ 与 $D$ 横截时，每次横截触发束缚态奇偶改变一次，故

$$
\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)}.
$$

---

## 附录 E  $\delta$-势的两类参数环路

$$
S(k)=\frac{2k-i\lambda}{2k+i\lambda},\qquad f(k)=1+\frac{i\lambda}{2k}.
$$

复 $\lambda$-环：$\lambda(\theta)=2ik+\rho e^{i\theta}$ 给出

$$
S(\lambda(\theta))=-1+\frac{4k}{i\rho}e^{-i\theta},
$$

随 $\theta$ 递增，$e^{-i\theta}$ 顺时针一周，$\deg(S|_\gamma)=-1\Rightarrow \nu_{\sqrt S}=-1$。实折返：在 $(E,\lambda)$ 平面绕行并横截 $D$ 一次，$\nu_{\sqrt S}=-1$。

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

---

## 附录 G  交换—旋转—散射的同伦配对（两体）

在 $d\ge 3$ 的两体中心势下，交换与 $2\pi$ 旋转同伦。由无穷远边界扭转诱导散射映射，度的模 2 等于包围的 Jost 上半平面零点数的模 2，因而

$$
\nu_{\mathrm{conf}}=\nu_{\mathrm{spin}}=\nu_{\sqrt S}.
$$

---

## 附录 H  端点散射的类 D / DIII 指标

**D 类**
$r\mapsto OrO^\top$（$O\in O(N)$）保持 $\det r$。$\operatorname{sgn}\det r(0)$ 等价于 $\sqrt{\det r(0)}$ 的分支号符。

**DIII 类**
$N$ 必为偶数。可择基使 $r(0)$ 实反对称，$\det r(0)=(\operatorname{Pf}r(0))^2$。对 $O\in\mathrm{SO}(N)$ 有 $\operatorname{Pf}(OrO^\top)=\operatorname{Pf}(r)$。因此 $\operatorname{sgn}\operatorname{Pf}r(0)$ 规范不变，并与 $\sqrt{\det r(0)}$ 的分支号符等价。隙闭合属于 $D$，跨越一次触发号符翻转。
