# 自指散射与费米子的诞生：Riccati 平方根、旋量双覆盖与 $\mathbb{Z}_2$ 交换相位

## 摘要

给定去鉴别子后的参数空间 $X$ 与定能散射相位指数 $S:X\to U(1)$（单通道情形 $S=e^{2i\delta}$，多通道取 $\det S$），沿平方覆盖 $p:z\mapsto z^2$ 的拉回

$$
P_{\sqrt S}=\{(x,\sigma)\in X\times U(1):\ \sigma^2=S(x)\}\longrightarrow X
$$

定义散射平方根覆盖。以 Maurer–Cartan 一形式

$$
\alpha=\frac{1}{2i}\,S^{-1}dS
$$

给出 $\mathbb{Z}_2$ holonomy

$$
\nu_{\sqrt S}(\gamma)=\exp\left(i\oint_\gamma \alpha\right)=(-1)^{\deg(S|_\gamma)}\in\{\pm1\},
$$

从而消除基于 $\arg S$ 的选支歧义。平方根存在与不变量的拓扑刻画分两层：其一为覆盖—提升（$[S]\in H^1(X;\mathbb{Z})$ 的 2 可整除）；其二为线丛—陈类（由 $S$ 黏合的带平直联络复线丛 $\mathcal L_S$ 满足 $c_1(\mathcal L_S)\in 2H^2(X;\mathbb{Z})$），两者经指数短正合列的 Bockstein 配对一致。谱理论方面，在短程且无零能异常条件下，结合 Birman–Kreĭn 公式与辩值原理，得到"模 2 Levinson"

$$
\nu_{\sqrt S}(\gamma)=(-1)^{N_b(\gamma)}=(-1)^{I_2(\gamma,D)},
$$

其中 $N_b(\gamma)$ 为束缚态谱流的奇偶，$I_2(\gamma,D)$ 为参数回路与鉴别子的模 2 交数。功能分析方面，于边界三元组—Weyl 函数框架将自指闭环

$$
L=\mathcal B_\tau\big(M(E;L)\big),\qquad \mathcal B_\tau\in \mathrm{PSL}(2,\mathbb{R}),
$$

严格化，并以 Möbius 类型（双曲/抛物/椭圆）与导数横越判据刻画"两不动点交换"，其奇偶与 $\nu_{\sqrt S}$ 一致。以一维 $\delta$-势与 Aharonov–Bohm 模型给出显式算例。拓扑凝聚态方面，类 D 的 $\mathrm{sgn}\det r(0)$ 与类 DIII 的 $\mathrm{sgn}\,\mathrm{Pf}\,r(0)$ 分别等价于 $\sqrt{\det r(0)}$ 的分支号符。框架在 $d\ge 3$ 直接刻画玻色/费米交换；在 $d=2$ 捕捉任意子统计的 $\mathbb{Z}_2$ 投影（$\theta=\pi$）。

---

## 0 记号、假设与对象

**参数空间与鉴别子**
令 $X$ 为分片可微流形。鉴别子

$$
D=\{\text{上半平面 Jost 零点的生成或湮灭、零能阈值异常、嵌入本征值等发生的参数}\}
$$

确保在 $X^\circ=X\setminus D$ 上 $S:X^\circ\to U(1)$ 连续或解析，散射数据正则。

**holonomy 统一口径**

$$
\alpha=\frac{1}{2i}\,S^{-1}dS,\qquad
\nu_{\sqrt S}(\gamma)=\exp\left(i\oint_\gamma \alpha\right)=(-1)^{\deg(S|_\gamma)} .
$$

**短程与谱假设**
势 $V$ 属短程类，使 $S(E,\lambda)-\mathbf 1$ 为迹类（多通道取修正 Fredholm 行列式）；$(E,\lambda)\mapsto S$ 在闭路 $\gamma$ 上分段 $C^1$；$\gamma$ 远离阈值与嵌入本征值（若不可完全回避，则以模 2 交数刻画）。

**Birman–Kreĭn 与谱位移**
在绝对连续谱能段

$$
\det S(E,\lambda)=e^{-2\pi i\,\xi(E,\lambda)},\qquad
2\delta\equiv -2\pi\,\xi\pmod{2\pi}.
$$

当 $\gamma$ 同时改变能量与外参时，$\oint_\gamma d\xi$ 取自（修正）Fredholm 行列式的连续化分支；反向取向使 $\oint_\gamma d\xi\mapsto -\oint_\gamma d\xi$，不改变其奇偶。

---

## 1 物理图景

半相位 $s=e^{i\delta}$ 的局域规范不可测，但其全局单值化障碍可由 $\nu_{\sqrt S}$ 读出：若 $S=e^{2i\delta}$ 的绕数为奇，则 $s$ 沿参数回路变号。由此将费米交换符号、旋量 $2\pi$ 负号与散射半相位的分支切换提升为统一的 $\mathbb{Z}_2$ holonomy 问题，并以覆盖—提升与线丛—陈类的两层判据严格化。

---

## 2 覆盖—提升与线丛—陈类

### 2.1 覆盖—提升

沿平方覆盖 $p:z\mapsto z^2$ 的拉回得主 $\mathbb{Z}_2$-丛 $P_{\sqrt S}=S^*(p)\to X^\circ$，其特征类 $[P_{\sqrt S}]=[S]\bmod 2\in H^1(X^\circ;\mathbb{Z}_2)$。对闭路 $\gamma\subset X^\circ$,

$$
\mathrm{Hol}_\gamma(P_{\sqrt S})=\exp\left(i\oint_\gamma \frac{1}{2i}\,S^{-1}dS\right)=(-1)^{\deg(S|_\gamma)}.
$$

**覆盖—提升判据**：存在 $s:X^\circ\to U(1)$ 使 $s^2=S$ 当且仅当 $[S]\in 2H^1(X^\circ;\mathbb{Z})$。

### 2.2 平直线丛与 Bockstein

由 $S$ 的 Čech 黏合得到带平直联络的复线丛（局部系统） $\mathcal L_S$。其同构类由

$$
H^1(X^\circ;U(1))\cong \mathrm{Hom}(\pi_1 X^\circ,U(1))
$$

分类；其第一陈类 $c_1(\mathcal L_S)$ 为挠元。指数短正合列

$$
0\longrightarrow \mathbb{Z}\longrightarrow \mathbb{R}\longrightarrow U(1)\longrightarrow 0
$$

给出 Bockstein 态射 $\beta:H^1(X^\circ;U(1))\to H^2(X^\circ;\mathbb{Z})$，满足 $\beta([S])=c_1(\mathcal L_S)$。**线丛平方根判据**：存在 $\mathcal L_{\sqrt S}$ 使 $\mathcal L_{\sqrt S}^{\otimes 2}\cong \mathcal L_S$ 当且仅当 $c_1(\mathcal L_S)\in 2H^2(X^\circ;\mathbb{Z})$。其模 2 约化与 2.1 的覆盖障碍一致。复线丛底层实二维丛天然可定向，$w_1=0$ 与平方根存在性无涉。

---

## 3 Riccati 变量、Weyl–Titchmarsh 与 Jost 结构

Riccati 变量 $L=\psi'/\psi$ 满足

$$
L'+L^2=V-E.
$$

Weyl–Titchmarsh $(m)$-函数与抽象 Weyl 函数 $M(z)$ 属 Herglotz/Nevanlinna 类：将上半平面自映，具有非切向边界值与单调性。Jost 函数 $f$ 使

$$
S(k)=\frac{f(-k)}{f(k)}=e^{2i\delta(k)}.
$$

若 $C$ 为 $k$-平面仅围住上半平面简单零点 $k_j$ 的小正向回路，则

$$
\mathrm{wind}\Big(\frac{f(-k)}{f(k)}\Big|_C\Big)=0-1=-1,\qquad \nu_{\sqrt S}(C)=-1 .
$$

一般 $m_j$ 重零点给出 $\mathrm{wind}=-m_j$、$\nu_{\sqrt S}=(-1)^{m_j}$。

---

## 4 Birman–Kreĭn、谱位移与"模 2 Levinson"

**定理 4.1（BK 与谱流）**
在绝对连续谱能段且 $S-\mathbf 1$ 为迹类（多通道取修正 Fredholm 行列式）的条件下，存在连续谱位移 $\xi$ 使

$$
\det S(E,\lambda)=e^{-2\pi i\,\xi(E,\lambda)},\qquad
\oint_\gamma d\xi=\mathrm{Sf}(\gamma)\in\mathbb{Z}.
$$

**多参闭路约定**
当 $\gamma$ 同时改变能量与外参时，$\xi$ 取（修正）Fredholm 行列式的连续化分支；反向取向仅改变 $\oint_\gamma d\xi$ 号符，奇偶不变。

**定理 4.2（模 2 Levinson）**
在定理 4.1 的假设下，

$$
\nu_{\sqrt S}(\gamma)=\exp\left(-i\pi\oint_\gamma d\xi\right)=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)} .
$$

---

## 5 鉴别子与模 2 交数

令

$$
D=\{\text{Jost 上半平面零点生成或湮灭、阈值异常}\}\subset X .
$$

当 $\gamma$ 与 $D$ 横截时，定义模 2 交数 $I_2(\gamma,D)$。

**定理 5.1（交数判据）**

$$
\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)} .
$$

---

## 6 可解模型：$\delta$-势与两类参数环路

对 $V(x)=\lambda\delta(x)$（$\hbar=2m=1$），

$$
t(k)=\frac{2k}{2k+i\lambda},\qquad
r(k)=-\frac{i\lambda}{2k+i\lambda},\qquad
S(k)=\frac{2k-i\lambda}{2k+i\lambda}.
$$

取 $f(k)=2k-i\lambda$，则 $S=f(-k)/f(k)$。束缚态仅当 $\lambda<0$ 存在，零点 $k_\ast=i|\lambda|/2\in\mathbb{C}_+$。

**复 $\lambda$-小环（绕极点）**
$\lambda(\theta)=2ik+\rho e^{i\theta}$ 时

$$
S(\lambda(\theta))=-1+\frac{4k}{i\rho}e^{-i\theta}.
$$

随 $\theta$ 递增，$e^{-i\theta}$ 在单位圆上顺时针一周，故 $\mathrm{wind}(S)=-1$，$\nu_{\sqrt S}=-1$。

**实参数折返环**
在 $(E,\lambda)$ 平面构造"穿越 $\lambda=0$ 后返回"的折返闭路，绕行鉴别子一次，$I_2(\gamma,D)=1\Rightarrow \nu_{\sqrt S}=-1$。

---

## 7 自指散射：Möbius 类型、判别式与交换

考虑自洽闭环

$$
L=\Phi_{\tau,E}(L):=\mathcal B_\tau\big(M(E;L)\big),\qquad
\mathcal B_\tau(w)=\frac{a_\tau w+b_\tau}{c_\tau w+d_\tau}\in\mathrm{PSL}(2,\mathbb{R}),
$$

其中 $M(E;L)$ 关于 $L$ 为 Nevanlinna 家族。典型点相互作用或 Schur 补模型下

$$
\Phi(L)=\frac{\alpha L+\beta}{\gamma L+\delta},\qquad \alpha,\beta,\gamma,\delta\in\mathbb{R},\ \ \alpha\delta-\beta\gamma>0 .
$$

定义判别式

$$
\Delta=(\delta-\alpha)^2+4\beta\gamma .
$$

**类型与判据**
双曲型（$\Delta>0$）存在两边界不动点 $L_\pm$，且

$$
\mathrm{ind}(L^*)=\operatorname{sgn}\big(1-\Phi'(L^*)\big),\qquad
\Phi'(L^*)=\frac{\alpha\delta-\beta\gamma}{(\gamma L^*+\delta)^2}.
$$

抛物型（$\Delta=0$）为两不动点并合的判别子。椭圆型（$\Delta<0$）仅存在一个内点不动点，交换数为零。

**交换只发生在双曲型**
处于双曲区且闭路横截 $\Delta=0$ 一次（横截性成立）时，$L_+$ 与 $L_-$ 交换一次；交换的奇偶与 $\nu_{\sqrt S}(\gamma)$ 一致。

---

## 8 同伦配对：交换—旋转—散射（两体，$d\ge 3$）

在两体中心势下，交换路径在相对坐标与 $2\pi$ 旋转同伦。由无穷远边界扭转诱导散射映射，使

$$
\nu_{\mathrm{conf}}=\nu_{\mathrm{spin}}=\nu_{\sqrt S}.
$$

本节严格涵盖两体；$N>2$ 的推广涉及辫群表示与通道选择，超出本文范围。

---

## 9 拓扑超导端点散射：类 D 与 DIII

**D 类（仅 PHS）**
费米能处 $r(0)\in O(N)$，拓扑量

$$
Q_{\mathrm D}=\mathrm{sgn}\,\det r(0)\in\{\pm1\},
$$

等价于 $\sqrt{\det r(0)}$ 的分支号符；端口正交规范 $r\mapsto OrO^\top$（$O\in O(N)$）不改变 $\det r$。

**DIII 类（PHS+TRS，$T^2=-1$）**
可择基使 $r(0)$ 为实反对称矩阵，维数 $N$ 必为偶数，

$$
Q_{\mathrm{DIII}}=\mathrm{sgn}\,\mathrm{Pf}\,r(0),\qquad \det r(0)=\big(\mathrm{Pf}\,r(0)\big)^2,
$$

且对 $O\in\mathrm{SO}(N)$ 有 $\mathrm{Pf}(OrO^\top)=\mathrm{Pf}(r)$，故 $\mathrm{sgn}\,\mathrm{Pf}\,r(0)$ 规范不变。隙闭合处号符翻转，与 $\nu_{\sqrt{\det r}}$ 的 holonomy 同步。

---

## 10 多通道与分波（最小自洽命题）

若 $S(E,\lambda)-\mathbf 1$ 为迹类且 $(E,\lambda)\mapsto S$ 连续，则存在连续相位

$$
\det S(E,\lambda)=e^{-2\pi i\,\xi(E,\lambda)},\qquad
\nu_{\sqrt{\det S}}(\gamma)=\exp\left(i\oint_\gamma \frac{1}{2i}\,(\det S)^{-1}d(\det S)\right)
=(-1)^{\sum_j \mathrm{Sf}_j(\gamma)}=(-1)^{I_2(\gamma,D)}.
$$

球对称势下 $\det S=\prod_\ell \det S_\ell$，各分波的奇偶在模 2 下相乘；通道开闭的影响由 $I_2(\gamma,D)$ 稳定记录。

---

## 11 二维任意子与 $\mathbb{Z}_2$ 投影

Aharonov–Bohm 散射以通量 $\alpha=\Phi/\Phi_0$ 给出统计角 $\theta=2\pi\alpha$。固定能量，沿 $\alpha\mapsto \alpha+1$ 的闭路，穿越 $\alpha=\tfrac12$（$\theta=\pi$）时 $\deg(\det S)=1$，故 $\nu_{\sqrt{\det S}}=-1$。一般 $\theta\neq 0,\pi$ 的连续统计超出本文的 $\mathbb{Z}_2$ 框架。

---

## 12 结论

以 $\alpha=\frac{1}{2i}S^{-1}dS$ 的 holonomy 统一刻画的"平方根—双覆盖—$\mathbb{Z}_2$ 指标"将交换统计、旋量双覆盖与散射谱结构整合为同一可计算不变量 $\nu_{\sqrt S}$。该不变量可由主 $\mathbb{Z}_2$-丛 holonomy、Birman–Kreĭn 与谱流、鉴别子的模 2 交数以及自指闭环的双曲型分支交换四条等价链路读出；在拓扑超导端点散射中与 $\mathrm{sgn}\det r$ 与 $\mathrm{sgn}\,\mathrm{Pf}\,r$ 的号符等价。多体与二维非阿贝尔任意子、强耦合阈值与非厄米散射的平方根拓扑构成自然延展方向。

---

## 参考文献（选）

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

$U(1)$ 是 $K(\mathbb{Z},1)$，故 $[X^\circ,U(1)]\cong H^1(X^\circ;\mathbb{Z})$。平方覆盖 $p:z\mapsto z^2$ 在 $\pi_1$ 与 $H^1$ 上对应乘以 2，从而 $s^2=S$ 的全局分支存在当且仅当 $[S]\in 2H^1(X^\circ;\mathbb{Z})$。对闭路 $\gamma\subset X^\circ$,

$$
\exp\left(i\oint_\gamma \frac{1}{2i}S^{-1}dS\right)=\exp\left(\frac{i}{2}\oint_\gamma d\arg S\right)=e^{i\pi\,\deg(S|_\gamma)}=(-1)^{\deg(S|_\gamma)} .
$$

### A.2 平直线丛的分类与 Bockstein

带平直联络的复线丛（局部系统）的同构类由

$$
H^1(X^\circ;U(1))\cong \mathrm{Hom}(\pi_1 X^\circ,U(1))
$$

分类；其第一陈类 $c_1(\mathcal L_S)$ 为挠元。指数短正合列

$$
0\longrightarrow \mathbb{Z}\longrightarrow \mathbb{R}\longrightarrow U(1)\longrightarrow 0
$$

诱导 Bockstein 态射

$$
\beta:H^1(X^\circ;U(1))\longrightarrow H^2(X^\circ;\mathbb{Z}),
$$

满足 $\beta([S])=c_1(\mathcal L_S)$。平方根线丛存在当且仅当 $c_1(\mathcal L_S)\in 2H^2(X^\circ;\mathbb{Z})$。其模 2 约化与 A.1 的覆盖障碍一致。

---

## 附录 B  Jost—辩值公式与绕数

令 $f$ 为上半平面亚纯函数，$S(k)=f(-k)/f(k)$。设 $C$ 为 $k$-平面仅围住上半平面零点集合 $\{k_j\}$（计重数 $m_j$）的小正向回路，则

$$
\mathrm{wind}\Big(S\Big|_C\Big)=\sum_j\left(\mathrm{wind}\big(f(-k)\big|_C\big)-\mathrm{wind}\big(f(k)\big|_C\big)\right)=0-\sum_j m_j=-\sum_j m_j .
$$

于是

$$
\nu_{\sqrt S}(C)=\exp\left(i\oint_C \frac{1}{2i}S^{-1}dS\right)=(-1)^{\sum_j m_j}.
$$

若 $C$ 同时围住对称点 $\pm k_j$，则两项抵消，$\mathrm{wind}(S|_C)=0$。

---

## 附录 C  Birman–Kreĭn 与谱流（定理化）

在短程与迹类假设下，$\det S=e^{-2\pi i\,\xi}$ 定义了连续谱位移 $\xi$。若沿闭路 $\gamma$ 的本征相位横截，且 $\gamma$ 避开阈值与嵌入本征值，则

$$
\oint_\gamma d\xi=\mathrm{Sf}(\gamma)\in\mathbb{Z},\qquad
\nu_{\sqrt S}(\gamma)=\exp\left(-i\pi\oint_\gamma d\xi\right)=(-1)^{\mathrm{Sf}(\gamma)} .
$$

当 $\gamma$ 同时改变能量与外参时，$\xi$ 取修正 Fredholm 行列式的连续化分支；反向取向仅改变 $\oint_\gamma d\xi$ 号符而不改变其奇偶。

---

## 附录 D  交数与鉴别子（证明）

鉴别子 $D\subset X$ 由上半平面 Jost 零点生成与湮灭、阈值异常的参数集合组成，局部为余维一的正则子流形或其分片并。闭路 $\gamma$ 与 $D$ 的每一处横截对应于谱位移的半整数跃迁，从而改变束缚态数的奇偶。故

$$
\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)} .
$$

---

## 附录 E  $\delta$-势两类环路（细算）

$$
S(k)=\frac{2k-i\lambda}{2k+i\lambda},\qquad f(k)=2k-i\lambda .
$$

**复 $\lambda$-环**
$\lambda(\theta)=2ik+\rho e^{i\theta}\Rightarrow S(\lambda(\theta))=-1+\frac{4k}{i\rho}e^{-i\theta}$。随 $\theta$ 递增，$e^{-i\theta}$ 顺时针一周，$\mathrm{wind}(S)=-1\Rightarrow \nu_{\sqrt S}=-1$。

**实折返**
沿 $(E,\lambda)$ 的折返闭路横截 $D$ 一次，$\nu_{\sqrt S}=-1$。

---

## 附录 F  自指散射：Möbius 类型与交换（证明）

$$
\Phi(L)=\frac{\alpha L+\beta}{\gamma L+\delta},\qquad \alpha\delta-\beta\gamma>0,\qquad \Delta=(\delta-\alpha)^2+4\beta\gamma .
$$

若 $\Delta>0$（双曲），存在两边界不动点 $L_\pm$，且

$$
\mathrm{ind}(L^*)=\operatorname{sgn}\big(1-\Phi'(L^*)\big),\qquad \Phi'(L^*)=\frac{\alpha\delta-\beta\gamma}{(\gamma L^*+\delta)^2}.
$$

闭路横截 $\Delta=0$ 一次且横截性成立时发生一次交换。若 $\Delta=0$（抛物），两不动点并合，对应判别子。若 $\Delta<0$（椭圆），仅一内点不动点，交换数为零。交换奇偶与 $\nu_{\sqrt S}$ 一致。

---

## 附录 G  交换—旋转—散射的同伦配对（两体）

在 $d\ge 3$ 的两体中心势下，交换与 $2\pi$ 旋转同伦；由无穷远边界扭转诱导散射映射，度的模 2 等于包围的上半平面 Jost 零点数的模 2，故

$$
\nu_{\mathrm{conf}}=\nu_{\mathrm{spin}}=\nu_{\sqrt S}.
$$

---

## 附录 H  端点散射的类 D 与 DIII 指标（规范不变性）

**D 类**
$r\mapsto OrO^\top$（$O\in O(N)$）保持 $\det r$；$\mathrm{sgn}\det r(0)$ 等价于 $\sqrt{\det r(0)}$ 的分支号符。

**DIII 类**
$N$ 必为偶；取 Majorana 基使 $r(0)$ 实反对称；对 $O\in \mathrm{SO}(N)$，$\mathrm{Pf}(OrO^\top)=\mathrm{Pf}(r)$。故 $\mathrm{sgn}\,\mathrm{Pf}\,r(0)$ 规范不变，并与 $\sqrt{\det r(0)}$ 的分支号符等价。

---

## 附录 I  多通道与分波（最小命题证明）

在短程与阈值回避条件下，$\det S$ 的相位连续化可取修正 Fredholm 行列式定义；分波分解 $\det S=\prod_\ell \det S_\ell$ 下，模 2 奇偶相乘并由 $I_2(\gamma,D)$ 稳定记录通道开闭的影响。
