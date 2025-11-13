# 自指散射与费米子的诞生：Riccati 平方根、旋量双覆盖与 $\mathbb{Z}_2$ 交换相位

Version: 2.29

## 摘要

在去除鉴别子后的参数空间 $X^\circ\subset X$ 上，考虑定能散射的**相位指数映射** $\mathfrak s:X^\circ\to U(1)$。沿平方覆盖 $p:U(1)\to U(1)$, $p(z)=z^2$ 的拉回

$$
P_{\sqrt{\mathfrak s}}=\mathfrak s^*(p)=\{(x,\sigma)\in X^\circ\times U(1):\ \sigma^2=\mathfrak s(x)\}\to X^\circ
$$

定义平方根覆盖。一般多通道或非迹类情形取

$$
\mathfrak s(E,\lambda):=e^{-2\pi i\,\xi_p(E,\lambda)}\in U(1),
$$

其中 $\xi_p$ 由（修正）Fredholm 行列式定义的谱位移。**单通道且散射矩阵** $S(E,\lambda)-\mathbf 1\in\mathfrak S_1$ **时**，$\mathfrak s=\det S$，并有

$$
\alpha=\tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s,\qquad
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \alpha\Bigr)
=\exp\Bigl(-i\pi\oint_\gamma d\xi_p\Bigr).
$$

$\deg(\mathfrak s|_\gamma)=\frac{1}{2\pi i}\oint_\gamma \mathfrak s^{-1}d\mathfrak s\in\mathbb{Z}$。其奇偶 $(-1)^{\deg(\mathfrak s|_\gamma)}$ 为天然的 $\mathbb{Z}_2$ 不变量（闭路取向改变仅翻号而不改奇偶）。平方根存在性由映射层的覆盖提升条件 $[\mathfrak s]\in 2H^1(X^\circ;\mathbb{Z})$ 刻画；$\nu_{\sqrt S}$ 为主 $\mathbb{Z}_2$‑丛 $\mathfrak s^*(p)$ 的 holonomy（'$\sqrt S$'指 $\mathfrak s$ 的平方根覆盖）。该条件与线丛平方根 $c_1(\mathcal L)\in2H^2$ 属不同层级，一般不互推。**谱理论方面**：在短程与假设 A 下，**（迹类）** 若 $S-\mathbf 1\in\mathfrak S_1$，由 Birman–Kreĭn 得

$$\mathrm{Sf}(\gamma)=\frac{1}{2\pi i}\oint \mathfrak s^{-1}d\mathfrak s=-\oint d\xi;$$

**（一般 Schatten）** 仅主张其**模 2**：

$$\nu_{\sqrt S}(\gamma)=\exp\Bigl(-i\pi\oint d\xi_p\Bigr),$$

而不宣称 $-\oint d\xi_p$ 等于整数谱流。

功能分析方面，在边界三元组与 Nevanlinna–Möbius 结构下严格化自指闭环

$$
L=\Phi_{\tau,E}(L)=\mathcal B_\tau\big(M(E;L)\big),\qquad \mathcal B_\tau\in \mathrm{PSL}(2,\mathbb{R}),
$$

其中 $L$ 取值域为闭上半平面边界/扩展实轴，以吻合 Möbius 变换在 $\mathrm{PSL}(2,\mathbb R)$ 作用下的自然相位边界。

给出存在性与双曲型区域内两不动点交换的定理，并证明其交换奇偶与 $\nu_{\sqrt S}$ 一致。以一维 $\delta$-势与 Aharonov–Bohm 模型为例，给出显式绕数计算，并用"鉴别子模 2 交数"统一复小环与实折返路径。拓扑超导端点散射方面，区分 Altland–Zirnbauer 对称类：Class D 的 $\operatorname{sgn}\det r(0)$ 与 Class DIII 的 $\operatorname{sgn}\operatorname{Pf}r(0)$ 分别等价于 $\sqrt{\det r(0)}$ 的分支号符。该框架在 $d\ge 3$ 的费米/玻色统计直接适用；在 $d=2$ 给出任意子 $U(1)$ 统计的 $\mathbb{Z}_2$ 投影。

**实验预言（单次 $\mathbb{Z}_2$ 读出协议）**

在门控可调 Josephson 结中，取 Andreev 通道数 $\lesssim 4$ 且能够分辨**单一** $\pi$ 跃迁。设超导相位差 $\phi$ 在一次 $2\pi$ 扫描中以步长 $\Delta\phi$ 记录零偏置信号 $Y(\phi)$（电导或干涉幅）。

**(i) 归一化**：以一周期平均 $\langle Y\rangle_\phi$ 做幅度归一化，得 $\widetilde Y(\phi)=Y(\phi)/\langle Y\rangle_\phi$。

**(ii) 翻转检出（形态学规则）**：用滑动窗口跟踪**局部极性**；当 $\widetilde Y(\phi)$ 在相邻采样点**首次**变号且其**邻域内无第二次变号**，记为一次**$\pi$ 跃迁**。累积翻转奇偶：

$$
G_{\mathbb{Z}_2}\equiv \nu_{\sqrt S}\in\{+1,-1\}.
$$

可设最小驻点幅度门限以抑制噪声误触发。

**(iii) 采样条件（充分而非必要）**：要求**相邻样本不跨两次翻转**，取

$$
\Delta\phi<\tfrac12\,\Delta\phi_\pi\quad
(\text{等价 }2\Delta\phi<\Delta\phi_\pi;\ \text{时间域 } 2\Delta t<\tau_\pi),
$$

其中 $\tau_\pi/\Delta\phi_\pi$ 为**单一 $\pi$ 跃迁**的最短时间/相位尺度。

*（以上规则对幅度漂移与弱非绝热扰动具有鲁棒的**模 2** 判据。）*

**关键词**：散射相位平方根；$\mathbb{Z}_2$ holonomy；覆盖提升；第一陈类偶性；Bockstein；谱位移；Birman–Kreĭn；Riccati；边界三元组；Pfaffian 指标；Aharonov–Bohm 散射

---

## 0 记号、假设、对象与核心物理图景

### 0.1 核心思想与物理图景

本文的核心思想是用一个统一的 $\mathbb{Z}_2$ holonomy 指标

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s\Bigr)
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

*黑盒提示*：本文记号"$\sqrt S$"一律指 $\mathfrak s:X^\circ\to U(1)$ 的**平方根覆盖**（即主 $\mathbb{Z}_2$-丛的 holonomy），**不**指矩阵意义上的平方根。详见 §2。

### 0.2 参数空间、鉴别子与一般位置

令 $X$ 为分片可微流形，记去鉴别子空间 $X^\circ:=X\setminus D$。我们以**一般位置/横截**作为默认正则性：

**假设 D（横截-余维一正则性）**

存在有限集合 $\{D_j\}_{j=1}^J$ 使

(i) 每个 $D_j\subset X$ 为**余维一**的分片 $C^1$ **闭**子流形；

(ii) $D:=\bigcup_{j=1}^J D_j$ 对应如下事件之一的参数超曲面：**（a）**Jost 上半平面零点的生成/湮灭；**（b）**零能阈值异常；**（c）**嵌入本征值；**（d）**通道开闭；

(iii) 若在具体模型族中某事件集合先验并非余维一，则允许对势或外参作任意小的 $C^1$-扰动使之处于一般位置而满足 (i)。

**注**：我们在每个连通的能-参域上工作，并**默认** $X^\circ$ 的每个连通分支内可作相位的连续支选择（见假设 A）。

在 $X^\circ$ 上散射数据关于参数连续或解析。基于 Alexander 对偶与 Mayer–Vietoris，可在 $X^\circ$ 上定义由 $D$ 诱导的**模 2 链接类**

$$
w_D\in H^1(X^\circ;\mathbb Z_2),
$$

其在几何上由绕行任意小的法向环（链接 $D$ 一次）取值为 $1$ 给出。该类在 (i)–(iii) 的一般位置假设下是**良定**的。

### 0.2a 避障闭路与取向约定

令 $D\subset X$ 为 §0.2 所述的鉴别子并满足一般位置。对任意闭路 $\gamma\subset X$，若 $\gamma\cap D\neq\varnothing$，在每个横截点处取半径 $\varepsilon>0$ 的小半圆向**法向正向**规避，得 $\gamma_\varepsilon\subset X^\circ:=X\setminus D$。本文一律以**数学正向（逆时针）**为取向约定，并定义

$$
\deg(\mathfrak s|_\gamma):=\frac{1}{2\pi i}\oint_{\gamma_\varepsilon}\mathfrak s^{-1}d\mathfrak s,\qquad
\nu_{\sqrt S}(\gamma):=\exp\Bigl(i\oint_{\gamma_\varepsilon}\tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s\Bigr).
$$

反向取向仅改变整数号符，不改其奇偶。规避方式的不同可能改变整数 $\deg$ 的号符，但**不影响**$\nu_{\sqrt S}(\gamma)\in\{\pm1\}$ 的取值；相应的模 $2$ 交数 $I_2(\gamma,D)$ 对规避方式也**不敏感**（§5）。

所有**模 2** 结论（$\nu_{\sqrt S}$、$I_2$ 等）对规避方式与闭路取向**不敏感**；仅整数绕数的号符受其影响。

### 0.2b  $w_D$ 的存在性与自然性（形式化）

**命题 0.2bis（$w_D$ 的存在性与自然性）**

设 $X$ 为第二可数的分片 $C^1$ 流形，$D\subset X$ 为**余维一**分片 $C^1$ **闭**子流形并满足一般位置假设。令 $X^\circ:=X\setminus D$。则存在唯一的类

$$
w_D\in H^1(X^\circ;\mathbb Z_2),
$$

使得任意充分小的法向正向小环 $\eta$ 链接 $D$ 一次时 $\langle w_D,[\eta]\rangle=1$。以下记号约定：对闭路 $\gamma$，其规避版本记为 $\gamma_\varepsilon\subset X^\circ$，并定义

$$
I_2(\gamma,D):=\langle w_D,[\gamma_\varepsilon]\rangle\in\mathbb Z_2 .
$$

规避独立性的具体陈述与交数计数见 §5。

### 0.3 联络、绕数与"$\sqrt S$"的含义

设

$$
\mathfrak s:=e^{-2\pi i\,\xi_p}\in U(1),\qquad
\alpha=\tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s .
$$

当 $S-\mathbf 1\in\mathfrak S_1$（迹类）时 $\mathfrak s=\det S$；一般情形取修正 Fredholm 行列式给出的 $\xi_p$（见 §0.4/§4）。对任意闭路 $\gamma\subset X$（若 $\gamma\cap D\neq\varnothing$ 按 §0.2a 取规避闭路 $\gamma_\varepsilon\subset X^\circ$），定义

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \alpha\Bigr)
=(-1)^{\deg(\mathfrak s|_\gamma)},\qquad
\deg(\mathfrak s|_\gamma)=\frac{1}{2\pi i}\oint_\gamma \mathfrak s^{-1}d\mathfrak s\in\mathbb Z .
$$

**取向**采用数学上正向（逆时针）；反向仅翻号，不改奇偶。

本文在**整数层级**仅使用 $\mathrm{Sf}(\gamma)=\deg(\mathfrak s|_\gamma)$ 的迹类结论（见 §4）；在**模 2 层级**比较 $\mathrm{Sf}$、束缚态奇偶与交数（见 §5）。"$\sqrt S$"一律指 $\mathfrak s$ 的平方根覆盖所对应的主 $\mathbb{Z}_2$-丛 holonomy。

**全篇唯一约定（重要）**：记号"$\sqrt S$"一律指 $\mathfrak s:X^\circ\to U(1)$ 的**平方根覆盖**（即主 $\mathbb{Z}_2$-丛 $P_{\sqrt{\mathfrak s}}=\mathfrak s^*(p)$ 的 holonomy），**不**指矩阵意义的平方根。文中"$\sqrt{\det r(0)}$ 的分支号符"等短语悉依此约定，均是指**映射层**平方根覆盖的**号符分支**，而非对 $\det r(0)$ 求矩阵平方根。参见 §2（覆盖—提升判据）与 §9（D/DIII 指标）。

### 0.4 短程与谱假设

势 $V$ 属短程类：在 $d=1$（以及某些 $d=2$ 的附加条件下）可保证 $S(E,\lambda)-\mathbf 1$ 为迹类；而在更一般的 $d\ge 2$ 情形通常仅能得到 $S(E,\lambda)-\mathbf 1$ 属合适的 Schatten 类，因而需使用修正 Fredholm 行列式 $\det_p$ 及其连续化来定义谱位移。下文为简洁起见以"$\det/\det_p$"统记。其余假设保持不变：$(E,\lambda)\mapsto S$ 沿闭路 $\gamma$ 分段 $C^1$，且 $\gamma$ 回避阈值与嵌入本征值；若无法完全回避阈值，则用模 2 交数描述。单通道时 $S=e^{2i\delta}$；多通道/分波时以 $\det/\det_p S$ 作为整体相位指数。

**假设 A（Schatten‑连续性与阈值规避的一致化选择）**

我们只使用 $\xi_p$ 的**连续化支**来定义整体相位指数；**不要求** $\det_p S\in U(1)$。

令 $\gamma\subset X$ 为闭路。存在 $p\in\mathbb N,\ p\ge2$ 与 $\varepsilon_0>0$，使得：

**(A1)** 对每点 $(E,\lambda)\in\gamma$，$S(E,\lambda)-\mathbf 1\in\mathfrak S_p$，且 $(E,\lambda)\mapsto S(E,\lambda)$ 在 $\gamma$ 上为连续的 $\mathfrak S_p$‑值映射；

**(A2)** $\gamma$ 与鉴别子 $D$ 至多作有限个横截交；按 §5 的规避约定取 $\gamma_{\varepsilon}\subset X^\circ$（$0<\varepsilon<\varepsilon_0$）并固定；

**(A3″)** 在绝对连续谱上 $S(E,\lambda)$ 幺正且 $S(E,\lambda)-\mathbf 1\in\mathfrak S_p$（$p\ge2$），**存在正则化谱位移** $\xi_p(E,\lambda)$ 的一条沿 $\gamma_\varepsilon$ 的**连续化支**，据此定义

$$
\mathfrak s(E,\lambda):=\exp\bigl(-2\pi i\,\xi_p(E,\lambda)\bigr)\in U(1).
$$

**我们不要求** $\det_p S(E,\lambda)$ 本身落在单位圆上。

**(A4″)** 以（A3″）选定的 $\xi_p$ 定义

$$
\deg(\mathfrak s|_{\gamma})=-\oint_{\gamma_\varepsilon} d\xi_p ,\qquad
\nu_{\sqrt S}(\gamma):=\exp\Bigl(-i\pi\oint_{\gamma_\varepsilon} d\xi_p\Bigr).
$$

上述 $\mathbb Z_2$ 读数对规避方式**不敏感**。

**引理 0.A（$\xi_p$ 的连续化与模 $2$ 稳定性）**

在 (A1)–(A2) 与 (A3″) 下，沿规避闭路 $\gamma_\varepsilon\subset X^\circ$ 存在正则化谱位移 $\xi_p$ 的**局部连续化选择**，且任意两条连续化选择之差为整数常数。因而

$$
\exp\Bigl(-i\pi\oint_{\gamma_\varepsilon} d\xi_p\Bigr)
$$

与选择无关；反向取向仅使积分变号，但**奇偶不变**。

*（证明略：利用 $\mathfrak S_p$‑连续性与幺正性在避开 $D$ 的管状邻域上拼接局部辐角，差别仅为 $\mathbb Z$，见**引理 4.0bis**的连续化与**定理 4.2**的模 2 一致性。）*

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

**横截局部模型（加强版）** 设闭路 $\gamma$ 与鉴别子 $D$ 横截。对每个横截点存在参数 $t$ 的局部坐标与本征相位基，使某一通道相位 $\theta_j(t)$ 满足 $\partial_t\theta_j(t_\ast)\neq0$ 且在 $t_\ast$ 邻域**跨越** $\pi$（模 $2\pi$），其余通道相位连续。在 $t=t_\ast$ 邻域除该单一通道外，其余本征相位在参考相位 $0,\pi$ 处**保持开隙**（不切触）。该"单通道跨 $\pi$"规范与 $D$ 的横截性等价，且用于 §4 的模 $2$ 谱流与 §5 的交数记账。

**引理 1.0ter（Kato‑选择 + 单通道化横截）**

在 §0.2 的横截‑余维一正则性与 §0.2a 的规避约定下，若参考相位 $0$ 或 $\pi$ 处开隙，且某时刻仅有一条本征相位与参考相位作一阶横截，则存在一组沿参数的连续本征向量与本征相位选择，使该通道在横截点邻域满足 $\partial_t\theta(t_\ast)\neq0$ 并跨越 $\pi$（模 $2\pi$），其余通道相位在 $t_\ast$ 连续。

*（证明略：由单值的 Herglotz 单调性与 Kato 选择定理，在横截点局部作可分离规范。）*

**引理 1.0bis（横截 ⇒ 单通道跨 $\pi$ 的规范化）**

在 §0.2 的横截-余维一正则性与 §0.2a 的规避约定下，设闭路参数化为 $t\mapsto x(t)$，并在横截点 $t=t_\ast$ 的邻域作本征相位的可分离规范。则存在某一通道相位 $\theta_j(t)$ 使得

$$
\theta_j(t_\ast-0)\in(-\pi,0),\qquad \theta_j(t_\ast+0)\in(0,\pi)\quad \text{或反之，}
$$

而其余通道相位在 $t_\ast$ 连续。因此相对于任意参考相位 $0$ 或 $\pi$，该横截点对 $\mathrm{Sf}$ 的贡献为 $\pm1$；其**奇偶**不依赖参考相位与规避方式。

**主定理 1.1（统一等价；整数=迹类，模 2=一般 Schatten）**

在 §0 的短程与正则性设定、假设 A 与假设 D 下，对任意闭路 $\gamma\subset X$（若 $\gamma\cap D\neq\varnothing$，按 §0.2a 取规避闭路 $\gamma_\varepsilon\subset X^\circ$）：

$$
\nu_{\sqrt S}(\gamma)
=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s\Bigr)
=(-1)^{\deg(\mathfrak s|_\gamma)}
=(-1)^{\mathrm{Sf}(\gamma)}
=(-1)^{N_b(\gamma)}
=(-1)^{I_2(\gamma,D)}.
$$

其中 $\mathfrak s=e^{-2\pi i\,\xi_p}$；当 $S-\mathbf 1\in\mathfrak S_1$ 时 $\mathfrak s=\det S$。

* **整数层级（迹类）**：若 $S-\mathbf 1\in\mathfrak S_1$ 沿 $\gamma_\varepsilon$ 连续，则 $\mathrm{Sf}(\gamma)=\deg(\mathfrak s|_\gamma)=-\oint_{\gamma_\varepsilon} d\xi\in\mathbb Z$。

* **模 2 层级（一般 Schatten）**：在假设 A（$p\ge2$ 可取）下，仅主张

  $$
  \exp\Bigl(-i\pi\oint_{\gamma_\varepsilon} d\xi_p\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}=(-1)^{I_2(\gamma,D)} .
  $$

**证明素描（统一版）**

迹类时由 BK 得 $\deg(\mathfrak s|_\gamma)=-\oint d\xi=\mathrm{Sf}(\gamma)\in\mathbb Z$；一般 Schatten 时，仅保留

$\exp(-i\pi\oint d\xi_p)=(-1)^{\mathrm{Sf}(\gamma)}$（见**引理 4.0bis**与**定理 4.2**）。横截局部模型把"相位跨 $\pi$"与"$\partial_t\theta\neq0$"等价，谱流的奇偶与"交/链接数"一致（§5 定理 5.1）。合并得

$$
\nu_{\sqrt S}(\gamma)=(-1)^{\deg}=(-1)^{\mathrm{Sf}}=(-1)^{N_b}=(-1)^{I_2}.
$$

*（整数层级不比较谱回路与参回路；仅在模 2 层级以交数作桥接。）*

**定义（束缚态奇偶）**

令 $\gamma$ 的规避为 $\gamma_\varepsilon$。沿 $\gamma_\varepsilon$ 连续追踪本征相位：每当存在一支相位 $\theta_j$ 在参考相位 $0$ 或 $\pi$ 处**横截**（见"横截局部模型（加强版）"），计 $+1$ 或 $-1$（方向决定符号）。定义 $\widetilde N_b(\gamma)$ 为总计数，$N_b(\gamma):=\widetilde N_b(\gamma)\bmod2$。

**括注**：此处"束缚态"一词仅为术语沿用，指的是**单位圆上本征相位对参考相位的横截事件**（亦即相位谱流的穿越计数），并不等价于哈密顿量在能量轴上的束缚能级穿越；选择 $\theta=0$ 或 $\pi$ 在 $\mathbb{Z}_2$ 层级等价。

**定义（模 2 交/链接数）** $I_2(\gamma,D)=\langle w_D,[\gamma_\varepsilon]\rangle\in\mathbb Z_2$。

**取向与规避**：闭路取向反转仅改变整数号符，不改奇偶；当 $\gamma$ 与 $D$ 横截时，按 §5 的规避约定取 $\gamma_\varepsilon\subset X^\circ$，本文所有模 2 结论对规避方式**不敏感**。

**注（谱回路 vs 参回路）** 见 §3 注。

**引理 1（BK→谱流；分层版）**

在第 0 节短程与正则性假设下，沿闭路 $\gamma$（按 §0.2a 规避为 $\gamma_\varepsilon$）：

(a) **迹类整数版**（$S-\mathbf 1\in\mathfrak S_1$）：

$$
\deg(\mathfrak s|_\gamma)=\frac{1}{2\pi i}\oint_{\gamma_\varepsilon}\mathfrak s^{-1}d\mathfrak s=-\oint_{\gamma_\varepsilon} d\xi,\qquad
\mathrm{Sf}(\gamma)=\deg(\mathfrak s|_\gamma)\in\mathbb Z.
$$

(b) **Schatten‑连续性模 2 版**（$p\ge 2$）：

$$
\exp\Bigl(-i\pi\oint_{\gamma_\varepsilon} d\xi_p\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}.
$$

反向取向仅改变积分号符，不影响 (b) 的奇偶结论。

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
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s\Bigr)=(-1)^{\deg(\mathfrak s|_\gamma)}.
$$

**定理 A（覆盖—提升判据）**
存在连续 $s:X^\circ\to U(1)$ 使 $s^2=\mathfrak s$ 当且仅当 $[\mathfrak s]\in 2H^1(X^\circ;\mathbb{Z})$。对应主 $\mathbb{Z}_2$-丛 $P_{\sqrt{\mathfrak s}}=\mathfrak s^*(p)$ 的 holonomy 等于 $\nu_{\sqrt S}$（此处"$\sqrt S$"指 $\mathfrak s$ 的平方根覆盖）。

*推论*：$\nu_{\sqrt S}(\gamma)=(-1)^{[\mathfrak s]([\gamma_\varepsilon])}$，即为 $[\mathfrak s]\in H^1(X^\circ;\mathbb Z)$ 对闭路类 $[\gamma_\varepsilon]$ 的奇偶配对。

**引理 2.A（holonomy 的规避独立性，模 $2$）**

若 $\gamma$ 与 $D$ 仅作有限个横截交，按 §0.2a 得到任意两条规避闭路 $\gamma_\varepsilon,\gamma_{\varepsilon'}\subset X^\circ$，则

$$
\operatorname{Hol}_{P_{\sqrt{\mathfrak s}}}(\gamma_\varepsilon)
=\operatorname{Hol}_{P_{\sqrt{\mathfrak s}}}(\gamma_{\varepsilon'})\in\{\pm1\},
$$

因而 $\nu_{\sqrt S}(\gamma)$ 在 $\mathbb Z_2$ 层级与规避选择无关。

*（证明见 §5 命题 5.0ter 与"规避独立性（模 2）"。）*

*补充*：若 $\gamma\cap D\neq\varnothing$，按 §0.2a 取规避闭路 $\gamma_\varepsilon\subset X^\circ$，并以 $\operatorname{Hol}_{P_{\sqrt{\mathfrak s}}}(\gamma_\varepsilon)$ 定义 $\nu_{\sqrt S}(\gamma)$；该值在 $\mathbb Z_2$ 层级对规避选择不变（见 §0.2a 与 §5 约定）。

### 2.2 平直线丛、Bockstein 与两类提升问题

**两类提升与障碍（映射层 vs 线丛层）**

（A）**映射层（函数的平方根）**：给定 $\mathfrak s:X^\circ\to U(1)$，平方覆盖 $p:z\mapsto z^2$ 的提升 $s:X^\circ\to U(1)$ 使 $s^2=\mathfrak s$ 存在，当且仅当 $[\mathfrak s]\in 2H^1(X^\circ;\mathbb{Z})$（因 $U(1)\simeq K(\mathbb{Z},1)$ 且 $p_*=\times 2$）。由此得到的主 $\mathbb{Z}_2$-丛 $P_{\sqrt{\mathfrak s}}=\mathfrak s^*(p)$ 的 holonomy 正是本文的 $\nu_{\sqrt S}$。

（B）**线丛层（丛的平方根）**：对任意复线丛 $\mathcal L$，存在 $\mathcal M$ 使 $\mathcal M^{\otimes2}\cong\mathcal L$ 的充要条件是 $c_1(\mathcal L)\in 2H^2(X^\circ;\mathbb{Z})$，其中 $c_1$ 由指数层序列 $0\to\mathbb{Z}\to\mathcal C^\infty(\mathbb R)\xrightarrow{\exp(2\pi i\,\cdot)}\mathcal C^\infty(U(1))\to0$ 的连接同态给出。

**警示**：两类问题**针对不同对象**，**两者不互推**。本文的 $\nu_{\sqrt S}$ 与 (A) 等价，而非与任意给定复线丛的 $c_1$ 偶性等价。仅当特指由 $P_{\sqrt{\mathfrak s}}$ 经包含 $\{\pm1\}\hookrightarrow U(1)$ 关联得到的**特定平直线丛** $\mathcal L_{\sqrt{\mathfrak s}}$ 时，其 $c_1$ 为 $2$-挠，与 $\nu_{\sqrt S}$ 的 holonomy 数据在挠/模 $2$ 层面相容，但该 $c_1$ 与 $w_1(P_{\sqrt{\mathfrak s}})\in H^1(X^\circ;\mathbb Z_2)$ **并非同度量的等价物**。本文一律以 (A) 的提升障碍与 $P_{\sqrt{\mathfrak s}}$ 的 holonomy 作为 $\nu_{\sqrt S}$ 的定义依据。

*读者提示（层级区分）*：本文的平方根问题分属两层级：

* **映射层**：$\mathfrak s:X^\circ\to U(1)$ 的提升障碍在 $H^1(X^\circ;\mathbb Z)$（判据：$[\mathfrak s]\in 2H^1$）。

* **线丛层**：复线丛 $\mathcal L$ 的平方根障碍在 $H^2(X^\circ;\mathbb Z)$（判据：$c_1(\mathcal L)\in 2H^2$）。

  **两者不互推**；仅当专指由 $P_{\sqrt{\mathfrak s}}$ 关联得到的平直线丛时，其 $c_1$ 的 2‑挠与 $\nu_{\sqrt S}$ 的 holonomy 在**挠/模2**层面相容。

**提示（层级区分）**：本文只讨论**映射层**平方根问题 $(s^2=\mathfrak s)$ 与其主 $\mathbb{Z}_2$‑丛 holonomy；一般复线丛的平方根 $(c_1(\mathcal L)\in 2H^2)$ 属**不同层级**，二者不互相推出。仅当专指由 $P_{\sqrt{\mathfrak s}}$ 关联得到的平直线丛 $\mathcal L_{\sqrt{\mathfrak s}}$ 时，其 $c_1$ 为 $2$‑挠并与 $\nu_{\sqrt S}$ 的挠/模 $2$ 数据相容。

---

## 3 Riccati 变量、Weyl–Titchmarsh 与 Jost 结构

**注（谱回路 vs 参回路）**

本节的回路 $C$ 位于 $k$-平面，用于分析 $S(k)=f(-k)/f(k)$ 的解析结构，给出 $\deg(S|_C)$ 的**谱参数**计数；而主文中的 $\gamma$ 是 $(E,\lambda)$-空间中的**外参闭路**。我们在**整数层级**从不比较 $\deg(S|_C)$ 与 $\deg(\mathfrak s|_\gamma)$；仅在 §4–§5 的桥接下，把两者作**模 $2$** 投影的比较，用于判定 $\nu_{\sqrt S}(\gamma)$。

**说明**：本节仅限单通道或球对称分波情形；多通道一般情形下 $S(k)$ 为矩阵，$f(k)$ 为多分量 Jost 解，表达式需修正为 $\det S(k)=\det[f(-k)f(k)^{-1}]$。

令 $L=\psi'/\psi$，则

$$
L'+L^2=V-E.
$$

*符号提示*：本节 $L=\psi'/\psi$ 为 Riccati 变量；"自指闭环"中的 $L$ 为边界参数的实轴取值，二者不相混。

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

**注（谱回路 vs 参回路）** 见本节开头总注。

---

## 4 Birman–Kreĭn、谱位移与模 2 Levinson

（本节主要引用 [9] 的整数值 Birman–Kreĭn 公式与 [10] 的边界三元组理论。）

**定义 4.0（本征相位的谱流，单位圆版本）**

对闭路 $\gamma\subset X$（若 $\gamma\cap D\neq\varnothing$，按 §0.2a 取规避闭路 $\gamma_\varepsilon\subset X^\circ$），定义**本征相位的谱流** $\mathrm{Sf}(\gamma)$ 为：沿 $\gamma_\varepsilon$ 连续追踪本征相位 $\theta(E,\lambda)$，每当其横截参考相位（如 $\theta=0$ 或 $\pi$）时计数 $\pm1$（穿越方向决定符号），总计数为 $\mathrm{Sf}(\gamma)\in\mathbb{Z}$。在迹类假设下，$\mathrm{Sf}(\gamma)$ 与绕数 $\deg(\mathfrak s|_\gamma)$ 一致；在一般 Schatten 情形，仅其奇偶 $(-1)^{\mathrm{Sf}(\gamma)}$ 为不变量。

**定义 4.0+（单位圆的模 2 谱流）**

给定沿规避闭路 $\gamma_\varepsilon\subset X^\circ$ 的连续幺正族 $S(E,\lambda)$。若仅在有限多个参数点，有本征相位 $\theta_j$ **一阶横截**参考相位 $0$ 或 $\pi$（即穿越瞬间 $\partial_t\theta_j\neq0$），其余时刻谱在 $(0,\pi)$ 处保持**开隙**，则定义

$$
(-1)^{\mathrm{Sf}(\gamma)}:=(-1)^{\#\{\text{所有横截穿越 }0\text{ 或 }\pi\}}\in\{\pm1\},
$$

该定义与参考选择 $(0)/(\pi)$ 等价，并与 $\exp\bigl(-i\pi\oint_{\gamma_\varepsilon} d\xi_p\bigr)$ 及 $I_2(\gamma,D)$ 一致。

**引理 4.0+（可用域与一致性）**

在假设 A 与假设 D（横截‑余维一正则性）下，"横截局部模型（加强版）"保证上述横截穿越仅以有限个、且均为一阶横截方式出现；于是 $(-1)^{\mathrm{Sf}(\gamma)}$ 良定，并与

$$
\exp\Bigl(-i\pi\oint_{\gamma_\varepsilon} d\xi_p\Bigr),\quad
(-1)^{I_2(\gamma,D)}
$$

逐一一致（见定理 4.2 与定理 5.1）。

**引理 4.0bis（BK 连续化与模 $2$ 稳定性）**

在假设 A（A1–A4″）下，存在沿 $\gamma_\varepsilon\subset X^\circ$ 的连续化谱位移 $\xi_p$ 使 $\mathfrak s=e^{-2\pi i\xi_p}$，并且：

(i) 反向取向使 $\oint_{\gamma_\varepsilon} d\xi_p\mapsto-\oint_{\gamma_\varepsilon} d\xi_p$，从而 $(-1)^{\mathrm{Sf}(\gamma)}$ 不变；

(ii) 若 $\gamma$ 与 $D$ 有限个横截交，在每个交点按 §0.2a 的规则取小半圆规避得到的任意两条 $\gamma_{\varepsilon},\gamma_{\varepsilon'}$ 满足

$$
\exp\Bigl(-i\pi\oint_{\gamma_{\varepsilon}} d\xi_p\Bigr)
=\exp\Bigl(-i\pi\oint_{\gamma_{\varepsilon'}} d\xi_p\Bigr),
$$

因而 $\nu_{\sqrt S}(\gamma)$ 与 $I_2(\gamma,D)$ 对规避选择**不敏感**。

**定理 4.U（$\mathrm{Sf}$–绕数–谱位移的统一陈述）**

在**假设 A 的 (A1)–(A4″)** 下，存在连续化的谱位移 $\xi_p$ 使 $\mathfrak s=e^{-2\pi i\xi_p}$。沿规避闭路 $\gamma_\varepsilon\subset X^\circ$：

* **(i) 迹类整数版**（若 $S-\mathbf1\in\mathfrak S_1$ 且连续）：

  $$
  \mathrm{Sf}(\gamma)=\deg(\mathfrak s|_\gamma)=\frac{1}{2\pi i}\oint_{\gamma_\varepsilon}\mathfrak s^{-1}d\mathfrak s
  =-\oint_{\gamma_\varepsilon} d\xi\in\mathbb Z .
  $$

* **(ii) 一般 Schatten 的模 2 版**（$p\ge2$）：

  $$
  \exp\Bigl(-i\pi\oint_{\gamma_\varepsilon} d\xi_p\Bigr)
  =(-1)^{\mathrm{Sf}(\gamma)}.
  $$

  反向取向使积分变号，但**奇偶不变**；当 $\gamma$ 不可完全回避 $D$ 时，整数号符依赖规避方向，而**模2**结果与 §5 的 $I_2(\gamma,D)$ 保持一致。

**定理 4.1（Birman–Kreĭn，迹类）**

在绝对连续谱能段且 $S-\mathbf 1\in\mathfrak S_1$ 时，$\det S=e^{-2\pi i\xi}$，并沿任意闭路 $\gamma$（若与 $D$ 相交则取 $\gamma_\varepsilon$）有

$$
\mathrm{Sf}(\gamma)=\deg(\mathfrak s|_\gamma)=-\oint_{\gamma_\varepsilon} d\xi\in\mathbb Z .
$$

**定理 4.2（模 2 Levinson，一般 Schatten）**

在假设 A 与假设 D 下，

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(-i\pi\oint_{\gamma_\varepsilon} d\xi_p\Bigr)
=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{N_b(\gamma)}=(-1)^{I_2(\gamma,D)} .
$$

当 $\gamma$ 不可完全回避 $D$ 时，整数 $\mathrm{Sf}(\gamma)$ 的符号依赖规避方向，但上式之**模 2** 等式与交数 $I_2$ 对规避**不变**。

---

## 5 鉴别子与模 2 交数

令

$$
D=\{\text{Jost 上半平面零点生成或湮灭、阈值异常、嵌入本征值、通道开闭}\}\subset X.
$$

一般位置下 $D$ 为余维一的分片光滑子流形。

**约定（避障与规避独立性，模 2）**

若闭路 $\gamma\subset X$ 与 $D$ 有有限个横截交点，在每个交点处取半径 $\varepsilon>0$ 的小半圆规避，得 $\gamma_\varepsilon\subset X^\circ$。则

$$
\nu_{\sqrt S}(\gamma):=\nu_{\sqrt S}(\gamma_\varepsilon),\qquad
I_2(\gamma,D):=\langle w_D,[\gamma_\varepsilon]\rangle\in\mathbb{Z}_2
$$

在**$\mathbb Z_2$ 层级**与规避选择**无关**。具体地，任意两条由不同微小规避方式得到的 $\gamma_{\varepsilon},\gamma_{\varepsilon'}\subset X^\circ$ 满足

$$
\langle w_D,[\gamma_{\varepsilon}]\rangle=\langle w_D,[\gamma_{\varepsilon'}]\rangle\in\mathbb Z_2,
$$

且

$$
\exp\bigl(-i\pi\oint_{\gamma_{\varepsilon}} d\xi_p\bigr)=\exp\bigl(-i\pi\oint_{\gamma_{\varepsilon'}} d\xi_p\bigr).
$$

**命题 5.0ter（规避独立性，统一版）**

设 $D\subset X$ 满足一般位置假设，$\gamma\subset X$ 为闭路。任取两条按 §0.2a 规则得到的规避闭路 $\gamma_{\varepsilon},\gamma_{\varepsilon'}\subset X^\circ$，有

$$
\langle w_D,[\gamma_{\varepsilon}]\rangle=\langle w_D,[\gamma_{\varepsilon'}]\rangle\in\mathbb Z_2,\qquad
\exp\Bigl(-i\pi\oint_{\gamma_{\varepsilon}} d\xi_p\Bigr)
=\exp\Bigl(-i\pi\oint_{\gamma_{\varepsilon'}} d\xi_p\Bigr).
$$

因而 $\nu_{\sqrt S}(\gamma)$ 与 $I_2(\gamma,D)$ 在 $\mathbb Z_2$ 层级对规避选择**不敏感**；非横截场景下取任意小 $C^1$ 扰动至分层横截，结论依旧成立。

*证明素描*：任意两种规避仅在每个横截点附近相差一条小半圆，其并合为若干个以法向小环为边界的 2‑链；配对 $w_D$ 的结果在 $\mathbb Z_2$ 中相同。由引理 0.A，$\exp(-i\pi\oint d\xi_p)$ 对此替换亦不变。

**补充（非横截情形的稳定化）** 若 $D$ 含角点/自交/切触等非正则点，取任意小的 $C^1$ 扰动将 $(\gamma,D)$ 调至**分层横截**情形；由模 2 同伦不变性与 $w_D\in H^1(X^\circ;\mathbb Z_2)$ 的自然性，$I_2(\gamma,D)$ 与 $\exp(-i\pi\oint d\xi_p)$ 在 $\mathbb Z_2$ 层级保持不变。

**命题 5.0bis（Alexander 对偶与横截代表）**

令 $w_D\in H^1(X^\circ;\mathbb Z_2)$ 为由**余维一**分片光滑子流形 $D$ 诱导的链接类。则：

**(a)（二维特例）** 若 **$\dim X=2$** 且闭路 $\gamma\pitchfork D$，则

$$
I_2(\gamma,D)=\langle w_D,[\gamma_\varepsilon]\rangle=\#\bigl(\gamma\cap D\bigr)\ \bmod 2 .
$$

**(b)** 一般情形，取 $D$ 的紧致管状邻域 $N(D)$，并按 §0.2a 将 $\gamma$ 规避为 $\gamma_\varepsilon\subset X^\circ$。当 $\gamma_\varepsilon\pitchfork\partial N(D)$ 时，

$$
I_2(\gamma,D)=\big([\gamma_\varepsilon]\cdot[\partial N(D)]\big)\bmod2
=\#\big(\gamma_\varepsilon\cap\partial N(D)\big)\bmod2,
$$

其中"$\cdot$"为**同调交数（模 2）**。**仅当 $\dim X=2$ 且 $\gamma\pitchfork D$ 时，(b) 式退化为上面的二维特例 (a) 的 $\#(\gamma\cap D)\bmod2$。两式对小的 $C^1$ 变形与规避同伦稳定。

**横截局部模型假设（单通道化跨 $\pi$）**

对每个横截点 $x_\ast\in\gamma\cap D$，存在局部坐标 $t$ 与本征相位基，使某一通道的相位 $\theta(t)$ 满足 $\partial_t\theta(t_\ast)\neq0$ 且 $\theta$ 在 $t_\ast$ 邻域跨越 $\pi$（模 $2\pi$），其余通道相位连续。该非退化性等价于鉴别子在 $x_\ast$ 的横截性。

**定义（模 2 链接数，闭路通用版）**

在假设 D 下，令 $w_D\in H^1(X^\circ;\mathbb Z_2)$ 为由 $D$ 诱导的链接类。对任意闭路 $\gamma\subset X$，取其规避版本 $\gamma_\varepsilon\subset X^\circ$，定义

$$
I_2(\gamma,D):=\langle w_D,[\gamma_\varepsilon]\rangle\in\mathbb Z_2 .
$$

若取 $D$ 的紧致管状邻域 $N(D)$ 并使规避闭路 $\gamma_\varepsilon\pitchfork\partial N(D)$，则

$$
I_2(\gamma,D)=\big([\gamma_\varepsilon]\cdot[\partial N(D)]\big)\bmod2
=\#\big(\gamma_\varepsilon\cap\partial N(D)\big)\bmod2 .
$$

当 $\dim X=2$ 且 $\gamma\pitchfork D$ 时，该值亦等于 $\#(\gamma\cap D)\bmod2$。

**定理 5.1（交数判据，模 2）**

在假设 A 与横截局部模型假设下，

$$
\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)} .
$$

当 $\gamma_\varepsilon\pitchfork\partial N(D)$ 时，$I_2(\gamma,D)=\big([\gamma_\varepsilon]\cdot[\partial N(D)]\big)\bmod2$。每个交点触发一条本征相位跨 $\pi$，致 $\mathrm{Sf}$ 在该点跳变 $\pm1$；取奇偶即得上式。

---

## 6 可解模型：$\delta$-势与两类参数环路

**提醒（谱回路 vs 参回路）**

下文在 $k$‑平面用小回路 $C$ 记账 $\deg(S|_C)$ 仅用于解析结构（Jost 零点）之**整数**计数；它**不是**参数空间闭路 $\gamma$ 的绕数。二者只在 $\mathbb{Z}_2$ 层级（经 §4–§5 的桥接）可比；涉及 $N_b(\gamma)$ 时务必在参数空间内工作。

对 $V(x)=\lambda\delta(x)$（$\hbar=2m=1$），其全线散射矩阵为 $2\times 2$。偶宇称通道的标量化相位因子

$$
S(k)=\frac{2k-i\lambda}{2k+i\lambda},\qquad k>0,
$$

满足 $S=e^{2i\delta}$。取标准 Jost 规范（$f$ 在 $\operatorname{Im}k>0$ 的渐近归一化）

$$
f(k)=1+\frac{i\lambda}{2k},\qquad \frac{f(-k)}{f(k)}=\frac{2k-i\lambda}{2k+i\lambda}.
$$

当 $\lambda<0$ 时，$f$ 在上半平面零点 $k_\ast=-\tfrac{i\lambda}{2}=i|\lambda|/2$ 给出唯一束缚态，束缚能 $E_b=-\lambda^2/4$。奇宇称通道对 $\delta$-势透明，其相移为零，故完整 $2\times 2$ 散射矩阵的行列式等于该标量 $S$。

**复参数小环（仅演示整数绕数，不进入 $D$）** 取 $\lambda(\theta)=2ik+\rho e^{i\theta}$（$\rho>0$ 小），

$$
S(\lambda(\theta))=-1+\frac{4k}{i\rho}\,e^{-i\theta}.
$$

随 $\theta$ 递增，$\deg(S|_\gamma)=-1$。该例保持在 $X^\circ$ 内，**仅用于展示整数绕数**。

*取向诊断*：$S(\lambda(\theta))=-1+\frac{4k}{i\rho}e^{-i\theta}$ 的像为以 $-1$ 为圆心、半径 $R=\frac{4k}{\rho}$ 的大圆；当 $\theta$ 递增时 $e^{-i\theta}$ 顺时针旋转，故绕 $0$ 的绕数为 $-1$（半径足够大时 $0$ 被包围）。该取向与本文"数学正向＝逆时针"的约定一致。反向取向仅翻号，不改奇偶。

**实参数折返环（可检验构型，$\delta$‑势）**

在 $(E,\lambda)$‑平面取小矩形

$$
\gamma=\partial\big([E_0-\varepsilon,E_0+\varepsilon]\times[-\varepsilon,\varepsilon]\big),\qquad E_0,\varepsilon>0,
$$

选择 $E_0,\varepsilon$ 使 **$E_0-\varepsilon<0<E_0+\varepsilon$**。对 $\delta$‑势有

$$
D={\lambda=0}\cup{E=0,\ \lambda<0}.
$$

按 §5 规避规则在 ${\lambda=0}$ 处作小半圆推开。则 $\gamma$ 与 $D$ **横截三次**（在 $(E_0-\varepsilon,0)$、$(E_0+\varepsilon,0)$ 与 $(0,-\varepsilon)$），故

$$
I_2(\gamma,D)=3\bmod2=1,\qquad \nu_{\sqrt S}(\gamma)=-1.
$$

规避方向仅影响整数绕数号符，不改上述 $\mathbb Z_2$ 结论。

**规避与整数不变性** 折返闭路不可完全避开 $D$；将其以小半圆规避后得到的 $\deg(\mathfrak s|_\gamma)$ 的**号符**取决于规避方向，但其奇偶固定，且与 $\nu_{\sqrt S}$ 与 $I_2$ 一致。

**注（两类环路的角色与取向）**

复参数小环（如 $\lambda(\theta)=2ik+\rho e^{i\theta}$）**仅**用于展示**整数绕数**且保持在 $X^\circ$ 内，不进入 $D$；实参数折返环用于**可检验构型**的**$\mathbb{Z}_2$** 读数，其与 $D$ 的横截以 §5 的规避规则处理。规避方向仅影响整数号符，不改模 $2$ 结论；本文取向约定为"数学正向＝逆时针"。

**对照：复参数小环 vs 实折返路径**

复小环（不入 $D$）：$\lambda(\theta)=2ik+\rho e^{i\theta}\Rightarrow S(\theta)=-1+\frac{4k}{i\rho}e^{-i\theta}$，$\deg(S|_\gamma)=-1$，$\nu_{\sqrt S}=-1$。

实折返（横越 $D$ 奇数次的封闭路径）：

$$
(E(t),\lambda(t))=(E_c+r\cos t,\ r\sin t),\quad t\in[0,2\pi],\ \ 0<E_c<r\ll1 .
$$

此时 $D={\lambda=0}\cup{E=0,\lambda<0}$，横截发生在 $t=0,\pi$（$\lambda=0$）及 $t=\arccos(-E_c/r)$（$E=0,\ \lambda<0$），合计 3 次，故 $I_2(\gamma,D)=1$，$\nu_{\sqrt S}(\gamma)=-1$。

两者在**模 2** 层级一致，体现"谱回路整数计数 → 参回路交数"的降格。

---

## 7 非线性 Herglotz–Möbius 本征值问题

相位偏置的平面 Josephson 结中已观测到与拓扑相变一致的 **π 相位跃迁** 特征，且与本文"固定点交换→相位跨 π"的图景相符 [Phys. Rev. Lett. **126**, 036802 (2021)]。

**设定**

*符号提示*：本节 $L$ 为边界参数的实轴取值（自指闭环 $L=\Phi_{\tau,E}(L)$），与 §3 的 Riccati 变量 $L=\psi'/\psi$ 不相混。

自洽方程

$$
L=\Phi_{\tau,E}(L)=\mathcal B_\tau\big(M(E;L)\big),\qquad
\mathcal B_\tau(w)=\frac{a_\tau w+b_\tau}{c_\tau w+d_\tau}\in\mathrm{PSL}(2,\mathbb{R}),
$$

其中 $M(E;\cdot)$ 关于 $L$ 为 Herglotz–Möbius（即 Nevanlinna–Möbius）家族。典型点相互作用或 Schur 补模型给出

$$
\mathcal B_\tau(w)=\frac{a_\tau w+b_\tau}{c_\tau w+d_\tau},\qquad
\operatorname{Tr}=a+d,\ \ \det=ad-bc,\ \
\Delta=(d-a)^2+4bc=\operatorname{Tr}^2-4\det .
$$

**约定**：$(a,b,c,d)$ 专指 Möbius 系数；$\gamma$ **专指**参数闭路。

**假设 B（非线性 Herglotz–Möbius 闭环的一致正则性）**

(B1) $E\mapsto M(E;L)$ 为 Herglotz（Nevanlinna）家族，且对 $L$ 在实轴上保序；

(B2) $\Phi_{\tau,E}(L)=\dfrac{a_\tau L+b_\tau}{c_\tau L+d_\tau}$ 的参数 $(a_\tau,b_\tau,c_\tau,d_\tau)$ 在回路 $\gamma$ 的投影上 $C^1$ 连续；

(B3) 双曲区域 ${\Delta>0}$ 在 $\gamma$ 的像的邻域非空且连通，且 $\gamma$ 仅以横截方式穿越 ${\Delta=0}$。

**定理 7.0*（交换 ⇒ 跨 $\pi$ 的充分条件）**

在假设 B 下，设沿闭路参数化 $t\mapsto(\tau(t),E(t))$。令

$$
\Delta(t)=\operatorname{Tr}^2-4\det
$$

在 $t=t_\ast$ 横截零（$\partial_t\Delta(t_\ast)\neq0$），并记 $L_\pm(t)$ 为双曲区的两条边界不动点支。若 $M(E;L)$ 关于 $L$ 为 Herglotz 单调，且 $\Phi'(L_\pm(t_\ast))\neq1$，则

$$
\partial_L\arg\det S(E;L)\Big|_{L=L_\pm(t_\ast)}\ \text{同号且非零},
$$

从而存在同一连续相位支 $\theta_j(t)$ 使

$$
\theta_j\big(E(t),L_+(t)\big)-\theta_j\big(E(t),L_-(t)\big)
$$

在 $t=t_\ast$ **跨越 $\pi$（模 $2\pi$）**，并对 $\mathrm{Sf}$ 贡献 $\pm1$（奇偶固定），其奇偶与 $\nu_{\sqrt S}$ 同步。

**命题 7.0bis（跨 $\pi$ 的微分判据；显式版）**

在假设 B 下，设 $t\mapsto(\tau(t),E(t))$ 使 $\Delta(t)=\mathrm{Tr}^2-4\det$ 在 $t=t_\ast$ 为横截零，记双曲区两条边界不动点支为 $L_\pm(t)$。若 $M(E;L)$ 关于 $L$ 为 Herglotz 单调，且 $\Phi'(L_\pm(t_\ast))\neq1$，则存在相位连续支 $\theta_j$ 使

$$
\frac{d}{dt}\Big(\theta_j(E(t),L_+(t))-\theta_j(E(t),L_-(t))\Big)\Big|_{t=t_\ast}\neq 0.
$$

其证要为：Herglotz 单调性给出 $\partial_L\arg\det S(E;L)$ 的定号；横截性 $\partial_t\Delta(t_\ast)\neq0$ 与 $\Phi'(L_\pm(t_\ast))\neq1$ 排除切触，使相位差导数在 $t_\ast$ 不为零，故在 $t_\ast$**跨过 $\pi$（模 $2\pi$）**，并对 $\mathrm{Sf}$ 贡献 $\pm1$（奇偶固定）。

**引理 7.A（Herglotz 单调 ⇒ 相位单调）**

在边界三元组框架下，设 $E$ 位于绝对连续谱上，$L\in\mathbb R\cup\{\infty\}$，并令散射整体相位 $\Theta(E;L)$ 由 $\det S(E;L)=e^{2i\,\Theta(E;L)}$ 定义。若 $M(E;L)$ 关于 $L$ 为 Herglotz（Nevanlinna）单调且 $\Phi(L)=\dfrac{a L+b}{c L+d}\in\mathrm{PSL}(2,\mathbb R)$ 的闭环满足 §7 的正则性，则在保持 $E$ 的同时沿着 $L$ 的单调变动，有

$$
\partial_L \Theta(E;L)\ \text{在所述区间内保持定号（不变号）}.
$$

*证要*：由边界三元组的散射公式（$S$ 以 $M(E;L)$ 与边界参数构成的 Möbius 组合给出），$M(\,\cdot\,)$ 的 Nevanlinna 性保证 $\Im M(E+i0;L)>0$，进而 $\partial_L\arg\det S(E;L)$ 的符号由 $\partial_L M$ 的保序性与 $\Phi$ 的边界不动点指数共同确定；故 $\Theta$ 随 $L$ 单调。与 §7 的"横截局部模型"结合可得"交换 ⇒ 跨 $\pi$"。

**引理 7.0ter（$\partial_L\arg\det S$ 的定号封装）**

在"假设 B"与"边界三元组/Weyl 函数 $M(E;L)$ 为 Herglotz（Nevanlinna）并对 $L$ 保序"的条件下，$\partial_L\arg\det S(E;L)$ 在边界分支上一致取定号；故当 $\Delta$ 在 $t_\ast$ 处横截零且 $\Phi'(L_\pm(t_\ast))\neq1$ 时，$\bigl(\arg\det S(E;L_+(t))-\arg\det S(E;L_-(t))\bigr)$ 在 $t_\ast$ 必**跨越 $\pi$**（模 $2\pi$），从而对 $\mathrm{Sf}$ 贡献 $\pm1$（奇偶固定）。

定义（Möbius 系数与判别式）

$$
\operatorname{Tr}=a+d,\qquad \det=ad-bc,\qquad
\Delta=(d-a)^2+4bc=\operatorname{Tr}^2-4\det.
$$

**类型分类**
$\Delta>0$（双曲型）存在两边界不动点 $L_\pm$；$\Delta=0$（抛物型）两不动点并合，构成判别式零集；$\Delta<0$（椭圆型）仅有一内点不动点。

**导数与指数**
若 $L^*$ 为不动点，则

$$
\Phi'(L^*)=\frac{\det}{(c L^*+d)^2},\qquad \mathrm{ind}(L^*)=\operatorname{sgn}\big(1-\Phi'(L^*)\big).
$$

在边界不动点上以非切触假设定义；若 $\Phi'(L^*)=1$ 则属抛物退化。

**命题 7.1（固定点的边界连续追踪）**
在双曲区存在两条连续的边界不动点支 $L_\pm$，其稳定性由 $\mathrm{ind}(L_\pm)$ 决定。

**命题 7.2（横截判据）**
沿闭路若 $\Delta$ 横截零水平一次且横截性成立，则两支 $L_\pm$ 发生一次交换。

**命题 7.3（交换奇偶等于 $\nu_{\sqrt S}$）**

在假设 B 与"横截局部模型假设"下，若沿闭路 $\gamma$ 的投影 $\Delta$ 横截零水平的次数为奇数，则两条边界不动点支 $L_\pm$ 发生奇数次交换，且存在同一连续相位支使

$$
\bigl(\arg\det S(E;L_+(t))-\arg\det S(E;L_-(t))\bigr)
$$

在每个横截点跨越 $\pi$（模 $2\pi$）。因此

$$
(-1)^{\#\mathrm{exch}(\gamma)}=\nu_{\sqrt S}(\gamma).
$$

*证要*：由 $M(E;L)$ 的 Herglotz 单调性与 $\partial_t\Delta\neq 0$ 的横截性，局部可单通道化并得到"跨 $\pi$"；奇偶相乘即得结论（附录 F）。

---

## 8 同伦配对：交换、$2\pi$ 旋转与散射相位（两体，$d\ge 3$）

本节严格涵盖两体、$d\ge3$ 的情形。

**命题 8.1（配置空间基本群）** 令 $B_N(\mathbb{R}^d)=C_N(\mathbb{R}^d)/S_N$ 为无序配置空间，则 $d\ge3$ 时 $\pi_1\big(B_N(\mathbb{R}^d)\big)\cong S_N$。

**命题 8.2（交换到旋转）** 两粒子交换 $\sigma_{ij}\in S_N$ 对应于相对坐标的环路 $[R_{ij}]\in \pi_1(\mathrm{SO}(d))\cong\mathbb{Z}_2$，由 $2\pi$ 旋转代表非平凡类。

下述 $\Psi:\pi_1(\mathrm{SO}(d))\to [X^\circ,U(1)]$ 的构造限制在短程中心势的两体散射对上；其边界同伦由无穷远球面上的旋转扭转诱导，并与单通道散射相移的半相位选择相容（见附录 G）。

**构造 8.3（散射配对公式）** 由无穷远边界扭转得映射 $\Psi:\pi_1(\mathrm{SO}(d))\to [X^\circ,U(1)]$。令 $\mathfrak s_R:=\Psi([R])$。记 $\alpha=\frac{1}{2i}\,\mathfrak s_R^{-1}d\mathfrak s_R$，则对闭路 $\gamma\subset X$（若 $\gamma\cap D\neq\varnothing$，按 §5 取避障闭路 $\gamma_\varepsilon\subset X^\circ$）

$$
\Psi([R])(\gamma)=\exp\Big(i\oint_\gamma \alpha\Big),\qquad
\nu_{\sqrt{\mathfrak s_R}}(\gamma)=\exp\Big(i\oint_\gamma \tfrac{1}{2i}\,\mathfrak s_R^{-1}d\mathfrak s_R\Big).
$$

特别地，对 $[R]$ 的非平凡类（$2\pi$ 旋转），有 $\nu_{\sqrt{\mathfrak s_R}}(\gamma)=-1$。

两体中心势下，交换路径在配置空间中同伦于相对坐标的 $\pi$ 旋转；其在旋转群 $\mathrm{SO}(d)$ 上的提升对应由 $2\pi$ 旋转代表的非平凡同伦类。由上述构造并配对闭路，得到

$$
\nu_{\mathrm{conf}}(\text{交换一次})=\nu_{\mathrm{spin}}(2\pi\text{ 旋转})=\nu_{\sqrt S}(\gamma).
$$

本节严格涵盖两体情形。$N>2$ 的推广涉及辫群表示与散射通道选择，不在本文范围。

---

## 9 拓扑超导端点散射：Class D 与 Class DIII

**模型前提**：工作在零能反射矩阵 $r(0)$；Class D 具 PHS 而无 TRS，$r(0)$ 可选实；Class DIII 具 PHS 与 $T^2=-1$ 的 TRS，使 $r(0)$ 在合适基下为反对称。于是 $\operatorname{sgn}\det r(0)$（D）与 $\operatorname{sgn}\operatorname{Pf}r(0)$（DIII）分别等价于 $\sqrt{\det r(0)}$ 的分支号符。

在费米能处，端点反射矩阵 $r(E)$ 的符号指标 $Q_{\mathrm D}$ 与 $Q_{\mathrm{DIII}}$ 分别对应 Class D 与 Class DIII 的拓扑不变量。

**零能正则化约定**

若 $r(0)$ 不可直接取值，则一律以 $E\downarrow 0$ 的**右极限**定义

$$
Q_{\mathrm D}:=\operatorname{sgn}\Big(\lim_{E\downarrow0}\det r(E)\Big),\qquad
Q_{\mathrm{DIII}}:=\operatorname{sgn}\Big(\lim_{E\downarrow0}\operatorname{Pf}r(E)\Big).
$$

该取向选择在整数层级可能改变号符，但在 $\mathbb{Z}_2$ 层级不影响判据，与 §5 的规避独立性一致。

**警示（规范方向）**：DIII 类中，必须限制端口规范为 $O\in\mathrm{SO}(N)$。若允许 $O\in O(N)\setminus\mathrm{SO}(N)$，则 $\operatorname{Pf}(OrO^\top)=\det(O)\operatorname{Pf}(r)$ 致号符翻转；本文指标在 $\mathrm{SO}(N)$ 规范下不变。

**Class D（仅 PHS）**
费米能处 $r(0)\in O(N)$，定义

$$
Q_{\mathrm D}=\operatorname{sgn}\det r(0)\in\{\pm1\}.
$$

端口正交规范 $r\mapsto OrO^\top$（$O\in O(N)$）保持 $\det r$ 与谱对称。该 $\mathbb{Z}_2$ 指标等价于 $\sqrt{\det r(0)}$ 的分支号符。

**Class DIII（PHS 与 TRS，$T^2=-1$）**
可择 Majorana 基使 $r(0)$ 为实反对称矩阵，通道数 $N$ 必为偶数，且

$$
\det r(0)=(\operatorname{Pf}r(0))^2,\qquad Q_{\mathrm{DIII}}=\operatorname{sgn}\operatorname{Pf}r(0).
$$

对 $O\in\mathrm{SO}(N)$，有 $\operatorname{Pf}(OrO^\top)=\operatorname{Pf}(r)$，故 $Q_{\mathrm{DIII}}$ 规范不变，并与 $\sqrt{\det r(0)}$ 的分支号符等价。

**注（规范方向）** DIII 类中 $\operatorname{Pf}r(0)$ 的号符在 $\mathrm{SO}(N)$ 端口规范下不变；若允许 $O\in O(N)\setminus\mathrm{SO}(N)$，则 $\operatorname{Pf}(OrO^\top)=\det(O)\operatorname{Pf}(r)$，号符随 $\det(O)$ 翻转，故规范必须限制为 $\mathrm{SO}(N)$。

上述实反对称范式系在 Kramers 基与 $\mathrm{SO}(N)$ 端口规范化下取得；能隙闭合事件属于 §0.2 定义的鉴别子 $D$，其每一次横截触发 $\operatorname{Pf}r(0)$ 的号符翻转，等价于 **$P_{\sqrt{\det r(0)}}$ 沿 $\gamma$ 的 holonomy 为 $-1$**（亦即 $(-1)^{\deg(\det r(0)|_\gamma)}=-1$）。

**引理（低能范式与号符翻转）**

*Class D*：在 Majorana 基下 $r(0)\in O(N)$。单一穿越事件存在角度本征相位 $\theta_j(E,\lambda)$ 在 $E=0$ 邻域跨越 $\pi$（模 $2\pi$），其余相位连续；故 $\det r(0^+)=(-1)\det r(0^-)$，即 $\operatorname{sgn}\det r(0)$ 翻转。

*Class DIII*：在 Kramers 配对与实反对称范式下，存在 $2\times2$ 反对称块号符穿越，$\operatorname{Pf}r(0)$ 号符改变而 $\det r(0)=(\operatorname{Pf}r(0))^2$ 仅变平方。

*结论*：两类中号符翻转 $\Longleftrightarrow$ 有一相位跨 $\pi$（模 $2\pi$），与 §5 的 $I_2$ 记账同步，等价于 **$P_{\sqrt{\det r(0)}}$ 沿 $\gamma$ 的 holonomy 为 $-1$**（亦即 $(-1)^{\deg(\det r(0)|_\gamma)}=-1$）。

---

## 10 多通道与分波：最小自洽陈述

若 $S(E,\lambda)-\mathbf 1$ 为迹类且 $(E,\lambda)\mapsto S$ 连续，则存在连续相位 $\mathfrak s=\det S=e^{-2\pi i\,\xi}$，且

$$
\nu_{\sqrt S}(\gamma)=\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s\Bigr)
=(-1)^{\mathrm{Sf}(\gamma)}=(-1)^{I_2(\gamma,D)}.
$$

球对称势下 $\mathfrak s=\det S=\prod_\ell \det S_\ell$，各分波的奇偶在模 2 下相乘；通道开闭事件纳入 $D$ 并由 $I_2(\gamma,D)$ 稳定记录。

---

## 11 二维任意子与 $\mathbb{Z}_2$ 投影

**一致化承诺（AB‑型二维散射）**

本文**固定采用**修正 Fredholm 行列式 $\det_2 S=e^{-2\pi i\xi_2}$，并沿闭路取同一连续化支 $\xi_2$。分波表示下，围绕半整数 $m=-\tfrac12$ 的**对称截断**

$$
\det_M S:=\prod_{-M-1\le m\le M}\det S_m
$$

满足 $m\leftrightarrow -m-1$ 配对抵消之**模 $2$** 稳定性：$\det S_{-m-1}=\overline{\det S_m}\Rightarrow \deg(\det S_m|_\gamma)+\deg(\det S_{-m-1}|_\gamma)\equiv0\pmod2$，故 $\nu_M(\gamma):=(-1)^{\deg(\det_M S|_\gamma)}$ 随 $M$ 稳定到 $\nu_{\sqrt S}(\gamma)$ 的 $\mathbb{Z}_2$ 读数。穿越 $\alpha=\tfrac12$（$\theta=\pi$）时，$\deg(\mathfrak s|_\gamma)\equiv1\pmod2$，故 $\nu_{\sqrt S}(\gamma)=-1$。本文不主张对**一切**正则化方案之普遍独立性，所用结果限于上述承诺与对称截断。

Aharonov–Bohm 散射以通量 $\alpha=\Phi/\Phi_0$ 给出统计角 $\theta=2\pi\alpha$。固定能量，沿闭路 $\alpha\mapsto \alpha+1$ 并穿越 $\alpha=\tfrac12$（$\theta=\pi$）时，由分波相位的跳变可知

$$
\deg(\mathfrak s|_\gamma)\equiv 1\pmod{2},\qquad \nu_{\sqrt S}(\gamma)=-1.
$$

一般 $\theta\neq 0,\pi$ 超出本文的 $\mathbb{Z}_2$ 框架，本文只捕获其模 2 投影。

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

**注 11.0bis（$\xi_2$ 的连续化与对称截断的一致化）**

沿闭路统一选择 $\xi_2$ 的连续化分支，使 $\exp(-2\pi i\,\xi_2)$ 与围绕 $m=-\tfrac12$ 的对称分波有限乘积在**模 2** 层级配对一致；该工艺化选择不影响 $\nu_{\sqrt S}$ 的读数。

**命题 11.3（模 2 稳定性，配对‑同支‑极限）**

在 AB‑型散射中，取围绕半整数 $m=-\tfrac12$ 的对称截断

$$
\det_M S:=\prod_{-M-1\le m\le M}\det S_m,\qquad \nu_M(\gamma):=(-1)^{\deg(\det_M S|_\gamma)}.
$$

则 $\nu_{M+1}(\gamma)\equiv \nu_M(\gamma)\pmod2$。

*证*：

(1)（配对）由 $m\leftrightarrow -m-1$ 的对称性，$\det S_{-m-1}=\overline{\det S_m}$，故

$$
\deg(\det S_m|_\gamma)+\deg(\det S_{-m-1}|_\gamma)\equiv 0\pmod2.
$$

(2)（同支）$\xi_2$ 的连续化支沿同一规避闭路统一选定，使 $\exp(-2\pi i\xi_2)$ 与对称截断的有限乘积在**模2层级**一致；

(3)（极限）随 $M\mapsto M+1$ 仅新增一对 $(m,-m-1)$，其模2绕数相消，故 $\nu_M$ 稳定到 $\nu_{\sqrt S}(\gamma)$。

本文仅在模 2 层级主张 $\nu_{\sqrt S}$ 与 $\det_2$（或对称分波截断 $\det_M$ 的极限）的一致读数；所有正则化依赖性在奇偶投影下抵消（命题 11.3），但不声明更强的正则化独立性。

---

## 12 结论与展望

以 $\alpha=\tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s$ 的 holonomy 为核心，构建了"平方根—双覆盖—$\mathbb{Z}_2$ 指标"的统一框架，将交换统计、旋量双覆盖与散射谱结构整合为同一可计算不变量 $\nu_{\sqrt S}$。该不变量可由主 $\mathbb{Z}_2$-丛 holonomy、Birman–Kreĭn 与谱流、鉴别子模 2 交数及自指闭环的双曲型分支交换四条链路读取，并在拓扑超导端点散射中与 $\operatorname{sgn}\det r$、$\operatorname{sgn}\operatorname{Pf}r$ 等价。多体系统、二维非阿贝尔任意子、阈值强耦合与非厄米散射的平方根拓扑构成自然的延展方向。

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
13. M. C. Dartiailh, W. Mayer, J. Yuan, K. S. Wickramasinghe, A. Matos‑Abiague, I. Žutić, J. Shabani, **Phase Signature of Topological Transition in Josephson Junctions**, *Phys. Rev. Lett.* **126** (2021) 036802.
14. T. Kanne **et al.**, **Epitaxial Pb on InAs Nanowires for Quantum Devices**, *Nat. Nanotechnol.* **16** (2021) 776–781.
15. **Retraction Note:** *Quantized Majorana conductance*, *Nature* **591** (2021) E30；H. Zhang **et al.**, *Quantized Majorana conductance*, *Nature* **556** (2018) 74–79 (**Retracted**).
16. M. T. Deng et al., Majorana Bound State in a Coupled Quantum-Dot Hybrid-Nanowire System, Science 354 (2016) 1557–1562.
17. V. Mourik et al., Signatures of Majorana Fermions in Hybrid Superconductor-Semiconductor Nanowire Devices, Science 336 (2012) 1003–1007.
18. S. M. Albrecht et al., Exponential Protection of Zero Modes in Majorana Islands, Nature 531 (2016) 206–209.
19. R. Yu, W. Zhang, H.-J. Zhang, S.-C. Zhang, X. Dai, Z. Fang, **Quantized Anomalous Hall Effect in Magnetic Topological Insulators**, *Science* **329** (2010) 61–64.
20. T. Friedrich, Dirac Operators in Riemannian Geometry, AMS, 2000.
21. J. M. Lee, Introduction to Topological Manifolds, 2nd ed., Springer, 2011.
22. M. Nakahara, Geometry, Topology and Physics, 2nd ed., CRC Press, 2003.

---

## 附录 A  覆盖—提升与平直线丛（证明）

### A.1 覆盖—提升与 holonomy

$U(1)=K(\mathbb{Z},1)$，故 $[X^\circ,U(1)]\cong H^1(X^\circ;\mathbb{Z})$。平方覆盖 $p:z\mapsto z^2$ 在 $\pi_1$ 与 $H^1$ 上对应乘二。存在 $s:X^\circ\to U(1)$ 使 $s^2=\mathfrak s$ 当且仅当 $[\mathfrak s]\in 2H^1(X^\circ;\mathbb{Z})$。对应主 $\mathbb{Z}_2$-丛为 $P_{\sqrt{\mathfrak s}}=\mathfrak s^*(p)$。对闭路 $\gamma$

$$
\exp\Bigl(i\oint_\gamma \tfrac{1}{2i}\,\mathfrak s^{-1}d\mathfrak s\Bigr)=e^{i\pi\,\deg(\mathfrak s|_\gamma)}=(-1)^{\deg(\mathfrak s|_\gamma)}.
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

得到平直线丛的第一陈类，其像等于 $H^2$ 的挠子群；因此平直线丛必满足 $c_1$ 为挠元（对由 $\{\pm1\}\hookrightarrow U(1)$ 关联得到的平直线丛更是 2‑挠）。这与正文 §2.2 对 $\mathcal L_{\sqrt{\mathfrak s}}$ 的描述相一致。

线丛平方根存在当且仅当 $c_1(\mathcal L)\in 2H^2(X^\circ;\mathbb{Z})$。这与 A.1 的**映射层**提升问题（$[\mathfrak s]\in 2H^1(X^\circ;\mathbb{Z})$）针对不同对象，一般不相互推出。本文的 $\nu_{\sqrt S}$ 与映射层平方根障碍等价，其由主 $\mathbb{Z}_2$-丛 $P_{\sqrt{\mathfrak s}}=\mathfrak s^*(p)$ 的 holonomy 给出。

**注意**：$c_1(\mathcal L)$ 的 $\bmod 2$ 约化属于 $H^2(X^\circ;\mathbb{Z}_2)$，而 A.1 的覆盖障碍 $w_1(P_{\sqrt{\mathfrak s}})\in H^1(X^\circ;\mathbb{Z}_2)$，两者不处于同一上同调次数，不能直接等同。仅当专指由 $P_{\sqrt{\mathfrak s}}$ 经 $\{\pm1\}\hookrightarrow U(1)$ 关联得到的平直复线丛 $\mathcal L_{\sqrt{\mathfrak s}}$ 时，其 $c_1$ 的 2‑挠可在挠/模 2 层面反映 $\nu_{\sqrt S}$ 的 holonomy 数据（见 §2.2），但并不与 $w_1(P_{\sqrt{\mathfrak s}})$ 作同度量的等价。*本稿不把二者等同*。

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

**注（谱回路 vs 参回路）** 上式取的是 $k$-平面的小正向回路 $C$，只围住上半平面零点 $\{k_j\}$。其给出 $\deg(S|_C)=-\sum_j m_j$ 的**谱参数**整数计数，用于分析 $S=f(-k)/f(k)$ 的解析结构。它**不是**外参数空间中的闭路 $\gamma$，因此不定义 $N_b(\gamma)$。$C$ 是 $k$-平面中的回路，$\gamma$ 是 $(E,\lambda)$-空间中的回路，二者维度与意义不同，仅在 $\mathbb{Z}_2$ 层级上可比。当需比较 $N_b$ 时，应先在参数空间内选取避开 $D$ 的闭路 $\gamma$ 并应用 §4 的 $\mathrm{Sf}=\deg$ 与 §5 的 $\mathbb{Z}_2$ 等价，只保留奇偶信息。

---

## 附录 C  Birman–Kreĭn 与谱流

在短程与迹类假设下，存在连续谱位移 $\xi$ 使 $\mathfrak s=\det S=e^{-2\pi i\,\xi}$。本征相位关于参数的横截与避障给出

$$
\mathrm{Sf}(\gamma)=\deg(\mathfrak s|_\gamma)=-\oint_\gamma d\xi\in\mathbb{Z},\qquad
\nu_{\sqrt S}(\gamma)=\exp\Bigl(-i\pi\oint_\gamma d\xi\Bigr)=(-1)^{\mathrm{Sf}(\gamma)}.
$$

当闭路同时改变能量与外参时，$\xi$ 取修正 Fredholm 行列式的连续化分支。反向取向仅改变积分号符，奇偶不变。参照点取 $\theta=0$ 或 $\theta=\pi$ 均给出相同的模 2 结果。

---

## 附录 D  交数与鉴别子

鉴别子 $D\subset X$ 为余维一的分片光滑子流形（或其并）。设 $N(D)$ 为 $D$ 的紧致管状邻域。对任意闭路 $\gamma$ 的规避版本 $\gamma_\varepsilon\subset X^\circ$，当 $\gamma_\varepsilon\pitchfork\partial N(D)$ 时，

$$
\nu_{\sqrt S}(\gamma)=(-1)^{I_2(\gamma,D)},\qquad
I_2(\gamma,D)=\big([\gamma_\varepsilon]\cdot[\partial N(D)]\big)\bmod2
=\#\big(\gamma_\varepsilon\cap\partial N(D)\big)\bmod2 .
$$

若 $\dim X=2$ 且 $\gamma\pitchfork D$，则 $I_2(\gamma,D)=\#(\gamma\cap D)\bmod2$。每个交点对应一次束缚态奇偶改变，故上式与 §5 的 $I_2(\gamma,D)=\langle w_D,[\gamma_\varepsilon]\rangle$ 一致。

---

## 附录 E  $\delta$-势的两类参数环路

$$
S(k)=\frac{2k-i\lambda}{2k+i\lambda},\qquad f(k)=1+\frac{i\lambda}{2k}.
$$

**复参数小环（仅演示整数绕数，不进入 $D$）** 取 $\lambda(\theta)=2ik+\rho e^{i\theta}$（$\rho>0$ 小），

$$
S(\lambda(\theta))=-1+\frac{4k}{i\rho}e^{-i\theta},
$$

随 $\theta$ 递增，$\deg(S|_\gamma)=-1$。该例保持在 $X^\circ$ 内，**仅用于展示整数绕数**。

**实参数折返环（$\delta$‑势）**

取 $E_0,\varepsilon>0$ 满足 **$E_0-\varepsilon<0<E_0+\varepsilon$**，并按 §5 以半径 $o(\varepsilon)$ 的小半圆规避 ${\lambda=0}$。对 $\delta$‑势，

$$
D={\lambda=0}\cup{E=0,\ \lambda<0}.
$$

此时 $\gamma$ 与 $D$ 的横截发生在 $(E_0-\varepsilon,0)$、$(E_0+\varepsilon,0)$ 与 $(0,-\varepsilon)$，合计 **3** 次，故 $I_2(\gamma,D)=1\Rightarrow \nu_{\sqrt S}(\gamma)=-1$；整数绕数号符依赖规避方向，但**模 2** 结果不变。

**规避与整数不变性** 折返闭路不可完全避开 $D$；将其以小半圆规避后得到的 $\deg(\mathfrak s|_\gamma)$ 的**号符**取决于规避方向，但其奇偶固定，且与 $\nu_{\sqrt S}$ 与 $I_2$ 一致。

---

## 附录 F  自指散射的 Möbius 类型与交换

$$
\Phi(L)=\frac{a L+b}{c L+d},\qquad a,b,c,d\in\mathbb{R},\ \ ad-bc>0.
$$

令

$$
\operatorname{Tr}=a+d,\qquad \det=ad-bc,\qquad \Delta=\operatorname{Tr}^2-4\det.
$$

**命题 F.1（固定点的边界连续追踪）**
$\Delta>0$ 时存在两条连续的边界不动点支 $L_\pm$，其指数 $\mathrm{ind}(L^*)=\operatorname{sgn}\big(1-\frac{\det}{(c L^*+d)^2}\big)$。

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
