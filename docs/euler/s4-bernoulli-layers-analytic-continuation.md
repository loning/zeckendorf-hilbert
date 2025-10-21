# S4. 伯努利层与解析延拓范式

**—— 有限阶 Euler–Maclaurin、余项整函数性与"极点 = 主尺度"原则**

## 摘要（定性）

建立"有限阶 Euler–Maclaurin（EM）—伯努利层—解析延拓"的统一范式：在一维尺度切片上，对依赖复参 $s$ 的函数族 $f(\cdot;s)$ 作**有限阶** EM 分解；给出使余项关于 $s$ **全纯/整函数**的可检条件；据此证明**极点仅来自主尺度项**（端点/主项积分与其有限阶导数），而 EM 校正的**伯努利层**仅贡献整函数修正，从而实现"极点 = 主尺度"。该范式与 S2 的"加法镜像—零集横截"在局部几何上相容，与 S3 的"自反核—完成函数—$\Gamma/\pi$ 正规化"在乘法镜像上拼接，并为 S5 的"沿方向亚纯化与极点定位"提供可检接口。

---

## 0. 记号与前置（与 S1/S2/S3 对齐）

* **尺度切片**：固定方向 $\mathbf v\in\mathbb S^{n-1}$ 与横向偏置 $\rho_\perp$，令

$$
f(x;s)\;:=\;F\bigl(\theta,\rho_\perp+x\,\mathbf v; s\bigr),\qquad x\in\mathbb R_{\ge0},
$$

其中 $\theta$ 固定（相位层），$s$ 为（Mellin/拉普拉斯）复参。所有换序、逐项微分与收敛均在 S1 的管域/条带契约下进行（C0–C3）。
* **离散—连续桥（步长与比率）**：尺度网格记为 $x_k:=a+k\Delta$（$k\in\mathbb N$），并记 $b:=e^{\Delta}$（乘法变量）；本文**仅使用有限阶** EM，不引入无穷伯努利级数。
* **S2/S3 接口**：S2 的"幅度平衡 + 相位对径"提供零集的余维 2 横截几何（用于主导项/二项闭合的局部化）；S3 给出 $\Gamma/\pi$ 正规化与完成函数模板（用于消除主尺度诱发的极点并获得镜像对称）。

---

## 1. 有限阶 Euler–Maclaurin 与"伯努利层"

### 定义 4.1（有限阶 EM / 伯努利层）

令 $M\in\mathbb N$、$N\in\mathbb N$，并假设 $f\in C^{2M}\bigl([a,a+N\Delta]\bigr)$。则有限阶 EM 公式为

$$
\sum_{k=0}^{N-1} f(a+k\Delta)
= \frac{1}{\Delta}\int_{a}^{a+N\Delta} f(x)\,dx
+ \frac{f(a)-f(a+N\Delta)}{2}
+ \sum_{m=1}^{M-1}\frac{B_{2m}}{(2m)!}\,\Delta^{2m-1}\bigl(f^{(2m-1)}(a+N\Delta)-f^{(2m-1)}(a)\bigr)
+ R_M,
$$

其中

$$
R_M=\frac{\Delta^{2M-1}}{(2M)!}\int_{a}^{a+N\Delta} B_{2M}\left(\Bigl\{\tfrac{x-a}{\Delta}\Bigr\}\right)\, f^{(2M)}(x)\,dx.
$$

记

$$
\mathcal B_m[f]\;:=\;\frac{B_{2m}}{(2m)!}\,\Delta^{2m-1}\bigl(f^{(2m-1)}(a+N\Delta)-f^{(2m-1)}(a)\bigr),\qquad 1\le m\le M-1,
$$

为**第 $m$ 层伯努利层**，$R_M$ 为**余项层**。其中 $B_{2m}$ 为伯努利数，$B_{2M}(\cdot)$ 为伯努利多项式，$\{\cdot\}$ 表示小数部分。

> 约定：本文始终取**有限 $M$**；$\mathcal B_m$ 与 $R_M$ 对复参 $s$ 的依赖满足后述可检条件，因而在 $s$ 上全纯/整函数。

---

## 2. 余项整函数性与条带全纯

令 $f(\cdot;s)$ 在 $x$-方向 $C^{2M}$，在复参 $s$ 上取值于连续可微函数空间。设存在开集 $U\subset\mathbb C$ 使：

* **(H1)** 对任意紧集 $K\subset U$，存在可积权 $w_M(x)\ge 0$ 使

$$
\sup_{s\in K}\bigl|f^{(k)}(x;s)\bigr|\le w_M(x),\qquad x\in[a,\infty),\ 0\le k\le 2M.
$$

* **(H2)** $\displaystyle \int_{a}^{\infty} w_M(x)\,dx<\infty$（或相应的半无限区间与端点分离变体），且端点满足有限阶消失/有界，以确保边界项存在。

* **(H0)**（点态全纯）对每个 $x\in[a,\infty)$ 与 $0\le k\le 2M$，映射 $s\mapsto f^{(k)}(x;s)$ 在 $U$ 内全纯；并与 (H1) 的主导界 $w_M\in L^1$ 共同成立（对紧集一致）。

### 定理 T4.1（余项与伯努利层的全纯/整函数性）

在 (H0)–(H2) 下，$R_M(a,N,\Delta;s)$ 关于 $s\in U$**全纯**；若 (H0)–(H2) 在 $U=\mathbb C$ 成立，则 $R_M$ 为 $s$ 的**整函数**。同理，每一层伯努利层 $\mathcal B_m[f(\cdot;s)]$ 在 $s\in U$ 全纯。

**证明（略要）**。由定义，

$$
R_M(s)=\frac{\Delta^{2M-1}}{(2M)!}\int_{a}^{a+N\Delta} B_{2M}\left(\Bigl\{\tfrac{x-a}{\Delta}\Bigr\}\right)\, f^{(2M)}(x;s)\,dx.
$$

固定 $K\subset U$ 紧集，$B_{2M}$ 有界且 $\sup_{s\in K}|f^{(2M)}(x;s)|\le w_M(x)\in L^1$。由受控/主导收敛与 Morera 定理（或 Weierstrass 一致收敛判别）可交换"积分—极限/微分"，得 $R_M$ 在 $U$ 内全纯；若 (H0)–(H2) 在 $\mathbb C$ 成立，则 $R_M$ 为整函数。伯努利层的全纯性同理（端点值与有限阶导数在 (H0)–(H2) 下对 $s$ 全纯）。$\square$

---

## 3. "极点 = 主尺度"原则

考虑半无限和的截断

$$
S_N(\Delta;s):=\sum_{k=0}^{N-1} f(a+k\Delta;s),\qquad N\to\infty,
$$

及其**主尺度项**

$$
\mathcal I(\Delta;s):=\frac{1}{\Delta}\int_a^{\infty} f(x;s)\,dx,
$$

与有限阶伯努利校正 $\sum_{m=1}^{M-1}\mathcal B_m[f(\cdot;s)]$ 及极限余项 $R_M(s)$（在 $N\to\infty$ 的意义下定义良好）。在众多母映射/拉普拉斯—Mellin 场景中（如 $f(x;s)=e^{-\sigma x}g(x;s)$ 且 $\sigma>0$），$\mathcal I(\Delta;s)$ 是 $s$ 的解析（亚纯）函数，而 $\mathcal B_m$ 与 $R_M$ 在 $s$ 上全纯/整函数。

* **(H3')**（无穷端点衰减，含 $k=0$）对任意紧集 $K\subset U$，有
$$
\sup_{s\in K}\big|f^{(k)}(a+N\Delta;s)\big|\xrightarrow[N\to\infty]{}0,\quad k\in\{0,1,3,\dots,2M-1\}.
$$
从而 $\sum_{m=1}^{M-1}\mathcal B_m[f(\cdot;s)]$ 的上端点导数项在 $N\to\infty$ 衰减消失，可定义**极限伯努利层** $\mathcal B_m^{(\infty)}[f(\cdot;s)]$（仅依赖于 $x=a$ 处的有限阶导数），并且**余项层极限** $R_M^{(\infty)}(s)$ 存在且对 $s\in U$ 局部一致。充分可选条件：存在 $\eta>0$ 使 $\sup_{s\in K} e^{\eta x}\,\big|f^{(k)}(x;s)\big|$ 在 $0\le k\le 2M-1$ 有界，则 (H3') 自动成立。

### 定理 T4.2（极点仅出自主尺度项）

设 $f(\cdot;s)$ 满足 T4.1 的 (H0)–(H2)，并取竖条 $V\subset U$

$$
V=\{\sigma_0<\Re s<\sigma_1\}.
$$

存在：

* **(A0)**（通常极限的存在）存在非空**收敛竖条** $W\subset V$，使得在 (H0)–(H3') 下，$\sum_{m=1}^{M-1}\mathcal B_m[f(\cdot;\cdot)]$ 与 $R_M$ 的 $N\to\infty$ 极限在 $W$ 内一致存在，且上端点各阶（含 $k=0$）满足 (H3') 的衰减；据此定义
  $\mathcal B_m^{(\infty)}[f(\cdot;s)]$、$R_M^{(\infty)}(s)$，并保留端点平均项 $\tfrac12 f(a;s)$；
* **(A1)** $\mathcal I(\Delta;s)$ 在 $V$ 内可解析延拓为**亚纯函数**，其极点集合 $\mathcal P\subset V$ 可数且无聚点；
* **(A2)** 每层伯努利层与余项在 $s\in V$ 上全纯（由 T4.1 保证）。

则：

* **（通常极限）** 在 $W$ 内，
$$
\lim_{N\to\infty}S_N(\Delta;s)
=\mathcal I(\Delta;s)
+\tfrac12 f(a;s)
+\sum_{m=1}^{M-1}\mathcal B_m^{(\infty)}[f(\cdot;s)]
+R_M^{(\infty)}(s).
$$

* **（解析延拓）** 在 $V$ 内，以右端定义
$$
S(\Delta;s):=\mathcal I(\Delta;s)+\tfrac12 f(a;s)+\sum_{m=1}^{M-1}\mathcal B_m^{(\infty)}[f(\cdot;s)]+R_M^{(\infty)}(s),
$$
从而 $S(\Delta;\cdot)$ 为 $V$ 内的亚纯延拓，且
$$
\mathrm{Sing}_V\bigl(S(\Delta;\cdot)\bigr)=\mathrm{Sing}_V\bigl(\mathcal I(\Delta;\cdot)\bigr)=\mathcal P.
$$

即在解析延拓的意义下，**极点仅由主尺度项 $\mathcal I$ 产生**；伯努利层与余项不引入新极点。

**注（与 S3 的完成函数拼接）**：若 $\mathcal I$ 的端点主项可归约为 Gamma/指数—多项式型，可按 S3 提供的模板选择对称因子 $r(s)$（$\Gamma/\pi$ 因子）使 $r(s)\mathcal I(\Delta;s)$ 消极点；结合 (A2) 即得在 $V$ 内**全纯（无极点）的完成函数**。

---

## 4. 方向化与指数—多项式情形（S5 接口）

固定尺度方向 $\mathbf v$，考虑离散计数与其拉普拉斯—Stieltjes变换：

$$
M_{\mathbf v}(t;s):=\sum_{k\ge 0} f(\rho_\perp+k\Delta\,\mathbf v;s)\,\mathbf 1_{[0,\infty)}(t-k\Delta),\qquad
\mathcal L_{\mathbf v}(s):=\int_{0}^{\infty} e^{-st}\,dM_{\mathbf v}(t;s).
$$

若 $f(\cdot;s)$ 在端点满足指数—多项式阶的增长/衰减，且 (H1)–(H2) 对某竖条成立，则对 $k$-变量施行有限阶 EM 并用 T4.2 可得 $\mathcal L_{\mathbf v}$ 在该竖条内的亚纯延拓，其**极点完全由主尺度拉普拉斯项决定**；其**位置与阶**与 S5 的极点定位定理一致（"主项指数—多项式 $\Rightarrow$ 极点阶 $\le$ 多项式次数 + 1"）。S2 的二项闭合判定可用于局部确定主导子和与横截性（零为简单/非简零），从而为方向化的极点结构提供几何模板。

---

## 5. 典型框架与示例（模板化落地）

### 框架 A（Mellin—EM 复合）

设 $K$ 为 S3 的 $a$-自反核。考虑

$$
\Phi(s)=\sum_{n\ge1} K(n)\,n^{-s}\quad\text{或}\quad \int_{1}^{\infty} K(x)\,x^{-s}\,dx.
$$

当仅具有限阶端点展开（而非 Schwartz 级）时，对 $\sum_{n\ge1}K(n)n^{-s}$ 施行有限阶 EM；主尺度项由 $\int K(x)x^{-s}dx$ 及其端点导数构成，余项全纯。由 T4.2，极点仅出自主尺度项。依 S3 选取 $r(s)$（$\Gamma/\pi$ 因子）可得在工作竖条内全纯（无极点）的完成函数 $\Xi=r\Phi$。

### 框架 B（方向化采样—Nyquist/Poisson + EM）

尺度网格 $\rho_k=\rho_0+k\Delta\,\mathbf v$（$b=e^\Delta$）上对 $F(\theta,\rho)$ 的采样生成函数，经有限阶 EM 分解为"主尺度积分 + 有限伯努利层 + 余项层"；主尺度积分决定条带内的亚纯延拓与潜在极点，余项层全纯。该框架与 S8 的一致逼近/误差常数表可直接拼接（误差三分解：别名/端点/截断）。

---

## 6. 反例与边界族（失效原因逐条标注）

* **R4.1（无限伯努利层）**：若将 EM 作为**无穷**级数而非有限阶使用，即便 $f$ 光滑，也可能导致**发散**或**非一致可和**，出现伪"极点"（实为形式外推的假象）。
* **R4.2（端点不可积/未消去）**：若 $f^{(k)}(\cdot;s)$ 在端点不满足 (H2) 的带权可积或必要的有限阶消失，则 $R_M$ 不再全纯；端点发散会渗入余项。
* **R4.3（换序违规）**：未在 S1 的管域/主导收敛下进行"求和—积分—微分"的互换，结论不成立。
* **R4.4（方向网格退化）**：$\Delta\to0$ 与 $N\to\infty$ 的极限若不按"先 $N$，后 $\Delta$"或缺少一致控制，可能破坏主尺度与余项的分离。

---

## 7. 统一"可检清单"（最小充分条件）

1. **有限阶**：固定 $M$，仅保留至 $B_{2(M-1)}$ 的伯努利层与 $R_M$。
2. **端点正则**：存在 $w_M\in L^1$ 主导 $\{f^{(k)}\}_{k\le 2M}$ 且满足端点有限阶消失/有界（H1–H2）。
3. **条带控制**：主尺度项 $\mathcal I(\Delta;s)$ 在工作竖条内亚纯，并给出潜在极点的**显式位置/阶**。
4. **余项全纯**：按 T4.1 验证 $\mathcal B_m$ 与 $R_M$ 在条带内全纯（若全域成立，则为整函数）。
5. **镜像拼接（可选）**：若需完成函数，对照 S3 选择 $r(s)$ 消去主尺度极点并获得镜像对称。
6. **几何一致性**：方向化/局部二项主导时，与 S2 的二项闭合—横截模板相容（零的简单性/退化判定）。

---

## 8. 与后续篇章的接口

* **→ S5（方向亚纯化）**：T4.2 提供"极点 = 主尺度"的解析基线；结合方向计数的指数—多项式形（S5）即可确定极点位置与阶。
* **→ S6（信息量刻度）**：EM 仅改变整函数层，故相位层的信息守恒（S0 基本原理）与尺度层的宇称破缺校正可在不更动极点结构的前提下开展。
* **→ S7（$L$-函数接口）**：主尺度项的极点由 archimedean 因子与端点主项诱发；以 S3 的 $r(s)$ 归一化后可直接嵌入显式公式。
* **→ S8（一致逼近）**：有限阶 EM 的余项上界与伯努利层常数进入误差三分解；与 Nyquist/Poisson 拼接给出非渐近常数表。
* **→ S10（几何增长）**：主尺度项决定的条带增长与 amoeba/Ronkin 几何约束相容；S2 的"平衡超平面"提供尺度投影的必要局部化。

---

## 附录 A：乘法版本的有限阶 EM（Mellin 侧速记）

令 $g\in C^{2M}([1,B])$，考虑乘法网格 $x_n=b^n$（$b=e^{\Delta}$）。对 $\sum_{n=0}^{N-1}g(b^n)$ 的 EM 公式可经变量代换 $y=\log x$ 自加法版本得到；伯努利层与余项形式保持不变，仅在系数中出现 $\Delta$ 的幂次。对 Mellin 变换 $\int g(x)\,x^{s-1}dx$ 的主尺度贡献与端点导数形成极点源，余项整函数。

---

## 附录 B：Stirling 与完成函数的垂线增长

取 S3 的对称因子 $r(s)$（$\Gamma/\pi$ 因子）。由 Stirling 估计，在任意闭竖条上 $|r(s)|$ 以 $\exp\bigl(-\tfrac{\pi}{2}J|t|\bigr)$ 衰减（$J$ 为成对 $\Gamma_{\mathbb R}$ 因子数目），故

$$
r(s)\left(\sum_{m<M}\mathcal B_m+R_M\right)
$$

至多多项式增长；若 $r(s)\mathcal I(\Delta;s)$ 在 $V$ 内消极点，则完成函数在 $V$ 内全纯（无极点）。

---

## 结语

有限阶 EM 将离散—连续桥接为"主尺度 + 伯努利层 + 余项层"的三段式结构：在 S1 的管域与换序纪律之下，**余项层全纯/整函数**、**极点仅由主尺度项诱发**；配合 S3 的 $\Gamma/\pi$ 正规化可消极点并获得镜像对称。该范式把 S2 的局部几何（两项闭合、横截）与 S5 的方向亚纯化精确拼接，为 S7/S8/S10 的算术接口、误差常数与几何增长提供统一、可检且可复用的解析基线。
