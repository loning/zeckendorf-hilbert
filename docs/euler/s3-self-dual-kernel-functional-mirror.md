# S3. 自反核与函数镜像

**—— Mellin 自反性、完成函数模板与增长界的可检基线**

## 摘要（定性）

在 S1 的管域/换序基线与 S2 的加法镜像几何之后，本文系统建立**自反核—Mellin 镜像**与**完成函数**的统一模板：在最小可积假设下，由自反核 $K(x)=x^{-a}K(1/x)$ 推出 $\Phi(s)=\Phi(a-s)$ 的严格定理；在乘法群 Schwartz 类与有限阶端点正则两类前提下，给出 $\Phi$ 的解析性与（按需）整性/亚纯性；构造满足 $r(s)=r(a-s)$ 的 $(\Gamma/\pi)$ 正规化因子，建立完成函数 $\Xi(s)=r(s)\Phi(s)$ 的**模板定义**与**垂线增长界**；并以 $\xi(s)$ 为例示范核的选取与对称性。全文给出可检条件与完整证明，记号与换序纪律与 S0/S1 保持一致。

---

## 0. 记号与前置（与 S0/S1/S2 对齐）

### 0.1 Mellin 变换与自反核

对 $K:(0,\infty)\to\mathbb C$ 与复数 $a$，称 $K$ 为**$a$-自反核**，若

$$
K(x)=x^{-a}K(1/x)\quad(x>0).
$$

$$
\boxed{\ \text{本文中 }a\in\mathbb R\ .\ }
$$

定义 Mellin 变换

$$
\Phi(s):=\mathcal M[K](s)=\int_0^\infty K(x) x^{s-1} dx
$$

在其绝对收敛条带内全纯。收敛、换序、逐项运算均遵循 S1 的 C0–C3（管域、Tonelli–Fubini、Morera、Weierstrass 判据）。

### 0.2 可积域

$$
\mathcal I(K):=\Big\{\sigma\in\mathbb R:\ \int_0^1 |K(x)| x^{\sigma-1} dx<\infty,\ \int_1^\infty |K(x)| x^{\sigma-1} dx<\infty\Big\}.
$$

若 $\mathcal I(K)\neq\varnothing$，则 $\mathcal I(K)^\circ$ 一般为若干开区间的并。取其中任一连通分量 $(\sigma_-,\sigma_+)$。

### 0.3 乘法群上的 Schwartz 类

定义

$$
\boxed{\quad H\in\mathcal S(\mathbb R_+^\times)\iff
\sup_{x>0}(1+|\log x|)^M\,\big|(x\partial_x)^N H(x)\big|<\infty\ \ (\forall M,N\in\mathbb N)\quad}
$$

等价于 $h(y):=H(e^y)\in\mathcal S(\mathbb R)$。此为标准的 Mellin–Fourier 词典。

### 0.4 与 S2 的镜像接口

S2 的"幅度平衡 + 相位对径"给出零集的横截几何（余维 $2$）。本篇在乘法侧给出解析对称 $\Phi(s)=\Phi(a-s)$，二者在核选取与完成函数构造上对偶。

---

## 1. 自反核推出函数镜像（最小可积前提）

### 定理 T3.1（Mellin 自反性 $\Rightarrow$ 函数镜像）

设 $K$ 为 $a$-自反核，且 $\mathcal I(K)\cap(a-\mathcal I(K))\neq\varnothing$。取 $\mathcal I(K)^\circ$ 的任一连通分量 $(\sigma_-,\sigma_+)$，则对

$$
\Re s\in(\sigma_-,\sigma_+)\cap(a-\sigma_+,a-\sigma_-)
$$

有

$$
\Phi(s)=\Phi(a-s).
$$

因此 $\Phi$ 在该竖条内关于 $\Re s=\tfrac a2$ 对称并全纯。

**证明。** 绝对收敛下换元 $x\mapsto 1/x$：

$$
\Phi(s)=\int_0^\infty K(x) x^{s-1} dx
:=\int_0^\infty x^{-a} K(1/x) x^{s-1} dx
:=\int_0^\infty K(u) u^{a-s-1} du
:=\Phi(a-s).
$$

端点项由绝对可积排除；全纯性由 S1 的 Morera–Tonelli 与 Cauchy 公式给出。∎

---

## 2. 自反核的构造与整性情形

### 命题 3.2（自反核的系统构造）

任取 $H:(0,\infty)\to\mathbb C$，令

$$
K_H^{(a)}(x):=x^{-a/2}\big(H(x)+H(1/x)\big).
$$

则 $K_H^{(a)}$ 为 $a$-自反核。若 $H\in\mathcal S(\mathbb R_+^\times)$，则

$$
\Phi(s)=\int_0^\infty K_H^{(a)}(x) x^{s-1} dx
$$

在中央竖线 $\Re s=\tfrac a2$ 上以 Lebesgue 积分一定良好定义，且 $t\mapsto \Phi(\tfrac a2+it)$ 为 Schwartz。若不额外假设指数型衰减或紧支撑，则一般仅能在中央竖线绝对可积；若存在 $\eta>0$ 使 $e^{\eta|\log x|}H\in L^1(\mathbb R_+^\times)$（或 $h$ 在 $y$ 上紧支撑），则可得 $|\Re s-\tfrac a2|<\eta$ 的竖条（或更大域）内的全纯与竖线多项式界（与下文一致）。

**证明要点。** 以 $y=\log x$ 化到加法群并反复做乘法分部积分，边界项因 $H\in\mathcal S(\mathbb R_+^\times)$ 消失；中央竖线对应偶 Fourier 变换给出 Schwartz 级衰减。若加入指数权假设，则由 Montel/Weierstrass 在中心条带内得全纯性与竖线多项式界。∎

---

## 3. 完成函数的 $\Gamma/\pi$ 正规化与垂线增长

### 定义 3.3（对称 $\Gamma/\pi$ 因子）

称 $r(s)$ 为**$a$-对称 $\Gamma/\pi$ 因子**，若存在有限组 $\{(\lambda_j,\delta_j)\}_{j=1}^J$（$\lambda_j\in\mathbb R$, $\delta_j\in\{0,1\}$）使

$$
r(s)=\prod_{j=1}^J\Big[\pi^{-\frac{s+\lambda_j}{2}}\,\Gamma\Big(\frac{s+\lambda_j}{2}\Big)\,\pi^{-\frac{a-s+\lambda_j}{2}}\,\Gamma\Big(\frac{a-s+\lambda_j}{2}\Big)\Big]^{\delta_j}
$$

从而 $r(a-s)=r(s)$。

### 定义 3.4（完成函数）

在 T3.1 的竖条内，定义

$$
\Xi(s):=r(s)\,\Phi(s)\quad\Rightarrow\quad \Xi(a-s)=\Xi(s).
$$

### 命题 3.5（垂线增长控制）

若 $\Phi$ 在竖条 $\sigma_0\le\Re s\le \sigma_1$ 内至多多项式增长，则 $\Xi(s)$ 在同一竖条内具多项式界，且**每一对** $\Gamma_{\mathbb R}$-因子同时附加

$$
\Gamma_{\mathbb R}(u):=\pi^{-u/2}\,\Gamma(u/2)
$$

在 $\Re s=\sigma$ 上提供 **$e^{-\frac{\pi}{2}|t|}$** 级别的指数衰减；若共有 $J$ 对，则在该竖条内整体获得 $e^{-\frac{\pi}{2}J|t|}$ 的指数级衰减。

**证明要点。** 固定 $\sigma$ 应用 Stirling 估计
$|\Gamma(\sigma'+it')|\sim \sqrt{2\pi}\,|t'|^{\sigma'-1/2}e^{-\frac{\pi}{2}|t'|}$，
对 $\Gamma_{\mathbb R}(s+\lambda_j)\Gamma_{\mathbb R}(a-s+\lambda_j)$ 得到 $e^{-\frac{\pi}{2}|t|}$ 衰减，与 $\Phi$ 的多项式界相乘即得结论。∎

---

## 4. 典型特例：$\xi(s)$ 的核化表达

令 Jacobi $\vartheta$-核

$$
\vartheta(x)=\sum_{n\in\mathbb Z}e^{-\pi n^2 x},\qquad \vartheta(x)=x^{-1/2}\vartheta(1/x),
$$

并取

$$
K_\vartheta(x):=\vartheta(x)-1-x^{-1/2},\qquad
\Phi_\vartheta(s):=\int_0^\infty K_\vartheta(x)\,x^{\frac{s}{2}-1}\,dx.
$$

上述积分在 $0<\Re s<1$ 绝对收敛并由此定义 $\Phi_\vartheta$；在该条带外，$\Phi_\vartheta$ 取其解析延拓（下述恒等式先在 $1<\Re s<2$ 成立，并由解析延拓确定 $\Phi_\vartheta$ 的整性）。

则 $K_\vartheta$ 为 $a=\tfrac12$ 的自反核；在 $x\to0^+$ 端有 $K_\vartheta(x)\to -1$，且 $\vartheta(x)-x^{-1/2}$ 部分指数小；在 $x\to\infty$ 端为 $-x^{-1/2}+O(e^{-\pi x})$ 的幂主导衰减。由正规化恒等式 $\pi^{-s/2}\Gamma(\tfrac s2)\zeta(s)=\tfrac{1}{2}\,\Phi_\vartheta(s)+\tfrac{1}{s(s-1)}$ 抵消因端点常数主项产生的极点，得 $\Phi_\vartheta$ 的整性（经解析延拓）。

经典恒等式（对 $1<\Re s<2$ 先成立，后解析延拓）为

$$
\boxed{\ \pi^{-s/2}\,\Gamma\Big(\frac{s}{2}\Big)\,\zeta(s)
:=\tfrac{1}{2}\,\Phi_\vartheta(s)+\frac{1}{s(s-1)}\ }\quad\text{（其中 }\tfrac{1}{s(s-1)}\text{ 由两端的主项（}x\to0^+\text{ 的常数项与 }x\to\infty\text{ 的幂主项）合并产生）}
$$

据此定义

$$
\boxed{\ \Xi_\vartheta(s):=\frac{1}{2}\,s(s-1)\Big(\tfrac{1}{2}\,\Phi_\vartheta(s)+\frac{1}{s(s-1)}\Big)
:=\frac{1}{2}\,s(s-1)\,\pi^{-s/2}\,\Gamma\Big(\frac{s}{2}\Big)\,\zeta(s)\ },
$$

则 $\Xi_\vartheta(1-s)=\Xi_\vartheta(s)$，即黎曼完成函数 $\xi(s)$ 的标准对称性。

---

## 5. 逆向命题与核—函数等价

### 定理 T3.6（镜像函数的核化表示）

设 $F(s)$ 在竖条 $\sigma_0\le\Re s\le\sigma_1$ 全纯并多项式增长，且 $F(s)=F(a-s)$。取 $\sigma\in(\sigma_0,\sigma_1)$ 使

$$
\boxed{\ \{\sigma,\ a-\sigma\}\subset(\sigma_0,\sigma_1)\ \text{且}\ F\ \text{在闭条带 } \min\{\sigma,a-\sigma\}\le \Re s\le \max\{\sigma,a-\sigma\}\ \text{内至多多项式增长}\ }
$$

在 Mellin-温和分布意义下定义

$$
K(x):=\frac{1}{2\pi i}\int_{\Re s=\sigma} F(s)\,x^{-s}\,ds.
$$

则（在分布意义下）有 $K(x)=x^{-a}K(1/x)$，且 $\mathcal M[K](s)=F(s)$ 在该条带成立；若进一步有 $F(\sigma+it)=O(|t|^{-1-\varepsilon})$（或充分的 $L^1$ 条件），则 $K$ 在函数意义下成立同样结论。

**证明要点。** 由增长界合法移线至 $\Re s=a-\sigma$，并用镜像 $F(s)=F(a-s)$ 与柯西定理，得自反关系与 Mellin 互逆。若要求在函数意义下直接移线，可补充 $F(\sigma+it)=O(|t|^{-1-\varepsilon})$（任一闭条带内）等 Phragmén–Lindelöf 型控制；否则按文中所述取分布意义。∎

---

## 6. 反例与边界族

* **R3.1（非严格自反）**：若 $K=x^{-a}K(1/x)+E$ 且 $E\not\equiv0$，则 $\Phi(s)-\Phi(a-s)=\mathcal M[E](s)$。
* **R3.2（端点不可积）**：若端点型 $K(x)\sim x^{-\beta}\ (x\to0^+)$ 或 $\sim x^{-\gamma}\ (x\to\infty)$ 致 $\mathcal I(K)=\varnothing$，则 $\Phi$ 无合法条带。
* **R3.3（换序违规）**：未满足 S1 的主导收敛/绝对收敛条件时，Poisson—Mellin 交换与微分/积分互换不成立。

---

## 7. 统一"可检清单"（S3-CL）

1. **自反性**：$K(x)=x^{-a}K(1/x)$。
2. **收敛竖条**：$\mathcal I(K)$ 含非空开区间；镜像在 $\max\{\sigma_-,a-\sigma_+\}<\Re s<\min\{\sigma_+,a-\sigma_-\}$ 内成立。
3. **换序纪律**：凡换元、Poisson、逐项运算，均在 S1 的 C0–C3 假设下进行。
4. **全纯/整性途径（二选一）**：
   (a) 若仅 $H\in\mathcal S(\mathbb R_+^\times)$，则保证中央竖线 $\Re s=\tfrac a2$ 上的可积与随 $t$ 的快速衰减；若需条带内全纯与多项式界，需额外指数权或改用 S4；或
   (b) 具有限阶端点展开并带权可积（极点来源与亚纯延拓由 S4 的"伯努利层 + 有限阶 EM"给出）。
5. **正规化**：取 $a$-对称 $\Gamma/\pi$ 因子 $r(s)$，则 $\Xi=r\Phi$ 满足 $\Xi(a-s)=\Xi(s)$；每对 $\Gamma_{\mathbb R}$ 在垂线给出 $e^{-\frac{\pi}{2}|t|}$ 衰减。

---

## 附录 A：Mellin 分部积分与整性判据

若 $f\in C^N(0,\infty)$ 且对某 $\sigma\in\mathbb R$，$(x\partial_x)^k f\in L^1((0,\infty),x^{\sigma-1}dx)$（$0\le k\le N$），并满足

$$
\lim_{x\to0^+}x^\sigma\sum_{k=0}^{N-1}\big|(x\partial_x)^k f(x)\big|=0,\quad
\lim_{x\to\infty}x^\sigma\sum_{k=0}^{N-1}\big|(x\partial_x)^k f(x)\big|=0,
$$

则在 $\Re s=\sigma$ 上（若 $s\notin\{0\}$）

$$
\int_0^\infty f(x)\,x^{s-1}dx=\frac{(-1)^N}{s^N}\int_0^\infty (x\partial_x)^N f(x)\,x^{s-1}dx.
$$

在 $s=0$ 处以极限作连续延拓。并要求在所取 $\Re s=\sigma$ 上满足带权可积与边界项消失。若右端对所有 $s\in\mathbb C$ 绝对收敛（例如 $f$ 紧支撑，或满足 $\forall\eta>0,\ e^{\eta|\log x|}f\in L^1$），则 $\Phi$ 整。

---

## 附录 B：$\vartheta$-核与 $\xi(s)$ 的积分表示

由 Poisson 求和得 $\vartheta(x)=x^{-1/2}\vartheta(1/x)$。对 $1<\Re s<2$,

$$
\int_0^\infty\big(\vartheta(x)-1\big)\,x^{\frac{s}{2}-1}dx=2\,\pi^{-s/2}\,\Gamma\Big(\frac{s}{2}\Big)\,\zeta(s),
$$

再以 $K_\vartheta=\vartheta-1-x^{-1/2}$ 规约两端发散并解析延拓，得到 §4 的恒等式与
$\Xi_\vartheta(s)=\xi(s)$。

---

## 附录 C：垂线增长的 Stirling 估计

记 $s=\sigma+it$。Stirling 公式给

$$
\big|\Gamma\big(\tfrac{s+\lambda}{2}\big)\big|\sim \sqrt{2\pi}\,\Big|\tfrac{t}{2}\Big|^{\frac{\sigma+\lambda}{2}-\frac12}\,e^{-\frac{\pi}{4}|t|}\quad(|t|\to\infty),
$$

故每对
$\Gamma_{\mathbb R}(s+\lambda)\Gamma_{\mathbb R}(a-s+\lambda)$
在 $\Re s=\sigma$ 上提供 $e^{-\frac{\pi}{2}|t|}$ 的指数级衰减，与 $\Phi$ 的多项式界合并即得命题 3.5。

---

## 结语

自反核把 S2 的**几何镜像**提升为乘法侧的**解析镜像**：在最小可积前提下得到 $\Phi(s)=\Phi(a-s)$；在强正则下获得整性与垂线增长控制；借助对称的 $\Gamma/\pi$ 正规化，完成函数 $\Xi$ 自然呈现对称轴 $\Re s=\tfrac a2$。该模板既支撑 **S4** 的有限阶 Euler–Maclaurin 解析延拓与极点消除，也为 **S7** 的 $L$-函数 archimedean 因子与显式公式提供统一语法与增长工具。
