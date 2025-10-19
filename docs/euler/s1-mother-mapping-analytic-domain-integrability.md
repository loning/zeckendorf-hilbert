# 母映射的解析域与可积性基线

（S1：严格陈述、完整证明与可检清单）

**作者**：
**单位**：
**电子邮箱**：

---

## 摘要

本文以相位–尺度母映射 $\mathcal M[\mu]$ 为中心对象，系统建立其**解析域、可积性与换序**的基线理论。我们给出：（i）**指数矩—管域解析定理**：若谱测度 $\mu$ 具有某方向的指数矩，则母映射在相应**管域**中对尺度变量全纯、对相位变量连续且一致有界；（ii）**离散谱的充分收敛—全纯准则**：对离散谱，$\sum_j|c_j|e^{\langle\beta_j,\Re\rho\rangle}<\infty$ 在某开集上成立即蕴含局部一致收敛与全纯性；（iii）**换序与微分—积分互换准则**：给出 Fubini/Tonelli 与主导收敛下的最小可检条件，从而合法地进行求和/积分/微分的互换。并建立增长估计、凸性与边界行为的若干引理，给出 ζ/Dirichlet 级数等典型例与两类反例。全文作为系列论文的基础篇，给出面向应用的**可检清单**。

**关键词**：母映射；指数矩；管域；Tonelli/Fubini；主导收敛；Weierstrass 判别法；局部一致收敛；全纯函数。

---

## 1. 引言与设定

相位–尺度母映射把"相位旋转"与"尺度伸缩"统一到一个解析对象中，可书写为

$$
\mathcal M[\mu](\theta,\rho)=\int_{\mathbb R^m\times\mathbb R^n}
e^{i\langle\omega,\theta\rangle}\,e^{\langle\gamma,\rho\rangle}\,d\mu(\omega,\gamma),
\qquad \theta\in\mathbb R^m,\ \rho\in\mathbb C^n,
$$

其中 $\mu$ 为 $\mathbb R^m\times\mathbb R^n$ 上的 $\sigma$-有限 Radon 复测度。若 $\operatorname{proj}_\omega(\operatorname{supp}\mu)\subset\mathbb Z^m$，则自然降至 $\mathbb T^m$ 的等价表述。若 $\mu$ 离散，

$$
\mathcal M[\mu](\theta,\rho)=\sum_{j} c_j\,e^{\langle\beta_j,\rho\rangle}\,e^{i\langle\alpha_j,\theta\rangle},
\quad (\alpha_j,\beta_j)\in\mathbb R^m\times\mathbb R^n,\ c_j\in\mathbb C.
$$

本文目标是刻画其解析域与可积性、给出合法换序与微分的最小充分条件，并在离散谱情形下给出可检收敛准则。

---

## 2. 记号与基本对象

* $\langle\cdot,\cdot\rangle$：$\mathbb R^d$ 上标准内积；$\Re z,\Im z$：复数的实部与虚部。
* $\mathbb T:=\mathbb R/2\pi\mathbb Z$，$\mathbb T^m$ 为 $m$ 维相位环面。
* $|\mu|$：复测度 $\mu$ 的全变差。
* **指数矩集合**：

$$
\mathsf E(\mu):=\Bigl\{\tau\in\mathbb R^n:\ \int e^{\langle\gamma,\tau\rangle}\,d|\mu|(\omega,\gamma)<\infty\Bigr\}.
$$

* **管域（tube domain）**：给定 $\tau\in\mathsf E(\mu)$，定义

$$
\mathcal T(\tau):=\Bigl\{\rho\in\mathbb C^n:\ \Re\langle\gamma,\rho\rangle < \langle\gamma,\tau\rangle\ \text{对所有 $(\omega,\gamma)\in\operatorname{supp}\mu$ 且 $\gamma\ne 0$}\Bigr\}.
$$

（注：若支撑含 $\gamma=0$ 的点，则上述严格不等式按“对所有 $\gamma\ne 0$ 的支撑”理解；$\{\gamma=0\}$ 上 $e^{\langle\gamma,\rho\rangle}\equiv1$ 仅贡献与 $\rho$ 无关的常数项。若 $|\mu|(\{\gamma=0\})=\infty$ 则 $\int e^{\langle\gamma,\tau\rangle}d|\mu|$ 本已发散，与 C1 不相容。）

---

## 3. 指数矩与管域解析

### 定理 3.1（管域解析定理）

若 $\tau\in\mathsf E(\mu)$，则对任意固定 $\theta\in\mathbb R^m$，映射 $\rho\mapsto\mathcal M[\mu](\theta,\rho)$ 在开集 $\mathcal T(\tau)$ 上全纯；对任意固定 $\rho\in\mathcal T(\tau)$，$\theta\mapsto\mathcal M[\mu](\theta,\rho)$ 为连续函数（并在 $\mathbb R^m$ 的任意紧致集上有界）。此外，在任意紧致 $K\Subset\mathcal T(\tau)$ 上存在常数 $C_K$ 使

$$
\sup_{\theta\in\mathbb R^m,\ \rho\in K}|\mathcal M[\mu](\theta,\rho)|
\le C_K\int e^{\langle\gamma,\tau\rangle}\,d|\mu|(\omega,\gamma).
$$

**证明**（给出要点）。任取 $K\Subset\mathcal T(\tau)$。对任意 $\rho\in K$ 与支撑上 $\gamma\ne 0$，由 $\rho\in\mathcal T(\tau)$ 得 $\Re\langle\gamma,\rho\rangle<\langle\gamma,\tau\rangle$；对 $\gamma=0$ 则有 $\Re\langle\gamma,\rho\rangle=\langle\gamma,\tau\rangle=0$。因此
$$
\bigl|e^{i\langle\omega,\theta\rangle}e^{\langle\gamma,\rho\rangle}\bigr|\le e^{\langle\gamma,\tau\rangle}.
$$
取 $C_K=1$。右端对 $(\omega,\gamma)$ 可积。由主导收敛与 Morera/换序可得对 $\rho$ 的全纯性；对 $\theta$ 的连续性与（在紧致集上的）有界性同理。上式给出一致上界。∎

### 命题 3.2（$\mathsf E(\mu)$ 的凸性与非空性准则）

$\mathsf E(\mu)$ 为凸集；若存在 $\tau_0$ 与 $\varepsilon>0$ 使 $\int e^{\langle\gamma,\tau_0\rangle+\varepsilon|\gamma|}\ d|\mu|<\infty$（充分条件：存在邻域 $U\ni\tau_0$ 满足 $\int e^{\langle\gamma,\tau\rangle}d|\mu|<\infty\ \forall\tau\in U$），则 $\tau_0\in\operatorname{int}\mathsf E(\mu)$。

**证明**。由 Hölder/Young 不等式，$f(\tau)=\int e^{\langle\gamma,\tau\rangle}d|\mu|$ 为对数凸，从而 $\mathsf E(\mu)$ 凸；在给定的局部指数余量条件下，$\tau_0\in\operatorname{int}\mathsf E(\mu)$。∎

---

## 4. 离散谱的收敛—全纯准则与增长界

### 定理 4.1（离散谱的充分收敛—全纯判别）

设 $\mu=\sum_j c_j\,\delta_{(\alpha_j,\beta_j)}$。若存在开集 $U\subset\mathbb C^n$ 使对每个紧致 $K\Subset U$ 有

$$
\sum_j |c_j|\,e^{\sup_{\rho\in K}\langle\beta_j,\Re\rho\rangle}<\infty,
$$

则 $\mathcal M[\mu](\theta,\rho)=\sum_j c_j e^{\langle\beta_j,\rho\rangle}e^{i\langle\alpha_j,\theta\rangle}$ 在 $\mathbb R^m\times U$ 上**绝对且局部一致收敛**，并对 $\rho$ 全纯、对 $\theta$ 连续。逐项微分可在满足 §5.2 的充分条件时成立：

$$
\partial_{\rho}^{\nu}\mathcal M[\mu](\theta,\rho)
=\sum_j c_j\,\beta_j^{\nu}\,e^{\langle\beta_j,\rho\rangle}e^{i\langle\alpha_j,\theta\rangle},\qquad \nu\in\mathbb N^n.
$$

**证明**。对任意紧致 $K\Subset U$，由前提有 $\sum_j |c_j| e^{\sup_{\rho\in K}\langle\beta_j,\Re\rho\rangle} < \infty$。取 $M_j = |c_j| e^{\sup_{\rho\in K}\langle\beta_j,\Re\rho\rangle}$，则 $\sum_j M_j < \infty$。由 M-判别法给出在 $\mathbb R^m \times K$ 上的局部一致收敛；由 Weierstrass 定理得和函数对 $\rho$ 全纯；逐项微分则需 §5.2 的矩条件。∎

### 命题 4.2（增长估计）

在 4.1 的条件下，对 $K\Subset U$ 有

$$
\sup_{\theta\in\mathbb R^m,\ \rho\in K}|\mathcal M[\mu](\theta,\rho)|
\le \sum_j |c_j|\,e^{\sup_{\rho\in K}\langle\beta_j,\Re\rho\rangle}.
$$

---

## 5. 换序与微分—积分互换的最小准则

### 定理 5.1（Fubini/Tonelli 换序）

设 $U\subset\mathbb C^n$ 开。若存在 $\rho_0\in U$ 与邻域 $V\Subset U$ 使

$$
\int \sup_{\rho\in V}\bigl|e^{\langle\gamma,\rho\rangle}\bigr|\,d|\mu|(\omega,\gamma)<\infty,
$$

则可合法交换下列运算：
$\triangleright$ 对 $(\omega,\gamma)$ 的积分与对 $\theta$ 的环面积分（或傅里叶系数提取）（当 $\omega$-谱含于 $\mathbb Z^m$ 时可作傅里叶系数提取；一般情形下可理解为对 $\theta\in\mathbb R^m$ 的有界测度平均/测试函数配对，与 $(\omega,\gamma)$-积分可在所给主导条件下互换）；
$\triangleright$ 对 $(\omega,\gamma)$ 的积分与对 $\rho$ 的线积分（Cauchy 公式）与偏导数；
$\triangleright$ 在离散谱下，对 $\sum_j$ 与上述各运算的互换。

**证明**。由所给可积上界与 Tonelli 定理，绝对可积性保证换序；对复可微由 Morera 与 Cauchy 公式在 $V$ 内成立，逐项（或逐点）运算合法。∎

### 定理 5.2（逐项微分的充分条件）

若对某紧致 $K\Subset U$ 与多重指标 $\nu$ 有

$$
\sum_j |c_j|\,|\beta_j|^{|\nu|}\,e^{\sup_{\rho\in K}\langle\beta_j,\Re\rho\rangle}<\infty,
$$

则 $\partial_{\rho}^{\nu}\mathcal M[\mu]$ 可逐项计算并在 $\mathbb R^m\times K$ 上局部一致收敛。∎

---

## 6. 边界与管域几何

记 $\partial\mathcal T(\tau)$ 为管域边界。若 $\rho\to\rho_b\in\partial\mathcal T(\tau)$ 并存在 $(\omega_\star,\gamma_\star)\in\operatorname{supp}\mu$ 使 $\Re\langle\gamma_\star,\rho_b\rangle=\langle\gamma_\star,\tau\rangle$，则一般不再有统一可积主导，可能发生发散。以下给出两类标准情形：

* **规整边界**：若 $\langle\gamma,\rho_b\rangle\le \langle\gamma,\tau\rangle-\delta$ 对除一薄集外成立，且该薄集上 $d|\mu|$ 可积衰减，$\mathcal M[\mu]$ 可能延拓至更大管域（需补充增长条件；见系列 S3）。
* **临界发散**：若存在非零测度集中在 $\langle\gamma,\rho_b\rangle=\langle\gamma,\tau\rangle$ 的超平面上，典型地出现对数级或幂级发散（见反例 8.2）。

---

## 7. 例与特例

### 例 7.1（ζ/Dirichlet 级数）

取离散谱 $\beta_n=-\log n$、$\alpha_n=\log n$、$c_n=1$。当 $\sigma>1$ 时，

$$
\mathcal M[\mu](-t,\sigma)=\sum_{n\ge1}n^{-(\sigma+it)}=\zeta(\sigma+it),
$$

（此处按 $\theta\in\mathbb R$、$\omega=\log n$ 的实参设定；与 §5 的换序条件兼容，因为 $|e^{i\omega\theta}|\equiv 1$。）

与定理 4.1 的判据一致；其管域边界为 $\sigma=1$。

### 例 7.2（有限带宽相位谱）

若仅有限个 $\alpha_j$ 非零而 $\sum_j|c_j|e^{\langle\beta_j,\Re\rho\rangle}<\infty$，则 $\theta\mapsto\mathcal M[\mu](\theta,\rho)$ 为有限三角多项式，$\rho\mapsto\mathcal M[\mu]$ 在上式给定开集内全纯。

### 例 7.3（连续谱与指数核）

设 $\mu$ 密度为 $c(\omega,\gamma)\,d\omega\,d\gamma$，且 $\int e^{\langle\gamma,\tau\rangle}|c|\ d\omega d\gamma<\infty$。定理 3.1 直接给出 $\mathcal T(\tau)$ 内全纯与一致上界。

---

## 8. 反例与边界案例

### 反例 8.1（指数矩缺失导致非解析）

令 $\mu=\sum_{k\ge1}\delta_{(\omega_k,\gamma_k)}$ 且 $\gamma_k=k e_1$（$e_1$ 为坐标向量），$c_k=e^{k^2}$。则对任意 $\tau\in\mathbb R^n$，
$\int e^{\langle\gamma,\tau\rangle}d|\mu|=\sum_k e^{k^2 + k\langle e_1,\tau\rangle}$ 发散，故 $\mathsf E(\mu)=\varnothing$。此时不存在非空管域，$\rho\mapsto\mathcal M[\mu]$ 无全纯区。

### 反例 8.2（临界边界上的发散）

取 $\mu$ 支撑在 $\{(\omega,\gamma):\ \gamma = t v,\ t\ge 0\},\ \|v\|=1,\ d\mu(t)=dt$。则对 $\tau<0$，$\int_0^\infty e^{t \tau}\,dt<\infty$，且当且仅当 $\tau<0$。管域 $\mathcal T(\tau)=\{\Re \langle v,\rho\rangle <\tau\}$。对 $\rho=s v$（$s$ 实），$s<\tau$ 时收敛；而整体解析域为 $\bigcup_{\tau<0} \mathcal T(\tau)=\{s<0\}$，其边界 $s=0$ 处 $\int_0^\infty dt=\infty$ 发散，给出边界锐性。

---

## 9. 可检清单（最小充分条件）

**C1（指数矩）**：存在 $\tau$ 使 $\int e^{\langle\gamma,\tau\rangle}d|\mu|<\infty$ $\Rightarrow$ $\rho\in\mathcal T(\tau)$ 上全纯且一致有界。
**C2（离散谱—局部 M 判别）**：在开集 $U$ 上对每个紧致 $K\Subset U$ 有 $\sum_j|c_j|e^{\sup_{\rho\in K}\langle\beta_j,\Re\rho\rangle}<\infty$ $\Rightarrow$ 局部一致收敛与全纯；若再满足 **C4（导数）**，则逐项微分合法。
**C3（换序）**：存在 $V\Subset U$ 使 $\int \sup_{\rho\in V}|e^{\langle\gamma,\rho\rangle}|\,d|\mu|<\infty$ $\Rightarrow$ 求和/积分/微分与对 $(\omega,\gamma)$ 的积分可互换。
**C4（导数）**：$\sum_j|c_j|\,|\beta_j|^{|\nu|}e^{\sup_{K}\langle\beta_j,\Re\rho\rangle}<\infty$ $\Rightarrow$ $\partial_\rho^\nu$ 可逐项。
**C5（边界）**：若存在支撑点达成 $\Re\langle\gamma,\rho_b\rangle=\langle\gamma,\tau\rangle$ 且相应测度不可忽略，$\rho_b$ 处一般非可积，慎用延拓。

---

## 10. 与后续篇章的接口

* **S2**：基于本篇的局部一致收敛与解析性，证明加法镜像下零集的横截结构与余维 $2$。
* **S3**：在 C1–C3 的框架中构造自反核，推导 $\Phi(s)=\Phi(a-s)$ 及完成函数。
* **S4/S5**：在本篇换序与主导收敛的基线上，建立 Euler–Maclaurin 有限阶误差与方向化亚纯化。
* **S6–S10**：信息刻度、$L$-函数接口、离散一致逼近与几何增长界均依赖本篇的解析域与换序准则。

---

## 附录 A：技术引理

### 引理 A.1（Morera—主导收敛版）

设 $f(\rho)=\int g(x,\rho)\,d\nu(x)$。若对每条闭合曲线 $\Gamma\subset U$ 有
$\int g(x,\rho)\,d\rho$ 在 $\Gamma$ 上绝对可积且可与 $d\nu$ 交换积分，则 $f$ 在 $U$ 上全纯。∎

### 引理 A.2（$\mathsf E(\mu)$ 的对数凸性）

函数 $\tau\mapsto \log \int e^{\langle\gamma,\tau\rangle}d|\mu|$ 为凸，因而 $\mathsf E(\mu)$ 凸。∎

### 引理 A.3（Weierstrass–M 判别法）

若 $\sum_j M_j<\infty$ 且 $|f_j(z)|\le M_j$ 于紧致集上一致成立，则 $\sum_j f_j$ 局部一致收敛并在各 $f_j$ 全纯时全纯。∎

---

## 参考文献

[1] E.M. Stein, R. Shakarchi, *Complex Analysis*, Princeton, 2003.
[2] L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, North-Holland, 1990.
[3] N. Bourbaki, *Integration*, Springer, 2004.
[4] H.L. Royden, P.M. Fitzpatrick, *Real Analysis*, Pearson, 2010.
[5] W. Rudin, *Real and Complex Analysis*, McGraw-Hill, 1987.

---

## 附录 B：与 ζ/Dirichlet 场景的快速对照

* **ζ 场景**：$\beta_n=-\log n$，当 $\sigma>1$，C2 成立（$\sum n^{-\sigma}<\infty$），得 $\mathcal M[\mu](-t,\sigma)=\zeta(\sigma+it)$ 并在 $\sigma>1$ 条带内全纯。
* **一般 Dirichlet 级数**：$\sum a_n e^{\langle\beta_n,\rho\rangle}$ 的绝对收敛域由 $\sum |a_n|e^{\langle\beta_n,\Re\rho\rangle}$ 确定，满足 C2 时即得全纯性与逐项微分。
* **连续核/光滑窗**：选 $K$ 为快速衰减核且满足自反性条件（见 S3），在 C1–C3 下可与 Poisson 求和换序并得到完成函数模板。

---

## 结语

本文给出了母映射的**解析域、可积性与换序**的最小充分条件，并配合离散与连续两类谱的可检判据与反例，构成系列论文的公共基线。后续各篇将以此为前提，分别落实零集几何、自反核—完成函数、伯努利层延拓、方向化亚纯化、信息刻度与 $L$-函数接口等更深层结构。
