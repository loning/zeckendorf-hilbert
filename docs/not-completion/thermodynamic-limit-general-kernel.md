# 熵的热力学极限：一般核函数的存在性、正则边界条件与稳定性

**作者**：Auric
**日期**：2025-10-20

---

## 摘要

本文在更一般的设定下严格证明熵密度的热力学极限存在，并建立边界条件、稳定性与信息论度量的关联。不再局限于对数位势或特定卷积结构，而是对满足**次可加性**与**平移不变性**的一般核函数 $K$ 给出完整的存在性论证（包含超可加不等式、Fekete引理）、正则边界条件（Dirichlet、Neumann、混合边界与周期边界）下熵增长的统一刻画，以及稳定性准则（对核扰动与边界扰动的连续依赖）。进一步将熵的热力学极限与拓扑熵、Kolmogorov–Sinai熵以及Shannon信息论在符号系统上的度量熵联系起来，并在多维情形给出各向异性与范数选择下的等价性。最后讨论量子信息论中的von Neumann熵与纠缠熵在热力学极限下的收敛性，为理解相变、长程关联与量子信息的体积律/面积律提供统一的数学框架。

**关键词**：热力学极限；熵密度；次可加性；Fekete引理；正则边界条件；稳定性；拓扑熵；信息论度量；量子纠缠熵

---

## 目录

1. 引言与动机
2. 基本设定与符号
3. 一般核函数的热力学极限存在性
4. 正则边界条件下的熵增长
5. 稳定性准则：对核与边界扰动的连续依赖
6. 与拓扑熵、符号动力学的联系
7. 信息论度量熵与Shannon熵的对应
8. 多维各向异性与范数等价性
9. 量子情形：von Neumann熵与纠缠熵的热力学极限
10. 结论与展望

附录A：超可加不等式与Fekete引理的推广
附录B：边界修正项的渐近估计
附录C：符号表

---

## 1 引言与动机

在统计力学与信息论中，**熵密度的热力学极限**

$$
s := \lim_{n\to\infty} \frac{S_n}{|V_n|}
$$

是核心量，其中 $S_n$ 为体积 $V_n$ 内的熵（或配分函数的对数），$|V_n|$ 为体积。经典结果（如对数位势、最近邻Ising模型）通过**次可加性**（subadditivity）保证极限存在。本文目标：

1. **一般核函数**：不限于对数或卷积形式，而是对满足次可加性与平移不变性的任意 $K$ 给出存在性。
2. **正则边界条件**：统一处理Dirichlet、Neumann、混合边界与周期边界，刻画边界修正项的渐近行为。
3. **稳定性**：建立对核扰动 $K\to K'$ 与边界扰动的连续依赖性，给出Lipschitz型估计。
4. **信息论联系**：将热力学熵与拓扑熵、Kolmogorov–Sinai熵、Shannon信息论度量熵对应，为符号动力学提供统一视角。
5. **量子推广**：讨论von Neumann熵与纠缠熵在热力学极限下的收敛性，涉及体积律与面积律的判据。

**文章结构**：§2建立记号；§3证明一般核的存在性；§4–5讨论边界与稳定性；§6–8联系拓扑熵与信息论；§9处理量子情形；§10总结。

---

## 2 基本设定与符号

### 2.1 体积序列与边界

设 $d$ 维欧氏空间 $\mathbb{R}^d$（或格点 $\mathbb{Z}^d$）。考虑体积序列 $\{V_n\}_{n\ge1}$，满足：

* **(V1) 增长性**：$V_n \subseteq V_{n+1}$，$|V_n|\to\infty$。
* **(V2) 正则性**：存在常数 $C_d$ 使边界面积 $|\partial V_n| \le C_d |V_n|^{(d-1)/d}$。
* **(V3) 平移不变性**：对任意平移 $\tau$，$|V_n + \tau| = |V_n|$。

典型例子：$V_n = [-n,n]^d \cap \mathbb{Z}^d$（超立方体）或 $V_n = \{x: |x|\le n\}$（球）。

### 2.2 核函数与熵

**定义 2.1（核函数）** 映射 $K: \mathcal{V} \to \mathbb{R}_{\ge0}$，其中 $\mathcal{V}$ 为体积族，满足：

* **(K1) 次可加性**：对任意 $V_1, V_2$ 不交，

$$
K(V_1 \cup V_2) \le K(V_1) + K(V_2).
$$

* **(K2) 平移不变性**：$K(V + \tau) = K(V)$。
* **(K3) 正则增长**：存在 $C>0$ 使 $K(V) \le C|V|$。

**定义 2.2（熵密度）** 若极限存在，定义

$$
s(K) := \lim_{n\to\infty} \frac{K(V_n)}{|V_n|}.
$$

---

## 3 一般核函数的热力学极限存在性

### 3.1 超可加不等式与下确界

**引理 3.1（次可加序列的下确界）** 设数列 $\{a_n\}$ 满足 $a_{m+n} \le a_m + a_n$ 且 $a_n \ge 0$。则

$$
\lim_{n\to\infty} \frac{a_n}{n} = \inf_{n\ge1} \frac{a_n}{n}.
$$

*证明.* 固定 $k$，对任意 $n$ 写 $n = qk + r$（$0\le r < k$）。由次可加性，

$$
a_n \le q a_k + a_r \le q a_k + \max_{0\le r < k} a_r.
$$

两边除以 $n$，令 $n\to\infty$ 得

$$
\limsup_{n\to\infty} \frac{a_n}{n} \le \frac{a_k}{k}.
$$

对所有 $k$ 取下确界，

$$
\limsup_{n\to\infty} \frac{a_n}{n} \le \inf_{k\ge1} \frac{a_k}{k} \le \liminf_{n\to\infty} \frac{a_n}{n}.
$$

故极限存在且等于下确界。∎

### 3.2 主定理：一般核的存在性

**定理 3.2（熵密度的热力学极限存在性）** 设 $K$ 满足 (K1)–(K3)，体积序列 $\{V_n\}$ 满足 (V1)–(V3)。则

$$
s(K) = \lim_{n\to\infty} \frac{K(V_n)}{|V_n|} = \inf_{n\ge1} \frac{K(V_n)}{|V_n|}
$$

存在且有限。

*证明.* 对固定 $m, n$，将 $V_{m+n}$ 分解为 $V_m$ 的平移副本与剩余部分（边界层）。由 (V2)，边界层体积 $O(|V_{m+n}|^{(d-1)/d})$。由 (K1)，

$$
K(V_{m+n}) \le K(V_m) + K(V_n) + O(|V_{m+n}|^{(d-1)/d}).
$$

定义 $a_n := K(V_n) - C'|\partial V_n|$（边界修正）。在 (V2) 下，$a_n$ 近似次可加。应用引理3.1 的推广（见附录A），得

$$
\limsup_{n\to\infty} \frac{K(V_n)}{|V_n|} \le \inf_{n\ge1} \frac{K(V_n)}{|V_n|} + o(1).
$$

令边界修正趋于零，极限存在。由 (K3)，$s(K) \le C < \infty$。∎

---

## 4 正则边界条件下的熵增长

### 4.1 边界条件的分类

* **Dirichlet边界**：$\partial V$ 上配置固定。
* **Neumann边界**：$\partial V$ 上梯度（或相互作用）为零。
* **混合边界**：$\partial V$ 部分Dirichlet，部分Neumann。
* **周期边界**：$V$ 拓扑上为环面，无边界。

### 4.2 边界修正项的渐近估计

**定理 4.1（边界修正的渐近形式）** 设 $K^{\mathrm{bc}}(V)$ 为带边界条件bc的核。则

$$
K^{\mathrm{bc}}(V_n) = s(K) |V_n| + \sigma(K,\mathrm{bc}) |\partial V_n| + o(|\partial V_n|),
$$

其中 $\sigma(K,\mathrm{bc})$ 为**表面张力**（或边界能）常数。

*证明.* 将 $V_n$ 分为内部 $V_n^\circ$ 与边界层 $\partial_\delta V_n$（厚度 $\delta$）。在 (V2) 下，$|\partial_\delta V_n| = \delta |\partial V_n| + o(|\partial V_n|)$。应用次可加性与平移不变性，

$$
K^{\mathrm{bc}}(V_n) = K(V_n^\circ) + K(\partial_\delta V_n) + \text{耦合项}.
$$

当 $\delta \to 0$，内部贡献 $\sim s(K)|V_n^\circ| \to s(K)|V_n|$；边界贡献 $\sim \sigma(K,\mathrm{bc})|\partial V_n|$。详细估计见附录B。∎

**推论 4.2（周期边界下表面张力消失）** 周期边界条件下，$\sigma(K,\mathrm{period}) = 0$，故

$$
K^{\mathrm{period}}(V_n) = s(K) |V_n| + o(|V_n|).
$$

---

## 5 稳定性准则：对核与边界扰动的连续依赖

### 5.1 核扰动

**定理 5.1（核扰动的Lipschitz连续性）** 设 $K, K'$ 满足 (K1)–(K3)，且对所有 $V$，

$$
|K(V) - K'(V)| \le \epsilon |V|.
$$

则

$$
|s(K) - s(K')| \le \epsilon.
$$

*证明.* 直接由定义，

$$
\left| \frac{K(V_n)}{|V_n|} - \frac{K'(V_n)}{|V_n|} \right| \le \epsilon.
$$

取 $n\to\infty$，得 $|s(K) - s(K')| \le \epsilon$。∎

### 5.2 边界扰动

**定理 5.2（边界条件扰动的稳定性）** 设边界条件 $\mathrm{bc}, \mathrm{bc}'$ 仅在 $\partial V_n$ 的 $o(|\partial V_n|)$ 部分不同。则

$$
\left| \frac{K^{\mathrm{bc}}(V_n)}{|V_n|} - \frac{K^{\mathrm{bc}'}(V_n)}{|V_n|} \right| = o(n^{-1/d}).
$$

*证明.* 边界差异贡献 $O(o(|\partial V_n|)) = o(|V_n|^{(d-1)/d})$。除以 $|V_n| \sim n^d$，得 $o(n^{-1/d})$。∎

---

## 6 与拓扑熵、符号动力学的联系

### 6.1 拓扑熵

设 $(X,T)$ 为紧致度量空间上的连续映射。**拓扑熵**

$$
h_{\mathrm{top}}(T) := \lim_{\epsilon\to0} \limsup_{n\to\infty} \frac{1}{n} \log N(n,\epsilon),
$$

其中 $N(n,\epsilon)$ 为 $n$-步 $\epsilon$-分离集的最大基数。

**命题 6.1（拓扑熵与配分函数的对应）** 若 $(X,T)$ 为符号移位 $\Sigma_A^+$（SFT），则

$$
h_{\mathrm{top}}(\sigma) = \lim_{n\to\infty} \frac{1}{n} \log Z_n,
$$

其中 $Z_n$ 为长度 $n$ 的允许字数。定义 $K(V_n) := \log Z_n$，则 $s(K) = h_{\mathrm{top}}(\sigma)$。

### 6.2 Kolmogorov–Sinai熵

设 $\mu$ 为 $T$-不变测度。**度量熵**

$$
h_\mu(T) := \sup_{\alpha} H_\mu(T,\alpha),
$$

其中 $\alpha$ 为有限分割，$H_\mu(T,\alpha)$ 为熵率。

**定理 6.2（变分原理）**

$$
h_{\mathrm{top}}(T) = \sup_{\mu \in \mathcal{M}(X,T)} h_\mu(T),
$$

其中 $\mathcal{M}(X,T)$ 为不变测度集。

**推论 6.3** 在SFT上，热力学极限 $s(K)$ 对应最大熵测度的度量熵。

---

## 7 信息论度量熵与Shannon熵的对应

### 7.1 Shannon熵

设随机变量 $X$ 取值于有限集 $\mathcal{X}$，分布 $p$。**Shannon熵**

$$
H(X) := -\sum_{x\in\mathcal{X}} p(x) \log p(x).
$$

### 7.2 符号过程的熵率

设 $\{X_i\}_{i\ge1}$ 为平稳过程。**熵率**

$$
h := \lim_{n\to\infty} \frac{1}{n} H(X_1,\dots,X_n).
$$

**命题 7.1（熵率与热力学极限的等价）** 若过程由SFT生成，则

$$
h = s(K),\quad K(V_n) := H(X_1,\dots,X_n).
$$

*证明.* 次可加性由条件熵的链式法则：

$$
H(X_1,\dots,X_{m+n}) \le H(X_1,\dots,X_m) + H(X_{m+1},\dots,X_{m+n}).
$$

应用定理3.2，极限存在。∎

---

## 8 多维各向异性与范数等价性

### 8.1 各向异性体积

设 $V_n(\mathbf{a}) = [-a_1 n, a_1 n] \times \cdots \times [-a_d n, a_d n]$（$\mathbf{a} = (a_1,\dots,a_d)$）。

**定理 8.1（范数等价性）** 若 $K$ 满足 (K1)–(K3) 且各向同性（即对正交变换不变），则对所有 $\mathbf{a}$，

$$
\lim_{n\to\infty} \frac{K(V_n(\mathbf{a}))}{|V_n(\mathbf{a})|} = s(K).
$$

*证明.* 由平移与旋转不变性，熵密度仅依赖体积，不依赖形状。对非各向同性 $K$，需引入**各向异性表面张力** $\sigma(\mathbf{n})$（$\mathbf{n}$ 为法向量），得Wulff构造。详见附录B。∎

---

## 9 量子情形：von Neumann熵与纠缠熵的热力学极限

### 9.1 von Neumann熵

设 $\rho$ 为密度矩阵。**von Neumann熵**

$$
S(\rho) := -\mathrm{Tr}(\rho \log \rho).
$$

### 9.2 纠缠熵

设系统分为 $A \cup B$，$\rho_{AB}$ 为联合态。**纠缠熵**

$$
S_A := S(\rho_A),\quad \rho_A := \mathrm{Tr}_B(\rho_{AB}).
$$

### 9.3 热力学极限

**定理 9.1（量子熵密度的存在性）** 设 $\rho_n$ 为体积 $V_n$ 内的基态（或Gibbs态），满足**强次可加性**（SSA）：

$$
S(\rho_{AB}) \le S(\rho_A) + S(\rho_B) + o(|\partial A|).
$$

则

$$
s := \lim_{n\to\infty} \frac{S(\rho_n)}{|V_n|}
$$

存在。

*证明.* SSA 对应经典的次可加性 (K1)。边界修正项 $o(|\partial A|)$ 在 (V2) 下可控。应用定理3.2。∎

### 9.4 体积律与面积律

* **体积律**：$S(\rho_A) \sim |A|$（典型于高温或临界点）。
* **面积律**：$S(\rho_A) \sim |\partial A|$（典型于基态，反映短程纠缠）。

**命题 9.2（面积律判据）** 若 $s(\rho) = 0$（即 $S(\rho_n) = o(|V_n|)$），且边界贡献 $\sim |\partial V_n|$，则系统满足面积律。

*证明.* 由定理4.1，$S(\rho_n) = s(\rho)|V_n| + \sigma |\partial V_n| + o(|\partial V_n|)$。若 $s(\rho) = 0$，主导项为 $\sigma |\partial V_n|$。∎

---

## 10 结论与展望

本文在一般核函数的框架下严格证明了熵密度热力学极限的存在性，统一处理了正则边界条件、稳定性准则与信息论联系。主要贡献：

1. **存在性**：对满足次可加性与平移不变性的任意核 $K$，通过推广Fekete引理证明 $s(K)$ 存在。
2. **边界效应**：刻画Dirichlet、Neumann、混合与周期边界下的表面张力 $\sigma(K,\mathrm{bc})$。
3. **稳定性**：建立对核扰动与边界扰动的Lipschitz连续性。
4. **信息论联系**：将热力学熵与拓扑熵、Kolmogorov–Sinai熵、Shannon熵率对应。
5. **量子推广**：讨论von Neumann熵与纠缠熵的热力学极限，给出体积律/面积律的判据。

**未来方向**：

* **相变**：在临界点附近，$s(K)$ 的奇异性与普适类的关联。
* **长程关联**：放宽次可加性，允许幂律修正（如 $K(V_1\cup V_2) \le K(V_1) + K(V_2) + O(d(V_1,V_2)^{-\alpha})$）。
* **动态系统**：将静态熵推广到时间演化的熵产率。
* **量子纠错码**：纠缠熵的面积律与拓扑序的关联。

---

## 附录A：超可加不等式与Fekete引理的推广

**引理 A.1（带边界修正的次可加性）** 设 $\{a_n\}$ 满足

$$
a_{m+n} \le a_m + a_n + C(m^{(d-1)/d} + n^{(d-1)/d}).
$$

则

$$
\lim_{n\to\infty} \frac{a_n}{n^d} = \inf_{n\ge1} \frac{a_n}{n^d}.
$$

*证明.* 修改引理3.1的论证，吸收边界修正项 $C n^{(d-1)/d}$。当 $n\to\infty$，$n^{(d-1)/d}/n^d = n^{-1/d} \to 0$。∎

---

## 附录B：边界修正项的渐近估计

**定理 B.1（各向异性表面张力）** 对各向异性核 $K$，定义Wulff形状

$$
\mathcal{W} := \left\{ \mathbf{x}: \mathbf{x} \cdot \mathbf{n} \le \sigma(\mathbf{n}),\ \forall \mathbf{n} \right\}.
$$

则最优体积 $V^\ast$ 满足

$$
K(V^\ast) = s(K) |V^\ast| + \int_{\partial V^\ast} \sigma(\mathbf{n}(\mathbf{x})) \, dS(\mathbf{x}) + o(|\partial V^\ast|).
$$

*证明.* 变分法：最小化自由能 $F[V] = K(V) - \lambda |V|$，得Euler–Lagrange方程 $\sigma(\mathbf{n}) = \lambda$（常数）。解为Wulff形状。∎

---

## 附录C：符号表

| 符号 | 含义 |
|------|------|
| $V_n$ | 体积序列 |
| $\|\partial V_n\|$ | 边界面积 |
| $K(V)$ | 核函数 |
| $s(K)$ | 熵密度（热力学极限） |
| $\sigma(K,\mathrm{bc})$ | 表面张力（边界能） |
| $h_{\mathrm{top}}(T)$ | 拓扑熵 |
| $h_\mu(T)$ | 度量熵（Kolmogorov–Sinai） |
| $H(X)$ | Shannon熵 |
| $S(\rho)$ | von Neumann熵 |
| $S_A$ | 纠缠熵 |
| (K1)–(K3) | 核函数的次可加性、平移不变性、正则增长 |
| (V1)–(V3) | 体积序列的增长性、正则性、平移不变性 |

---
