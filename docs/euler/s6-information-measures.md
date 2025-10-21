# S6. 信息量刻度

**—— 相位层守恒、尺度/离散层对偶与 $\Lambda$–$\Lambda^\ast$ 的凸几何**

## 摘要（定性）

在 S2–S5 的几何—解析基座上，本文建立母映射的**信息量刻度**：以软最大（log-sum-exp）势函数 $\Lambda(\rho)$ 及其凸对偶 $\Lambda^\ast$ 为核心，系统定义并分析熵 $H$、有效模态数 $N_{\mathrm{eff}}=e^H$ 与参与率 $N_2=(\sum p_j^2)^{-1}$ 的结构性质；证明**相位层酉变换不改变刻度**（守恒），而尺度/离散层在自然流形上形成**凸分析对偶**，其梯度—Hessian 分别给出"有效模态质心"与"协方差度量"；建立 Bregman–KL 恒等式与方向（切片）上的导数/方差公式，从而与 S2 的横截零几何、S3 的 $\Gamma/\pi$ 正规化、S4 的"极点 = 主尺度"及 S5 的方向亚纯化实现一致拼接与互补。

---

## 0. 记号与前置（与 S2/S3/S4/S5 对齐）

**离散谱与软最大势。** 在母映射的离散谱表述

$$
F(\theta,\rho)=\sum_{j=1}^J c_j\,e^{i\langle \alpha_j,\theta\rangle}e^{\langle \beta_j,\rho\rangle},\qquad
w_j:=|c_j|>0,\ \ \beta_j\in\mathbb R^n,
$$

上定义

$$
\Lambda(\rho):=\log\Big(\sum_{j=1}^J w_j\,e^{\langle \beta_j,\rho\rangle}\Big),\qquad
p_j(\rho):=\frac{w_j\,e^{\langle \beta_j,\rho\rangle}}{e^{\Lambda(\rho)}}.
$$

则 $p(\rho)=(p_j(\rho))_{j=1}^J$ 为刻度上的概率向量。S2 的二项闭合与横截用于零集局部几何，不影响 $\Lambda$ 的凸性与下述熵结构。

**信息量刻度量。**

$$
H(\rho):=-\sum_{j=1}^J p_j(\rho)\log p_j(\rho),\qquad
N_{\mathrm{eff}}(\rho):=e^{H(\rho)},\qquad
N_2(\rho):=\Big(\sum_{j=1}^J p_j(\rho)^2\Big)^{-1}.
$$

**与镜像/延拓的相容性。** S3 的 $\Gamma/\pi$ 正规化与完成函数只乘一个不依赖 $j$ 的整体标量，不改变 $p_j$ 的归一化；S4 的有限阶 Euler–Maclaurin（EM）仅叠加整函数层，不改离散数据 $(\beta_j,w_j)$；S5 的方向切片 $\rho=\rho_\perp+s\mathbf v$ 可直接代入本节公式。

**基本可积域假设（S1 管域对齐）。** 存在非空开集 $\mathcal T\subset\mathbb R^n$ 使得对所有 $\rho\in\mathcal T$，有 $\sum_j w_j e^{\langle \beta_j,\rho\rangle}<\infty$。本文一律在 $\mathcal T$ 内讨论。并且，为保证对 $\rho$ 的一、二阶导数与求和（或极限）可交换，存在包含 $\rho$ 的邻域 $\mathcal U\subset\mathcal T$，使
$$
\sum_j w_j\,|\beta_j|\,e^{\langle\beta_j,\rho'\rangle}<\infty,\qquad
\sum_j w_j\,|\beta_j|^2\,e^{\langle\beta_j,\rho'\rangle}<\infty,
$$

$$
\sum_j w_j\,|y_j|\,e^{\langle\beta_j,\rho'\rangle}<\infty,\qquad
\sum_j w_j\,|\beta_j|\,|y_j|\,e^{\langle\beta_j,\rho'\rangle}<\infty\quad(\forall\rho'\in\mathcal U),
$$

其中 $y_j=\log w_j$。据此，§2 的梯度—Hessian 恒等式与 §5 的方向导数/方差律严格成立。

---

## 1. 相位层守恒与刻度的规约不变性

### 定理 6.1（相位—完成函数—伯努利层对刻度的守恒）

本节之刻度 $\Lambda,H,N_{\mathrm{eff}},N_2$ 仅由 §0 所定的离散谱数据 $(\beta_j,\,w_j)$ 定义；S4 的有限阶 EM 仅叠加整函数层，不改变 $(\beta_j,\,w_j)$。

在固定 $\rho\in\mathcal T$ 下，以下操作均保持 $p(\rho)$ 及 $(H,N_{\mathrm{eff}},N_2)$ 不变：

1. **相位层酉变换**：$(c_j,\alpha_j)\mapsto (c_j e^{i\phi_j},\alpha_j+\delta\alpha_j)$；
2. **完成函数正规化**：$F\mapsto r(s)\,F$，其中 $r$ 为满足 $r(s)=r(a-s)$ 的 $\Gamma/\pi$ 因子；
3. **有限阶 EM 校正**：叠加 S4 的有限阶伯努利层与余项整函数。

*证明.* $p_j(\rho)$ 仅依赖 $w_j=|c_j|$、$\beta_j$ 与当前 $\rho$。操作 1) 改变相位不改模；2) 乘以对 $j$ 不变的因子在分子分母同消；3) 不改变 $(w_j,\beta_j)$。故得。∎

---

## 2. 软最大势的凸结构与"质心—协方差"律

### 定理 6.2（梯度—Hessian 恒等式）

$$
\nabla_\rho \Lambda(\rho)=\sum_{j=1}^J p_j(\rho)\,\beta_j=:\mathbb E_\rho[\beta],\qquad
\nabla_\rho^2 \Lambda(\rho)=\operatorname{Cov}_\rho(\beta):=\mathbb E_\rho\big[(\beta-\mathbb E_\rho\beta)(\beta-\mathbb E_\rho\beta)^\top\big]\succeq 0.
$$

因此 $\Lambda$ 凸；$\nabla\Lambda$ 给出以 $p(\rho)$ 为权的"有效模态质心"，Hessian 为"协方差度量"。

*证明.* 直接对 $\Lambda=\log\sum_j w_j e^{\langle \beta_j,\rho\rangle}$ 求导并标准化得一阶式；对 $p_j$ 再求导得二阶式。协方差半正定显然。∎

### 推论 6.3（方向方差律）

沿 S5 的方向切片 $\rho=\rho_\perp+s\mathbf v$ 有

$$
\frac{d^2}{ds^2}\Lambda(\rho_\perp+s\mathbf v)=\operatorname{Var}_\rho\big(\langle \beta,\mathbf v\rangle\big)\ge 0.
$$

故 $\Lambda$ 关于 $s$ 的凸性由投影方差控制；解析侧的"极点由主尺度决定"（S4/S5）与几何侧的"增长由方差给界"互补。

---

## 3. 熵、有效模态数与参与率：不等式与等价条件

### 命题 6.4（刻度不等式链）

对任意 $\rho\in\mathcal T$ 与有限 $J$：

$$
1\ \le\ N_2(\rho)\ \le\ N_{\mathrm{eff}}(\rho)\ \le\ J,\qquad
\log N_2(\rho)\ \le\ H(\rho)\ \le\ \log J.
$$

等号情形：
— $N_2=N_{\mathrm{eff}}=J$ 当且仅当 $p_j\equiv 1/J$（全均匀）；
— $N_2=N_{\mathrm{eff}}=1$ 当且仅当 $p$ 为某一模态的单位向量（全集中）。

*证明.* 由 Hölder 与 $\sum p_j^2\ge e^{-H}$ 得第一条；Jensen 给出 $H\le\log J$。等号条件由均匀/集中分布判别。∎

---

## 4. $\Lambda$ 的变分表征与对偶 $\Lambda^\ast$

【适用域说明】本节假定 $J<\infty$；或 $J$ 可数但 $W:=\sum_j w_j<\infty$（从而 $\pi$ 为良定义的基准分布）。当 $W=\infty$ 时，以下变分/对偶式不直接适用（需改以 $\sigma$-有限基准测度的连续型表述，本文不展开）。在可数 $J$ 且 $W<\infty$ 的情形，以上变分/对偶式中的最优解 $q^\star$ 存在且唯一；若允许 $u$ 在闭凸包边界，见上文关于相对内部/边界的补充说明。

记 $W:=\sum_{j=1}^J w_j$、$\pi_j:=w_j/W$（基准分布），$\Delta_J$ 为 $J$ 维概率单纯形。

### 定理 6.5（Gibbs 变分）

$$
\Lambda(\rho)=\log W+\sup_{q\in\Delta_J}\Big\{\big\langle \rho,\ \mathbb E_q[\beta]\big\rangle - D(q\,|\,\pi)\Big\},
$$

其中 $D(q\,|\,\pi)=\sum_j q_j\log\frac{q_j}{\pi_j}$ 为 KL 散度。极值 $q^\star=p(\rho)$。

*证明.* 经典 log-sum-exp 变分式：$\log\sum_j \pi_j e^{\langle \rho,\beta_j\rangle}=\sup_q\{\langle \rho,\mathbb E_q[\beta]\rangle - D(q\,|\,\pi)\}$。乘回 $W$ 并取对数即得。最优性由一阶条件给出 $q^\star=p(\rho)$。∎

### 定义 6.6（凸对偶）

$$
\Lambda^\ast(u):=\sup_{\rho\in\mathbb R^n}\big\{\langle u,\rho\rangle-\Lambda(\rho)\big\},\qquad
u\in\overline{\operatorname{conv}}\{\beta_1,\dots,\beta_J\}\text{（闭凸包）}.
$$

### 定理 6.7（$\Lambda^\ast$ 的熵型表示）

$$
\Lambda^\ast(u)=\ \inf_{\substack{q\in\Delta_J\\ \mathbb E_q[\beta]=u}}\Big\{D(q\,|\,\pi)\Big\}\ -\ \log W.
$$

当 $u$ 落在 $\overline{\operatorname{conv}}\{\beta_j\}$ 的**相对内部**时，存在 $\rho$ 使 $\nabla\Lambda(\rho)=u$；**若** $\operatorname{aff}\{\beta_j\}$ **张满** $\mathbb R^n$，则该 $\rho$ **唯一**；**一般情形** $\rho$ 仅在 $\operatorname{aff}\{\beta_j\}$ 上唯一（沿其正交补的平移不改变 $p(\rho)$ 与 $\nabla\Lambda(\rho)$），而极小解 $q^\star$ 仍唯一。此时极小解由 $q^\star=p(\rho)$ 给出；若 $u$ 在边界上，则一般不存在有限的 $\rho$ 使 $\nabla\Lambda(\rho)=u$，但极小化问题仍有解（可由逼近序列 $\rho_k\to\infty$ 获得极限分布 $q^\star$）。

*证明.* 对定理 6.5 作 Fenchel 变换并引入线性约束 $\mathbb E_q[\beta]=u$。∎

### 推论 6.8（Bregman–KL 恒等式）

对任意 $\rho,\rho'\in\mathcal T$，有

$$
B_\Lambda(\rho'\mid\rho):=\Lambda(\rho')-\Lambda(\rho)-\langle \nabla\Lambda(\rho),\rho'-\rho\rangle
= D\big(p(\rho)\,|\,p(\rho')\big).
$$

故刻度上的"势能差"正等于两刻度分布的 KL 散度。∎

---

## 5. 熵的导数结构与方向公式

设 $y_j:=\log w_j$。利用

$$
H(\rho)=\Lambda(\rho)-\big\langle \rho,\ \mathbb E_\rho[\beta]\big\rangle-\sum_{j=1}^J p_j(\rho)\,y_j,
$$

可得：

### 命题 6.9（熵梯度与方向导数）

$$
\nabla_\rho H(\rho)= -\operatorname{Cov}_\rho(\beta)\,\rho\ -\ \operatorname{Cov}_\rho(\beta,\ y),
$$

其中 $\operatorname{Cov}_\rho(\beta,\ y):=\sum_j p_j(\rho)\,(\beta_j-\mathbb E_\rho\beta)\,(y_j-\mathbb E_\rho y)$。沿方向 $\mathbf v$ 的切片 $\rho=\rho_\perp+s\mathbf v$ 上，

$$
\frac{d}{ds}H(\rho_\perp+s\mathbf v)= -\,\mathbf v^\top\operatorname{Cov}_\rho(\beta)\,\rho\ -\ \big\langle \operatorname{Cov}_\rho(\beta,\ y),\ \mathbf v\big\rangle.
$$

若 $w_j$ 等幅（即 $y$ 常数），第二项消失，熵随尺度流的变化完全由 $\operatorname{Cov}_\rho(\beta)$ 控制。上述方向化与 S5 兼容，而 S4 的有限阶 EM 不改变 $(w,\beta)$，故不影响此导数结构。∎

---

## 6. $\zeta$ 的刻度特例（结构陈述）

以下等式在 $\sigma>1$ 成立。取 $\mu=\sum_{n\ge 1}\delta_{(\log n,\,-\log n)}$，令 $(\theta,\rho)=(-t,\sigma)$ 得 $\zeta(\sigma+it)$（此时 $W=\sum_n w_n=\infty$，故本节**不**调用 §4 的变分/对偶结果，仅依 §2 的导数—方差律与 §0 的矩条件的一维版本推导）。于是

$$
w_n\equiv 1,\qquad \beta_n=-\log n,\qquad
p_n(\sigma)=\frac{n^{-\sigma}}{\sum_{m\ge 1} m^{-\sigma}}=\frac{n^{-\sigma}}{\zeta(\sigma)}.
$$

因此

$$
\Lambda(\sigma)=\log\zeta(\sigma),\quad
\Lambda'(\sigma)=-\mathbb E_\sigma[\log n],\quad
\Lambda''(\sigma)=\operatorname{Var}_\sigma(\log n)\ \ge 0,
$$

且

$$
H(\sigma)=\log\zeta(\sigma)+\sigma\,\mathbb E_\sigma[\log n].
$$

在等幅权情形，命题 6.9 的 $\operatorname{Cov}_\rho(\beta,y)$ 项为零。该刻度与 S3 的完成函数正规化、S4 的 EM 余项整函数相容（均不改 $(w_n,\beta_n)$），而方向化（S5）对应一维切片 $\mathbf v=1$。

---

## 7. 边界与反例

**R6.1（非可归一化）。** 若 $\sum_j w_j e^{\langle \beta_j,\rho\rangle}=\infty$，则 $p(\rho)$ 不存在，刻度未定义；这对应 S5 的收敛半平面之外或 S4 中主尺度发散情形。

**R6.2（相位参与的失当）。** 若误将复系数 $c_j$（含相位）直接用于归一化而非 $w_j=|c_j|$，则 $p_j$ 可能不为实非负，刻度失去意义；与定理 6.1 的相位守恒原则相悖。

**R6.3（无界异质权）。** 若 $y_j=\log w_j$ 在 $\rho$ 族上导致 $\operatorname{Cov}_\rho(\beta,y)$ 不可控，则命题 6.9 的方向导数可能不收敛；需以 S1/S4 的管域与端点正则确保换序与可积。

---

## 8. 统一"可检清单"（本篇最小充分条件）

1. **归一化存在：** 存在 $\rho$ 使 $\Lambda(\rho)<\infty$，从而 $p(\rho)$ 定义良好（与 S5 的收敛半平面一致）。
2. **相位规约：** 仅以 $w_j=|c_j|$ 入式；任何 $\Gamma/\pi$ 正规化或相位变换不进入 $p$ 的分子（守恒）。
3. **凸对偶：** 使用定理 6.5–6.7 的变分与对偶式（必要时验证极值 $q^\star=p(\rho)$）。
4. **方向化：** 在 $\rho=\rho_\perp+s\mathbf v$ 上使用方差律与命题 6.9 的方向导数；若需解析延拓，调用 S5 的亚纯化与 S4 的"极点 = 主尺度"。
5. **不等式核查：** 核对 $N_2\le N_{\mathrm{eff}}\le J$ 及等号条件（命题 6.4）。
6. **$\zeta$ 特例：** 记 $p_n(\sigma)=n^{-\sigma}/\zeta(\sigma)$，使用 $\Lambda'=-\mathbb E[\log n]$、$\Lambda''=\operatorname{Var}(\log n)$ 与命题 6.9 的简化式。

---

## 9. 与其它篇章的接口

**→ S2（零集几何）。** 刻度不改变余维 $2$ 的横截结构，但提供"局部主导项"的定量指示（平衡超平面附近 $p_j$ 可比），与二项闭合的局部几何互补。

**→ S3（完成函数）。** 刻度与正规化正交；完成函数改变整体增长与条带对称，不改 $p$ 及其导数结构。

**→ S4（有限阶 EM）。** 伯努利层与余项整函数不改变刻度；主尺度项的极点消除/延拓与刻度的可归一化域相容。

**→ S5（方向亚纯化）。** $\Lambda$ 的方向凸性与方差律为极点定位提供"增长侧"信息，构成"主尺度—极点 / 质心—方差"的拼接。

**→ S7（$L$-函数接口）。** 变分式为本地/无穷处因子下的**试验核选择准则**（最大化/约束化 $\mathbb E_q[\beta]$ 或最小化 $D(q\,|\,\pi)$）。

**→ S8（离散一致逼近）。** $N_{\mathrm{eff}},N_2$ 可作离散近似的"有效自由度/复杂度"指标；EM 的有限阶误差层不改变其数值解释。

**→ S9/S10（指数和与几何增长）。** $\Lambda$ 的 Hessian/方差与 S10 的 Ronkin 凸性同构，可约束 S9 的近零复访与集中不等式（此处不展开）。

---

## 结语

信息量刻度以 $\Lambda(\rho)$ 的凸几何为纽带，将相位—尺度母映射的离散谱数据 $(w_j,\beta_j)$ 统一折射为"质心—协方差—熵"的统计三元组：相位层守恒、尺度/离散层对偶、方向方差律与 Bregman–KL 恒等式共同构成一套可检、可拼接的"信息—几何—解析"词典。该词典既与 S2 的横截零几何、S3 的完成函数、S4 的有限阶延拓、S5 的方向亚纯化兼容，又为后续 $L$-函数接口与一致逼近中的核选择和复杂度评估提供统一指标与方法论。∎
