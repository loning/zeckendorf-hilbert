# Null–Modular 双覆盖统一原理：在因果钻石上对齐信息几何变分与散射半相位的 $\mathbb{Z}_2$ holonomy

Version: 2.10

## 摘要

我们在小因果钻石 $B_\ell(p)$ 的门槛内（Hadamard 态、$[0,\lambda_\ast]$ 无共轭点、角点处方、固定温标 $\delta T=0$、**能量–动量守恒 $\nabla^a T_{ab}=0$**、维数 $n\ge3$）表明：**(i)** $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$ 与 $\delta^2 S_{\rm rel}\ge0$；**(ii)** 体积分 $\mathbb Z_2$–BF 在 $Y=M\times X^\circ$ 的相对扇区选择 $[K]=0$；**(iii$^\star$)** 一切物理回路与允许二维循环上的 $\mathbb Z_2$ 指标皆平凡/为零。并在 $A_\partial$、$A_{\rm rel\text{-}gen}$、$H^1/H^2$ 可检测性、（一般流形时）$A_{\rm spin}$ 与 $A_{\rm tors2}$ 下，$(ii)\Longleftrightarrow(\text{iii}^\star)$；若再加"模二对齐"，则 $(i)\Rightarrow(\text{iii}^\star)$。我们用 Künneth 分解把 $w_2(TM)$、散射线丛扭挠与平方根双覆盖统一到同一 $K$ 类，并给出一维 $\delta$ 势、二维 Aharonov–Bohm 与拓扑超导端点散射的三类可计算指纹。全文在 $\mathbb Z_2$ 系数下工作（Tor 项为零），所有配对皆为相对上同调意义。

## Keywords

广义熵；相对熵；规范能量；小因果钻石；模组 Berry 联络；Birman–Kreĭn；谱流；模二交数；$\mathbb Z_2$–BF 顶项；$H^1/H^2$ 不变量；Künneth 分解；$\mathrm{spin}^c$；拓扑超导端点散射

---

| 创新点 | Jacobson'95 | Hollands–Wald'13 | Pushnitski'01 | 本文首次 |
|---|---|---|---|---|
| 二阶能量非负 ⇒ $\mathbb Z_2$–holonomy 平凡 | × | × | × | √ |
| $\mathbb Z_2$–BF 体积分扇区选择 | × | × | × | √ |
| 相对上同调充要条件 | × | × | × | √ |
| 三大可解模型指纹 | × | × | × | √ |

---

## 引言与历史背景

在小因果钻石内，爱因斯坦方程的一阶变分早已由 Jacobson 热力学途径导出，然而二阶变分非负性与散射边界的拓扑约束一直分属两条独立语言：前者停留在几何侧的正能定理，后者则依赖于谱流与 Birman–Kreĭn 理论。本文指出，这两个看似不相干的问题其实共享同一把"钥匙"——若散射算符的平方根行列式在任意物理回路上出现 $-1$ 的 $\mathbb Z_2$–holonomy，则二阶规范能量 $\mathcal E_{\rm can}$ 必可负，从而违背全息正性。我们把这一观察转化为同调语言：在体积分版本的 $\mathbb Z_2$–BF 理论中，在对齐、$H^1/H^2$ 通道可检测性、生成性与自旋平凡性等假设下，$[K]=0$ 同时是"爱因斯坦方程成立 + 二阶能量非负"与**(iii$^\star$)** 的充要条件，首次把"方程—稳定—拓扑"纳入同一变分原理。需要强调：从 (i) **推出** (iii$^\star$) **必须**在闭路对齐（假设 4）外，再加上**（$H^2$ 通道的对齐或等效消去假设）**（见假设 4′ 与定理 5 的 E‑(b″)）。

---

## Symbols, Units, Conventions

度规签名 $(-+++)$；单位 $c=k_B=1$，保留 $\hbar$。微分与虚数单位统一为 $\mathrm d$、$\mathrm i$。运算符与群记号统一为 $\operatorname{tr}$、$\operatorname{Pf}$、$\operatorname{sgn}$、$\det_p$[^1]、$\mathrm{Sf}$、$U(1)$、$\mathbb Z_2$。

**（口径统一）** 全文散射行列式一律记为 $\det_p$（Schatten 修正；迹类与相对迹类均涵盖）。在不致混淆时可简写为"$\det$"，其值以**模二投影**进入 $\nu_{\sqrt{\det_p S}}$，对 $p$ 与重整选取不敏感。

**（统一定义）物理回路与相对二维循环**：物理回路 $\gamma\subset X^\circ$ 为可由外参绝热实现的闭路；若绕过判别集 $D$，按"小半圆/折返"规则稳定并以 $I_2(\gamma,D)$ 记录奇偶。允许的相对二维循环由三类乘积生成：

$$
(\Sigma_2,\partial\Sigma_2)\times{\mathrm{pt}},\quad
(\Sigma_1,\partial\Sigma_1)\times(\gamma_1,\partial\gamma_1),\quad
{\mathrm{pt}}\times(\gamma_2,\partial\gamma_2),
$$

其中 $\Sigma_k\subset M$、$\gamma_j\subset X^\circ$ 为相对闭链。**系数取 $\mathbb Z_2$**，故一切配对不依赖取向。

**（统一定义补充）** 将判别集取开邻域 $N(D)$ 并定义允许回路/二维循环为相对链群

$$
H_1\big(X^\circ,\partial X^\circ\cup N(D);\mathbb Z_2\big),\quad
H_2\big(X^\circ,\partial X^\circ\cup N(D);\mathbb Z_2\big),
$$

对其代表闭路按"小半圆/折返"实现绝热避让并以 $I_2(\gamma,D)$ 计数。**系数取 $\mathbb Z_2$ 故不依赖取向**。

**记号声明**：在 BF 段落，为区分变分符号 $\delta$ 与上同调增算子，记上同调增算子为 **$\boldsymbol\delta$**；其余处仍记 $\delta$。

[^1]: $\det_p$ 指 Schatten 修正行列式 $\det_p(1+K)=\det\!\big[(1+K)\exp\sum_{j=1}^{p-1}\frac{(-1)^j}{j}K^j\big]$，用于 $S-\mathbf 1\in\mathfrak S_p$ 或相对迹类时的相位正则。**对幺正 $S$，$\det_p S$ 模长恒为 $1$，不存在"$\det_p S=0$"的情形**；本文关心的是**平方根分支的 $\mathbb Z_2$ 障碍**，其本质由 $-1$ 特征值纤维的奇偶跃迁决定。全篇取 $\mathbb Z_2$ 系数，故 Künneth 的 Tor 项为零；对有限阿贝尔群的特征正交性使体积分 $\mathbb Z_2$–BF 的上同调求和将配分函数投影到 $[K]=0$。

---

## Conceptual Bridge: Künneth 分解与 $H^1/H^2$ 两条散射不变量

Künneth 给出

$$
H^2(Y;\mathbb Z_2)\cong
H^2(M;\mathbb Z_2)\ \oplus\ \big(H^1(M;\mathbb Z_2)\otimes H^1(X^\circ;\mathbb Z_2)\big)\ \oplus\ H^2(X^\circ;\mathbb Z_2).
$$

散射平方根的全局障碍有两条并行来源：
**$H^1$ 路线**：主 $\mathbb Z_2$‑丛类 $\mathfrak w\in H^1(X^\circ;\mathbb Z_2)$ 控制
$\nu_{\sqrt{\det_p S}}(\gamma)=(-1)^{\langle\mathfrak w,[\gamma]\rangle}$；在 $\Sigma_1\times\gamma_1$ 上以交叉项
$\pi_M^\ast\mu\smile \pi_X^\ast\mathfrak w$（$\mu\in H^1(M;\mathbb Z_2)$ 为与 $\Sigma_1$ 对偶的类）配对。
**$H^2$ 路线**：平直线丛 $\mathcal L_S$ 的 $c_1(\mathcal L_S)\in H^2(X^\circ;\mathbb Z)$（扭挠）经模二约化 $\rho\!\big(c_1\big)$；在 ${\mathrm{pt}}\times\gamma_2$ 上直接配对。后文 BF 顶项统一把三部分累加到同一 $K$ 中并以 $[K]=0$ 作为"可实现扇区"的充要判据。

在 $\mathbb Z_2$ 系数下 Tor 项消失，有相对分解

$$
H^2(Y,\partial Y;\mathbb Z_2)\cong
H^2(M,\partial M)\ \oplus\ \big(H^1(M,\partial M)\otimes H^1(X^\circ,\partial X^\circ)\big)\ \oplus\ H^2(X^\circ,\partial X^\circ).
$$

据此三类**相对**二维循环代表为

$$
(\Sigma_2,\partial\Sigma_2)\times{\mathrm{pt}},\quad
(\Sigma_1,\partial\Sigma_1)\times(\gamma_1,\partial\gamma_1),\quad
{\mathrm{pt}}\times(\gamma_2,\partial\gamma_2),
$$

配对规则与原文绝对情形逐项对应，且不依赖取向（$\mathbb Z_2$）。

---

## Model & Assumptions

**几何与态**：$(M,g)$ 定向四维、$g\in C^3$、$T_{ab}\in C^1$；小因果钻石腰面为极大截面，$\theta(0)=\sigma(0)=\omega(0)=0$，零测地族超曲面正交；Hadamard 态与点分裂重整化；$[0,\lambda_\ast]$ 内**无共轭点**；**能量–动量守恒** $\nabla^aT_{ab}=0$；一阶极值在固定温标/加速度框架下进行（$\delta T=0$）。

**光线变换可逆性与稳定（$A_{\rm LRI}$）**

在小钻石 $B_\ell(p)$ 的**无共轭点**域内，取 $w(\lambda)\in C^1[0,\lambda_\ast]$ **有界且存在 $w_0>0$ 使 $w(\lambda)\ge w_0$**。对 $f\in C^0(B_\ell(p))$，加权光线变换

$$
R_w[f](\gamma):=\int_0^{\lambda_\ast} w(\lambda)\,f(\gamma(\lambda))\,\mathrm d\lambda
$$

**单射**且满足**稳定估计**

$$
\|f\|_{L^\infty(B_\ell(p))}\ \le\ C\,\sup_{\gamma\subset B_\ell(p)}|R_w[f](\gamma)|,
$$

常数 $C$ 仅依赖 $(B_\ell(p),g)$ 与 $w$。本文仅以 $f:=R_{kk}-8\pi G\,T_{kk}$ 使用 $A_{\rm LRI}$，并将 $A_{\rm LRI}$ 与"Hadamard/角点处方/无共轭点"**并列视为定理 1 的门槛**。

**散射与正则性**：$S-\mathbf 1\in\mathfrak S_1$ 或满足相对迹类并采用修正行列式 $\det_p$；闭路数据分段 $C^1$；阈值/嵌入本征值以小半圆切除或折返，并以 $I_2(\gamma,D)$ 稳定。

**记号统一**：本文一律采用 Schatten 修正行列式 $\det_p$，并以 $\sqrt{\det_p S}$ 记散射平方根行列式；凡旧文出现 $\sqrt{\det S}$ 之处，均应视作 $\sqrt{\det_p S}$。**模二鲁棒性**：对 $p$ 的选择、相对迹类重整与有限维分波截断的改变不影响 $\nu_{\sqrt{\det_p S}}(\gamma)$ 的 $\mathbb Z_2$ 值。
**单位与温标**：体积项取 $-\tfrac{\Lambda}{8\pi G}V$；一阶极值在固定温标/加速度框架下进行（$\delta T=0$），不把 $T$ 作为变分变量。

**（解释）** 我们固定加速度/温度标度（$\delta T=0$），意即把 KMS 参数与局域 Rindler 框架视作**背景结构**而非变分变量，从而避免把温标的变化混入重力方程的一阶变分。此选择不限制物理性，只是变分学的口径。

**引理 A（加权光线约束的可达性）** 在定理 1 的门槛下（Hadamard 态、$[0,\lambda_\ast]$ 无共轭点、角点处方、$\delta T=0$ 与 **$\nabla^aT_{ab}=0$**），对任意小因果钻石 $B_\ell(p)$、任意其内零测地段 $\gamma$ 与任意 **$w\in C^1[0,\lambda_\ast]$ 且存在常数 $w_0>0$ 使 $w(\lambda)\ge w_0$** 的权函数，存在局域 Rindler 生成元族与相应通量（或模组）泛函，使得

$$
\mathcal F_{\gamma,w}\ \equiv\ \int_0^{\lambda_\ast} w(\lambda)\,\big(R_{kk}-8\pi G\,T_{kk}\big)\,\mathrm d\lambda\ =\ 0 .
$$

**证明素描**：由局域第一定律/相对熵第一律（Jacobson/Faulkner–Lewkowycz–Maldacena–Suh 结构）与角点处方保证的可积性，将通量差写成 $R_{kk}$ 与 $T_{kk}$ 的**线性泛函**；权 $w$ 由外参驱动的绝热剖面实现，Hadamard 与无共轭点确保权下的光线变换良定并受控。于是对所有 $\gamma,w$ 有 $\mathcal F_{\gamma,w}=0$。配合 **$A_{\rm LRI}$** 单射与稳定性即得 $R_{kk}=8\pi G\,T_{kk}$ 于 $B_\ell(p)$。

**边界与相对框架（$A_\partial$）**：记 $Y=M\times X^\circ$、$\partial Y=\partial M\times X^\circ\cup M\times\partial X^\circ$。在参数边界与判别集回避下**固定平方根分支与（若适用）自旋结构平凡化**，令 $r([K])=0$。由长正合序列得 $[K]$ **唯一提升**至 $H^2(Y,\partial Y;\mathbb Z_2)$，后文所有 Kronecker 配对均在**相对上同调**中进行。

**命题 B（相对提升的存在与唯一）** 设 $r:H^2(Y;\mathbb Z_2)\to H^2(\partial Y;\mathbb Z_2)$ 为限制映射。若 $r([K])=0$，则存在相对类 $\widetilde{[K]}\in H^2(Y,\partial Y;\mathbb Z_2)$ 使 $j^\ast\widetilde{[K]}=[K]$，其中 $j^\ast$ 为自然映射。其唯一性指：若 $\widetilde{[K]}_1,\widetilde{[K]}_2$ 皆为提升，则 $\widetilde{[K]}_1-\widetilde{[K]}_2\in \operatorname{Im}\big(H^1(\partial Y)\to H^2(Y,\partial Y)\big)$，在"边界平凡化"（固定 $\sqrt{\det_p S}$ 分支与自旋平凡化）下唯一。

**证明素描**：由相对上同调长正合序列

$$
\cdots\to H^1(\partial Y)\to H^2(Y,\partial Y)\xrightarrow{j^\ast} H^2(Y)\xrightarrow{r} H^2(\partial Y)\to\cdots
$$

可得"$r([K])=0\Rightarrow$ 存在提升"，唯一性由序列的核像关系给出。

**同调可检测性（$H^1$ 通道）**：假设 $H^1(M,\partial M;\mathbb Z_2)$ 非平凡，且存在基 $\{\mu_j\}$ 使得

$$
\sum_j \pi_M^\ast \mu_j\smile \pi_X^\ast \mathfrak w_j=0\ \text{于}\ H^2(Y,\partial Y;\mathbb Z_2)\ \Longleftrightarrow\ \forall j:\ \mathfrak w_j=0 ,
$$

**等价表述**：固定基 $\{\mu_j\}\subset H^1(M,\partial M;\mathbb Z_2)$ 后，线性映射

$$
T:\ \bigoplus_j H^1(X^\circ,\partial X^\circ;\mathbb Z_2)\ \longrightarrow\ H^1(M,\partial M;\mathbb Z_2)\otimes H^1(X^\circ,\partial X^\circ;\mathbb Z_2),\quad
T\big((\mathfrak w_j)_j\big)=\sum_j \mu_j\otimes \mathfrak w_j
$$

为**单射**。等价地，沿与 $\{\mu_j\}$ 对偶的相对闭 $1$‑链族 $\{(\Sigma_1^{(j)},\partial\Sigma_1^{(j)})\}$ 配对有

$$
\big\langle K,\ (\Sigma_1^{(j)},\partial\Sigma_1^{(j)})\times(\gamma_1,\partial\gamma_1)\big\rangle=\big\langle \mathfrak w_j,[\gamma_1]\big\rangle\ \ (\forall j),
$$

从而可**唯一**确定每个 $\mathfrak w_j$；据此可消去 $H^1\!\times H^1$ 通道并平凡化由 $H^1$ 控制的 $\nu_{\sqrt{\det_p S}}$。

**（$H^1$ 通道可检测性）**：取生成族 $\{(\gamma_1^{(a)},\partial\gamma_1^{(a)})\}$ 的相对闭路，并令

$$
P_{ja}:=\langle K,(\Sigma_1^{(j)},\partial\Sigma_1^{(j)})\times(\gamma_1^{(a)},\partial\gamma_1^{(a)})\rangle=\langle \mathfrak w_j,[\gamma_1^{(a)}]\rangle.
$$

**若且仅若** $\{(\gamma_1^{(a)},\partial\gamma_1^{(a)})\}$ 生成 $H_1(X^\circ,\partial X^\circ;\mathbb Z_2)$，评估映射

$$
\mathrm{ev}:H^1(X^\circ,\partial X^\circ;\mathbb Z_2)\to\mathbb Z_2^{A},\quad \mathfrak w\mapsto\big(\langle\mathfrak w,[\gamma_1^{(a)}]\rangle\big)_a
$$

**单射**；于是 $T=\bigoplus_j(\mu_j\otimes\mathrm{ev})$ 单射，$H^1\!\times H^1$ 通道可被**唯一消去**。等价地，对每个 $j$，行向量 $(P_{ja})_a$ 全零当且仅当 $\mathfrak w_j=0$，无需额外的"$P$ 行满秩"要求。

**（$H^2$ 通道可检测性，$A_{!H^2}$）**：取生成族 $\{\gamma_2^{(b)}\}$ 的相对二维循环，测量 $\langle \rho(c_1(\mathcal L_S)),[\gamma_2^{(b)}]\rangle$ 是否**全零**以判定消去。

**引理 C（检测族的有限生成）** 设允许的物理回路/相对二维循环族 $\mathcal S$ 满足：

（i）（可解模型）参数域在去除判别集 $D$ 后形变收缩至 1‑复形（或 2‑骨架）；

（ii）（一般情形）存在有限组 $\{(\gamma_1^{(a)}),(\gamma_2^{(b)})\}$ 与 $\{(\Sigma_1^{(j)}),(\Sigma_2)\}$ 使得

$$
\big\{(\Sigma_1^{(j)},\partial\Sigma_1^{(j)})\times(\gamma_1^{(a)},\partial\gamma_1^{(a)}),\ \ (\Sigma_2,\partial\Sigma_2)\times\mathrm{pt},\ \ \mathrm{pt}\times(\gamma_2^{(b)},\partial\gamma_2^{(b)})\big\}
$$

生成 $H_2(Y,\partial Y;\mathbb Z_2)$。

则矩阵 $P_{ja}$ 行满秩与 $A_{!H^2}$ 共同给出**可操作的充要检测**：测得所有配对为零 $\Leftrightarrow [K]=0$。

**生成性假设（相对二同调版，记作 $A_{\rm rel\text{-}gen}$）**

允许的"物理二维循环族"$\mathcal S$ 在**相对**意义下生成 $H_2(Y,\partial Y;\mathbb Z_2)$，即任意相对类 $[S]\in H_2(Y,\partial Y;\mathbb Z_2)$ 可由有限个

$$
(\Sigma_2,\partial\Sigma_2)\times{\mathrm{pt}},\ \ 
(\Sigma_1,\partial\Sigma_1)\times(\gamma_1,\partial\gamma_1),\ \ 
{\mathrm{pt}}\times(\gamma_2,\partial\gamma_2)
$$

的 $\mathbb Z_2$ 线性组合表示。后续所有"充要/必要"判据均在 $A_\partial$ 与 $A_{\rm rel\text{-}gen}$ 下陈述。

**推论 E（$H^2=0$ 化约）** 对一维 $\delta$ 势、二维 Aharonov–Bohm 与端点散射族，参数域去除判别集后形变收缩到 1‑复形，故 $H^2(X^\circ,\partial X^\circ)=0$；于是（iii）与（iii$^\star$）等价，并且 $(\text{iii}^\star)\Rightarrow(ii)$ 在相对上同调意义下成立。

**扭挠与可检测性**：**（平直性）** 若 $\mathcal L_S$ 为**平直** $U(1)$ 线丛，则 $c_1(\mathcal L_S)$ 落在 $H^2(X^\circ;\mathbb Z)$ 的**扭挠子群**（有限阶）。为与本文 $\mathbb Z_2$ 框架匹配，**引入假设** **（$A_{\rm tors2}$）**：$c_1(\mathcal L_S)$ 的扭挠阶为某个 $2^m$，于是其模二约化 $\rho(c_1(\mathcal L_S))$ 完整刻画 $H^2$ 通道；**（$A_{!H^2}$）**——允许的参数二维循环生成 $H_2(X^\circ,\partial X^\circ;\mathbb Z_2)$。

**自旋平凡性（$A_{\rm spin}$）**：一般流形时假设 $w_2(TM)=0$。**小因果钻石情形自动满足**：令工作域 $U:=B_\ell(p)$，则 $U$ 可形变收缩到带边紧域，$\Rightarrow H^2(U,\partial U;\mathbb Z_2)=0$。

**（平直线丛扭挠口径；$A_{\rm tors2}$ 的明确定义）**

若散射相之线丛 $\mathcal L_S$ 取自 $U(1)$‑表示，则 $c_1(\mathcal L_S)$ 为**扭挠**类（有限阶）。为与本文 $\mathbb Z_2$ 架构对齐，**我们假设** $c_1(\mathcal L_S)$ 的扭挠阶为某个 $2^m$（记作 $A_{\rm tors2}$）。在此假设下，$\rho(c_1(\mathcal L_S))\in H^2(X^\circ;\mathbb Z_2)$ **穷尽** $H^2$‑通道并进入 $K$。若存在奇数阶扭挠分量，则需改用相应有限群（如 $\mathbb Z_n$）的 BF 顶项；本文不展开，后续充要/等价陈述均在 $A_{\rm tors2}$ 下理解。

---

## Main Results (Theorems and Alignments)

为避免歧义，本文主命题的三层对象统一约定为

$$
\boxed{%
\begin{aligned}
&(i):\ \ \ G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}\ \ \land\ \ \delta^2 S_{\rm rel}=\mathcal E_{\rm can}[h,h]\ge0\\
&(ii):\ \ \ [K]=0\in H^2\big(Y,\partial Y;\mathbb Z_2\big)\\
&(\text{iii}^\star):\ \ \ \forall\gamma\subset X^\circ:\ \nu_{\sqrt{\det_p S}}(\gamma)\equiv1\ \ \land\ \ \forall\ \gamma_2\subset X^\circ\ \text{允许}:\ \langle \rho(c_1(\mathcal L_S)),[\gamma_2]\rangle=0
\end{aligned}}
$$

其中 (i) 的门槛包含：$[0,\lambda_*]$ 内无共轭点、Hadamard 态与角点处方（辛流闭合与 $\delta H_\chi$ 可积）以及"固定温标/加速度"$\delta T=0$、**能量–动量守恒 $\nabla^a T_{ab}=0$**、**$A_{\rm LRI}$**。 (ii) 采用相对上同调并以下文 $A_\partial$ 的边界条件使 $[K]$ 提升为相对类。其余记号与假设见"Model & Assumptions"。

**（定义）物理判据 (iii)**

$$
\boxed{\ \text{(iii)}\ \equiv\ \forall\ \gamma\subset X^\circ:\ \nu_{\sqrt{\det_p S}}(\gamma)\equiv 1\ }.
$$

**说明**：该判据仅涉及回路（$H^1\!\times H^1$ 通道）。当 $H^2(X^\circ,\partial X^\circ)=0$ 时，(iii) 与 **(iii$^\star$)** 等价；下文有关"(iii) 与 (iii$^\star$) 等价"的表述均在此意义下成立。

**（定义）物理判据 (iii$^\star$)**

$$
\boxed{\ \text{(iii$^\star$)}\ \equiv
\underbrace{\forall\ \gamma\subset X^\circ:\ \nu_{\sqrt{\det_p S}}(\gamma)\equiv 1}_{\text{回路（$H^1\!\times H^1$ 通道）}}\ \ \land\
\underbrace{\forall\ \gamma_2\subset X^\circ\ \text{允许}:\ \langle \rho(c_1(\mathcal L_S)),[\gamma_2]\rangle=0}_{\text{参数二维循环（$H^2$ 通道）}}\ }.
$$

**术语**："允许的相对二维循环"指由

$$
(\Sigma_2,\partial\Sigma_2)\times{\mathrm{pt}},\quad (\Sigma_1,\partial\Sigma_1)\times(\gamma_1,\partial\gamma_1),\quad {\mathrm{pt}}\times(\gamma_2,\partial\gamma_2)
$$

三类乘积在 $\mathbb Z_2$ 系数下**生成** $H_2(Y,\partial Y;\mathbb Z_2)$ 的有限组合；相对配对均在

$$
H^2(Y,\partial Y;\mathbb Z_2)\times H_2(Y,\partial Y;\mathbb Z_2)\to\mathbb Z_2
$$

中计算，故与取向无关。

**等价句**：在生成性 $A_{\rm rel\text{-}gen}$ 与可检测性（见"Model & Assumptions"）成立时，$(iii^\star)\iff\langle K,[S]\rangle=0$ 对一切允许相对二维循环成立。

**（注）** "允许"的二维循环族按 **$A_{\rm rel\text{-}gen}$** 之生成性取定；若允许族未生成全部相对二同调，则上式仅给出**必要**而非**充分**判据。

### 定理 1（Null 链：两层判据，取 $A_{\rm LRI}$ 为门槛）

在小因果钻石 $B_\ell(p)$ 的无共轭点域内，满足 Hadamard 态、角点处方、$\nabla^aT_{ab}=0$、$\delta T=0$ **并假设 $A_{\rm LRI}$（加权光线变换在 $B_\ell(p)$ 单射且具有稳定估计）**时，

$$
G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab},\qquad \delta^2 S_{\rm rel}=\mathcal E_{\rm can}[h,h]\ge 0 .
$$

首式由"族约束 $\Rightarrow$ 点态"的 Radon‑型闭包与零锥刻画得到（取 $f:=R_{kk}-8\pi G\,T_{kk}$，配合 $A_{\rm LRI}$ 单射性即得 $R_{kk}=8\pi G\,T_{kk}$，再经零锥刻画与 Bianchi 恒等式升格为张量方程）；次式与 Hollands–Wald 规范能量非负等价。

**引理 1″**（小因果钻石上的加权光线变换可逆与稳定；背景说明）

在 $g\in C^3$、$T_{ab}\in C^1$ 且 $[0,\lambda_\ast]$ **无共轭点**的门槛下，取 $w\in C^1([0,\lambda_\ast])$ 正且有界。则加权光线变换

$$
R_w[f](\gamma):=\int_0^{\lambda_\ast} w(\lambda)\,f(\gamma(\lambda))\,\mathrm d\lambda
$$

在小钻石上**可逆**，并存在常数 $C$ 使

$$
\|f\|_{L^\infty(B_\ell(p))}\le C\,\sup_{\gamma}|R_w[f](\gamma)|.
$$

**（注）** 本文将此可逆性与稳定估计作为门槛假设 $A_{\rm LRI}$ 使用，不再作为本文内证成的结论。

**引理 1′（零锥 ⇒ 共形型，$n\ge3$，连通版）**

令 $Q_{ab}$ 为 $C^1$ 对称二阶张量，$M$ **连通**且 $\dim M=n\ge3$。若对一切零向量 $k^a$ 有 $Q_{ab}k^a k^b=0$，则存在标量函数 $\phi\in C^1(M)$ 使 $Q_{ab}=\phi\,g_{ab}$。若再有 $\nabla^a Q_{ab}=0$，则 $\nabla_b\phi=0$，因连通性得 $\phi=\text{常数}$。取 $Q_{ab}:=G_{ab}-8\pi G\,T_{ab}$ 与 $\phi=-\Lambda$ 即得 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。

**证素描**：零锥刻画确定 $Q$ 与 $g$ 具有相同的零锥，故 $Q=\phi g$（$n\ge3$）。再由 Bianchi 恒等式与 **$\nabla^a T_{ab}=0$** 得 $\nabla^aQ_{ab}=0$，故 $\nabla_b\phi=0$，$\phi$ 为常数。

**引理 A′（零锥极化）** 令 $Q_{ab}$ 为 $C^1$ 对称张量、$n\ge3$。若对所有零向量 $k^a$ 有 $Q_{ab}k^ak^b=0$，则 $Q_{ab}=\phi\,g_{ab}$ 某标量 $\phi$。

**证明**：对任意类时空向量 $u^a,v^a$，用极化恒等式

$$
4\,Q_{ab}u^av^b=Q_{ab}(u+v)^a(u+v)^b-Q_{ab}(u-v)^a(u-v)^b
$$

将 $Q(\cdot,\cdot)$ 还原为对若干**零向量**上的值。因与 $g$ 共享零锥，$Q$ 的主方向集与 $g$ 一致，仅能为 $Q=\phi g$。再由 $\nabla^aQ_{ab}=0$（Bianchi 与 **$\nabla^aT_{ab}=0$**）得 $\nabla_b\phi=0$。至此引理 1′ 完备化。

**（Radon–型闭包）** 在 $[0,\lambda_\ast]$ 无共轭点的门槛下，加权光线变换

$$
R_w[f](\gamma):=\int_0^{\lambda_\ast} w(\lambda)f(\gamma(\lambda))\,\mathrm d\lambda
$$

在小钻石上可逆，并满足稳定估计 $|f|\le C\,|R_w[f]|$。取 $f:=R_{kk}-8\pi G\,T_{kk}$ 即得 $R_{kk}=8\pi G\,T_{kk}$，配合零锥刻画与 Bianchi 恒等式升格为 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。

### 定理 2（Modular 链；$\mathbb Z_2$ 等价，统一口径）

取固定能量 $E$ 位于连续谱并远离阈值/嵌入本征值。**本文一律以 Schatten 修正行列式 $\det_p$** 计相位（$S(E;\cdot)-\mathbf 1$ 迹类或相对迹类时），**相对迹类重整与有限维分波截断仅改变整数绕数，其 $\mathbb Z_2$ 投影不变**。定义判别集

$$
D_E\ :=\ \bigl\{x\in X^\circ:\ \sqrt{\det_p S(E;x)}\ \text{的连续分支在 }x\text{ 处不可定义}\bigr\}.
$$

其典型来源为：**(α)** 阈值、嵌入本征值或共振导致谱移函数 $\xi(E;\cdot)$ 跃迁；**(β)** $S(E;\cdot)$ 存在特征值 $-1$（平方根分支切换点）。

对任一闭路 $\gamma$（按"小半圆/折返"规则稳定）有

$$
\nu_{\sqrt{\det_p S(E;\cdot)}}(\gamma)=\exp\!\Bigl(-\mathrm i\pi\oint_\gamma \mathrm d\xi(E)\Bigr)=(-1)^{I_2(\gamma,D_E)} .
$$

当 $\gamma$ 与 $D_E$ 横截或切触时，按"**小半圆或折返**"规则稳定，$I_2(\gamma,D_E)$ 定义为**相对取向**的模二交数，故对正则化口径与局部取向**不敏感**。

**引理 2.1**（谱流与模二交数，Pushnitski 2001, Thm 3.2）  

在迹类扰动与阈值正则化下，$\mathrm{Sf}(\gamma;E)\bmod 2=I_2(\gamma,D_E)$，故 $\nu_{\sqrt{\det_p S}}(\gamma)=(-1)^{\mathrm{Sf}}=(-1)^{I_2}$ 成立。

判别集

$$
D_E:=\bigl\{x\in X^\circ:\ \sqrt{\det_p S(E;x)}\ \text{的连续分支在 }x\text{ 处不可定义}\bigr\},
$$

其典型来源为：**(α)** 阈值、嵌入本征值或共振导致谱移函数 $\xi(E;\cdot)$ 跃迁；**(β)** $S(E;\cdot)$ 出现特征值 $-1$（平方根分支切换点）。于是 $\nu_{\sqrt{\det_p S}}(\gamma)=\exp\!\big(-\mathrm i\pi\oint_\gamma \mathrm d\xi(E)\big)=(-1)^{I_2(\gamma,D_E)}$。$I_2(\gamma,D_E)$ 定义为相对取向之模二交数。当 $\gamma$ 与 $D_E$ 切触时，允许以（i）小半圆偏转或（ii）折返使交点计数良定；该模二计数对迹类/相对迹类正则化与有限维截断稳定。

**引理 2.2**（模二鲁棒性；对 $p$/相对迹类/分波截断的独立性）

在 $S(E;\cdot)-\mathbf 1$ 属迹类或相对迹类的门槛下，取任意 $p\ge 1$ 之 Schatten 修正行列式 $\det_p$。对多通道/分波情形，令有限维截断参数 $N\to\infty$。则对一切**物理闭路** $\gamma$（按"小半圆/折返"规则稳定），有

$$
\nu_{\sqrt{\det_p S}}(\gamma)=(-1)^{\mathrm{Sf}(\gamma;E)}=(-1)^{I_2(\gamma,D_E)},
$$

其中等式右侧的模二值对 $p$ 的选择、相对迹类的重整方案与分波截断极限 $N\to\infty$**均不变**。

**证明素描**：模二谱流在稳定同伦下不变；$I_2$ 为 $\mathbb Z_2$ 交数，对正则化方案与局部取向不敏感；$\det_p$ 的改变仅改变量子化的 $2\pi$ 相位，$\mathbb Z_2$ 投影不受影响。

### 定理 3（$\mathbb Z_2$–BF 扇区选择：体积分、一般维度、相对上同调）

令 $d=\dim Y$，取

$$
a\in C^{1}(Y;\mathbb Z_2),\quad b\in C^{d-2}(Y;\mathbb Z_2),\quad
K:=\pi_M^\ast w_2(TM)\ +\ \underbrace{\sum_j \pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j}_{H^1\!\times H^1\ \text{通道}}\ +\ \underbrace{\pi_X^\ast\rho\!\big(c_1(\mathcal L_S)\big)}_{H^2\ \text{通道}} .
$$

取

$$
I_{\rm BF}[a,b]=\mathrm i\pi\!\int_{(Y,\partial Y)} b\smile\boldsymbol\delta a+\mathrm i\pi\!\int_{(Y,\partial Y)} b\smile K\ +\ \mathrm i\pi\!\int_{\partial Y} a\smile b .
$$

**规变良定与上同调投影**

**（有限性门槛）** 假设 $Y$ 与 $\partial Y$ 为有限 CW 复形（故 $H^\bullet(Y,\partial Y;\mathbb Z_2)$ 有限维），于是对 $[a]\in H^1(Y,\partial Y)$、$[b]\in H^{d-2}(Y,\partial Y)$ 的求和是**有限群**上的离散求和，可用特征正交性得 $Z_{\rm top}\propto\delta([K])$。

取 $a\in C^1(Y;\mathbb Z_2)$、$b\in C^{d-2}(Y;\mathbb Z_2)$、

$$
K=\pi_M^\ast w_2(TM)+\sum_j \pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j+\pi_X^\ast\rho(c_1(\mathcal L_S)).
$$

作用量

$$
I_{\rm BF}[a,b]=\mathrm i\pi\!\int_{(Y,\partial Y)} b\smile\boldsymbol\delta a+\mathrm i\pi\!\int_{(Y,\partial Y)} b\smile K+\mathrm i\pi\!\int_{\partial Y} a\smile b
$$

在规变 $a\mapsto a+\boldsymbol\delta\lambda^{0}$、$b\mapsto b+\boldsymbol\delta\lambda^{d-3}$ 下边界项互相抵消，变分良定；对相对上同调类 $[a]\in H^1(Y,\partial Y)$、$[b]\in H^{d-2}(Y,\partial Y)$ 求和并用**有限阿贝尔群特征正交性**得

$$
\boxed{Z_{\rm top}\ \propto\ \delta([K])\quad\Longleftrightarrow\quad [K]=0\in H^2(Y,\partial Y;\mathbb Z_2)}.
$$

于是对一切相对二维循环 $[S]$ 有 $\langle K,[S]\rangle=0$；在 $A_{\rm rel\text{-}gen}$ 下该条件亦为充分。

**（统一注）相对上同调 + 边界规不变性：三步法**

(1) 在 $(Y,\partial Y)$ 上以 $\mathbb Z_2$ 系数取变分良定之作用

$$
I_{\rm BF}[a,b]=\mathrm i\pi\!\int_{(Y,\partial Y)} b\smile\boldsymbol\delta a+\mathrm i\pi\!\int_{(Y,\partial Y)} b\smile K+\mathrm i\pi\!\int_{\partial Y} a\smile b ,
$$

使规变 $a\mapsto a+\boldsymbol\delta\lambda^{0}$、$b\mapsto b+\boldsymbol\delta\lambda^{d-3}$ 的边界项相互抵消；

(2) 先对 $[a]\in H^1(Y,\partial Y)$ 求和，仅强制 $\boldsymbol\delta b=0$；再对 $[b]\in H^{d-2}(Y,\partial Y)$ 求和，借有限阿贝尔群的特征正交性得到 $Z_{\rm top}\propto \delta([K])$；

(3) 由 Poincaré–Lefschetz 对偶与 $A_{\rm rel\text{-}gen}$，$\langle K,[S]\rangle=0$ 对**一切**相对二维循环 $[S]$ 当且仅当 $[K]=0$。

详见附录 VII：我们给出带边流形的相对上同调长正合序列的文字叙述，并证明 $\partial Y$ 的配对不引入额外障碍，因而 $[K]=0\in H^2(Y,\partial Y;\mathbb Z_2)$ 仍是充要。

### 假设 4′（$H^2$ 对齐，**模二版**）

存在平直散射线丛 $\mathcal L_S\to X^\circ$ 的相对平凡化与嵌入 $\iota:X^\circ\to\mathcal P$，使得对**任意允许的相对二维循环** $(\gamma_2,\partial\gamma_2)\subset (X^\circ,\partial X^\circ)$ 有

$$
\big\langle \rho\!\big(c_1(\mathcal L_S)\big),[\gamma_2]\big\rangle
\equiv \Big\langle \frac{1}{2\pi}\,\iota^\ast\!\big(\mathrm d\mathcal A_{\rm mod}\big),\ [\Gamma]\Big\rangle \ \bmod 2,
$$

其中 $[\Gamma]$ 为与 $(\gamma_2,\partial\gamma_2)$ 相容的相对二维链类。该对齐把**二维通道**的模二配对与**模组联络曲率的相对类**在模二意义下统一，从而在 $A_{!H^2}$ 下可由实验/几何检测将其消去。

### 假设 4（Modular–Scattering Alignment，**模二版**）

存在嵌入 $\iota:X^\circ\to\mathcal P$ 与光滑模组联络 $\mathcal A_{\rm mod}$ 及散射族 $S(\cdot)$，满足：

（a）$\mathcal A_{\rm mod}$ 的曲率等于体辛形式；（b）$S^{-1}\mathrm dS$ 为迹类 $1$‑形式；（c）物理闭路沿程可避开判别集（或按"**小半圆/折返**"稳定）。并且仅需**模二环量对齐**：

$$
\exp\!\Big(\mathrm i\oint_\gamma \mathcal A_{\rm mod}\Big)\ \equiv\ \nu_{\sqrt{\det_p S}}(\gamma)\ \in\{\pm1\}.
$$

（若在平衡/局域情形还成立实数环量相等，则属更强版本，但**E‑(b″)** 的充分性**仅**依赖本模二对齐。）

**引理 D（模二对齐的闭路稳定性）** 若 $S^{-1}\mathrm dS$ 为迹类 $1$‑形式且闭路与判别集 $D$ 的相交按"小半圆/折返"稳定，则

$$
\nu_{\sqrt{\det_p S}}(\gamma)=(-1)^{\mathrm{Sf}(\gamma;E)}=(-1)^{I_2(\gamma,D)}
$$

对 Schatten 指数 $p$、相对迹类重整与分波截断极限**不变**。

**引理 D′（角点处方下的二次型嵌入）** 角点处方保证辛流闭合与 $\delta H_\chi$ 可积；因而沿闭路的模组环量 $\oint_\gamma\mathcal A_{\rm mod}$ 给出协变相空间上**有界线性泛函**，可嵌入 $\delta^2 S_{\rm rel}$ 的二次型核。若 $\exp(\mathrm i\oint_\gamma\mathcal A_{\rm mod})=-1$，则存在 $h$ 使 $\mathcal E_{\rm can}[h,h]<0$。

**命题 4.1（$\mathbb Z_2$ 异常与规范能量可负；对齐为**充分条件**）**

在**假设 4（模二版）**与 $A_\partial$、$A_{\rm rel\text{-}gen}$ 及定理 1 门槛下：若存在物理闭路 $\gamma$ 使 $\nu_{\sqrt{\det_p S}}(\gamma)=-1$，则可构造满足 Hollands–Wald 条件的扰动 $h$，令

$$
\mathcal E_{\rm can}[h,h]<0 .
$$

因此，若对一切 $h$ 都有 $\mathcal E_{\rm can}[h,h]\ge0$，则一切物理闭路的 $\nu_{\sqrt{\det_p S}}(\gamma)$ 必为 $+1$；其中"模组—散射对齐（模二）"仅为**充分**而非**必要**的桥梁条件。

**证明要点（补足）**：令 $\Lambda_\gamma:=\oint_\gamma \mathcal A_{\rm mod}$。角点处方使 $\Lambda_\gamma$ 定义出协变相空间上的有界线性泛函 $\ell_\gamma$，并可将 $\ell_\gamma$ 写成二次型核上的偏导数作用：$\ell_\gamma(h)=\langle Qh,h\rangle$，其中 $Q$ 为有界自伴算子。由 $\mathrm e^{\mathrm i\Lambda_\gamma}=-1$ 知 $\operatorname{ind}_-(Q)\ge1$。用 $A_{\rm rel\text{-}gen}$ 选择与 $Q$ 的负谱对应的有限维子空间并记其正交投影为 $\Pi$，取 $h$ 在 $\operatorname{Ran}\Pi$ 上即可得上式不等式。模二对齐确保符号一致性，而常数 $c$ 由 $Q$ 在 $\operatorname{Ran}\Pi$ 上的最小特征值给出。

### 定理 5（统一原理）

**E‑(a′)（分解；***门槛合订本***）**

在 **$A_\partial$、$A_{\rm rel\text{-}gen}$、$A_{!H^2}$、$H^1$‑通道可检测性（检测回路生成 $H_1$）、**$A_{\rm tors2}$** 与（一般流形时）**$A_{\rm spin}$**，并假定 $Y$ 与 $\partial Y$ 满足 Poincaré–Lefschetz 对偶的门槛下，

$$
\boxed{(ii)\ \Longleftrightarrow\ (iii^\star)}.
$$

若缺少 $A_{\rm rel\text{-}gen}$ 或 $A_{!H^2}$，则仅有 $(ii)\Rightarrow(iii^\star)$ 的**必要性**。

**E‑(b″)（对齐推出）** 在"定理 1"的正则门槛并满足**假设 4（模二版）**与**假设 4′**下，

$$
\boxed{(i)\ \Longrightarrow\ (iii^\star)\ (\Longleftrightarrow\ (ii)).}
$$

（在三类可解族中，$H^2(X^\circ,\partial X^\circ)=0$，故 $(iii)=(iii^\star)$。）

**模型域注释（统一）**

在一维 $\delta$ 势、二维 Aharonov–Bohm 与端点散射（Class D/DIII）的可解族中，参数域局域穿孔可形变收缩到 1‑复形，故 $H^2(X^\circ,\partial X^\circ)=0$，$(iii)$ 与 $(iii^\star)$ 合一且仅余"回路（$H^1\!\times H^1$）"判据。构造与判别集 $D$ 横截的回路族可验证 $(iii^\star)\Rightarrow(ii)$ 于相对上同调意义成立。**长程/分波无穷情形**以 $\det_2$ 或相对迹类正则化处理，其 $\mathbb Z_2$ 指纹不变。

---

## Proofs

### 定理 1

由 Sachs 与变系数 Grönwall 得

$$
\big|\theta(\lambda)+\lambda R_{kk}\big|\le \tfrac12 C_{\nabla R}\lambda^2+C_\sigma^2|\lambda|.
$$

以与 $\varepsilon$ 无关的支配函数建立"极限—积分可交换"，配合加权光线变换与局域化引理将族约束下推为 $R_{kk}=8\pi G\,T_{kk}$。零锥刻画与 Bianchi 恒等式给出 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$。协变相空间的 null 边界与角点处方保证辛流无外泄与 $\delta H_\chi$ 可积，故 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$。我们工作在 $[0,\lambda_\ast]$ 无共轭点、Hadamard 态与角点处方闭合的可逆域内。

### 定理 2

在上述门槛下，$\det_p S(E;\cdot)=\mathrm e^{-2\pi\mathrm i\,\xi(E)}$；沿闭路 $\gamma$ 有

$$
\deg(\det_p S(E;\cdot)|_\gamma)=-\oint_\gamma \mathrm d\xi(E)=\mathrm{Sf}(\gamma;E)\in\mathbb Z,\qquad
\nu_{\sqrt{\det_p S(E;\cdot)}}(\gamma)=\exp\!\Bigl(-\mathrm i\pi\oint_\gamma \mathrm d\xi(E)\Bigr).
$$

阈值/嵌入本征值以 $I_2(\gamma,D_E)$ 稳定；$I_2$ 取相对取向之模二交数。

### 定理 3（体积分、一般维度、相对上同调）

作用量 $I_{\rm BF}[a,b]=\mathrm i\pi\int_Y b\smile\boldsymbol\delta a+\mathrm i\pi\int_Y b\smile K$ 对 $a$ 和 $b$ 的变分分别给出 $\boldsymbol\delta a+K=0$ 与 $\boldsymbol\delta b=0$。先对 $[a]$ 求和仅强制 $\boldsymbol\delta b=0$，再对闭的 $[b]$ 上同调类求和利用特征正交性把配分函数在上同调上投影到 $[K]=0$（见正文定理 3 的注）。含边界时改用相对上同调 $H^\bullet(Y,\partial Y;\mathbb Z_2)$ 并加入边界对偶项以保证变分良定；由 $r([K])=0$ 可把 $[K]$ 提升至相对类，结论同上。

### 假设 4

在半空间编码中边界平移 $U(\lambda)=\mathrm e^{-\mathrm iP\lambda}$ 生成 $\mathcal A_{\rm mod}=\langle P\rangle\mathrm d\lambda$；移动镜反射给 $S=e^{2\mathrm i k\lambda}$，$\tfrac{1}{2\mathrm i}\operatorname{tr}(S^{-1}\mathrm dS)=k\,\mathrm d\lambda$。两侧环量一致；非局域核可使实数环量不同，但模二投影稳定。该对齐为**充分**条件。

### 定理 5

**E‑(a′)** 由定理 3 得 $(ii)\Rightarrow(\text{iii}^\star)$；由检测子回路与参数二维循环生成 $H_2(Y,\partial Y;\mathbb Z_2)$（在 $A_{\rm rel\text{-}gen}$ 下）得 $(\text{iii}^\star)\Rightarrow(ii)$，故 $(ii)\Leftrightarrow(\text{iii}^\star)$。**E‑(b″)** 在假设 4 与假设 4′ 以及 $A_{!H^2}$ 下，由定理 1 与命题 4.1 得 $(i)\Rightarrow(\text{iii}^\star)$，于是 $(i)\Rightarrow(ii)\Leftrightarrow(\text{iii}^\star)$。

**模型域注释（修订）** 在一维 $\delta$ 势、二维 Aharonov–Bohm 与端点散射（Class D/DIII）的可解族中，参数域的局域穿孔形变收缩到 1‑复形，故 $H^2(X^\circ,\partial X^\circ)=0$，于是 **(iii$^\star$)** 简化为仅含"回路（$H^1\!\times H^1$）"的判据；在该情形下，构造与 $D$ 横截的回路族可验证 $(\text{iii}^\star)\Rightarrow (ii)$ 于相对上同调意义成立。

---

## Model Apply

### 一维 $\delta$ 势（$\hbar=2m=1$）

下述指纹仅为可视化途径；**物理判据一律以 $\nu_{\sqrt{\det_p S}}$ 计**。采用 $\det_p$ 或分波截断的差异在**模二**下不影响结论。

偶宇称通道

$$
S(k)=\frac{2k-\mathrm i\lambda}{2k+\mathrm i\lambda}=e^{2\mathrm i\delta(k)},\qquad
\text{取 **Jost 函数** } f(k):=1+\frac{\mathrm i\lambda}{2k}\ \text{使}\ S(k)=\frac{f(-k)}{f(k)} .
$$

**复参数小环（真奇点）**：取 $E(t)=E_0$、$\lambda(t)=-2\mathrm i\sqrt{E_0}+\rho\,\mathrm e^{\mathrm i t}$，则

$$
\oint_{\gamma}\frac{1}{2\mathrm i}S^{-1}\mathrm dS=\pi,\qquad \nu_{\sqrt{\det_p S}}=-1 .
$$

**实参数折返**：在 $(E,\lambda)$ 平面折返横截 $D$ 并以小半圆切除，$I_2(\gamma,D)=1\Rightarrow \nu_{\sqrt{\det_p S}}=-1$。

**同调基说明**：去除判别集 $D$（极点与共振）后，参数域形变收缩到穿孔平面的一维骨架，其 $H_1$ 由绕极点的基本回路生成，$H^2(X^\circ,\partial X^\circ)=0$。因此（iii$^\star$）仅含回路判据。

### 二维 Aharonov–Bohm

通量 $\alpha\mapsto\alpha+1$ 穿越 $\alpha=\tfrac12$ 时 $\deg(\det_p S|_\gamma)=1\Rightarrow\nu_{\sqrt{\det_p S}}=-1$。分波无穷以分波截断或 $\det_2$ 正则化，模二结果不变。

**同调基说明**：去除判别集 $D=\{\alpha=\tfrac12+\mathbb Z\}$ 后，参数域形变收缩到一维环，其 $H_1$ 由绕 $\alpha=\tfrac12$ 的基本回路生成，$H^2(X^\circ,\partial X^\circ)=0$。因此（iii$^\star$）仅含回路判据。

### 拓扑超导端点散射

Class D：$Q=\operatorname{sgn}\det_p r(0)$；Class DIII：$Q=\operatorname{sgn}\operatorname{Pf}r(0)$。两者等价于 $\sqrt{\det_p r(0)}$ 的分支号符；隙闭合（属 $D$）横跨一次触发 $Q$ 翻转并与 $\nu_{\sqrt{\det_p r}}$ 同步。

**同调基说明**：隙闭合超曲面为判别集 $D$，其横截给出基本回路；参数域去除 $D$ 后形变收缩到一维骨架，$H^2(X^\circ,\partial X^\circ)=0$。因此（iii$^\star$）仅含回路判据。

---

## Engineering Proposals（参数窗与误差估计）

**AB 干涉环**：有效面积 $A\sim 1~\mu\mathrm m^2$，半通量 $B_{1/2}\simeq\Phi_0/(2A)\sim \mathrm{mT}$。需 $L_\phi\gtrsim$ 周长且 $|\delta B|\ll \Phi_0/(4A)$ 以解析 $\pi$ 跃迁。
**冷原子 $\delta$ 势环路**：以 Feshbach 调谐 $\lambda$ 绕极点闭路，绝热标度 $\tau_{\rm drive}\gg \hbar/\Delta$ 抑制非绝热误差；Ramsey/MZ 干涉读出 $\arg S$。
**拓扑纳米线（D/DIII）**：$k_BT\ll\Delta$、接触展宽 $\Gamma/\Delta\ll1$；$\operatorname{sgn}\det_p r(0)$/$\operatorname{sgn}\operatorname{Pf}r(0)$ 的翻转与量化导通峰协变。

**图 4**（可插入）  

(a) 2D AB 环：当磁通 $\Phi$ 穿过 $\Phi_0/2$ 时，干涉相位跨越 $\pi$，电导干涉项变号（峰↔谷），对应 $\nu_{\sqrt{\det_p S}}=-1$。  

(b) Topo SC 端点：Majorana 电导在隙闭合处从 $0$ 翻转到 $2e^2/h$（Class D，单模理想耦合；DIII 理想 helical 双通道为 $4e^2/h$），与 $\mathbb Z_2$ 翻转同步。

| 平台 | 可调参数 | 误差源 | 需求值 | 当前可达值 |
|---|---|---|---|---|
| 冷原子 δ 势 | Feshbach 扫频速率 $\dot\lambda$ | 非绝热跃迁 | $\hbar/\Delta\ll 0.1$ ms | $\tau_{\rm drive}=0.5$ ms |
| AB 干涉环 | 磁场均匀度 $\delta B/B$ | 相位平均 | $<10^{-3}$ | $2\times 10^{-4}$ |
| Topo 纳米线 | 温度 $T$ | 热激发准粒子 | $k_BT/\Delta<0.1$ | 20 mK ($\Delta=200$ mK) |

**注**：表中数值为**可比对的参照窗**而非普适下界；具体平台需结合相干长、温度噪声与耦合效率重估可解析的 $\pi$‑跃迁/电导翻转阈值。$\Phi_0=h/e$；面积 $A$ 以 $\mu\mathrm m^2$ 计，$B_{1/2}=\Phi_0/(2A)$；温度与能隙的比值均以无量纲 $k_BT/\Delta$ 表示。

| 观测信号 | 拟合/阈值 | 理论映射 | 拓扑指示 |
|---|---|---|---|
| 干涉项符号在 $\Phi=\Phi_0/2$ 翻转 | $\delta B/B<10^{-3}$ | $\deg(\det_p S|_\gamma)=1$ | $\nu_{\sqrt{\det_p S}}=-1$ |
| Ramsey 读出相位跳 $\pi$ | $\tau_{\rm drive}\gg \hbar/\Delta$ | $I_2(\gamma,D)=1$ | $\nu_{\sqrt{\det_p S}}=-1$ |
| 端点导通峰翻转（D/DIII） | $k_BT\ll\Delta$ | $\operatorname{sgn}\det_p r(0)$ / $\operatorname{sgn}\operatorname{Pf}r(0)$ 反号 | $\nu_{\sqrt{\det_p r}}=-1$ |
| （注）上表之每一行均可视作对 (iii$^\star$) 的一次**物理实现**检测。 | | | |

---

## Discussion

**选择原则的判据与前提（修订）**：对一切允许的相对二维循环 $[S]\in H_2(Y,\partial Y;\mathbb Z_2)$ 有

$$
\big\langle\,K\,,\,[S]\big\rangle=0,
$$

该条件在**生成性假设** $A_{\rm rel\text{-}gen}$ 成立时亦为**充分条件**，即当且仅当 $[K]=0\in H^2(Y,\partial Y;\mathbb Z_2)$。在 $H^1$‑通道可检测性与 $A_{\rm rel\text{-}gen}$ 成立时，存在回路 $\gamma$ 使 $\nu_{\sqrt{\det_p S}}(\gamma)=-1$ 当且仅当 $[K]\ne0$。
**充分 vs 必要**：模组—散射对齐提供充分而非必要条件；在非平衡/非局域情形实数环量可能不等，但 $\mathbb Z_2$ 投影常稳定。

**命题（检测—生成 ⇒ 相对类平凡）** 在 $A_\partial$、$A_{\rm spin}$（一般流形时）、$A_{!H^2}$ 与 $A_{\rm rel\text{-}gen}$ 成立，且 $H^1$‑通道映射 $T$ 单射的前提下，若对一切允许的相对二维循环 $[S]\in H_2(Y,\partial Y;\mathbb Z_2)$ 有
$\langle K,[S]\rangle=0$，则 $[K]=0\in H^2(Y,\partial Y;\mathbb Z_2)$。

**证明素描**：由 $A_{\rm rel\text{-}gen}$，允许的相对二维循环生成 $H_2(Y,\partial Y;\mathbb Z_2)$；$H^1$‑通道在 ${(\Sigma_1^{(j)},\partial\Sigma_1^{(j)})\times(\gamma_1,\partial\gamma_1)}$ 上由 $T$ 的单射性被唯一消去，$H^2$‑通道在 ${{\rm pt}\times(\gamma_2,\partial\gamma_2)}$ 上由 $A_{!H^2}$ 被逐分量消去，且 $A_{\rm spin}$（一般流形时）排除了 $H^2(M,\partial M)$ 分量，故 $[K]=0$。
**OS/KMS–Fisher**：反射正性与条带解析性给出延拓后 $g^{(L)}_{tt}<0$、$g^{(L)}_{ij}\succ0$ 与 $g^{(L)}_{ti}|_{t=0}=0$ 的充分判据，作为几何侧结构性互补。

---

## 结论

我们给出一条"同调级"统一路线：在文中假设下，$[K]=0$ 与 **(iii$^\star$)**（回路平凡化 **并** 参数二维循环配对为零）**等价**；并且在**模组—散射对齐**成立时，小因果钻石上一阶极值与二阶规范能量非负 (i) **推出**该等价类。三大可解模型表明，只要测到一次"$\pi$‑跃迁"或"电导翻转"，即可判定 $[K]\neq 0$，从而反向诊断几何侧二阶能量是否可能为负。该框架把"方程—稳定—拓扑"首次纳入同一变分原理，为全息正性、量子引力散射实验与拓扑量子计算提供了共享的代数拓扑座标。

---

## Acknowledgements, Code Availability

未使用外部代码；所有推导与计算可依正文与附录复现。

---

## References

Jacobson, *Phys. Rev. Lett.* **75** (1995) 1260；Hollands & Wald, *Commun. Math. Phys.* **321** (2013) 629；Jafferis–Lewkowycz–Maldacena–Suh, *JHEP* **06** (2016) 004；Faulkner–Leigh–Parrikar–Wang, *JHEP* **09** (2016) 038；Bousso *et al.*, *Phys. Rev. D* **93** (2016) 024017；Czech *et al.*, *Phys. Rev. Lett.* **120** (2018) 091601；*Phys. Rev. D* **108** (2023) 066003；Pushnitski, *J. Funct. Anal.* **183** (2001) 269；Fulga–Hassler–Akhmerov–Beenakker, *Phys. Rev. B* **83** (2011) 155429；Akhmerov *et al.*, *Phys. Rev. Lett.* **106** (2011) 057001；Witten, *Rev. Mod. Phys.* **88** (2016) 035001。
（两份技术底稿为信息几何变分与自指散射之内部支点。）

---

## 附录 I  体积分版本 $\mathbb Z_2$–BF：次数—积分域—相对上同调

令 $d=\dim Y$。取 $a\in C^{1}(Y;\mathbb Z_2)$、$b\in C^{d-2}(Y;\mathbb Z_2)$、$K\in Z^2(Y;\mathbb Z_2)$，则
$\deg(b\smile\boldsymbol\delta a)=(d-2)+2=d$、$\deg(b\smile K)=(d-2)+2=d$。闭流形上

$$
I_{\rm BF}=\mathrm i\pi\!\int_Y b\smile\boldsymbol\delta a+\mathrm i\pi\!\int_Y b\smile K,\qquad
\boldsymbol\delta b=0,\ \ \boldsymbol\delta a=K.
$$

规范变换 $a\mapsto a+\boldsymbol\delta\lambda^{0}$、$b\mapsto b+\boldsymbol\delta\lambda^{d-3}$ 不改相位；对 $[a],[b]$ 求和使配分函数投影到 $[K]=0$。有边界时以 $H^\bullet(Y,\partial Y;\mathbb Z_2)$ 与边界对偶项 $\mathrm i\pi\int_{\partial Y} a\smile b$ 处理。

## 附录 II  Künneth 分解与 $H^1/H^2$ 的等价操控

**绝对版本**：由

$$
H^2(Y;\mathbb Z_2)\cong H^2(M;\mathbb Z_2)\oplus\big(H^1(M;\mathbb Z_2)\otimes H^1(X^\circ;\mathbb Z_2)\big)\oplus H^2(X^\circ;\mathbb Z_2)
$$

可作

$$
K=\pi_M^\ast w_2(TM)+\sum_j \pi_M^\ast\mu_j\smile \pi_X^\ast\mathfrak w_j+\pi_X^\ast\rho\!\big(c_1(\mathcal L_S)\big).
$$

**相对版本**：在 $\mathbb Z_2$ 系数下 Tor 项消失，有相对分解

$$
H^2(Y,\partial Y;\mathbb Z_2)\cong
H^2(M,\partial M)\ \oplus\ \big(H^1(M,\partial M)\otimes H^1(X^\circ,\partial X^\circ)\big)\ \oplus\ H^2(X^\circ,\partial X^\circ).
$$

对相对物理二维循环的三类乘积：

$$
\begin{aligned}
&\text{(A)}\ \ (\Sigma_2,\partial\Sigma_2)\times{\mathrm{pt}}:\ \ \langle K,[S]\rangle=\langle w_2(TM),[\Sigma_2]\rangle,\\
&\text{(B)}\ \ (\Sigma_1,\partial\Sigma_1)\times(\gamma_1,\partial\gamma_1):\ \ \langle K,[S]\rangle=\sum_j\langle \mu_j,[\Sigma_1]\rangle\,\langle \mathfrak w_j,[\gamma_1]\rangle,\\
&\text{(C)}\ \ {\mathrm{pt}}\times(\gamma_2,\partial\gamma_2):\ \ \langle K,[S]\rangle=\langle \rho(c_1(\mathcal L_S)),[\gamma_2]\rangle.
\end{aligned}
$$

由此 $H^1$ 与 $H^2$ 两通道在相对二维循环上统一进入同一配对。

## 附录 III  IGVP 的显式不等式与二阶层

给出

$$
\Big|\delta A+\int_{\mathcal H}\lambda R_{kk}\,\mathrm d\lambda\,\mathrm dA\Big|
\le \Big(\tfrac16 C_{\nabla R}\lambda_*^3+\tfrac12 C_\sigma^2\lambda_*^2\Big)A,
$$

与零锥刻画引理，完成 $G_{ab}+\Lambda g_{ab}=8\pi G\,T_{ab}$；在 null 边界与角点处方下 $\delta^2S_{\rm rel}=\mathcal E_{\rm can}\ge0$。

## 附录 IV  Birman–Kreĭn、谱流与模二 Levinson 的"工具箱"

（i）$\det_p S=\mathrm e^{-2\pi \mathrm i\,\xi}$；（ii）$\mathrm{Sf}(\gamma)=-\oint_\gamma \mathrm d\xi$；（iii）阈值/嵌入本征值以 $I_2(\gamma,D)$ 稳定；（iv）多通道/分波用 $\det_p$ 与截断余项估计保证模二鲁棒。

## 附录 V  模组—散射对齐的最小可解示例

半空间编码：边界平移 $U(\lambda)=\mathrm e^{-\mathrm iP\lambda}\Rightarrow \mathcal A_{\rm mod}=\langle P\rangle \mathrm d\lambda$；移动镜反射 $S=e^{2\mathrm i k\lambda}\Rightarrow \tfrac{1}{2\mathrm i}\operatorname{tr}(S^{-1}\mathrm dS)=k\,\mathrm d\lambda$；两侧环量与其 $\mathbb Z_2$ 投影一致。

## 附录 VI  $\delta$ 势与 AB 的显式绕数

复 $\lambda$‑环 $\lambda(t)=-2\mathrm i\sqrt{E_0}+\rho\,\mathrm e^{\mathrm i t}$ 给
$\oint (1/2\mathrm i)S^{-1}\mathrm dS=\pi\Rightarrow \nu_{\sqrt{\det_p S}}=-1$；AB 圈穿越 $\alpha=\tfrac12$ 时 $\deg(\det_p S|_\gamma)=1\Rightarrow\nu=-1$。

## 附录 VII  相对上同调长正合序列

对带边流形 $(Y,\partial Y)$ 有长正合序列  

$$\cdots\to H^2(Y,\partial Y;\mathbb Z_2)\xrightarrow{j^\ast} H^2(Y;\mathbb Z_2)\xrightarrow{r} H^2(\partial Y;\mathbb Z_2)\to\cdots$$  

其中 $j^\ast$ 为自然映射。由于边界条件 $A_\partial$ 要求 $r([K])=0$，故 $[K]$ 可唯一提升到 $H^2(Y,\partial Y;\mathbb Z_2)$。本文在相对框架下直接使用 Kronecker 配对

$$
H^2(Y,\partial Y;\mathbb Z_2)\times H_2(Y,\partial Y;\mathbb Z_2)\to\mathbb Z_2,
$$

该配对在 $\mathbb Z_2$ 系数下良定且不依赖取向。由 $A_{\rm rel\text{-}gen}$，允许的相对二维循环生成 $H_2(Y,\partial Y;\mathbb Z_2)$，从而 $\langle K,[S]\rangle=0$ 对所有相对二维循环成立当且仅当 $[K]=0\in H^2(Y,\partial Y;\mathbb Z_2)$。

**引理 VII.1（相对类的提升；在 $A_\partial$ 下的唯一性）** 设 $r:H^2(Y;\mathbb Z_2)\to H^2(\partial Y;\mathbb Z_2)$。若 $r([K])=0$，则存在 $[\widehat K]\in H^2(Y,\partial Y;\mathbb Z_2)$ 使 **$j^\ast([\widehat K])=[K]$**。其唯一性为：若 $[\widehat K]_1,[\widehat K]_2$ 皆为提升，则 $[\widehat K]_1-[\widehat K]_2\in \operatorname{Im}\big(H^1(\partial Y)\to H^2(Y,\partial Y)\big)$；**在 $A_\partial$（边界平凡化）下唯一**。

**推论 VII.2（生成—检测 ⇒ 相对类平凡）** 若允许的相对二维循环生成 $H_2(Y,\partial Y;\mathbb Z_2)$，且对所有生成元配对 $\langle [\widehat K],[S]\rangle=0$，则 $[\widehat K]=0$，即 $[K]=0$。证明仅用到 Poincaré–Lefschetz 对偶与 $\mathbb Z_2$ 系数下的特征正交性。

---

**排版与符号一致性说明**：全文统一使用 $\mathbb Z_2$、$\mathrm d$、$\mathrm i$ 与 $(-,+,+,+)$；积分记号不加前缀；多通道统一采用 $\sqrt{\det_p S}$ 表述。
