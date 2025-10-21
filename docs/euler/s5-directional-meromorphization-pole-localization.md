# S5. 沿方向的亚纯化与极点定位

**—— 方向计数、指数–多项式渐近与 Laplace–Stieltjes 极点结构**

## 摘要（定性）

在 S1 的管域/换序基线与 S2/S3/S4 的镜像—延拓范式之上，建立沿给定方向的计数/加权累积与其 Laplace–Stieltjes 变换之间的统一解析结构：当方向计数或加权累积具有限的指数–多项式渐近时，其沿方向的拉普拉斯–Stieltjes 变换在适当半平面内亚纯，全部极点由各指数率项的主尺度产生，极点位置由指数率决定、阶数受对应多项式次数的上界约束；在自然的单调/非负或变差控制下，反向可由变换的极点型奇性回推出计数的指数–多项式主项。该结果与 S4 的"极点 = 主尺度"原则一致，并与 S2 的二项闭合—横截几何、S3 的完成函数模板（$\Gamma/\pi$ 正规化）相互拼接。

---

## 0. 记号与前置（与 S1/S2/S3/S4 对齐）

**方向切片与参数化。** 固定方向 $\mathbf v\in\mathbb S^{n-1}$ 与横向偏置 $\rho_\perp$（$\langle\rho_\perp,\mathbf v\rangle=0$），记

$$
\rho=\rho_\perp+s\,\mathbf v,\qquad s\in\mathbb C\ \text{（随后在绝对收敛半平面内按管域准则复化使用）} .
$$

对离散谱

$$
F(\theta,\rho)=\sum_{j} c_j\,\mathrm e^{\,\mathrm i\langle\alpha_j,\theta\rangle}\,\mathrm e^{\,\langle\beta_j,\rho\rangle},
$$

定义方向位移

$$
t_j:=\langle-\beta_j,\mathbf v\rangle .
$$

**方向计数与加权累积。**

$$
N_{\mathbf v}(t):=\#\{j:\ t_j\le t\},\qquad
M_{\mathbf v}(t;\theta,\rho_\perp):=\sum_{t_j\le t} c_j\,\mathrm e^{\,\langle\beta_j,\rho_\perp\rangle}\,\mathrm e^{\,\mathrm i\langle\alpha_j,\theta\rangle}.
$$

两者视作右连续、局部有界变差函数（或相应 Stieltjes 测度的分布函数）。

【边界规范化与起点】如存在有限个 $t_j<0$ 的初始点，其贡献可吸收进常数（或整函数）项而不影响后续极点定位。为避免符号歧义并保证边界项消失，以下均采用规范化：

$$
N_{\mathbf v}(0^+)=M_{\mathbf v}(0^+)=0,\qquad t_j\ge0\ (\forall j) .
$$

如未做规范化，有限个 $t_j<0$ 的项在方向变换中仅贡献常数/整函数，不改变 $\mathscr N_{\mathbf v}$ 与 $\mathcal L_{\mathbf v}$ 的极点集合与阶。

**方向 Laplace–Stieltjes 变换（收敛半平面内）。**

$$
\mathscr N_{\mathbf v}(s):=\int_{0}^{\infty} \mathrm e^{-s t}\,\mathrm dN_{\mathbf v}(t)
=\sum_{t_j\ge0}\mathrm e^{-s t_j}
=\sum_{t_j\ge0} \mathrm e^{\,s\langle\beta_j,\mathbf v\rangle},
$$

$$
\mathcal L_{\mathbf v}(s;\theta,\rho_\perp):=\int_{0}^{\infty} \mathrm e^{-s t}\,\mathrm dM_{\mathbf v}(t;\theta,\rho_\perp)
=\sum_{t_j\ge0} c_j\,\mathrm e^{\,\langle\beta_j,\rho_\perp+s\mathbf v\rangle}\,\mathrm e^{\,\mathrm i\langle\alpha_j,\theta\rangle}.
$$

因此在绝对收敛半平面内（并在上述规范化下），

$$
\mathcal L_{\mathbf v}(s;\theta,\rho_\perp)=F\big(\theta,\rho_\perp+s\,\mathbf v\big).
$$

**工作准则。** 一切换序/逐项操作遵循 S1 的管域与主导收敛准则；离散—连续桥接仅使用 S4 的**有限阶** Euler–Maclaurin（EM）分解，其伯努利层与余项在参数 $s$ 上全纯/整函数，不改变极点集合。

**局部零结构接口。** 在主导两项情形，使用 S2 的二项闭合—横截模板判定方向切片上一元函数零的简单性与局部结构。

**完成函数接口。** 必要时使用 S3 的 $\Gamma/\pi$ 正规化因子于乘法侧配平增长并构造对称完成函数。

---

## 1. 收敛阈与基本半平面

**引理 5.1（方向绝对收敛的阈值）。** 设

$$
\gamma_{\mathrm{abs}}:=\limsup_{t\to\infty}\frac{1}{t}\log N_{\mathbf v}(t)\in[-\infty,\infty] .
$$

则：
(i) 当 $\Re s>\gamma_{\mathrm{abs}}$ 时，$\mathscr N_{\mathbf v}(s)$ 绝对收敛；
(ii) **若存在无穷多跳点**（即 $N_{\mathbf v}(t)\to\infty$），且 $\Re s<\gamma_{\mathrm{abs}}$，则 $\mathscr N_{\mathbf v}(s)$ 发散。**若仅有限个跳点**，则 $\mathscr N_{\mathbf v}(s)$ 为有限和因而在 $s$ 平面整，断言 (ii) 不适用。
在命题 5.3 的**局部多项式有界**前提下（权重在单位长度区间内受控），$\mathcal L_{\mathbf v}(s)$ 与 $\mathscr N_{\mathbf v}(s)$ 具有相同的方向绝对收敛半平面与阈值；否则权重可能改变绝对收敛阈值。

*证明*。对任意 $\varepsilon>0$，存在 $T$ 使 $N_{\mathbf v}(t)\le C\,\mathrm e^{(\gamma_{\mathrm{abs}}+\varepsilon)t}$（$t\ge T$）。分部积分得

$$
\int_0^\infty \mathrm e^{-s t}\,\mathrm dN_{\mathbf v}(t)
=s\int_0^\infty \mathrm e^{-s t}N_{\mathbf v}(t)\,\mathrm dt
\; +\;\big[\mathrm e^{-s t}N_{\mathbf v}(t)\big]_{0^+}^{\infty},
$$

当 $\Re s>\gamma_{\mathrm{abs}}+\varepsilon$ 时右端有界且边界项消失，得 (i)。反向取子列 $t_k\to\infty$ 使 $N_{\mathbf v}(t_k)\ge \mathrm e^{(\gamma_{\mathrm{abs}}-\varepsilon)t_k}$，与几何级数对比得 (ii)。当且仅当存在无穷多跳点（$N_{\mathbf v}(t)\to\infty$）时，收敛边界（abscissa）满足
$$
\sigma_a\;=\;\limsup_{t\to\infty}\frac{1}{t}\log N_{\mathbf v}(t),
$$
参见 Widder《The Laplace Transform》或 Doetsch《Laplace Transformation》。若仅有限跳点，则约定 $\sigma_a:=-\infty$（此时 $\mathscr N_{\mathbf v}$ 为整函数）。此外，在命题 5.3 的**局部多项式有界**前提下，$\mathcal L_{\mathbf v}$ 与 $\mathscr N_{\mathbf v}$ 具有相同的方向绝对收敛半平面；若仅有限跳点，则二者在 $s$ 平面整，收敛边界按约定取 $-\infty$。$\square$

---

## 2. 指数–多项式主项 $\Rightarrow$ 亚纯延拓与极点上界

**定义 5.2（方向指数–多项式渐近）。** 称 $M_{\mathbf v}(t)$ 在 $t\to\infty$ 具有**有限指数–多项式渐近**，若存在有限指标集 $\mathcal I$、实数 $\gamma_\ell$（允许重复）、多项式 $Q_\ell$ 及 $\eta>0$，使

$$
M_{\mathbf v}(t)=\sum_{\ell\in\mathcal I} Q_\ell(t)\,\mathrm e^{\gamma_\ell t}
\;+\; O\left(\mathrm e^{(\gamma_\ast-\eta)t}\right),\qquad \gamma_\ast:=\max_{\ell}\gamma_\ell ,
$$

且 $M_{\mathbf v}$ 局部有界变差、右连续。将此定义用于非加权计数 $N_{\mathbf v}$ 时，$Q_\ell$ 取实多项式且系数非负。

为处理重复速率，记唯一速率集合 $\Gamma:=\{\gamma:\ \exists\,\ell\in\mathcal I,\ \gamma_\ell=\gamma\}$，并对每个 $\gamma\in\Gamma$ 定义聚合多项式
$$
Q_\gamma(t):=\sum_{\ell:\,\gamma_\ell=\gamma} Q_\ell(t)
=\sum_{r=0}^{d_\gamma} a_{\gamma,r}\,t^r,\qquad d_\gamma:=\deg Q_\gamma.
$$

**定理 T5.1（Abelian 方向亚纯化与极点上界）。** 若 $M_{\mathbf v}$ 满足定义 5.2，则 $\mathcal L_{\mathbf v}(s)$ 在半平面 $\Re s>\gamma_\ast-\eta$ **亚纯**，其全部极点均位于 $\{s=\gamma:\ \gamma\in\Gamma\}$，并且

$$
\operatorname{ord}_{\,s=\gamma}\mathcal L_{\mathbf v}\ \le\ d_\gamma+1\qquad(\gamma\ne0),
$$
当 $\gamma=0$ 时，整体 $s$ 因子消去一阶，进一步有
$$
\operatorname{ord}_{\,s=0}\mathcal L_{\mathbf v}\ \le\ d_0.
$$

更具体地，若

$$
Q_\gamma(t)=\sum_{r=0}^{d_\gamma} a_{\gamma,r}\,t^r,
$$

则在 $s=\gamma$ 邻域有主部展开

$$
\mathcal L_{\mathbf v}(s)
=\sum_{\gamma\in\Gamma}\left[\,s\sum_{r=0}^{d_\gamma} a_{\gamma,r}\,\frac{r!}{(s-\gamma)^{r+1}}\right]\;+\;H(s),
$$

其中 $H$ 在 $\Re s>\gamma_\ast-\eta$ 全纯。

*证明（补充与引用）。* 记 $\mathrm dM_{\mathbf v}$ 为 $M_{\mathbf v}$ 的 Stieltjes 测度。对 $\Re s>\gamma_\ast$ 有

$$
\mathcal L_{\mathbf v}(s)=\int_0^\infty \mathrm e^{-s t}\,\mathrm dM_{\mathbf v}(t)
=s\int_0^\infty \mathrm e^{-s t}M_{\mathbf v}(t)\,\mathrm dt .
$$

代入渐近式并逐项积分：第二项在 $\Re s>\gamma_\ast-\eta$ 全纯；第一项对每个 $(\ell,r)$ 给出

$$
s\,a_{\ell,r}\int_0^\infty t^r\,\mathrm e^{-(s-\gamma_\ell)t}\,\mathrm dt
=s\,a_{\ell,r}\,\frac{r!}{(s-\gamma_\ell)^{r+1}},
$$

由解析延拓唯一性得结论。这可视为 Abelian/传递定理的直接实例：$\int_0^\infty t^r\mathrm e^{-(s-\gamma)t}\,dt=r!/(s-\gamma)^{r+1}$ 给出极点结构（参见 Flajolet–Sedgewick《Analytic Combinatorics》；Widder；Doetsch）。$\square$

**计数版。** 对 $\mathscr N_{\mathbf v}$ 结论相同；在率 $\gamma$ 处最高阶主部系数为 $\gamma\,a_{\gamma,d_\gamma}\,d_\gamma!$（$\gamma\ne0$）。若 $\gamma\ge 0$ 则该系数非负；$\gamma=0$ 时为 $0$；$\gamma<0$ 时为非正。

**与 S4 的一致性。** 伯努利层与余项在 $s$ 上全纯，仅主尺度项可能产生极点，故"极点 = 主尺度"。

---

## 3. 从计数到加权：极点位置不右移（阶至多增加 $\kappa$）

**命题 5.3（位置不右移；阶的上界）。** 设 $M_{\mathbf v}$ 与 $N_{\mathbf v}$ 的跳点相同，且存在常数 $C,\kappa\ge0$ 使

$$
\sup_{t<\tau\le t+1}\big|M_{\mathbf v}(\tau)-M_{\mathbf v}(t)\big|
\le C(1+t)^\kappa\,
\sup_{t<\tau\le t+1}\big(N_{\mathbf v}(\tau)-N_{\mathbf v}(t)\big).
$$

若 $N_{\mathbf v}$ 满足定义 5.2，则 $M_{\mathbf v}$ 满足上界
$$
M_{\mathbf v}(t)\ \ll\ \sum_{\ell}\,(1+t)^{\deg Q_\ell(N_{\mathbf v})+\kappa}\,\mathrm e^{\gamma_\ell t},
$$
因而其**最大指数率不大于**计数侧（极点位置不右移），并且**绝对收敛半平面不右移**。仅凭上述上界**不能**断言极点阶。

若**进一步假设** $M_{\mathbf v}$ **亦满足定义 5.2**（例如：权重最终非负、单位区间内多项式有界且**无系统性抵消**，使其拥有与计数侧相同的速率集并存在带隙 $\eta>0$），**则**由 T5.1 可得
$$
\operatorname{ord}_{\,s=\gamma}\mathcal L_{\mathbf v}\ \le\ d_\gamma(N_{\mathbf v})+\kappa+1\qquad(\gamma\ne 0),
$$
且在 $\gamma=0$ 时
$$
\operatorname{ord}_{\,s=0}\mathcal L_{\mathbf v}\ \le\ d_0(N_{\mathbf v})+\kappa .
$$

特例：当 $\kappa=0$（单位区间内权重一致有界）时，有
$$
\operatorname{ord}_{\,s=\gamma_\ell}\mathcal L_{\mathbf v}\ \le\ \deg Q_\ell(N_{\mathbf v})+1,\qquad\text{且极点位置不右移}.
$$
若并且计数侧在 $s=\gamma_\ell$ 处**达到上界**（例如非负/无系统性抵消，使 $\operatorname{ord}_{\,s=\gamma_\ell}\mathscr N_{\mathbf v}=\deg Q_\ell(N_{\mathbf v})+1$），则进一步有（阶不增）
$$
\operatorname{ord}_{\,s=\gamma_\ell}\mathcal L_{\mathbf v}\ \le\ \operatorname{ord}_{\,s=\gamma_\ell}\mathscr N_{\mathbf v}\qquad\text{（阶不增）},
$$
并且位置与阶与计数侧一致（仅主部系数改变）。

*证明略*（分部求和与局部有界振幅控制）。$\square$

**说明.** 在母映射中，权重 $c_j\,\mathrm e^{\langle\beta_j,\rho_\perp\rangle}\,\mathrm e^{\mathrm i\langle\alpha_j,\theta\rangle}$ 在单位长度的 $\langle-\beta_j,\mathbf v\rangle$ 区间内多项式有界，极点几何的**位置**由指数率决定而与相位层无涉；对**极点阶**，仅在 $\kappa=0$ 时与计数侧一致，否则至多增加 $\kappa$。

---

## 4. 方向 Tauberian：极点 $\Rightarrow$ 指数–多项式主项

**定理 T5.2（单极点的 Tauberian 反演，Ikehara–Delange 型）。** 设 $\mathscr N_{\mathbf v}(s)$ 在 $\Re s>\gamma_0$ 全纯并可延拓至包含 $\Re s\ge\gamma_0$ 的开邻域，在 $s=\gamma_0$ 有阶 $m\ge1$ 的极点，且
$$
G(s):=\mathscr N_{\mathbf v}(s)-\sum_{r=1}^{m}\frac{A_{-r}}{(s-\gamma_0)^r}
$$
在上述邻域内有界（例如：在 $\Re s=\gamma_0$ 具有连续且有界的边界值，且 $G(\gamma_0+iy)=o(1)$ 当 $|y|\to\infty$）。若 $N_{\mathbf v}$ 非减（或最终非减），则

若 $\gamma_0\ne 0$，则
$$
N_{\mathbf v}(t)=\frac{A_{-m}}{\gamma_0\,(m-1)!}\,\mathrm e^{\gamma_0 t}\,t^{m-1}
+o\big(\mathrm e^{\gamma_0 t}t^{m-1}\big)\qquad (t\to\infty).
$$
若 $\gamma_0=0$，则
$$
N_{\mathbf v}(t)=\frac{A_{-m}}{m!}\,t^{m}\,+o\big(t^{m}\big)\qquad (t\to\infty).
$$

*证明要点（补充与引用）。* 取 $\sigma>\gamma_0$，用 Laplace–Stieltjes 反演

$$
\frac{N_{\mathbf v}(t+)+N_{\mathbf v}(t-)}{2}
=\frac{1}{2\pi\mathrm i}\int_{\Re s=\sigma}\frac{\mathscr N_{\mathbf v}(s)}{s}\,\mathrm e^{s t}\,\mathrm ds,
$$

向左移路至 $\Re s=\gamma_0+\varepsilon$ 并取环绕 $s=\gamma_0$ 的小圆，主部来自该极点的留数；其余边界在单调性与 $G$ 的垂线增长控制下为低阶项。此为一侧 Tauberian 范畴的典型结论：对非减（或最终非减）$N_{\mathbf v}$，在 $s=\gamma_0$ 的有限阶极点蕴含 $N_{\mathbf v}(t)\sim c\,\mathrm e^{\gamma_0 t}t^{m-1}$（参见 Korevaar, Tauberian Theory；Feller, Vol. II）。$\square$

*注。* 若失去单调性，可在全变差有界与局部平均化条件下得到 $\ll \mathrm e^{\gamma_0 t}t^{m-1}$ 的上界；等号型结论需更强 Tauberian 工具。

---

## 5. 极点阶的上—下界与主项系数

若

$$
M_{\mathbf v}(t)\sim \sum_{\ell} Q_\ell(t)\,\mathrm e^{\gamma_\ell t},\qquad
Q_\ell(t)=\sum_{r=0}^{d_\ell} a_{\ell,r} t^r,
$$

则由 T5.1

$$
\operatorname{ord}_{\,s=\gamma_\ell}\mathcal L_{\mathbf v}\le d_\ell+1,
$$

且最高阶主部系数为

$$
\operatorname{Coeff}_{(s-\gamma_\ell)^{-(d_\ell+1)}}\mathcal L_{\mathbf v}(s)
=\gamma_\ell\,a_{\ell,d_\ell}\,d_\ell! .
$$

反向地，在 T5.2 的单极点情形，若 $m=d+1$ 且 $A_{-m}\neq0$，则

$$
a_{d}=\frac{A_{-m}}{\gamma_0\,d!}
$$

若 $\gamma_0=0$，则 $m=d$，并且
$$
a_{d}=\frac{A_{-d}}{d!}.
$$

当 $\gamma_\ell=0$ 时，由于主部存在整体 $s$ 因子，极点阶自动降一阶，普遍上界可收紧为
$$
\operatorname{ord}_{\,s=\gamma_\ell}\mathcal L_{\mathbf v}\ \le\ d_\ell\qquad(\gamma_\ell=0).
$$

给出主项最高次系数。

---

## 6. 与 S4 的 EM 范式拼接（"极点 = 主尺度"）

对沿方向的离散和（如 $\sum_k f(a+k\Delta;s)$ 或更一般的谱和），采用 S4 的**有限阶** EM 分解为"主尺度积分 + 若干伯努利层 + 余项"。伯努利层与余项在 $s$ 上全纯/整函数，仅主尺度项可能产生极点；与第 2 节的指数–多项式主项相结合，可在所需竖条内完成**亚纯延拓与极点定位**。

---

## 7. 方向零–极点的互补几何（与 S2 对齐）

在方向切片 $\rho=\rho_\perp+s\mathbf v$ 上，若某区段由两项主导，则 S2 的**二项闭合**给出零的局部方程（相位对径与幅度平衡），一般位置下零为**简单零**。与之互补地，**极点**来自方向累积（计数或加权）之指数增长，并非由局部两项相消产生。于是，截面函数的零—极点在几何上互补。

---

## 8. 完成函数与增长配平（与 S3 对齐）

为在更宽竖条上控制垂线增长或实现关于 $\Re s=\tfrac a2$ 的镜像对称，可取 S3 的 $a$-对称 $\Gamma/\pi$ 因子 $r(s)$，定义完成函数

$$
\Xi_{\mathbf v}(s):=r(s)\,\mathcal L_{\mathbf v}(s).
$$

在 T5.1 的半平面内，$\Xi_{\mathbf v}$ 仍亚纯；借助 Stirling 估计，沿垂线的指数增长得到配平。若 $r$ 同时消去主尺度极点，则 $\Xi_{\mathbf v}$ 在该半平面内全纯（无极点）。

---

## 9. 反例与边界族（失效原因标注）

* **R5.1（亚指数累积）**：若 $N_{\mathbf v}(t)$ 仅有 $\mathrm e^{\sqrt t}$ 级增长，则 $\mathscr N_{\mathbf v}$ 仅在 $\Re s>0$ 收敛且一般**无极点**；指数–多项式前提不成立。
* **R5.2（剧烈振荡权重）**：若加权跳跃在单位区间内呈超多项式爆长，命题 5.3 失效，可导致极点阶上升或出现自然边界。
* **R5.3（无限伯努利层）**：将 EM 误作**无穷级数**会破坏一致可和并伪造极点；必须坚持**有限阶**并验证余项全纯。
* **R5.4（方向退化）**：若 $\langle\beta_j-\beta_k,\mathbf v\rangle\equiv0$（所有项沿该方向同速），则方向切片退化；零/极点结构需改以横向参数（$\theta$ 或 $\rho_\perp$）展开。

---

## 10. 统一"可检清单"（最小充分条件）

1. **收敛半平面**：计算 $\gamma_{\mathrm{abs}}=\limsup_{t\to\infty}t^{-1}\log N_{\mathbf v}(t)$，在 $\Re s>\gamma_{\mathrm{abs}}$ 起步。
2. **指数–多项式主项**：给出 $M_{\mathbf v}$ 或 $N_{\mathbf v}$ 的有限指数–多项式渐近（指数率 $\gamma_\ell$、次数 $d_\ell$、间隙 $\eta>0$）。
3. **亚纯化**：由 T5.1 得到 $\mathcal L_{\mathbf v}/\mathscr N_{\mathbf v}$ 的极点位置 $s=\gamma_\ell$ 与阶上界 $d_\ell+1$。
4. **权重稳健性（上界向）**：核对命题 5.3 的局部多项式有界条件，保证极点位置**不右移**（指数率不大于计数侧）；极点**阶**在 $\kappa=0$ 时**不增**。如需“位置/阶一致”，需另加“无系统性抵消”（如非负权重）假设。
5. **Tauberian 反演（等号型）**：在单调/非负等前提且满足 T5.2 的 Ikehara–Delange 边界条件时，由极点得到指数–多项式主项；若缺少该边界条件，仅可得上界，不保证等号型主项。
6. **EM 拼接**：任何离散—连续互换均以 S4 的有限阶 EM 执行；伯努利层与余项在 $s$ 上全纯。
7. **几何一致性**：主导两项区间内与 S2 的二项闭合—横截模板一致（零的简单性与退化分支）。
8. **增长配平（可选）**：需要镜像/增长控制时，选用 S3 的对称 $\Gamma/\pi$ 因子构造完成函数。

---

## 附录 A：Laplace–Stieltjes 基本公式（变差与分部积分）

令 $G$ 为右连续、局部有界变差函数，$\mathrm dG$ 其 Stieltjes 测度。若 $\Re s>\sigma_0$ 且 $|G(t)|\le C\,\mathrm e^{(\sigma_0+\varepsilon)t}$（$t\ge T$），则

$$
\int_0^\infty \mathrm e^{-s t}\,\mathrm dG(t)
=s\int_0^\infty \mathrm e^{-s t}G(t)\,\mathrm dt\; +\;\big[\mathrm e^{-s t}G(t)\big]_{0^+}^{\infty},
$$

边界项在 $\Re s>\sigma_0+\varepsilon$ 下消失。若再假设 $G$ 非减，则有反演公式

$$
\frac{G(t+)+G(t-)}{2}
=\frac{1}{2\pi\mathrm i}\int_{\Re s=\sigma}\frac{1}{s}\left(\int_0^\infty \mathrm e^{-s u}\,\mathrm dG(u)\right)\mathrm e^{s t}\,\mathrm ds
\quad (\sigma>\sigma_0),
$$

并配合留数定理与垂线增长估计给出 T5.2 的主项与误差控制。

---

## 结语

沿方向的计数/加权累积将母映射的谱—尺度数据压缩为一元可检对象；当其呈有限的**指数–多项式**增长时，沿方向的 Laplace–Stieltjes 变换在适当半平面内**亚纯**，其**极点完全由主尺度决定**：位置等于指数率，阶至多为相应多项式次数加一。该方向版解析结构与 S4 的 EM 范式严格一致，并与 S2 的零集几何、S3 的完成函数模板互补，为后续 S6 的信息刻度与 S7 的 $L$-函数接口提供了可检、可拼接的极点—增长基线。

---

## 参考文献（指引性）

1. D. V. Widder, The Laplace Transform, Princeton Univ. Press.
2. G. Doetsch, Introduction to the Theory and Application of the Laplace Transformation.
3. J. Korevaar, Tauberian Theory: A Century of Developments, Springer.
4. W. Feller, An Introduction to Probability Theory and Its Applications, Vol. II, Wiley.
5. P. Flajolet, R. Sedgewick, Analytic Combinatorics, Cambridge Univ. Press.
