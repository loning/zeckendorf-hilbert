# S13. 大值与 Ω-下界：共振器谱半径、软窗 AFE 与非渐近存在性

**完成函数模板下的大值法（resonance method）与可检下界**

**作者**：Auric
**日期**：2025-10-21

---

## 摘要（定性）

在完成函数与母映射的统一语法下，本文将**软窗近似功能方程（AFE）**、**共振器/放大器的谱变分**与**Pretentious 距离**组织为一套**非渐近、可检**的大值存在性与 Ω-下界框架。核心机制：对任一固定窗权，窗口二次型的**谱半径**给出窗内**点态大值**的阈值；Pretentious 区与非 Pretentious 区分别以"相干链路/非相干链路"提供稳定下界；误差统一由**Nyquist–Poisson–有限阶 Euler–Maclaurin（EM）**三分解精确记账，并与"极点 = 主尺度""方向增长 = 支持函数上包"保持一致。

---

## 0. 记号与前置

### 0.1 完成函数与功能方程

设

$$
\Lambda(s)=Q^{\frac s2}\,r(s)\,L(s),\qquad \Lambda(s)=\varepsilon\,\Lambda(a-s),\quad |\varepsilon|=1,
$$

其中 $r(s)$ 由有限个 $\Gamma$-因子与 $\pi$ 的幂配平，使中心轴为 $\Re s=\tfrac a2$。垂线增长由 $r$ 的 Stirling 展开配平。工作竖条记 $\sigma=\Re s\ge\sigma_0>0$。

### 0.2 窗口化平均、Gram 核与半正性

取 $w\in \mathcal S(\mathbb R)$，$w\ge0$，并假定

$$
0<\int_{\mathbb R} w(t)\,dt<\infty.
$$

定义

$$
\mathbb E_w[F]:=\frac{1}{\int_{\mathbb R} w}\int_{\mathbb R}F(\sigma+it)\,w(t)\,dt,\qquad
|f|_w:=\big(\mathbb E_w[|f|^2]\big)^{1/2}.
$$

对任意有限支撑系数列 $r=(r_n)$ 与 Dirichlet 多项式 $\mathcal R(s)=\sum_{n\le Y} r_n n^{-s}$，有

$$
|\mathcal R|_{w}^{2}
=\frac{1}{\int_{\mathbb R} w}\sum_{m,n\le Y}\frac{r_m\overline{r_n}}{(mn)^\sigma}\,\widehat w\!\big(\log(n/m)\big)
=:\langle r,Gr\rangle,
$$

其中 $\widehat w(\xi):=\int_{\mathbb R}e^{-it\xi}w(t)\,dt$，

$$
G_{mn}:=\frac{(mn)^{-\sigma}}{\int_{\mathbb R} w}\,\widehat w\!\big(\log(n/m)\big).
$$

由构造 $\langle r,Gr\rangle=\mathbb E_w[|\mathcal R|^2]\ge0$，故 $G$ **半正定**。选窗 $w$ 使 $(G_{mn})_{m,n\le Y}$ 可逆；若退化，则在等价范数中添加微正则化

$$
\langle r,Gr\rangle\rightsquigarrow \langle r,Gr\rangle+\eta\sum_{n\le Y}\frac{|r_n|^2}{n^{2\sigma}}\quad(\eta>0),
$$

所有结论对 $\eta\to0$ 连续。全程在 $\eta\downarrow0$ 的极限下解读广义本征对与 Paley–Zygmund，以排除“取极向量 vs. 去正则”的次序歧义。

### 0.3 软窗 AFE（双窗型）

取偶窗 $h$。记 $H$ 为 $h$ 的 Mellin 变换（或在合适归一下的 Fourier 变换）。存在与 $(h,r,Q)$ 相容的光滑核 $V_\pm(x;s)$，使

$$
\Lambda(s)=\sum_{n\ge1}\frac{a_n}{n^{s}}\,V_+\!\Big(\frac{n}{Q^{1/2}};s\Big)
+\varepsilon\sum_{n\ge1}\frac{a_n^\ast}{n^{a-s}}\,V_-\!\Big(\frac{n}{Q^{1/2}};s\Big)+R(s;h),
$$

**算术侧**：$(a_n^\ast)$ 为对偶 $L^\ast$ 的 Dirichlet 系数；自对偶时依标准归一有 $a_n^\ast=\overline{a_n}$。**一般情形下 $\overline{L}$ 的交叉项涉及 $\overline{a_n^\ast}$，非 $a_n^\ast$**，相应出现在 $K_{mn}$ 的 $+\!-$ 与 $-\!+$ 行。本文所有换序与端点处理**一律采用有限阶 EM**；余项全纯/整，极点仅由主尺度项产生。

**余项 $R(s;h)$ 的整性**：若**变换** $H\in\mathrm{PW}_B$（Paley–Wiener 类，即带限）且 $V_\pm$ 由 Mellin–Barnes 表达并在以 $r(s)$ 配平 $\Gamma$-增长后不再引入新的 $s$-方向指数增长，则 $R(\cdot;h)$ 为指数型（$\le B$）的整函数；若 $h\in\mathcal S(\mathbb R)$（快衰窗），则仅保证 $R$ 全纯且在竖条上次指数增长。

### 0.4 共振器二次型、广义本征问题与自伴性

置

$$
Z(s):=L(s)\,\mathcal R(s),\qquad
|Z|_w^2=\langle r,\mathsf K r\rangle,
$$

其中 $\mathsf K$ 为由 AFE 与 $w$ 诱导的有限维核算子。令

$$
\langle u,\mathsf K v\rangle:=\mathbb E_w\!\big[(L\mathcal R_u)\,\overline{(L\mathcal R_v)}\big].
$$

因 $w$ 取实且 $h$ 取偶并可取实，$V_\pm(\sigma+it)$ 满足 $\overline{V_\pm(\sigma+it)}=V_\pm(\sigma-it)$，据此

$$
\langle u,\mathsf K v\rangle=\overline{\langle v,\mathsf K u\rangle},
$$

故 $\mathsf K$ 在此二次型下自伴且半正。定义**谱半径**

$$
\lambda_{\max}:=\sup_{r\ne0}\frac{\langle r,\mathsf K r\rangle}{\langle r,Gr\rangle}.
$$

由有限维谱定理，存在单位 $G$-范数本征向量 $r^\star$ 使

$$
\mathsf K r^\star=\lambda_{\max}\,G r^\star,\qquad \langle r^\star,Gr^\star\rangle=1.
$$

### 0.5 Pretentious 距离、适用域与幅度基线

对 $|f(n)|\le 1$ 的乘法函数，定义

$$
\mathbb D_{\sigma,X}(f; t)^2
:=\sum_{p\le X}\frac{1-\Re(f(p)p^{-it})}{p^\sigma}.
$$

**适用域**：本文中与 Pretentious 距离相关的结论适用于 GL(1)（如 Dirichlet $L$）或经归一使 Dirichlet 系数满足 $|f(n)|\le1$ 的情形；**高阶族不可直接移用 $\mathbb D_{\sigma,X}$**，需改用（谱）大筛替代版本。特别提醒：**高阶族请勿直接移用本节 Pretentious 公式**，必须改用谱化大筛版本。
定义**幅度基线**

$$
A_\sigma(X):=\Big(\sum_{n\le X}n^{-2\sigma}\Big)^{1/2}.
$$

---

## 1. 谱半径 $\Rightarrow$ 点态大值

### 定理 1.1（RMS–sup 与 Paley–Zygmund 的谱阈值）

对广义本征对 $(\mathsf K,G)$ 的最大本征向量 $r^\star$，记 $\mathcal R^\star(s)=\sum_{n\le Y}r_n^\star n^{-s}$。则

$$
\sup_{t\in\mathrm{supp}(w)}|L(\sigma+it)\,\mathcal R^\star(\sigma+it)|\ \ge\ \sqrt{\lambda_{\max}}.
$$

进一步，若存在显式常数 $M_4(w,h;Y)$ 满足

$$
|L\,\mathcal R|_{w,4}^{4}\ \le\ M_4(w,h;Y)\,\big(|L\,\mathcal R|_{w}^{2}\big)^{2}\quad(\text{对所有 }\mathcal R),
$$

则存在 $t_0\in\mathrm{supp}(w)$ 使

$$
|L(\sigma+it_0)\,\mathcal R^\star(\sigma+it_0)|\ \ge\ (1-\theta)\sqrt{\lambda_{\max}}.
$$

为书写简洁，记

$$
d\mu_w(t):=\frac{w(t)\,dt}{\int_{\mathbb R} w},\qquad \mathbb P_w(\cdot)\ \text{为由 }d\mu_w\text{ 诱导的概率测度}.
$$

**证明**。一方面，

$$
|L\,\mathcal R^\star|_{w}^{2}=\langle r^\star,\mathsf K r^\star\rangle=\lambda_{\max}\langle r^\star,Gr^\star\rangle=\lambda_{\max}.
$$

由二次均值（RMS）不超过上确界（$|Z|_{w}=\big(\mathbb E_w[|Z|^2]\big)^{1/2}\le |Z|_{L^\infty(\mathrm{supp}\,w)}$）得第一不等式。另一方面取 $X:=|Z|^{2}\ge0$，令 $\alpha\in(0,1)$，Paley–Zygmund 给出

$$
\mathbb P_w\!\big(|Z|\ge \alpha\,|Z|_{w}\big)\ \ge\ \frac{\big(1-\alpha^2\big)^{2}}{M_4(w,h;Y)}.
$$

取阈值 $\alpha=1-\theta$ 时，

$$
\mathbb P_w\!\big(|Z|\ge (1-\theta)\,|Z|_{w}\big)\ \ge\ \frac{\big(2\theta-\theta^2\big)^2}{M_4(w,h;Y)}.
$$

□

### 推论 1.2（转化为 $|L|$ 的下界）

若在 $\mathrm{supp}(w)$ 上 $|\mathcal R^\star(\sigma+it)|\le B$，其中可用 Cauchy–Schwarz 给出

$$
\sup_{t\in\mathrm{supp}(w)}\big|\mathcal R(\sigma+it)\big|
\le \Big(\sum_{n\le Y}|r_n|^2\Big)^{1/2}\Big(\sum_{n\le Y}n^{-2\sigma}\Big)^{1/2},
$$

则

$$
\sup_{t\in\mathrm{supp}(w)}|L(\sigma+it)|\ \ge\ B^{-1}\sqrt{\lambda_{\max}}.
$$

**说明**：该界与广义本征归一 $\langle r,Gr\rangle=1$ 无冲突（缩放不改变 Rayleigh 商），只需报告实际解得的 $B$ 或采用 $\ell^2$ 归一的保守界。若将 $B$ 规模化为 1，则需在优化问题中显式约束 $|\mathcal R|_{L^\infty(\mathrm{supp}\,w)}\le1$（见 §8.A）。

---

## 2. AFE-诱导核与四次能量

### 引理 2.1（$\mathsf K$ 的显式表达）

记 $\rho:=m/n$、$x=\tfrac{k}{Q^{1/2}},y=\tfrac{\ell}{Q^{1/2}}$。在 §0.3 的 AFE 下，

$$
|L\,\mathcal R|_{w}^{2}
=\frac{1}{\int_{\mathbb R} w}\sum_{m,n\le Y}\frac{r_m\overline{r_n}}{(mn)^\sigma}\,K_{mn}+\text{整层校正},
$$

其中

$$
\begin{aligned}
K_{mn}
&=\sum_{k,\ell\ge1}\frac{a_k\overline{a_\ell}}{(k\ell)^\sigma}\,B_{++}(x,y,\rho;\sigma)\\
&\quad+\sum_{k,\ell\ge1}\frac{a_k\,\overline{a_\ell^\ast}}{k^\sigma\,\ell^{a-\sigma}}\,B_{+-}(x,y,\rho;\sigma)\\
&\quad+\sum_{k,\ell\ge1}\frac{a_k^\ast\,\overline{a_\ell}}{k^{a-\sigma}\,\ell^\sigma}\,B_{-+}(x,y,\rho;\sigma)\\
&\quad+\sum_{k,\ell\ge1}\frac{a_k^\ast\,\overline{a_\ell^\ast}}{(k\ell)^{a-\sigma}}\,B_{--}(x,y,\rho;\sigma),
\end{aligned}
$$

其中

$$
B_{\circ\circ'}(x,y,\rho;\sigma)=\int_{\mathbb R}V_\circ(x;\sigma+it)\,\overline{V_{\circ'}(y;\sigma+it)}\,\rho^{it}\,w(t)\,dt,\quad \circ,\circ'\in\{+,-\}.
$$

**备注**：自对偶（$a_n^\ast=\overline{a_n}$）时，第二与第三行可合并为 $2\,\Re\big[\sum a_k\overline{a_\ell}\,\cdots B_{+-}\big]$ 的等价写法，但为保持一般性与自伴性，建议保留四项显式展开。**按上式四项展开，$K_{nm}=\overline{K_{mn}}$**。

"整层校正"由 AFE 余项与有限阶 EM 端点项诱导，给出一个有界的自伴扰动矩阵 $\Delta$。故

$$
\big|\lambda_{\max}(\mathsf K+\Delta)-\lambda_{\max}(\mathsf K)\big|
\ \le\ \|\Delta\|_{\mathrm{op}},
$$

且 $\|\Delta\|_{\mathrm{op}}$ 可由 §2.2 的四次能量常数与 §6 的"别名 + 伯努利层 + 窗尾"三项**显式**上界。

**说明**：此处补全 $|L|^2$ 展开后对 $(k,\ell)$ 的双重和与 $+$/$-$ 交叉项（含正确的共轭结构），使 $\langle r,\mathsf K r\rangle=\mathbb E_w[|L\mathcal R|^2]$ 成立。□

### 引理 2.2（四次能量的可检上界）

存在有限常数

$$
M_4=M_4\big(\sigma,w,h;Y,\ |\Xi|_{L^\infty(\mathrm{supp}\,w)}\big)
$$

（或以 §7 的方向增长上包取代 $|\Xi|_{L^\infty}$）使

$$
|L\,\mathcal R|_{w,4}^{4}\ \le\ M_4\,\big(|L\,\mathcal R|_{w}^{2}\big)^{2}.
$$

当 $h$ 带限并按 Nyquist 采样时，可经采样离散化为有限矩阵范数问题，继而以 Schur/Hilbert–Schmidt 界结合“**别名=0** + 伯努利层 + 窗尾”三项给出构造性的有限上界（见 §6）。□

---

## 3. Pretentious 相干链路（**GL(1) 适用**）

### 定理 3.1（Pretentious 小距离 $\Rightarrow$ 窗口大值）

**本节仅适用于 GL(1)**。以下结论在**取共振器长度 $Y\asymp X$**（或至少 $Y\ge X$）的约定下成立，统一以 $A_\sigma(\min\{X,Y\})$ 计。取 $\sigma>1$。若存在 $X\ge2$ 与配准 $(\chi^\star,\tau^\star)$ 使 $\mathbb D_{\sigma,X}(f;\tau^\star)\le D_0$，且 $w$ 在 $|t-\tau^\star|\le T$ 平滑，则对谱最优 $\mathcal R^\star$ 有

$$
\sup_{|t-\tau^\star|\le T}|L(\sigma+it)\,\mathcal R^\star(\sigma+it)|
\ \gg_\sigma\ A_\sigma\big(\min\{X,Y\}\big)\,e^{-C_\sigma D_0^2}.
$$

**证明略**（相干近似嵌入 AFE 主和，配合谱优化与定理 1.1）。

---

## 4. 非相干链路的 Ω-下界（Rayleigh 测试向量法）

**定义（AFE 主系数向量）**：取

$$
c_n(\sigma;h):=\overline{a_n}\,V_+\!\Big(\frac{n}{Q^{1/2}};\sigma\Big),\qquad n\ge1.
$$

（直观：以 AFE 主和的"形状"作同相测试向量。）

### 定理 4.1（非相干 $\Rightarrow$ Ω-下界）

以下结论在**取共振器长度 $Y\asymp X$**（或至少 $Y\ge X$）的约定下成立。设 $\inf_{|t|\le T}\mathbb D_{\sigma,X}(f;t)\ge D>0$ 并满足 §0 的窗/AFE/EM 条件。令 $c=(c_n(\sigma;h))$ 为按上式定义的 AFE 主系数向量。则存在常数 $\kappa=\kappa(\sigma,w,h)>0$ 使

$$
\lambda_{\max}\ \ge\ \frac{\langle c,\mathsf K c\rangle}{\langle c,G c\rangle}
\ \ge\ \kappa\,e^{-2C'_\sigma D^2},
$$

从而（若 $|\mathcal R^\star|\le B$）

$$
\boxed{\ \sup_{t\in\mathrm{supp}(w)}|L(\sigma+it)|\ \gg_\sigma\ B^{-1}\,e^{-C'_\sigma D^2}\ }.
$$

---

## 5. 中心轴与完成函数

令

$$
\Xi(s):=r(s)L(s)=Q^{-s/2}\Lambda(s).
$$

### 定理 5.1（中心轴的共振下界）

在 $\Re s=\tfrac a2$ 上取使 AFE 对称的偶窗 $h$。则对 $\mathcal R^\star$ 有

$$
\sup_{t\in\mathrm{supp}(w)}|\Xi(\tfrac a2+it)|\ \gg\ \sqrt{\lambda_{\max}\big(\tfrac a2\big)}.
$$

带限窗时，$\lambda_{\max}$ 的误差**主要**由 §6 的三分解给出显式上界；此外仍受 §2 的四次能量常数与 §7 的方向上包常数控制。此处误差指数值离散与 EM 端点；与 $L$ 解析增长相关的常数由 §2 的 $M_4$ 与 §7 的方向上包控制。

---

## 6. 非渐近误差预算：Nyquist–Poisson–EM 三分解

令 $g_\rho(t)$ 为窗口化 integrand，具体形式为

$$
g_\rho(t):=|L(\sigma+it)|^2\,\rho^{it}\quad\text{或}\quad g_\rho(t):=|L(\sigma+it)\mathcal R(\sigma+it)|^2\,\rho^{it}
$$

（分别用于计算 $K_{mn}$ 或含 $\mathcal R$ 的能量）。取步长 $\Delta$、EM 阶 $M$、截断 $T$。则

$$
\boxed{
\text{阈值误差}\ \le
\underbrace{\sum_{m\neq 0}\big|\widehat g(2\pi m/\Delta)\big|}_{\text{别名}}
+\underbrace{\sum_{k=1}^{M-1} C_k\,\Delta^{2k}\,\max_{j\le 2k-1}|g^{(j)}|_\infty}_{\text{伯努利层}}
+\underbrace{\int_{|t|>T}\!|g(t)|\,dt}_{\text{窗尾}}\ }.
$$

**带宽规则**：当 $h,w$ 均带限时，$g_\rho$ 的带宽由两者带宽的**卷积**上界给出。当 $\Delta$ 满足 Nyquist 条件（步长 $\le$ 带宽倒数）时，**别名项严格为 0**；否则按上式给出显式上界。完成函数的垂线配平与 S10 的支持函数上包共同给出窗尾指数衰减。常数 $C_k$ 与 $|g^{(j)}|_\infty$ 可由 $h,w$ 的带宽与伯努利数**显式**给出。

---

## 7. 极点—增长兼容性

**方向上包的可检定义**：存在凸函数 $H:\mathbb R\to[0,\infty)$（称为**方向上包**），使得对固定 $\sigma$ 与所有 $t$，有

$$
|\Xi(\sigma+it)|\ \le\ C(\sigma)\,\exp\big(H(t)\big).
$$

当 $h,w$ 带限且数值积分满足 Nyquist 条件时，上包 $H$ 与带宽常数给出 $|L\mathcal R|_{w,4}$ 的有限性与 §6 "窗尾"的指数衰减常数。

### 命题 7.1（"极点 = 主尺度""方向增长 = 支持函数上包"保持）

AFE 双窗、mollifier/共振器插入与有限阶 EM 校正仅改变整/全纯层，**不引入新极点且不提高任何已存在极点的阶**；方向增长指标仍受支持函数上包控制。因此大值法与极点定位/增长几何完全一致。

---

## 8. 例示模板

**A. Dirichlet $L(\chi,s)$，$\sigma>1$**
取 $w$ 为平滑区间窗，$X=T^\vartheta$，$Y\asymp X$。按谱问题得 $\mathcal R^\star$；若 $|\mathcal R^\star|\le B$，则

$$
\sup_{|t-\tau|\le T}|L(\sigma+it)|\ \gg_\sigma\ B^{-1}\,A_\sigma\big(\min\{X,Y\}\big)\,e^{-C_\sigma \mathbb D_{\sigma,X}(\chi;\tau)^2}.
$$

可通过 $\ell^2$ 归一配合 Cauchy–Schwarz 控制 $B\ll (\sum_{n\le Y}n^{-2\sigma})^{1/2}$。**若要把 $\mathcal R^\star$ 规模化至 $B=1$**，需在谱问题中加入

$$
|\mathcal R|_{L^\infty(\mathrm{supp}\,w)}\le1
$$

的**非线性（凸）约束**；为保持广义本征问题的线性结构，本文默认采用 $\ell^2$ 归一配合 Cauchy–Schwarz 的保守上界控制 $B$（或仅在事后报告由解得的 $B$ 值）。**提醒**：$\ell^2$ 控制的 $B$ 一般偏保守，数值阈值因此可能下降，但理论不等式仍成立。

**B. 椭圆曲线 $L(E,s)$ 的中心轴**
在 $\Re s=1$ 上取带限窗并考虑 $\Xi_E(s)$。则

$$
\sup_{t\in\mathrm{supp}(w)}|\Xi_E(1+it)|\ \gg\ \sqrt{\lambda_{\max}},
$$

误差由 §6 三项显式上界控制。

---

## 9. 失效族与边界机制

1. **EM 无穷层**：将 EM 误作无穷级会引入伪极点与阈值扭曲；应固定有限阶，余项整函数吸收。
2. **别名污染**：步长与带宽不匹配致 $\widehat g$ 采样重叠；用带限窗并满足 Nyquist 条件消除。
3. **方向退化**：若主项同速同向，核能量集中导致退化；可更换方向或采用多方向联合。
4. **Pretentious 极端平台**：高相干使四次能量常数恶化；提高正则、拓宽窗或避免完全对齐。

---

## 10. 可检清单（最小充分条件）

1. **接口/条带**：给出 $(Q,a,r)$ 并验证完成函数模板；竖条内一律用**有限阶 EM**。
2. **AFE**：选偶窗 $h$（带限或指数衰减），构造 $V_\pm$ 并记录 $R(s;h)$ 的整/指数型整性质。
3. **谱解**：建立 $G,\mathsf K$，解 $\mathsf K r=\lambda G r$；校核 $|\mathcal R^\star|$ 的点态上界（或采用上段 $L^\infty$ 非线性约束的替代方案）。
4. **四次能量**：用引理 2.2 或"二/四次能量比 + Paley–Zygmund"校核 $M_4(w,h;Y)$。
5. **Pretentious 评估**：计算 $\mathbb D_{\sigma,X}$ 并在相干/非相干两端分别调用 §3/§4 的结论（GL(1) 适用）。
6. **误差预算**：按 §6 逐项给出"别名 + 伯努利层 + 窗尾"的数值上界，并在带限/Nyquist 条件下声明"别名=0"。
7. **极点/增长一致**：确认"极点 = 主尺度""方向增长 = 支持函数上包"未被改变。
8. **可逆性/正则化**：确保 $(G_{mn})_{m,n\le Y}$ 可逆；必要时采用 $\eta$-正则并令 $\eta\to0$。
9. **长度匹配**：明确共振器长度 $Y$ 与分析长度 $X$ 的匹配（$Y\asymp X$ 或 $Y\ge X$；若 $Y<X$ 则以 $\min\{X,Y\}$ 计）。

---

## 11. 公开判据与工具（引用）

* **Rayleigh–Ritz 与有限维谱定理**：最大 Rayleigh 商由本征向量取得（广义本征对 $(\mathsf K,G)$ 同理）。
* **Paley–Zygmund 不等式**：对非负随机变量 $X$，$\mathbb P(X\ge \theta\mathbb E[X])\ge (1-\theta)^2\,\mathbb E[X]^2/\mathbb E[X^2]$。
（本文取 $X=|Z|^2\ge0$，且四次能量界保证 $\mathbb E[X^2]<\infty$。）
* **Schur 检验**：以核的行/列可和性界定 Hilbert–Schmidt/算子范数。
* **Nyquist–Shannon 带限采样**：带限窗下别名项全消。
* **有限阶 Euler–Maclaurin**：端点校正仅贡献整层/全纯层，极点来源保持主尺度。

---

## 12. 与既有篇章的接口

- ↔ S2（零集几何）：选择方向/尺度带与窗形时，幅度平衡超平面提供局部化骨架；在中心轴场景与二项闭合模板一致。
- ↔ S3（完成函数）：$\Gamma/\pi$ 正规化与中心轴 $a$ 的对称用于垂线配平；本篇的阈值与 AFE 依赖于完成函数模板的合法域。
- ↔ S4（有限阶 EM）：“极点 = 主尺度”的保持与误差学的端点层全由有限阶 EM 保障；谱核/矩阵中的“整层校正”来自 EM 端点。
- ↔ S5（方向亚纯化）：方向极点位置与阶用于评估窗尾与方向增长，指导步长与带宽的选择。
- ↔ S6（信息刻度）：$\Lambda$ 的方差律与对偶为窗宽选择与“典型规模”度量提供信息—几何依据；$A_\sigma(X)$ 与 S6 的刻度一致化。
- ↔ S7（$L$-函数接口）：degree/conductor/完成函数的参数化为窗与尺度变量提供统一记账；与显式公式一侧的核选择相容。
- ↔ S8（Nyquist–Poisson–EM 三分解）：别名/伯努利层/窗尾三项给出非渐近误差常数；带限窗 + Nyquist 消除别名。
- ↔ S9（Pretentious 距离）：相干/非相干链路分别以 $\mathbb D_{\sigma,X}$ 控制大值窗口与 Ω-下界；GL(1) 之外需改用谱化大筛。
- ↔ S10（Amoeba 几何与增长）：支持函数上包控制方向增长；Ronkin 凸性与主导子和区解释“阈值=谱半径”的几何稳定性。
- ↔ S11（迹公式接口）：选用与显式/迹公式同族的窗核（$\mathcal C,\mathcal B^{\pm}$）可将谱侧放大与几何侧局部化统一到同一变分框架。
- ↔ S12（AFE/放大器）：本篇的大值与 Ω-下界完全构建在软窗 AFE 与广义本征放大之上；误差预算与 S12 的三分解一致。

---

## 结语

本文以**谱半径—RMS–sup—Paley–Zygmund**为外壳、以**软窗 AFE**为内核，并辅以**Pretentious 距离**与**Nyquist–Poisson–EM**误差学，建立了在固定窗下**非渐近、可检**的**大值存在性与 Ω-下界**：$\lambda_{\max}$ 即为窗内点态大值的能量阈值；相干—非相干两端分别提供稳定窗口与指数折扣的普适下界；全程保持"**极点 = 主尺度**"与方向增长几何的一致性。长度参数 $Y$ 与 $X$ 的匹配、核的自伴性来源及整层扰动的可控性均在统一框架内明确，便于直接落地到 GL(1) 族与中心轴场景，并为更高阶族的谱化推广提供清晰接口。
