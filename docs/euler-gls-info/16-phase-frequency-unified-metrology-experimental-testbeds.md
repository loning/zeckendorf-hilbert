# 计算宇宙中的相位–频率统一计量与实验测试台

从 FRB 真空窗化上限到 δ–环散射可辨识性的统一时间刻度实现

---

## 摘要

在此前"计算宇宙"框架中，宇宙被公理化为离散对象 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$，并在其上构造了离散复杂性几何、离散信息几何、统一时间刻度诱导的控制流形 $(\mathcal M,G)$、任务信息流形 $(\mathcal S_Q,g_Q)$ 以及时间–信息–复杂性联合变分原理。统一时间刻度由散射母尺
$$
\kappa(\omega) = \varphi'(\omega)/\pi = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\operatorname{tr}Q(\omega)
$$
将相位导数、谱移密度与 Wigner–Smith 群延迟迹统一为单一刻度。然而，这一框架仍然主要停留在"理论几何"层面，尚未系统给出如何在现实实验中对统一时间刻度与计算宇宙结构进行计量与校准。

本文在计算宇宙–统一时间刻度–谱窗化读数的基础上，构造一个以"相位–频率"为唯一观测量的跨平台计量范式，并将其具体落实在两类代表性测试台上：宇宙学距离的快速射电暴传播 (FRB) 与实验室尺度的 δ–环–Aharonov–Bohm (AB) 通量散射。核心思想是：从计算宇宙视角出发，所有可观测量均通过统一时间刻度下的相位–频率读数实现；FRB 与 δ–环散射分别提供宇宙尺度与实验室尺度的"同源读数"，它们在统一时间刻度与复杂性几何上可被视为同一计量范式在不同尺度下的实现。

本文主要结果如下：

1. 在计算宇宙–物理宇宙范畴等价的框架下，引入"相位–频率读数函子" $\mathsf{PhFr}$，其将任一物理可实现的计算宇宙对象送到一个仅含相位–频率数据的计量对象。证明 $\mathsf{PhFr}$ 与统一时间刻度母尺兼容：在可追踪扰动与波算子完备条件下，$\mathsf{PhFr}$ 的输出完全由 $\kappa(\omega)$ 与有限个谱–散射不变量决定。

2. 针对 FRB，构造一个"真空极化窗化上限"模型：以 PSWF/DPSS 类型窗函数对 FRB 频域相位进行窗化，证明在固定复杂性预算与宇宙学距离约束下，任何统一时间刻度改变量 $\delta \kappa(\omega)$ 对 FRB 相位残差的贡献可被界定为一个严格上界；若观测残差低于该上界，则得到对真空极化或其它新物理的统一时间刻度型上限。

3. 针对 δ–环–AB 通量散射，重述谱量化方程
   $$
   f(k,\alpha_\delta,\theta) = \cos(kL) + (\alpha_\delta/k)\sin(kL) - \cos\theta = 0
   $$
   与"振幅修正的相位闭合式"
   $$
   \cos\gamma(k) = |t(k)|\cos\theta
   $$
   之间的等价，并在计算宇宙–控制流形视角下证明：在固定 $(L,\theta)$ 的谱观测 $\{k_n(\theta)\}$ 下，δ–耦合强度 $\alpha_\delta$ 与 AB 通量 $\theta$ 在非病态域内是可辨识的 (Jacobian 满秩)，从而可用作统一时间刻度–相位计量的"实验室标尺"。

4. 在统一时间刻度–谱窗化读数框架下，将 FRB 与 δ–环散射嵌入同一"相位–频率计量宇宙"中，证明存在一个"跨平台刻度同一条件"：当 FRB 相位残差与 δ–环散射谱偏移被同一 $\kappa(\omega)$ 模型所解释时，两者的窗化读数在适当 PSWF/DPSS 空间上属于同一等价类，因而可通过联合拟合对统一时间刻度进行尺度标定与一致性检验。

5. 将上述相位–频率计量结构嵌入时间–信息–复杂性变分原理，将"选择 FRB/δ–环窗函数与控制参数"形式化为联合流形上的变分问题，给出"在有限复杂性预算下同时利用宇宙尺度与实验室尺度相位–频率读数以最大化统一时间刻度辨识度"的变分条件。

本文从而在计算宇宙框架内完成了"相位–频率统一计量"的实验落地点设计：FRB 与 δ–环散射成为统一时间刻度与复杂性几何的两端测试台，PSWF/DPSS 窗函数成为误差控制的自然工具，二者共同构成了一个跨尺度、跨平台、但在计算宇宙视角下完全统一的相位–频率计量体系。

---

## 1 引言

在此前的系列工作中，我们已经完成了以下几个层次的构造：

1. 在离散层面，将宇宙抽象为一个公理化的计算宇宙对象 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$，并在其上构造了复杂性图 $G_{\mathrm{comp}} = (X,E,\mathsf C)$、复杂性距离 $d_{\mathrm{comp}}$、复杂性维数与离散 Ricci 曲率。

2. 在统一时间刻度–散射理论层面，引入
   $$
   \kappa(\omega) = \varphi'(\omega)/\pi = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\operatorname{tr}Q(\omega),
   $$
   作为"三位一体母尺"，统一了散射相位导数、谱移密度与群延迟迹。

3. 通过统一时间刻度与复杂性几何构造了控制流形 $(\mathcal M,G)$，证明离散复杂性距离在细化极限下收敛到测地距离 $d_G$。

4. 通过观察算子族与相对熵二阶结构构造任务信息流形 $(\mathcal S_Q,g_Q)$，并在联合流形 $\mathcal E_Q = \mathcal M\times\mathcal S_Q$ 上给出了时间–信息–复杂性的联合变分原理。

5. 在谱窗化误差控制一篇中，我们引入 PSWF/DPSS 窗函数，说明在统一时间刻度–频域中，它们是有限时间–带宽–复杂性预算下最优的读数窗。

这些结果为构建一个"统一时间刻度–计算宇宙"的理论体系奠定了基础，但并未直接回答一个关键问题：如何通过具体的物理实验对这一统一时间刻度母尺进行**计量与校准**？仅有统一时间刻度的数学存在性不足以说明其物理可测性；我们需要将散射母尺与实际可观测的相位–频率数据联系起来，并设计一个跨平台的计量策略，使得来自宇宙尺度与实验室尺度的相位–频率读数可以被共同用来检验与标定统一时间刻度。

在这一背景下，快速射电暴 (FRB) 与 δ–环–AB 通量散射成为两个非常自然的测试台：

* FRB 是穿越宇宙学距离的短时宽带射电信号，其传播相位、群延迟与色散结构包含了宇宙学介质与真空特性的积分信息；在统一时间刻度–散射视角下，FRB 本质上是一类"宇宙级散射实验"。

* δ–环–AB 通量散射则是在实验室尺度上对一维环几何、点势与 AB 通量的谱–散射结构的精细测量；其谱量化方程与相位闭合式提供了高度可控的相位–频率测试台，可以在已知几何参数与耦合常数下对统一时间刻度模型进行"反向标定"。

本文的目标是：将 FRB 与 δ–环散射统一嵌入计算宇宙–统一时间刻度框架，并建立一个以相位–频率为唯一读数的计量范式，使得两类实验可以在同一统一时间刻度母尺上进行互相标定与一致性检验。

---

## 2 计算宇宙中的相位–频率读数函子

本节在计算宇宙–物理宇宙范畴等价的背景下，引入一个"相位–频率读数函子" $\mathsf{PhFr}$，其输出仅包含相位–频率数据，与统一时间刻度母尺直接相连。

### 2.1 物理宇宙与计算宇宙的等价回顾

在此前范畴等价工作中，我们构造了物理宇宙范畴 $\mathbf{PhysUniv}^{\mathrm{QCA}}$ 与计算宇宙范畴 $\mathbf{CompUniv}^{\mathrm{phys}}$，并给出互逆函子

$$
F:\mathbf{PhysUniv}^{\mathrm{QCA}}\to\mathbf{CompUniv}^{\mathrm{phys}},
$$

$$
G:\mathbf{CompUniv}^{\mathrm{phys}}\to\mathbf{PhysUniv}^{\mathrm{QCA}}.
$$

物理宇宙对象可以抽象为

$$
U_{\mathrm{phys}} = (M,g,\mathcal F,\kappa,\mathsf S),
$$

计算宇宙对象为

$$
U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I).
$$

函子 $F,G$ 保持统一时间刻度密度 $\kappa(\omega)$ 与散射数据 $\mathsf S(\omega)$ 的结构：从物理侧到计算侧，统一时间刻度被离散化为单步代价；从计算侧到物理侧，复杂性几何被连续化为控制–散射流形。

### 2.2 相位–频率数据对象

定义一个"相位–频率数据对象"为

$$
U_{\mathrm{PhFr}} = (\Omega,\Theta(\omega),\kappa(\omega)),
$$

其中 $\Omega \subset\mathbb R$ 为有效频带，$\Theta(\omega)$ 为总散射相位 (或其归一化)，$\kappa(\omega)$ 为统一时间刻度密度。按照统一时间刻度母尺，在可追踪扰动条件下有

$$
\kappa(\omega) = \Theta'(\omega)/\pi
$$

在加常数意义下成立。

### 2.3 相位–频率读数函子

**定义 2.1（相位–频率读数函子）**

定义函子

$$
\mathsf{PhFr}:\mathbf{PhysUniv}^{\mathrm{QCA}}\to\mathbf{PhFrUniv},
$$

其中 $\mathbf{PhFrUniv}$ 对象为 $U_{\mathrm{PhFr}}$，态射为保持 $\omega$ 及 $\Theta(\omega),\kappa(\omega)$ 结构的频域变换。

对物理宇宙对象 $U_{\mathrm{phys}}$，$\mathsf{PhFr}(U_{\mathrm{phys}}) = (\Omega,\Theta(\omega),\kappa(\omega))$ 由其散射数据与统一时间刻度母尺确定。

通过范畴等价，给定计算宇宙对象 $U_{\mathrm{comp}}$，可先用 $G(U_{\mathrm{comp}}) = U_{\mathrm{phys}}$ 得到物理宇宙，再应用 $\mathsf{PhFr}$ 得到相位–频率数据对象。于是得到组合函子

$$
\mathsf{PhFr}\circ G:\mathbf{CompUniv}^{\mathrm{phys}}\to\mathbf{PhFrUniv}.
$$

**命题 2.2（统一时间刻度与相位–频率读数的一致性）**

在可追踪扰动与波算子完备条件下，相位–频率读数对象 $U_{\mathrm{PhFr}} = (\Omega,\Theta(\omega),\kappa(\omega))$ 完全由统一时间刻度密度 $\kappa(\omega)$ 与一个常数相位偏移决定，即

$$
\Theta(\omega) = \pi\int^\omega \kappa(\omega')\,\mathrm d\omega' + \Theta_0.
$$

特别地，任何两对 $(\Theta,\kappa)$、$(\Theta',\kappa')$ 若 $\kappa\equiv\kappa'$ 且 $\Theta-\Theta'$ 为常数，则对应同一统一时间刻度结构。

证明略。

---

## 3 FRB 真空极化窗化上限：计算宇宙视角

本节将 FRB 传播视为宇宙尺度的散射–传播过程，在统一时间刻度–谱窗化下构造"真空极化窗化上限"。

### 3.1 FRB 传播的散射–传播模型

简化起见，考虑 FRB 信号在频域上的复振幅 $A(\omega)$，其相位部分可写为

$$
A(\omega) = |A(\omega)|\exp(i\Phi_{\mathrm{FRB}}(\omega)).
$$

若传播过程中仅有已知色散与重离子介质贡献，则

$$
\Phi_{\mathrm{FRB}}(\omega) = \Phi_{\mathrm{known}}(\omega) + \Phi_{\mathrm{new}}(\omega),
$$

其中 $\Phi_{\mathrm{known}}$ 来自常规色散测度与介质模型，$\Phi_{\mathrm{new}}$ 表示可能来自真空极化、新粒子或统一时间刻度微扰的贡献。

在统一时间刻度–散射视角下，$\Phi_{\mathrm{FRB}}(\omega)$ 可以理解为某个有效散射相位 $\Theta_{\mathrm{FRB}}(\omega)$，其导数给出一个有效时间刻度密度 perturbation

$$
\delta\kappa_{\mathrm{FRB}}(\omega) = \frac{1}{\pi}\partial_\omega \Phi_{\mathrm{new}}(\omega).
$$

### 3.2 窗化 FRB 相位与误差上界

观测上，我们只能在有限频带 $\Omega_{\mathrm{FRB}} = [\omega_{\min},\omega_{\max}]$ 上、以有限分辨率测量相位–频率数据。引入窗函数 $W_{\mathrm{FRB}}(\omega)$（例如由 PSWF/DPSS 频谱产生）并定义窗化残差

$$
R_{\mathrm{FRB}} = \int_{\Omega_{\mathrm{FRB}}} W_{\mathrm{FRB}}(\omega)\big(\Phi_{\mathrm{FRB}}(\omega) - \Phi_{\mathrm{known}}(\omega)\big)\,\mathrm d\omega.
$$

若 FRB 信号的统一时间刻度微扰 $\delta\kappa_{\mathrm{FRB}}(\omega)$ 在某个谱范数下有约束 $|\delta\kappa_{\mathrm{FRB}}| \le \Lambda$，则透过积分与 Cauchy–Schwarz 不等式得到

$$
|R_{\mathrm{FRB}}| \le \Lambda |W_{\mathrm{FRB}}|_{L^2(\Omega_{\mathrm{FRB}})} C_{\mathrm{FRB}},
$$

其中 $C_{\mathrm{FRB}}$ 由宇宙学传播核与几何因子决定。

反过来,若观测上残差 $|R_{\mathrm{FRB}}| \le \varepsilon_{\mathrm{obs}}$，则得到统一时间刻度扰动的上界

$$
\Lambda \ge \Lambda_{\min} \ge \frac{|R_{\mathrm{FRB}}|}{|W_{\mathrm{FRB}}| C_{\mathrm{FRB}}}.
$$

将最优窗函数选择问题写成最小化 $|W_{\mathrm{FRB}}|$ 的约束问题，经典结果表明 PSWF/DPSS 类型窗在给定时间–频率–复杂性预算下使误差上界最小，从而给出了"FRB 真空极化窗化上限器"。

---

## 4 δ–环–AB 通量散射的谱–相位–散射等价与可辨识性

本节从计算宇宙–控制流形视角，重述 δ–环–AB 通量散射的谱–相位–散射结构，并给出可辨识性定理。

### 4.1 δ–环–AB 通量模型

考虑一维环，周长 $L$，坐标 $x\in[0,L)$ 并周期 $x\sim x+L$。在环上引入一点 δ–势，强度 $\alpha_\delta$，以及 AB 通量 $\theta \in [0,2\pi)$。对应哈密顿量 (单位质量并忽略常数) 可写为

$$
H = -\partial_x^2 + \alpha_\delta\delta(x),
$$

边界条件含 AB 相位：

$$
\psi(L^-) = \mathrm e^{i\theta}\psi(0^+), \quad \psi'(L^-) = \mathrm e^{i\theta}\psi'(0^+).
$$

求解本征方程 $H\psi = k^2\psi$ 得到谱量化条件

$$
f(k,\alpha_\delta,\theta) = \cos(kL) + (\alpha_\delta/k)\sin(kL) - \cos\theta = 0.
$$

对应散射振幅 $t(k)$ 与相位 $\gamma(k)$ 满足某种相位闭合式，典型形式

$$
\cos\gamma(k) = |t(k)|\cos\theta,
$$

其中 $\gamma(k)$ 与 $kL$ 及 $\alpha_\delta$ 的函数关系由散射理论给出。

### 4.2 计算宇宙中的 δ–环控制流形

将 δ–环散射视为一个低维控制流形上的计算宇宙：控制参数空间

$$
\mathcal M_{\delta{\text -}\mathrm{ring}} = \{(L,\alpha_\delta,\theta)\},
$$

配以某个度量 $G$，例如

$$
G = g_{LL}\mathrm dL^2 + g_{\alpha\alpha}\mathrm d\alpha_\delta^2 + g_{\theta\theta}\mathrm d\theta^2.
$$

谱观测 $\{k_n(\theta)\}$ 对应信息流形上的数据点，而统一时间刻度密度由散射相位导数与群延迟给出。δ–环因此成为一个三维控制流形上高度可控的"计算子宇宙"，用于统一时间刻度与相位–频率计量。

### 4.3 谱–相位–散射等价定理

**定理 4.1（谱量化与相位闭合等价）**

在 δ–环–AB 通量模型中，谱量化条件

$$
f(k,\alpha_\delta,\theta) = 0
$$

与相位–振幅闭合式

$$
\cos\gamma(k) = |t(k)|\cos\theta
$$

在通常的散射正则性条件下等价；特别地，当 $|t(k)|\to 1$ (弱散射或透射共振) 时，退化为纯相位闭合 $\cos\gamma(k) = \cos\theta$。

*证明思路*：从边界条件与 δ–势跨越条件推导传输矩阵，要求波函数在环上一圈后匹配自身，得到谱量化方程；另一方面，计算散射矩阵元素 $t(k),r(k)$ 与相移 $\gamma(k)$，将谱条件重写为相位–振幅闭合式。两者之间的代数等价可通过直接代入与简化验证。详见附录 B.1。

### 4.4 参数可辨识性定理

**定理 4.2（δ–环的局部可辨识性）**

在给定 $L$ 与若干 AB 通量值 $\theta_j$ 下，若观测到充分多本征波数 $\{k_n(\theta_j)\}$，并且这些点处雅可比矩阵

$$
J = \left( \partial f/\partial k, \partial f/\partial \alpha_\delta, \partial f/\partial \theta \right)
$$

在 $(k,\alpha_\delta,\theta)$ 处满秩，则 $(\alpha_\delta,\theta)$ 在该点附近是谱数据的局部可辨识参数，即存在局部反函数将 $(\alpha_\delta,\theta)$ 写成 $\{k_n(\theta_j)\}$ 的函数。

*证明思路*：应用隐函数定理：若 $\partial f/\partial k \ne 0$ 且关于 $(\alpha_\delta,\theta)$ 的偏导子矩阵满秩，则可解出 $k = k(\alpha_\delta,\theta)$，再对多个 $\theta_j$ 建合成映射，得到局部可逆性。对于多个本征值，可以分量堆叠，若综合雅可比满秩，则整体可辨识。详见附录 B.2。

### 4.5 病态域与条件数

通过显式计算

$$
\frac{\partial k}{\partial \alpha_\delta} = -\frac{f_{\alpha_\delta}}{f_k},
$$

其中 $f_{\alpha_\delta} = (\sin(kL))/k$、$f_k = -L\sin(kL) + \alpha_\delta(\dots)$，可定义病态条件数区域 $f_k\approx 0$，对应谱量化曲线对参数高度敏感或不可逆。在计算宇宙–复杂性几何视角下，这些病态区域对应控制流形上曲率较大、谱–相位信息对参数的"测地灵敏度"急剧放大的区域，需要窗函数与实验设计在复杂性预算内回避或专门处理。

---

## 5 FRB 与 δ–环的统一相位–频率计量

本节将 FRB 与 δ–环散射嵌入同一相位–频率计量框架，给出"跨平台刻度同一"的几何条件。

### 5.1 相位–频率读数对象的并置

对于 FRB 与 δ–环，我们分别得到相位–频率数据对象

$$
U_{\mathrm{PhFr}}^{\mathrm{FRB}} = (\Omega_{\mathrm{FRB}},\Theta_{\mathrm{FRB}}(\omega),\kappa_{\mathrm{FRB}}(\omega)),
$$

$$
U_{\mathrm{PhFr}}^{\delta} = (\Omega_{\delta},\Theta_{\delta}(\omega),\kappa_{\delta}(\omega)).
$$

在统一时间刻度假设下，存在一个"母刻度密度" $\kappa_{\mathrm{univ}}(\omega)$，使得 FRB 与 δ–环对应的有效时间刻度分别为

$$
\kappa_{\mathrm{FRB}}(\omega) = g_{\mathrm{FRB}}(\omega)\kappa_{\mathrm{univ}}(\omega),
$$

$$
\kappa_{\delta}(\omega) = g_{\delta}(\omega)\kappa_{\mathrm{univ}}(\omega),
$$

其中 $g_{\mathrm{FRB}},g_{\delta}$ 为由几何与传播核决定的权重函数。

### 5.2 跨平台刻度同一条件

**定义 5.1（跨平台刻度同一）**

称 FRB 与 δ–环散射在统一时间刻度上刻度同一，如果存在母刻度密度 $\kappa_{\mathrm{univ}}$ 与权重 $g_{\mathrm{FRB}},g_{\delta}$，使得窗化相位残差满足一致的解释：

$$
R_{\mathrm{FRB}}(W_{\mathrm{FRB}}) \approx \int W_{\mathrm{FRB}}(\omega)\delta g_{\mathrm{FRB}}(\omega)\kappa_{\mathrm{univ}}(\omega)\,\mathrm d\omega,
$$

$$
R_{\delta}(W_{\delta}) \approx \int W_{\delta}(\omega)\delta g_{\delta}(\omega)\kappa_{\mathrm{univ}}(\omega)\,\mathrm d\omega,
$$

对一族窗函数 $W_{\mathrm{FRB}},W_{\delta}$ 均成立。

**定理 5.2（统一时间刻度的跨平台一致性检验）**

若存在母刻度密度 $\kappa_{\mathrm{univ}}$ 与权重 $g_{\mathrm{FRB}},g_{\delta}$ 使得对一组 PSWF/DPSS 型窗函数族 $\{W_j\}$，FRB 与 δ–环的窗化残差满足

$$
R_{\mathrm{FRB}}(W_j) = \lambda_j R_{\delta}(W_j) + \mathcal O(\varepsilon_j),
$$

其中 $\lambda_j$ 为可由几何因子预先计算的比例，当 $\varepsilon_j$ 在实验误差内可接受时，则 FRB 与 δ–环散射的相位–频率数据与统一时间刻度模型一致。

反之，若对某些窗函数 $W_j$ 存在系统性偏差超出误差容忍度，则可判定统一时间刻度模型在该频带与尺度上存在不一致，需修正 $\kappa_{\mathrm{univ}}$ 或权重模型。

证明思路：利用 PSWF/DPSS 的完备性，将 $\kappa_{\mathrm{univ}}$ 在窗函数空间中展开，把 FRB 与 δ–环残差写成对同一基的系数向量，检验它们是否在预先给定的线性关系中。详见附录 B.3。

---

## 6 窗函数与控制参数的联合变分：最优跨平台计量策略

本节把 FRB 与 δ–环窗函数与控制参数选择纳入时间–信息–复杂性联合变分原理，给出"有限复杂性预算下最优跨平台计量"的变分形式。

### 6.1 扩展联合流形

此前联合流形为 $\mathcal E_Q = \mathcal M\times\mathcal S_Q$。现在引入两类额外自由度：

1. FRB 窗函数参数空间 $\mathcal W_{\mathrm{FRB}}$，例如由若干 PSWF 模式的线性系数张成；

2. δ–环控制参数空间 $\mathcal M_\delta = \{(L,\alpha_\delta,\theta)\}$ 与对应窗函数空间 $\mathcal W_{\delta}$。

扩展联合配置为

$$
\widehat z(t) = (\theta(t),\phi(t);\theta_\delta(t),\phi_\delta(t);\{W_{\mathrm{FRB},j}\},\{W_{\delta,j}\}).
$$

在实际计量问题中，FRB 窗函数多为时间独立参数，δ–环控制可以随实验步骤变化，$t$ 只是一个形式化的"执行参数"。

### 6.2 联合作用量与极小性条件

定义扩展作用量

$$
\mathcal A_{\mathrm{cal}}[\widehat z] = \mathcal A_{\mathrm{dyn}}[\theta,\phi,\theta_\delta,\phi_\delta] + \mu_{\mathrm{FRB}}\mathcal E_{\mathrm{win}}^{\mathrm{FRB}}(\{W_{\mathrm{FRB},j}\}) + \mu_{\delta}\mathcal E_{\mathrm{win}}^{\delta}(\{W_{\delta,j}\}) - \lambda_{\mathrm{univ}}\mathcal I_{\mathrm{cons}}[\kappa_{\mathrm{univ}}],
$$

其中：

* $\mathcal A_{\mathrm{dyn}}$ 为控制–信息–复杂性部分的动能–势能；
* $\mathcal E_{\mathrm{win}}^{\mathrm{FRB}},\mathcal E_{\mathrm{win}}^{\delta}$ 为两侧的窗函数误差泛函；
* $\mathcal I_{\mathrm{cons}}[\kappa_{\mathrm{univ}}]$ 度量 FRB 与 δ–环对统一时间刻度的一致性，例如残差平方和；
* $\mu_{\mathrm{FRB}},\mu_{\delta},\lambda_{\mathrm{univ}}$ 为权重。

对 $\theta,\theta_\delta$ 变分得到控制参数的 geodesic–势方程，对 $W_{\mathrm{FRB},j},W_{\delta,j}$ 变分得到窗函数方向上的极小性条件（由前文可知解为 PSWF/DPSS 子空间），对 $\kappa_{\mathrm{univ}}$ 变分得到统一时间刻度的最优估计条件。

在联合变分的极小解处，获得如下意义的"最优计量策略"：

1. FRB 与 δ–环各自使用最优窗函数 (PSWF/DPSS) 实现误差控制；

2. δ–环控制参数被选择在既增强时间刻度敏感度、又避免可辨识性病态域的区域；

3. FRB 观测频带与 δ–环实验频带在统一时间刻度模型下尽可能互补，从而对 $\kappa_{\mathrm{univ}}$ 的全域提供最大信息量。

---

## 附录 A：PSWF/DPSS 的时间–频率集中性与最优性

本附录简要回顾 PSWF/DPSS 的经典结果，并给出在本文框架下使用所需的变分表述。

### A.1 PSWF 的变分表述

考虑带限函数空间

$$
\mathcal B_W = \{ f\in L^2(\mathbb R) : \widehat f(\omega)=0\ \text{对}\ |\omega|>W \}.
$$

在 $\mathcal B_W$ 中，定义时间区间 $[-T,T]$ 上的能量集中度

$$
\alpha(f) = \frac{\int_{-T}^{T}|f(t)|^2\,\mathrm dt}{\int_{-\infty}^{\infty}|f(t)|^2\,\mathrm dt}.
$$

变分问题：在 $\mathcal B_W$ 中寻找最大化 $\alpha(f)$ 的 $f\ne 0$。标准方法将其写作 Rayleigh 商，对应积分算子

$$
(\mathcal K f)(t) = \int_{-T}^{T}\frac{\sin W(t-s)}{\pi(t-s)}f(s)\,\mathrm ds.
$$

特征方程 $\mathcal K f = \lambda f$ 的特征值 $\lambda$ 即为能量集中度 $\alpha(f)$。按特征值从大到小排序得到 $\lambda_0\ge\lambda_1\ge\cdots$，对应特征函数 $\psi_0,\psi_1,\dots$ 即 PSWF。

最优性结论：对任意维度为 $N$ 的子空间 $V\subset\mathcal B_W$，有

$$
\sum_{f\in\mathrm{ONB}(V)}\alpha(f) \le \sum_{n=0}^{N-1}\lambda_n.
$$

特别地，当 $V$ 由 $\{\psi_0,\dots,\psi_{N-1}\}$ 张成时取等号。

### A.2 DPSS 的离散类比

长度为 $N$ 的序列空间 $\mathbb C^N$ 中，定义 Toeplitz 矩阵

$$
K_{mn} = \frac{\sin 2\pi W(m-n)}{\pi(m-n)},\ 0\le m,n\le N-1,
$$

对角元素取极限 $K_{mm} = 2W$。特征值–特征向量问题

$$
\sum_{n=0}^{N-1}K_{mn}v_n^{(k)} = \lambda_k v_m^{(k)}
$$

定义 DPSS $v^{(k)}$ 及其能量集中度 $\lambda_k$。DPSS 在离散频带 $[-W,W]$ 与有限长度 $N$ 条件下具有与 PSWF 对应的最优性：在所有维度为 $K$ 的子空间中，DPSS 子空间在频带内能量集中度总和最大。

---

## 附录 B：δ–环谱–散射等价与可辨识性证明细节

### B.1 定理 4.1 的证明要点

从 δ–环边界条件出发，写出在 $x\in(0,L)$ 区间的平面波解 $\psi(x) = A\mathrm e^{ikx} + B\mathrm e^{-ikx}$，δ–势引入在 $x=0$ 与 $x=L^-$ 的间断条件；AB 通量通过在 $x=0$ 与 $x=L^-$ 之间施加相因子 $\mathrm e^{i\theta}$ 表示。集合条件可以整理为一个 $2\times 2$ 传输矩阵的本征值方程，其一致性条件给出谱量化式

$$
\cos(kL) + (\alpha_\delta/k)\sin(kL) = \cos\theta.
$$

另一方面，通过构造相应散射矩阵 $S(k)$ 与透射振幅 $t(k)$，计算它们的相位 $\gamma(k)$ 与模 $|t(k)|$，可将一致性条件重写为

$$
\cos\gamma(k) = |t(k)|\cos\theta.
$$

二者之间的代数等价性通过初等三角恒等式与传输矩阵–散射矩阵转换关系得到，细节略。

### B.2 定理 4.2 的隐函数定理应用

谱量化方程 $f(k,\alpha_\delta,\theta)=0$ 对三变量的偏导矩阵在一般点处为

$$
\partial f/\partial k,\ \partial f/\partial \alpha_\delta,\ \partial f/\partial\theta.
$$

若 $\partial f/\partial k\ne 0$，则可局部写成 $k = k(\alpha_\delta,\theta)$。对多组 $\theta_j$ 与对应本征值 $k_n(\theta_j)$，把这些函数堆叠起来，得到从参数空间 $(\alpha_\delta,\theta)$ 到观测空间 $\{k_n(\theta_j)\}$ 的映射。若该映射在某点处雅可比满秩，则存在局部逆映射，参数可辨识性成立。

病态区域对应 $\partial f/\partial k=0$，即谱曲线具有水平切线，此时小改参数可导致 $k$ 的剧烈变化，反之从有限精度谱数据回推参数不稳定。

### B.3 定理 5.2 的线性代数形式

选取一族窗函数 $\{W_j\}$（如 PSWF 基底），在该基底中展开统一刻度扰动

$$
\delta\kappa_{\mathrm{univ}}(\omega) = \sum_j c_j W_j(\omega).
$$

FRB 与 δ–环的窗化残差分别写作

$$
R_{\mathrm{FRB}}(W_j) \approx a_j c_j, \quad R_{\delta}(W_j) \approx b_j c_j,
$$

其中 $a_j,b_j$ 由传播核与几何因子决定。若理论预言 $R_{\mathrm{FRB}} = \lambda_j R_{\delta}$，则等式变为 $a_j c_j = \lambda_j b_j c_j$。一方面，对所有 $j$ 同时成立要求 $a_j = \lambda_j b_j$ 与 $c_j$ 不为零；另一方面，实际拟合中可通过最小二乘或极大似然估计检验这一线性关系是否在实验误差内成立，构成统一时间刻度的一致性检验。

---

## 附录 C：窗函数变分最优性的形式化

在扩展作用量中，窗函数部分的误差泛函为

$$
\mathcal E_{\mathrm{win}}(\{W_j\}) = \sup_{f\in\mathcal B_W} \frac{|f - \sum_{j=1}^K\langle f,W_j\rangle W_j|}{|f|}.
$$

该泛函在窗函数子空间 $V = \mathrm{span}\{W_1,\dots,W_K\}$ 上仅依赖于 $V$ 本身。标准 Hilbert 空间理论表明，该误差等于 $\sqrt{1-\lambda_{\min}(V)}$，其中 $\lambda_{\min}(V)$ 为 $\mathcal K$ 在 $V$ 上的最小特征值。通过最小最大原理可知，当 $V$ 由前 $K$ 个 PSWF 特征函数张成时，该最小特征值最大，从而误差最小，PSWF 子空间为全局极小解。DPSS 离散情形完全类似，用矩阵谱替代积分算子即可。

这一点保证了在时间–信息–复杂性联合变分原理中，将窗函数自由度也纳入变分时，极小解必然选择 PSWF/DPSS 型窗函数，从而将误差控制与统一时间刻度读数的最优性统一在同一个变分框架内。
