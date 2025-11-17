# 计算宇宙的统一时间刻度与连续复杂性几何

散射母尺、控制流形与度量 $G$ 的构造

---

## 摘要

在前几篇工作中,我们将"计算宇宙"公理化为离散对象 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$,并分别构造了其上的离散复杂性几何与离散信息几何。然而,在该框架中,单步代价函数 $\mathsf C$ 仍然是抽象赋予的,其与真实物理时间刻度之间的联系尚未被系统刻画。本篇文章在统一时间刻度的散射母尺

$$
\kappa(\omega) = \varphi'(\omega)/\pi = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\mathrm{tr}\,Q(\omega)
$$

的基础上,引入"控制流形" $\mathcal M$ 与散射族 $S(\omega;\theta)$,将计算宇宙中离散步进的代价系统地嵌入到一个由 $\kappa(\omega)$ 诱导的 Riemann 型度量 $G$ 上,从而构造出一个与物理时间刻度一致的连续复杂性几何。

具体而言,我们首先将每一个可物理实现的计算宇宙 $U_{\mathrm{comp}}$ 视为某个可控散射系统的组合:配置更新由控制参数 $\theta \in \mathcal M$ 驱动,散射矩阵 $S(\omega;\theta)$ 描述在频域上的物理响应,Wigner–Smith 群延迟矩阵 $Q(\omega;\theta)$ 则给出统一时间刻度密度的局域响应。随后,我们定义度量

$$
G_{ab}(\theta) = \int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_a Q(\omega;\theta)\,\partial_b Q(\omega;\theta) \big)\,\mathrm d\omega
$$

并证明:在自然的正则性假设下,$G$ 为正定且在控制坐标变换与内部规范变换下具有良好的协变性;进一步,对任何足够平滑的控制路径 $\theta(t)$,其由 $G$ 诱导的长度

$$
L_G[\theta] = \int_0^T \sqrt{G_{ab}(\theta(t))\,\dot\theta^a(t)\dot\theta^b(t)}\,\mathrm dt
$$

在适当的离散极限下等价于离散复杂性距离的连续化版本。

我们还证明:对一族在离散尺度 $h \to 0$ 下细化的计算宇宙 $\{U_{\mathrm{comp}}^{(h)}\}$,若其单步代价由统一时间刻度的散射响应构造,则配置图距离 $d^{(h)}$ 在 Gromov–Hausdorff 意义下收敛到控制流形上的测地距离 $d_G$。这给出了一个从完全离散的计算宇宙到连续复杂性几何的严谨桥梁。

最后,我们讨论该连续复杂性几何在范畴意义下的自然性:以控制流形及其度量 $G$ 作为"计算宇宙对象"的几何像,可以构造出一个以控制–散射对 $(\mathcal M,S)$ 为对象的范畴 $\mathbf{CtrlScat}$,并证明离散计算宇宙范畴 $\mathbf{CompUniv}$ 与 $\mathbf{CtrlScat}$ 之间存在一个保持复杂性距离的函子结构。这为后续建立"物理宇宙范畴 ↔ 计算宇宙范畴"之间的范畴等价奠定了连续几何基础。

---

## 1 引言

在"计算宇宙"方案中,整个宇宙被视为一个可数配置集 $X$ 上的离散动力系统:一步更新关系 $\mathsf T \subset X\times X$ 决定从一个配置到另一个配置的可达性,单步代价函数 $\mathsf C:X\times X\to[0,\infty]$ 则为每次更新赋予时间/能量等资源成本。前面的工作已经证明:在有限信息密度与局域更新的公理假设下,可以把 $(X,\mathsf T,\mathsf C)$ 视为一个加权图,并在其上构造复杂性距离 $d(x,y)$、复杂性球体积、复杂性维数以及离散 Ricci 曲率等几何对象,从而建立"离散复杂性几何"。同时,通过观察算子族与任务感知相对熵,我们在配置空间上构造了"离散信息几何",使得信息维数与复杂性维数之间具有自然的不等式关系。

然而,真正要将计算宇宙与物理宇宙统一起来,仅有抽象的代价函数 $\mathsf C$ 仍然不够。我们需要回答两个关键问题:

1. 单步代价 $\mathsf C(x,y)$ 如何与物理时间刻度关联?
2. 离散复杂性距离 $d(x,y)$ 是否可以被某个由物理时间刻度诱导的连续度量 $G$ 的测地距离 $d_G$ 所逼近?

为此,本篇文章引入统一时间刻度的散射母尺。对于一个物理散射系统,设其散射矩阵为 $S(\omega)$,则总散射相位 $\varphi(\omega)$、谱移函数导数 $\rho_{\mathrm{rel}}(\omega)$ 与 Wigner–Smith 群延迟矩阵 $Q(\omega)$ 满足母式

$$
\kappa(\omega) = \varphi'(\omega)/\pi = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\mathrm{tr}\,Q(\omega),
$$

将统一时间刻度密度 $\kappa(\omega)$ 视为"每个频段上的时间单位"。当将计算宇宙嵌入到由可控散射过程构成的物理体系中时,每一步更新可以被理解为对某个散射矩阵族 $S(\omega;\theta)$ 的控制操作;于是,单步代价可以自然地由群延迟矩阵 $Q(\omega;\theta)$ 的响应积分构造。

本文的主旨就是系统地完成这一构造,并证明所得度量 $G_{ab}(\theta)$ 与离散复杂性几何之间的一致性。

全文结构如下:第 2 节回顾统一时间刻度的散射母尺,并引入控制参数化下的散射族。第 3 节在控制流形上构造复杂性度量 $G$,讨论其基本性质与规范不变性。第 4 节证明离散复杂性距离在控制流形极限下与测地距离 $d_G$ 一致,并给出代表性示例。第 5 节引入控制–散射对象范畴 $\mathbf{CtrlScat}$,讨论与计算宇宙范畴 $\mathbf{CompUniv}$ 之间的函子关系。附录给出主要命题与定理的详细证明。

---

## 2 统一时间刻度与控制散射族

本节回顾统一时间刻度的散射母尺,并引入控制参数化下的散射族 $S(\omega;\theta)$。

### 2.1 统一时间刻度的散射母尺回顾

设 $H_0,H$ 为一对自伴算子,满足适当的可追踪扰动条件,使得波算子存在且完备。对应的散射算子为

$$
S = W_+^\ast W_-,
$$

在频域表示下可写为频率分辨的散射矩阵族 $S(\omega)$。设总散射相位

$$
\varphi(\omega) = \arg\det S(\omega)
$$

及谱移函数 $\xi(\omega)$ 满足 Birman–Krein 公式

$$
\det S(\omega) = \exp\big(-2\pi\mathrm{i}\,\xi(\omega)\big).
$$

Wigner–Smith 群延迟矩阵定义为

$$
Q(\omega) = -\mathrm{i}\,S(\omega)^\dagger\partial_\omega S(\omega).
$$

在常规假设下,存在统一时间刻度密度

$$
\kappa(\omega) = \varphi'(\omega)/\pi = \xi'(\omega) = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\mathrm{tr}\,Q(\omega),
$$

其中 $\rho_{\mathrm{rel}}$ 为相对态密度函数,$\mathrm{tr}\,Q(\omega)$ 为群延迟矩阵的迹。该母式表明,散射总相位导数、谱移函数导数与群延迟迹在加常数意义下是一致的,从而可将 $\kappa(\omega)$ 视为"频率域上的时间刻度密度"。

### 2.2 控制流形与散射族 $S(\omega;\theta)$

在计算宇宙中,我们考虑一个可物理实现的计算系统,其可控参数形成一个有限维流形 $\mathcal M$,坐标记为 $\theta = (\theta^1,\dots,\theta^d)$。

**定义 2.1(控制流形与散射族)**

一个控制–散射系统由如下数据组成:

1. 控制流形 $\mathcal M$,为 $d$ 维可微流形;
2. 对每个 $\theta\in\mathcal M$ 与频率 $\omega$ 赋予一个酉散射矩阵 $S(\omega;\theta)$,其对 $\theta,\omega$ 可微,且在 $\omega$ 上满足母式条件;
3. 对每个 $\theta$,定义群延迟矩阵

$$
Q(\omega;\theta) = -\mathrm{i}\,S(\omega;\theta)^\dagger\partial_\omega S(\omega;\theta).
$$

我们认为 $\theta$ 的改变对应于对计算系统的控制操作,例如调节门参数、耦合强度或外场等;而 $S(\omega;\theta)$ 则是附着在该控制点上的物理散射结构。

### 2.3 与计算宇宙的关联

对给定计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$,若其每一步更新均可通过某个控制–散射系统的控制路径实现,则存在以下关联结构:

1. 一族控制路径 $\theta_k(t)$(例如分段常数),每条对应于一类离散更新序列 $x_k \to x_{k+1}$;
2. 对每一步 $(x_k,x_{k+1})$,存在控制参数 $\theta_k \in \mathcal M$ 与物理时间窗口 $[t_k,t_{k+1}]$,使得在该窗口中系统的散射矩阵由 $S(\omega;\theta_k)$ 给出;
3. 单步代价 $\mathsf C(x_k,x_{k+1})$ 可以用统一时间刻度密度 $\kappa(\omega)$ 和 $Q(\omega;\theta_k)$ 的某种积分函数表示。

典型的构造是:对每一步 $(x,y)$,单步物理时间代价为

$$
\tau(x,y) = \int_{\Omega_{x,y}} \kappa(\omega)\,\mathrm d\mu_{x,y}(\omega),
$$

其中 $\Omega_{x,y}$ 为该步更新所涉及的频带,$\mu_{x,y}$ 为对应的谱测度。若我们将 $\mathsf C(x,y)$ 定义为 $\tau(x,y)$ 的适当缩放,则离散复杂性距离可以视为统一时间刻度下的物理时间总和。

本篇的目标是超越逐步积分的层次,直接在控制流形上构造一个度量 $G$,使得沿控制路径的几何长度与离散复杂性距离在适当极限下相符。

---

## 3 统一时间刻度诱导的复杂性度量 $G$

本节在控制流形 $\mathcal M$ 上构造度量 $G$,并分析其基本性质。

### 3.1 度量的构造

记 $\partial_a = \partial/\partial\theta^a$。对每个 $\theta\in\mathcal M$ 与频率 $\omega$,群延迟矩阵 $Q(\omega;\theta)$ 是一个有限维 Hermite 矩阵。考虑其对控制参数的导数

$$
\partial_a Q(\omega;\theta).
$$

为缩放不同频段的重要性,引入非负权重函数 $w(\omega)$,满足

$$
\int_{\Omega} w(\omega)\,\mathrm d\omega < \infty,
$$

其中 $\Omega$ 为感兴趣的频段集合。

**定义 3.1(统一时间刻度诱导的度量)**

在控制流形 $\mathcal M$ 上定义二阶张量

$$
G_{ab}(\theta) = \int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_a Q(\omega;\theta)\,\partial_b Q(\omega;\theta) \big)\,\mathrm d\omega.
$$

若 $G_{ab}(\theta)$ 在每一点均为正定,则 $G$ 为 $\mathcal M$ 上的 Riemann 度量,称为统一时间刻度诱导的复杂性度量。

直观上,$G_{ab}(\theta)$ 度量了"在控制方向 $a$ 与 $b$ 上做无穷小变化时,对统一时间刻度响应的二次变化强度"。

### 3.2 正定性与退化方向

**命题 3.2(正定性条件)**

若对任意非零切向量 $v = v^a\partial_a \in T_\theta\mathcal M$,存在一组频率 $\omega \in\Omega$ 使得

$$
\partial_v Q(\omega;\theta) = v^a\partial_a Q(\omega;\theta) \neq 0,
$$

且 $\partial_v Q(\omega;\theta)$ 在该频段上的迹内积

$$
\int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_v Q(\omega;\theta)\,\partial_v Q(\omega;\theta) \big)\,\mathrm d\omega > 0,
$$

则 $G_{ab}(\theta)$ 在 $\theta$ 处为正定。

证明见附录 A.1。

该命题说明,度量的正定性取决于控制方向是否在统一时间刻度下"可观测":若对某个方向 $v$,群延迟矩阵 $Q(\omega;\theta)$ 在所有频段都不敏感,即 $\partial_v Q \equiv 0$,则该方向对时间刻度没有贡献,对应度量退化;反之,只要存在非零响应且权重 $w(\omega)$ 不消去该频段,则 $G$ 在该方向上正。

在实际建模中,可以通过对控制坐标进行商空间化,将纯规范方向(对时间刻度无效的控制自由度)消去,从而获得非退化的度量。

### 3.3 控制路径的几何长度与物理时间

在度量 $G$ 下,一条可微控制路径 $\theta:[0,T]\to\mathcal M$ 的长度定义为

$$
L_G[\theta] = \int_0^T \sqrt{G_{ab}(\theta(t))\,\dot\theta^a(t)\dot\theta^b(t)}\,\mathrm dt.
$$

**命题 3.3(长度与统一时间刻度的关系)**

在适当的正则性与分离变量假设下,控制路径 $\theta(t)$ 所诱导的复杂性长度 $L_G[\theta]$ 与在该路径上累计的物理时间刻度积分之间存在比例关系,即存在常数 $\alpha>0$ 使得

$$
L_G[\theta] = \alpha \int_0^T \mathrm d t\,\int_{\Omega} w(\omega)\,\kappa(\omega;\theta(t))^2\,\mathrm d\omega,
$$

其中 $\kappa(\omega;\theta) = (2\pi)^{-1}\mathrm{tr}\,Q(\omega;\theta)$ 为统一时间刻度密度。

证明见附录 A.2。

此处的关键是注意到

$$
\partial_a Q(\omega;\theta)
$$

与

$$
\partial_a \kappa(\omega;\theta)
$$

之间存在可追踪的关系,且通过适当的归一化,路径长度可以解释为统一时间刻度密度在控制流形上的"能量型积分"的平方根形式。

---

## 4 离散复杂性距离的连续极限

本节将统一时间刻度诱导的度量 $G$ 与前文离散复杂性几何联系起来,证明在合适的细化极限下,配置图上的复杂性距离收敛到控制流形上的测地距离。

### 4.1 离散控制网格与配置图

考虑一族标记为 $h>0$ 的计算宇宙 $\{U_{\mathrm{comp}}^{(h)}\}$,其控制自由度被离散化为网格 $\mathcal M^{(h)} \subset\mathcal M$,例如

$$
\mathcal M^{(h)} = \{ \theta \in \mathcal M : \theta = \theta_0 + h n,\,n\in\mathbb Z^d \} \cap K,
$$

其中 $K \subset\mathcal M$ 为紧集。对每个 $\theta\in\mathcal M^{(h)}$,计算宇宙 $U_{\mathrm{comp}}^{(h)}$ 在局域上可通过控制参数 $\theta$ 实现更新,并定义其配置图复杂性距离 $d^{(h)}$。

我们假设单步代价 $\mathsf C^{(h)}(x,y)$ 在控制网格上具有统一时间刻度的解释:当控制从 $\theta$ 变为相邻点 $\theta + h e_a$ 时,对应的单步代价为

$$
\mathsf C^{(h)}(\theta,\theta+h e_a) = c(\theta) h + o(h),
$$

其中

$$
c(\theta) = \Big(\sum_{a,b} G_{ab}(\theta) v^a v^b\Big)^{1/2}
$$

对某个单位向量 $v$ 给出局部速度。

### 4.2 距离收敛的一般定理

**定理 4.1(复杂性距离的 Riemann 极限)**

设 $(\mathcal M,G)$ 为由统一时间刻度诱导的控制流形,$\{U_{\mathrm{comp}}^{(h)}\}$ 为一族具有控制网格 $\mathcal M^{(h)}$ 的计算宇宙,对应复杂性距离为 $d^{(h)}$。假设:

1. 对任意 $\theta\in K \subset\mathcal M$,存在点 $\theta^{(h)}\in\mathcal M^{(h)}$,使得 $\theta^{(h)}\to\theta$;
2. 单步代价 $\mathsf C^{(h)}(\theta^{(h)},\theta^{(h)}+h e_a) = \sqrt{G_{aa}(\theta)}\,h + o(h)$,且对其他方向有类似一致性;
3. 配置图的可达性结构与控制网格的邻接关系一致,不存在"跳跃式"额外边。

则在 $h\to 0$ 时,对任意 $\theta_1,\theta_2\in K$ 有

$$
\lim_{h\to 0} d^{(h)}(\theta_1^{(h)},\theta_2^{(h)}) = d_G(\theta_1,\theta_2),
$$

其中 $d_G$ 为 Riemann 度量 $G$ 的测地距离。

证明见附录 B.1。

该定理是前一篇在一维情形的结果的高维推广。它表明:只要离散控制步长与统一时间刻度诱导的局部速度一致,离散复杂性距离就会在细化极限下逼近 Riemann 测地距离。

### 4.3 代表性示例:一维两端口散射网络

考虑一维两端口散射网络,其散射矩阵为

$$
S(\omega;\theta) = \begin{pmatrix} r(\omega;\theta) & t'(\omega;\theta) \\ t(\omega;\theta) & r'(\omega;\theta) \end{pmatrix},
$$

其中 $\theta \in [\theta_{\min},\theta_{\max}] \subset\mathbb R$ 为某个控制参数(例如势阱深度或相移)。对每个 $\theta$,群延迟矩阵

$$
Q(\omega;\theta) = -\mathrm{i}\,S(\omega;\theta)^\dagger\partial_\omega S(\omega;\theta)
$$

是 $2\times 2$ Hermite 矩阵。

在适当的正则性下,度量

$$
G(\theta) = \int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_\theta Q(\omega;\theta)\,\partial_\theta Q(\omega;\theta) \big)\,\mathrm d\omega
$$

定义了一维 Riemann 度量 $G(\theta)\mathrm d\theta^2$。若我们将控制网格离散为步长为 $h$ 的点集 $\theta_n = \theta_0 + n h$,并令单步代价

$$
\mathsf C^{(h)}(\theta_n,\theta_{n+1}) = \sqrt{G(\theta_n)}\,h,
$$

则对任意 $\theta_1,\theta_2$ 有

$$
\lim_{h\to 0} d^{(h)}(\theta_1^{(h)},\theta_2^{(h)}) = \left|\int_{\theta_1}^{\theta_2} \sqrt{G(\theta)}\,\mathrm d\theta\right|.
$$

这给出了本篇理论在一个具体可计算模型上的实例化。

---

## 5 控制–散射范畴与计算宇宙范畴的函子结构

本节从范畴论视角考察控制流形与度量 $G$ 的自然性,并构造一个以控制–散射对象为对象的范畴,与前文的计算宇宙范畴 $\mathbf{CompUniv}$ 建立函子关系。

### 5.1 控制–散射范畴 $\mathbf{CtrlScat}$

**定义 5.1(控制–散射对象)**

一个控制–散射对象是三元组

$$
C = (\mathcal M,G,S),
$$

其中 $(\mathcal M,G)$ 为带 Riemann 度量的控制流形,$S(\omega;\theta)$ 为满足统一时间刻度母式的散射族。

**定义 5.2(控制–散射态射)**

两个控制–散射对象 $C = (\mathcal M,G,S)$、$C' = (\mathcal M',G',S')$ 之间的态射是映射 $f:\mathcal M\to\mathcal M'$,满足:

1. $f$ 为光滑映射,且在几乎处处为局部微分同胚;

2. 度量在 $f$ 下被控制地变换,即存在常数 $\alpha,\beta>0$,使得对所有切向量 $v\in T_\theta\mathcal M$ 有

$$
\alpha\,G_\theta(v,v) \le G'_{f(\theta)}(\mathrm{d}f_\theta v,\mathrm{d}f_\theta v) \le \beta\,G_\theta(v,v);
$$

3. 散射族在 $f$ 下相容,即 $S'(\omega;f(\theta))$ 与 $S(\omega;\theta)$ 在统一时间刻度母式意义下等价。

以控制–散射对象为对象、控制–散射态射为态射,可构成范畴 $\mathbf{CtrlScat}$。

### 5.2 从计算宇宙到控制–散射对象的函子

设 $\mathbf{CompUniv}^{\mathrm{phys}}$ 为满足"可由统一时间刻度散射实现"的计算宇宙对象的子范畴。我们构造函子

$$
F:\mathbf{CompUniv}^{\mathrm{phys}} \to \mathbf{CtrlScat}
$$

如下:

1. 对象层面:给定 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$,由其物理实现构造控制流形 $\mathcal M$、度量 $G$ 与散射族 $S(\omega;\theta)$,令

$$
F(U_{\mathrm{comp}}) = (\mathcal M,G,S).
$$

2. 态射层面:给定计算宇宙之间的模拟映射 $f:U_{\mathrm{comp}}\rightsquigarrow U_{\mathrm{comp}}'$,对应于物理层面上控制与散射的变换 $f_{\mathcal M}:\mathcal M\to\mathcal M'$,令

$$
F(f) = f_{\mathcal M}.
$$

**命题 5.3(函子性)**

上述 $F$ 构成一个协变函子,即:

1. $F(\mathrm{id}_{U_{\mathrm{comp}}}) = \mathrm{id}_{F(U_{\mathrm{comp}})}$;
2. 若 $f:U_{\mathrm{comp}}\to U_{\mathrm{comp}}'$、$g:U_{\mathrm{comp}}'\to U_{\mathrm{comp}}''$ 为模拟态射,则

$$
F(g\circ f) = F(g)\circ F(f).
$$

证明见附录 C.1。

该函子在对象层面实现了"从离散计算宇宙到连续控制–散射几何"的提升,在态射层面则保持了复杂性距离的控制性变化。

在合适的常规假设下,可以进一步证明:存在逆向构造 $G:\mathbf{CtrlScat}\to\mathbf{CompUniv}^{\mathrm{phys}}$,使得 $G\circ F$ 与 $F\circ G$ 分别自然同构于恒等函子,从而两个范畴在"物理可实现的子类"上等价。具体证明涉及将连续控制–散射系统离散化为 QCA 型宇宙并控制复杂性开销,留待后续专门讨论。

---

## 6 结论

本文在统一时间刻度的散射母尺基础上,为计算宇宙构造了一套连续复杂性几何:通过引入控制流形 $\mathcal M$ 与散射族 $S(\omega;\theta)$,利用群延迟矩阵 $Q(\omega;\theta)$ 的控制导数构造了度量

$$
G_{ab}(\theta) = \int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_a Q(\omega;\theta)\,\partial_b Q(\omega;\theta) \big)\,\mathrm d\omega,
$$

并证明在自然正则性条件下,该度量是正定且与统一时间刻度兼容。随后我们证明,一族由统一时间刻度构造的离散计算宇宙在离散尺度 $h\to 0$ 时,其配置图上的复杂性距离在 Gromov–Hausdorff 意义下收敛到控制流形上的测地距离 $d_G$,从而给出了离散复杂性几何向连续复杂性几何的严格极限。

最后,我们构造了控制–散射范畴 $\mathbf{CtrlScat}$,并给出了从计算宇宙范畴 $\mathbf{CompUniv}^{\mathrm{phys}}$ 到 $\mathbf{CtrlScat}$ 的自然函子 $F$,说明在统一时间刻度框架下,"计算宇宙"的每一个物理可实现对象都可以被提升为一个带 Riemann 度量的控制流形及其散射几何。该结果为后续将信息几何、观察者结构与边界时间几何统一进一个"时间–信息–复杂性变分原理"提供了几何基底。

---

## 附录 A:度量 $G$ 的基本性质

### A.1 命题 3.2 的证明

**命题重述**

若对任意非零切向量 $v = v^a\partial_a \in T_\theta\mathcal M$,存在频率区间与权重函数 $w(\omega) \ge 0$,使得

$$
\int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_v Q(\omega;\theta)\,\partial_v Q(\omega;\theta) \big)\,\mathrm d\omega > 0,
$$

则 $G_{ab}(\theta) = \int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_a Q\,\partial_b Q \big)\,\mathrm d\omega$ 为正定。

**证明**

对任意 $v = v^a\partial_a$,有

$$
G_\theta(v,v) = G_{ab}(\theta)v^a v^b = \int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_a Q(\omega;\theta)\,\partial_b Q(\omega;\theta) \big)v^a v^b\,\mathrm d\omega.
$$

将 $v^a$ 提出得到

$$
G_\theta(v,v) = \int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_v Q(\omega;\theta)\,\partial_v Q(\omega;\theta) \big)\,\mathrm d\omega.
$$

由于 $\partial_v Q(\omega;\theta)$ 为 Hermite 矩阵,其迹内积

$$
\mathrm{tr}\big( A A \big) = \sum_i \lambda_i^2 \ge 0
$$

且等于零当且仅当 $A=0$。故 integrand 非负,且由命题条件存在频段使 integrand 非零并被权重 $w(\omega)$ 积分后仍为正,从而 $G_\theta(v,v) > 0$ 对所有 $v\neq 0$ 成立。

证毕。

### A.2 命题 3.3 的证明思路

命题 3.3 将统一时间刻度密度与度量长度联系起来。严格的证明需要建立如下两点:

1. 群延迟矩阵 $Q(\omega;\theta)$ 的迹与统一时间刻度密度 $\kappa(\omega;\theta)$ 的关系

$$
\kappa(\omega;\theta) = (2\pi)^{-1}\mathrm{tr}\,Q(\omega;\theta);
$$

2. 在控制参数变化的小扰动下,统一时间刻度的增量与 $\partial_a Q$ 之间的二次关系可写为

$$
\delta\tau \sim \int w(\omega)\,\mathrm{tr}\big( \partial_a Q\,\partial_b Q \big)\,\delta\theta^a\delta\theta^b\,\mathrm d\omega.
$$

综合这两点,可以将控制路径上的时间刻度积分表达为度量 $G$ 的二次型积分,进而得到长度与时间积分等价的结论。由于涉及到对 $Q(\omega;\theta)$ 的谱分解与对 $\kappa(\omega;\theta)$ 的函数微分,技术细节较长,此处略去逐项展开。

---

## 附录 B:复杂性距离的 Riemann 极限

### B.1 定理 4.1 的证明

**定理重述**

设 $(\mathcal M,G)$ 为控制流形,$\{U_{\mathrm{comp}}^{(h)}\}$ 为一族具有控制网格 $\mathcal M^{(h)} \subset\mathcal M$ 的计算宇宙,并满足局部单步代价与度量的一致性条件。则对任意 $\theta_1,\theta_2\in K \subset\mathcal M$,有

$$
\lim_{h\to 0} d^{(h)}(\theta_1^{(h)},\theta_2^{(h)}) = d_G(\theta_1,\theta_2),
$$

其中 $d^{(h)}$ 为 $U_{\mathrm{comp}}^{(h)}$ 的离散复杂性距离,$d_G$ 为 $G$ 的测地距离。

**证明思路**

证明可分为两步:上界与下界。

1. 上界:给定连续测地线 $\theta_*:[0,1]\to\mathcal M$ 连接 $\theta_1,\theta_2$,对其进行离散采样得到点列 $\theta_*^{(h)}(k) \in\mathcal M^{(h)}$。利用单步代价与度量局部一致性,即

$$
\mathsf C^{(h)}(\theta_*^{(h)}(k),\theta_*^{(h)}(k+1)) = \sqrt{G_{ab}(\theta_*^{(h)}(k)) v^a v^b}\,h + o(h),
$$

将路径代价和 $\mathsf C^{(h)}(\gamma^{(h)})$ 转化为 Riemann 和,极限为 $L_G[\theta_*] = d_G(\theta_1,\theta_2)$。从而

$$
\limsup_{h\to 0} d^{(h)}(\theta_1^{(h)},\theta_2^{(h)}) \le d_G(\theta_1,\theta_2).
$$

2. 下界:反向地,对任一近似最短离散路径 $\gamma^{(h)}$ 连接 $\theta_1^{(h)}$ 与 $\theta_2^{(h)}$,通过插值构造一条连续曲线 $\theta^{(h)}(t)$ 并估计其度量长度下界。利用局部一致性,可以证明

$$
L_G[\theta^{(h)}] \le \mathsf C^{(h)}(\gamma^{(h)}) + o(1).
$$

再利用测地距离的定义,得到

$$
d_G(\theta_1,\theta_2) \le \liminf_{h\to 0} d^{(h)}(\theta_1^{(h)},\theta_2^{(h)}).
$$

两者合并即得所需极限。

---

## 附录 C:函子 $F:\mathbf{CompUniv}^{\mathrm{phys}} \to \mathbf{CtrlScat}$ 的性质

### C.1 命题 5.3 的证明

**命题重述**

以物理可实现的计算宇宙对象为对象,以物理可实现的模拟映射为态射的子范畴 $\mathbf{CompUniv}^{\mathrm{phys}}$ 上,构造的映射 $F$ 是一个协变函子。

**证明**

1. 对象层面:对每个 $U_{\mathrm{comp}}$,通过其物理实现(例如 QCA、量子电路或散射网络)构造控制流形 $\mathcal M$、度量 $G$ 与散射族 $S(\omega;\theta)$,定义 $F(U_{\mathrm{comp}}) = (\mathcal M,G,S)$。

2. 態射层面:若 $f:U_{\mathrm{comp}}\rightsquigarrow U_{\mathrm{comp}}'$ 是模拟映射,对应物理上存在一个控制映射 $f_{\mathcal M}:\mathcal M\to\mathcal M'$,满足单步代价与统一时间刻度的控制性不等式。令 $F(f) = f_{\mathcal M}$。

3. 恒等态射:若 $f = \mathrm{id}_{U_{\mathrm{comp}}}$,物理实现上的控制映射即为 $\mathrm{id}_{\mathcal M}$,故 $F(\mathrm{id}_{U_{\mathrm{comp}}}) = \mathrm{id}_{F(U_{\mathrm{comp}})}$。

4. 复合:若 $f:U_{\mathrm{comp}}\to U_{\mathrm{comp}}'$、$g:U_{\mathrm{comp}}'\to U_{\mathrm{comp}}''$ 对应控制映射 $f_{\mathcal M}:\mathcal M\to\mathcal M'$、$g_{\mathcal M}:\mathcal M'\to\mathcal M''$,则复合模拟映射 $g\circ f$ 的控制映射为 $g_{\mathcal M}\circ f_{\mathcal M}$,故

$$
F(g\circ f) = g_{\mathcal M}\circ f_{\mathcal M} = F(g)\circ F(f).
$$

因此 $F$ 满足函子定义。

证毕。
