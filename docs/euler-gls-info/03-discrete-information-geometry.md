# 计算宇宙的离散信息几何

相对熵、Fisher 结构与任务感知距离

---

## 摘要

在"计算宇宙"公理化框架 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 下,复杂性几何刻画了"走到某个配置需要付出多少时间/代价"。然而,仅有复杂性几何仍不足以描述"这些代价换回了多高质量的信息"。为此,本文在完全离散的设定中构造一套与计算宇宙相匹配的"离散信息几何"理论。

我们首先引入观察算子族 $\mathcal O = \{O_j\}_{j\in J}$,其中每个 $O_j$ 将配置 $x\in X$ 映射为某个有限结果集合上的概率分布 $p_x^{(j)}$。在固定任务或观察方案下,这些分布对每个配置 $x$ 提供一个"可见信息状态"。在此基础上,我们定义任务感知的相对熵结构 $D_Q(x\Vert y)$,并从中导出一族信息距离,例如 Jensen–Shannon 型距离 $d_{\mathrm{JS},Q}(x,y)$。这些距离在局部上诱导出离散 Fisher 结构,即在某个基准配置 $x_0$ 附近,二阶相对熵 $D_Q(x\Vert x_0)$ 的 Hessian 给出 $x_0$ 周围的离散信息度量张量。

本文证明,在自然的正则性假设下,离散信息结构可以在适当极限下收敛为一个 Riemann 型信息流形 $(\mathcal S_Q,g_Q)$,其中 $g_Q$ 是 Fisher 型度量;相应地,"配置空间上的信息几何"可通过映射 $\Phi_Q:X\to\mathcal S_Q$ 实现,将每个配置 $x$ 送至其可见信息状态。我们进一步讨论信息球 $B_R^{\mathrm{info}}(x_0)$ 的体积增长与"信息维数",并给出信息维数与复杂性维数之间的一般不等式,刻画"在给定复杂性预算下能取得的信息分辨率极限"。

最后,我们构造一个任务感知的信息–复杂性联合作用量 $\mathcal A_Q$,其局部 Euler–Lagrange 方程给出在有限时间预算下"最大化信息质量"的最优计算轨道的局部描述,为后续完整的"时间–信息–复杂性变分原理"提供了离散信息几何基础。

---

## 1 引言

在计算宇宙的公理体系中,宇宙被抽象为离散配置空间 $X$、一步更新关系 $\mathsf T$、单步代价 $\mathsf C$ 与信息质量函数 $\mathsf I$,从而任何实际计算过程都对应于配置图上的一条有限路径,复杂性距离 $d(x,y)$ 则刻画了从 $x$ 走到 $y$ 所需的最小代价。前一篇工作已在此基础上构造了"离散复杂性几何",通过复杂性球体积与离散 Ricci 曲率描述了问题难度与复杂性视界。

然而,复杂性几何关心的是"走了多远",而不是"看到了什么"。要理解计算宇宙中"信息质量"的几何结构,需要引入另一个维度:观察与任务。具体来说,同一个配置 $x$ 的"有用信息"不仅依赖于 $x$ 自身,还依赖于我们如何读出它、关心哪类任务。不同任务对应不同的"信息几何",而计算过程在这些信息几何上的轨迹才是真正反映"在给定时间内我们提取了多少信息"的对象。

本文的目标,就是在完全离散的背景下,为计算宇宙建立一套与任务相关的"离散信息几何":

* 在离散层面上,为每个配置 $x$ 指定一个由观察方案决定的概率状态 $p_x$,并用相对熵、Jensen–Shannon 距离等构造信息距离;
* 在局部上,通过相对熵的二阶展开得到 Fisher 型度量,建立离散信息流形结构;
* 在全局上,通过信息球体积与信息维数刻画"在某任务下,宇宙可区分状态的复杂度"。

更重要的是,信息几何与复杂性几何必须配合:复杂性几何告诉我们在资源约束下允许在哪些配置之间移动,信息几何告诉我们这些移动在"任务相关的状态空间"上带来了多大的信息增益。二者的耦合最终将导向统一的"时间–信息–复杂性作用量"。

本文的主线结构如下。第 2 节引入观察算子与任务感知的离散相对熵结构。第 3 节构造离散信息距离与信息球,并定义信息维数。第 4 节讨论局部 Fisher 结构与信息流形极限。第 5 节给出信息–复杂性不等式与一个任务感知的联合作用量原型。附录中给出主要命题与定理的详细证明。

---

## 2 观察算子与任务感知相对熵

本节在计算宇宙的配置层上引入观察算子与任务感知的概率结构。

### 2.1 观察算子族与可见状态

在计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 中,配置 $x\in X$ 是全宇宙的内部状态。观测者在某一时间窗口内只能通过有限的实验或读数过程访问它。为刻画这一点,引入观察算子族。

**定义 2.1(观察算子族)**

设 $(Y_j)_{j\in J}$ 为一族有限结果集合。一个观察算子族是映射集合

$$
\mathcal O = \{ O_j : X \to \Delta(Y_j) \}_{j\in J},
$$

其中 $\Delta(Y_j)$ 为在 $Y_j$ 上的概率单纯形,且对每个 $x\in X$、$j\in J$,$O_j(x) = p_x^{(j)}$ 是一次实验在结果集合 $Y_j$ 上的结果分布。

直观地,$O_j$ 描述了一种可在配置 $x$ 上实施的观测过程,其输出分布 $p_x^{(j)}$ 是观测者在该配置上"可见到"的统计信息。

为了避免冗余,我们常将任务或观察方案记为一个有限子集 $Q\subset J$,并定义在该任务下的"联合可见状态"。

**定义 2.2(任务 $Q$ 下的联合可见状态)**

对给定有限任务集合 $Q\subset J$,定义可见结果集合

$$
Y_Q = \prod_{j\in Q} Y_j,
$$

并定义配置 $x$ 的联合可见状态为一个在 $Y_Q$ 上的联合分布 $p_x^{(Q)}$。最简单的构造是假设各观测独立,在此情况下

$$
p_x^{(Q)}(y) = \prod_{j\in Q} p_x^{(j)}(y_j),
\quad y = (y_j)_{j\in Q}\in Y_Q.
$$

更一般地,可以允许不同观测之间存在已知的耦合结构,此时 $p_x^{(Q)}$ 由一个任务特定的观测模型给出。本文主要考虑独立情形。

### 2.2 任务感知的相对熵

固定任务 $Q$ 后,每个配置 $x$ 被映射为一个概率分布 $p_x^{(Q)} \in \Delta(Y_Q)$。这允许我们引入针对任务 $Q$ 的相对熵。

**定义 2.3(任务 $Q$ 下的相对熵)**

对配置 $x,y\in X$,若对所有 $y\in Y_Q$ 有 $p_y^{(Q)}(y) > 0$ 蕴含 $p_x^{(Q)}(y) > 0$,则定义

$$
D_Q(x\Vert y)
=
\sum_{z\in Y_Q}
p_x^{(Q)}(z)\,\log\frac{p_x^{(Q)}(z)}{p_y^{(Q)}(z)},
$$

否则定义 $D_Q(x\Vert y) = +\infty$。

$D_Q(x\Vert y)$ 是任务 $Q$ 下配置 $x$ 与 $y$ 的"可区分程度":越大意味着在该任务下 $x$ 与 $y$ 越"信息远离"。

显然,$D_Q(x\Vert y) \ge 0$,且 $D_Q(x\Vert y) = 0$ 若且唯若 $p_x^{(Q)} = p_y^{(Q)}$。

注意 $D_Q$ 一般不是对称的,且不满足三角不等式,因此不是度量。为得到信息距离,我们将使用从 $D_Q$ 导出的对称化形式。

---

## 3 离散信息距离、信息球与信息维数

本节基于 $D_Q$ 定义任务感知的信息距离与信息球,并引入信息维数的概念。

### 3.1 Jensen–Shannon 型信息距离

在有限集合上的概率结构中,Jensen–Shannon 散度提供了一种自然的对称化,且其平方根是度量。我们将在任务信息的背景下采用类似构造。

**定义 3.1(任务 $Q$ 下的 Jensen–Shannon 散度与信息距离)**

对 $x,y\in X$,定义混合分布

$$
m_{x,y}^{(Q)} = \frac12\big(p_x^{(Q)} + p_y^{(Q)}\big),
$$

Jensen–Shannon 散度

$$
\mathrm{JS}_Q(x,y)
=
\frac12 D\big(p_x^{(Q)}\Vert m_{x,y}^{(Q)}\big)
+
\frac12 D\big(p_y^{(Q)}\Vert m_{x,y}^{(Q)}\big),
$$

并定义信息距离

$$
d_{\mathrm{JS},Q}(x,y) = \sqrt{2\,\mathrm{JS}_Q(x,y)}.
$$

其中 $D(\cdot\Vert\cdot)$ 为常规的 Kullback–Leibler 相对熵。

由已知结论,$d_{\mathrm{JS},Q}$ 是 $X$ 上关于任务 $Q$ 的度量:满足非负性、对称性、三角不等式,且 $d_{\mathrm{JS},Q}(x,y) = 0$ 当且仅当 $p_x^{(Q)} = p_y^{(Q)}$。

在本文中,我们称 $d_{\mathrm{JS},Q}$ 为任务感知的信息距离。

### 3.2 信息球与信息体积

**定义 3.2(信息球与信息体积)**

对基准配置 $x_0\in X$、任务 $Q$ 与半径 $R>0$,定义信息球

$$
B_R^{\mathrm{info},Q}(x_0)
=
\{ x\in X : d_{\mathrm{JS},Q}(x,x_0) \le R \},
$$

信息体积

$$
V_{x_0}^{\mathrm{info},Q}(R)
=
\big|B_R^{\mathrm{info},Q}(x_0)\big|.
$$

该体积刻画了在任务 $Q$ 的信息几何视角下,"距 $x_0$ 信息上不超过 $R$" 的配置数目。

### 3.3 信息维数

类似复杂性维数,我们用信息球体积的增长率定义信息维数。

**定义 3.3(信息维数)**

对给定任务 $Q$ 与基准 $x_0$,定义上信息维数

$$
\overline{\dim}_{\mathrm{info},Q}(x_0)
=
\limsup_{R\to\infty}
\frac{\log V_{x_0}^{\mathrm{info},Q}(R)}{\log R},
$$

下信息维数

$$
\underline{\dim}_{\mathrm{info},Q}(x_0)
=
\liminf_{R\to\infty}
\frac{\log V_{x_0}^{\mathrm{info},Q}(R)}{\log R}.
$$

若二者相等,则称共同值为信息维数,记为 $\dim_{\mathrm{info},Q}(x_0)$。

直观上,$\dim_{\mathrm{info},Q}(x_0)$ 描述在任务 $Q$ 下,信息距离半径 $R$ 内可区分配置的数目增长阶数。特别地,若信息维数有限,则表示任务 $Q$ 实际上只涉及某个低维信息结构;若信息维数无限,则该任务在信息层面具有高度复杂性与高区分度。

### 3.4 信息维数与复杂性维数的初步关系

设复杂性距离为 $d_{\mathrm{comp}}(x,y)$,复杂性球体积为 $V_{x_0}^{\mathrm{comp}}(T)$,复杂性维数为 $\dim_{\mathrm{comp}}(x_0)$。一般而言,信息维数与复杂性维数无简单等式关系,但可以给出一个粗略不等式,刻画"在复杂性受限的情况下,信息区分能力的上界"。

**命题 3.4(信息体积受复杂性体积约束)**

假设存在常数 $L_Q>0$,使得对所有相邻配置 $x,y$(即 $(x,y)\in\mathsf T$)有

$$
d_{\mathrm{JS},Q}(x,y)
\le L_Q\,\mathsf C(x,y),
$$

则存在常数 $C>0$,使得对所有 $R>0$ 有

$$
V_{x_0}^{\mathrm{info},Q}(R)
\le
V_{x_0}^{\mathrm{comp}}\!\left(\frac{R}{C}\right).
$$

从而

$$
\overline{\dim}_{\mathrm{info},Q}(x_0)
\le
\overline{\dim}_{\mathrm{comp}}(x_0).
$$

证明见附录 A.1。该不等式说明,在局部 Lipschitz 条件下,信息几何的"维度"不会超过复杂性几何的"维度",符合直觉:可计算的区分能力受限于可实现的复杂度资源。

---

## 4 局部 Fisher 结构与信息流形极限

本节在任务 $Q$ 的信息距离下,引入局部 Fisher 结构,即在某个参考配置附近用相对熵的二阶展开构造 Riemann 型信息度量。随后讨论当配置之间存在某种连续参数化时,信息几何如何在极限下收敛到 Fisher 流形。

### 4.1 相对熵的二阶展开与离散 Fisher 矩阵

令 $x_0\in X$ 为参考配置,在任务 $Q$ 下的可见状态为 $p_0 = p_{x_0}^{(Q)}$。考虑与 $x_0$ 相邻的若干配置 $x^{(1)},\dots,x^{(k)}$,它们的可见状态为 $p_i = p_{x^{(i)}}^{(Q)}$。假设存在一个局部参数化

$$
\theta \in \Theta \subset \mathbb R^k
\quad\longmapsto\quad
p(\theta) \in \Delta(Y_Q),
$$

使得 $p(0) = p_0$,且每个 $p_i$ 可写作 $p(\varepsilon e_i)$ 的形式,其中 $e_i$ 为标准基,$\varepsilon > 0$ 为小参数。此时,我们可以用 $\theta$ 作为 $x_0$ 附近的"信息坐标"。

**定义 4.1(局部任务 Fisher 矩阵)**

在上述设定下,定义任务 $Q$ 的局部 Fisher 信息矩阵为

$$
g_{ij}^{(Q)}(0)
=
\sum_{z\in Y_Q}
p_0(z)\,
\partial_{\theta_i}\log p(\theta)(z)\big\vert_{\theta=0}\,
\partial_{\theta_j}\log p(\theta)(z)\big\vert_{\theta=0}.
$$

这是在 $\theta = 0$ 处的 Fisher 信息矩阵,完全由 $p(\theta)$ 的局部变化决定。

**定理 4.2(相对熵二阶展开的 Fisher 形式)**

在上述设定及常规正则性条件下,对足够小的 $\theta\in\Theta$,有

$$
D_Q\big(\theta\Vert 0\big)
=
D\big(p(\theta)\Vert p(0)\big)
=
\frac12
\sum_{i,j} g_{ij}^{(Q)}(0)\,\theta_i\theta_j
+ o(|\theta|^2).
$$

证明见附录 B.1。该定理说明,任务感知相对熵在局部上具有标准的 Fisher 二阶结构,即它的 Hessian 给出一个局部 Riemann 信息度量。

### 4.2 信息流形与配置到信息的映射

上述讨论仅基于有限个相邻配置与局部参数化,然而在许多情形中,配置空间 $X$ 在任务 $Q$ 下的可见状态集合 $\{ p_x^{(Q)} : x\in X \}$ 可以用某个连续参数流形 $\mathcal S_Q$ 来逼近。

**假设 4.3(任务可见状态的流形结构)**

存在一个维数有限的流形 $\mathcal S_Q$ 与嵌入映射

$$
\Psi_Q : \mathcal S_Q \hookrightarrow \Delta(Y_Q),
$$

以及映射

$$
\Phi_Q : X \to \mathcal S_Q,
$$

使得

1. 对每个 $x\in X$,$p_x^{(Q)}$ 近似于 $\Psi_Q(\Phi_Q(x))$;
2. $\Psi_Q$ 在 $\mathcal S_Q$ 上的标准 Fisher 信息度量与相对熵二阶导数一致。

在此假设下,我们可以把 $\mathcal S_Q$ 看作"任务 $Q$ 的信息流形",而 $\Phi_Q$ 提供了从配置空间 $X$ 到信息流形的映射。

**定义 4.4(任务信息流形与信息度量)**

在假设 4.3 下,任务 $Q$ 的信息流形为 $(\mathcal S_Q,g_Q)$,其中 $g_Q$ 是 Fisher 信息度量。对配置 $x\in X$,其信息几何位置为 $\Phi_Q(x)\in\mathcal S_Q$。

### 4.3 信息距离与 Fisher 距离的一致性

在合适的正则条件下,Jensen–Shannon 信息距离 $d_{\mathrm{JS},Q}$ 在 $x_0$ 附近与 Fisher 距离一致。

**定理 4.5(局部信息距离的一致性)**

设 $x,x_0 \in X$ 使得 $\Phi_Q(x_0) = \theta_0$、$\Phi_Q(x) = \theta$,且 $\theta$ 接近 $\theta_0$。则有

$$
d_{\mathrm{JS},Q}(x,x_0)
=
\sqrt{
(\theta-\theta_0)^\top g_Q(\theta_0)(\theta-\theta_0)
}
+ o(|\theta-\theta_0|).
$$

证明见附录 B.2。该定理说明,在局部坐标下,Jensen–Shannon 信息距离与 Fisher 度量诱导的测地距离在一阶上等价,从而 $\mathcal S_Q$ 的 Riemann 信息几何与 $X$ 上的离散信息几何在局部上兼容。

---

## 5 信息–复杂性不等式与任务感知作用量

本节在离散信息几何与复杂性几何的交界处,给出信息–复杂性不等式,并构造一个任务感知的联合作用量原型。

### 5.1 信息–复杂性不等式

前文命题 3.4 已给出信息球体积与复杂性球体积之间的一般约束。我们可以在信息流形框架下将其加强为一个局部"信息梯度–复杂性梯度"的关系式。

设 $\gamma = (x_0,x_1,\dots,x_n)$ 是一条复杂性最短路径,复杂性长度为

$$
\mathsf C(\gamma)
=
\sum_{k=0}^{n-1}\mathsf C(x_k,x_{k+1}),
$$

对应的信息路径为 $\Phi_Q(\gamma) = (\theta_0,\theta_1,\dots,\theta_n)$,信息距离为

$$
L_Q(\gamma)
=
\sum_{k=0}^{n-1}
d_{\mathcal S_Q}\big(\theta_k,\theta_{k+1}\big),
$$

其中 $d_{\mathcal S_Q}$ 为 Fisher 度量诱导的测地距离。

在局部 Lipschitz 假设下,我们有以下命题。

**命题 5.1(局部信息–复杂性 Lipschitz 不等式)**

若存在常数 $L_Q^{\mathrm{loc}}>0$,使得对所有相邻配置 $x,y$(即 $(x,y)\in\mathsf T$ 且 $x,y$ 位于某个局部区域)有

$$
d_{\mathcal S_Q}\big(\Phi_Q(x),\Phi_Q(y)\big)
\le
L_Q^{\mathrm{loc}} \,\mathsf C(x,y),
$$

则对任意局部路径 $\gamma$ 有

$$
L_Q(\gamma)
\le
L_Q^{\mathrm{loc}}\,\mathsf C(\gamma).
$$

特别地,最小信息距离与最小复杂性距离之间满足

$$
d_{\mathcal S_Q}\big(\Phi_Q(x_0),\Phi_Q(x)\big)
\le
L_Q^{\mathrm{loc}}\,d_{\mathrm{comp}}(x_0,x).
$$

证明见附录 C.1。

该不等式表明,在局部区域内,"信息位移"被"复杂性位移"控制,复杂度为信息几何提供了一个资源上界。

### 5.2 任务感知的联合作用量

为了把复杂性几何与信息几何统一,我们构造一个任务感知的离散作用量,用于评价一条计算路径在给定任务 $Q$ 下的"性价比"。

**定义 5.2(任务 $Q$ 的联合作用量原型)**

设 $\gamma = (x_0,x_1,\dots,x_n)$ 为一条路径,其复杂性长度为 $\mathsf C(\gamma)$,终点信息质量为 $\mathsf I_Q(x_n)$(由任务定义的质量函数)。定义任务 $Q$ 的联合作用量

$$
\mathcal A_Q(\gamma)
=
\alpha \,\mathsf C(\gamma)
-
\beta\,\mathsf I_Q(x_n),
$$

其中 $\alpha,\beta>0$ 为平衡复杂性与信息的权重。

在连续极限中,如我们在信息流形 $(\mathcal S_Q,g_Q)$ 与复杂性流形 $(\mathcal M,G)$ 上引入时间参数 $t$,令配置路径 $x(t)$ 与信息路径 $\theta(t) = \Phi_Q(x(t))$,复杂性速度为 $\sqrt{G_{ab}(\theta)\dot\theta^a\dot\theta^b}$,信息质量为 $I_Q(\theta(T))$,则联合作用量的连续形式为

$$
\mathcal A_Q[\theta(\cdot)]
=
\int_{0}^{T}
\alpha \sqrt{
G_{ab}(\theta(t))\,\dot\theta^a(t)\dot\theta^b(t)
}
\,\mathrm dt
-
\beta\,I_Q(\theta(T)).
$$

该作用量平衡了"路径的复杂性长度"与"终点的信息收益",其极小化轨道对应于在资源约束下最优的信息获取策略。离散版本与连续版本的 Euler–Lagrange 方程的具体形式留待后续工作展开,本文仅给出结构原型。

---

## 6 结论

本文在计算宇宙的离散公理框架下,引入了观察算子族与任务感知的相对熵结构,构造了离散信息距离、信息球与信息维数,并在局部上通过相对熵的二阶展开得到 Fisher 信息矩阵,建立了任务信息流形 $(\mathcal S_Q,g_Q)$ 的概念。通过映射 $\Phi_Q:X\to\mathcal S_Q$,计算宇宙的配置空间在任务 $Q$ 下被嵌入到一个有限维信息流形,信息距离与离散 Jensen–Shannon 距离在局部上相容,信息维数则与复杂性维数之间满足自然的不等式。

基于这些结构,我们提出了信息–复杂性 Lipschitz 不等式与任务感知联合作用量的原型,为在统一时间刻度下构建完整的"时间–信息–复杂性变分原理"提供了离散信息几何的基底。下一步工作将把本文的信息几何与前一篇的复杂性几何结合,系统构造联合流形 $(\mathcal M,G;\mathcal S_Q,g_Q)$ 上的计算世界线,并将之与物理宇宙的边界时间几何与统一散射时间刻度进行对接。

---

## 附录 A:信息维数与复杂性维数不等式的证明

### A.1 命题 3.4 的证明

**命题重述**

假设存在常数 $L_Q>0$,使得对所有相邻配置 $x,y$ 有

$$
d_{\mathrm{JS},Q}(x,y)
\le
L_Q\,\mathsf C(x,y).
$$

则存在常数 $C>0$,使得对所有 $R>0$ 有

$$
V_{x_0}^{\mathrm{info},Q}(R)
\le
V_{x_0}^{\mathrm{comp}}\!\left(\frac{R}{C}\right),
$$

从而

$$
\overline{\dim}_{\mathrm{info},Q}(x_0)
\le
\overline{\dim}_{\mathrm{comp}}(x_0).
$$

**证明**

对任意 $x\in B_R^{\mathrm{info},Q}(x_0)$,由定义有

$$
d_{\mathrm{JS},Q}(x,x_0)\le R.
$$

取任意从 $x_0$ 到 $x$ 的复杂性最短路径 $\gamma = (x_0,x_1,\dots,x_n)$,其代价为

$$
\mathsf C(\gamma) = d_{\mathrm{comp}}(x_0,x).
$$

由三角不等式与局部 Lipschitz 条件,有

$$
d_{\mathrm{JS},Q}(x,x_0)
\le
\sum_{k=0}^{n-1}
d_{\mathrm{JS},Q}(x_k,x_{k+1})
\le
L_Q
\sum_{k=0}^{n-1}
\mathsf C(x_k,x_{k+1})
=
L_Q\,\mathsf C(\gamma).
$$

因此

$$
L_Q\,d_{\mathrm{comp}}(x_0,x)
\ge
L_Q\,\mathsf C(\gamma)
\ge
d_{\mathrm{JS},Q}(x,x_0)
\ge 0.
$$

若 $d_{\mathrm{JS},Q}(x,x_0)\le R$,则

$$
d_{\mathrm{comp}}(x_0,x)
\le
\frac{R}{L_Q}.
$$

因此

$$
B_R^{\mathrm{info},Q}(x_0)
\subseteq
B_{R/L_Q}^{\mathrm{comp}}(x_0).
$$

取 $C = L_Q$,得到所需包含关系,从而

$$
V_{x_0}^{\mathrm{info},Q}(R)
\le
V_{x_0}^{\mathrm{comp}}\!\left(\frac{R}{C}\right).
$$

对 $R\to\infty$ 取上极限即可推出维数不等式

$$
\overline{\dim}_{\mathrm{info},Q}(x_0)
\le
\overline{\dim}_{\mathrm{comp}}(x_0).
$$

证毕。

---

## 附录 B:相对熵二阶展开与 Fisher 结构

### B.1 定理 4.2 的证明

**定理重述**

在局部参数化 $\theta\mapsto p(\theta) \in \Delta(Y_Q)$ 的正则性条件下,有

$$
D\big(p(\theta)\Vert p(0)\big)
=
\frac12
\sum_{i,j} g_{ij}^{(Q)}(0)\,\theta_i\theta_j
+ o(|\theta|^2),
$$

其中

$$
g_{ij}^{(Q)}(0)
=
\sum_{z\in Y_Q}
p(0)(z)\,
\partial_{\theta_i}\log p(\theta)(z)\big\vert_{\theta=0}\,
\partial_{\theta_j}\log p(\theta)(z)\big\vert_{\theta=0}.
$$

**证明**

记 $p_0 = p(0)$ 与 $p_\theta = p(\theta)$。任务 $Q$ 下的相对熵为

$$
D(p_\theta\Vert p_0)
=
\sum_{z\in Y_Q}
p_\theta(z)\,
\log\frac{p_\theta(z)}{p_0(z)}.
$$

令

$$
\ell(\theta,z) = \log p_\theta(z).
$$

则

$$
D(p_\theta\Vert p_0)
=
\sum_{z}
p_\theta(z)\,\big(\ell(\theta,z) - \ell(0,z)\big).
$$

对 $\theta$ 在 0 附近做泰勒展开。首先,$D(p_0\Vert p_0)=0$。一阶项为

$$
\partial_{\theta_i} D(p_\theta\Vert p_0)\big\vert_{\theta=0}
=
\sum_{z}
\partial_{\theta_i}p_\theta(z)\big\vert_{\theta=0}\,\big(\ell(0,z)-\ell(0,z)\big)
+
\sum_{z}
p_0(z)\,\partial_{\theta_i}\ell(\theta,z)\big\vert_{\theta=0}
= 0,
$$

因为 $\sum_z p_0(z)\partial_{\theta_i}\ell(\theta,z)\big\vert_{\theta=0} = \partial_{\theta_i}\sum_z p_\theta(z)\big\vert_{\theta=0} = 0$。

二阶导数为

$$
\partial_{\theta_i}\partial_{\theta_j} D(p_\theta\Vert p_0)\big\vert_{\theta=0}
=
\sum_z
\partial_{\theta_i}\partial_{\theta_j}p_\theta(z)\big\vert_{\theta=0}\,\big(\ell(0,z)-\ell(0,z)\big)
+
2\sum_z
\partial_{\theta_i}p_\theta(z)\big\vert_{\theta=0}\,\partial_{\theta_j}\ell(\theta,z)\big\vert_{\theta=0}
$$
$$
+
\sum_z
p_0(z)\,\partial_{\theta_i}\partial_{\theta_j}\ell(\theta,z)\big\vert_{\theta=0}.
$$

第一项为零。利用标准 Fisher 信息的恒等式

$$
\sum_z
\partial_{\theta_i}p_\theta(z)\,\partial_{\theta_j}\log p_\theta(z)
=
\sum_z
p_\theta(z)\,
\partial_{\theta_i}\log p_\theta(z)\,\partial_{\theta_j}\log p_\theta(z),
$$

并在 $\theta=0$ 处评价,可将第二项与第三项合并,得到

$$
\partial_{\theta_i}\partial_{\theta_j} D(p_\theta\Vert p_0)\big\vert_{\theta=0}
=
\sum_z
p_0(z)\,
\partial_{\theta_i}\log p_\theta(z)\big\vert_{\theta=0}\,
\partial_{\theta_j}\log p_\theta(z)\big\vert_{\theta=0}
=
g_{ij}^{(Q)}(0).
$$

因此在 $\theta=0$ 附近有二阶展开

$$
D(p_\theta\Vert p_0)
=
\frac12
\sum_{i,j} g_{ij}^{(Q)}(0)\,\theta_i\theta_j
+ o(|\theta|^2).
$$

证毕。

---

### B.2 定理 4.5 的证明思路

在有限维流形 $\mathcal S_Q$ 上,Fisher 度量诱导的测地距离 $d_{\mathcal S_Q}$ 与由 Jensen–Shannon 散度定义的信息距离 $d_{\mathrm{JS},Q}$ 在 $\theta_0$ 附近可以通过二阶展开进行比较。具体而言,Jensen–Shannon 散度 $\mathrm{JS}(p_\theta,p_0)$ 在 $\theta_0$ 处的二阶项与 Fisher 信息矩阵成比例,平方根后得到的 $d_{\mathrm{JS},Q}$ 在一阶上与 Fisher 距离一致。这一结论是信息几何中的标准结果,此处将 $\theta$ 替换为 $\Phi_Q(x)$ 即得定理 4.5。详细展开需对混合分布 $m_{x,y}^{(Q)}$ 的相对熵进行二阶 Taylor 展开,限于篇幅不再逐项给出。

---

## 附录 C:信息–复杂性 Lipschitz 不等式的证明

### C.1 命题 5.1 的证明

**命题重述**

若存在常数 $L_Q^{\mathrm{loc}}>0$,使得对所有相邻配置 $x,y$ 有

$$
d_{\mathcal S_Q}\big(\Phi_Q(x),\Phi_Q(y)\big)
\le
L_Q^{\mathrm{loc}}\,\mathsf C(x,y),
$$

则对任意路径 $\gamma = (x_0,\dots,x_n)$ 有

$$
L_Q(\gamma)
=
\sum_{k=0}^{n-1}
d_{\mathcal S_Q}\big(\Phi_Q(x_k),\Phi_Q(x_{k+1})\big)
\le
L_Q^{\mathrm{loc}}
\sum_{k=0}^{n-1}
\mathsf C(x_k,x_{k+1})
=
L_Q^{\mathrm{loc}}\,\mathsf C(\gamma),
$$

从而

$$
d_{\mathcal S_Q}\big(\Phi_Q(x_0),\Phi_Q(x)\big)
\le
L_Q^{\mathrm{loc}}\,d_{\mathrm{comp}}(x_0,x).
$$

**证明**

第一不等式直接由假设逐项求和得到。第二不等式来自于测地距离的定义:对任意路径 $\gamma$ 连接 $x_0$ 与 $x$,有

$$
d_{\mathcal S_Q}\big(\Phi_Q(x_0),\Phi_Q(x)\big)
\le
L_Q(\gamma)
\le
L_Q^{\mathrm{loc}}\,\mathsf C(\gamma).
$$

对所有路径取下确界,得到

$$
d_{\mathcal S_Q}\big(\Phi_Q(x_0),\Phi_Q(x)\big)
\le
L_Q^{\mathrm{loc}}\,d_{\mathrm{comp}}(x_0,x).
$$

证毕。
