# 观察者共识的几何化：冲突指标、信息几何与边界时间结构

## Abstract

在无时间的块宇宙视角中,宇宙被建模为一张由因果偏序构成的拓扑结构,而任何具体观察者只能访问其中有限区域并携带关于全局因果网的预测模型。不同观察者对同一因果区域的描述在多个层面上产生冲突:局部偏序粘合时出现有向环,时间刻度函数不一致,广义熵箭头与模流方向不一致,以及 Null–Modular 双覆盖中的 $\mathbb Z_2$ 扇区错配。本文构建一个统一的"共识几何空间",将观察者的统计模型、因果集、时间刻度与边界状态嵌入到一个带有 Riemann 度量的乘积流形上,并在其上定义总势能函数,将上述冲突指标编码为几何势能。在线性与非线性信息几何、因果集几何与量子态空间几何的协同下,本文证明:在完备性与强凸性等适定假设下,该势能的梯度流给出一种自然的"共识动力学",使所有冲突指标单调下降并收敛到"共识流形"。在共识流形上,局部偏序可无矛盾地粘合为全局因果偏序,统一母刻度函数仅差仿射重标,广义熵箭头与模流方向在重叠区域一致,所有观察者共处同一 $\mathbb Z_2$ 拓扑扇区。本文最后将该几何化框架与边界时间几何、统一时间刻度以及 Null–Modular 双覆盖耦合,并提出在多观察者量子场论、全息信息和多智能体系统中的应用与工程化实现路径。

## Keywords

因果网;信息几何;Riemann 共识;边界时间几何;模流;Bures 度量;Null–Modular 双覆盖;多观察者系统

---

## Introduction & Historical Context

### 时间与因果的无时间图景

在经典相对论中,时空被刻画为带有因果锥结构的 Lorentz 流形,时间作为流形参数出现;而在因果集方案中,空间与时间被替换为离散事件集合及其偏序关系,几何被认为由"次序+计数"决定。([www2.perimeterinstitute.ca][1]) 这一视角将"时间"从基本结构中剥离,只保留事件间的因果偏序 $(E,\preceq)$,时间箭头与刻度则是从偏序与度量结构中导出。

在量子场论与引力的交汇处,边界方法与全息思想表明,许多动力学信息可以压缩到边界上:散射矩阵的能量导数给出 Wigner–Smith 群延迟与相位时间,继而定义散射时间刻度;([Optica Publishing Group][2]) Gibbons–Hawking–York 边界项与 Brown–York 准局域量则表明,引力作用的良定变分与能量定义在关键层面上是"边界现象"。([APS Link][3]) 此外,Tomita–Takesaki 模块理论与 Connes–Rovelli 热时间假说将时间刻画为状态–代数对内禀的模流参数,为"边界时间几何"提供代数基础。

### 信息几何、量子态几何与共识算法

在统计学与信息论方面,Fisher 信息度量与 Amari–Nagaoka 所发展的信息几何,将参数化统计模型看作带有 Fisher–Rao 度量的 Riemann 流形,给出散度与梯度流的自然几何背景。([bsi-ni.brain.riken.jp][4]) 在量子态空间上,Bures 度量与量子 Fisher 信息提供了密度矩阵空间的自然 Riemann 结构,与量子估计理论和几何相位密切相关。([语义学者][5])

另一方面,多智能体系统中的平均一致算法从 Euclid 空间推广到 Riemann 流形,形成 Riemann 共识理论。Tron 等人在有限曲率流形上构造了 Fréchet 均值的 Riemann 一致算法,并给出收敛条件;其后工作在更一般情形下分析了梯度流共识的病态与限制。([arXiv][6]) 这些研究揭示了"在弯曲几何上达成一致"的早期数学结构。

### 多观察者、一致性与边界时间几何

在块宇宙或因果集图景中,存在一个概念上的紧张:一方面,宇宙因果网本身被视为不依赖观察者的全局结构;另一方面,任何实际观察者只能访问有限的因果区域,获得有限精度的边界散射数据或模流信息,从而只能构造对全局结构的不完全预测。不同观察者之间对同一因果区域的判断——因果序、时间刻度、广义熵箭头、拓扑扇区——可能不一致。

传统上,对于多观察者一致性,人们更多讨论的是:在给定动力学规律下,如何从局域观测恢复一个共同的宏观几何;在多智能体学习中,如何通过通信与更新算法让所有代理收敛到同一模型。([arXiv][6]) 然而,将这些问题提升到"边界时间几何"语境,需要同时处理:

1. 统计模型空间上的信息几何;
2. 因果集模空间上的组合几何;
3. 母刻度函数空间上的 Hilbert 几何;
4. 边界量子态空间上的 Bures 几何与模流结构;
5. Null–Modular 双覆盖上的 $\mathbb Z_2$ 拓扑扇区。

本文的目标是:在统一时间刻度与边界时间几何框架下,为多观察者的冲突与共识提供一个严格的几何化刻画,构造一个"共识几何空间",并在其上定义一个自然的势能与梯度流,使"解决冲突"对应于该空间上的几何收缩过程。

### 主要贡献

在上述背景下,本文的贡献可以概括为:

1. 提出一族针对多观察者冲突的定量指标,分别刻画统计模型散度、因果偏序粘合冲突、母刻度函数不一致、广义熵箭头与模流方向失配、Null–Modular 双覆盖 $\mathbb Z_2$ 扇区的错配。
2. 构造一个统一的共识几何空间 $\mathcal M$,将统计流形、因果集模空间、母刻度 Hilbert 空间与边界状态空间通过带权直和度量粘合,形成一个适合描述多观察者状态的 Riemann 流形。
3. 在 $(\mathcal M,G)$ 上定义总势能函数 $F$,将上述冲突指标编码进去;证明沿梯度流 $\dot X=-\operatorname{grad}_G F$ 势能单调下降,并在强凸性与完备性条件下指数收敛到一个"共识流形" $\mathcal M_{\mathrm{cons}}$。
4. 在共识流形上,给出"完全共识"的几何–物理刻画:存在全局因果偏序、统一母刻度、统一熵箭头与模流、统一 $\mathbb Z_2$ 扇区,所有观察者状态可以嵌入同一边界时间几何与 Null–Modular 结构中。
5. 通过简单模型展示该框架在有限因果集、多智能体学习和边界散射网络中的应用潜力,并提出初步的工程实现方案。

---

## Model & Assumptions

### 宇宙因果网与因果集

设 $E$ 为宇宙中所有事件的集合。因果关系由偏序 $\preceq\subset E\times E$ 给出,满足:

1. 自反性:对任意 $e\in E$,有 $e\preceq e$;
2. 反对称性:若 $e\preceq f$ 且 $f\preceq e$,则 $e=f$;
3. 传递性:若 $e\preceq f$ 且 $f\preceq g$,则 $e\preceq g$。

二元组 $(E,\preceq)$ 称为宇宙因果网或因果集。与因果集理论相似,可以在适当假设下将 $(E,\preceq)$ 与连续时空几何联系起来,但本文不预设具体的连续极限,仅使用偏序结构。([www2.perimeterinstitute.ca][1])

对任意事件 $e\in E$,定义其因果未来与过去为

$$
J^+(e):=\{f\in E\mid e\preceq f\},\quad
J^-(e):=\{f\in E\mid f\preceq e\}.
$$

集合族 $\{J^+(e)\cap J^-(f)\mid e\preceq f\}$ 生成的拓扑称为 Alexandrov 拓扑,将因果集视作拓扑空间。

### 观察者、局部视界与预测模型

定义观察者集合 $\mathcal O=\{O_1,\dots,O_N\}$。对每个观察者 $O_i$:

1. 存在可见事件子集 $E_i\subset E$,称为其因果视界;
2. 在 $E_i$ 上给出局部偏序 $\preceq_i\subset E_i\times E_i$,满足偏序公理;
3. 给出关于全局因果网的预测模型。

预测模型有两种等价表示:

* 概率表示:在候选因果网空间 $\mathsf{Cau}$ 上给出概率测度

$$
\mu_i\colon\mathsf{Cau}\to[0,1],\quad
\sum_{\mathcal C\in\mathsf{Cau}}\mu_i(\mathcal C)=1,
$$

  其中 $\mathcal C=(E,\preceq^{(\mathcal C)})$ 为候选因果结构;
* 参数表示:存在统计模型 $p_\theta$ 与参数流形 $\Theta$,观察者模型由参数点 $\theta_i\in\Theta$ 指定。

通过映射 $\theta_i\mapsto \mu_i$ 可以在两种表示之间转换。统计模型 $(\Theta,p_\theta)$ 配备 Fisher–Rao 度量,使 $\Theta$ 成为统计流形。([bsi-ni.brain.riken.jp][4])

**定义 1(观察者状态)**
观察者 $O_i$ 在某一"共识步骤参数" $\tau$ 下的状态定义为四元组

$$
X_i(\tau):=(E_i,\preceq_i,\theta_i(\tau),\omega_i(\tau)),
$$

其中 $\theta_i(\tau)\in\Theta$ 为其统计模型参数,$\omega_i(\tau)$ 为其在边界代数上的状态(将在下文给出)。

多观察者状态族 $\{X_i(\tau)\}$ 构成对宇宙因果网的多重局部描写。

### 统一时间刻度与母刻度函数

在统一时间刻度与边界时间几何框架中,总散射半相位 $\varphi(\omega)$、相对态密度 $\rho_{\mathrm{rel}}(\omega)$ 与 Wigner–Smith 延迟算子 $Q(\omega)=-\mathrm i S^\dagger(\omega)\partial_\omega S(\omega)$ 的迹,被统一为母刻度密度函数

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

其中 $S(\omega)$ 为散射矩阵。该刻度同时编码散射延迟、态密度与群延迟,是边界时间几何的核心刻度对象,与近年的 Wigner 时间延迟和群延迟研究相容。([Optica Publishing Group][2])

不同观察者通过各自可及的散射实验与边界状态,可在某能量窗 $I\subset\mathbb R$ 上重建局部母刻度函数 $\kappa_i(\omega)$。理想情况下,存在常数 $a_i>0,b_i\in\mathbb R$,使得

$$
\kappa_i(\omega)=a_i\kappa(\omega)+b_i.
$$

为消除仿射自由度,需要在 $I$ 上对各 $\kappa_i$ 做重标定。

### 边界代数、模流与 Null–Modular 双覆盖

设边界可观测代数为 $C^\ast$ 或 von Neumann 代数 $\mathcal A_{\partial}$,其上态 $\omega_i$ 为正归一线性泛函。Tomita–Takesaki 理论保证存在一一对应的模群 $\{\sigma_t^{(\omega_i)}\}$,其生成元为模哈密顿 $K^{(i)}$,即

$$
\frac{\mathrm d}{\mathrm dt}\sigma_t^{(\omega_i)}(A)\big|_{t=0}
=\mathrm i[K^{(i)},A].
$$

Connes–Rovelli 热时间假说将模参数 $t$ 视作时间刻度,从而使时间成为状态–代数对的内禀对象。模哈密顿允许仿射变换 $K^{(i)}\mapsto aK^{(i)}+b\mathbf 1$ 而不改变物理解。

在小因果菱形及其 Null 边界上,广义熵 $S_{\mathrm{gen}}$ 的变化与模流方向共同刻画"时间箭头"。Null–Modular 双覆盖将小因果菱形的几何与模流共同提升到某个 $\mathbb Z_2$ 双覆盖空间,其扇区由上同调类 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$ 决定。不同观察者在各自覆盖区域 $U_i$ 内看到的扇区记为 $[K_i]$。

---

## Main Results (Theorems and Alignments)

在上述模型与假设下,本节给出本文的主要结果。首先构造冲突指标,其次定义共识几何空间与势能函数,最后陈述梯度流收敛到共识流形的定理。

### 冲突指标的构造

**定义 2(模型散度与共识速度)**
对两个观察者 $O_i,O_j$,令 $\mu_i,\mu_j$ 为其在 $\mathsf{Cau}$ 上的概率测度。定义 Kullback–Leibler 散度

$$
D_{\mathrm{KL}}(\mu_i\Vert\mu_j)
:=\sum_{\mathcal C\in\mathsf{Cau}}\mu_i(\mathcal C)
\log\frac{\mu_i(\mathcal C)}{\mu_j(\mathcal C)},
$$

以及 Jensen–Shannon 散度

$$
D_{\mathrm{JS}}(\mu_i,\mu_j)
:=\frac12 D_{\mathrm{KL}}(\mu_i\Vert\bar\mu)
+\frac12 D_{\mathrm{KL}}(\mu_j\Vert\bar\mu),
\quad
\bar\mu=\tfrac12(\mu_i+\mu_j).
$$

若观察者状态随参数 $\tau$ 演化,即 $\mu_i=\mu_i(\tau)$,定义共识速度为

$$
v_{ij}(\tau)
:=-\frac{\mathrm d}{\mathrm d\tau}
D_{\mathrm{JS}}\bigl(\mu_i(\tau),\mu_j(\tau)\bigr).
$$

**定义 3(破环代价)**
令 $R:=\bigcup_{i=1}^N\preceq_i$ 为局部偏序的合并关系,$\preceq_{\mathrm{glue}}$ 为其传递闭包。赋予每条有向边 $e\to f\in R$ 权重 $w(e\to f)\ge 0$。破环代价定义为

$$
V_{\mathrm{cycle}}
:=\min\left\{
\sum_{(e\to f)\in S} w(e\to f)
\ \Bigm|
S\subset R,
R\setminus S \text{ 的传递闭包为偏序}
\right\}.
$$

显然 $V_{\mathrm{cycle}}\ge 0$,且 $V_{\mathrm{cycle}}=0$ 当且仅当 $\preceq_{\mathrm{glue}}$ 本身为偏序。

**定义 4(重标定母刻度与刻度散度)**
在能量窗 $I\subset\mathbb R$ 上,选取权函数 $w(\omega)>0$ 可积。对观察者 $O_i$,选择 $a_i>0,b_i$ 使得

$$
\int_I\bigl(\kappa_i(\omega)-a_i\kappa_{\mathrm{ref}}(\omega)-b_i\bigr)^2 w(\omega)\,\mathrm d\omega
$$

最小,其中 $\kappa_{\mathrm{ref}}$ 为参考刻度。记重标定刻度

$$
\kappa_i^{\mathrm{ren}}(\omega)
:=a_i\kappa_i(\omega)+b_i,
$$

平均刻度为

$$
\bar\kappa(\omega)
:=\frac1N\sum_{i=1}^N\kappa_i^{\mathrm{ren}}(\omega).
$$

定义刻度散度

$$
\Delta_\kappa^2
:=\int_I
\left(
\frac1N\sum_{i=1}^N
\bigl(\kappa_i^{\mathrm{ren}}(\omega)-\bar\kappa(\omega)\bigr)^2
\right)
w(\omega)\,\mathrm d\omega.
$$

**定义 5(熵箭头失配率与模流差异)**
在重叠的 Null 生成元上,令 $\lambda$ 为仿射参数,$S_{\mathrm{gen}}^{(i)}(\lambda)$ 为观察者 $O_i$ 计算的广义熵。定义熵箭头失配率

$$
\Xi_{ij}
:=\frac{
\int_{\mathrm{overlap}}
\mathbf 1\Bigl(
\operatorname{sign}\partial_\lambda S_{\mathrm{gen}}^{(i)}
\neq
\operatorname{sign}\partial_\lambda S_{\mathrm{gen}}^{(j)}
\Bigr)\,\mathrm d\mu
}{
\int_{\mathrm{overlap}}\mathrm d\mu
},
$$

其中 $\mathrm d\mu$ 为自然测度,$\mathbf 1(\cdot)$ 为指示函数。

模哈密顿 $K^{(i)},K^{(j)}$ 在重叠区域上的差异定义为

$$
\Delta_{\mathrm{mod}}^{(ij)}
:=\inf_{a>0,b\in\mathbb R}
\bigl\|K^{(i)}-aK^{(j)}-b\mathbf 1\bigr\|,
$$

范数可取算子范数或 Hilbert–Schmidt 范数。

**定义 6(拓扑扇区冲突指标)**
设 $[K_i]\in H^2(Y,\partial Y;\mathbb Z_2)$ 为观察者 $O_i$ 的 Null–Modular 双覆盖扇区。定义拓扑扇区数

$$
\Delta_{\mathrm{topo}}
:=\#\{[K_i]\mid i=1,\dots,N\},
$$

以及两两指示函数

$$
\delta_{\mathrm{topo}}^{(ij)}
:=\begin{cases}
0,& [K_i]=[K_j],\\[2pt]
1,& [K_i]\neq[K_j].
\end{cases}
$$

当 $\Delta_{\mathrm{topo}}=1$ 时,所有观察者处于同一 $\mathbb Z_2$ 扇区。

### 共识几何空间与势能函数

统计模型族 $\{p_\theta\mid\theta\in\Theta\}$ 在 Fisher–Rao 度量

$$
g^{\mathrm{FR}}_{ab}(\theta)
:=\mathbb E_\theta\bigl[
\partial_a\log p_\theta(X)\,\partial_b\log p_\theta(X)
\bigr]
$$

下构成 Riemann 统计流形 $(\Theta,g^{\mathrm{FR}})$。([bsi-ni.brain.riken.jp][4])

假设存在因果集模空间 $(\mathcal C,d_{\mathrm C})$,其上定义与度量相容的 Riemann 结构 $g^{\mathrm C}$;母刻度函数空间为 Hilbert 空间

$$
\mathcal H_\kappa=L^2(I,w(\omega)\,\mathrm d\omega),
$$

配备标准内积与度量 $g^\kappa$;边界状态空间在有限维情形下可取为密度矩阵集合 $\mathcal S$,配备 Bures 度量 $d_{\mathrm{Bures}}$ 与相应 Riemann 结构 $g^{\mathrm{Bures}}$。([维基百科][7])

**定义 7(共识几何空间及总度量)**
对 $N$ 个观察者,定义

$$
\mathcal M
:=\Theta^N\times\mathcal C\times\mathcal H_\kappa^N\times\mathcal S^N,
$$

其中一般元记作

$$
X=(\theta_1,\dots,\theta_N;\ \mathcal C;\ \kappa_1,\dots,\kappa_N;\ \rho_1,\dots,\rho_N).
$$

在 $\mathcal M$ 上定义总度量

$$
G
:=\alpha\bigoplus_{i=1}^N g^{\mathrm{FR}}_{(i)}
+\beta\,g^{\mathrm C}
+\gamma\bigoplus_{i=1}^N g^\kappa_{(i)}
+\delta\bigoplus_{i=1}^N g^{\mathrm{Bures}}_{(i)},
$$

其中 $\alpha,\beta,\gamma,\delta>0$ 为权重参数。

**定义 8(共识势能函数)**
给定权重 $w_{ij}^{\mathrm{model}},w_{ij}^{\Xi},w_{ij}^{\mathrm{mod}}\ge 0$ 及 $\lambda_{\mathrm{poset}},\lambda_\kappa,\lambda_{\mathrm{topo}}>0$,定义

$$
F_{\mathrm{model}}
:=\sum_{1\le i<j\le N} w_{ij}^{\mathrm{model}}
D_{\mathrm{JS}}(\theta_i,\theta_j),
$$

$$
F_{\mathrm{poset}}
:=\lambda_{\mathrm{poset}} V_{\mathrm{cycle}}(\mathcal C;\{\preceq_i\}),
\quad
F_{\kappa}
:=\lambda_\kappa\Delta_\kappa^2(\{\kappa_i\}),
$$

$$
F_{\mathrm{mod}}
:=\sum_{1\le i<j\le N}
\bigl(
w_{ij}^{\Xi}\,\Xi_{ij}
+w_{ij}^{\mathrm{mod}}\,\Delta_{\mathrm{mod}}^{(ij)}
\bigr),
\quad
F_{\mathrm{topo}}
:=\lambda_{\mathrm{topo}}\bigl(\Delta_{\mathrm{topo}}-1\bigr)^2.
$$

总势能定义为

$$
F:=F_{\mathrm{model}}
+F_{\mathrm{poset}}
+F_{\kappa}
+F_{\mathrm{mod}}
+F_{\mathrm{topo}}.
$$

**定义 9(共识流形)**
共识流形定义为

$$
\mathcal M_{\mathrm{cons}}
:=\{X\in\mathcal M\mid F(X)=0\}.
$$

由构造,$F\ge 0$,当且仅当 $F_{\mathrm{model}}=F_{\mathrm{poset}}=F_\kappa=F_{\mathrm{mod}}=F_{\mathrm{topo}}=0$ 时 $F=0$。该极值条件对应"完全共识"状态,其几何与物理意义将在后文与附录中分析。

### 共识梯度流与收敛性定理

在 $(\mathcal M,G)$ 上考虑势能 $F$ 的梯度流。

**定义 10(共识梯度流)**
给定初始状态 $X(0)\in\mathcal M$,共识梯度流定义为

$$
\frac{\mathrm d}{\mathrm d\tau}X(\tau)
=-\operatorname{grad}_G F\bigl(X(\tau)\bigr),\quad
X(0)\ \text{给定},
$$

其中 $\operatorname{grad}_G$ 为相对于度量 $G$ 的梯度。

**命题 1(势能单调性)**
沿共识梯度流,有

$$
\frac{\mathrm d}{\mathrm d\tau}F\bigl(X(\tau)\bigr)
=-\bigl|\operatorname{grad}_G F\bigl(X(\tau)\bigr)\bigr|_G^2
\le 0.
$$

证明依赖于 Riemann 流形上梯度流的一般公式,在附录 A 中给出。其直接含义是:共识演化过程始终沿"最陡下降方向"降低总冲突势能。

为了讨论收敛性,引入以下假设。

**假设 1(完备性与强凸性)**

1. $(\mathcal M,G)$ 为完备 Riemann 流形;
2. 势能 $F\colon\mathcal M\to[0,\infty)$ 为 $C^2$ 函数且下有界;
3. 存在常数 $m>0$,使得在包含梯度流轨道的某个测地凸子集上,对任意切向量 $v\in T_X\mathcal M$,有

$$
\operatorname{Hess}_G F(X)[v,v]
   \ge m\,G_X(v,v),
$$

   即 $F$ 在该子集上为 $m$-强凸;
4. 共识流形 $\mathcal M_{\mathrm{cons}}$ 非空且为闭的测地凸子集。

在此假设下,可以得到如下主结果。

**定理 1(共识梯度流的指数收敛)**
在假设 1 成立时,对任意初始值 $X(0)\in\mathcal M$,共识梯度流存在唯一全局解 $X(\tau)$。沿该解:

1. 势能 $F\bigl(X(\tau)\bigr)$ 单调下降并收敛到极小值 $F_\ast\ge 0$;
2. 若 $F_\ast=0$,则存在唯一点 $X_\ast\in\mathcal M_{\mathrm{cons}}$ 使得

$$
\mathrm{dist}_G\bigl(X(\tau),X_\ast\bigr)
   \le C\mathrm e^{-m\tau},
$$

   其中常数 $C>0$ 仅依赖于初始条件与 $F$ 的局部几何。

该定理表明,在适当构造的几何与势能下,"多观察者解决冲突"的过程可以被理解为共识几何空间上的一条梯度流线,沿该流线所有冲突指标单调下降并指数收敛到共识流形上的一点。

**命题 2(破环代价与全局偏序的等价性)**
在局部一致性条件下(各 $\preceq_i$ 在重叠区域上的判断一致),以下命题等价:

1. $V_{\mathrm{cycle}}=0$;
2. $\preceq_{\mathrm{glue}}$ 为偏序;
3. 存在全局偏序 $\preceq$ 使得对所有 $i$,$\preceq|_{E_i}=\preceq_i$。

因此,破环代价的消失等价于存在兼容所有局部视角的全局因果结构。

命题 2 的证明见附录 B。

**命题 3(冲突指标同时为零的几何–物理意义)**
若在某状态 $X\in\mathcal M$ 上有

$$
F_{\mathrm{model}}=F_{\mathrm{poset}}=F_\kappa
=F_{\mathrm{mod}}=F_{\mathrm{topo}}=0,
$$

则存在:

1. 全局因果偏序 $(E,\preceq)$,同时容纳所有局部偏序;
2. 统一统计模型参数点 $\theta_\ast\in\Theta$,代表所有观察者的概率模型;
3. 统一母刻度函数 $\kappa_\ast(\omega)$,与各观察者重标定刻度一致;
4. 统一 Null–Modular 双覆盖扇区 $[K]$,所有观察者处于该扇区;
5. 在上述背景下兼容的边界状态族 $\{\rho_i\}$,其差异不再引入宏观因果与时间几何冲突。

命题 3 的详细论证见附录 C。

---

## Proofs

本节给出上述主要结果的证明结构与要点,将技术细节放入附录。

### 命题 1 的证明要点

在 Riemann 流形 $(\mathcal M,G)$ 上,梯度定义为

$$
G_X(\operatorname{grad}_G F(X),V)
=\mathrm dF_X(V),
\quad\forall V\in T_X\mathcal M.
$$

沿梯度流 $\dot X=-\operatorname{grad}_G F(X)$ 有

$$
\frac{\mathrm d}{\mathrm d\tau}F\bigl(X(\tau)\bigr)
=\mathrm dF_{X(\tau)}(\dot X(\tau))
=G_{X(\tau)}\bigl(\operatorname{grad}_G F(X(\tau)),-\operatorname{grad}_G F(X(\tau))\bigr)
=-|\operatorname{grad}_G F(X(\tau))|_G^2\le 0.
$$

因此 $F$ 沿流线非增,并在极限达到极小值。

### 定理 1 的证明结构

定理 1 属于完备 Riemann 流形上强凸函数梯度流的一般理论,可分为三步:

1. 在 Lipschitz 条件下,利用常微分方程理论与 Hopf–Rinow 定理,证明梯度流的全局存在与唯一性;
2. 利用强凸性条件与 Hessian 的下界,证明极小点存在且唯一;
3. 利用强凸性与梯度流方程,推导函数值与 Riemann 距离的指数收敛估计。

完整证明细节见附录 A。

### 命题 2 的证明结构

破环代价 $V_{\mathrm{cycle}}$ 的定义直接对应"最小删边使图无环"的组合问题。在局部一致性条件下,可以证明:

* 若 $V_{\mathrm{cycle}}=0$,则无需删边,传递闭包 $\preceq_{\mathrm{glue}}$ 即为偏序;
* 若存在全局偏序 $\preceq$ 兼容所有局部偏序,则 $\preceq$ 的图包含 $R$,其传递闭包必无环,从而 $V_{\mathrm{cycle}}=0$。

这给出破环代价与全局偏序存在性的等价性。详细论证见附录 B。

### 命题 3 的证明轮廓

将各冲突指标同时为零的条件分解:

1. $F_{\mathrm{model}}=0$ 推出所有 $\theta_i$ 表示的概率模型一致;
2. $F_{\mathrm{poset}}=0$ 推出存在全局偏序 $\preceq$;
3. $F_\kappa=0$ 推出重标定后所有刻度一致;
4. $F_{\mathrm{mod}}=0$ 推出在重叠区域上熵箭头与模流可通过仿射重标定对齐;
5. $F_{\mathrm{topo}}=0$ 推出存在唯一扇区 $[K]$。

将这些结论统一起来即可得到命题 3 中的几何–物理图景。细节见附录 C。

---

## Model Apply

本节通过两个简化模型展示共识几何框架的具体适用方式。

### 模型一:有限因果集与离散统计模型

考虑有限事件集合 $E_n=\{1,\dots,n\}$,候选因果网空间 $\mathsf{Cau}_n$ 为所有 $E_n$ 上偏序的集合。取 Dirichlet 族作为统计模型:

$$
\Theta=\Delta^{M-1},\quad
p_\theta(\mathcal C)=\theta_{k(\mathcal C)},\quad
\mathsf{Cau}_n=\{\mathcal C_1,\dots,\mathcal C_M\}.
$$

每个观察者 $O_i$ 通过局部观测给出一个 Dirichlet 参数 $\theta_i$,Fisher–Rao 度量在简单情形下与标准 Fisher 信息一致,$\Theta$ 成为带有 Fisher 度量的概率单纯形。

因果偏序部分:各观察者给出 $E_i\subseteq E_n$ 上的偏序 $\preceq_i$,其合并关系 $R$ 与破环代价 $V_{\mathrm{cycle}}$ 可以通过图算法显式计算。破环代价的梯度下降对应于在 $R$ 上重新赋权或修正局部偏序,从而消除有向环。

时间刻度与边界状态在该有限模型中可采用简单标量与有限维密度矩阵近似,从而使 $\mathcal H_\kappa$ 与 $\mathcal S$ 降维为有限维 Euclid 空间。此时 $(\mathcal M,G)$ 接近于带约束的 Euclid 空间,梯度流可用常规最优化算法实现。

该模型适合用作数值实验:在给定的 $\mathsf{Cau}_n$ 与初始 $\theta_i,\preceq_i,\kappa_i,\rho_i$ 下,可以直接积分梯度流,观察势能 $F$ 与各分量的单调下降,验证定理 1 的收敛预测。

### 模型二:Riemann 共识与边界散射网络

考虑一个由 $N$ 个节点组成的边界散射网络,每个节点对应一个局部观察者,持有局部散射矩阵 $S_i(\omega)$ 与重建的刻度函数 $\kappa_i(\omega)$,同时通过网络结构交换邻居散射数据。

为了简化,取 $\kappa_i$ 属于有限维函数子空间,例如由正交基 $\{\phi_k(\omega)\}_{k=1}^K$ 张成的子空间,将

$$
\kappa_i(\omega)=\sum_{k=1}^K c_{ik}\phi_k(\omega)
$$

视作向量 $c_i\in\mathbb R^K$,并在 $\mathbb R^K$ 上采用标准内积。此时 $\mathcal H_\kappa^N$ 简化为 $KN$ 维 Euclid 空间,$F_\kappa$ 成为关于 $\{c_i\}$ 的二次函数,其梯度流即为线性共识算法。

在统计模型部分,可以选取高斯过程或指数族模型,使参数空间 $\Theta$ 具备自然 Riemann 结构,结合 Tron 等关于 Riemann 共识的结果,可以将 $F_{\mathrm{model}}$ 的下降视作 Riemann 流形上的共识演化,为多节点散射网络提供几何一致性算法。([arXiv][6])

边界状态 $\rho_i$ 的演化则在 Bures 度量下进行,其最陡下降方向对应于量子 Fisher 信息导向的"最优变形",与量子参数估计和几何量子控制存在联系。([维基百科][7])

---

## Engineering Proposals

从工程角度,本文的几何框架可以为多观察者物理系统与多智能体学习系统提供一致性协议的设计原则。

### 多探测器引力波/FRB 阵列中的共识几何

考虑一组空间上分布的探测器阵列,用于测量引力波或快速射电暴(FRB)的相位与到达时间。每个探测器 $O_i$:

* 在局部重建一个时间刻度 $\kappa_i(\omega)$,对应其仪器响应与传播延迟;
* 在候选事件空间上建立统计模型 $p_{\theta_i}$,描述源位置与传播介质的先验与后验;
* 在有效"边界代数"上给出数据压缩后的密度矩阵 $\rho_i$,例如使用高斯态近似。

基于本文的共识几何空间,可以:

1. 设计分布式梯度流算法,在网络通信拓扑约束下,使 $\{\theta_i,\kappa_i,\rho_i\}$ 逐步趋向共识,从而在无中心控制的情况下重建统一的源参数与时间刻度;
2. 将破环代价 $V_{\mathrm{cycle}}$ 与拓扑指标 $\Delta_{\mathrm{topo}}$ 作为质量控制指标,检测某些探测器的系统性偏差或拓扑误标;
3. 利用 Bures 度量优化多探测器数据融合中的量子/高斯态加权方案,使整体信息增益最大。

### 多智能体强化学习中的因果共识

多智能体强化学习系统中,智能体在共享环境中探索并更新各自的因果模型(如策略因果图、环境动力学模型)。本文框架提供以下工程思路:

1. 将每个智能体的因果模型参数嵌入统计流形 $\Theta$,使用 Fisher–Rao 度量指导模型更新;
2. 使用破环代价 $V_{\mathrm{cycle}}$ 作为多智能体因果图合并时的约束,避免因不同视角导致的因果循环;
3. 利用刻度散度 $\Delta_\kappa$ 与 Bures 距离 $d_{\mathrm{Bures}}$ 定义"时间一致性"与"状态一致性"的正则项,在训练目标中显式惩罚多智能体之间在时间刻度和状态估计上的偏差;
4. 通过共识势能 $F$ 的梯度流,实现一种"几何一致性–性能优化"联合算法。

### 实验方案与数值验证

对于数值验证,可以从以下层级逐步推进:

1. 纯信息几何层级:在简单指数族与有限因果集模型下实现共识梯度流,验证模型散度与破环代价的单调下降;
2. Riemann 共识层级:在正曲率或非正曲率流形上模拟多智能体参数共识,比较本文势能构造与现有 Riemann 共识算法的差异;([arXiv][6])
3. 量子态与 Bures 几何层级:在有限维密度矩阵空间上实现 Bures 度量下的共识流线,分析其与量子 Fisher 信息与最优估计的关系。([维基百科][7])

---

## Discussion (risks, boundaries, past work)

### 几何与势能构造的限制

本文的几何化框架依赖于若干关键假设:

1. 统计流形 $(\Theta,g^{\mathrm{FR}})$ 的光滑性与完整性,这在有限维正则模型中成立,但在非正则或无限维模型中需要额外条件;
2. 因果集模空间 $(\mathcal C,d_{\mathrm C})$ 的度量结构较为抽象,实际构造具有良好几何性质的 $d_{\mathrm C}$ 仍是一个开放问题;
3. Bures 度量在无限维情形下的技术复杂性,以及与具体物理实现之间的对应关系。

此外,势能函数 $F$ 的强凸性假设在全域上通常很难满足,Riemann 共识文献表明,在非线性流形上,梯度共识流可能出现极值多重性与病态行为,需要局部曲率与拓扑的约束。([arXiv][6])

### 与因果集与边界时间几何工作的关系

因果集理论强调"次序+计数=几何",本文接续这一思路,将"多观察者共识"看作在因果集模空间上的几何收缩。([www2.perimeterinstitute.ca][1]) 与之不同的是,本文引入了统一时间刻度与边界时间几何,将时间刻度与模流、广义熵与 Null–Modular 双覆盖统一进同一结构,使因果、时间与拓扑在共识过程中同时对齐。

在边界引力与全息方向,最近关于 Gibbons–Hawking–York 边界项、广义边界项和全息边界条件的工作,为"边界作为统一舞台"的观点提供了更丰富的技术背景。([APS Link][3]) 本文框架为这些边界结构增加了一个"多观察者共识"的维度。

### 风险与开放问题

1. **非凸性与极小值多重性**:在复杂物理系统中,总势能 $F$ 很可能具有多个局部极小值,对应不同的"共识相"。如何刻画这些相之间的跃迁与稳定性,是一个自然问题。
2. **拓扑扇区的动力学**:$\Delta_{\mathrm{topo}}$ 的变化往往涉及拓扑变换,其在连续动力学中的实现需要谨慎处理,可能引入不可逆或瞬时跃迁。
3. **与经验的对接**:本文主要构造了一个几何–公理化框架,如何将其与实在世界中的实验与观测(如多探测器天体物理观测、多智能体系统日志)对接,仍需进一步探索。

---

## Conclusion

本文在"无时间的因果网"与"边界时间几何"的统一框架中,为多观察者之间的冲突与共识构建了一个几何化理论。通过:

* 将观察者的统计模型、局部因果偏序、母刻度函数与边界状态嵌入统一的共识几何空间 $(\mathcal M,G)$;
* 定义模型散度、破环代价、刻度散度、熵箭头与模流差异、拓扑扇区错配等冲突指标,并将其编码为总势能函数 $F$;
* 证明在完备性与强凸性假设下,共识梯度流 $\dot X=-\operatorname{grad}_G F(X)$ 指向共识流形 $\mathcal M_{\mathrm{cons}}$,并使势能指数收敛;

本文给出一种将"观察者解决冲突、达成共识"理解为几何收缩过程的统一方式。在共识流形上,全球因果网、统一母刻度、熵箭头与模流结构以及 Null–Modular 双覆盖扇区彼此兼容,形成多观察者共享的边界时间几何。

未来工作将包括:在具体物理与工程系统中实现该几何框架,分析非凸性与多共识相的结构,以及将拓扑扇区的动力学纳入更完整的因果–时间–拓扑统一理论中。

---

## Acknowledgements, Code Availability

本工作未使用公开代码实现具体数值实验,相关数值实现方案在"Engineering Proposals"部分给出概念性描述。若在后续工作中实现完整代码,将在公开仓库中给出链接与说明。

---

## References

[1] S.-I. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS–Oxford, 2000. ([vielbein.it][8])

[2] M. Suzuki, "Information Geometry and Statistical Manifold," arXiv:1410.3369, 2014. ([ResearchGate][9])

[3] D. Bures, "An extension of Kakutani's theorem on infinite product measures to the tensor product of semifinite *-algebras," *Trans. Amer. Math. Soc.*, 1969. ([维基百科][7])

[4] C. W. Helstrom, "Minimum mean-squared error of estimates in quantum statistics," *Phys. Lett. A*, 1967. ([维基百科][7])

[5] D. Spehner, "Bures geodesics and quantum metrology," *Quantum* 7, 1715 (2023). ([Quantum][10])

[6] R. Tron, A. A. Sarlette, R. Sepulchre, "Riemannian Consensus for Manifolds with Bounded Curvature," *CDC 2011* / arXiv:1202.0030. ([arXiv][6])

[7] J. Markdahl, S. E. Tuna, J. M. Hendrickx, "Pathologies of consensus seeking gradient descent flows on manifolds," *Automatica* 132, 2021. ([科学直通车][11])

[8] L. Mi, J. Gonçalves, M. Dahl, "Riemannian polarization of multi-agent gradient flows," 2023. ([repository.cam.ac.uk][12])

[9] S. Chen, X. Liu, "Consensus on complete Riemannian manifolds in finite time," *J. Math. Anal. Appl.*, 2013. ([科学直通车][13])

[10] R. D. Sorkin, "Spacetime and Causal Sets," in *Relativity and Gravitation: Classical and Quantum*, World Scientific, 1991. ([www2.perimeterinstitute.ca][1])

[11] B. F. Dribus, "On the Axioms of Causal Set Theory," arXiv:1311.2148, 2013. ([arXiv][14])

[12] S. Baron, "Causal Set Theory is (Strongly) Causal," *Found. Phys.*, 2025. ([SpringerLink][15])

[13] R. Bourgain, D. Faccio, "Direct measurement of the Wigner time delay for light," *Opt. Lett.* 38, 1963 (2013). ([Optica Publishing Group][2])

[14] B. Fetić, A. et al., "Wigner time delay revisited," *Ann. Phys.* 460, 2024. ([科学直通车][16])

[15] G. W. Gibbons, S. W. Hawking, "Action integrals and partition functions in quantum gravity," *Phys. Rev. D* 15, 2752 (1977). ([APS Link][3])

[16] J. W. York, "Role of conformal three-geometry in the dynamics of gravitation," *Phys. Rev. Lett.* 28, 1082 (1972); "Quasilocal energy in general relativity," 1992. ([APS Link][3])

[17] K. Bhattacharya, "Boundary terms and Brown–York quasi-local parameters in GR and ST gravity," 2023. ([arXiv][17])

[18] A. Parvizi et al., "Freelance holography, part I: Setting boundary conditions in holography," *SciPost Phys.* 19, 043 (2025). ([SciPost][18])

[19] A. Teimouri, S. Talaganis, J. Edholm, A. Mazumdar, "Generalised boundary terms for higher derivative theories of gravity," *JHEP* 08, 144 (2016). ([SpringerLink][19])

[20] K. Sun, G. Lebanon, S. Sra, "An Information Geometry of Statistical Manifold Learning," *AISTATS 2014*. ([Proceedings of Machine Learning Research][20])

---

## Appendix A: 梯度流收敛性的技术证明

设 $(\mathcal N,h)$ 为完备 Riemann 流形,$f\colon\mathcal N\to\mathbb R$ 为 $C^2$ 函数。梯度流定义为

$$
\frac{\mathrm d}{\mathrm d\tau}x(\tau)
=-\operatorname{grad}_h f\bigl(x(\tau)\bigr).
$$

### A.1 极小点唯一性

假设存在 $m>0$ 使得对所有 $x\in\mathcal N$ 和 $v\in T_x\mathcal N$,有

$$
\operatorname{Hess}_h f(x)[v,v]\ge m\,h_x(v,v),
$$

即 $f$ 为 $m$-强凸。若 $x_\ast,y_\ast$ 为两个极小点,则 $\operatorname{grad}_h f(x_\ast)=\operatorname{grad}_h f(y_\ast)=0$,且 $f(x_\ast)=f(y_\ast)$。取连接 $x_\ast,y_\ast$ 的测地线 $\gamma:[0,1]\to\mathcal N$,考虑 $g(s):=f(\gamma(s))$。则

$$
g''(s)
=\operatorname{Hess}_h f\bigl(\dot\gamma(s),\dot\gamma(s)\bigr)
\ge m\,h(\dot\gamma(s),\dot\gamma(s))\ge 0.
$$

因此 $g$ 为强凸函数,除非 $x_\ast=y_\ast$,不可能在区间两端同时取得最小值,故极小点唯一。

### A.2 梯度流解的存在唯一性

若 $\operatorname{grad}_h f$ 在有界集上 Lipschitz,则通过 Riemann 流形上的常微分方程理论,可以在任意初值附近构造局部解。完备性与梯度有界性保证解不会在有限时间内逃逸到无穷远,从而解可延拓到全 $\tau\ge 0$。

### A.3 指数收敛估计

设 $x(\tau)$ 为梯度流解,$x_\ast$ 为唯一极小点。定义

$$
\Phi(\tau):=f(x(\tau))-f(x_\ast)\ge 0.
$$

强凸性与 Taylor 展开给出

$$
f(y)\ge f(x)
+\langle\operatorname{grad}_h f(x),\exp_x^{-1}y\rangle_h
+\frac m2|\exp_x^{-1}y|_h^2.
$$

取 $x=x(\tau),y=x_\ast$,注意 $\operatorname{grad}_h f(x_\ast)=0$,可得

$$
\Phi(\tau)
\le -\langle\operatorname{grad}_h f(x(\tau)),\exp_{x(\tau)}^{-1}x_\ast\rangle_h
-\frac m2|\exp_{x(\tau)}^{-1}x_\ast|_h^2.
$$

另一方面

$$
\frac{\mathrm d}{\mathrm d\tau}\Phi(\tau)
=\langle\operatorname{grad}_h f(x(\tau)),\dot x(\tau)\rangle_h
=-|\operatorname{grad}_h f(x(\tau))|_h^2.
$$

综合上述估计,可以得到

$$
\frac{\mathrm d}{\mathrm d\tau}\Phi(\tau)
\le -2m\Phi(\tau),
$$

从而

$$
\Phi(\tau)\le\mathrm e^{-2m\tau}\Phi(0).
$$

进一步利用强凸性,可以将 $\Phi(\tau)$ 与 Riemann 距离 $\mathrm{dist}_h(x(\tau),x_\ast)$ 关联,得到

$$
\mathrm{dist}_h(x(\tau),x_\ast)\le C\mathrm e^{-m\tau},
$$

其中 $C$ 仅依赖初始条件与 $f$ 的局部几何。这完成了定理 1 的证明框架。

---

## Appendix B: 破环代价与全局偏序的存在性

给定事件集合 $E$ 与局部偏序族 $\{\preceq_i\}_{i=1}^N$,合并关系

$$
R=\bigcup_{i=1}^N\preceq_i
$$

的传递闭包记作 $\preceq_{\mathrm{glue}}$。假设对所有 $i,j$,在重叠区域 $E_i\cap E_j$ 上的偏序判断一致,即

$$
x\preceq_i y\iff x\preceq_j y,\quad
\forall x,y\in E_i\cap E_j.
$$

### B.1 破环代价为零与传递闭包为偏序的等价性

由破环代价定义:

$$
V_{\mathrm{cycle}}
=\min\left\{\sum_{(e\to f)\in S}w(e\to f)\mid
S\subset R,\ R\setminus S \text{ 的传递闭包为偏序}\right\}.
$$

显然,若存在有向环,则必须删去至少一条边,故 $V_{\mathrm{cycle}}>0$;反之,若 $\preceq_{\mathrm{glue}}$ 已为偏序,则无需删边,取 $S=\varnothing$ 即可,故 $V_{\mathrm{cycle}}=0$。于是

$$
V_{\mathrm{cycle}}=0
\iff \preceq_{\mathrm{glue}}\ \text{为偏序}.
$$

### B.2 传递闭包为偏序与全局偏序存在性的等价性

定义全局关系 $\preceq:=\preceq_{\mathrm{glue}}$。显然 $\preceq$ 的限制 $\preceq|_{E_i}$ 包含 $\preceq_i$。由于重叠区域内局部偏序一致,任何由其他 $\preceq_j$ 在 $E_i$ 内推导出的关系必与 $\preceq_i$ 兼容,从而 $\preceq|_{E_i}=\preceq_i$。因此,若 $\preceq_{\mathrm{glue}}$ 为偏序,则它是实现所有局部偏序的全局偏序。

反之,若存在全局偏序 $\widehat{\preceq}$ 满足 $\widehat{\preceq}|_{E_i}=\preceq_i$,则 $\widehat{\preceq}$ 的图包含 $R$,其传递闭包为自身,因 $\widehat{\preceq}$ 为偏序,无环,从而 $V_{\mathrm{cycle}}=0$。

综上,命题 2 得证。

---

## Appendix C: 冲突指标同时为零的几何与物理意义

假设在某状态 $X\in\mathcal M$ 上,各冲突指标同时为零:

$$
F_{\mathrm{model}}=F_{\mathrm{poset}}=F_\kappa
=F_{\mathrm{mod}}=F_{\mathrm{topo}}=0.
$$

### C.1 统计模型的一致性

$F_{\mathrm{model}}=0$ 意味着对所有 $i,j$,有 $D_{\mathrm{JS}}(\theta_i,\theta_j)=0$。Jensen–Shannon 散度为零当且仅当两分布几乎处处相同,从而所有 $p_{\theta_i}$ 一致。在参数空间 $\Theta$ 上,这意味着存在唯一参数点 $\theta_\ast$ 使得 $\theta_i=\theta_\ast$ 对所有 $i$ 成立。

### C.2 全局因果偏序的存在

$F_{\mathrm{poset}}=0$ 即 $V_{\mathrm{cycle}}=0$,在局部一致性假设下由附录 B 可知存在全局偏序 $\preceq$ 将所有局部偏序 $\preceq_i$ 嵌入其中。因此,存在全局因果网 $(E,\preceq)$,各观察者视界 $E_i$ 的偏序结构为其限制。

### C.3 统一母刻度与时间刻度共识

$F_\kappa=0$ 意味着刻度散度 $\Delta_\kappa=0$,即对所有 $\omega\in I$,有

$$
\kappa_i^{\mathrm{ren}}(\omega)=\bar\kappa(\omega).
$$

因此存在统一母刻度函数 $\kappa_\ast(\omega):=\bar\kappa(\omega)$,使得每个观察者的局部刻度在适当仿射重标定后与之吻合。在统一时间刻度框架下,这对应所有观察者在散射相位导数、相对态密度与群延迟三者之间采用了相同的刻度同一式。

### C.4 熵箭头与模流方向的一致性

$F_{\mathrm{mod}}=0$ 蕴含对所有 $i,j$,$\Xi_{ij}=0$ 且 $\Delta_{\mathrm{mod}}^{(ij)}=0$。前者意味着在重叠 Null 生成元上,$\partial_\lambda S_{\mathrm{gen}}^{(i)}$ 与 $\partial_\lambda S_{\mathrm{gen}}^{(j)}$ 的符号一致,故熵箭头方向一致;后者意味着存在 $a_{ij}>0,b_{ij}\in\mathbb R$ 使得 $K^{(i)}=a_{ij}K^{(j)}+b_{ij}\mathbf 1$。通过传递性,可以选择一组全局系数 $a_i>0,b_i\in\mathbb R$ 使得所有 $K^{(i)}$ 与某统一模哈密顿 $K_\ast$ 仿射等价。

因此,在共识状态下,所有观察者在模流与广义熵箭头上取得一致,时间箭头的定义成为全局性的边界时间几何结构。

### C.5 Null–Modular 双覆盖扇区的一致性

$F_{\mathrm{topo}}=0$ 给出 $\Delta_{\mathrm{topo}}=1$,即所有 $[K_i]$ 相同。因 $\mathbb Z_2$ 主丛在上同调中的分类,由此可知存在一个全局双覆盖扇区 $[K]$ 使得 $[K_i]=[K]|_{U_i}$。这意味着 Null–Modular 双覆盖的拓扑结构在所有观察者视界上兼容,共识流形上不存在扇区错配。

### C.6 总结

综合 C.1–C.5,可以给出如下图景:

* 存在统一的统计模型点 $\theta_\ast$,描述所有观察者对因果网的概率预测;
* 存在统一的全局因果偏序 $\preceq$,容纳所有局部偏序;
* 存在统一母刻度函数 $\kappa_\ast(\omega)$ 与统一模哈密顿 $K_\ast$,在适当前因子与零点选择后,所有观察者的时间刻度与模流与之对齐;
* 存在统一 Null–Modular 双覆盖扇区 $[K]$;

从而,多观察者系统处于一个在因果、时间、熵与拓扑各层面完全一致的状态,这一状态在几何上对应共识流形 $\mathcal M_{\mathrm{cons}}$ 上的点或轨道,是"观察者共识的几何化"在本框架中的极限形式。

[1]: https://www2.perimeterinstitute.ca/personal/rsorkin/some.papers/66.cocoyoc.pdf?utm_source=chatgpt.com
[2]: https://opg.optica.org/ol/abstract.cfm?uri=ol-38-11-1963&utm_source=chatgpt.com
[3]: https://link.aps.org/doi/10.1103/PhysRevD.52.2001?utm_source=chatgpt.com
[4]: https://bsi-ni.brain.riken.jp/database/file/166/169.pdf?utm_source=chatgpt.com
[5]: https://www.semanticscholar.org/paper/The-Metric-of-Bures-and-the-Geometric-Phase.-Uhlmann/2b42ef8ee44b3f0cfa0cae5a56d8a04ae142ab85?utm_source=chatgpt.com
[6]: https://arxiv.org/pdf/1202.0030?utm_source=chatgpt.com
[7]: https://en.wikipedia.org/wiki/Bures_metric?utm_source=chatgpt.com
[8]: https://vielbein.it/pdf/Traduzioni/2000-Amer-Methods_of_Information_Geometry.pdf?utm_source=chatgpt.com
[9]: https://www.researchgate.net/publication/266856209_Information_Geometry_and_Statistical_Manifold?utm_source=chatgpt.com
[10]: https://quantum-journal.org/papers/q-2025-04-18-1715/?utm_source=chatgpt.com
[11]: https://www.sciencedirect.com/science/article/abs/pii/S0005109821004714?utm_source=chatgpt.com
[12]: https://www.repository.cam.ac.uk/bitstreams/e60713ca-ec69-4cc7-b61e-f60b1043e671/download?utm_source=chatgpt.com
[13]: https://www.sciencedirect.com/science/article/pii/S0022247X12009225?utm_source=chatgpt.com
[14]: https://arxiv.org/abs/1311.2148?utm_source=chatgpt.com
[15]: https://link.springer.com/article/10.1007/s10701-025-00875-w?utm_source=chatgpt.com
[16]: https://www.sciencedirect.com/science/article/abs/pii/S0003491624000745?utm_source=chatgpt.com
[17]: https://arxiv.org/pdf/2307.06674?utm_source=chatgpt.com
[18]: https://scipost.org/SciPostPhys.19.2.043/pdf?utm_source=chatgpt.com
[19]: https://link.springer.com/article/10.1007/JHEP08%282016%29144?utm_source=chatgpt.com
[20]: https://proceedings.mlr.press/v32/suna14.pdf?utm_source=chatgpt.com
