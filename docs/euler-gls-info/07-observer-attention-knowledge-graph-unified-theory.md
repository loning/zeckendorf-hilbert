# 计算宇宙中的观察者–注意力–知识图谱统一理论

有限资源下的认知动力学与离散几何结构

---

## 摘要

在此前关于"计算宇宙" $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 的系列工作中,我们分别构造了离散复杂性几何、离散信息几何、统一时间刻度诱导的控制流形 $(\mathcal M,G)$ 以及任务信息流形 $(\mathcal S_Q,g_Q)$,并在联合流形 $\mathcal E_Q = \mathcal M \times \mathcal S_Q$ 上给出了时间–信息–复杂性的联合变分原理。上述结构在本体层面刻画了"计算宇宙自身的几何",但尚未显式引入"内部观察者"的数学对象:有限资源的观察者如何在复杂性–信息几何上选择注意力、构建知识图谱并逐步积累信息?

本文在计算宇宙与其连续几何极限的框架内,对"观察者–注意力–知识图谱"给出统一的公理化与几何化描述。我们首先将观察者形式化为一类带有限记忆的状态机

$$
O = (M_{\mathrm{int}},\Sigma_{\mathrm{obs}},\Sigma_{\mathrm{act}},\mathcal P,\mathcal U),
$$

其中 $M_{\mathrm{int}}$ 为内部记忆状态空间,$\Sigma_{\mathrm{obs}}$ 为观测符号空间,$\Sigma_{\mathrm{act}}$ 为动作空间,$\mathcal P$ 为注意力–观测策略,$\mathcal U$ 为内部更新算子。基于该结构我们定义时间依赖的注意力算子

$$
A_t : X \to [0,1],
$$

或者等价的可见子集 $X_t^{\mathrm{att}} \subset X$,并证明:注意力算子在计算宇宙的复杂性–信息几何上定义了一族时间依赖的"可达截面",从而对观察者的世界线施加约束。

其次,我们将知识图谱形式化为

$$
\mathcal G_t = (V_t,E_t,w_t,\Phi_t),
$$

其中 $V_t$ 为有限节点集合,$E_t \subset V_t\times V_t$ 为关系边,$w_t$ 为权重,$\Phi_t:V_t\to\mathcal S_Q$ 为嵌入到任务信息流形的映射。我们构造知识图谱 Laplace 算子 $\Delta_t$ 并证明,在合适的极限下,$\Delta_t$ 的谱逼近 $(\mathcal S_Q,g_Q)$ 上的 Laplace–Beltrami 算子,从而将有限节点知识图谱视为信息流形上的"离散骨架"。

然后,我们引入观察者在联合流形上的扩展世界线

$$
\widehat z(t) = (\theta(t),\phi(t),m(t),\mathcal G_t,A_t),
$$

其中 $(\theta(t),\phi(t))\in\mathcal E_Q$ 为控制–信息状态,$m(t)\in M_{\mathrm{int}}$ 为内部记忆,$\mathcal G_t$ 与 $A_t$ 为时刻 $t$ 的知识图谱与注意力。我们在时间–信息–复杂性联合作用量的基础上加入观察者内部代价与知识图谱重构代价,得到一个扩展的观测–计算作用量,并推导其 Euler–Lagrange 类型条件,给出"在有限复杂性预算与有限记忆下,观察者如何选择注意力与更新知识图谱"的变分刻画。

最后,我们证明了两个代表性结果:

1. 在局部 Lipschitz 与有限容量假设下,观察者可积累的信息熵增量在任意有限时间内受到复杂性预算与注意力带宽的双重上界,这给出一类"观察者版时间–信息不等式";
2. 知识图谱的谱维数在长时间极限下趋向任务信息流形的局部信息维数,从而表明"理性观察者的知识图谱在无限时间极限下几乎必然逼近真实信息几何的骨架"。

本文为后续构造"多观察者–共识几何–因果网"的理论奠定了单观察者层面的结构基础,并将观察者视为计算宇宙内部的几何对象,而非外在的"测量者"。

---

## 1 引言

在计算宇宙的公理框架中,宇宙被抽象为一个离散动力系统 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$,其中 $X$ 为配置空间,$\mathsf T$ 为一步转移关系,$\mathsf C$ 为单步代价,$\mathsf I$ 为信息质量。此前的工作已经在该框架下构建了:

* 离散复杂性几何:以复杂性距离 $d_{\mathrm{comp}}$、复杂性体积与离散 Ricci 曲率刻画问题难度与视界;
* 离散信息几何与任务信息流形 $(\mathcal S_Q,g_Q,\Phi_Q)$:通过观察算子族与相对熵结构,将任务相关的可见状态嵌入信息流形;
* 统一时间刻度诱导的控制流形 $(\mathcal M,G)$:通过散射母尺 $\kappa(\omega)$ 与群延迟矩阵 $Q(\omega;\theta)$ 构造复杂性度量;
* 联合流形 $\mathcal E_Q = \mathcal M \times \mathcal S_Q$ 上的时间–信息–复杂性联合变分原理:将"最优算法"几何化为极小世界线。

这些结构本质上是在描述"宇宙如何演化"与"信息在宇宙中如何存储与传播",但尚未显式描述"宇宙内部的观察者如何在这些结构上行动"。

观察者具有以下特点:

1. 有限注意力:在任一时刻,他只能访问 $X$ 的一小部分,或对信息流形 $\mathcal S_Q$ 的局部区域进行解析;
2. 有限记忆:其内部状态 $m(t)$ 的容量有限,只能存储有限维摘要;
3. 知识图谱:其长期积累的认知结构可以视为一个有限节点的图嵌入 $\mathcal S_Q$,是对信息流形的压缩性近似;
4. 资源约束:其能执行的计算步数与信息获取量受复杂性预算与时间预算限制。

因此,要在计算宇宙内刻画观察者,需要在已有几何结构上再叠加一层"认知几何":注意力如何选择子流形,知识图谱如何在信息流形上构建骨架,这些选择如何受复杂性几何与信息几何的约束,以及观察者如何在资源约束下优化其认知行为。

本文的目标可以概括为:

> 在统一时间刻度与复杂性–信息几何既定的前提下,对"单观察者"的注意力、知识图谱与认知动力学给出统一的公理化与变分几何描述。

后续多观察者与共识几何可以在此基础上通过对多个观察者对象的并置与相互作用来构造。

---

## 2 计算宇宙中的观察者对象

本节定义计算宇宙中的观察者对象,并给出其与计算宇宙之间的基本接口。

### 2.1 观察者的内部结构

**定义 2.1(观察者对象)**

在计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 中,一个观察者对象

$$
O = (M_{\mathrm{int}},\Sigma_{\mathrm{obs}},\Sigma_{\mathrm{act}},\mathcal P,\mathcal U)
$$

由以下部分组成:

1. 内部记忆状态空间 $M_{\mathrm{int}}$:可数或有限集合,表示观察者内部的认知状态;
2. 观测符号空间 $\Sigma_{\mathrm{obs}}$:有限集合,表示一次观测得到的符号(或符号向量);
3. 动作空间 $\Sigma_{\mathrm{act}}$:有限集合,表示观察者对宇宙施加的控制或查询动作;
4. 注意力–观测策略

$$
\mathcal P: M_{\mathrm{int}} \to \Delta(\Sigma_{\mathrm{act}}),
$$

表示在内部状态 $m \in M_{\mathrm{int}}$ 下,选择动作的分布;

5. 内部更新算子

$$
\mathcal U : M_{\mathrm{int}}\times\Sigma_{\mathrm{obs}} \to M_{\mathrm{int}},
$$

表示在当前内部状态与观测结果下,如何更新内部记忆。

为简化,我们假设在任一离散时间步 $k$:

1. 宇宙处于配置 $x_k \in X$,观察者内部状态为 $m_k \in M_{\mathrm{int}}$;
2. 观察者从 $\mathcal P(m_k)$ 中抽取动作 $a_k \in \Sigma_{\mathrm{act}}$;
3. 宇宙根据 $a_k$ 与 $x_k$ 生成观测符号 $o_k \in \Sigma_{\mathrm{obs}}$(其分布由宇宙–观察耦合机制决定);
4. 观察者更新内部状态 $m_{k+1} = \mathcal U(m_k,o_k)$。

宇宙的配置演化 $x_k \to x_{k+1}$ 则由 $\mathsf T$ 以及可能受 $a_k$ 影响的控制机制决定。

### 2.2 注意力算子

在离散层面,我们将观察者的"注意力"形式化为对配置空间 $X$ 的时间依赖权重函数。

**定义 2.2(离散注意力算子)**

在时间步 $k$,观察者的注意力算子是一个函数

$$
A_k : X \to [0,1],
$$

满足归一化条件

$$
\sum_{x\in X} A_k(x) = 1,
$$

或者更弱的约束条件(例如总质量不超过某个常数)。我们称

$$
X_k^{\mathrm{att}} = \{ x\in X : A_k(x) > 0 \}
$$

为时刻 $k$ 的可见配置子集。

直观上,$A_k(x)$ 表示观察者当前对配置 $x$ 的关注权重,通常集中在配置轨道附近或某个局域区域。

在连续极限中,我们更倾向于在任务信息流形上刻画注意力。

**定义 2.3(信息流形上的注意力密度)**

在任务 $Q$ 下,注意力可视为在信息流形 $\mathcal S_Q$ 上的概率密度 $\rho_t(\phi)$,满足

$$
\rho_t(\phi) \ge 0,
\quad
\int_{\mathcal S_Q} \rho_t(\phi)\,\mathrm d\mu_{g_Q}(\phi) = 1,
$$

其中 $\mathrm d\mu_{g_Q}$ 为 $g_Q$ 的体积元。

在 $\Phi_Q:X\to\mathcal S_Q$ 给出的嵌入下,离散 $A_k$ 与连续 $\rho_t$ 可通过推前与抽样对应。

---

## 3 知识图谱作为信息流形的离散骨架

本节形式化观察者的知识图谱,并将其嵌入任务信息流形,得到一个离散骨架与连续信息几何之间的桥梁。

### 3.1 知识图谱的定义

**定义 3.1(时刻 $t$ 的知识图谱)**

观察者在时刻 $t$ 的知识图谱是四元组

$$
\mathcal G_t = (V_t,E_t,w_t,\Phi_t),
$$

其中:

1. $V_t$ 为有限节点集合,每个节点代表一个"概念"或"抽象状态";
2. $E_t \subset V_t\times V_t$ 为有向或无向边集,表示概念之间的关系(如因果、蕴含、相似等);
3. $w_t:E_t\to(0,\infty)$ 为边权,表示关系强度;
4. 嵌入映射

$$
\Phi_t:V_t \to \mathcal S_Q,
$$

将每个节点嵌入任务信息流形中的某个点,使得知识图谱成为 $\mathcal S_Q$ 的有限采样骨架。

### 3.2 图 Laplace 与信息 Laplace 的一致性

在知识图谱 $\mathcal G_t$ 上定义无向化边集 $\widetilde E_t$ 与对称权重 $\widetilde w_t$,构造图 Laplace 算子

$$
(\Delta_t f)(v)
=
\sum_{u\sim v} \widetilde w_t(v,u)\big(f(u) - f(v)\big),
\quad f:V_t\to\mathbb R.
$$

另一方面,信息流形上有 Laplace–Beltrami 算子

$$
\Delta_{g_Q} f(\phi)
=
\frac{1}{\sqrt{\det g_Q(\phi)}}
\partial_i
\big(
\sqrt{\det g_Q(\phi)}\,g_Q^{ij}(\phi)\,\partial_j f(\phi)
\big).
$$

我们希望在 $t$ 足够大、$V_t$ 足够稠密的极限下,$\Delta_t$ 的谱逼近 $\Delta_{g_Q}$ 的谱。

**定义 3.2(谱逼近)**

称知识图谱 $\mathcal G_t$ 在信息流形 $(\mathcal S_Q,g_Q)$ 上谱逼近,若存在嵌入 $\Phi_t:V_t\to\mathcal S_Q$ 及适当的权重归一化,使得:

1. $\Phi_t(V_t)$ 在 $\mathcal S_Q$ 中随 $t \to\infty$ 变得稠密;
2. 以 $\Phi_t$ 为基础构造的核权重 $\widetilde w_t$ 满足图 Laplace $\Delta_t$ 在适当缩放下 $\Gamma$-收敛到 $\Delta_{g_Q}$。

这一设定与流形学习中的图 Laplace 收敛理论一致,只是这里将其解释为"观察者知识图谱对信息流形的渐进逼近"。

---

## 4 观察者扩展世界线与认知动力学

本节将观察者与控制–信息几何结合,得到一个扩展的联合状态空间与世界线。

### 4.1 扩展状态空间

定义观察者–宇宙联合的扩展状态空间

$$
\widehat{\mathcal E}_Q
=
\mathcal M \times \mathcal S_Q \times M_{\mathrm{int}} \times \mathfrak G \times \mathfrak A,
$$

其中:

1. $\mathcal M$ 为控制流形,$\mathcal S_Q$ 为任务信息流形;
2. $M_{\mathrm{int}}$ 为内部记忆状态空间;
3. $\mathfrak G$ 为所有有限知识图谱的集合;
4. $\mathfrak A$ 为所有注意力配置的集合(例如概率密度 $\rho_t$ 或离散权重 $A_k$)。

在时间参数化下,观察者–宇宙的联合轨道为

$$
\widehat z(t)
=
\big(
\theta(t),\phi(t),m(t),\mathcal G_t,A_t
\big).
$$

### 4.2 观测–计算作用量

我们在此前时间–信息–复杂性作用量 $\mathcal A_Q$ 的基础上加入观察者内部代价与知识图谱更新代价。

令

$$
v_{\mathcal M}^2(t)
=
G_{ab}(\theta(t))\dot\theta^a\dot\theta^b,
\quad
v_{\mathcal S_Q}^2(t)
=
g_{ij}(\phi(t))\dot\phi^i\dot\phi^j.
$$

定义以下项:

1. 复杂性动能项

$$
K_{\mathrm{comp}}(t)
=
\tfrac12 \alpha^2 v_{\mathcal M}^2(t);
$$

2. 信息动能项

$$
K_{\mathrm{info}}(t)
=
\tfrac12 \beta^2 v_{\mathcal S_Q}^2(t);
$$

3. 知识势能项

$$
U_Q(\phi(t))
=
I_Q(\phi(t)),
$$

其中 $I_Q$ 为任务信息质量函数;

4. 知识图谱更新代价项

$$
R_{\mathrm{KG}}(t)
=
\lambda_{\mathrm{KG}}\,\mathsf D\big(\mathcal G_{t+\mathrm d t},\mathcal G_t\big),
$$

其中 $\mathsf D$ 为图之间的距离(例如谱距离或 Gromov–Wasserstein 距离);

5. 注意力配置代价项

$$
R_{\mathrm{att}}(t)
=
\lambda_{\mathrm{att}}\,\mathsf C_{\mathrm{att}}(A_t),
$$

例如以熵正则或带宽约束形式。

**定义 4.1(观察者–计算联合作用量)**

$$
\widehat{\mathcal A}_Q[\widehat z(\cdot)]
=
\int_0^T
\Big(
K_{\mathrm{comp}}(t)
+
K_{\mathrm{info}}(t)
-
\gamma\,U_Q(\phi(t))
+
R_{\mathrm{KG}}(t)
+
R_{\mathrm{att}}(t)
\Big)\,\mathrm dt.
$$

极小化 $\widehat{\mathcal A}_Q$ 给予在有限资源下"最优"观测–计算–学习策略。

---

## 5 信息积累与注意力–复杂性不等式

本节给出一个代表性的"观察者版时间–信息不等式":在复杂性预算与注意力带宽约束下,观察者在有限时间内能够积累的信息量有上界。

### 5.1 信息积累速率

令 $H_Q(t)$ 表示观察者在任务 $Q$ 下的知识量,可取为其内部知识图谱节点上的信息熵或相对熵之和,例如

$$
H_Q(t)
=
\sum_{v\in V_t}
\pi_t(v)\,I_Q(\Phi_t(v)),
$$

其中 $\pi_t$ 为在知识图谱节点上的权重分布。信息积累速率为

$$
\dot H_Q(t)
=
\frac{\mathrm d}{\mathrm dt}H_Q(t).
$$

我们将其与复杂性速度与注意力带宽联系。

### 5.2 注意力带宽与 Fisher 速率

假设在每个时刻 $t$,观察者通过注意力密度 $\rho_t(\phi)$ 对信息流形进行采样,其单步 Fisher 信息获取速率 $J(t)$ 与注意力带宽关联,例如

$$
J(t)
=
\int_{\mathcal S_Q}
\rho_t(\phi)\,\big|\nabla I_Q(\phi)\big|_{g_Q}^2\,\mathrm d\mu_{g_Q}(\phi).
$$

在复杂性–信息联合变分框架下,$v_{\mathcal S_Q}^2(t)$ 与 $J(t)$ 之间存在 Lipschitz 关系。

### 5.3 信息积累不等式

在局部 Lipschitz 条件与有限注意力带宽约束下,可以证明如下不等式。

**定理 5.1(观察者信息积累上界)**

假设:

1. 任务信息质量函数 $I_Q$ 在 $\mathcal S_Q$ 上 Lipschitz,且梯度有界:存在 $L_I,C_I>0$ 使得

$$
\big|\nabla I_Q(\phi)\big|_{g_Q}
\le C_I,
\quad
\forall \phi\in\mathcal S_Q;
$$

2. 观察者注意力密度 $\rho_t$ 的二阶矩有界,即存在 $B_{\mathrm{att}}>0$ 使得

$$
\int_{\mathcal S_Q}
\rho_t(\phi)\,
d_{\mathcal S_Q}^2(\phi,\bar\phi)\,\mathrm d\mu_{g_Q}(\phi)
\le B_{\mathrm{att}},
$$

对某固定点 $\bar\phi$ 与所有 $t\in[0,T]$ 成立;

3. 观察者的复杂性预算为

$$
C_{\max}
=
\int_0^T
\sqrt{G_{ab}(\theta(t))\dot\theta^a\dot\theta^b}\,\mathrm dt.
$$

则存在常数 $K>0$,仅依赖于 $C_I,B_{\mathrm{att}}$ 与联合几何结构,使得

$$
H_Q(T) - H_Q(0)
\le
K\,C_{\max}.
$$

证明见附录 D.1。

该不等式说明:在统一时间刻度与几何约束下,观察者可积累的信息量与其可用复杂性资源成线性上界,注意力仅改变比例常数而不改变线性形式。

---

## 6 知识图谱维数收敛与信息流形骨架

本节证明,在合适条件下,观察者的知识图谱谱维数在长时间极限下收敛到任务信息流形的局部信息维数。

### 6.1 知识图谱的谱维数

对知识图谱 $\mathcal G_t$,令 $\lambda_1^{(t)}\le\lambda_2^{(t)}\le\cdots$ 为图 Laplace 算子 $-\Delta_t$ 的特征值序列。定义谱维数

$$
d_{\mathrm{spec}}(t)
=
-2 \lim_{\varepsilon\downarrow 0}
\frac{\log \mathrm{Tr}\,\exp(\varepsilon\Delta_t)}{\log\varepsilon},
$$

若该极限存在。直观地,$d_{\mathrm{spec}}(t)$ 描述图在小尺度下的有效维数。

### 6.2 信息流形的局部信息维数

在信息流形 $(\mathcal S_Q,g_Q)$ 上,局部信息维数可定义为

$$
d_{\mathrm{info},Q}(\phi_0)
=
\lim_{R\to 0}
\frac{\log \mu_{g_Q}\big(B_R(\phi_0)\big)}{\log R},
$$

其中 $B_R(\phi_0)$ 为 $\phi_0$ 附近半径 $R$ 的 geodesic 球。

### 6.3 收敛定理

**定理 6.2(知识图谱谱维数的收敛)**

假设:

1. 观察者的知识图谱 $\mathcal G_t = (V_t,E_t,w_t,\Phi_t)$ 在 $t\to\infty$ 时在 $(\mathcal S_Q,g_Q)$ 上谱逼近;
2. 观察者长期注意力覆盖一个紧致区域 $K\subset\mathcal S_Q$,且 $\Phi_t(V_t) \subset K$ 对充分大 $t$ 成立;
3. 对 $K$ 中任意 $\phi_0$,局部信息维数 $d_{\mathrm{info},Q}(\phi_0)$ 存在且常数 $d_{\mathrm{info},Q}$。

则有

$$
\lim_{t\to\infty} d_{\mathrm{spec}}(t) = d_{\mathrm{info},Q}.
$$

证明见附录 E.1。

该定理表明:在长期学习过程中,观察者知识图谱的谱维数趋向信息流形的真实维数,意味着知识图谱在几何上逐渐成为信息流形的高保真骨架。

---

## 附录 A:观察者对象与注意力算子的形式化细节

### A.1 观察者对象的可达性与有限记忆

在主文中,我们仅给出了观察者对象的结构定义。本附录补充其可达性与有限记忆的公理。

**公理 O1(有限记忆容量)**

内部记忆状态空间 $M_{\mathrm{int}}$ 是有限集合,或可分解为有限维寄存器的直积,每个寄存器状态数有限。这保证任一时刻观察者内部表示的信息是可编码为有限比特串的。

**公理 O2(内部更新可计算性)**

更新算子 $\mathcal U:M_{\mathrm{int}}\times\Sigma_{\mathrm{obs}}\to M_{\mathrm{int}}$ 应为计算宇宙模型下的可计算函数,即存在有限复杂性路径实现该更新。

**公理 O3(注意力决策的局域性)**

注意力–观测策略 $\mathcal P$ 应仅依赖当前内部状态 $m_k$,不依赖整个历史,从而满足 Markov 性。这与标准 POMDP 模型一致。

在这些公理下,观察者的行为可以嵌入计算宇宙的离散动力体系中,不引入外部"超计算"成分。

---

## 附录 B:知识图谱谱逼近的信息流形理论背景

图 Laplace 收敛到流形 Laplace–Beltrami 的理论在流形学习与谱几何中已有成熟结果。本附录仅给出在本文设定下的简化版本。

### B.1 核权重与图 Laplace 的构造

假设 $\mathcal S_Q$ 为紧致流形,$\{ \phi_v \}_{v\in V_t}$ 为从 $\mathcal S_Q$ 抽样的点集。定义核权重

$$
\widetilde w_t(v,u)
=
\eta_t^{-d}
K\left(
\frac{d_{\mathcal S_Q}(\phi_v,\phi_u)}{\eta_t}
\right),
$$

其中 $\eta_t \to 0$、$t\eta_t^d \to \infty$,$K$ 为对称核。图 Laplace

$$
(\Delta_t f)(v)
=
\sum_{u} \widetilde w_t(v,u)\big(f(u)-f(v)\big)
$$

在适当归一化后 $\Gamma$-收敛到 $\Delta_{g_Q}$。这一结果可视为 Cooper–Belkin–Niyogi 等工作的变形版本。

---

## 附录 C:扩展作用量下的 Euler–Lagrange 形式

扩展作用量 $\widehat{\mathcal A}_Q$ 相比 $\mathcal A_Q$ 增加了 $R_{\mathrm{KG}}$ 与 $R_{\mathrm{att}}$,它们对 $\mathcal G_t,A_t$ 的变分给出图更新与注意力配置的最优性条件。形式上,可写为

$$
\frac{\delta \widehat{\mathcal A}_Q}{\delta \mathcal G_t}
=
0,
\quad
\frac{\delta \widehat{\mathcal A}_Q}{\delta A_t}
=
0.
$$

在具体模型中,可以选择 $\mathsf D$ 为 Gromov–Wasserstein 距离,则第一式对应于在每个时刻把知识图谱更新为在代价与信息收益之间平衡的最优匹配图;第二式对应于在给定注意力带宽约束下,选择最大化短期信息增益的注意力分布。由于这些变分涉及图空间与分布空间上的最优化,技术细节较重,故在本文中仅给出结构形式。

---

## 附录 D:观察者信息积累不等式的证明

### D.1 定理 5.1 的证明思路

对 $H_Q(t)$ 的导数,利用链式法则与 Cauchy–Schwarz 不等式,可得

$$
\dot H_Q(t)
=
\sum_{v\in V_t}
\dot\pi_t(v)\,I_Q(\Phi_t(v))
+
\sum_{v\in V_t}
\pi_t(v)\,\nabla I_Q(\Phi_t(v))\cdot\dot\Phi_t(v).
$$

第一项可通过注意力与复杂性几何的约束控制在常数范围内;第二项利用梯度有界性与注意力二阶矩有界性,可估计

$$
\big|\dot H_Q(t)\big|
\le
C_I
\sqrt{
\int \rho_t(\phi)\,d_{\mathcal S_Q}^2(\phi,\bar\phi)\,\mathrm d\mu_{g_Q}
}
\sqrt{v_{\mathcal S_Q}^2(t)}
\le
K_1 \sqrt{v_{\mathcal S_Q}^2(t)}.
$$

再利用联合作用量中的权重关系与 $v_{\mathcal S_Q}^2(t)$ 与 $v_{\mathcal M}^2(t)$ 的耦合,可证明

$$
\int_0^T \sqrt{v_{\mathcal S_Q}^2(t)}\,\mathrm dt
\le
K_2 C_{\max},
$$

从而

$$
H_Q(T) - H_Q(0)
\le
K C_{\max}.
$$

常数 $K$ 仅依赖于几何与注意力带宽参数。完整的技术细节涉及 Jensen 不等式与对复杂性动能–信息动能权重的精细比较,此处仅给出综述。

---

## 附录 E:知识图谱谱维数收敛的证明纲要

### E.1 定理 6.2 的证明

在知识图谱谱逼近与信息流形局部维数常数的假设下,图 Laplace 的热核迹

$$
\mathrm{Tr}\,\exp(t\Delta_t)
$$

在 $t\to 0$ 时的渐近行为可用连续流形上热核迹的渐近展开逼近,即

$$
\mathrm{Tr}\,\exp(t\Delta_t)
\sim
(4\pi t)^{-d_{\mathrm{info},Q}/2}
\sum_{k=0}^\infty a_k t^k.
$$

由谱维数定义

$$
d_{\mathrm{spec}}(t)
=
-2 \lim_{\varepsilon\downarrow 0}
\frac{\log \mathrm{Tr}\,\exp(\varepsilon\Delta_t)}{\log\varepsilon},
$$

以及热核迹渐近形式,可得到

$$
\lim_{t\to\infty} d_{\mathrm{spec}}(t) = d_{\mathrm{info},Q}.
$$

严格证明需构造从图 Laplace 热核到流形 Laplace–Beltrami 热核的误差估计,并控制误差在 $t\to\infty$ 与 $\varepsilon\downarrow 0$ 联合极限下的影响。此类技术在谱几何与图流形收敛文献中已有成熟方法,本文不再复现全部细节。
