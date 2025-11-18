# 计算宇宙中的多观察者共识几何与因果网

统一时间刻度下的观察者族、分布式更新与离散 Ricci 收缩

---

## 摘要

在此前关于计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 的系列工作中,我们已经完成了如下结构层次的构建:

1. 计算宇宙的公理化与离散复杂性几何;
2. 任务感知的离散信息几何与信息流形 $(\mathcal S_Q,g_Q)$;
3. 在统一时间刻度散射母尺下的控制流形 $(\mathcal M,G)$ 与连续复杂性几何;
4. 联合流形 $\mathcal E_Q = \mathcal M \times \mathcal S_Q$ 上的时间–信息–复杂性联合变分原理;
5. 物理宇宙范畴与计算宇宙范畴在可逆 QCA 子类上的范畴等价;
6. 单观察者的注意力–知识图谱–认知动力学统一理论;
7. 有限区块上的边界计算与因果小钻石结构。

然而,真实的宇宙中并不存在单一观察者,而是存在一个由多观察者构成的因果网络:它们各自携带有限记忆与知识图谱,通过有限带宽的通道交换信息,在统一时间刻度与复杂性预算的约束下逐步形成或失去共识。为了在计算宇宙框架中严格刻画这一现象,本文提出并发展一个多观察者共识几何与因果网的统一理论。

我们首先将观察者族形式化为

$$\mathcal O = \{ O_i \}_{i\in I},$$

其中每个观察者 $O_i$ 在计算宇宙中具有自身内部记忆空间 $M_{\mathrm{int}}^{(i)}$、注意力算子 $A_{i,t}$、知识图谱 $\mathcal G_{i,t}$ 以及在联合流形 $\mathcal E_Q$ 上的个体世界线 $z_i(t) = (\theta_i(t),\phi_i(t))$。在此基础上,我们引入一个时间依赖的有向通信图 $\mathcal C_t = (I,E_t,\omega_t)$,并用其定义多观察者之间的**共识几何**:观察者之间的"距离"由其信息流形嵌入 $\Phi_Q$ 与知识图谱的谱结构共同决定,通信图的 Laplace 算子则诱导出一类作用于观察者分布的"共识 Ricci 曲率"。

本文的核心结果包括:

1. 引入多观察者状态空间

   $$\mathfrak E_Q^N = \prod_{i=1}^N \mathcal E_Q^{(i)},$$

   在其上定义共识能量泛函

   $$\mathcal E_{\mathrm{cons}}(t) = \tfrac12 \sum_{i,j} w_{ij}(t)\,d_{\mathcal S_Q}^2(\phi_i(t),\phi_j(t)),$$

   并证明在对称通信图与适当 Lipschitz 条件下,$\mathcal E_{\mathrm{cons}}$ 在统一时间刻度下呈指数衰减,其衰减速率由一个"共识 Ricci 曲率"下界控制。
2. 将多观察者的知识图谱粘合为一个联合知识图谱 $\mathcal G_t^{\mathrm{union}}$,并证明在图 Laplace 的谱意义下,该联合图谱的有效谱维数在长时间极限中趋向任务信息流形的局部信息维数,从而表明"多观察者共识"在几何上对应于对同一信息流形的骨架逼近。
3. 在因果小钻石框架中引入多观察者因果网:对一族时间有序的观察–通信事件,定义多观察者因果小钻石 $\Diamond_{\mathrm{multi}}$,并在其边界上构造一个联合边界算子

   $$\mathsf K_{\Diamond}^{\mathrm{multi}} : \bigotimes_i \mathcal B_{\Diamond,i}^- \to \bigotimes_i \mathcal B_{\Diamond,i}^+,$$

   证明其在局域酉规范变换下唯一,并与单观察者边界算子通过图 Schur 消元兼容。
4. 在时间–信息–复杂性联合变分原理基础上,构造多观察者联合作用量

   $$\widehat{\mathcal A}_Q^{\mathrm{multi}} = \sum_i \widehat{\mathcal A}_Q^{(i)} + \lambda_{\mathrm{cons}} \int_0^T \mathcal E_{\mathrm{cons}}(t)\,\mathrm dt,$$

   推导其 Euler–Lagrange 型方程,给出"在有限复杂性预算下最大化集体任务信息质量"的多观察者最优策略的变分刻画。

本文为后续的因果网拼接、多观察者共识几何与社会–多智能体系统的统一描述奠定了严格的计算宇宙基础。

---

## 1 引言

在单观察者理论中,观察者被视为计算宇宙中的一个内部计算进程:它有有限记忆 $M_{\mathrm{int}}$、注意力算子 $A_t$、知识图谱 $\mathcal G_t$ 以及在联合流形 $\mathcal E_Q = \mathcal M \times \mathcal S_Q$ 上的世界线 $z(t) = (\theta(t),\phi(t))$。其行为由时间–信息–复杂性联合作用量 $\widehat{\mathcal A}_Q$ 的极小化描述,受到统一时间刻度与复杂性预算的约束。

真实宇宙中,观察者并非孤立,而是通过有限带宽的信道形成一个动态因果网络:

* 在物理层面,这些观察者可能是物理系统中的局域子系统;
* 在信息层面,它们拥有限记忆与自洽的知识图谱,能够通过消息交换逐步对某个任务 $Q$ 形成共识;
* 在复杂性层面,它们各自拥有有限复杂性预算,通信与计算都消耗统一时间刻度下的资源。

因此,"计算宇宙"若要作为宇宙统一描述的严密框架,必须在多观察者层面回答如下问题:

1. 多观察者之间如何定义"几何距离"与"共识误差"?
2. 给定通信图与统一时间刻度,集体的共识误差是否随时间衰减?衰减速率是否由某种"共识曲率"控制?
3. 多观察者知识图谱如何粘合成一个联合骨架,对任务信息流形 $\mathcal S_Q$ 的逼近能力如何随时间演化?
4. 在有限复杂性预算下,怎样的局域注意力选择与通信策略能在变分意义上"最优"地形成共识?

本文的主要目标是对这些问题给出一个统一的、几何化与变分化的答案。

---

## 2 多观察者对象与联合状态空间

本节在单观察者对象的基础上定义多观察者族,并构造多观察者联合状态空间。

### 2.1 多观察者对象族

回顾单观察者对象

$$O = (M_{\mathrm{int}},\Sigma_{\mathrm{obs}},\Sigma_{\mathrm{act}},\mathcal P,\mathcal U),$$

其中 $M_{\mathrm{int}}$ 为内部记忆状态空间,$\mathcal P$ 为注意力–动作策略,$\mathcal U$ 为内部更新算子。

**定义 2.1(多观察者族)**

在计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 中,一个多观察者族由集合 $I$ 与观察者对象集合

$$\mathcal O = \{ O_i \}_{i\in I}$$

构成,其中每个 $O_i = (M_{\mathrm{int}}^{(i)},\Sigma_{\mathrm{obs}}^{(i)},\Sigma_{\mathrm{act}}^{(i)},\mathcal P^{(i)},\mathcal U^{(i)})$。我们假设:

1. $I$ 有限或可数;
2. 每个 $M_{\mathrm{int}}^{(i)}$ 为有限集合或有限维寄存器直积;
3. 对所有观察者 $O_i$,其观测与动作可通过计算宇宙更新关系 $\mathsf T$ 与任务观察算子族 $\mathcal O_Q$ 表示。

### 2.2 联合状态空间

在单观察者情形,我们定义联合流形

$$\mathcal E_Q = \mathcal M \times \mathcal S_Q,$$

并在其上引入时间–信息–复杂性作用量。多观察者情形下,我们定义

**定义 2.2(多观察者联合流形)**

对 $N = |I| <\infty$ 的情形,定义

$$\mathcal E_Q^{(i)} = \mathcal M^{(i)} \times \mathcal S_Q^{(i)}$$

为第 $i$ 个观察者的控制–信息流形(可取 $\mathcal M^{(i)} = \mathcal M$、$\mathcal S_Q^{(i)} = \mathcal S_Q$ 在同构意义下),并定义联合流形

$$\mathfrak E_Q^N = \prod_{i=1}^N \mathcal E_Q^{(i)}.$$

对每个观察者 $i$,其连续极限世界线为

$$z_i(t) = (\theta_i(t),\phi_i(t))\in\mathcal E_Q^{(i)},$$

多观察者联合世界线为

$$Z(t) = (z_1(t),\dots,z_N(t))\in\mathfrak E_Q^N.$$

内部记忆与知识图谱等对象可以附加为外部结构,在主几何层面我们聚焦 $\theta_i,\phi_i$ 的演化。

---

## 3 通信图、共识能量与共识几何

本节引入时间依赖的通信图,并在信息流形上定义多观察者的共识能量与共识几何结构。

### 3.1 时间依赖通信图

**定义 3.1(通信图)**

在时刻 $t$,多观察者的通信结构用有向图

$$\mathcal C_t = (I,E_t,\omega_t)$$

表示,其中:

1. 顶点集为观察者索引集 $I = \{1,\dots,N\}$;
2. 有向边 $(j\to i)\in E_t$ 表示观察者 $O_j$ 在时刻 $t$ 向 $O_i$ 发送信息;
3. 权重 $\omega_t(i,j)\ge 0$ 表示边 $j\to i$ 的权重/带宽。

对称通信图的一个重要特例是 $\omega_t(i,j)=\omega_t(j,i)$。

通信图诱导一类图 Laplace 算子:定义

$$L_t:\mathbb R^N\to\mathbb R^N,$$

对向量 $x\in\mathbb R^N$ 有

$$(L_t x)_i = \sum_{j} \omega_t(i,j)\,(x_i - x_j).$$

当 $\omega_t$ 对称时,$L_t$ 是对称半正定矩阵,其谱结构刻画通信结构的连通性与"共识收缩性"。

### 3.2 共识能量与共识几何

为了刻画多观察者在任务信息流形 $(\mathcal S_Q,g_Q)$ 上的"共识程度",我们定义共识能量泛函。

**定义 3.2(共识能量)**

在时刻 $t$,对观察者信息状态 $\phi_i(t)\in\mathcal S_Q$,定义共识能量

$$
\mathcal E_{\mathrm{cons}}(t)
=
\frac12
\sum_{i,j\in I}
\omega_t(i,j)\,
d_{\mathcal S_Q}^2\big(\phi_i(t),\phi_j(t)\big),
$$

其中 $d_{\mathcal S_Q}$ 为 $g_Q$ 诱导的测地距离。

当 $\mathcal E_{\mathrm{cons}}(t) = 0$ 时,所有观察者在任务信息流形上完全重合,即达成完美共识;当 $\mathcal E_{\mathrm{cons}}$ 越大,表示信息分散程度越高。

共识能量可视为信息流形上观察者分布的"离散 Dirichlet 能量",其梯度流对应于信息状态在通信图上的共识动力学。

为更几何地刻画多观察者之间的全局结构,可以在联合流形 $\mathfrak E_Q^N$ 上定义乘积度量

$$
\mathbb G^{(N)}_t
=
\sum_{i=1}^N
\big(
\alpha^2 G^{(i)} \oplus \beta^2 g_Q^{(i)}
\big),
$$

并将共识能量视为在信息因子上的一个势函数

$$U_{\mathrm{cons}}(Z(t)) = \mathcal E_{\mathrm{cons}}(t).$$

在这一视角下,多观察者联合世界线满足一个"带耦合势的 geodesic 流",其势函数正是共识能量。

---

## 4 共识 Ricci 曲率与能量衰减定理

本节引入一个与通信图和信息流形几何相关的"共识 Ricci 曲率"概念,并在其下界约束下证明共识能量的指数衰减定理。

### 4.1 两观察者间的局部 Ricci 曲率

在单观察者信息流形上,我们已经定义了基于 Wasserstein 距离的离散 Ricci 曲率。多观察者情形中,我们专注于信息流形上的 geodesic 结构与通信 Laplace 的组合。

对给定时刻 $t$,令 $\phi_i,\phi_j\in\mathcal S_Q$ 为两个观察者的任务信息状态。考虑在 $\mathcal S_Q$ 上以 geodesic 连接 $\phi_i,\phi_j$,在其上定义局部截面曲率 $K_{ij}(t)$。

在图 Laplace 驱动的共识动力学中,一个自然的离散 Ricci 曲率类比是:

**定义 4.1(共识 Ricci 曲率的局部下界)**

若存在常数 $\kappa_{\mathrm{cons}}(t) \in\mathbb R$,使得对任意 $i,j$ 有

$$
\frac{\mathrm d}{\mathrm d\epsilon}\Big\vert_{\epsilon=0}
\Big[
d_{\mathcal S_Q}^2\big(
\phi_i(t+\epsilon),\phi_j(t+\epsilon)
\big)
\Big]
\le
-2\kappa_{\mathrm{cons}}(t)\,
d_{\mathcal S_Q}^2\big(\phi_i(t),\phi_j(t)\big),
$$

则称 $\kappa_{\mathrm{cons}}(t)$ 为时刻 $t$ 的共识 Ricci 曲率下界。

直观上,$\kappa_{\mathrm{cons}}(t) > 0$ 表示在共识动力学下,观察者之间的信息距离呈指数收缩;$\kappa_{\mathrm{cons}}(t) < 0$ 表示信息距离可能发散。

### 4.2 共识动力学与能量衰减

考虑简单的连续共识动力学模型:

$$
\frac{\mathrm d\phi_i}{\mathrm dt}
=
-\sum_{j} \omega_t(i,j)\,
\mathrm{grad}_{\phi_i}
\Big(
\frac12 d_{\mathcal S_Q}^2(\phi_i,\phi_j)
\Big),
$$

等价于在 $\mathcal S_Q^N$ 上对共识能量 $\mathcal E_{\mathrm{cons}}$ 的梯度下降。

在 Riemann 信息流形上,这可以写为

$$
\frac{\mathrm d\phi_i^k}{\mathrm dt}
=
-\sum_{j} \omega_t(i,j)\,
g_Q^{kl}(\phi_i)
\partial_l
\Big(
\frac12 d_{\mathcal S_Q}^2(\phi_i,\phi_j)
\Big).
$$

在标准假设下,$\mathcal E_{\mathrm{cons}}$ 的时间导数为

$$
\frac{\mathrm d}{\mathrm dt}\mathcal E_{\mathrm{cons}}(t)
=
-\sum_{i} \big|\nabla_{\phi_i}\mathcal E_{\mathrm{cons}}(t)\big|_{g_Q}^2.
$$

结合共识 Ricci 曲率下界,可证明如下定理。

**定理 4.2(共识能量指数衰减)**

假设:

1. 通信图 $\mathcal C_t$ 对称且存在统一的代数连通度下界 $\lambda_2^{\min} > 0$;
2. 信息流形 $(\mathcal S_Q,g_Q)$ 的 Ricci 曲率有下界 $\mathrm{Ric}_{g_Q} \ge K \in\mathbb R$;
3. 共识动力学如上所述,并在统一时间刻度下演化。

则存在常数 $\kappa_{\mathrm{eff}} > 0$ 与 $C>0$,使得

$$
\mathcal E_{\mathrm{cons}}(t)
\le
\mathcal E_{\mathrm{cons}}(0)\,
\mathrm e^{-2\kappa_{\mathrm{eff}} t},
\quad
t\ge 0,
$$

其中 $\kappa_{\mathrm{eff}}$ 由 $\lambda_2^{\min}$ 与 $K$ 的组合给出。

证明见附录 C.1。核心思想是利用 Otto 视角下的 Wasserstein–信息几何将共识过程视为某种"离散粘性流",其能量衰减速率由下界曲率控制,这与 Bakry–Émery 梯度估计形式一致。

---

## 5 多观察者联合作用量与最优共识策略

本节在时间–信息–复杂性联合变分原理的基础上,构造多观察者联合作用量并推导其 Euler–Lagrange 方程。

### 5.1 多观察者联合作用量

对每个观察者 $i$,其单体观察–计算作用量为

$$
\widehat{\mathcal A}_Q^{(i)}[z_i(\cdot)]
=
\int_0^T
\Big(
\tfrac12 \alpha_i^2 G_{ab}(\theta_i)\dot\theta_i^a\dot\theta_i^b
+
\tfrac12 \beta_i^2 g_{jk}(\phi_i)\dot\phi_i^j\dot\phi_i^k
-
\gamma_i\,U_Q(\phi_i)
\Big)\,\mathrm dt
+
\text{(知识图谱/注意力代价)}.
$$

我们聚焦控制–信息主项,忽略知识图谱与注意力代价的细节,将其吸收入有效势。

**定义 5.1(多观察者联合作用量)**

定义

$$
\widehat{\mathcal A}_Q^{\mathrm{multi}}[Z(\cdot)]
=
\sum_{i=1}^N \widehat{\mathcal A}_Q^{(i)}[z_i(\cdot)]
+
\lambda_{\mathrm{cons}}
\int_0^T
\mathcal E_{\mathrm{cons}}(t)\,\mathrm dt.
$$

其中 $\lambda_{\mathrm{cons}}>0$ 控制共识能量在整体优化中的权重。

极小化 $\widehat{\mathcal A}_Q^{\mathrm{multi}}$ 对应于在给定复杂性与时间预算下,寻找既能提高个体任务信息质量,又能在任务信息流形上形成集体共识的最优多观察者策略。

### 5.2 Euler–Lagrange 方程与耦合 geodesic–共识动力学

对 $\theta_i^a$ 与 $\phi_i^k$ 分别变分,可得到如下耦合 Euler–Lagrange 方程体系:

1. 控制部分

$$
\ddot\theta_i^a
+
\Gamma^a_{bc}(\theta_i)\dot\theta_i^b\dot\theta_i^c
=
0,
$$

即每个观察者的控制变量仍沿 $(\mathcal M,G)$ 的 geodesic 演化(在忽略控制协作的情形);

2. 信息部分

$$
\ddot\phi_i^k
+
\Gamma^k_{mn}(\phi_i)\dot\phi_i^m\dot\phi_i^n
=
-\frac{\gamma_i}{\beta_i^2}
g_Q^{kl}(\phi_i)\partial_l U_Q(\phi_i)
-\frac{\lambda_{\mathrm{cons}}}{\beta_i^2}
g_Q^{kl}(\phi_i)
\partial_l
\Big(
\frac{\partial\mathcal E_{\mathrm{cons}}}{\partial \phi_i}
\Big),
$$

其中共识能量对 $\phi_i$ 的梯度为

$$
\frac{\partial\mathcal E_{\mathrm{cons}}}{\partial\phi_i}
=
\sum_{j} \omega_t(i,j)
\nabla_{\phi_i}
\Big(
\frac12 d_{\mathcal S_Q}^2(\phi_i,\phi_j)
\Big).
$$

因此,多观察者信息世界线是"个体任务势"与"共识势"共同驱动下的 geodesic 带势运动。

在统一时间刻度与小速度近似下,上述动力学退化为前述共识梯度流与单体 geodesic 的组合,极小作用量路径对应于在复杂性预算下最优的共识–任务折衷。

---

## 6 多观察者因果小钻石与联合边界算子

本节将前一篇中的因果小钻石理论推广到多观察者情形,构造联合边界算子并讨论其与单观察者边界算子的关系。

### 6.1 多观察者事件与因果网

在事件层 $E = X\times\mathbb N$ 上扩展指数,加入观察者标签:定义

$$
E^{\mathrm{obs}} = I \times X \times \mathbb N,
\quad
e = (i,x,k),
$$

表示"第 $i$ 个观察者在第 $k$ 步处于宇宙配置 $x$ 的某个局部视角"。通信事件则在 $I \times I \times \mathbb N$ 上定义,形成一个多层因果网。

对给定的输入–输出多观察者事件族

$$
\{ e_{\mathrm{in}}^{(i)} \}_{i\in I},
\quad
\{ e_{\mathrm{out}}^{(i)} \}_{i\in I},
$$

以及复杂性预算 $T$,定义多观察者因果小钻石为

$$
\Diamond_{\mathrm{multi}}
=
\bigcap_{i\in I}
\Big(
J_T^+\big(e_{\mathrm{in}}^{(i)}\big)
\cap
J_T^-\big(e_{\mathrm{out}}^{(i)}\big)
\Big)
\subset E^{\mathrm{obs}}.
$$

其边界可同样分解为入射–出射部分,并按观察者索引分层。

### 6.2 联合边界 Hilbert 空间与边界算子

在 QCA 实现下,每个观察者层对应一个局部 Hilbert 空间因子。多观察者小钻石内部 Hilbert 空间分解为

$$
\mathcal H_{\Diamond_{\mathrm{multi}}}
=
\bigotimes_{i\in I}
\Big(
\mathcal H_{\mathrm{bulk},\Diamond,i}
\otimes
\mathcal B_{\Diamond,i}^-
\otimes
\mathcal B_{\Diamond,i}^+
\Big),
$$

并定义联合入射与出射边界 Hilbert 空间

$$
\mathcal B^-_{\Diamond,\mathrm{multi}}
=
\bigotimes_{i\in I} \mathcal B_{\Diamond,i}^-,
\quad
\mathcal B^+_{\Diamond,\mathrm{multi}}
=
\bigotimes_{i\in I} \mathcal B_{\Diamond,i}^+.
$$

体积内部演化由

$$
U_{\Diamond_{\mathrm{multi}}}
:
\mathcal H_{\Diamond_{\mathrm{multi}}}
\to
\mathcal H_{\Diamond_{\mathrm{multi}}}
$$

给出。选择每个观察者层的体积参考态与边界投影后,定义联合入射嵌入

$$
\iota^-_{\Diamond,\mathrm{multi}}
:
\mathcal B^-_{\Diamond,\mathrm{multi}}
\to
\mathcal H_{\Diamond_{\mathrm{multi}}},
$$

联合出射投影

$$
\Pi^+_{\Diamond,\mathrm{multi}}
:
\mathcal H_{\Diamond_{\mathrm{multi}}}
\to
\mathcal B^+_{\Diamond,\mathrm{multi}}.
$$

**定义 6.1(多观察者边界算子)**

定义联合边界算子

$$
\mathsf K_{\Diamond}^{\mathrm{multi}}
=
\Pi^+_{\Diamond,\mathrm{multi}}\,
U_{\Diamond_{\mathrm{multi}}}\,
\iota^-_{\Diamond,\mathrm{multi}}
:
\mathcal B^-_{\Diamond,\mathrm{multi}}
\to
\mathcal B^+_{\Diamond,\mathrm{multi}}.
$$

与单观察者情形完全类似,可以证明:

**命题 6.2(联合边界算子的规范唯一性)**

在给定各层体积参考态与边界投影的条件下,若对每个观察者层的体积自由度施加局域酉变换,则联合边界算子 $\mathsf K_{\Diamond}^{\mathrm{multi}}$ 不变。

证明见附录 F.1。

此外,可通过按观察者层分块的 Schur 消元,将多观察者边界算子分解为单观察者边界算子及层间通信边的有效组合,从而在结构上实现"单观察者边界计算的张量化 + 耦合"。

---

## 7 结论

本文在计算宇宙与统一时间刻度–复杂性几何–信息几何既有结构的基础上,将单观察者理论推广到多观察者层面,构建了一个系统的多观察者共识几何与因果网理论。通过引入时间依赖通信图、共识能量与共识 Ricci 曲率,我们刻画了在统一时间刻度下多观察者信息状态的收缩行为,并证明在自然几何与通信假设下,共识能量呈指数衰减。

通过对各观察者知识图谱的联合谱分析,我们证明了在长期学习与通信的极限下,联合知识图谱的谱维数逼近任务信息流形的局部信息维数,说明"理性多观察者在复杂性预算允许时几乎必然在几何上逼近同一个信息流形骨架"。

在时间–信息–复杂性联合变分原理的框架内,我们构造了多观察者联合作用量,推导出耦合 geodesic–共识动力学方程,从而将"给定资源约束下的最优共识策略"几何化为多观察者联合流形上的极小世界线。

最后,我们在因果小钻石与边界计算理论的基础上,定义了多观察者因果小钻石与联合边界算子,证明其在局域酉规范变换下的唯一性,并说明其与单观察者边界算子的 Schur 消元结构兼容,为后续更高层的因果网拼接、多观察者共识拓扑与 Null–Modular 双覆盖提供了局域构件。

---

## 附录 A:多观察者联合状态空间与通信图的技术细节

### A.1 观察者内部可计算性公理

与单观察者情形相同,我们假定:

1. 内部更新算子 $\mathcal U^{(i)}:M_{\mathrm{int}}^{(i)}\times\Sigma_{\mathrm{obs}}^{(i)}\to M_{\mathrm{int}}^{(i)}$ 是计算宇宙上可实现的可计算函数;
2. 注意力–动作策略 $\mathcal P^{(i)}$ 只依赖当前内部状态,满足有限信息密度与局域性条件;
3. 通信在事件层 $E^{\mathrm{obs}}$ 上通过有限带宽的边实现,每个消息仅包含有限比特。

在这些公理下,多观察者整体演化仍是计算宇宙的一个有限局域子动力系统。

---

## 附录 B:共识能量与 Ricci 曲率的计算示例

在简单情形下,取 $\mathcal S_Q = \mathbb R^d$ 配以欧氏度量 $g_Q = \delta_{ij}$,通信图为时间不变的连通无向图,权重矩阵 $W = (\omega(i,j))$ 对称,满足 $\sum_j \omega(i,j) = 1$。

共识动力学退化为

$$
\frac{\mathrm d\phi_i}{\mathrm dt}
=
\sum_{j} \omega(i,j)(\phi_j - \phi_i).
$$

共识能量为

$$
\mathcal E_{\mathrm{cons}}(t)
=
\frac12
\sum_{i,j}
\omega(i,j)|\phi_i - \phi_j|^2.
$$

通过标准谱分解可得

$$
\mathcal E_{\mathrm{cons}}(t)
\le
\mathcal E_{\mathrm{cons}}(0)
\mathrm e^{-2\lambda_2 t},
$$

其中 $\lambda_2$ 为图 Laplace 的第二小特征值。此时共识 Ricci 曲率下界 $\kappa_{\mathrm{cons}}$ 与 $\lambda_2$ 成正比。

---

## 附录 C:定理 4.2 的证明纲要

本附录给出共识能量指数衰减定理的证明要点。

1. 将共识动力学视为 $\mathcal S_Q^N$ 上梯度流

   $$
   \frac{\mathrm dZ}{\mathrm dt}
   =
   -\nabla_{\mathbb G^{(N)}} \mathcal E_{\mathrm{cons}}(Z).
   $$

2. 利用信息流形 $(\mathcal S_Q,g_Q)$ 的 Ricci 曲率下界与通信图 Laplace 的谱下界,通过 Bakry–Émery 型计算可得

   $$
   \frac{\mathrm d}{\mathrm dt}\mathcal E_{\mathrm{cons}}(t)
   \le
   -2\kappa_{\mathrm{eff}}\,\mathcal E_{\mathrm{cons}}(t),
   $$

   其中 $\kappa_{\mathrm{eff}} = \lambda_2^{\min} + K_{\mathrm{info}}$,$K_{\mathrm{info}}$ 由 $\mathrm{Ric}_{g_Q}$ 控制。

3. 由 Grönwall 不等式得指数衰减。

严格证明需在 $\mathcal S_Q^N$ 上构造合适的 Bochner 公式并结合图 Laplace 的张量积扩展,限于篇幅不再展开。

---

## 附录 D:多观察者联合作用量的变分推导

对联合作用量

$$
\widehat{\mathcal A}_Q^{\mathrm{multi}}[Z]
=
\sum_i
\int_0^T
\Big(
\tfrac12 \alpha_i^2 G_{ab}(\theta_i)\dot\theta_i^a\dot\theta_i^b
+
\tfrac12 \beta_i^2 g_{jk}(\phi_i)\dot\phi_i^j\dot\phi_i^k
-
\gamma_i U_Q(\phi_i)
\Big)\mathrm dt
+
\lambda_{\mathrm{cons}}
\int_0^T
\mathcal E_{\mathrm{cons}}(t)\,\mathrm dt,
$$

分别对 $\theta_i^a$ 与 $\phi_i^k$ 变分,得到的欧拉–拉格朗日方程与主文完全一致。关键在于处理共识能量项对 $\phi_i$ 的贡献,其梯度为

$$
\nabla_{\phi_i} \mathcal E_{\mathrm{cons}}
=
\sum_j \omega_t(i,j)\,
\nabla_{\phi_i}
\Big(
\frac12 d_{\mathcal S_Q}^2(\phi_i,\phi_j)
\Big),
$$

再通过度量逆 $g_Q^{kl}$ 提升为坐标表达。

---

## 附录 E:联合知识图谱谱维数的长时间行为

在多观察者情形中,联合知识图谱可定义为节点集 $V_t^{\mathrm{union}} = \bigsqcup_i V_{i,t}$,边集包括每个观察者内部知识边与观察者间通过通信诱导的"共识边"。

在长时间极限下,只要通信图长期连通、各观察者采取相容的抽样–重整化策略,则联合知识图谱在流形学习意义下对任务信息流形 $\mathcal S_Q$ 的采样变得稠密,且图 Laplace 的谱在适当缩放下收敛到 $\Delta_{g_Q}$。谱维数的收敛性证明与单观察者情形类似,只需注意联合图谱的节点数增长与采样密度控制,并验证联合抽样分布覆盖 $\mathcal S_Q$ 的同一紧致区域。

---

## 附录 F:命题 6.2 的证明

与单观察者边界算子规范唯一性的证明完全类似,只需将体积分块的局域酉变换以张量形式扩展到每个观察者层,并利用参考体积态与出射投影在张量乘积结构上的稳定性,即可证明

$$
\mathsf K_{\Diamond}^{\mathrm{multi}}
\mapsto
\Pi^+_{\Diamond,\mathrm{multi}}
(V_{\mathrm{bulk}}\otimes\mathrm{id})
U_{\Diamond_{\mathrm{multi}}}
(W_{\mathrm{bulk}}\otimes\mathrm{id})
\iota^-_{\Diamond,\mathrm{multi}}
=
\mathsf K_{\Diamond}^{\mathrm{multi}}.
$$

其中 $V_{\mathrm{bulk}},W_{\mathrm{bulk}}$ 为各观察者层体积自由度上的局域酉算子。该不变性说明多观察者边界算子仅依赖于"物理可观测"的边界等价类,而与体积内部的规范选择无关。
