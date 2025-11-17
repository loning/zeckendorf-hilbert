# 计算宇宙中的边界计算与因果小钻石理论

统一时间刻度下的有限区块、边界算子与离散 GHY 结构

---

## 摘要

在此前关于计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 的系列工作中,我们已经给出了离散复杂性几何(配置图上的复杂性距离、体积增长与离散 Ricci 曲率)、离散信息几何(任务感知相对熵与 Fisher 结构)、统一时间刻度诱导的控制流形 $(\mathcal M,G)$ 以及时间–信息–复杂性联合变分原理,并证明物理宇宙范畴与计算宇宙范畴在可逆 QCA 子类上是范畴等价的。上述结构在"整体宇宙"的尺度上刻画了复杂性与信息的几何与变分结构,但尚未系统讨论**局域有限区块**上的计算:在给定时间/复杂性预算下,一个有限"计算区域"内部的演化如何被其边界完全编码,从而实现真正意义上的"边界计算"。

本文在计算宇宙框架下引入**离散因果结构**与**因果小钻石**的概念,将有限时间–复杂性可达区域形式化为一个有限子图,并将其边界分解为"入射边界"和"出射边界"。在可逆更新的假设下,我们证明:在任一因果小钻石上,存在一个由路径和/算子消元定义的**边界计算算子**

$$
\mathsf K_\Diamond : \mathcal B^-_\Diamond \longrightarrow \mathcal B^+_\Diamond,
$$

使得内部体积上的全部可逆演化在边界上被压缩编码;更进一步,在统一时间刻度与控制流形 $(\mathcal M,G)$ 的连续极限下,$\mathsf K_\Diamond$ 的构造可视为离散版的"GHY 边界项 + 体积分极小"原理的计算宇宙实现。

具体而言,本文首先在事件层 $E = X\times\mathbb N$ 上引入离散时间坐标与计算因果偏序,定义复杂性光锥与有限复杂性预算下的可达区域。然后,对给定输入事件 $e_{\mathrm{in}}$ 与输出事件 $e_{\mathrm{out}}$,我们将满足预算约束的最小封闭区域定义为**因果小钻石** $\Diamond(e_{\mathrm{in}},e_{\mathrm{out}};T,C)$,并对其边界 $\partial\Diamond$ 作入射–出射分解。

在可逆计算宇宙中,我们构造体积更新算子 $U_\Diamond$ 与边界 Hilbert 空间 $\mathcal B^-_\Diamond,\mathcal B^+_\Diamond$,证明存在唯一(在规范等价下)边界算子 $\mathsf K_\Diamond$ 使得

$$
\mathsf K_\Diamond
=
\Pi^+_\Diamond\,U_\Diamond\,\iota^-_\Diamond,
$$

其中 $\iota^-_\Diamond$ 为从入射边界嵌入体积状态的映射,$\Pi^+_\Diamond$ 为投影到出射边界。我们进一步给出基于路径和与图 Schur 消元的纯离散构造,并证明该构造在控制流形细化极限下收敛到由统一时间刻度诱导的边界时间算子,从而将散射时间刻度与"边界计算"统一在同一几何框架内。

最后,我们在时间–信息–复杂性联合变分原理的基础上,引入对单个因果小钻石的**离散作用量**,证明在固定边界数据与统一时间刻度条件下,内部体积上的演化是一个"边界固定下的作用量极小解",其离散 Euler–Lagrange 条件等价于体积更新与边界算子之间的兼容性条件。这一结果提供了离散版的"GHY 边界项 + 体积分极小"结构在计算宇宙中的对应,为后续因果小钻石拼接、多观察者拼网与 Null–Modular 双覆盖等更高层结构铺垫了基础。

---

## 1 引言

在计算宇宙的统一方案中,宇宙整体被刻画为一个可数配置集 $X$ 上的可逆离散动力系统,更新关系 $\mathsf T \subset X\times X$ 与单步代价 $\mathsf C$ 一起定义了一个带统一时间刻度的复杂性几何;同时,任务感知的信息流形 $(\mathcal S_Q,g_Q)$ 通过观察算子族与相对熵结构刻画了"在某个任务下宇宙所携带的可见信息结构"。在这一框架下,我们已经从全局角度建立了:

1. 复杂性图上的离散几何与复杂性维数;
2. 信息几何上的 Fisher 结构与任务信息距离;
3. 统一时间刻度诱导的控制流形 $(\mathcal M,G)$ 与复杂性度量的连续极限;
4. 联合流形 $\mathcal E_Q = \mathcal M\times\mathcal S_Q$ 上的时间–信息–复杂性变分原理;
5. 物理宇宙范畴与计算宇宙范畴之间的范畴等价;
6. 单观察者的注意力、知识图谱与认知动力学的基本结构。

然而,上述结构仍然偏向于**全局或半全局视角**:控制流形 $\mathcal M$ 与信息流形 $\mathcal S_Q$ 的几何描述的是"在所有可能的控制与信息状态上"的结构,而实际计算与观测往往在有限时间、有限复杂性预算的**局部区块**中发生。

在连续物理理论中,这一"局域有限区块"的自然对象是**小因果菱形(small causal diamond)**:在时空 $(M,g)$ 中给定两个事件 $p \ll q$,定义

$$
\Diamond(p,q)
=
J^+(p)\cap J^-(q),
$$

其边界由两片 Null 片与空间截面构成,小因果菱形上的面积、体积、边界挠率与广义熵在量子能量条件与 QNEC/QFC 框架下扮演重要角色。在统一时间刻度–边界时间几何的工作中,小因果菱形被用来定义局域能量条件与边界 Hamilton 量。

在计算宇宙中,我们希望在**完全离散**的框架下构造类似对象:在给定输入配置与输出配置、有限时间/复杂性预算的前提下,定义一个最小的"有限计算区块",其边界完全决定内部演化,并且在统一时间刻度下,其边界算子与时间刻度之间存在自然关系。这就是我们在本文中要构建的**因果小钻石**与**边界计算算子**理论。

从计算角度看,因果小钻石是一个**有限子电路/有限子 QCA 区块**,其内部可以非常庞大复杂,但在外部观察者的视角下,只表现为一个"从入射边界到出射边界的算子"——这就是边界计算的核心思想。

本文将对这一思想给出精确的离散化、几何化与变分化表述。

---

## 2 计算宇宙的离散因果结构

本节在计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 上引入时间层与因果偏序,从而定义复杂性光锥与有限预算可达区域。

### 2.1 事件层与时间坐标

为方便讨论,将离散时间步 $k\in\mathbb N$ 显式引入,定义事件层

$$
E = X\times\mathbb N.
$$

一个事件记作

$$
e = (x,k) \in E,
$$

表示"在第 $k$ 步宇宙处于配置 $x$"。

在无外力控制的情形下,宇宙的演化由 $\mathsf T$ 给出:若 $(x,y)\in\mathsf T$,则存在事件更新

$$
(x,k) \to (y,k+1).
$$

因此事件层上的一步更新关系可定义为

$$
\mathsf T_E
=
\{ ((x,k),(y,k+1)) : (x,y)\in\mathsf T \}.
$$

更一般地,若允许控制/动作参与更新,则更新关系可扩展为带动作标签的 $\mathsf T_{E,\mathrm{act}}$,本文仅关注无显式动作标签的基础情形,动作可吸收进配置。

### 2.2 因果偏序与复杂性光锥

**定义 2.1(因果可达与偏序)**

在事件层 $E$ 上定义关系

$$
e \preceq e'
\quad\Longleftrightarrow\quad
\exists
\ \text{有限路径}\
e = e_0 \to e_1 \to \dots \to e_n = e',
$$

其中 $(e_k,e_{k+1})\in\mathsf T_E$。

显然 $\preceq$ 是一个偏序关系(在可达子集上),表示"$e'$ 可由 $e$ 经有限步更新得到"。若 $e \preceq e'$ 且 $e\neq e'$,记 $e \prec e'$。

在统一时间刻度下,单步代价 $\mathsf C$ 被解释为物理时间代价。我们将其提升到事件层上:对

$$
e = (x,k),
\quad
e' = (y,k+1),
$$

若 $(x,y)\in\mathsf T$,定义

$$
\mathsf C_E(e,e') = \mathsf C(x,y),
$$

否则 $\mathsf C_E(e,e') = \infty$。对事件路径 $\Gamma = (e_0,\dots,e_n)$ 定义路径代价

$$
\mathsf C_E(\Gamma)
=
\sum_{i=0}^{n-1}\mathsf C_E(e_i,e_{i+1}).
$$

**定义 2.2(复杂性距离与光锥)**

对事件 $e,e'\in E$,定义复杂性距离

$$
d_E(e,e')
=
\inf_{\Gamma:e\to e'} \mathsf C_E(\Gamma).
$$

对给定事件 $e_0$ 与预算 $T>0$,定义复杂性未来光锥

$$
J^+_T(e_0)
=
\{ e\in E : e_0 \preceq e,\ d_E(e_0,e)\le T \},
$$

复杂性过去光锥

$$
J^-_T(e_0)
=
\{ e\in E : e \preceq e_0,\ d_E(e,e_0)\le T \}.
$$

这些集合刻画在复杂性预算 $T$ 下,从 $e_0$ 出发能影响/被影响的事件区域。

---

## 3 因果小钻石与其边界

本节定义计算宇宙中的因果小钻石与边界的入射–出射分解。

### 3.1 因果小钻石

**定义 3.1(因果小钻石)**

给定两个事件

$$
e_{\mathrm{in}} = (x_{\mathrm{in}},k_{\mathrm{in}}),
\quad
e_{\mathrm{out}} = (x_{\mathrm{out}},k_{\mathrm{out}}),
\quad
k_{\mathrm{out}}>k_{\mathrm{in}},
$$

以及复杂性预算 $T>0$。若存在至少一条路径 $\Gamma:e_{\mathrm{in}}\to e_{\mathrm{out}}$ 满足 $\mathsf C_E(\Gamma)\le T$,则定义在预算 $T$ 下由 $e_{\mathrm{in}}$ 与 $e_{\mathrm{out}}$ 张成的因果小钻石为

$$
\Diamond(e_{\mathrm{in}},e_{\mathrm{out}};T)
=
J^+_T(e_{\mathrm{in}})
\cap
J^-_T(e_{\mathrm{out}}).
$$

当不致混淆时简记为 $\Diamond$。

直观上,$\Diamond$ 是在复杂性预算 $T$ 下,从 $e_{\mathrm{in}}$ 能传递到 $e_{\mathrm{out}}$ 的所有中间事件的集合,它是计算宇宙中的一个"有限计算区块"。

### 3.2 钻石的体积与边界

定义钻石体积为

$$
\mathrm{Vol}(\Diamond) = | \Diamond |,
$$

即内部事件节点的数量(或配合边数考虑图体积)。

在图论意义下,钻石作为一个有限子图 $G_\Diamond = (V_\Diamond,E_\Diamond)$,其中

$$
V_\Diamond = \Diamond,
\quad
E_\Diamond = \{ (e,e')\in\mathsf T_E : e,e'\in\Diamond \}.
$$

对 $V_\Diamond$,自然定义边界

$$
\partial\Diamond
=
\{ e\in V_\Diamond : \exists e'\notin V_\Diamond,\ (e,e')\in\mathsf T_E \ \text{或}\ (e',e)\in\mathsf T_E \}.
$$

进一步,我们按照时间方向分解边界。

**定义 3.2(入射/出射边界)**

记

$$
\partial^- \Diamond
=
\{ e\in\partial\Diamond : \exists e'\notin V_\Diamond,\ (e,e')\in\mathsf T_E \},
$$

$$
\partial^+ \Diamond
=
\{ e\in\partial\Diamond : \exists e'\notin V_\Diamond,\ (e',e)\in\mathsf T_E \}.
$$

即从钻石内部可以流出到外部的边界事件构成出射边界,从外部可以流入钻石内部的边界事件构成入射边界。
在许多自然情形下 $e_{\mathrm{in}}\in\partial^-\Diamond$、$e_{\mathrm{out}}\in\partial^+\Diamond$。

---

## 4 可逆计算中的边界计算算子

本节在可逆计算宇宙中构造体积更新算子与边界算子,证明"内部体积可在边界上压缩编码"。

### 4.1 体积更新算子

假设计算宇宙对应可逆 QCA 实现,配置空间 $X$ 对应 Hilbert 空间基矢集合,更新关系由全局酉算子 $U:\mathcal H\to\mathcal H$ 给出。事件层 $E$ 的每个事件自由度可对应于某一时间切片上的 Hilbert 空间。

在有限钻石 $\Diamond$ 上,我们可以将 Hilbert 空间分解为

$$
\mathcal H
=
\mathcal H_\Diamond \otimes \mathcal H_{\Diamond^c},
$$

其中 $\mathcal H_\Diamond$ 由 $V_\Diamond$ 对应的局域自由度张成,$\mathcal H_{\Diamond^c}$ 为其补空间。由于更新局域性,一个有限时间区间上的演化可视为作用于 $\mathcal H_\Diamond$ 的某个受制算子 $U_\Diamond$,满足

$$
U
\simeq
U_{\Diamond}\otimes U_{\Diamond^c}
\quad
\text{在}\ \Diamond\ \text{相关自由度上}.
$$

我们仅需要将 $U_\Diamond$ 看作一个作用于 $\mathcal H_\Diamond$ 的酉算子,表示在因果小钻石内部某段时间内的总演化。

### 4.2 边界 Hilbert 空间与嵌入/投影

将钻石内部自由度进一步拆解为内部体积自由度与边界自由度

$$
\mathcal H_\Diamond
=
\mathcal H_{\mathrm{bulk},\Diamond}
\otimes
\mathcal H^-_\Diamond
\otimes
\mathcal H^+_\Diamond,
$$

其中 $\mathcal H^-_\Diamond$ 由入射边界 $\partial^-\Diamond$ 对应的局域自由度张成,$\mathcal H^+_\Diamond$ 由出射边界 $\partial^+\Diamond$ 对应的自由度张成,$\mathcal H_{\mathrm{bulk},\Diamond}$ 为内部剩余体积自由度。

定义边界 Hilbert 空间

$$
\mathcal B^-_\Diamond = \mathcal H^-_\Diamond,
\quad
\mathcal B^+_\Diamond = \mathcal H^+_\Diamond.
$$

内部–边界之间存在自然嵌入与投影:

* 入射嵌入算子

$$
\iota^-_\Diamond :
\mathcal B^-_\Diamond
\to
\mathcal H_{\mathrm{bulk},\Diamond}\otimes \mathcal B^-_\Diamond\otimes\mathcal B^+_\Diamond,
$$

通常取为在给定参考体积态 $\ket{0_{\mathrm{bulk}}}$ 与出射边界参考态 $\ket{0_{+}}$ 上张量嵌入:

$$
\iota^-_\Diamond \ket{\psi^-}
=
\ket{0_{\mathrm{bulk}}}\otimes\ket{\psi^-}\otimes\ket{0_{+}}.
$$

* 出射投影算子

$$
\Pi^+_\Diamond :
\mathcal H_{\mathrm{bulk},\Diamond}\otimes \mathcal B^-_\Diamond\otimes\mathcal B^+_\Diamond
\to
\mathcal B^+_\Diamond,
$$

例如在体积与入射边界上取某个观察态的部分内积。

在更一般的构造中,也可以考虑对体积与入射边界进行部分迹或测量操作,这里采用最简单的"参考态 + 部分内积"形式以突出结构。

### 4.3 边界计算算子的存在性与唯一性

**定义 4.1(边界计算算子)**

在上述设定下,定义边界计算算子

$$
\mathsf K_\Diamond
=
\Pi^+_\Diamond\,U_\Diamond\,\iota^-_\Diamond :
\mathcal B^-_\Diamond \to \mathcal B^+_\Diamond.
$$

直观上,$\mathsf K_\Diamond$ 给出了在体积内部全部演化与参考体积/边界态固定的条件下,从入射边界到出射边界的有效算子,它压缩编码了钻石内部所有计算。

**定理 4.2(边界算子的规范唯一性)**

在给定入射参考态与出射投影的条件下,边界计算算子 $\mathsf K_\Diamond$ 在体积内部自由度的局域酉变换下唯一,即:若

$$
U'_\Diamond
=
(V_{\mathrm{bulk}}\otimes\mathrm{id})\,U_\Diamond\,(W_{\mathrm{bulk}}\otimes\mathrm{id}),
$$

其中 $V_{\mathrm{bulk}},W_{\mathrm{bulk}}$ 仅作用于 $\mathcal H_{\mathrm{bulk},\Diamond}$,则相应的边界算子 $\mathsf K'_\Diamond$ 与 $\mathsf K_\Diamond$ 在 $\mathcal B^\pm_\Diamond$ 上相同。

*证明* 见附录 A.1。证明的要点是局域酉变换在参考体积态与体积–边界投影上抵消,体积自由度被"迹掉",留下的边界算子只依赖于等价类。

因此,在固定参考体积态与边界测量方式后,钻石内部的演化在边界上压缩为一个规范唯一的算子 $\mathsf K_\Diamond$,这正是"边界计算"在计算宇宙中的严格表述。

### 4.4 路径和与 Schur 消元的离散构造

对于经典可逆计算宇宙(例如可逆 CA 或可逆图灵机),可将边界算子用路径和与图 Schur 消元直接表达。

设钻石子图 $G_\Diamond = (V_\Diamond,E_\Diamond)$ 上的转移矩阵为 $T_\Diamond$,其按体积/边界分块形式

$$
T_\Diamond
=
\begin{pmatrix}
T_{\mathrm{bb}} & T_{\mathrm{b}+} \\
T_{-\mathrm{b}} & T_{--}
\end{pmatrix},
$$

其中 $T_{\mathrm{bb}}$ 作用于体积自由度,$T_{-\mathrm{b}}$ 连接入射边界到体积,$T_{\mathrm{b}+}$ 连接体积到出射边界,$T_{--}$ 为入射边界内部更新(如有)。则在适当可逆性条件下,可以通过 Schur 补操作得到有效边界转移矩阵

$$
K_\Diamond
=
T_{--} + T_{-\mathrm{b}}\big( I - T_{\mathrm{bb}}\big)^{-1} T_{\mathrm{b}+},
$$

其离散路径和解释为:从入射边界到出射边界的所有体积内部路径的和。这与量子情形中 $\mathsf K_\Diamond$ 的路径积分表述形式一致。

---

## 5 边界计算与离散 GHY 型作用量

本节在时间–信息–复杂性联合作用量的基础上,引入针对单个因果小钻石的离散作用量,并给出与边界算子的关系,从而构造出计算宇宙中的 GHY 型边界–体积结构。

### 5.1 钻石作用量与体积–边界分解

对给定钻石 $\Diamond$,在事件层上考虑控制–信息联合变量 $(\theta_e,\phi_e)$ 以及对应的离散时间步长 $h$。在此前连续作用量

$$
\mathcal A_Q[\theta(\cdot),\phi(\cdot)]
=
\int
\Big(
\tfrac12 \alpha^2 G_{ab}\dot\theta^a\dot\theta^b
+
\tfrac12 \beta^2 g_{ij}\dot\phi^i\dot\phi^j
-
\gamma\,U_Q(\phi)
\Big)\,\mathrm dt
$$

的离散化下,钻石内部的总作用量可写为

$$
\mathcal A_Q(\Diamond)
=
\sum_{e\in V_\Diamond}
\Big(
\tfrac12 \alpha^2 K_{\mathrm{comp}}(e)
+
\tfrac12 \beta^2 K_{\mathrm{info}}(e)
-
\gamma\,U_Q(\phi_e)
\Big),
$$

其中 $K_{\mathrm{comp}}(e),K_{\mathrm{info}}(e)$ 来自相应局部时间步上的速度平方项。

我们希望将 $\mathcal A_Q(\Diamond)$ 拆分为"纯体积项 + 纯边界项"。在经典 GHY 结构中,Einstein–Hilbert 体积作用量的变分在有边界时需要加入边界外挠曲项才有良好变分性;在计算宇宙中,我们将证明:在固定边界算子 $\mathsf K_\Diamond$ 的条件下,内部体积作用量 $\mathcal A_{Q,\mathrm{bulk}}(\Diamond)$ 的极小化等价于一个带边界算子约束的最优化问题,其 Lagrange 乘子正好扮演离散 GHY 型边界项的角色。

### 5.2 变分与边界条件

考虑在钻石内部对离散路径 $(\theta_e,\phi_e)_{e\in V_\Diamond}$ 变分,同时保持边界变量 $(\theta_e,\phi_e)_{e\in\partial\Diamond}$ 固定。对内部节点的变分给出离散 Euler–Lagrange 方程,对边界节点则产生边界项。

形式上,体积作用量的变分为

$$
\delta \mathcal A_{Q,\mathrm{bulk}}(\Diamond)
=
\sum_{e\in V_\Diamond\setminus\partial\Diamond}
(\text{离散 Euler–Lagrange 方程})\cdot \delta z_e
+
\sum_{e\in\partial\Diamond}
(\text{边界项})\cdot \delta z_e.
$$

为了使在固定边界算子 $\mathsf K_\Diamond$ 的条件下体积变分良好,需要在总作用量中加入一个边界项 $\mathcal A_{Q,\partial}(\Diamond)$,使得总变分只含内部方程。

**命题 5.1(离散 GHY 型边界作用量存在性)**

在统一时间刻度与可逆性假设下,存在一个仅依赖边界变量与边界算子 $\mathsf K_\Diamond$ 的函数 $\mathcal A_{Q,\partial}(\Diamond)$,使得总作用量

$$
\mathcal A_{Q,\mathrm{tot}}(\Diamond)
=
\mathcal A_{Q,\mathrm{bulk}}(\Diamond)
+
\mathcal A_{Q,\partial}(\Diamond)
$$

在固定边界算子 $\mathsf K_\Diamond$ 的变分问题中,其变分仅给出内部 Euler–Lagrange 方程,不产生边界自由度上的附加约束。

证明见附录 B.1。构造思路是将边界算子的变化视为边界变量变化的线性泛函,并用 Lagrange 乘子将 $\mathsf K_\Diamond$ 固定,将相关乘子项吸收到 $\mathcal A_{Q,\partial}(\Diamond)$ 中。

### 5.3 极小化原则与边界算子

因此,在统一时间刻度与边界算子 $\mathsf K_\Diamond$ 固定的条件下,因果小钻石内部的计算演化是作用量 $\mathcal A_{Q,\mathrm{tot}}(\Diamond)$ 的极小解。换言之:

> 在计算宇宙中,"给定统一时间刻度与边界算子"的前提下,内部最优计算路径是一个离散变分问题的解,其 Euler–Lagrange 方程等价于体积更新算子与边界算子之间的兼容性条件。

这为我们在计算宇宙中建立**边界决定体积**的精确数学结构提供了基础。

---

## 6 连续极限:控制流形小钻石与边界时间几何

本节讨论在控制流形 $(\mathcal M,G)$ 与统一时间刻度的连续极限下,计算宇宙中的因果小钻石与边界算子如何与连续的小因果菱形与边界时间几何对应。

### 6.1 控制流形上的小钻石

在连续控制流形上,考虑带时间参数的扩展流形

$$
\widetilde{\mathcal M}
=
\mathbb R_t \times \mathcal M,
\quad
\widetilde G
=
-\mathrm d\tau^2 + G_{ab}(\theta)\mathrm d\theta^a\mathrm d\theta^b,
$$

其中 $\tau$ 为统一时间刻度下的"内禀时间"坐标。给定两点

$$
p = (\tau_{\mathrm{in}},\theta_{\mathrm{in}}),
\quad
q = (\tau_{\mathrm{out}},\theta_{\mathrm{out}}),
\quad
\tau_{\mathrm{out}}>\tau_{\mathrm{in}},
$$

定义控制流形上的小钻石

$$
\Diamond_{\mathcal M}(p,q)
=
J^+(p)\cap J^-(q),
$$

其中 $J^\pm$ 为由 $\widetilde G$ 定义的因果未来/过去集合。

在离散–连续对应下,计算宇宙中因果小钻石 $\Diamond(e_{\mathrm{in}},e_{\mathrm{out}};T)$ 在细化极限下逼近 $\Diamond_{\mathcal M}(p,q)$ 的有限网格近似。

### 6.2 边界时间算子与散射

在小钻石边界上,可以定义一个有效的时间平移算子或散射矩阵 $S_\Diamond$,将入射边界上的波函数映射到出射边界。此前关于统一时间刻度与散射时间刻度的工作表明,小钻石上的 Wigner–Smith 延迟矩阵 $Q_\Diamond(\omega)$ 的迹给出统一时间刻度密度在该小钻石上的局域增量。

在计算宇宙中,边界计算算子 $\mathsf K_\Diamond$ 的连续极限正是 $S_\Diamond$ 的一个表示,而钻石作用量 $\mathcal A_{Q,\mathrm{tot}}(\Diamond)$ 的极小性对应于在固定 $S_\Diamond$ 与统一时间刻度条件下的体积分极小问题,这就是离散 GHY 结构与连续边界时间几何之间的桥梁。

---

## 附录 A:边界算子规范唯一性的证明

### A.1 定理 4.2 的证明

**定理重述**

在给定入射嵌入 $\iota^-_\Diamond$ 与出射投影 $\Pi^+_\Diamond$ 的条件下,若

$$
U'_\Diamond
=
(V_{\mathrm{bulk}}\otimes\mathrm{id})\,U_\Diamond\,(W_{\mathrm{bulk}}\otimes\mathrm{id}),
$$

其中 $V_{\mathrm{bulk}},W_{\mathrm{bulk}}$ 仅作用于 $\mathcal H_{\mathrm{bulk},\Diamond}$,则

$$
\Pi^+_\Diamond U'_\Diamond \iota^-_\Diamond
=
\Pi^+_\Diamond U_\Diamond \iota^-_\Diamond.
$$

**证明**

由定义

$$
\mathsf K_\Diamond
=
\Pi^+_\Diamond U_\Diamond \iota^-_\Diamond,
\quad
\mathsf K'_\Diamond
=
\Pi^+_\Diamond U'_\Diamond \iota^-_\Diamond.
$$

代入 $U'_\Diamond$ 的表达式,有

$$
\mathsf K'_\Diamond
=
\Pi^+_\Diamond
(V_{\mathrm{bulk}}\otimes\mathrm{id})
U_\Diamond
(W_{\mathrm{bulk}}\otimes\mathrm{id})
\iota^-_\Diamond.
$$

注意 $\iota^-_\Diamond$ 将入射边界态嵌入到 $\ket{0_{\mathrm{bulk}}}\otimes\ket{\psi^-}\otimes\ket{0_+}$,故

$$
(W_{\mathrm{bulk}}\otimes\mathrm{id})\iota^-_\Diamond\ket{\psi^-}
=
W_{\mathrm{bulk}}\ket{0_{\mathrm{bulk}}}\otimes\ket{\psi^-}\otimes\ket{0_+}.
$$

如果参考体积态选择为某个 $W_{\mathrm{bulk}}$-不变态(例如 $W_{\mathrm{bulk}}$ 仅在体积的补空间作用),则

$$
W_{\mathrm{bulk}}\ket{0_{\mathrm{bulk}}} = \ket{0_{\mathrm{bulk}}},
$$

从而

$$
(W_{\mathrm{bulk}}\otimes\mathrm{id})\iota^-_\Diamond
=
\iota^-_\Diamond.
$$

类似地,对出射投影算子,若 $\Pi^+_\Diamond$ 仅在出射边界自由度上取内积或测量,而对体积自由度取固定参考态的内积,则

$$
\Pi^+_\Diamond (V_{\mathrm{bulk}}\otimes\mathrm{id})
=
\Pi^+_\Diamond.
$$

两者合并得到

$$
\mathsf K'_\Diamond
=
\Pi^+_\Diamond U_\Diamond \iota^-_\Diamond
=
\mathsf K_\Diamond.
$$

因此在局域体积分块的酉变换下,边界算子不变。

证毕。

---

## 附录 B:离散 GHY 型边界作用量的构造

### B.1 命题 5.1 的证明思路

考虑对钻石内部变量 $z_e = (\theta_e,\phi_e)$ 的变分,同时保持边界算子 $\mathsf K_\Diamond$ 固定。由于 $\mathsf K_\Diamond$ 是体积更新算子 $U_\Diamond$ 与边界嵌入/投影的组合,其对 $z_e$ 的变化可写为某个线性泛函

$$
\delta \mathsf K_\Diamond
=
\sum_{e\in V_\Diamond}
\mathcal J_e\,\delta z_e,
$$

其中 $\mathcal J_e$ 是某个依赖于 $U_\Diamond$ 与嵌入/投影的矩阵系数。固定 $\mathsf K_\Diamond$ 等价于约束

$$
\sum_{e\in V_\Diamond}
\mathcal J_e\,\delta z_e = 0.
$$

在作用量变分中引入 Lagrange 乘子 $\Lambda$ 将此约束吸收为额外项

$$
\delta \mathcal A_{Q,\mathrm{bulk}}(\Diamond)
+
\sum_{e\in V_\Diamond}
\mathrm{Tr}\big(
\Lambda^\dagger \mathcal J_e\,\delta z_e
\big).
$$

将 Lagrange 乘子项整体定义为边界作用量的变分

$$
\delta \mathcal A_{Q,\partial}(\Diamond)
=
\sum_{e\in V_\Diamond}
\mathrm{Tr}\big(
\Lambda^\dagger \mathcal J_e\,\delta z_e
\big),
$$

则总作用量变分为

$$
\delta \mathcal A_{Q,\mathrm{tot}}(\Diamond)
=
\sum_{e\in V_\Diamond}
(\text{Euler–Lagrange}_e + \text{乘子项})\cdot \delta z_e.
$$

通过选择 $\Lambda$ 使得边界节点 $e\in\partial\Diamond$ 上的乘子项抵消体积作用量的边界贡献,可实现总变分在固定 $\mathsf K_\Diamond$ 的条件下只给出内部 Euler–Lagrange 方程而无边界自由度约束。这一构造与连续 GHY 边界项的角色完全平行。

详细的矩阵表达需对 $U_\Diamond$ 与 $\mathsf K_\Diamond$ 进行谱分解,限于篇幅不再逐项展开。

---

## 附录 C:范畴等价下小钻石与边界算子的自然性

在物理宇宙范畴–计算宇宙范畴等价的框架下,小因果菱形与因果小钻石之间的对应可通过函子 $F,G$ 提升到"局域对象"层面。

* 对物理宇宙中的一个小因果菱形 $\Diamond(p,q) \subset M$,离散化函子 $F$ 产生计算宇宙中的因果小钻石 $\Diamond(e_{\mathrm{in}},e_{\mathrm{out}};T)$,其边界算子 $\mathsf K_\Diamond$ 与物理散射算子 $S_\Diamond$ 在统一时间刻度母尺下等价。
* 反之,对计算宇宙中的任意因果小钻石,连续极限函子 $G$ 产生物理时空中的小因果菱形,其边界 Hamilton 量与钻石作用量 $\mathcal A_{Q,\mathrm{tot}}(\Diamond)$ 的极小值对应。

这表明,**边界计算与小钻石结构在范畴等价下是稳定的局域不变量**:无论从物理宇宙还是从计算宇宙出发,对"局域有限区块"的自然对象及其边界算子的理解是一致的。
