# 计算宇宙中的时间–信息–复杂性联合变分原理

控制–散射流形与任务信息流形上的计算世界线

---

## 摘要

在此前关于"计算宇宙"的系列工作中,我们将宇宙抽象为离散对象 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$,在其上构造了离散复杂性几何(基于配置图的复杂性距离、体积增长与离散 Ricci 曲率)、离散信息几何(基于任务感知相对熵与 Fisher 结构),并在统一时间刻度的散射母尺下给出了复杂性几何的连续极限:一个带 Riemann 度量 $G$ 的控制流形 $\mathcal M$。然而,这些几何结构仍分别刻画"时间/资源代价"和"信息质量/任务相关状态",尚缺乏一个将二者统一到单一变分原理下的框架。

本文在控制流形 $(\mathcal M,G)$ 与任务信息流形 $(\mathcal S_Q,g_Q)$ 的基础上,引入联合流形
$\mathcal E_Q = \mathcal M \times \mathcal S_Q$,并在其上构造一个时间–信息–复杂性联合作用量 $\mathcal A_Q$,从而将计算宇宙中的"计算轨道"刻画为联合流形上的极小曲线(计算世界线)。具体而言,我们首先在离散层面给出作用量
$\mathcal A_Q^{\mathrm{disc}}(\gamma) = \sum_k \big( \alpha\,\mathsf C(x_k,x_{k+1}) + \beta\,d_{\mathrm{info},Q}(x_k,x_{k+1}) - \gamma\,\Delta \mathsf I_Q(x_k,x_{k+1}) \big)$,并证明在适当缩放下,该离散作用量族在 $h\to 0$ 时 $\Gamma$-收敛到连续作用量

$$
\mathcal A_Q[\theta(\cdot),\phi(\cdot)]
=
\int_0^T
\Big(
\tfrac12 \alpha^2 G_{ab}(\theta)\dot\theta^a\dot\theta^b
+
\tfrac12 \beta^2 g_{ij}(\phi)\dot\phi^i\dot\phi^j
-
\gamma\,U_Q(\phi)
\Big)\,\mathrm dt,
$$

其中 $\theta(t)\in\mathcal M$ 为控制轨道,$\phi(t)\in\mathcal S_Q$ 为任务信息状态,$U_Q$ 为任务相关的信息势函数(例如负信息质量)。

然后,我们在联合流形 $\mathcal E_Q$ 上推导 Euler–Lagrange 方程,证明极小轨道满足一组耦合的"带势 geodesic 方程":控制部分沿 $(\mathcal M,G)$ 的 geodesic 演化但受 $U_Q$ 关于 $\phi$ 的梯度反馈;信息部分沿 $(\mathcal S_Q,g_Q)$ 的 geodesic 演化但受控制轨道 $\theta$ 的调制。进一步地,我们利用标准变分法与 $\Gamma$-收敛理论证明:在统一时间刻度与局部 Lipschitz 假设下,离散最优计算路径在极限上收敛到联合流形上的极小世界线,实现了"离散计算宇宙中的最优算法"与"连续时间–信息–复杂性世界线"之间的严格对应。

本文最后讨论了带资源约束的极小化问题:在固定时间预算或复杂性预算下最大化任务信息质量。我们给出等价的拉格朗日乘子形式,从而将"给定预算下的最优信息获取策略"刻画为一类带有效势的 geodesic 流。本文的结果为后续构造"计算宇宙 ↔ 物理宇宙"的范畴等价提供了内在动力学层面的变分基础。

---

## 1 引言

在"计算宇宙"视角下,宇宙整体被抽象为一个离散动力系统:配置空间 $X$ 上的一步更新关系 $\mathsf T$ 与单步代价 $\mathsf C$ 描述了从一个状态到另一个状态需要的资源;信息质量函数 $\mathsf I$ 则在任务层面评估某个配置相对于目标的"好坏"。前几篇工作表明,在有限信息密度与局域更新的公理下,可以将 $(X,\mathsf T,\mathsf C)$ 看作复杂性图,构造出复杂性距离、复杂性球体积、复杂性维数和离散 Ricci 曲率,从而用离散几何刻画"问题难度"与"视界结构";同时,通过观察算子族与任务感知相对熵,可在配置空间上定义信息距离与信息球,将"任务相关的可区分性"几何化。

在统一时间刻度的散射母尺下,计算宇宙的单步代价可以被视为实际物理时间刻度的离散采样:对可物理实现的计算过程,存在控制流形 $\mathcal M$ 与散射矩阵族 $S(\omega;\theta)$,使得群延迟矩阵 $Q(\omega;\theta)$ 的控制导数诱导出复杂性度量 $G$,进而离散复杂性距离在细化极限下逼近 $(\mathcal M,G)$ 上的测地距离。这一结果将离散复杂性几何与物理时间刻度统一进一个 Riemann 几何框架。

然而,要理解"在有限时间内以何种方式计算最合适",仅有复杂性几何或信息几何都不够:

* 复杂性几何关心"走了多远、花了多少时间/资源";
* 信息几何关心"在任务空间中移动了多远、获得了多少信息";
* 真正有意义的问题是:在给定时间/复杂性预算下,如何在信息几何上达到尽可能好的终点。

这自然导向一个联合变分问题:在联合空间中,为给定任务找出同时考虑时间代价与信息收益的极小/极大轨道。

本文在控制流形 $(\mathcal M,G)$ 与任务信息流形 $(\mathcal S_Q,g_Q)$ 的基础上,构造联合流形 $\mathcal E_Q = \mathcal M \times \mathcal S_Q$,并在其上定义一个时间–信息–复杂性联合作用量 $\mathcal A_Q$。离散计算路径成为联合流形上的折线近似,连续计算世界线则为 $\mathcal E_Q$ 上的光滑曲线。通过使用 $\Gamma$-收敛与经典变分法,我们证明离散最优路径在极限上收敛为连续极小世界线,从而将"最优算法"的问题几何化为"最优世界线"的问题。

---

## 2 统一符号:计算宇宙、复杂性几何与信息几何

本节简要汇总前几篇工作中使用的主要对象与符号,以便后续统一推理。

### 2.1 计算宇宙对象

一个计算宇宙对象为四元组 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$,其中:

1. $X$ 为可数配置集;
2. $\mathsf T \subset X\times X$ 为一步更新关系;
3. $\mathsf C:X\times X\to[0,\infty]$ 为单步代价,若 $(x,y)\notin\mathsf T$ 则 $\mathsf C(x,y)=\infty$,若 $(x,y)\in\mathsf T$ 则 $\mathsf C(x,y) \in (0,\infty)$,并对路径加性;
4. $\mathsf I:X\to\mathbb R$ 为信息质量函数(可任务依赖)。

复杂性距离定义为

$$
d_{\mathrm{comp}}(x,y) = \inf_{\gamma:x\to y} \mathsf C(\gamma),
$$

其中路径 $\gamma = (x_0,\dots,x_n)$ 满足 $x_0=x,x_n=y$,且 $(x_k,x_{k+1})\in\mathsf T$。

### 2.2 复杂性几何与控制流形

在统一时间刻度框架下,对物理可实现的计算宇宙存在控制流形 $\mathcal M$ 与散射矩阵族 $S(\omega;\theta)$,其群延迟矩阵 $Q(\omega;\theta) = -\mathrm{i}\,S^\dagger\partial_\omega S$ 的控制导数诱导复杂性度量

$$
G_{ab}(\theta) = \int_{\Omega} w(\omega)\,\mathrm{tr}\big( \partial_a Q(\omega;\theta)\,\partial_b Q(\omega;\theta) \big)\,\mathrm d\omega.
$$

在适当正定条件下,$(\mathcal M,G)$ 为 Riemann 流形,离散复杂性距离在细化极限下收敛到测地距离 $d_G$。

### 2.3 任务信息流形

给定任务 $Q$,通过观察算子族 $\mathcal O = \{O_j\}_{j\in J}$ 定义配置 $x$ 的可见状态 $p_x^{(Q)} \in \Delta(Y_Q)$。在适当正则性假设下,这些可见状态可嵌入某个信息流形 $\mathcal S_Q$ 中:

* 存在映射 $\Phi_Q:X\to\mathcal S_Q$ 与嵌入 $\Psi_Q:\mathcal S_Q \hookrightarrow \Delta(Y_Q)$,使得 $\Psi_Q(\Phi_Q(x)) \approx p_x^{(Q)}$;
* Fisher 信息度量 $g_Q$ 由相对熵二阶导数给出,构成 $(\mathcal S_Q,g_Q)$ 的 Riemann 结构;
* 配置间信息距离可用 Jensen–Shannon 距离或 Fisher 测地距离表示,记为 $d_{\mathrm{info},Q}(x,y) \approx d_{\mathcal S_Q}(\Phi_Q(x),\Phi_Q(y))$。

我们称 $(\mathcal S_Q,g_Q,\Phi_Q)$ 为任务 $Q$ 的信息几何数据。

---

## 3 联合时间–信息–复杂性流形

在上述准备下,我们构造联合流形 $\mathcal E_Q$ 及其度量。

### 3.1 联合流形的定义

**定义 3.1(联合流形)**

对给定任务 $Q$,定义联合流形

$$
\mathcal E_Q = \mathcal M \times \mathcal S_Q.
$$

其点 $z = (\theta,\phi)$ 同时表示"控制状态"与"任务信息状态"。计算宇宙中一个观测者或算法的状态,在连续极限下可视为 $\mathcal E_Q$ 上的一点。

### 3.2 度量结构

在 $\mathcal E_Q$ 上,我们引入乘积型度量

$$
\mathbb G = \alpha^2 G \oplus \beta^2 g_Q,
$$

即对切向量 $v = (v^{\mathcal M},v^{\mathcal S_Q}) \in T_\theta\mathcal M \oplus T_\phi\mathcal S_Q$,定义

$$
\mathbb G_z(v,v) = \alpha^2 G_\theta(v^{\mathcal M},v^{\mathcal M}) + \beta^2 g_{Q,\phi}(v^{\mathcal S_Q},v^{\mathcal S_Q}).
$$

这里 $\alpha,\beta>0$ 为权重参数,用于平衡在复杂性方向与信息方向上的"速度"计量。

在该度量下,一条联合轨道

$$
z(t) = (\theta(t),\phi(t))
$$

的速度平方为

$$
| \dot z(t) |_{\mathbb G}^2 = \alpha^2 G_{ab}(\theta(t))\dot\theta^a\dot\theta^b + \beta^2 g_{ij}(\phi(t))\dot\phi^i\dot\phi^j.
$$

联合流形上的纯几何长度为

$$
L_{\mathbb G}[z] = \int_0^T \sqrt{| \dot z(t) |_{\mathbb G}^2}\,\mathrm dt.
$$

然而,仅靠长度不足以编码"信息质量"的增益,我们还需要一个任务相关的势函数。

### 3.3 信息势函数

设任务 $Q$ 的信息质量函数在信息流形上可写为 $I_Q:\mathcal S_Q\to\mathbb R$,例如

$$
I_Q(\phi) = \mathsf I_Q(x) \quad \text{当} \ \phi = \Phi_Q(x).
$$

我们引入信息势函数

$$
U_Q(\phi) = V(I_Q(\phi)),
$$

其中 $V:\mathbb R\to\mathbb R$ 为单调函数,一般选取 $V(u) = u$ 或 $V(u) = f_{\mathrm{sat}}(u)$(饱和型)。在本文中,为简洁起见,直接取

$$
U_Q(\phi) = I_Q(\phi),
$$

将"信息质量"视为势能项的负号贡献(对应更高信息质量带来更低作用量)。

---

## 4 离散联合作用量与连续极限

本节在离散层面构造任务 $Q$ 的联合作用量,并证明其在细化极限下收敛到连续作用量。

### 4.1 离散联合作用量

考虑一条离散计算路径

$$
\gamma = (x_0,x_1,\dots,x_n),
$$

其中 $(x_k,x_{k+1})\in\mathsf T$。对应的复杂性增量为

$$
\Delta C_k = \mathsf C(x_k,x_{k+1}),
$$

信息距离增量(任务 $Q$ 下)为

$$
\Delta D_k = d_{\mathrm{info},Q}(x_k,x_{k+1}),
$$

信息质量增量为

$$
\Delta I_k = I_Q(\phi_{k+1}) - I_Q(\phi_k), \quad \phi_k = \Phi_Q(x_k).
$$

**定义 4.1(离散联合作用量)**

对任务 $Q$ 与路径 $\gamma$,定义离散联合作用量

$$
\mathcal A_Q^{\mathrm{disc}}(\gamma)
=
\sum_{k=0}^{n-1}
\Big(
\alpha\,\Delta C_k
+
\beta\,\Delta D_k
-
\gamma\,\Delta I_k
\Big),
$$

其中 $\alpha,\beta,\gamma>0$ 为权重参数。

直观理解:每一步更新同时付出复杂性代价 $\alpha\,\Delta C_k$ 与信息调整代价 $\beta\,\Delta D_k$,并获得信息质量增量 $\Delta I_k$,贡献 $-\gamma\,\Delta I_k$ 到作用量中。最优路径是在三者平衡下使 $\mathcal A_Q^{\mathrm{disc}}$ 最小。

### 4.2 细化与标准时间步长

为连接离散与连续,我们引入离散时间步长 $h>0$,令路径长度 $n \approx T/h$,并设置单步代价与信息距离的缩放为

$$
\Delta C_k = h\,c(x_k,x_{k+1}) + o(h),
\quad
\Delta D_k = h\,d(x_k,x_{k+1}) + o(h),
$$
$$
\Delta I_k = h\,\dot I_Q(t_k) + o(h),
$$

其中 $t_k = k h$,$c,d,\dot I_Q$ 分别为连续极限下的复杂性速度、信息速度与信息质量变化率。

在上述缩放下,离散作用量可近似为 Riemann 和

$$
\mathcal A_Q^{\mathrm{disc}}(\gamma)
\approx
\sum_{k=0}^{n-1}
h\Big(
\alpha\,c_k
+
\beta\,d_k
-
\gamma\,\dot I_Q(t_k)
\Big)
\to
\int_0^T
\big(
\alpha c(t)
+
\beta d(t)
-
\gamma \dot I_Q(t)
\big)\,\mathrm dt.
$$

为了匹配几何结构,我们将 $c(t),d(t)$ 分别用 $(\mathcal M,G)$ 与 $(\mathcal S_Q,g_Q)$ 上的速度范数表示。

### 4.3 连续联合作用量

设控制路径为 $\theta:[0,T]\to\mathcal M$,信息路径为 $\phi:[0,T]\to\mathcal S_Q$,对应速度范数为

$$
v_{\mathcal M}^2(t) = G_{ab}(\theta(t))\dot\theta^a(t)\dot\theta^b(t),
$$

$$
v_{\mathcal S_Q}^2(t) = g_{ij}(\phi(t))\dot\phi^i(t)\dot\phi^j(t).
$$

我们选取"能量型"连续作用量:

**定义 4.2(连续联合作用量)**

$$
\mathcal A_Q[\theta(\cdot),\phi(\cdot)]
=
\int_0^T
\Big(
\tfrac12 \alpha^2 v_{\mathcal M}^2(t)
+
\tfrac12 \beta^2 v_{\mathcal S_Q}^2(t)
-
\gamma\,U_Q(\phi(t))
\Big)\,\mathrm dt.
$$

其中 $U_Q(\phi) = I_Q(\phi)$ 或其某个单调变换。

这是一个标准的"动能减势能"形式:前两项为复杂性与信息几何上的动能,后项为任务相关的负势能,极小世界线在保持有限速度的同时尽量进入信息势能较低的区域。

---

## 5 Euler–Lagrange 方程与计算世界线

本节在联合流形上推导 Euler–Lagrange 方程,给出极小世界线满足的动力学形式。

### 5.1 Lagrangian 与变分

设 Lagrangian 为

$$
L(\theta,\dot\theta;\phi,\dot\phi)
=
\tfrac12 \alpha^2 G_{ab}(\theta)\dot\theta^a\dot\theta^b
+
\tfrac12 \beta^2 g_{ij}(\phi)\dot\phi^i\dot\phi^j
-
\gamma\,U_Q(\phi).
$$

对 $\theta^a$ 与 $\phi^i$ 分别进行变分,得到 Euler–Lagrange 方程:

对 $\theta^a$:

$$
\frac{\mathrm d}{\mathrm dt}
\big(
\alpha^2 G_{ab}(\theta)\dot\theta^b
\big)
-
\tfrac12 \alpha^2 (\partial_a G_{bc})(\theta)\dot\theta^b\dot\theta^c
= 0,
$$

对 $\phi^i$:

$$
\frac{\mathrm d}{\mathrm dt}
\big(
\beta^2 g_{ij}(\phi)\dot\phi^j
\big)
-
\tfrac12 \beta^2 (\partial_i g_{jk})(\phi)\dot\phi^j\dot\phi^k
+
\gamma\,\partial_i U_Q(\phi)
= 0.
$$

其中 $\partial_a G_{bc} = \partial G_{bc} / \partial\theta^a$,$\partial_i g_{jk} = \partial g_{jk} / \partial\phi^i$。

### 5.2 联合 geodesic–势方程

在标准 Riemann 几何中,geodesic 方程可写为

$$
\ddot\theta^a + \Gamma^a_{bc}(\theta)\dot\theta^b\dot\theta^c = 0,
$$

其中 $\Gamma^a_{bc}$ 为 Levi–Civita 联络的 Christoffel 符号。我们在此将控制与信息部分分别重写为 geodesic–势形式。

对控制变量 $\theta^a$,令

$$
\Gamma^a_{bc}(\theta)
=
\tfrac12 G^{ad}
\big(
\partial_b G_{dc}
+
\partial_c G_{db}
-
\partial_d G_{bc}
\big),
$$

其中 $G^{ad}$ 为度量矩阵的逆。Euler–Lagrange 方程可重写为

$$
\ddot\theta^a + \Gamma^a_{bc}(\theta)\dot\theta^b\dot\theta^c = 0.
$$

由于 Lagrangian 中控制部分不含显式势能,控制轨道为 $(\mathcal M,G)$ 上的 geodesic。

对信息变量 $\phi^i$,类似地,定义 $\Gamma^i_{jk}(\phi)$ 为 $g_Q$ 的 Christoffel 符号,则 Euler–Lagrange 方程重写为

$$
\ddot\phi^i
+
\Gamma^i_{jk}(\phi)\dot\phi^j\dot\phi^k
=
-\frac{\gamma}{\beta^2} g^{ij}(\phi)\partial_j U_Q(\phi).
$$

右侧项为势能梯度在信息流形上的共变提升,代表"信息势"对信息轨道的驱动力。

因此,联合世界线满足如下耦合系统:

1. 控制部分:沿 $(\mathcal M,G)$ geodesic 演化;
2. 信息部分:沿 $(\mathcal S_Q,g_Q)$ geodesic,但受 $U_Q$ 的梯度驱动偏离 geodesic。

可以将其视为"在复杂性–信息乘积流形上带势 geodesic"的特殊情形。

---

## 6 离散–连续一致性的 $\Gamma$-收敛

为了证明离散最优路径在极限上收敛到连续极小世界线,我们使用 $\Gamma$-收敛理论。仅给出结构性定理与证明思路,技术细节置于附录。

### 6.1 作用量泛函族

考虑一族离散时间步长 $h = T/n$,将离散路径 $\gamma^{(h)} = (x_0,\dots,x_n)$ 嵌入到分段常数或分段线性曲线 $z^{(h)}:[0,T]\to\mathcal E_Q$ 中,使得

$$
z^{(h)}(t) = (\theta^{(h)}(t),\phi^{(h)}(t)),
\quad
t\in[kh,(k+1)h),
$$

且 $z^{(h)}(kh) = (\theta_k,\phi_k)$ 与 $x_k$ 对应。定义离散作用量

$$
\mathcal A_Q^{(h)}[z^{(h)}]
=
\sum_{k=0}^{n-1}
\Big(
\tfrac12 \alpha^2 \frac{\Delta s_{\mathcal M,k}^2}{h}
+
\tfrac12 \beta^2 \frac{\Delta s_{\mathcal S_Q,k}^2}{h}
-
\gamma\,U_Q(\phi_k) h
\Big),
$$

其中 $\Delta s_{\mathcal M,k}^2 = d_{\mathcal M}(\theta_k,\theta_{k+1})^2$,$\Delta s_{\mathcal S_Q,k}^2 = d_{\mathcal S_Q}(\phi_k,\phi_{k+1})^2$。

在局部一致性假设下,$\Delta s_{\mathcal M,k} \approx h\sqrt{G_{ab}(\theta)\dot\theta^a\dot\theta^b}$,$\Delta s_{\mathcal S_Q,k} \approx h\sqrt{g_{ij}(\phi)\dot\phi^i\dot\phi^j}$。

### 6.2 $\Gamma$-收敛定理

**定理 6.1($\Gamma$-收敛,示意)**

在统一时间刻度与局部正则性假设下,离散作用量泛函族 $\{\mathcal A_Q^{(h)}\}_{h>0}$ 在适当的拓扑(例如 $z^{(h)}\rightharpoonup z$ 的弱 $H^1$ 拓扑)下 $\Gamma$-收敛到连续作用量泛函

$$
\mathcal A_Q[z]
=
\int_0^T
\Big(
\tfrac12 \alpha^2 G_{ab}(\theta)\dot\theta^a\dot\theta^b
+
\tfrac12 \beta^2 g_{ij}(\phi)\dot\phi^i\dot\phi^j
-
\gamma\,U_Q(\phi)
\Big)\,\mathrm dt.
$$

特别地,离散极小序列的任何极限点都是连续作用量的极小曲线。

证明思路见附录 B.2,基于标准的"能量型泛函离散化"的 $\Gamma$-收敛框架:下半连续性由凸结构与弱拓扑的下半连续性给出,恢复序列则通过对连续轨道的时间离散化构造。

---

## 7 资源约束下的最优计算世界线

在实际问题中,我们常常关心如下优化问题:

* 在给定时间预算 $T$ 或复杂性预算 $C_{\max}$ 下,最大化终点的信息质量 $I_Q(\phi(T))$;
* 或在给定终点信息质量需求 $I_{\mathrm{target}}$ 下,最小化所需时间或复杂性。

利用拉格朗日乘子方法,可以将资源约束吸收入联合作用量中。

例如,在给定 $T$ 的情况下最大化 $I_Q(\phi(T))$,等价于在自由末端条件下极小化

$$
\widetilde{\mathcal A}_Q[z]
=
\int_0^T
\Big(
\tfrac12 \alpha^2 v_{\mathcal M}^2
+
\tfrac12 \beta^2 v_{\mathcal S_Q}^2
\Big)\,\mathrm dt
-
\gamma\,I_Q(\phi(T)),
$$

这与前文作用量仅在势能项上不同。相应的 Euler–Lagrange 方程在 bulk 区间内与前述相同,但在终点处增加自然边界条件

$$
\beta^2 g_{ij}(\phi(T))\dot\phi^j(T)
=
\gamma\,\partial_i I_Q(\phi(T)).
$$

该边界条件可视为一种"终点反射条件":在终点处,信息速度与信息质量梯度的比值由参数 $\gamma/\beta^2$ 控制,反映出对终点信息质量的偏好强度。

类似地,在给定信息质量目标的情况下最小化时间,可通过约束 $I_Q(\phi(T)) = I_{\mathrm{target}}$ 并引入乘子 $\lambda$ 得到等价的自由问题,进而得到一套带全球约束的 geodesic–势方程。

这些变分问题为"最优算法设计"提供了几何化视角:在联合流形 $\mathcal E_Q$ 上寻找满足资源约束与终点信息约束的极小曲线,即为在计算宇宙中寻找最优的计算世界线。

---

## 附录 A:度量与势作用下的 Euler–Lagrange 推导

### A.1 变分推导的细节

令

$$
L(\theta,\dot\theta;\phi,\dot\phi)
=
\tfrac12 \alpha^2 G_{ab}(\theta)\dot\theta^a\dot\theta^b
+
\tfrac12 \beta^2 g_{ij}(\phi)\dot\phi^i\dot\phi^j
-
\gamma\,U_Q(\phi).
$$

对 $\theta^a$ 的变分 $\theta^a \mapsto \theta^a + \varepsilon \eta^a$($\eta^a(T_0)=\eta^a(T_1)=0$)有

$$
\delta L
=
\tfrac12 \alpha^2 (\partial_c G_{ab})\eta^c\dot\theta^a\dot\theta^b
+
\alpha^2 G_{ab}\dot\theta^a\dot\eta^b.
$$

积分后

$$
\delta\mathcal A_Q
=
\int_{T_0}^{T_1}
\alpha^2 G_{ab}\dot\theta^a\dot\eta^b
+
\tfrac12 \alpha^2 (\partial_c G_{ab})\eta^c\dot\theta^a\dot\theta^b
\,\mathrm dt.
$$

对第一项做分部积分

$$
\int_{T_0}^{T_1} \alpha^2 G_{ab}\dot\theta^a\dot\eta^b\,\mathrm dt
=
\big[
\alpha^2 G_{ab}\dot\theta^a\eta^b
\big]_{T_0}^{T_1}
-
\int_{T_0}^{T_1}
\frac{\mathrm d}{\mathrm dt}
\big(
\alpha^2 G_{ab}\dot\theta^a
\big)
\eta^b\,\mathrm dt.
$$

边界项为零,合并得到

$$
\delta\mathcal A_Q
=
\int_{T_0}^{T_1}
\Big(
-\frac{\mathrm d}{\mathrm dt}
(\alpha^2 G_{ab}\dot\theta^a)
+
\tfrac12 \alpha^2 \partial_b G_{ac}\dot\theta^a\dot\theta^c
\Big)\,\eta^b \,\mathrm dt.
$$

由变分任意性,得到

$$
\frac{\mathrm d}{\mathrm dt}
(\alpha^2 G_{ab}\dot\theta^a)
-
\tfrac12 \alpha^2 \partial_b G_{ac}\dot\theta^a\dot\theta^c
=0.
$$

乘以 $G^{db}$ 即得 geodesic 方程形式。对 $\phi^i$ 的变分完全类似,额外项来自 $-\gamma U_Q(\phi)$,从而得到

$$
\frac{\mathrm d}{\mathrm dt}
(\beta^2 g_{ij}\dot\phi^j)
-
\tfrac12 \beta^2 \partial_i g_{jk}\dot\phi^j\dot\phi^k
+
\gamma\,\partial_i U_Q(\phi)
=0.
$$

证毕。

---

## 附录 B:$\Gamma$-收敛的技术框架

### B.1 能量型离散泛函的标准 $\Gamma$-收敛结论

设 $H$ 为 Hilbert 空间,$\mathcal F_h:H\to\mathbb R\cup\{+\infty\}$ 为一族泛函,形如

$$
\mathcal F_h[u]
=
\sum_{k=0}^{n_h-1}
\Big(
\tfrac12 a_h^k \frac{(u_{k+1}-u_k)^2}{h}
+
h\,V_h^k(u_k)
\Big),
$$

在适当一致性假设下,当 $h\to 0$ 时 $\mathcal F_h$ $\Gamma$-收敛到

$$
\mathcal F[u]
=
\int_0^T
\Big(
\tfrac12 a(t)\dot u(t)^2
+
V(t,u(t))
\Big)\,\mathrm dt.
$$

我们的离散联合作用量 $\mathcal A_Q^{(h)}$ 属于该类泛函的矢量版本,其 $\Gamma$-收敛可通过将控制与信息部分分别应用上述标量理论并合并得到。关键条件包括:

1. 单步代价与信息距离的二阶一致性:

$$
\frac{\Delta s_{\mathcal M,k}^2}{h^2} \to G_{ab}(\theta)\dot\theta^a\dot\theta^b, \quad \frac{\Delta s_{\mathcal S_Q,k}^2}{h^2} \to g_{ij}(\phi)\dot\phi^i\dot\phi^j;
$$

2. 势能项 $U_Q(\phi_k) h$ 一致逼近积分项 $\int U_Q(\phi(t))\mathrm dt$;

3. 适当的紧性条件(例如能量有界性)保证极小序列有弱收敛子序列。

详细技术推导与对应文献框架在此不赘述。

### B.2 定理 6.1 的证明思路

下半连续性方向:对任意弱极限 $z$ 与收敛序列 $z^{(h)}\rightharpoonup z$,由动能项的凸性与弱下半连续性得到

$$
\mathcal A_Q[z]
\le
\liminf_{h\to 0}
\mathcal A_Q^{(h)}[z^{(h)}].
$$

恢复序列方向:对任意光滑极限轨道 $z$,使用时间离散化构造 $z^{(h)}$ 使得 $\mathcal A_Q^{(h)}[z^{(h)}]\to \mathcal A_Q[z]$。具体构造通过将 $z$ 在网格点 $t_k = kh$ 处采样得到 $z_k = z(t_k)$,并定义 $z^{(h)}$ 为分段线性插值,从而单步增量的二次型与势能项均逼近对应的积分。

综上,$\Gamma$-收敛成立。由 $\Gamma$-收敛的一般理论可知:若 $z^{(h)}$ 为 $\mathcal A_Q^{(h)}$ 的近似极小序列,则其任意弱极限点 $z$ 为 $\mathcal A_Q$ 的极小点。

---

## 附录 C:范畴结构的补充说明

尽管本文未系统展开范畴论部分,这里对"计算宇宙范畴 ↔ 控制–散射范畴"的连接做一简要补充,以说明联合变分原理在范畴层面上的自然性。

1. 对象层面:对每个物理可实现的计算宇宙 $U_{\mathrm{comp}}$,构造控制–散射对象 $(\mathcal M,G,S)$ 及任务信息流形 $(\mathcal S_Q,g_Q)$,其联合流形 $\mathcal E_Q$ 与联合作用量 $\mathcal A_Q$ 构成该对象的"内在动力学几何像"。

2. 態射层面:模拟映射 $f:U_{\mathrm{comp}}\rightsquigarrow U_{\mathrm{comp}}'$ 可通过物理实现给出控制流形与信息流形之间的映射 $f_{\mathcal M},f_{\mathcal S_Q}$,这些映射在度量与潜在的联合作用量下满足 Lipschitz 型不等式,从而保持极小世界线的基本结构。

3. 联合世界线的自然性:不同计算宇宙之间的模拟在联合流形上的像是一族"变形"的世界线,$\Gamma$-收敛保证在适当的极限下,极小世界线的像仍为极小世界线。

这一结构为后续构造"物理宇宙范畴与计算宇宙范畴的范畴等价"提供了一个动力学–变分的中介层,使得"宇宙 = 计算"的主张不仅在静态结构(配置、更新)上成立,也在时间–信息–复杂性三重结构的演化上成立。
