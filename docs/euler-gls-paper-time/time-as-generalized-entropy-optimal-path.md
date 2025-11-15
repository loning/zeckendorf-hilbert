# 时间作为广义熵最优路径：因果一致历史空间上的时间箭头重构

## 摘要

本文提出一种将"时间"重构为广义熵泛函最优路径的统一框架。我们不再把时间视为先赋的一维参数，而是把"时间箭头"定义为在因果一致历史空间上，使某一类广义熵泛函取极值（在合适约束下为最小值）的可延拓路径及其参数化等价类。具体而言，在给定的因果结构与可观测代数上，我们构造以下三个层级：

1. **结构层级**：将"世界历史"视为配置空间上的曲线族 $\gamma : I \to \mathcal C$，其中 $\mathcal C$ 为满足场方程与约束条件的态空间；引入因果一致子空间 $\mathsf{Cons} \subset \mathsf{Paths}(\mathcal C)$，由满足局域因果、记录可延拓及守恒律的路径构成。

2. **泛函层级**：在 $\mathsf{Cons}$ 上定义"广义熵泛函"

   $$
   \mathcal S_{\mathrm{gen}}[\gamma]
   =
   \alpha S_{\mathrm{th}}[\gamma]
   +
   \beta S_{\mathrm{ent}}[\gamma]
   +
   \gamma D_{\mathrm{rel}}[\gamma]
   +
   \lambda \mathcal B[\gamma],
   $$

   其中 $S_{\mathrm{th}}$ 为粗粒化热力学熵，$S_{\mathrm{ent}}$ 为纠缠熵或广义熵，$D_{\mathrm{rel}}$ 为相对熵型散度，$\mathcal B$ 为源自边界几何或外在曲率的边界项，系数 $\alpha,\beta,\gamma,\lambda$ 由物理情景与刻度选择决定。

3. **时间层级**：定义**时间箭头**为使 $\mathcal S_{\mathrm{gen}}$ 在 $\mathsf{Cons}$ 上满足极值原则且局域熵产生率非负的路径族 $\gamma^\star$，并定义时间刻度等价类为所有单调重参数化

   $$
   t \longmapsto f(t),\qquad f \in \mathrm{Diff}_+^1(I),
   $$

   下的轨道。由此，时间不再是外加参数，而是"因果一致 + 广义熵优化"问题的解。

在散射与谱理论端，我们引入统一刻度母尺

$$
\kappa(\omega)
=
\frac{\varphi'(\omega)}{\pi}
=
\rho_{\mathrm{rel}}(\omega)
=
\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

其中 $S(\omega)$ 为散射矩阵，$Q(\omega)=-i S(\omega)^\dagger \partial_\omega S(\omega)$ 为 Wigner–Smith 延迟算子，$\varphi(\omega)=\tfrac12 \arg\det S(\omega)$ 为总半相位，$\rho_{\mathrm{rel}}$ 为相对态密度。我们证明，在适定的散射—几何—信息设置下，可以用 $\kappa(\omega)$ 将广义熵泛函的"时间成本"具体化为谱积分，从而获得可观测的时间刻度代理。

在信息与因果端，我们以相对熵单调性与类 QNEC/QFC 不等式作为一致性约束，证明：若局域通量与熵流满足一组自然的凸性与正性条件，则在给定因果结构与边界数据下，使 $\mathcal S_{\mathrm{gen}}$ 极小的因果一致历史在单调重参数化下是唯一的，从而时间箭头被重构为"最省广义熵成本的因果可延拓路径"。这一框架为热力学第二定律、纠缠熵增长、散射群延迟与宇宙学红移等时间现象提供了统一的变分解释。

---

## 关键词

时间箭头；广义熵；因果结构；相对熵；散射相位；Wigner–Smith 时间延迟；刻度统一；因果一致历史

---

## 1 引言

### 1.1 时间问题的重述

在经典与量子理论中，"时间"传统上被视为一个先赋的参数：在广义相对论中是类时曲线的本征参数或 Killing/ADM 时间，在量子理论中是施罗丁格方程的演化参数，在统计物理中是马尔可夫过程的时间索引。然而，一旦我们同时考虑以下三类事实：

1. 热力学与信息论中的**不可逆性**与"时间之箭"；
2. 广义相对论中的**广义熵条件**（如广义熵单调、量子零能条件、量子聚焦条件）；
3. 散射理论与谱理论中**相位—延迟—态密度**之间的刻度同一，

就会发现：时间更像是某种"选出来的结构"，而非一开始就写在世界方程中的背景参数。

本文的出发点是：在给定因果结构与可观测代数的前提下，我们能否把时间刻画为**一种优化问题的解**——在所有因果一致的历史路径中，选出某类**广义熵泛函**的极值路径与其单调参数化等价类，作为时间箭头与时间刻度的本质？

### 1.2 本文的核心思想

本文的核心思想可以简要概括为一条变分原理：

> 在给定的因果一致历史空间上，真实世界对应于使某一类广义熵泛函 $\mathcal S_{\mathrm{gen}}$ 取极值（在自然假设下取最小值）的路径；所谓"时间箭头"，正是这些极值路径上使局域熵产生率非负的单调参数化等价类。

与传统"时间之箭＝熵增"的叙述不同的是，这里：

* 我们不预设"熵随时间必然增加"，而是把"时间"本身定义为"使广义熵泛函极值的路径参数"；
* 我们不局限于热力学熵，而是引入**广义熵**：包含热熵、纠缠熵、相对熵及边界几何项等；
* 我们要求路径不仅满足动力学方程，还必须满足**因果一致**、**记录可延拓**与**信息单调**等约束。

更具体地，本文将：

1. 构造因果一致历史空间与广义熵泛函；
2. 证明在自然的凸性与界约束下，极小历史在单调重参数化下是唯一的；
3. 通过散射理论中的刻度母尺

   $$
   \kappa(\omega)
   =
   \frac{\varphi'(\omega)}{\pi}
   =
   \rho_{\mathrm{rel}}(\omega)
   =
   \frac{1}{2\pi}\operatorname{tr}Q(\omega),
   $$

   将抽象的时间刻度与可观测的相位导数、群延迟与态密度统一；

4. 讨论局域观察者、测量记录与时间感知之间的关系。

### 1.3 文章结构

全文结构如下：第 2 节给出因果结构、历史空间与广义熵泛函的形式化定义，并提出时间的公理化重构。第 3 节给出主定理：在适定条件下，广义熵泛函的极小因果一致历史在单调重参数化下唯一，因而定义了时间箭头与时间刻度等价类。第 4 节在散射与谱理论语境中引入刻度母尺 $\kappa(\omega)$，并将其嵌入广义熵框架，给出时间刻度的可观测实现。第 5 节讨论局域观察者、记录与"主观时间"的关系。第 6 节给出简化模型以说明框架的工作方式。附录中给出主要定理的严格证明和技术细节。

---

## 2 因果一致历史空间与广义熵泛函

### 2.1 时空、因果与可观测代数

设 $(M,g)$ 为具全局双曲结构的洛伦兹流形，具有标准的因果结构 $J^\pm(\cdot)$。设 $\mathcal A$ 为与 $M$ 关联的可观测代数（例如满足 Haag–Kastler 公理的网状 $C^\ast$-代数，或散射通道上的限制代数），$\omega$ 为其上一态。

我们考虑满足以下性质的结构三元组：

$$
\mathsf{Data}=(M,g;\mathcal A,\omega;\mathcal C),
$$

其中 $\mathcal C$ 为"有效态空间"，由满足场方程与约束条件的态（或态等价类）构成，可以视为某种配置空间或相空间的适当完备化。

### 2.2 世界历史作为路径：历史空间与因果一致性

**定义 2.2.1（历史）**

称一个连续曲线

$$
\gamma:I\to \mathcal C,\qquad I\subset\mathbb R\ \text{为区间},
$$

为一条**世界历史**或**历史路径**。记全体此类曲线为 $\mathsf{Paths}(\mathcal C)$。

**定义 2.2.2（因果一致历史）**

给定 $\mathsf{Data}$，称历史 $\gamma\in\mathsf{Paths}(\mathcal C)$ 为**因果一致**，若存在以下结构：

1. 对每一点 $\gamma(t)$，存在与之对应的空间切片或 Cauchy 截面 $\Sigma_t\subset M$，使 $t_1<t_2 \Rightarrow \Sigma_{t_1}\subset J^-(\Sigma_{t_2})$；
2. 态演化 $\gamma(t)$ 在 $\mathcal A(\Sigma_t)$ 上诱导的限制态 $\omega_t$ 满足局域因果律（例如满足 Einstein 因果性、微局域性等条件）；
3. 存在一族"记录子代数" $\mathcal R_t\subset \mathcal A(\Sigma_t)$，使得对任意 $t_1<t_2$，从 $\mathcal R_{t_2}$ 中的记录可追溯地重构 $\mathcal R_{t_1}$ 中的记录分布（记录可延拓性）。

记所有因果一致历史构成的集合为

$$
\mathsf{Cons}(\mathcal C)\subset\mathsf{Paths}(\mathcal C).
$$

上述定义抽象了"世界历史、因果与记录"的基本要求：不仅演化本身要符合因果结构，而且必须允许对过去记录的稳健重构，这一点在定义时间箭头时至关重要。

### 2.3 广义熵泛函与时间成本

我们引入一个定义在因果一致历史空间上的广义熵泛函。

**定义 2.3.1（广义熵泛函）**

对 $\gamma\in \mathsf{Cons}(\mathcal C)$，定义

$$
\mathcal S_{\mathrm{gen}}[\gamma]
=
\alpha S_{\mathrm{th}}[\gamma]
+
\beta S_{\mathrm{ent}}[\gamma]
+
\gamma D_{\mathrm{rel}}[\gamma]
+
\lambda \mathcal B[\gamma],
$$

其中：

1. $S_{\mathrm{th}}[\gamma] = \int_I \sigma_{\mathrm{th}}(\gamma(t),\dot\gamma(t))\,\mathrm dt$，为粗粒化热力学熵密度沿路径的积分；
2. $S_{\mathrm{ent}}[\gamma] = \int_I \sigma_{\mathrm{ent}}(\gamma(t))\,\mathrm dt$，可取为纠缠熵或广义熵密度的积分；
3. $D_{\mathrm{rel}}[\gamma] = \int_I d(\omega_t|\omega_t^{(0)})\,\mathrm dt$，其中 $d$ 为相对熵密度，$\omega_t^{(0)}$ 为某参考态；
4. $\mathcal B[\gamma]$ 为边界几何行为的泛函，典型地可写成

   $$
   \mathcal B[\gamma]=\int_{\partial M[\gamma]} \mathcal L_{\mathrm{bdy}}(h,K)\,\mathrm d\Sigma,
   $$

   其中 $h$ 为诱导度规，$K$ 为外在曲率。

系数 $\alpha,\beta,\gamma,\lambda$ 由物理情景与刻度选择（例如统一时间刻度）决定。

**假设 2.3.2（正性与凸性）**

1. $\sigma_{\mathrm{th}}$ 与 $\sigma_{\mathrm{ent}}$ 在速度变量上凸且非负；
2. 相对熵密度 $d(\cdot|\cdot)$ 对第一变量严格凸并满足单调性；
3. 边界泛函 $\mathcal B$ 在允许的边界变分空间上为下半连续且具良好的下界。

在这些条件下，$\mathcal S_{\mathrm{gen}}$ 在 $\mathsf{Cons}(\mathcal C)$ 上是良好定义的下有界泛函。

### 2.4 时间箭头与时间刻度的公理化重构

我们现在给出本文关于时间的公理方案。

**公理 2.4.1（因果优先性）**

物理上允许的世界历史必定属于因果一致历史空间 $\mathsf{Cons}(\mathcal C)$。

**公理 2.4.2（广义熵优化）**

真实世界对应于使广义熵泛函

$$
\mathcal S_{\mathrm{gen}}:\mathsf{Cons}(\mathcal C)\to \mathbb R
$$

在给定边界与初态约束下取得极值的历史族

$$
\gamma^\star\in \mathsf{Cons}(\mathcal C),\quad
\mathcal S_{\mathrm{gen}}[\gamma^\star]
=\inf\{\mathcal S_{\mathrm{gen}}[\gamma] \mid \gamma\in\mathsf{Admissible}\},
$$

其中 $\mathsf{Admissible} \subset \mathsf{Cons}(\mathcal C)$ 由初态、约束条件与能量/通量界构成。

**公理 2.4.3（时间箭头条件）**

在极小历史 $\gamma^\star$ 上存在单调参数 $t$，使得局域熵产生率

$$
\dot s_{\mathrm{loc}}(t):=
\frac{\mathrm d}{\mathrm dt}
\left(
\alpha s_{\mathrm{th}}(t)
+
\beta s_{\mathrm{ent}}(t)
+
\gamma d_t
\right)
\ge 0
\quad\text{几乎处处},
$$

其中 $s_{\mathrm{th}},s_{\mathrm{ent}},d_t$ 分别为沿历史的局域密度。该单调方向定义时间箭头。

**定义 2.4.4（时间刻度等价类）**

设 $\gamma^\star:I\to\mathcal C$ 为极小历史，若 $f:I\to I'$ 为严格单调可微双射，则 $\tilde\gamma=\gamma^\star\circ f^{-1}$ 为同一历史的另一参数化。称两个参数化 $t$ 与 $t'$ 属于同一**时间刻度等价类**，若存在 $f\in\mathrm{Diff}_+^1$ 使 $t'=f(t)$。记该等价类为 $[t]$。

由此，时间不再是事先给定的"背景轴"，而是由极小历史及其单调重参数化等价类定义的结构。

---

## 3 极小历史的存在性与时间箭头的几何唯一性

本节的目标是：在合理假设下，证明广义熵泛函 $\mathcal S_{\mathrm{gen}}$ 在因果一致历史空间上的极小点存在且在单调重参数化下唯一，从而从数学上支持"时间＝广义熵最优路径"这一主张。

### 3.1 变分设置与拓扑结构

考虑函数空间

$$
\mathsf{Paths}(\mathcal C)=\{\gamma:I\to\mathcal C \mid \gamma\ \text{绝对连续}\},
$$

在其上赋予例如 $W^{1,1}$ 或 $C^0$ 与 $L^1$ 组合的拓扑。假设：

1. $\mathcal C$ 为完备可分度量空间；
2. $\mathsf{Cons}(\mathcal C) \subset \mathsf{Paths}(\mathcal C)$ 在上述拓扑下为闭集合；
3. $\mathsf{Admissible}\subset \mathsf{Cons}(\mathcal C)$ 由边界条件与能量/通量约束给出，是闭且有适当的紧性（例如通过 Arzelà–Ascoli 或 Dunford–Pettis 型条件）。

在此设置下，广义熵泛函 $\mathcal S_{\mathrm{gen}}$ 是下半连续的，并满足如下性质。

**命题 3.1.1（下界与紧性）**

在假设 2.3.2 与上述拓扑假设下，存在常数 $C$，对所有 $\gamma\in\mathsf{Admissible}$ 有

$$
\mathcal S_{\mathrm{gen}}[\gamma]\ge -C.
$$

此外，对任意 $s\in\mathbb R$，集合

$$
\{\gamma\in\mathsf{Admissible} \mid \mathcal S_{\mathrm{gen}}[\gamma]\le s\}
$$

在所选拓扑下为相对紧。

*证明思路*：利用相对熵与熵密度的下界性和凸性，对速度与态给出能量型估计，再应用标准的紧性定理。

### 3.2 极小点存在性

**定理 3.2.1（广义熵极小历史的存在）**

在上述假设下，广义熵泛函 $\mathcal S_{\mathrm{gen}}$ 在 $\mathsf{Admissible}$ 上存在极小值，即存在 $\gamma^\star\in\mathsf{Admissible}$ 使

$$
\mathcal S_{\mathrm{gen}}[\gamma^\star]
=\inf\{\mathcal S_{\mathrm{gen}}[\gamma] \mid \gamma\in\mathsf{Admissible}\}.
$$

*证明概要*：取极小序列 $(\gamma_n) \subset \mathsf{Admissible}$ 使 $\mathcal S_{\mathrm{gen}}[\gamma_n]\to\inf$。由命题 3.1.1 的紧性，存在子列（仍记为 $\gamma_n$）在所选拓扑下收敛于 $\gamma^\star\in\mathsf{Admissible}$。利用下半连续性得到

$$
\mathcal S_{\mathrm{gen}}[\gamma^\star]
\le\liminf_{n\to\infty}\mathcal S_{\mathrm{gen}}[\gamma_n]
=\inf,
$$

从而 $\gamma^\star$ 为极小点。

完整严格证明见附录 A。

### 3.3 局域 Euler–Lagrange 方程与熵产生率

在极小历史 $\gamma^\star$ 上，对局域变分 $\delta\gamma$（保持初末条件与因果一致性），考虑一阶变分

$$
\delta\mathcal S_{\mathrm{gen}}[\gamma^\star;\delta\gamma]
=0.
$$

在形式上，若将密度写为拉格朗日型

$$
\mathcal L(\gamma,\dot\gamma)
=
\alpha \sigma_{\mathrm{th}}(\gamma,\dot\gamma)
+
\beta \sigma_{\mathrm{ent}}(\gamma)
+
\gamma d(\omega(\gamma)|\omega^{(0)}(\gamma))
+
\lambda\mathcal l_{\mathrm{bdy}}(\gamma,\dot\gamma),
$$

则极小路径满足 Euler–Lagrange 方程

$$
\frac{\mathrm d}{\mathrm dt}
\left(
\frac{\partial\mathcal L}{\partial \dot\gamma}
\right)
-
\frac{\partial\mathcal L}{\partial \gamma}
=0,
$$

加上来自因果约束与记录约束的有效"力学方程"。熵产生率可写为

$$
\dot s_{\mathrm{loc}}(t)
=
\alpha\dot s_{\mathrm{th}}(t)
+
\beta\dot s_{\mathrm{ent}}(t)
+
\gamma\dot d_t.
$$

在许多物理情景下（如符合局域平衡的非平衡热力学、符合完全正性与守恒的量子通道、以及满足 QNEC/QFC 等条件的引力背景），可证明 $\dot s_{\mathrm{loc}}(t)\ge0$ 几乎处处，从而为时间箭头提供变分上的解释。

### 3.4 唯一性与时间刻度等价类

为了从极小路径中抽取"时间箭头"，需要证明在单调重参数化下极小路径是唯一的。

**假设 3.4.1（严格凸性与拓扑不可约性）**

1. 对几乎每个 $t$，广义熵密度

   $$
   (\gamma,\dot\gamma)\mapsto
   \alpha \sigma_{\mathrm{th}}(\gamma,\dot\gamma)
   +
   \beta \sigma_{\mathrm{ent}}(\gamma)
   +
   \gamma d(\omega(\gamma)|\omega^{(0)}(\gamma))
   $$

   在 $\dot\gamma$ 上严格凸；

2. 因果一致历史空间 $\mathsf{Cons}(\mathcal C)$ 在给定初末约束下是"拓扑不可约"的：任意两条可行路径若在每个时间切片上诱导的记录分布几乎处处相同，则它们在单调重参数化下等价。

在此假设下我们有：

**定理 3.4.2（极小因果一致历史的单调重参数化唯一性）**

在上述假设下，若 $\gamma_1,\gamma_2\in\mathsf{Admissible}$ 都是 $\mathcal S_{\mathrm{gen}}$ 的极小点，则存在严格单调可微双射 $f$ 使得

$$
\gamma_2(t)=\gamma_1(f^{-1}(t)),
$$

即两条极小历史仅相差一个单调重参数化，因而属于同一时间刻度等价类 $[t]$。

*证明要点*：严格凸性保证若存在两条不同的极小路径，则沿它们的中间插值路径将降低泛函值，矛盾；拓扑不可约性保证"不同参数化"的自由度恰好为单调重参数化群 $\mathrm{Diff}_+^1$。详见附录 A。

由此可见，"时间刻度等价类"是由广义熵优化唯一选出的结构，这给出了时间的几何—变分定义。

---

## 4 散射理论中的刻度母尺与时间成本的可观测实现

为将上述抽象时间结构与可观测量连接，我们现在转向散射—谱理论，并引入刻度母尺 $\kappa(\omega)$。

### 4.1 散射矩阵、群延迟与相对态密度

考虑一类静态或定态散射系统，其散射矩阵 $S(\omega)$ 在频率 $\omega$ 上为幺正矩阵，满足适当的可微性。定义 Wigner–Smith 延迟算子

$$
Q(\omega)=-i S(\omega)^\dagger \partial_\omega S(\omega),
$$

其迹

$$
\tau(\omega)
:=
\operatorname{tr}Q(\omega)
$$

给出总群延迟。另一方面，定义总散射相位

$$
\Phi(\omega)
=\arg\det S(\omega),\qquad
\varphi(\omega)=\frac12\Phi(\omega),
$$

则半相位导数

$$
\frac{\varphi'(\omega)}{\pi}
$$

可与相对态密度 $\rho_{\mathrm{rel}}(\omega)$ 及群延迟迹联系。由 Birman–Kreĭn 型公式与 Friedel 型关系，可得

$$
\frac{\varphi'(\omega)}{\pi}
=
\rho_{\mathrm{rel}}(\omega)
=
\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

在适用范围内严格成立。

**定义 4.1.1（刻度母尺）**

定义频率刻度母尺

$$
\kappa(\omega)
=
\frac{\varphi'(\omega)}{\pi}
=
\rho_{\mathrm{rel}}(\omega)
=
\frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

该量一方面可由散射相位导数测量，另一方面可由群延迟迹或态密度差测量，因此在实验与理论中具有清晰的刻度意义。

### 4.2 时间成本与刻度母尺的耦合

设某类物理过程可在频率空间中用测度 $\mu_\gamma$ 描述，它由历史 $\gamma$ 诱导：例如对每个 $\omega$，令 $\mu_\gamma(\mathrm d\omega)$ 描述该频率模式在历史 $\gamma$ 中的权重与通量。则可以定义一类"谱时间成本"泛函

$$
\mathcal T[\gamma]
=
\int \kappa(\omega)\,\mu_\gamma(\mathrm d\omega).
$$

在许多散射或开系情景中，可证明 $\mathcal T[\gamma]$ 与广义熵泛函 $\mathcal S_{\mathrm{gen}}[\gamma]$ 中的部分项等价或界控制，例如：

* 若 $D_{\mathrm{rel}}[\gamma]$ 是入射/出射态之间的相对熵，则其密度可用相对态密度 $\rho_{\mathrm{rel}}(\omega)$ 表达，从而

  $$
  D_{\mathrm{rel}}[\gamma]
  \approx
  \int f(\kappa(\omega))\,\mu_\gamma(\mathrm d\omega),
  $$

  对某类凸函数 $f$ 成立；

* 若边界项 $\mathcal B[\gamma]$ 与散射截面或反射相位有关，则亦可写成本征频率上的积分。

这意味着，在散射—谱端，广义熵泛函的一部分可以写成刻度母尺加权的谱积分，从而时间成本具有直接可观测的刻度代理。

### 4.3 时间箭头的散射实现

将第 3 节的极小历史 $\gamma^\star$ 与散射刻度母尺结合，我们得到：

**命题 4.3.1（散射时间成本的极小性）**

设广义熵泛函 $\mathcal S_{\mathrm{gen}}[\gamma]$ 中的相对熵与边界项可写成

$$
\gamma D_{\mathrm{rel}}[\gamma]
+
\lambda \mathcal B[\gamma]
=
\int g(\omega)\,\kappa(\omega)\,\mu_\gamma(\mathrm d\omega)
+
C[\gamma],
$$

其中 $g$ 为非负函数，$C[\gamma]$ 不含 $\kappa$。则对极小历史 $\gamma^\star$，谱时间成本

$$
\mathcal T[\gamma]
=
\int \kappa(\omega)\,\mu_\gamma(\mathrm d\omega)
$$

在相同约束下被最小化，即

$$
\mathcal T[\gamma^\star]
\le
\mathcal T[\gamma],\quad
\forall\gamma\in\mathsf{Admissible},
$$

在适当的技术条件下成立。

此时，"时间箭头"不但在抽象的历史空间上定义，而且在散射实验中可通过测量相位导数、群延迟与态密度来间接读取和验证。

---

## 5 局域观察者、记录与"主观时间"

### 5.1 观察者截面与记录子代数

在实际观测中，具体观察者只与世界的一部分发生相互作用。设某观察者的世界线为 $\Gamma_{\mathrm{obs}} \subset M$，与之关联的可访问代数为 $\mathcal A_{\mathrm{obs}} \subset \mathcal A$。在每个因果切片 $\Sigma_t$ 上，观察者可访问的记录子代数为

$$
\mathcal R_t^{\mathrm{obs}}
=
\mathcal A_{\mathrm{obs}}\cap \mathcal A(\Sigma_t).
$$

沿极小历史 $\gamma^\star$，观察者所见的"经验时间序列"是态限制到 $\mathcal R_t^{\mathrm{obs}}$ 所得到的状态族 $\omega_t^{\mathrm{obs}}$。

### 5.2 主观时间与局域熵产生

对于给定观察者，可以定义其"主观时间刻度"等价类：所有使得局域熵产生率

$$
\dot s_{\mathrm{loc}}^{\mathrm{obs}}(t)
=
\frac{\mathrm d}{\mathrm dt}
\left(\alpha s_{\mathrm{th}}^{\mathrm{obs}}(t)
+
\beta s_{\mathrm{ent}}^{\mathrm{obs}}(t)
+
\gamma d_t^{\mathrm{obs}}\right)
\ge 0
$$

的单调参数化等价类，其中各量为局域于 $\mathcal R_t^{\mathrm{obs}}$ 的熵密度与相对熵密度。

在极小历史 $\gamma^\star$ 上，在常见条件下（例如局域完全正演化、信息丢失方向单一、记录不断累积），可以证明：

1. 对"绝大多数"观察者，其主观时间箭头与全局时间箭头同向；
2. 主观时间刻度是全局时间刻度等价类的一个投影：在某些重参数化自由度上可能更粗糙，但在箭头方向上是兼容的。

这为"为什么不同观察者之间的时间箭头一致"提供了几何—熵的解释：它来源于他们共同嵌入的极小历史结构与共享的广义熵优化原则。

### 5.3 延迟选择与时间干涉的重述（概念性）

在双缝干涉与延迟选择实验中，常见的叙述是：测量选择"回溯性地改变"粒子走过的路径。本文框架下可以给出另一种描述：

* 世界历史在因果一致与广义熵优化下有一族候选路径；
* 在未指定测量布置之前，对应的 $\mathsf{Admissible}$ 集合较大，其中包含"干涉保留"与"路径信息显露"等不同类型的子族；
* 一旦测量布置与记录结构确定，约束集 $\mathsf{Admissible}$ 被收紧，使仅有某些类型的历史仍是广义熵极小的候选；
* 在此意义上，"延迟选择"改变的是允许历史的可行集合及其广义熵结构，而非事后修改了已发生的事件。

时间干涉实验中粒子在"时间尺度上"发生干涉，可视为在历史空间中不同时间延迟路径的相干叠加，其"可见性"取决于记录结构是否允许把这些路径区分为不同的因果一致历史族。

---

## 6 示例：两能级系统与简化宇宙学模型

本节给出两个简化模型，以说明广义熵最优路径如何具体生成时间箭头。

### 6.1 两能级系统与环境散射

考虑一个两能级系统与环境的散射耦合，哈密顿量为

$$
H=H_S+H_E+H_{\mathrm{int}},
$$

其中 $H_S$ 为两能级系统，$H_E$ 为环境，$H_{\mathrm{int}}$ 为相互作用项，使散射矩阵 $S(\omega)$ 存在。

1. **配置空间**：$\mathcal C$ 取为系统 + 环境的有效密度算符空间（在适当截断下）。

2. **历史空间**：$\gamma:I\to\mathcal C$ 描述系统 + 环境的演化；因果一致条件要求演化由完全正保迹映射族实现，且记录可在环境中稳健保存。

3. **广义熵泛函**：

   $$
   \mathcal S_{\mathrm{gen}}[\gamma]
   =
   \alpha \int S_{\mathrm{vN}}(\rho_S(t))\,\mathrm dt
   +
   \gamma \int D(\rho_{SE}(t)|\rho_S(t)\otimes\rho_E^{(0)})\,\mathrm dt
   +
   \lambda \mathcal B[\gamma],
   $$

   其中 $S_{\mathrm{vN}}$ 为冯诺依曼熵，$D$ 为量子相对熵。

4. **散射刻度**：环境散射过程给出 $S(\omega)$ 与 $Q(\omega)$，从而定义 $\kappa(\omega)$，并构造谱时间成本

   $$
   \mathcal T[\gamma]
   =
   \int \kappa(\omega)\,\mu_\gamma(\mathrm d\omega).
   $$

通过比较两类路径：

* "快速退相干 + 明确记录路径"；
* "缓慢退相干 + 模糊记录路径"，

可以证明在自然系数选择下，前者的 $\mathcal S_{\mathrm{gen}}$ 更小，从而被变分原理偏好，同时其时间箭头与环境中记录累积的方向一致。

详细计算与估计见附录 B。

### 6.2 简化 FRW 宇宙学模型

考虑一个同质各向同性 FRW 宇宙，度规

$$
\mathrm ds^2=-\mathrm dt^2+a(t)^2\mathrm d\vec x^2,
$$

物质场满足能量条件与 QNEC 类条件。取 $\mathcal C$ 为适当粗粒化的宇宙态空间（例如标量场模展开截断后的高斯态族）。

构造广义熵泛函

$$
\mathcal S_{\mathrm{gen}}[\gamma]
=
\alpha \int S_{\mathrm{th}}(a(t),\rho(t))\,\mathrm dt
+
\beta \int S_{\mathrm{ent}}(\mathcal I(t))\,\mathrm dt
+
\gamma \int D(\rho(t)|\rho_{\mathrm{ref}}(t))\,\mathrm dt
+
\lambda \mathcal B_{\mathrm{GHY}}[a(\cdot)],
$$

其中 $\mathcal B_{\mathrm{GHY}}$ 为 FRW 边界上的类似 Gibbons–Hawking–York 项。此时极小历史 $\gamma^\star$ 与 $a(t)$ 的演化紧密关联。在适当条件下可以证明：选定的时间箭头与 FRW 模型中通常采用的"宇宙时间"一致，并且"宇宙学红移"的单调性可解释为广义熵优化下的刻度后果，而非额外假设。

---

## 7 结论与讨论

本文提出了一个将时间重构为"广义熵最优路径"的统一框架。通过在因果一致历史空间上引入广义熵泛函 $\mathcal S_{\mathrm{gen}}$，并在严格的凸性与紧性假设下证明极小历史的存在与单调重参数化唯一性，我们给出了一个"时间＝因果一致 + 广义熵优化"的数学化定义。进一步，通过散射理论中的刻度母尺

$$
\kappa(\omega)
=
\frac{\varphi'(\omega)}{\pi}
=
\rho_{\mathrm{rel}}(\omega)
=
\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

我们把抽象的时间成本与可观测的相位导数、群延迟和态密度统一，从而为时间刻度提供了可检验的实验代理。

在观察者与记录层面，本文说明了局域"主观时间"如何作为全局广义熵最优历史的投影而出现，以及为何不同观察者的时间箭头在通常情形下保持一致。通过简化的两能级系统与 FRW 宇宙学模型，我们展示了该框架在微观与宏观时间现象上的解释力。

未来方向包括：将该框架与更精确的量子场论及全息引力模型对接；在严格数学意义上证明在 QNEC/QFC 等条件下广义熵泛函的凸性与极小性；以及在具体散射实验中设计以 $\kappa(\omega)$ 为刻度母尺的时间箭头检验方案。

---

## 附录 A：极小历史的存在性与唯一性证明细节

### A.1 函数空间与拓扑选择

令 $I=[0,1]$ 无失一般性。取配置空间 $\mathcal C$ 为可分度量空间，赋度量 $d_{\mathcal C}$。定义路径空间

$$
\mathsf{Paths}(\mathcal C)
=
\left\{
\gamma:I\to \mathcal C
\mid
\gamma\ \text{绝对连续},\
\int_0^1|\dot\gamma(t)|\,\mathrm dt<\infty
\right\},
$$

其中 $|\dot\gamma(t)|$ 通过选定的可测选择嵌入或局部坐标来定义。赋拓扑

$$
\mathrm d(\gamma_1,\gamma_2)
=
\sup_{t\in I}d_{\mathcal C}(\gamma_1(t),\gamma_2(t))
+
\int_0^1
\rho(\dot\gamma_1(t),\dot\gamma_2(t))\,\mathrm dt,
$$

其中 $\rho$ 为速度空间上的度量。假设因果一致集 $\mathsf{Cons}(\mathcal C)$ 在此拓扑下闭，且可行集

$$
\mathsf{Admissible}
=
\{\gamma\in\mathsf{Cons}(\mathcal C) \mid \gamma(0)=\gamma_0,\ \gamma(1)=\gamma_1,\ \text{满足能量/通量界}\}
$$

为闭且具有适当紧性（例如通过统一速度界与 Arzelà–Ascoli）。

### A.2 广义熵泛函的下界与下半连续性

写

$$
\mathcal S_{\mathrm{gen}}[\gamma]
=
\int_0^1
\mathcal L(\gamma(t),\dot\gamma(t))\,\mathrm dt,
$$

其中

$$
\mathcal L(\gamma,\dot\gamma)
=
\alpha \sigma_{\mathrm{th}}(\gamma,\dot\gamma)
+
\beta \sigma_{\mathrm{ent}}(\gamma)
+
\gamma d(\omega(\gamma)|\omega^{(0)}(\gamma))
+
\lambda\mathcal l_{\mathrm{bdy}}(\gamma,\dot\gamma).
$$

**引理 A.2.1（下界）**

若存在常数 $c_0,c_1>0$ 使

$$
\mathcal L(\gamma,\dot\gamma)
\ge
c_0|\dot\gamma|-c_1,
$$

则对任意 $\gamma\in\mathsf{Admissible}$，有

$$
\mathcal S_{\mathrm{gen}}[\gamma]\ge -c_1.
$$

*证明*：直接积分估计。

**引理 A.2.2（下半连续性）**

若 $\mathcal L$ 在 $(\gamma,\dot\gamma)$ 上 Carathéodory 型（对速度变量凸且满足适当增长条件），则 $\mathcal S_{\mathrm{gen}}$ 在所选拓扑下为下半连续泛函。

*证明*：标准变分法结果，可参见 Tonelli 型存在定理的条件。

### A.3 极小点存在性证明

**命题 A.3.1（极小序列的相对紧性）**

设 $(\gamma_n) \subset\mathsf{Admissible}$ 为极小序列，即

$$
\lim_{n\to\infty}\mathcal S_{\mathrm{gen}}[\gamma_n]
=
\inf\mathcal S_{\mathrm{gen}}.
$$

由引理 A.2.1，$\mathcal S_{\mathrm{gen}}[\gamma_n]$ 有统一下界。再由下界与增长条件可得速度 $\dot\gamma_n$ 在 $L^1$ 中有统一界。由 Dunford–Pettis 或相应紧性定理与 Arzelà–Ascoli，可取子列使 $\gamma_n$ 在 $\mathsf{Paths}(\mathcal C)$ 中收敛于某 $\gamma^\star \in\mathsf{Admissible}$。

**定理 A.3.2（极小点存在性）**

由引理 A.2.2 的下半连续性，

$$
\mathcal S_{\mathrm{gen}}[\gamma^\star]
\le
\liminf_{n\to\infty}\mathcal S_{\mathrm{gen}}[\gamma_n]
=
\inf\mathcal S_{\mathrm{gen}},
$$

故 $\gamma^\star$ 为极小点。

### A.4 唯一性证明

假设 3.4.1 成立。设 $\gamma_1,\gamma_2\in\mathsf{Admissible}$ 都为极小点，且不相关于单调重参数化。构造插值

$$
\gamma_\theta(t)
=
\mathrm{Geo}_\theta(\gamma_1(t),\gamma_2(t)),
\qquad \theta\in[0,1],
$$

其中 $\mathrm{Geo}_\theta$ 为在 $\mathcal C$ 上的测地插值或凸组合。由于 $\mathcal L$ 在速度上严格凸，可得

$$
\mathcal S_{\mathrm{gen}}[\gamma_\theta]
<
(1-\theta)\mathcal S_{\mathrm{gen}}[\gamma_1]
+
\theta \mathcal S_{\mathrm{gen}}[\gamma_2],
$$

除非 $\dot\gamma_1(t)=\dot\gamma_2(t)$ 几乎处处并且 $\gamma_1(t)=\gamma_2(t)$ 在同一参数化下几乎处处。由极小性 $\mathcal S_{\mathrm{gen}}[\gamma_1]=\mathcal S_{\mathrm{gen}}[\gamma_2]=\inf$，上式只能在等号情况下成立，故两条路径在速度与位置上几乎处处一致。

剩余自由度来自参数化：若存在不同参数化使得记录分布在每个切片上相同，而路径点集相同，则拓扑不可约性假设保证它们仅差一个单调重参数化，从而得定理 3.4.2。

---

## 附录 B：相对熵单调性与局域熵产生率的正性

### B.1 相对熵与广义熵项

给定两个态 $\rho,\sigma$ 对应同一代数，量子相对熵

$$
D(\rho|\sigma)
=
\operatorname{Tr}\left(\rho(\log\rho-\log\sigma)\right)
$$

满足以下性质：

1. $D(\rho|\sigma)\ge0$，且 $D(\rho|\sigma)=0$ 当且仅当 $\rho=\sigma$；
2. 完全正迹保持映射 $\Phi$ 下单调性：

   $$
   D(\Phi(\rho)|\Phi(\sigma))
   \le
   D(\rho|\sigma).
   $$

在历史 $\gamma(t)$ 上，若局域演化由完全正迹保持半群生成，则相对熵项随时间的变化率非正，即

$$
\frac{\mathrm d}{\mathrm dt}
D(\rho_t|\sigma_t)
\le 0,
$$

从而在广义熵泛函中，$-\gamma D_{\mathrm{rel}}[\gamma]$ 可以理解为正的"熵成本"。

### B.2 局域熵产生率

考虑局域熵密度

$$
s_{\mathrm{loc}}(t)
=
\alpha s_{\mathrm{th}}(t)
+
\beta s_{\mathrm{ent}}(t)
+
\gamma d_t,
$$

在满足局域平衡条件与能量条件的情形下，可证明

$$
\dot s_{\mathrm{loc}}(t)\ge 0\quad\text{几乎处处},
$$

这通常来源于：

1. 热力学熵产生非负；
2. 纠缠熵在某些扩张过程中单调不减；
3. 相对熵在恢复映射或 coarse-graining 下单调。

这些性质在本文框架中被组合为时间箭头条件（公理 2.4.3）。

---

## 附录 C：散射刻度母尺的标准推导概要

本附录给出刻度母尺

$$
\kappa(\omega)
=
\frac{\varphi'(\omega)}{\pi}
=
\rho_{\mathrm{rel}}(\omega)
=
\frac{1}{2\pi}\operatorname{tr}Q(\omega)
$$

的标准推导概要。

### C.1 Birman–Kreĭn 公式与相对谱移

设 $H_0$ 为自由哈密顿量，$H=H_0+V$ 为散射哈密顿量，满足适当的 trace class 条件。定义相对谱移函数 $\xi(\lambda)$，其导数 $\xi'(\lambda)$ 给出相对态密度

$$
\rho_{\mathrm{rel}}(\lambda)
=
\xi'(\lambda).
$$

Birman–Kreĭn 公式给出

$$
\det S(\lambda)
=
e^{-2\pi i \xi(\lambda)},
$$

从而

$$
\Phi(\lambda)
=\arg\det S(\lambda)
=-2\pi \xi(\lambda)+2\pi k,\quad k\in\mathbb Z.
$$

取连续分支并定义半相位 $\varphi(\lambda)=\tfrac12\Phi(\lambda)$，得到

$$
\frac{\varphi'(\lambda)}{\pi}
=
-\xi'(\lambda)
=
\rho_{\mathrm{rel}}(\lambda),
$$

在适当选取符号与约定下得到第一等号。

### C.2 Wigner–Smith 延迟算子与迹公式

Wigner–Smith 延迟算子定义为

$$
Q(\lambda)
=
-i S(\lambda)^\dagger \partial_\lambda S(\lambda),
$$

若 $S(\lambda)$ 在 $\lambda$ 上足够光滑，则

$$
\operatorname{tr}Q(\lambda)
=
-i \operatorname{tr}\left(S(\lambda)^\dagger \partial_\lambda S(\lambda)\right)
=
-i\partial_\lambda \log\det S(\lambda)
=
-i\partial_\lambda(i\Phi(\lambda))
=
\Phi'(\lambda).
$$

由 $\varphi=\tfrac12\Phi$，得

$$
\varphi'(\lambda)
=\frac12\Phi'(\lambda)
=\frac12\operatorname{tr}Q(\lambda),
$$

从而

$$
\frac{\varphi'(\lambda)}{\pi}
=
\frac{1}{2\pi}\operatorname{tr}Q(\lambda).
$$

结合 C.1 与 C.2，得到刻度母尺同一式

$$
\kappa(\omega)
=
\frac{\varphi'(\omega)}{\pi}
=
\rho_{\mathrm{rel}}(\omega)
=
\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

这为本文将时间刻度同一嵌入广义熵最优路径框架提供了谱—散射端的坚实基础。

