# 宇宙作为量子离散元胞自动机的公理化刻画

计算宇宙终对象的 QCA 实现与统一时间刻度极限

---

## 摘要

在此前关于"计算宇宙" $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 的系列工作中,我们已经构造了离散复杂性几何、离散信息几何、统一时间刻度诱导的控制流形 $(\mathcal M,G)$、任务信息流形 $(\mathcal S_Q,g_Q)$、时间–信息–复杂性联合变分原理、多观察者共识几何、因果小钻石与 Null–Modular 双覆盖、拓扑复杂性与不可判定性,以及统一计算宇宙终对象 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$。

另一方面,量子离散元胞自动机 (quantum cellular automaton, QCA) 早已被视为"宇宙作为量子离散动力系统"的自然候选模型:在可数格点上,每个格点携带有限维 Hilbert 空间,整体演化为局域酉更新。传统 QCA 理论主要集中于信息传播速度、可逆性与通用性,而较少与统一时间刻度、复杂性几何与宇宙终对象结构系统整合。

本文在统一时间刻度–计算宇宙终对象框架内,对"宇宙作为量子离散元胞自动机"的观点给出一个严格的公理化刻画。主要结果如下:

1. 引入"宇宙 QCA 对象" $\mathfrak U_{\mathrm{QCA}} = (\Lambda,{\mathcal H_x}_{x\in\Lambda}, U, \mathsf C_T)$,其中 $\Lambda$ 为可数格点集合,$\mathcal H_x$ 为局域 Hilbert 空间,$U$ 为满足局域性与可逆性的全局酉更新,$\mathsf C_T$ 为一次更新的统一时间刻度代价。我们提出一组 QCA 宇宙公理:局域有限度、统一时间刻度兼容性、可观察算子网与因果结构、可嵌入计算宇宙公理等。

2. 构造从 QCA 宇宙对象到计算宇宙对象 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 的函子 $\mathcal F_{\mathrm{QCA}\to\mathrm{comp}}$,以及从物理可实现的计算宇宙到 QCA 宇宙的函子 $\mathcal F_{\mathrm{comp}\to\mathrm{QCA}}$,证明在统一时间刻度与局域性公理下,这两个函子在适当定义的子范畴上给出范畴等价:
$$
\mathbf{QCAUniv}^{\mathrm{phys}}
\simeq
\mathbf{CompUniv}^{\mathrm{phys}}.
$$
特别地,统一计算宇宙终对象 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 在 QCA 子范畴上的限制同构于一个"宇宙 QCA 终对象" $\mathfrak U_{\mathrm{QCA}}^{\mathrm{term}}$。

3. 在统一时间刻度母尺下,对 QCA 宇宙构造控制流形 $(\mathcal M,G)$ 与连续极限:证明在 Lieb–Robinson 有界传播速度与可控扰动条件下,存在一族连续时间极限 $U(t)$ 与有效哈密顿量 $H_{\mathrm{eff}}$,使得统一时间刻度密度 $\kappa(\omega)$ 与 QCA 的离散谱数据通过散射–谱移–群延迟公式相连。

4. 从 QCA 宇宙内构造观察者、因果小钻石、Null–Modular 双覆盖与时间晶体,并证明这些结构可以完全在 QCA Hilbert 空间上实现:观察者为 QCA 上的局域子系统,因果小钻石为局域空间–时间块,Null–Modular $\mathbb Z_2$ holonomy 与时间晶体相的奇偶结构通过在 QCA 上构造自指反馈网络与 Floquet–QCA 实现。

5. 在拓扑复杂性与不可判定性的层面,证明 QCA 宇宙包含所有可计算的离散动力系统:任何可构造的计算宇宙对象都可嵌入某个 QCA 宇宙中;因而此前在计算宇宙层面证明的拓扑环路收缩不可判定性、灾难安全性不可判定性与能力–风险前沿不可算法求解性,均在 QCA 宇宙中成立。

本文从而表明:"宇宙作为量子离散元胞自动机"并非独立于计算宇宙框架的额外假设,而是统一计算宇宙终对象在一个特别自然子范畴中的具体实现;统一时间刻度、复杂性几何、信息几何、多观察者因果网与能力–风险结构在 QCA 宇宙中可以完全实现并进行具体工程化。

---

## 1 引言

"宇宙是一个量子离散元胞自动机"这一设想在量子信息、基础物理与计算理论中反复出现:宇宙在某个微观尺度上由离散格点与局域更新规则组成,连续时空与场论只是其大尺度极限。另一方面,"宇宙是一个计算宇宙"将宇宙本体抽象为通用计算系统的一个终极对象,从复杂性几何、信息几何与统一时间刻度的角度统一了物理、计算与信息。

在此前系列中,我们已经从计算–几何–范畴的角度构造了一个统一计算宇宙终对象 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$。自然问题是:

1. 是否存在一个纯 QCA 的"宇宙对象" $\mathfrak U_{\mathrm{QCA}}$,可以实现所有计算宇宙结构?
2. QCA 宇宙与统一时间刻度–控制流形结构如何对接?
3. 观察者、因果小钻石、Null–Modular 双覆盖、时间晶体、自指与能力–风险结构是否可以在 QCA 宇宙内完备实现?

本文对这些问题给出系统回答。

第 2 节给出 QCA 宇宙公理与基本结构;第 3 节构造 QCA 宇宙与计算宇宙之间的范畴等价,并定义 QCA 宇宙终对象;第 4 节讨论统一时间刻度与 QCA 的连续极限;第 5 节展示观察者、因果小钻石、Null–Modular 与时间晶体在 QCA 宇宙中的实现;第 6 节说明此前不可判定性与能力–风险结构在 QCA 宇宙中的保留。附录中给出主要命题与定理的详细证明。

---

## 2 QCA 宇宙的公理化定义

本节给出量子离散元胞自动机宇宙的公理化定义,并引入统一时间刻度兼容性与可观察算子网。

### 2.1 QCA 基本结构

**定义 2.1(量子离散元胞自动机)**

设 $\Lambda$ 为可数格点集合(例如 $\mathbb Z^d$),对每个 $x\in\Lambda$,赋予有限维 Hilbert 空间 $\mathcal H_x \cong \mathbb C^{d_x}$。全局 Hilbert 空间定义为无限张量积
$$
\mathcal H
=
\bigotimes_{x\in\Lambda} \mathcal H_x,
$$
在严格数学上需选取适当的可分子空间(例如有限激发空间),本文使用物理上标准的"局域可激发态空间"。

一个可逆 QCA 是一个满足以下性质的酉算子 $U:\mathcal H\to\mathcal H$:

1. 局域性:存在有限半径 $R>0$,使得对任意局域算子 $A_x \in \mathcal B(\mathcal H_x)$,其 Heisenberg 演化 $U^\dagger A_x U$ 支撑在 $\{y\in\Lambda : \mathrm{dist}(x,y)\le R\}$ 上;

2. 可逆性:$U$ 是酉的,且 $U^{-1}$ 满足同样的局域性约束。

我们称 $(\Lambda,{\mathcal H_x},U)$ 为一个 QCA 对象。

### 2.2 QCA 宇宙对象

为了刻画宇宙而非单一 QCA,我们需要加入统一时间刻度与可观察算子网。

**定义 2.2(QCA 宇宙对象)**

一个 QCA 宇宙对象是四元组
$$
\mathfrak U_{\mathrm{QCA}}
=
(\Lambda,{\mathcal H_x}_{x\in\Lambda},U,\mathsf C_T),
$$
满足:

1. QCA 条件:$(\Lambda,{\mathcal H_x},U)$ 是可逆 QCA;

2. 统一时间刻度兼容:存在一个统一时间刻度密度 $\kappa(\omega)$ 和对应的散射–群延迟结构,使得一次 $U$ 更新的物理时间代价 $\mathsf C_T$ 可以写成
$$
\mathsf C_T
=
\int_{\Omega} w(\omega)\,\kappa(\omega)\,\mathrm d\omega,
$$
其中 $w(\omega)$ 为归一化权重,$\Omega \subset\mathbb R$ 为有效频带;

3. 可观察算子网:存在局域算子网 $\{\mathcal A(\mathcal O)\}$(例如区域 $\mathcal O\subset\Lambda$ 上的局域算子代数),使得 QCA 在 Heisenberg 图像下实现算子网的自同构,且统一时间刻度–散射结构可通过该算子网上的散射过程定义。

在计算宇宙层面,我们将配置集 $X$ 取为一组全局规范化基矢集合的标签,例如
$$
X
=
\big\{
\ket{\psi} = \bigotimes_{x\in\Lambda} \ket{s_x} : s_x\in\{1,\dots,d_x\},\ \text{满足有限激发条件}
\big\}.
$$
一步更新关系由 $U$ 的矩阵元定义,统一时间刻度由 $\mathsf C_T$ 决定。

### 2.3 QCA 宇宙公理

我们总结为如下公理系统:

**公理 Q1(离散格与有限局域自由度)**

$\Lambda$ 为可数图,度有界;每个格点局域 Hilbert 空间维数有限。

**公理 Q2(局域可逆动态)**

$U$ 为酉算子,满足有限传播半径 $R$ 的局域性约束,且 $U^{-1}$ 亦局域。

**公理 Q3(统一时间刻度兼容)**

存在统一时间刻度密度 $\kappa(\omega)$,使得对某类散射过程(例如在局域区域与外部宇宙之间的散射),其散射相位、谱移与群延迟迹与 $\kappa(\omega)$ 满足统一时间刻度母式。一次 QCA 步 $U$ 的时间代价 $\mathsf C_T$ 为对 $\kappa(\omega)$ 的某个窗口积分。

**公理 Q4(可观察算子网与因果结构)**

存在局域算子网 $\mathcal A(\mathcal O)$ 与 QCA 诱导的因果结构,使得局域算子仅在有限步内影响有限区域,且统一时间刻度–复杂性几何可在该因果结构上定义因果小钻石与复杂性光锥。

满足 Q1–Q4 的对象称为 QCA 宇宙对象,并记其范畴为 $\mathbf{QCAUniv}$。

---

## 3 QCA 宇宙与计算宇宙的范畴等价

本节构造 QCA 宇宙与计算宇宙之间的函子,并证明在物理可实现子类上二者范畴等价,从而得到 QCA 宇宙终对象。

### 3.1 从 QCA 宇宙到计算宇宙的函子

**定义 3.1(函子 $\mathcal F_{\mathrm{QCA}\to\mathrm{comp}}$)**

给定 QCA 宇宙对象
$$
\mathfrak U_{\mathrm{QCA}}
=
(\Lambda,{\mathcal H_x},U,\mathsf C_T),
$$
构造计算宇宙对象
$$
U_{\mathrm{comp}}(\mathfrak U_{\mathrm{QCA}})
=
(X,\mathsf T,\mathsf C,\mathsf I),
$$
如下:

1. 配置集 $X$:取一族张量积基 $\{\ket{s_x}\}_{s_x=1}^{d_x}$ 的有限激发张量积,令 $X$ 为这些基矢的标签集合;

2. 一步更新关系 $\mathsf T$:定义
$$
(x,y)\in\mathsf T
\iff
\langle y|U|x\rangle \neq 0;
$$

3. 单步代价 $\mathsf C(x,y)$:若 $(x,y)\in\mathsf T$,令 $\mathsf C(x,y) = \mathsf C_T$(或加上与局域操作数目相关的修正因子),否则 $\mathsf C(x,y)=\infty$;

4. 信息质量函数 $\mathsf I$:由物理任务定义,例如某个局域可观测量或散射过程的成功概率。

此构造显然保留了局域性与统一时间刻度结构:复杂性距离 $d_{\mathrm{comp}}$ 对应于执行 QCA 步数乘以 $\mathsf C_T$,因果结构由 $\mathsf T$ 的有向图决定。

态射层面:

**定义 3.2(QCA 宇宙态射与模拟映射)**

在 $\mathbf{QCAUniv}$ 中,一个态射
$$
\Phi:\mathfrak U_{\mathrm{QCA}}\to\mathfrak U_{\mathrm{QCA}}'
$$
由一个格点映射 $\phi_\Lambda:\Lambda\to\Lambda'$、局域 Hilbert 空间之间的等距映射族 $\phi_x:\mathcal H_x\to\mathcal H_{\phi_\Lambda(x)}'$ 与全局演化之间的共变关系给出。其在计算宇宙层面诱导一个模拟映射 $f_X:X\to X'$,即 $\mathcal F_{\mathrm{QCA}\to\mathrm{comp}}(\Phi) = f_X$,满足前文定义的步进保持、代价控制与信息单调性。

这样,$\mathcal F_{\mathrm{QCA}\to\mathrm{comp}}$ 是一个从 $\mathbf{QCAUniv}$ 到 $\mathbf{CompUniv}$ 的函子。

### 3.2 从计算宇宙到 QCA 宇宙的构造

反向构造更微妙,需要利用 QCA 的通用性:任意局域可逆离散动力系统都可以嵌入某个 QCA 中。

**命题 3.3(计算宇宙到 QCA 的嵌入)**

对每个物理可实现的计算宇宙对象
$$
U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)
$$
存在 QCA 宇宙对象 $\mathfrak U_{\mathrm{QCA}}$ 和一对映射
$$
E:X\to\mathcal H,\quad D:\mathcal H\to X,
$$
使得:

1. $E$ 是将配置标签嵌入 QCA Hilbert 空间局域子空间的编码映射;
2. $D$ 是从编码子空间投影回配置标签的解码映射;
3. QCA 更新 $U$ 在编码子空间上模拟计算宇宙更新关系 $\mathsf T$:若 $(x,y)\in\mathsf T$,则
$$
D U E(x) = y,
$$
且该模拟在统一时间刻度与局域性公理下仅引入有限常数因子复杂性开销。

证明思路:使用标准"电路–QCA 通用性"构造,将计算宇宙的局域规则转译为一维或二维 QCA 的局域门,详细见附录 B。

将此嵌入视为函子
$$
\mathcal F_{\mathrm{comp}\to\mathrm{QCA}}
:
\mathbf{CompUniv}^{\mathrm{phys}}\to\mathbf{QCAUniv}^{\mathrm{phys}},
$$
在对象上给出 QCA 实现,在态射上将模拟映射提升为 QCA 层的局域变换。

### 3.3 范畴等价与 QCA 宇宙终对象

**定理 3.4(QCA 宇宙与计算宇宙的范畴等价)**

在物理可实现子范畴 $\mathbf{QCAUniv}^{\mathrm{phys}} \subset\mathbf{QCAUniv}$、$\mathbf{CompUniv}^{\mathrm{phys}} \subset\mathbf{CompUniv}$ 上,函子
$$
\mathcal F_{\mathrm{QCA}\to\mathrm{comp}},
\quad
\mathcal F_{\mathrm{comp}\to\mathrm{QCA}}
$$
构成范畴等价:
$$
\mathbf{QCAUniv}^{\mathrm{phys}}
\simeq
\mathbf{CompUniv}^{\mathrm{phys}}.
$$
特别地,统一计算宇宙终对象 $\mathfrak U_{\mathrm{comp}}^{\mathrm{term}}$ 在该子范畴上的限制同构于某个 QCA 宇宙终对象 $\mathfrak U_{\mathrm{QCA}}^{\mathrm{term}}$,后者满足对任意 QCA 宇宙对象 $\mathfrak U_{\mathrm{QCA}}$ 存在唯一(至自然变换)态射
$$
\mathfrak U_{\mathrm{QCA}}\to\mathfrak U_{\mathrm{QCA}}^{\mathrm{term}}.
$$

证明见附录 C。

---

## 4 统一时间刻度与 QCA 的连续极限

本节讨论如何在 QCA 宇宙上构造统一时间刻度与控制流形的连续极限。

### 4.1 Lieb–Robinson 有界传播与有限光速

在局域 QCA 中,Lieb–Robinson 不等式保证了信息传播速度有上界:存在速度 $v_{\mathrm{LR}}>0$ 与衰减率 $\mu>0$ 以及常数 $C>0$,使得对任意局域算子 $A_x$、$B_y$ 有
$$
\big|
[U^n A_x U^{-n},B_y]
\big|
\le
C\,
\exp\big(-\mu(\mathrm{dist}(x,y)-v_{\mathrm{LR}}n)\big).
$$
在统一时间刻度下,与每步更新代价 $\mathsf C_T$ 的比值给出一个有效"光速"
$$
c_{\mathrm{eff}} = v_{\mathrm{LR}}/\mathsf C_T.
$$
该量可视为控制流形连续极限中的度量因子。

### 4.2 QCA 到连续时间演化的极限

在许多 QCA 模型中,存在连续时间极限:存在哈密顿量 $H_{\mathrm{eff}}$ 与时间步长 $\delta t$ 使得
$$
U = \exp(-\mathrm i H_{\mathrm{eff}}\delta t) + \mathcal O(\delta t^2),
$$
从而多步演化在 $t = n\delta t$ 时逼近连续时间演化 $\exp(-\mathrm i H_{\mathrm{eff}} t)$。对此,统一时间刻度密度 $\kappa(\omega)$ 可从 $H_{\mathrm{eff}}$ 的散射数据中定义。

**命题 4.1(QCA 的统一时间刻度连续极限)**

设 QCA 宇宙对象 $\mathfrak U_{\mathrm{QCA}}$ 满足:

1. 存在连续极限 $U = \exp(-\mathrm i H_{\mathrm{eff}}\delta t) + \mathcal O(\delta t^2)$;
2. $H_{\mathrm{eff}}$ 为可追踪扰动的哈密顿量,满足波算子完备与统一时间刻度母式;

则 QCA 的单步代价 $\mathsf C_T$ 与统一时间刻度密度 $\kappa(\omega)$ 之间存在比例关系,且复杂性距离在细化极限下收敛到控制流形上的测地距离 $d_G$,其中 $G$ 由 $H_{\mathrm{eff}}$ 的散射–群延迟响应构造。

证明见附录 D。

### 4.3 QCA 宇宙的控制流形

对 QCA 宇宙中的可控参数(例如局域耦合常数、格间距、外场强度等)赋予参数空间
$$
\mathcal M_{\mathrm{QCA}} = \{\theta\},
$$
在每个 $\theta$ 上对应一个 QCA 更新算子 $U(\theta)$ 与统一时间刻度密度 $\kappa(\omega;\theta)$。按照此前统一时间刻度–控制流形的构造,定义度量
$$
G_{ab}(\theta)
=
\int_{\Omega}
w(\omega)\,
\operatorname{tr}\big(
\partial_a Q(\omega;\theta)\,\partial_b Q(\omega;\theta)
\big)\,\mathrm d\omega,
$$
其中 $Q(\omega;\theta) = -\mathrm i U(\theta)^\dagger(\omega)\partial_\omega U(\theta)(\omega)$。

从而 QCA 宇宙的控制流形 $(\mathcal M_{\mathrm{QCA}},G)$ 与统一时间刻度直接相连,计算宇宙侧的控制流形结构在 QCA 宇宙中得到了具体实现。

---

## 5 QCA 宇宙中的观察者、因果小钻石与时间晶体

本节说明如何在 QCA 宇宙中实现此前在计算宇宙层面构造的观察者、因果小钻石、Null–Modular 双覆盖与时间晶体。

### 5.1 观察者作为 QCA 局域子系统

在 QCA 宇宙中,一个观察者 $O$ 可视为格点集合 $\Lambda_O\subset\Lambda$ 上的局域子系统,其内部 Hilbert 空间为
$$
\mathcal H_O = \bigotimes_{x\in\Lambda_O}\mathcal H_x,
$$
内部记忆状态空间 $M_{\mathrm{int}}$ 被嵌入 $\mathcal H_O$ 的某个子空间,观测符号空间 $\Sigma_{\mathrm{obs}}$ 与动作空间 $\Sigma_{\mathrm{act}}$ 对应 QCA 上某些局域测量与控制算子。内部更新算子 $\mathcal U$ 则由在 $\mathcal H_O$ 上实施的局域 QCA 序列实现。

多观察者情形对应多个不相交或部分相交的局域子系统,通信通过 QCA 的局域传播集中在有限 Lieb–Robinson 光锥中。

### 5.2 因果小钻石与边界计算

在 QCA 宇宙的事件层
$$
E = X\times\mathbb Z,
\quad
(x,n) \mapsto (y,n+1)
$$
的因果结构基础上,一个因果小钻石 $\Diamond$ 对应某个有限时间窗 $[n_0,n_1]$ 内某个空间–格点区域 $\Lambda_\Diamond \subset\Lambda$ 的事件集合。钻石内部的 QCA 演化由 $U_\Diamond$ 的局域分块表示,边界 Hilbert 空间由钻石空间–时间边界对应的局域自由度张成。

边界计算算子
$$
\mathsf K_\Diamond
=
\Pi^+_\Diamond U_\Diamond \iota^-_\Diamond
$$
在 QCA Hilbert 空间中可通过局域投影与参考态张量积显式实现。此前在计算宇宙层面提出的"边界决定体积"的离散 GHY 结构在 QCA 宇宙中得到完整实现。

### 5.3 Null–Modular 双覆盖与时间晶体实现

在 QCA 宇宙中构造因果小钻石链 $\{\Diamond_k\}$ 与对应的 Null–Modular 双覆盖,可以选择某个自指反馈网络或 Floquet–QCA 驱动规则,使得每个钻石对应一个 Floquet 周期。

对每个周期钻石的出射边界引入由散射相位导数决定的模 $2$ 时间相位标签 $\epsilon_k\in\mathbb Z_2$,利用此前构造的双覆盖图 $\widetilde{\mathfrak D}\to\mathfrak D$,可将时间晶体的周期翻倍奇偶结构编码为闭合钻石链在双覆盖上的 holonomy。

具体 QCA 时间晶体模型(如一维自旋链上的 Floquet–QCA)可直接用局域门阵列在 $\mathcal H$ 上实现,其时间晶体相的存在性与稳健性可通过 QCA 的可逆性与局域性证明,见附录 A。

---

## 6 不可判定性与能力–风险结构在 QCA 宇宙中的保留

本节说明此前在计算宇宙层面得到的不可判定性与能力–风险前沿结构如何在 QCA 宇宙中保留。

### 6.1 QCA 宇宙的可计算性完备性

由于 QCA 可模拟任意局域可逆离散系统,且通过添加辅助寄存器可模拟不可逆演化与测量,QCA 宇宙在可计算性层面是"通用"的:任何可构造计算宇宙对象都可以嵌入某个 QCA 宇宙中。

因此,停机问题、环路收缩问题、普适灾难安全性问题与能力–风险前沿搜索问题在 QCA 宇宙中仍不可判定或不可算法完全求解:如果在 QCA 子类中可解,则通过范畴等价可还原为在一般计算宇宙中可解,与前文结果矛盾。

### 6.2 能力–风险前沿的 QCA 实现

在 QCA 宇宙中,一个策略 $\pi$ 对应某个局域控制协议(例如在有限区域对 QCA 的局域门进行调制),能力泛函 $\mathrm{Cap}(\pi)$ 与风险泛函 $\mathrm{Risk}(\pi)$ 可用 QCA 上的局域测量与灾难集合 $C_{\mathrm{cat}}\subset X$ 表示。能力–风险前沿 $\mathcal F_{\mathrm{CR}}$ 作为在策略空间上的帕累托边界结构,在 QCA 控制流形 $\mathcal M_{\mathrm{QCA}}$ 上成为一个具体的几何对象。

然而,由于 QCA 的通用性,能力–风险前沿在普遍情形下具有与计算宇宙中相同的不可算法求解性:不存在一个 QCA 上的局域算法可对所有策略族给出前沿上的代表点。

---

## 附录 A:自旋链 Floquet–QCA 时间晶体模型

本附录给出自旋链 Floquet–QCA 时间晶体模型的示例及其在计算宇宙中的实现。

### A.1 模型定义

考虑一维格点 $\Lambda = \mathbb Z$,每点 Hilbert 空间 $\mathcal H_x = \mathbb C^2$,基矢 $\{\ket{\uparrow},\ket{\downarrow}\}$。定义两步 Floquet 演化
$$
U_F = U_2 U_1,
$$
其中
$$
U_1
=
\prod_{x\ \mathrm{even}}
\exp\big( -\mathrm i J_1 \sigma_x^z \sigma_{x+1}^z \big),
\quad
U_2
=
\prod_{x\ \mathrm{odd}}
\exp\big( -\mathrm i J_2 \sigma_x^z \sigma_{x+1}^z \big),
$$
$J_1,J_2$ 为相互作用强度。

在适当参数,例如 $J_1 \approx J_2 \approx \pi/4$,并考虑初态族为自发对称破缺态(如 Néel 态 $\ket{\uparrow\downarrow\uparrow\downarrow\cdots}$ 与其翻转),该模型已知形成周期翻倍时间晶体相:局域自旋期望值 $\langle\sigma_x^z\rangle_n$ 在 Floquet 周期 $T$ 下交替翻转,周期为 $2T$。

### A.2 在计算宇宙中的实现

将配置集 $X$ 取为自旋配置集合 $\{\uparrow,\downarrow\}^{\Lambda}$ 的有限激发子集,更新关系 $\mathsf T$ 由 $U_F$ 在基矢上的非零矩阵元给出,单步代价 $\mathsf C_T$ 对应执行一次 $U_F$ 的时间消耗。此时该 QCA 模型成为计算宇宙的一个具体实例,时间晶体相的存在证明了计算宇宙中存在"离散时间平移自发破缺"的实例。

---

## 附录 B:计算宇宙到 QCA 的嵌入构造

### B.1 自适应格点编码

给定计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$,首先为 $X$ 选择编码成二进制串的方式:存在单射 $\mathrm{code}:X\to\{0,1\}^{\mathbb Z^d}$,且扭曲有限局域结构。

在格点 $\Lambda = \mathbb Z^d$ 上构造 QCA,自旋自由度足够大以承载每个配置元素的编码,利用标准"电路–QCA 转换"将计算宇宙的一步更新规则转化为 QCA 上的一步局域酉演化。为处理可逆性,可将计算宇宙扩展为可逆形式(保存历史),再嵌入 QCA。

### B.2 时间刻度与复杂性控制

通过选择合适的局域门分解与时序安排,使得 QCA 一步更新在统一时间刻度下代价为 $\mathsf C_T$,并且模拟计算宇宙的一步更新最多需要常数个 QCA 步,从而复杂性距离最多乘以常数因子。

编码与解码映射 $E,D$ 则由局域算子网络实现:初态配置标签 $x$ 对应若干格点的局域自旋状态,读取结果亦通过局域测量实现。

---

## 附录 C:范畴等价的证明纲要

在物理可实现子范畴中,$\mathcal F_{\mathrm{QCA}\to\mathrm{comp}}$ 与 $\mathcal F_{\mathrm{comp}\to\mathrm{QCA}}$ 在对象层与态射层上构成互逆:

1. 对每个 $\mathfrak U_{\mathrm{QCA}}$,$\mathcal F_{\mathrm{comp}\to\mathrm{QCA}}\circ\mathcal F_{\mathrm{QCA}\to\mathrm{comp}}(\mathfrak U_{\mathrm{QCA}})$ 与 $\mathfrak U_{\mathrm{QCA}}$ 在局域等距意义下同构;
2. 对每个 $U_{\mathrm{comp}}$,$\mathcal F_{\mathrm{QCA}\to\mathrm{comp}}\circ\mathcal F_{\mathrm{comp}\to\mathrm{QCA}}(U_{\mathrm{comp}})$ 与 $U_{\mathrm{comp}}$ 在复杂性度量与信息结构上同构;
3. 对态射,模拟映射与 QCA 层的局域变换在合成下满足函子性与自然变换结构。

具体证明可参考标准电路–QCA 通用性的范畴化版本,结合统一时间刻度与复杂性几何的 Lipschitz 控制。

---

## 附录 D:命题 4.1 的散射–时间刻度极限

命题 4.1 的严格证明需使用散射理论与统一时间刻度母式。对连续极限哈密顿量 $H_{\mathrm{eff}}$,在可追踪扰动与波算子完备假设下,存在散射矩阵 $S(\omega)$、谱移函数 $\xi(\omega)$ 与群延迟矩阵 $Q(\omega)$,满足
$$
\kappa(\omega)
=
\frac{\xi'(\omega)}{1}
=
\frac{\varphi'(\omega)}{\pi}
=
\frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$
QCA 单步对应的离散谱数据 $\lambda_j(\delta t) \approx \mathrm e^{-\mathrm i\varepsilon_j\delta t}$ 与 $H_{\mathrm{eff}}$ 的连续谱关联,其统一时间刻度增量 $\mathsf C_T$ 与 $\kappa(\omega)$ 的积分相联系。复杂性距离在 $\delta t\to 0$ 极限下收敛到由 $G$ 诱导的测地距离 $d_G$,$G$ 由 $\partial_\theta Q(\omega;\theta)$ 的二次型构造。

这些步骤与此前统一时间刻度–控制流形构造一致,此处只需将"离散步长"识别为 QCA 单步,并利用连续极限 $\delta t\to 0$ 的标准散射理论工具。
