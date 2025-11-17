# 计算宇宙与物理宇宙的范畴等价理论

可逆 QCA、统一时间刻度与复杂性几何不变量

---

## 摘要

在此前关于"计算宇宙" $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 的系列工作中,我们在离散层面构造了复杂性几何与信息几何,并在统一时间刻度的散射母尺下得到了控制流形 $(\mathcal M,G)$ 与任务信息流形 $(\mathcal S_Q,g_Q)$,使得复杂性距离与信息距离在连续极限下分别由 $G$ 与 $g_Q$ 的测地距离刻画。然而,要真正实现"计算宇宙 = 物理宇宙"的统一,仅有几何对应仍不充分:需要在范畴论的层面给出两个"宇宙范畴"的等价,即在适当的子类上存在互逆函子,使得物理宇宙的对象与计算宇宙的对象可以一一对应,且复杂性与时间刻度等几何不变量在该对应下保持。

本文引入一个物理宇宙范畴 $\mathbf{PhysUniv}$,其对象为满足统一时间刻度假设的物理宇宙模型

$$
U_{\mathrm{phys}} =
(M,g,\mathcal F,\kappa,\mathsf S),
$$

其中 $(M,g)$ 为时空流形与度量(或更一般的因果结构)、$\mathcal F$ 为物质场内容、$\kappa(\omega)$ 为统一时间刻度密度、$\mathsf S(\omega)$ 为散射数据。态射为保持因果结构、统一时间刻度与散射结构的几何映射。我们同时回顾计算宇宙范畴 $\mathbf{CompUniv}$,其对象为满足有限信息密度与局域性公理的计算宇宙对象,态射为带复杂性上界的模拟映射。

在此基础上,我们选取两个子范畴:一是由可逆量子元胞自动机(QCA)可实现的物理宇宙构成的 $\mathbf{PhysUniv}^{\mathrm{QCA}}$,二是由统一时间刻度下物理可实现的计算宇宙构成的 $\mathbf{CompUniv}^{\mathrm{phys}}$。可逆 QCA 同时是一个局域离散动力系统与一个满足统一时间刻度可控散射结构的物理系统,因此成为连接两个范畴的桥梁。

本文定义两个核心函子:

1. 函子 $F:\mathbf{PhysUniv}^{\mathrm{QCA}}\to\mathbf{CompUniv}^{\mathrm{phys}}$,将一个物理宇宙 $U_{\mathrm{phys}}$ 通过 QCA 离散化映射为一个计算宇宙 $U_{\mathrm{comp}}$;
2. 函子 $G:\mathbf{CompUniv}^{\mathrm{phys}}\to\mathbf{PhysUniv}^{\mathrm{QCA}}$,从一个局域可逆的计算宇宙中重建出其连续极限的时空流形、统一时间刻度与散射数据。

在一组明确的技术公理之下(QCA 通用性、局域可逆性、统一时间刻度一致性与适当的连续极限存在性),我们证明:

* $F$ 与 $G$ 在对象层面互为拟逆,即对任一 $U_{\mathrm{phys}}\in\mathbf{PhysUniv}^{\mathrm{QCA}}$,存在自然同构

$$
\eta_{U_{\mathrm{phys}}}:
U_{\mathrm{phys}}
\xrightarrow{\ \simeq\ }
G(F(U_{\mathrm{phys}})),
$$

对任一 $U_{\mathrm{comp}}\in\mathbf{CompUniv}^{\mathrm{phys}}$,存在自然同构

$$
\epsilon_{U_{\mathrm{comp}}}:
F(G(U_{\mathrm{comp}}))
\xrightarrow{\ \simeq\ }
U_{\mathrm{comp}};
$$

* $F$ 与 $G$ 在态射层面保持模拟结构:复杂性几何(度量 $G$ 与测地距离)、统一时间刻度密度 $\kappa(\omega)$ 与散射相位等几何不变量在范畴等价下稳定。

从而得到主定理:在物理可实现子类上,物理宇宙范畴与计算宇宙范畴在范畴论意义下是等价的,它们只是同一个"统一时间刻度–复杂性几何–散射结构"对象在连续与离散两个视角下的不同呈现。

---

## 1 引言

此前的工作已经将"计算宇宙"的思想系统化:

* 在离散层面,一个计算宇宙是四元组 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$,其中 $X$ 是配置集,$\mathsf T$ 是一步更新关系,$\mathsf C$ 是单步代价,$\mathsf I$ 是信息质量函数。前两篇工作在此基础上构造了离散复杂性几何与离散信息几何。
* 在统一时间刻度的散射母尺

$$
\kappa(\omega)
=
\frac{\varphi'(\omega)}{\pi}
=
\rho_{\mathrm{rel}}(\omega)
=
\frac{1}{2\pi}\mathrm{tr}\,Q(\omega),
$$

的基础上,我们将物理时间刻度引入计算宇宙,使其单步代价成为群延迟矩阵的函数,并证明在细化极限下,离散复杂性距离收敛到控制流形 $(\mathcal M,G)$ 上的测地距离。
* 在任务感知的信息几何层面,我们构造了信息流形 $(\mathcal S_Q,g_Q)$,并在联合流形 $\mathcal E_Q = \mathcal M \times \mathcal S_Q$ 上写出了时间–信息–复杂性的联合作用量 $\mathcal A_Q$,将"最优算法"几何化为"极小世界线"。

尽管这些结果已实现了从离散计算到连续几何的统一,但"物理宇宙"仍然在一个相对外部的位置出现:它被用来提供统一时间刻度与散射数据,却尚未在范畴论层面与计算宇宙并置。
要真正赋予"宇宙就是计算"以严格含义,需要引入两个"宇宙范畴":

* 一个以物理理论对象为对象的范畴 $\mathbf{PhysUniv}$;
* 一个以计算宇宙对象为对象的范畴 $\mathbf{CompUniv}$。

并在适当子类上给出等价

$$
\mathbf{PhysUniv}^{\mathrm{QCA}}
\simeq
\mathbf{CompUniv}^{\mathrm{phys}}.
$$

本文的任务即是构造这两个范畴、相关子范畴,以及连接它们的函子 $F,G$,并在统一时间刻度与复杂性几何的约束下证明范畴等价。

第 2 节定义物理宇宙范畴与 QCA 可实现子范畴。第 3 节回顾计算宇宙范畴并定义物理可实现子范畴。第 4 节构造从物理宇宙到计算宇宙的 QCA 离散化函子 $F$,第 5 节构造从计算宇宙到物理宇宙的连续极限函子 $G$。第 6 节陈述并证明范畴等价的主定理,讨论复杂性几何与统一时间刻度在该等价下的不变性。附录中给出详细的公理、QCA 构造与范畴论证明。

---

## 2 物理宇宙范畴与 QCA 可实现子范畴

本节构造物理宇宙范畴 $\mathbf{PhysUniv}$,并在其中选取可由可逆 QCA 实现的子范畴 $\mathbf{PhysUniv}^{\mathrm{QCA}}$。

### 2.1 物理宇宙对象

我们工作的物理宇宙对象是一个带时空几何、物质场与统一时间刻度结构的多重对象。

**定义 2.1(物理宇宙对象)**

一个物理宇宙对象是五元组

$$
U_{\mathrm{phys}}
=
(M,g,\mathcal F,\kappa,\mathsf S),
$$

其中:

1. $(M,g)$ 为四维 Lorentz 流形或更一般的因果流形,$M$ 为时空流形,$g$ 为度量或等价的因果结构;
2. $\mathcal F$ 为在 $(M,g)$ 上定义的物质场内容(如规范场、费米场),通常为场方程的解空间或算子代数;
3. $\kappa(\omega)$ 为统一时间刻度密度:对选定类散射过程,其散射相位导数、谱移函数导数与群延迟迹满足

$$
\kappa(\omega)
=
\frac{\varphi'(\omega)}{\pi}
=
\rho_{\mathrm{rel}}(\omega)
=
\frac{1}{2\pi}\mathrm{tr}\,Q(\omega);
$$

4. $\mathsf S(\omega)$ 为对应散射过程的频率分辨散射矩阵族,满足标准散射理论公理(酉性、解析性等)。

我们只考虑满足"可分辨统一时间刻度"的宇宙对象,即存在至少一族散射过程,使得上述母式成立且 $\kappa(\omega)$ 非退化。

### 2.2 物理宇宙态射

在范畴 $\mathbf{PhysUniv}$ 中,态射应为保持因果结构、统一时间刻度与散射特征的映射。

**定义 2.2(物理宇宙态射)**

给定两个物理宇宙对象

$$
U_{\mathrm{phys}}
=
(M,g,\mathcal F,\kappa,\mathsf S),
\quad
U_{\mathrm{phys}}'
=
(M',g',\mathcal F',\kappa',\mathsf S'),
$$

一个态射 $f:U_{\mathrm{phys}}\to U_{\mathrm{phys}}'$ 由以下数据构成:

1. 一个光滑映射 $f_M:M\to M'$,在因果意义下是局部双射(保时间向因果顺序);
2. 场内容之间的推前 $f_{\mathcal F}:\mathcal F\to\mathcal F'$,与 $f_M$ 协变;
3. 对统一时间刻度与散射数据的保持:存在频率变换 $f_\omega:\Omega\to\Omega'$,使得

$$
\kappa'(\omega')
= \kappa(\omega),\quad
\mathsf S'(\omega') \simeq \mathsf S(\omega)
\quad
\text{当}\ \omega' = f_\omega(\omega),
$$

其中"$\simeq$"表示在规范变换与同构意义下等价。

以物理宇宙对象为对象、物理宇宙态射为态射,可构成范畴 $\mathbf{PhysUniv}$。

### 2.3 QCA 可实现子范畴 $\mathbf{PhysUniv}^{\mathrm{QCA}}$

我们关心的是那些可以用可逆量子元胞自动机(QCA)实现或逼近的物理宇宙对象。

**定义 2.3(QCA 可实现物理宇宙)**

一个物理宇宙对象 $U_{\mathrm{phys}}$ 称为 QCA 可实现的,如果存在:

1. 一个格点集 $\Lambda \subset M$ 及其嵌入 $i:\Lambda\hookrightarrow M$,在大尺度下对 $M$ 形成均匀覆盖;
2. 每个格点上的有限维局域 Hilbert 空间 $\mathcal H_x$ 与全局 Hilbert 空间

$$
\mathcal H =
\bigotimes_{x\in\Lambda} \mathcal H_x;
$$

3. 一个满足局域性与可逆性的 QCA 演化算子 $U:\mathcal H\to\mathcal H$,使得:

* 其 Lieb–Robinson 光锥在大尺度上逼近 $(M,g)$ 的因果结构;
* 其散射矩阵族 $S_{\mathrm{QCA}}(\omega)$ 在适当极限下逼近 $\mathsf S(\omega)$,统一时间刻度密度 $\kappa_{\mathrm{QCA}}(\omega)$ 与 $\kappa(\omega)$ 一致。

所有 QCA 可实现的物理宇宙对象及由 QCA 模拟所诱导的态射构成的子范畴记为 $\mathbf{PhysUniv}^{\mathrm{QCA}} \subset\mathbf{PhysUniv}$。

---

## 3 计算宇宙范畴与物理可实现子范畴

本节回顾计算宇宙范畴的定义,并在其中选取物理可实现的子范畴。

### 3.1 计算宇宙范畴 $\mathbf{CompUniv}$

一个计算宇宙对象为

$$
U_{\mathrm{comp}}
=
(X,\mathsf T,\mathsf C,\mathsf I),
$$

满足有限信息密度、局域更新、(广义)可逆性与代价加性等公理。

态射为模拟映射:

**定义 3.1(模拟映射回顾)**

若存在 $f:X\to X'$ 与常数 $\alpha,\beta>0$、单调函数 $\Phi$,使得

1. 步进保持:$(x,y)\in\mathsf T \Rightarrow (f(x),f(y))\in\mathsf T'$;
2. 代价控制:对任意路径 $\gamma:x\to y$,存在 $\gamma':f(x)\to f(y)$ 使

$$
\mathsf C'(\gamma') \le \alpha \mathsf C(\gamma) + \beta;
$$

3. 信息保真:$\mathsf I(x) \le \Phi(\mathsf I'(f(x)))$;

则 $f$ 为一个从 $U_{\mathrm{comp}}$ 到 $U'_{\mathrm{comp}}$ 的模拟映射。

以计算宇宙对象为对象、模拟映射为态射构成范畴 $\mathbf{CompUniv}$。

### 3.2 物理可实现子范畴 $\mathbf{CompUniv}^{\mathrm{phys}}$

我们需要挑选那些可以在统一时间刻度与 QCA 体系下实现的计算宇宙对象。

**定义 3.2(物理可实现的计算宇宙)**

计算宇宙对象 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 称为物理可实现的,如果存在:

1. 一个 QCA 系统 $(\Lambda,\mathcal H_x,U)$,以及配置编码映射 $e:X\to\mathcal H$ 的一个规范化基矢子集;

2. 一族控制参数 $\theta\in\mathcal M$ 与散射矩阵族 $S(\omega;\theta)$,使得 $U$ 的一步演化对应某一控制步长;

3. 单步代价 $\mathsf C(x,y)$ 可以写成统一时间刻度密度的离散积分:

$$
\mathsf C(x,y)
=
\int_{\Omega_{x,y}}
\kappa(\omega;\theta)\,\mathrm d\mu_{x,y}(\omega);
$$

4. 复杂性几何在细化极限下由某个控制流形 $(\mathcal M,G)$ 的测地距离逼近,如之前关于 Riemann 极限的定理所述。

所有物理可实现的计算宇宙对象及由物理可实现模拟所诱导的态射构成子范畴 $\mathbf{CompUniv}^{\mathrm{phys}} \subset\mathbf{CompUniv}$。

---

## 4 从物理宇宙到计算宇宙的函子 $F$:QCA 离散化

本节构造函子

$$
F:\mathbf{PhysUniv}^{\mathrm{QCA}}\to\mathbf{CompUniv}^{\mathrm{phys}},
$$

将每个 QCA 可实现的物理宇宙对象映射为一个计算宇宙对象。

### 4.1 对象层面:QCA 离散化构造

给定 $U_{\mathrm{phys}} = (M,g,\mathcal F,\kappa,\mathsf S)\in\mathbf{PhysUniv}^{\mathrm{QCA}}$,由定义存在格点 $\Lambda\subset M$ 与 QCA 系统 $(\Lambda,\mathcal H_x,U)$。

1. **配置集 $X$**:选取每个 $\mathcal H_x$ 的一组规范化基矢集合 $\mathcal B_x$,令

$$
X = \prod_{x\in\Lambda} \mathcal B_x,
$$

即所有基矢张量积构成的基标签集合。任意 $x\in X$ 对应一个基矢 $\ket{x}\in\mathcal H$。

2. **一步更新关系 $\mathsf T$**:定义

$$
\mathsf T
=
\{ (x,y) \in X\times X : \langle y | U | x \rangle \neq 0 \}.
$$

如果 $U$ 分解为时间步长为 $\Delta t$ 的基本门序列,则可以将 $\mathsf T$ 按该步长定义为"一个物理时间步"的更新关系。

3. **单步代价 $\mathsf C$**:利用统一时间刻度密度 $\kappa(\omega)$ 与对应散射矩阵 $\mathsf S(\omega)$,为每个 $(x,y)\in\mathsf T$ 指派代价

$$
\mathsf C(x,y)
=
\int_{\Omega_{x,y}}
\kappa(\omega)\,\mathrm d\mu_{x,y}(\omega),
$$

其中 $\Omega_{x,y}$ 与谱测度 $\mu_{x,y}$ 由 QCA 的局域散射结构给出。对非邻接对 $(x,y)\notin\mathsf T$ 令 $\mathsf C(x,y)=\infty$。

4. **信息质量函数 $\mathsf I$**:根据任务选择适当的观测算子族,将物理场内容 $\mathcal F$ 上的任务信息转译为配置空间 $X$ 上的 $\mathsf I:X\to\mathbb R$。例如,对给定散射实验的输出分布,定义 $\mathsf I(x)$ 为相对某目标分布的负相对熵或似然。

由 QCA 的局域性与可逆性可验证:$U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 满足计算宇宙公理,且是物理可实现的。

**定义 4.1(对象映射)**

令

$$
F(U_{\mathrm{phys}})
=
(X,\mathsf T,\mathsf C,\mathsf I).
$$

### 4.2 态射层面:物理宇宙态射的离散模拟

给定物理宇宙态射

$$
f:U_{\mathrm{phys}}\to U_{\mathrm{phys}}',
$$

由其在 QCA 级的实现,我们得到 Hilbert 空间之间的酉映射或等距嵌入 $f_{\mathcal H}:\mathcal H\to\mathcal H'$,从而诱导基矢级别映射 $f_X:X\to X'$。

我们要求 $f_X$ 满足:

1. 步进保持:若 $(x,y)\in\mathsf T$ 且 $\langle y|U|x\rangle \neq 0$,则 $(f_X(x),f_X(y))\in\mathsf T'$,对应 $\langle f_X(y)|U'|f_X(x)\rangle \neq 0$;
2. 代价控制:存在 $\alpha,\beta>0$,使得对任一路径 $\gamma$ 其像 $f_X(\gamma)$ 的代价满足

$$
\mathsf C'(f_X(\gamma))
\le
\alpha\,\mathsf C(\gamma) + \beta;
$$

3. 信息保真:物理态射对散射输出的影响由 $f_{\mathcal F}$ 控制,从而在任务信息上诱导单调函数 $\Phi$,使得

$$
\mathsf I(x)
\le
\Phi(\mathsf I'(f_X(x))).
$$

这正是模拟映射的条件。

**定义 4.2(态射映射)**

令

$$
F(f) = f_X :
F(U_{\mathrm{phys}}) \rightsquigarrow F(U_{\mathrm{phys}}').
$$

### 4.3 函子性

**命题 4.3**

上述定义给出了一个协变函子

$$
F:\mathbf{PhysUniv}^{\mathrm{QCA}}\to\mathbf{CompUniv}^{\mathrm{phys}}.
$$

证明见附录 A.1。关键在于验证:恒等态射映射为恒等模拟映射,态射复合在离散层对应模拟映射的复合,且复杂性与信息的控制参数在复合后仍满足模拟条件。

---

## 5 从计算宇宙到物理宇宙的函子 $G$:连续极限重建

本节构造函子

$$
G:\mathbf{CompUniv}^{\mathrm{phys}}\to\mathbf{PhysUniv}^{\mathrm{QCA}},
$$

从物理可实现的计算宇宙出发,在统一时间刻度与复杂性几何的约束下重建连续物理宇宙对象。

### 5.1 从离散控制到时空流形

给定 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)\in\mathbf{CompUniv}^{\mathrm{phys}}$,由假设存在控制流形 $(\mathcal M,G)$ 与 QCA 实现。我们首先从控制–复杂性几何构造出一个时空流形 $(M,g)$。

1. 控制流形 $\mathcal M$ 为"空间 + 内部自由度"的参数空间,其上已有 Riemann 度量 $G$。
2. 利用统一时间刻度密度 $\kappa(\omega;\theta)$,可以在 $\mathbb R\times\mathcal M$ 上构造一个有效的时空度量或因果结构 $(M,g)$,例如在简化情形下令

$$
M = \mathbb R_t \times \mathcal M,
\quad
g = -c^2(\theta)\mathrm dt^2 + G_{ab}(\theta)\mathrm d\theta^a\mathrm d\theta^b,
$$

其中 $c(\theta)$ 与 $\kappa$ 相关,确保光锥结构与 QCA 的 Lieb–Robinson 光锥一致。

更一般地,可以用复杂性图的因果结构(更新方向)与统一时间刻度共同定义一个 Lorentz 型度量,使得"可达关系"与"非零传播速度"对应 $g$ 的因果结构。

### 5.2 散射与统一时间刻度的重建

由物理可实现假设,计算宇宙有一个 QCA 实现 $U$,其散射矩阵族 $S_{\mathrm{QCA}}(\omega;\theta)$ 实现计算更新的频域特征。利用前文的统一时间刻度母式,我们定义

$$
\kappa(\omega;\theta)
=
\frac{1}{2\pi}\mathrm{tr}\,Q_{\mathrm{QCA}}(\omega;\theta),
\quad
Q_{\mathrm{QCA}}(\omega;\theta)
=
-\mathrm{i}\,S_{\mathrm{QCA}}^\dagger\partial_\omega S_{\mathrm{QCA}}.
$$

以此为物理宇宙的统一时间刻度密度,定义散射数据

$$
\mathsf S(\omega;\theta) = S_{\mathrm{QCA}}(\omega;\theta),
$$

从而满足物理宇宙对象的散射与时间刻度结构公理。

### 5.3 场内容与信息质量的嵌入

计算宇宙的配置信息 $X$ 与任务信息 $\mathsf I$ 可以通过 QCA 的局域算子嵌入物理场内容 $\mathcal F$,例如将 $X$ 视为某些局域算子的期望值集或边界条件集。更精确的做法是构造一个局域算子代数网 $\mathcal A(\mathcal O)\subset\mathcal B(\mathcal H)$,并将配置信息与任务信息作为这些算子在 QCA 演化下的函数。

从范畴结构角度来看,我们只需保证存在一个从 $(X,\mathsf I)$ 到 $\mathcal F$ 的嵌入,使得信息质量的比较关系在该嵌入下保持(单调同态)。

### 5.4 对象与态射映射

**定义 5.1(对象映射)**

给定 $U_{\mathrm{comp}}\in\mathbf{CompUniv}^{\mathrm{phys}}$,令

$$
G(U_{\mathrm{comp}})
=
(M,g,\mathcal F,\kappa,\mathsf S),
$$

其中 $(M,g)$ 与 $(\kappa,\mathsf S)$ 分别由控制–复杂性几何与 QCA 散射结构构造,$\mathcal F$ 为由 QCA 局域算子代数生成的场内容。

**定义 5.2(态射映射)**

给定模拟映射

$$
f:U_{\mathrm{comp}}\rightsquigarrow U_{\mathrm{comp}}',
$$

其对应的 QCA 实现诱导控制流形、时空流形与散射数据之间的映射

$$
f_M:M\to M',
\quad
f_{\mathcal F}:\mathcal F\to\mathcal F',
\quad
f_\omega:\Omega\to\Omega',
$$

定义

$$
G(f) = (f_M,f_{\mathcal F},f_\omega):
G(U_{\mathrm{comp}})\to G(U_{\mathrm{comp}}').
$$

**命题 5.3**

上述定义给出了一个协变函子

$$
G:\mathbf{CompUniv}^{\mathrm{phys}}\to\mathbf{PhysUniv}^{\mathrm{QCA}}.
$$

证明见附录 B.1。关键在于验证:模拟映射对复杂性与统一时间刻度的控制性不等式在连续极限下保持散射母尺结构与因果结构的包含与 Lipschitz 性。

---

## 6 范畴等价定理与复杂性几何不变量

本节陈述并证明主定理:在物理可实现子类上,物理宇宙范畴与计算宇宙范畴范畴等价,并讨论复杂性几何与统一时间刻度在该等价下的不变性。

### 6.1 等价公理

为了陈述等价定理,我们引入以下公理假设:

* 公理 E1(QCA 通用性)
任一 $U_{\mathrm{phys}}\in\mathbf{PhysUniv}^{\mathrm{QCA}}$ 都存在 QCA 实现;任一 $U_{\mathrm{comp}}\in\mathbf{CompUniv}^{\mathrm{phys}}$ 都存在 QCA 实现,其控制–复杂性几何与物理宇宙对象的统一时间刻度结构兼容。

* 公理 E2(连续极限存在性)
对任一物理可实现计算宇宙 $U_{\mathrm{comp}}$,其复杂性图在离散尺度 $h\to 0$ 下在 Gromov–Hausdorff 意义上收敛到某个控制流形 $(\mathcal M,G)$,并可进一步扩展为时空流形 $(M,g)$。

* 公理 E3(散射与时间刻度一致性)
QCA 的散射矩阵族 $S_{\mathrm{QCA}}(\omega;\theta)$ 在连续极限下逼近物理宇宙的散射数据 $\mathsf S(\omega)$,且统一时间刻度母尺在两者之间保持:

$$
\kappa_{\mathrm{QCA}}(\omega;\theta)
=
\kappa(\omega) + \text{可控误差}.
$$

* 公理 E4(模拟映射的物理实现)
任一范畴 $\mathbf{PhysUniv}^{\mathrm{QCA}}$ 中的态射可在 QCA 层面实现为局域可逆映射;任一 $\mathbf{CompUniv}^{\mathrm{phys}}$ 中的模拟映射可通过控制–散射系统的映射实现。

在这组公理下,我们可证明两个范畴在对象与态射层面互为拟逆。

### 6.2 主定理:范畴等价

**定理 6.1(范畴等价)**

在公理 E1–E4 下,函子

$$
F:\mathbf{PhysUniv}^{\mathrm{QCA}}\to\mathbf{CompUniv}^{\mathrm{phys}},
\quad
G:\mathbf{CompUniv}^{\mathrm{phys}}\to\mathbf{PhysUniv}^{\mathrm{QCA}}
$$

构成范畴等价,即存在自然同构

$$
\eta:\mathrm{Id}_{\mathbf{PhysUniv}^{\mathrm{QCA}}}
\xRightarrow{\ \sim\ }
G\circ F,
\quad
\epsilon:F\circ G
\xRightarrow{\ \sim\ }
\mathrm{Id}_{\mathbf{CompUniv}^{\mathrm{phys}}}.
$$

**证明纲要**

1. **本质满射性(对象层面)**

* 对任一 $U_{\mathrm{phys}}\in\mathbf{PhysUniv}^{\mathrm{QCA}}$,由公理 E1 有 QCA 实现,应用 $F$ 得到 $U_{\mathrm{comp}}=F(U_{\mathrm{phys}})$。再应用 $G$ 得到 $U_{\mathrm{phys}}' = G(U_{\mathrm{comp}})$。

* 由 E2–E3,QCA 的连续极限时空与散射数据回到原物理宇宙 $U_{\mathrm{phys}}$(在规范变换与等距同构意义下),因此存在自然同构

$$
\eta_{U_{\mathrm{phys}}}:U_{\mathrm{phys}}\xrightarrow{\ \simeq\ }U_{\mathrm{phys}}' = G(F(U_{\mathrm{phys}})).
$$

* 类似地,对任一 $U_{\mathrm{comp}}\in\mathbf{CompUniv}^{\mathrm{phys}}$,应用 $G$ 再应用 $F$ 得到 $U_{\mathrm{comp}}' = F(G(U_{\mathrm{comp}}))$。由 E1–E3 与 QCA 通用性,$U_{\mathrm{comp}}'$ 与 $U_{\mathrm{comp}}$ 同构(在模拟映射意义下),得到自然同构

$$
\epsilon_{U_{\mathrm{comp}}}:
F(G(U_{\mathrm{comp}}))
\xrightarrow{\ \simeq\ }
U_{\mathrm{comp}}.
$$

2. **忠实–充满性(态射层面)**

* 对任一物理态射 $f:U_{\mathrm{phys}}\to U_{\mathrm{phys}}'$,由 E4 可在 QCA 层构造局域可逆实现,从而在计算宇宙层面得到模拟映射 $F(f)$。
* 反过来,对任一模拟映射 $g:U_{\mathrm{comp}}\rightsquigarrow U_{\mathrm{comp}}'$,由 E4 可在控制–散射系统层面构造相应的物理映射 $G(g)$。
* 通过标准范畴论手段(见附录 C.1),可证明 $F$ 与 $G$ 在态射层面是满忠实的,即

$$
\mathrm{Hom}_{\mathbf{PhysUniv}^{\mathrm{QCA}}}(U_{\mathrm{phys}},U_{\mathrm{phys}}')
\cong
\mathrm{Hom}_{\mathbf{CompUniv}^{\mathrm{phys}}}(F(U_{\mathrm{phys}}),F(U_{\mathrm{phys}}')),
$$

$$
\mathrm{Hom}_{\mathbf{CompUniv}^{\mathrm{phys}}}(U_{\mathrm{comp}},U_{\mathrm{comp}}')
\cong
\mathrm{Hom}_{\mathbf{PhysUniv}^{\mathrm{QCA}}}(G(U_{\mathrm{comp}}),G(U_{\mathrm{comp}}')).
$$

综合对象层面的本质满射性与态射层面的满忠实性,即得范畴等价。

证毕。

### 6.3 复杂性几何与统一时间刻度的不变性

范畴等价不仅是集合论上的一一对应,还应保持关键几何结构。

**命题 6.2(复杂性几何不变性)**

在等价函子 $F,G$ 下:

1. 物理宇宙对象 $U_{\mathrm{phys}}$ 的统一时间刻度密度 $\kappa(\omega)$ 与其像 $F(U_{\mathrm{phys}})$ 的单步代价 $\mathsf C$ 所诱导的复杂性几何兼容,即离散复杂性距离在连续极限下与 $(\mathcal M,G)$ 的测地距离一致;
2. 对任一物理态射 $f$ 与对应模拟映射 $F(f)$,在复杂性几何上,测地距离被控制地保持,即存在常数 $c_1,c_2>0$ 使得

$$
c_1 d_G(\theta_1,\theta_2)
\le
d_G'(f_{\mathcal M}(\theta_1),f_{\mathcal M}(\theta_2))
\le
c_2 d_G(\theta_1,\theta_2).
$$

类似的不变性在从计算宇宙到物理宇宙的函子 $G$ 下也成立。证明依赖于统一时间刻度母尺与 Riemann 极限定理的稳定性,见附录 C.2。

---

## 附录 A:函子 $F$ 的细节与证明

### A.1 函子性证明

**命题 A.1**

构造 $F$ 满足 $F(\mathrm{id}) = \mathrm{id}$ 与 $F(f\circ g) = F(f)\circ F(g)$。

**证明**

1. 对任一 $U_{\mathrm{phys}}$,物理恒等态射对应 QCA 层的恒等酉算子,诱导基矢集上的恒等映射 $\mathrm{id}_X$。因此 $F(\mathrm{id}_{U_{\mathrm{phys}}}) = \mathrm{id}_{F(U_{\mathrm{phys}})}$。

2. 对态射复合,设

$$
f:U_{\mathrm{phys}}\to U_{\mathrm{phys}}',
\quad
g:U_{\mathrm{phys}}'\to U_{\mathrm{phys}}'',
$$

对应 QCA 层映射 $f_{\mathcal H},g_{\mathcal H}$,在配置集上诱导 $f_X,g_X$。则复合态射 $g\circ f$ 对应 QCA 层映射 $g_{\mathcal H}\circ f_{\mathcal H}$,在配置集上的像为 $g_X\circ f_X$。因此

$$
F(g\circ f) = g_X\circ f_X = F(g)\circ F(f).
$$

模拟条件中的复杂性控制参数 $(\alpha,\beta)$ 在复合后按照此前离散复杂性几何中的规则叠加,仍满足模拟映射的要求。

证毕。

---

## 附录 B:函子 $G$ 的细节与证明

### B.1 函子性证明

**命题 B.1**

构造 $G$ 满足 $G(\mathrm{id}) = \mathrm{id}$ 与 $G(f\circ g) = G(f)\circ G(g)$。

**证明思路**

1. 对任一 $U_{\mathrm{comp}}$,恒等模拟映射对应 QCA 层的恒等演化,控制流形、时空流形与散射数据均不变,因此 $G(\mathrm{id}_{U_{\mathrm{comp}}}) = \mathrm{id}_{G(U_{\mathrm{comp}})}$。

2. 对两个连续模拟映射 $f:U_{\mathrm{comp}}\to U_{\mathrm{comp}}'$、$g:U_{\mathrm{comp}}'\to U_{\mathrm{comp}}''$,在 QCA 层面有相应的控制–散射映射 $f_{\mathcal M},g_{\mathcal M}$ 与 $f_\omega,g_\omega$。复合模拟映射 $g\circ f$ 在控制与散射层面的像即为 $g_{\mathcal M}\circ f_{\mathcal M}$ 与 $g_\omega\circ f_\omega$,因此

$$
G(g\circ f)
=
(g_{\mathcal M}\circ f_{\mathcal M},g_{\mathcal F}\circ f_{\mathcal F},g_\omega\circ f_\omega)
=
G(g)\circ G(f).
$$

细节依赖于模拟映射在统一时间刻度与散射结构上的控制性条件,保证组合后的映射仍为物理态射。

证毕。

---

## 附录 C:等价与几何不变量的证明纲要

### C.1 满忠实性

对任意 $U_{\mathrm{phys}},U_{\mathrm{phys}}' \in\mathbf{PhysUniv}^{\mathrm{QCA}}$,QCA 实现保证态射在 QCA 层可视为局域可逆酉变换或等距嵌入,其在配置集上的像即为模拟映射。
反之,任意 $\mathbf{CompUniv}^{\mathrm{phys}}$ 中的模拟映射,对应于 QCA 层的局域控制操作,对应的连续极限即为物理态射。这给出 Hom 集之间的一一对应,从而证明满忠实性。

### C.2 复杂性几何不变性

由统一时间刻度母尺,度量 $G$ 与散射数据通过 $Q(\omega;\theta)$ 一起变动。
QCA 层的局域可逆变换在散射理论中对应规范变换,不改变统一时间刻度密度的谱内容,从而测地距离在 Lipschitz 意义下保持。
因此在范畴等价下,复杂性几何与统一时间刻度是"软不变量":在等价对象之间,只在常数尺度上变化。

(详细技术证明需利用 Birman–Krein 型公式与统一时间刻度对谱流的控制,篇幅所限不再展开。)
