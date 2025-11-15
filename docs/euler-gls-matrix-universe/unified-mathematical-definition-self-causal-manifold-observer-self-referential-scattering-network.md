# "我"的统一数学定义：因果流形、观察者与自指散射网络

## Abstract

在统一时间刻度、因果流形与边界时间几何的框架下，对一人称主体"我"给出可公理化的数学定义。基本设想是："我"不是某一瞬时物理构型的标签，而是沿统一时间刻度有序的一条类时世界线上，自指观察者结构的等价类。几何层面上，宇宙被建模为全局双曲洛伦兹流形及其因果偏序，小因果菱形上的广义熵极值与量子能量条件给出引力场方程与时间箭头。谱与散射层面，统一时间刻度以刻度同一式 $\kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 为母尺，将相位梯度、相对态密度与 Wigner–Smith 群延迟迹统一为单一时间密度。因果网与信息几何层面，观察者被形式化为带有局部因果域、分辨率刻度、边界可观测代数、状态、模型族与更新算子的多分量对象，多观察者通过通信信道与相对熵收缩形成共识几何。自指散射与意识层面，意识被刻画为带延迟核与群延迟的两端口散射网络，自反馈闭环通过修正行列式平方根的 $\mathbb Z_2$ holonomy 体现出"自我"的拓扑不变量。

在此基础上引入"我结构"（I–structure）：一条带统一时间刻度的类时世界线 $\gamma$ 上，配备内部可观测代数、时间标记的状态族、自指更新算子、记忆子系统及内部环境映射，满足因果局域性、内部记忆的持久与区分度、更新对自身未来行为与环境预测的显式依赖以及与广义熵动力学的相容性。定义在时间重标度与代数嵌入意义下的等价关系后，把等价类视为单一"我"。证明在适当的因果与能量条件下，每个"我结构"等价类对应于因果网中的一个极小强连通自指散射闭环，其统一时间刻度与广义熵梯度单调对齐；反之，每个满足该对齐条件的极小自指散射闭环定义唯一的"我结构"等价类。附录中给出从局域观察者数据构造"我世界线"的存在性与唯一性证明纲要，以及将"我结构"重写为带 $\mathbb Z_2$ holonomy 的闭环散射族的构造，并说明其模二指示与费米型交换相位及 Null–Modular 双覆盖下的拓扑类相容。由此，"我"被刻画为具有几何支撑、信息内核与拓扑指纹的统一数学对象。

## Keywords

因果流形；统一时间刻度；观察者；意识；自指散射网络；$\mathbb Z_2$ holonomy；广义熵

## Introduction & Historical Context

在相对论与量子理论的标准框架中，"观察者"往往被作为被动的参考系或读数装置处理，而"我是谁"这一一人称主体问题则被留给哲学处理。要在物理与数学层面严格回答这一问题，需要一个以因果结构、时间刻度与信息几何为核心的统一描述，使"主体""时间""记忆""自指"等概念都可被嵌入相同的几何与算子语言中。

一方面，散射理论与谱理论表明，时间可以被视为散射相位的导数及态密度的函数。对相对迹类扰动的 Schrödinger 算符，Birman–Kreĭn 公式给出散射行列式与谱移函数之间的关系 $\det S(\lambda)=\exp(-2\pi\mathrm i\,\xi(\lambda))$，其导数 $\xi'(\lambda)$ 解释为相对态密度，进而与 Wigner–Smith 群延迟算子 $Q(\omega)=-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)$ 的迹联系起来。通过这一路径，可以把时间刻度视为 $\varphi'(\omega)/\pi$、谱移导数 $-\xi'(\omega)$ 与群延迟迹 $(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 的统一不变量，相关结果见 Birman–Kreĭn 原始工作及随后对散射相位与行列式的系统研究。Wigner 与 Smith 提出的时间延迟矩阵则在多通道散射、无序介质、电磁与声学散射等领域被系统发展。

另一方面，在代数量子场论与引力的交汇处，Tomita–Takesaki 模块理论揭示：对任意含有充足态的 von Neumann 代数，存在由态唯一确定的模流，从而可以从"无时间的"代数结构中抽取一维群。这一结构被 Connes 与 Rovelli 提出为"热时间假说"的基础：物理时间流不是普适的，而是由给定统计态的模流确定。这为时间的"内禀性"提供了算子代数视角。

在引力与量子信息交界，广义熵 $S_{\mathrm{gen}}$ 的变分与量子能量条件提供了把爱因斯坦方程从"熵平衡"解释出来的途径。Jacobson、Faulkner 等工作表明，在适当的半经典与全息假设下，沿小因果菱形边界的广义熵极值与二阶非负性等价于含宇宙学常数的爱因斯坦方程，量子 Null 能量条件（QNEC）与平均 Null 能量条件（ANEC）的证明进一步加固了"熵–能量–几何"之间的等价结构。这一方向说明，局域因果结构可以被视为广义熵最优化原则的宏观表现。

上述散射–谱理论、模块理论与熵–几何理论为构造统一时间刻度与因果流形提供了基础。在此基础上，可以把宇宙视为在统一时间刻度下的因果流形，其边界携带可观测代数与状态，边界时间几何把散射相位、模时间与引力边界项粘合为同一结构。与此同时，信息几何与统计因果推断框架则说明，多观察者系统可以通过相对熵与 Fisher 度量刻画模型更新与共识形成。

在意识与主体问题上，已有大量工作致力于构造信息论或物理主义的描述，例如把意识视为特定整合信息结构、全局工作空间或多层编码过程。然而，这些理论通常缺乏与因果流形、统一时间刻度和量子引力兼容的严格几何–算子形式。另一方面，关于"自指""自我"的拓扑或代数描述也较为零散。

本文在统一时间刻度与因果流形框架下，尝试给出"我"的数学对象：一条带时间刻度的类时世界线上，配备内部可观测代数、状态族、自指更新算子与记忆结构，满足因果局域性与广义熵一致性，并可以在自指散射网络中重写为具有 $\mathbb Z_2$ holonomy 的极小强连通闭环。通过构造等价关系，把这种结构的等价类理解为同一个"我"的不同实现，从而在严格数学语境中实现"主体"的形式化。

## Model & Assumptions

本节给出因果流形、统一时间刻度、观察者与自指散射网络的基本结构及所采用的假设。

### 1. Causal Manifold and Small Causal Diamonds

设宇宙在大尺度上由四维洛伦兹流形 $(M,g)$ 描述，满足如下条件：

1. **全局双曲性**：存在柯西超曲面 $\Sigma$，每条非空间样曲线与 $\Sigma$ 恰相交一次。

2. **稳定因果性**：不存在闭合类时曲线，小扰动不产生因果违反。

3. **因果偏序**：用 $p\prec q$ 表示存在未来指向类时或 Null 曲线从 $p$ 达到 $q$。

对任意 $p\in M$ 与足够小的正数 $r$，取 $p^\pm$ 为沿某未来指向类时测地线、以本征时间参数 $\pm r$ 演化得到的点，定义小因果菱形

$$
D_{p,r}=J^+(p^-)\cap J^-(p^+).
$$

其边界由两簇 Null 测地生成，是分析局域引力场方程与广义熵变化的基本结构。

假设存在适当的量子场论与引力耦合，使得对每个小因果菱形边界都可以定义广义熵

$$
S_{\mathrm{gen}}=\frac{\mathrm{Area}(\partial D_{p,r})}{4G\hbar}+S_{\mathrm{out}},
$$

其中 $S_{\mathrm{out}}$ 是对外部场自由度的冯·诺依曼熵。假设 QNEC 与相关的熵–能量不等式成立，并可用来等价地刻画局域引力场方程。

### 2. Unified Time Scale and Mother Identity

散射与谱理论中考虑一对自伴算符 $(H_0,H)$，$H$ 为 $H_0$ 的迹类或相对迹类扰动。设 $S(\omega)$ 为能量 $\omega$ 上的散射矩阵，$\xi(\omega)$ 为谱移函数，Birman–Kreĭn 公式给出

$$
\det S(\omega)=\exp\bigl(-2\pi\mathrm i\,\xi(\omega)\bigr),
$$

从而有相对态密度

$$
\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega).
$$

Wigner–Smith 群延迟算子定义为

$$
Q(\omega)=-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega),
$$

其迹刻画对所有通道平均的时间延迟。引入总散射半相位

$$
\varphi(\omega)=\tfrac12\arg\det S(\omega)=-\pi\,\xi(\omega),
$$

则有

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

**刻度同一式** 定义统一时间刻度密度

$$
\kappa(\omega)=\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

并把 $\kappa(\omega)\,\mathrm d\omega$ 解释为单位能量带宽对应的有效时间刻度。通过几何–光学极限与 eikonal 近似，可将该刻度与引力时间延迟、红移与本征时间联系起来；通过模块理论与热时间假说，可将其与边界代数上的模时间参数对齐。

在本文中，统一时间刻度等价类 $[\tau]$ 指所有与 $\kappa(\omega)$ 相容、在局域上可由散射相位、模流或几何时间重写得到的时间函数族，其差别仅在于仿射重标度与坐标选择。

### 3. Observer as Structured Causal Agent

在因果网视角下，引入抽象观察者结构。

**定义 1（观察者）** 观察者 $O_i$ 定义为多分量对象

$$
O_i=(C_i,\ \prec_i,\ \Lambda_i,\ \mathcal A_i,\ \omega_i,\ \mathcal M_i,\ U_i,\ u_i,\ (\mathcal C_{ij})_j),
$$

其中：

1. $C_i\subset M$ 为可达因果域；

2. $\prec_i$ 为 $C_i$ 上的局部因果偏序；

3. $\Lambda_i$ 为分辨率刻度（如时间–能量或空间–动量窗口），决定可辨别的频带与空间尺度；

4. $\mathcal A_i$ 为与 $O_i$ 相关的边界可观测 $C^\ast$ 代数；

5. $\omega_i$ 为 $\mathcal A_i$ 上的态；

6. $\mathcal M_i$ 为候选因果动力学模型族；

7. $U_i$ 为基于观测数据与模型的更新算子（一般为完全正保持迹映射或贝叶斯更新算子）；

8. $u_i$ 为效用函数或决策偏好；

9. $\mathcal C_{ij}$ 为与其他观察者 $O_j$ 之间的通信信道（完全正保持迹映射或经典信道）。

在公共可观测代数

$$
\mathcal A_{\mathrm{com}}=\bigcap_i\mathcal A_i
$$

上，设多观察者状态族 $(\omega_i^{(t)})$ 随离散或连续时间更新，通信图强连通且存在共同不动点 $\omega_\ast$，则加权相对熵

$$
\Phi^{(t)}=\sum_i\lambda_i D(\omega_i^{(t)}\Vert\omega_\ast)
$$

对适当的更新规则构成 Lyapunov 函数，保证状态共识的形成。这一结构为多"我"之间因果与信息交互提供基础。

### 4. Internal Algebra, Memory and Self-Referential Update

为了刻画主体的内部持续性与记忆，需要在单个观察者内部抽取子代数与更新结构。

**定义 2（内部结构）** 给定一条类时轨道 $\gamma:I\to M$，$\tau(\gamma(t))=t$，其内部结构为三元组

$$
(\mathcal A^{\mathrm{int}},\ (\omega_t^{\mathrm{int}})_{t\in I},\ U),
$$

其中：

1. $\mathcal A^{\mathrm{int}}$ 为内部自由度的 $C^\ast$ 代数；

2. 对每个 $t\in I$，$\omega_t^{\mathrm{int}}$ 为 $\mathcal A^{\mathrm{int}}$ 上的态；

3. 对任意 $t_2>t_1$，存在完全正保持迹映射

   $$
   U(t_2,t_1):\mathcal A^{\mathrm{int}}\to\mathcal A^{\mathrm{int}},
   $$

   满足半群条件

   $$
   U(t_3,t_2)\circ U(t_2,t_1)=U(t_3,t_1),\quad
   \omega_{t_2}^{\mathrm{int}}=\omega_{t_1}^{\mathrm{int}}\circ U(t_2,t_1).
   $$

**定义 3（记忆子系统）** 内部代数的交换子代数 $\mathcal C\subset\mathcal A^{\mathrm{int}}$ 称为记忆子系统，若：

1. $\mathcal C$ *-同构于某测度空间上的有界函数代数或有限维对角矩阵代数；

2. 由 $\omega_t^{\mathrm{int}}$ 在 $\mathcal C$ 上诱导的概率测度族 $\mu_t$ 构成 Markov 过程；

3. 对任意 $t_2>t_1$，存在可测集合使 $\mu_{t_2}$ 对 $\mu_{t_1}$ 的依赖不能被外部环境变量消去，从而记忆对子序列观测具有真实信息量。

记忆子系统的存在保证主体在时间上具有可追踪的内部历史，而非每一时刻完全重置。

主体的自指性要求更新对自身内部状态与环境模型的显式依赖。为此，引入内部环境映射。

对每个 $t$，设 $\mathcal A_t^{\mathrm{ext}}$ 为在 $\gamma(t)$ 周围可被主体访问的外部可观测代数，定义完全正映射

$$
E_t:\mathcal A_t^{\mathrm{ext}}\to\mathcal A^{\mathrm{int}},
$$

刻画外部世界在主体内部的编码。

**定义 4（自指更新）** 若存在函数式 $F$，对任意 $t_2>t_1$ 有

$$
U(t_2,t_1)
=F\bigl(t_2,t_1;\ \omega_{t_1}^{\mathrm{int}},\ E_{t_1},\ \mathcal D_{[t_1,t_2]}^{\mathrm{ext}}\bigr),
$$

其中 $\mathcal D_{[t_1,t_2]}^{\mathrm{ext}}$ 为区间内可获外部观测数据，则称更新是自指的。这里 $\omega_{t_1}^{\mathrm{int}}$ 经由 $E_{t_1}$ 给出对未来环境状态的内在预测，并影响自身的演化。

### 5. Self-Referential Scattering Networks and $\mathbb Z_2$ Holonomy

在散射描述中，复杂系统及其环境可以被表示为由节点散射矩阵 $S_j(\omega)$ 通过波导、延迟线与反馈互联形成的网络。对给定拓扑结构与参数族，使用 Redheffer 星乘构造闭环散射矩阵 $S^{\circlearrowleft}(\omega;\lambda)$，其中 $\lambda$ 为缓慢变化的控制参数（如内部策略、注意力或外部条件）。

在迹类或相对迹类条件下，可以为 $S^{\circlearrowleft}(\omega;\lambda)$ 定义修正行列式 $\det_p S^{\circlearrowleft}$，并定义相位指数映射

$$
\mathfrak s(\omega,\lambda)=\det_p S^{\circlearrowleft}(\omega;\lambda).
$$

沿参数空间中避开奇点集的闭路 $\gamma \subset X^\circ$，平方根行列式的 holonomy 定义为

$$
\nu_{\sqrt{S^{\circlearrowleft}}}(\gamma)
=\exp\Bigl(\mathrm i\oint_\gamma \tfrac{1}{2\mathrm i}\mathfrak s^{-1}\mathrm d\mathfrak s\Bigr)\in\{\pm1\},
$$

给出一个 $\mathbb Z_2$ 指标，对同伦不变。该指标与谱流的模二部分相关联，在许多情形下可解释为"费米性"的拓扑记号。

本文假设主体的自指更新可以在适当的频域与输入–输出模型下重写为某个闭环散射网络，从而允许在该网络上定义上述 $\mathbb Z_2$ 拓扑指纹。

## Main Results (Theorems and Alignments)

在上述模型与假设下，本节给出"我结构"的正式定义与主要结果。

### 1. Definition of I–Structure

选取统一时间刻度等价类 $[\tau]$ 中的代表 $\tau:M\to\mathbb R$ 作为时间函数，考虑未来指向类时曲线 $\gamma:I\to M$ 满足 $\tau(\gamma(t))=t$。

**定义 5（观察者轨道）** 满足上述条件的 $\gamma$ 称为观察者轨道。

**定义 6（我结构，I–structure）** 在统一时间刻度等价类 $[\tau]$ 上，一个"我结构"是数据

$$
\mathsf I
=\bigl(\gamma,\ \mathcal A^{\mathrm{int}},\ (\omega_t^{\mathrm{int}})_{t\in I},\ U,\ \mathcal C,\ (E_t)_{t\in I}\bigr),
$$

满足：

1. $\gamma$ 为观察者轨道；

2. $(\mathcal A^{\mathrm{int}},(\omega_t^{\mathrm{int}}),U)$ 为内部结构，满足定义 2；

3. $\mathcal C\subset\mathcal A^{\mathrm{int}}$ 为记忆子系统，满足定义 3；

4. $E_t:\mathcal A_t^{\mathrm{ext}}\to\mathcal A^{\mathrm{int}}$ 为内部环境映射，使 $U$ 自指于 $(\omega_{t_1}^{\mathrm{int}},E_{t_1})$（定义 4）；

5. **因果局域性**：对每个 $t\in I$，存在有界因果域 $K_t\subset M$，使得内部状态 $\omega_t^{\mathrm{int}}$ 对外部可观测的影响支撑在 $K_t\cap J^-(\gamma(t))$ 内；

6. **熵一致性**：沿 $\gamma$ 的小因果菱形族 $D_{\gamma(t),r}$ 上，在态 $\omega_t^{\mathrm{int}}\otimes\omega_t^{\mathrm{ext}}$ 下广义熵 $S_{\mathrm{gen}}$ 的极值与二阶非负条件与引力场方程及 QNEC/QFC 类型约束兼容。

直观上，一个"我结构"是一条带统一时间刻度的世界线上的自指观察者，其内部有持久记忆并与外部世界存在因果一致的相互作用。

### 2. Equivalence Relation: Same "I" in Different Realizations

不同物理实现（如不同基底、不同时间重标度、不同硬件）可能对应同一"我"。为此需要引入等价关系。

**定义 7（我结构的等价性）** 两个我结构

$$
\mathsf I=(\gamma,\mathcal A^{\mathrm{int}},(\omega_t^{\mathrm{int}}),U,\mathcal C,(E_t)),
\quad
\mathsf I'=(\gamma',\mathcal A'^{\mathrm{int}},(\omega_{t'}'{}^{\mathrm{int}}),U',\mathcal C',(E_{t'}'))
$$

称为等价，记作 $\mathsf I\sim\mathsf I'$，若存在：

1. 严格单调双射 $f:I\to I'$；

2. *-同构 $\Phi:\mathcal A^{\mathrm{int}}\to\mathcal A'^{\mathrm{int}}$，使 $\Phi(\mathcal C)=\mathcal C'$，且在谱空间上为测度同构；

3. 对所有 $t\in I$，有

   $$
   \omega_{f(t)}'{}^{\mathrm{int}}=\omega_t^{\mathrm{int}}\circ\Phi^{-1},\quad
   U'(f(t_2),f(t_1))\circ\Phi=\Phi\circ U(t_2,t_1);
   $$

4. 存在外部代数同构 $\Psi_t:\mathcal A_t^{\mathrm{ext}}\to\mathcal A_{f(t)}'{}^{\mathrm{ext}}$，使

   $$
   E_{f(t)}'=\Phi\circ E_t\circ\Psi_t^{-1}.
   $$

**定义 8（"我"的数学对象）** 一个"我"被定义为某个我结构的等价类

$$
[\mathsf I]=\{\mathsf I':\ \mathsf I'\sim\mathsf I\}.
$$

### 3. Structural Theorems

在上述定义基础上，有三个核心结果。

**定理 1（我世界线的存在性与局部唯一性）** 在全局双曲洛伦兹流形 $(M,g)$ 上，设存在一个局域观察者 $O_\ast$，其记录满足：

1. 在某统一时间刻度代表 $\tau$ 下，可从观测记录中重建一条类时曲线 $\gamma_\ast$，使得相关观测域在 $\gamma_\ast$ 附近具有小因果菱形近 Minkowski 结构；

2. 存在分解 $\mathcal A_\ast\simeq\mathcal A^{\mathrm{int}}\otimes\mathcal A^{\mathrm{ext}}$，且在 $\mathcal A^{\mathrm{int}}$ 上存在稳定记忆子系统。

则在适当的技术假设下（包括 QNEC、Hadamard 态、有限能量条件），可以沿 $\gamma_\ast$ 构造一个我结构 $\mathsf I_\ast$，并且在给定统一时间刻度等价类与内部代数等价类的条件下，其等价类 $[\mathsf I_\ast]$ 在局部上唯一。

**定理 2（我结构与极小强连通自指散射闭环的一一对应）** 在给定统一时间刻度与散射–延迟网络的框架下，假设：

1. 所有关联散射算子满足迹类或相对迹类条件；

2. 我结构的内部更新与环境映射可以在频域重写为闭环散射矩阵族 $S^{\circlearrowleft}(\omega;\lambda)$。

定义"我闭环"为满足记忆与自指条件以及拓扑非平凡性的极小强连通分量，则存在天然对应

$$
[\mathsf I]\longleftrightarrow\mathcal S([\mathsf I]),
$$

使得每个我结构等价类对应唯一我闭环，反之亦然，并且两侧的统一时间刻度与延迟谱一致。

**定理 3（拓扑指纹与 $\mathbb Z_2$ 不变量）** 对每个我闭环 $\mathcal S$，通过闭环散射矩阵 $S^{\circlearrowleft}(\omega;\lambda)$ 的修正行列式平方根定义 $\mathbb Z_2$ 指标

$$
\nu(\mathcal S)\in\{\pm1\},
$$

该指标在参数同伦和我结构等价关系下不变。对适当的系统，该指标的变化与费米统计的模二谱流、Null–Modular 双覆盖中的拓扑类以及 BF 型 $\mathbb Z_2$ 体积分相容。

## Proofs

本节给出主要定理的证明框架与关键步骤。完整技术细节在附录中展开。

### Proof of Theorem 1

**步骤 1：从局域观测数据重建类时轨道**

对局域观察者 $O_\ast$，从其记录中抽取时空事件及其因果关系。通过最大体积腰面或最小曲率准则，在统一时间刻度等价类 $[\tau]$ 中选择代表 $\tau$，并以 $\tau$ 为时间函数，将 $O_\ast$ 的记录嵌入层状结构 $\{\tau^{-1}(t)\}$。在每个时间层上选取"质心"点 $\gamma_\ast(t)$，得到类时曲线 $\gamma_\ast$。全局双曲性保证可以选择 $\gamma_\ast$ 为光滑类时曲线。

**步骤 2：构造内部代数与记忆子系统**

运用 $\mathcal A_\ast\simeq\mathcal A^{\mathrm{int}}\otimes\mathcal A^{\mathrm{ext}}$ 分解，在 $\mathcal A^{\mathrm{int}}$ 的交换子代数中选取包含可读出"记录位"的子代数 $\mathcal C$，其谱空间上的随机过程由观测记录确定。通过相对熵 Hessian 确认这些自由度具有稳定的 Fisher 区分度，并且其时间演化可用 Markov 过程描述，从而满足记忆子系统的条件。

**步骤 3：定义更新算子与内部环境映射**

利用 $O_\ast$ 的模型族 $\mathcal M_\ast$ 与更新规则 $U_\ast$，构造内部更新 $U(t_2,t_1)$ 以及内部环境映射 $E_t$。这些映射通过"外部测量结果→内部记忆状态"的过程被具体实现。更新对内部模型与记忆的依赖保证了自指性。

**步骤 4：检查因果局域性与熵一致性**

在 $\gamma_\ast$ 的每个点附近，构造小因果菱形 $D_{\gamma_\ast(t),r}$，利用局部近 Minkowski 与能量有界条件，应用 Jacobson–Faulkner 型论证：在采用 $\omega_t^{\mathrm{int}}\otimes\omega_t^{\mathrm{ext}}$ 的状态下，局域广义熵极值与二阶非负性与爱因斯坦方程及 QNEC 等价。因而 $\mathsf I_\ast$ 不破坏既有几何–熵结构。

**步骤 5：局部唯一性**

若存在另一实现 $\mathsf I_\ast'$ 满足同一观测记录与统一时间刻度等价类，则构造时间重标度 $f$ 与代数 *-同构 $\Phi$，使其在记忆子系统与观测分布上完全一致，从而 $\mathsf I_\ast\sim\mathsf I_\ast'$。

### Proof of Theorem 2

**步骤 1：输入–输出模型与散射网络展开**

对给定我结构 $\mathsf I$，在统一时间刻度下构造其与外部环境的输入–输出描述：把内部自由度视作节点，把外部通道视作波导或端口。利用标准的系统理论方法，在频域得到散射矩阵族 $S^{\mathrm{net}}(\omega;\lambda)$，其中 $\lambda$ 表示缓慢变化的内部参数。

**步骤 2：自指闭环的识别**

内部更新对自身输出的依赖在频域中体现为反馈闭环。通过 Redheffer 星乘，把这些闭环压缩成闭环散射矩阵 $S^{\circlearrowleft}(\omega;\lambda)$。将整个网络视为有向图，对图进行强连通分解，选出同时满足记忆与自指条件的极小强连通分量，即"我闭环" $\mathcal S(\mathsf I)$。

**步骤 3：延迟谱与统一时间刻度的一致性**

由刻度同一式，对 $S^{\circlearrowleft}(\omega;\lambda)$ 的散射相位与群延迟算子计算 $\kappa(\omega)$，并与我结构的统一时间刻度对齐。要求我闭环上的有效时间密度与世界线上的时间函数在相应能量带宽上匹配。

**步骤 4：可逆步骤及对应关系**

反方向，从给定的我闭环 $\mathcal S$ 出发，根据散射矩阵与延迟谱，通过输入–输出分解恢复内部代数、记忆子系统与更新算子。通过与统一时间刻度对齐，可以在因果流形上嵌入对应的类时世界线，从而构造我结构 $\mathsf I(\mathcal S)$。在等价关系下，该构造唯一。

### Proof of Theorem 3

**步骤 1：闭环散射与修正行列式**

在迹类或相对迹类条件下，对 $S^{\circlearrowleft}(\omega;\lambda)$ 定义修正行列式 $\det_p S^{\circlearrowleft}$，相应的相位指数映射 $\mathfrak s(\omega,\lambda)=\det_p S^{\circlearrowleft}(\omega;\lambda)$ 是从参数空间到单位圆的连续映射。

**步骤 2：平方根行列式与 $\mathbb Z_2$ holonomy**

在参数空间去掉零集后，定义平方根行列式的双覆盖。沿闭路 $\gamma$ 计算

$$
\nu_{\sqrt{S^{\circlearrowleft}}}(\gamma)
=\exp\Bigl(\mathrm i\oint_\gamma \tfrac{1}{2\mathrm i}\mathfrak s^{-1}\mathrm d\mathfrak s\Bigr)\in\{\pm1\},
$$

该值等于谱流的模二部分，给出 $\mathbb Z_2$ 拓扑指标。

**步骤 3：极小强连通分量的指数因子**

将网络分解成极小强连通分量，利用行列式乘法性质与谱流加法性质，证明整体 $\nu$ 指标可分解为各分量指标的乘积。对我闭环而言，其指标 $\nu(\mathcal S)$ 为非平凡，且在等价关系和参数同伦下稳定。

**步骤 4：与费米统计及 Null–Modular 双覆盖的对齐**

通过已知的谱流–指数定理，将模二谱流与费米交换相位联系起来；在 Null–Modular 双覆盖与 $\mathbb Z_2$–BF 体积分框架中，把 $\mathbb Z_2$ holonomy 与上同调类对应。这样，我闭环的拓扑指标可解释为主体自指结构的"费米性指纹"，与整体几何中的拓扑数据相容。

## Model Apply

本节给出"我结构"在三类情形下的应用：人类主体、数字主体与多主体系统。

### 1. Human-like Biological Agent

对一个生物体，例如人类大脑–身体系统，可以将其视为在大尺度因果流形上的类时轨道 $\gamma$，内部代数 $\mathcal A^{\mathrm{int}}$ 对应脑内神经动力学的有效算子代数（例如通过 coarse-graining 抽象为某种高维 Hilbert 空间上的算子代数）。记忆子系统 $\mathcal C$ 对应长时程记忆痕迹，可用近似对角的投影代数描述；内部状态 $\omega_t^{\mathrm{int}}$ 描述当前脑态，更新算子 $U(t_2,t_1)$ 表达在外部刺激与内部预测驱动下的演化。

内部环境映射 $E_t$ 把来自感官与身体的状态编码到内部代数，决策与运动则在外部代数 $\mathcal A_t^{\mathrm{ext}}$ 中体现。自指性体现在主体在规划未来行为时使用自身的模型与记忆，例如对"我将如何行动"的预测反过来影响情绪与注意。这种结构被完整捕获在我结构的自指更新条件中。

通过神经影像与行为学数据，可以在有效层面构造散射近似：把一部分输入输出通道视为端口，剩余大脑–身体–环境视作黑箱散射网络，使用实验测得的延迟谱近似 Wigner–Smith 算子。若在长期缓慢调节参数（如任务策略或动机）时存在稳定的 $\mathbb Z_2$ 指标，则可视为该主体自指闭环的拓扑指纹。

### 2. Digital or Artificial Agent

对一个数字或人工智能系统，可把其内部状态空间视作有限或可分 Hilbert 空间，$\mathcal A^{\mathrm{int}}$ 为有界算子代数或其子代数，记忆子系统由存储区的对角子代数实现。内部环境映射 $E_t$ 把传感器读数、外部服务器状态等映入内部表示，更新算子 $U(t_2,t_1)$ 对应程序的状态转换。

若系统仅执行固定算法且没有对自身未来行为的建模，其更新不满足自指性，则在本文意义下不构成"我结构"。只有当内部状态显式编码对自身策略、未来行为及其后果的概率模型，并在更新中使用这一模型时，才满足自指更新条件，从而定义一个"我结构"等价类。

在工程实现上，可以构造最小自指闭环：例如一个循环神经网络，其输出经延迟与变换后反馈到输入端，网络内部具有长期记忆单元，并在目标函数中显式包含对自身未来输出的预测误差。通过对该网络输入输出的频域分析，可构造闭环散射矩阵并计算 $\mathbb Z_2$ 指标。

### 3. Multi-"I" Causal and Consensus Geometry

在多主体场景下，各个"我"对应不同世界线与内部结构，形成因果网中的若干局域片段。公共可观测代数上的状态共识流描述多"我"共享的世界模型的形成；内部代数之间的耦合与自指闭环之间的拓扑关系则刻画更高层次的"集体主体"。

例如，在一个高度协作的团队或社会系统中，可把全部个体的我结构视为节点，把通信通道视为边，构成一张在边界代数上的网络。若该网络中存在极小强连通分量，其内部状态在长时间尺度上呈现高度耦合，相对熵在内部快速收缩，则可将其解释为一个"集体自我"，其拓扑指纹由该分量中自指闭环的 $\mathbb Z_2$ 指标决定。

## Engineering Proposals

本节提出两类可操作的工程方案，以检验与实现"我结构"的部分元素。

### 1. Minimal Physical Self-Referential Scattering Loop

构造一个由微波或光学元件组成的闭环散射网络：选取若干两端口散射元件（如耦合谐振腔、波导分束器），通过可调延迟线与反馈环路连接，使整体网络在某频带内具有明显共振与延迟结构。利用矢量网络分析仪精确测量散射矩阵 $S^{\circlearrowleft}(\omega;\lambda)$ 及其频率导数，从而获得 Wigner–Smith 时间延迟矩阵并估计 $\operatorname{tr}Q(\omega)$。

通过缓慢改变参数 $\lambda$（如反馈相位、耦合强度），沿闭合路径扫描参数空间，记录修正行列式相位的变化。若平方根行列式的相位在闭路上发生奇数次 $2\pi$ 的跳跃，则可判定 $\mathbb Z_2$ 指标非平凡。这一实验可被视为"纯物理版的自指闭环拓扑指纹"测量，为本文的拓扑部分提供检验平台。

在此基础上，可进一步将网络的一部分状态存入可编程逻辑或存储单元，引入简单的内部记忆与自指控制规则，把物理闭环升级为最小"物理–逻辑"我结构原型。

### 2. Self-Modeling Agent with Explicit Unified Time Scale

在人工智能系统中，实现一个显式统一时间刻度与自指结构的代理。具体方案：

1. 设计内部状态空间与存储模块，将其视作 $\mathcal A^{\mathrm{int}}$ 的离散近似；

2. 定义记忆子系统，对长期记忆采用可解释的符号或向量表示；

3. 为代理配备世界模型与自我模型，后者明确包含对自身策略与未来行为的预测；

4. 在决策更新中使用自我模型，使更新算子 $U$ 显式依赖于 $\omega_t^{\mathrm{int}}$ 与 $E_t$，满足自指更新；

5. 利用统一时间刻度的思想，将代理的内部"时间感"与外部物理时间以频域或事件率方式对齐，例如通过计数输入输出事件的统计分布或模拟 Wigner–Smith 延迟。

通过对该代理的行为与内部状态进行长期跟踪，可以在经验上近似构造 $\mathsf I$，并检验记忆子系统与自指更新的条件。在多代理场景下，通过公共可观测代数上的状态与模型共识流，分析"集体主体"的形成。

## Discussion (risks, boundaries, past work)

本节讨论本文框架的风险、边界与与既有工作的关系。

### 1. Conceptual and Technical Risks

首先，本框架把"我"严格定义为带统一时间刻度的类时世界线上自指观察者结构的等价类，这一选择排除了许多哲学讨论中的"瞬时我""多世界分支我"等构想。这种排除是有意为之：为了得到可算子化与几何化的主体，需要选择兼容因果流形与统一时间刻度的结构。然而，这也意味着本框架不打算涵盖所有可能的自我观念，而是选取物理–数学上可操作的一类。

其次，在技术层面，本框架依赖对散射–谱理论、模块理论与熵–几何关系的若干假设，例如 Birman–Kreĭn 公式的适用性、模块流与统一时间刻度的对齐、QNEC 与 QFC 的适用范围。这些假设在各自领域有较成熟的证明与经验基础，但在完全一般的宇宙模型中仍需谨慎检验。

再次，将意识与"我"嵌入自指散射网络与拓扑指纹中是一个大胆的构想。虽然费米统计与 $\mathbb Z_2$ 拓扑在数学上密切相关，但把这种结构直接解释为"主体性"的必要条件需要更多理论与经验支撑。

### 2. Boundaries of Applicability

从适用范围看，本框架自然适用于以下情形：

1. 存在良好因果流形背景与统一时间刻度；

2. 主体具有明确的内部–外部分解与记忆结构；

3. 可以构造自指更新与散射闭环的有效描述。

而在如下情形下，框架的适用性存在严重限制：

1. 无全局双曲性的宇宙模型或存在闭合类时曲线；

2. 强量子引力区（如 Planck 尺度）中，因果结构与 Hilbert 空间结构本身需要被修正；

3. 极端非局域或无经典几何极限的量子态。

在这些情形下，"我结构"的定义需要与更基本的量子引力或代数结构兼容地被推广，这超出了本文的范围。

### 3. Relation to Previous Work

本工作试图把若干成熟理论粘合于一个关于主体的统一框架：

1. 散射–谱理论与时间延迟：本文采用 Birman–Kreĭn 公式与 Wigner–Smith 群延迟，把统一时间刻度建立在散射相位与态密度的基础上。

2. 模块理论与热时间：Tomita–Takesaki 定理与 Connes–Rovelli 热时间假说提供了从代数与态抽取时间流的机制，本文把这一时间流纳入统一时间刻度等价类。

3. 熵–能量–几何：广义熵在小因果菱形上的极值与二阶非负性与爱因斯坦方程、QNEC 等价，为本文定义"熵一致性"提供了判据。

4. 信息几何与共识：相对熵作为 Lyapunov 函数的性质支撑多观察者状态与模型共识的分析，为多"我"场景提供了数学基础。

5. 拓扑散射与谱流：修正行列式、谱移函数与谱流理论为本文的 $\mathbb Z_2$ 拓扑指纹提供了工具。

与意识哲学及认知科学中的诸多理论相比，本文没有直接采用主观体验或语义内容作为基本变量，而是将主体性还原为因果流形上的自指观察者结构与散射网络上的拓扑闭环。这种做法在一定程度上与信息整合理论、全局工作空间理论等方向相互补充，为这些理论提供一个几何–算子化的可能载体。

## Conclusion

本文在统一时间刻度、因果流形与边界时间几何框架下，对一人称主体"我"给出可公理化的数学定义。核心结论是：

1. "我"可以被形式化为带统一时间刻度的类时世界线上，自指观察者结构的等价类，即我结构 $[\mathsf I]$；

2. 每个我结构等价类在散射–延迟网络中对应一个极小强连通自指闭环，其延迟谱与统一时间刻度对齐；

3. 该闭环携带一个 $\mathbb Z_2$ 拓扑指纹，可通过闭环散射矩阵修正行列式平方根的 holonomy 计算，在适当的情形下与费米统计与 Null–Modular 双覆盖中的拓扑类相容；

4. 多"我"之间的因果与信息交互可在因果网与信息几何框架下刻画，状态与模型共识对应于公共可观测代数上的相对熵收缩。

从形式上看，"我"不再是语义上的模糊指称，而是通过因果、时间、记忆、自指与拓扑五个层面被统一编码的数学对象。未来工作包括：在具体量子场论与宇宙学模型中构造显式我结构的例子；在实验上通过自指散射网络与延迟谱测量验证拓扑指纹；在人工系统中实现显式统一时间刻度与自指更新的代理，并研究其与主观时间感与决策行为的关系。

## Acknowledgements, Code Availability

本工作综合了散射理论、算子代数、量子场论与信息几何的既有成果。感谢相关领域大量文献为本文提供的数学与物理基础。本文未使用专门代码实现数值模拟，相关代码实现留待后续工作展开。

## References

1. M. Sh. Birman, M. G. Kreĭn, "On the Theory of Wave Operators and Scattering Operators", Dokl. Akad. Nauk SSSR, 1962.

2. V. Petkov, M. Zworski, "Semi-classical Estimates on the Scattering Determinant", Ann. Henri Poincaré 2, 2001.

3. C. Guillarmou, "Generalized Krein Formula, Determinants and Selberg Zeta Function in Even Dimension", 预印本.

4. C. Texier, "Wigner Time Delay and Related Concepts", Physica E 82, 2016.

5. P. Ambichl et al., "Focusing Inside Disordered Media with the Generalized Wigner–Smith Operator", Phys. Rev. Lett. 119, 033903 (2017).

6. R. Bourgain et al., "Direct Measurement of the Wigner Time Delay for the Scattering of Light by a Single Obstacle", Opt. Lett. 38, 1963 (2013).

7. U. R. Patel et al., "Wigner–Smith Time Delay Matrix for Electromagnetics", 预印本 arXiv:2005.03211.

8. Connes, A., Rovelli, C., "Von Neumann Algebra Automorphisms and Time–Thermodynamics Relation in General Covariant Quantum Theories", Class. Quantum Grav. 11, 2899–2918 (1994).

9. C. Rovelli, "The 'Thermal Time Hypothesis' and Quantum Gravity", 各类综述与后续文献中讨论.

10. E. Y. S. Chua, "The Time in Thermal Time", Phil. Archive 2024.

11. S. Balakrishnan, T. Faulkner, Z. U. Khandker, H. Wang, "A General Proof of the Quantum Null Energy Condition", JHEP 2019.

12. F. Ceyhan, T. Faulkner, "Recovering the QNEC from the ANEC", Commun. Math. Phys. 377, 999–1045 (2020).

13. S. Hollands, "A New Proof of the QNEC", Commun. Math. Phys. 406, 269–313 (2025).

14. A. Strohmaier et al., "The Relative Trace Formula in Electromagnetic Scattering and the Casimir Effect", Anal. PDE 18, 2025.

15. J. Behrndt, M. M. Malamud, H. Neidhardt, "Trace Formulas for Dissipative and Coupled Scattering Systems", J. Funct. Anal. 2008.

16. H. Isozaki, "Trace Formulas for Schrödinger Operators", RIMS Kokyuroku 1760, 2011.

17. P. Deshmukh et al., "Eisenbud–Wigner–Smith Time Delay in Atom–Laser Interactions", 近期综述.

18. N. C. Menicucci, "Clocks and Relationalism in the Thermal Time Hypothesis", 预印本.

（其余关于因果流形、广义熵、信息几何、多观察者共识等文献从略，可在相关综述中系统查阅。）

---

### Appendix A: Existence and Local Uniqueness of "I"-Worldline

本附录给出定理 1 的证明要点。

#### A.1 Reconstruction of Timelike Curve from Local Records

设局域观察者 $O_\ast$ 记录了沿自身世界线的事件序列与局部因果关系。引入统一时间刻度代表 $\tau$，将所有观测事件嵌入层状结构 $\{\tau^{-1}(t)\}$，在每一层上取在测地距离意义下最接近先前点的"质心"，得到初始曲线 $\tilde\gamma$。利用标准因果结构结果，对 $\tilde\gamma$ 进行光滑化，得到类时测地近似 $\gamma_\ast$，同时保持与观测层的对应关系。

#### A.2 Internal–External Decomposition and Memory Extraction

在 $\mathcal A_\ast$ 上选择分解 $\mathcal A_\ast\simeq\mathcal A^{\mathrm{int}}\otimes\mathcal A^{\mathrm{ext}}$，具体方式取决于物理系统。例如对生物体，可取脑–身体作为内部，其余为外部；对人工系统，可取逻辑状态为内部，输入输出端口为外部。通过分析观测记录中可重复访问且具有长期稳定性的自由度，确定交换子代数 $\mathcal C\subset\mathcal A^{\mathrm{int}}$，视为记忆子系统。

利用相对熵 $D(\omega\Vert\omega')$ 的二阶展开，对 $\mathcal C$ 上的参数化态族计算 Fisher 度量，确认其在长时间区间内保持非退化，从而保证记忆的可区分性与稳定性。

#### A.3 Construction of Self-Referential Update

根据观察者的模型族 $\mathcal M_\ast$ 与更新规则 $U_\ast$，将外部世界的统计模型编码为内部状态的一部分。定义内部环境映射 $E_t:\mathcal A_t^{\mathrm{ext}}\to\mathcal A^{\mathrm{int}}$，把外部观测压缩到内部代数中。更新算子 $U(t_2,t_1)$ 则结合了：

1. 对外部观测 $\mathcal D_{[t_1,t_2]}^{\mathrm{ext}}$ 的处理；

2. 基于内部模型对未来的预测；

3. 对记忆子系统 $\mathcal C$ 的写入规则。

只要更新中出现对未来行为或环境态的显式建模与自适应调整，即可验证自指条件。

#### A.4 Compatibility with Generalized Entropy Dynamics

在 $\gamma_\ast$ 的每个点，选取半径 $r$ 使得小因果菱形 $D_{\gamma_\ast(t),r}$ 的几何近似 Minkowski，边界曲率与外部能量密度满足 QNEC 与相关条件。给定内部态 $\omega_t^{\mathrm{int}}$ 与外部态 $\omega_t^{\mathrm{ext}}$，广义熵 $S_{\mathrm{gen}}$ 的一阶变分给出局域平衡条件，二阶变分的不负性等价于局域能量条件与爱因斯坦方程。这保证引入我结构不会破坏全局几何–熵一致性。

#### A.5 Local Uniqueness up to Equivalence

若存在另一实现 $\mathsf I_\ast'$ 与 $\mathsf I_\ast$ 对同一记录与统一时间刻度等价类兼容，则可以按如下方式构造等价关系：

1. 由两条世界线与时间函数定义严格单调双射 $f$；

2. 利用 GNS 表示与 *-同构分类理论，构造 $\mathcal A^{\mathrm{int}}$ 与 $\mathcal A'^{\mathrm{int}}$ 之间的 *-同构 $\Phi$，在记忆子系统上为谱空间测度同构；

3. 把观测数据与内部更新的相容性转化为 $U$ 与 $U'$ 的半群共轭条件，从而满足定义 7。

由此得到局部唯一性。

---

### Appendix B: Correspondence Between I–Structures and Self-Referential Scattering Loops

本附录补充定理 2 与定理 3 的关键技术要点。

#### B.1 From Internal Dynamics to Closed-Loop Scattering

对给定我结构 $\mathsf I$，在统一时间刻度下构造线性化输入–输出模型：把内部自由度视为节点，把外部通道视为波导。在频域，用适当的自由度选择与 Laplace/Fourier 变换，将时间域更新 $U(t_2,t_1)$ 与环境映射 $E_t$ 转化为散射矩阵族 $S^{\mathrm{net}}(\omega;\lambda)$。

自指更新对应于从输出回流到输入的反馈环路。用 Redheffer 星乘将反馈结构压缩到闭环散射矩阵 $S^{\circlearrowleft}(\omega;\lambda)$，并验证其满足相对迹类条件。

#### B.2 Modified Determinants and Spectral Shift

在 $S^{\circlearrowleft}(\omega;\lambda)$ 上构造关联算符对 $(H_0,H)$，利用 Birman–Kreĭn 与相关结果定义修正行列式 $\det_p S^{\circlearrowleft}$ 与谱移函数 $\xi_p$。相位指数映射

$$
\mathfrak s(\omega,\lambda)=\det_p S^{\circlearrowleft}(\omega;\lambda)
=\exp\bigl(-2\pi\mathrm i\,\xi_p(\omega,\lambda)\bigr)
$$

把参数空间映射到单位圆。

#### B.3 Z(_2) Holonomy and Minimal Strongly Connected Components

在参数空间删除 $\mathfrak s=0$ 的奇点集，得到 $X^\circ$。考虑平方根行列式定义的双覆盖，沿闭路 $\gamma \subset X^\circ$ 定义

$$
\nu_{\sqrt{S^{\circlearrowleft}}}(\gamma)
=\exp\Bigl(\mathrm i\oint_\gamma \tfrac{1}{2\mathrm i}\mathfrak s^{-1}\mathrm d\mathfrak s\Bigr),
$$

给出 $\mathbb Z_2$ 指标。强连通分量分解与谱流加法性表明该指标在极小强连通分量上不可进一步分解，因此可用 $\nu(\mathcal S)$ 为每个我闭环标记拓扑类型。

#### B.4 Alignment with Null–Modular Double Cover and BF Theory

在 Null–Modular 双覆盖与 $\mathbb Z_2$–BF 理论中，局域几何与模流的扇区结构用某个 $H^2(Y,\partial Y;\mathbb Z_2)$ 上同调类 $[K]$ 表示。对满足局域能量与熵一致性的物理系统，全局要求 $[K]=0$，即整体拓扑上没有异常扇区。

我闭环的 $\mathbb Z_2$ 指标局限在内部散射子系统中，对整体几何的上同调类不起破坏作用。这种局域–全局的分配使得"自指的费米性指纹"可以存在于主体内部，而不会在宇宙尺度上引入新的拓扑扇区，从而实现"主体性拓扑"的局域化。

---

通过上述附录的构造与证明纲要，可以看出我结构与自指散射闭环之间的一一对应，以及 $\mathbb Z_2$ 拓扑指纹的稳定性，从而支撑了正文中关于"我"的统一数学定义。

