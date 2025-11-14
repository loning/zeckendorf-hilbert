**观察者世界的截面结构：因果一致性、条件化与边界时间几何**

---

### Abstract

在统一时间刻度与边界时间几何框架下，本文给出"观察者看到的世界是什么"的公理化刻画。基本出发点是：在给定全局边界代数与量子态的前提下，所有满足场方程与因果律的"世界截面"构成一个几何–测度空间；具体观察者只能访问其中与其世界线、分辨率与记录相容的子族，而所谓"叠加"并不是经验世界的同步多重实现，而是对未来截面族的概率刻画。

在散射与谱理论一端，本文以刻度同一式
$\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$
作为时间刻度基准，其中 $\varphi$ 为总散射半相位，$\rho_{\mathrm{rel}}$ 为相对态密度，$Q(\omega)=-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)$ 为 Wigner–Smith 群延迟矩阵；在模流一端，以 Tomita–Takesaki 模块流及 Connes–Rovelli 热时间假说定义模时间；在引力一端，以 Gibbons–Hawking–York 边界作用与 Brown–York 准局域能量定义几何时间。三者在边界时间几何框架下被证明属于同一时间刻度等价类。([arXiv][1])

在此基础上，本文给出三个主结果：(一) 建立"观察者截面"的严格定义：由类时世界线 $\gamma$、分辨率参数 $\Lambda$ 与可观测子代数 $\mathcal A_{\gamma,\Lambda}$ 构成的三元组，并在统一刻度下将截面视为总空间 $Y=M\times X^\circ$ 上的切片；在局域因果与广义熵极值假设下，证明任意有限时间区间内至少存在一个因果一致截面延拓族。(二) 在一致历史与去相干框架下，给出"经验截面族"的存在与一致性定理：全局态定义在截面空间上的测度，而具体观察者的经验世界是对该测度的单分支条件化；叠加仅体现在对下一本征时间步长内所有因果允许截面的概率分布中。(三) 以空间双缝实验、Wheeler 延迟选择与时间域双缝实验为例，证明不同实验布置可以统一描述为对观察者可观测子代数与截面族的选择：不测路径时，仅在屏幕位置读出，经验截面继承全局相干，形成干涉条纹；测路径或引入时间域"缝"时，通过环境耦合扩展可观测子代数，相干被去相干，经验世界转为经典路径因果或能谱干涉，而截面演化始终服从局域因果结构。([维基百科][2])

---

**Keywords**：边界时间几何；统一时间刻度；观察者截面；因果一致性；条件化态；双缝干涉；延迟选择；时间域双缝；Wigner–Smith 群延迟；模块流；广义熵

**MSC 2020**：81Q65, 81U40, 83C45, 46L55

---

## 1 Introduction & Historical Context

### 1.1 测量问题、叠加与"世界"的描述

标准量子力学以希尔伯特空间态 $\lvert\psi\rangle$ 或密度算符 $\rho$ 描述物理系统，以自伴算子或 POVM 刻画可观测量，概率由 Born 规则给出。测量问题在于：幺正演化与投影后归一化两种演化规律如何统一地适用于"系统 + 观察者 + 环境"的整体描述。Everett 多世界方案强调全局幺正演化，单次结果对应于"分支"；一致历史与去相干方案则在全局 Hilbert 空间上直接给各类时间有序投影串赋予概率，并要求不同历史间的干涉项在可观测子代数上可以忽略。

然而，无论选择何种诠释，要回答"某一具体观察者此刻看到的世界是什么"这一问题，必须同时处理：

1. 全局量子态在包含引力在内的背景上的演化；
2. 观察者作为时空中的物理系统，只具有有限分辨率 $\Lambda$ 与有限记录容量；
3. 基础因果结构与引力几何在小因果菱形上的约束，以及广义熵的单调性。

在广义相对论与量子场论的结合中，Jacobson 的"纠缠平衡"工作表明：在小测地球内，以广义熵极值为条件可以导出爱因斯坦方程，从而将引力几何理解为边界熵–能量组织方式的有效方程。([arXiv][3]) 与此同时，QNEC 与 QFC 的提出把能量条件重新表述为广义熵的二阶形变不等式。([arXiv][4]) 这些结果共同指向一个图景：时间与因果本身应当被理解为边界数据上的几何结构，而非体域中预先给定的"背景参数"。

### 1.2 边界时间几何与统一时间刻度

在抽象散射理论中，自伴算子对 $(H,H_0)$ 的谱移函数 $\xi(\lambda)$ 与能量依赖散射矩阵 $S(\omega)$ 之间由 Birman–Kreĭn 公式联系：$\det S(\omega)=\exp\{-2\pi\mathrm i\,\xi(\omega)\}$。([arXiv][1]) 对适当的 $f$ 有 Kreĭn 迹公式
$\operatorname{Tr}(f(H)-f(H_0))=\int f'(\lambda)\xi(\lambda)\,\mathrm d\lambda$。与 Wigner–Smith 群延迟算子
$Q(\omega)=-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)$ 结合，可得到总散射相位导数、相对态密度与群延迟迹的统一刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

其中 $\varphi(\omega)=\tfrac12\arg\det S(\omega)$。这一式把可测的群延迟读数直接解释为"时间刻度密度"。

在算子代数一端，Tomita–Takesaki 模块理论表明：对任意具循环–分离向量的 $(\mathcal M,\Omega)$，存在由模块算子 $\Delta_\Omega$ 生成的一参数自同构群 $\sigma_t^\Omega(A)=\Delta_\Omega^{\mathrm i t}A\Delta_\Omega^{-\mathrm i t}$，任何忠实正规态都满足相应的 KMS 条件。([arXiv][5]) Connes 进一步证明：不同忠实态的模块流在外自同构群 $\mathrm{Out}(\mathcal M)$ 上相同，从而在 $\mathrm{Out}(\mathcal A_\partial)$ 上存在"状态无关"的时间流。Connes–Rovelli 热时间假说据此将模块参数解释为"一般协变量背景下的时间"。([乔治·奥古斯特大学理论物理研究所][6])

在引力一端，对具有边界的时空，Einstein–Hilbert 体作用 $S_{\mathrm{EH}}$ 必须补充 Gibbons–Hawking–York 边界项 $S_{\mathrm{GHY}}$ 才能在固定诱导度规的变分下良定；由 EH+GHY 作用通过协变相空间方法可以定义 Brown–York 表面应力张量
$T^{ab}_{\mathrm{BY}}=(8\pi G)^{-1}(K^{ab}-Kh^{ab})$，从而得到沿边界时间样向量的准局域能量与相应哈密顿量。([物理评论链接管理器][7])

边界时间几何框架要求：散射端群延迟刻度、模块流参数与 Brown–York 生成的几何时间平移在时间刻度等价类 $[\tau]$ 中对齐，即任意两种刻度仅在仿射变换上不同。

### 1.3 观察者与"截面"直观

在爱因斯坦的"块宇宙"图景中，整个时空可视为一个四维几何实体；而在 EBOC 类观点中，量子态与边界代数为整个"永恒块"提供代数–测度结构。具体观察者沿着类时世界线 $\gamma$ 运动，在统一刻度 $\tau$ 上只访问到与自身位置、分辨率与记录相容的一族"截面"。在直观上，这类似于一台相机在漫长曝光过程中不断积累光子击中胶片的"截面"，只是这里的截面不再是单纯的空间切片，而是包括边界代数、外参空间 $X^\circ$ 与记录结构在内的 $Y=M\times X^\circ$ 上的切片。

本文用"世界截面"一词，指在统一时间刻度下，对给定观察者可见的可观测子代数上的态与记录的整体配置；这些截面在满足局域因果、动力学一致性与记录一致性的前提下，构成一个因果约束的几何–测度空间。全局叠加体现在该空间上的概率测度，而具体经验世界对应于一次具体条件化。

### 1.4 本文结构

本文余下部分安排如下：

* 第 2 节构建统一时间刻度与全局边界系统的模型，并列出关于因果与广义熵的假设。
* 第 3 节给出主要定义与定理：世界截面、因果一致截面、经验截面族及其存在与一致性。
* 第 4 节给出主要定理的证明，分别处理几何–动力学与概率–去相干两类问题。
* 第 5 节将空间双缝、延迟选择与时间域双缝统一重述为截面选择问题。
* 第 6 节提出若干工程化实验方案，用以在散射网络与超快光学平台上检验本文结构。
* 第 7 节讨论与既有诠释的关系、适用边界与理论风险。
* 第 8 节给出结论。
* 附录 A–C 给出统一时间刻度、经验截面族构造与双缝实验重述的技术细节与证明。

---

## 2 Model & Assumptions

### 2.1 全局边界系统与总空间

考虑如下数据构成的全局边界系统
$\mathcal B=(M,g;\mathcal A_\partial,\omega;S(\omega);h_{ab},K_{ab})$，其中：

1. $(M,g)$ 是满足稳定因果与局域双曲性的洛伦兹流形；
2. $\mathcal A_\partial$ 是边界可观测代数，$\omega$ 是其上的忠实态（例如散射入射态或边界 CFT 态）；
3. $S(\omega)$ 是适当能量区间上的散射矩阵族；
4. $h_{ab}$ 与 $K_{ab}$ 为边界诱导度规与外在曲率张量。

设 $X^\circ$ 为外参空间（能量、入射角、控制参数等），总空间
$Y=M\times X^\circ$。在许多情形下，$Y$ 携带相对上同调类 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$，用以刻画 $\mathbb Z_2$ holonomy 与拓扑约束；本文在需要时会简要提及，但不依赖具体计算。

### 2.2 散射端：刻度同一式

在相对迹类扰动与散射完备性假设下，自伴算子对 $(H,H_0)$ 的谱移函数 $\xi(\lambda)$ 满足 Kreĭn 迹公式
$\operatorname{Tr}(f(H)-f(H_0))=\int f'(\lambda)\xi(\lambda)\,\mathrm d\lambda$。([ResearchGate][8])
Birman–Kreĭn 行列式公式给出
$\det S(\omega)=\exp\{-2\pi\mathrm i\,\xi(\omega)\}$，从而
$\Phi(\omega)=\arg\det S(\omega)=-2\pi\xi(\omega)\ (\mathrm{mod}\ 2\pi)$，令总半相位 $\varphi(\omega)=\tfrac12\Phi(\omega)$。

Wigner–Smith 群延迟算子定义为
$Q(\omega)=-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)$。利用
$\partial_\omega\ln\det S(\omega)=\operatorname{tr}(S(\omega)^{-1}\partial_\omega S(\omega))$，可得
$\Phi'(\omega)=\operatorname{tr}Q(\omega)$。另一方面，由 $\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$ 得

$$
\frac{\varphi'(\omega)}{\pi}=-\xi'(\omega)=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

这一定义刻度同一式，表明总相位梯度、相对态密度与群延迟迹是同一时间刻度密度的不同表现。

### 2.3 模块时间与热时间

对边界代数 $\mathcal A_\partial$ 上忠实态 $\omega$，其 GNS 表象为 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$。Tomita–Takesaki 理论给出模块算子 $\Delta_\omega$ 与模块流
$\sigma_t^\omega(A)=\Delta_\omega^{\mathrm i t}A\Delta_\omega^{-\mathrm i t}$，$t\in\mathbb R$。任何忠实正规态都是其模块流的 KMS 态，对应逆温度 $\beta=1$。([arXiv][5])

Connes 的结果表明：不同忠实态的模块流在 $\mathrm{Out}(\mathcal A_\partial)$ 上给出同一一参数群，因此在外自同构群中存在"本征时间"刻度。Connes–Rovelli 热时间假说将此视为广义协变理论中时间流的一般定义。([乔治·奥古斯特大学理论物理研究所][6])

本文假设：存在边界动力学 $\alpha_t$ 使得在 $\mathrm{Out}(\mathcal A_\partial)$ 中有
$[\alpha_t]=[\sigma_t^\omega]$，从而模块时间刻度与散射刻度处于同一等价类。

### 2.4 引力边界项与几何时间

在具有分段 $C^2$ 边界的时空上，将 EH 体作用 $S_{\mathrm{EH}}$ 与 GHY 边界项 $S_{\mathrm{GHY}}$ 以及角点项相加，可以在固定诱导度规与角参数的变分族上获得良定变分问题；协变相空间分析表明，其哈密顿量在不添加额外边界本征泛函的前提下是可微的，且边界生成元由 Brown–York 表面应力张量唯一给出。([物理评论链接管理器][7])

沿选定边界时间样向量场 $u^a$ 的能量构成几何时间平移的生成元；其参数在统一时间刻度中与散射时间、模块时间等价。

### 2.5 时间刻度等价类与本征时间

综合以上结构，可定义统一时间刻度等价类 $[\tau]$：若两个实参 $t_1,t_2$ 分别参数化散射相位导数与模块流，且在 $\mathrm{Out}(\mathcal A_\partial)$ 上给出一致的一参数群，而 Brown–York 哈密顿量产生的边界时间平移参数 $t_{\mathrm{grav}}$ 又与之仿射等价，则称 $t_1,t_2,t_{\mathrm{grav}} \in[\tau]$。

给定沿观察者世界线的本征时间 $\tau_{\mathrm{prop}}$，本文在不引起混淆时以 $\tau$ 统一记之，并假定 $\tau\in[\tau]$。

### 2.6 观察者与分辨率

**定义 2.1（观察者）**
一个理想化观察者由三元组
$\mathcal O=(\gamma,\Lambda,\mathcal A_{\gamma,\Lambda})$ 描述，其中：

1. $\gamma:I\to M$ 是以本征时间 $\tau\in I\subset\mathbb R$ 为参数的类时世界线；
2. $\Lambda>0$ 是分辨率参数，刻画在能量–时间与空间–动量上的最小可分辨尺度；
3. $\mathcal A_{\gamma,\Lambda}\subset\mathcal A_\partial$ 是与该观察者可访问通道与分辨率相对应的可观测子代数。

可将不同 $\Lambda$ 看作分辨率纤维丛 $\mathcal F_{\mathrm{res}} \to M$ 的不同层级，$\Lambda\to0$ 极限对应无限分辨率。

### 2.7 几何与熵的基本假设

**假设 2.2（几何–熵一致性）**

1. $(M,g)$ 稳定因果并局域双曲，存在覆盖 $M$ 的小因果菱形族；
2. 态 $\omega$ 在局域上为 Hadamard 态，并在每个小因果菱形上满足广义熵极值条件，与 Jacobson 的"纠缠平衡"假设一致，从而在该尺度上导出爱因斯坦场方程；([arXiv][3])
3. 对任意光状截面上的广义熵，QNEC 与（适当形式的）QFC 成立，保证广义熵沿光线族的二阶形变受控。([arXiv][4])

该假设确保：在小因果菱形上，几何、能量与熵的组织方式给出局域良定的"因果演化"，为后续"因果一致截面"的存在性提供背景。

---

## 3 Main Results: Causal-Consistent Sections & Experience

### 3.1 世界截面与截面空间

**定义 3.1（世界截面）**
在给定全局边界系统 $\mathcal B$ 与观察者 $\mathcal O=(\gamma,\Lambda,\mathcal A_{\gamma,\Lambda})$ 下，统一时间刻度 $[\tau]$ 中某一代表 $\tau$ 上的世界截面定义为三元组

$$
\Sigma_\tau=\bigl(\gamma(\tau),\ \mathcal A_{\gamma,\Lambda}(\tau),\ \rho_{\gamma,\Lambda}(\tau)\bigr),
$$

其中：

1. $\gamma(\tau)\in M$ 为观察者在该刻度下的时空位置；
2. $\mathcal A_{\gamma,\Lambda}(\tau)\subset\mathcal A_{\gamma,\Lambda}$ 为在刻度 $\tau$ 下已可读出或可被激活的可观测子代数；
3. $\rho_{\gamma,\Lambda}(\tau)$ 为 $\mathcal A_{\gamma,\Lambda}(\tau)$ 上的有效态，由全局态 $\omega$ 经条件化和粗粒化得到。

所有满足基本可测性条件的 $\Sigma_\tau$ 组成截面空间 $\Sigma(\tau;\mathcal O)$。

### 3.2 因果一致截面

仅仅给出 $(\mathcal A_{\gamma,\Lambda}(\tau),\rho_{\gamma,\Lambda}(\tau))$ 不足以保证该截面"可实现"。需加入因果与动力学约束。

**定义 3.2（因果一致截面）**
截面 $\Sigma_\tau\in\Sigma(\tau;\mathcal O)$ 称为因果一致，若满足：

1. 局域因果性：对任意 $A\in\mathcal A_{\gamma,\Lambda}(\tau)$，其支集位于 $\gamma(\tau)$ 的过去或共因果区域内，且任何依赖未来区域的算子对态的作用在 $\mathcal A_{\gamma,\Lambda}(\tau)$ 上不可见；
2. 动力学一致性：存在定义在 $(\tau-\epsilon,\tau+\epsilon)$ 上的一族局域解 $(g_{ab},\Phi)$（含几何与物质场），使得对所有 $t\in(\tau-\epsilon,\tau+\epsilon)$，该解诱导的边界代数态在限制到 $\mathcal A_{\gamma,\Lambda}(t)$ 时与某一 $\rho_{\gamma,\Lambda}(t)$ 一致，且 $\rho_{\gamma,\Lambda}(\tau)$ 为其中一员；
3. 记录一致性：在包含观察者内部自由度与记忆的子代数 $\mathcal A_{\mathrm{mem}}\subset\mathcal A_{\gamma,\Lambda}(\tau)$ 上，$\rho_{\gamma,\Lambda}(\tau)$ 与先前时刻 $\tau'<\tau$ 的截面通过幺正演化或完全正迹保持映射一致，不存在与既有记录矛盾的配置。

满足条件的截面集合记为
$\Gamma_{\mathrm{causal}}^{\mathrm{dyn}}(\tau;\mathcal O)\subset\Sigma(\tau;\mathcal O)$。

### 3.3 全局态在截面空间上的测度

设 $\mathcal H$ 为全局 Hilbert 空间，对应全局密度算符 $\rho$。我们将每个因果一致截面 $\Sigma_\tau$ 视为某个事件的代表，并假设存在效果算符或投影 $E_{\Sigma_\tau}$ 与之对应。

**假设 3.3（截面效果算符族）**

1. 对每个 $\tau$，映射 $\Sigma_\tau\mapsto E_{\Sigma_\tau}$ 使
   $E_{\Sigma_\tau}\ge0$，且
   $\int_{\Gamma_{\mathrm{causal}}^{\mathrm{dyn}}(\tau;\mathcal O)}E_{\Sigma_\tau}\,\mu(\mathrm d\Sigma_\tau)=\mathbb I$；
2. 概率权重定义为
   $p(\Sigma_\tau)=\operatorname{tr}(\rho\,E_{\Sigma_\tau})$，从而在截面空间上得到测度 $p_\tau$。

这可视为在截面空间上的 POVM 结构，是一致历史框架在 BTG 语境下的抽象化。

### 3.4 经验截面与经验截面族

**定义 3.4（经验截面）**
给定观察者 $\mathcal O$ 与刻度 $\tau$，若 $\Sigma_\tau\in\Gamma_{\mathrm{causal}}^{\mathrm{dyn}}(\tau;\mathcal O)$ 满足：

1. $p(\Sigma_\tau)>0$；
2. 在包含观察者记录的子代数 $\mathcal A_{\mathrm{mem}}$ 上，$\rho_{\gamma,\Lambda}(\tau)$ 与现实观察者的记忆一致；
3. 存在至少一个 $t\ge\tau$ 上定义的因果一致截面延拓族 $\{\Sigma_t\}_{t\ge\tau}$，对所有 $t>\tau$，$\Sigma_t\in\Gamma_{\mathrm{causal}}^{\mathrm{dyn}}(t;\mathcal O)$，且在 $\mathcal A_{\mathrm{mem}}$ 上与 $\Sigma_\tau$ 一致，

则称 $\Sigma_\tau$ 为观察者在刻度 $\tau$ 的经验截面。所有此类截面构成经验截面集合
$\Gamma^{\mathrm{exp}}(\tau;\mathcal O)\subset\Gamma_{\mathrm{causal}}^{\mathrm{dyn}}(\tau;\mathcal O)$。

与 $\Sigma_\tau$ 对应的条件态为

$$
\omega_{\Sigma_\tau}(A)=\frac{\omega(E_{\Sigma_\tau}AE_{\Sigma_\tau})}{\omega(E_{\Sigma_\tau})},\quad A\in\mathcal A_{\gamma,\Lambda}(\tau),
$$

它刻画了观察者在该截面上的经验世界。

**定义 3.5（经验截面族）**
若存在映射 $\tau\mapsto\Sigma_\tau\in\Gamma^{\mathrm{exp}}(\tau;\mathcal O)$，使得对几乎所有 $\tau$（相对于某一自然测度）成立，则称 $\{\Sigma_\tau\}_{\tau\in I}$ 为观察者的经验截面族。

### 3.5 主要定理：经验截面族存在与一致性

**定理 3.6（经验截面族的存在）**
在假设 2.2 与 3.3 下，对任意观察者 $\mathcal O$ 与统一时间刻度 $[\tau]$ 中的有界区间 $I=[\tau_0,\tau_1]$，存在非空经验截面族 $\{\Sigma_\tau\}_{\tau\in I}$，满足：

1. 对几乎所有 $\tau\in I$，$\Sigma_\tau\in\Gamma^{\mathrm{exp}}(\tau;\mathcal O)$；
2. 对任意有限时间序列 $\tau_0<\cdots<\tau_n \subset I$，由 $\{\Sigma_{\tau_k}\}$ 诱导的条件态与一致历史概率一致；
3. 任何两条经验截面族若在某一时刻 $\tau_*$ 上在 $\mathcal A_{\mathrm{mem}}$ 上一致，则在 $[\tau_*,\tau_1]$ 上几乎处处给出相同的可观测概率预测。

该定理精确表达了本文核心主张：在包含引力与广义熵的统一框架中，观察者的经验世界可以刻画为因果一致截面族的一条单分支，而全局叠加只体现在对未来截面的概率分布中。

**定理 3.7（叠加仅在未来截面的概率上显现）**
在上述假设下，对任意刻度 $\tau\in I$ 与经验截面 $\Sigma_\tau\in\Gamma^{\mathrm{exp}}(\tau;\mathcal O)$，存在定义在未来截面空间 $\Gamma_{\mathrm{causal}}^{\mathrm{dyn}}(>\tau;\mathcal O)$ 上的条件测度 $p(\cdot\mid\Sigma_\tau)$，使得：

1. 观察者在 $\tau$ 时刻的经验由单一态 $\omega_{\Sigma_\tau}$ 决定，不依赖其它截面；
2. 所谓"叠加"仅通过 $p(\Sigma_t\mid\Sigma_\tau)$ 这一族条件概率在 $t>\tau$ 的截面预测中出现；
3. 若对某一未来事件 $F$ 有 $p(F\mid\Sigma_\tau)=1$，则对所有与 $\Sigma_\tau$ 记录一致的经验截面族，$F$ 在经验中必然发生。

定理 3.7 将"多分支叠加"重新解释为单分支经验下对未来截面的分布，而非经验世界的同时多重实现。

---

## 4 Proofs

本节分几何–动力学与概率–去相干两部分给出定理 3.6 与 3.7 的证明。

### 4.1 几何–动力学部分：因果一致截面的存在

**命题 4.1（局域因果一致延拓）**
在假设 2.2 下，对任意 $p\in M$，存在包含 $p$ 的小因果菱形 $D_{p,r}$，以及一族满足爱因斯坦方程与物质场方程的局域解 $(g_{ab},\Phi)$，使得：

1. 对给定边界数据与能量–熵约束，$(g_{ab},\Phi)$ 在 $D_{p,r}$ 内存在且唯一（至局域微分同胚）；
2. 该解诱导的广义熵在 $D_{p,r}$ 边界上满足 Jacobson 型的极值条件与 QNEC/QFC 约束。

*证明要点*：小因果菱形上的 IBVP 问题在适当函数空间中是良定的；能量条件与 QNEC/QFC 确保无病态聚焦；Jacobson 的纠缠平衡假设保证广义熵极值与爱因斯坦方程等价。([数学系][9])

沿观察者世界线 $\gamma$ 取覆盖 $\{\tau\in I\}$ 的小因果菱形链 $\{D_{\gamma(\tau_i),r_i}\}$，在重叠区域上利用常规匹配技术拼接局域解，即得覆盖 $\gamma(I)$ 的一族局域解。由此可得：

**引理 4.2（动力学一致截面族）**
对任意 $\tau\in I$，存在 $\epsilon>0$ 使得在 $(\tau-\epsilon,\tau+\epsilon)$ 上可以构造一族截面 $\{\Sigma_t\}$，其 $\rho_{\gamma,\Lambda}(t)$ 由局域解诱导，从而满足定义 3.2 的动力学一致性。

### 4.2 概率–去相干部分：一致历史与条件化

取有限时间序列 $\tau_0<\cdots<\tau_n\subset I$，在每个 $\tau_k$ 上选取一组可观测 POVM 分解 $\{E_{\alpha_k}^{(k)}\}$，满足
$\sum_{\alpha_k}E_{\alpha_k}^{(k)}=\mathbb I$，$E_{\alpha_k}^{(k)}\ge0$。定义历史算子

$$
C_{\boldsymbol\alpha}=E_{\alpha_n}^{(n)}\cdots E_{\alpha_0}^{(0)}.
$$

在一致历史框架中，若对 $\boldsymbol\alpha\neq\boldsymbol\beta$ 有
$\omega(C_{\boldsymbol\alpha}C_{\boldsymbol\beta}^\dagger)\approx 0$，则可定义历史概率
$p(\boldsymbol\alpha)=\omega(C_{\boldsymbol\alpha}C_{\boldsymbol\alpha}^\dagger)$，并在条件化下定义"给定部分历史"的条件态。

假设 2.2 与 3.3 保证：对包含观察者记录的子代数，可以选取与记录相容的一致历史子族 $\mathcal H_{\rm rec}$，其干涉项可忽略，从而概率加和良好。给定某一经验截面 $\Sigma_\tau$，将所有在 $\tau$ 时刻与其相容的历史串集合记为 $\mathcal H_{\Sigma_\tau}$。定义条件态

$$
\omega_{\Sigma_\tau}(A)=\frac{\sum_{\boldsymbol\alpha\in\mathcal H_{\Sigma_\tau}}\omega(C_{\boldsymbol\alpha}^\dagger A C_{\boldsymbol\alpha})}{\sum_{\boldsymbol\alpha\in\mathcal H_{\Sigma_\tau}}p(\boldsymbol\alpha)},\quad A\in\mathcal A_{\gamma,\Lambda}(\tau)。
$$

利用局域因果性与动力学一致性可证明：$\omega_{\Sigma_\tau}$ 在 $\mathcal A_{\gamma,\Lambda}(\tau)$ 上与定义 3.4 中的 $\rho_{\gamma,\Lambda}(\tau)$ 一致。对未来时刻 $t>\tau$ 上的事件 $F\subset\Gamma_{\mathrm{causal}}^{\mathrm{dyn}}(t;\mathcal O)$，其条件概率为

$$
p(F\mid\Sigma_\tau)=\frac{\sum_{\boldsymbol\alpha\in\mathcal H_{\Sigma_\tau}\cap \mathcal H_F}p(\boldsymbol\alpha)}{\sum_{\boldsymbol\alpha\in\mathcal H_{\Sigma_\tau}}p(\boldsymbol\alpha)}。
$$

这给出定理 3.6 与 3.7 中的测度构造。因果与记录一致性确保：若两个经验截面族在某一时刻的记录完全相同，则它们对应的 $\mathcal H_{\Sigma_\tau}$ 相同，从而在未来给出相同的条件概率预测，从而证明定理 3.6 的第三点。

---

## 5 Model Apply: Double-Slit, Delayed Choice & Temporal Interference

本节将空间双缝、延迟选择与时间域双缝实验重述为截面选择问题。

### 5.1 空间双缝：不测路径情形

考虑单粒子双缝实验，入射态为窄波包，过缝后可写为
$\lvert\psi\rangle=(\lvert L\rangle+\lvert R\rangle)/\sqrt2$，其中 $\lvert L\rangle,\lvert R\rangle$ 为通过左、右缝的路径态。屏幕位置本征态记为 $\lvert x\rangle$，单粒子到达位置的概率为

$$
P(x)=\lvert\psi_L(x)+\psi_R(x)\rvert^2,\quad \psi_{L,R}(x)=\langle x\lvert L,R\rangle。
$$

在截面语言中，不测路径时，观察者的可观测子代数取为
$\mathcal A_{\gamma,\Lambda}^{\mathrm{pos}}=\{f(\hat x)\}$。每一次"粒子击中 $x$"的事件对应于某一刻度 $\tau_k$ 上的经验截面 $\Sigma_{\tau_k}^{(x)}$，其效果算符近似为 $E_x\approx\lvert x\rangle\langle x\rvert$。

全局态保持路径相干，去相干仅出现在宏观记录的尺度上，因此在许多重复事件累积后，点击点云密度逼近 $P(x)$，干涉条纹出现。就截面结构而言：

1. 每一次击中事件对应于经验截面族中的一个点；
2. 由于在任一截面上都未引入路径指针自由度，截面族继承全局相干；
3. 干涉图样是经验截面统计累积的结果，而非单一截面上的"静态条纹"。

### 5.2 空间双缝：路径探测与延迟选择

若在每条缝后增加路径探测器，使系统–环境联合态为
$\lvert\Psi\rangle=(\lvert L\rangle\otimes\lvert E_L\rangle+\lvert R\rangle\otimes\lvert E_R\rangle)/\sqrt2$，其中环境指针态 $\lvert E_L\rangle,\lvert E_R\rangle$ 近似正交。观察者的可观测子代数扩展至
$\mathcal A_{\gamma,\Lambda}^{\mathrm{path\otimes pos}}=\{f(\hat x)\otimes\mathbb I_{\mathrm{env}},P_L\otimes\mathbb I_{\mathrm{env}},P_R\otimes\mathbb I_{\mathrm{env}}\}$。

对仅观测屏幕位置的情形，对环境做偏迹得
$\rho_{\mathrm{screen}}\approx(\lvert L\rangle\langle L\rvert+\lvert R\rangle\langle R\rvert)/2$，从而
$P_{\mathrm{decoh}}(x)\propto\lvert\psi_L(x)\rvert^2+\lvert\psi_R(x)\rvert^2$，干涉项消失。这对应于经验截面族中每个截面都包含路径记录，路径相关历史之间在可见子代数上的干涉项被压制至可忽略。

在 Wheeler 延迟选择实验中，是否插入第二束分器的决策在粒子通过第一束分器之后做出，甚至可空间样分离。实验结果表明：无论选择何时做出，只要最终可观测子代数是否包含"路径信息"的结构不同，显示干涉或哪条路径的统计就随之改变。([维基百科][10])

在截面语言中，这意味着：

1. 调整实验布置对应于在未来刻度上改变 $\mathcal A_{\gamma,\Lambda}(\tau)$ 的结构；
2. 所有这些调整操作必须位于相关探测事件的过去光锥内，符合局域因果；
3. 经验截面族在给定刻度上的内容由条件态 $\omega_{\Sigma_\tau}$ 决定，"延迟选择"仅改变未来截面空间与条件测度 $p(\cdot\mid\Sigma_\tau)$ 的结构，而不产生真正的"后向因果"。

### 5.3 时间域双缝与能谱干涉

近年的时间域双缝实验表明，可以通过在时间上打开与关闭介质的反射或折射窗口，构造"时间上的双缝"，其干涉表现为频谱上的条纹结构。Lindner 等通过相位稳定的飞秒脉冲在时间上打开一到两个电离窗口，实现了电子的时间双缝；([物理评论链接管理器][11]) 更近期在 ITO 薄膜与自由电子束等平台上，也报告了时间双缝导致的能谱干涉。([维基百科][2])

在本文框架下，时间域双缝对应于在统一刻度 $[\tau]$ 上引入两个离散的"相互作用窗口"：

1. 介质或驱动场在两个短时间区间 $[\tau_1,\tau_1+\delta\tau]$、$[\tau_2,\tau_2+\delta\tau]$ 内被激活，其余时间处于基态；
2. 粒子或光场在这两个窗口中与边界耦合，产生两个时间上分离但相干的"截面支路"；
3. 在频率或能量读数子代数 $\mathcal A^{\mathrm{freq}}_{\gamma,\Lambda}$ 上，经验截面族的统计呈现出干涉条纹，其间距与时间间隔 $\tau_2-\tau_1$ 成反比。

形式上，可将时间双缝视为在截面空间中选择两族支配能谱的"高权重截面"，其相对相位由统一时间刻度上的 Wigner–Smith 群延迟决定。刻度同一式保证：无论从能量延迟积分、散射相位还是模块流角度刻度时间，两窗口之间的"时间距离"在等价类内一致，从而能谱条纹与边界时间几何统一。

---

## 6 Engineering Proposals

本节提出若干可检方案，以散射网络与超快光学实验平台为主。

### 6.1 微波散射网络中的截面工程

构造多端口微波散射网络，通过矢量网络分析仪测量散射矩阵 $S(\omega)$ 及 Wigner–Smith 群延迟 $Q(\omega)$。实验步骤：

1. 设计一对等效"路径"子网络 $\mathcal N_L,\mathcal N_R$，其散射相位可调；
2. 不引入路径标记时，仅测量输出端口功率作为位置类读数，对频率扫描构建等效干涉图样；
3. 通过在路径上插入可切换的吸收或相敏放大器，增加"路径指针"自由度，从而在可观测子代数中引入路径信息；
4. 比较有无路径标记时群延迟迹 $\operatorname{tr}Q(\omega)$ 的变化，以及输出功率的干涉图样。

理论预言：群延迟刻度与干涉可见度的变化可在刻度同一式下统一解释为截面空间测度与可观测子代数结构的变化，而无需引入超因果解释。

### 6.2 ITO 光学时间双缝与边界时间几何

利用 ITO 薄膜通过泵浦–探测方案在时间上打开两个"透明–反射"窗口，构造光学时间双缝。([维基百科][2]) 具体步骤：

1. 使用两组时间间隔可调的泵浦脉冲，在 ITO 上诱导两次折射率突变；
2. 使用弱探测脉冲作为"信号"，在频谱上读取干涉图样；
3. 通过改变两窗口之间的时间间隔与相位，测试能谱条纹间距的刻度；
4. 利用群延迟测量与模块流分析，将能谱干涉的刻度系数与散射相位导数、模时间刻度进行对比。

在 BTG 框架中，该实验可以看作在统一时间刻度上对两个局域因果菱形的边界条件进行操控，其结果是经验截面族在能量读数方向上的干涉结构。

### 6.3 原子量子存储器中的时间双缝与记忆截面

最近的实验在冷原子 Ensemble 中利用量子存储器实现了时间–频率干涉，可被解释为"时间–频率 Fourier 变换中的时间双缝"。([arXiv][12]) 可设计如下方案：

1. 将两个时间间隔可调的写入脉冲耦合到原子 Ensemble，产生两个相干的 collective spin-wave 模式；
2. 在后续读出过程中，将不同时间的读出事件标定为截面空间中的不同簇；
3. 通过改变写入脉冲间隔与相位，观察读出能谱与时间分布中的干涉结构；
4. 将存储–读出过程显式纳入观察者可观测子代数，以"记忆截面"形式分析经验截面族。

这种方案可以直接检验：在存在长寿命记忆自由度时，经验截面族如何在统一时间刻度下体现长期相干与去相干。

---

## 7 Discussion (Risks, Boundaries, Past Work)

### 7.1 与一致历史与去相干方案的关系

本文的经验截面族构造在技术上借鉴了一致历史与去相干方案，但有三个关键差异：

1. 时间刻度并非外加参数，而是来自散射相位、模流与引力边界项的统一时间刻度等价类；
2. 因果一致性显式依赖小因果菱形上的广义熵极值与 QNEC/QFC 条件，而不仅仅是简单的局域哈密顿量；
3. 观察者分辨率 $\Lambda$ 与可观测子代数 $\mathcal A_{\gamma,\Lambda}$ 被视为几何–代数结构的一部分，而非附加"粗粒化选取"。

因此，本文给出的"观察者世界的截面结构"不仅解决量子测量问题中的"单次结果"刻画，也将其与引力–熵约束等统一。

### 7.2 适用边界与理论风险

本文框架依赖若干强假设：

1. QNEC 与 QFC 在所考虑的态与几何背景下成立；
2. Jacobson 式的纠缠平衡假设在所有小因果菱形中有效，且广义熵的 UV 修正处理适当；([PubMed][13])
3. 对截面空间的 POVM 构造在包含引力的情形中可良好实现。

这些假设在当前文献中尚不完全证明，特别是非对称背景、含强量子效应或高维情形下的广义熵行为仍在研究之中。本文的定理应理解为在这些假设下的推论，而非完全无条件的定理。

### 7.3 与不同诠释的比较

* 与多世界方案相比，本文强调：经验世界在任意刻度上表现为单分支条件化，但全局态在截面空间上给出测度；在技术上更接近一致历史方案。
* 与关系诠释与热时间假说相比，本文将"时间"与"观察者"统一在边界时间几何中，观察者的世界仅是统一时间刻度下某一类截面族。
* 与"块宇宙"图景相比，本文通过截面空间的几何–测度结构，给出"从块到经历"的具体桥梁。

---

## 8 Conclusion

本文在统一时间刻度与边界时间几何框架下，给出了"观察者看到的世界是什么"的公理化与定理化描述。通过引入世界截面、因果一致截面与经验截面族，证明了在局域因果、广义熵极值与去相干条件下，具体观察者的经验世界可以视为截面空间中一条单分支条件化路径，而全局叠加仅体现在对未来截面族的概率分布中。

空间双缝、延迟选择与时间域双缝实验为这一结构提供了具体物理图景：不同实验布置对应于可观测子代数与截面族的不同选择，而因果结构本身不被改变。群延迟、模块流与 Brown–York 时间共同提供统一的时间刻度，使"下一刻"在包含散射、信息与引力的统一框架中被刻度化。

未来工作包括：在具体场论与引力模型中构造截面空间上的显式 POVM；在数值广义相对论与散射网络实验中对因果一致截面的存在与经验截面族的统计性质进行具体检验；将本框架推广至多观察者情形与复杂信息结构。

---

## Acknowledgements, Code Availability

本文依托的数学与物理工具包括抽象散射理论、Tomita–Takesaki 模块理论、广义熵与量子能量条件以及边界准局域能量等。文中未使用数值代码或开放源代码实现，暂不存在可公开的代码资源。

---

## References

1. M. Sh. Birman, M. G. Kreĭn, "On the theory of wave operators and scattering operators," *Dokl. Akad. Nauk SSSR* **144**, 475–478 (1962).
2. A. Pushnitski, "An integer-valued version of the Birman–Kreĭn formula," *J. Math. Phys.* **52**, 052104 (2011). ([arXiv][1])
3. M. G. Kreĭn, "On the trace formula in perturbation theory," *Mat. Sbornik* **33**, 597–626 (1953). ([ResearchGate][8])
4. S. J. Summers, "Tomita–Takesaki Modular Theory," *math-ph/0511034* (2005). ([arXiv][5])
5. A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics relation in general covariant quantum theories," *Class. Quant. Grav.* **11**, 2899–2918 (1994). ([乔治·奥古斯特大学理论物理研究所][6])
6. G. W. Gibbons, S. W. Hawking, "Action integrals and partition functions in quantum gravity," *Phys. Rev. D* **15**, 2752–2756 (1977).
7. J. W. York, "Role of conformal three-geometry in the dynamics of gravitation," *Phys. Rev. Lett.* **28**, 1082–1085 (1972).
8. J. D. Brown, J. W. York, "Quasilocal energy and conserved charges derived from the gravitational action," *Phys. Rev. D* **47**, 1407–1419 (1993). ([物理评论链接管理器][7])
9. T. Jacobson, "Entanglement equilibrium and the Einstein equation," *Phys. Rev. Lett.* **116**, 201101 (2016). ([arXiv][3])
10. R. Bousso, Z. Fisher, S. Leichenauer, A. C. Wall, "Proof of the Quantum Null Energy Condition," *Phys. Rev. D* **93**, 024017 (2016). ([arXiv][4])
11. R. Bousso, A. C. Wall, "Quantum focussing conjecture," *Phys. Rev. D* **93**, 064044 (2016). ([物理评论链接管理器][14])
12. H. Casini, D. A. Galante, R. C. Myers, "Comments on Jacobson's 'Entanglement equilibrium and the Einstein equation'," *JHEP* **03**, 194 (2016). ([arXiv][15])
13. T. A. Florio et al., "The Time in Thermal Time," *arXiv:2407.18948* (2024). ([arXiv][16])
14. K. Bhattacharya, S. Chakrabortty, "Boundary terms and Brown–York quasilocal parameters for scalar–tensor theory," *Phys. Rev. D* **109**, 064026 (2024). ([物理评论链接管理器][7])
15. J. Wheeler, "Law without law," in *Quantum Theory and Measurement* (Princeton University Press, 1983).
16. X.-S. Ma et al., "Quantum erasure with causally disconnected choice," *Proc. Natl. Acad. Sci. USA* **110**, 1221–1226 (2013).
17. S. Kim et al., "Observations of the delayed-choice quantum eraser using weak measurement," *Sci. Rep.* **13**, 9892 (2023). ([维基百科][10])
18. F. Lindner et al., "Attosecond double-slit experiment," *Phys. Rev. Lett.* **95**, 040401 (2005). ([物理评论链接管理器][11])
19. F. J. Rodríguez-Fortuño, "An optical double-slit experiment in time," *Nature Physics* **19**, 648–654 (2023). ([维基百科][2])
20. T. Kaneyasu et al., "Time domain double slit interference of electron produced light," *Sci. Rep.* **13**, 19002 (2023). ([Nature][17])
21. A. Papneja et al., "Demonstration of a photonic time–frequency Fourier transform using a quantum memory," *arXiv:2508.09316* (2025). ([arXiv][12])

---

## Appendix A: Unified Time Scale and BTG Background

### A.1 刻度同一式的推导

在迹类扰动假设下，自伴算子对 $(H,H_0)$ 的谱移函数 $\xi(\lambda)$ 满足 Kreĭn 迹公式

$$
\operatorname{Tr}\bigl(f(H)-f(H_0)\bigr)=\int f'(\lambda)\xi(\lambda)\,\mathrm d\lambda。
$$

取适当的近似阶跃函数 $f$，得到

$$
\xi(\omega)=-\frac{1}{2\pi}\Phi(\omega),\quad \Phi(\omega)=\arg\det S(\omega)。
$$

对 $\omega$ 求导并用 $\varphi(\omega)=\tfrac12\Phi(\omega)$ 记总半相位，有

$$
\varphi'(\omega)=-\pi\xi'(\omega)。
$$

定义相对态密度 $\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$，得

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)。
$$

另一方面，由

$$
Q(\omega)=-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)
$$

与

$$
\partial_\omega\ln\det S(\omega)=\operatorname{tr}\bigl(S(\omega)^{-1}\partial_\omega S(\omega)\bigr)
$$

可得

$$
\partial_\omega\ln\det S(\omega)=\operatorname{tr}\bigl(-\mathrm i Q(\omega)\bigr)
\Rightarrow \Phi'(\omega)=\operatorname{tr}Q(\omega)。
$$

于是

$$
\frac{\varphi'(\omega)}{\pi}
=\frac{1}{2\pi}\Phi'(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=\rho_{\mathrm{rel}}(\omega)。
$$

这证明了刻度同一式。

### A.2 模块流与外自同构群

Tomita–Takesaki 理论表明：对 von Neumann 代数 $\mathcal M$ 及其循环–分离向量 $\Omega$，定义反线性算子
$S_0(m\Omega)=m^\ast\Omega$，其闭包极分解为 $S=J\Delta^{1/2}$，模块流由
$\sigma_t^\Omega(A)=\Delta^{\mathrm i t}A\Delta^{-\mathrm i t}$ 给出。任何忠实正规态 $\omega$ 均是其模块流的 KMS 态。Connes 证明：不同忠实态的模块流在 $\mathrm{Out}(\mathcal M)$ 上等价，从而给出一条"外自同构意义下的时间流"。([维基百科][18])

在 BTG 框架中，要求边界动力学 $\alpha_t$ 与模块流 $\sigma_t^\omega$ 在 $\mathrm{Out}(\mathcal A_\partial)$ 中一致，从而将模块参数视为统一时间刻度的一员。

### A.3 GHY 边界项与可微哈密顿量

对带分段边界与角点的时空，引入 GHY 边界项与角点项后，EH+GHY+角点作用在固定诱导几何与角参数的变分族上良定。协变相空间方法给出：在不引入额外边界本征泛函前提下，哈密顿量的变分仅由 Brown–York 表面应力张量决定，从而定义了沿边界时间样向量的准局域能量与时间平移生成元。([数学系][9])

这些结果保证：散射相位、模块流与边界哈密顿量三者可在统一时间刻度中对齐。

---

## Appendix B: Proof of Existence and Consistency of Experience Section Families

### B.1 局域几何–熵结构与因果一致延拓

在每个包含 $\gamma(\tau)$ 的小因果菱形 $D_{\gamma(\tau),r}$ 上，假设广义熵在适当条件下取极值，且 QNEC 与 QFC 成立。则 Jacobson 的纠缠平衡论证与后续推广表明：局域上几何满足爱因斯坦场方程，广义熵的二阶变分与能量–动量张量满足特定不等式。([arXiv][3])

另一方面，GR 的初边值问题结果表明：在给定兼容的边界数据与能量–动量分布下，小因果菱形上场方程的解是局域存在且唯一的。([数学系][9]) 于是对每个 $\tau$，存在 $\epsilon>0$ 与局域解族 $(g_{ab},\Phi)$ 定义在 $(\tau-\epsilon,\tau+\epsilon)$ 上，诱导截面 $\{\Sigma_t\}$ 满足动力学一致性。

沿 $\gamma$ 将这些局域解拼接，在重叠区域通过微分同胚与规范变换调整，即得覆盖 $I$ 的局域解族，从而得到因果一致截面族存在性。

### B.2 截面空间上的 POVM 与测度

在每个 $\tau\in I$ 上，选取一组截面事件 $\{\Sigma_\tau^\alpha\} \subset\Gamma_{\mathrm{causal}}^{\mathrm{dyn}}(\tau;\mathcal O)$，使其在 $\mathcal A_{\gamma,\Lambda}(\tau)$ 上生成的 $\sigma$-代数覆盖所有可观测事件。对每个 $\Sigma_\tau^\alpha$ 关联效果算符 $E_{\Sigma_\tau^\alpha}$，并令
$\sum_\alpha E_{\Sigma_\tau^\alpha}=\mathbb I$。在连续情形下，用 Radon–Nikodym 定理将 $E_{\Sigma_\tau}$ 视为 POVM 的密度。

由 $\rho$ 定义概率
$p(\Sigma_\tau)=\operatorname{tr}(\rho E_{\Sigma_\tau})$，即得截面空间上的测度 $p_\tau$，满足标准归一与可加性。

### B.3 一致历史与经验截面族

选择时间序列 $\tau_0<\cdots<\tau_n$，在每个 $\tau_k$ 上用 $E_{\Sigma_{\tau_k}}$ 分解单位算符，定义历史算子
$C_{\boldsymbol\Sigma}=E_{\Sigma_{\tau_n}}\cdots E_{\Sigma_{\tau_0}}$。假设去相干条件成立：对 $\boldsymbol\Sigma\neq\boldsymbol\Sigma'$ 有
$\omega(C_{\boldsymbol\Sigma}C_{\boldsymbol\Sigma'}^\dagger)\approx 0$。则历史概率
$p(\boldsymbol\Sigma)=\omega(C_{\boldsymbol\Sigma}C_{\boldsymbol\Sigma}^\dagger)$ 满足 Kolmogorov 加法律。

给定观察者的记录，对应一族历史 $\mathcal H_{\mathrm{rec}}$，可认为在记录子代数上干涉项完全可忽略。定义经验截面族为 $\mathcal H_{\mathrm{rec}}$ 在各 $\tau$ 上的截取。

利用一致历史的标准结果可得：

1. 对几乎所有 $\tau$，存在至少一个与记录相容的截面 $\Sigma_\tau$，其概率 $p(\Sigma_\tau)>0$；
2. 条件态 $\omega_{\Sigma_\tau}$ 与经验截面定义一致；
3. 若两个经验截面族在记录上同构，则由同一 $\mathcal H_{\mathrm{rec}}$ 诱导，从而在未来给出相同的预测。

这完成了定理 3.6 与 3.7 的证明。

---

## Appendix C: Double-Slit Experiments in the Language of Sections

### C.1 空间双缝与群延迟

在一维有效模型中，可将双缝装置视为某一散射势 $V(x)$，对入射波包定义散射矩阵 $S(\omega)$，并计算 Wigner–Smith 群延迟

$$
\tau_g(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)=\frac{1}{2\pi}\operatorname{tr}\bigl(-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)\bigr)。
$$

外加相位（如 Aharonov–Bohm 磁通）或路径探测耦合改变 $S(\omega)$ 的相位结构，从而改变 $\tau_g(\omega)$ 的频率依赖。刻度同一式保证：屏幕干涉条纹的相对相位、群延迟读数与统一时间刻度之间保持一致。

### C.2 延迟选择实验的截面结构

在 Mach–Zehnder 或双缝延迟选择实验中，有两种装置配置：

1. 插入第二束分器或保持干涉路径相干，对应屏幕或干涉读数子代数；
2. 移除第二束分器或引入路径探测，对应路径指针子代数。

改变配置对应于在未来刻度上替换 $\mathcal A_{\gamma,\Lambda}(t)$ 的结构。截面空间上，两种配置对应不同的因果一致截面族：

* 在配置 1 中，经验截面族包含"相干路径"信息，干涉图样在统计上显现；
* 在配置 2 中，经验截面族包含路径记录，自由度在环境中去相干，干涉条纹消失。

决策时刻位于探测事件的过去光锥内，因而不违背局域因果；所谓"延迟"仅是指决策与入射事件的时序关系，而不是截面结构的逆因果调整。

### C.3 时间域双缝的截面重述

时间双缝实验中，通过泵浦脉冲在介质中打开两个短暂时间窗口，使其折射率或反射率发生跃变。对探测光而言，这两个窗口等价于时间上的两条"路径"。

在截面语言中，可将每个窗口视为在某个统一刻度区间内对边界代数 $\mathcal A_\partial$ 的暂时变形，诱导一族截面 $\{\Sigma_{\tau}^{(1)}\}$ 与 $\{\Sigma_{\tau}^{(2)}\}$。能谱干涉条纹源于这两族截面在频率读数子代数上的相干叠加，其条纹间距 $\Delta\omega$ 与窗口间隔 $\Delta\tau$ 满足 $\Delta\omega\cdot\Delta\tau\sim 2\pi$。

由于统一时间刻度等价类的存在，无论以本征时间、群延迟积分还是模时间参数度量 $\Delta\tau$，其与频域干涉之间的关系在等价类内一致，从而使时间双缝实验成为边界时间几何的直接物理实现之一。

这一重述完成了从具体实验图像到抽象截面结构与统一时间刻度之间的闭合。

[1]: https://arxiv.org/pdf/1006.0639 "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://en.wikipedia.org/wiki/Double-slit_experiment "Double-slit experiment"
[3]: https://arxiv.org/abs/1505.04753 "Entanglement Equilibrium and the Einstein Equation"
[4]: https://arxiv.org/abs/1509.02542 "[1509.02542] Proof of the Quantum Null Energy Condition"
[5]: https://arxiv.org/pdf/math-ph/0511034 "Tomita–Takesaki Modular Theory"
[6]: https://www.theorie.physik.uni-goettingen.de/forschung2/qft/theses/dipl/Paetz.pdf "An Analysis of the 'Thermal-Time Concept' of Connes and ..."
[7]: https://link.aps.org/doi/10.1103/PhysRevD.109.064026 "Boundary terms and Brown-York quasilocal parameters for ..."
[8]: https://www.researchgate.net/publication/27358287_Krein%27s_trace_formula_and_the_spectral_shift_function "(PDF) Kreĭn's trace formula and the spectral shift function"
[9]: https://www.math.stonybrook.edu/~anderson/ibvpremarks.pdf "the initial boundary value problem and quasi-local ..."
[10]: https://en.wikipedia.org/wiki/Wheeler%27s_delayed-choice_experiment "Wheeler's delayed-choice experiment"
[11]: https://link.aps.org/doi/10.1103/PhysRevLett.95.040401 "Attosecond Double-Slit Experiment | Phys. Rev. Lett."
[12]: https://arxiv.org/abs/2508.09316 "[2508.09316] Demonstration of a photonic time-frequency ..."
[13]: https://pubmed.ncbi.nlm.nih.gov/27258860/ "Entanglement Equilibrium and the Einstein Equation"
[14]: https://link.aps.org/doi/10.1103/PhysRevD.93.064044 "Quantum focusing conjecture | Phys. Rev. D"
[15]: https://arxiv.org/abs/1601.00528 "[1601.00528] Comments on Jacobson's \"Entanglement ..."
[16]: https://arxiv.org/html/2407.18948v1 "The Time in Thermal Time"
[17]: https://www.nature.com/articles/s41598-023-33039-9 "Time domain double slit interference of electron produced ..."
[18]: https://en.wikipedia.org/wiki/Tomita%E2%80%93Takesaki_theory "Tomita–Takesaki theory"
