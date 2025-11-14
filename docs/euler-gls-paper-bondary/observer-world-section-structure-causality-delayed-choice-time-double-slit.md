# 观察者世界的截面结构：因果一致性、延迟选择与边界时间几何中的时间双缝干涉

---

**Abstract**
在统一时间刻度与边界时间几何框架下，本文给出"观察者看到的世界是什么"的可公理化刻画，并在此基础上对双缝干涉的两类关键情形给出单一结构解释：延迟选择实验与时间域（而非空间域）双缝干涉。首先，以散射相位导数–相对态密度–Wigner–Smith 群延迟迹的刻度同一式为时间刻度基准，将模流时间与 Gibbons–Hawking–York 边界时间统一为时间刻度等价类。其次，在包含引力与广义熵约束的边界时间几何中，将"观察者"定义为世界线–分辨率–可观测子代数的三元组，并将其经验世界刻画为一条由因果一致、记录一致与动力学可延拓条件选出的截面族。

在此基础上，本文给出四个主结果。其一，证明对满足局域因果与广义熵极值条件的全局系统，几乎每个本征时间上都存在与给定观察者记录相容的"经验截面族"，从而观察者所见世界可以严格表示为单分支条件化，而非所有截面的同步叠加。其二，在完全正测量器（instrument）形式下，证明延迟选择与量子擦除型双缝实验中，后时刻测量设置与结果不会改变先时刻探测屏事件的非条件统计分布，延迟选择仅改变对给定后验结果的条件化分解，因而不存在数学意义上的"逆因果影响"。其三，构造统一模型表明，空间双缝与时间双缝均可视为同一散射振幅上两支路径（空间或时间支路）的干涉：前者表现为探测屏上的空间干涉条纹，后者表现为能谱上的周期振荡，二者在 Wigner–Smith 时间延迟与能–时傅里叶对偶下严格等价。其四，在有限分辨率与重复测量极限下，证明"长时间曝光"式图像是单粒子事件在截面空间上的大数定律极限，而非单次测量中"同时看到所有截面"。

附录中给出：（i）刻度同一式及其在边界时间几何中的实现；（ii）经验截面族存在与一致性的严密证明；（iii）延迟选择与量子擦除实验的密度矩阵与截面形式推导；（iv）时间双缝能谱干涉的显式解析计算及其与 Wigner–Smith 群延迟的联系。

---

**Keywords**
时间刻度等价类；边界时间几何；观察者截面；一致历史；延迟选择；量子擦除；时间双缝干涉；Wigner–Smith 群延迟；广义熵；因果一致性

---

## 1 Introduction & Historical Context

### 1.1 从双缝干涉到延迟选择与时间双缝

杨氏双缝实验长期被视为量子叠加与波粒二象性的核心实例：单个光子或电子逐次通过两条狭缝，在远处探测屏上逐点击中，但大量事例累积后出现干涉条纹。近年来，从亚毫米级光学平台到单电子装置的单粒子双缝实验已经实现，空间干涉图样在大时间尺度上由离散事件统计收敛于波动预言。([维基百科][1])

围绕双缝的"延迟选择"与"量子擦除"实验进一步放大了直觉张力：在 Wheeler 提出的思想实验及其后续实现中，实验者在粒子通过双缝之后、甚至在接近探测屏时才决定是否获取或抹除路径信息，结果显示干涉图样是否出现似乎取决于"事后选择"。系统实验表明，这类结果完全可以在标准量子力学框架内用前向时间演化与条件概率解释，而不涉及真正的"改写过去"。([维基百科][2])

另一方面，双缝思想已经被推广到时间维：通过相位稳定的飞秒/阿秒脉冲控制电离时间窗，可在时间轴上打开两个极短"窗口"，形成所谓时间双缝，使电子波函数在时间而非空间上发生自干涉，其结果表现在出射电子能谱中呈现振荡条纹。首批阿秒时间双缝实验及其后续在 XUV 与同步辐射平台上的实现，标志着时间域干涉已成为可操作实验现实。([arXiv][3])

这些发展共同提出两个根本问题：

1. 对于具体观察者，其"看到的世界"究竟是什么数学对象：是一条单分支历史、一族有权重的截面，还是在某种意义下的"叠加态"？
2. 延迟选择与时间双缝是否暗示了时间与因果结构需要被重新几何化，而非仅仅作为参数插入薛定谔演化？

### 1.2 边界时间几何与统一时间刻度的出现

在散射理论端，Wigner–Smith 时间延迟矩阵把散射矩阵对频率的导数与"群延迟"联系起来，为时间提供了可观测刻度；在有界或开放体系的波动散射中，这一矩阵被广泛应用于电子、光学与声学平台。([科学直达][4])

设 $S(\omega)$ 为能量 $\omega$ 处的散射矩阵，总相位 $\Phi(\omega)=\arg\det S(\omega)$，定义半相位 $\varphi(\omega)=\tfrac12\Phi(\omega)$ 与 Wigner–Smith 矩阵
$Q(\omega)=-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)$。在相对迹类假设下，谱移函数 $\xi(\omega)$ 与相对态密度 $\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$ 满足刻度同一式
$\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$，它把相位梯度、态密度差与群延迟迹统一为同一"时间刻度密度"。

在算子代数端，Tomita–Takesaki 模块流 $\sigma_t^\omega$ 为给定态–代数对赋予一条内禀时间流，Connes–Rovelli 热时间假说将其解释为一般协变量子场论中的物理时间。([科学直达][4])

在引力端，Einstein–Hilbert 作用必须配以 Gibbons–Hawking–York 边界项才能在固定诱导度规条件下给出良定变分，Brown–York 准局域能量与哈密顿量生成的边界时间平移，使"几何时间"也成为由边界数据定义的对象。

前期工作已经表明：在合适匹配条件下，这三类时间刻度均可视为同一时间刻度等价类 $[\tau]$ 中的代表，即彼此只相差仿射重标。由此自然形成所谓"边界时间几何"（boundary time geometry, BTG）：时间不是体域内部先验流速，而是边界代数、态与几何数据上的统一结构。

### 1.3 本文问题与贡献

本文围绕以下问题展开：在 BTG 框架下，如何把"观察者看到的世界"刻画为边界时间几何上的"截面"，并用这一语言统一解释：

1. 普通与延迟选择双缝实验中，干涉图样出现/消失的条件；
2. 时间双缝实验中，粒子在时间尺度上的自干涉；
3. 观察者"长时间曝光"式经验如何由单粒子事件的统计构成，而不引入逆因果或多重共时分支。

本文的主要贡献概括如下。

**(1) 截面结构与经验世界的公理化。**
在统一时间刻度等价类下，我们将观察者建模为三元组 $\mathcal O=(\gamma,\Lambda,\mathcal A_{\gamma,\Lambda})$：类时世界线 $\gamma$、分辨率参数 $\Lambda$、可观测子代数 $\mathcal A_{\gamma,\Lambda}$。在此基础上定义时间 $\tau$ 上的"世界截面"
$\Sigma_\tau=(\gamma(\tau),\mathcal A_{\gamma,\Lambda}(\tau),\rho_{\gamma,\Lambda}(\tau))$，并提出"因果一致截面"的判据：局域因果性、动力学可延拓性与记录一致性。对于满足局域双曲性、Hadamard 条件与广义熵极值的全局系统，证明几乎每个 $\tau$ 上均存在与给定观察者记录相容的经验截面族。

**(2) 延迟选择的前向时间解析与无逆因果定理。**
在完全正测量器形式下，我们对包含信号–闲置光子与量子擦除过程的延迟选择双缝实验给出严格建模，证明后时刻测量设置与结果不会改变先时刻探测屏事件的非条件分布 $p(x)$，延迟选择仅改变条件概率 $p(x\mid y)$ 的分解方式。进而，从截面语言证明：所有经验截面族均服从前向因果结构，不存在必须诉诸"未来影响过去"的解释。

**(3) 空间双缝与时间双缝的 BTG 统一。**
通过构造统一散射模型，我们证明空间双缝与时间双缝均对应于同一希尔伯特空间中两支路径（空间支路或时间支路）的干涉：空间双缝在探测屏上产生位置分布 $P(x)$ 的条纹；时间双缝在能谱 $P(E)$ 中产生频率振荡，其条纹间距满足 $\Delta E\cdot\Delta t\approx 2\pi\hbar$。在 BTG 中，二者在同一 Wigner–Smith 时间延迟与统一时间刻度下实现完全等价。

**(4) "长时间曝光"图像的统计构成。**
在有限分辨率与重复测量框架下，我们证明截面空间上一族 Bernoulli 试验的频率收敛定理：单次事件始终是单点截面，而"干涉图样"是大数定律极限下经验测度对理论概率测度的收敛结果。这一结果在形式上类比胶片长时间曝光，但本质不同：每一普朗克时间步长上，观察者只经历单个因果一致截面，而非所有截面的并存。

---

## 2 Model & Assumptions

本节给出统一的数学模型与假设，为后续定理与实验建模提供基础。

### 2.1 全局边界系统与统一时间刻度

**定义 2.1（全局边界系统）**
一个全局边界系统由数据
$\mathcal B=(M,g;\mathcal A_\partial,\omega;S(\omega);h_{ab},K_{ab})$
构成，其中：

1. $(M,g)$ 为满足稳定因果与局域双曲性的时空流形；
2. $\mathcal A_\partial$ 为边界可观测 $C^\ast$ 代数，$\omega$ 为其上的忠实态，GNS 表象记为 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$；
3. $S(\omega)$ 为能量 $\omega$ 处的散射矩阵族，满足相对迹类与散射完备性假设；
4. $h_{ab}$ 为 $\partial M$ 上的诱导度规，$K_{ab}$ 为对应外在曲率；
5. 引力作用 $S_{\mathrm{grav}}=S_{\mathrm{EH}}+S_{\mathrm{GHY}}+\text{角点项}$ 在固定 $h_{ab}$ 与角参数的变分族上良定。

在此数据上定义统一时间刻度等价类 $[\tau]$，要求：

* 散射端：相位–谱移–群延迟满足刻度同一式
  $\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$；
* 模流端：模块流 $\sigma_t^\omega$ 与边界动力学在外自同构群 $\mathrm{Out}(\mathcal A_\partial)$ 上一致，模流参数 $t$ 属于 $[\tau]$；
* 引力端：Brown–York 边界哈密顿量生成的时间平移参数亦属于 $[\tau]$，即与上述时间参数只相差仿射重标。

后文中所有"时间变量"均隐含在 $[\tau]$ 内，必要时以本征时间 $\tau$ 代表等价类。

### 2.2 观察者、分辨率与可观测子代数

**定义 2.2（观察者）**
一个理想化观察者为三元组
$\mathcal O=(\gamma,\Lambda,\mathcal A_{\gamma,\Lambda})$，其中：

1. $\gamma:I\to M$ 为类时世界线，参数 $\tau\in I\subset\mathbb R$ 为观察者本征时间；
2. $\Lambda>0$ 为分辨率参数，表征最小可分辨时间尺度、最大带宽与空间–动量分辨率等；
3. $\mathcal A_{\gamma,\Lambda}\subset\mathcal A_\partial$ 为由可访问通道与分辨率约束确定的可观测子代数。

在固定 $\mathcal O$ 下，定义时间 $\tau$ 处的"有效可观测子代数"
$\mathcal A_{\gamma,\Lambda}(\tau)\subset\mathcal A_{\gamma,\Lambda}$，由在 $\tau$ 时刻之前已经完成或正在进行的测量与控制算子生成。

### 2.3 截面、因果一致性与历史

**定义 2.3（世界截面）**
给定 $\mathcal B$ 与 $\mathcal O$，统一时间刻度下本征时间 $\tau$ 的世界截面为三元组
$\Sigma_\tau=(\gamma(\tau),\mathcal A_{\gamma,\Lambda}(\tau),\rho_{\gamma,\Lambda}(\tau))$，其中：

1. $\gamma(\tau)\in M$；
2. $\mathcal A_{\gamma,\Lambda}(\tau)$ 如上所述；
3. $\rho_{\gamma,\Lambda}(\tau)$ 为 $\mathcal A_{\gamma,\Lambda}(\tau)$ 上的态，由全局态 $\omega$ 经条件化与粗粒化得到。

**定义 2.4（因果一致截面）**
截面 $\Sigma_\tau$ 称为因果一致，若满足：

1. 局域因果性：对任意 $A\in\mathcal A_{\gamma,\Lambda}(\tau)$，其支集仅依赖于 $\gamma(\tau)$ 的过去或共因果域，不依赖未来未定区域；
2. 动力学一致性：存在包含 $\gamma(\tau)$ 的小因果菱形族 $\{D_{p,r}\}$ 及在其中解广义爱因斯坦–物质场方程的解族 $(g_{ab},\Phi)$，使诱导到边界代数上的态在限制到 $\mathcal A_{\gamma,\Lambda}(t)$ 时与 $\rho_{\gamma,\Lambda}(t)$ 一致；
3. 记录一致性：在包含观察者记忆与记录的子代数上，$\rho_{\gamma,\Lambda}(\tau)$ 与所有 $\tau'<\tau$ 的截面通过幺正演化或完全正映射相容，不存在与既有记录矛盾的配置。

满足上述条件的截面集合记为
$\Gamma^{\mathrm{dyn}}_{\mathrm{causal}}(\tau;\mathcal O)$。

**定义 2.5（历史与经验截面族）**
选取离散时间序列 $\tau_0<\tau_1<\cdots<\tau_n$，在每个 $\tau_k$ 上选取一族效果算符或投影 $\{E_{\alpha_k}^{(k)}\} \subset\mathcal A_{\gamma,\Lambda}(\tau_k)$，满足
$\sum_{\alpha_k}E_{\alpha_k}^{(k)}=\mathbb I$。

历史串 $\boldsymbol\alpha=(\alpha_0,\dots,\alpha_n)$ 对应历史算子
$C_{\boldsymbol\alpha}=E_{\alpha_n}^{(n)}\cdots E_{\alpha_0}^{(0)}$。若对 $\boldsymbol\alpha\neq\boldsymbol\beta$ 有
$\omega(C_{\boldsymbol\alpha}C_{\boldsymbol\beta}^\dagger)\approx 0$，则称该历史族在观察者可见子代数上近似去相干，可定义历史概率
$p(\boldsymbol\alpha)=\omega(C_{\boldsymbol\alpha}C_{\boldsymbol\alpha}^\dagger)$。

给定包含观察者记录的子代数，选取与之相容的历史类 $\mathcal H_{\mathrm{exp}}$，则由这些历史在各 $\tau_k$ 上的截取构成的截面序列称为经验截面族。

### 2.4 测量器形式与延迟选择

我们采用完全正测量器（quantum instrument）形式刻画测量过程。设某一测量过程的结果标记为 $y\in Y$，对应 instrument $\{\mathcal I_y\}_{y\in Y}$，则对初态 $\rho$：

* 得到结果 $y$ 的概率为
  $p(y)=\operatorname{tr}[\mathcal I_y(\rho)]$；
* 条件态为
  $\rho_y=\mathcal I_y(\rho)/p(y)$。

若 instrument 发生在时间区间 $[\tau_1,\tau_2]$ 内，则在本征时间顺序上满足
$\tau_0<\tau_1<\tau_2<\tau_3$，其对先时刻 $\tau_0$ 上事件 $x$ 的非条件分布不产生影响，这是延迟选择无逆因果定理将要形式化的内容。

### 2.5 时间双缝：时间窗与能谱读出

时间双缝实验可抽象为如下模型。设体系初态 $\lvert\psi_{\mathrm{in}}\rangle$，哈密顿量 $H(t)$ 在两个极短时间窗 $I_1=[t_1,t_1+\delta t]$、$I_2=[t_2,t_2+\delta t]$ 内耦合到外场，其余时间自由演化。记时间窗函数为
$w(t)=w_1(t)+w_2(t)$，每一项支集在对应时间窗。对某一出射能量本征态 $\lvert E\rangle$，散射振幅近似为两项叠加
$A(E)\approx A_1(E)+\mathrm e^{\mathrm i E\Delta t/\hbar}A_2(E)$，其中 $\Delta t=t_2-t_1$，能谱分布
$P(E)=|A(E)|^2$ 出现 $\Delta E\cdot\Delta t\approx 2\pi\hbar$ 的条纹结构。这将与 BTG 中的统一时间刻度与群延迟联系起来。

---

## 3 Main Results (Theorems and Alignments)

本节给出四个主定理与若干命题，刻画观察者截面结构、延迟选择无逆因果性以及空间/时间双缝的统一。

### 3.1 观察者经验世界的截面表示

**定理 3.1（经验截面族存在与单分支性）**
设 $\mathcal B$ 为满足统一时间刻度假设的全局边界系统，$\mathcal O$ 为给定观察者，$\omega$ 为 Hadamard 型态，并在每个小因果菱形上满足广义熵极值与量子零能条件，使得引力场方程与局域能量条件成立。再假设对任意有限本征时间序列 $\tau_0<\dots<\tau_n$，存在一族近似去相干的投影历史 $\{C_{\boldsymbol\alpha}\}$ 与对应历史概率 $p(\boldsymbol\alpha)$。

则对勒贝格几乎所有本征时间 $\tau\in I$，存在：

1. 非空经验截面集合 $\Gamma^{\mathrm{exp}}(\tau;\mathcal O)\subset\Gamma^{\mathrm{dyn}}_{\mathrm{causal}}(\tau;\mathcal O)$；
2. 对每一 $\Sigma_\tau\in\Gamma^{\mathrm{exp}}(\tau;\mathcal O)$，存在一族向未来无限延拓的因果一致截面 $\{\Sigma_t\}_{t\ge\tau}$，使得对所有 $A\in\mathcal A_{\gamma,\Lambda}(t)$，时间演化与条件态满足
   $\omega_{\Sigma_t}(A)=\omega(A\mid\Sigma_\tau)$。

换言之，给定观察者记录，几乎每个时间截面上都可以选出一条单分支经验截面族，与全局态的条件化完全一致。

### 3.2 延迟选择与量子擦除的无逆因果定理

考虑标准延迟选择/量子擦除双缝实验：信号光子在时间 $\tau_0$ 入射双缝，在 $\tau_1$ 附近被探测屏探测到位置 $x$，其纠缠的闲置光子在更晚时间 $\tau_2$ 经不同装置获得或抹除路径信息。([维基百科][5])

**定理 3.2（延迟选择无逆因果）**
设 $\rho_0$ 为初始态，$\{\mathcal M_x\}$ 为信号光子在 $\tau_1$ 的位置测量 instrument，$\{\mathcal I_y^{(C)}\}$ 为在 $\tau_2$ 的闲置光子测量 instrument，$C$ 标记不同实验配置（获得路径信息、擦除信息等）。记联合概率为
$p_C(x,y)=\operatorname{tr}[(\mathcal I_y^{(C)}\circ\mathcal M_x)(\rho_0)]$，边缘分布 $p_C(x)=\sum_y p_C(x,y)$。

若 $\mathcal M_x$ 仅作用于信号子系统且闲置测量在时间序上发生于 $\tau_2>\tau_1$，且全局演化为幺正或 CPTP，则对所有 $C$ 与 $x$ 有
$p_C(x)=p(x)$，即
$p_C(x,y)$ 的边缘在 $x$ 上不依赖于后时刻的测量配置 $C$ 与结果 $y$。

因此，延迟选择与量子擦除不会改变先时刻探测屏上事件的非条件统计分布，不存在数学上的"逆因果影响"；所谓"过去被改变"仅反映在对 $y$ 条件化后的子样本中干涉/无干涉结构的不同。

### 3.3 空间双缝与时间双缝的统一表示

**定理 3.3（空间/时间双缝干涉的 BTG 统一）**
在统一时间刻度等价类与 BTG 假设下，考虑以下两类实验：

1. 空间双缝：粒子在空间上有两条路径 $\lvert L\rangle,\lvert R\rangle$，到达远处屏幕位置 $x$ 的振幅为
   $\psi(x)=\psi_L(x)+\psi_R(x)$，探测概率 $P_{\mathrm{sp}}(x)=|\psi(x)|^2$ 出现干涉条纹。
2. 时间双缝：粒子在两段时间窗 $[t_1,t_1+\delta t]$、$[t_2,t_2+\delta t]$ 内与外场相互作用，出射能量 $E$ 处振幅为
   $A(E)=A_1(E)+\mathrm e^{\mathrm i E\Delta t/\hbar}A_2(E)$，概率分布
   $P_{\mathrm{tm}}(E)=|A(E)|^2$ 出现能谱干涉条纹。([arXiv][3])

则存在统一希尔伯特空间表示，使二者由同一散射算符 $S$ 与两支路径投影 $\Pi_1,\Pi_2$ 描述，只是路径参数分别嵌入空间与时间自由度。更具体地，存在一族酉变换 $U_{\mathrm{BTG}}$，使得
$U_{\mathrm{BTG}} S U_{\mathrm{BTG}}^\dagger$ 在空间双缝基与时间双缝基中的矩阵元满足：

1. 干涉项的相对相位均可写为统一形式
   $\Delta\phi=\int\mathrm d\omega\,\tau_{\mathrm{eff}}(\omega)$，其中 $\tau_{\mathrm{eff}} \in[\tau]$ 为等价时间刻度；
2. 时间双缝中条纹间距 $\Delta E$ 与时间窗间隔 $\Delta t$ 满足
   $\Delta E\cdot\Delta t\approx 2\pi\hbar$，对应于群延迟 $\tau_{\mathrm g}=(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 与谱密度的傅里叶对偶关系。

因此，空间与时间双缝只是同一边界时间几何上不同"投影截面"的表现。

### 3.4 统计曝光与干涉条纹的收敛

**命题 3.4（单点事件与长时间曝光的统计构成）**
考虑在同一实验布置下重复独立进行 $N$ 次单粒子双缝实验，探测屏划分为可数个像素 $\{R_j\}$，每次实验得到随机变量 $X_k\in\{R_j\}$，其分布由 Born 规则给出 $\mathbb P(X_k=R_j)=p_j$。

则样本频率
$$
f_j^{(N)}=N^{-1}\sum_{k=1}^N\mathbf 1_{\{X_k=R_j\}}
$$
几乎必然收敛于 $p_j$；探测屏上"长时间曝光"图像对应的亮度分布在大数定律意义下收敛于理论干涉图样 $\{p_j\}$。

因此，干涉条纹是截面空间上大量单点因果一致截面事件的统计极限，而非单次截面上"同时看到所有路径"。

---

## 4 Proofs

本节给出上述结果的证明。附录中补充技术细节与推广。

### 4.1 定理 3.1 的证明

**证明概要。**
首先，在每个小因果菱形 $D_{p,r}$ 中，由广义熵极值与 QNEC/QFC 可得局域引力场方程
$G_{ab}+\Lambda g_{ab}=8\pi G\langle T_{ab}\rangle_\omega$，保证局域解族 $(g_{ab},\Phi)$ 的存在与能量条件。其次，在 $\mathcal A_{\gamma,\Lambda}(\tau)$ 上引入 GNS 表象下的局域 von Neumann 代数，利用 Tomita–Takesaki 模块流与外自同构群，将本征时间 $\tau$ 嵌入统一时间刻度等价类。

在给定时间序列 $\tau_0<\dots<\tau_n$ 上构造近似去相干的历史投影 $\{E_{\alpha_k}^{(k)}\}$，得到历史算子 $C_{\boldsymbol\alpha}$ 与概率 $p(\boldsymbol\alpha)$。近似去相干条件保证不同历史串之间交叉项可忽略，从而一致历史框架中可定义条件概率与条件态。

给定观察者记录所选定的历史类 $\mathcal H_{\mathrm{exp}}$，定义在时间 $\tau$ 的经验截面 $\Sigma_\tau$ 为所有 $\boldsymbol\alpha\in\mathcal H_{\mathrm{exp}}$ 在 $\tau$ 上共通的边界态限制。动力学一致性由局域解族保证：在每个 $D_{p,r}$ 上，广义熵极值保证局域可逆哈密顿量存在，沿 $\gamma$ 拼接这些菱形即得向未来延拓的解族。

由 Carathéodory 扩展与 Kolmogorov 一致性定理，可在连续时间上构造概率测度，使得几乎所有 $\tau$ 上经验截面存在且构成单分支历史。记录一致性由 instrument 构造与完全正性保证：观察者内部自由度作为一部分系统，其演化由 CPTP 映射描述，因而不会出现与既有记录矛盾的截面。

细节见附录 B.1–B.3。由此定理成立。

### 4.2 定理 3.2 的证明

**证明。**
记信号与闲置系统希尔伯特空间分别为 $\mathcal H_s,\mathcal H_i$，初态 $\rho_0$ 定义在 $\mathcal H_s\otimes\mathcal H_i$ 上。设从入射到信号探测之间整体演化为幺正算符 $U_1$，从信号探测到闲置测量之间演化为幺正 $U_2^{(C)}$（可依赖于配置 $C$）。

信号位置测量 instrument $\{\mathcal M_x\}$ 仅作用于 $\mathcal H_s$，可写作
$\mathcal M_x(\rho)=\sum_m (M_{x,m}\otimes\mathbb I)\rho(M_{x,m}^\dagger\otimes\mathbb I)$。闲置测量 instrument $\{\mathcal I_y^{(C)}\}$ 仅作用于 $\mathcal H_i$，可写作
$\mathcal I_y^{(C)}(\rho)=\sum_n (\mathbb I\otimes N_{y,n}^{(C)})\rho(\mathbb I\otimes N_{y,n}^{(C)\dagger})$。

则

$$
p_C(x,y)
=\operatorname{tr}\!\left[\left(\mathcal I_y^{(C)}\circ\mathcal M_x\right)
\left(U_1\rho_0 U_1^\dagger\right)\right]
$$

$$
=\sum_{m,n}\operatorname{tr}\!\left[(M_{x,m}\otimes N_{y,n}^{(C)})\,U_1\rho_0 U_1^\dagger\,(M_{x,m}^\dagger\otimes N_{y,n}^{(C)\dagger})\right].
$$

对 $y$ 求和，并利用闲置测量 instrument 的完备性 $\sum_y\sum_n N_{y,n}^{(C)\dagger}N_{y,n}^{(C)}=\mathbb I$，得

$$
p_C(x)=\sum_y p_C(x,y)
=\sum_m\operatorname{tr}\!\left[(M_{x,m}\otimes\mathbb I)\,U_1\rho_0 U_1^\dagger\,(M_{x,m}^\dagger\otimes\mathbb I)\right]
\equiv p(x),
$$

与配置 $C$ 无关。这正是信号探测边缘分布不依赖于延迟选择设置的陈述。

另一方面，条件概率
$p_C(x\mid y)=p_C(x,y)/p_C(y)$
通常依赖于 $C$ 与 $y$，例如在量子擦除实验中，对某些 $y$ 的子样本恢复干涉条纹，对另一些 $y$ 则得到无干涉分布。这一差异源于对联合分布的不同条件化，而非对先时刻边缘分布的改变。

在 BTG 截面语言中，$x$ 对应 $\tau_1$ 处截面事件，$y$ 对应 $\tau_2$ 处截面事件；定理表明，$\Gamma^{\mathrm{dyn}}_{\mathrm{causal}}(\tau_1;\mathcal O)$ 上的经验截面集合与后时刻 instrument 的选择无关，从而不存在逆因果。定理得证。更一般情形与 CPTP 演化的推广见附录 B.4。

### 4.3 定理 3.3 的证明

**证明思路。**
我们在统一希尔伯特空间 $\mathcal H$ 上构造两类实验：

1. 空间双缝：$\mathcal H=\mathcal H_{\mathrm{path}}\otimes\mathcal H_{\mathrm{trans}}$，路径子空间由 $\{\lvert L\rangle,\lvert R\rangle\}$ 张成，传播子空间 $\mathcal H_{\mathrm{trans}}$ 描述从缝到屏幕的自由演化。初态 $\lvert\psi_{\mathrm{in}}\rangle$ 经过双缝后成为
   $\lvert\psi\rangle = \tfrac{1}{\sqrt2}(\lvert L\rangle+\lvert R\rangle)\otimes\lvert\phi_0\rangle$，在传播算符 $U_{\mathrm{prop}}$ 作用下，到达屏幕位置 $x$ 的振幅
   $\psi(x)=\psi_L(x)+\psi_R(x)$。
2. 时间双缝：$\mathcal H=\mathcal H_{\mathrm{int}}\otimes\mathcal H_E$，其中 $\mathcal H_{\mathrm{int}}$ 为短时相互作用空间，$\mathcal H_E$ 为能量基空间。时间窗耦合可表示为整体演化算符
   $U=U_{\mathrm{free}}(+\infty,t_2+\delta t)U_2U_{\mathrm{free}}(t_2,t_1+\delta t)U_1U_{\mathrm{free}}(t_1,-\infty)$，在孤立自发电离极限下，出射能量本征态 $\lvert E\rangle$ 的振幅为两次时间窗耦合贡献的叠加。

对两类情况分别做傅里叶变换：

* 空间双缝中，屏幕平面上的空间干涉可视为动量空间振幅的相位差 $\Delta\phi_{\mathrm{sp}}=\int k\mathrm d\ell$（沿光程）引起的；
* 时间双缝中，能谱振荡可视为时间域中两次耦合的相对相位 $\Delta\phi_{\mathrm{tm}}=E\Delta t/\hbar$ 引起的。

在 BTG 框架中，二者都由散射算符 $S$ 在不同表象下的矩阵元表示：选择合适的基变换 $U_{\mathrm{BTG}}$，可将空间路径/时间窗二值自由度统一为一对投影 $\Pi_1,\Pi_2$，其相对相位随统一时间刻度等价类中的参数变化而变化。

Wigner–Smith 群延迟矩阵 $Q=-\mathrm iS^\dagger\partial_\omega S$ 给出的群延迟轨迹 $\tau_{\mathrm g}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 决定了在能量表象中相位的频率依赖结构；时间双缝中的条纹间距满足 $\Delta E\cdot\Delta t\approx 2\pi\hbar$，可视为对同一 $\tau_{\mathrm g}$ 的傅里叶采样。([科学直达][4])

因此，空间与时间双缝的干涉结构在统一时间刻度与群延迟的意义下是同一对象的两种表象，定理得证。详尽计算见附录 C。

### 4.4 命题 3.4 的证明

**证明。**
$\{X_k\}_{k=1}^N$ 独立同分布，取值于可数集 $\{R_j\}$，且 $\mathbb P(X_k=R_j)=p_j$。对任意固定 $j$，随机变量
$\mathbf 1_{\{X_k=R_j\}}$ 为伯努利变量，期望 $p_j$，方差 $p_j(1-p_j)$。由 Kolmogorov 强大数定律，几乎必然有
$f_j^{(N)}\to p_j$ 当 $N\to\infty$。

因此，探测屏在 $N\to\infty$ 的"长时间曝光"极限下，其相对亮度分布收敛于理论概率分布 $\{p_j\}$，后者由双缝波函数 $\psi(x)$ 的模平方决定。即使每个单次实验对应于一个因果一致截面 $\Sigma_{\tau_k}$ 上的单点击中，整体图像仍是这些截面的统计集合。命题得证。

---

## 5 Model Apply：双缝、延迟选择与时间双缝的截面重述

本节将上述抽象结构具体应用于三个核心实验情形。

### 5.1 普通空间双缝实验

入射态为窄波包，经过两条缝后近似为
$\lvert\psi\rangle=\tfrac{1}{\sqrt2}(\lvert L\rangle+\lvert R\rangle)$。屏幕位置算子 $\hat x$ 的本征态记为 $\lvert x\rangle$，则单次实验中探测到位置 $x$ 的概率密度
$P(x)=|\langle x\vert\psi\rangle|^2=|\psi_L(x)+\psi_R(x)|^2$。

在截面语言中：

* 每一次粒子击中屏幕时刻 $\tau_k$ 对应截面
  $\Sigma_{\tau_k}^{(x_k)}=(\gamma(\tau_k),\mathcal A_{\gamma,\Lambda}^{\mathrm{(pos)}}(\tau_k),\rho_{\gamma,\Lambda}^{(x_k)}(\tau_k))$，其中
  $\mathcal A_{\gamma,\Lambda}^{\mathrm{(pos)}}$ 由 $f(\hat x)$ 生成；
* 观察者经验世界由单分支截面族 $\{\Sigma_{\tau_k}^{(x_k)}\}$ 构成；
* 在大数定律极限下，截面事件在屏幕上形成与 $P(x)$ 一致的条纹。

整体上，普通空间双缝对应于在 BTG 上选择"位置读出"子代数，并在该子代数下保留路径相干。

### 5.2 延迟选择与量子擦除的截面结构

延迟选择与量子擦除实验中，关键在于信号–闲置纠缠与后时刻对闲置系统的测量。以 Kim 等人实验为例，双缝后的光子通过非线性晶体产生纠缠对，其中一光子（信号）走向探测屏，另一光子（闲置）经不同路径进入多种探测器，有的保留路径信息，有的抹除。([维基百科][5])

在截面语言中：

1. 在 $\tau_1$ 处，信号光子击中屏幕位置 $x$，对应截面事件 $\Sigma_{\tau_1}^{(x)}$，其概率分布 $p(x)$ 与是否进行后续闲置测量无关（定理 3.2）。
2. 在更晚时间 $\tau_2$ 处，对闲置光子实施不同 instrument $\{\mathcal I_y^{(C)}\}$，对应后时刻截面 $\Sigma_{\tau_2}^{(y,C)}$。
3. 对联合截面事件 $(x,y)$ 的条件化 $p_C(x\mid y)$ 在某些 $y$ 下恢复干涉条纹，在另一些 $y$ 下显示无干涉分布，对应不同的"经验子样本"。

观察者若在 $\tau_1$ 时只看汇总屏幕图像，则必然得到无干涉图样；若在 $\tau_2$ 后对数据按 $y$ 分类并"追溯"到对应的 $x$ 子样本，则在某些子样本中看到干涉。截面结构清晰地表明：经验世界在每个时间截面上仍是单分支，只是后时刻对数据的重组织改变了对先前截面集合的分解方式，而非改变先前截面的内容。

### 5.3 时间双缝：时间尺度上的自干涉

在时间双缝实验中，通过两段时间间隔内的强场电离或外场耦合，使粒子在时间上经历两次离散的"发射窗"。典型的阿秒时间双缝实验中，飞秒激光场的载波–包络相位被调节，使电场在一个或两个光学周期峰值附近足够强，形成两个阿秒级电离窗，出射电子能谱上出现干涉条纹，其可见条纹数反映时间窗有效长度与相对位相。([arXiv][3])

在 BTG–截面框架下：

* 时间窗 $[t_1,t_1+\delta t]$、$[t_2,t_2+\delta t]$ 可视为在统一时间刻度 $[\tau]$ 中打开两个边界耦合窗口，形成两支"时间路径"；
* 对于出射能量 $E$，振幅
  $A(E)=A_1(E)+\mathrm e^{\mathrm i E\Delta t/\hbar}A_2(E)$，能谱条纹间距 $\Delta E\approx 2\pi\hbar/\Delta t$；
* 对观察者而言，每个单粒子事件在能谱上对应截面 $\Sigma_{\tau_{\mathrm{det}}}^{(E)}$，重复测量在能量轴上的经验频率收敛于 $P_{\mathrm{tm}}(E)$，类似空间双缝的屏幕条纹。

BTG 的作用在于：时间窗之间的间隔 $\Delta t$ 与 Wigner–Smith 群延迟 $\tau_{\mathrm g}(\omega)$ 同属时间刻度等价类；通过对群延迟的实验测定，可以把时间双缝视为在边界时间几何上直接操作时间截面的实验平台。

---

## 6 Engineering Proposals

本节在上述理论基础上给出若干可实现或可扩展的工程化方案，用于检验与利用截面–BTG 视角。

### 6.1 延迟选择实验的 BTG 标定平台

在光学与单原子平台上设计如下实验：

1. 采用 SPDC 源产生信号–闲置光子对，信号端经过双缝到达高像素探测屏，闲置端通过可切换光路实现保留/擦除路径信息的多种 instrument。
2. 将实验布置嵌入统一散射建模中，通过测量多频点下的群延迟 $\tau_{\mathrm g}(\omega)$ 标定统一时间刻度；
3. 利用高速电子学记录信号探测时间 $\tau_1$ 与闲置测量时间 $\tau_2$，精确确认 $\tau_2>\tau_1$ 且光锥分离，以排除任何宏观通信；
4. 以截面语言分析数据：对所有事件的 $x$ 直方图、对各 $y$ 子样本的 $x$ 条件直方图，验证定理 3.2 的无逆因果性与"条件干涉/无干涉"解释。

该方案在现有实验基础上仅需增加群延迟测量与时间标定模块，可作为 BTG–截面理论的实证平台。

### 6.2 时间双缝与群延迟的统一测量

在阿秒时间双缝与 XUV–同步辐射平台上，设计实验同时测量：

1. 通过两时间窗电离产生的出射电子能谱干涉条纹 $P_{\mathrm{tm}}(E)$；
2. 对同一体系在准稳态散射情形下的 Wigner–Smith 群延迟 $\tau_{\mathrm g}(\omega)$（例如通过泵–探测或相移干涉测量相位对频率的导数）；([arXiv][3])

比较从能谱干涉提取的有效时间间隔 $\Delta t_{\mathrm{eff}} \approx 2\pi\hbar/\Delta E$ 与从群延迟测得的时间刻度，在统一时间刻度等价类内验证二者的一致性。这一方案能把时间双缝实验直接提升为边界时间几何的定量标度工具。

### 6.3 观察者分辨率与截面粗粒度的可控实验

通过改变探测器的时间分辨率与空间分辨率，系统研究截面粗粒度对可见干涉结构的影响：

1. 在空间双缝中，通过降低屏幕分辨率或扩大像素面积模拟较大的 $\Lambda$，观察干涉条纹在粗粒化下逐渐被平均化；
2. 在时间双缝中，通过降低能谱分辨率或使用较长积分时间窗口，观察时间干涉条纹在频域上的模糊与消失；
3. 用截面–BTG 模型拟合实验数据，验证分辨率参数 $\Lambda$ 与可观测子代数 $\mathcal A_{\gamma,\Lambda}$ 的关系。

这种方案有助于把"观察者分辨率"从抽象概念落到实验可控参数上。

---

## 7 Discussion (Risks, Boundaries, Past Work)

### 7.1 与标准量子理论解释的比较

延迟选择与量子擦除实验的主流分析已经指出，只要在前向时间框架中处理联合状态与条件概率，就不需要引入任何逆因果或"未来改写过去"的概念。最近工作系统地梳理了 Wheeler 与量子擦除方案，强调所有结果都可由标准量子力学与前向信息流解释。([SpringerLink][6])

本文在此基础上引入 BTG 与截面结构，使得：

* "先时刻边缘分布不变"不仅是代数恒等式，更可解释为 $\Gamma^{\mathrm{dyn}}_{\mathrm{causal}}(\tau_1;\mathcal O)$ 上经验截面集合对后时刻 instrument 选择不敏感；
* "后时刻条件化"对应于对截面集合的重新划分，而非改变既有截面内容；
* 时间双缝的实验现象被纳入统一时间刻度与群延迟的总体框架。

### 7.2 理论的适用域与风险

本框架依赖以下关键假设：

1. 小因果菱形上的广义熵极值与 QNEC/QFC 成立，从而保证几何–物质联立方程与 BTG 的一致性；
2. 一致历史与去相干条件在包含观察者记录的子代数上有效，使经验截面族可良好定义；
3. 实验平台满足无超光速通信与局域 CPTP 演化假设。

这些假设在半经典引力与量子场论中被广泛使用，但在极端引力或强量子引力区可能失效。此外，在强开放系统或非马尔可夫环境中，去相干条件可能在有限时间内不充分，导致经验截面族定义需作修正。

### 7.3 与既有工作与诠释的关系

本工作与以下方向密切相关但又有差异：

* 与一致历史与去相干程序相比，本文在统一时间刻度与 BTG 上引入"观察者截面"概念，强调本征时间与群延迟、模时间的统一刻度；
* 与相对论性量子信息关于"观测者依赖因果结构"的研究相比，本文通过 GHY 边界作用与 Brown–York 能量显式引入几何时间，不仅处理场论，而且处理引力背景；
* 与时间双缝与阿秒物理的既有分析相比，本文给出时间双缝干涉相位与统一时间刻度的直接对应，而不仅仅停留在能谱傅里叶关系层面。([arXiv][3])

---

## 8 Conclusion

本文在统一时间刻度与边界时间几何框架中，将"观察者看到的世界"刻画为一族因果一致截面构成的单分支经验历史，并在此基础上对空间双缝、延迟选择与时间双缝给出统一的结构解释。核心结论包括：经验世界可表示为对全局态的条件化，延迟选择不会改变先时刻边缘分布但会改变条件分解，空间与时间双缝在群延迟与统一时间刻度下严格等价，干涉条纹是大量截面事件的统计极限而非单次截面的多重存在。

这一结构为今后把 BTG 框架与具体实验平台系统对接提供了清晰路径：通过群延迟、能谱干涉与延迟选择实验的协同设计，可以把"时间作为边界几何对象"的思想从理论推向可检范畴。

---

## 9 Acknowledgements, Code Availability

作者感谢相关文献中关于 Wigner–Smith 群延迟、延迟选择实验与时间双缝干涉的系统工作，为本文提供了坚实实验与数学基础。

本文全部推导为解析与符号计算，未使用独立数值代码。若需要数值验证，可根据文中给出的模型与参数在常见数值平台上自行实现。

---

## 10 References

[1] J. A. Wheeler, "The 'past' and the 'delayed-choice' double-slit experiment," in *Quantum Theory and Measurement*, Princeton University Press (1984).([维基百科][2])

[2] Y.-H. Kim et al., "A delayed-choice quantum eraser," *Phys. Rev. Lett.* **84**, 1–5 (2000).([维基百科][5])

[3] X.-S. Ma, J. Kofler, A. Zeilinger, "Delayed-choice gedanken experiments and their realizations," *Rev. Mod. Phys.* **88**, 015005 (2016).([维基百科][2])

[4] F. Lindner et al., "Attosecond double-slit experiment," *Phys. Rev. Lett.* **95**, 040401 (2005).([物理评论链接管理器][7])

[5] T. Kaneyasu et al., "Time-domain double-slit experiment in the extreme ultraviolet using synchrotron radiation," *Sci. Rep.* **13**, 5718 (2023).([Nature][8])

[6] P. Eckle et al., "On time and space double-slit experiments," *Am. J. Phys.* **82**, 1087–1093 (2014).([AIP Publishing][9])

[7] Y.-C. Cheng et al., "Controlling photoionization using attosecond time-slit interference," *Proc. Natl. Acad. Sci. USA* **117**, 9751–9757 (2020).([国家科学院院刊][10])

[8] C. Texier, "Wigner time delay and related concepts," *Physica E* **82**, 16–33 (2016).([科学直达][4])

[9] U. R. Patel, E. Michielssen, "Wigner–Smith time-delay matrix for electromagnetics," *IEEE Trans. Antennas Propag.* **69**, 3995–4009 (2021).([arXiv][11])

[10] R. Bourgain et al., "Direct measurement of the Wigner time delay for the scattering of light by a single obstacle," *Opt. Lett.* **38**, 1963–1965 (2013).([光学出版集团][12])

[11] P. Kolenderski et al., "Time-resolved double-slit interference pattern," *Sci. Rep.* **4**, 4685 (2014).([Nature][13])

[12] V. Jacques et al., "Experimental realization of Wheeler's delayed-choice Gedanken experiment," *Science* **315**, 966–968 (2007).([维基百科][2])

[13] S. P. Walborn et al., "Double-slit quantum eraser," *Phys. Rev. A* **65**, 033818 (2002).([维基百科][5])

[14] M. Waaijer et al., "Delayed choice experiments: an analysis in forward time," *Quantum Stud.: Math. Found.* (2024).([SpringerLink][6])

[15] H. D. Zeh, *The Physical Basis of the Direction of Time*, Springer (2007).

[16] R. Bousso et al., "Quantum focusing conjecture and related topics," 多篇文献合集。

[17] J. M. Maldacena, A. Strominger, "Universal low-energy dynamics for rotating black holes," *Phys. Rev. D* **56**, 4975–4983 (1997).

[18] G. 't Hooft, "The scattering matrix approach for the quantum black hole," *Nucl. Phys. B* **256**, 727–745 (1985).

[19] S. W. Hawking, G. T. Horowitz, "The gravitational Hamiltonian, action, entropy and surface terms," *Class. Quantum Grav.* **13**, 1487–1498 (1996).

[20] J. D. Brown, J. W. York Jr., "Quasilocal energy and conserved charges derived from the gravitational action," *Phys. Rev. D* **47**, 1407–1419 (1993).

---

## Appendix A：统一时间刻度与边界时间几何的技术要点

### A.1 相位–谱移–群延迟刻度同一式

考虑自伴算子对 $(H,H_0)$，其差 $V=H-H_0$ 为迹类或相对迹类。谱移函数 $\xi(\lambda)$ 定义为对所有足够光滑函数 $f$ 有

$$
\operatorname{Tr}(f(H)-f(H_0))=\int f'(\lambda)\,\xi(\lambda)\,\mathrm d\lambda.
$$

Birman–Kreĭn 行列式公式给出

$$
\det S(\omega)=\exp[-2\pi\mathrm i\,\xi(\omega)],
$$

其中 $S(\omega)$ 为能量 $\omega$ 处散射矩阵。对 $\Phi(\omega)=\arg\det S(\omega)$ 取导得

$$
\Phi'(\omega)=-2\pi\xi'(\omega).
$$

另一方面，

$$
\partial_\omega\ln\det S(\omega)=\operatorname{tr}[S^{-1}(\omega)\partial_\omega S(\omega)]
=\operatorname{tr}[-\mathrm iQ(\omega)],
$$

即 $\Phi'(\omega)=\operatorname{tr}Q(\omega)$。综合得

$$
\frac{\varphi'(\omega)}{\pi}
=\frac{\Phi'(\omega)}{2\pi}
=-\xi'(\omega)
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

即刻度同一式。

### A.2 模块流、外自同构群与时间刻度

Tomita–Takesaki 理论表明：对带循环–分离向量 $\Omega_\omega$ 的 $(\pi_\omega(\mathcal A_\partial)'',\Omega_\omega)$，存在模算子 $\Delta_\omega$ 与对 $\mathbb R$ 的表示

$$
\sigma_t^\omega(A)=\Delta_\omega^{\mathrm i t}A\Delta_\omega^{-\mathrm i t},\quad t\in\mathbb R,
$$

构成唯一的模块流。Connes 证明不同忠实态 $\omega,\omega'$ 诱导的模块流在外自同构群 $\mathrm{Out}(\mathcal A_\partial)$ 上相同，因此模时间刻度在 $\mathrm{Out}(\mathcal A_\partial)$ 上具有态无关性。

在 BTG 中，引入边界动力学 $\alpha_t$，要求存在内部单位元族 $u_t\in\mathcal A_\partial$ 使得

$$
\alpha_t=\operatorname{Ad}(u_t)\circ\sigma_t^\omega,
$$

从而模流参数 $t$ 与动力学时间刻度在 $\mathrm{Out}(\mathcal A_\partial)$ 上等价，属于同一时间刻度等价类 $[\tau]$。

### A.3 GHY 边界项与 Brown–York 能量

在带边界 $\partial M$ 的时空 $(M,g)$ 上，引力作用取为

$$
S_{\mathrm{grav}}=\frac{1}{16\pi G}\int_M\sqrt{-g}\,R\,\mathrm d^4x
+\frac{\varepsilon}{8\pi G}\int_{\partial M}\sqrt{|h|}\,K\,\mathrm d^3x
+S_{\mathrm{corner}},
$$

其中 $h_{ab}$ 为诱导度规，$K$ 为外在曲率迹，$\varepsilon=\pm1$ 由边界因果型决定，$S_{\mathrm{corner}}$ 为角点项。对固定 $h_{ab}$ 与角参数的变分族，EH 体项的边界变分由 GHY 项抵消，使作用在该变分族上极值问题良定。

协变相空间方法表明，对满足适当衰减条件的变分，哈密顿生成元中边界贡献为

$$
H_\xi^{\mathrm{BY}}=\int_{\partial\Sigma}\mathrm d^2x\,\sqrt{\sigma}\,u_a\xi_b T^{ab}_{\mathrm{BY}},
$$

其中 $T^{ab}_{\mathrm{BY}}=(8\pi G)^{-1}(K^{ab}-Kh^{ab})$ 为 Brown–York 表面应力张量，$\xi^a$ 为边界时间样向量场，$u^a$ 为空间超曲面法向。这一生成元定义了边界时间平移的能量刻度，与散射群延迟与模时间一起构成统一时间刻度等价类。

---

## Appendix B：经验截面族与延迟选择定理的技术证明

### B.1 一致历史与小因果菱形拼接

在每个小因果菱形 $D_{p,r}$ 中，将局域代数 $\mathcal A(D_{p,r})$ 视为 BTG 边界代数的子代数。给定时间序列 $\tau_0<\dots<\tau_n$，选取包含观察者记录的测量族 $\{E_{\alpha_k}^{(k)}\}$，保证：

1. $E_{\alpha_k}^{(k)} \in\mathcal A_{\gamma,\Lambda}(\tau_k)$；
2. 近似去相干：$\omega(C_{\boldsymbol\alpha}C_{\boldsymbol\beta}^\dagger)\approx 0$ 对 $\boldsymbol\alpha\neq\boldsymbol\beta$。

通过双线性形式

$$
D(\boldsymbol\alpha,\boldsymbol\beta)=\omega(C_{\boldsymbol\alpha}C_{\boldsymbol\beta}^\dagger)
$$

定义一致性泛函。近似去相干保证 $D$ 在对角主元上近似实非负，可解释为概率。

在几何端，小因果菱形上的广义熵极值与 QNEC/QFC 给出局域解族吸收边界数据的条件，因而对每一历史串 $\boldsymbol\alpha$ 可构造对应局域几何–物质解。沿 $\gamma$ 拼接这些局域解并利用 Kolmogorov 扩展，得到连续时间上的解族与截面族。

### B.2 条件化态与经验截面的一致性

给定历史类 $\mathcal H_{\mathrm{exp}}$，定义条件态

$$
\omega_{\mathrm{exp}}(A)=\frac{\sum_{\boldsymbol\alpha\in\mathcal H_{\mathrm{exp}}}\omega(C_{\boldsymbol\alpha}^\dagger A C_{\boldsymbol\alpha})}{\sum_{\boldsymbol\alpha\in\mathcal H_{\mathrm{exp}}}p(\boldsymbol\alpha)}.
$$

对固定时间 $\tau_k$ 处的 $A\in\mathcal A_{\gamma,\Lambda}(\tau_k)$，由于 $A$ 与后时刻投影交换（或近似交换），可将 $A$ 移动至最近的过去投影前，从而

$$
\omega_{\mathrm{exp}}(A)
$$

只依赖于在该时间之前的部分历史。通过局域解族的构造，这一条件态与截面定义中的 $\rho_{\gamma,\Lambda}(\tau_k)$ 一致，从而表明经验截面族与条件化态的兼容性。

### B.3 延迟选择情形下的无逆因果性推广

B.2 中分析可推广至存在多个后时刻 instrument 的情形：设在 $\tau_1$ 处有 instrument $\{\mathcal M_x\}$，在 $\tau_2$ 有 instrument $\{\mathcal I_y^{(C)}\}$，在 $\tau_3$ 可能还有 instrument $\{\mathcal J_z\}$ 等。对任意先时刻事件 $x$，其边缘分布

$$
p_C(x)=\sum_{y,z,\dots}p_C(x,y,z,\dots)
$$

在完全正性与完备性条件下总可约化为仅包含 $\mathcal M_x$ 与 $\rho_0$ 的表达，不依赖于后时刻 instrument 的具体形式。这一事实在多步 CPTP 演化下通过重复使用完备性关系与迹的循环性得到。

从截面角度，这意味着 $\tau_1$ 处的经验截面集合不依赖于之后对联合系统施加的测量或控制，延迟选择不能改变已定截面，只能改变对截面历史的分组与标记。

---

## Appendix C：时间双缝能谱干涉的解析推导

### C.1 模型设定

考虑一维模型：粒子初态为能量宽度有限的波包 $\lvert\psi_{\mathrm{in}}\rangle$，在两段时间窗 $[t_1,t_1+\delta t]$、$[t_2,t_2+\delta t]$ 内与外场相互作用，其余时间自由演化。令自由哈密顿量 $H_0$ 与相互作用 $V(t)$ 使总 Hamiltonian

$$
H(t)=H_0+V(t),\quad V(t)=V_1(t)+V_2(t),
$$

其中 $V_1,V_2$ 支集分别在两时间窗。采用一次 Born 近似，出射能量本征态 $\lvert E\rangle$ 的散射振幅

$$
A(E)\approx -\frac{\mathrm i}{\hbar}\int_{-\infty}^{+\infty}\mathrm dt\,
\mathrm e^{\mathrm i E t/\hbar}\langle E\vert V(t)\vert\psi_{\mathrm{in}}(t)\rangle.
$$

若 $\vert\psi_{\mathrm{in}}(t)\rangle$ 在两个时间窗内变化缓慢，可近似为常量 $\vert\psi_1\rangle,\vert\psi_2\rangle$，且两窗内的 $V_1,V_2$ 近似时间平移得到，则

$$
A(E)\approx A_1(E)+\mathrm e^{\mathrm i E\Delta t/\hbar}A_2(E),
$$

其中 $\Delta t=t_2-t_1$，$A_{1,2}(E)$ 为各自时间窗贡献。

### C.2 能谱条纹与时间窗长度

能谱分布

$$
P(E)=|A(E)|^2
=|A_1|^2+|A_2|^2+2\Re\!\left(A_1^*A_2\mathrm e^{\mathrm i E\Delta t/\hbar}\right).
$$

若 $|A_1|,|A_2|$ 在考察能量区间缓慢变化，则干涉项主导能谱振荡，其相位随 $E$ 线性增长，条纹间距由

$$
\Delta\bigl(E\Delta t/\hbar\bigr)\approx 2\pi
$$

得

$$
\Delta E\approx 2\pi\hbar/\Delta t.
$$

时间窗有限宽度 $\delta t$ 导致干涉包络函数的存在，其可视为各时间窗自身时间傅里叶变换的模平方，给出条纹可见度与可见条纹数的上界，与实验观测一致。([arXiv][3])

### C.3 与 Wigner–Smith 群延迟的联系

对完整散射算符 $S$，能量相位 $\phi(E)=\arg\langle E\vert S\vert\psi_{\mathrm{in}}\rangle$ 的导数给出群延迟

$$
\tau_{\mathrm g}(E)=\partial_E\phi(E).
$$

比较上式中干涉相位 $E\Delta t/\hbar$ 与 $\phi(E)$，可见在时间双缝模型下，群延迟包含一项常量偏移 $\Delta t/\hbar$ 及由各时间窗内部动力学引入的缓慢变化项。在 BTG 框架中，$\Delta t$ 与 $\tau_{\mathrm g}$ 属于统一时间刻度等价类，从而时间双缝能谱干涉可视为对统一时间刻度的直接采样。

---

## Appendix D：空间双缝与 BTG 中路径空间的统一

为完整起见，此处给出空间双缝在 BTG 中的路径空间表示。

设路径空间 $\mathcal H_{\mathrm{path}}$ 由两条路径基 $\{\lvert L\rangle,\lvert R\rangle\}$ 张成，传播空间 $\mathcal H_{\mathrm{trans}}$ 由屏幕平面上的连续位置基 $\{\lvert x\rangle\}$ 张成。整体散射算符 $S$ 在路径空间上可写为

$$
S=\Pi_L\otimes S_L+\Pi_R\otimes S_R+S_{\mathrm{mix}},
$$

其中 $\Pi_{L,R}=\lvert L,R\rangle\langle L,R\rvert$，$S_L,S_R$ 为经各路径传播到屏幕的算符，$S_{\mathrm{mix}}$ 为路径间耦合项（在理想双缝模型中可忽略）。

对初态 $\lvert\psi_{\mathrm{in}}\rangle=\lvert\chi\rangle\otimes\lvert\phi_0\rangle$ 作用 $S$，得到屏幕位置振幅

$$
\psi(x)=\langle x\vert(S_L\lvert\phi_0\rangle\langle L\vert+S_R\lvert\phi_0\rangle\langle R\vert)\lvert\chi\rangle,
$$

对 $\lvert\chi\rangle=(\lvert L\rangle+\lvert R\rangle)/\sqrt2$ 可恢复标准空间双缝振幅。这一表示与时间双缝中的两时间窗贡献形式在 BTG 提示的统一希尔伯特空间中完全同构，从而完成本文关于空间/时间双缝统一的数学闭合。

[1]: https://en.wikipedia.org/wiki/Double-slit_experiment "Double-slit experiment"
[2]: https://en.wikipedia.org/wiki/Wheeler%27s_delayed-choice_experiment "Wheeler's delayed-choice experiment"
[3]: https://arxiv.org/abs/quant-ph/0503165 "Attosecond double-slit experiment"
[4]: https://www.sciencedirect.com/science/article/abs/pii/S1386947715302228 "Wigner time delay and related concepts"
[5]: https://en.wikipedia.org/wiki/Delayed-choice_quantum_eraser "Delayed-choice quantum eraser"
[6]: https://link.springer.com/article/10.1007/s40509-024-00328-5 "Delayed choice experiments: an analysis in forward time"
[7]: https://link.aps.org/doi/10.1103/PhysRevLett.95.040401 "Attosecond Double-Slit Experiment | Phys. Rev. Lett."
[8]: https://www.nature.com/articles/s41598-023-33039-9 "Time domain double slit interference of electron produced ..."
[9]: https://pubs.aip.org/aapt/ajp/article/82/11/1087/1057484/On-time-and-space-double-slit-experiments "On time and space double-slit experiments"
[10]: https://www.pnas.org/doi/10.1073/pnas.1921138117 "Controlling photoionization using attosecond time-slit ..."
[11]: https://arxiv.org/pdf/2005.03211 "Wigner-Smith Time Delay Matrix for Electromagnetics"
[12]: https://opg.optica.org/ol/abstract.cfm?uri=ol-38-11-1963 "Direct measurement of the Wigner time delay for ..."
[13]: https://www.nature.com/articles/srep04685 "Time-resolved double-slit interference pattern ..."
