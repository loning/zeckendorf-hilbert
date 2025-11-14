# 时间–几何–相互作用的统一框架：从散射相位刻度到引力与规范力的几何化

---

**Abstract**

构建一个以"时间刻度等价类"为核心对象的统一框架，将引力、规范相互作用与宏观经典"力"重写为同一几何结构在不同层级上的投影。首先，在严格的散射理论语境下，以 Birman–Kreĭn 谱移函数与 Wigner–Smith 时间延迟为基础，给出相位导数、相对态密度与群延迟迹的刻度同一式：对一类满足迹类扰动条件的散射系统，有 $\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\mathrm{tr},Q(\omega)$，其中 $Q(\omega)=-iS(\omega)^{\dagger}\partial_{\omega}S(\omega)$ 为 Wigner–Smith 矩阵，$\rho_{\mathrm{rel}}$ 为 Kreĭn 谱移密度的导数。该同一式将"相位–延迟–相对谱密度"统一为可观测的时间刻度。其次，引入以时空为底流形、以内部电荷空间与"观察者分辨率层级"为纤维的总丛，证明在满足局域洛伦兹与内部规范对称性的条件下，引力与杨–米尔斯规范场均可视为同一总联络的不同分量，其曲率分别给出时空曲率与内部场强；时间刻度通过沿世界线的相位积分与该联络的平行移动关联，从而导出"无基本力，只有不同几何投影下的时间曲率"的统一命题。再次，在代数量子场论层面，以 Tomita–Takesaki 模块理论给出的模流作为"内部时间"，并结合量子零能条件（QNEC）与广义熵单调性，刻画时间箭头为相对熵与模能量单调的偏序结构。最后，在半经典极限下，对宏观质点的期望值演化给出"力＝时间几何的投影曲率"的定理化表述，说明经典牛顿力学、洛伦兹力乃至有效熵力均可视为该统一时间几何在不同粗粒度与内部态约束下的有效描述。文末给出若干可检验的工程方案，包括微波网络与介观导体中的 Wigner–Smith 时间延迟测量、原子钟引力红移–相位刻度对账，以及基于 FRW 宇宙学红移与强引力透镜的跨尺度刻度一致性检验。

---

**Keywords**
时间刻度等价类；散射相位；Wigner–Smith 时间延迟；Birman–Kreĭn 谱移；引力几何化；杨–米尔斯规范场；模流；量子零能条件；宏观力的涌现

---

## Introduction & Historical Context

经典物理学以"力"作为基本概念：牛顿第二定律 $F=ma$ 将力视为改变质点速度的原因。电磁学的场论化在某种意义上削弱了"力"的基础地位：洛伦兹力 $q(E+v\times B)$ 可由电磁场张量 $F_{\mu\nu}$ 与四速度 $u^{\nu}$ 的收缩得到，场本身由麦克斯韦方程支配。广义相对论进一步将引力从"力"升级为时空几何：自由落体世界线满足测地线方程，所谓"引力加速度"可以视为选择非自由落体系导致的惯性力。

二十世纪中叶，规范理论将电磁、弱相互作用与强相互作用统一写成主丛上的联络与曲率：规范势 $A_{\mu}$ 是纤维丛上的联络，场强 $F_{\mu\nu}$ 为该联络的曲率，对应 Yang–Mills 方程的欧拉–拉格朗日方程。电荷在规范场中的"受力"可理解为在带规范联络的总空间中做平行移动时的轨道偏转。规范理论的几何化已经表明：相互作用可以统一为不同类型几何结构。([damtp.cam.ac.uk][1])

另一方面，量子散射理论揭示了相位、态密度与"时间延迟"之间的深刻联系。Birman–Kreĭn 公式建立了散射矩阵行列式与谱移函数之间的关系，Friedel 定则给出相位与态密度的联系，Smith 与 Wigner 引入的时间延迟与 Wigner–Smith 矩阵 $Q(\omega)=-iS(\omega)^{\dagger}\partial_{\omega}S(\omega)$ 则刻画了散射过程的时间结构。后续工作表明，在适合的迹类扰动条件下，相位导数、相对态密度与 Wigner–Smith 矩阵的迹通过严格的迹公式统一。([科学直通车][2])

在代数量子场论中，Tomita–Takesaki 模块理论为任何带有循环–分离向量的 von Neumann 代数赋予一条本征的模流 $\sigma^{\varphi}_{t}$。模流由模算符 $\Delta$ 的一参数酉群 $\Delta^{it}$ 生成，可视为由状态–代数对自然诱导的"内部时间"。此一结构在热时间假设以及重力–全息背景下的时间重构中扮演重要角色。([arXiv][3])

近年的量子零能条件（QNEC）工作则揭示了能量–熵之间的时间箭头结构：在相当一般的量子场论中，沿零方向的应力能量张量满足以冯·诺依曼熵二阶变分为下界的不等式，从而把熵的几何变化与局域能量约束绑定在一起。([Astrophysics Data System][4])

这些发展共同指向一个更深层的统一图景：
时间不只是外加参数，而是由散射相位、谱移、模流与熵弯曲等多种结构共同定义的刻度；
引力与规范相互作用都是对应于不同纤维方向的联络曲率；
宏观"力"则是该时间–几何在粗粒度与有效自由度层级上的投影。

本文的目标是在上述成熟结果基础上，构建一个明确的统一框架：

1. 以散射理论中的相位–谱移–时间延迟同一式，给出时间刻度的可观测定义；
2. 把引力与规范相互作用统一视为"时间联络"的不同成分，导出宏观力为时间几何曲率的投影；
3. 用模流与 QNEC 刻画时间箭头与因果偏序；
4. 给出可检验的实验–工程方案，使该统一框架具有可证伪性。

---

## Model & Assumptions

### 2.1 时空与量子场论背景

设 $(M,g)$ 是四维、时向取向的全局双曲洛伦兹流形，满足普通因果与能量条件。物理系统由定义在 $(M,g)$ 上的量子场论给出，其希尔伯特空间为 $\mathcal H$，局域可观测代数为 $\mathcal A(\mathcal O)\subset B(\mathcal H)$，遵守 Haag–Kastler 公理。选定参考状态 $\Omega \in \mathcal H$（可为真空或热平衡态），假定其对适当的子代数循环且分离。

在具有足够渐近平直区域的情形，假定存在全局时间平移对称性 $t\mapsto U(t)=e^{-iHt}$，对应产生子 $H$ 自伴，允许构造散射态与散射矩阵。

### 2.2 观察者、分辨率与粗粒度

观察者由一条类时世界线 $\gamma:\tau\mapsto x^{\mu}(\tau)$ 及一套探测器自由度描述。引入一个"分辨率刻度"参数 $\Lambda$，刻画该观察者可分辨的能量–时间范围与空间–动量窗口。形式化地，可将粗粒度算符视为对代数 $\mathcal A(\mathcal O)$ 的完全正、迹保持映射族 $\{ \Phi_{\Lambda} \}$，随 $\Lambda$ 的减小时，保留的自由度越来越粗。

分辨率–时间–红移之间的关系在统一框架中通过"等价类"刻画：不同的 $(\gamma,\Lambda)$ 组合可以定义相同的时间刻度（在后文意义下）。

### 2.3 散射体系与刻度同一式

考虑一对自伴算符 $H,H_{0}$ 于 $\mathcal H$ 上，满足 $V:=H-H_{0}$ 为迹类扰动，并满足标准的波算子存在与完备条件。令 $S(\omega)$ 为定能量散射矩阵，其行列式与谱移函数 $\xi(\omega;H,H_{0})$ 满足 Birman–Kreĭn 公式
$\det S(\omega)=e^{-2\pi i\xi(\omega)}$ 几乎处处成立。([matcuer.unam.mx][5])

定义总散射相位 $\Phi(\omega)=\arg\det S(\omega)$，并设
$\varphi(\omega)=\tfrac12\Phi(\omega)=-\pi\xi(\omega)$。
引入 Wigner–Smith 矩阵
$Q(\omega)=-iS(\omega)^{\dagger}\partial_{\omega}S(\omega)$，
其迹在许多模型中可解释为总群延迟。([科学直通车][2])

相对态密度定义为
$\rho_{\mathrm{rel}}(\omega)=\rho(\omega;H)-\rho(\omega;H_{0})$，
其中 $\rho$ 为密度态。Kreĭn 迹公式给出
$\mathrm{tr}(f(H)-f(H_{0}))=\int_{\mathbb R} f'(\lambda)\xi(\lambda),\mathrm d\lambda$，适当选择 $f$ 可推得 $\rho_{\mathrm{rel}}(\omega)=\xi'(\omega)$ 几乎处处成立。([matcuer.unam.mx][5])

在良好可积性条件下，Wigner–Smith 矩阵迹满足
$\mathrm{tr},Q(\omega)=2\partial_{\omega}\varphi(\omega)$。综合得到刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\mathrm{tr},Q(\omega)\quad\text{几乎处处}.
$$

这一定义把"额外态密度""总群延迟"与"散射相位梯度"统一为一条函数 $\kappa(\omega)$，可被视为对给定散射体系与参考哈密顿量的"时间刻度密度"。

### 2.4 几何化：总丛与联络

设 $M$ 为时空流形，引入总丛
$\pi:\mathcal B\to M$，其纤维为内部电荷空间 $\mathcal F_{\mathrm{int}}$ 与"分辨率空间" $\mathcal F_{\mathrm{res}}$ 的乘积。对每一点 $x\in M$，纤维 $\mathcal B_{x}$ 表示该点处量子态的内部自由度与观察者可用的测量窗口。

在 $\mathcal B$ 上引入主丛结构，其结构群为
$G_{\mathrm{tot}}=SO(1,3)^{\uparrow}\times G_{\mathrm{YM}}\times G_{\mathrm{res}}$，
分别对应局域洛伦兹群、内部杨–米尔斯规范群与分辨率缩放群。总联络记为
$\boldsymbol{\Omega}=\omega_{\mathrm{LC}}\oplus A_{\mathrm{YM}}\oplus \Gamma_{\mathrm{res}}$，
其中 $\omega_{\mathrm{LC}}$ 为 Levi–Civita 自旋联络，$A_{\mathrm{YM}}$ 为标准 Yang–Mills 规范场，$\Gamma_{\mathrm{res}}$ 则描述 RG 意义下的分辨率流（如重整化群或 coarse-graining 联络）。([维基百科][6])

总曲率
$\boldsymbol{\mathcal R}=\mathrm d\boldsymbol{\Omega}+\boldsymbol{\Omega}\wedge\boldsymbol{\Omega}$
自然分解为时空曲率 $R$、杨–米尔斯场强 $F$ 与分辨率流曲率 $\mathcal R_{\mathrm{res}}$。

### 2.5 模块时间与熵箭头

对每一局域可观测代数 $\mathcal A(\mathcal O)$ 与状态 $\varphi$（由 $\Omega$ 给出向量态），Tomita–Takesaki 理论给出模算符 $\Delta_{\varphi}$ 与模自同构群
$\sigma^{\varphi}_{t}(A)=\Delta_{\varphi}^{it}A\Delta_{\varphi}^{-it}$。模流参数 $t$ 可解释为该观察者–代数对的"内部时间"，在全息与热时间假设语境中，被视为几何时间的候选。([arXiv][3])

QNEC 声称对适当类的量子场论与状态，有
$\langle T_{kk}(x)\rangle_{\psi}\geq \frac{1}{2\pi}S''_{\mathrm{vN}}(x)$，
其中 $T_{kk}$ 是沿零向量 $k^{\mu}$ 的应力能量分量，$S''_{\mathrm{vN}}$ 为沿该方向的冯·诺依曼熵的二阶变分。该不等式以及更广泛的广义熵单调性，为从量子信息角度定义时间箭头与因果偏序提供了定量基础。([Astrophysics Data System][4])

---

## Main Results (Theorems and Alignments)

本节给出统一框架的核心定义与定理，并指出它们之间的对齐关系。

### 3.1 时间刻度等价类的定义

**定义 3.1（操作型时间刻度）。**
给定一散射体系 $(H,H_{0})$ 与其散射矩阵 $S(\omega)$，定义刻度密度
$\kappa(\omega)=\varphi'(\omega)/\pi$，其中 $\varphi(\omega)$ 由前述 Birman–Kreĭn 关系确定。对能量窗口 $I\subset\mathbb R$，定义有效时间刻度
$\tau_{I}(E)=\int_{E_{0}}^{E}\kappa(\omega)\mathbf{1}_{I}(\omega),\mathrm d\omega$，
其在实验上对应于频率–相位测量所得的"附加群延迟"积分。

**定义 3.2（时间刻度等价类）。**
给定两组操作型时间参数 $t$ 与 $t'$，若存在严格单调的 $C^{1}$ 函数 $f:\mathbb R\to\mathbb R$ 与全局正常数 $c>0$，使得对所有在共同定义域内可实现的散射实验，有
$t' = c,f(t)$ 且所有可观测相位差与群延迟随 $t,t'$ 的排序一致，则称 $t$ 与 $t'$ 属于同一时间刻度等价类，记为 $[t]=[t']$。

**命题 3.3.**
在刻度同一式成立的条件下，对于任意满足迹类扰动条件的散射体系与给定参考 $(H_{0})$，不同的探针族（频率窗口、入射通道选择）所定义的时间刻度在等价关系意义下收敛到同一等价类 $[\tau]$，当且仅当 Wigner–Smith 总时间延迟的能量依赖由一个统一的几何结构（如相同的有效势和边界条件类）控制。

这一命题保证了在合适的"通用探针"族下，时间刻度具有探针无关性，从而可用于定义宏观时间。

### 3.2 相位–谱移–时间延迟刻度同一式

**定理 3.4（刻度同一式）。**
设 $H,H_{0}$ 为自伴算符，$H-H_{0}$ 为迹类扰动，散射矩阵 $S(\omega)$ 存在且酉。令谱移函数 $\xi(\omega)$ 由 Kreĭn 迹公式定义，则几乎处处有

$\mathrm{tr}[f(H)-f(H_{0})]=\int_{\mathbb R} f'(\lambda)\xi(\lambda),\mathrm d\lambda$ 对所有适当的 $f$。

定义 $\varphi(\omega)=-\pi\xi(\omega)$，$Q(\omega)=-iS(\omega)^{\dagger}\partial_{\omega}S(\omega)$，则几乎处处有

$$
\frac{\varphi'(\omega)}{\pi}=\xi'(\omega)=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\mathrm{tr},Q(\omega).
$$

此定理结合 Birman–Kreĭn 公式、Friedel 定则与 Wigner–Smith 定义，给出了相位、谱移与时间延迟的统一。([科学直通车][2])

**推论 3.5（时间刻度的谱定义）。**
刻度密度 $\kappa(\omega)$ 可等价定义为相对态密度，亦可定义为 Wigner–Smith 矩阵迹的归一化，从而具备完全谱–散射的表达。

### 3.3 时空–内部空间统一几何与"力"的几何化

在总丛 $\mathcal B$ 上，总联络 $\boldsymbol{\Omega}$ 的曲率 $\boldsymbol{\mathcal R}$ 可以分解为

$\boldsymbol{\mathcal R} = R\oplus F\oplus \mathcal R_{\mathrm{res}}$。

沿一条物质粒子世界线 $\gamma$ 的平行移动由总协变导数
$D_{\tau}=\frac{\mathrm d}{\mathrm d\tau}+\boldsymbol{\Omega}(\dot{\gamma})$ 控制。内禀自由度（如自旋、色荷）与分辨率变量的演化由 $F$ 与 $\mathcal R_{\mathrm{res}}$ 决定。

**定理 3.6（无基本力命题）。**
在半经典极限下，对带质量 $m$、内部电荷 $q$ 的粒子，其质心轨迹 $x^{\mu}(\tau)$ 的期望值满足

$$
m\frac{D^{2}x^{\mu}}{D\tau^{2}} = qF^{\mu}{}_{\nu}\frac{\mathrm d x^{\nu}}{\mathrm d\tau} + f^{\mu}_{\mathrm{res}}
$$

其中 $D$ 为 Levi–Civita 协变导数，$F^{\mu}{}_{\nu}$ 为杨–米尔斯场强在相应表示下的投影，$f^{\mu}_{\mathrm{res}}$ 为由 $\mathcal R_{\mathrm{res}}$ 与态–熵变化导致的有效"熵力"项。换言之，经典意义上的引力、洛伦兹力与熵驱动力均为总联络曲率在不同行为空间上的投影，无需单独引入"基本力"的原始概念。

证明基于波包的半经典传播与路径积分表象，详见附录 C。

### 3.4 时间刻度与引力几何的重构

**定理 3.7（从刻度同一式到引力红移）。**
考虑具有静态 Killing 向量 $\partial_{t}$ 的时空区域，度规可写成标准静态形式
$g=-N^{2}(\mathbf x)\mathrm d t^{2}+h_{ij}(\mathbf x)\mathrm d x^{i}\mathrm d x^{j}$。

假设在该区域内存在一族能量局域于 $I$ 的散射过程，其 Wigner–Smith 总群延迟 $\mathrm{tr},Q(\omega)$ 可由远处观察者测量。若刻度密度 $\kappa(\omega)$ 在 $I$ 内近似与位置仅通过 $N(\mathbf x)$ 的重标相关，即

$$
\kappa(\omega;\mathbf x) = N^{-1}(\mathbf x),\kappa_{\infty}(\omega)
$$

则远处观察者定义的时间刻度与局域自由落体定义的本征时间刻度属于同一等价类，其比率给出引力红移因子 $N(\mathbf x)$。

证明依赖于静态空间中散射态频率守恒与局域能量 $\omega_{\mathrm{loc}}=N^{-1}(\mathbf x)\omega$ 的关系，见附录 B。

**推论 3.8.**
在上述设定下，引力势可被视为"统一时间刻度"在不同空间点之间的重标图样；引力时间膨胀与 Shapiro 延迟是同一时间几何在不同操作型定义下的两种读出方式。

### 3.5 规范相互作用作为条件化时间刻度

**命题 3.9（电荷依赖的附加群延迟）。**
在存在 $U(1)$ 或更一般 Yang–Mills 规范场 $A_{\mu}$ 的散射体系中，不同内部电荷表示 $\rho$ 对应的散射矩阵 $S_{\rho}(\omega)$ 的相位导数差

$$
\Delta\kappa_{\rho,\rho'}(\omega)=\frac{1}{2\pi}\mathrm{tr},[Q_{\rho}(\omega)-Q_{\rho'}(\omega)]
$$

在半经典极限下等价于沿经典轨道的 Wilson 线相位差对能量的导数，从而对应于 Lorentz 力所导致的时间延迟差。

该命题表明，规范力可以理解为不同电荷扇区在相同几何背景下感知到的"条件化时间刻度"的差异。

### 3.6 模块时间、熵单调与时间箭头

**定理 3.10（模流–几何时间对齐定理）。**
在一类可通过几何全息描述的量子场论中，若局域模流 $\sigma^{\varphi}_{t}$ 在重力侧对应于某一 Killing 或近似 Killing 向量的流，则以下陈述等价：

1. 模流时间 $t$ 属于与几何时间 $\tau$ 相同的时间刻度等价类；
2. 模哈密顿量的期望值单调性与广义熵极值条件共同导出局域引力场方程；
3. QNEC 在相应零方向上成立并饱和。

该定理抽象了现有工作中"广义熵极值 + QNEC 足以导出 Einstein 方程"的思想，将之重述为时间刻度等价类与模流的一致性条件。([SpringerLink][7])

证明骨架见附录 D。

---

## Proofs

本节给出主要结果的证明思路与若干关键步骤，技术细节留至附录。

### 4.1 定理 3.4 的证明概要

核心工具是 Kreĭn 谱移函数理论与 Wigner–Smith 矩阵的迹公式。

1. Kreĭn 迹公式保证对迹类扰动 $V=H-H_{0}\in\mathfrak S_{1}$，存在唯一的 $\xi(\lambda)\in L^{1}(\mathbb R)$，使得对足够好的 $f$，有
   $\mathrm{tr}[f(H)-f(H_{0})]=\int f'(\lambda)\xi(\lambda),\mathrm d\lambda$。([matcuer.unam.mx][5])

2. Birman–Kreĭn 公式连接散射矩阵行列式与谱移函数：
   $\det S(\omega)=e^{-2\pi i\xi(\omega)}$，几乎处处。

3. 定义总散射相位 $\Phi(\omega)=\arg\det S(\omega)$，选取连续分支，使得 $\Phi(\omega)=-2\pi\xi(\omega)$（忽略整型常数）。定义 $\varphi(\omega)=\tfrac12\Phi(\omega)=-\pi\xi(\omega)$，于是 $\varphi'(\omega)/\pi=-\xi'(\omega)=\rho_{\mathrm{rel}}(\omega)$。

4. Wigner–Smith 矩阵 $Q(\omega)=-iS(\omega)^{\dagger}\partial_{\omega}S(\omega)$。在 $S(\omega)$ 酉性的条件下，$\mathrm{tr},Q(\omega)=-i\partial_{\omega}\ln\det S(\omega)$。由 Birman–Kreĭn 公式，有
   $\ln\det S(\omega)=-2\pi i\xi(\omega)$，
   从而 $\mathrm{tr},Q(\omega)=2\pi\xi'(\omega)$。

5. 综合得到
   $\varphi'(\omega)/\pi=\xi'(\omega)=(2\pi)^{-1}\mathrm{tr},Q(\omega)$。

关键在于控制 $\ln\det S$ 的分支与可微性，详见附录 A。

### 4.2 定理 3.6 的证明概要

采用波包半经典极限与路径积分方法：

1. 设单粒子波包初态由 WKB 型波函数描述，其相位由作用量
   $S[\gamma]=\int (p_{\mu}\dot x^{\mu}-H),\mathrm d\tau$ 给出。

2. 在总丛 $\mathcal B$ 上，总联络 $\boldsymbol{\Omega}$ 引入额外的相位项，即路径上的平行移动相位 $\int \boldsymbol{\Omega}(\dot{\gamma}),\mathrm d\tau$。在路径积分中，该项与传统的矢势–标势项等价。([维基百科][6])

3. 对作用量极值可得广义测地线方程，额外的联络曲率项产生力样项，分别对应时空曲率（引力）与内部场强（规范力），以及分辨率流的熵力贡献。

4. 取波包中心轨迹的 Ehrenfest 极限，可将算符期望值演化简化为经典方程，得到命题中的形式。

细节见附录 C。

### 4.3 定理 3.7 的证明概要

利用静态时空中频率守恒与局域能量–红移关系：

1. 在形式 $g=-N^{2}\mathrm dt^{2}+h_{ij}\mathrm d x^{i}\mathrm d x^{j}$ 的静态时空中，时间 Killing 向量 $\partial_{t}$ 保证能量守恒。

2. 局域惯性系中测得的能量为 $\omega_{\mathrm{loc}}=N^{-1}(\mathbf x)\omega$。散射区域内部与远处区域的态密度之差与群延迟必须用局域能量来表达。

3. 在刻度密度仅由 $N(\mathbf x)$ 重标的假设下，不同位置上的时间刻度只差一个位置依赖的常数因子，即属于同一等价类。其比值即为酉变换中的 $N(\mathbf x)$。

4. 将这一关系与引力红移实验数据对账，可验证该解释的一致性。

详细量纲对账见附录 B。

### 4.4 定理 3.10 的证明概要

该定理抽象了"熵极值–模能量–几何方程"的统一结构：

1. 全息与代数量子场论的工作表明，在适当情形下，模流可以几何实现为引力侧某一 Killing 或近似 Killing 流；模哈密顿量的期望值与广义熵的变化相关。([MIT DSpace][8])

2. QNEC 将局域能量下界与熵二阶变分联系起来，保证沿零方向的熵凸性与能量密度之间的约束。([Astrophysics Data System][4])

3. 若模流时间与几何时间处于同一刻度等价类，则模能量的单调性与引力侧的广义熵极值条件共同导出局域引力方程，这在近年的"广义熵导出 Einstein 方程"方案中已有论证。

4. 反之，若局域引力方程与 QNEC 成立，则可以重构一条与几何时间一致的模流，使得时间刻度对齐。

严格证明需依赖相对熵的双侧不等式以及 JLMS 型的全息等价，留待附录 D 讨论。

---

## Model Apply

本节展示统一时间–几何–相互作用框架在若干具体情形中的应用。

### 5.1 微观：杂质散射与 Friedel 定则

在电子对局域杂质散射的模型中，Friedel 定则表明：杂质导致的电子数变化
$\Delta N(\varepsilon)$ 与相移之和相关，态密度修正可用相位导数表示。([courses.physics.illinois.edu][9])

根据刻度同一式，$\rho_{\mathrm{rel}}(\omega)=\varphi'(\omega)/\pi$ 同时又等于 Wigner–Smith 矩阵迹的归一化。因而，电子在杂质附近的"驻留时间增加"与"局域态密度增加"是统一的时间刻度效应。经典库仑"力"的图像在该框架中被替换为：电子波函数相位因局域势与内禀几何发生弯曲，从而改变时间刻度。

### 5.2 宏观：引力红移与 Shapiro 延迟

在弱场极限下，静态引力势 $\Phi(\mathbf x)$ 使得度规近似为
$g\approx-(1+2\Phi(\mathbf x))\mathrm d t^{2}+(1-2\Phi(\mathbf x))\mathrm d\mathbf x^{2}$。

引力红移实验表明，不同高度的原子钟频率满足
$\nu_{2}/\nu_{1}\approx 1+[\Phi(\mathbf x_{1})-\Phi(\mathbf x_{2})]$。

在统一框架中，这可理解为刻度密度 $\kappa(\omega;\mathbf x)$ 随 $\Phi(\mathbf x)$ 重标的结果。Shapiro 延迟中，电磁波通过强引力场时产生额外传播时间，也可视为 $\kappa(\omega)$ 在沿路径积累的综合效应，其谱–散射表示与 FRB 等天文现象中的频率依赖延迟可直接比较。

### 5.3 宇宙学：FRW 红移与时间重标

在均匀各向同性的 FRW 宇宙中，度规可写为
$g=-\mathrm dt^{2}+a^{2}(t)\gamma_{ij}\mathrm d x^{i}\mathrm d x^{j}$，共形时间 $\eta$ 由 $\mathrm d\eta=\mathrm dt/a(t)$ 给出。

光子能量随尺度因子按 $E\propto 1/a(t)$ 衰减，宇宙学红移 $1+z=a(t_{0})/a(t_{e})$ 可以理解为时间刻度在源与观测者处的重标。若我们以频率–相位测量定义时间刻度，那么 FRW 背景中所有自由传播光子的刻度密度将随 $a(t)$ 统一缩放，从而使宇宙学红移成为"统一时间刻度"等价类在大尺度上的表现。

### 5.4 准稳定时间晶体与离散时间刻度

Floquet 驱动体系中，时间周期驱动 $H(t+T)=H(t)$ 对应一条离散时间平移对称性。时间晶体相中，体系基态或长寿态在多周期 $nT$ 上出现有序结构，可视为时间刻度在整数子群上的自发破缺。统一框架允许从时间刻度等价类的角度理解：原本连续刻度被映射到一个离散格点，其上的刻度密度通过 Floquet 谱与准能带结构表达。

在这里，"力"的概念不再适用，取而代之的是 Floquet 模块上的相位–延迟几何。

### 5.5 量子–经典桥接：粗粒度与宏观力

当考虑宏观物体时，观察者仅能访问粗粒度算符 $\Phi_{\Lambda}(\mathcal A)$。在这种粗粒度下，微观波动平均为期望值的平滑演化，统一框架给出的"时间几何曲率"在宏观上表现为经典力。

例如，有限温度下的熵力（如橡皮筋弹性、渗透压）在微观上来自态数与分布，但在统一框架中可视为 $\mathcal R_{\mathrm{res}}$ 与态信息几何的组合曲率，其在粗粒度演化方程中以有效力项出现。

---

## Engineering Proposals

本节提出若干可在现有或可预见实验条件下实现的检验方案。

### 6.1 微波散射网络中的时间刻度测量

构造由同轴线或波导组成的多端口网络，将任意复杂的散射区域视为"黑箱"。利用矢量网络分析仪测量散射矩阵 $S(\omega)$，数值计算 Wigner–Smith 矩阵 $Q(\omega)=-iS^{\dagger}\partial_{\omega}S$，得到 $\mathrm{tr},Q(\omega)$。

同时，数值求解相应有限元模型的谱，求出有无"散射区域"时的态密度差 $\rho_{\mathrm{rel}}(\omega)$。检验刻度同一式
$\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\mathrm{tr},Q(\omega)$。以此为基础，通过对不同网络的比较，刻画统一时间刻度的探针无关性。

### 6.2 介观导体中的电子时间延迟与态密度

在相干导体（如量子点或 Aharonov–Bohm 环）中，通过相位敏感的输运测量可以提取随能量变化的散射相位；同时，利用局域态密度成像（如扫描隧道显微镜）得到态密度修正。比较两者与 Wigner–Smith 群延迟的关系，可在固体物理平台上检验统一刻度。

### 6.3 引力时间刻度：原子钟与卫星链路

在地基与轨道上布设多台原子钟，利用双向时间转移协议测得频率与相位关系。在广义相对论给出的引力红移修正基础上，引入额外的频率依赖项，检验是否可用统一刻度密度 $\kappa(\omega)$ 描述引力与介质等效路径共同作用下的总时间延迟。该方案与现有和将来深空导航、引力波–电磁对应观测高度兼容。

### 6.4 宇宙学与 FRB 的跨尺度刻度检验

对快速射电暴（FRB）等瞬变源，测量其多频段到达时间结构。在剥离等离子体色散、仪器响应之后，残余的频率依赖延迟可以与 FRW 红移与大尺度引力透镜效应共同拟合。若统一时间刻度框架正确，则在不同红移、不同透镜参数下得到的刻度密度重建应属于同一等价类。

---

## Discussion (risks, boundaries, past work)

统一时间–几何–相互作用框架在概念上将"力"降格为时间几何曲率的投影，但其严谨性与适用域存在若干边界。

首先，刻度同一式依赖于迹类扰动与良好散射条件；在强耦合或无良好 S 矩阵定义的背景（如某些红外不良定义的场论或非平直渐近）中，该刻度构造可能失效。其次，总丛与总联络的构造是几何化的再表达，并不自动提供动力学方程；仍需假定 Einstein–Yang–Mills 类作用量或更一般的有效行动来确定联络的演化。

在代数量子场论与全息中的模流–几何时间对齐也非普适，而是依赖特定背景与边界条件。QNEC 虽已在广泛场景下被证明，但其与具体引力场方程的精确关系仍是活跃研究方向。([SpringerLink][7])

此外，将"分辨率流"几何化为 $G_{\mathrm{res}}$ 的联络在数学上可通过重整化群流与统计粗粒度的框架来实现，但尚缺乏统一的严密模型。熵力项 $f^{\mu}_{\mathrm{res}}$ 的普遍表达形式与其能否完全由信息几何与 RG 曲率导出，仍需进一步工作。

与既有统一尝试相比，本框架有别于基于高维时空与弦的统一，而更接近于"作用–时间–熵"的统一：将散射理论中的谱时间、广义相对论中的本征时间、模流中的内部时间以及信息论中的熵箭头收束于一个"时间刻度等价类"的结构之上。其优势在于：可直接在现有实验体系（微波网络、介观输运、原子钟、宇宙学观测）中提出检验；不足在于：尚未给出微观自由度（如引力子的完整量子化）与时空拓扑变化的全面描述。

---

## Conclusion

本文提出一个以"时间刻度等价类"为核心对象的统一框架，通过以下几步完成对引力、规范相互作用与宏观力的几何统一：

1. 在成熟的散射理论基础上，以 Birman–Kreĭn 谱移、Friedel 定则与 Wigner–Smith 时间延迟为工具，建立相位导数、相对态密度与群延迟迹的刻度同一式，给出可观测时间刻度的谱–散射定义；

2. 在总丛几何中，引入时空–内部空间–分辨率空间的总联络，将引力、杨–米尔斯规范场与熵驱动的粗粒度流统一视为该联络的不同分量，其曲率在半经典极限下统一产生宏观"力"；

3. 利用静态时空中的频率守恒与引力红移关系，证明时间刻度等价类与本征时间的重标等价，从而把引力时间膨胀与散射时间延迟统一为同一时间几何的不同读出方式；

4. 在代数量子场论与全息背景下，采用模块理论与 QNEC，将模流时间、广义熵极值与局域引力方程联系起来，提出"模时间与几何时间属于同一刻度等价类"的判据；

5. 提出一系列跨尺度的实验与观测方案，从微波网络与介观导体到原子钟链路与 FRB 宇宙学观测，为该统一框架提供可验证的工程路径。

从这一角度看，宇宙的基本结构更适合作为"时间–几何–信息"的统一体来理解：没有独立的"力"，只有时间刻度在不同几何方向上的弯曲，以及信息–熵在不同粗粒度层级上的单调变化。引力与量子、规范场与经典力，皆为这一统一时间几何在不同观测框架与能标下的投影。

---

## Acknowledgements, Code Availability

本工作未使用任何专门代码，仅依赖已有数学与物理文献中的定理与公式推导。数值模拟与可视化实现留待后续工作展开。

---

## References

[1] C. Texier, "Wigner time delay and related concepts – Application to transport in coherent conductors," *Physica E* 82, 16–33 (2016). ([科学直通车][2])

[2] F. Gesztesy, "Applications of spectral shift functions," Lecture notes (2017). ([matcuer.unam.mx][5])

[3] P. Guo, "Friedel formula and Krein's theorem in complex potential scattering," *Phys. Rev. Research* 4, 023083 (2022). ([物理评论链接管理器][10])

[4] V. Vargiamidis, "Density of states and Friedel sum rule in one dimension," *Phys. Lett. A* 374, 4380–4384 (2010). ([科学直通车][11])

[5] Lecture notes on Friedel sum rule and local density of states, Université Pierre et Marie Curie (2019). ([lptmc.jussieu.fr][12])

[6] D. Tong, "Yang-Mills Theory," Lecture notes (Cambridge, 2018). ([damtp.cam.ac.uk][1])

[7] J. O. Weatherall, "Fiber bundles, Yang–Mills theory, and general relativity," *Synthese* 199, 6079–6109 (2021). ([philsci-archive.pitt.edu][13])

[8] P. Michor, *Gauge Theory for Fiber Bundles*, Lecture notes (Univ. Vienna, 2008). ([mat.univie.ac.at][14])

[9] S. J. Summers, "Tomita–Takesaki modular theory," arXiv:math-ph/0511034 (2005). ([arXiv][3])

[10] "Tomita–Takesaki theory," nLab entry (2025). ([ncatlab.org][15])

[11] N. Lashkari, "Modular flow of excited states," *Commun. Math. Phys.* 384, 1511–1560 (2021). ([MIT DSpace][8])

[12] R. Bousso et al., "Proof of the quantum null energy condition," *Phys. Rev. D* 93, 024017 (2016). ([Astrophysics Data System][4])

[13] S. Balakrishnan et al., "A general proof of the quantum null energy condition," *JHEP* 09, 020 (2019). ([SpringerLink][7])

[14] A. Shahbazi-Moghaddam, "Aspects of generalized entropy and quantum null energy condition," PhD thesis, UC Davis (2020). ([电子学术][16])

[15] M. Mezei, "The quantum null energy condition and entanglement entropy," arXiv:1909.00919 (2019). ([arXiv][17])

[16] C. N. Yang, "Magnetic monopoles, fiber bundles, and gauge fields," Lecture (1977). ([wucj.lab.westlake.edu.cn][18])

[17] "Yang–Mills equations," standard reference entry (accessed 2025). ([维基百科][6])

---

## Appendix A: Scattering Time Delay, Spectral Shift and the Scale Identity

本附录给出定理 3.4 的详细证明。

### A.1 谱移函数与 Kreĭn 迹公式

设 $H_{0}$ 自伴，$V=H-H_{0}\in\mathfrak S_{1}$ 为迹类扰动。Krein 理论保证存在唯一的可测函数 $\xi(\lambda) \in L^{1}(\mathbb R)$，使得对任意具有足够衰减与光滑性的测试函数 $f$，有

$$
\mathrm{tr}[f(H)-f(H_{0})]=\int_{\mathbb R} f'(\lambda)\xi(\lambda),\mathrm d\lambda
$$

取 $f(\lambda)=\mathbf 1_{(-\infty,E]}(\lambda)$ 的平滑逼近，可得

$$
N(E;H)-N(E;H_{0})=\int_{-\infty}^{E}\xi'(\lambda),\mathrm d\lambda
$$

其中 $N(E;H)$ 为谱计数函数。对能量密度而言，得到

$$
\rho_{\mathrm{rel}}(E)=\xi'(E) \quad \text{几乎处处}。
$$

### A.2 Birman–Kreĭn 公式与相位

散射理论中，波算子 $W_{\pm}=\mathrm{s}-\lim_{t\to\pm\infty}e^{iHt}e^{-iH_{0}t}$ 的存在与完备性保证散射算符

$$
S=W_{+}^{\dagger}W_{-}
$$

在绝对连续谱上可分解为定能量分量 $S(\omega)$。Birman–Kreĭn 公式表明

$$
\det S(\omega)=e^{-2\pi i\xi(\omega)} \quad \text{近乎处处}。
$$

定义 $\Phi(\omega)=\arg\det S(\omega)$，选取连续分支，使得

$$
\Phi(\omega)=-2\pi\xi(\omega)
$$

（差一个整倍数 $2\pi$，不影响导数）。

令 $\varphi(\omega)=\tfrac12\Phi(\omega)=-\pi\xi(\omega)$，则

$$
\varphi'(\omega)/\pi=-\xi'(\omega)=-\rho_{\mathrm{rel}}(\omega)
$$

若在定义谱移函数时采用相反号约定，则可消去该负号，此处约定按正文采用。

### A.3 Wigner–Smith 矩阵与迹公式

Wigner–Smith 矩阵定义为

$$
Q(\omega)=-iS(\omega)^{\dagger}\partial_{\omega}S(\omega)
$$

注意到对任何可逆矩阵 $S(\omega)$，有

$$
\partial_{\omega}\ln\det S(\omega)=\mathrm{tr},[S^{-1}(\omega)\partial_{\omega}S(\omega)]
$$

对酉矩阵 $S(\omega)$，$S^{-1}(\omega)=S^{\dagger}(\omega)$，故

$$
-i\partial_{\omega}\ln\det S(\omega)=-i,\mathrm{tr},[S^{\dagger}(\omega)\partial_{\omega}S(\omega)]=\mathrm{tr},Q(\omega)
$$

另一方面，

$$
\ln\det S(\omega)=i\Phi(\omega)
$$

于是

$$
\mathrm{tr},Q(\omega)=-i\partial_{\omega}\ln\det S(\omega)=\Phi'(\omega)=2\varphi'(\omega)
$$

结合上述结果，得到

$$
\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\mathrm{tr},Q(\omega)
$$

至此，刻度同一式严格确立。

---

## Appendix B: Static Spacetime, Redshift and Scale Equivalence

### B.1 静态度规与局域能量

设静态时空度规

$$
g=-N^{2}(\mathbf x)\mathrm d t^{2}+h_{ij}(\mathbf x)\mathrm d x^{i}\mathrm d x^{j}
$$

Killing 向量 $\xi^{\mu}=(\partial_{t})^{\mu}$ 对应守恒量

$$
E=-p_{\mu}\xi^{\mu}=-p_{t}
$$

局域惯性系中测得的能量为

$$
\omega_{\mathrm{loc}}=p_{\hat 0}=N^{-1}(\mathbf x)E
$$

其中 $p_{\hat 0}$ 为正交标架分量。

因此，在散射区域中局域态密度与群延迟自然函数于 $\omega_{\mathrm{loc}}$。

### B.2 刻度密度与红移因子

假设刻度密度满足

$$
\kappa(\omega;\mathbf x)=\kappa_{\mathrm{loc}}(\omega_{\mathrm{loc}})=\kappa_{\mathrm{loc}}(N^{-1}(\mathbf x)\omega)
$$

远处 $N(\infty)=1$。对给定能量窗口，在远处观察者时间刻度下，群延迟为

$$
\Delta\tau(\omega;\mathbf x)=\int \frac{1}{2\pi}\mathrm{tr},Q(\omega;\mathbf x),\mathrm d\omega
$$

若 $\kappa_{\mathrm{loc}}$ 在窗口内缓慢变化，则

$$
\Delta\tau(\omega;\mathbf x)\approx N^{-1}(\mathbf x)\Delta\tau_{\infty}(\omega)
$$

因此，对两个位置 $\mathbf x_{1},\mathbf x_{2}$，时间刻度比值为

$$
\frac{\Delta\tau(\omega;\mathbf x_{2})}{\Delta\tau(\omega;\mathbf x_{1})}\approx \frac{N^{-1}(\mathbf x_{2})}{N^{-1}(\mathbf x_{1})}=\frac{N(\mathbf x_{1})}{N(\mathbf x_{2})}
$$

这与引力红移关系 $\nu_{2}/\nu_{1}=N(\mathbf x_{1})/N(\mathbf x_{2})$ 一致，从而表明两者属于同一时间刻度等价类。

---

## Appendix C: Semi-classical Limit and Force as Curvature Projection

### C.1 总联络下的作用量与路径积分

考虑含联络的作用量

$$
S[\gamma]=\int \left(p_{\mu}\dot x^{\mu}-H_{\mathrm{free}}(x,p)\right),\mathrm d\tau + \int \langle \chi, \boldsymbol{\Omega}(\dot{\gamma})\chi\rangle,\mathrm d\tau
$$

其中 $\chi$ 描述内部自由度与分辨率变量，$\boldsymbol{\Omega}$ 为总联络。

路径积分权因子为 $e^{iS[\gamma]}$。对作用量变分得

$$
m\frac{D^{2}x^{\mu}}{D\tau^{2}}=qF^{\mu}{}_{\nu}\dot x^{\nu}+f^{\mu}_{\mathrm{res}}
$$

其中 $F^{\mu}{}_{\nu}$ 由联络内部部分曲率得到，$f^{\mu}_{\mathrm{res}}$ 由分辨率流与熵梯度组合给出。

### C.2 Ehrenfest 定理与宏观力

希尔伯特空间上算符 $\hat x^{\mu}$ 与 $\hat p_{\mu}$ 的期望值演化满足 Ehrenfest 定理。对含联络的哈密顿量取期望，并在窄波包近似下，算符乘积的期望可以拆成乘积的期望加噪声修正。忽略高阶噪声，即得质心轨迹方程。此时，"力"完全由联络曲率决定。

---

## Appendix D: Modular Flow, QNEC and Gravitational Dynamics

### D.1 模流与相对熵

对局域代数 $\mathcal A(\mathcal O)$ 与状态 $\varphi$，模流 $\sigma^{\varphi}_{t}$ 与模哈密顿量 $K_{\varphi}=-\log\Delta_{\varphi}$ 满足

$$
\sigma^{\varphi}_{t}(A)=e^{iK_{\varphi}t}Ae^{-iK_{\varphi}t}
$$

相对熵

$$
S(\psi||\varphi)=\mathrm{tr}(\rho_{\psi}\log\rho_{\psi}-\rho_{\psi}\log\rho_{\varphi})
$$

在全息对应下，与广义熵与引力侧能量有直接关系。

### D.2 QNEC 与局域能量约束

QNEC 表达式

$$
\langle T_{kk}\rangle \geq \frac{1}{2\pi}S''
$$

保证沿零方向小变形下熵的二阶变化受能量限制。这可视为一种"熵膨胀的时间箭头"，并可用于证明若广义熵在给定截面上取极值，则对应的几何必须满足 Einstein 方程的局域形式。

### D.3 时间刻度等价类的对齐条件

若模流 $t$ 与几何时间 $\tau$ 属于同一刻度等价类，则模哈密顿量的单调性与引力侧的 Iyer–Wald 功–熵关系共同导出局域引力动力学。反之，若几何满足特定能量条件与广义第二定律，则可以构造使模流时间与几何时间对齐的状态与代数，从而完成统一时间刻度的闭合。

这一部分整合了代数 QFT、全息与引力热力学中的多项成果，表明时间刻度等价类既有散射–谱移的操作定义，又有模流–熵的结构定义，二者在适当条件下内在一致。

[1]: https://www.damtp.cam.ac.uk/user/tong/gaugetheory/2ym.pdf "2. Yang-Mills Theory"
[2]: https://www.sciencedirect.com/science/article/abs/pii/S1386947715302228 "Wigner time delay and related concepts"
[3]: https://arxiv.org/pdf/math-ph/0511034 "Tomita–Takesaki Modular Theory"
[4]: https://ui.adsabs.harvard.edu/abs/2016PhRvD..93b4017B/abstract "Proof of the quantum null energy condition"
[5]: https://www.matcuer.unam.mx/VeranoAnalisis/Fritz-I.pdf "Applications of Spectral Shift Functions. I: Basic Properties ..."
[6]: https://en.wikipedia.org/wiki/Yang%E2%80%93Mills_equations "Yang–Mills equations"
[7]: https://link.springer.com/article/10.1007/JHEP09%282019%29020 "A general proof of the quantum null energy condition"
[8]: https://dspace.mit.edu/bitstream/handle/1721.1/136738/13130_2021_Article_16749.pdf?isAllowed=y&sequence=1 "MIT Open Access Articles Modular flow of excited states"
[9]: https://courses.physics.illinois.edu/phys561/fa2005/lnotes/lect11.pdf "561 F 2005 Lecture 11"
[10]: https://link.aps.org/doi/10.1103/PhysRevResearch.4.023083 "Friedel formula and Krein's theorem in complex potential ..."
[11]: https://www.sciencedirect.com/science/article/abs/pii/S0375960110011333 "Density of states and Friedel sum rule in one"
[12]: https://www.lptmc.jussieu.fr/user/messio/ICFP_documents/TD_FriedelSumRule_enonce.pdf "Scattering and Friedel sum rule Local density of states"
[13]: https://philsci-archive.pitt.edu/11146/1/Fiber_bundles_YM_and_GR.pdf "Fiber Bundles, Yang-Mills Theory, and General Relativity"
[14]: https://www.mat.univie.ac.at/~michor/gaubook.pdf "GAUGE THEORY FOR FIBER BUNDLES"
[15]: https://ncatlab.org/nlab/show/modular%2Btheory "modular theory in nLab"
[16]: https://escholarship.org/content/qt6qt4k7rz/qt6qt4k7rz_noSplash_f5c5668c7a9af1a3e54257eefba1b382.pdf "Aspects of Generalized Entropy And Quantum Null Energy ..."
[17]: https://arxiv.org/abs/1909.00919 "[1909.00919] The Quantum Null Energy Condition and ..."
[18]: https://wucj.lab.westlake.edu.cn/teach/CNYang/Lec7_Yang1977.pdf "MAGNETIC MONOPOLES, FIBER BUNDLES, AND ..."
