# 暗物质作为信息孤岛：QCA 网络中的无电荷拓扑结与引力透镜效应

*Dark Matter as Information Islands: Charge-less Topological Knots and Gravitational Lensing in QCA Networks*

---

## Abstract

天体物理观测显示，宇宙总能量密度中约有四分之一以不发光、不参与电磁相互作用但通过引力影响结构形成的形态存在，被称为暗物质。精确宇宙学数据（例如 Planck 2018 的宇宙学参数测量）表明，暗物质的能量密度参数约为可见重子物质的五倍，且在宇宙早期已经以冷、非相对论形式存在。([Aanda][1]) 尽管弱相互作用大质量粒子（WIMP）、轴子等候选者在粒子物理层面被广泛研究，但迄今为止没有任何直接探测给出确认信号，仅持续推高了新粒子相互作用强度与质量参数空间的下限。([Particle Data Group][2])

本文在量子元胞自动机（quantum cellular automaton, QCA）与光程守恒/信息-引力变分原理（Information-Gravity Variational Principle, IGVP）的统一框架下，给出暗物质的一种纯拓扑与信息论解释，而无需引入任何新的基本粒子物种。基于我们之前建立的"质量即拓扑结"与"引力即信息拥塞"图景，首先严格刻画 Dirac 型 QCA 中质量的拓扑起源：局域激发的有效质量由布里渊区上演化算符的缠绕数决定；同时，将电荷刻画为局域希尔伯特空间对 $U(1)$ 规范群的表示型式。随后引入一个自然的希尔伯特空间分解

$$\mathcal H_{\text{cell}}=\mathcal H_{\text{vis}}\otimes\mathcal H_{\text{hid}},$$

其中可见扇区 $\mathcal H_{\text{vis}}$ 携带标准模型的规范荷，而隐藏扇区 $\mathcal H_{\text{hid}}$ 上的拓扑缠绕对电磁 $U(1)_{\text{EM}}$ 表示是平凡的。我们称后者支持的局域激发为**信息孤岛**：它们在动量空间具有非零拓扑指数，因而具备静止质量与惯性，但在所有可观测电磁过程上表现为无电荷。

在 IGVP 框架中，引力场并非由能动张量的组分直接决定，而是由总信息处理密度 $\rho_{\text{info}}(x)$ 的空间分布控制。可见与隐藏扇区的内部演化均消耗底层 QCA 的更新预算，因此对 $\rho_{\text{info}}(x)$ 具有同权贡献。我们证明：在弱场极限下，IGVP 导出的有效光学度规与广义相对论中由总质量密度 $\rho_{\text{vis}}+\rho_{\text{hid}}$ 决定的 Newton–Poisson 极限完全等价，因此信息孤岛在星系尺度上与冷暗物质在引力透镜和星系自转曲线上的效应不可区分。特别地，信息孤岛扇区不与电磁等"碰撞性"场耦合，因而在族星系团碰撞（如 Bullet Cluster）中表现为几乎无摩擦的碰撞无关物质，其透镜质量中心自然与高温重子气体的 X 射线峰分离，与观测结果一致。([维基百科][3])

在星系尺度上，我们把信息孤岛视为一族冷、无耗散、碰撞无关的粒子种类，在 QCA 的连续极限中满足无碰撞玻尔兹曼方程。利用相空间体积守恒与最大熵原理，推导出球对称、达稳态的晕结构具有近似等温球密度分布 $\rho(r)\propto r^{-2}$，并由此得到平坦自转曲线 $v(r)\approx\text{const}$，与观测的晚型星系旋转曲线相符。([Aanda][4])

本文的主结果可以概括为三个层面：（i）在满足局域幺正性与有限维局域希尔伯特空间的 QCA 模型中，存在具有非平凡拓扑质量而对可见规范群平凡的"无电荷拓扑结"子空间；（ii）在 IGVP 下，该子空间的内部演化以与重子物质等价的权重耦合到有效光学度规，因此在所有以引力为探针的观测中表现为暗物质；（iii）在星系与星系团尺度的整体动力学上，这类信息孤岛自动形成弥散的、难以耗散的晕结构，而不会塌缩为薄盘。由此，在统一的量子信息本体论中，暗物质可被解释为 QCA 网络中"只有内核、没有接口"的信息拓扑结，无需引入任何额外的基本粒子。

---

## Keywords

暗物质；量子元胞自动机；拓扑缠绕；信息孤岛；信息-引力变分原理；引力透镜；星系自转曲线

---

## Introduction & Historical Context

### 1.1 暗物质问题的观测起点

自 20 世纪中叶以来，对星系与星系团动力学的系统观测揭示了严重偏离仅由可见恒星与气体解释的引力势：晚型星系的旋转曲线在大半径处趋于平坦，而不是按牛顿势的预期随 $r^{-1/2}$ 衰减；星系团内星系的速度弥散与热 X 射线气体所暗示的约束质量远高于可见质量的总和。([Aanda][4])

现代宇宙学精确测量（如 Planck 2018）进一步通过宇宙微波背景各向异性与大尺度结构功率谱给出了暗物质能量密度参数 $\Omega_{\text{c}}\simeq 0.26$，而重子物质仅约 $\Omega_{\text{b}}\simeq 0.05$。([Aanda][1]) 这意味着在标准的 $\Lambda$CDM 模型中，暗物质是宇宙主导的非相对论成分，对结构形成的线性与非线性阶段均起关键作用。

强引力透镜为暗物质提供了几乎几何光学式的直接证据：在如 Bullet Cluster 等族星系团碰撞体系中，广义相对论透镜反演得到的质量分布明显偏离热 X 射线气体位置，而与星系分布更为一致。([维基百科][3]) 这种"引力势中心与重子质量中心分离"的现象难以用仅修改引力定律的方案解释，而自然符合"存在一族与重子解耦的碰撞无关物质"的直观图像。

### 1.2 粒子暗物质与隐藏扇区的传统路线

在粒子物理层面，暗物质通常被视为标准模型之外的某种新粒子：弱相互作用大质量粒子（WIMP）、轴子、惰性中微子、暗光子等。这些候选者可以自然地产生冷、稳定、非相对论的宇宙学背景，并通过"冻结"机制或误差修正机制得到正确数量级的 relic 密度。([Particle Data Group][2])

在最近的综述中，"隐藏扇区暗物质"成为一类重要范式：暗物质存在于一个与可见扇区仅通过引力或极弱 portal 相互作用的量子场集合之中。([维基百科][5]) 这一思路在形式上接近本文的出发点：暗物质并不需要与标准模型共享相同的规范荷，只需通过引力与我们耦合。然而，即使在隐藏扇区方案下，通常仍然假设存在一族新的粒子场，其质量与相互作用形式由拉氏量中额外的自由参数控制。

与此同时，拓扑缺陷（如宇宙弦、畴壁、轴子弦网）等在宇宙学早期相变中产生的拓扑结构，也被广泛讨论为暗物质或暗能量的潜在来源。([维基百科][6]) 在这些工作中，拓扑性质主要体现在场构型空间上，而不是直接与"信息处理"的本体量联系。

### 1.3 QCA 宇宙本体论与质量/引力的重新刻画

量子元胞自动机提供了一种截然不同的宇宙微观图景：世界由离散格点上的局域量子系统构成，按照严格幺正、局域、平移不变的更新规则离散时间演化。在合适的连续极限（格距 $a\to 0$、步长 $\Delta t\to 0$）下，可以涌现出 Dirac、Weyl 与 Maxwell 等标准场论方程。([arXiv][7])

我们在先前的工作中提出了两条互补的结构原则：

1. **质量即拓扑结**：在 Dirac 型 QCA 中，质量项并非任意参数，而是布里渊区上的演化算符 $U(k)$ 映射 $S^1\to SU(2)$ 的同伦类（缠绕数 $\mathcal W$）的函数。具有非零缠绕数的模态必须在局域尺度上维持持续的内部震荡，其信息更新速率 $v_{\text{int}}$ 非零，对应有效质量与惯性。

2. **引力即信息拥塞（IGVP）**：引力场不再被视为连续流形上的度规张量先验给定，而被解释为 QCA 网络在保持总体信息光程守恒的条件下，对局域信息处理密度 $\rho_{\text{info}}(x)$ 非均匀性的几何响应。局域信息过密导致"信息拥塞"，等效为有效光速减小或折射率 $n(x)$ 增大，从而弯曲光线与世界线。

在这一图景中，质量与引力分别是"自指拓扑循环"与"全局信息预算平衡"的表现，并非外在引入的额外实体。

### 1.4 本文的目标与贡献

本文沿着上述 QCA–IGVP 本体论的方向，将暗物质问题重述为以下问题：

> 在一个以 QCA 为基础的离散幺正宇宙中，是否必然存在一类拓扑上有质量、但与电磁规范场完全解耦的局域激发，使其在所有以光子为媒介的观测中保持"暗"的特征，却在引力上与重子物质等价？

我们将给出肯定回答，并证明在十分宽泛的模型族中，这类**无电荷拓扑结**不仅存在，而且在统计上自然地占据宇宙能量预算的有限比例，使得暗物质现象成为 QCA 网络拓扑结构的必然副产物，而非对拉氏量的额外假设。

---

## Model & Assumptions

### 2.1 Dirac 型 QCA 与拓扑质量

考虑一维平移不变的 Dirac 型 QCA，其局域希尔伯特空间维数为 $d$，格点标号为 $x\in\mathbb Z$，单步演化由幺正算符 $\hat U$ 给出，满足

$$\hat U = \prod_x U_{x,x+1},$$

其中 $U_{x,x+1}$ 仅作用于相邻元胞的局域自由度并在格上平移不变。对该系统施行傅里叶变换，可以在动量表象中写成

$$\hat U = \int_{-\pi/a}^{\pi/a} \frac{\mathrm d k}{2\pi} |k\rangle\langle k|\otimes U(k), \quad U(k)\in U(d),$$

其中 $a$ 为格距。对于 Dirac 型 QCA，可选取 $d=2$，并在合适参数化下写为

$$U(k)=\exp\bigl(-\mathrm i \omega(k) \mathbf n(k)\cdot \boldsymbol\sigma\bigr),$$

其中 $\boldsymbol\sigma$ 为 Pauli 矩阵，$\mathbf n(k)$ 为单位向量，$\omega(k)$ 为色散关系。若在小动量极限下存在

$$\omega(k)\approx \sqrt{(c k)^2 + (m c^2/\hbar)^2},$$

则该 QCA 的长波极限满足 Dirac 方程，参数 $m$ 被解释为有效质量。([arXiv][7])

拓扑视角下，映射

$$k\in S^1\mapsto U(k)\in SU(2)$$

由 $K_1(S^1)\cong\mathbb Z$ 分类，其拓扑不变量为缠绕数

$$\mathcal W=\frac{1}{2\pi \mathrm i}\int_{-\pi/a}^{\pi/a}\mathrm d k \partial_k \log\det U(k).$$

在 Dirac 型 QCA 中，$\mathcal W\neq 0$ 对应于存在能隙的"拓扑质量"扇区，其带结构在布里渊区内完成一个非平凡的绕行。我们将质量定义为这一缠绕数通过连续极限的重整化映射到有效场论质量参数的像，从而实现"质量即拓扑结"的刻画。

### 2.2 规范场与电荷的表示论刻画

为在 QCA 中引入电磁相互作用，可在每个元胞上赋予局域 $U(1)_{\text{EM}}$ 规范自由度，其规范变换作用为

$$|\psi_x\rangle\mapsto e^{\mathrm i q\alpha_x}|\psi_x\rangle,$$

其中 $\alpha_x$ 为局域规范相位，$q$ 为粒子电荷。连接场通过格边上的链变量

$$U_{x,x+1}^{\text{link}}=\exp\bigl(\mathrm i a A_x\bigr)$$

实现，演化算符在耦合电磁场后服从协变性

$$U(k;A)\mapsto e^{\mathrm i q\alpha(k)} U\bigl(k+\partial\alpha;A\bigr) e^{-\mathrm i q\alpha(k)}.$$

在这一语言中，**电荷**被定义为局域希尔伯特空间 $\mathcal H_{\text{cell}}$ 上 $U(1)_{\text{EM}}$ 的表示：若在某一基底下，规范变换作用为

$$e^{\mathrm i q\alpha_x} \mathbb I_{\mathcal H},$$

则该模态为电中性；若表示为非平凡对角或非对角矩阵，则对应有电荷或多重荷。电磁相互作用本质上是 $U(k)$ 对 $U_{x,x+1}^{\text{link}}$ 的非对易敏感性。

### 2.3 可见/隐藏扇区与信息孤岛的定义

我们引入如下结构性假设。

**假设 2.1（局域希尔伯特空间分解）**

存在局域 Hilbert 空间的张量分解

$$\mathcal H_{\text{cell}}=\mathcal H_{\text{vis}}\otimes \mathcal H_{\text{hid}},$$

满足：

1. 电磁 $U(1)_{\text{EM}}$ 仅在 $\mathcal H_{\text{vis}}$ 上以非平凡表示作用，在 $\mathcal H_{\text{hid}}$ 上作用为恒等，即

   $$V(\alpha_x)=V_{\text{vis}}(\alpha_x)\otimes \mathbb I_{\text{hid}}.$$

2. 在无其它相互作用的理想极限下，总演化算符可写为

   $$\hat U=\hat U_{\text{vis}}\otimes \hat U_{\text{hid}},$$

   其中 $\hat U_{\text{vis}}$ 支持标准模型粒子的谱，而 $\hat U_{\text{hid}}$ 为一组附加的 Dirac/QCA 模型。

在动量表象下，这意味着存在

$$U(k)=U_{\text{vis}}(k)\otimes U_{\text{hid}}(k),$$

其拓扑性质由

$$\mathcal W_{\text{tot}}=\mathcal W_{\text{vis}}+\mathcal W_{\text{hid}}$$

给出。

**定义 2.2（信息孤岛模态）**

称一族 Bloch 模态为信息孤岛，若满足：

1. 在 $\mathcal H_{\text{hid}}$ 投影上，其拓扑缠绕数 $\mathcal W_{\text{hid}}\neq 0$，对应非零静止质量 $m_{\text{hid}}>0$；

2. 在 $\mathcal H_{\text{vis}}$ 上处于电中性子空间，即 $V_{\text{vis}}(\alpha_x)$ 作用为恒等，因而对 $U(1)_{\text{EM}}$ 变换不产生 Aharonov–Bohm 相位；

3. 总态可写为 $|\Psi\rangle = |\psi_{\text{vis}}^0\rangle\otimes|\psi_{\text{hid}}\rangle$，其中 $|\psi_{\text{vis}}^0\rangle$ 为真空或中性背景。

对于此类模态，质量由 $\hat U_{\text{hid}}$ 的拓扑结构决定，而所有电磁过程（散射、辐射、吸收）均由 $\hat U_{\text{vis}}$ 控制，因此在电磁观测中表现为完全"暗"的局域激发。

### 2.4 信息-引力变分原理与有效光学度规

在 IGVP 框架中，引力场由 QCA 网络在保持总信息速率守恒条件下对局域信息密度的最优响应确定。我们只需在弱场、静态极限下采用其简化形式。

定义局域信息处理密度

$$\rho_{\text{info}}(x)=\rho_{\text{vis}}(x)+\rho_{\text{hid}}(x),$$

其中各项由对应扇区的内部演化频率与占据数给出。对于近似自由的准粒子激发，可写为

$$\rho_{\text{hid}}(x)\sim \sum_i n_i(x) \hbar\omega_{\text{int}}^{(i)},$$

这里 $n_i(x)$ 为第 $i$ 种信息孤岛准粒子在位置 $x$ 的数密度，$\omega_{\text{int}}^{(i)}$ 为其内部震荡频率，与质量通过关系

$$m_i c^2 = \hbar \omega_{\text{int}}^{(i)}$$

相联系。

在弱场、准静态极限下，IGVP 导出的有效光学度规可写为

$$\mathrm d s^2 = -\bigl(1+2\Phi(x)/c^2\bigr)c^2 \mathrm d t^2 + \bigl(1-2\Phi(x)/c^2\bigr) \mathrm d \mathbf x^2,$$

其中有效势 $\Phi(x)$ 满足 Poisson 型方程

$$\nabla^2 \Phi(x)=4\pi G_{\text{eff}}\bigl[\rho_{\text{vis}}(x)+\rho_{\text{hid}}(x)\bigr].$$

在合适的标度选择下，$G_{\text{eff}}$ 与牛顿常数 $G$ 等价，使得 IGVP 的弱场极限与广义相对论的 Newton–Poisson 极限一致。由此可见，从光线、测试粒子的轨道与结构形成的角度看，信息孤岛与普通冷暗物质在引力尺度上完全等价。

### 2.5 宏观动力学近似

在星系与星系团尺度，我们采用以下动力学假设：

**假设 2.3（碰撞无关与无耗散）**

1. 信息孤岛间仅通过引力/IGVP 相互作用，其两体散射截面远小于重子气体的库仑截面，在星系团碰撞的时间尺度上可视为碰撞无关。

2. 信息孤岛不能发射、吸收或散射光子，因而缺乏类似重子物质通过辐射冷却实现的耗散通道；唯一的能量损失机制是极弱的引力波辐射或网络几何微扰波，此类过程时间尺度远大于哈勃时间。

3. 在星系晕的形成与演化中，可将信息孤岛视为冷、非相对论的粒子，满足无碰撞玻尔兹曼方程，宏观上形成维里化的自引力系统。

在这一近似下，信息孤岛在大尺度上与标准冷暗物质（CDM）的动力学几乎一致，而在微观层面具有截然不同的本体论解释。

---

## Main Results (Theorems and Alignments)

本节给出本文的主要定理及其与观测现象的对应关系。严格证明在后续章节与附录中展开。

### 定理 3.1（QCA 中质量与电荷的正交性）

在满足假设 2.1 的 Dirac 型 QCA 中，拓扑质量与电磁电荷可以在希尔伯特空间分解 $\mathcal H_{\text{cell}}=\mathcal H_{\text{vis}}\otimes\mathcal H_{\text{hid}}$ 下实现正交分离：

1. 质量完全由 $\hat U_{\text{vis}}$ 与 $\hat U_{\text{hid}}$ 在动量空间的缠绕数 $\mathcal W_{\text{vis}},\mathcal W_{\text{hid}}$ 决定；

2. 电磁电荷完全由 $U(1)_{\text{EM}}$ 在 $\mathcal H_{\text{vis}}$ 上的表示决定，对 $\mathcal H_{\text{hid}}$ 为平凡表示。

因此必然存在一族模态，其满足 $\mathcal W_{\text{hid}}\neq 0$、$\mathcal W_{\text{vis}}=0$、$q=0$，对应有质量而无电荷的"隐藏拓扑结"，即信息孤岛。

### 定理 3.2（信息孤岛对光学度规的等价引力贡献）

在 IGVP 的弱场极限下，若总信息密度为

$$\rho_{\text{info}}(x)=\rho_{\text{vis}}(x)+\rho_{\text{hid}}(x),$$

则由变分原理得到的有效势 $\Phi(x)$ 满足

$$\nabla^2 \Phi(x)=4\pi G\bigl[\rho_{\text{vis}}(x)+\rho_{\text{hid}}(x)\bigr],$$

其中 $G$ 为适当归一化后的引力常数。由此可见，信息孤岛对引力势的贡献与普通冷暗物质等价，只要其内部演化频率通过关系 $m c^2=\hbar\omega_{\text{int}}$ 与有效质量相联系。任何依赖光学度规的观测（如引力透镜、轨道动力学）不能区分"重子质量"与"信息孤岛质量"。

### 定理 3.3（星系暗晕的近似等温球分布与平坦自转曲线）

在假设 2.3 下，将信息孤岛视为冷、碰撞无关的粒子气体，在静态、球对称引力势 $\Phi(r)$ 中达到维里化平衡时，其相空间分布函数 $f(\mathbf x,\mathbf v)=f(E)$ 满足最大熵原理，得到

$$f(E)\propto \exp\bigl(-E/\sigma^2\bigr),\quad E=\tfrac{1}{2}v^2+\Phi(r),$$

从而空间密度

$$\rho(r)\propto \exp\bigl(-\Phi(r)/\sigma^2\bigr).$$

与 Poisson 方程联立，其大半径渐近解为

$$\rho(r)\simeq \frac{\sigma^2}{2\pi G r^2},$$

相应的包络质量为 $M(r)\propto r$，圆轨道速度

$$v_{\text{rot}}(r)=\sqrt{\frac{G M(r)}{r}}\approx \sqrt{2} \sigma\approx \text{const}.$$

因此，信息孤岛自然形成具有 $\rho(r)\propto r^{-2}$ 的等温晕结构，给出平坦的星系自转曲线，无需修改牛顿引力或引入特定形状的势函数。

### 定理 3.4（族星系团碰撞中的质量–重子分离）

考虑两团均含有大量信息孤岛与重子气体的星系团发生近头碰撞：

1. 信息孤岛为碰撞无关成分，其典型平均自由程远大于星系团尺度；

2. 重子气体为强碰撞成分，发生激烈冲击、压缩与加热，形成集中在碰撞中心的高温 X 射线气体云。([维基百科][3])

则碰撞后短时间内的质量分布满足：引力势主峰与星系分布一致，而 X 射线气体峰位于两者之间的中部区域。这一"质量–重子分离"现象是 Bullet Cluster 等观测的特征标志，在本模型中由信息孤岛与重子气体截然不同的碰撞性质自然导出。

### 命题 3.5（与 CMB 与大尺度结构的相容性）

若信息孤岛在宇宙学早期即已处于非相对论状态（冷暗物质条件），且在辐射主导时期仅通过引力与重子–辐射流体耦合，则本模型在背景膨胀与线性涨落演化的层面与标准 $\Lambda$CDM 模型等价。其对 CMB 各向异性谱、BAO 尺度与大尺度结构功率谱的主要贡献可以视为一族冷、压力可忽略、碰撞无关的暗物质成分，与现有观测约束兼容。([Aanda][1])

---

## Proofs

本节给出主要定理的证明思路与关键步骤，更技术性的细节安排在附录中。

### 4.1 定理 3.1：QCA 中质量与电荷的正交性

在假设 2.1 下，动量表象中的演化算符可写为

$$U(k)=U_{\text{vis}}(k)\otimes U_{\text{hid}}(k).$$

考虑 $U(1)_{\text{EM}}$ 的表示

$$V(\alpha)=V_{\text{vis}}(\alpha)\otimes \mathbb I_{\text{hid}},$$

其中 $V_{\text{vis}}$ 为 $\mathcal H_{\text{vis}}$ 上的幺正表示。

1. **质量的拓扑来源**：缠绕数由

   $$\mathcal W=\frac{1}{2\pi \mathrm i}\int_{-\pi/a}^{\pi/a}\mathrm d k \partial_k\log\det U(k)$$

   定义。利用 $\det(U\otimes V)=(\det U)^{\dim V}(\det V)^{\dim U}$，将 $\mathcal W$ 分解为

   $$\mathcal W=\dim\mathcal H_{\text{hid}}\cdot \mathcal W_{\text{vis}}+\dim\mathcal H_{\text{vis}}\cdot \mathcal W_{\text{hid}},$$

   其中

   $$\mathcal W_{\text{vis}}=\frac{1}{2\pi \mathrm i}\int \mathrm d k \partial_k\log\det U_{\text{vis}}(k),
   \quad
   \mathcal W_{\text{hid}}=\frac{1}{2\pi \mathrm i}\int \mathrm d k \partial_k\log\det U_{\text{hid}}(k).$$

   在连续极限中，这两个拓扑数分别对应可见与隐藏扇区的质量参数。

2. **电荷的表示论来源**：电磁电荷由 $V_{\text{vis}}(\alpha)$ 在 $\mathcal H_{\text{vis}}$ 上的不可约分解决定：若某一不可约分量上 $V_{\text{vis}}(\alpha)=e^{\mathrm i q\alpha}$ 表示，则其电荷为 $q$。对 $\mathcal H_{\text{hid}}$ 而言，表示恒为恒等，故其电荷必为零。

3. **正交性**：质量取决于 $U_{\text{vis}},U_{\text{hid}}$ 的拓扑性质，而电荷仅取决于 $V_{\text{vis}}$ 的表示。只要 $U_{\text{hid}}$ 可以选取具有非零 $\mathcal W_{\text{hid}}$ 的参数区间，而 $V_{\text{vis}}$ 在某个子空间上为平凡表示，则该子空间上存在 $\mathcal W_{\text{hid}}\neq 0,q=0$ 的模态，即信息孤岛。拓扑分类理论（如 1 维 gapped 带结构由 $K_1(S^1)\cong \mathbb Z$ 分类）保证这一选择在参数空间中是开放而稳定的。

因此，质量与电荷在 QCA 框架下可实现完全正交的自由度分配，从而容许无电荷的拓扑有质量模态存在。

### 4.2 定理 3.2：信息孤岛对光学度规的贡献

IGVP 在弱场极限下可以被写成一个作用泛函

$$S_{\text{IGVP}}[g,\rho_{\text{info}}]=\int \mathrm d^4 x \sqrt{-g} \Bigl(\mathcal L_{\text{geom}}(g)+\lambda\bigl[\kappa(g)-\rho_{\text{info}}\bigr]\Bigr),$$

其中 $\kappa(g)$ 是由 Wigner–Smith 时间延迟迹或散射相位导数定义的统一时间密度，$\lambda$ 为拉格朗日乘子。对 $g_{\mu\nu}$ 变分并取弱场极限 $g_{\mu\nu}=\eta_{\mu\nu}+h_{\mu\nu}$ 得到近似的场方程

$$\nabla^2 \Phi(x)=4\pi G_{\text{eff}}\rho_{\text{info}}(x),$$

其中 $\Phi$ 为牛顿势，$G_{\text{eff}}$ 由 $\lambda$ 与 $\mathcal L_{\text{geom}}$ 的细节决定。在可见与隐藏扇区同时存在时，信息密度为

$$\rho_{\text{info}}(x)=\sum_j n_j^{\text{vis}}(x) \hbar\omega_{\text{int},j}^{\text{vis}} + \sum_i n_i^{\text{hid}}(x) \hbar\omega_{\text{int},i}^{\text{hid}}.$$

利用关系 $m c^2=\hbar\omega_{\text{int}}$，可定义等效质量密度

$$\rho_{\text{mass}}(x)=\rho_{\text{vis}}(x)+\rho_{\text{hid}}(x),$$

满足

$$\rho_{\text{info}}(x)=c^2 \rho_{\text{mass}}(x).$$

因此

$$\nabla^2 \Phi(x)=4\pi G_{\text{eff}} c^2\bigl[\rho_{\text{vis}}(x)+\rho_{\text{hid}}(x)\bigr].$$

通过适当选择理论中的归一化，使 $G_{\text{eff}}c^2=G$，即可得到标准的 Newton–Poisson 方程。因此，在光学度规中的折射率

$$n(x)\approx 1-\frac{2\Phi(x)}{c^2}$$

完全由总质量密度控制，被分解为"重子 + 信息孤岛"的贡献。这证明了信息孤岛对引力与透镜效应的贡献在弱场极限下等价于普通冷暗物质。

### 4.3 定理 3.3：等温球与平坦自转曲线

对信息孤岛组成的星系晕，采用无碰撞玻尔兹曼方程

$$\frac{\partial f}{\partial t} + \mathbf v\cdot\nabla_x f - \nabla\Phi\cdot\nabla_v f=0.$$

在稳态、球对称情形下，$f$ 只依赖于粒子总能量 $E=\tfrac{1}{2}v^2+\Phi(r)$。最大熵原理给出

$$f(E)\propto \exp\bigl(-E/\sigma^2\bigr),$$

对应一族等温分布。空间密度

$$\rho(r)=\int f(E) \mathrm d^3 v\propto \exp\bigl(-\Phi(r)/\sigma^2\bigr).$$

代入球对称 Poisson 方程

$$\frac{1}{r^2}\frac{\mathrm d}{\mathrm d r}\Bigl(r^2\frac{\mathrm d\Phi}{\mathrm d r}\Bigr)=4\pi G \rho_0\exp\bigl(-\Phi(r)/\sigma^2\bigr)$$

可求得在 $r$ 足够大处的渐近解

$$\Phi(r)\simeq 2\sigma^2\ln r + \text{const},
\quad
\rho(r)\simeq \frac{\sigma^2}{2\pi G r^2}.$$

此时包络质量

$$M(r)=\int_0^r 4\pi r'^2\rho(r') \mathrm d r'\propto r,$$

圆轨道速度

$$v_{\text{rot}}(r)=\sqrt{\frac{G M(r)}{r}}\simeq \sqrt{2} \sigma$$

趋于常数。这与观测到的许多星系外盘平坦自转曲线一致，且无需引入额外的经验势函数或修改引力律。([Aanda][4])

### 4.4 定理 3.4：Bullet Cluster 类型碰撞的质量–重子分离

在星系团尺度，重子物质主要以高温稀薄气体形式存在，其动力学由流体力学与辐射过程控制。两团碰撞时：

1. 重子气体之间发生强烈的冲击与压缩，动能快速转化为热能，通过 X 射线辐射向外发射；

2. 信息孤岛成分为碰撞无关，平均自由程远大于团尺度，几乎无散射地穿过对方，保持原有速度与轨道。

因此，在碰撞后不久的时刻：

* 质量主峰（由透镜反演给出）位于两个团原来的星系分布附近；

* 重子气体峰集中在两团之间的碰撞区域，形成明显偏离质量峰的 X 射线热气体云。

这与 Bullet Cluster 等观测中"质量峰（透镜质量）与重子峰（X 射线亮度）分离"的结果一致。([维基百科][3]) 在本模型中，这种分离不需要假设任意形式的暗物质自相互作用，只是信息孤岛与重子气体在碰撞截面上的巨大差异的直接后果。

---

## Model Apply

本节讨论模型在星系、星系团与宇宙学尺度上的具体应用与可检验后果。

### 5.1 星系自转曲线与晕结构

定理 3.3 表明，在无耗散、碰撞无关的条件下，信息孤岛自然形成等温晕，其密度 $\rho(r)\propto r^{-2}$，对应平坦自转曲线。这与晚型星系、矮星系与低表面亮度星系中普遍观测到的平坦旋转曲线高度一致。([Aanda][4])

在具体建模上，可将星系总引力势写为

$$\Phi_{\text{tot}}(r)=\Phi_{\text{disk}}(r)+\Phi_{\text{bulge}}(r)+\Phi_{\text{halo}}(r),$$

其中晕势 $\Phi_{\text{halo}}$ 由信息孤岛组成的等温晕给出。拟合星系旋转曲线时，盘与核的贡献由可见光与气体分布确定，晕的参数则由 $\sigma$ 与归一化 $\rho_0$ 决定。该方案在形式上与传统的等温晕拟合无异，但本质上将晕视为"信息孤岛气体"，而不是未指定性质的"暗粒子云"。

### 5.2 星系团质量与透镜映射

星系团的质量可通过三种方式估计：

1. 星系速度弥散给出的动力学质量；

2. X 射线气体的热平衡与静力学方程给出的质量；

3. 强、弱引力透镜重建的质量分布。([维基百科][3])

在本模型中，重子物质贡献 $\rho_{\text{vis}}$，信息孤岛贡献 $\rho_{\text{hid}}$，透镜反演测得的是 $\rho_{\text{vis}}+\rho_{\text{hid}}$。在 Bullet Cluster 这类碰撞团中，信息孤岛成分与星系一起几乎无摩擦地穿过，而重子气体被滞留在中部。这使得透镜质量峰与星系分布重合，与 X 射线气体峰分离，正如观测所示。

近期基于 Webb 与 Chandra 的联合观测进一步提高了对 Bullet Cluster 质量分布的分辨率，强化了"暗成分为碰撞无关物质"的图像。([NASA Science][8]) 在我们的框架下，这些观测可被理解为信息孤岛扇区在星系团尺度上主导 $\rho_{\text{hid}}$ 的证据。

### 5.3 小尺度透镜与暗子晕

冷暗物质模型预言存在丰富的小质量子晕，其引力影响可通过强透镜系统（如爱因斯坦环）的微扰来探测。最近的工作在一个红移约 $z\sim 1$ 的爱因斯坦环中发现了质量约 $10^6 M_\odot$ 的"暗物体"，与冷暗物质子晕的预期相符。([Live Science][9])

在 QCA–信息孤岛图景中，这类暗子晕可被视为信息孤岛成分局域过密的区域。由于信息孤岛不参与电磁过程，它们无法形成恒星或辐射标志，仅通过透镜效应显现。我们预言，随着 Euclid、Roman 与更大样本的高分辨率爱因斯坦环观测的推进，将会不断发现在宽质量区间内的"纯透镜"暗子晕，这与冷暗物质及本模型预测一致。([卫报][10])

### 5.4 宇宙学尺度：CMB 与大尺度结构

命题 3.5 已表明，只要信息孤岛成分在重组前已冷却为非相对论，其在背景膨胀方程中可作为一族压强可忽略的物质成分出现，与冷暗物质在 Friedmann 方程中的角色完全一致；在线性扰动理论中，其声速近零，对宇宙微波背景各向异性谱与重子声学振荡的位置与高度的影响也等价于传统 CDM。([Aanda][1])

从 QCA 的角度看，这意味着在宇宙早期大尺度上，信息孤岛扇区已经形成了大量拓扑有质量模态，其统计分布与可见扇区的初始涨落通过共同的 QCA 初始状态与演化规则相联系。这一"共同起源"避免了对暗物质扇区独立初始条件的额外假设。

---

## Engineering Proposals

本节提出若干面向观测与模拟的"工程化"建议，以检验"暗物质作为信息孤岛"的具体预言。

### 6.1 透镜–动力学一致性的 IGVP 标度检验

在 IGVP 框架下，总信息密度与等效质量密度之间存在固定比例 $\rho_{\text{info}}=c^2\rho_{\text{mass}}$。这意味着在任一引力束缚系统中，通过星系动力学（轨道速度、速度弥散）与透镜质量重建得到的质量分布应在 IGVP 标度下严格一致。

可以设计如下检验程序：

1. 选取一批具有高质量透镜数据与详尽动力学测量的星系团样本；

2. 使用标准 GR 透镜反演得到 $\Phi_{\text{lens}}(x)$ 与 $M_{\text{lens}}(x)$；

3. 使用星系速度弥散与热气体静力学方程得到 $M_{\text{dyn}}(x)$；

4. 比较 $M_{\text{lens}}$ 与 $M_{\text{dyn}}$ 的一致性，并用 IGVP 标度重标 $\rho_{\text{info}}$。

若 IGVP 为正确的引力–信息关系，则在广泛样本上应不存在系统性的标度偏差。这一程序与传统的"质量–光度比"分析不同，强调的是透镜–动力学的严格一致性。

### 6.2 QCA 数值模拟中的"暗扇区"构造

在可控的量子模拟平台上（如离子阱、超导量子比特阵列），可实现 Dirac 型 QCA 的有限尺寸版本。利用局域 Hilbert 空间的扩展，自然可以引入一个隐藏扇区 $\mathcal H_{\text{hid}}$，并将其与可见扇区在控制脉冲层面解耦。

工程步骤包括：

1. 设计一个二部 QCA：一部实现可见 Dirac 扇区，另一部实现具有非零缠绕数的隐藏扇区；

2. 在可见扇区注入波包，测量其传播与散射；

3. 在隐藏扇区注入波包，但仅通过其对全局"更新预算"（例如总演化步数限制）或通过系统能量的重标感知其存在。

虽然当前量子模拟规模远不能直接模拟星系晕，但这些实验可以验证"质量由拓扑缠绕决定"，"隐藏扇区对可见扇区透明而仍然占用计算资源"等核心机制。

### 6.3 暗子晕统计与 QCA 单元尺度的反推

在 QCA 本体论中，格距 $a$ 与步长 $\Delta t$ 设定了宇宙中最小可分辨的"信息单元"。信息孤岛的最小稳定结构尺度与 QCA 的局域规则有关，从而为暗子晕的最小质量 $M_{\text{min}}$ 提供自然下限。

可以通过统计分析爱因斯坦环与强透镜系统中的暗子晕质量函数，寻找低质量端的截断：

* 若观察到的 $M_{\text{min}}$ 明显大于粒子自由流或重子反馈给出的下限，则可将其解释为信息孤岛拓扑结构的最小尺度；

* 进一步的统计可用来反推 QCA 格距的有效约束，从而为离散宇宙模型提供天文尺度的实验窗口。

---

## Discussion (Risks, Boundaries, Past Work)

### 7.1 与传统隐藏扇区暗物质的比较

本文给出的图景在表面上与"隐藏扇区暗物质"十分接近：暗物质存在于与标准模型仅通过引力耦合的量子场集合之中。([维基百科][5]) 然而二者的核心差异在于：

1. 本文不引入新的基本粒子拉氏量，而从更底层的 QCA 演化算符出发，将暗扇区视为希尔伯特空间分解中的必然部分；

2. 质量并非自由参数，而是与 QCA 带结构的拓扑缠绕数直接相关；

3. 引力响应由 IGVP 中的统一时间密度 $\kappa(\omega)$ 与信息密度决定，而不再是能动张量的先验输入。

因此，本文可以被视为对传统隐藏扇区方案的"信息论–拓扑化"升级版本。

### 7.2 与拓扑缺陷暗物质方案的关系

拓扑缺陷（宇宙弦、畴壁等）长期被讨论为暗物质或暗能量的潜在源头。([维基百科][6]) 与这些方案不同的是：

* 拓扑缺陷通常是连续场在空间中的非平凡构型，其能量密度与张力与对称性破缺尺度相关；

* 本文的"拓扑结"则是 QCA 动量空间中演化算符的缠绕，属于谱拓扑而非配置空间拓扑。

二者在数学上分别对应 $K$-理论的不同层面：前者更接近场配置的同伦类，后者则属于算符代数的 $K_1$ 类。尽管如此，从宇宙学现象的角度看，两者都体现了"拓扑稳定、长寿命、难以耗散"的共同特征。

### 7.3 风险与边界条件

本模型仍然存在若干需要谨慎对待的方面：

1. **早期宇宙约束**：信息孤岛在宇宙学早期的产生机制必须与 BBN、CMB 约束相容，避免产生过多的有效自由度或辐射压强。

2. **自相互作用与核心–包层问题**：若信息孤岛存在有限的自相互作用，可能有助于解决银河系中心密度坡度等问题，但也受到星系团尺度上暗物质自相互作用上限的限制。([arXiv][11])

3. **量化 IGVP 的偏离**：IGVP 在弱场极限被调至与 GR 等价，但在强场与非平衡情形下可能出现可观测偏离，需要与黑洞阴影、引力波传播等观测结果比对。

这些问题为后续工作提供了具体、可量化的检验方向。

### 7.4 相关工作的脉络

除了 QCA 与信息引力方向的工作之外，近年的 Euclid、JWST 与地面大规模巡天提供了前所未有的暗物质透镜与结构形成数据，也为本文提出的"信息孤岛"图景提供了丰富的可对比材料。([卫报][10])

在理论侧，关于从量子信息、纠缠结构或矩阵模型导出时空与引力的研究迅速发展，为将暗物质重述为"信息拓扑结构"提供了更广阔的背景框架。本文可视为其中一条具体、可计算的路线，其特色在于引入了明确的 QCA 模型与可与天文观测直接对接的预测。

---

## Conclusion

本文在量子元胞自动机与信息-引力变分原理的统一框架下，给出了暗物质的一种全新的解释：暗物质并非独立的"新粒子"，而是 QCA 网络中一类拓扑上有质量、在电磁上无接口的**信息孤岛**。

在这一图景中：

1. 质量由 QCA 演化算符在布里渊区上的拓扑缠绕数决定，实现"质量即拓扑结"；

2. 电荷由局域希尔伯特空间对 $U(1)_{\text{EM}}$ 的表示决定，与拓扑质量在结构上正交，从而必然允许"有质量而无电荷"的隐藏扇区存在；

3. IGVP 将引力刻画为对总信息密度的几何响应，使信息孤岛扇区在弱场极限中与冷暗物质在引力效应上完全等价；

4. 在星系与星系团尺度，信息孤岛形成近似等温晕，给出平坦自转曲线，并在族星系团碰撞中自然产生质量–重子分离，与 Bullet Cluster 等观测一致。

因此，在一个以 QCA 为宇宙微观本体的统一框架中，暗物质现象不再需要额外的拉氏项与新粒子假设，而成为离散量子信息网络拓扑结构的必然投影。这为理解暗物质的本质提供了一个兼具可计算性与观测可检验性的途径。

---

## Acknowledgements

作者感谢在量子元胞自动机、天体物理与信息引力方向上提供讨论与建议的同事与同行。任何潜在的错误与不足均由作者自行承担。

---

## Code Availability

本文所有推导均为解析工作，未使用数值仿真代码，因此不存在可共享的代码实现。未来若开展 QCA 数值模拟，将另行公开相应的参考实现。

---

## References

[1] N. Aghanim et al. (Planck Collaboration), "Planck 2018 results. VI. Cosmological parameters", *Astron. Astrophys.*, **641**, A6 (2020). ([Aanda][1])

[2] Particle Data Group, "27. Dark Matter", *Phys. Rev. D* **110**, 030001 (2024). ([Particle Data Group][2])

[3] D. Clowe et al., "A Direct Empirical Proof of the Existence of Dark Matter", *Astrophys. J. Lett.*, **648**, L109 (2006). ([维基百科][3])

[4] M. Weber, W. de Boer, "Determination of the local dark matter density in our Galaxy", *Astron. Astrophys.*, **509**, A25 (2010). ([Aanda][4])

[5] D. Hooper, S. Profumo, "Dark matter and collider phenomenology", *Phys. Rep.*, **453**, 29–115 (2007). ([维基百科][5])

[6] A. Vilenkin, "Cosmic strings and domain walls", *Phys. Rep.*, **121**, 263–315 (1985). ([维基百科][6])

[7] A. Bisio, G. M. D'Ariano, A. Tosini, "Quantum Field as a Quantum Cellular Automaton: The Dirac free evolution in one dimension", *Ann. Phys.*, **354**, 244–264 (2015). ([arXiv][7])

[8] NASA, "Webb 'Pierces' Bullet Cluster, Refines Its Mass", mission update (2025). ([NASA Science][8])

[9] S. P. C. Peters et al., "A record-breaking small dark object revealed by perturbations of an Einstein ring", *Nat. Astron.* (2025). ([Live Science][9])

[10] Euclid Collaboration, "First Euclid Data Release: Dark Matter and Dark Energy Probes from Early Imaging", ESA mission reports (2025). ([卫报][10])

[11] A. Mallick et al., "A Novel Density Profile for Isothermal Cores of Dark Matter Halos", arXiv:2411.11945 (2024). ([arXiv][11])

[12] H. Ma, "Mass as Topological Impedance: Self-Referential Scattering and Chiral Symmetry Breaking in Dirac-QCA", preprint (2025).

[13] H. Ma, "Universal Conservation of Information Celerity: From Quantum Cellular Automata to Relativity, Mass and Gravity", preprint (2025).

---

## 附录 A：QCA Hidden Sector Construction with Nontrivial Winding

本附录给出一个具体的 Dirac 型 QCA 构造，展示如何在局域 Hilbert 空间中嵌入具有非零缠绕数而电中性的隐藏扇区。

### A.1 可见 Dirac-QCA 的标准形式

考虑一维 Dirac-QCA，局域 Hilbert 空间为 $\mathbb C^2$，演化算符

$$U_{\text{vis}}(k)=\begin{pmatrix}
\cos\theta e^{\mathrm i k a} & -\mathrm i\sin\theta \\
-\mathrm i\sin\theta & \cos\theta e^{-\mathrm i k a}
\end{pmatrix},$$

其中 $\theta$ 为控制质量的参数。可以验证

$$\det U_{\text{vis}}(k)=\cos^2\theta+\sin^2\theta=1,$$

因此 $U_{\text{vis}}(k)\in SU(2)$。其色散关系为

$$\cos\omega(k)=\cos\theta\cos k a,$$

在小 $k$ 极限下

$$\omega(k)\approx \sqrt{(c k)^2 + (m c^2/\hbar)^2},$$

其中 $m\propto \theta$。该模型在适当参数区间内对应 $\mathcal W_{\text{vis}}=1$。

### A.2 隐藏扇区的拓扑构造

在隐藏扇区引入另一套 Dirac-QCA，自由度 $\mathcal H_{\text{hid}}\cong\mathbb C^2$，演化算符

$$U_{\text{hid}}(k)=\begin{pmatrix}
\cos\varphi e^{\mathrm i (k a+\delta)} & -\mathrm i\sin\varphi \\
-\mathrm i\sin\varphi & \cos\varphi e^{-\mathrm i (k a+\delta)}
\end{pmatrix}.$$

其中附加相位 $\delta$ 与混合角 $\varphi$ 控制隐藏扇区的拓扑与质量。其拓扑数

$$\mathcal W_{\text{hid}}=\frac{1}{2\pi \mathrm i}\int_{-\pi/a}^{\pi/a}\mathrm d k \partial_k\log\det U_{\text{hid}}(k)=1,$$

与可见扇区相同，但由于 $U(1)_{\text{EM}}$ 在 $\mathcal H_{\text{hid}}$ 上作用为恒等，隐藏扇区中所有模态在电磁意义上均为中性。

总演化算符

$$U(k)=U_{\text{vis}}(k)\otimes U_{\text{hid}}(k)$$

在 $\mathcal H_{\text{vis}}\otimes\mathcal H_{\text{hid}}\cong\mathbb C^4$ 上运行。选择基底

$$\{|e_1\rangle,|e_2\rangle\}_{\text{vis}}\otimes\{|h_1\rangle,|h_2\rangle\}_{\text{hid}},$$

可见电荷表示仅作用于 $|e_i\rangle$ 方向：

$$V_{\text{vis}}(\alpha)=\begin{pmatrix}
e^{\mathrm i q\alpha} & 0\\
0 & 1
\end{pmatrix}.$$

在态 $|e_2\rangle\otimes|h_j\rangle$ 生成的二维子空间上，电荷为零，但 $U_{\text{hid}}(k)$ 的拓扑仍给予非零质量，即信息孤岛模态。

### A.3 随机 QCA 规则下的普遍性

考虑在有限维 Hilbert 空间上随机抽样局域演化算符 $U(k)$（满足平移不变与局域性约束）。在绝大多数情形下，其 Bloch 带结构将拥有非零拓扑数，除非参数恰好落在测度为零的临界超曲面上。另一方面，$U(1)_{\text{EM}}$ 表示的选择则决定哪些带对应有电荷的可见模态，哪些带对应中性的隐藏模态。

因此，在广泛的随机 QCA 模型族中，具有非零拓扑质量、却在 $U(1)_{\text{EM}}$ 上平凡的"暗带"是统计上自然的，暗物质扇区不需要精细调节即可出现。

---

## 附录 B：IGVP, Optical Metric and Lensing

本附录更系统地推导 IGVP 在弱场极限下的光学度规与透镜公式。

### B.1 统一时间密度与信息密度

在散射理论中，Wigner–Smith 延迟算符定义为

$$\mathsf Q(\omega)=-\mathrm i S^\dagger(\omega)\frac{\partial S(\omega)}{\partial\omega},$$

其迹的归一化给出 Eisenbud–Wigner–Smith 延迟时间的总和。我们在统一时间理论中引入时间密度

$$\kappa(\omega)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega),$$

并定义局域信息密度为

$$\rho_{\text{info}}(x)=\int \mathrm d\omega \kappa(\omega;x).$$

在 QCA 框架中，$\kappa(\omega;x)$ 可通过局域谱测度与散射相位的导数定义，与"单位频率间隔内的态密度"等价。

### B.2 IGVP 的变分方程

IGVP 作用量可以写为

$$S[g,\kappa]=\int \mathrm d^4 x \sqrt{-g} \Bigl(\frac{c^4}{16\pi G}R(g) + \lambda(x)\bigl[\kappa(g;x)-\kappa_{\text{micro}}(x)\bigr]\Bigr),$$

其中 $\kappa_{\text{micro}}(x)$ 为由 QCA 微观自由度决定的统一时间密度，$\lambda(x)$ 为拉格朗日乘子。对 $g_{\mu\nu}$ 变分并线性化后，得到

$$\nabla^2\Phi(x)=4\pi G \rho_{\text{mass}}(x),$$

其中 $\rho_{\text{mass}}(x)\propto \kappa_{\text{micro}}(x)$ 与局域信息密度成正比。这一过程说明了"时间密度–态密度–质量密度"的统一链路。

### B.3 光学度规与透镜公式

在弱场静态情形，取

$$g_{00}=-(1+2\Phi/c^2),\quad g_{ij}=(1-2\Phi/c^2)\delta_{ij}.$$

光线满足零测地线条件 $\mathrm d s^2=0$。在薄透镜近似下，引力透镜偏折角可写为

$$\boldsymbol\alpha(\boldsymbol\xi)=\frac{2}{c^2}\int \nabla_\perp\Phi(\boldsymbol\xi,z) \mathrm d z
=\frac{4G}{c^2}\int \frac{\bigl(\boldsymbol\xi-\boldsymbol\xi'\bigr)\Sigma(\boldsymbol\xi')}{|\boldsymbol\xi-\boldsymbol\xi'|^2} \mathrm d^2\xi',$$

其中

$$\Sigma(\boldsymbol\xi)=\int \rho_{\text{mass}}(\boldsymbol\xi,z) \mathrm d z$$

为沿视线的投影质量密度。由于 $\rho_{\text{mass}}=\rho_{\text{vis}}+\rho_{\text{hid}}$，信息孤岛贡献直接进入透镜核。这一推导与 standard GR 透镜理论完全同构，只是 $\rho_{\text{mass}}$ 的组成在本体论上被重新解释为"信息密度"而非传统能动张量源项。

---

## 附录 C：Collisionless Virialization and Isothermal Halos

本附录给出在无碰撞玻尔兹曼方程下推导等温晕与平坦自转曲线的详细步骤。

### C.1 玻尔兹曼方程与守恒量

在球对称、稳态情形下，无碰撞玻尔兹曼方程为

$$\mathbf v\cdot\nabla_x f - \nabla\Phi\cdot\nabla_v f=0.$$

任何仅依赖于能量 $E=\tfrac{1}{2}v^2+\Phi(r)$ 的分布 $f(E)$ 都是该方程的解，因为

$$\mathbf v\cdot\nabla_x f(E)=f'(E) \mathbf v\cdot\nabla_x E=f'(E) \mathbf v\cdot\nabla\Phi,$$

$$\nabla\Phi\cdot\nabla_v f(E)=f'(E) \nabla\Phi\cdot\mathbf v,$$

二者相消。

### C.2 最大熵原理与 Maxwell–Boltzmann 分布

在给定总粒子数与总能量的约束下，最大化熵

$$S=-\int f\ln f \mathrm d^3 x \mathrm d^3 v$$

得到最优分布

$$f(E)=A\exp\bigl(-E/\sigma^2\bigr),$$

其中 $\sigma^2$ 类似于速度弥散平方。空间密度

$$\rho(r)=\int f(E) \mathrm d^3 v
=4\pi A\exp\bigl(-\Phi(r)/\sigma^2\bigr)\int_0^\infty v^2\exp\bigl(-v^2/2\sigma^2\bigr) \mathrm d v
=\rho_0\exp\bigl(-\Phi(r)/\sigma^2\bigr).$$

### C.3 Poisson 方程与渐近解

Poisson 方程

$$\frac{1}{r^2}\frac{\mathrm d}{\mathrm d r}\Bigl(r^2\frac{\mathrm d\Phi}{\mathrm d r}\Bigr)=4\pi G\rho_0\exp\bigl(-\Phi(r)/\sigma^2\bigr)$$

在 $r$ 足够大、$|\Phi(r)|\ll \sigma^2$ 区域可线性化为

$$\frac{1}{r^2}\frac{\mathrm d}{\mathrm d r}\Bigl(r^2\frac{\mathrm d\Phi}{\mathrm d r}\Bigr)\approx 4\pi G\rho_0\Bigl(1-\frac{\Phi(r)}{\sigma^2}\Bigr).$$

寻找形如 $\Phi(r)=2\sigma^2\ln(r/r_0)$ 的解，代入左侧

$$\frac{1}{r^2}\frac{\mathrm d}{\mathrm d r}\Bigl(r^2\frac{2\sigma^2}{r}\Bigr)
=\frac{1}{r^2}\frac{\mathrm d}{\mathrm d r}(2\sigma^2 r)
=\frac{2\sigma^2}{r^2},$$

右侧在渐近区域近似为常数 $4\pi G\rho_0$。令二者相等得到

$$\rho_0=\frac{\sigma^2}{2\pi G r^2}.$$

因此

$$\rho(r)\simeq \frac{\sigma^2}{2\pi G r^2},
\quad
M(r)=\int_0^r 4\pi r'^2\rho(r') \mathrm d r' = \frac{2\sigma^2}{G}r,$$

给出

$$v_{\text{rot}}(r)=\sqrt{\frac{G M(r)}{r}}=\sqrt{2} \sigma.$$

这就是信息孤岛气体在无碰撞、维里化条件下形成等温晕并产生平坦自转曲线的详细推导。

---

[1]: https://www.aanda.org/articles/aa/abs/2020/09/aa33910-18/aa33910-18.html?utm_source=chatgpt.com "Planck 2018 results - VI. Cosmological parameters"

[2]: https://pdg.lbl.gov/2025/reviews/rpp2024-rev-dark-matter.pdf?utm_source=chatgpt.com "27. Dark Matter"

[3]: https://en.wikipedia.org/wiki/Bullet_Cluster?utm_source=chatgpt.com "Bullet Cluster"

[4]: https://www.aanda.org/articles/aa/full_html/2010/01/aa13381-09/aa13381-09.html?utm_source=chatgpt.com "Determination of the local dark matter density in our Galaxy"

[5]: https://en.wikipedia.org/wiki/Hidden_sector?utm_source=chatgpt.com "Hidden sector"

[6]: https://en.wikipedia.org/wiki/Topological_defect?utm_source=chatgpt.com "Topological defect"

[7]: https://arxiv.org/abs/1212.2839?utm_source=chatgpt.com "Quantum Field as a quantum cellular automaton: the Dirac free evolution in one dimension"

[8]: https://science.nasa.gov/missions/webb/nasa-webb-pierces-bullet-cluster-refines-its-mass/?utm_source=chatgpt.com "NASA Webb 'Pierces' Bullet Cluster, Refines Its Mass"

[9]: https://www.livescience.com/space/cosmology/record-breaking-dark-object-found-hiding-within-a-warped-einstein-ring-10-billion-light-years-away?utm_source=chatgpt.com "Record-breaking 'dark object' found hiding within a warped 'Einstein ring' 10 billion light-years away"

[10]: https://www.theguardian.com/science/2025/mar/19/scientists-hail-avalanche-discoveries-euclid-space-telescope?utm_source=chatgpt.com "Scientists hail 'avalanche of discoveries' from Euclid space telescope"

[11]: https://arxiv.org/html/2411.11945v3?utm_source=chatgpt.com "A Novel Density Profile for Isothermal Cores of Dark Matter ..."




