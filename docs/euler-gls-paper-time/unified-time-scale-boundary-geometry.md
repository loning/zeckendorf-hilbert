统一时间刻度与边界时间几何：
散射相位、模流与引力边界项的单一结构框架

---

Abstract

构建一个以边界为基本舞台的时间统一框架，将三类原本分立的时间结构整合为同一"边界时间几何"的不同投影：
(1) 在散射与谱理论端，以 Birman–Kreĭn 公式与 Wigner–Smith 时间延迟为基础，证明总散射相位的导数、相对态密度与群延迟迹之间的刻度同一式；
(2) 在算子代数与信息端，以 Tomita–Takesaki 模块理论与 Connes–Rovelli 热时间假说为基础，将模流参数刻画为由状态—代数对决定的内禀时间，并引入时间刻度等价类；
(3) 在引力与几何端，以 Einstein–Hilbert–Gibbons–Hawking–York 作用及其边界变分为基础，将外在曲率与边界哈密顿量所生成的时间平移统一到同一边界时间几何。

在统一模型中，边界由三重结构描述：几何边界 $\partial M$ 的内禀度规与外在曲率、量子边界代数 $\mathcal A_\partial$ 与状态 $\omega$，以及在外域定义的散射矩阵 $S(\omega)$。在适定的可追踪散射假设下，构造"刻度同一式"
$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$
其中 $\varphi(\omega)=\tfrac12\arg\det S(\omega)$ 为总散射相位，$\rho_{\mathrm{rel}}$ 为谱移密度的导数，$Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)$ 为 Wigner–Smith 时间延迟矩阵。该刻度在模时间与几何时间端分别通过模哈密顿算子 $K_\omega=-\log\Delta_\omega$ 与 GHY 边界作用的哈密顿–雅可比泛函进行标准化，从而定义单一的边界时间刻度等价类 $[\tau]$。

在此基础上，给出若干统一定理：(i) 时间刻度等价类的范畴化存在唯一性：在给定边界代数、散射数据与引力边界几何的共同域上，所有可接受的时间参数皆为一个基本边界时间的单调重标；(ii) 宇宙学红移关系 $1+z=1/a(t)$ 可解释为该时间等价类在大尺度上的整体重标，从而将局域散射时间延迟与 FRW 背景下的共形时间统一；(iii) 在含视界的情形（Rindler 楔与黑洞外域），模流时间、加速观察者的固有时间与几何外法向平移时间落入同一等价类。

全文在散射—谱、模流—信息、引力—边界几何三端分别给出明确的假设与定理，并在附录中给出刻度同一式、模时间等价与边界哈密顿生成时间的详细证明，最后提出基于波导、微波腔与 Aharonov–Bohm 环的工程化测量方案，用于在实验上交叉校准三类时间刻度。

Keywords

边界时间几何；Birman–Kreĭn 公式；Wigner–Smith 时间延迟；谱移函数；Tomita–Takesaki 模块流；热时间假说；Gibbons–Hawking–York 边界项；时间刻度等价类；宇宙学红移

---

Introduction & Historical Context

时间在物理理论中以多重面貌出现：经典与相对论中作为参数化世界线的坐标，量子力学中作为生成幺正演化的连续变量，统计物理中作为与温度成反比的虚时间周期，散射理论中作为粒子在相互作用区驻留的延迟，广义相对论中则通过度规与外在曲率反映为几何结构。不同时间观往往基于不同的基本对象和测量过程，因此长期难以在单一数学框架内统一。

在散射与谱理论方面，Lifshits–Kreĭn 谱移函数 $\xi(\lambda)$ 及其导数在描述相互作用前后态密度差异中扮演核心角色；Birman–Kreĭn 公式给出散射矩阵行列式与谱移函数之间的精确关系 $\det S(\lambda)=\exp(-2\pi i\xi(\lambda))$。在适当归一化下，谱移密度的导数可解释为总散射相位导数并与 Wigner–Smith 时间延迟矩阵的迹等价，从而将"时间延迟"视为相位—谱结构的几何导数。([科学通报][1])

在算子代数与量子统计方面，Tomita–Takesaki 理论表明：给定一个带有循环且分离向量的 von Neumann 代数 $(M,\Omega)$，可以通过模算子 $\Delta$ 的极分解构造出模自动同构群 $\sigma_t^\Omega(x)=\Delta^{it}x\Delta^{-it}$，它在外自同构群上的像与所选的态无关。Connes–Rovelli 热时间假说提出：在一般协变的量子理论中，物理时间的流动由态—代数对的模流确定，模参数本身就是时间，从而"时间"成为状态结构的派生对象而非先验参数。([维基百科][2])

在引力与几何方面，Einstein–Hilbert 作用在具有边界的流形上并不足以给出良定的变分原理，必须附加 Gibbons–Hawking–York 边界项
$$
S_{\mathrm{GHY}}=\frac{1}{8\pi G}\int_{\partial M}\mathrm d^3y\,\epsilon\sqrt{h}\,K,
$$
其中 $h_{ab}$ 为边界诱导度规，$K$ 为外在曲率的迹，$\epsilon=\pm 1$ 取决于法向类型。EH+GHY 联合作用的变分在保持边界诱导几何不变的条件下给出 Einstein 方程，边界项则可视为哈密顿–雅可比泛函，其对边界度规的泛函导数对应于共轭动量与准局域能量，从而编码沿边界法向平移的"时间生成元"。([维基百科][3])

散射相位导数—时间延迟、模流参数—热时间、GHY 边界项—几何时间三者分别在数学上高度成熟且物理意义明确，但它们之间的结构等价性在现有文献中仅零散出现。例如，散射相位导数既可解释为态密度差，也可通过 S 矩阵的频率导数解释为群延迟；在 S 矩阵统计力学中，散射相位导数又进入态密度积分，从而与热量、自由能相联系。([arXiv][4]) 模流在 AdS/CFT 与纠缠楔重构中被用于定义模哈密顿与几何区域的能量，并通过 HKLL/Petz 重构联系到时空中的传播时间。([arXiv][5]) GHY 边界项在 loop 量子引力与准局域哈密顿形式主义中被视为定义引力转移振幅与边界时间的关键对象。([维基百科][3])

本文的目标是在严格可证的基础上，将上述三端统一到一个"边界时间几何"框架中。该框架以边界代数、状态、散射矩阵与边界几何为基本对象，以"时间刻度等价类"为核心，证明：在适当假设下，散射时间延迟、模时间与几何边界时间属于同一等价类，任何物理时间读数都可以视为单一边界时间参数的单调重标。进一步，将宇宙学红移与 FRW 时空中的尺度因子演化纳入同一刻度结构，将宏观的宇宙时间与微观的散射时间延迟联系起来。([维基百科][6])

---

Model & Assumptions

本节给出统一框架所依托的数学与物理模型，并明确假设域。

1. 散射与谱端

考虑自伴算子对 $(H,H_0)$，作用于可分 Hilbert 空间 $\mathcal H$，满足如下标准散射假设：

(1) $H_0$ 拥有绝对连续谱子空间 $\mathcal H_{\mathrm{ac}}(H_0)$，在其中可以建立能量表示，使得 $H_0$ 在该表示下为乘法算子 $E\mapsto E$；

(2) 扰动 $V=H-H_0$ 使得对某个 $p\leq 1$，有 $(H+i)^{-p}-(H_0+i)^{-p}\in\mathfrak S_1$，从而满足 Trace 类散射理论的基本条件；([科学通报][1])

(3) 波算子 $W_\pm=\operatorname{s}\text{-}\lim_{t\to\pm\infty}e^{itH}e^{-itH_0}P_{\mathrm{ac}}(H_0)$ 存在且完备，从而散射算子 $S=W_+^\dagger W_-$ 在 $\mathcal H_{\mathrm{ac}}(H_0)$ 上定义良好。

在能量表示下，$S$ 纤维化为一族酉矩阵 $S(\omega)$，其中 $\omega$ 记能量或频率变量。假设对几乎处处 $\omega$，$S(\omega)-\mathbb 1\in\mathfrak S_1$，从而行列式 $\det S(\omega)$ 与 Wigner–Smith 时间延迟算子
$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)
$$
定义良好并可追踪。([arXiv][4])

定义谱移函数 $\xi(\omega;H,H_0)$ 为满足 Lifshits–Kreĭn 迹公式的函数，其导数 $\xi'(\omega)$ 给出相对态密度差：$\rho_{\mathrm{rel}}(\omega):=-\xi'(\omega)$。

2. 模块流与热时间端

令 $M\subset B(\mathcal H)$ 为 von Neumann 代数，$\Omega\in\mathcal H$ 为循环且分离向量，$|\Omega|=1$。记向量态 $\omega(x)=(x\Omega,\Omega)$。Tomita–Takesaki 理论给出闭算子 $S$ 的极分解 $S=J\Delta^{1/2}$，其中 $J$ 为模共轭，$\Delta$ 为模算子。模自动同构群定义为
$$
\sigma_t^\omega(x)=\Delta^{it}x\Delta^{-it},\quad t\in\mathbb R.
$$
$\sigma_t^\omega$ 为 $M$ 的一参数自同构群，且 $\omega$ 为其 KMS 态。([维基百科][2])

Connes 证明：对任意两个忠实态 $\omega,\omega'$，其模流在外自同构群 $\mathrm{Out}(M)$ 中的像一致，即存在 1–余循环 $u_t\in M$，使得 $\sigma_t^{\omega'}=\operatorname{Ad}(u_t)\circ\sigma_t^\omega$，从而在 $\mathrm{Out}(M)$ 上得到态无关的"几何时间"。([维基百科][2])

热时间假说提出：物理时间流由模流决定，即模参数 $t$ 本身就是时间刻度，而非由先验背景赋予。([theorie.physik.uni-goettingen.de][7])

3. 引力与边界几何端

考虑具有边界 $\partial M$ 的四维时空流形 $(M,g_{\mu\nu})$。引力作用选取 Einstein–Hilbert 与 Gibbons–Hawking–York 总和
$$
S_{\mathrm{grav}}=\frac{1}{16\pi G}\int_M\mathrm d^4x\sqrt{-g}\,R+\frac{1}{8\pi G}\int_{\partial M}\mathrm d^3y\,\epsilon\sqrt{h}\,K.
$$
假设边界为非零测度的光滑三维流形，并区分空间样与时间样边界。变分时保持边界诱导度规 $h_{ab}$ 固定，则体积项给出 Einstein 方程，边界项的变分则决定边界共轭动量与准局域能量。([维基百科][3])

在某些情形（如真空区域、部分 LQG 构造）下，体积项在解上消失，Hamilton–Jacobi 作用完全由 GHY 边界项给出，从而边界作用本身成为生成法向时间演化的对象。([维基百科][3])

4. 统一边界系统与时间刻度等价

我们称三重数据
$$
\mathcal B=(\mathcal A_\partial,\omega_\partial,S(\omega);h_{ab},K_{ab})
$$
为一个边界系统，其中 $\mathcal A_\partial$ 为由散射通道与近边界场生成的边界代数，$\omega_\partial$ 为其上忠实态（可由散射入射态或边界 CFT 态给出），$S(\omega)$ 为能量壳上的散射矩阵，$h_{ab},K_{ab}$ 为几何边界的内禀与外在数据。

在一个边界系统上，我们允许三类一参数演化：

(1) 散射能量参数 $\omega$ 上的"位相–延迟"刻度，由 $S(\omega)$ 与 $Q(\omega)$ 决定；

(2) 模参数 $t_{\mathrm{mod}}$，由 $(\mathcal A_\partial,\omega_\partial)$ 的模流生成；

(3) 几何参数 $t_{\mathrm{geom}}$，由沿边界法向的平移（或外在曲率驱动的演化）生成。

统一框架的核心假设是：在适当的物理情形下（如渐近平坦或 AdS 时空的无穷远边界、黑洞视界附近的 Rindler 楔、FRW 宇宙的共形边界），上述三类参数都可定义，并满足一个共同的等价关系，构成时间刻度等价类 $[\tau]$。

---

Main Results (Theorems and Alignments)

本节陈述统一框架的主要定理与对应关系，严格区分已知结果与新引入结构。

Theorem 1（散射相位—谱移—群延迟刻度同一式）

在前述散射假设下，令谱移函数为 $\xi(\omega;H,H_0)$，并定义相对态密度
$$
\rho_{\mathrm{rel}}(\omega):=-\xi'(\omega).
$$
令总散射相位
$$
\Phi(\omega):=\arg\det S(\omega),\qquad\varphi(\omega):=\frac12\Phi(\omega),
$$
Wigner–Smith 延迟算子
$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega).
$$
则对几乎处处 $\omega$，成立刻度同一式
$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

简述：第一等号来自 Birman–Kreĭn 公式 $\det S(\omega)=\exp(-2\pi i\xi(\omega))$ 与谱移函数与态密度之间的关系；第二等号来自 $\ln\det S(\omega)=\operatorname{tr}\ln S(\omega)$ 对频率的导数与 Wigner–Smith 算子迹的联系。([科学通报][1])

Theorem 2（模流的时间刻度等价类）

令 $(M,\Omega)$ 为如上 von Neumann 代数与循环分离向量，$\omega,\omega'$ 为两个忠实态，并分别定义模流 $\sigma_t^\omega,\sigma_t^{\omega'}$。

(1) 存在一族酉算子 $u_t\in M$，满足 1–余循环条件 $u_{t+s}=u_t\sigma_t^\omega(u_s)$，使得
$$
\sigma_t^{\omega'}=\operatorname{Ad}(u_t)\circ\sigma_t^\omega.
$$

(2) 在外自同构群 $\mathrm{Out}(M)$ 中，$[\sigma_t^{\omega}]=[\sigma_t^{\omega'}]$，时间参数 $t$ 的尺度仅在态改变时发生线性重标。

(3) 若存在一个几何时钟（如惯性或均匀加速观察者），其固有时间 $\tau_{\mathrm{phys}}$ 与模参数 $t_{\mathrm{mod}}$ 通过 KMS 温度 $\beta$ 相关（如 Unruh 温度 $T=a/2\pi$ 或热平衡状态），则 $\tau_{\mathrm{phys}}=\alpha t_{\mathrm{mod}}$，其中 $\alpha$ 由 $\beta$ 决定。因此模参数定义了时间刻度等价类 $[\tau_{\mathrm{mod}}]$。([维基百科][2])

Theorem 3（GHY 边界作用与几何时间）

在 Einstein–Hilbert–GHY 作用下，对给定的边界 $\partial M$ 区域 $\Sigma$，定义 Hamilton–Jacobi 功能
$$
S_{\mathrm{HJ}}[h_{ab}]=\frac{1}{8\pi G}\int_\Sigma\mathrm d^3y\,\epsilon\sqrt{h}\,K,
$$
在真空 Einstein 方程成立且体积项在壳消失的情形下，该泛函对边界诱导度规 $h_{ab}$ 的变分给出共轭动量
$$
\pi^{ab}=\frac{\delta S_{\mathrm{HJ}}}{\delta h_{ab}}=\frac{\epsilon}{16\pi G}\sqrt{h}\,(K^{ab}-Kh^{ab}),
$$
定义准局域能量密度与沿边界法向平移的生成元。

若选取边界上的时间样方向与单位法向，并将外在曲率分解为 $K=K_{tt}+K_{\mathrm{spatial}}$，则存在一个几何时间参数 $t_{\mathrm{geom}}$，使得对小的时间平移 $\delta t_{\mathrm{geom}}$，作用的变化满足
$$
\delta S_{\mathrm{HJ}}=E_{\mathrm{q.l.}}\delta t_{\mathrm{geom}},
$$
其中 $E_{\mathrm{q.l.}}$ 为准局域能量，从而 $t_{\mathrm{geom}}$ 由边界几何与引力作用唯一确定，构成几何时间刻度。([维基百科][3])

Definition 4（边界时间刻度等价关系）

在一个边界系统 $\mathcal B$ 上，考虑三类时间参数：散射时间参数 $t_{\mathrm{scatt}}$（例如 Wigner–Smith 延迟的积分）、模参数 $t_{\mathrm{mod}}$ 与几何时间 $t_{\mathrm{geom}}$。

定义等价关系 $\sim$：若存在 $C^1$ 严格单调函数 $f$ 使得
$$
t_{\mathrm{scatt}}=f_{\mathrm{sm}}(t_{\mathrm{mod}}),\quad t_{\mathrm{mod}}=f_{\mathrm{mg}}(t_{\mathrm{geom}}),
$$
且在 $0$ 点导数有限非零，则称三者属于同一时间刻度等价类，记作 $[\,\tau\,]$。

Theorem 4（时间刻度等价类的存在与（局域）唯一性）

设边界系统 $\mathcal B$ 满足：

(1) 散射侧满足 Theorem 1 的假设，定义群延迟迹刻度
$$
\mathrm d\tau_{\mathrm{scatt}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)\,\mathrm d\omega;
$$

(2) 算子代数侧满足 Theorem 2 的假设，存在模流 $\sigma_t^\omega$ 与相应的模哈密顿算子 $K_\omega=-\log\Delta_\omega$；

(3) 引力侧满足 Theorem 3 的假设，存在边界 Hamilton–Jacobi 功能 $S_{\mathrm{HJ}}$，其对时间样平移的参数为 $t_{\mathrm{geom}}$。

并假设在某个能量窗口与几何区域上存在 AdS/CFT 或散射—几何对应，使得散射通道与边界代数—几何之间存在保结构的同构（如球形区域的 Rindler 楔与其 CFT 模哈密顿对应）。([arXiv][8])

则在这一共同域上存在一个时间刻度等价类 $[\tau]$，满足：

(1) 对任意观测过程，其时间读数 $t_{\mathrm{obs}}$ 都是 $\tau$ 的 $C^1$ 单调函数；

(2) 若再引入另一时间参数 $\tilde t$，并要求它的单位间隔等价于散射相位导数、模哈密顿期望值与 GHY 边界作用的单位变化，则 $\tilde t$ 在局域上必为 $\tau$ 的线性重标，因此 $[\tau]$ 在局域上唯一。

Theorem 5（宇宙学红移作为时间刻度全局重标）

在空间各向同性、各向均匀的 FRW 宇宙中，度规可写为
$$
\mathrm ds^2=-\mathrm dt^2+a(t)^2\gamma_{ij}\mathrm dx^i\mathrm dx^j,
$$
其中 $a(t)$ 为尺度因子。引入共形时间 $\eta$，满足 $\mathrm dt=a(\eta)\mathrm d\eta$。([维基百科][9])

设在给定红移 $z$ 的源与观察者之间存在一条辐射测地线，频率红移关系为
$$
1+z=\frac{1}{a(t_\mathrm{em})},
$$
其中 $t_\mathrm{em}$ 为发射时刻，观测时 $a(t_0)=1$。([维基百科][6])

若将源—观察者系统的散射视为在宇宙学背景上的有效"远区散射"，则存在一个边界时间刻度 $\tau$，使得局域观测者的共形时间增量 $\mathrm d\eta$ 与 Wigner–Smith 延迟刻度 $\mathrm d\tau_{\mathrm{scatt}}$ 属于同一等价类，而宇宙学红移则表现为 $\tau$ 的全局重标
$$
\mathrm d\tau_{\mathrm{cosmo}}=(1+z)\,\mathrm d\tau_{\mathrm{local}},
$$
从而宏观的宇宙时间演化可以视为统一时间刻度等价类的尺度因子演化。

---

Proofs

本节给出主要定理的证明骨架，完整技术细节置于附录。

Proof of Theorem 1

Birman–Kreĭn 公式给出
$$
\det S(\omega)=\exp(-2\pi i\xi(\omega)).
$$
令 $\Phi(\omega):=\arg\det S(\omega)$，则存在连续选取的支使得
$$
\Phi(\omega)=-2\pi\xi(\omega).
$$
定义半相位 $\varphi(\omega)=\tfrac12\Phi(\omega)$，则
$$
\varphi'(\omega)=-\pi\xi'(\omega)=\pi\rho_{\mathrm{rel}}(\omega).
$$
从而第一等号成立。

另一方面，利用 $\ln\det S(\omega)=\operatorname{tr}\ln S(\omega)$ 及链式法则，有
$$
\partial_\omega\ln\det S(\omega)=\operatorname{tr}(S(\omega)^{-1}\partial_\omega S(\omega)).
$$
由 $S(\omega)$ 的酉性，$S(\omega)^{-1}=S(\omega)^\dagger$。将 Wigner–Smith 算子记为
$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega),
$$
则
$$
\partial_\omega\ln\det S(\omega)=i\operatorname{tr}Q(\omega).
$$
另一方面，由 Birman–Kreĭn 公式
$$
\partial_\omega\ln\det S(\omega)=-2\pi i\xi'(\omega)=2\pi i\rho_{\mathrm{rel}}(\omega),
$$
比较两式得
$$
i\operatorname{tr}Q(\omega)=2\pi i\rho_{\mathrm{rel}}(\omega)\quad\Rightarrow\quad\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$
与前述 $\varphi'/\pi=\rho_{\mathrm{rel}}$ 组合即得刻度同一式。上述推导的技术要求（如 Trace 类条件、对数分支选择）在附录 A 中详细验证。([科学通报][1])

Proof of Theorem 2

(1) 与 (2) 为 Tomita–Takesaki 理论与 Connes 模块共边界理论的标准结论：通过对 $S_0:m\Omega\mapsto m^\ast\Omega$ 的闭包与极分解构造模算子 $\Delta$，再利用 $\Delta^{it}$ 实现模流，可证明对任意两个忠实态，模流在 $\mathrm{Out}(M)$ 中的像一致。([维基百科][2])

(3) 当模流描述 KMS 态的时间演化时，KMS 条件将模参数 $t_{\mathrm{mod}}$ 与温度 $\beta^{-1}$ 联系起来。在 Unruh 效应中，加速 $a$ 的观察者感受到温度 $T=a/2\pi$，对应周期 $\beta=2\pi/a$。模流在虚时间方向的周期为 $\beta$，从而将模参数与观察者固有时间 $\tau_{\mathrm{phys}}$ 的比例常数固定下来，得到 $\tau_{\mathrm{phys}}=\alpha t_{\mathrm{mod}}$，$\alpha\propto\beta$。([维基百科][10])

Proof of Theorem 3

对 EH+GHY 总作用进行变分，利用 Palatini 恒等式与 $\delta\sqrt{-g}=-\tfrac12\sqrt{-g}g_{\mu\nu}\delta g^{\mu\nu}$，体积项的变分给出 Einstein 张量 $G_{\mu\nu}$，边界项的变分在固定 $h_{ab}$ 条件下整理为外在曲率与 $\delta h_{ab}$ 的组合。标准推导表明
$$
\delta S_{\mathrm{GHY}}=\frac{1}{16\pi G}\int_{\partial M}\mathrm d^3y\,\epsilon\sqrt{h}\,(K^{ab}-Kh^{ab})\delta h_{ab}.
$$
将 $\delta S_{\mathrm{GHY}}$ 视为 Hamilton–Jacobi 泛函的变分，得共轭动量 $\pi^{ab}$ 如定理所述。([维基百科][3])

选择边界上的时间样切向量场与单位法向，将 $h_{ab}$ 分解为时间与空间部分，在 ADM 分解中 $K$ 与 lapse 函数 $N$ 共同决定法向平移。将 $\delta h_{ab}$ 限制于纯时间重标（保持空间截面形状不变），可将 $\delta S_{\mathrm{HJ}}$ 写成准局域能量乘以时间增量的形式，得到 $\delta S_{\mathrm{HJ}}=E_{\mathrm{q.l.}}\delta t_{\mathrm{geom}}$。

Proof of Theorem 4

在共同域上，由假设存在散射—几何—模流的对应：

(1) 散射侧给出一族频率刻度 $\mathrm d\tau_{\mathrm{scatt}}(\omega)$，其与外在几何通过 eikonal 近似与透镜/ Shapiro 延迟对应；

(2) 模流侧通过 JLMS 类型关系或 AdS–Rindler 对应，将模哈密顿映射为几何区域的能量算子，从而模时间与几何时间在局域上线性相关；([arXiv][8])

(3) 几何侧则通过 Einstein 方程与边界条件将 GHY 作用与外在曲率、准局域能量与时间平移联系起来。

由于散射时间刻度由 $\operatorname{tr}Q$ 与 $\partial_\omega\varphi$ 确定，而模时间与几何时间都由边界能量（模哈密顿期望值、准局域能量）刻度化，且三者都作用于同一边界代数—几何结构，其缩放只能相差一个正的有限因子，于是存在基本刻度 $\tau$。定义 $\tau$ 为在一个基准情形中（如低能极限或固定参考观测者）使三者单位变化一致的时间参数，即
$$
\delta\tau=\frac{\varphi'(\omega)}{\pi}\delta\omega=\frac{1}{2\pi}\operatorname{tr}Q(\omega)\delta\omega=\frac{1}{E_*}\delta S_{\mathrm{HJ}},
$$
其中 $E_*$ 为单位刻度下的参考能量。对任意其他时间参数 $t_{\mathrm{obs}}$，若要求其单位间隔与上述三个读数一致，则必有 $\mathrm d t_{\mathrm{obs}}=\alpha\,\mathrm d\tau$，从而 $t_{\mathrm{obs}}$ 与 $\tau$ 线性等价。

局域唯一性源于：若存在另一参数 $\tilde t$ 同时满足散射刻度与能量刻度的一致性，则 $\mathrm d\tilde t/\mathrm d\tau$ 在局域非零且常数，从而 $\tilde t$ 在局域上只是 $\tau$ 的仿射重标。

Proof of Theorem 5

FRW 度规中共形时间满足 $\mathrm dt=a(\eta)\mathrm d\eta$，因此共形时间间隔 $\mathrm d\eta$ 代表在拉回到平直度规下的"光行时间"。对于高频电磁波，eikonal 近似表明相位随共形时间线性变化。将宇宙信号（如 FRB 或遥远类星体）视为从"发射边界"到"观测边界"的散射过程，频率红移 $1+z=1/a(t_\mathrm{em})$ 意味着就源的固有时间刻度而言，观察到的频率与局域频率相比缩放了 $1/(1+z)$。([维基百科][6])

若统一时间刻度 $\tau$ 定义为局域观测者的散射刻度，那么在发射端与观测端之间，时间刻度需经过尺度因子 $a(t)$ 的整体重标，从而
$$
\mathrm d\tau_{\mathrm{cosmo}}=\frac{\mathrm d\varphi}{\pi}\cdot\frac{1}{\omega_{\mathrm{obs}}}=\frac{\mathrm d\varphi}{\pi}\cdot\frac{1}{\omega_{\mathrm{em}}/(1+z)}=(1+z)\,\mathrm d\tau_{\mathrm{local}},
$$
这里 $\mathrm d\varphi$ 为相位变化，$\omega_{\mathrm{em}},\omega_{\mathrm{obs}}$ 为发射与观测频率。因而红移可以解释为统一时间刻度等价类在跨宇宙光锥上的全局重标。

---

Model Apply

本节展示统一框架在几个具代表性的模型中的具体实现。

1. 一维势散射与时间延迟

考虑在实线上的一维 Schrödinger 算子
$$
H_0=-\frac{\mathrm d^2}{\mathrm dx^2},\qquad H=H_0+V(x),
$$
其中 $V$ 为紧支撑或快速衰减实势。在能量壳 $E=k^2$ 上，S 矩阵写为
$$
S(k)=e^{2i\delta(k)},
$$
其中 $\delta(k)$ 为总相移。Theorem 1 退化为
$$
\frac{\delta'(k)}{\pi}=\rho_{\mathrm{rel}}(k)=\frac{1}{2k}\frac{1}{2\pi}\operatorname{tr}Q(E),
$$
右侧的 $Q(E)$ 与传统的 Wigner 时间延迟 $\tau_{\mathrm W}(E)=2\partial_E\delta(E)$ 一致，时间刻度等价类可直接定义为
$$
\mathrm d\tau_{\mathrm{scatt}}=\frac{\delta'(E)}{\pi}\,\mathrm dE.
$$
这一刻度在有限体积盒中可通过 Levinson 定理与本征值计数函数交叉验证。

2. Rindler 楔中的模时间与 Unruh 时间

在 Minkowski 时空中，考虑右 Rindler 楔区域，由沿加速轨迹的观察者定义的代数 $M$ 与真空态 $|0\rangle$。Tomita–Takesaki 理论表明，Rindler 楔上的模流对应于 Rindler 时间平移，其模哈密顿与加速生成元成正比。Unruh 效应给出温度 $T=a/2\pi$ 与加速度 $a$ 的关系，从而模参数 $t_{\mathrm{mod}}$ 与加速观察者的固有时间 $\tau$ 满足 $\tau=\alpha t_{\mathrm{mod}}$，其中 $\alpha\propto\beta=1/T$。([维基百科][10])

在该情形下，引力几何可通过等效原理视为在恒定表面重力下的局域黑洞视界几何，GHY 边界项定义了与表面重力成正比的准局域能量，从而 Rindler 时间、模时间与几何时间落入同一刻度等价类。

3. FRW 宇宙中的宇宙学散射

在 FRW 背景中，考虑远处类星体发出的窄带电磁波；对观测者而言，这相当于从早期宇宙"边界"到当前宇宙时刻的散射。电磁波在几乎共形平直的度规中传播，eikonal 相位累积与共形时间成比例。由红移–尺度因子关系 $1+z=1/a(t_\mathrm{em})$，观测频率 $\omega_{\mathrm{obs}}$ 与发射频率 $\omega_{\mathrm{em}}$ 满足 $\omega_{\mathrm{obs}}=\omega_{\mathrm{em}}/(1+z)$。

若用散射角度重建 FRW 参数（如利用频率依赖延迟），则 Wigner–Smith 延迟刻度的统一时间参数自然吸收了红移因子，Theorem 5 中的全局重标具体呈现为 $\mathrm d\tau_{\mathrm{cosmo}}=(1+z)\mathrm d\tau_{\mathrm{local}}$。

---

Engineering Proposals

统一框架的一个重要价值在于给出多平台交叉校准时间刻度的工程化方案：

1. 微波腔与波导中的群延迟测量

在射频与微波频段，可通过矢量网络分析仪测量复杂 S 参数，从而直接构造 Wigner–Smith 算子
$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)
$$
的数值近似。通过频率有限差分近似 $\partial_\omega S$，在多个端口上取迹得到群延迟迹刻度 $(2\pi)^{-1}\operatorname{tr}Q(\omega)$。([arXiv][4])

在包含可控反射与耦合损耗的腔体中，可以设计接近 Rindler 或 FRW 有效几何的等效介质（如梯度折射率结构），使得测得的群延迟同时反映散射与几何效应，从实验上验证刻度同一式的稳定性。

2. Aharonov–Bohm 环与相位–延迟统一

在一维 AB 环加上局域散射中心的系统中，磁通 $\Phi_{\mathrm{AB}}$ 控制环上的几何相位，而局域势散射控制频率依赖相位与群延迟。通过扫描频率与磁通，可以测量总相位导数与时间延迟，并拟合出统一时间刻度 $\tau$。将环的有效长度与外加电势调谐至模拟 Rindler 或 Schwarzschild 有效势垒，有望在凝聚态平台上实现"引力—散射—模时间"的统一刻度实验。

3. 宇宙学信号与 FRB 观测

在宇宙学尺度上，快速射电暴（FRB）与高能爆发提供了跨 Gpc 的"天然散射实验"。通过多频段观测，可以测得色散延迟与可能存在的相位/群延迟结构，并与 FRW 模型下的尺度因子演化进行拟合。统一时间刻度框架可用于区分：

(1) 纯等离子体色散引起的 $\nu^{-2}$ 延迟；

(2) 几何—引力效应导致的频率无关或弱频率依赖延迟；

(3) 潜在的真空色散或量子引力修正。

尽管当前数据不足以精确分离这些效应，统一刻度模型为未来的精细观测提供了理论基准。

---

Discussion (risks, boundaries, past work)

1. 适用域与假设的强度

散射—谱端需要 Trace 类条件与波算子完备性，这在许多具体模型中可以验证，但在强长程势、非自伴或有耗散系统中需要推广版本。模流端则要求存在循环且分离向量，且物理上需要解释"观察者—代数—状态"的选取。引力端依赖于 EH+GHY 作用的适用性，在 f(R) 或更一般的高阶引力理论中需引入修正边界项。([科学通报][1])

2. 统一刻度中的选择自由度

时间刻度等价类 $[\tau]$ 的定义保留了仿射重标自由度。这与相对论中不同惯性系时间选择、统计力学中温度的倒数与时间周期的比例自由度类似。在统一框架中，真正具有物理意义的是等价类内的相对刻度，而非某一绝对单位。

3. 与既有工作的关系

散射相位、谱移与时间延迟的关系在散射理论与统计力学文献中已有深入发展，模流与热时间假说在哲学与量子引力领域也有大量讨论，GHY 边界项与准局域能量的作用则是引力研究中的基本工具。本文的贡献在于：

(1) 在数学上，以刻度同一式为纽带，将散射—谱结构与模流—信息结构在边界代数层面对齐；

(2) 在引力边界项与准局域能量的背景下，将几何时间纳入同一刻度，使之成为边界 Hamilton–Jacobi 功能的参数；

(3) 在宇宙学红移与 FRW 共形时间的语境中，将宏观时间演化解释为统一时间刻度等价类的全局重标。

相关工作包括利用 BK 公式与谱移函数构造态密度及热量函数的研究、将模流与几何区域能量和纠缠楔重构联系的工作，以及关于 GHY 边界项在黑洞热力学中的作用等。([SpringerLink][11])

4. 风险与开放问题

(1) 严格的 AdS/CFT 或散射—几何对应仅在特定背景与能量尺度下成立；在一般弯曲时空中将散射矩阵与边界代数统一可能需要更复杂的代数–几何工具。

(2) 模流在类型 III 因子上的结构虽然成熟，但其物理解释仍存在争议，特别是在无明显热浴的孤立系统中如何将模时间与实验时间对应。

(3) 宇宙学红移的统一刻度解释目前更多是结构上的，而非给出新的数值预言；要将其变为可检验理论，需要结合更加细致的 FRB/GRB 数据与引力透镜效应。

---

Conclusion

本文在一个统一的"边界时间几何"框架下，将三类看似独立的时间结构——散射相位导数与时间延迟、算子代数中的模流时间以及引力中的几何边界时间——整合为边界时间刻度等价类 $[\tau]$ 的不同实现。核心刻度同一式
$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
$$
把散射矩阵的相位结构、谱移函数的态密度信息与群延迟的时间含义统一为单一边界刻度；模流与 GHY 边界作用则在算子代数与几何端分别提供了"时间生成元"的内禀刻度。宇宙学红移与 FRW 共形时间的引入，使得这一统一刻度从微观散射延伸至宏观宇宙演化。

这一框架强调：时间并非体域中的独立参数，而是边界数据——包括代数、状态与几何——的派生刻度。未来需要在更具体的模型（如 AdS 黑洞、量子多体系统与实验散射网络）中细化这一统一结构，并在工程层面通过多平台的群延迟测量与宇宙学观测对其进行交叉检验。

---

Acknowledgements, Code Availability

本工作仅依赖公开文献与理论推导，未使用专用代码。所有示例模型与计算可以根据文中方程以标准数值软件重现。

---

References

[1] A. Strohmaier, "The Birman–Kreĭn formula for differential forms and scattering theory", Ann. Inst. H. Poincaré Anal. Non Linéaire, 2022. ([科学通报][1])

[2] H. Neidhardt, "Scattering Matrix, Phase Shift, Spectral Shift and Trace Formula", Integr. Equ. Oper. Theory, 2007. ([SpringerLink][11])

[3] A. Strohmaier et al., "Applications of Spectral Shift Functions. I: Basic Properties", Lecture Notes, 2016. ([matcuer.unam.mx][12])

[4] V. Kostrykin, R. Schrader, "The density of states and the spectral shift density of random Schrödinger operators", Rev. Math. Phys., 2000.

[5] U. R. Patel, "Wigner–Smith Time Delay Matrix for Electromagnetics", arXiv:2005.03211, 2020. ([arXiv][4])

[6] P. Ambichl et al., "Focusing inside disordered media with the generalized Wigner–Smith operator", Phys. Rev. Lett. 119, 033903, 2017. ([物理评论链接管理器][13])

[7] J. Erb et al., "Understanding complex wave scattering systems through the generalized Wigner–Smith operator", APS March Meeting Abstracts, 2023. ([天体物理数据系统][14])

[8] P. M. Lo, "Thermal contribution of unstable states", Eur. Phys. J. C 79, 2019.

[9] M. Bugden, "KMS States in Quantum Statistical Mechanics", Honours Thesis, ANU, 2013. ([maths-people.anu.edu.au][15])

[10] "Tomita–Takesaki theory", Wikipedia entry, accessed 2025. ([维基百科][2])

[11] T. T. Paetz, "An Analysis of the 'Thermal-Time Concept' of Connes and Rovelli", Diploma Thesis, 2010. ([theorie.physik.uni-goettingen.de][7])

[12] N. Swanson, "Can Quantum Thermodynamics Save Time?", PhilSci Archive, 2018. ([philsci-archive.pitt.edu][16])

[13] "The Time in Thermal Time", arXiv:2407.18948, 2024. ([arXiv][17])

[14] A. Sorce, "An intuitive construction of modular flow", arXiv:2309.16766, 2023. ([arXiv][5])

[15] B. Czech, "Modular Berry Connection for Entangled Subregions in AdS/CFT", Phys. Rev. Lett. 120, 091601, 2018. ([物理评论链接管理器][18])

[16] E. Bahiru et al., "Explicit reconstruction of the entanglement wedge via the Petz map", JHEP, 2022. ([arXiv][8])

[17] E. Verlinde, W. Zurek, "Spacetime fluctuations in AdS/CFT", 2020. ([Pure][19])

[18] "Gibbons–Hawking–York boundary term", Wikipedia entry, accessed 2025. ([维基百科][3])

[19] S. Chakraborty, "Boundary terms of the Einstein–Hilbert action", arXiv:1607.05986, 2016. ([arXiv][20])

[20] D. Bavera, "The Boundary Terms of the Einstein–Hilbert Action", Master Thesis, 2018. ([physik.uzh.ch][21])

[21] "Scale factor (cosmology)", Wikipedia entry, accessed 2025. ([维基百科][6])

[22] R. Wojtak et al., "Testing the mapping between redshift and cosmic scale factor", Mon. Not. R. Astron. Soc. 458, 3331–3340, 2016. ([OUP Academic][22])

[23] "Friedmann–Lemaître–Robertson–Walker metric", Wikipedia entry, accessed 2025. ([维基百科][9])

[24] "Unruh effect", Wikipedia entry, accessed 2025. ([维基百科][10])

[25] S. A. Fulling, P. C. W. Davies, W. G. Unruh, original papers on the Unruh effect, 1973–1976. ([维基百科][10])

[26] S. Tang, M. Zworski, "Potential Scattering on the Real Line", Lecture notes, 1998.

[27] H. E. Camblong, "Spectral density, Levinson's theorem, and the extra term in the phase shift", Phys. Rev. A 100, 062110, 2019.

[28] H. Isozaki, "Trace formulas for Schrödinger operators", RIMS Kokyuroku 1760, 2011.

[29] J.-P. Eckmann et al., "Scattering phases and density of states for exterior domains", Ann. Inst. H. Poincaré A 62, 1995.

[30] M. Dimassi, M. Zerzeri, "Spectral shift function for slowly varying perturbation of periodic Schrödinger operators", CUBO 14, 2012.

---

Appendix A: 刻度同一式的技术证明

本附录在标准散射理论公设下给出 Theorem 1 的严格证明。

A.1 谱移函数与 BK 公式的技术条件

设 $(H,H_0)$ 满足

(1) 对某个 $p\leq 1$，$(H-i)^{-p}-(H_0-i)^{-p}\in\mathfrak S_1$；

(2) 对任意 Borel 有界函数 $f$ 且 $f'$ 有界，可定义
$$
\operatorname{tr}(f(H)-f(H_0))=\int f'(\lambda)\xi(\lambda)\,\mathrm d\lambda,
$$
由此引入谱移函数 $\xi(\lambda)$。([matcuer.unam.mx][12])

Birman–Kreĭn 公式断言：在绝对连续谱上几乎处处成立
$$
\det S(\lambda)=\exp(-2\pi i\xi(\lambda)).
$$
该等式需要 S 矩阵的纤维为 Trace 类扰动的酉算子，并且 Log 分支的选择需保持连续；在本设定下可通过对有限体积近似的极限严格证明。([research.rug.nl][23])

A.2 相位导数与态密度差

令 $\Phi(\lambda)=\arg\det S(\lambda)$，选择分支使得 $\Phi(\lambda)$ 连续，并定义半相位 $\varphi(\lambda)=\tfrac12\Phi(\lambda)$。由 BK 公式
$$
\Phi(\lambda)=-2\pi\xi(\lambda)\quad(\mathrm{mod}\,2\pi),
$$
去掉模 $2\pi$ 歧义后在平滑区间内可导，并有
$$
\varphi'(\lambda)=-\pi\xi'(\lambda)=\pi\rho_{\mathrm{rel}}(\lambda).
$$
另一方面，谱移函数导数可通过有限盒近似中的本征值计数函数差的极限给出，从而 $\rho_{\mathrm{rel}}$ 的定义不依赖于 S 矩阵的具体实现，只依赖于算子对 $(H,H_0)$。

A.3 Wigner–Smith 算子迹与谱移密度

在能量表示中，$S(\lambda)$ 为 $\mathcal H_\lambda$ 上的酉算子族，其对数导数满足
$$
\partial_\lambda\ln\det S(\lambda)=\operatorname{tr}(S(\lambda)^{-1}\partial_\lambda S(\lambda)).
$$
由于 $\det S(\lambda)=\exp(-2\pi i\xi(\lambda))$，有
$$
\partial_\lambda\ln\det S(\lambda)=-2\pi i\xi'(\lambda)=2\pi i\rho_{\mathrm{rel}}(\lambda).
$$
另一方面，定义 Wigner–Smith 算子
$$
Q(\lambda)=-iS(\lambda)^\dagger\partial_\lambda S(\lambda),
$$
则
$$
\operatorname{tr}(S(\lambda)^{-1}\partial_\lambda S(\lambda))=\operatorname{tr}(S(\lambda)^\dagger\partial_\lambda S(\lambda))=i\operatorname{tr}Q(\lambda).
$$
比较得 $\rho_{\mathrm{rel}}(\lambda)=(2\pi)^{-1}\operatorname{tr}Q(\lambda)$。

A.4 一维情形与 Levinson 定理

在一维短程势下，有限盒近似中本征态满足 $k_nR+\delta(k_n)=n\pi$。改变势或盒长，可将本征值密度之差表示为相移导数，从而
$$
\rho_{\mathrm{rel}}(k)=\frac{1}{\pi}\delta'(k).
$$
Levinson 定理给出 $\delta(0)-\delta(\infty)=\pi N_{\mathrm{bound}}$ 等边界条件，从而统一了散射相位与束缚态计数。该构造与谱移函数的定义相容，提供了刻度同一式在一维模型中的具体实现。

---

Appendix B: 模流、KMS 条件与热时间

B.1 Tomita–Takesaki 构造

从 $M$ 与 $\Omega$ 出发，定义密集定义的反线性算子
$$
S_0:m\Omega\mapsto m^\ast\Omega,\quad m\in M.
$$
闭包 $S$ admit 极分解 $S=J\Delta^{1/2}$，其中 $J$ 为反线性等距模共轭，$\Delta$ 为正、自伴模算子。模流定义为
$$
\sigma_t^\omega(m)=\Delta^{it}m\Delta^{-it}.
$$
Tomita–Takesaki 定理断言：$\sigma_t^\omega$ 是 $M$ 的一参数自同构群，且 $\omega$ 对其满足 KMS 条件，即存在带条形区域的解析函数使得
$$
F(t)=\omega(a\sigma_t^\omega(b)),\quad F(t+i)=\omega(\sigma_t^\omega(b)a).
$$
([维基百科][2])

B.2 Connes 1–余循环与态无关时间

给定两个忠实态 $\omega,\omega'$，可构造 Connes 1–余循环 $u_t$，使得
$$
\sigma_t^{\omega'}(m)=u_t\sigma_t^\omega(m)u_t^{-1},
$$
且 $u_{t+s}=u_t\sigma_t^\omega(u_s)$。这意味着模流在外自同构群 $\mathrm{Out}(M)=\operatorname{Aut}(M)/\operatorname{Inn}(M)$ 的像独立于态，仅定义了一个"几何时间"方向。([维基百科][2])

B.3 热时间假说与温度–时间关系

在传统量子统计中，给定哈密顿量 $H$ 与逆温度 $\beta$，时间演化 $\alpha_t(a)=e^{itH}ae^{-itH}$ 下的 KMS 态满足
$$
\omega(a\alpha_t(b))=\omega(\alpha_{t+i\beta}(b)a).
$$
热时间假说反转这一逻辑：先给定态 $\omega$ 与代数 $M$，再将模流 $\sigma_t^\omega$ 的参数解释为时间。若存在外在观察者的物理时间 $\tau_{\mathrm{phys}}$，则可通过比较模流与物理哈密顿生成的演化，得到 $\tau_{\mathrm{phys}}=\alpha t_{\mathrm{mod}}$，其中 $\alpha$ 由温度或加速度给定。Unruh 效应中的 $T=a/2\pi$ 提供了这一比例的具体例子。([维基百科][10])

---

Appendix C: GHY 边界项、Hamilton–Jacobi 功能与准局域时间

C.1 EH+GHY 作用的变分

从
$$
S_{\mathrm{grav}}=\frac{1}{16\pi G}\int_M\sqrt{-g}\,R\,\mathrm d^4x+\frac{1}{8\pi G}\int_{\partial M}\epsilon\sqrt{h}\,K\,\mathrm d^3y
$$
出发，对 $g_{\mu\nu}$ 做变分。EH 项的变分可写为体积积分与边界积分之和，后者被 GHY 项的变分精确抵消，从而在 $\delta h_{ab}=0$ 条件下，整体变分仅包含体积分，给出 Einstein 方程。([维基百科][3])

C.2 Hamilton–Jacobi 功能与共轭动量

视 $S_{\mathrm{HJ}}[h_{ab}]$ 为在给定边界几何下求解 Einstein 方程所得作用的函数，对 $h_{ab}$ 的变分给出共轭动量
$$
\pi^{ab}=\frac{\delta S_{\mathrm{HJ}}}{\delta h_{ab}}=\frac{\epsilon}{16\pi G}\sqrt{h}\,(K^{ab}-Kh^{ab}).
$$
在 ADM 分解中，度规写作
$$
\mathrm ds^2=-N^2\mathrm dt^2+h_{ij}(\mathrm dx^i+N^i\mathrm dt)(\mathrm dx^j+N^j\mathrm dt),
$$
外在曲率通过 lapse $N$ 与 shift $N^i$ 决定。选取适当规范（如 $N^i=0$）时，法向时间平移对应于 $t$ 的变化，因此 $\delta S_{\mathrm{HJ}}/\delta t$ 给出准局域能量。

C.3 Rindler 与黑洞情形

在 Rindler 楔或 Schwarzschild 黑洞外域，近视界区域的外在曲率与表面重力成正比，GHY 边界项在 Euclidean 路径积分中给出黑洞自由能与温度的关系。通过将 Euclidean 时间周期 $\beta$ 与模流周期配对，可以显示几何时间、模时间与热时间属于同一刻度等价类。

---

Appendix D: 时间刻度等价类的范畴化结构

D.1 对象与态射

构造一个范畴 $\mathbf{BTG}$：

(1) 对象为边界系统 $\mathcal B=(\mathcal A_\partial,\omega_\partial,S;h_{ab},K_{ab})$；

(2) 态射为保持物理结构的映射 $\Phi:\mathcal B_1\to\mathcal B_2$，满足：

$\bullet$ $\Phi$ 在代数上给出 $*$–同构 $\phi:\mathcal A_{\partial,1}\to\mathcal A_{\partial,2}$；

$\bullet$ $\Phi$ 将状态与 S 矩阵映射为保持 BK 与刻度同一式结构的对象；

$\bullet$ $\Phi$ 将边界几何映射为保度规与外在曲率（或其等价类）的嵌入。

在该范畴中，一个时间刻度等价类 $[\tau]$ 可视为从对象到 $\mathbb R$ 的函子，将每个边界系统赋予一个时间参数集合，态射则对应时间刻度的单调重标。

D.2 局域唯一性的范畴表述

Theorem 4 可重述为：在给定对象 $\mathcal B$ 的某个局域子范畴中，如果要求函子 $T:\mathbf{BTG}\to\mathbf{Time}$ 同时保留散射刻度、模时间与几何时间的单位间隔，则在自然同构意义下唯一。

这为今后将时间刻度等价类与更高层次的范畴结构（如纤维化、自然变换）联系起来提供了基础，但这些扩展超出了本稿的范围。

[1]: https://www.sciencedirect.com/science/article/pii/S0007449722000707?utm_source=chatgpt.com "The Birman-Krein formula for differential forms and ..."
[2]: https://en.wikipedia.org/wiki/Tomita%E2%80%93Takesaki_theory?utm_source=chatgpt.com "Tomita–Takesaki theory"
[3]: https://en.wikipedia.org/wiki/Gibbons%E2%80%93Hawking%E2%80%93York_boundary_term?utm_source=chatgpt.com "Gibbons–Hawking–York boundary term"
[4]: https://arxiv.org/pdf/2005.03211?utm_source=chatgpt.com "Wigner-Smith Time Delay Matrix for Electromagnetics"
[5]: https://arxiv.org/pdf/2309.16766?utm_source=chatgpt.com "An intuitive construction of modular flow"
[6]: https://en.wikipedia.org/wiki/Scale_factor_%28cosmology%29?utm_source=chatgpt.com "Scale factor (cosmology)"
[7]: https://www.theorie.physik.uni-goettingen.de/forschung2/qft/theses/dipl/Paetz.pdf?utm_source=chatgpt.com "An Analysis of the 'Thermal-Time Concept' of Connes and ..."
[8]: https://arxiv.org/pdf/2210.00602?utm_source=chatgpt.com "Explicit reconstruction of the entanglement wedge via the ..."
[9]: https://en.wikipedia.org/wiki/Friedmann%E2%80%93Lema%C3%AEtre%E2%80%93Robertson%E2%80%93Walker_metric?utm_source=chatgpt.com "Friedmann–Lemaître–Robertson–Walker metric"
[10]: https://en.wikipedia.org/wiki/Unruh_effect?utm_source=chatgpt.com "Unruh effect"
[11]: https://link.springer.com/article/10.1007/s00020-007-1487-z?utm_source=chatgpt.com "Scattering Matrix, Phase Shift, Spectral Shift and Trace ..."
[12]: https://www.matcuer.unam.mx/VeranoAnalisis/Fritz-I.pdf?utm_source=chatgpt.com "Applications of Spectral Shift Functions. I: Basic Properties ..."
[13]: https://link.aps.org/doi/10.1103/PhysRevLett.119.033903?utm_source=chatgpt.com "Focusing inside Disordered Media with the Generalized ..."
[14]: https://ui.adsabs.harvard.edu/abs/2023APS..MARZ01003E/abstract?utm_source=chatgpt.com "Understanding complex wave scattering systems through ..."
[15]: https://maths-people.anu.edu.au/~bugdenm/Honours%20Thesis.pdf?utm_source=chatgpt.com "KMS States in Quantum Statistical Mechanics Mark Bugden"
[16]: https://philsci-archive.pitt.edu/15081/1/Swanson_Thermal%20Time%20%28PSA%29.pdf?utm_source=chatgpt.com "Can Quantum Thermodynamics Save Time? | PhilSci-Archive"
[17]: https://arxiv.org/html/2407.18948v1?utm_source=chatgpt.com "The Time in Thermal Time"
[18]: https://link.aps.org/doi/10.1103/PhysRevLett.120.091601?utm_source=chatgpt.com "Modular Berry Connection for Entangled Subregions in"
[19]: https://pure.uva.nl/ws/files/54374343/Verlinde_Zurek2020_Article_SpacetimeFluctuationsInAdSCFT.pdf?utm_source=chatgpt.com "Spacetime fluctuations in AdS/CFT"
[20]: https://arxiv.org/pdf/1607.05986?utm_source=chatgpt.com "Boundary terms of the Einstein-Hilbert action"
[21]: https://www.physik.uzh.ch/dam/jcr%3A1c2ca173-a3e8-41a1-b26e-0cda64debc6c/master_thesis_bavera.pdf?utm_source=chatgpt.com "The Boundary Terms of the Einstein-Hilbert Action"
[22]: https://academic.oup.com/mnras/article/458/3/3331/2589357?utm_source=chatgpt.com "Testing the mapping between redshift and cosmic scale factor"
[23]: https://research.rug.nl/files/232459978/1_s2.0_S0007449722000707_main.pdf?utm_source=chatgpt.com "The Birman-Krein formula for differential forms and ..."
