# 边界、观察者注意力与时间轴:广义熵测地线与截面宇宙的统一框架

---

## Abstract

构建一个以边界为基本舞台的时间与观察者统一框架。假定在无观察者读数的规范场状态下,时空与场的边界数据是确定的,但不存在优先的时间参数;时间只在观察者实施读数、其注意力选择一族边界截面时作为"测地线参数"出现。首先在散射理论端,以刻度同一式

$$
\varphi'(\omega)/\pi=\rho_{\rm rel}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)
$$

为基础,将可观测时间刻度定义为边界散射相位、相对谱密度与 Wigner–Smith 时间延迟迹的统一读数。其次在几何与引力端,以 Einstein–Hilbert–Gibbons–Hawking–York 作用的变分为基础,将边界视为"把法向通量转化为可读出量"的发生器,并以广义熵 $S_{\rm gen}$ 的极值与量子聚焦不等式刻画"广义熵测地线"。在此基础上引入"注意力截面"与"截面宇宙":观察者的注意力通过选择一族边界截面与可访问代数,生成一条由刻度同一式标定、由广义熵测地线选出的时间轴;不同观察者的时间轴对应于同一边界几何上的不同截面族,从而解释双缝干涉等现象中"观测改变图样"可视为"进入不同截面"的几何化表述。最后给出一系列可检验预言与工程提案,包括基于电磁散射网络的群延迟–广义熵对齐实验、基于类岛公式的黑洞信息读数、以及通过调整观测分辨率控制经典–量子过渡的双缝实验路径。

---

## Keywords

边界时间几何;注意力截面;广义熵测地线;Wigner–Smith 时间延迟;Gibbons–Hawking–York 边界项;量子极值面;Page–Wootters 关联时间;双缝干涉

---

## 1 Introduction & Historical Context

### 1.1 无观察者时间与边界优先性

在广义相对论与量子场论的标准表述中,时间常被视为预先给定的外参:广义相对论中为流形上的参数化测地线,量子理论中为生成幺正演化的参数。然而若考虑具有边界的引力作用,单纯的 Einstein–Hilbert 体作用不足以给出良定变分,必须加入 Gibbons–Hawking–York 边界项

$$
\mathcal S_{\rm GHY}=\frac{1}{8\pi}\int_{\partial\mathcal M}\epsilon\sqrt{h}\,K
$$

以消除法向导数贡献,使得在固定边界几何时变分良定。这一事实表明:在有边界的情形,边界并非被动的"终点",而是体域几何与动力学的生成条件。

在量子引力与全息研究中,广义熵

$$
S_{\rm gen}[\sigma]=\frac{{\rm Area}(\sigma)}{4G\hbar}+S_{\rm out}[\sigma]
$$

成为描述边界截面的基本量,其中 $\sigma$ 为共维二截面,$S_{\rm out}$ 为其外侧量子场熵。量子极值面(Quantum Extremal Surface, QES)由 $S_{\rm gen}$ 的驻点条件给出,是构造引力系统熵与岛公式的核心。与此平行,量子聚焦猜想(Quantum Focusing Conjecture, QFC)提出,沿着正交于 $\sigma$ 的任意零测地束,广义熵的"量子膨胀"单调不增,统一了 Bousso 光片界与经典聚焦定理,并蕴含量子零能条件。

这些结构共同指向一个观念:在无观察者读数的"规范场状态"下,边界几何与广义熵流动确是确定的,但并不存在优先的时间参数;一切只是"块宇宙"上的几何与熵函数。时间要成为"经验量",还需要一个额外输入:观察者及其读数。

### 1.2 散射刻度、相位与时间延迟

在散射理论中,Wigner–Smith 时间延迟矩阵

$$
Q(\omega)=-i\,S(\omega)^\dagger\partial_\omega S(\omega)
$$

描述入射态在频率 $\omega$ 处相对于自由传播的群延迟。其迹与总散射相位 $\Phi(\omega)=\arg\det S(\omega)$ 的导数及谱移函数之间存在刻度同一式

$$
\varphi'(\omega)/\pi=\rho_{\rm rel}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega),
$$

其中 $\varphi(\omega)=\tfrac12\Phi(\omega)$,$\rho_{\rm rel}$ 为 Kreĭn 谱移密度。该类关系最早由 Birman–Kreĭn 与 Lifshitz–Kreĭn 迹公式系统化,谱移函数的系统课程可见 Gesztesy 等人的综述。在电磁与波动系统中,Wigner–Smith 矩阵已在微波腔、随机介质中被直接计算与测量。

这类刻度同一式说明:对于给定的散射系统,可观测时间刻度在本质上由边界散射矩阵 $S(\omega)$ 决定,而非由体域某个预设的"绝对时间"变量决定。时间读数是边界谱数据的派生量。

### 1.3 关联时间与内部参考系

在量子时间问题中,Page–Wootters 机制提出:在一个满足约束 $\hat H_{\rm tot}|\Psi\rangle=0$ 的整体静态态 $|\Psi\rangle$ 中,若将某一子系统解释为"钟",则相对于钟指针结果的条件态可满足有效的演化方程,从而"时间"作为系统–钟之间相关性的参数出现。这一机制代表一种"内部参考系"视角:时间不预先给定,而由观测关联与条件化生成。

这些发展共同构成本文的历史背景:边界项保证变分一致性,广义熵与 QES/QFC 提供了对"边界截面"的动力学约束,散射刻度同一式给出边界时间读数的统一代理,Page–Wootters 等关联时间方案则表明时间可以由条件概率与注意力选择导出。

### 1.4 本文的核心问题与思路

本文尝试回答三个相关问题:

1. 在无观察者读数的规范场状态下,边界如何"存在而无时间"?
2. 当观察者进行读数时,注意力如何选择边界上的截面族,从而不得不沿着一条测地线运动,这条测地线如何成为观察者的"时间轴"?
3. 在这一意义上,双缝干涉中图样的变化、宇宙中"所有可能截面"的共存如何被统一解释为"截面宇宙"几何,而观察者只是以注意力在其中选择路径?

为此,本文引入"边界时间几何"的统一框架,并在严格的模型假设下给出可证明的定理,将时间轴刻画为由刻度同一式标定、由广义熵极值与聚焦条件选出的"注意力测地线"。

---

## 2 Model & Assumptions

### 2.1 底层几何与边界数据

设 $(\mathcal M,g_{\mu\nu})$ 为具有边界 $\partial\mathcal M$ 的洛伦兹流形,外法向单位向量为 $n^\mu$,边界诱导度规为 $h_{ab}$。引力作用取为

$$
\mathcal S_{\rm grav}=\frac{1}{16\pi G}\int_{\mathcal M}\sqrt{-g}\,(R-2\Lambda)\,{\rm d}^4x+\frac{1}{8\pi G}\int_{\partial\mathcal M}\epsilon\sqrt{h}\,K\,{\rm d}^3y,
$$

其中 $K$ 为外在曲率迹,$\epsilon=\pm1$ 区分类空间/类时间边界。物质场的体作用记为 $\mathcal S_{\rm matter}$,总作用为 $\mathcal S=\mathcal S_{\rm grav}+\mathcal S_{\rm matter}$。

假定体域场动力学由可重整化或有效场论给出,使得在给定边界条件下存在良态的路径积分或配分函数 $Z[\partial\mathcal M]$。在半经典极限下,给定边界胚 $(\partial\mathcal M,h_{ab},K_{ab})$ 的主导贡献来自满足 Einstein 方程的驻定几何。

### 2.2 边界可观测代数与状态

设 $\mathcal A_{\partial}$ 为附着于边界 $\partial\mathcal M$ 的可观测代数,可取为某个适定局域算子代数的 $C^*$ 或 von Neumann 代数,态由正归一线性泛函 $\omega:\mathcal A_{\partial}\to\mathbb C$ 表示。给定划分 $\partial\mathcal M=R\cup\bar R$,可定义局域子代数 $\mathcal A_R\subset\mathcal A_{\partial}$ 及其限制态 $\omega_R$。

在具有引力对偶的情形中,假定对每个适定边界区域 $R$ 存在一个共维二截面 $\sigma_R$(如 HRT 面或 QES)作为对应的"熵边界",其广义熵 $S_{\rm gen}[\sigma_R]$ 等于 $\omega_R$ 的冯·诺依曼熵加上几何面积项。

### 2.3 广义熵测地线与量子聚焦

给定一个光滑共维二截面族 $\{\sigma(\lambda)\}$,其沿某一零测地束 $N$ 的变形由参数 $\lambda$ 描述。定义广义熵

$$
S_{\rm gen}(\lambda)=\frac{{\rm Area}[\sigma(\lambda)]}{4G\hbar}+S_{\rm out}[\sigma(\lambda)].
$$

量子聚焦猜想提出,广义熵的"量子膨胀"

$$
\Theta(\lambda)=\frac{4G\hbar}{{\rm Area}[\sigma(\lambda)]}\frac{{\rm d}S_{\rm gen}}{{\rm d}\lambda}
$$

沿 $N$ 单调不增,即 ${\rm d}\Theta/{\rm d}\lambda\le0$,在适定极限下导出量子零能条件及 Bousso 光片界。

本文中称满足下述条件的曲线族为"广义熵测地线"(generalized entropic geodesic):

* 每一截面 $\sigma(\lambda)$ 在微小横向变形下使 $S_{\rm gen}$ 驻定:$\delta S_{\rm gen}[\sigma(\lambda)]=0$;
* 沿族方向的量子膨胀单调不增:${\rm d}\Theta/{\rm d}\lambda\le0$。

在半经典极限下,上述条件退化为面积极值与经典聚焦定理,从而与通常的极值曲面与测地线概念对齐。

### 2.4 散射刻度母尺与时间读数

考虑边界上的散射过程,其 S 矩阵谱分解为 $S(\omega)$。定义刻度母尺

$$
\kappa(\omega)=\frac{\varphi'(\omega)}{\pi}=\rho_{\rm rel}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

其中 $Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)$。刻度同一式在适定的 trace-class 扰动条件下可由 Birman–Kreĭn 谱移函数与 Wigner–Smith 时间延迟矩阵的关系证明。

在工程语境中,可通过测量群延迟谱 $(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 或散射相位导数 $\varphi'(\omega)/\pi$ 来实现时间刻度的标定。本文中将 $\kappa(\omega)$ 视为"边界时间刻度母尺",即在无观察者时背景上已经存在的、但尚未被选为某一特定时间轴的刻度结构。

### 2.5 观察者、注意力截面与时间轴

观察者 $\mathcal O$ 由三要素刻画:

1. 一条类时曲线(候选世界线)$\gamma:\tau\mapsto x^\mu(\tau)$,参数 $\tau$ 未必预先等同于固有时间;
2. 一族"注意力截面" $\{\Sigma_\tau\}$,其中每个 $\Sigma_\tau$ 为嵌入 $\partial\mathcal M$ 的共维一截面,与 $\gamma(\tau)$ 横截;
3. 附着于 $\Sigma_\tau$ 的可访问代数 $\mathcal A_{\Sigma_\tau}^\Lambda\subset\mathcal A_{\partial}$ 与相应条件态 $\omega_{\Sigma_\tau}^\Lambda$,其中 $\Lambda$ 表示观测分辨率或粗粒化尺度。

"注意力"在此形式化为一族完全正迹保持映射 $\mathcal E_{\tau,\Lambda}:\mathcal A_{\partial}\to\mathcal A_{\Sigma_\tau}^\Lambda$,以及从全局态 $\omega$ 到条件态 $\omega_{\Sigma_\tau}^\Lambda$ 的 Bayes 型更新。观察者的时间轴将由 $\tau$ 与 $\gamma$ 的联合条件选出,使得 $\tau$ 同时满足:

* 相对于刻度母尺 $\kappa(\omega)$ 的读数保持线性:$\tau\sim\int\kappa(\omega)\,w(\omega)\,{\rm d}\omega$,其中 $w(\omega)$ 为与实验装置相关的权函数;
* 对应的截面族 $\{\sigma(\tau)\}$(由 $\Sigma_\tau$ 与体域几何决定)满足广义熵测地线条件。

在此意义上,时间轴是"由注意力选择的广义熵测地线,并以散射刻度母尺标定的参数"。

---

## 3 Main Results (Theorems and Alignments)

本节给出本文的三条主结果。证明在第 4 节与附录中展开。

### 定理 3.1(无观察者时间与边界块结构)

设 $(\mathcal M,g_{\mu\nu})$ 满足 Einstein 方程,$\partial\mathcal M$ 上给定引力–物质边界数据,使得对任意共维二截面族 $\{\sigma(\lambda)\}$ 定义良好的广义熵 $S_{\rm gen}(\lambda)$。若不选定任何注意力截面族 $\{\Sigma_\tau\}$ 与可访问代数族 $\{\mathcal A_{\Sigma_\tau}^\Lambda\}$,则:

1. 可定义全局的刻度母尺 $\kappa(\omega)$,但不存在选出的单一时间参数 $\tau$,仅有一个无优先方向的"刻度场";
2. 任何关于"演化"的描述都可重述为在 $(\partial\mathcal M,\mathcal A_{\partial},\omega)$ 上的自同构,等价于块宇宙上的坐标重标。

从而在无观察者的意义下,边界具有确定的几何–熵–刻度结构,但不存在优先的时间轴。

### 定理 3.2(注意力测地线定理)

在 2.1–2.5 的假设下,假定存在一族类时曲线候选 $\gamma$ 与注意力映射 $\mathcal E_{\tau,\Lambda}$,满足:

1. 对每个 $\tau$,由 $\gamma(\tau)$ 与边界数据确定的共维二截面 $\sigma(\tau)$ 使得 $S_{\rm gen}[\sigma(\tau)]$ 对于小的横向变形驻定;
2. 沿由 $\sigma(\tau)$ 所确定的零测地束,广义熵的量子膨胀严格单调不增;
3. 时间读数 $\tau$ 由刻度母尺给出,即存在非负可积权函数 $w(\omega)$,使得

   $$
   \frac{{\rm d}\tau}{{\rm d}\lambda}=\int\kappa(\omega)\,w_\lambda(\omega)\,{\rm d}\omega,
   $$

   且 $w_\lambda$ 仅依赖于 $\mathcal E_{\lambda,\Lambda}$ 与边界散射结构。

则存在一一对应(模单调重参数化)在:

* 满足上述 1–3 条件的"注意力时间轴"族 $\{\gamma,\tau,\mathcal E_{\tau,\Lambda}\}$;
* 以作用泛函 $\mathcal J[\gamma]=\int L_{\rm eff}(x,\dot x)\,{\rm d}\tau$ 为极值的类时测地线族,其中 $L_{\rm eff}$ 为包含广义熵与刻度项的有效 Lagrangian。

换言之,满足刻度同一式与广义熵测地线条件的注意力时间轴等价于某一有效几何上的测地线。

### 定理 3.3(截面宇宙与观测分支)

在定理 3.2 的设定下,考虑一族不同观测分辨率 $\{\Lambda_i\}$ 与相应注意力截面族 $\{\Sigma_\tau^{(i)}\}$,定义一族注意力时间轴 $\{\gamma^{(i)},\tau^{(i)}\}$。若对每对 $(i,j)$ 存在一族截面间的完全正映射

$$
\Phi_{ij,\tau}:\mathcal A_{\Sigma_\tau^{(i)}}^{\Lambda_i}\to\mathcal A_{\Sigma_{\tilde\tau}^{(j)}}^{\Lambda_j}
$$

满足相对熵单调性

$$
S(\omega^{(i)}_{\Sigma_\tau^{(i)}}\Vert\omega^{(i)}_{\Sigma_\tau^{(i)}}\circ\Phi_{ij,\tau})\ge0,
$$

则可以:

1. 把所有注意力时间轴嵌入到一个"截面宇宙"空间 $\mathfrak S$,其点为等价类 $[\Sigma,\mathcal A_\Sigma^\Lambda,\omega_\Sigma^\Lambda]$;
2. 把每个观察者的体验历史理解为 $\mathfrak S$ 上的路径,而不同观察者之间的差异对应于在 $\mathfrak S$ 上选择不同的测地线族。

当将此结构应用于双缝干涉实验时,带或不带路径探测器的情形对应于截面宇宙中不同的注意力路径:干涉条纹的出现与消失是"截面选择"而非"单一波函数突变"的几何化表达。

### 命题 3.4(宏观引力–微观时间延迟桥接)

在弱场、慢变引力背景下,宏观引力势 $\Phi_{\rm grav}$ 沿观测者世界线产生的 Shapiro 延迟,可在一阶近似上写为边界散射相位的有效贡献,从而宏观引力时间延迟与微观 Wigner–Smith 时间延迟在刻度母尺上统一。由此可将"引力势"解释为对刻度母尺积分的几何效应,而非额外力的存在。

---

## 4 Proofs

本节给出定理 3.1–3.3 与命题 3.4 的证明骨架,详细计算推迟至附录。

### 4.1 定理 3.1

定理 3.1 的关键在于分离"存在的结构"与"被选出的参数"。

1. 由给定边界数据与体域场方程,可定义路径积分 $Z[\partial\mathcal M]$ 或相应的边界态 $|\Psi_{\partial}\rangle$,其包含所有允许的体域历史。
2. 对任何共维二截面族 $\{\sigma(\lambda)\}$,可通过半经典方法计算广义熵 $S_{\rm gen}(\lambda)$,得到一个标量函数族。
3. 刻度母尺 $\kappa(\omega)$ 完全由边界散射矩阵 $S(\omega)$ 决定,而 $S(\omega)$ 又由 $(\mathcal M,g_{\mu\nu},\text{边界条件})$ 决定,与是否存在观察者无关。

然而,要把 $\kappa(\omega)$ 与 $S_{\rm gen}(\lambda)$ 组合成一个"一维时间参数"$\tau$,必须选择:

* 一个具体的曲线族 $\{\gamma\}$;
* 一个具体的截面族 $\{\Sigma_\tau\}$ 与可访问代数族;
* 一个具体的权函数族 $w_\lambda(\omega)$。

在未做这些选择时,$\kappa(\omega)$ 与 $S_{\rm gen}(\lambda)$ 只是块宇宙上的场与函数,没有任何优先的参数化。任何"演化"都可视为边界态 $\omega$ 的自同构,即坐标重标,与 Page–Wootters 形式中整体静态态 $|\Psi\rangle$ 的情形类似。从而定理 3.1 直接成立。

### 4.2 定理 3.2

证明分为三个步骤。

**步骤一:从注意力截面到有效作用。**

给定注意力映射 $\mathcal E_{\tau,\Lambda}$ 与截面族 $\{\Sigma_\tau\}$,可定义在每个 $\tau$ 上的"局域自由能"

$$
F(\tau)=\langle H_{\Sigma_\tau}\rangle_{\omega_{\Sigma_\tau}^\Lambda}-\Theta_0 S_{\rm gen}[\sigma(\tau)],
$$

其中 $H_{\Sigma_\tau}$ 为与可访问代数 $\mathcal A_{\Sigma_\tau}^\Lambda$ 相应的模块哈密顿量,$\Theta_0$ 为常数。广义熵驻定条件 $\delta S_{\rm gen}=0$ 与量子聚焦单调性保证

$$
\frac{{\rm d}F}{{\rm d}\tau}=\left\langle\frac{{\rm d}H_{\Sigma_\tau}}{{\rm d}\tau}\right\rangle-\Theta_0\frac{{\rm d}S_{\rm gen}}{{\rm d}\tau}\le0,
$$

界定了一种"信息耗散"的时间箭头。

另一方面,刻度条件给出 ${\rm d}\tau/{\rm d}\lambda=\int\kappa(\omega)w_\lambda(\omega)\,{\rm d}\omega$,可视为从频域刻度到参数 $\lambda$ 的测度变换。

**步骤二:构造有效 Lagrangian。**

令 $\gamma$ 的切向量满足 $u^\mu={\rm d}x^\mu/{\rm d}\tau$,定义有效 Lagrangian

$$
L_{\rm eff}(x,u)=m\sqrt{-g_{\mu\nu}u^\mu u^\nu}+\alpha\,\Theta[u]+\beta\,\mathcal K[u],
$$

其中第一项为标准固有时间 Lagrangian,第二项 $\Theta[u]$ 为沿 $\gamma$ 所截零测地束的量子膨胀函数,第三项 $\mathcal K[u]$ 为由刻度母尺诱导的"刻度势"。参数 $\alpha,\beta$ 由具体物理归一化决定。

在半经典与弱场极限下,$\Theta[u]$ 与 $\mathcal K[u]$ 的贡献可视为小修正,Euler–Lagrange 方程给出的轨迹与经典测地线相近。要求 $F(\tau)$ 单调不增相当于要求 $\gamma$ 使 $\mathcal J[\gamma]=\int L_{\rm eff}\,{\rm d}\tau$ 极小。

**步骤三:一一对应性。**

若给定一族注意力时间轴满足定理 3.2 的 1–3 条件,则可按步骤一、二构造对应的有效 Lagrangian,从而得到一族极值曲线;反之,给定一族极值曲线,在适定正则条件下可反推对应的截面族与刻度权函数,使之满足广义熵驻定与量子聚焦条件。由于 Lagrangian 仅在整体重参数化下改变总作用的数值,时间参数 $\tau$ 仅在单调重参数化下不唯一,从而得到模此自由度的一一对应。

### 4.3 定理 3.3

定理 3.3 的关键是利用相对熵单调性构造一个全局的"截面宇宙"空间。

1. 将每个三元组 $(\Sigma,\mathcal A_\Sigma^\Lambda,\omega_\Sigma^\Lambda)$ 视为一个对象,若存在保持相对熵不增的完全正映射,则定义一个态射。由相对熵单调性可知,这样的态射构成一个范畴。
2. 对所有观察者与分辨率的截面三元组取并,得到一族对象与态射。通过适当的等价关系(如彼此间存在同构映射)将之压缩成商空间 $\mathfrak S$。
3. 每个观察者的注意力时间轴对应于 $\mathfrak S$ 上的路径,其切向量可由相对熵变化率与广义熵变化率共同控制。不同观察者路径之间的"距离"可由某种信息几何度量(如 Fisher–Rao 或 Bures 距)定义,从而将"体验差异"几何化。

在双缝实验中,不加探测器的路径对应于保持干涉相干的截面族,其相对熵结构允许跨缝的相干;加入路径探测器则等于施加一个投影型或近似投影的注意力映射,改变可访问代数,使跨缝相干信息被不可逆地编码于环境,从而对应于截面宇宙中的另一条路径。两条路径并存于 $\mathfrak S$,但单个观察者沿其注意力时间轴只访问其中之一,相当于在"所有可能性同时存在"的结构上选择了特定截面序列。

### 4.4 命题 3.4

在弱场、静态势 $\Phi_{\rm grav}$ 下,经典 Shapiro 延迟可写为沿光路的积分

$$
\Delta t_{\rm grav}\approx-\frac{2}{c^3}\int\Phi_{\rm grav}\,{\rm d}\ell.
$$

另一方面,弱势极限下的引力对相位的贡献可视为 S 矩阵中一个附加相位 $\delta\varphi_{\rm grav}(\omega)$,其导数给出附加群延迟 $\Delta t_{\rm WS}=(\partial_\omega\delta\varphi_{\rm grav})$。在几何光学极限中,两者可通过折射率与有效势的关系对应,从而

$$
\Delta t_{\rm grav}\approx\Delta t_{\rm WS}\approx\frac{1}{2\pi}\operatorname{tr}\Delta Q(\omega).
$$

因此,宏观引力产生的时间延迟可统一为刻度母尺上的相位–延迟效应,而无需引入独立的"力"的概念。这一桥接在波导与引力透镜背景下已有多种形式的研究支持。

---

## 5 Model Apply

本节展示框架在三个典型场景中的应用:黑洞信息、宇宙红移与双缝干涉。

### 5.1 黑洞信息与岛公式

在黑洞蒸发现象中,晚时 Hawking 辐射的冯·诺依曼熵随时间增长直至 Page 时间附近达到峰值,然后下降,整体曲线可由"岛公式"给出

$$
S(R)=\min_{\rm QES}\left\{\frac{{\rm Area}(\partial I)}{4G\hbar}+S_{\rm bulk}(I\cup R)\right\},
$$

其中 $R$ 为辐射区域,$I$ 为岛区域。在本框架下:

* 远处观察者的注意力截面族 $\{\Sigma_\tau^{\rm out}\}$ 主要支配于近无穷远的边界,其对应的 QES 为穿过黑洞内部的面;
* 自由落入观察者的截面族 $\{\Sigma_\tau^{\rm in}\}$ 则局域于近视界区域,其对应 QES 与外部截面不同。

两类观察者的注意力时间轴在截面宇宙 $\mathfrak S$ 中对应于不同路径。对外观察者而言,岛区域的信息"编码于辐射";对内观察者而言,同一信息以局域方式存在于黑洞内部。信息保真但分布在不同截面族上,从而缓解"信息在何处"的表述性张力。

### 5.2 宇宙红移与时间刻度重标

在标准 FRW 宇宙学中,共动观测者的红移–时间关系由尺度因子 $a(t)$ 控制,频率满足 $\omega\propto a^{-1}$。在本框架中,宇宙视界或大尺度边界上的散射矩阵随时间演化,其相位导数给出刻度母尺 $\kappa(\omega)$。宇宙红移可被重述为:

* 背景几何决定了刻度母尺随频率的重标;
* 不同宇宙年代的观察者通过各自的注意力截面族与可访问频段选择不同的权函数 $w_\lambda(\omega)$;
* 时间轴的比较变成不同观察者之间刻度积分的比较,而非某种绝对时间的流逝。

这种重述为"宇宙时间"提供了一个边界–散射–刻度的统一解释,有利于分析引力–暗能量–信息流之间的关系。

### 5.3 双缝干涉中的截面选择

考虑标准双缝实验。在未引入路径探测器时,入射粒子态 $|\psi_{\rm in}\rangle$ 经由两缝演化到探测屏的边界态 $|\psi_{\rm out}\rangle$,其强度分布由干涉项控制。加入路径探测器可通过与环境的纠缠实现,导致有效态在屏上近似为不含干涉项的混合态。

在本文框架中:

* 未探测时,注意力截面族 $\{\Sigma_\tau^{\rm free}\}$ 对应于保持两缝相干的可访问代数,其广义熵结构允许跨缝的相干;
* 有探测时,注意力映射 $\mathcal E_{\tau,\Lambda}^{\rm path}$ 将可访问代数压缩到路径可辨的子代数,其相对熵结构与环境信息流决定了新截面族 $\{\Sigma_\tau^{\rm decoh}\}$。

两套截面族在截面宇宙 $\mathfrak S$ 中对应不同路径。实验者通过选择是否开启探测器,实际上在截面宇宙中选择了自己的注意力时间轴,而并非直接"改变了宇宙状态"。宇宙在结构上容纳所有截面路径,观测只是选择其一。

---

## 6 Engineering Proposals

### 6.1 基于电磁散射网络的刻度–熵对齐实验

构建多端口电磁散射网络,利用矢量网络分析仪测量频率依赖的 S 矩阵 $S(\omega)$,并通过数值微分得到 Wigner–Smith 矩阵 $Q(\omega)$ 与其迹。同时,在网络内部划分"可访问区域"与"环境区域",通过改变耦合强度与有耗元件配置控制广义熵 $S_{\rm out}$ 的分布。测量方案包括:

1. 通过端口功率谱估计输出态的冯·诺依曼或 Rényi 熵近似;
2. 验证群延迟谱的变化与熵变化之间的相关性,检验刻度同一式在受控环境中的稳定性;
3. 通过引入可调开关与路径可识别探测端口,实现双缝类情景,在同一网络中比较不同注意力截面下的群延迟–熵–图样三者之间的关系。

### 6.2 基于冷原子与量子光学的 Page–Wootters 方案

在冷原子或 trapped-ion 平台上实现 Page–Wootters 类关联时间实验,将一部分自由度作为"钟",另一部分作为"系统",制备整体近似静态约束态。通过条件测量钟的结果,重构系统的有效演化。结合本框架:

* 以实验装置的光学边界为 $\partial\mathcal M$ 的近似;
* 通过量子层析重构边界可观测代数上的态变化,验证不同注意力截面族对应的时间参数化是否一致;
* 测量条件态的熵变化,检验广义熵测地线的近似条件。

### 6.3 引力透镜与 FRB 时间延迟

利用快速射电暴(FRB)或类 FRB 脉冲信号的多像时间延迟与频率色散特性,分析宏观引力势与微观频率刻度之间的关系。在本框架下,观测者在不同像面上的注意力截面族对应于不同的边界散射路径,其刻度母尺上的群延迟差异直接给出宏观引力效应。结合统计大量事件,有望对命题 3.4 的桥接关系给出天文级的检验。

---

## 7 Discussion (risks, boundaries, past work)

### 7.1 风险与适用域

本框架的主要风险在于:

* 对 QES 与岛公式的依赖,使得严格适用域限于具有半经典引力对偶的态;对一般 QFT 背景,广义熵测地线与截面宇宙的构造可能不充分。
* 对 QFC 的假定目前仍处于猜想状态,虽已有部分证明与强支持例,但缺乏完全一般的数学证明。
* 刻度同一式在散射理论中的严格性依赖于特定的 trace-class 扰动条件与谱性假设,对复杂开放系统需谨慎外推。

因此,本框架应被理解为在"半经典引力 + 良态散射 + 可控观测"三重条件下的统一图景,其外推到强量子引力、非局域相互作用或高度非平衡系统时需要额外论证。

### 7.2 与观察者–时间–测量的既有工作关系

本文与 Page–Wootters、内部参考系与关系时间、量子测量与解耦历史等方向存在紧密联系。本文的特色在于:

* 把"时间"不只视为关联参数,而视为"由边界刻度母尺与广义熵测地线共同选出的注意力时间轴";
* 通过刻度同一式将散射相位、群延迟与谱移函数统一为时间读数的代理,从而把宏观引力与微观散射放在同一边界框架中;
* 以截面宇宙 $\mathfrak S$ 的构造,为"多世界""分支"给出一个基于边界与信息几何的形式化表述,而不必引入额外本体。

### 7.3 下一步发展方向

可能的延伸包括:

* 将截面宇宙 $\mathfrak S$ 丰富为带有测地线结构的信息几何流形,系统研究不同观察者之间的"距离"与"相似性";
* 在离散化模型(如张量网络、因果集或可逆元胞自动机)中,实现本框架的完全代数化版本;
* 将伦理、价值与决策中的时间折扣与注意力截面联系起来,探讨"社会时间轴"的广义熵基础。

---

## 8 Conclusion

本文在边界–散射–广义熵–注意力的统一框架中,对"没有观察者时边界如何存在而无时间""观察者注意力如何生成时间轴"与"双缝干涉何以体现截面选择"这三类问题给出了一套可证明与可检验的表述。核心元素包括:

* 刻度母尺 $\kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\rm rel}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 作为时间读数的唯一代理;
* 广义熵测地线与量子聚焦作为"注意力时间轴"的几何判据;
* 截面宇宙 $\mathfrak S$ 作为容纳所有注意力路径的结构空间,观察者的体验只是其上的一条测地线。

在此图景中,宇宙在结构上同时包含"所有可能截面",而观察者的注意力在这些截面之间选择一条广义熵–刻度一致的路径,这条路径被感知为"时间轴"。时间因此不再是独立实在,而是边界刻度与注意力截面之间稳定对齐的产物。

---

## Acknowledgements, Code Availability

感谢在广义熵、量子极值面、量子聚焦、Wigner–Smith 时间延迟、Page–Wootters 关联时间等方向的既有研究工作,为本文提供了必要的数学与物理基础。本文所有结果基于解析推导与概念构造,未使用数值代码;因此无附带代码库可供公开。

---

## References

1. R. Bousso, Z. Fisher, S. Leichenauer, A. C. Wall, "A Quantum Focussing Conjecture", Phys. Rev. D 93, 064044 (2016).
2. C. Akers, S. Hernández-Cuenca, P. Rath, "Quantum Extremal Surfaces and the Holographic Entropy Cone", arXiv:2108.07280.
3. D. Marolf 等, "The entropy of bulk quantum fields and the entanglement wedge", 相关综述文献。
4. T. Hartman 等, "Islands in the Stream: Quantum Islands and Black Hole Interiors", JHEP 11 (2020) 111.
5. F. Gesztesy, "A Short Course on the Spectral Shift Function ξ", Lecture Notes (2017).
6. F. D. Cunden et al., "Statistical distribution of the Wigner-Smith time-delay matrix in chaotic cavities", Phys. Rev. E 91, 060102 (2015).
7. U. R. Patel et al., "Wigner-Smith Time Delay Matrix for Electromagnetics", arXiv:2005.03211.
8. G. W. Gibbons, S. W. Hawking, "Action Integrals and Partition Functions in Quantum Gravity", Phys. Rev. D 15, 2752 (1977).
9. A. Ahmadain et al., "A Comment on Deriving the Gibbons-Hawking-York Term From the String Worldsheet", arXiv:2407.18866.
10. D. N. Page, W. K. Wootters, "Evolution without evolution: Dynamics described by stationary observables", Phys. Rev. D 27, 2885 (1983).
11. L. R. S. Mendes, "Non-linear equation of motion for Page-Wootters clocks", arXiv:2107.11452.
12. E. Adlam, "Interpreting the Page–Wootters Formalism and the Internal Perspectives on Time", 相关综述论文。
13. A. Calcinari, "Relational dynamics and Page–Wootters formalism in relativistic settings", Quantum 9, 1610 (2025).

---

## Appendix A: 刻度同一式与 Wigner–Smith 矩阵的严格推导纲要

本附录回顾刻度母尺 $\kappa(\omega)$ 的数学基础。

### A.1 谱移函数与 Birman–Kreĭn 公式

设 $H_0,H$ 为自伴算子,$H=H_0+V$ 且 $V$ 为 trace-class 扰动。谱移函数 $\xi(\lambda)$ 满足

$$
\operatorname{tr}(f(H)-f(H_0))=\int_{-\infty}^{+\infty} f'(\lambda)\,\xi(\lambda)\,{\rm d}\lambda
$$

对足够光滑的 $f$ 成立。Birman–Kreĭn 公式给出

$$
\det S(\lambda)=\exp\{-2\pi i\xi(\lambda)\},
$$

其中 $S(\lambda)$ 为对应的散射矩阵。因此

$$
\Phi(\lambda)=\arg\det S(\lambda)=-2\pi\xi(\lambda)\mod 2\pi,
$$

从而

$$
\varphi'(\lambda)=\tfrac12\Phi'(\lambda)=-\pi\xi'(\lambda).
$$

定义相对态密度 $\rho_{\rm rel}(\lambda)=-\xi'(\lambda)$,则立即得到

$$
\frac{\varphi'(\lambda)}{\pi}=\rho_{\rm rel}(\lambda).
$$

### A.2 Wigner–Smith 矩阵与迹公式

Wigner–Smith 时间延迟矩阵定义为

$$
Q(\lambda)=-iS(\lambda)^\dagger\partial_\lambda S(\lambda).
$$

在 trace-class 扰动条件下,其迹与谱移函数导数满足

$$
\operatorname{tr}Q(\lambda)=2\pi\xi'(\lambda).
$$

结合上一节得到

$$
\rho_{\rm rel}(\lambda)=\frac{1}{2\pi}\operatorname{tr}Q(\lambda),
$$

综上给出刻度同一式

$$
\kappa(\lambda)=\frac{\varphi'(\lambda)}{\pi}=\rho_{\rm rel}(\lambda)=\frac{1}{2\pi}\operatorname{tr}Q(\lambda).
$$

### A.3 工程实现中的有限带宽与数值近似

在实际测量中,可用有限差分近似 $\partial_\omega S(\omega)$,并在有限频带上估计 $\kappa(\omega)$ 的平均值。误差控制可通过:

* 频率步长选择满足 Nyquist 条件与信噪比权衡;
* 数值平滑与正则化处理谱干扰;
* 利用物理模型拟合 $S(\omega)$ 的解析结构,从而提高导数估计精度。

这些技术细节在电磁与声学散射文献中已有系统讨论。

---

## Appendix B: 广义熵测地线与量子聚焦

### B.1 QFC 的形式

给定截面 $\sigma$ 与正交零测地束 $N$,定义广义熵

$$
S_{\rm gen}=\frac{{\rm Area}(\sigma)}{4G\hbar}+S_{\rm out}(\sigma).
$$

沿 $N$ 的量子膨胀定义为

$$
\Theta=\frac{4G\hbar}{{\rm Area}(\sigma)}\frac{{\rm d}S_{\rm gen}}{{\rm d}\lambda}.
$$

QFC 声称

$$
\frac{{\rm d}\Theta}{{\rm d}\lambda}\le0
$$

在适定的半经典引力系统中普遍成立,统一了 Bousso 界与经典聚焦定理,并蕴含量子零能条件。

### B.2 广义熵测地线的 Euler–Lagrange 方程

考虑截面族 $\{\sigma(\lambda)\}$ 的变分 $\delta X^i(\lambda)$,定义有效作用

$$
\mathcal I[\sigma]=\int L_{\rm gen}(\sigma,\partial\lambda\sigma)\,{\rm d}\lambda,
$$

其中 $L_{\rm gen}=\frac{{\rm Area}(\sigma)}{4G\hbar}+S_{\rm out}(\sigma)$。驻定条件

$$
\delta\mathcal I=0
$$

给出类似极小曲面方程的广义 Euler–Lagrange 方程,其解即为 QES。进一步要求 $\Theta$ 单调不增,相当于对二阶导数施加约束,保证极值为极小或鞍点而非极大。

### B.3 与类时测地线的耦合

当截面族 $\sigma(\tau)$ 与类时曲线 $\gamma(\tau)$ 耦合,即每个 $\sigma(\tau)$ 以 $\gamma(\tau)$ 为锚点时,可构造联合作用

$$
\mathcal J[\gamma,\sigma]=\int\left(m\sqrt{-g_{\mu\nu}\dot x^\mu\dot x^\nu}+\lambda_1 L_{\rm gen}[\sigma(\tau)]+\lambda_2\Theta[\sigma(\tau)]\right){\rm d}\tau.
$$

对 $\sigma$ 变分给出广义熵测地线方程,对 $\gamma$ 变分给出修正的测地线方程。定理 3.2 的陈述可理解为:在合适的参数与约束下,此联合极值问题等价于在带有有效度规 $\tilde g_{\mu\nu}=g_{\mu\nu}+\delta g_{\mu\nu}(S_{\rm gen},\Theta)$ 上寻找测地线。

---

## Appendix C: 截面宇宙与相对熵单调性

### C.1 截面对象与态射的定义

定义对象为三元组 $(\Sigma,\mathcal A_\Sigma^\Lambda,\omega_\Sigma^\Lambda)$。若存在完全正迹保持映射 $\Phi:\mathcal A_{\Sigma_1}^{\Lambda_1}\to\mathcal A_{\Sigma_2}^{\Lambda_2}$,满足

$$
S(\omega_{\Sigma_1}^{\Lambda_1}\Vert\omega_{\Sigma_1}^{\Lambda_1}\circ\Phi)\ge0,
$$

则称其为一个"可物理实现"的态射。由 Uhlmann 定理与 Stinespring 表象可知,这样的映射总可由与环境的幺正耦合与部分迹实现,因此具有明确物理意义。

### C.2 商空间构造

将所有对象与态射组成范畴 $\mathfrak C$。若两个对象之间存在双向可逆态射,则视为等价。对等价类取商,得到截面宇宙 $\mathfrak S$。信息几何结构可通过对每个对象赋予 Fisher–Rao 度量或 Bures 距,并对态射要求为收缩映射来定义。

### C.3 观察者路径与双缝情形

在双缝情形中,不加探测器对应于对象族

$$
(\Sigma_\tau^{\rm free},\mathcal A_{\rm full},\omega_{\rm coh}),
$$

其相对熵结构允许跨缝相干;加入探测器对应于

$$
(\Sigma_\tau^{\rm decoh},\mathcal A_{\rm block},\omega_{\rm mix}),
$$

相对熵结构体现了哪条路径信息的泄露。两者在 $\mathfrak S$ 上为不同的路径,且无双向可逆态射连接(因相干不可无耗恢复),故属于不同区域。观察者的注意力选择决定其所在路径,从而给出"观测改变图样"的几何与信息论解释。

---

## Appendix D: Page–Wootters 形式中的注意力时间轴

Page–Wootters 形式以整体静态态 $|\Psi\rangle$ 与约束 $\hat H_{\rm tot}|\Psi\rangle=0$ 为基础,系统–钟分解为 $\mathcal H_{\rm S}\otimes\mathcal H_{\rm C}$,条件态

$$
|\psi_{\rm S}(t)\rangle\propto\langle t|\Psi\rangle
$$

满足有效 Schrödinger 方程。在本框架下:

* 边界可观测代数 $\mathcal A_{\partial}$ 包含系统与钟的算子;
* 注意力截面对应该如何选择 $|t\rangle$ 的测量基底与粗粒化方式;
* 不同的时间分辨率 $\Lambda$ 对应于不同的钟子空间划分,从而生成不同的注意力时间轴。

这一视角加强了"时间作为注意力生成的参数"的物理解读,并为刻度母尺与关联时间之间的对齐提供了一个微观机制。
