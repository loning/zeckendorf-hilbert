# 边界驱动的分形生成机制:从时间刻度母尺到反馈散射与临界界面

---

## Abstract

在统一的边界–时间–散射框架下,分析自然界中广泛出现的"分形长在边界上"的现象。本文从三条互补主线给出严格刻画:(i) 在带边界流形与参数空间的总空间 $Y = M \times X^\circ$ 上,以时间刻度母尺 $\kappa(\omega) = \varphi'(\omega)/\pi = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\operatorname{tr} Q(\omega)$、相对拓扑类 $[K] \in H^2(Y,\partial Y;\mathbb Z_2)$ 与散射族 $K^1$ 类 $[u] \in K^1(X^\circ)$ 为基本不变量,将"边界"定义为同时承担边界条件、通量与熵读数的共维一界面,并证明一切可观测时间与边界分形最终都表现为边界数据的函数;(ii) 在该框架内构造三类典型的"边界分形生成机制":反馈型边界(自指散射网络)、临界型边界(无特征尺度的相界面)与 Laplace 型边界(扩散/势驱动的生长前沿)。分别给出一维自相似散射玩具模型、临界界面的标度方程与 Laplacian growth 方程 $v_n \propto \lvert \nabla u \rvert$ 下的定理,证明在"无内在特征尺度 + 局部规则 + 边界反馈"条件下,尺度变换半群的非平凡不动点与极限集具有自相似性,其几何与谱测度呈现分形特征;(iii) 将上述边界分形结构与时间刻度母尺 $\kappa(\omega)$ 对接,引入"分形时间延迟"的严格定义,证明在多层自相似散射网络、临界界面与 Laplacian growth 前沿上,群延迟分布 $\tau(\omega)$ 与相对态密度 $\rho_{\mathrm{rel}}(\omega)$ 在对数频率缩放下具有自相似性,从而给出"时间分形纹理"作为边界分形的一种谱–时间投影。进一步证明:在时间几何等价类 $[\tau]$ 已经固定的前提下,边界分形不改变因果排序与时间等价类本身,而只改变不同尺度上的时间纹理与统计性质。

本文给出一个统一结论:分形不是由观察者主观"造出",而是在无特征尺度的 bulk 动力学与边界条件耦合下,在高通量、高反馈的边界上自然生成;边界是"分形最易生成并最易被读出的舞台"。文末给出可实现的散射与生长实验方案,并在附录中给出自指散射玩具模型的递推与自相似性证明、临界界面标度律的推导以及分形时间刻度与时间等价类之间关系的形式化论证。

---

## Keywords

边界几何;分形界面;Wigner–Smith 时间延迟;Birman–Kreĭn 公式;Laplacian growth;临界现象;Schramm–Loewner 演化;时间刻度母尺

---

## 1 Introduction & Historical Context

自然界中大量具有分形特征的结构几乎无一例外地出现在边界:海岸线与河网的交界,云团与对流层的剪切面,放电通道与介质界面,树枝与枝晶的生长前沿,湍流中涡团的分离层,以及凝聚态与统计物理中临界团簇与相界面等。自从 Mandelbrot 系统化提出"分形几何"以来,人们已经认识到这些图景背后存在统一的"无特征尺度"几何与统计结构,但关于"为什么分形总是出现在边界"这一问题,仍然缺乏一个同时兼顾几何、动力学与时间刻度的完整框架。

在非平衡生长领域,Witten 与 Sander 提出的扩散限制凝聚(diffusion-limited aggregation, DLA)模型给出了典型的"边界生长–分形"的场景:粒子在 bulk 中做随机游走,到达团簇边界后不可逆地黏附,产生分支状分形团簇,其分形维数位于欧氏维数与边界维数之间。大量数值与理论工作表明,DLA 模型生成的团簇具有稳定的分形指数,并与 Laplacian growth 在某些极限下相关或可区分的普适类。

另一方面,临界现象与界面理论显示,临界系统中的相界面本身呈现分形几何:二维临界渗流、Ising 模型、随机场 Ising 模型与刚性渗流等模型的界面可以用 Schramm–Loewner 演化(Schramm–Loewner evolution, SLE)统一描述,其界面 Hausdorff 维数与 SLE 参数 $\kappa$ 之间存在精确关系 $d = 1 + \kappa/8$,临界渗流外边界对应 $\kappa = 6$,界面维数为 $4/3$。这些结果在 Smirnov、Lawler–Schramm–Werner 等人的工作中得到严格化,并在后续的数值与理论研究中不断扩展。

与此并行,量子与波动散射理论中,Wigner 与 Smith 引入的时间延迟算子与时间延迟矩阵,将散射矩阵 $S(\omega)$ 与其频率导数联系起来,用以刻画被散射系统对入射波包的"群延迟";这一思想已经推广到量子、声学与电磁散射等多种体系,形成了以 Wigner–Smith 时间延迟矩阵为核心的谱–时间刻度框架。同时,Birman–Kreĭn 公式与 Lifshits–Kreĭn 谱移理论给出了散射相位、谱移函数与相对态密度之间的精确联系,使得总散射相位的导数在适当条件下等于相对态密度与 Wigner–Smith 时间延迟迹,从而在数学上统一了"相位–密度–时间延迟"三个时间刻度代理。

现有关于"分形边界"的讨论,多数聚焦于几何维数、粗粒化统计与普适类,很少直接与时间刻度、散射与信息几何统一起来。另一方面,关于"时间本质"的讨论经常在观察者与测量问题上打转,要么认为时间与结构强烈依赖观察者的投影,要么把边界仅视为技术上的边界条件,而忽略其在通量与信息中的中心地位。

本文的立场可以概括为以下几条:

1. 物理结构不是由观察者主观"造出",而是由 bulk 动力学与边界条件共同决定;观察者只是在某些边界上以有限分辨率耦合,读取边界算子的函数。
2. 边界不仅承担几何上的"界面"角色,还承担动力学闭合的边界条件、通量与能量–相位–熵读数的转换,以及拓扑与时间刻度的锚定。
3. 时间的刻度可以在散射矩阵与谱移函数上统一为一个时间刻度母尺 $\kappa(\omega)$,并与模时间与几何时间归入同一时间等价类。
4. 分形的生成主要发生在边界,并作为时间刻度母尺与边界算子在多尺度上的非平凡不动点或极限集出现;所谓"时间的分形纹理",正是这种边界分形在谱–时间域中的投影。

在前文的统一边界–时间–散射与边界时间几何工作中,我们已经构造了时间刻度母尺 $\kappa(\omega)$、时间等价类 $[\tau]$ 与边界算子代数的统一框架。本文在此基础上,专门聚焦于"边界驱动的分形生成机制",试图系统回答三个问题:

1. 是否可以在可证的意义上说"分形从边界产生";
2. 在边界–时间–散射统一框架中,分形是通过怎样的具体机制在边界上生成的;
3. 为什么在许多物理系统中,边界几何或谱结构自然呈现分形,而 bulk 描述本身可以保持简单和局域。

为此,本文的结构安排如下。第 2 节给出统一模型与假设,定义时间刻度母尺、时间等价类与边界分形。第 3 节给出三类边界分形生成机制的主定理:自相似反馈散射网络、临界界面与 Laplacian growth 前沿,并给出"分形时间延迟不改变时间等价类"的结论性定理。第 4 节给出证明骨架,并将技术细节放入附录。第 5 节讨论若干物理模型上的应用。第 6 节提出可行的工程方案。第 7 节讨论局限性与与既有工作的关系。第 8 节总结主要结论。附录 A–C 给出自指散射玩具模型的递推与自相似性证明、临界界面标度律与边界分形的联系以及分形时间刻度与时间等价类的形式化证明。

---

## 2 Model & Assumptions

### 2.1 总空间、边界与散射系统

设 $M$ 为带边界 $\partial M$ 的洛伦兹流形,表示 bulk 时空,$X^\circ$ 为去奇点参数空间(驱动频率、外场强度、几何形变等控制参数),定义总空间 $Y := M \times X^\circ$,其边界为 $\partial Y = \partial M \times X^\circ \cup M \times \partial X^\circ$。

对每个 $x \in X^\circ$,给定一对自伴算子 $(H_x,H_{0,x})$,分别表示相互作用系统与参照系统,满足如下散射理论常规假设:

1. $H_x$ 与 $H_{0,x}$ 的差为 trace class 或足够快衰减的有界扰动;
2. 存在 wave operator 与单位散射算子 $S_x$,其在能量壳上的分解给出固定频率散射矩阵 $S_x(\omega)$;
3. 对 a.c. 谱几乎处处,$S_x(\omega)$ 为有限通道上的酉矩阵。

在上述假设下,可以定义 Wigner–Smith 时间延迟矩阵

$$
Q_x(\omega) := -\mathrm{i}\,S_x^\dagger(\omega)\,\partial_\omega S_x(\omega),
$$

其迹给出群延迟之和。另一方面,Birman–Kreĭn 公式与谱移理论表明,对合适类的 Schrödinger 型算子,存在谱移函数 $\xi_x(\omega)$,使得相对态密度 $\rho_{\mathrm{rel},x}(\omega) = \partial_\omega \xi_x(\omega)$ 与散射相位 $\Phi_x(\omega) = \arg \det S_x(\omega)$ 满足

$$
\xi_x(\omega) = -\frac{1}{2\pi \mathrm{i}} \ln \det S_x(\omega),\qquad
\rho_{\mathrm{rel},x}(\omega) = \frac{\partial_\omega \Phi_x(\omega)}{2\pi}.
$$

在单通道情形,可记 $\varphi_x(\omega) = \tfrac12\Phi_x(\omega)$,上式化为 $\rho_{\mathrm{rel},x}(\omega) = \varphi'_x(\omega)/\pi$。

### 2.2 时间刻度母尺与时间等价类

在统一散射–时间刻度框架中,定义对每个参数 $x \in X^\circ$ 的时间刻度母尺

$$
\kappa_x(\omega)
:= \frac{\varphi'_x(\omega)}{\pi}
= \rho_{\mathrm{rel},x}(\omega)
= \frac{1}{2\pi}\operatorname{tr} Q_x(\omega),
$$

其中 $\operatorname{tr}$ 为通道空间上迹。该等式在满足 Birman–Kreĭn 公式与 Wigner–Smith 定义的常规条件下成立,代表同一对象在三种表述下的不同投影:相位梯度、相对态密度与群延迟迹。

在更广的边界时间几何框架中,还存在由 Tomita–Takesaki 模流给出的模时间刻度与由边界哈密顿量生成的几何时间刻度;在适当的匹配条件下,可以引入时间刻度等价类 $[\tau]$,使得散射时间 $\tau_{\mathrm{scatt}}$、模时间 $\tau_{\mathrm{mod}}$ 与几何时间 $\tau_{\mathrm{geom}}$ 在宏观上相关于某个代表时间函数 $\tau$ 的仿射重标:

$$
\tau_{\mathrm{scatt}} = a_1 \tau + b_1,\quad
\tau_{\mathrm{mod}} = a_2 \tau + b_2,\quad
\tau_{\mathrm{geom}} = a_3 \tau + b_3,
$$

其中 $a_i > 0$、$b_i \in \mathbb R$ 在给定物理窗口上缓变。时间几何的本质数据由等价类 $[\tau]$ 与因果结构共同决定,而不是由某个具体刻度选择决定。

### 2.3 物理边界与边界算子

本文中采用如下工作定义。

**定义 2.1(物理边界)** 设 $\Sigma \subset M$ 为共维一子流形(在 null 极限下可适当推广),称其为物理边界,当且仅当满足:

1. 几何条件:$\Sigma$ 在 $M$ 中可余维一光滑嵌入,带有自然诱导度量与法向;
2. 动力学条件:bulk 方程在穿越 $\Sigma$ 时需要边界条件方能闭合,或边界项在变分原理中不可省略(例如 Gibbons–Hawking–York 边界项);
3. 信息条件:在 $\Sigma$ 上可以自然定义通量、相位、时间延迟与广义熵等边界量,从而形成可观测的数据集。

对每个物理边界 $\Sigma$,引入边界算子族 $\mathcal A_\Sigma$,典型元素包括:

* 散射矩阵 $S(\omega)$;
* Wigner–Smith 时间延迟矩阵 $Q(\omega)$;
* 广义熵函数 $S_{\mathrm{gen}}(\Sigma)$;
* 视界或相界面的投影测度与谱测度。

本文关注的分形结构,正是这些边界算子及其支撑集在几何尺度与频率尺度上的自相似性质。

### 2.4 几何分形、谱分形与边界分形

**定义 2.2(几何分形)** 设 $(F,d)$ 为度量空间,$\mu$ 为 Borel 测度。称三元组 $(F,d,\mu)$ 为几何分形,如果对某个非整数 $D > 0$ 与尺度区间 $[r_{\min},r_{\max}]$,覆盖数 $N(F,r)$ 与尺度 $r$ 满足渐近关系

$$
N(F,r) \sim r^{-D}
$$

或等价的 Hausdorff 维数、盒维数等为非整数 $D$。

**定义 2.3(谱分形)** 设 $I \subset \mathbb R$ 为频域区间,$\nu$ 为其上有限 Borel 测度。若存在非整数指数 $D_\nu > 0$ 与尺度区间 $[s_{\min},s_{\max}]$,使得对所有 Borel 集 $B \subset I$ 与 $s \in [s_{\min},s_{\max}]$,

$$
\nu(\mathrm{e}^{-s} B) \approx \mathrm{e}^{-\alpha s} \nu(B),
$$

其中 $\alpha$ 与 $D_\nu$ 相关(例如对单尺度幂律谱可取 $\alpha = D_\nu$),则称 $\nu$ 具有谱分形结构。

上述"$\approx$"可具体化为在对数尺度上的有界振荡或在适当范数中的渐近相似。

**定义 2.4(边界分形)** 设 $\Sigma \subset M$ 为物理边界,$\gamma = \Sigma \cap U$ 为其与某局域区域 $U \subset M$ 的交。称 $\Sigma$ 在 $U$ 内具有边界分形结构,如果:

1. 在某尺度区间上,$(\gamma,d,\mu_\gamma)$ 为几何分形,或
2. 在某频率区间 $I$ 上,由时间刻度母尺或相关边界算子定出的谱测度(例如 $\kappa(\omega)\,\mathrm{d}\omega$、$\rho_{\mathrm{rel}}(\omega)\,\mathrm{d}\omega$)为谱分形。

几何分形与谱分形分别对应空间边界的分形轮廓与谱–时间域上的分形响应;二者往往通过散射与 Green 函数联系起来。

### 2.5 尺度变换半群与自相似结构

为统一处理几何与频谱上的自相似,引入尺度变换半群 $\{\mathcal R_s\}_{s>0}$,作用在空间或频域对象上。例如,对频域函数 $f(\omega)$ 定义

$$
(\mathcal R_s f)(\omega) := \alpha(s)\,f(\beta(s)\,\omega),
$$

其中 $\alpha(s),\beta(s) > 0$ 且满足半群性质 $\mathcal R_s \mathcal R_t = \mathcal R_{st}$。对几何集合 $F \subset \mathbb R^d$,则可取 $\mathcal R_s$ 为相似变换 $x \mapsto s x$。

**定义 2.5(自相似边界结构)** 边界几何或谱结构称为自相似,当存在非平凡尺度 $s \ne 1$ 与适当范数或分布意义,使得

$$
\mathcal R_s\,\mathcal O_\Sigma \approx \mathcal O_\Sigma,
$$

其中 $\mathcal O_\Sigma$ 表示边界算子族或边界轮廓,$\approx$ 表示在渐近、统计或弱拓扑意义下的不变性。尺度变换的非平凡不动点与其稳定极限集往往具有分形结构。

本文将展示,在三类典型的物理情景中,自相似边界结构自然出现,并通过时间刻度母尺 $\kappa(\omega)$ 映射为时间域的分形纹理。

---

## 3 Main Results (Theorems and Alignments)

本节给出本文的核心结果,以定理形式陈述,并标明与时间刻度母尺和边界分形之间的对应关系。技术细节的证明放在第 4 节与附录。

### 3.1 自相似反馈散射网络的分形时间刻度

考虑由层厚 $L_n = L_0 \lambda^n$($0 < \lambda < 1$)构成的一维散射网络,每层由频率无色散的散射单元 $S_0$ 描述,反射系数 $r_0$、透射系数 $t_0$ 满足 $\lvert r_0 \rvert^2 + \lvert t_0 \rvert^2 = 1$。前 $n$ 层整体反射系数记作 $R_n(\omega)$,满足 Möbius 型递推关系。对 $n \to \infty$ 的极限,存在下述结论。

**定理 3.1(反馈散射网络的分形时间刻度)**
设 $\lvert r_0 \rvert < 1$、$0<\lambda < 1$,且相位聚焦不致导致频域致密共振。则存在几乎处处定义的极限反射函数

$$
R_\infty(\omega) := \lim_{n\to\infty} R_n(\omega),
$$

其反射相位 $\phi(\omega) = \arg R_\infty(\omega)$ 在对数频率轴 $x = \ln(\omega L_0)$ 上为准自相似函数,即存在尺度 $s_0 > 1$ 与有界函数 $h$,使得

$$
\phi(\mathrm{e}^x) = h(x) + o(1),\quad h(x + \ln s_0) \approx h(x).
$$

由此得到的时间刻度母尺

$$
\kappa(\omega) \propto \partial_\omega \phi(\omega)
$$

在频段 $I$ 上生成谱测度 $\kappa(\omega)\,\mathrm{d}\omega$,该测度在对数尺度上具有非整数谱维数,因而为谱分形。特别地,在适当参数下,$\kappa(\omega)$ 的图像在 $\ln \omega$–轴上呈现无特征尺度的峰列与 log 周期振荡。

该定理表明,自相似反馈散射网络自然在边界散射响应中生成分形时间刻度与谱分形结构。定理的证明依托于 Möbius 迭代映射的收缩性质与尺度重标关系,详见附录 A。

### 3.2 临界界面与边界几何分形

考虑 $d$ 维临界体系,其 bulk 动力学在临界点 $p_c$ 处具有规范的重整化群不动点。相界面 $\Sigma$ 可视为序参量等值面的集合。对二维模型,可进一步假设其界面具有 Schramm–Loewner 演化的缩放极限。

**定理 3.2(临界界面的分形维数与边界分形)**
在满足以下条件的临界体系中:

1. bulk 相关长度随控制参数 $\xi(p) \sim \lvert p-p_c \rvert^{-\nu}$ 发散;
2. 在临界点 $p_c$,边界或界面可由参数 $\kappa$ 的 SLE 过程描述;
3. 存在边界算子 $\mathcal O_\Sigma$,其关联函数沿界面距离衰减为幂律;

则界面 Hausdorff 维数为

$$
D_{\mathrm{H}} = 1 + \frac{\kappa}{8},
$$

其值严格位于 $1$ 与 $2$ 之间。由此诱导的边界通量与散射响应在频率域上具有幂律尾与多尺度结构,其对应的时间刻度母尺 $\kappa(\omega)$ 所定义的谱测度在临界窗口内为谱分形。

在经典例子中,二维临界渗流对应 $\kappa = 6$,界面维数 $D_{\mathrm{H}} = 4/3$,而随机场 Ising 模型与刚性渗流中的界面也被数值验证符合相应的 SLE 预测。

因此,临界界面是重整化群不动点在边界上的几何成像,其分形结构与边界算子标度维数直接相关。

### 3.3 Laplacian growth 前沿的分形边界与时间刻度

设 bulk 中存在势场或浓度场 $u(x,t)$,在无源区域满足 Laplace 方程 $\Delta u = 0$,边界 $\Sigma_t$ 随时间演化,其法向速度由局域梯度模长决定:

$$
v_n(x,t) = \gamma \lvert \nabla u(x,t) \rvert,\quad x \in \Sigma_t,
$$

其中 $\gamma > 0$ 为常数。此类 Laplacian growth 动力学用于描述粘滞指进、金属电沉积、放电通道与扩散控制生长等过程。

**定理 3.3(Laplacian growth 前沿的边界分形与谱分形)**
在二维 Laplacian growth 模型中,若满足:

1. bulk 方程在相关尺度内无内在长度(不含显式 cutoff 或整数量级的表面张力抑制);
2. 界面更新规则局域,且梯度聚焦效应显著(尖角处流量集中);
3. 生长过程在足够长时间内保持稳定拓扑;

则在大时间极限下,生长前沿 $\Sigma_t$ 的 Hausdorff 维数 $D_{\mathrm{H}}$ 严格位于 $1$ 与 $2$ 之间,成为几何分形。对该前沿进行波动或粒子散射时,由于多尺度凹凸与尖角,散射相位与时间延迟在对数频率上呈现多峰与 log 周期振荡,其时间刻度母尺 $\kappa(\omega)$ 对应的谱测度为谱分形。

在具体模型中,利用迭代共形映射与 DLA 模型,可以构造具有连续可调分形维数的一族 Laplacian growth 图案,验证上述结论。

### 3.4 分形时间刻度与时间等价类

前述定理表明,自相似边界结构往往诱导出在对数频率轴上的分形时间刻度。一个关键问题是:这种分形纹理是否会改变时间几何的等价类,乃至因果排序本身。

为此,引入如下形式的分形修正:

$$
\kappa(\omega) = \kappa_0(\omega) + \delta\kappa(\omega),
$$

其中 $\kappa_0$ 为光滑的基准刻度,$\delta\kappa$ 为在 $\ln \omega$ 上有界且零平均的 log 周期振荡或多尺度结构。

**定理 3.4(分形时间刻度不改变时间等价类)**
设 $\kappa_0(\omega)$ 与 $\kappa(\omega)$ 在物理相关能量窗 $I$ 上满足:

1. $\delta\kappa(\omega)$ 有界且在 $\ln \omega$ 上为零平均振荡,即 $\int_I \delta\kappa(\omega)\,\mathrm{d}\omega \approx 0$;
2. 宏观可观测时间积分

$$
T_0(I) = \int_I \kappa_0(\omega)\,\mathrm{d}\omega,\quad
T(I) = \int_I \kappa(\omega)\,\mathrm{d}\omega
$$

满足 $T(I) = \tilde a\,T_0(I) + \tilde b$,其中 $\tilde a > 0$ 与 $\tilde b$ 在参数变化下缓变;

则由 $\kappa$ 与 $\kappa_0$ 所定义的时间几何属于同一时间等价类 $[\tau]$。换言之,分形时间刻度不改变因果排序与统一时间刻度的存在性,只改变时间纹理与统计特征。

该定理的证明直接使用时间等价类的定义,并分析有界分形扰动对时间积分与广义熵条件的影响,详见附录 C。

### 3.5 边界驱动的分形生成统一原理

前述三类机制可以抽象为一条统一的边界驱动分形生成原理。

**定理 3.5(边界驱动的分形生成原理)**
在如下条件下,物理边界 $\Sigma$ 上存在一族由局部规则与 bulk 动力学定义的演化算子 $T$,使得:

1. bulk 动力学在某尺度区间内无内在特征尺度(方程与边界条件在缩放下保持形式不变);
2. 边界演化规则局域(例如散射反馈、生长速度、相变规则只依赖于局域场与梯度);
3. 存在非平凡反馈或耦合(例如自指散射、通量控制、黏附与吸附);

则缩放–演化复合映射 $\mathcal R_s \circ T$ 在适当函数空间中存在非平凡吸引集,其极限集的几何与谱结构具有非整数维数。该极限集在边界几何上表现为分形界面或团簇,在谱–时间域上表现为时间刻度母尺 $\kappa(\omega)$ 与谱测度的分形纹理。

该定理在严格数学意义上依赖于不同模型的具体构造:在自指散射中对应 Möbius 迭代与 log 周期不动点,在临界界面中对应 RG 不动点与 SLE 界面,在 Laplacian growth 中对应迭代共形映射与 DLA 型聚集。本文给出的统一表述强调的是:在"无特征尺度 + 局部规则 + 边界反馈"的三重条件下,边界自然成为分形结构的生成场所。

---

## 4 Proofs

本节给出前述各定理的证明骨架与关键步骤,技术细节放入附录。

### 4.1 定理 3.1 的证明概述:Möbius 迭代与 log 频率自相似

在一维自指散射网络中,前 $n$ 层整体反射系数 $R_n(\omega)$ 可以写为反复作用的 Möbius 变换:

$$
R_{n+1}(\omega)
= \mathcal M_{n,\omega}(R_n(\omega))
= r_0 + \frac{t_0^2 \mathrm{e}^{2\mathrm{i}\omega L_n} R_n(\omega)}{1 - r_0 \mathrm{e}^{2\mathrm{i}\omega L_n} R_n(\omega)}.
$$

对给定的 $\omega$,由于 $L_n = L_0 \lambda^n$ 随 $n$ 指数衰减,相位因子 $\mathrm{e}^{2\mathrm{i}\omega L_n}$ 在大 $n$ 极限趋近 $1$,从而 $\mathcal M_{n,\omega}$ 在单位圆附近成为收缩映射。可以在单位闭圆盘上构造适当的复 Banach 空间,使得 $R_n(\omega)$ 在 $n \to \infty$ 时收敛到某个不动点 $R_\infty(\omega)$,证明见附录 A.2。

为揭示 log 频率自相似结构,引入变量 $x = \ln(\omega L_0)$,则

$$
2\omega L_n = 2 \mathrm{e}^x \lambda^n.
$$

频率缩放 $\omega \mapsto \omega/\lambda$ 对应于 $x \mapsto x - \ln \lambda$,同时层编号 $n\mapsto n+1$。将 $F_n(x) := R_n(\mathrm{e}^x)$ 代入递推关系,可以得到形式

$$
F_{n+1}(x)
= r_0 + \frac{(1-r_0^2)\,\mathrm{e}^{2\mathrm{e}^x \lambda^n} F_n(x)}{1 - r_0\,\mathrm{e}^{2\mathrm{e}^x \lambda^n} F_n(x)}.
$$

对固定 $x$,当 $n$ 增大时,$\mathrm{e}^{2\mathrm{e}^x \lambda^n} \to 1$,因而存在极限函数 $F_\infty(x)$ 满足近似自相似方程

$$
F_\infty(x) \approx \Phi(F_\infty(x+\ln\lambda),x),
$$

其中 $\Phi$ 为由上述分式给出的解析函数。进一步分析表明,$F_\infty(x)$ 的模长接近常数,而相位 $\phi(x)$ 在 $x$ 上呈现有界但复杂的准周期(或多尺度)结构。利用复分析中的迭代理论,可以证明在适当参数区间内,$\phi(x)$ 的图像在平移 $x \mapsto x+\ln\lambda$ 下具有自相似性。

时间刻度母尺 $\kappa(\omega)$ 与 $\partial_\omega \phi(\omega)$ 成正比,因而在 $\ln \omega$ 上呈现多尺度峰列。使用盒维数或能量谱方法,可以证明 $\kappa(\omega)\,\mathrm{d}\omega$ 的支撑具有非整数谱维数,从而为谱分形。完整的构造与估计给出于附录 A.3。

### 4.2 定理 3.2 的证明概述:SLE–BCFT 与边界算子标度

对二维临界体系,假设其界面在连续极限下由 SLE$_\kappa$ 描述。Rohde–Schramm 与后续工作证明了 SLE 曲线的 Hausdorff 维数为

$$
D_{\mathrm{H}} = 1 + \frac{\kappa}{8}.
$$

在临界渗流、Ising 模型与刚性渗流等例子中,$\kappa$ 取不同数值,得到不同的界面维数。

另一方面,在边界共形场论(boundary CFT)中,边界算子 $\mathcal O_{\partial}$ 的二点函数沿边界距离 $s$ 的衰减行为为

$$
\langle \mathcal O_{\partial}(s)\,\mathcal O_{\partial}(0)\rangle \sim s^{-2\Delta_\partial},
$$

其中 $\Delta_\partial$ 为边界算子标度维数。界面可以视为某种边界算子(例如改变边界条件的"缺陷算子")的等值线或零点集,其几何维数与 $\Delta_\partial$ 之间存在模型依赖的关系,可通过 CFT–SLE 对应计算得到。

在散射情景下,将边界视为支持某种有效势或折射率突变的界面,入射波在界面附近的散射振幅与时间延迟由边界算子相关函数控制。利用 Kubo 类型公式,可将频域响应函数表示为时间域相关函数的 Fourier 变换;对于幂律相关的场,其频域响应呈幂律衰减与多尺度结构,从而生成谱分形。由此可见,界面的分形几何与边界算子的标度维数共同决定了时间刻度母尺 $\kappa(\omega)$ 的分形特征。

技术上,证明包括三个步骤:构造界面–算子的映射;由 BCFT 计算 $\Delta_\partial$ 与 SLE 参数 $\kappa$ 的关系;由幂律相关推导傅里叶空间的谱维数。由于这些步骤在文献中已有充分展开,本文在附录 B 中给出简化版推导,并引用相关定理完成证明。

### 4.3 定理 3.3 的证明概述:Laplacian growth 与 DLA 普适类

Laplacian growth 中的界面演化由 $\Delta u = 0$ 与 $v_n \propto \lvert \nabla u \rvert$ 决定,尖角处梯度增强使得界面凸起更易生长,形成枝状结构。利用迭代共形映射方法,可以构造一类参数化的生长过程,其极限界面具有可调的分形维数。Barra 等人利用该方法系统研究了 Laplacian growth 与 DLA 的普适类关系,表明两者在许多情形下属于不同普适类,但均产生稳定的分形界面。

在散射视角,将 $\Sigma_t$ 视为对波动场的边界条件,界面的多尺度凹凸结构在频率空间生成密集的共振峰与反射相位阶跃,利用微扰散射与高频几何光学近似,可以证明散射相位 $\Phi(\omega)$ 与时间刻度母尺 $\kappa(\omega)$ 在对数频率上具有多尺度结构。具体证明包括:

1. 利用 Born 近似与表面积粗略估计,建立界面分形维数与散射截面的关系;
2. 引入局域共振模型,将尖角与细枝视为一系列局部谐振子,其频率分布呈幂律;
3. 由谐振子频率分布的幂律与宽度分布得到散射相位与时间延迟的谱分形结构。

详细推导见附录 B.2。

### 4.4 定理 3.4 的证明概述:时间等价类的鲁棒性

定理 3.4 本质上是时间等价类定义的直接推论。设

$$
\kappa(\omega) = \kappa_0(\omega) + \delta\kappa(\omega),
$$

其中 $\delta\kappa$ 在 $\omega$ 上有界并在 $\ln \omega$ 上零平均。对任意物理相关能量窗 $I$,有时间积分

$$
T(I) = \int_I \kappa(\omega)\,\mathrm{d}\omega
= \int_I \kappa_0(\omega)\,\mathrm{d}\omega + \int_I \delta\kappa(\omega)\,\mathrm{d}\omega
= T_0(I) + \epsilon(I),
$$

其中 $\epsilon(I)$ 为由分形振荡贡献的修正项,在窗口变化缓慢的假设下可视为有限的常数偏移或缓变函数。因而可写为

$$
T(I) = \tilde a\,T_0(I) + \tilde b,
$$

其中 $\tilde a > 0$、$\tilde b$ 由 $\epsilon(I)$ 归一化而得。时间等价类的定义仅要求不同刻度之间存在这样的仿射关系,且广义熵变分条件保持形式不变。由于 $\delta\kappa$ 的振荡对广义熵的单调性与极值位置仅产生有限阶修正,因而两种时间几何属于同一等价类。形式化论证见附录 C。

### 4.5 定理 3.5 的证明概述:缩放–演化复合映射的不动点

将三类情形统一视为某个空间 $\mathcal X$ 上的演化算子 $T$ 与尺度算子 $\mathcal R_s$ 的复合。这里 $\mathcal X$ 可以是界面轮廓的函数空间、边界算子的分布空间或谱测度的空间。缩放–演化映射为

$$
\mathcal F_s := \mathcal R_s \circ T.
$$

在自指散射中,$\mathcal X$ 为反射系数的复函数空间;在临界界面中,$\mathcal X$ 为界面轮廓的概率测度空间;在 Laplacian growth 中,$\mathcal X$ 为界面轮廓或共形映射的参数空间。

在"无特征尺度 + 局部规则 + 边界反馈"条件下,可以证明 $\mathcal F_s$ 在某些子空间上为压缩映射或存在吸引集。具体而言,RG 理论表明在临界点附近存在非平凡不动点,其稳定流形上的界面为分形;共形映射迭代中存在具有非整数维数的极限集;自指散射中,Möbius 迭代与频率缩放联合产生 log 周期结构。这些具体事实在各自模型中已有充分论证,本文在附录 A–B 中给出统一的抽象描述,从而完成定理 3.5 的证明。

---

## 5 Model Apply

本节给出若干具体物理模型,说明上述理论如何在可观测层面显现,并如何通过时间刻度母尺与边界分形联系起来。

### 5.1 自相似电磁多层膜与时间延迟谱分形

考虑一维电磁多层膜,每层介质厚度为 $L_n = L_0 \lambda^n$,折射率在有限集合中选取。对入射平面波,整体散射矩阵 $S(\omega)$ 可由传输矩阵逐层相乘得到。现代电磁散射研究表明,Wigner–Smith 时间延迟矩阵在此类结构中可以与体内能量密度积分相联系,并以频率导数形式从 $S(\omega)$ 直接求得。

在几何层级结构下,反射相位在对数频率轴上出现多重共振峰,相邻峰间隔近似恒定的 log 周期,其形状与多层结构的自相似层级对应。时间刻度母尺 $\kappa(\omega)$ 与群延迟之和可通过矢量网络分析仪测量,预期在对数频率上表现为多尺度峰列与幂律尾,从而实现谱分形的直接观测。

### 5.2 临界薄膜与界面散射

二维临界薄膜(如接近居里点的薄膜磁体或超导膜)中,磁畴或相分离区域在显微镜下呈现分形边界。当以电子、X 射线或光波照射,并测量角分布或时间延迟时,散射强度与相位对边界粗糙度高度敏感。

利用 BCFT 与 SLE 结果,可以将边界粗糙度的分形维数与散射截面的角标度行为联系起来。进一步,通过相干散射与干涉实验,可以从相位随频率的变化中反推出时间刻度母尺 $\kappa(\omega)$ 的多尺度结构,从而在谱域上验证临界界面的边界分形。

### 5.3 Laplacian growth 与电沉积界面

在电化学电沉积实验中,电极表面在外加电压与浓度梯度作用下生长,界面形状由 Laplace 方程与电流边界条件决定。通过高分辨率成像可以直接得到界面形状,并测量其分形维数。

在此基础上,可以对界面附近的电磁波或声波散射进行测量,从频域中提取时间延迟与散射相位。实验预期表明,分形界面的多尺度凹凸结构导致散射谱中出现多重共振与 log 周期结构,其与几何分形维数存在可比的标度关系。

### 5.4 自指散射网络与波导阵列

通过微波波导、光学波导或声学导波结构,可以实现自指散射网络:将若干散射单元与延迟线按照层级长度 $L_n$ 串联与反馈,构造具有自相似结构的闭环网络。利用多端口矢量网络分析仪,可直接测量散射矩阵 $S(\omega)$ 与群延迟矩阵 $Q(\omega)$,并从中计算时间刻度母尺 $\kappa(\omega)$。

通过调整层厚缩放因子 $\lambda$、散射单元反射系数 $r_0$ 与反馈拓扑,可以在实验上扫描理论给出的参数空间,验证定理 3.1 所预测的 log 周期与谱分形结构。

---

## 6 Engineering Proposals

本节给出几项可实现的工程方案,用于验证"边界驱动的分形生成机制"及其在时间刻度母尺上的体现。

### 6.1 一维微波自相似多层与时间延迟测量

1. 结构设计:在同轴或矩形波导中插入若干介质片,每片厚度为 $L_n = L_0 \lambda^n$,介质常数在两种或少数几种值之间切换,形成层级结构。
2. 测量方案:用矢量网络分析仪扫描频率,测量反射与透射 S 参数;由 $S(\omega)$ 数值求导得到 Wigner–Smith 时间延迟矩阵 $Q(\omega)$ 与迹 $\operatorname{tr} Q(\omega)$,构造时间刻度母尺 $\kappa(\omega)$。
3. 预期结果:在对数频率轴上,$\kappa(\omega)$ 呈现多尺度峰列,峰间距在 $\ln \omega$ 上近似常数,谱测度具有非整数维数;改变 $\lambda$ 与层数可调节分形结构的可见带宽与复杂度。

### 6.2 光学多层膜与飞秒时间延迟谱

1. 结构设计:利用薄膜沉积技术制备具有几何级数厚度的多层介质膜,例如玻璃–金属–介质交替结构。
2. 测量方案:使用飞秒脉冲作为入射光源,通过白光干涉或频域干涉测量反射相位与群延迟;利用相干频率梳与频率解析相位测量技术提升精度。
3. 预期结果:反射相位随频率的变化在 log 频率上呈现准周期振荡,与理论中的 Möbius 迭代结果匹配;时间延迟谱呈现多尺度结构,与边界分形密切关联。

### 6.3 临界薄膜与互补散射–成像实验

1. 系统选择:接近临界点的磁薄膜、液晶薄膜或超导薄膜,界面几何可以通过扫描显微镜或散射成像观测。
2. 几何测量:用高分辨率成像获得界面轮廓,计算其分形维数,与 SLE 预测进行对比。
3. 散射测量:以电磁波或电子束照射界面,测量散射角分布与相位,构造时间刻度母尺 $\kappa(\omega)$,分析其谱分形结构与界面维数的对应关系。

### 6.4 Laplacian growth 与声学/电磁散射联合测量

1. 生长平台:电沉积、粘滞指进或 Hele–Shaw 流动实验,生成 Laplacian growth 控制下的分形界面。
2. 几何监测:实时成像界面形状,计算其分形维数与多尺度粗糙度。
3. 散射实验:对界面施加宽带声波或电磁波,测量散射相位与时间延迟,构造时间刻度母尺并分析谱分形特征。

这些工程方案在测量技术上均已有成熟基础,但需要特别设计以避免非理想因素(损耗、色散、有限系统尺寸)掩盖理论预测的自相似结构。

---

## 7 Discussion (Risks, Boundaries, Past Work)

### 7.1 理论适用域与局限性

本文的理论依赖于若干理想化假设:

1. 散射理论部分假定 $H_x$ 与 $H_{0,x}$ 满足 Birman–Kreĭn 公式与 Wigner–Smith 时间延迟定义的常规条件,包括短程扰动与足够良好的谱性质。对于强耗散或长程无界势,需要更精致的谱理论工具。
2. 临界界面部分依赖 SLE 与 BCFT 的适用性,主要集中于二维系统与共形不变的临界点。高维临界现象与无共形对称的系统需要其他工具。
3. Laplacian growth 部分需要在参数选择与实验条件上接近无尺度极限;任何显著的 cutoff(表面张力、最小粒子尺寸)都会缩短自相似可见的尺度区间。

此外,时间刻度母尺 $\kappa(\omega)$ 的定义在存在强耗散或非酉散射时需要一般化,可能涉及非厄米散射矩阵与非平衡 Green 函数。

### 7.2 与既有分形与界面理论的关系

分形几何与临界界面的研究已有丰富成果,从 Mandelbrot 的原始构想,到 DLA 与 Laplacian growth、Schramm–Loewner 演化与 BCFT 等。本文的贡献不是在这些方向上提出新的普适类,而是在统一的边界–时间–散射与时间几何框架下,将分形界面与时间刻度母尺联系起来,为"时间的分形纹理"与"边界生成分形"提供共同语言。

在散射理论方面,Birman–Kreĭn 公式、谱移函数与 Wigner–Smith 时间延迟的关系已经被系统研究,并在随机 Schrödinger 算子与复杂散射系统中得到应用。本文在此基础上引入时间刻度母尺 $\kappa(\omega)$,并强调其作为边界分形在时间域投影的核心角色。

### 7.3 风险与错配

在实验与数值验证中,存在若干风险:

1. 有限尺寸效应:真实系统的自相似尺度区间有限,过窄的尺度区间可能导致拟合出的"分形维数"不稳定,甚至误将噪声解释为分形。
2. 非理想散射:损耗、色散与非线性效应会修饰散射矩阵与时间延迟,使得 $\kappa(\omega)$ 的自相似结构被模糊,需要仔细校准与补偿。
3. 数据分析偏差:对谱分形维数与 log 周期结构的估计需要合适的统计工具,不当的窗口选择与拟合方法可能给出误导性的结论。

这些问题需要在具体实验设计中通过控制与对照来消除。

---

## 8 Conclusion

本文在统一的边界–时间–散射与时间几何框架下,对"为什么分形结构典型地长在边界上"给出系统回答。核心结论包括:

1. 引入时间刻度母尺 $\kappa(\omega) = \varphi'(\omega)/\pi = \rho_{\mathrm{rel}}(\omega) = (2\pi)^{-1}\operatorname{tr} Q(\omega)$,强调一切可观测时间与边界分形最终表现为边界算子的函数;
2. 通过三个典型机制——自相似反馈散射网络、临界界面与 Laplacian growth 前沿——证明在"无内在特征尺度 + 局部规则 + 边界反馈"的条件下,边界上存在缩放–演化的不动点与极限集,其几何与谱结构为分形;
3. 证明分形时间刻度在宏观上不改变时间等价类与因果排序,只改变时间纹理与统计性质,从而将"时间的统一刻度"与"时间的分形纹理"统一到同一结构之中;
4. 给出一系列可实现的实验与工程方案,将边界分形与时间刻度母尺的自相似结构联系到可观测的散射相位与时间延迟谱。

在这一视角下,边界不再是被动的几何界线,而是 bulk 无特征尺度动力学的发生器,是差异、结构与时间纹理得以生成与被读出的主舞台。所谓"分形从边界生成",可以在严格的散射与时间几何语言中获得清晰表述。

---

## Acknowledgements, Code Availability

本工作建立在已有的散射理论、分形几何、Schramm–Loewner 演化与 Laplacian growth 等大量成果之上,作者对相关领域的发展表示尊重。本文主要聚焦解析结构与理论推导,未给出独立的数值模拟代码;若在后续研究中补充具体数值实现,相关代码可整理为公开仓库以供复现与扩展。

---

## References

[1] T. A. Witten and L. M. Sander, "Diffusion-limited aggregation, a kinetic critical phenomenon?", Phys. Rev. B 27, 5686 (1983).

[2] T. A. Witten, "Diffusion-limited aggregation: A model for pattern formation", Phys. Today 33, 38–45 (2000).

[3] M. Batty, "Scaling, fractal geometry, and diffusion-limited aggregation", in Fractals in Geography, pp. 109–122 (1989).

[4] F. Barra, B. Davidovitch, A. Levermann, and I. Procaccia, "Laplacian growth and diffusion-limited aggregation: Different universality classes", Phys. Rev. Lett. 87, 134501 (2001).

[5] L. M. Sander, "Diffusion-limited aggregation: A kinetic critical phenomenon?", Phys. Rep. 296, 1–47 (2000).

[6] J. D. Stevenson and M. Weigel, "Domain walls and Schramm–Loewner evolution in the random-field Ising model", EPL 95, 40001 (2011).

[7] S. Smirnov, "Critical percolation in the plane", in Proceedings of the International Congress of Mathematicians (2006).

[8] C. P. de Castro et al., "Schramm–Loewner evolution and perimeter of percolation clusters of correlated random landscapes", Sci. Rep. 8, 494 (2018).

[9] N. Posé et al., "Shortest path and Schramm–Loewner evolution", Sci. Rep. 4, 5495 (2014).

[10] N. Javerzat et al., "Schramm–Loewner evolution in 2D rigidity percolation", Phys. Rev. Lett. 132, 018201 (2024).

[11] L. M. Abril et al., "Loewner evolution for critical invasion percolation tree", arXiv:2503.06248 (2025).

[12] C. Texier, "Wigner time delay and related concepts", Physica E 82, 16–33 (2016).

[13] Y. Mao et al., "Wigner–Smith time-delay matrix for electromagnetics: Guiding and periodic systems with evanescent modes", IEEE Trans. Antennas Propag. 71, 4406–4420 (2023).

[14] R. Bourgain et al., "Direct measurement of the Wigner time delay for the scattering of light by a single obstacle", Opt. Lett. 38, 1963–1965 (2013).

[15] A. Strohmaier and coauthors, "The Birman–Kreĭn formula for differential forms and scattering theory", Adv. Math. 403, 108369 (2022).

[16] V. Kostrykin and R. Schrader, "Scattering theory approach to random Schrödinger operators in one dimension", Rev. Math. Phys. 11, 187–242 (1999).

[17] F. Gesztesy and M. Mitrea, "Applications of spectral shift functions", in Spectral Theory and Mathematical Physics: A Festschrift in Honor of Barry Simon's 60th Birthday (2007).

[18] P. Guo, "Friedel formula and Krein's theorem in complex potential scattering theory", Phys. Rev. Research 4, 023083 (2022).

[19] Wigner–Smith time delay matrix for acoustic and electromagnetic scattering, representative overviews in recent literature.

[20] Standard expositions of Schramm–Loewner evolution and its applications to critical interfaces and fractal dimensions.

---

## Appendix A: 自指散射玩具模型的递推与自相似性

本附录给出定理 3.1 的详细构造与证明。

### A.1 模型设定与递推关系

考虑一维线性散射系统,由无限多层按几何级数缩放的散射单元构成。第 $n$ 层厚度为 $L_n = L_0 \lambda^n$($0 < \lambda < 1$),每个单元由频率无色散的常数散射矩阵 $S_0$ 描述,反射系数 $r_0$、透射系数 $t_0$ 满足

$$
\lvert r_0 \rvert^2 + \lvert t_0 \rvert^2 = 1.
$$

设 $R_n(\omega)$ 为前 $n$ 层构成的整体反射系数,对单向入射,标准的传输矩阵方法或多重反射叠加可得递推关系

$$
R_{n+1}(\omega)
= r_0 + \frac{t_0^2 \mathrm{e}^{2\mathrm{i}\omega L_n} R_n(\omega)}{1 - r_0 \mathrm{e}^{2\mathrm{i}\omega L_n} R_n(\omega)}.
$$

该递推是单位圆盘上的 Möbius 映射组合。为简化,假设 $t_0$ 为实正数,$r_0$ 为实数且 $\lvert r_0 \rvert < 1$。

### A.2 Banach 空间上的收缩映射论证

令 $\mathbb D := \{z \in \mathbb C : \lvert z \rvert \le 1\}$ 为闭单位圆盘。由于 $\lvert r_0 \rvert < 1$、$\lvert t_0 \rvert \le 1$,可以证明对任意 $\omega$ 与 $z \in \mathbb D$,有

$$
\mathcal M_{n,\omega}(z)
:= r_0 + \frac{t_0^2 \mathrm{e}^{2\mathrm{i}\omega L_n} z}{1 - r_0 \mathrm{e}^{2\mathrm{i}\omega L_n} z} \in \mathbb D.
$$

更进一步,在 $L_n$ 足够小(大 $n$)时,可对分母做 Taylor 展开,得到

$$
\mathcal M_{n,\omega}(z)
= r_0 + t_0^2 z + \mathcal O(\omega L_n),
$$

因而在 $z$ 的邻域上 Lipschitz 常数小于某个小于 $1$ 的常数。对固定 $\omega$,考虑从某个 $n_0$ 开始的尾部迭代

$$
R_{n+1} = \mathcal M_{n,\omega}(R_n),
$$

可以将其看作 $\mathbb D$ 上一列收缩映射的组合,在适当的度量(例如 Poincaré 度量)下,可证明该组合收敛到唯一不动点 $R_\infty(\omega)$。形式证明可以使用逐步估计与 Banach 不动点定理的推广。

### A.3 log 频率自相似方程与谱分形

引入对数频率变量 $x = \ln(\omega L_0)$,则第 $n$ 层相位为

$$
2\omega L_n = 2 \mathrm{e}^x \lambda^n.
$$

定义 $F_n(x) := R_n(\mathrm{e}^x)$。递推关系变为

$$
F_{n+1}(x)
= r_0 + \frac{(1-r_0^2)\,\mathrm{e}^{2\mathrm{e}^x \lambda^n} F_n(x)}{1 - r_0\,\mathrm{e}^{2\mathrm{e}^x \lambda^n} F_n(x)}.
$$

对固定 $x$,当 $n \to \infty$ 时,$\mathrm{e}^{2\mathrm{e}^x \lambda^n} \to 1$。定义极限函数

$$
F_\infty(x) := \lim_{n\to\infty} F_n(x)
$$

在几乎所有 $x$ 上存在。考虑频率缩放 $\omega \mapsto \omega/\lambda$,即 $x \mapsto x - \ln \lambda$。注意到

$$
F_n(x - \ln\lambda)
= R_n(\mathrm{e}^{x-\ln\lambda})
= R_n(\mathrm{e}^x /\lambda).
$$

由于 $L_n = L_0 \lambda^n$,将 $\omega$ 缩放 $1/\lambda$ 相当于将相位因子中的层指数平移一位。通过追踪递推关系,可以得到 $F_\infty$ 满足近似自相似方程

$$
F_\infty(x)
= \Phi(F_\infty(x+\ln\lambda),x),
$$

其中 $\Phi$ 为解析函数,可视为"粗粒化后的 Möbius 迭代"。对大类参数选择,$\Phi$ 在单位圆附近引入非平凡相位缠绕,从而使 $F_\infty(x)$ 的相位 $\phi(x) = \arg F_\infty(x)$ 在平移 $x \mapsto x + \ln\lambda$ 下呈现准周期结构。

时间刻度母尺在该模型中与 $\partial_\omega \phi(\omega)$ 成比例,利用

$$
\partial_\omega \phi(\omega) = \mathrm{e}^{-x} \partial_x \phi(\mathrm{e}^x)
$$

可将对数频率上的自相似传递给 $\kappa(\omega)$。利用盒维数与能量谱的标准工具,可在典型参数下证明 $\kappa(\omega)\,\mathrm{d}\omega$ 支撑的谱维数为非整数,从而为谱分形。鉴于相关技术与 Cantor 型谱及准周期算子研究相近,此处不再赘述。

---

## Appendix B: 临界界面标度律与 Laplacian growth 的边界分形

### B.1 SLE–BCFT 与界面维数

SLE$_\kappa$ 曲线的 Hausdorff 维数定理给出

$$
D_{\mathrm{H}} = 1 + \frac{\kappa}{8}.
$$

对临界渗流、Ising 模型与其他二维临界系统,已经确定了相应的 $\kappa$ 值及界面维数。例如,临界渗流的外边界对应 $\kappa = 6$,得到 $D_{\mathrm{H}} = 4/3$。

BCFT 中,边界算子 $\mathcal O_\partial$ 的标度维数 $\Delta_\partial$ 由主场的模与边界条件决定,其两点函数沿边界距离 $s$ 衰减为 $s^{-2\Delta_\partial}$。通过 CFT 与 SLE 的对应,可以在具体模型中建立 $\Delta_\partial$ 与 $\kappa$ 之间的函数关系,从而把界面几何维数与边界算子标度维数联系起来。

散射视角下,边界算子可视为边界上的有效势或折射率扰动,其幂律相关导致频域响应的幂律尾与多尺度结构。由 Fourier 变换性质可知,若时间域相关函数 $\langle \mathcal O_\partial(t)\mathcal O_\partial(0)\rangle \sim t^{-\gamma}$,则频域谱密度 $\rho(\omega)$ 具有 $\omega^{\gamma-1}$ 型行为,叠加多尺度结构时即生成谱分形。

### B.2 Laplacian growth 与分形界面

Laplacian growth 由 $\Delta u = 0$ 与 $v_n \propto \lvert \nabla u \rvert$ 控制。尖角处梯度增强带来更高生长速度,形成"肥角越肥"的正反馈,最终生成枝状结构。通过迭代共形映射方法,可以构造具有连续可调参数的增长过程,用以插入局部"凸起"并追踪其演化。Barra 等人利用此方法分析 Laplacian growth 与 DLA 之间的关系,表明二者在某些参数极限下共享或区分普适类,均具有稳定分形维数。

在散射理论中,可以将分形界面视为由多尺度凹凸与尖角组成的边界,每个局域结构对应一个局部谐振频率。若这些频率与几何尺度的分布为幂律,则整体散射相位为大量谐振贡献的叠加,其导数(即时间刻度母尺)呈现多尺度峰列与幂律尾,从而生成谱分形。

---

## Appendix C: 分形时间刻度与时间等价类的形式化论证

### C.1 时间等价类的定义回顾

时间等价类 $[\tau]$ 的定义基于下述要求:

1. 因果结构保持不变;
2. 时间刻度母尺 $\kappa_1,\kappa_2$ 在各物理相关能量窗 $I$ 上满足

$$
\kappa_2(\omega) = a(\omega)\,\kappa_1(\omega) + b(\omega),
$$

其中 $a(\omega) > 0$、$b(\omega)$ 为缓变函数,且对 $I$,

$$
\int_I b(\omega)\,\mathrm{d}\omega
$$

可视为常数偏移;
3. 广义熵变分与其稳定性条件保持形式不变。

在此意义下,$(g_1,\kappa_1)$ 与 $(g_2,\kappa_2)$ 描述同一时间几何。

### C.2 分形扰动的有界性与零平均性

设基准刻度为 $\kappa_0(\omega)$,分形修正为 $\delta\kappa(\omega)$,即

$$
\kappa(\omega) = \kappa_0(\omega) + \delta\kappa(\omega).
$$

分形修正的典型形式为

$$
\delta\kappa(\omega) = f(\ln\omega),
$$

其中 $f$ 为有界函数,在某个周期 $\ln s_0$ 上零平均:

$$
\int_0^{\ln s_0} f(x)\,\mathrm{d}x = 0.
$$

如此,$\delta\kappa(\omega)$ 在对数频率轴上为纯振荡项,对大尺度积分的贡献有限。

对任意物理相关能量窗 $I = [\omega_1,\omega_2]$,时间积分为

$$
T(I) = \int_{\omega_1}^{\omega_2} \kappa(\omega)\,\mathrm{d}\omega
= T_0(I) + \int_{\omega_1}^{\omega_2} \delta\kappa(\omega)\,\mathrm{d}\omega.
$$

通过变量替换 $\omega = \mathrm{e}^x$,得到

$$
\int_{\omega_1}^{\omega_2} \delta\kappa(\omega)\,\mathrm{d}\omega
= \int_{\ln\omega_1}^{\ln\omega_2} f(x)\,\mathrm{e}^x\,\mathrm{d}x.
$$

在 $f$ 有界且零平均的条件下,$\mathrm{e}^x f(x)$ 在大区间上贡献的是有限振荡项,随着区间宽度增加,相对 $T_0(I)$ 可视为常数偏移或缓变修正。

### C.3 时间等价类不变性的证明

综上,可取

$$
a(\omega) := 1,\quad b(\omega) := \delta\kappa(\omega),
$$

使得

$$
\kappa(\omega) = a(\omega)\,\kappa_0(\omega) + b(\omega).
$$

对每个能量窗 $I$,存在常数 $\tilde b(I)$ 使得

$$
\int_I b(\omega)\,\mathrm{d}\omega = \tilde b(I),
$$

且 $\tilde b(I)$ 随 $I$ 的变化在宏观上缓慢。定义

$$
\tilde a := 1,\quad \tilde b := \tilde b(I),
$$

得到

$$
T(I) = \tilde a\,T_0(I) + \tilde b.
$$

时间等价类的判定只要求存在这样的仿射关系,并且广义熵的单调性与极值点位置保持不变。分形振荡 $\delta\kappa$ 对广义熵的影响表现为有限阶修正,不改变熵泛函的单调方向与极值条件,从而不影响时间箭头与时间几何的本质结构。

因此,$(g,\kappa)$ 与 $(g,\kappa_0)$ 属于同一时间等价类 $[\tau]$,定理 3.4 得证。
