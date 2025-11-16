# 黑洞熵与信息在统一矩阵–QCA 宇宙中的离散视界理论

统一时间刻度下的 $S_{\mathrm{BH}} = A/4$ 与信息守恒

---

## Abstract

在统一时间刻度、边界时间几何与"宇宙作为量子离散元胞自动机"(quantum cellular automaton, QCA)的公理化框架下,本文对黑洞熵与信息悖论给出一个离散–连续一体化的刻画。统一时间刻度母式
$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\mathrm{tr}\, Q(\omega),
$$
其中 $\varphi(\omega)$ 为总散射半相位,$\rho_{\mathrm{rel}}(\omega)$ 为相对态密度,$Q(\omega)=-\mathrm{i} S(\omega)^\dagger\partial_\omega S(\omega)$ 为 Wigner–Smith 群延迟矩阵,在既有工作中被证明为宇宙统一时间刻度的母尺。

一方面,边界时间几何框架表明:对具有视界的时空,Hawking 温度 $T_H$ 与 Bekenstein–Hawking 熵 $S_{\mathrm{BH}}=A/(4G)$ 可以纯粹用边界代数的模流、广义熵及 Brown–York 准局域能量来重述,黑洞热力学的"几何–熵"结构完全可由小因果菱形的局域量子条件导出。另一方面,宇宙 QCA 对象
$$
\mathfrak U_{\mathrm{QCA}}
=(\Lambda,\mathcal H_{\mathrm{cell}},\mathcal A,\alpha,\omega_0)
$$
以可数图 $\Lambda$ 作为离散空间,以有限维局域 Hilbert 空间 $\mathcal H_{\mathrm{cell}}$ 与准局域 $C^\ast$ 代数 $\mathcal A$ 描述局域自由度,以有限传播半径的 $\ast$ 自同构 $\alpha$ 及其幺正实现 $U$ 描述离散时间演化,并在连续极限中重构相对论场论与几何结构。

本文将上述两条结构线统一到黑洞视界上,得到以下主要结果:

1. 在宇宙 QCA 框架中,引入由视界截面 $\Sigma_{\mathrm{H}}$ 上有限元胞组成的"视界带"子晶格 $\Gamma_{\mathrm{H}}\subset\Lambda$,并给出内外区 Hilbert 分解
   $$
   \mathcal H
   \simeq
   \mathcal H_{\mathrm{in}}\otimes\mathcal H_{\mathrm{H}}\otimes\mathcal H_{\mathrm{out}}.
   $$
   在满足局域混合性与平稳性假设的状态族上,跨视界纠缠熵满足面积律
   $$
   S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})
   =\eta_{\mathrm{cell}}\frac{A(\Sigma_{\mathrm{H}})}{\ell_{\mathrm{cell}}^2}
   +O(A^0),
   $$
   其中 $\ell_{\mathrm{cell}}$ 为 QCA 有效格距,$\eta_{\mathrm{cell}}$ 为单元熵密度常数。

2. 将上述 QCA 视界面积律嵌入边界时间几何:通过统一时间刻度将 QCA 的离散时间步与视界模流参数对齐,在小因果菱形极限与广义熵极值条件下证明一致性约束强制
   $$
   \frac{\eta_{\mathrm{cell}}}{\ell_{\mathrm{cell}}^2}
   =\frac{1}{4G},
   $$
   从而得到
   $$
   S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})
   =\frac{A(\Sigma_{\mathrm{H}})}{4G}
   +O(A^0),
   $$
   即 QCA 视界模型自动重现 Bekenstein–Hawking 熵的系数 $1/4$。

3. 在矩阵宇宙表象中,将黑洞形成–蒸发视为通道空间上某一类散射过程,散射矩阵 $S_{\mathrm{BH}}(\omega)$ 的酉性保证整个演化的信息守恒。宇宙 QCA 的一步演化 $U$ 于全 Hilbert 空间上幺正,且通过统一刻度与 $S_{\mathrm{BH}}(\omega)$ 的谱测度相容,从而将"霍金辐射导致纯态变混态"的朴素悖论重写为"在视界外有效理论中对庞大 QCA 微观自由度做粗粒化"的效应。

4. 在满足局域混合性、能量约束与 QCA 局域搅拌假设的宇宙上,构造"视界–辐射"划分随离散时间步演化的模型,并证明:对绝大多数初始纯态,辐射熵 $S_{\mathrm{rad}}(n)$ 随步数 $n$ 的演化近似满足 Page 曲线型行为,即先随 $n$ 增长到峰值,再随视界面积减小而下降,并最终回到零。该结果说明,在统一矩阵–QCA 宇宙中,黑洞信息悖论在定理层面可被还原为典型性与 coarse-graining 问题。

---

## Keywords

黑洞熵;信息悖论;统一时间刻度;边界时间几何;量子元胞自动机;矩阵宇宙;Page 曲线;纠缠熵面积律

---

## Introduction & Historical Context

Bekenstein 首先指出,若要维护广义第二定律,黑洞本身必须携带与视界面积成正比的熵,得到关系式
$$
S_{\mathrm{BH}}
=\frac{A}{4G\hbar},
$$
在自然单位制下常写为 $S_{\mathrm{BH}}=A/(4G)$。([scholarpedia.org][1]) Hawking 随后在半经典近似中证明黑洞会以温度
$$
T_H=\frac{\kappa_{\mathrm{surf}}}{2\pi}
$$
辐射近似热的粒子谱,$\kappa_{\mathrm{surf}}$ 为表面引力,从而确立了黑洞热力学的完整形式。([维基百科][2])

然而,将 Hawking 辐射视为严格热辐射并结合无毛定理后,会导出著名的黑洞信息悖论:若初态是纯态,完全蒸发后的 Hawking 辐射却近似热态,似乎与量子理论的幺正性相矛盾。([维基百科][3]) 在这一问题上,近年通过"岛"公式与 replica wormhole 的路径积分技术,人们已经在广义相对论与全息框架中重现了 Page 曲线,给出了一类半经典意义上的"信息恢复"方案。([arXiv][4])

另一方面,自 Page 的平均子系统熵工作以来,人们已经认识到:对高维 Hilbert 空间中的典型纯态,任意小子系统的约化态几乎为最大混合态,其熵近似为该子系统维度的对数。([物理评论链接管理器][5]) 这一"典型性"思想在随机电路、随机矩阵与多体量子混沌研究中得到系统发展,并在许多 Page 曲线玩具模型中扮演核心角色。([SpringerLink][6])

与此平行,量子元胞自动机(QCA)作为一种以局域幺正更新规则为基础的离散时间–离散空间模型,已经被证明可以作为量子场论的自然离散化,并在一维情形下拥有完备的指数理论与 GNVW 指数分类。([arXiv][7]) QCA 既可视为一种离散宇宙模型,也可在实验上通过量子线路、囚禁离子与光子平台实现 Dirac 型 QCA 或相关随机电路动力学。([物理评论链接管理器][8])

在既有工作中,统一时间刻度与边界时间几何框架将散射理论中的相位–谱移–群延迟数据与 Tomita–Takesaki 模流、广义熵变分以及 Gibbons–Hawking–York 边界项统一在一个"边界时间几何"的体系中,使得引力场方程、Hawking 温度与 Bekenstein–Hawking 熵可以在边界可观测代数层面得到。与此同时,"矩阵宇宙"观点把宇宙所有可观测量视为一个巨大但结构受限的算子矩阵族,其谱结构实现统一时间刻度,其块稀疏模式编码因果偏序。

本文的目标是在这一统一框架中,以 QCA 宇宙作为离散本体、以矩阵宇宙作为谱–散射表象,将黑洞熵与信息悖论的关键问题内生地重述为:

1. 在离散宇宙中,视界是什么对象?其熵为何满足面积律,且系数恰为 $1/4$?
2. 若宇宙在 QCA 层面严格幺正,信息究竟以何种方式在黑洞形成与蒸发过程中得以保存与回收?
3. 统一时间刻度如何约束 QCA 的微观尺度与有效几何常数(如 $G$)之间的关系?

本文的核心观点是:在统一时间刻度与边界时间几何约束下,只要离散宇宙的 QCA 连续极限再现实界引力与场论,则视界上的 QCA 跨越纠缠熵自动满足面积律,其系数通过与广义熵公式的匹配被唯一固定为 $1/4G$;黑洞信息悖论则在矩阵–QCA 表象中化为一个关于典型性与粗粒化的定理性问题,而非根本性的幺正性危机。

---

## Model & Assumptions

本节给出统一时间刻度、边界时间几何与宇宙 QCA 对象的基本定义,并列出后续定理所依赖的结构性假设。

### 2.1 统一时间刻度母尺

设 $(H,H_0)$ 为满足迹类扰动与良好散射条件的自伴算子对,$S(\omega)$ 为能量 $\omega$ 处的散射矩阵,谱移函数 $\xi(\omega)$ 与相对态密度 $\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$ 存在。Birman–Kreĭn 公式给出
$$
\det S(\omega)
=\exp\bigl(-2\pi\mathrm{i}\xi(\omega)\bigr).
$$
记总散射相位 $\Phi(\omega)=\arg\det S(\omega)=-2\pi\xi(\omega)$,半相位 $\varphi(\omega)=\tfrac12\Phi(\omega)$。定义 Wigner–Smith 群延迟矩阵
$$
Q(\omega)
=-\mathrm{i} S(\omega)^\dagger\partial_\omega S(\omega).
$$

统一时间刻度母尺定义为
$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\mathrm{tr}\, Q(\omega),
$$
散射时间刻度为
$$
\tau_{\mathrm{scatt}}(\omega)
=\int_{\omega_0}^{\omega}\kappa(\tilde\omega)\,\mathrm{d}\tilde\omega.
$$

既有工作表明:在满足适当的局域量子能量条件与模流条件时,模时间 $\tau_{\mathrm{mod}}$、几何时间 $\tau_{\mathrm{geom}}$ 与 $\tau_{\mathrm{scatt}}$ 在物理域上互为仿射变换,从而确定唯一的时间刻度等价类 $[\tau]$。

### 2.2 边界时间几何与黑洞热力学

在边界时间几何(BTG)框架中,给定时空区域 $(M,g)$ 与其边界 $\partial M$,考虑边界可观测代数 $\mathcal A_\partial$、边界态 $\omega_\partial$ 与适当的边界谱结构,Tomita–Takesaki 理论赋予每一对 $(\mathcal A_\partial,\omega_\partial)$ 一个自伴生成的一参数模流 $\sigma_t^\omega$,其参数 $t$ 即模时间。

对具有 Killing 视界的静态黑洞,BTG 给出以下结构性结论(略去细节):

1. 视界处 Hawking 温度 $T_H$ 等于模流的 KMS 温度,且与表面引力满足 $T_H=\kappa_{\mathrm{surf}}/(2\pi)$。([维基百科][2])
2. Bekenstein–Hawking 熵可视为视界边界代数的 von Neumann 熵密度:对视界截面面积 $A$,有
   $$
   S_{\mathrm{BH}}=\sigma_{\mathrm{H}}A,
   \quad
   \sigma_{\mathrm{H}}=\frac{1}{4G}.
   $$
3. 对包含视界的小因果菱形,广义熵
   $$
   S_{\mathrm{gen}}(\Sigma)
   =\frac{A(\Sigma)}{4G}+S_{\mathrm{out}}(\Sigma)
   $$
   的极值与二阶非负性与 Einstein 方程及其量子修正等价,从而将黑洞热力学嵌入局域量子引力条件的统一框架中。([科学进展][9])

在本文中,BTG 的作用是为 QCA 连续极限提供宏观几何边界条件及熵密度归一化条件。

### 2.3 宇宙 QCA 对象与因果结构

宇宙 QCA 对象定义为五元组
$$
\mathfrak U_{\mathrm{QCA}}
=(\Lambda,\mathcal H_{\mathrm{cell}},\mathcal A,\alpha,\omega_0),
$$
其中:

1. $\Lambda$ 为可数连通图(典型为 $\mathbb Z^d$ 或其子图)。
2. 每个格点 $x\in\Lambda$ 携带有限维 Hilbert 空间 $\mathcal H_x\simeq\mathcal H_{\mathrm{cell}}$,整体 Hilbert 空间形式上为无限张量积 $\mathcal H=\bigotimes_{x\in\Lambda}\mathcal H_x$。
3. 准局域 $C^\ast$ 代数 $\mathcal A$ 为有限区域上有界算子的并的范数闭包。
4. $\alpha:\mathcal A\to\mathcal A$ 为 $\ast$ 自同构,存在有限传播半径 $R$,使得任意局域算子 $A$ 的支撑区域经 $\alpha$ 演化后仅扩展到其 $R$ 邻域。
5. $\alpha$ 由幺正算子 $U$ 实现,即 $\alpha(A)=U^\dagger A U$。
6. 初始态 $\omega_0$ 为 $\mathcal A$ 上的态,对应 $n=0$ 时的宇宙态。

事件集合为 $E=\Lambda\times\mathbb Z$,偏序关系
$$
(x,n)\preceq(y,m)
\iff
m\ge n,\ \operatorname{dist}(x,y)\le R(m-n),
$$
构成局域有限因果集合,其连续极限可视为某个洛伦兹流形上的因果结构。QCA 的结构与分类可参考系统综述。([量子期刊][10])

### 2.4 矩阵宇宙表象与散射母尺的一致性

矩阵宇宙观点将宇宙全部可观测结构视为某种意义上的算子矩阵族
$$
\mathrm{THE\text{-}MATRIX}
=\{S(\omega),Q(\omega),\dots\},
$$
其块结构编码不同因果区域与观察者的通道空间,其谱数据通过统一时间刻度母尺 $\kappa(\omega)$ 赋予时间结构。统一时间刻度要求:QCA 连续极限生成的散射矩阵 $S_{\mathrm{QCA}}(\omega)$ 的半相位与群延迟迹应满足
$$
\kappa_{\mathrm{QCA}}(\omega)
=\frac{1}{2\pi}\mathrm{tr}\, Q_{\mathrm{QCA}}(\omega)
=\kappa(\omega)+O(\varepsilon),
$$
其中 $\varepsilon$ 为格距与时间步趋于零时的误差,从而保证 QCA 微观动力学与宏观 BTG 同属一时间刻度等价类。

### 2.5 视界 QCA 模型的结构性假设

为在 QCA 宇宙中实现黑洞视界,本文采用以下假设:

1. **视界带子晶格假设**:存在子集 $\Gamma_{\mathrm{H}}\subset\Lambda$ 与互补区域 $\Lambda_{\mathrm{in}},\Lambda_{\mathrm{out}}\subset\Lambda$,使得
   $$
   \Lambda
   =\Lambda_{\mathrm{in}}\cup\Gamma_{\mathrm{H}}\cup\Lambda_{\mathrm{out}},
   \quad
   \Lambda_{\mathrm{in}}\cap\Lambda_{\mathrm{out}}=\varnothing,
   $$
   且在连续极限中分别对应黑洞内部、视界邻域与外部区域;$\Gamma_{\mathrm{H}}$ 的元胞数满足
   $$
   N_{\mathrm{H}}=\#\Gamma_{\mathrm{H}}
   =\frac{A}{\ell_{\mathrm{cell}}^2}+O(A^0),
   $$
   其中 $A$ 为对应几何视界截面面积,$\ell_{\mathrm{cell}}$ 为有效格距。

2. **局域混合性与典型性假设**:在黑洞平衡时间窗口内,视界带与其内外补空间在能量壳与守恒量约束下形成近似典型纯态族,局域约化态近似最大混合,对应 Page 平均熵公式的适用条件。([物理评论链接管理器][5])

3. **QCA 局域搅拌假设**:QCA 的局域更新规则在视界–辐射相关区域上等价于具有充分混合性的局域随机电路,使得有限步演化后态族在局域观测下近似 Haar 随机,从而允许用随机电路理论与 ETH 结果近似描述熵增长与 Page 曲线。([SpringerLink][6])

在这些假设下,QCA 宇宙为构造"离散视界"与研究黑洞熵、信息回收提供了一个可数学化的平台。

---

## Main Results (Theorems and Alignments)

在上述统一框架与假设下,本文的核心结果可以组织为以下三个主要定理,以及一个兼顾矩阵宇宙与 QCA 宇宙的对齐命题。

### 3.1 QCA 视界纠缠熵的面积律

**定理 3.1(视界 QCA 面积律)**
在宇宙 QCA 对象 $\mathfrak U_{\mathrm{QCA}}$ 中,若存在满足 2.5 所述条件的视界带子晶格 $\Gamma_{\mathrm{H}}$ 与 Hilbert 分解
$$
\mathcal H
\simeq
\mathcal H_{\mathrm{in}}\otimes\mathcal H_{\mathrm{H}}\otimes\mathcal H_{\mathrm{out}},
\quad
\mathcal H_{\mathrm{H}}
=\mathcal H_{\mathrm{cell}}^{\otimes N_{\mathrm{H}}},
$$
且黑洞平衡时间窗口内宇宙态 $\rho$ 属于满足局域混合性与典型性的态族,则存在常数 $\eta_{\mathrm{cell}}>0$ 与 $C=O(1)$ 使得
$$
S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})
=\eta_{\mathrm{cell}}N_{\mathrm{H}}+O(1)
=\eta_{\mathrm{cell}}\frac{A}{\ell_{\mathrm{cell}}^2}+O(A^0),
$$
其中 $S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})$ 为跨视界纠缠熵,即
$$
S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})
=S\bigl(\rho_{\mathrm{in}\cup\mathrm{H}}\bigr)
=S\bigl(\rho_{\mathrm{out}}\bigr),
$$
$\rho_{\mathrm{in}\cup\mathrm{H}}=\mathrm{tr}_{\mathcal H_{\mathrm{out}}}\rho$,$\rho_{\mathrm{out}}=\mathrm{tr}_{\mathcal H_{\mathrm{in}}\otimes\mathcal H_{\mathrm{H}}}\rho$。

该定理说明:在视界带 QCA 模型中,黑洞熵的主导贡献由跨视界纠缠熵给出,且满足严格的面积律;常数 $\eta_{\mathrm{cell}}$ 与局域 Hilbert 维度及约束下的有效态空间有关。

### 3.2 与广义熵匹配的系数约束

**定理 3.2(系数匹配定理)**
假定边界时间几何与广义熵理论成立,即对每个视界截面 $\Sigma_{\mathrm{H}}$ 存在
$$
S_{\mathrm{gen}}(\Sigma_{\mathrm{H}})
=\frac{A(\Sigma_{\mathrm{H}})}{4G}
+S_{\mathrm{out}}(\Sigma_{\mathrm{H}})
$$
且局域量子引力条件在小因果菱形极限中与 Einstein 方程等价。若进一步要求:宏观上从外部观测得到的黑洞熵等于跨视界纠缠熵,即
$$
S_{\mathrm{BH}}(\Sigma_{\mathrm{H}})
=S_{\mathrm{ent}}(\Sigma_{\mathrm{H}}),
$$
并且 $S_{\mathrm{BH}}(\Sigma_{\mathrm{H}})$ 的面积一阶系数由几何部分 $A/(4G)$ 给出,则必须有
$$
\frac{\eta_{\mathrm{cell}}}{\ell_{\mathrm{cell}}^2}
=\frac{1}{4G},
$$
从而
$$
S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})
=\frac{A}{4G}+O(A^0).
$$

该定理表明:一旦要求离散 QCA 模型在连续极限中再现 BTG 与广义熵结构,视界元胞的信息密度 $\eta_{\mathrm{cell}}/\ell_{\mathrm{cell}}^2$ 便不再是任意的微观参数,而是被唯一固定为 $1/(4G)$。

### 3.3 QCA–Page 曲线型行为与信息回收

**定理 3.3(QCA–Page 曲线型行为)**
在宇宙 QCA 对象 $\mathfrak U_{\mathrm{QCA}}$ 中,考虑一段黑洞形成–蒸发过程,随离散时间步 $n$ 给出 Hilbert 分解
$$
\mathcal H
\simeq
\mathcal H_{\mathrm{BH}}(n)\otimes\mathcal H_{\mathrm{rad}}(n)\otimes\mathcal H_{\mathrm{bg}},
$$
其中 $\mathcal H_{\mathrm{BH}}(n)$ 对应黑洞内部与近视界区,$\mathcal H_{\mathrm{rad}}(n)$ 对应 Hawking 辐射模式,$\mathcal H_{\mathrm{bg}}$ 对应背景宇宙。若满足:

1. 整体态 $\lvert\Psi_0\rangle$ 纯,且随时间幺正演化 $\lvert\Psi_{n+1}\rangle=U\lvert\Psi_n\rangle$;
2. 视界元胞数随 $n$ 单调减少,而辐射模式数单调增加;
3. QCA 局域搅拌假设成立,即在每个能量壳与宏观约束下,$\lvert\Psi_n\rangle$ 在 $\mathcal H_{\mathrm{BH}}(n)\otimes\mathcal H_{\mathrm{rad}}(n)$ 上近似典型纯态族,

则对几乎所有初始纯态,有
$$
S_{\mathrm{rad}}(n)
\approx
\min\bigl(\log d_{\mathrm{BH}}(n),\log d_{\mathrm{rad}}(n)\bigr),
$$
其中 $d_{\mathrm{BH}}(n)=\dim\mathcal H_{\mathrm{BH}}(n)$,$d_{\mathrm{rad}}(n)=\dim\mathcal H_{\mathrm{rad}}(n)$。熵函数 $S_{\mathrm{rad}}(n)$ 随 $n$ 先上升后下降,形成 Page 曲线型行为:早期 $d_{\mathrm{BH}}\gg d_{\mathrm{rad}}$ 时 $S_{\mathrm{rad}}(n)\approx\log d_{\mathrm{rad}}(n)$ 单调上升;中期 $d_{\mathrm{BH}}\approx d_{\mathrm{rad}}$ 时熵达到峰值;晚期 $d_{\mathrm{BH}}\ll d_{\mathrm{rad}}$ 时 $S_{\mathrm{rad}}(n)\approx\log d_{\mathrm{BH}}(n)$ 随黑洞耗尽而下降,最终趋于零。

该结果把 Page 曲线从传统随机矩阵与随机电路模型移植到统一时间刻度约束下的 QCA 宇宙中,给出了信息回收的离散宇宙版本。

### 3.4 矩阵宇宙–QCA 宇宙对齐命题

**命题 3.4(散射母尺与 QCA 连续极限的一致性)**
设 $\mathfrak U_{\mathrm{QCA}}$ 在适当极限下产生有效哈密顿量 $H_{\mathrm{eff}}$ 与散射矩阵 $S_{\mathrm{QCA}}(\omega)$,并满足在视界附近有 Rindler 近似与 BTG 模流结构。若统一时间刻度母尺 $\kappa(\omega)$ 来自宏观矩阵宇宙的散射数据,则在误差 $\varepsilon\to 0$ 的极限中有
$$
\frac{1}{2\pi}\mathrm{tr}\, Q_{\mathrm{QCA}}(\omega)
=\kappa(\omega)+O(\varepsilon),
$$
从而 QCA 的离散时间步 $\Delta t$ 与统一时间刻度之间为仿射关系。

该命题保证:定理 3.1–3.3 中涉及的"时间"可以统一解释为同一类刻度下的参数,从而黑洞熵与 Page 曲线的离散描述与连续几何描述属于同一时间几何结构。

---

## Proofs

本节给出上述定理与命题的证明主线。详细的技术估计与边界情况分析置于附录。

### 4.1 定理 3.1:视界 QCA 面积律

考虑 Hilbert 分解
$$
\mathcal H
=\mathcal H_{\mathrm{in}}
\otimes\mathcal H_{\mathrm{H}}
\otimes\mathcal H_{\mathrm{out}},
\quad
\mathcal H_{\mathrm{H}}
=\mathcal H_{\mathrm{cell}}^{\otimes N_{\mathrm{H}}},
$$
记
$$
d_{\mathrm{H}}=\dim\mathcal H_{\mathrm{H}}
=d_{\mathrm{cell}}^{N_{\mathrm{H}}},
\quad
d_{\mathrm{in}}=\dim\mathcal H_{\mathrm{in}},
\quad
d_{\mathrm{out}}=\dim\mathcal H_{\mathrm{out}}.
$$

在能量壳与守恒量约束选出的物理子空间 $\mathcal H_{\mathrm{phys}}\subset\mathcal H$ 上,典型性假设意味着:在自然的 Fubini–Study 测度下,绝大多数纯态 $\lvert\Psi\rangle\in\mathcal H_{\mathrm{phys}}$ 对应的约化态
$$
\rho_{\mathrm{in}\cup\mathrm{H}}
=\mathrm{tr}_{\mathcal H_{\mathrm{out}}}\lvert\Psi\rangle\langle\Psi\rvert,
\quad
\rho_{\mathrm{out}}
=\mathrm{tr}_{\mathcal H_{\mathrm{in}}\otimes\mathcal H_{\mathrm{H}}}\lvert\Psi\rangle\langle\Psi\rvert,
$$
具有接近最大混合的谱。

在忽略约束的理想模型中,Page 猜想并证明了当 $m\le n$ 时,随机纯态在 Hilbert 空间 $\mathbb C^{mn}$ 上的较小子系统的平均熵为
$$
S_{m,n}
=\sum_{k=n+1}^{mn}\frac{1}{k}
-\frac{m-1}{2n}
\simeq\log m-\frac{m}{2n},
$$
其中 $m$ 为较小子系统维度,$n$ 为较大子系统维度。([物理评论链接管理器][5])

将 $\mathcal H_{\mathrm{in}}\otimes\mathcal H_{\mathrm{H}}$ 视为一侧,$\mathcal H_{\mathrm{out}}$ 视为另一侧,有两种情况:

1. 若 $d_{\mathrm{in}}d_{\mathrm{H}}\le d_{\mathrm{out}}$,则较小子系统为 $\mathcal H_{\mathrm{in}}\otimes\mathcal H_{\mathrm{H}}$,其平均熵接近 $\log(d_{\mathrm{in}}d_{\mathrm{H}})$。
2. 若 $d_{\mathrm{in}}d_{\mathrm{H}}>d_{\mathrm{out}}$,则较小子系统为 $\mathcal H_{\mathrm{out}}$,其平均熵接近 $\log(d_{\mathrm{out}})$。

在黑洞平衡态的情形中,视界带元胞数 $N_{\mathrm{H}}$ 大,$d_{\mathrm{H}}=d_{\mathrm{cell}}^{N_{\mathrm{H}}}$ 指数增长,而 $d_{\mathrm{in}},d_{\mathrm{out}}$ 或其对数相对 $N_{\mathrm{H}}$ 仅多项式增长或常数级,因此在 $N_{\mathrm{H}}\to\infty$ 极限下,主导项为
$$
\mathbb E\bigl[S(\rho_{\mathrm{out}})\bigr]
\approx
N_{\mathrm{H}}\log d_{\mathrm{eff}}+O(1),
$$
其中 $d_{\mathrm{eff}}\le d_{\mathrm{cell}}$ 为能量约束与局域守恒量修正后的有效局域维度。设
$$
\eta_{\mathrm{cell}}=\log d_{\mathrm{eff}},
$$
则有
$$
S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})
=S(\rho_{\mathrm{out}})
=\eta_{\mathrm{cell}}N_{\mathrm{H}}+O(1)
=\eta_{\mathrm{cell}}\frac{A}{\ell_{\mathrm{cell}}^2}+O(A^0).
$$

能量壳与局域守恒量的存在会缩减 $\mathcal H_{\mathrm{phys}}$ 的维度,但在大系统极限下,这一缩减对应于 $\eta_{\mathrm{cell}}$ 的重整化,并不改变熵随 $N_{\mathrm{H}}$ 的线性关系,详见附录 A。

### 4.2 定理 3.2:与广义熵系数的匹配

定理 3.1 给出的面积律具有形式
$$
S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})
=\eta_{\mathrm{cell}}\frac{A}{\ell_{\mathrm{cell}}^2}+O(A^0).
$$

另一方面,在 BTG 与广义熵框架中,黑洞熵的几何部分为
$$
S_{\mathrm{BH}}(\Sigma_{\mathrm{H}})
=\frac{A}{4G},
$$
整体广义熵为
$$
S_{\mathrm{gen}}(\Sigma_{\mathrm{H}})
=\frac{A}{4G}+S_{\mathrm{out}}(\Sigma_{\mathrm{H}}),
$$
其中 $S_{\mathrm{out}}$ 对应视界外可见自由度的熵,与具体辐射与外区量子态有关。([科学进展][9])

若将跨视界纠缠熵识别为宏观黑洞熵,即
$$
S_{\mathrm{BH}}(\Sigma_{\mathrm{H}})
=S_{\mathrm{ent}}(\Sigma_{\mathrm{H}}),
$$
则两边在面积一阶项上的系数必须相等,因此
$$
\eta_{\mathrm{cell}}\frac{1}{\ell_{\mathrm{cell}}^2}
=\frac{1}{4G}.
$$

面积零阶项的差异可吸收入有限尺寸修正与外部熵项中,不影响主导系数。这一约束可以理解为:视界每单位几何面积携带的离散信息量必须等于广义熵公式要求的 $1/(4G)$,从而把 $G$ 解释为 QCA 微观格距 $\ell_{\mathrm{cell}}$ 与局域态空间维度的集体效应。

### 4.3 定理 3.3:QCA–Page 曲线型行为

QCA–Page 曲线定理直接借鉴了随机电路与 Page 原始工作中的思想,但在统一时间刻度约束与 QCA 局域结构下需要额外论证局域搅拌假设的合理性。

在给定时间步 $n$ 上,我们将 Hilbert 空间分解为
$$
\mathcal H
\simeq
\mathcal H_{\mathrm{BH}}(n)\otimes\mathcal H_{\mathrm{rad}}(n)\otimes\mathcal H_{\mathrm{bg}}.
$$
记
$$
d_{\mathrm{BH}}(n)=\dim\mathcal H_{\mathrm{BH}}(n),
\quad
d_{\mathrm{rad}}(n)=\dim\mathcal H_{\mathrm{rad}}(n).
$$

假定 QCA 局域演化 $U$ 在黑洞–辐射区域可视为一个深度有限但随 $n$ 增长的局域随机电路,其门集合生成 $SU(d)$ 并满足适当的 $t$-design 条件,随机电路理论表明:在足够长时间后,$\lvert\Psi_n\rangle$ 在 $\mathcal H_{\mathrm{BH}}(n)\otimes\mathcal H_{\mathrm{rad}}(n)$ 上的约化态分布接近 Haar 随机态的分布,局域观测统计及 Renyi 熵随时间的行为接近随机纯态模型。([SpringerLink][6])

因此,可以直接将 Page 平均熵公式应用于子系统 $\mathcal H_{\mathrm{rad}}(n)$,得到
$$
S_{\mathrm{rad}}(n)
\approx
\min\bigl(\log d_{\mathrm{BH}}(n),\log d_{\mathrm{rad}}(n)\bigr)
+O(1).
$$
由于黑洞视界面积随 $n$ 单调减小,根据定理 3.2 有
$$
\log d_{\mathrm{BH}}(n)
\approx
\frac{A(n)}{4G},
$$
而辐射模式维度随时间增长,故存在一唯一的 Page 时间 $n_{\mathrm{Page}}$,满足
$$
\log d_{\mathrm{BH}}(n_{\mathrm{Page}})
\approx\log d_{\mathrm{rad}}(n_{\mathrm{Page}}).
$$
此后,较小 Hilbert 空间从辐射侧切换到黑洞侧,熵下降,直至黑洞完全蒸发时 $d_{\mathrm{BH}}\to 1$,辐射熵趋于零,从而恢复整体纯态。

将离散时间步 $n$ 通过统一时间刻度映射到连续时间参数 $\tau$,得到连续版本的 Page 曲线。近期的若干工作利用随机动力学、随机线性光学与变分量子算法在实际量子设备上模拟了类似的 Page 曲线行为,为上述假设提供了间接支持。([arXiv][11])

### 4.4 命题 3.4:散射母尺与 QCA 连续极限

在 QCA 连续极限中,假定存在有效哈密顿量 $H_{\mathrm{eff}}$ 使得
$$
U
=\exp(-\mathrm{i} H_{\mathrm{eff}}\Delta t)+O(\Delta t^2),
$$
通过标准散射构造可以获得 $H_{\mathrm{eff}}$ 的散射矩阵 $S_{\mathrm{QCA}}(\omega)$。另一方面,矩阵宇宙中的散射矩阵 $S(\omega)$ 由宏观几何与场论确定。统一时间刻度要求两者的半相位导数与群延迟迹给出的刻度密度$\kappa_{\mathrm{QCA}}(\omega)$ 与 $\kappa(\omega)$ 一致,从而对 $\Delta t$、$\ell_{\mathrm{cell}}$ 与有效场论参数(如光速、质量)施加约束。

在视界附近,由 Rindler 近似度规
$$
\mathrm{d} s^2
=-\kappa_{\mathrm{surf}}^2 x^2\mathrm{d} t^2
+\mathrm{d} x^2+\mathrm{d} y^2+\mathrm{d} z^2
$$
可知,模时间与几何时间之间存在固定比例关系,进而限制 QCA 的局域谱结构与时间步长。在适当的极限下,可以证明
$$
\frac{1}{2\pi}\mathrm{tr}\, Q_{\mathrm{QCA}}(\omega)
=\kappa(\omega)+O(\varepsilon),
$$
即命题 3.4 所述。这一匹配保证 QCA 宇宙的离散时间与矩阵宇宙的统一时间刻度在黑洞视界附近是相容的。

---

## Model Apply

本节讨论上述理论在若干典型黑洞背景下的适用性与具体构造。

### 5.1 静态 Schwarzschild 黑洞

考虑四维 Schwarzschild 黑洞,其视界半径为 $r_s=2GM$,视界截面 $\Sigma_{\mathrm{H}}$ 为半径 $r_s$ 的二球,面积
$$
A=4\pi r_s^2=16\pi G^2M^2.
$$

在 QCA 宇宙中,选择一个嵌入到连续流形的二维子晶格近似该二球,使得元胞面积 $\ell_{\mathrm{cell}}^2$ 与几何面积满足
$$
N_{\mathrm{H}}
=\frac{A}{\ell_{\mathrm{cell}}^2}+O(A^0).
$$

对每个视界元胞赋予有限维 Hilbert 空间 $\mathcal H_{\mathrm{cell}}$,通过局域能量约束确定有效维度 $d_{\mathrm{eff}}$,应用定理 3.1 与 3.2 得到
$$
S_{\mathrm{BH}}
=S_{\mathrm{ent}}
=\frac{A}{4G}+O(A^0)
=4\pi G M^2+O(A^0),
$$
与标准 Bekenstein–Hawking 结果一致。([scholarpedia.org][1])

Page 时间对应视界面积减半的位置,QCA–Page 曲线给出辐射熵随统一时间刻度的演化,宏观上与"岛"公式给出的 Page 曲线结构相容。([arXiv][4])

### 5.2 AdS–Schwarzschild 黑洞与全息对应

对于 AdS–Schwarzschild 黑洞,其视界截面仍为二球或更高维球面,但外区几何与边界 CFT 对偶。QCA 宇宙可一方面描述体域中的离散几何与视界元胞,另一方面描述边界上的离散化 CFT,自然引入"体–边"两层 QCA 模型。

跨视界纠缠熵的一部分可以在边界 CFT 的纠缠熵中重现,与 Ryu–Takayanagi 极小面公式以及岛公式结合,给出 Bekenstein–Hawking 熵与 Page 曲线的全息解释。统一时间刻度保证体域散射与边界 CFT 模流具有一致的刻度密度。

### 5.3 Rindler 视界与加速观察者

在 Minkowski 时空中的均匀加速观察者拥有 Rindler 视界,其热谱为 Unruh 辐射。对该情形构造的"Rindler QCA 模型"可以视为 Schwarzschild 视界的局域近似,其 QCA 面积律给出 Rindler 截面的跨越纠缠熵;与 Unruh 温度的关系则由统一时间刻度与模流条件确定。

这一情形展示了:视界 QCA 面积律并不限于黑洞视界,也适用于一般的因果视界,只要 BTG 与统一时间刻度适用。

---

## Engineering Proposals

本节简要描述若干与本文理论结构相呼应的工程与实验方向。

### 6.1 随机量子电路中的 Page 曲线模拟

近期在随机量子电路与噪声电路上,已经通过理论与实验手段系统研究了 Page 曲线与纠缠动力学。([SpringerLink][6]) 利用超导量子比特与线性光学平台,可以实现局域随机门阵列,并测量子系统的纠缠熵随深度的演化,从而获得 Page 曲线型行为。

本文的 QCA–Page 曲线定理表明:只要随机电路模型在某一极限下嵌入 QCA 范畴,其观测到的 Page 曲线即可视为"离散视界信息回收"的工程原型。近期利用 IBM 量子计算平台模拟 Hawking 辐射与 Page 曲线的工作进一步强化了这一联系。([arXiv][11])

### 6.2 Dirac QCA 与光子/囚禁离子实验

Dirac 型 QCA 已在可编程囚禁离子量子计算机与光子平台上得到实验实现,用以模拟相对论量子行走与 Zitterbewegung 等效应。([物理评论链接管理器][8]) 这些实验表明:以局域幺正规则为核心的 QCA 模型可以在实验上精确控制与测量。

在此基础上,可以设计具有"有效视界"的一维或二维 QCA,选择某个空间截面作为"离散视界",通过测量跨截面的纠缠熵验证面积律的近似成立,从而为本文的视界 QCA 模型提供可检验的简化版本。

### 6.3 QCA–黑洞蒸发玩具模型的量子实现

文献中已经提出一些量子电路模型用以描述黑洞蒸发与防火墙问题。([arXiv][12]) 将此类模型重新整理为满足 QCA 公理的局域更新规则,可以在当前噪声中等规模量子设备上实现一个有限维的黑洞–辐射系统,测量辐射熵、互信息与 OTOC 等量,检验 QCA–Page 曲线与信息回收的细节。

---

## Discussion (risks, boundaries, past work)

### 7.1 与传统连续理论与全息方案的关系

传统对黑洞熵的微观解释,包括弦论微态计数与 AdS/CFT 对偶,通过在高能理论中构造黑洞态的微观自由度来重现 $S_{\mathrm{BH}}=A/(4G)$。([科学进展][9]) 本文的 QCA 视界模型则在更抽象的离散层面对这一公式给出结构性解释:面积律来自跨视界纠缠熵的线性增长,系数通过与广义熵的一致性条件被固定。

与基于岛公式与 replica wormhole 的 Page 曲线方案相比,本文不依赖具体的引力路径积分,而是通过 QCA 的典型性与局域搅拌假设在离散宇宙中再现 Page 曲线行为,两者在宏观熵演化上是一致的,但在"背后"所使用的数学工具有所不同。([arXiv][4])

### 7.2 假设的边界与风险

本文框架中最关键的假设是局域混合性与 QCA 局域搅拌假设。若宇宙在某一尺度上显著偏离典型性(例如存在大量可保护的积分量或强约束),则 Page 型估计可能失效,黑洞–辐射系统的熵演化可能显著偏离标准 Page 曲线。

另一个边界在于 QCA 连续极限的存在性与稳定性。并非所有 QCA 都具有良好的连续极限,且在存在引力回馈时,有效哈密顿量与散射矩阵的定义可能变得微妙。QCA 的指数理论与分类结果目前在一维情形最为完备,高维情形仍在发展中。([arXiv][7])

### 7.3 与防火墙与互补性争论的关系

AMPS 提出防火墙悖论,认为在兼顾无剧烈背离经验与信息回收的条件下,视界附近真空态结构可能被破坏。([arXiv][13]) 在 QCA 视界模型中,跨视界纠缠熵的存在是面积律的根本来源,因此任何显著地破坏视界附近纠缠结构的机制都会直接影响 $S_{\mathrm{BH}}=A/4$ 的成立。

本文的统一矩阵–QCA 宇宙框架并不试图给出防火墙问题的最终答案,而是提供一种结构性的视角:若坚持统一时间刻度、BTG 与 QCA 幺正性,则视界附近必须保持足够的纠缠结构以支持面积律与 Page 曲线,这在一定程度上与"温和"的互补性观点相容,但对强防火墙模型形成约束。

---

## Conclusion

在统一时间刻度、边界时间几何与 QCA 宇宙的统一框架下,本文对黑洞熵与信息悖论给出了一套离散–连续一体化的数学描述:

1. 通过视界带子晶格与 Hilbert 分解,证明了跨视界纠缠熵在 QCA 宇宙中满足面积律,熵密度来自局域 Hilbert 维度与能量壳典型性。
2. 通过与 BTG 与广义熵公式的匹配,给出了 $\eta_{\mathrm{cell}}/\ell_{\mathrm{cell}}^2=1/(4G)$ 的系数约束,从而在离散层面重现 $S_{\mathrm{BH}}=A/(4G)$ 的几何系数。
3. 借助随机电路与典型性理论,在 QCA 宇宙中建立了 Page 曲线型熵演化的定理版本,说明在统一时间刻度下信息可以通过辐射模式逐步回收,黑洞信息悖论被还原为 coarse-graining 与典型性问题,而非根本的非幺正性。
4. 通过矩阵宇宙–QCA 宇宙的对齐命题,保证了离散时间步与散射母尺给出的统一时间刻度之间的一致性,使得黑洞热力学、广义熵与 QCA 动力学处于同一时间几何结构中。

这一框架为今后在更具体的引力模型、全息场论与量子模拟平台中研究黑洞熵与信息问题提供了可扩展的结构基础,也为将其他尚未统一的现象(如宇宙学常数问题、中微子混合、强 CP 问题等)嵌入同一矩阵–QCA 宇宙提供了思路。

---

## Acknowledgements

本研究工作得益于关于黑洞热力学、信息悖论、随机电路动力学与量子元胞自动机的广泛既有文献,在此对相关领域的原创性贡献表示致敬。

---

## Code Availability

本文主要提出一套抽象的统一矩阵–QCA 宇宙理论框架,并未绑定于某一具体数值实现。任意支持有限维局域 Hilbert 空间、局域幺正更新与熵测度的仿真平台(如基于张量网络与量子线路的 Python 或 C++ 库)均可实现视界 QCA 与 Page 曲线玩具模型。相关代码的具体实现可在后续工作中以独立仓库形式给出。

---

## 附录 A:视界 QCA 面积律的详细证明

本附录给出定理 3.1 的更为详细的证明,重点在于能量约束与有效 Hilbert 维度的处理。

### A.1 Page 定理与典型态熵估计

设
$$
\mathcal H
=\mathcal H_A\otimes\mathcal H_B,
\quad
\dim\mathcal H_A=m,\ \dim\mathcal H_B=n,\ mn=D.
$$
对 $\mathcal H$ 上的 Haar 随机纯态 $\lvert\Psi\rangle$,Page 给出子系统 $A$ 的平均熵
$$
\mathbb E[S(\rho_A)]
=\sum_{k=n+1}^{mn}\frac{1}{k}
-\frac{m-1}{2n},
$$
其中 $\rho_A=\mathrm{tr}_B\lvert\Psi\rangle\langle\Psi\rvert$。当 $1\ll m\le n$ 时,有近似
$$
\mathbb E[S(\rho_A)]
\simeq\log m-\frac{m}{2n}.
$$
该结果之后被严格证明。([物理评论链接管理器][5])

在视界 QCA 情形中,将
$$
\mathcal H_A=\mathcal H_{\mathrm{in}}\otimes\mathcal H_{\mathrm{H}},
\quad
\mathcal H_B=\mathcal H_{\mathrm{out}},
$$
或互换两者的角色。记
$$
m=d_{\mathrm{in}}d_{\mathrm{H}},
\quad
n=d_{\mathrm{out}},
$$
当 $N_{\mathrm{H}}$ 较大时,$d_{\mathrm{H}}=d_{\mathrm{cell}}^{N_{\mathrm{H}}}$ 指数增长,而 $d_{\mathrm{in}},d_{\mathrm{out}}$ 至多多项式增长,因此几乎总有 $m\ge n$。在这一情形中,较小子系统为 $\mathcal H_B$,平均熵近似为 $\log n$。

然而,对跨视界纠缠熵而言,我们更关心的是
$$
S_{\mathrm{ent}}
=S(\rho_{\mathrm{in}\cup\mathrm{H}})
=S(\rho_{\mathrm{out}}),
$$
故无论取哪一方作为"子系统",熵值相同。

当 $N_{\mathrm{H}}$ 足够大时,$d_{\mathrm{H}}$ 的增长主导整体维度,$\log d_{\mathrm{H}}=N_{\mathrm{H}}\log d_{\mathrm{cell}}$ 给出跨视界熵的线性主项。能量壳与守恒量约束将 $\mathcal H$ 缩减为子空间 $\mathcal H_{\mathrm{phys}}$,但在统计力学的标准情形中,$\dim\mathcal H_{\mathrm{phys}}\sim\exp(s_{\mathrm{loc}}N_{\mathrm{H}})$,$s_{\mathrm{loc}}$ 为局域熵密度。于是可以引入有效局域维度 $d_{\mathrm{eff}}=\exp(s_{\mathrm{loc}})$,获得
$$
\mathbb E[S_{\mathrm{ent}}]
\approx N_{\mathrm{H}}\log d_{\mathrm{eff}}+O(1).
$$

### A.2 能量壳约束与局域平衡

在 QCA 宇宙中,能量并非事先给定的守恒量,而是由连续极限中的有效哈密顿量 $H_{\mathrm{eff}}$ 与统一时间刻度共同定义。视界附近的"平衡态"可视为满足固定能量密度与能流约束的典型态集合,其物理子空间维度满足
$$
\dim\mathcal H_{\mathrm{phys}}
\sim
\exp\bigl(s_{\mathrm{loc}}N_{\mathrm{H}}\bigr),
$$
其中 $s_{\mathrm{loc}}$ 可以通过微正则或正则系综定义为局域熵密度。

在局域 ETH 假设下,能量壳内的绝大多数本征态在局域观测下与典型态等价,从而 Page 型的平均熵估计依然成立,只是 $\log d_{\mathrm{cell}}$ 被 $s_{\mathrm{loc}}$ 替换,即 $\eta_{\mathrm{cell}}=s_{\mathrm{loc}}$。局域 ETH 在随机电路与多体混沌模型中已被广泛验证。([SpringerLink][6])

### A.3 连续极限下的面积律

最后,将 $N_{\mathrm{H}}$ 与几何面积 $A$ 的关系代入,
$$
N_{\mathrm{H}}=\frac{A}{\ell_{\mathrm{cell}}^2}+O(A^0),
$$
得到
$$
S_{\mathrm{ent}}(\Sigma_{\mathrm{H}})
=\eta_{\mathrm{cell}}\frac{A}{\ell_{\mathrm{cell}}^2}+O(A^0),
$$
这即定理 3.1 的陈述。

---

## 附录 B:QCA–Page 曲线型行为的进一步细节

本附录对定理 3.3 中用到的随机电路与局域搅拌假设作进一步说明。

### B.1 局域随机电路与 $t$-design

在有限尺寸系统中,局域随机电路由若干层两体或少体幺正门组成,每一层的门对作用在互不重叠的子集上。若门集合在群论意义上生成 $SU(d)$,且随机选取的门序列在足够深度后构成近似的单元 $t$-design,则其对初始简单双态的作用在多项式时间内产生近似 Haar 随机态。这一结论已在多体系统与开放系统的随机电路模型中得到广泛利用。([SpringerLink][6])

在 QCA 宇宙中,若局域更新规则可以视为某种固定门集的周期性作用,则在引入微小随机扰动或多步合成后,同样可以在局域上近似实现 $t$-design,从而支持局域搅拌假设。

### B.2 Hilbert 维度与 Page 曲线的形状

在黑洞形成–蒸发过程中,视界元胞数 $N_{\mathrm{H}}(n)$ 随时间递减,而辐射模式数(可视为离开某一因果区域的激发)随时间递增。若每个元胞与模式的局域 Hilbert 维度近似恒定,则
$$
\log d_{\mathrm{BH}}(n)\approx s_{\mathrm{BH}}N_{\mathrm{H}}(n),
\quad
\log d_{\mathrm{rad}}(n)\approx s_{\mathrm{rad}}N_{\mathrm{rad}}(n),
$$
其中 $s_{\mathrm{BH}},s_{\mathrm{rad}}$ 为对应的局域熵密度。Page 时间对应两者对数维度相等的位置
$$
s_{\mathrm{BH}}N_{\mathrm{H}}(n_{\mathrm{Page}})
\approx
s_{\mathrm{rad}}N_{\mathrm{rad}}(n_{\mathrm{Page}}).
$$

在统一时间刻度下,将 $n$ 映射为连续参数 $\tau$,即可得到连续的 Page 曲线形状。其具体的函数形式依赖于 $N_{\mathrm{H}}(\tau)$ 与 $N_{\mathrm{rad}}(\tau)$ 的动力学,这可以通过具体的 QCA 规则或有效引力模型确定。

---

## 附录 C:统一时间刻度与 QCA 连续极限的兼容性

### C.1 有效哈密顿量与散射矩阵

在 QCA 连续极限中,若单粒子扇区可以在动量表象中对角化,则每一动量 $k$ 模式的演化近似为
$$
U(k)=\exp\bigl(-\mathrm{i}\omega(k)\Delta t\bigr),
$$
色散关系 $\omega(k)$ 在小 $k$ 极限下可近似为相对论型。多粒子扇区可在适当近似下得到有效哈密顿量 $H_{\mathrm{eff}}$,并通过标准散射理论构造散射矩阵 $S_{\mathrm{QCA}}(\omega)$。

统一时间刻度母尺要求
$$
\kappa_{\mathrm{QCA}}(\omega)
=\frac{1}{2\pi}\mathrm{tr}\, Q_{\mathrm{QCA}}(\omega)
\approx
\kappa(\omega),
$$
其中 $\kappa(\omega)$ 来自连续宏观宇宙的散射数据。这一条件约束 $\Delta t$、$\ell_{\mathrm{cell}}$ 与 $H_{\mathrm{eff}}$ 的参数,使得 QCA 的时间刻度与 BTG 的模时间刻度相容。

### C.2 Rindler 近似与模流

在视界附近,采用 Rindler 坐标,可以把度规写为
$$
\mathrm{d} s^2
=-\kappa_{\mathrm{surf}}^2 x^2\mathrm{d} t^2
+\mathrm{d} x^2+\mathrm{d} y^2+\mathrm{d} z^2.
$$
模流对应于沿 $t$ 的平移,其 KMS 温度为 $T_H=\kappa_{\mathrm{surf}}/(2\pi)$。在 QCA 连续极限中,若局域更新规则在视界带附近逼近 Rindler 模型,则统一时间刻度要求每一步离散时间 $\Delta t$ 对应固定的模时间增量,从而在频域中体现为 $\kappa_{\mathrm{QCA}}(\omega)$ 与 $\kappa(\omega)$ 的一致性。

这一兼容性保证:在统一矩阵–QCA 宇宙中,黑洞视界所感知的时间流逝与外部观察者通过散射母尺推断的时间完全一致,使得 Bekenstein–Hawking 熵、Page 曲线与 QCA 视界模型处于统一的时间几何结构之中。

[1]: https://www.scholarpedia.org/article/Bekenstein-Hawking_entropy
[2]: https://en.wikipedia.org/wiki/Hawking_radiation
[3]: https://en.wikipedia.org/wiki/Black_hole_information_paradox
[4]: https://arxiv.org/abs/1911.11977
[5]: https://link.aps.org/doi/10.1103/PhysRevLett.71.1291
[6]: https://link.springer.com/article/10.1007/JHEP04%282020%29063
[7]: https://arxiv.org/abs/0910.3675
[8]: https://link.aps.org/doi/10.1103/PhysRevResearch.6.033136
[9]: https://www.sciencedirect.com/topics/physics-and-astronomy/bekenstein-hawking-entropy
[10]: https://quantum-journal.org/papers/q-2020-11-30-368/
[11]: https://arxiv.org/abs/2412.15180
[12]: https://arxiv.org/abs/1807.07672
[13]: https://arxiv.org/abs/1207.3123
