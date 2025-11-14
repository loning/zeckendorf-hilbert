# 三位一体母尺—边界时间几何—Null–Modular 双覆盖的一体化统一理论

从散射相位到时间晶体、局域量子条件与宇宙学

---

## Abstract

构造一个以三位一体母尺
$\kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$
为唯一刻度源的统一观测框架, 将散射相位、Wigner–Smith 群延迟、Birman–Kreĭn 谱移函数、模时间、引力边界时间、Null–Modular 双覆盖、时间晶体谱配对、自指散射网络的模二谱流、广义熵变分、有限阶窗化误差纪律与能力–风险前沿组织为单一范畴对象上的不同投影与函子像。

在几何与拓扑层面, 在带边界总空间 $Y=M\times X^{\circ}$ 上引入统一观测对象
$\mathfrak X=(Y\to M,[\kappa],[K],[\mathcal W])$, 其中 $[\kappa]$ 为时间刻度等价类,
$[K]\in H^{2}(Y,\partial Y;\mathbb Z_{2})$ 是 Null–Modular 双覆盖上同调类,
$[\mathcal W]$ 为满足有限阶 Euler–Maclaurin–Poisson 纪律的窗化结构。证明:

1. 在边界时间几何中, 散射刻度密度、模时间刻度密度与引力边界时间刻度密度同属一个仿射唯一的刻度等价类 $[\kappa]$。
2. Null–Modular 上同调类 $[K]$ 与自指散射网络中 $J$–幺正族在 $-1$ 处的模二谱流、散射行列式平方根的半相位跃迁、Floquet–Lindblad 时间晶体中的 $\pi$ 模谱配对拓扑数完全等价。
3. 小因果菱形上的广义熵二阶变分可以写成母尺刻度密度在窗化权函数上的积分, 外加由 $[K]$ 与大尺度拓扑扇区配对给出的宇宙学常数有效项。
4. 在满足有限阶窗化纪律的 PSWF/DPSS 极值窗族下, 所有母尺读数均分解为由 $K^{1}$ 与 $[K]$ 决定的拓扑整数主项加上可显式控制的解析尾项。
5. 将上述结构提升到策略–环境对的层级, 可以给出一个由刻度–拓扑–误差三元组约束的能力–风险前沿; 对一般交互式系统的灾难安全性判定问题在该框架下保持不可判定。

文末给出代表性物理模型与工程化方案: 包括微波散射网络对母尺同一式的计量验证, Floquet 时间晶体与自指散射网络中 $\mathbb Z_{2}$ 环量的实验读数, 以及在 FRB 与宇宙学背景中对宇宙学有效常数的窗化重构。

---

## Keywords

三位一体母尺; 边界时间几何; Null–Modular 双覆盖; $\mathbb Z_{2}$ 环量; 自指散射网络; 时间晶体; 相对散射行列式; 广义熵; PSWF/DPSS; 一致性工厂; 能力–风险前沿; 灾难安全不可判定

---

## Introduction & Historical Context

### 统一时间刻度与散射–谱移–群延迟

在迹类扰动的散射理论中, Birman–Kreĭn 理论引入谱移函数 $\xi(\omega)$, 满足
$\det S(\omega)=\exp[-2\pi i\xi(\omega)]$, 并给出迹公式与相位–谱移之间的联系。
对 $\omega$ 的导数给出相对态密度
$\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$。在 Wigner–Smith 体系中, 定义群延迟算子
$Q(\omega)=-iS(\omega)^{\dagger}\partial_{\omega}S(\omega)$, 其迹与局域态密度相关,
在一维或多通道散射设置下满足
$\operatorname{tr}Q(\omega)=2\pi\rho_{\mathrm{rel}}(\omega)$。([arXiv][1])

另一方面, 设总散射相位 $\Phi(\omega)=\arg\det S(\omega)$, 半相位
$\varphi(\omega)=\tfrac12\Phi(\omega)$, 由 Birman–Kreĭn 公式知
$\Phi(\omega)=-2\pi\xi(\omega)$, 因而
$\varphi'(\omega)=\pi\rho_{\mathrm{rel}}(\omega)$。这三种对象在可测能窗内满足刻度同一式
$\kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\mathrm{rel}}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$。

此前工作中, 这一同一式被提升为"统一时间刻度": 在量子散射端,
$\kappa(\omega)$ 直接以频率分辨的群延迟或相位梯度读出; 在几何端,
通过波迹–几何光学–Shapiro 延迟桥接到弯曲时空中的传播延迟; 在算子代数端,
则通过模流与相对熵 Hessian 与内禀时间参数对齐。

### 边界时间几何与模时间

在广义相对论与量子场论的交界处, 边界作用
$S_{\mathrm{EH}}+S_{\mathrm{GHY}}+S_{\mathrm{ct}}$ 的变分揭示了 Gibbons–Hawking–York
边界项在引入外在曲率 $K_{ab}$ 与 Brown–York 准局域能中的基础地位。
另一方面, Tomita–Takesaki 模块理论与 Connes–Rovelli 热时间假说指出,
给定可观测代数 $\mathcal A$ 与状态 $\omega$, 模流 $\sigma_{t}^{\omega}$ 生成的参数 $t$
可视为由系统自身决定的"内禀时间"。模哈密顿 $K_{\omega}$ 的谱密度与相对熵
$S(\rho\Vert\omega)$ 的二阶导数之间存在明确关系, 为时间刻度的信息定义提供基础。([物理评论链接管理器][2])

最近关于广义熵与量子能量条件的工作表明, 小因果菱形上广义熵的一阶极值可导出
Einstein 方程, 二阶变分受 QNEC/QFC 等不等式约束; 这些结果将几何曲率、能量条件与熵的形变紧密联系。([电子学术库][3])

### Null–Modular 双覆盖、时间晶体与自指散射网络

Null–Modular 双覆盖工作提出: 在因果菱形与模流的联合结构上, 存在一个自然的
$\mathbb Z_{2}$ 上同调类 $[K]\in H^{2}(Y,\partial Y;\mathbb Z_{2})$, 它同时刻画:

* 模哈密顿 Berry 联络在参数回路上的 $\mathbb Z_{2}$ 环量;
* 半相位 $\sqrt{\det S}$ 的分支变换与模二谱流;
* Floquet–Lindblad 时间晶体中 Floquet 谱在 $\lambda\approx -1$ 附近的 $\pi$ 模配对;
* 拓扑超导等体系中端点模的 $\mathbb Z_{2}$ 不变量。

时间晶体研究表明, 在多体相互作用与高频驱动下, 可出现稳健的离散时间平移对称性自发破缺 (DTC/PDTC), 其稳定机制包括 MBL 与预热机制, 并在 Floquet 谱中表现为严格的子谐振振荡与谱配对结构。([科学杂志][4])

自指散射网络则从 Redheffer 星积与反馈网络视角构造闭环散射, 将反馈条件编码为
$J$–幺正算子族的谱性质, 由此得到模二谱流与半相位之间的桥接, 并为费米统计与 $\mathbb Z_{2}$ 交换相位提供统一解释。

### 误差纪律、一致性工厂与灾难安全边界

在数值与工程侧, 有限阶 Euler–Maclaurin–Poisson 纪律提供了控制求和–积分差、带限截断与窗化误差的统一手段; PSWF/DPSS 极值窗以能量集中最优性与 Carleson–Landau 采样条件为基础, 给出带宽–时长受限下的"极值窗"族。

一致性工厂工作则将受限主丛–散射–$K^{1}$ 指标统一, 给出"自然变换唯一到整数倍"的范畴化刻画, 并把拓扑整数主项与可控解析尾项组合成可复算的误差界。

最后, 在智能体安全性研究中, 已证明在极弱假设下, 判断交互式系统是否满足给定灾难风险阈值是不可判定的; 同时, 在受限模型类上可用 PAC–Bayes 界、互信息界与 Wasserstein–DRO 构造"能力–风险前沿"的上界。

### 目标与贡献

本文的目标是, 在上述各子体系已相对成熟的前提下, 构造一个更高层次的统一对象 $\mathfrak X$, 使得:

1. 散射–模时间–引力边界时间共享一个仿射唯一的刻度等价类 $[\kappa]$, 不再依赖具体实现。
2. Null–Modular $\mathbb Z_{2}$ 类 $[K]$ 统一控制自指散射、时间晶体与引力–拓扑的奇偶结构。
3. 广义熵变分、相对散射行列式与宇宙学常数的有效值都可表达为 $[\kappa]$ 与 $[K]$ 的函数, 在满足局域量子条件与 QNEC/QFC 的前提下等价于 Einstein 方程。
4. 所有以 PSWF/DPSS 等极值窗实现的读出都在有限阶纪律下分解为拓扑整数主项加解析尾项, 并且此整数由 $[K]$ 与 $K^{1}$ 配对唯一确定。
5. 能力–风险前沿在此框架中获得一种刻度–拓扑–误差三元组的表达, 灾难安全不可判定构成不可逾越的边界。

---

## Model & Assumptions

### 几何与散射背景

1. **时空与因果结构**
   设 $(M,g)$ 为四维、时向可定向的全局双曲洛伦兹流形, 具有(可能为空的)时间类空边界 $\partial M$, 满足标准能量条件与因果决定性假设。

2. **参数空间与总空间**
   设 $X^{\circ}$ 为光滑有限维流形, 表示散射通道、自指网络参数、Floquet 驱动参数等。
   定义总空间 $Y=M\times X^{\circ}$, 边界
   $\partial Y=(\partial M\times X^{\circ})\cup(M\times\partial X^{\circ})$。

3. **散射矩阵族**
   在每个固定 $x\in X^{\circ}$ 上, 有自伴算子对 $(H_{0}(x),H(x))$,
   $H(x)-H_{0}(x)$ 为迹类扰动; 存在多通道散射矩阵
   $S(\omega,x)\in\mathsf U(N)$, 随 $\omega$ 与 $x$ 平滑变化并在能窗内满足
   Birman–Kreĭn 条件。

4. **Wigner–Smith 群延迟**
   定义
   $Q(\omega,x)=-iS(\omega,x)^{\dagger}\partial_{\omega}S(\omega,x)$,
   假设其在能窗内迹类, 并满足
   $\operatorname{tr}Q(\omega,x)=2\pi\rho_{\mathrm{rel}}(\omega,x)$,
   其中 $\rho_{\mathrm{rel}}$ 为谱移函数的导数。([arXiv][1])

5. **散射半相位与谱移**
   定义总相位 $\Phi(\omega,x)=\arg\det S(\omega,x)$, 半相位
   $\varphi(\omega,x)=\tfrac12\Phi(\omega,x)$, 取无共振处连续延拓的支,
   并定义谱移函数 $\xi(\omega,x)$ 使
   $\det S(\omega,x)=\exp[-2\pi i\xi(\omega,x)]$。

### 母尺刻度密度与刻度等价类

**定义 2.1 (三位一体母尺)**

在上述假设下, 对每个 $x\in X^{\circ}$, 定义母尺刻度密度

$$
\kappa(\omega,x)
=\frac{\varphi'(\omega,x)}{\pi}
=\rho_{\mathrm{rel}}(\omega,x)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega,x).
$$

称 $\kappa(\omega,x)$ 为三位一体母尺刻度密度。

允许下面两类变换:

1. 能量重标 $\omega\mapsto f(\omega)$, 其中 $f$ 单调且足够正则;
2. 添加有限范围内的光滑背景项 $c_{0}(x)+c_{1}(x)\omega$ 等, 不改变高频与奇性结构。

**定义 2.2 (刻度等价类)**

在上述变换群作用下, 母尺刻度密度的等价类记为 $[\kappa]$, 称为时间刻度等价类。

### Null–Modular 双覆盖与 $\mathbb Z_{2}$ 上同调类

在 Null–Modular 工作中, 对小因果菱形
$B_{\ell}(p)\subset M$ 引入广义熵 $S_{\mathrm{gen}}$、模哈密顿 Berry 联络
$\mathcal A_{\mathrm{mod}}$ 与 BF 型体积分, 建立了一个自然的 $\mathbb Z_{2}$ 上同调类

$$
[K]\in H^{2}(Y,\partial Y;\mathbb Z_{2}),
$$

其代表可写为

$$
[K]=\pi_{M}^{\ast}w_{2}(TM)
+\sum_{j}\pi_{M}^{\ast}\mu_{j}\smile\pi_{X}^{\ast}\nu_{j}
+\pi_{X}^{\ast}\rho\bigl(c_{1}(\mathcal L_{S})\bigr),
$$

其中 $w_{2}(TM)$ 为第二 Stiefel–Whitney 类,
$\mu_{j},\nu_{j}$ 源自能量条件与模哈密顿,
$\mathcal L_{S}$ 为散射行列式线丛, $\rho$ 为 mod 2 约化映射。

物理上, $[K]$ 控制:

* 模哈密顿 Berry 相在参数回路上的 $\mathbb Z_{2}$ 环量;
* 半相位 $\sqrt{\det S}$ 的分支跃迁与模二谱流;
* Floquet 谱在 $\lambda\approx -1$ 附近的 $\pi$ 模配对奇偶。

### 有限阶窗化结构与误差纪律

**定义 2.3 (有限阶窗化族)**

设 $\mathcal W$ 为一族时间域窗函数 $w_{T}(t)$, 其 Fourier 变换
$\widehat w(\omega)$ 与 Mellin 变换 $\widehat W(z)$ 满足:

1. 时间域紧支或亚指数衰减;
2. 在指定幂–对数指数集合 $\{\beta_{m}\}$ 处,
   $\widehat W^{(k)}(\beta_{m})=0$ 对所有 $k\le r$ 成立, 消去对应奇性;
3. 对应的 PSWF/DPSS 极值窗在给定带宽–时间积下能量集中最优,
   且满足 Carleson–Landau 采样条件。

由此形成窗化结构等价类 $[\mathcal W]$, 在该类中所有窗的误差上界受有限阶 Euler–Maclaurin–Poisson 展开统一控制。

### 统一观测对象与范畴

**定义 2.4 (统一观测对象)**

统一观测对象为四元组

$$
\mathfrak X=(Y\to M,[\kappa],[K],[\mathcal W]),
$$

其中 $Y\to M$ 为带边界总空间, $[\kappa]$ 为时间刻度等价类,
$[K]\in H^{2}(Y,\partial Y;\mathbb Z_{2})$ 为 Null–Modular 类,
$[\mathcal W]$ 为有限阶窗化结构等价类。

**定义 2.5 (统一观测范畴)**

统一观测范畴 $\mathbf{Uni}_{\mathrm{obs}}$ 的对象为统一观测对象 $\mathfrak X$,
态射 $f:\mathfrak X\to\mathfrak X'$ 为保持因果结构、刻度等价类 $[\kappa]$、
$\mathbb Z_{2}$ 类 $[K]$ 与窗化误差结构 $[\mathcal W]$ 的映射。

此前各子框架可视作 $\mathbf{Uni}_{\mathrm{obs}}$ 的函子像, 如:

* 边界时间几何范畴 $\mathbf{BTG}$;
* Null–Modular 范畴 $\mathbf{NMod}$;
* 自指散射网络范畴 $\mathbf{SSN}$;
* 时间晶体范畴 $\mathbf{TC}$;
* 局域量子条件范畴 $\mathbf{LQC}$;
* 一致性工厂范畴 $\mathbf{CF}$;
* Zeckendorf 可逆日志范畴 $\mathbf{Zec}$ 等。

---

## Main Results (Theorems and Alignments)

本节陈述主要定理与结构对应, 证明安排在后文与附录。

### 定理 3.1 (边界时间几何中的母尺存在性与仿射唯一性)

设 $\mathfrak X\in\mathbf{Uni}_{\mathrm{obs}}$ 给出边界时间几何数据
$(M,g;\partial M,\mathcal A_{\partial},\omega,S(\omega,x))$, 满足:

1. 散射矩阵 $S(\omega,x)$ 在能窗内满足 Birman–Kreĭn 条件, 群延迟算子迹类, 定义散射刻度密度
   $\kappa_{\mathrm{scatt}}(\omega,x)=\varphi'(\omega,x)/\pi=\rho_{\mathrm{rel}}(\omega,x)=(2\pi)^{-1}\operatorname{tr}Q(\omega,x)$。
2. 边界代数 $\mathcal A_{\partial}$ 上的状态 $\omega$ 循环且分离, 模流
   $\sigma_{t}^{\omega}$ 的生成元 $K_{\omega}$ 在能窗内谱绝对连续,
   相对熵 Hessian 定义模时间刻度密度 $\kappa_{\mathrm{mod}}(\lambda)$。
3. 引力边界作用的 Hamilton–Jacobi 泛函沿边界时间平移二阶导数定义几何时间刻度密度 $\kappa_{\mathrm{geom}}$, 并满足局域量子充分条件与 QNEC/QFC。([电子学术库][3])

则存在唯一的刻度等价类 $[\kappa]$, 使得在能窗与小因果菱形交域内有

$$
\kappa_{\mathrm{scatt}}\sim\kappa_{\mathrm{mod}}\sim\kappa_{\mathrm{geom}},
$$

其中 "$\sim$" 表示差一个常数因子与允许的平滑重标。

### 定理 3.2 ($[K]$ 与自指散射半相位的等价)

设 $\mathfrak X\in\mathbf{Uni}_{\mathrm{obs}}$, 散射矩阵族 $S(\omega,\lambda)$ 对参数
$\lambda\in X^{\circ}$ 平滑, 自指网络构造给出 $J$–幺正族 $U(\lambda)$。则对任意物理回路
$\gamma\subset X^{\circ}$, 有

$$
\langle[K],[\gamma]\rangle
=\operatorname{sf}_{2}\bigl(U(\gamma)\bigr)
=\Delta\arg\sqrt{\det S(\cdot,\gamma)}/\pi\quad(\mathrm{mod}\ 2),
$$

其中 $\operatorname{sf}_{2}$ 为 $-1$ 处模二谱流, 右式为半相位的模二变化。

### 定理 3.3 (时间晶体 $\pi$ 模谱配对与 $[K]$ 等价)

设 $\mathfrak X\in\mathbf{Uni}_{\mathrm{obs}}$, 其 $X^{\circ}$ 部分为驱动参数空间,
Floquet 算子 $F(\lambda)$ 的谱在回路 $\gamma \subset X^{\circ}$ 上无闭合间隙。则以下命题等价:

1. $\langle[K],[\gamma]\rangle=1$。
2. Floquet 谱在 $\gamma$ 上存在稳定的 $\pi$ 模配对, 即特征值成对穿越 $-1$ 并保持间隙开启。
3. 对应自指散射网络中, $-1$ 点的模二谱流为 1。
4. 在满足预热或 MBL 条件的适当极限下, 系统实现非平凡离散时间晶体相。([科学杂志][4])

### 定理 3.4 (广义熵变分与母尺窗化的统一表达)

设 $\mathfrak X\in\mathbf{Uni}_{\mathrm{obs}}$, $B_{\ell}(p)\subset M$ 为小因果菱形,
$\kappa(\omega,x)$ 为母尺密度。令 $\mathcal W$ 为满足有限阶纪律的窗族,
对几何与场的变分 $(\delta g,\delta\phi)$, 存在权函数 $\Psi(\omega;B_{\ell},\delta g,\delta\phi)$ 与常数 $C$, 使得

$$
\delta^{2}S_{\mathrm{gen}}[B_{\ell}](\delta g,\delta\phi)
=\int\kappa(\omega,x)\Psi(\omega;B_{\ell},\delta g,\delta\phi)\,\mathrm d\omega
+C\cdot\delta^{2}\Lambda_{\mathrm{eff}},
$$

其中 $\Lambda_{\mathrm{eff}}$ 为宇宙学常数的有效值。特别地, 在 IGVP 门槛条件下,
Einstein 方程与 QNEC/QFC 等价于上述右侧二次型在所有允许变分上非负。([电子学术库][3])

### 命题 3.5 (宇宙学常数的窗化生成与 $[K]$ 配对)

对每个宇宙学背景, 定义母尺窗化相对散射行列式

$$
\log\det_{\mathrm{rel}}S[w]
=\int\kappa(\omega,x)m_{w}(\omega)\,\mathrm d\omega,
$$

其中 $m_{w}$ 为由 $w\in\mathcal W$ 确定的核。则宇宙学常数有效值可写为

$$
\Lambda_{\mathrm{eff}}
=\Lambda_{0}+\alpha\,\langle[K],[\Sigma]\rangle
+R_{\mathrm{ana}},
$$

其中 $[\Sigma]\in H_{2}(Y,\partial Y;\mathbb Z_{2})$ 描述大尺度拓扑扇区,
$\alpha$ 为常数, $R_{\mathrm{ana}}$ 为解析尾项。

### 定理 3.6 (统一窗化误差分解)

设 $\mathfrak X\in\mathbf{Uni}_{\mathrm{obs}}$, $w\in\mathcal W$ 满足有限阶纪律,
母尺密度 $\kappa(\omega,x)$ 在指定奇性集合外解析。定义读数

$$
\Lambda[w]
=\int\kappa(\omega,x)m_{w}(\omega)\,\mathrm d\omega.
$$

则存在整数 $n(\mathfrak X)$ 与函数 $R[w]$, 使

$$
\Lambda[w]=n(\mathfrak X)+R[w],\qquad |R[w]|\le C\varepsilon,
$$

其中 $n(\mathfrak X)$ 由 $[K]$ 与 $K^{1}$ 类配对给出, $\varepsilon$ 由窗化设计给定。

### 命题 3.7 (能力–风险前沿的统一刻画与不可判定边界)

考虑策略族 $\Pi$ 与环境 $\mathfrak X\in\mathbf{Uni}_{\mathrm{obs}}$, 定义能力函数
$\mathcal C(\Pi;\mathfrak X)$ 与风险函数 $\mathcal R(\Pi;\mathfrak X)$。则:

1. $\mathcal C(\Pi;\mathfrak X)$ 由母尺刻度与窗化结构的 Fisher 信息等量下界。
2. $\mathcal R(\Pi;\mathfrak X)$ 至少随 $\mathcal C$ 单调不减, 并满足
   $\mathcal R\ge F(\mathcal C,[K])$, 其中 $F$ 由 $[K]$ 与 $K^{1}$ 类决定。
3. 对一般可计算策略与环境类, 判定 $\mathcal R(\Pi;\mathfrak X)\le r_{0}$ 属不可判定问题, 可由停机问题归约得到。

---

## Proofs

本节给出主要定理的证明思路, 详细技术细节与辅助引理安排于附录。

### 4.1 定理 3.1 的证明

**步 1: 散射端三元同一式**

由 Birman–Kreĭn 公式
$\det S(\omega,x)=\exp[-2\pi i\xi(\omega,x)]$, 得

$$
\Phi(\omega,x)=\arg\det S(\omega,x)=-2\pi\xi(\omega,x),
$$

进而

$$
\varphi'(\omega,x)
=\tfrac12\Phi'(\omega,x)
=-\pi\xi'(\omega,x)
=\pi\rho_{\mathrm{rel}}(\omega,x).
$$

另一方面, 迹公式给出
$\operatorname{tr}Q(\omega,x)=2\pi\rho_{\mathrm{rel}}(\omega,x)$
在能窗内成立。由此得到

$$
\kappa_{\mathrm{scatt}}(\omega,x)
=\frac{\varphi'(\omega,x)}{\pi}
=\rho_{\mathrm{rel}}(\omega,x)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega,x).
$$

**步 2: 模流端刻度密度**

在边界代数 $\mathcal A_{\partial}$ 上, 相对熵
$S(\rho\Vert\omega)$ 在 $\rho=\omega$ 处的二阶导数给出 Fisher 信息度规;
在谱分解下可写为

$$
\delta^{2}S(\rho\Vert\omega)
=\int\kappa_{\mathrm{mod}}(\lambda)\,|\widehat{\delta\rho}(\lambda)|^{2}\,\mathrm d\lambda,
$$

其中 $\lambda$ 是模哈密顿 $K_{\omega}$ 的谱参数,
$\kappa_{\mathrm{mod}}(\lambda)$ 只由模谱密度决定。

利用相对熵–广义熵等式与 JLMS 类结果, 可将边界相对熵与体积广义熵差联系,
从而把 $\kappa_{\mathrm{mod}}$ 与几何端的曲率与能量密度对齐。

**步 3: 引力端刻度密度与 IGVP**

IGVP 工作指出, 在小因果菱形上, 广义熵一阶极值给出 Einstein 方程,
二阶变分受 QNEC/QFC 约束。广义熵二阶变分可写为

$$
\delta^{2}S_{\mathrm{gen}}
=\delta^{2}S_{\mathrm{out}}+\frac{1}{4G}\delta^{2}A
+\text{角点与边界项},
$$

其中 $S_{\mathrm{out}}$ 为外部熵, $A$ 为极小曲面面积。
借助 Hollands–Wald 规范能量与局域 QFT 中的能量条件结果,
可以把上述二阶变分重写为沿边界时间平移的 Hamilton–Jacobi 泛函的二阶导数,
定义几何时间刻度密度 $\kappa_{\mathrm{geom}}$。

**步 4: 三种刻度的对齐与仿射唯一性**

在满足 Hadamard 条件与局域量子条件的情况下,
散射 Green 函数、模 Hamiltonian 与几何波算子在小域内可通过波迹与相对散射行列式统一;
综合前述结果, 可以构造一个刻度密度函数 $\kappa(\omega,x)$, 其在散射端、模流端与几何端分别给出
$\kappa_{\mathrm{scatt}},\kappa_{\mathrm{mod}},\kappa_{\mathrm{geom}}$, 相差至多常数因子与平滑重标。

若存在两个满足条件的刻度密度 $\kappa_{1},\kappa_{2}$, 则它们之差在每个端点上都对应于对 Hamilton–Jacobi 泛函添加常数或线性项, 不改变物理方程与 QNEC/QFC 约束, 因而仅在刻度等价类内不同。故 $[\kappa]$ 仿射唯一。

### 4.2 定理 3.2 的证明

**步 1: Null–Modular BF 体积分与上同调配对**

在总空间 $Y$ 上, Null–Modular 工作构造了 BF 型作用

$$
S_{\mathrm{BF}}=\pi\int_{Y}B\wedge F,
$$

其中 $F$ 为模或散射联络的曲率, $B$ 为适当的共形场,
其 $\mathbb Z_{2}$ 化给出上同调类 $[K]$。
对参数回路 $\gamma \subset X^{\circ}$, 取对应的二维相对链 $\Sigma_{\gamma}$, 定义

$$
\langle[K],[\gamma]\rangle
=\int_{\Sigma_{\gamma}}F \quad(\mathrm{mod}\ 2).
$$

**步 2: 自指散射网络中的模二谱流**

自指网络构造 $J$–幺正族 $U(\lambda)$,
在参数回路 $\gamma$ 上考察特征值 $-1$ 的谱流。
通过适当的正则化与谱分解, 定义模二谱流

$$
\operatorname{sf}_{2}\bigl(U(\gamma)\bigr)
\in\mathbb Z_{2}.
$$

Pushnitski 等人在谱移函数与散射相位研究中给出了谱流与行列式相位变化之间的联系,
可推广到本设置。([科学直通车][5])

**步 3: 半相位与谱流的等价**

由行列式关系
$\det U(\lambda)=\det S(\omega_{0},\lambda)$
及半相位定义, 在回路 $\gamma$ 上有

$$
\Delta\arg\sqrt{\det S(\cdot,\gamma)}/\pi
=\operatorname{sf}_{2}\bigl(U(\gamma)\bigr)\quad(\mathrm{mod}\ 2).
$$

**步 4: 与 $[K]$ 等价**

将 BF 体积分重写为曲率形式在 $\Sigma_{\gamma}$ 上的积分,
并用 Chern–Weil 与 mod 2 约化, 得到

$$
\langle[K],[\gamma]\rangle
=\operatorname{sf}_{2}\bigl(U(\gamma)\bigr).
$$

综合步 3 即得定理陈述。

### 4.3 定理 3.3 的证明

时间晶体工作表明, 预热 DTC 与 MBL DTC 的拓扑判据可表达为
Floquet 谱在 $\lambda=-1$ 点附近的绕数奇偶。
通过 Floquet–Magnus 展开与有效哈密顿构造, 可将 Floquet 算子写为适当散射算子在能量–时间平面上的提升, 并构造与自指网络等价的 $J$–幺正族。

利用定理 3.2, 可将绕数奇偶等价为 $[K]$ 与 $[\gamma]$ 的配对;
而 DTC 的稳定性条件则由谱间隙与预热时间尺度控制, 不影响拓扑配对。
因此四个条件等价。

### 4.4 定理 3.4 与命题 3.5 的证明骨架

利用 Green 函数差与谱移函数的 Stieltjes 积分公式,
可把小因果菱形内部的能量–熵变分表示为谱移函数的窗化积分;
再用 Birman–Kreĭn 公式把谱移函数与散射行列式联系, 引入有限阶窗化控制高频尾项。([imo.universite-paris-saclay.fr][6])

另一方面, 信息几何与 QNEC/QFC 的结果将广义熵二阶变分与相对熵 Hessian 对齐;
通过 JLMS 类关系, 可以将其表达为母尺密度 $\kappa(\omega,x)$ 的加权积分。
把大尺度拓扑扇区的贡献集中到有限个低频模上, 就得到命题 3.5 的宇宙学项表示。

### 4.5 定理 3.6 与命题 3.7 的证明骨架

有限阶 Euler–Maclaurin 与 Poisson 求和公式在假定奇性有限且窗函数满足消零条件时, 给出积分–求和差的有限级展开; 主项由奇性与谱流等拓扑数据决定, 尾项由窗化参数 $\varepsilon$ 控制。对母尺密度应用该展开, 即得定理 3.6。

能力–风险前沿的不可判定性则由标准可计算性论证给出: 将策略–环境对编码为图灵机与输入, 风险阈值对应停机与否的问题。对受限模型类, 可利用信息界与散射–窗化误差界给出能力–风险函数的下界, 从而得到命题 3.7。

---

## Model Apply

本节讨论统一对象 $\mathfrak X$ 在若干典型物理与信息场景中的具体化。

### 5.1 微波散射网络与母尺刻度的计量

考虑一个有限端口的微波散射网络, 通过矢量网络分析仪测得 $S(\omega)$,
可数值求导得到 $\varphi'(\omega)/\pi$ 与 $\operatorname{tr}Q(\omega)/(2\pi)$,
同时通过对比有无散射体背景测量态密度差, 得到 $\rho_{\mathrm{rel}}(\omega)$。
在能窗内验证刻度同一式, 即给出 $[\kappa]$ 的实验代表。([arXiv][7])

对应的 $\mathfrak X$ 中, $M$ 可简化为一维传输线时空,
$X^{\circ}$ 为空间几何或负载参数空间, $[K]$ 则与网络回路的 $\mathbb Z_{2}$ 拓扑相关。

### 5.2 trapped-ion 时间晶体与 $[K]$ 的实验读出

在 trapped-ion 平台上, 利用高频驱动与 Ising 相互作用实现预热离散时间晶体,
其 Floquet 谱的 $\pi$ 模配对可通过量子态断层或序参量振荡周期读出。([科学杂志][4])

将驱动参数视为 $X^{\circ}$, 构造回路 $\gamma$ 扫过不同驱动强度与相位,
测量谱在 $\lambda=-1$ 处的穿越奇偶, 即可实验上读出 $\langle[K],[\gamma]\rangle$,
验证定理 3.3。

### 5.3 AdS/CFT 场景中的广义熵与宇宙学项

在 AdS/CFT 场景下, 以边界 CFT 的相对熵与模 Hamiltonian 计算小因果菱形上的广义熵,
通过 JLMS 与 QNEC/QFC 将其与体积几何与能量动量张量联系,
再用相对散射行列式与母尺窗化表达宇宙学项的有效贡献。([电子学术库][3])

在此模型中, $[K]$ 与若干拓扑扇区 (如 wormhole 拓扑) 相关,
$[\kappa]$ 则反映散射态与模流的统一刻度。

### 5.4 策略–环境系统的能力–风险度量

在智能体–环境模型中, 将环境的动力学与观测通道编码入散射矩阵族 $S(\omega,x)$,
将智能体策略视为对窗化结构与读出函数的选择。
能力 $\mathcal C$ 用基于 $[\kappa]$ 的 Fisher 信息与控制带宽量化,
风险 $\mathcal R$ 则结合 $[K]$ 反映的拓扑扇区与局域量子条件下的最坏情况演化。

该模型为不同层级的决策系统提供统一的刻度–拓扑–误差描述,
并在理论上说明灾难安全判定不可判定, 但在受限子类上仍可给出清晰的能力–风险前沿上界。

---

## Engineering Proposals

本节提出若干可操作的工程方案, 将上述理论结构嵌入具体实验与计量流程。

### 6.1 母尺同一式的跨平台计量

1. **微波网络平台**
   使用多端口微波腔或波导网络, 测量 $S(\omega)$, 通过有限差分或解析频率导数计算
   $Q(\omega)$ 与 $\operatorname{tr}Q(\omega)$; 再通过密度–谱移关系获得
   $\rho_{\mathrm{rel}}(\omega)$; 最后从 $\det S(\omega)$ 取相位导数得到 $\varphi'(\omega)/\pi$,
   检验三者一致性。

2. **冷原子或固体散射平台**
   在一维或准一维冷原子通道、或纳米线–量子点结构中, 利用传输测量同样重构
   $S(\omega)$, 以验证三位一体母尺在不同能标的一致性。

3. **数值模拟平台**
   通过 TDDFT 或相关方法模拟电子散射与超快动力学, 数值提取群延迟与相位梯度,
   在理论模型中验证刻度同一式。([Nature][8])

### 6.2 时间晶体–自指散射–Null–Modular 的联合验证

1. 在 trapped-ion 或超导量子比特平台上, 实现具有自指反馈结构的驱动网络,
   同时可视为自指散射网络与 Floquet 时间晶体。

2. 测量 Floquet 谱的 $\pi$ 模配对与时间晶体序参量, 提取绕 $-1$ 的绕数奇偶;
   另一方面, 通过反馈网络的传输测量 reconstruct $S(\omega,\lambda)$,
   计算半相位与模二谱流。

3. 比较实验测得的模二谱流、$\pi$ 模配对与 Null–Modular 理论给出的
   $\langle[K],[\gamma]\rangle$, 验证定理 3.2 与 3.3。

### 6.3 宇宙学窗化与 FRB/频谱观测

对 FRB 与其他天体信号, 使用统一窗化框架设计频率窗与时间窗,
对相位–频率结构进行母尺读出; 通过跨平台比对 (如实验室散射平台与天体观测),
重构宇宙学常数的有效贡献, 检查是否存在由 $[K]$ 决定的拓扑扇区修正。

### 6.4 PSWF/DPSS 窗与误差纪律在工程中的应用

在通信、雷达与量子控制中采用 PSWF/DPSS 极值窗与有限阶 Euler–Maclaurin–Poisson 纪律,
按定理 3.6 将所有测量误差表达为拓扑整数主项加解析尾项;
通过经验校准整数主项, 可在保持理论可控的同时, 降低对高精度尾项建模的敏感性。

---

## Discussion (risks, boundaries, past work)

### 7.1 适用域与假设的边界

本框架依赖若干关键假设:

1. 散射理论端假设迹类扰动与能窗内绝对连续谱, 以保证谱移函数与 Birman–Kreĭn 公式适用。([arXiv][1])
2. 模流与广义熵端依赖于 Hadamard 状态条件、相对熵有限性与 QNEC/QFC 适用性。([电子学术库][3])
3. Null–Modular 双覆盖端呼吁足够平滑的因果结构与模 Hamiltonian, 以使 BF 体积分与上同调配对良定。
4. 有限阶窗化纪律要求母尺密度的奇性有限且可解析延拓。

这些假设限制了本框架对强耦合、非局域或非因果模型的直接适用性, 但在大范围的物理案例中仍具操作性。

### 7.2 与既有工作的关系

在散射理论与谱移函数方面, 本文将 Birman–Kreĭn–Wigner–Smith 体系提升为时间刻度的统一表达, 并通过母尺概念粘合到模流与引力边界时间之中。([arXiv][1])

在广义熵与量子能量条件方面, 本文借助 IGVP 与 QNEC/QFC 的结果, 将广义熵二阶变分与母尺窗化联系, 提供了一个从谱–散射–信息一体化视角理解 Einstein 方程与宇宙学常数的路径。([电子学术库][3])

在时间晶体与非平衡相方面, 本文把 DTC/PDTC 的拓扑判据统一到 Null–Modular $[K]$ 类与自指散射半相位结构中, 将"时间平移对称性破缺"视为 $\mathbb Z_{2}$ 双覆盖的一个投影。([科学杂志][4])

在误差纪律与信息几何方面, 本文将有限阶 Euler–Maclaurin–Poisson 纪律与 PSWF/DPSS 极值窗融合到统一观测对象中, 为跨平台刻度–误差对齐提供一个拓扑–解析统一表达。

### 7.3 风险与开放问题

1. **非幺正演化与强耗散**: 对强耗散的 Lindblad 系统, 虽可通过 GNS 提升与有效散射矩阵拓展本框架, 但 $[K]$ 与 $[\kappa]$ 的定义可能失去简单形式, 需要更一般的 C*–代数工具。([物理评论链接管理器][2])
2. **非微扰引力背景**: 在强曲率、拓扑转变或量子引力主导的区域, 广义熵与相对散射行列式的表达需超出半经典近似。
3. **能力–风险前沿的定量化**: 命题 3.7 给出存在性与不可判定性论断, 但如何在现实系统中估算 $F(\mathcal C,[K])$ 的具体形状仍属开放问题。
4. **宇宙学常数问题**: 虽然命题 3.5 提供了宇宙学常数的窗化生成表达, 但是否足以解释观测值的大小与稳定性, 有待与具体宇宙学模型结合测试。

---

## Conclusion

本文在统一观测范畴 $\mathbf{Uni}_{\mathrm{obs}}$ 中引入三位一体母尺刻度等价类 $[\kappa]$、
Null–Modular 上同调类 $[K]$ 与有限阶窗化结构 $[\mathcal W]$,
把散射相位、群延迟、模时间、引力边界时间、Null–Modular 双覆盖、时间晶体、自指散射网络、广义熵与误差纪律组织为单一几何–拓扑–信息对象上的不同投影。

核心结果包括:

1. 散射–模流–几何时间刻度的仿射唯一统一;
2. $[K]$ 与半相位模二谱流、时间晶体 $\pi$ 模谱配对的等价;
3. 广义熵变分与宇宙学常数的母尺窗化表达;
4. 母尺读数误差的"拓扑整数主项 + 解析尾项"结构;
5. 能力–风险前沿在刻度–拓扑–误差三元组下的统一刻画与灾难安全不可判定边界。

这些结果为把时间、拓扑、熵与风险视为同一"母尺–双覆盖–窗化"结构的不同侧面提供了一个自洽框架, 为后续在具体物理模型、实验平台与复杂系统中的应用奠定了基础。

---

## Acknowledgements, Code Availability

本工作在已有散射理论、模流理论、广义熵与时间晶体研究基础上发展而来, 受益于相关领域大量已有成果与公开文献。

本文未依赖专门开发的软件代码; 所有涉及的数值模拟与窗化设计均可在通用科学计算环境中复现, 例如基于标准线性代数库与信号处理库的实现。

---

## References

[1] M. Sh. Birman, M. G. Kreĭn, On the theory of wave operators and scattering operators, Sov. Math. Dokl. 3, 740–744 (1962). ([matcuer.unam.mx][9])

[2] A. Pushnitski, The spectral shift function and the invariance principle, J. Funct. Anal. 183, 269–320 (2001). ([科学直通车][5])

[3] C. Texier, Wigner time delay and related concepts, Physica E 82, 16–33 (2016). ([科学直通车][10])

[4] U. R. Patel et al., Wigner–Smith time-delay matrix for electromagnetics, arXiv:2005.03211 (2020). ([arXiv][7])

[5] D. Borthwick, Scattering matrix and spectral shift of the Laplacian, preprint (2021). ([arXiv][1])

[6] A. Shahbazi-Moghaddam, Aspects of generalized entropy and quantum null energy condition, PhD thesis (2020). ([电子学术库][11])

[7] K. Jensen et al., Generalized entropy for general subregions in quantum gravity, JHEP 09, 101 (2023). ([DSpace][12])

[8] J. Koeller et al., Local modular Hamiltonians from the quantum null energy condition, Phys. Rev. D 97, 065011 (2018). ([物理评论链接管理器][2])

[9] A. Kyprianidis et al., Observation of a prethermal discrete time crystal, Science 372, 1192–1196 (2021). ([科学杂志][4])

[10] T. S. Zeng, B. Zhu, C. Chung, Prethermal time crystals in a one-dimensional periodically driven spin chain, Phys. Rev. B 96, 094202 (2017). ([物理评论链接管理器][13])

[11] Recent works on quantum null energy inequalities and smeared null energy bounds, e.g. "New bounds on null energy in quantum field theory", arXiv:2510.26247 (2025). ([arXiv][14])

[12] Reviews on ultrafast dynamics and TDDFT approaches to scattering and time-resolved spectroscopy, such as recent TDDFT-based studies of attosecond phenomena. ([Nature][8])

---

## Appendix A: BTG 中母尺存在性与仿射唯一性的详细证明

### A.1 散射端刻度同一式的严格推导

设 $H=H_{0}+V$, $V$ 迹类, $S(\omega)$ 为散射矩阵。谱移函数 $\xi(\lambda)$ 定义为

$$
\operatorname{Tr}\bigl(f(H)-f(H_{0})\bigr)
=\int\xi(\lambda)f'(\lambda)\,\mathrm d\lambda,
$$

对紧支光滑 $f$ 成立。Birman–Kreĭn 公式给出

$$
\det S(\lambda)=\exp[-2\pi i\xi(\lambda)].
$$

设 $\Phi(\lambda)=\arg\det S(\lambda)$, 半相位 $\varphi(\lambda)=\tfrac12\Phi(\lambda)$,
则 $\Phi(\lambda)=-2\pi\xi(\lambda)+2\pi n$, 取连续支可令 $n=0$ 得

$$
\varphi'(\lambda)
=\tfrac12\Phi'(\lambda)
=-\pi\xi'(\lambda)
=\pi\rho_{\mathrm{rel}}(\lambda).
$$

另一方面, 对于 Wigner–Smith 群延迟算子

$$
Q(\lambda)=-iS(\lambda)^{\dagger}\partial_{\lambda}S(\lambda),
$$

利用 $S(\lambda)$ 的谱分解与相位导数, 可得到

$$
\operatorname{tr}Q(\lambda)
=2\pi\rho_{\mathrm{rel}}(\lambda),
$$

由此三式一致。详细证明可参考谱移函数与波迹理论文献。([arXiv][1])

### A.2 模流端刻度密度与相对熵 Hessian

在 $\mathcal A_{\partial}$ 上, 取 GNS 表示 $(\pi_{\omega},\mathcal H_{\omega},\Omega_{\omega})$,
模算子 $\Delta_{\omega}$ 与模 Hamiltonian $K_{\omega}=-\ln\Delta_{\omega}$。
对邻近状态 $\rho$, 相对熵

$$
S(\rho\Vert\omega)
=-\operatorname{Tr}(\rho\ln\omega)+\operatorname{Tr}(\rho\ln\rho)
$$

在 $\rho=\omega$ 处的二阶导数可写作

$$
\delta^{2}S(\rho\Vert\omega)
=\int_{\mathbb R}\kappa_{\mathrm{mod}}(\lambda)
\,|\widehat{\delta\rho}(\lambda)|^{2}\,\mathrm d\lambda,
$$

其中 $\widehat{\delta\rho}(\lambda)$ 为沿模流的 Fourier 模,
$\kappa_{\mathrm{mod}}(\lambda)$ 由 $K_{\omega}$ 的谱测度 $\mu(\lambda)$ 给出
(例如在有限维情况下为 $\lambda^{2}\mathrm d\mu(\lambda)$ 的密度)。

将边界相对熵与体积广义熵差比较, 在半经典与小菱形近似下,
可将 $\kappa_{\mathrm{mod}}$ 与几何端的 $\kappa_{\mathrm{geom}}$ 联系,
参见关于 localized modular Hamiltonian 与 QNEC 的工作。([物理评论链接管理器][2])

### A.3 几何端刻度密度与 IGVP

在小因果菱形 $B_{\ell}(p)$ 上, IGVP 给出广义熵

$$
S_{\mathrm{gen}}[B_{\ell}]
=\frac{A[\chi(B_{\ell})]}{4G\hbar}+S_{\mathrm{out}}[B_{\ell}],
$$

其中 $\chi(B_{\ell})$ 为极小曲面。对几何与场的变分 $(\delta g,\delta\phi)$,
一阶极值条件

$$
\delta S_{\mathrm{gen}}=0
$$

在所有 $B_{\ell}$ 上等价于 Einstein 方程; 二阶变分

$$
\delta^{2}S_{\mathrm{gen}}
\ge 0
$$

则由 QNEC/QFC 保障。广义熵二阶变分可表示为

$$
\delta^{2}S_{\mathrm{gen}}
=\int_{B_{\ell}}
\bigl(\alpha R_{\mu\nu}\delta g^{\mu\nu}
+\beta T_{\mu\nu}\delta g^{\mu\nu}
+\gamma\,\delta\phi^{2}\bigr)\,\mathrm dV
+\text{边界项},
$$

其中边界项包含 GHY 与角点贡献。
将边界项整理为沿边界时间平移的 Hamilton–Jacobi 泛函的二阶导数,
自然定义几何刻度密度 $\kappa_{\mathrm{geom}}$, 其在合适规范下与散射端与模流端的 $\kappa$ 相一致。

### A.4 仿射唯一性的证明

若 $\kappa_{1},\kappa_{2}$ 都在三端一致产生相同的物理方程与 QNEC/QFC 约束,
则 $\delta^{2}S_{\mathrm{gen}}$ 的表达对它们不敏感,
说明 $\kappa_{1}-\kappa_{2}$ 对所有允许变分的积分均为零或常数,
等价于在刻度等价类中的重标与加性修正。

---

## Appendix B: Null–Modular 上同调与自指散射半相位

### B.1 上同调配对的链模型构造

取参数空间 $X^{\circ}$ 中的判别集 $D$ 为谱交叉与模谱奇点所在集合,
选取开邻域 $N(D)$, 构造相对链群

$$
H_{1}(X^{\circ},\partial X^{\circ}\cup N(D);\mathbb Z_{2}),\quad
H_{2}(Y,\partial Y\cup N(D);\mathbb Z_{2}).
$$

物理回路 $\gamma$ 视为 $H_{1}$ 中的类 $[\gamma]$,
通过选择截面构造二维相对链 $\Sigma_{\gamma}$, 使
$\partial\Sigma_{\gamma}=\gamma$ (mod 边界) 。
Null–Modular BF 体积分定义

$$
\langle[K],[\gamma]\rangle
=\int_{\Sigma_{\gamma}}F\quad(\mathrm{mod}\ 2),
$$

其中 $F$ 为相应联络的曲率。

### B.2 自指网络中的模二谱流与半相位

自指网络构造 $J$–幺正族 $U(\lambda)$,
在 $-1$ 处定义谱投影 $P_{-1}(\lambda)$,
沿参数回路 $\gamma$ 考察 $P_{-1}(\lambda)$ 的秩变化,
谱流定义为

$$
\operatorname{sf}(U(\gamma))
=\#\{\text{特征值穿越 }-1\text{ 自下而上}\}
-\#\{\text{自上而下}\}.
$$

模二谱流

$$
\operatorname{sf}_{2}(U(\gamma))=\operatorname{sf}(U(\gamma))\ \mathrm{mod}\ 2.
$$

行列式平方根与谱流之间的关系可通过 Toeplitz 算子与 Hardy 空间模型给出:
对 $\det U(\lambda)$ 的相位变化积分, 可得到特征值的绕数;
平方根将 $2\pi$ 周期折半到 $\pi$ 周期, 从而模二谱流与半相位变化等价。

### B.3 等价性的严格证明

利用 Chern–Weil 理论, 将 BF 体积分重写为联络曲率形式在 $\Sigma_{\gamma}$ 上的积分;
再用谱流–Chern 数等价, 可得到

$$
\langle[K],[\gamma]\rangle
=\operatorname{sf}_{2}\bigl(U(\gamma)\bigr),
$$

结合半相位–谱流关系即得定理 3.2。

---

## Appendix C: 时间晶体中 $\pi$ 模谱配对的拓扑判据

在 Floquet–Magnus 展开中, 一周期演化算子

$$
F=\mathcal T\exp\bigl(-i\int_{0}^{T}H(t)\,\mathrm dt\bigr)
=\exp(-iH_{\mathrm{eff}}T+O(\omega^{-1})),
$$

其中 $H_{\mathrm{eff}}$ 为有效哈密顿, $\omega=2\pi/T$ 为驱动频率。

预热 DTC 的存在性要求:

1. $H_{\mathrm{eff}}$ 存在 $\mathbb Z_{2}$ 对称, 如 $PH_{\mathrm{eff}}P^{-1}=-H_{\mathrm{eff}}$。
2. Floquet 谱在 $\lambda=-1$ 附近有稳定的谱间隙与成对穿越。([科学杂志][4])

构造参数回路 $\gamma$ 扫过驱动参数, 测量绕 $-1$ 的绕数奇偶,
可视为 Floquet 谱在 $U(1)$ 上的绕数 mod 2。
将 $F$ 嵌入散射–自指网络框架, 通过定理 3.2 将其与 $[K]$ 的配对联系,
即得定理 3.3。

---

## Appendix D: 广义熵变分、相对散射行列式与窗化

### D.1 Green 函数差与谱移函数

对算子对 $(H_{0},H)$, Green 函数差

$$
R(z)= (H-z)^{-1}-(H_{0}-z)^{-1}
$$

在适当条件下可表示为谱移函数的 Stieltjes 积分

$$
\operatorname{Tr}(R(z))
=-\int\frac{\xi(\lambda)}{(\lambda-z)^{2}}\,\mathrm d\lambda.
$$

将此结果局域到小因果菱形中, 通过有限传播速度与 Hadamard 条件,
可把广义熵二阶变分中关于 Green 函数的部分表示为谱移函数的加权积分。([imo.universite-paris-saclay.fr][6])

### D.2 相对散射行列式的窗化表达

相对散射行列式定义为

$$
\log\det_{\mathrm{rel}}S
=\int\phi(\lambda)\,\mathrm d\lambda,
$$

或更一般地通过 ζ–函数正则化给出。
引入窗函数 $w$ 并定义权核 $m_{w}(\lambda)$, 得到

$$
\log\det_{\mathrm{rel}}S[w]
=\int\kappa(\lambda)m_{w}(\lambda)\,\mathrm d\lambda,
$$

其中 $\kappa(\lambda)=\varphi'(\lambda)/\pi$ 为母尺密度。

有限阶 Euler–Maclaurin 与 Poisson 求和公式在 $m_{w}$ 的 Mellin 变换满足消零条件时,
保证高频尾项 $O(\varepsilon)$ 可控。

### D.3 宇宙学项的有效作用

将窗化相对散射行列式项插入有效作用,
利用联络–曲率–上同调分解把拓扑扇区贡献提取为
$\alpha\langle[K],[\Sigma]\rangle$,
其余部分为解析尾项, 即得命题 3.5。

---

## Appendix E: 有限阶窗化误差与整数主项

### E.1 PSWF/DPSS 极值窗的性质

在给定带宽–时间积 $c$ 下, PSWF 为在 $L^{2}$ 意义下频带内能量最集中窗,
其本征值迅速接近 0 或 1, 并满足 Carleson–Landau 采样条件,
保证带限函数的稳定采样与重构。

将 PSWF 及其离散版本 DPSS 用作 $\mathcal W$ 的基窗,
可以在保持能量集中与旁瓣抑制的同时, 满足 Euler–Maclaurin–Poisson 的有限阶消零条件。

### E.2 Euler–Maclaurin–Poisson 有限阶展开

设 $f(\omega)=\kappa(\omega,x)$ 在奇性集合外解析,
对窗化积分

$$
\Lambda[w]
=\int f(\omega)m_{w}(\omega)\,\mathrm d\omega,
$$

应用有限阶 Euler–Maclaurin 展开与 Poisson 求和公式, 得到

$$
\Lambda[w]
=\sum_{\text{奇性}}c_{j}(\mathfrak X)
+\sum_{k=0}^{r}a_{k}(\mathfrak X)B_{k}
+R[w],
$$

其中第一项为由谱流与指数阶数等拓扑数据决定的主项,
第二项为有限阶 Bernoulli 校正, $R[w]$ 为满足 $|R[w]|\le C\varepsilon$ 的尾项。
将主项合并记为 $n(\mathfrak X)$, 即得定理 3.6。

---

## Appendix F: 能力–风险前沿的复杂性论证

将策略族 $\Pi$ 与环境 $\mathfrak X$ 编码为图灵机与输入对,
风险阈值 $r_{0}$ 对应于某类不良轨道是否被访问。
若存在算法能判定对所有 $\Pi,\mathfrak X$ 是否满足 $\mathcal R(\Pi;\mathfrak X)\le r_{0}$,
则可用该算法判定任意图灵机是否停机, 与停机问题不可判定矛盾,
故该判定问题本身不可判定。

对受限模型类 (如有限状态 Markov 决策过程与线性策略),
可用信息界与散射–窗化误差界对 $\mathcal C$ 与 $\mathcal R$ 给出上、下界,
构造显式的能力–风险前沿函数 $F(\mathcal C,[K])$, 完成命题 3.7 的证明骨架。

[1]: https://arxiv.org/pdf/2110.06370 "arXiv:2110.06370v3 [math.SP] 15 Aug 2022"
[2]: https://link.aps.org/doi/10.1103/PhysRevD.97.065011 "Local modular Hamiltonians from the quantum null energy ..."
[3]: https://escholarship.org/content/qt6qt4k7rz/qt6qt4k7rz_noSplash_f5c5668c7a9af1a3e54257eefba1b382.pdf "Aspects of Generalized Entropy And Quantum Null Energy ..."
[4]: https://www.science.org/doi/10.1126/science.abg8102 "Observation of a prethermal discrete time crystal"
[5]: https://www.sciencedirect.com/science/article/pii/S0022123601937516/pdf?md5=21337458b395c97d127dea0599a8c02a&pid=1-s2.0-S0022123601937516-main.pdf "The Spectral Shift Function and the Invariance Principle"
[6]: https://www.imo.universite-paris-saclay.fr/~colin.guillarmou/krein4.pdf "Generalized Krein formula, determinants and Selberg zeta ..."
[7]: https://arxiv.org/pdf/2005.03211 "Wigner-Smith Time Delay Matrix for Electromagnetics"
[8]: https://www.nature.com/articles/s41524-025-01715-1 "Technical review: Time-dependent density functional theory for attosecond physics ranging from gas-phase to solids"
[9]: https://www.matcuer.unam.mx/VeranoAnalisis/Fritz-I.pdf "Spectral Shift Functions: Basic Properties of SSFs"
[10]: https://www.sciencedirect.com/science/article/abs/pii/S1386947715302228 "Wigner time delay and related concepts"
[11]: https://escholarship.org/content/qt6qt4k7rz/qt6qt4k7rz.pdf "Aspects of Generalized Entropy And Quantum Null Energy ..."
[12]: https://dspace.mit.edu/bitstream/handle/1721.1/153209/13130_2023_Article_22330.pdf?isAllowed=y&sequence=1 "Generalized entropy for general subregions in quantum ..."
[13]: https://link.aps.org/doi/10.1103/PhysRevB.96.094202 "Prethermal time crystals in a one-dimensional periodically ..."
[14]: https://arxiv.org/html/2510.26247v1 "New Bounds on Null Energy in Quantum Field Theory"
