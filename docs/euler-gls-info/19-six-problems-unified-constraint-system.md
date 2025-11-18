# 六大未解难题的统一约束系统

统一时间刻度、宇宙参数向量 $\Theta$ 与共同解空间

---

## Abstract

Within the standard framework of general relativity, quantum field theory and precision cosmology, six problems remain in strong tension with a naive extrapolation of known principles: the microscopic origin of black hole entropy and the information problem, the naturalness of the cosmological constant and dark energy, the structure of neutrino masses and PMNS mixing, the range of validity of the eigenstate thermalization hypothesis (ETH), the strong CP problem in QCD, and possible dispersion or Lorentz violation in gravitational waves. These are usually treated as independent questions attached to different energy scales and sectors.

This work embeds all six into a single structural framework based on a unified time-scale in scattering theory, boundary time geometry and a parameterized quantum cellular automaton (QCA) / matrix universe description. A finite-dimensional parameter vector $\Theta \in \mathcal P \subset \mathbb R^N$ is introduced, from which a universe object $\mathfrak U(\Theta)$ is constructed. All low-energy effective constants and laws are treated as derived observables $\mathcal O(\Theta)$. The six "open problems" are rephrased as six scalar constraints on $\Theta$, forming a single constraint map

$$
\mathcal C(\Theta) = \bigl(\mathcal C_{\mathrm{BH}},\mathcal C_\Lambda,\mathcal C_\nu,\mathcal C_{\mathrm{ETH}},\mathcal C_{\mathrm{CP}},\mathcal C_{\mathrm{GW}}\bigr)(\Theta) \in \mathbb R^6.
$$

Technically, the construction relies on the unified time-scale identity in scattering theory,

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{tr} Q(\omega),
$$

which equates the derivative of the total scattering phase, the relative density of states and the trace of the Wigner–Smith delay operator under standard trace-class perturbation assumptions. Via a QCA/matrix-universe continuous limit, this frequency-domain time-scale controls small causal diamonds, black hole thermodynamics, the vacuum contribution to the effective cosmological constant and the propagation of long-wavelength gravitational waves. Jointly with an internal Dirac block for fermions and Yukawa textures, it also controls neutrino masses and mixing, ETH-like spectral statistics, and the effective QCD CP angle.

On the mathematical side, under natural differentiability and independence hypotheses, the zero set

$$
\mathcal S = \{\Theta\in\mathcal P:\mathcal C(\Theta)=0\}
$$

is shown to be, locally, an embedded submanifold of dimension $N-6$. When $N=6$ and the Jacobian at a physical point has full rank, the solution set is locally discrete. In addition, strong-CP and topological-sector constraints force certain components of $\Theta$ to take values in a discrete set, so that the physically admissible parameter set is a finite or countable union of such lower-dimensional branches. This realizes, at the level of a well-defined map $\mathcal C(\Theta)=0$, the idea that "our Universe" is one point (or a finite set of points) in a strongly constrained parameter space.

On the physical side, the unified constraint system couples sectors that are usually analyzed separately. Black hole entropy and gravitational-wave dispersion jointly constrain the high- and low-frequency behavior of $\kappa(\omega;\Theta)$; cosmological constant naturalness and ETH constrain the mid-frequency spectral density; neutrino mixing and strong CP link internal Dirac spectra, Yukawa phases and topological data. The framework thus yields qualitative cross-predictions between areas such as neutrino physics and cosmology, or black hole thermodynamics and gravitational-wave propagation, and defines a systematic target for model-building: construct explicit QCA/matrix-universe realizations for which the six-component constraint $\mathcal C(\Theta)=0$ holds.

---

## Keywords

统一时间刻度；散射与谱移；Wigner–Smith 群延迟；量子元胞自动机；矩阵宇宙；黑洞熵；宇宙学常数；中微子质量与 PMNS 矩阵；本征态热化假设（ETH）；强 CP 问题；引力波色散；参数空间约束

---

## Introduction & Historical Context

### 1.1 六大未解难题的结构性张力

在广义相对论与量子场论的标准框架中，观测宇宙在定量上被极为成功地描述。然而，至少有六个问题在结构上暴露出该框架的"空白"与自然性难题：

1. **黑洞熵与信息问题**

   Bekenstein 与 Hawking 的工作表明，黑洞具有与视界面积成正比的熵，通常写作"面积除以 Planck 面积的四分之一"的定律，并满足类似普通热力学的四条定律。然而，这一天然结构的微观自由度实现及其与量子信息单调性、公理化量子引力的关系仍未被统一刻画。

2. **宇宙学常数与暗能量问题**

   观测表明宇宙当前加速膨胀，可由极小但非零的有效宇宙学常数或暗能量密度描述，而零点能的朴素量子场论估计则大出多数量级，形成所谓"宇宙学常数灾难"。如何在不依赖严重精细调参的前提下解释该自然性，是一个长期开放问题。

3. **中微子质量与 PMNS 混合结构**

   中微子振荡实验表明中微子具有非零质量和显著的味混合，标准 PMNS 矩阵同时携带多重混合角和可能的大 CP 破缺相位，要求超出标准模型的质量生成机制。如何从更上层的统一结构中推导出该质量层级与混合模式，是味物理与统一理论的重要问题。

4. **量子混沌与本征态热化假设（ETH）**

   ETH 为"孤立量子多体系统为何表现出热化行为"提供了一个本征态层面的解释，将高能本征态的局域可观测期望值与热力学函数联系在一起，并将非对角元抑制到熵指数小量。但 ETH 的适用范围、失效情形及其与底层微观动力学（如 QCA或随机矩阵行为）的关系，仍缺乏一个兼容引力和宇宙学的统一描述。

5. **强 CP 问题**

   QCD 允许含有 $\theta_{\mathrm{QCD}} F\tilde F$ 的 CP 破缺项，其自然值应为阶一常数。然而，中子电偶极矩实验将可观测有效角 $\bar\theta$ 约束在极小范围内，从而提出"为何强相互作用几乎不破坏 CP"的难题。现有解包括 Peccei–Quinn 机制与多种非标准模型构造，但在量子引力与宇宙整体层面上的根本解释仍不清晰。

6. **引力波色散与 Lorentz 破缺**

   联合观测事件 GW170817/GRB 170817A 显示，引力波速度与光速在天体尺度上高度一致，强烈限制了大类修正引力与 Lorentz 破缺模型中的色散修正和传播速度偏差。若引力与物质的底层结构是离散的，如由某种 QCA 或格点动力学给出，则为何在可观测频带上几乎不留下色散痕迹，构成了一项非平凡约束。

在常规研究中，这六个难题附着在不同的能标、自由度和观测渠道上，被视为"互不相干"的问题清单。本工作将它们统一重写为对一个有限维"宇宙参数向量" $\Theta$ 的六条约束，并分析这些约束在参数空间上的共同解结构。

### 1.2 统一时间刻度与边界时间几何

统一时间刻度的出发点是有界可追踪扰动下的散射理论。设 $H_0$ 是自由 Hamilton 量，$H=H_0+V$ 为可追踪扰动，定义散射矩阵 $S(\omega)$、谱移函数 $\xi(\omega)$、总散射相位

$$
\varphi(\omega) = \frac{1}{2\pi}\arg\det S(\omega),
$$

以及 Wigner–Smith 群延迟算符

$$
Q(\omega) = -\mathrm i\,S(\omega)^\dagger\partial_\omega S(\omega).
$$

在 Birman–Kreĭn 公式与 Lifshits–Kreĭn 迹公式的标准假设下，谱移函数的导数等于相对态密度。再结合 Wigner–Smith 延迟与态密度之间的关系，可得到同一式

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

其中 $\kappa(\omega)$ 被解释为每个频率模式的"时间刻度密度"，$\rho_{\mathrm{rel}}(\omega)$ 为相对态密度。

在前期工作中，可将 $\kappa(\omega)$ 通过小因果菱形上的相对熵与能量条件联系到量子 Null 能量条件（QNEC）及其几何版本，从而在边界时间几何上重构广义相对论的若干结构，尤其是 Raychaudhuri 方程、焦点定理及广义熵的单调性。因此，统一时间刻度将散射、谱与时空几何联系在一个频域尺度上。

### 1.3 宇宙的 QCA/矩阵宇宙刻画与有限信息假设

另一方面，将宇宙视作一个可逆 QCA 或"矩阵宇宙"对象，是一类在量子信息与宇宙学交界处被广泛讨论的构想。其基本思路是以离散元胞格点、有限维局域 Hilbert 空间及有限传播半径的更新规则描述时空与物质，再通过连续极限与 coarse graining 重建有效连续时空与场论。

在本工作中假设存在一个有限维参数空间

$$
\mathcal P \subset \mathbb R^N, \quad \Theta=(\Theta^1,\dots,\Theta^N),
$$

其中 $\Theta$ 包含所有独立的宇宙级自由参数：包括局域 Hilbert 维数、局域更新算符的耦合常数与相位、内部对称群与其破缺模式、拓扑扇区标记以及边界条件等。有限维性的物理动机是"有限可区分信息"原则：如果在某一宇宙中可观测的全部物理常数与有效规律有界精度、可分辨阶数有限，则其参数化描述应当可以压缩到有限维变量。

本论文的中心问题随之表述为：

> 在统一时间刻度与 QCA/矩阵宇宙刻画下，六大未解难题对应的约束对 $\Theta$ 有何几何与拓扑上的共同作用？它们定义的解集 $\mathcal S$ 具有怎样的结构？

接下来依照"模型与假设—主结果—证明—应用与工程方案—讨论与结论"的顺序给出系统刻画。

---

## Model & Assumptions

本节定义参数化宇宙对象 $\mathfrak U(\Theta)$、派生物理量 $\mathcal O(\Theta)$ 以及统一约束映射的基本形态，并说明所依赖的主要假设。

### 2.1 统一时间刻度母式

从散射理论出发，设 $H_0$ 与 $H=H_0+V$ 为自伴算符，并满足

1. $(H-H_0)(H_0-\mathrm i)^{-1}$ 为迹类算符；
2. 波算子存在且完备，从而散射算符 $S$ 定义良好；
3. 对能量壳分解 $S(\omega)$ 的依赖足够光滑，使得 $\partial_\omega S(\omega)$ 存在并可定义 Wigner–Smith 算符。

Birman–Kreĭn 公式给出

$$
\det S(\omega) = \exp\bigl(-2\pi\mathrm i\,\xi(\omega)\bigr),
$$

其中 $\xi(\omega)$ 为谱移函数。对 $\omega$ 求导可得

$$
\frac{\varphi'(\omega)}{\pi} = \xi'(\omega), \quad \varphi(\omega) = \frac{1}{2\pi}\arg\det S(\omega).
$$

另一方面，Lifshits–Kreĭn 迹公式给出谱移导数与态密度差 $\rho_{\mathrm{rel}}(\omega)$ 的同一式，进而得到

$$
\xi'(\omega) = \rho_{\mathrm{rel}}(\omega).
$$

最后，利用

$$
Q(\omega) = -\mathrm i\,S(\omega)^\dagger\partial_\omega S(\omega),
$$

可证明相对态密度等于 Wigner–Smith 延迟算符迹的 $(2\pi)^{-1}$ 倍，从而得到

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

该统一刻度母式在本文中作为时间刻度的唯一源：所有几何、熵与信息流量的时间参数化均通过 $\kappa(\omega)$ 及其适当频段积分实现。

### 2.2 参数化宇宙对象 $\mathfrak U(\Theta)$

对每个 $\Theta\in\mathcal P$ 假设存在一类宇宙对象

$$
\mathfrak U(\Theta) = \bigl(
\Lambda(\Theta),
\mathcal H_{\mathrm{cell}}(\Theta),
\mathcal A(\Theta),
\alpha_\Theta,
\omega_0^\Theta,
\kappa(\cdot;\Theta)
\bigr),
$$

其中：

1. $\Lambda(\Theta)$ 为局部有限的格点集合或图；
2. $\mathcal H_{\mathrm{cell}}(\Theta)$ 为单元胞 Hilbert 空间，维数有限；
3. $\mathcal A(\Theta)$ 为由局域算子生成的准局域 $C^\ast$ 代数；
4. $\alpha_\Theta:\mathbb Z\to\mathrm{Aut}(\mathcal A(\Theta))$ 为具有有限传播半径的时间演化自同构；
5. $\omega_0^\Theta$ 为具有有限能量密度的初始态；
6. $\kappa(\omega;\Theta)$ 为通过有限区域输入–输出散射过程定义的统一时间刻度密度。

通过对 $\mathfrak U(\Theta)$ 的连续极限和 coarse graining，重建出有效时空 $(M(\Theta),g(\Theta))$ 与低能有效场论拉氏量 $\mathcal L_{\mathrm{eff}}(\Theta)$。统一时间刻度在该过程中提供了从散射谱到几何时间的桥梁。

### 2.3 派生物理量族 $\mathcal O(\Theta)$

由 $\mathfrak U(\Theta)$ 构造一组派生物理量

$$
\mathcal O(\Theta) = \Bigl(
S_{\mathrm{BH}}^{\mathrm{micro}}(\Theta),
S_{\mathrm{BH}}^{\mathrm{macro}}(\Theta),
\Lambda_{\mathrm{eff}}(\Theta),
\mathbf m_\nu(\Theta),
U_{\mathrm{PMNS}}(\Theta),
\mathrm{ETH\ deviation}(\Theta),
\bar\theta(\Theta),
\omega_{\mathrm{gw}}(k;\Theta),
\ldots
\Bigr),
$$

其中：

* $S_{\mathrm{BH}}^{\mathrm{micro}}(\Theta)$ 为在固定守恒量下的黑洞微观态计数熵；
* $S_{\mathrm{BH}}^{\mathrm{macro}}(\Theta)$ 为由广义熵及 QNEC/焦点条件推导的宏观黑洞熵系数；
* $\Lambda_{\mathrm{eff}}(\Theta)$ 为由零点能与散射谱窗化积分得到的有效宇宙学常数；
* $\mathbf m_\nu(\Theta)$ 和 $U_{\mathrm{PMNS}}(\Theta)$ 由内部 Dirac 算符的谱与混合矩阵给出；
* $\mathrm{ETH\ deviation}(\Theta)$ 度量局域可观测在高能本征态中的 ETH 偏离程度；
* $\bar\theta(\Theta)$ 为有效强 CP 角，取决于 QCD 裸 $\theta_{\mathrm{QCD}}(\Theta)$ 与 Yukawa 行列式相位；
* $\omega_{\mathrm{gw}}(k;\Theta)$ 为在类 FRW 背景上的引力波色散关系。

这些量在连续极限和相应观测窗口中与实际观测物理量相对应。

### 2.4 基本正则性与有限信息假设

为使约束映射 $\mathcal C(\Theta)$ 良好定义并可应用微分几何方法，采用如下假设：

1. **可微性假设**：映射 $\Theta\mapsto\mathfrak U(\Theta)$ 在适当拓扑下是 $C^1$ 的；派生物理量 $\mathcal O(\Theta)$ 为 $\Theta$ 的 $C^1$ 函数。

2. **有限信息假设**：$\mathcal P$ 为有限维流形（可嵌入 $\mathbb R^N$），并可拆分为连续与离散部分的直积

   $$
   \mathcal P \cong \mathcal P_{\mathrm{cont}} \times \mathcal P_{\mathrm{disc}},
   $$

   其中 $\mathcal P_{\mathrm{disc}}$ 为有限或可数集（例如拓扑扇区编号）。

3. **存在物理解假设**：存在至少一个 $\Theta_\star\in\mathcal P$ 使得相应宇宙对象 $\mathfrak U(\Theta_\star)$ reproduces 当前观测宇宙的全部已知量，在理想化极限下可视为 $\mathcal C(\Theta_\star)=0$ 的解。

在这些假设下，统一约束系统可视为参数空间上的 $C^1$ 映射零点问题。

---

## Main Results (Theorems and Alignments)

本节将六个物理难题重写为对 $\Theta$ 的六个标量约束函数，构造统一约束映射 $\mathcal C:\mathcal P\to\mathbb R^6$，并给出共同解空间的几何定理。

### 3.1 六个标量约束函数

**(1) 黑洞熵约束 $\mathcal C_{\mathrm{BH}}$**

在固定守恒量族的黑洞构型上，引入微观熵

$$
S_{\mathrm{BH}}^{\mathrm{micro}}(\Theta) = \ln\mathcal N_{\mathrm{BH}}(\Theta),
$$

以及由广义熵极值与 QNEC 推导的宏观面积律系数

$$
S_{\mathrm{BH}}^{\mathrm{macro}}(\Theta) = \frac{A_{\mathrm{hor}}}{4\ell_{\mathrm{Pl}}^2(\Theta)} + \cdots,
$$

其中 $\ell_{\mathrm{Pl}}(\Theta)$ 由 $\kappa(\omega;\Theta)$ 的高频行为给出。定义宏观系数偏差

$$
F_{\mathrm{BH}}(\Theta) = \lim_{A_{\mathrm{hor}}\to\infty} \left(
\frac{S_{\mathrm{BH}}^{\mathrm{macro}}(\Theta)}{A_{\mathrm{hor}}} - \frac{1}{4\ell_{\mathrm{Pl}}^2(\Theta)}
\right),
$$

以及微观–宏观一致性偏差

$$
\Delta_{\mathrm{micro\text{-}macro}}(\Theta) = \sup_{\mathrm{BH\ family}} \left|
\frac{S_{\mathrm{BH}}^{\mathrm{micro}}(\Theta) - S_{\mathrm{BH}}^{\mathrm{macro}}(\Theta)}{A_{\mathrm{hor}}}
\right|.
$$

定义黑洞熵约束函数

$$
\mathcal C_{\mathrm{BH}}(\Theta) = \left|F_{\mathrm{BH}}(\Theta)\right| + \Delta_{\mathrm{micro\text{-}macro}}(\Theta).
$$

**(2) 宇宙学常数约束 $\mathcal C_\Lambda$**

借助谱窗化形式，将有效宇宙学常数写为

$$
\Lambda_{\mathrm{eff}}(\Theta;\mu) = \Lambda_{\mathrm{bare}}(\Theta) + \int_{\mu_0}^{\mu} \Xi(\omega;\Theta)\,\mathrm d\ln\omega,
$$

其中核 $\Xi(\omega;\Theta)$ 由 $\kappa(\omega;\Theta)$ 与给定重整化方案确定。观测宇宙对应某一宇宙学尺度 $\mu_{\mathrm{cos}}$ 的值 $\Lambda_{\mathrm{obs}}$。为惩罚不自然的精细调参，引入多尺度自然性泛函 $R_\Lambda(\Theta)$，测度在宽频带上 $\Lambda_{\mathrm{eff}}(\Theta;\mu)$ 的变化是否需要高度精细抵消。

宇宙学常数约束函数定义为

$$
\mathcal C_\Lambda(\Theta) = \left|
\Lambda_{\mathrm{eff}}(\Theta;\mu_{\mathrm{cos}}) - \Lambda_{\mathrm{obs}}
\right| + R_\Lambda(\Theta).
$$

**(3) 中微子质量与混合约束 $\mathcal C_\nu$**

设由内部 Dirac 块得到的轻中微子质量向量为

$$
\mathbf m_\nu(\Theta) = \bigl(m_{\nu,1}(\Theta),m_{\nu,2}(\Theta),m_{\nu,3}(\Theta)\bigr),
$$

PMNS 矩阵为 $U_{\mathrm{PMNS}}(\Theta)\in U(3)$。实验给出质量差平方和混合角的允许区域，记为中心值向量 $\mathbf m_\nu^{\mathrm{obs}}$ 与 $U_{\mathrm{PMNS}}^{\mathrm{obs}}$ 及其误差域。选取合适加权范数，定义

$$
\mathcal C_\nu(\Theta) = \bigl|
\mathbf m_\nu(\Theta)-\mathbf m_\nu^{\mathrm{obs}}
\bigr|_w + \bigl|
U_{\mathrm{PMNS}}(\Theta)-U_{\mathrm{PMNS}}^{\mathrm{obs}}
\bigr|_w.
$$

**(4) ETH 约束 $\mathcal C_{\mathrm{ETH}}$**

在有限区域 $\Lambda_L$ 上构造多体 Hamilton 量，取一段能窗与代表性局域算符族 $\mathcal O_{\mathrm{loc}}$，定义有限体积 ETH 偏离度

$$
\mathrm{ETH\ deviation}_L(\Theta) = \sup_{\hat O\in\mathcal O_{\mathrm{loc}}} \sup_{E\in[E_1,E_2]} \left(
\frac{\bigl|\langle E|\hat O|E\rangle - f_O(E)\bigr|}{\mathrm e^{-S(E)/2}} +
\frac{\max_{\alpha\neq\beta}\bigl|\langle E_\alpha|\hat O|E_\beta\rangle\bigr|}{\mathrm e^{-S(\bar E)/2}}
\right).
$$

取上极限

$$
\mathrm{ETH\ deviation}(\Theta) = \limsup_{L\to\infty} \mathrm{ETH\ deviation}_L(\Theta),
$$

定义

$$
\mathcal C_{\mathrm{ETH}}(\Theta) = \mathrm{ETH\ deviation}(\Theta).
$$

**(5) 强 CP 约束 $\mathcal C_{\mathrm{CP}}$**

强相互作用的物理 CP 角为

$$
\bar\theta(\Theta) = \theta_{\mathrm{QCD}}(\Theta) - \arg\det\bigl(Y_u(\Theta)Y_d(\Theta)\bigr),
$$

其中 $\theta_{\mathrm{QCD}}(\Theta)$ 由规范场拓扑扇区和基本相位给出，$Y_u,Y_d$ 为 Yukawa 矩阵。为排除通过连续微调实现的小 $\bar\theta$ 解，引入拓扑自然性泛函 $R_{\mathrm{top}}(\Theta)$，测度 $\bar\theta \approx 0$ 是否由拓扑与离散对称性自动实现。

强 CP 约束函数定义为

$$
\mathcal C_{\mathrm{CP}}(\Theta) = \bigl|\bar\theta(\Theta)\bigr| + R_{\mathrm{top}}(\Theta).
$$

**(6) 引力波色散约束 $\mathcal C_{\mathrm{GW}}$**

由 QCA 连续极限得到的引力波色散关系可写为

$$
\omega(k;\Theta) = c_{\mathrm{gw}}(\Theta)\,k \left[
1 + \alpha_2(\Theta)\bigl(k\ell(\Theta)\bigr)^2 + \alpha_4(\Theta)\bigl(k\ell(\Theta)\bigr)^4 +\cdots
\right].
$$

定义速度偏差

$$
\Delta c(\Theta) = \left|
\frac{c_{\mathrm{gw}}(\Theta)}{c_{\mathrm{em}}(\Theta)}-1
\right|,
$$

以及观测频带 $[k_{\min},k_{\max}]$ 内的色散偏差

$$
\Delta_{\mathrm{disp}}(\Theta) = \sup_{k\in[k_{\min},k_{\max}]} \left|
\frac{\omega(k;\Theta)-c\,k}{c\,k}
\right|.
$$

引力波色散约束函数定义为

$$
\mathcal C_{\mathrm{GW}}(\Theta) = \Delta c(\Theta) + \Delta_{\mathrm{disp}}(\Theta).
$$

### 3.2 统一约束映射与解集

统一约束映射

$$
\mathcal C:\mathcal P\to\mathbb R^6
$$

定义为

$$
\mathcal C(\Theta) = \bigl(
\mathcal C_{\mathrm{BH}}(\Theta),
\mathcal C_\Lambda(\Theta),
\mathcal C_\nu(\Theta),
\mathcal C_{\mathrm{ETH}}(\Theta),
\mathcal C_{\mathrm{CP}}(\Theta),
\mathcal C_{\mathrm{GW}}(\Theta)
\bigr).
$$

观测上"与现实宇宙等价"的参数向量应满足 $\mathcal C(\Theta)$ 在实验误差和理论容忍度内接近零。理想化地，将其视为零点条件

$$
\mathcal C(\Theta)=0.
$$

定义解集

$$
\mathcal S := \{\Theta\in\mathcal P:\mathcal C(\Theta)=0\}.
$$

本论文的主要数学结果描述 $\mathcal S$ 在 $\mathcal P$ 中的局部子流形结构以及拓扑扇区导致的离散化。

### 3.3 共同解空间定理（主结果）

记 Jacobian 矩阵

$$
D\mathcal C(\Theta) = \left(
\frac{\partial\mathcal C_i}{\partial\Theta^j}(\Theta)
\right)_{1\le i\le 6,\ 1\le j\le N}.
$$

**假设 3.1（正则性与一阶独立性）**

存在 $\Theta_\star\in\mathcal P$ 满足 $\mathcal C(\Theta_\star)=0$，且

$$
\operatorname{rank}D\mathcal C(\Theta_\star)=6.
$$

该假设物理上意味着六条约束在一阶近似下相互独立。

**定理 3.2（共同解空间的局部子流形结构）**

在假设 2.4 与 3.1 下，存在 $\Theta_\star$ 的邻域 $U\subset\mathcal P$，使得

$$
\mathcal S\cap U = \{\Theta\in U:\mathcal C(\Theta)=0\}
$$

是维数为 $N-6$ 的 $C^1$ 嵌入子流形。

特别地，当 $N=6$ 时，$\mathcal S\cap U$ 为孤立点集；若进一步假设 $\mathcal S$ 在全局上闭且 $\mathcal P$ 具有适当紧性，则 $\mathcal S$ 为有限点集。

**命题 3.3（拓扑扇区离散化）**

若 $\mathcal P\cong\mathcal P_{\mathrm{cont}}\times\mathcal P_{\mathrm{disc}}$，其中 $\mathcal P_{\mathrm{disc}}$ 为离散集，且强 CP 约束 $\mathcal C_{\mathrm{CP}}(\Theta)=0$ 在 $\mathcal P_{\mathrm{disc}}$ 上只允许有限个值，则解集可写为有限并

$$
\mathcal S = \bigcup_{t\in\mathcal P_{\mathrm{disc}}^{\mathrm{phys}}} \left(
\{t\} \times \mathcal S_t
\right),
$$

其中 $\mathcal P_{\mathrm{disc}}^{\mathrm{phys}} \subset\mathcal P_{\mathrm{disc}}$ 为允许的拓扑扇区集合，而每个分支

$$
\mathcal S_t = \{\Theta_{\mathrm{cont}}\in\mathcal P_{\mathrm{cont}}:
\mathcal C_t(\Theta_{\mathrm{cont}})=0\}
$$

在局部上为维数 $N_{\mathrm{cont}}-6$ 的子流形。

上述定理与命题的证明基于隐函数定理与离散簇分解，详见附录 C。

---

## Proofs

本节给出上述主定理的证明纲要，并在附录中给出关键技术细节。证明分为两部分：其一是统一时间刻度母式的散射–谱–延迟同一性，其二是共同解空间的微分几何结构。

### 4.1 统一时间刻度母式的散射–谱–延迟同一性

统一时间刻度同一式

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{tr}Q(\omega)
$$

由三步构造而来：

1. **Birman–Kreĭn 公式**

   在 $(H-H_0)(H_0-\mathrm i)^{-1}$ 迹类假设下，Birman 与 Kreĭn 证明了散射行列式与谱移函数之间的关系

   $$
   \det S(\omega) = \exp\bigl(-2\pi\mathrm i\,\xi(\omega)\bigr),
   $$

   从而

   $$
   \frac{\varphi'(\omega)}{\pi} = \xi'(\omega),
   $$

   其中 $\varphi(\omega) = (2\pi)^{-1}\arg\det S(\omega)$。

2. **Lifshits–Kreĭn 迹公式与相对态密度**

   Lifshits–Kreĭn 迹公式在同样的迹类条件下，给出谱移函数与算符函数之差的迹之间的积分关系，对特征函数作适当选择可导出

   $$
   \xi'(\omega) = \rho_{\mathrm{rel}}(\omega) = \rho(\omega)-\rho_0(\omega),
   $$

   即谱移导数等于相对态密度。

3. **Wigner–Smith 延迟算符与态密度**

   Wigner 与 Smith 在单通道情况下引入群延迟概念，后被推广到多通道算符

   $$
   Q(\omega) = -\mathrm i\,S(\omega)^\dagger\partial_\omega S(\omega).
   $$

   在多通道散射系统的态密度理论中，可以证明相对态密度满足

   $$
   \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{tr}Q(\omega),
   $$

   即 Wigner–Smith 延迟矩阵迹的 $(2\pi)^{-1}$ 倍。

综上，三项依次相等，得到统一时间刻度母式。附录 A 对每一步的算子理论条件、迹类假设与收敛性问题作出更详细说明。

### 4.2 共同解空间定理的证明纲要

定理 3.2 的证明（附录 C）遵循标准隐函数定理的模板：

1. 假设 3.1 给出 $\Theta_\star$ 处 Jacobian $D\mathcal C(\Theta_\star)$ 的秩为 6。可选择局部坐标，将 $\Theta$ 写为 $(x,y)$，其中 $x\in\mathbb R^6$、$y\in\mathbb R^{N-6}$，并使得 $\partial\mathcal C/\partial x$ 在 $(x_\star,y_\star)$ 处可逆。

2. 应用隐函数定理：存在 $y_\star$ 的邻域 $V$ 与唯一光滑函数 $g:V\to\mathbb R^6$，使得

   $$
   \mathcal C(x,y)=0 \iff x=g(y), \quad y\in V.
   $$

3. 因此，解集在邻域 $U$ 内可写为

   $$
   \mathcal S\cap U = \{(x,y)\in U:x=g(y),\,y\in V\},
   $$

   这是 $\mathbb R^{N-6}$ 向 $\mathcal P$ 的 $C^1$ 嵌入像，故为维数 $N-6$ 的嵌入子流形。

当 $N=6$ 时，$y$ 不存在，$\mathcal S\cap U$ 由孤立点组成。对含离散拓扑扇区的情形，分别在每个固定 $t\in\mathcal P_{\mathrm{disc}}$ 的连续片上应用同样论证即可得到命题 3.3。

完整证明包括坐标图构造、嵌入性质与解集闭性条件，见附录 C。

---

## Model Apply

本节从结构上分析统一约束系统的交叉锁定，展示其在不同物理领域中的应用模式与潜在预言。

### 5.1 黑洞熵与宇宙学常数的谱–几何锁定

黑洞熵约束 $\mathcal C_{\mathrm{BH}}=0$ 与宇宙学常数约束 $\mathcal C_\Lambda=0$ 都通过不同频段的 $\kappa(\omega;\Theta)$ 约束宇宙的谱结构：

* 高频段 $\omega\gg \omega_{\mathrm{Pl}}$ 的 $\kappa(\omega;\Theta)$ 决定小因果菱形的能量涨落与局域 Planck 长度 $\ell_{\mathrm{Pl}}(\Theta)$，进而控制黑洞熵系数；
* 低频段 $\omega\ll \omega_{\mathrm{cos}}$ 的 $\kappa(\omega;\Theta)$ 通过谱窗化核 $\Xi(\omega;\Theta)$ 积分进入 $\Lambda_{\mathrm{eff}}(\Theta;\mu_{\mathrm{cos}})$。

统一约束系统要求这两部分在同一 $\Theta$ 上同时满足观测要求，意味着谱密度的高频尾与低频尾不能独立调节。例如：

* 若未来观测发现黑洞熵在大质量极限偏离面积律，则可反推 $\kappa(\omega;\Theta)$ 高频结构的修正，从而改变对 $\Lambda_{\mathrm{eff}}$ 的谱窗化预测；
* 反之，若宇宙学观测进一步压缩 $\Lambda_{\mathrm{eff}}$ 的容许区间，可对许可的高频谱密度施加约束，排除某些黑洞微观模型。

### 5.2 中微子–强 CP 的内部谱–拓扑耦合

内部 Dirac 块 $D_\Theta$ 同时决定轻中微子质量与夸克 Yukawa 矩阵 $Y_u(\Theta),Y_d(\Theta)$。许多统一构想中，这些都来自单一内部几何或代数对象的谱数据。

中微子约束 $\mathcal C_\nu=0$ 将质量差平方与混合角压到实验允许区间内；强 CP 约束 $\mathcal C_{\mathrm{CP}}=0$ 则要求

$$
\bar\theta(\Theta) = \theta_{\mathrm{QCD}}(\Theta) - \arg\det\bigl(Y_u(\Theta)Y_d(\Theta)\bigr) \approx 0
$$

且由拓扑或离散对称性自动实现。两者共同作用于 $D_\Theta$ 的谱与行列式相位，使得：

* 给定某类拓扑扇区与内部几何构型，可推导出 PMNS 参数与 Yukawa 相位之间的一组代数关系；
* 若未来中微子实验强烈限制 PMNS 中的 CP 相位，则可排除相当一部分强 CP 解型。

因此，在统一约束系统中，中微子物理与强相互作用的 CP 结构不再独立，而通过 $\Theta$ 的内部坐标与离散扇区耦合。

### 5.3 ETH–黑洞–引力波的多体–引力耦合

ETH 约束 $\mathcal C_{\mathrm{ETH}}=0$ 要求 QCA 宇宙在多体高能谱上表现出类似随机矩阵的混沌行为与强热化；黑洞熵与引力波色散约束则要求几何扇区在宏观上分别实现面积律与近乎无色散的传播。

统一约束系统强迫同一套局域更新规则 $\alpha_\Theta$ 同时满足：

* 在视界附近，产生足够强的纠缠与混合，以支持黑洞信息的有效湮灭与再辐射，并在大尺度上恢复广义熵与广义第二定律；
* 在类 FRW 背景上，引力波模式的传播保持近似线性、不显著色散，以匹配当前引力波观测。

这导致一个"有限元胞宇宙"的工程约束：给定元胞 Hilbert 维数与局域相互作用模数，能同时通过 ETH、黑洞熵与引力波色散检验的更新规则落在参数空间的极窄子域内。

### 5.4 参数反演与联合拟合框架

统一约束系统为反演 $\Theta$ 提供了清晰的数学目标：利用观测构造数值近似的 $\hat{\mathcal C}(\Theta)$，在给定先验分布与约束下求解 $\hat{\mathcal C}(\Theta)\approx 0$ 的解集或后验分布。概念上可采用如下步骤：

1. 利用引力波、宇宙学与 FRB 相位频谱数据重建 $\kappa(\omega;\Theta)$ 在特定频带上的形状；
2. 利用黑洞并合、阴影与准正常模数据拟合 $S_{\mathrm{BH}}^{\mathrm{macro}}(\Theta)$ 与 $\ell_{\mathrm{Pl}}(\Theta)$；
3. 利用中微子振荡与 $\beta$ 衰变谱数据拟合 $\mathbf m_\nu(\Theta)$ 与 $U_{\mathrm{PMNS}}(\Theta)$；
4. 利用多体实验与数值模拟约束 ETH 偏离函数；
5. 利用中子电偶极矩与强 CP 模型约束 $\bar\theta(\Theta)$ 与拓扑扇区；
6. 利用多信使引力波事件约束 $c_{\mathrm{gw}}(\Theta)$ 与色散修正系数。

在数值层面，可将 $\Theta$ 视为高维参数，使用全局优化、贝叶斯推断或信息几何方法，探索 $\hat{\mathcal S}=\{\Theta:\hat{\mathcal C}(\Theta)\approx 0\}$ 的结构。这一框架为未来"数据驱动的宇宙 QCA/矩阵宇宙模型"提供了系统工程路径。

---

## Engineering Proposals

本节从工程和数值模拟角度提出若干具体方案，用于实现统一约束系统的检验与应用。

### 6.1 QCA/矩阵宇宙仿真架构

构建面向统一约束系统的 QCA 仿真平台，可分为三层：

1. **离散动力学层**

   在有限格点 $\Lambda_L$ 上实现参数化局域更新算符族 $U_{\mathrm{loc}}(\Theta)$，允许运行在经典高性能集群或量子模拟平台上。通过控制 $\Theta$ 中的耦合常数和相位，探索满足 ETH 与黑洞熵约束的区域。

2. **散射–时间刻度层**

   在离散模型上构造有限区域的输入–输出散射矩阵 $S_{\mathrm{reg}}(\omega;\Theta)$，数值计算 $Q(\omega;\Theta)$ 与 $\kappa(\omega;\Theta)$，并与理论预测及观测数据进行匹配。

3. **几何–观测层**

   在适当极限下，从传播锥与相关长度重建有效度规 $g(\Theta)$ 与引力波色散关系，进而计算黑洞视界性质、宇宙学背景解与对应的观测量（CMB、BAO、引力波时延等）。

上述三层通过统一时间刻度 $\kappa(\omega;\Theta)$ 与参数向量 $\Theta$ 耦合，方便将约束函数 $\mathcal C_i(\Theta)$ 直接实现为数值函数。

### 6.2 多源数据联合约束的数值管线

为在实数据基础上反演或约束 $\Theta$，可设计如下多源数据管线：

1. 将不同观测数据集（宇宙学、引力波、中微子、强 CP 与多体量子实验）预处理为对应的"约束算子"，例如估计 $\Lambda_{\mathrm{obs}}$、PMNS 参数、速度与色散界等；
2. 建立从 $\Theta$ 到可观测量的预测映射 $\mathcal O(\Theta)$，可通过解析近似、有效场论估计或 QCA 仿真得到；
3. 将每个物理问题的偏差构成单独的子损失函数，对应 $\mathcal C_i(\Theta)$ 的数值实现；
4. 定义总损失 $|\mathcal C(\Theta)|$ 并进行全局优化或贝叶斯采样，探索解集 $\hat{\mathcal S}$ 的形状和维数；
5. 分析不同假设下 $\mathcal S$ 的拓扑变化，以识别对大尺度物理影响最大的参数子集。

这一工程框架可视为"宇宙参数空间的逆问题"，与传统宇宙学参数拟合类似，但目标参数 $\Theta$ 包括内部 Dirac 光谱、拓扑数据与 QCA 动力学细节。

### 6.3 可检预言的观测方案

统一约束系统提出了若干跨领域的可检预言类别，其对应的观测方案包括：

1. **引力波–黑洞联测**

   系统分析黑洞并合事件中的视界面积变化与引力波色散特征，将 Hawking 面积定律的精确性与色散修正上界联系起来。

2. **中微子–强 CP 关联**

   通过精确测量 PMNS 中 CP 破缺相位与质量层级，反向约束强 CP 解型的拓扑模式与可行参数空间。

3. **ETH–黑洞信息模拟**

   利用可控量子多体系统（如冷原子或超导量子比特阵列）实现模拟 QCA 规则，检验 ETH 偏离与信息回收时间是否与黑洞信息悖论方案的要求兼容。

这些方案为将本框架提升为可部分验证的理论提供了具体路径。

---

## Discussion (risks, boundaries, past work)

### 7.1 与既有统一构想的比较

本工作将六大难题视为统一约束方程组的六个分量，与以下思路形成对照：

* 与"人择原理/景观"方案相比，本框架不依赖庞大多重宇宙集合，而是将物理宇宙的选择归结为有限维参数空间上的零点问题；
* 与单一问题导向的构想（如仅针对宇宙学常数或仅针对强 CP 的解）相比，本框架在结构上要求各解型相互兼容，因而在模型构造时自动排除大量"孤立解"。

从技术上，本框架与散射理论中的谱移函数和迹公式、量子信息视角下的 QNEC、以及 ETH 与随机矩阵理论的成果紧密相关。

### 7.2 假设边界与潜在风险

本框架依赖若干关键假设：

1. 有限维参数空间 $\mathcal P$ 的存在，这在严格数学上需要从更基础的可分辨性或计算复杂性原理中推导；
2. 统一时间刻度 $\kappa(\omega;\Theta)$ 能在适当意义上由 QCA 或矩阵宇宙对象构造并控制所有相关尺度；
3. 派生物理量对 $\Theta$ 的 $C^1$ 依赖及 Jacobian 满秩假设在物理解附近成立。

若其中任一假设被否定，则共同解空间结构可能发生根本性变化。例如，若存在无限多独立的高能自由度，则 $N$ 可能无上界，定理 3.2 的物理意义弱化；若 $\mathcal C_i$ 之间在高阶上存在隐含关系，则实质上独立约束数可能小于 6。

### 7.3 未来工作方向

可能的拓展包括：

1. 在具体 QCA 模型上构造可计算的 $\kappa(\omega;\Theta)$ 与约束函数，给出数值级别的 $\mathcal S$ 形状示例；
2. 将参数空间 $\mathcal P$ 的几何结构（如自然度量与曲率）与信息几何框架结合，研究"物理解附近"的曲率是否与物理可调性相关；
3. 将统一约束系统与量子引力候选理论（如弦论、圈量子引力或非交换几何）中的参数化方案对接，比较不同理论对 $\Theta$ 的参数化与约束实现方式。

---

## Conclusion

本文在统一时间刻度、边界时间几何与 QCA/矩阵宇宙框架下，引入有限维宇宙参数向量 $\Theta$，并将黑洞熵、宇宙学常数、中微子质量与 PMNS 混合、ETH、强 CP 问题以及引力波色散六个看似独立的难题，统一重写为对 $\Theta$ 的六条标量约束函数 $\mathcal C_i(\Theta)=0$。由此构造的约束映射

$$
\mathcal C(\Theta) = \bigl(\mathcal C_{\mathrm{BH}},\mathcal C_\Lambda,\mathcal C_\nu,\mathcal C_{\mathrm{ETH}},\mathcal C_{\mathrm{CP}},\mathcal C_{\mathrm{GW}}\bigr)(\Theta)
$$

定义了参数空间上的解集 $\mathcal S=\{\Theta:\mathcal C(\Theta)=0\}$。

在自然的可微性与一阶独立性假设下，利用隐函数定理证明 $\mathcal S$ 在物理解附近是维数 $N-6$ 的嵌入子流形；当 $N=6$ 时，解集局部上离散。结合由强 CP 问题与拓扑扇区引入的离散化，得到解集整体上是有限或可数个低维分支的并，体现出"有限信息宇宙"的强约束性。

在物理上，统一约束系统将黑洞热力学、宇宙学常数、中微子与强相互作用 CP 结构、量子混沌与 ETH 以及引力波传播属性置于同一参数空间框架之内，实现了跨尺度、跨现象的结构性耦合。这一框架为构造具体统一模型提供了明确目标：寻找满足 $\mathcal C(\Theta)=0$ 的 QCA/矩阵宇宙实现，并通过未来多源观测逐步约束或反演 $\Theta$ 的取值。

---

## Acknowledgements, Code Availability

本工作假定存在一类参数化的 QCA/矩阵宇宙模型族及其散射–几何–信息结构，目前尚未给出特定模型的公开数值代码。统一约束系统的数值实现与反演算法可在未来研究中以开源方式发布，目前阶段仅给出理论与工程框架。

---

## References

1. S. Weinberg, "The Cosmological Constant Problem," *Rev. Mod. Phys.* **61**, 1 (1989).

2. A. Pushnitski, "The spectral shift function and the invariance principle," *J. Funct. Anal.* **183**, 269–320 (2001).

3. A. Grabsch, et al., "Wigner-Smith time-delay matrix in chaotic cavities," *Phys. Rev. B* **98**, 045409 (2018).

4. Z. Fu, J. Koeller, D. Marolf, "The quantum null energy condition in curved space," *Phys. Rev. Lett.* **120**, 071601 (2018).

5. J. M. Deutsch, "Eigenstate thermalization hypothesis," *Rep. Prog. Phys.* **81**, 082001 (2018).

6. L. D'Alessio, Y. Kafri, A. Polkovnikov, M. Rigol, "From quantum chaos and eigenstate thermalization to statistical mechanics," *Adv. Phys.* **65**, 239–362 (2016).

7. R. D. Peccei, H. R. Quinn, "CP Conservation in the Presence of Pseudoparticles," *Phys. Rev. Lett.* **38**, 1440 (1977).

8. C. Giganti, et al., "Neutrino oscillations: The rise of the PMNS paradigm," *Prog. Part. Nucl. Phys.* **98**, 1–54 (2018).

9. "GW170817," multi-messenger neutron star merger event summary and constraints on the speed of gravity and dark energy models.

10. "Black hole thermodynamics" and "Bekenstein–Hawking entropy," overviews of black hole entropy–area relation and its thermodynamic interpretation.

11. Recent reviews on quantum null energy condition (QNEC) and its proofs for various field theories.

12. Representative works on axion and non-axion solutions to the strong CP problem and corresponding EDM constraints.

13. Representative reviews on neutrino masses and mixing, including PMNS matrix parametrization and open questions.

14. M. Davy, et al., and related works on the use of Wigner–Smith time-delay in complex scattering environments, illustrating the connection between delay operators and path lengths/density of states.

15. Recent observational tests of black hole thermodynamic laws and horizon area theorems using gravitational wave detections.

其余关于散射理论、谱移函数、QCA 连续极限及 ETH 数值研究的文献可在上述综述中找到系统综述与延伸参考。

---

## Appendix A: Scattering, Spectral Shift and Unified Time Scale

本附录给出统一时间刻度同一式的算子理论背景与技术细节，说明在何种条件下可以严格建立

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

### A.1 Birman–Kreĭn 公式

设 $H_0$ 与 $H=H_0+V$ 为自伴算符，满足

1. $(H-H_0)(H_0-\mathrm i)^{-1}$ 为迹类算符；
2. 两者的绝对连续谱在考虑的能区内重合；
3. 波算子 $W_\pm(H,H_0)$ 存在且完备。

定义散射算符

$$
S = W_+^\dagger W_-,
$$

以及能量壳散射矩阵 $S(\omega)$。谱移函数 $\xi(\omega)$ 通过相对迹定义：

对适当类的测试函数 $f$ 有

$$
\operatorname{tr}\bigl(f(H)-f(H_0)\bigr) = \int_{-\infty}^{+\infty} f'(\omega)\,\xi(\omega)\,\mathrm d\omega.
$$

Birman–Kreĭn 公式指出

$$
\det S(\omega) = \exp\bigl(-2\pi\mathrm i\,\xi(\omega)\bigr),
$$

其中行列式以适当正则化方式定义。对 $\omega$ 求导得

$$
\frac{\varphi'(\omega)}{\pi} = \xi'(\omega), \quad \varphi(\omega) = \frac{1}{2\pi}\arg\det S(\omega).
$$

### A.2 Lifshits–Kreĭn 迹公式与相对态密度

对 $f$ 属于一类足够光滑且衰减的函数，可写出

$$
\operatorname{tr}\bigl(f(H)-f(H_0)\bigr) = \int_{-\infty}^{+\infty} f'(\omega)\,\xi(\omega)\,\mathrm d\omega.
$$

若将 $f$ 取为能量窗的平滑近似，则

$$
\xi'(\omega) = \rho_{\mathrm{rel}}(\omega) = \rho(\omega)-\rho_0(\omega),
$$

其中 $\rho(\omega)$ 与 $\rho_0(\omega)$ 分别为 $H$ 与 $H_0$ 的态密度。由此得到

$$
\frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega).
$$

### A.3 Wigner–Smith 延迟算符与态密度

Wigner 与 Smith 在单通道散射中将相位导数解释为时间延迟，多通道情形下定义

$$
Q(\omega) = -\mathrm i\,S(\omega)^\dagger\partial_\omega S(\omega).
$$

在多通道散射的态密度理论中，可证明相对态密度

$$
\rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

证明通常依赖于将两个系统的 Green 函数差表示为散射矩阵的能量导数，结合散射矩阵与 T 矩阵之间的关系，并使用解析延拓与迹类界控制积分。

综合 A.1–A.3 即得统一时间刻度同一式。

---

## Appendix B: Construction of Constraint Functions from $\mathfrak U(\Theta)$

本附录说明如何从参数化宇宙对象 $\mathfrak U(\Theta)$ 构造正文中定义的各个约束函数，并检查它们对 $\Theta$ 的可微性。

### B.1 黑洞熵约束 $\mathcal C_{\mathrm{BH}}$ 的构造

在 QCA 宇宙中，将黑洞视作满足固定守恒量的局域缺陷或高度纠缠区域。选择一族宏观黑洞构型，使视界可以在格点上近似为离散面元集合，其数目记为 $N_{\mathrm{cell}}(\Theta)$，局域 Hilbert 维数为 $d_{\mathrm{eff}}(\Theta)$。则微观态数

$$
\mathcal N_{\mathrm{BH}}(\Theta) \simeq d_{\mathrm{eff}}(\Theta)^{N_{\mathrm{cell}}(\Theta)},
$$

微观熵

$$
S_{\mathrm{BH}}^{\mathrm{micro}}(\Theta) = N_{\mathrm{cell}}(\Theta)\ln d_{\mathrm{eff}}(\Theta) + o\bigl(N_{\mathrm{cell}}(\Theta)\bigr),
$$

而 $N_{\mathrm{cell}}(\Theta)\propto A_{\mathrm{hor}}/\ell_{\mathrm{Pl}}^2(\Theta)$。宏观一侧，通过 QNEC 与广义熵极值条件，在小因果菱形极限中将统一时间刻度与能动张量的 null 投影联系起来，进而得到有效 $G_{\mathrm{eff}}(\Theta)$ 与 $\ell_{\mathrm{Pl}}(\Theta)$，在大视界极限上恢复面积律。比较两者，即得到 $F_{\mathrm{BH}}(\Theta)$ 与 $\Delta_{\mathrm{micro\text{-}macro}}(\Theta)$ 的表达，从而构造 $\mathcal C_{\mathrm{BH}}(\Theta)$。

### B.2 宇宙学常数约束 $\mathcal C_\Lambda$ 的谱窗化形式

在半经典重整化框架中，真空能密度形式上为所有模式零点能的积分。采用相对谱的观点，可将对背景的差分表达为 $\kappa(\omega;\Theta)$ 的加权积分。选择一个满足重整化群方程的窗函数 $W(\omega/\mu)$，定义

$$
\Xi(\omega;\Theta) = W(\omega/\mu)\,\kappa(\omega;\Theta),
$$

从而

$$
\Lambda_{\mathrm{eff}}(\Theta;\mu) = \Lambda_{\mathrm{bare}}(\Theta) + \int\Xi(\omega;\Theta)\,\mathrm d\ln\omega.
$$

不同的重整化方案对应不同的 $W$，但 $\mathcal C_\Lambda(\Theta)$ 的结构形式不依赖于具体选择。$\Theta \mapsto \Lambda_{\mathrm{eff}}(\Theta;\mu)$ 的可微性来自于 $\kappa(\omega;\Theta)$ 对 $\Theta$ 的光滑依赖及积分收敛性。

### B.3 中微子与强 CP 约束的耦合结构

将内部 Dirac 块 $D_\Theta$ 视作一个作用于内部 Hilbert 空间的自伴算符，其谱分解提供轻子和夸克质量矩阵以及混合矩阵。对给定 $\Theta$：

1. 从 $D_\Theta$ 中读出轻中微子质量矩阵并对角化，得到 $\mathbf m_\nu(\Theta)$ 与 $U_{\mathrm{PMNS}}(\Theta)$；
2. 从同一内部结构中抽取夸克 Yukawa 矩阵 $Y_u(\Theta),Y_d(\Theta)$，计算 $\arg\det(Y_uY_d)$；
3. 由规范拓扑扇区与基本相位定义 $\theta_{\mathrm{QCD}}(\Theta)$，从而构造 $\bar\theta(\Theta)$。

在许多统一理论中，$D_\Theta$ 的谱与行列式相位通过 index 定理或 $K$-理论与拓扑数据相关，从而在结构上耦合 $\mathcal C_\nu$ 与 $\mathcal C_{\mathrm{CP}}$。在适当的谱稳定性假设下，$\mathbf m_\nu(\Theta),U_{\mathrm{PMNS}}(\Theta),\bar\theta(\Theta)$ 对 $\Theta$ 的依赖是 $C^1$ 的，因而 $\mathcal C_\nu,\mathcal C_{\mathrm{CP}}$ 为 $C^1$ 映射。

### B.4 ETH 与引力波色散约束的可微性

对 ETH 约束，有限体积下的 $\mathrm{ETH\ deviation}_L(\Theta)$ 可由有限维矩阵本征分析得到，对 $\Theta$ 的依赖光滑。若在 $L\to\infty$ 极限下收敛或上极限存在，则可定义 $\mathrm{ETH\ deviation}(\Theta)$ 并保持上半连续，如进一步假设收敛光滑，则 $\mathcal C_{\mathrm{ETH}}(\Theta)$ 为 $C^1$ 函数。

对引力波色散，线性化 QCA 动力学得到差分方程，Fourier 分析得到色散关系 $\omega(k;\Theta)$，其系数 $c_{\mathrm{gw}}(\Theta),\alpha_2(\Theta),\dots$ 为 $\Theta$ 的光滑函数。因此 $\Delta c(\Theta),\Delta_{\mathrm{disp}}(\Theta)$ 及 $\mathcal C_{\mathrm{GW}}(\Theta)$ 也是 $C^1$ 的。

---

## Appendix C: Proof of the Joint Solution Space Theorem

本附录给出定理 3.2 与命题 3.3 的完整证明。

### C.1 纯连续参数情形的证明

设 $\mathcal P\subset\mathbb R^N$ 为开集，$\mathcal C:\mathcal P\to\mathbb R^6$ 为 $C^1$ 映射。假设存在 $\Theta_\star\in\mathcal P$ 满足 $\mathcal C(\Theta_\star)=0$ 且

$$
\operatorname{rank}D\mathcal C(\Theta_\star)=6.
$$

**步骤 1：局部坐标分解**

由于 Jacobian 在 $\Theta_\star$ 处秩为 6，存在指标集合 $J\subset\{1,\dots,N\}$ 且 $|J|=6$，使得 $D\mathcal C(\Theta_\star)$ 中对应列构成 $6\times 6$ 可逆矩阵。重排坐标，使得 $J=\{1,\dots,6\}$。将 $\Theta$ 写为

$$
\Theta = (x,y), \quad x\in\mathbb R^6,\ y\in\mathbb R^{N-6},
$$

并在 $\Theta_\star=(x_\star,y_\star)$ 的邻域内视 $\mathcal C$ 为 $(x,y)$ 的函数。

此时，偏导矩阵

$$
\frac{\partial\mathcal C}{\partial x}(x_\star,y_\star)
$$

为可逆矩阵。

**步骤 2：应用隐函数定理**

隐函数定理表明：存在 $y_\star$ 的邻域 $V\subset\mathbb R^{N-6}$ 与唯一 $C^1$ 函数 $g:V\to\mathbb R^6$，使得在某个邻域 $U \subset \mathcal P$ 内有

$$
\mathcal C(x,y)=0 \iff x=g(y), \quad y\in V.
$$

**步骤 3：解集的子流形结构**

定义映射

$$
\Phi:V\to U,\quad \Phi(y)=(g(y),y).
$$

则

$$
\mathcal S\cap U = \{\Theta\in U:\mathcal C(\Theta)=0\} = \Phi(V).
$$

由于 $g$ 为 $C^1$ 函数，$\Phi$ 为 $C^1$ 嵌入，其像为维数 $N-6$ 的 $C^1$ 子流形。于是定理 3.2 在纯连续参数情形下成立。

当 $N=6$ 时，$y$ 为空向量，$V$ 退化为一点，$\mathcal S\cap U$ 仅包含 $\Theta_\star$ 一点，局部上为离散集。若进一步假设 $\mathcal S$ 在 $\mathcal P$ 内闭合且 $\mathcal P$ 紧，则 $\mathcal S$ 为有限点集。

### C.2 含离散拓扑扇区的情形

设 $\mathcal P\cong\mathcal P_{\mathrm{cont}}\times\mathcal P_{\mathrm{disc}}$，其中 $\mathcal P_{\mathrm{disc}}$ 为离散集。对每个固定 $t\in\mathcal P_{\mathrm{disc}}$，定义限制映射

$$
\mathcal C_t:\mathcal P_{\mathrm{cont}}\to\mathbb R^6, \qquad \mathcal C_t(\Theta_{\mathrm{cont}}) := \mathcal C(\Theta_{\mathrm{cont}},t).
$$

若对某个 $t$ 存在 $\Theta_{\mathrm{cont},\star}$ 满足 $\mathcal C_t(\Theta_{\mathrm{cont},\star})=0$ 且 $D\mathcal C_t(\Theta_{\mathrm{cont},\star})$ 秩为 6，则可在 $\mathcal P_{\mathrm{cont}}$ 内应用 C.1 的论证，得到解集

$$
\mathcal S_t = \{\Theta_{\mathrm{cont}}\in\mathcal P_{\mathrm{cont}}:\mathcal C_t(\Theta_{\mathrm{cont}})=0\}
$$

在 $\Theta_{\mathrm{cont},\star}$ 附近是维数 $N_{\mathrm{cont}}-6$ 的子流形。

全体解集

$$
\mathcal S = \{(\Theta_{\mathrm{cont}},t)\in\mathcal P_{\mathrm{cont}}\times\mathcal P_{\mathrm{disc}}:
\mathcal C_t(\Theta_{\mathrm{cont}})=0\} = \bigcup_{t\in\mathcal P_{\mathrm{disc}}} \left(
\{t\} \times \mathcal S_t
\right)
$$

为各拓扑扇区子流形的并。若强 CP 约束与拓扑结构将允许的拓扑扇区缩减为有限子集 $\mathcal P_{\mathrm{disc}}^{\mathrm{phys}} \subset\mathcal P_{\mathrm{disc}}$，则上式并集变为有限个分支之和，从而得到命题 3.3。

这样，在严格的微分几何意义上，统一约束系统给出的零点集 $\mathcal S$ 由少数连续模参数与有限拓扑选择构成，为"宇宙为何取当前参数值"给出了一个可解析的几何框架。

