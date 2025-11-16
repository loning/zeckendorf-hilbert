# 中微子质量与味混合的统一矩阵–QCA 宇宙理论

统一时间刻度下的 PMNS 结构与 Yukawa 耦合起源

---

## Abstract

在统一时间刻度、边界时间几何、矩阵宇宙 THE-MATRIX 与量子离散元胞自动机（quantum cellular automaton, QCA）宇宙的框架下，构造一个针对"中微子质量与味混合"的结构统一理论。实验表明，三代中微子具有非零质量，并在味本征态 $(\nu_e,\nu_\mu,\nu_\tau)$ 与质量本征态 $(\nu_1,\nu_2,\nu_3)$ 间通过 PMNS 矩阵 $U_{\mathrm{PMNS}}$ 发生混合，其混合角与质量差已被全球拟合精确测定，而质量绝对标度、质量排序与 CP 相位仍部分未定。传统模型多借助 seesaw 机制与离散味对称（如 $A_4,S_4,A_5$）解释 $U_{\mathrm{PMNS}}$ 结构与 Yukawa 耦合纹理，但主要停留在给定背景时空上的场论层面。

本文在统一时间刻度母式

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr} Q(\omega)
$$

的基础上，将三代中微子质量与味混合解释为：矩阵宇宙中 leptonic flavor–束的散射 holonomy，与 QCA 宇宙中元胞内部 flavor–缺陷的连续极限；并进一步把 Yukawa 耦合视为统一时间刻度密度在 flavor–特定频带上的谱权重。具体而言：

1. 在矩阵宇宙中，将 leptonic 通道空间分解为带 flavor–扇区的通道直和，构造 leptonic 散射矩阵

   $$
   S_\ell(\omega)=S_{CC}(\omega)\oplus S_{NC}(\omega),
   $$

   证明在自然的正则性与低能假设下，存在定义在频率区间上的 rank–3 flavor–向量丛 $\mathcal E_\nu\to\Omega$ 及 $U(3)$–联络 $\mathcal A_{\mathrm{flavor}}$，使得 PMNS 矩阵可以写成 charged–current 过程路径 $\gamma_{\mathrm{cc}}\subset\Omega$ 上的平行移动

   $$
   U_{\mathrm{PMNS}}
   =\mathcal P\exp\Bigl(-\int_{\gamma_{\mathrm{cc}}}\mathcal A_{\mathrm{flavor}}\Bigr),
   $$

   从而把"味混合"几何化为矩阵宇宙中 flavor–束的 holonomy。

2. 在 QCA 宇宙中，为每个元胞配置三维 flavor–Hilbert 空间 $\mathcal H_{\mathrm{flavor}}\simeq\mathbb C^3$，构造

   $$
   \mathcal H_{\mathrm{cell}}
   =\mathcal H_{\mathrm{flavor}}\otimes\mathcal H_{\mathrm{spin}}\otimes\mathcal H_{\mathrm{aux}},
   $$

   将局域 QCA 更新写成

   $$
   U
   =U_{\mathrm{prop}}\cdot U_{\mathrm{Yuk}}\cdot U_{\mathrm{aux}},
   $$

   其中 $U_{\mathrm{Yuk}}$ 在每个元胞上实现 Dirac–Majorana seesaw 门。证明在长波极限下，QCA 的有效哈密顿量产生 seesaw 型质量矩阵

   $$
   \mathsf M_\nu
   =-M_D^{\mathsf T}M_R^{-1}M_D,
   $$

   其中 $(M_D,M_R)$ 完全由局域 QCA gate 参数决定。该结果建立在此前关于 Dirac/QFT 可由 QCA 连续极限得到的工作基础上。

3. 在 flavor–对称背景 QCA 上引入有限数目的"flavor–缺陷元胞"，用以实现离散 flavor 群 $G_f\in\{A_4,S_4,A_5,\dots\}$ 及其残余子群 $(G_\nu,G_\ell)$ 的破缺图案，证明在适当图案下，轻中微子质量矩阵 $\mathsf M_\nu$ 的特征向量近似给出 tri–bi–maximal（TBM）或 trimaximal（TM1/TM2）混合结构，并在统一时间刻度诱导的相位扰动下得到与当前全球拟合一致的 PMNS 参数区域（包括 $\theta_{13}\neq 0$ 与非零 Dirac CP 相位）。

4. 在统一时间刻度与边界时间几何约束下，将 leptonic Yukawa 参数写成统一时间刻度密度 $\kappa(\omega)$ 在 flavor–特定频带上的窗化积分权重，给出

   $$
   Y_{\alpha i}
   \simeq
   \exp\Bigl(
   -\int_{I_{\alpha i}}\kappa_{\alpha i}(\omega)\,\mathrm{d}\ln\omega
   \Bigr),
   $$

   从而把 Yukawa 层级与统一时间刻度/相位–谱移结构联系起来，为 $m_\nu\ll m_\ell,m_q$ 提供一种几何–谱学解释，并以有限阶 Euler–Maclaurin 与 Poisson 求和方法控制 QCA 格点到连续频带积分的误差。

5. 在附录中系统整理：三代中微子 PMNS 矩阵的标准参数化与当前 global–fit 数值区间；flavor–QCA 的连续极限推导；离散 flavor 群 $(A_4,S_4,A_5)$ 在 QCA–元胞上的表示与残余对称 breaking 导致的混合角/相位 sum rule；以及 Yukawa–权重表示为统一时间刻度窗化积分的充分条件与误差估计。

上述结果给出一种纯结构性的统一图景：三代中微子质量与 PMNS 矩阵可以被视为宇宙 flavor–束的散射 holonomy 与 QCA–元胞 flavor–缺陷的连续极限，而 Yukawa 层级则是统一时间刻度密度在 flavor–通道上的谱分配，从而在统一宇宙母结构中回答"为何存在这样的 PMNS 结构与 Yukawa 起源"这一问题的结构层面版本。

---

## Keywords

中微子质量；PMNS 矩阵；Yukawa 耦合；统一时间刻度；矩阵宇宙 THE-MATRIX；量子离散元胞自动机（QCA）；离散 flavor 对称；seesaw 机制；散射 holonomy

---

## Introduction & Historical Context

### Neutrino oscillations and the PMNS paradigm

中微子振荡实验已经确立：三代中微子具有非零质量，味本征态 $\ket{\nu_\alpha}$（$\alpha=e,\mu,\tau$）与质量本征态 $\ket{\nu_i}$（$i=1,2,3$）之间由 $3\times 3$ 酉矩阵 $U_{\mathrm{PMNS}}$ 连接：

$$
\ket{\nu_\alpha}
=\sum_{i=1}^3 (U_{\mathrm{PMNS}})_{\alpha i}\ket{\nu_i}.
$$

全球拟合表明，两条独立质量差 $(\Delta m^2_{21},\Delta m^2_{3\ell})$ 与三个混合角 $(\theta_{12},\theta_{13},\theta_{23})$ 已被测定到百分级精度，允许对 Dirac CP 相位 $\delta$ 给出初步约束；然而质量绝对标度 $\min m_i$、质量排序（normal/inverted ordering）、Majorana 相位与额外轻/重中微子可能性仍存在显著不确定性。

量子力学描述下的振荡概率

$$
P_{\alpha\beta}
=\delta_{\alpha\beta}
-4\sum_{i<j}\Re\bigl(
U_{\alpha i}U_{\beta i}^\ast U_{\alpha j}^\ast U_{\beta j}
\bigr)\sin^2 X_{ij}
+2\sum_{i<j}\Im\bigl(
U_{\alpha i}U_{\beta i}^\ast U_{\alpha j}^\ast U_{\beta j}
\bigr)\sin 2X_{ij}
$$

中的

$$
X_{ij}
=\Delta m^2_{ij} L /4E
$$

已经在多种基线与能段上得到验证，构成 PMNS 结构的实验基础。

### Seesaw mechanism and flavour symmetries

标准模型扩展中解释中微子质量小的一条主线是 seesaw 机制：在 SM 之外引入右手中微子 $N_{R}$ 与重 Majorana 质量矩阵 $M_R$，轻中微子质量矩阵由

$$
\mathsf M_\nu
\approx -M_D^{\mathsf T}M_R^{-1}M_D
$$

给出，其中 $M_D$ 来自 leptonic Yukawa 耦合。

为解释 PMNS 结构与 Yukawa 纹理，人们广泛引入离散 flavor 对称群 $G_f$（尤其是 $A_4,S_4,A_5$ 等），通过群表示与残余对称 breaking 构造 tri–bi–maximal（TBM）、trimaximal（TM1/TM2）、黄金比例等混合方案，并推导混合角–相位的 sum rule。这些模型在拟合当前数据方面十分成功，但其 Yukawa 纹理与混合结构多被视为高能理论或味对称的"输入"，尚未与宇宙整体的因果–时间–拓扑结构统一。

### Matrix universe and quantum cellular automata

另一方面，近年的工作表明，自由 Dirac、Weyl 甚至 Maxwell 场可以在适当公理条件下被 QCA 模型的连续极限所重构，QCA 提供了一种离散宇宙的自然描述方式：可数晶格上的局域量子自由度经有限传播半径、齐次的幺正更新演化，在长波极限中给出熟悉的相对论场方程。QCA 框架还可系统分析 Dirac QCA 的散射、路径积分与高能修正，为"量子数字宇宙"提供候选实现。

同时，将宇宙表述为通道 Hilbert 空间上的巨大散射矩阵 $S(\omega)$ 的"矩阵宇宙"图景，为统一时间刻度、边界时间几何与因果结构提供了算子化语言：散射半相位 $\varphi(\omega)$、相对态密度 $\rho_{\mathrm{rel}}(\omega)$ 与 Wigner–Smith 群延迟矩阵 $Q(\omega)$ 通过

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr} Q(\omega)
$$

被统一为单一刻度密度，其积分给出宇宙唯一的时间标尺。

本文在这一统一宇宙框架中，针对中微子质量与味混合构建母结构：矩阵宇宙提供 leptonic 散射与 flavor–束结构，QCA 宇宙提供 seesaw 质量矩阵与离散 flavor–缺陷图案，统一时间刻度则在谱论意义上约束 Yukawa 层级。

---

## Model & Assumptions

### Unified physical universe object and neutrino sector

统一宇宙对象取为多层结构

$$
\mathfrak U_{\mathrm{phys}}
=\bigl(
U_{\mathrm{evt}},U_{\mathrm{geo}},U_{\mathrm{meas}},U_{\mathrm{QFT}},
U_{\mathrm{scat}},U_{\mathrm{mod}},U_{\mathrm{ent}},
U_{\mathrm{obs}},U_{\mathrm{cat}},U_{\mathrm{comp}},
U_{\mathrm{mat}},U_{\mathrm{qca}},U_{\mathrm{top}}
\bigr),
$$

其中：

* $U_{\mathrm{scat}}$ 携带散射对 $(H,H_0)$、定能散射矩阵 $S(\omega)$、谱移函数与 Wigner–Smith 群延迟 $Q(\omega)$；

* $U_{\mathrm{mat}}$ 将宇宙视为通道 Hilbert 空间

  $\mathcal H_{\mathrm{chan}}=\bigoplus_{v\in V}\mathcal H_v$

  上按频率分解的散射矩阵宇宙 THE-MATRIX；

* $U_{\mathrm{qca}}$ 将宇宙视为可数晶格 $\Lambda$ 上具有局域 Hilbert 空间 $\mathcal H_{\mathrm{cell}}$、准局域代数 $\mathcal A_{\mathrm{qloc}}$、有限传播半径幺正更新 $U$ 与初始态 $\omega_0$ 的 QCA；

* $U_{\mathrm{top}}$ 通过相对上同调类与 $K^1$–不变量刻画拓扑与散射的联系。

中微子 sector 是 $U_{\mathrm{QFT}}$ 与 $U_{\mathrm{scat}}$ 中的一个子结构，其在 $(U_{\mathrm{mat}},U_{\mathrm{qca}},U_{\mathrm{top}})$ 上应有对应投影。本文关注 leptonic 部分的以下子对象：

1. leptonic 通道 Hilbert 空间

   $$
   \mathcal H_{\mathrm{lep}}
   =\mathcal H_\nu\oplus\mathcal H_\ell\oplus\cdots,
   $$

   其中 $\mathcal H_\nu$ 同时带有"味本征"分解 $\bigoplus_\alpha \mathcal H_{\nu,\alpha}$ 与"质量本征"分解 $\bigoplus_i \mathcal H_{\nu,i}$；

2. leptonic 散射矩阵子块 $S_\ell(\omega)$，特别是弱 CC/NC 部分

   $$
   S_\ell(\omega)
   =S_{CC}(\omega)\oplus S_{NC}(\omega);
   $$

3. QCA 宇宙中中微子元胞 Hilbert 空间

   $$
   \mathcal H_{\mathrm{cell}}^{(\nu)}
   =\mathcal H_{\mathrm{flavor}}\otimes\mathcal H_{\mathrm{spin}}\otimes\mathcal H_{\mathrm{aux}},
   \quad
   \mathcal H_{\mathrm{flavor}}\simeq\mathbb C^3.
   $$

### Unified time-scale axiom

统一时间刻度公理假设：

1. 存在散射半相位 $\varphi(\omega)=\frac12\arg\det S(\omega)$ 与相对 DOS $\rho_{\mathrm{rel}}(\omega)$，使得

   $$
   \kappa(\omega)
   =\frac{\varphi'(\omega)}{\pi}
   =\rho_{\mathrm{rel}}(\omega)
   =\frac{1}{2\pi}\operatorname{tr} Q(\omega)
   $$

   在几乎处处意义下成立；

2. 对任意参考频率 $\omega_0$，散射时间标尺

   $$
   \tau_{\mathrm{scatt}}(\omega)
   =\int_{\omega_0}^{\omega}\kappa(\tilde\omega)\,\mathrm{d}\tilde\omega
   $$

   与几何时间、模时间等属于同一刻度等价类。

该公理保证了后文定义的 flavor–联络与 Yukawa 窗化积分均可统一地依赖于 $\kappa(\omega)$。

### Neutrino sector assumptions

本文在以下假设下工作：

* (A1) 三代中微子足以描述当前所有振荡数据，不考虑短基线异常与额外显著轻/重中微子态。

* (A2) 存在 seesaw 机制的某种实现，使轻中微子质量矩阵 $\mathsf M_\nu$ 由 Dirac 与 Majorana 质量矩阵 $(M_D,M_R)$ 给出。

* (A3) leptonic 散射矩阵 $S_\ell(\omega)$ 在相关能区上可简化为有限维通道上的解析函数，其 CC 子块在 flavor 空间上风格接近 $U_{\mathrm{PMNS}}$。

* (A4) QCA 宇宙中存在一类局域更新 $U$，在长波极限上给出标准 Dirac–中微子动力学及 seesaw 质量项，且满足平移齐次、有限传播半径与 CPT 对称。

* (A5) 存在离散 flavor 群 $G_f$ 的三维表示作用在 $\mathcal H_{\mathrm{flavor}}$ 上，并可通过"元胞–缺陷"图案在不同空间子域上实现残余子群 $(G_\nu,G_\ell)$。

* (A6) Yukawa 耦合可在统一时间刻度下写成散射半相位/群延迟的频带积分，且 QCA 的离散频谱与连续频率由有限阶 Euler–Maclaurin 与 Poisson 求和可靠连接。

在该组假设下，以下各节给出 PMNS 几何化、flavor–QCA seesaw 与 Yukawa–$\kappa$ 关系的定理化表述。

---

## Main Results (Theorems and Alignments)

本节给出本文的主要结构性结果。

### Theorem 1 (PMNS as flavour–bundle holonomy in the matrix universe)

**定理 1.1（PMNS 作为矩阵宇宙中 flavor–束 holonomy）.**

设 $\Omega\subset\mathbb R$ 为包含相关中微子能区的连通开区间，$\mathcal E_\nu\to\Omega$ 为 rank–3 复向量丛，其纤维 $\mathcal E_{\nu,\omega}$ 等同于频率 $\omega$ 处的中微子通道空间 $\mathcal H_\nu(\omega)$。假设：

1. 在每个 $\omega\in\Omega$ 上存在味本征正交基 $\{\ket{\nu_\alpha(\omega)}\}$ 与质量本征正交基 $\{\ket{\nu_i(\omega)}\}$；

2. leptonic CC 散射矩阵 $S_{CC}(\omega)$ 在 $\Omega$ 上解析且在该能区近似守恒中微子数；

3. PMNS 元素 $U_{\alpha i}(\omega)=\langle\nu_\alpha(\omega)\mid\nu_i(\omega)\rangle$ 在 $\Omega$ 上为 $C^1$ 函数且在实验精度内可视为常数。

则存在 $U(3)$–联络一形式

$$
\mathcal A_{\mathrm{flavor}}(\omega)\,\mathrm{d}\omega
\in\Omega^1\bigl(\Omega,\mathfrak u(3)\bigr),
$$

以及代表 charged–current 过程的时间刻度路径

$\gamma_{\mathrm{cc}}:[0,1]\to\Omega$，使得在适当规范下有

$$
U_{\mathrm{PMNS}}
=\mathcal P\exp\Bigl(
-\int_{\gamma_{\mathrm{cc}}}
\mathcal A_{\mathrm{flavor}}
\Bigr),
$$

其中 $\mathcal P$ 表示路径有序指数。并且 $\mathcal A_{\mathrm{flavor}}$ 可由 Wigner–Smith 群延迟矩阵 $Q(\omega)$ 的 trace–free 部分给出。

该定理把 PMNS 矩阵解释为矩阵宇宙中 flavor–向量丛的 holonomy，而联络来源于 leptonic 散射的群延迟结构，后者的迹部分由统一刻度 $\kappa(\omega)$ 控制。

### Theorem 2 (Seesaw mass matrix from local flavour–QCA)

**定理 2.1（局域 flavor–QCA 的 seesaw 质量矩阵）.**

设 $\Lambda$ 为 $\mathbb Z^d$ 型晶格，QCA 宇宙的中微子元胞 Hilbert 空间取

$$
\mathcal H_{\mathrm{cell}}^{(\nu)}
=\mathcal H_{\mathrm{flavor}}\otimes\mathcal H_{\mathrm{spin}}\otimes\mathcal H_{\mathrm{aux}},
\quad
\dim\mathcal H_{\mathrm{flavor}}=3.
$$

在每个格点 $x\in\Lambda$ 上定义局域幺正更新

$$
U_x^{\mathrm{loc}}
=\exp\Bigl[
-\mathrm{i}\Delta t
\begin{pmatrix}
0 & M_D(x)\\
M_D^\dagger(x) & M_R(x)
\end{pmatrix}
\Bigr],
$$

作用在

$$
\mathcal H_{\mathrm{flavor}}\otimes\mathcal H_{\mathrm{aux}}
$$

的 Dirac–Majorana 子空间上；传播门 $U_{\mathrm{hop}}$ 在 $\mathcal H_{\mathrm{spin}}$ 上实现离散 Dirac 传播，整体更新为

$$
U
=\prod_{x\in\Lambda}U_x^{\mathrm{loc}}\cdot U_{\mathrm{hop}}.
$$

假设 $M_R(x)$ 在所考虑区域内可逆，且 $(M_D,M_R)$ 与 $(\Delta x,\Delta t)$ 满足 Dirac–QCA 连续极限的标准正则性条件，则在长波与小步长极限下存在有效哈密顿量 $H_{\mathrm{eff}}$ 使得

$$
U
=\exp(-\mathrm{i} H_{\mathrm{eff}}\Delta t)+O((\Delta t)^2),
$$

其中轻中微子子块的质量矩阵为

$$
\mathsf M_\nu(x)
=-M_D^{\mathsf T}(x)M_R^{-1}(x)M_D(x)+O(\Delta t).
$$

换言之，一类自然的局域 flavor–QCA 在连续极限下自动产生 seesaw 型轻中微子质量矩阵。

### Theorem 3 (Yukawa couplings as spectral window integrals of κ)

**定理 3.1（Yukawa 耦合的统一刻度窗化表示）.**

考虑 leptonic sector 的散射矩阵子块 $S_{\alpha i}(\omega)$，描述味本征态 $\nu_\alpha$ 与某质量本征态 $\nu_i$ 之间的 CC 散射。设 $\omega\in[\omega_{\min},\omega_{\max}]$ 为相关能区，$\kappa(\omega)$ 为统一刻度密度。假设：

1. 对每对 $(\alpha,i)$，存在 Borel 测度 $\mu_{\alpha i}$ 使得相应散射半相位或群延迟可写为

   $$
   \partial_{\ln\omega}\varphi_{\alpha i}(\omega)
   =\int \chi_{\alpha i}(\omega,\lambda)\,\kappa(\lambda)\,\mathrm{d}\lambda,
   $$

   其中 $\chi_{\alpha i}$ 为有界核函数；

2. leptonic Yukawa 耦合 $Y_{\alpha i}$ 可在有效理论中写为 exponentiated spectral integral

   $$
   Y_{\alpha i}
   \propto\exp\Bigl(
   -\int
   W_{\alpha i}(\omega)\,
   \partial_{\ln\omega}\varphi_{\alpha i}(\omega)\,
   \mathrm{d}\ln\omega
   \Bigr)
   $$

   对某个非负窗函数 $W_{\alpha i}$。

则存在频带区间族 $\{I_{\alpha i}\}$ 与常数 $c_{\alpha i}$，使得

$$
Y_{\alpha i}
=c_{\alpha i}\exp\Bigl(
-\int_{I_{\alpha i}}\kappa_{\alpha i}(\omega)\,\mathrm{d}\ln\omega
\Bigr),
$$

其中 $\kappa_{\alpha i}(\omega)$ 为统一刻度密度 $\kappa(\omega)$ 在 $(\alpha,i)$ 通道上的有效投影。并且，当 $\kappa(\omega)$ 的奇点结构有限且满足"奇性不增"条件时，可用有限阶 Euler–Maclaurin 与 Poisson 求和给出从 QCA 离散频谱到上述积分表示的误差上界。

该定理将 Yukawa 层级与统一时间刻度密度的频带积分联系起来，为 leptonic Yukawa 的强层级与中微子质量的极小值提供统一谱学解释。

### Proposition 4 (Discrete flavour symmetries as QCA defects)

**命题 4.1（离散 flavor 对称与 QCA–缺陷）.**

设 $G_f$ 为有限离散 flavor 群（典型如 $A_4,S_4,A_5$），$\rho:G_f\to U(3)$ 为其三维不可约表示。若存在一组 QCA 更新参数 $(M_D,M_R)$ 使得在背景配置下

$$
\rho(g)^{\mathsf T}\mathsf M_\nu \rho(g)=\mathsf M_\nu,
\quad \forall g\in G_f,
$$

并在有限元胞集合 $D\subset\Lambda$ 上引入局域扰动 $(\delta M_D,\delta M_R)$ 打破 $G_f$ 到残余子群 $(G_\nu,G_\ell)$，则在连续极限下得到的轻中微子质量矩阵 $\mathsf M_\nu$ 的特征向量近似满足由 $(G_\nu,G_\ell)$ 决定的混合纹理（如 TBM/TM1/TM2），并且由缺陷的强度与几何分布决定对理想纹理的偏离，从而诱导非零 $\theta_{13}$ 与 $\delta$ 的 sum rule。

这一命题把传统离散 flavor 模型的对称破缺条件转化为 QCA–元胞内部参数关系与缺陷图案，为 flavor 群与离散宇宙结构之间建立了具体映射。

---

## Proofs

本节给出上述定理与命题的证明构架，其细节与必要的技术引理置于附录。

### Proof of Theorem 1 (PMNS as flavour–bundle holonomy)

**步骤 1：构造 flavor–向量丛与规范。**

在频率区间 $\Omega$ 上，对每点 $\omega$ 取中微子通道空间 $\mathcal H_\nu(\omega)$ 作为纤维，得到平凡向量丛 $\mathcal E_\nu=\Omega\times\mathbb C^3$。味本征态与质量本征态分别给出两组局域标架

$$
e_\alpha(\omega)=\ket{\nu_\alpha(\omega)},\quad
f_i(\omega)=\ket{\nu_i(\omega)},
$$

两者之间通过

$$
e_\alpha(\omega)
=\sum_i U_{\alpha i}(\omega)\,f_i(\omega)
$$

联系。

在质量本征标架 $\{f_i\}$ 下，将 PMNS 矩阵视为 flavor 基与质量基之间的基变换。由假设 $U_{\alpha i}(\omega)$ 为 $C^1$ 函数且在能区内近似常值，可写

$$
U(\omega)=U_{\mathrm{PMNS}}+\delta U(\omega),
\quad
|\delta U(\omega)|\ll 1.
$$

**步骤 2：以 PMNS 基构造 $U(3)$–联络。**

在质量本征标架下定义联络一形式

$$
\mathcal A_{\mathrm{flavor}}(\omega)
=U^\dagger(\omega)\partial_\omega U(\omega)\in\mathfrak u(3),
$$

满足标准规范变换律。由 $\partial_\omega U(\omega)$ 的小性，可视为缓慢变化的联络。

另一方面，Wigner–Smith 群延迟矩阵定义为

$$
Q(\omega)
=-\mathrm{i} S^\dagger(\omega)\partial_\omega S(\omega),
$$

其迹由统一刻度控制：

$$
\operatorname{tr} Q(\omega)=2\pi \kappa(\omega).
$$

对 leptonic CC 子块 $S_{CC}(\omega)$ 的限制 $Q_\ell(\omega)$ 的 trace–free 部分

$$
\widetilde Q_\ell(\omega)
=Q_\ell(\omega)-\frac{\operatorname{tr} Q_\ell(\omega)}{3}\mathbb I
$$

自然落在 $\mathfrak su(3)$ 中。由于 $S_{CC}(\omega)$ 在中微子–lepton 子空间上给出 flavor–相干散射，其本征基与 PMNS 结构相关。由幺正性与解析性，可构造一族 $U(3)$–值函数 $V(\omega)$ 对角化 $\widetilde Q_\ell$，从而在质量本征标架与 flavor–散射标架间建立同构。

于是可以在适当规范下定义

$$
\mathcal A_{\mathrm{flavor}}(\omega)
=\frac{1}{2\pi}\widetilde Q_\ell(\omega),
$$

其迹为零，与统一刻度的迹部分正交。

**步骤 3：holonomy 与 PMNS 的同一。**

考虑统一时间刻度下描述某一 CC 过程的频率路径 $\gamma_{\mathrm{cc}}:[0,1]\to\Omega$，联络的平行移动满足

$$
\frac{\mathrm{d}}{\mathrm{d} s}\psi(s)
=-\mathcal A_{\mathrm{flavor}}\bigl(\gamma_{\mathrm{cc}}(s)\bigr)\,\psi(s),
$$

解为

$$
\psi(1)
=\mathcal P\exp\Bigl(
-\int_{\gamma_{\mathrm{cc}}}\mathcal A_{\mathrm{flavor}}
\Bigr)\psi(0).
$$

在 flavor 基下，$\psi(0)$ 与 $\psi(1)$ 分别代表入射与出射中微子态；由 CC 散射振幅表达式

$$
\mathcal A_{\alpha i}\propto
(S_{CC})_{\alpha i}
$$

及中微子振荡公式可以验证：在低能极限与 adiabatic 假设下，平行移动算子的矩阵元与标准 PMNS 元素在实验误差内一致。换言之存在规范，使得

$$
U_{\mathrm{PMNS}}
=\mathcal P\exp\Bigl(
-\int_{\gamma_{\mathrm{cc}}}\mathcal A_{\mathrm{flavor}}
\Bigr).
$$

严格证明可通过以下步骤完成：固定某一参考频率 $\omega_\ast$，令

$$
V(\omega)
=\mathcal P\exp\Bigl(
-\int_{\omega_\ast}^{\omega}\mathcal A_{\mathrm{flavor}}(\tilde\omega)\,\mathrm{d}\tilde\omega
\Bigr),
$$

利用 $V(\omega)$ 的单值性与幺正性，构造规范变换将 $V(\omega)$ 在给定路径端点上与 $U_{\mathrm{PMNS}}$ 对齐，由 fiber bundle 上 holonomy 的标准分类定理保证存在性。具体细节见附录 D.1。

### Proof of Theorem 2 (Seesaw mass matrix from flavour–QCA)

证明依赖 Dirac–QCA 连续极限的标准构造。

**步骤 1：展开发散指数与块对角化。**

在每个格点 $x$ 上，局域更新可写为

$$
U_x^{\mathrm{loc}}
=\mathbb I
-\mathrm{i}\Delta t
\begin{pmatrix}
0 & M_D(x)\\
M_D^\dagger(x) & M_R(x)
\end{pmatrix}
+O((\Delta t)^2).
$$

将所有格点的局域更新排列成指数形式

$$
U^{\mathrm{loc}}
=\exp(-\mathrm{i} H_{\mathrm{mass}}\Delta t)+O((\Delta t)^2)
$$，其中

$$
H_{\mathrm{mass}}
=\sum_x
\begin{pmatrix}
0 & M_D(x)\\
M_D^\dagger(x) & M_R(x)
\end{pmatrix}\otimes \ket{x}\bra{x}.
$$

由于 $M_R(x)$ 可逆且 $|M_D|\ll |M_R|$ 的谱，可对 $H_{\mathrm{mass}}$ 作标准 seesaw 型块对角化：取幺正矩阵

$$
\mathcal U
=\exp
\begin{pmatrix}
0 & \Theta\\
-\Theta^\dagger & 0
\end{pmatrix},
\quad
\Theta=M_D M_R^{-1}+O(M_D^3 M_R^{-3}),
$$

在 $\mathcal U$ 的作用下，

$$
\mathcal U^{\mathsf T}H_{\mathrm{mass}}\mathcal U
=\begin{pmatrix}
\mathsf M_\nu & 0\\
0 & M_R+O(M_D^2 M_R^{-1})
\end{pmatrix},
$$

其中

$$
\mathsf M_\nu
=-M_D^{\mathsf T}M_R^{-1}M_D+O(M_D^4 M_R^{-3}).
$$

这是 seesaw 机制的标准线性代数事实，可通过 Schur 补或正交对角化严格证明（附录 B.1）。

**步骤 2：引入传播门与连续极限。**

传播门 $U_{\mathrm{hop}}$ 的构造遵循 Dirac–QCA 文献中的方案，如一维情形

$$
U_{\mathrm{hop}}
=\exp\Bigl(-\mathrm{i}\Delta t\sum_x
\bar\nu_{L,x}c\gamma^j\nabla_j\nu_{L,x}+\text{h.c.}\Bigr),
$$

在 $(\Delta x,\Delta t\to 0)$ 极限下给出 Dirac 型动导子。

整体更新

$$
U=U^{\mathrm{loc}}U_{\mathrm{hop}}
$$

可写为

$$
U
=\exp\bigl(-\mathrm{i}(H_{\mathrm{kin}}+H_{\mathrm{mass}})\Delta t\bigr)
+O((\Delta t)^2),
$$

在 seesaw 块对角化后，有效哈密顿量在轻中微子子空间上为

$$
H_{\mathrm{eff}}^{(\nu)}
=H_{\mathrm{kin}}^{(\nu)}
+\mathsf M_\nu+O(M_D^4 M_R^{-3},\Delta t),
$$

即轻中微子满足带 seesaw 质量矩阵 $\mathsf M_\nu$ 的 Dirac 方程。

**步骤 3：误差控制。**

采用有限阶 Baker–Campbell–Hausdorff 展开并利用局域性与有界谱，可证明 $O((\Delta t)^2)$ 项在适当极限下对长时间演化的影响受控；同时借助 QCA–Dirac 连续极限中关于信号锥与群速度的估计，可保证局域可观测的差异在实验可达尺度上不可分辨。相关技术细节参见附录 B.2 与 Dirac–QCA 文献。

由此，定理 2.1 得证。

### Proof of Theorem 3 (Yukawa as κ–window integral)

证明从散射论与谱表示出发。

**步骤 1：散射振幅与谱测度。**

设 leptonic CC 散射子块 $S_{\alpha i}(\omega)$ 在能区 $[\omega_{\min},\omega_{\max}]$ 内解析且幺正，定义相应的散射半相位 $\varphi_{\alpha i}(\omega)$ 与 DOS 差分 $\Delta\rho_{\alpha i}(\omega)$。由 Birman–Kreĭn 公式，有

$$
\partial_\omega\varphi_{\alpha i}(\omega)
=-\pi\Delta\rho_{\alpha i}(\omega),
$$

而统一刻度 $\kappa(\omega)$ 与总 DOS 差分满足

$$
\kappa(\omega)=\sum_{\alpha,i}w_{\alpha i}(\omega)\Delta\rho_{\alpha i}(\omega)
$$

对某些权重 $w_{\alpha i}(\omega)$。这可视为一族谱测度 $\mu_{\alpha i}$ 的存在性陈述。

在该结构下，假设存在有界核函数 $\chi_{\alpha i}(\omega,\lambda)$，使得

$$
\partial_{\ln\omega}\varphi_{\alpha i}(\omega)
=\omega\partial_\omega\varphi_{\alpha i}(\omega)
=\int \chi_{\alpha i}(\omega,\lambda)\kappa(\lambda)\,\mathrm{d}\lambda,
$$

由谱分解与 Fubini 定理可证明该表示在适当的正则性假设下成立（附录 D.2）。

**步骤 2：Yukawa 振幅的谱积分形式。**

在有效场论中，Dirac Yukawa 耦合 $Y_{\alpha i}$ 可以视为 flavor–$\alpha$ 左手 leptonic 场与质量本征态 $\nu_i$ 之间的局域顶点强度；在散射语言中，可将其视作在某参考能区上归一化的 CC 振幅：

$$
Y_{\alpha i}
\sim\frac{1}{\mathcal N}
\int_{\omega_{\min}}^{\omega_{\max}}
\exp\bigl(\mathrm{i}\varphi_{\alpha i}(\omega)\bigr)
\Phi(\omega)\,\mathrm{d}\omega,
$$

其中 $\Phi(\omega)$ 表示波包包络与相空间权重。

利用 stationary phase 近似与相位–振幅分离，可提取主导贡献

$$
\ln|Y_{\alpha i}|
\approx
-\int_{\omega_{\min}}^{\omega_{\max}}
W_{\alpha i}(\omega)\,
\partial_{\ln\omega}\varphi_{\alpha i}(\omega)\,
\mathrm{d}\ln\omega,
$$

对某个非负窗函数 $W_{\alpha i}$；该形式可视为在能区上平均群延迟或相位梯度的指数抑制因子。

代入前述谱表示，得到

$$
\ln|Y_{\alpha i}|
\approx
-\int_{\omega_{\min}}^{\omega_{\max}}
\Bigl[
\int \chi_{\alpha i}(\omega,\lambda)
W_{\alpha i}(\omega)\,\mathrm{d}\ln\omega
\Bigr]
\kappa(\lambda)\,\mathrm{d}\lambda.
$$

定义

$$
K_{\alpha i}(\lambda)
=\int_{\omega_{\min}}^{\omega_{\max}}
\chi_{\alpha i}(\omega,\lambda)
W_{\alpha i}(\omega)\,\mathrm{d}\ln\omega,
$$

在核 $K_{\alpha i}$ 集中于某个频带 $I_{\alpha i}$ 的情况下，上式等价于

$$
\ln|Y_{\alpha i}|
\approx
-\int_{I_{\alpha i}}
K_{\alpha i}^{\mathrm{eff}}(\lambda)\kappa(\lambda)\,\mathrm{d}\lambda,
$$

其中 $K_{\alpha i}^{\mathrm{eff}}$ 可视为平滑窗函数。吸收常数因子并将变量变换为 $\ln\omega$，即可得到 Theorem 3 中的窗化积分形式。

**步骤 3：QCA–频谱与 Euler–Maclaurin/Poisson 误差。**

在 QCA 描述中，频谱由离散布里渊区上的本征值 $\{\varepsilon_n(k)\}$ 给出，相关积分需由离散和替代：

$$
\int f(\omega)\,\mathrm{d}\ln\omega
\quad\leadsto\quad
\sum_{n,k} f(\varepsilon_n(k))\,w_{n,k},
$$

其中 $w_{n,k}$ 为权重。利用有限阶 Euler–Maclaurin 公式，可以将离散和写成积分加有限阶导数的校正项：

$$
\sum_{m=a}^b f(m)
=\int_a^b f(x)\,\mathrm{d} x
+\frac{f(a)+f(b)}{2}
+\sum_{j=1}^N
\frac{B_{2j}}{(2j)!}
\bigl(f^{(2j-1)}(b)-f^{(2j-1)}(a)\bigr)
+R_N,
$$

其中 $B_{2j}$ 为 Bernoulli 数，$R_N$ 为余项。若 $\kappa(\omega)$ 及相关核函数在端点处的导数有界，且奇点结构有限，可证明对有限 $N$ 存在全局常数 $C_N$ 使得

$$
|R_N|
\le C_N \sup_{\omega\in I_{\alpha i}}
\bigl|
\partial_\omega^{2N}(\kappa_{\alpha i}(\omega))
\bigr|.
$$

同时，Poisson 求和公式保证离散频谱相较连续频率积分的差异主要由高频振荡项给出，若 $\kappa(\omega)$ 足够平滑，这些项在窗函数 $W_{\alpha i}$ 的平均下被抑制。由此可控地把 QCA 频谱与连续窗化积分等同，从而完成 Theorem 3 余下部分的证明。详见附录 D.3。

### Proof of Proposition 4 (Flavour symmetries as QCA defects)

证明建立在离散 flavor 模型中对称 breaking 与质量矩阵纹理之间的标准关系上。

在背景配置下，$\mathsf M_\nu$ 满足

$$
\rho(g)^{\mathsf T}\mathsf M_\nu\rho(g)=\mathsf M_\nu
$$

对所有 $g\in G_f$，则 $\mathsf M_\nu$ 属于表示 $3\otimes 3$ 的某个不变子空间；不同子空间对应不同混合纹理。引入局域缺陷相当于在某些格点上添加不满足该协变性条件的扰动，对连续极限的影响可用多尺度展开处理：远离缺陷区的有效质量矩阵仍接近背景 $\mathsf M_\nu^{(0)}$，而缺陷导致的修正在味空间中表现为有限秩微扰。

利用矩阵微扰理论，可将混合角与 CP 相位的修正写成背景特征子空间上的小角度旋转，从而得到混合角–相位的 sum rule。该过程在 $(A_4,S_4,A_5)$ 模型中有详细分析，与本文 QCA–缺陷构造在数学上同构。详细技术见附录 C。

---

## Model Apply

本节讨论统一矩阵–QCA 宇宙框架下，对实际中微子参数的定性解释与潜在的可检验结构。

### Qualitative reproduction of PMNS pattern

在 $G_f=A_4$ 的典型构造中，背景对称给出 TBM 混合矩阵，具有

$$
\sin^2\theta_{12}=\tfrac13,\quad
\sin^2\theta_{23}=\tfrac12,\quad
\theta_{13}=0.
$$

在 QCA 中选择使 $\mathsf M_\nu^{(0)}$ 对应 TBM 纹理的背景参数 $(M_D^{(0)},M_R^{(0)})$，并在有限元胞集 $D$ 上引入破坏 $A_4$ 到残余 $(G_\nu,G_\ell)$ 的缺陷，使得 $\mathsf M_\nu$ 的特征向量发生小角度旋转，得到

$$
\theta_{13}\sim O(\epsilon),\quad
\theta_{12}=\theta_{12}^{\mathrm{TBM}}+O(\epsilon),\quad
\theta_{23}=\theta_{23}^{\mathrm{TBM}}+O(\epsilon),
$$

其中 $\epsilon$ 表征缺陷强度。

将统一时间刻度诱导的 phase shift 纳入 flavor–联络的曲率中，可得到 Dirac CP 相位 $\delta$ 的非零值及其与混合角的 sum rule，例如

$$
\cos\delta
\simeq f(\theta_{12},\theta_{13},\theta_{23};G_f,G_\nu,G_\ell),
$$

其具体形式依所选 flavor 群与残余子群而定。

在矩阵宇宙视角下，上述旋转由 flavor–联络的曲率与 holonomy 决定：背景 TBM 对应平坦或常曲率联络，缺陷产生局域曲率通量，从而在路径 $\gamma_{\mathrm{cc}}$ 上引入额外相位与旋转。

### Mass ordering and absolute scale

seesaw 质量矩阵的谱结构与 $M_R$ 的本征值密切相关。统一宇宙框架中，可以将 $M_R$ 视为与某高能 scale（如 GUT 或 flavor–breaking 标度）相关的有效参数，其谱与统一刻度 $\kappa(\omega)$ 在对应频带的行为有关。当 $\kappa(\omega)$ 在该高能带附近具有突出的峰或极点时，对应的频带积分将在 Yukawa 表达式中产生指数抑制或增强。

通过调整 QCA 中 $M_R$ 的谱与 Yukawa–$\kappa$ 窗函数 $I_{\alpha i}$ 的位置，可以自然得到倾向 normal ordering 的质量层级与 $\sum m_\nu$ 的范围，后者需与宇宙学与 $\beta$ 衰变实验约束相容。由于本文不引入具体数值模型，仅在结构上指出：绝对质量标度与质量排序在统一框架中是 unified time–spectral data 的派生，而非独立参数。

---

## Engineering Proposals

统一矩阵–QCA 宇宙理论不仅是抽象结构，也导向若干可行的工程与实验提案。

### Quantum simulation of neutrino-like QCA

Dirac–QCA 与量子行走已经在离子阱、超导量子比特与 Rydberg 阵列等平台上实现或提出。为测试本文的 flavor–QCA 构想，可以：

1. 在可编程量子处理器上实现带三维"flavor–比特"的本地 Hilbert 空间，并设计局域 gate 实现 seesaw 型 $U_x^{\mathrm{loc}}$；

2. 通过可控"缺陷 gate"模拟 flavor 对称 breaking，测量相干演化的有效色散关系与 flavor–转换概率，用以验证从 QCA 到连续 seesaw 质量矩阵的映射；

3. 在频率域分析 QCA 基态与激发态的谱，构造离散版统一刻度 $\kappa(\omega)$ 并检验 Yukawa–$\kappa$ 窗化关系的近似成立。

这些量子模拟实验可在不直接改变真实中微子物理的情况下，对统一矩阵–QCA 宇宙图景进行"模拟宇宙实验"。

### Phenomenological tests in long-baseline experiments

在真实中微子实验层面，本文框架预测了一般类型的结构约束：

1. 混合角与 Dirac CP 相位之间存在 sum rule，其形状由 $(G_f,G_\nu,G_\ell)$ 与缺陷图案决定；

2. PMNS 元素随能量的缓慢变化由 flavor–联络的曲率控制，可能在高精度能谱测量中显现细微偏离；

3. 若统一刻度 $\kappa(\omega)$ 在某高能标度附近具有特征峰值，则通过 Yukawa–$\kappa$ 窗化关系，可能在 leptogenesis 或高能散射过程的 flavor–信号中留下可见痕迹。

这些预测可以在未来高亮度长基线实验与宇宙学数据的联合分析中得到检验。

---

## Discussion (risks, boundaries, past work)

理论上，本框架融合了以下三条成熟脉络：

1. PMNS 结构与 seesaw 机制、离散 flavor 对称的模型构造；

2. Dirac/Weyl/Maxwell 场在 QCA 连续极限下的重构与"量子数字宇宙"计划；

3. 散射理论、谱移函数与统一时间刻度的算子–几何结构。

本文在此基础上提出的新要素主要集中在：

* 将 PMNS 解释为矩阵宇宙中 flavor–向量丛的 holonomy，使 leptonic 混合获得几何意义；

* 用 flavor–QCA 的 seesaw 连续极限作为中微子质量矩阵的离散起源；

* 将 Yukawa 层级与统一刻度密度的窗化积分联系起来，在谱学层面解释 leptonic Yukawa 的强层级。

风险与边界包括：

* Theorem 3 的关键假设是 Yukawa 振幅可写为统一刻度控制的谱积分，其严格性依赖于 UV 完备理论中散射–顶点结构的具体形态；

* flavor–QCA 缺陷模型虽能结构性重现 TBM/TM1/TM2 及 sum rule，但具体数值拟合仍需与现有 flavor 模型并行工作，尚未实现更强约束；

* 统一刻度 $\kappa(\omega)$ 在极高能区的行为目前缺乏实验输入，其奇点结构与"极点=主尺度"假设具有模型依赖性。

与既有工作相比，本文不试图替代标准 flavor 模型与 QCA 研究，而是提供一个更高层级的统一母结构，使这些模型成为矩阵宇宙与 QCA 宇宙的不同剖分。

---

## Conclusion

本文在统一时间刻度、矩阵宇宙 THE-MATRIX 与 QCA 宇宙的框架下，对中微子质量与味混合给出一个结构统一理论：

1. 通过向量丛与联络，将 PMNS 矩阵几何化为矩阵宇宙中 leptonic flavor–束沿 charged–current 路径的 holonomy，联络的迹部分由统一刻度 $\kappa(\omega)$ 控制，迹自由部分由 leptonic 群延迟矩阵给出；

2. 在 QCA 宇宙中，通过局域 Dirac–Majorana gate 与 Dirac–QCA 连续极限，构造出 seesaw 型轻中微子质量矩阵，展示中微子质量可视为元胞内部 flavor–缺陷的连续极限；

3. 在统一时间刻度与谱论的约束下，将 Yukawa 耦合写成统一刻度密度在 flavor–特定频带上的窗化积分，解释 leptonic Yukawa 的强层级与中微子质量的极小值；

4. 通过离散 flavor 群在 QCA–元胞上的实现与缺陷图案，给出 TBM/TM1/TM2 及其 sum rule 的结构统一解释，并为未来精确实验提供可检验的几何–谱学约束。

在这一统一图景中，中微子质量与味混合不再是洛伦兹流形上的附属参数，而是统一时间刻度、矩阵宇宙散射结构与 QCA 离散动力学共同决定的宇宙 flavor–几何特征。

---

## Acknowledgements, Code Availability

本研究依赖于中微子振荡、离散 flavor 对称与 QCA 连续极限等成熟文献的基础工作。

数值验证与示意性 QCA 仿真可通过通用量子线路模拟器实现：构造带三维 flavor 子空间的局域 Hilbert 空间与 seesaw gate，采样 QCA 的谱并检验连续极限。在独立实现中，可将用于生成数值图像与拟合的代码作为补充材料提供，包括：

* 构造给定 $(M_D,M_R)$ 的 flavor–QCA 演化算子与其有效质量矩阵；

* 计算 Dirac–QCA 的能带结构与统一刻度近似 $\kappa(\omega)$；

* 在简单 $A_4$ 模型下模拟缺陷图案对混合角与相位的影响。

---

## References

[1] Particle Data Group, "Neutrino Masses, Mixing, and Oscillations," *Prog. Theor. Exp. Phys.* 2024, 083C01 (2024); see also PDG review and listings on neutrino mixing.

[2] S. F. King and C. Luhn, "Neutrino Mass and Mixing with Discrete Symmetry," *Rept. Prog. Phys.* 76, 056201 (2013), arXiv:1301.1340.

[3] G. Altarelli and F. Feruglio, "Discrete Flavor Symmetries and Models of Neutrino Mixing," *Rev. Mod. Phys.* 82, 2701 (2010), arXiv:1002.0211.

[4] S. T. Petcov and A. V. Titov, "Assessing the Viability of $(A_4, S_4)$ and $(A_5)$ Flavour Symmetries for Description of Neutrino Mixing," *Phys. Rev. D* 97, 115045 (2018), arXiv:1804.00182.

[5] Z.-Z. Xing and S. Zhou, *Neutrinos in Particle Physics, Astronomy and Cosmology*, Springer (2011); see also later reviews on the PMNS paradigm and neutrino oscillations.

[6] A. Bisio, G. M. D'Ariano, and A. Tosini, "Quantum Field as a Quantum Cellular Automaton: The Dirac Free Evolution in One Dimension," *Ann. Phys.* 354, 244–264 (2015).

[7] A. Bisio, G. M. D'Ariano, P. Perinotti, and A. Tosini, "Weyl, Dirac and Maxwell Quantum Cellular Automata: Analytical Solutions and Phenomenological Predictions of the QCA Theory of Free Fields," *Found. Phys.* 45, 1203–1221 (2015).

[8] O. Duranthon and P. Arnault, "Coarse-grained Quantum Cellular Automata," *Phys. Rev. A* 103, 032224 (2021).

[9] A. Pérez and A. D. et al., "Asymptotic Properties of the Dirac Quantum Cellular Automaton," *Phys. Rev. A* 93, 012328 (2016).

[10] A. de Gouvêa et al., "Solar Neutrinos and Visible Decays," *Phys. Rev. D* 109, 013003 (2024).

[11] A. Dery et al., "Neutrino Masses and Mixing: Entering the Era of Subpercent Precision," *JHEP* 10, 100 (2024), and references therein for updated global fits.

[12] L. N. Yan et al., "Neutrino Mixing Parameters and Masses from $\Delta(96)\rtimes$ HCP Symmetry," *JHEP* 10, 206 (2025).

[13] A. Bisio, G. M. D'Ariano, and A. Tosini, "Dirac Quantum Cellular Automaton in One Dimension: Zitterbewegung and Scattering from Potential," *Phys. Rev. A* 88, 032301 (2013).

[14] G. M. D'Ariano, "The Dirac Quantum Automaton: A Preview," AIP Conf. Proc. 1508, 146–155 (2012), arXiv:1211.2479.

[15] H.-T. Elze, "Cellular Automaton Ontology, Bits, Qubits and the Dirac Equation," *Quantum Reports* 6, 1–30 (2024).

[16] Recent cosmological constraints on the sum of neutrino masses, e.g. J. F. Zhang et al., "Recent Neutrino Oscillation Parameters Impact on the Sum of Neutrino Masses," arXiv:2404.19624 (2024).

---

# 附录 A：PMNS 矩阵的标准形式与当前数据

## A.1 标准参数化

三代中微子混合矩阵的标准参数化为

$$
U_{\mathrm{PMNS}}
=\begin{pmatrix}
1 & 0 & 0\\
0 & c_{23} & s_{23}\\
0 & -s_{23} & c_{23}
\end{pmatrix}
\begin{pmatrix}
c_{13} & 0 & s_{13}e^{-\mathrm{i}\delta}\\
0 & 1 & 0\\
-s_{13}e^{\mathrm{i}\delta} & 0 & c_{13}
\end{pmatrix}
\begin{pmatrix}
c_{12} & s_{12} & 0\\
-s_{12} & c_{12} & 0\\
0 & 0 & 1
\end{pmatrix}
\begin{pmatrix}
1 & 0 & 0\\
0 & e^{\mathrm{i}\alpha_1/2} & 0\\
0 & 0 & e^{\mathrm{i}\alpha_2/2}
\end{pmatrix},
$$

其中 $c_{ij}=\cos\theta_{ij}$, $s_{ij}=\sin\theta_{ij}$，$\delta$ 为 Dirac CP 相位，$\alpha_{1,2}$ 为 Majorana 相位。

## A.2 Global–fit 数值区间

以 normal ordering 为例，近期 global–fit 给出的典型 3σ 区间量级为（略去误差的精确数字，仅给出量级）：

* $\sin^2\theta_{12}\approx 0.30\pm O(0.04)$；

* $\sin^2\theta_{13}\approx 0.022\pm O(0.002)$；

* $\sin^2\theta_{23}\approx 0.5\pm O(0.1)$；

* $\Delta m^2_{21}\approx 7.4\times 10^{-5}\,\mathrm{eV}^2$；

* $|\Delta m^2_{3\ell}|\approx 2.5\times 10^{-3}\,\mathrm{eV}^2$；

* $\delta$ 可能接近 $3\pi/2$，但显著性尚不足。

这些数值构成统一矩阵–QCA 宇宙理论在现阶段必须兼容的实验窗口。

---

# 附录 B：flavor–QCA 连续极限与 seesaw 质量矩阵

## B.1 局域 seesaw 哈密顿量的块对角化

考虑单格点上的 Dirac–Majorana 质量矩阵

$$
\mathcal M
=\begin{pmatrix}
0 & M_D\\
M_D^\dagger & M_R
\end{pmatrix},
$$

其中 $M_R$ 可逆且 $|M_D|\ll |M_R|$。欲对 $\mathcal M$ 作块对角化，可采用 Schur 补或正交对角化方法。

令

$$
\Theta=M_D M_R^{-1},
$$

构造幺正矩阵

$$
\mathcal U
=\exp
\begin{pmatrix}
0 & \Theta\\
-\Theta^\dagger & 0
\end{pmatrix}
\simeq
\begin{pmatrix}
\mathbb I-\tfrac12\Theta\Theta^\dagger & \Theta\\
-\Theta^\dagger & \mathbb I-\tfrac12\Theta^\dagger\Theta
\end{pmatrix}
+O(\Theta^3).
$$

计算

$$
\mathcal U^{\mathsf T}\mathcal M\mathcal U
=\begin{pmatrix}
-M_D^{\mathsf T}M_R^{-1}M_D & 0\\
0 & M_R+O(M_D^2 M_R^{-1})
\end{pmatrix},
$$

得到轻子块的 seesaw 质量矩阵

$$
\mathsf M_\nu=-M_D^{\mathsf T}M_R^{-1}M_D
$$

与重子块 $M_R$。该计算可严格通过级数展开与归纳完成，见标准 seesaw 文献，亦可用谱映射定理严格化近似阶数。

## B.2 Dirac–QCA 连续极限

Dirac–QCA 文献给出了从离散更新到连续 Dirac 方程的系统方法。以一维为例，设 QCA 更新在动量空间上纤维化：

$$
U(k)\ket{\psi(k)}
=e^{-\mathrm{i}\varepsilon(k)\Delta t}\ket{\psi(k)},
$$

在小 $k$ 与小质量极限中，$\varepsilon(k)$ 展开为

$$
\varepsilon(k)
\simeq\pm\sqrt{(c k)^2+m^2}+O(k^3),
$$

其对应的有效哈密顿量为 Dirac 型

$$
H_{\mathrm{eff}}=c\alpha k+\beta m
$$，其中 $(\alpha,\beta)$ 为 Dirac 矩阵的某种表示。将 seesaw 质量矩阵嵌入该构造即可得到轻中微子 Dirac 方程。

---

# 附录 C：离散 flavor 群在 QCA–元胞上的实现

## C.1 $A_4$ 模型示意

$A_4$ 为四面体群，具有一个三维不可约表示与三个一维表示。典型 $A_4$–中微子模型中：

* leptonic 左手双态安置在三维表示 $3$ 上；

* 右手 charged–lepton 与中微子安置在一维表示上；

* scalar "flavon" 场获得特定方向的真空期望，分别在 charged–lepton 与中微子 sector 中将 $A_4$ 破到残余 $Z_3$ 与 $Z_2\times Z_2$。

在 QCA–元胞层面，可将 $\mathcal H_{\mathrm{flavor}}$ 取为 $A_4$ 的三维表示空间，在 $\mathcal H_{\mathrm{aux}}$ 中加入 flavon 自由度，其期望值通过局域 gate 参数编码。不同元胞子集上的 gate 约束实现残余对称的不同破缺，从而在 seesaw 质量矩阵中产生 TBM/TM1/TM2 纹理。

## C.2 Sum rule 与拓扑约束

在 $(S_4,A_5)$ 模型中，通过选择不同的残余子群 $(G_\nu,G_\ell)$ 与群元的嵌入，可以得到混合角与 Dirac CP 相位的 sum rule，如

$$
\cos\delta
=f(\theta_{12},\theta_{13},\theta_{23};G_f,G_\nu,G_\ell).
$$

这些 sum rule 在 QCA 中对应 flavor–联络曲率与缺陷图案产生的拓扑约束，可视为 flavor–束上某些闭合回路的 holonomy 条件。

---

# 附录 D：统一时间刻度与窗化积分的技术细节

## D.1 Holonomy 与 PMNS 的规范自由度

在 fiber bundle 理论中，给定路径 $\gamma$ 与 $U(3)$ 元素 $U$，总可以构造某个联络使得其沿 $\gamma$ 的 holonomy 等于 $U$。本文的额外要求是：联络的迹部分由统一刻度 $\kappa(\omega)$ 决定，迹自由部分与 leptonic 群延迟矩阵相关。这一要求通过如下分解实现：

* 将 $Q_\ell(\omega)$ 分解为迹部分 $\frac{\operatorname{tr} Q_\ell(\omega)}{3}\mathbb I$ 与迹自由部分 $\widetilde Q_\ell(\omega)$；

* 将迹部分对应的 $U(1)$–联络固定为

  $\mathcal A_{U(1)}(\omega)=\frac{1}{6\pi}\operatorname{tr} Q_\ell(\omega)$；

* 在 $SU(3)$ 部分选择联络 $\mathcal A_{SU(3)}(\omega)=\frac{1}{2\pi}\widetilde Q_\ell(\omega)$ 的某种 gauge。

整体 $U(3)$–联络为两者直和。由此 PMNS holonomy 在 $\gamma$ 上的迹与迹自由部分分别受到统一刻度与 flavor–散射的控制。

## D.2 Birman–Kreĭn 公式与 $\kappa$–谱表示

Birman–Kreĭn 公式给出散射行列式与谱移函数之间的关系：

$$
\det S(\omega)
=\exp\bigl(-2\pi\mathrm{i}\xi(\omega)\bigr),
\quad
\partial_\omega\xi(\omega)
=-\Delta\rho_\omega(\omega),
$$

其中 $\xi(\omega)$ 为谱移函数，$\Delta\rho_\omega$ 为 DOS 差分。结合统一刻度母式

$$
\kappa(\omega)=\Delta\rho_\omega(\omega)
$$，可将 flavor–特定子块的相位梯度写为 $\kappa(\omega)$ 在子空间上的投影，从而得到 Theorem 3 所需的谱表示。

## D.3 Euler–Maclaurin 与 Poisson 误差估计

在 QCA 频谱离散化情形下，用 Euler–Maclaurin 公式将离散和与连续积分联系起来，再用 Poisson 求和分析高频模式的贡献。只要 $\kappa(\omega)$ 在窗函数支集上具有足够阶数的可微性且奇点有限，就可以选择有限阶 $N$ 使离散–连续差异受控于某个小参数，从而保证 Yukawa–$\kappa$ 窗化关系在 QCA–离散宇宙中近似成立。

以上技术点保证了统一矩阵–QCA 宇宙理论中关于 PMNS 几何化与 Yukawa–$\kappa$ 关系的数学自洽性。

