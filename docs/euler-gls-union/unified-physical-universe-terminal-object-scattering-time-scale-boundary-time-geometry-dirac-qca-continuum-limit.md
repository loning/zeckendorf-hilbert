# 统一物理宇宙终对象：散射时间刻度、边界时间几何与 Dirac–QCA 连续极限

**Version: 2.7**

## Abstract

本文在散射谱理论、广义相对论的边界 Hamilton 形式、量子 Null 能量条件（quantum null energy condition, QNEC）以及 Dirac 型量子元胞自动机（quantum cellular automaton, QCA）的连续极限研究基础上，引入一个以统一时间刻度为核心的"物理宇宙终对象"结构。

在标准可追踪扰动与波算子完备的散射设定下，利用 Birman–Kreĭn 公式与 Eisenbud–Wigner–Smith 理论，证明存在一个几乎处处唯一的刻度密度函数

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=-\xi'(\omega),
$$

其中 $\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$。将"散射总相位导数 $\varphi'(\omega)$""谱移函数导数/相对态密度 $\rho_{\mathrm{rel}}(\omega)$"与 Wigner–Smith 群延迟矩阵迹 $\operatorname{tr}Q(\omega)$ 统一为单一时间刻度母尺 $\kappa$。

当能谱不含连续部分（如反射型 AdS 背景）时，上述等式仅以**分布**形式保留 $\kappa(\omega)=-\xi'(\omega)$，不再使用 $S(\omega)$、$Q(\omega)$ 与相位导数表述。

在引力与量子场论侧，本文选择四维渐近 AdS 的 Einstein 引力与其对偶的大 $N$ 共形场论这一具体背景类。在 Brown–York 准局域能量与 Hamilton–Jacobi 边界形式以及基于相对熵形变的 QNEC 与 holographic QNEC 结果基础上，引入一个明确假设：边界 Hamilton 量沿 null 形变的二阶变分可表示为广义熵 $S_{\rm gen}$ 二阶形变的配权积分。证明在该假设及一个谱–几何对应存在的条件下，可以选择刻度规范使边界时间函数 $\tau$ 的重标度刚性锁定到同一 $\kappa(\omega)$，从而在边界时间几何中得到刻度函数 $\kappa_{\mathrm{geo}}(\omega)=\kappa(\omega)$。

在离散宇宙侧，本文考虑 Dirac 型 QCA，将 split-step 量子行走及其高维推广作为具体模型族。在适当局域性和平滑性假设下，利用 Dirac 连续极限与有限阶 Euler–Maclaurin–Poisson 公式，证明包含有限散射区的 Dirac–QCA 的离散 Wigner–Smith 群延迟迹在长波极限中收敛到同一 $\kappa(\omega)$，并在一维 split-step 模型上给出幂次误差上界，从而在 $a,\Delta t\to 0$ 极限下定义离散刻度 $\kappa_{\mathrm{QCA}}(\omega)=\kappa(\omega)$。

上述三层结构在一个以 Grothendieck 宇宙控制大小的 2–范畴 $\mathbf{Univ}_\kappa$ 中被统一：对象为携带统一刻度的"物理宇宙对象"，1–态射为刻度保持的结构态射，2–态射为相应自然同构。**在此基础上，并在 $\mathbf{Univ}_\kappa$ 为（2,1）–范畴且具 smallness 与 2–（弱）极限，以及存在对象 $\mathfrak{U}_\ast$ 具备：对任意对象存在唯一（至 2–同构）刻度保持 1–态射入射之泛性质的附加范畴假设下，本文得到条件性结果：$\mathfrak{U}_\ast$ 为终对象。**

在模型应用部分，本文分别在 Minkowski 真空、渐近 AdS 黑洞散射及一维 Dirac–QCA 玩具模型上具体重建刻度函数 $\kappa(\omega)$，展示统一时间刻度如何将黑洞群延迟、边界熵流与离散时间步长联系起来。在工程方案部分，提出在微波/声学散射实验与量子行走/离子阱平台中实现部分刻度结构的可行路径，并讨论统一刻度在这些平台上的数值验证方式。

## Keywords

统一时间刻度；谱移函数；Wigner–Smith 群延迟；Birman–Kreĭn 公式；Brown–York 准局域能量；量子 Null 能量条件（QNEC）；边界时间几何；Dirac 量子元胞自动机（QCA）；连续极限；2–范畴终对象

---

## 1 Introduction & Historical Context

### 1.1 时间刻度的散射、几何与离散起源

在散射谱理论中，对于 trace-class 扰动与波算子完备的自伴算子对 $(H,H_0)$，Birman–Kreĭn 理论引入谱移函数 $\xi(\omega)$ 以刻画含相互作用哈密顿量 $H$ 相对自由哈密顿量 $H_0$ 的谱变化，并给出

$$
\det S(\omega)
=\exp(-2\pi\mathrm{i}\,\xi(\omega)),
$$

其中 $S(\omega)$ 为能量纤维上的散射矩阵。$\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$；其中 $\xi'$ 可由 resolvent 迹差给出，$\rho_{\mathrm{rel}}$ 亦可由 $S$ 矩阵或 $Q$ 的迹给出。

Eisenbud–Wigner 与 Smith 将散射相位对能量的导数解释为时间延迟，引入 Wigner–Smith 群延迟矩阵

$$
Q(\omega)
=-\mathrm{i}\,S(\omega)^\dagger\partial_\omega S(\omega),
$$

其迹给出"总时间延迟"，并通过 trace 公式与谱移函数导数关联。

在广义相对论中，Brown–York 基于 Einstein–Hilbert 作用与 Gibbons–Hawking–York 边界项的 Hamilton–Jacobi 分析，定义了准局域能量与边界 Hamilton 面电荷，表明在适当边界条件下，类时边界上的时间平移矢量场与准局域能量密度共轭。

量子 Null 能量条件（QNEC）则在量子场论中给出沿 null 方向的能流 $\langle T_{kk}\rangle$ 与广义熵 $S_{\rm gen}$ 二阶形变之间的不等式关系。Bousso 等在自由及可控相互作用的场论中给出了严格证明，Koeller–Leichenauer 在大 $N$ holographic CFT 中给出了 holographic 证明。

另一方面，量子元胞自动机与离散时间量子行走为在离散时空上构造幺正演化提供了自然平台。Mallick 与 Chandrashekar 以及后续工作表明，一维 split-step 量子行走的长波极限收敛到 Dirac 方程，并在适当条件下可构造出 Dirac 型 QCA；后续研究将该框架推广到 higher-dimensional QCA 与自由费米场的离散实现。

这些理论分别给出了时间刻度的散射谱、引力边界与离散演化刻画，但三者在形式上彼此独立。本文的目标是在一个统一的数学结构中，将这三类时间刻度强制对齐到一个单一刻度密度母尺 $\kappa(\omega)$。

### 1.2 统一时间刻度与终对象图景

本文的核心思想是：将

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=-\xi'(\omega)
$$

视为统一时间刻度母尺，并在三个层级上强制对齐：

1. **散射侧**：$\kappa(\omega)$ 来自 Birman–Kreĭn 谱移函数与 Wigner–Smith 群延迟的标准等式；

2. **边界时间几何侧**：在 4D 渐近 AdS + 大 $N$ holographic CFT 背景类中，在 Brown–York 准局域能量与 QNEC 兼容性假设下，通过谱–几何对应将边界时间函数重标度到同一 $\kappa(\omega)$；

3. **Dirac–QCA 侧**：在 Dirac–QCA 模型上，通过连续极限与 Euler–Maclaurin–Poisson 估计，将离散 Wigner–Smith 群延迟迹的能量依赖收敛到同一 $\kappa(\omega)$。

在此基础上，引入一个以统一刻度为核心的"物理宇宙对象"，并在 **§3.4 的条件性结果**（存在具唯一入射态射泛性质的对象）下，构造满足终对象普适性质的对象 $\mathfrak{U}_\ast$。

---

## 2 Model & Assumptions

### 2.1 散射时间刻度母式

设 $\mathcal{H}$ 为可分 Hilbert 空间，$H_0$ 与 $H$ 为自伴算子，满足：

1. $H_0$ 具有纯绝对连续谱；

2. $V:=H-H_0$ 为 trace–class 扰动；

3. Møller 波算子

   $$
   \Omega^\pm
   =\mathrm{s}\text{-}\lim_{t\to\pm\infty}
   \mathrm{e}^{\mathrm{i}Ht}\mathrm{e}^{-\mathrm{i}H_0t}
   $$

   存在且完备。

散射算子

$$
S=(\Omega^+)^\dagger\Omega^-
$$

在 $H_0$ 的绝对连续谱上纤维分解为

$$
S=\int^\oplus S(\omega)\,\mathrm{d}\mu(\omega),
$$

其中 $\omega$ 为能量，$\mu$ 为谱测度。

定义散射行列式

$$
\det S(\omega)=\exp(2\mathrm{i}\,\varphi(\omega)),
$$

谱移函数 $\xi(\omega)$ 满足 Birman–Kreĭn 公式

$$
\det S(\omega)
=\exp(-2\pi\mathrm{i}\,\xi(\omega))。
$$

$\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$；其中 $\xi'$ 可由 resolvent 迹差给出，$\rho_{\mathrm{rel}}$ 亦可由 $S$ 矩阵或 $Q$ 的迹给出。定义 Wigner–Smith 群延迟矩阵

$$
Q(\omega)
=-\mathrm{i}\,S(\omega)^\dagger\partial_\omega S(\omega)。
$$

由 $\det S(\omega)=\exp(-2\pi\mathrm{i}\,\xi(\omega))$ 与 $Q(\omega)=-\mathrm{i}\,S(\omega)^\dagger\partial_\omega S(\omega)$ 可得

$$
\operatorname{tr}Q(\omega)
=-\mathrm{i}\partial_\omega\log\det S(\omega)
=2\partial_\omega\varphi(\omega)
=-2\pi\xi'(\omega)。
$$

统一时间刻度密度定义为

$$
\kappa(\omega)
:=\frac{\varphi'(\omega)}{\pi}
:=\rho_{\mathrm{rel}}(\omega)
:=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
:=-\xi'(\omega)\quad(\text{a.e.}).
$$

这一等式在 Lebesgue 绝大多数能量点上成立。

**注**：本节等式在 $H_0$ 具纯绝对连续谱、$V$ 为 trace–class 扰动且波算子完备的设定下，于几乎处处的能量点成立。对无连续谱或纯点谱的体系（例如反射型边界条件下的 AdS 几何），仅谱移函数 $\xi$ 及其**分布意义**的导数 $-\xi'$ 有意义；此时统一刻度定义为 $\kappa:=-\xi'$（按分布理解），不再引入 $S(\omega)$、$Q(\omega)$ 与 $\varphi(\omega)$。

### 2.2 渐近 AdS 背景类与边界时间几何假设

引力与量子场论侧的背景类选取为：

* 四维渐近 AdS 的 Einstein 引力 $(M,g)$，**非全局双曲**；其无穷远边界 $\partial M$ 为**类时**。**引力侧**采用固定边界度规（Dirichlet 型）并配合 holographic counterterms，使 Brown–York 面电荷与 Hamilton–Jacobi 变分良定；**线性/探测场**可在 $\partial M$ 处施加使对应动力学算子自伴的反射型（如 Dirichlet/Robin）边界条件。

* 边界上存在三维诱导度规 $\gamma_{ab}$ 与一族类空截面 $B_\lambda$，$\lambda$ 为沿某 null 方向的形变参数；

* **在 $\partial M$ 上存在大 $N$ 共形场论（边界 CFT）**，与 bulk Einstein 引力满足 AdS/CFT 对偶。

Brown–York 准局域能量与 Hamilton–Jacobi 分析提供边界 Hamilton 面电荷的系统定义。

QNEC 在多种量子场论背景下已被证明，在 holographic CFT 中的版本适用于大 $N$ 极限下具有 Einstein 引力对偶的情形。

**假设 2.1（边界 Hamilton 量与广义熵形变的匹配）**

在上述背景类中，存在一族类空截面 $B_\lambda$ 及边界时间函数 $\tau$，使得边界 Hamilton 量 $H_{\partial M}[\tau]$ 沿 $\lambda$ 的二阶变分可写为

$$
\partial_\lambda^2 H_{\partial M}[\tau]
=\int_{B_\lambda} f(\lambda,\mathbf{x})
\,\partial_\lambda^2 S_{\rm gen}(\lambda,\mathbf{x})\,\mathrm{d}\Sigma,
$$

其中 $f(\lambda,\mathbf{x})$ 为**局域有界可测的配权函数（允许取符号）**，典型选取为 $f(\lambda,\mathbf{x})=\kappa(\omega(\lambda,\mathbf{x}))$，$S_{\rm gen}(\lambda,\mathbf{x})$ 为以 $\mathbf{x}\in B_\lambda$ 标记的广义熵密度或 coarse–grained 熵密度。

谱–几何对应通过 AdS/CFT 中的模式展开或模 Hamiltonian 的谱来实现：边界模 Hamiltonian 的本征频率 $\omega_n$ 与 bulk normal mode 的频率对应，从而在小形变极限下，将 entangling cut 的形变模式 $(\lambda,\mathbf{x})$ 映射到一个能量窗口中的 $\omega(\lambda,\mathbf{x})$。这一对应在 holographic relative entropy 与 modular flow 的研究中已有具体实现途径。

### 2.3 Dirac–QCA 模型与连续极限假设

QCA 侧考虑定义在格点 $\Lambda=\mathbb{Z}^d$ 上的可逆 QCA。局域 Hilbert 空间记为 $\mathcal{H}_{\mathrm{cell}}$，全局空间为无限张量积

$$
\mathcal{H}
=\bigotimes_{x\in\Lambda}\mathcal{H}_{\mathrm{cell}},
$$

演化由具有有限传播半径 $R$ 的幺正算子 $U:\mathcal{H}\to\mathcal{H}$ 给出，满足空间齐次性与因果局域性。

一维 Dirac 型 QCA 选取 split-step 形式：$\Lambda=\mathbb{Z}$、$\mathcal{H}_{\mathrm{cell}}=\mathbb{C}^2$，

$$
U(a,\Delta t;\theta_1,\theta_2)
=S_+C(\theta_2)S_-C(\theta_1),
$$

其中 $C(\theta)=\exp(-\mathrm{i}\theta\,\sigma_y)$，$S_\pm$ 为条件平移算子，$a$ 为格点间距，$\Delta t$ 为时间步长。已有结果表明，在适当缩放下，$U(a,\Delta t;\theta_1,\theta_2)$ 的长波极限收敛到 Dirac 方程的时间演化算子。

在有限散射区 $\Lambda_{\mathrm{scat}}\subset\Lambda$ 内改变 coin 角度或引入局域幺正扰动，其余区域保持自由演化，对每个准能量 $\varepsilon$ 可构造散射矩阵 $S_{\mathrm{QCA}}(\varepsilon)$，定义离散 Wigner–Smith 矩阵

$$
Q_{\mathrm{QCA}}(\varepsilon)
=-\mathrm{i}\,S_{\mathrm{QCA}}(\varepsilon)^\dagger
\partial_\varepsilon S_{\mathrm{QCA}}(\varepsilon)。
$$

**假设 2.2（Dirac–QCA 连续极限与散射刻度）**

1. 存在从准能量 $\varepsilon$ 到连续能量 $\omega$ 的缩放 $\varepsilon=\varepsilon(\omega,a,\Delta t)$，以及有效哈密顿量 $H_{\mathrm{eff}}(k)$，使得

   $$
   U(a,\Delta t;\theta_1,\theta_2)
   =\exp(-\mathrm{i}H_{\mathrm{eff}}\Delta t)
   +\mathcal{O}(\Delta t^2),
   $$

   且 $H_{\mathrm{eff}}$ 在长波极限下收敛到带势 Dirac 哈密顿量；

2. 对每个能量窗口 $\omega\in I$ 与势配置类 $\mathcal{V}$，存在正整数 $p,q$ 与常数 $C_1(I,\mathcal{V}),C_2(I,\mathcal{V})$，使得

   $$
   \left|
   \frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{QCA}}(\varepsilon(\omega,a,\Delta t))
   -\frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{Dirac}}(\omega)
   \right|
   \le C_1 a^{p}+C_2 \Delta t^{q},
   $$

   其中 $Q_{\mathrm{Dirac}}(\omega)$ 为连续 Dirac 散射的 Wigner–Smith 矩阵；

3. $C_1,C_2$ 仅依赖于散射区长度、coin 角度及有效势的有限阶导数界。

### 2.4 物理宇宙对象与统一刻度 2–范畴

**定义 2.3（物理宇宙对象）**

物理宇宙对象是一个 13 元组

$$
\mathfrak{U}_{\mathrm{phys}}
=(U_{\mathrm{evt}},U_{\mathrm{geo}},U_{\mathrm{meas}},U_{\mathrm{QFT}},
U_{\mathrm{scat}},U_{\mathrm{mod}},U_{\mathrm{ent}},U_{\mathrm{obs}},
U_{\mathrm{cat}},U_{\mathrm{comp}},U_{\mathrm{BTG}},U_{\mathrm{QCA}},U_{\mathrm{top}})
$$

满足：

1. $U_{\mathrm{evt}}$：事件集合与因果偏序；

2. $U_{\mathrm{geo}}$：带边界的洛伦兹流形 $(M,g,\partial M)$；

3. $U_{\mathrm{meas}}$：测量装置与实验配置；

4. $U_{\mathrm{QFT}}$：体与边界上的局域代数网及其态；

5. $U_{\mathrm{scat}}$：**散射系统** $(H,H_0,\xi(\omega),\kappa_{\mathrm{scat}}(\omega);[S(\omega),Q(\omega)]_{\text{当且仅当 a.c. 谱存在}})$，其中在绝对连续谱且波算子完备时

  $$
  \kappa_{\mathrm{scat}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)=\frac{\varphi'(\omega)}{\pi}=-\xi'(\omega)\quad\text{（a.e.）},
  $$

  若含纯点/无连续谱，则统一刻度以**分布**形式定义为 $\kappa_{\mathrm{scat}}:=-\xi'$，此时不使用 $S(\omega),Q(\omega),\varphi(\omega)$。

6. $U_{\mathrm{mod}}$：模流与 KMS 结构；

7. $U_{\mathrm{ent}}$：熵与相对熵函数族；

8. $U_{\mathrm{obs}}$：观察者世界线与其可访问代数；

9. $U_{\mathrm{cat}}$：将上述结构封装为范畴对象与函子；

10. $U_{\mathrm{comp}}$：**可计算结构**（量子电路模型、复杂度与可计算性断言、编码/解码映射），**不含 QCA 动力学本体**；

11. $U_{\mathrm{BTG}}$：边界时间几何 $(\partial M,\gamma_{ab},\tau,\kappa_{\mathrm{geo}})$，满足假设 2.1；

12. $U_{\mathrm{QCA}}$：**Dirac–QCA 模型** $(\Lambda,\mathcal{H}_{\mathrm{cell}},U,\kappa_{\mathrm{QCA}})$，满足假设 2.2，用于刻度对齐与连续极限分析。

13. $U_{\mathrm{top}}$：全局拓扑与 $K$ 理论不变量。

三元组

$$
(U_{\mathrm{scat}},U_{\mathrm{BTG}},U_{\mathrm{QCA}})
$$

称为该对象的核心时间对齐层。

**定义 2.4（统一刻度 2–范畴 $\mathbf{Univ}_\kappa$）**

固定一个 Grothendieck 宇宙 $\mathcal{U}$，使得上述所有 Hilbert 空间、流形、代数与范畴都是 $\mathcal{U}$–small。定义 2–范畴 $\mathbf{Univ}_\kappa$：

* 对象：带统一刻度 $\kappa$ 的物理宇宙对象 $\mathfrak{U}_{\mathrm{phys}}$，其核心时间层满足

  $$
  \kappa_{\mathrm{scat}}(\omega)
  =\kappa_{\mathrm{geo}}(\omega)
  =\kappa_{\mathrm{QCA}}(\omega)
  =\kappa(\omega)；
  $$

* 1–态射：从 $\mathfrak{U}$ 到 $\mathfrak{V}$ 的**刻度保持结构态射** $F$。为避免歧义，本文约定：每个对象通过 $U_{\mathrm{cat}}$ 封装为内部（2,1）–范畴，因此 $F$ 可等价视为该封装上的 **pseudofunctor**；在事件与因果层面为因果同态，在局域代数层面为 $(*)$–同态，并在核心时间层满足

  $$
  F^\ast\kappa_{\mathfrak{V}}(\omega)=\kappa_{\mathfrak{U}}(\omega)\quad\text{（于绝对连续谱处为 a.e. 等式；含纯点/混合谱时按分布意义成立）}。
  $$

  若仅把对象看作裸的 13 元组，则 1–态射理解为相同约束下的结构保持映射，并与上述 pseudofunctor 通过 $U_{\mathrm{cat}}$ 等价。

* 2–态射：1–态射之间的自然同构，允许在散射侧相差整数倍 $2\pi$ 的相位重标度，在几何侧相差边界坐标变换，在 QCA 侧相差局域酉变换及有限 coarse–graining。

---

## 3 Main Results (Theorems and Alignments)

### 3.1 散射时间刻度的三重等价

**定理 3.1（统一散射时间刻度）**

在第 2.1 节散射设定下，存在一个（a.e. 唯一）的 Borel 可测函数 $\kappa(\omega)$，使得在 Lebesgue 绝大多数能量点上成立

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=-\xi'(\omega).
$$

其中 $\det S(\omega)=\exp(2\mathrm{i}\,\varphi(\omega))$，$\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$，$Q(\omega)=-\mathrm{i}\,S(\omega)^\dagger\partial_\omega S(\omega)$。

这是散射谱理论中关于谱移函数与时间延迟的标准结论。

### 3.2 边界时间几何中的刻度同一（条件性命题）

**命题 3.2（假设 2.1 下的边界时间刻度统一）**

在第 2.2 节给出的四维渐近 AdS Einstein 背景与大 $N$ holographic CFT 背景类中，**若假设 2.1 成立，且该假设中的配权函数满足**

$$
f(\lambda,\mathbf{x})=\kappa(\omega(\lambda,\mathbf{x})),
$$

并存在谱–几何对应 $(\lambda,\mathbf{x})\mapsto\omega(\lambda,\mathbf{x})$，则存在边界时间函数族

$$
\tau_\kappa(\lambda,\mathbf{x})
=\int^{\omega(\lambda,\mathbf{x})}
\kappa(\tilde{\omega})\,\mathrm{d}\tilde{\omega},
$$

其中 $\kappa(\omega)$ 为定理 3.1 中由散射侧定义的统一刻度。由上述前提直接得到边界 Hamilton 量沿 null 形变的二阶变分可写为

$$
\partial_\lambda^2 H_{\partial M}[\tau_\kappa]
=\int_{B_\lambda}
\kappa(\omega(\lambda,\mathbf{x}))
\,\partial_\lambda^2 S_{\rm gen}(\lambda,\mathbf{x})\,\mathrm{d}\Sigma。
$$

在 QNEC 饱和或近似饱和的极限中，可得到边界时间几何中的刻度函数满足

$$
\kappa_{\mathrm{geo}}(\omega)=\kappa(\omega)。
$$

该命题是在假设 2.1、配权函数满足 $f(\lambda,\mathbf{x})=\kappa(\omega(\lambda,\mathbf{x}))$ 及谱–几何对应存在的条件下成立的条件性结构结果。

### 3.3 Dirac–QCA 连续极限与刻度收敛

**推论 3.3（由假设 2.2 与定理 3.1）**

在第 2.3 节 Dirac–QCA 模型设定与**假设 2.2**下，由假设 2.2(2) 的误差上界以及定理 3.1 的统一刻度等式，**直接得到**：对给定能量窗口 $I$ 与势配置类 $\mathcal{V}$，存在 $p,q\ge 1$ 与常数 $C_1(I,\mathcal{V}),C_2(I,\mathcal{V})$，使得对所有 $\omega\in I$ 有

$$
\left|
\frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{QCA}}(\varepsilon(\omega,a,\Delta t))
-\kappa(\omega)
\right|
\le C_1(I,\mathcal{V})\,a^{p}
+C_2(I,\mathcal{V})\,\Delta t^{q},
$$

其中 $\kappa(\omega)$ 为定理 3.1 中的统一刻度。因而在 $a,\Delta t\to 0$ 极限下，可以定义

$$
\kappa_{\mathrm{QCA}}(\omega)
:=\lim_{a,\Delta t\to 0}
\frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{QCA}}(\varepsilon(\omega,a,\Delta t))
=\kappa(\omega),
$$

并可将 QCA 时间步长映射为连续时间参数

$$
t(\omega)
=\int^{\omega}\kappa(\tilde{\omega})\,\mathrm{d}\tilde{\omega}。
$$

在一维 split-step Dirac–QCA 的具体模型中，可进一步得到下述命题。

**命题 3.3.1（一维 split-step QCA 的误差估计）**

考虑一维 split-step QCA，散射区长度为 $L=Na$，coin 角度函数在散射区内属于 $C^{2r}$ 类。对能量窗口 $I$ 中的每个 $\omega$，存在整数 $r\ge 1$ 与常数 $C(I,L,\lVert\partial^k\theta_i\rVert_\infty)$，使得

$$
\left|
\frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{QCA}}(\varepsilon(\omega,a,\Delta t))
-\kappa(\omega)
\right|
\le C(I,L,\lVert\partial^k\theta_i\rVert_\infty)
\,a^{2r-1}
+\mathcal{O}(\Delta t^{q}),
$$

其中 $q$ 由有效哈密顿量近似的阶数决定。

### 3.4 统一物理宇宙终对象（泛性质刻画，条件性）

**命题 3.4（终对象的泛性质刻画）**

在第 2 节设定下，若 $\mathbf{Univ}_\kappa$ 为（2,1）–范畴且具有所需的小性与 2–（弱）极限，并存在对象 $\mathfrak{U}_\ast$ 满足：对任意对象 $\mathfrak{V}$，存在唯一（至 2–同构）刻度保持 1–态射 $F_{\mathfrak{V}}:\mathfrak{V}\to\mathfrak{U}_\ast$，则 $\mathfrak{U}_\ast$ 为 $\mathbf{Univ}_\kappa$ 的终对象。

---

## 4 Proofs

### 4.1 定理 3.1 的证明

由谱移函数的 trace 公式，对光滑紧支撑的 $f$ 有

$$
\operatorname{Tr}(f(H)-f(H_0))
=\int_{-\infty}^{+\infty} f'(\omega)\,\xi(\omega)\,\mathrm{d}\omega。
$$

取 $f(\lambda)=(\lambda-z)^{-1}$ 可得到 resolvent 迹差表示，从而定义 $\xi'(\omega)$。Birman–Kreĭn 公式给出

$$
\det S(\omega)
=\exp(-2\pi\mathrm{i}\,\xi(\omega))。
$$

对数求导得到

$$
\partial_\omega\log\det S(\omega)
=-2\pi\mathrm{i}\,\xi'(\omega)。
$$

另一方面，

$$
\partial_\omega\log\det S(\omega)
=\operatorname{tr}\big(S(\omega)^{-1}\partial_\omega S(\omega)\big)
=\operatorname{tr}\big(S(\omega)^\dagger\partial_\omega S(\omega)\big)。
$$

由

$$
Q(\omega)
=-\mathrm{i}\,S(\omega)^\dagger\partial_\omega S(\omega)
$$

得到

$$
\operatorname{tr}Q(\omega)
=-\mathrm{i}\operatorname{tr}\big(S(\omega)^\dagger\partial_\omega S(\omega)\big)
=-\mathrm{i}\partial_\omega\log\det S(\omega)
=-2\pi\,\xi'(\omega)。
$$

又由 $\det S(\omega)=\exp(2\mathrm{i}\,\varphi(\omega))$ 可得

$$
\partial_\omega\log\det S(\omega)
=2\mathrm{i}\,\varphi'(\omega)，
$$

从而

$$
\operatorname{tr}Q(\omega)=2\,\varphi'(\omega)。
$$

于是

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=-\xi'(\omega),
$$

定理得证。

### 4.2 命题 3.2 的证明概要

在 Einstein–Hilbert 作用加 Gibbons–Hawking–York 边界项下，固定边界度规的变分给出 Brown–York 准局域应力张量

$$
T^{ab}_{\mathrm{BY}}
=\frac{2}{\sqrt{\lvert h\rvert}}
\frac{\delta I}{\delta h_{ab}}
=\frac{1}{8\pi G}(K^{ab}-Kh^{ab})
+(\text{参照项})。
$$

选择边界上的时间向量场 $t^a$，进行 ADM 分解，可得到 Hamilton 面电荷

$$
H_{\partial M}[t]
=\int_{B_t}\big(N\,\epsilon - N^a j_a\big)\,\mathrm{d}\Sigma，
$$

$\epsilon,j_a$ 为能量与动量密度，$N,N^a$ 为 lapse 与 shift。

在 holographic CFT 中，对 entangling cut 沿 null 方向的形变，QNEC 给出

$$
\langle T_{kk}(\lambda)\rangle
\ge \frac{1}{2\pi}\partial_\lambda^2 S_{\rm gen}(\lambda)。
$$

在形状导数与相对熵框架下，熵二阶形变可通过能流与模 Hamiltonian 的变分表达。

在假设 2.1 中，若配权函数满足 $f(\lambda,\mathbf{x})=\kappa(\omega(\lambda,\mathbf{x}))$，则 Brown–York Hamilton 量二阶变分可写为广义熵二阶形变的配权积分。引入谱–几何对应 $(\lambda,\mathbf{x})\mapsto\omega(\lambda,\mathbf{x})$ 与统一刻度 $\kappa(\omega)$，定义

$$
\tau_\kappa(\lambda,\mathbf{x})
=\int^{\omega(\lambda,\mathbf{x})}
\kappa(\tilde{\omega})\,\mathrm{d}\tilde{\omega}。
$$

在 QNEC 饱和或近饱和条件下，由上述前提直接得到

$$
\partial_\lambda^2 H_{\partial M}[\tau_\kappa]
=\int_{B_\lambda}
\kappa(\omega(\lambda,\mathbf{x}))
\,\partial_\lambda^2 S_{\rm gen}(\lambda,\mathbf{x})\,\mathrm{d}\Sigma，
$$

从而在边界时间几何中定义 $\kappa_{\mathrm{geo}}(\omega)=\kappa(\omega)$，命题得证。

### 4.3 推论 3.3 与命题 3.3.1 的依据

**推论 3.3 的依据** 由**假设 2.2(2)** 与定理 3.1 **直接推出**；命题 3.3.1 的误差估计继续使用 split-step QCA 的显式色散与 Euler–Maclaurin–Poisson 余项控制。

对一维 split-step QCA，动量空间中单步演化算子可写为

$$
U(k)
=S_+(k)C(\theta_2)S_-(k)C(\theta_1)，
$$

本征值 $\mathrm{e}^{-\mathrm{i}\varepsilon(k)\Delta t}$ 满足

$$
\cos(\varepsilon(k)\Delta t)
=\cos\theta_1\cos\theta_2\cos(ka)
-\sin\theta_1\sin\theta_2。
$$

在小 $k,a,\theta_i$ 极限下，$\varepsilon(k)\approx\pm\sqrt{k^2+m^2}$，对应一维 Dirac 哈密顿量。

对有限散射区的 QCA 构型，可通过传输矩阵方法构造散射矩阵 $S_{\mathrm{QCA}}(\varepsilon)$，定义

$$
\operatorname{tr}Q_{\mathrm{QCA}}(\varepsilon)
=2\,\partial_\varepsilon\varphi_{\mathrm{QCA}}(\varepsilon)，
$$

其中 $\varphi_{\mathrm{QCA}}(\varepsilon)$ 为 QCA 散射行列式相位。

将离散动量求和

$$
\sum_{k\in\mathrm{BZ}} f(k)
$$

用 Euler–Maclaurin 公式近似为积分并控制余项，再结合 Poisson 求和公式，可得到

$$
\frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{QCA}}(\varepsilon(\omega,a,\Delta t))
=\frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{Dirac}}(\omega)
+\mathcal{O}(a^{p})+\mathcal{O}(\Delta t^{q})，
$$

其中 $\frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{Dirac}}(\omega)=\kappa(\omega)$。这直接推出推论 3.3。若角度函数属于 $C^{2r}$ 类，则余项可进一步细化为 $a^{2r-1}$ 阶，得到命题 3.3.1。

### 4.4 命题 3.4 的说明

**说明 4.4（标准化过程与泛性质）**

定义标准化函子 $N$ 将对象重写到刻度一致的规范形式：在散射层将谱移函数、相位与群延迟重写为满足定理 3.1 的统一刻度形式；在边界时间几何层将时间函数重标度为 $\tau_\kappa$，满足命题 3.2；在 QCA 层将时间步长与准能量拓扑重标度，使其满足推论 3.3。标准化过程在态射上对应于刻度保持条件下的规范变换，构成 2–函子 $N:\mathbf{Univ}_\kappa\to\mathbf{Univ}_\kappa$。

若存在对象 $\mathfrak{U}_\ast$，使得对任意对象 $\mathfrak{V}$，由 $\mathfrak{V}\to N(\mathfrak{V})$ 的规范态射与 $N(\mathfrak{V})\to\mathfrak{U}_\ast$ 的唯一（至 2–同构）态射复合得到 $\mathfrak{V}\to\mathfrak{U}_\ast$ 的唯一（至 2–同构）态射，则由命题 3.4 可知 $\mathfrak{U}_\ast$ 为终对象。若存在另一对象 $\mathfrak{U}'_\ast$ 也满足该泛性质，则从 $\mathfrak{U}_\ast$ 到 $\mathfrak{U}'_\ast$ 与反向态射的组合与各自恒等态射 2–同构，从而二者在 2–范畴意义下等价。

---

## 5 Model Apply

### 5.1 Minkowski 真空

四维 Minkowski 时空中，取 $H_0=H$ 为自由哈密顿量，则散射矩阵 $S(\omega)=\mathbb{I}$，谱移函数 $\xi(\omega)=0$，统一刻度 $\kappa(\omega)=0$。Brown–York 准局域能量为零，引力边界 Hamilton 量退化为参照背景项。Dirac–QCA 侧选取不含散射区的自由 QCA，其散射矩阵平凡，离散 Wigner–Smith 矩阵迹为零，故 $\kappa_{\mathrm{QCA}}(\omega)=0$。

这一情形对应于无散射、无曲率的完全对称背景，统一时间刻度退化为零函数。

### 5.2 渐近 AdS 黑洞外部区域

考虑四维渐近 AdS 的 Schwarzschild–AdS 黑洞外部区域。由于存在地平线，体系以**准正则模（QNM）**的**复频谱**为主；因此标准意义上的"到无穷远散射相位"及实频离散本征谱表述**不直接适用**。在四维球对称背景下，**标量场**（$s=0$）的角动量简并度为 $(2\ell+1)$，因此

$$
\kappa(\omega)=-\sum_{\ell=0}^{\infty}(2\ell+1)\xi'_{\ell}(\omega),
$$

其中在每个角动量通道 $\ell$ 上，本文以**实频 resolvent 边界值**定义相对于参照背景的谱移函数 $\xi_\ell(\omega)$。对于**具有自旋的场**，通道应以**总角动量** $j$ 为标签，简并度为 $(2j+1)$。例如 **Dirac（$s=\tfrac12$）** 情形中，部分波由 $j=\ell\pm\tfrac12$（亦可用 Dirac 的 $\kappa$ 量子数）标记，统一刻度的分布形式应写为

$$
\kappa(\omega)=-\sum_{j}(2j+1)\xi'_{j}(\omega),
$$

而**不应**将自旋简并简单地与 $(2\ell+1)$ 因式分解为 $(2\ell+1)(2s+1)$。上述按 $j$ 的计数与 Wigner–Smith 时间延迟与态密度的标准对应 $\operatorname{Tr}Q=2\,\partial_E\delta_{\rm sum}$、$\rho=(2\pi)^{-1}\operatorname{Tr}Q$ 一致。其奇点结构由 QNM 极点数据控制。若将无穷远边界改为**吸收/透明条件**或外接耗散浴以恢复**连续谱极限**，则 $\kappa(\omega)$ 的分布弱收敛为几乎处处定义的函数，并可再次写成

$$
\kappa(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)=\frac{\varphi'(\omega)}{\pi}.
$$

在边界时间几何侧，选取靠近无穷远的类时边界 $\partial M$，在其上定义 Brown–York 准局域能量与 Hamilton 量。AdS/CFT 对偶下，边界 CFT 的能量谱与体内散射模式谱对应，null 截面 $B_\lambda$ 的形变参数 $\lambda$ 可与 entangling cut 的形变模式及模 Hamiltonian 本征频率关联。利用 holographic QNEC 与相对熵形变结果，可将边界 Hamilton 量的形变重写为广义熵二阶形变的配权积分，从而按命题 3.2 将 $\tau_\kappa$ 与 $\kappa(\omega)$ 关联。

在 Dirac–QCA 侧，可构造一个在有限区域内模拟黑洞有效势的 QCA：在一维格点上引入空间依赖的 coin 角度或散射单元阵列，使其连续极限在有效势层面近似黑洞外部散射。通过数值计算 QCA 的 $S_{\mathrm{QCA}}(\varepsilon)$ 与 $Q_{\mathrm{QCA}}(\varepsilon)$，可以检验统一刻度 $\kappa_{\mathrm{QCA}}(\omega)$ 与连续 Dirac 散射刻度 $\kappa(\omega)$ 之间的误差收敛。

### 5.3 一维 Dirac–QCA 玩具模型

考虑一维 split-step Dirac–QCA，散射区为长度 $L=Na$ 的势垒，外侧为自由 QCA。对每个准能量 $\varepsilon$，可通过传输矩阵明确计算散射矩阵 $S_{\mathrm{QCA}}(\varepsilon)$，再求

$$
Q_{\mathrm{QCA}}(\varepsilon)
=-\mathrm{i}\,S_{\mathrm{QCA}}(\varepsilon)^\dagger
\partial_\varepsilon S_{\mathrm{QCA}}(\varepsilon)。
$$

数值上选取能量窗口 $I$，对不同格点间距 $a$ 与时间步长 $\Delta t$ 计算

$$
\Delta\kappa(\omega;a,\Delta t)
=\frac{1}{2\pi}\operatorname{tr}Q_{\mathrm{QCA}}(\varepsilon(\omega,a,\Delta t))
-\kappa(\omega),
$$

拟合其对 $a,\Delta t$ 的幂次依赖，检验命题 3.3.1 中给出的 $a^{2r-1}$ 与 $\Delta t^q$ 误差律。

---

## 6 Engineering Proposals

### 6.1 微波与声学散射平台

在微波腔与声学散射系统中，可以测量多通道散射矩阵 $S(\omega)$，通过数值微分得到 Wigner–Smith 矩阵 $Q(\omega)$ 及统一刻度 $\kappa(\omega)$。通过设计介质结构或障碍物阵列以模拟黑洞势垒，可在实验平台上观测到与引力散射类似的群延迟结构，从而在实验上重构统一刻度的谱形。

### 6.2 量子行走与 QCA 平台

在 trapped-ion 与超导量子比特平台上，split-step 量子行走与 Dirac–QCA 已被实现。

在这些平台上可以通过以下步骤实现部分统一刻度结构：

1. 实现含有限散射区的 Dirac–QCA 序列；

2. 利用相干散射相位测量或过程层析重建 $S_{\mathrm{QCA}}(\varepsilon)$；

3. 对准能量求导得到 $Q_{\mathrm{QCA}}(\varepsilon)$ 与 $\kappa_{\mathrm{QCA}}(\omega)$，通过改变 $a,\Delta t$ 验证刻度的连续极限；

4. 对比实验测得的 $\kappa_{\mathrm{QCA}}(\omega)$ 与连续 Dirac 模型的 $\kappa(\omega)$，检验推论 3.3 预言。

### 6.3 张量网络与 holographic 量子模拟

在 AdS/CFT 启发的张量网络与 holographic 量子模拟中，可以构造 entangling cut 的离散形变，测量局域熵与能流，并验证 QNEC 及其 Rényi 版本。在这些平台上，可尝试将统一刻度 $\kappa(\omega)$ 作为边界时间形变参数与 Hamilton 生成元之间的重标度因子，在数值模拟中重建边界 Hamilton 量形变与广义熵形变之间的关系，间接检验命题 3.2 的结构预言。

---

## 7 Discussion (risks, boundaries, past work)

散射侧的刻度同一完全扎根于成熟的谱移函数与时间延迟理论，适用于大量 Schrödinger 型与 Dirac 型散射系统。边界时间几何侧的命题 3.2 是在特定背景类与 Hamilton–熵匹配假设下的条件性结果，适用范围主要限于具有良好 holographic 对偶的渐近 AdS 背景。Dirac–QCA 部分在一维与部分高维模型上具备严格的连续极限证明，但在一般多通道高维系统中给出显式的 Euler–Maclaurin–Poisson 误差界仍具有技术挑战。

范畴层面的命题 3.4 为**条件性结果**：除 smallness 与 2–（弱）极限外，还需存在具唯一入射态射泛性质的对象这一附加假设，方可得到终对象结论。

统一物理宇宙终对象框架为连接黑洞热力学、宇宙学常数、量子混沌与多观察者信息几何提供了结构起点。未来工作可以在包含规范场与完整标准模型散射的设定中推广统一刻度结构，并在非 AdS 背景下通过数值相对熵与 QNEC 检验边界刻度同一的适用性。

---

## 8 Conclusion

本文在散射谱理论、边界时间几何与 Dirac–QCA 连续极限之间建立了一条统一时间刻度主线，并在统一刻度条件下，在附加范畴假设下得到条件性结论：存在具有终对象性质的物理宇宙对象。

散射侧的 Birman–Kreĭn 与 Wigner–Smith 理论给出

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=-\xi'(\omega),
$$

其中 $\rho_{\mathrm{rel}}(\omega)=-\xi'(\omega)$。这一刻度母式为时间的统一提供了谱论基础。在渐近 AdS + holographic CFT 背景类中，在 Brown–York 准局域 Hamilton 量与 QNEC 兼容性假设及谱–几何对应存在的条件下，可以将边界时间函数的形变重标度到同一刻度 $\kappa(\omega)$。在 Dirac–QCA 侧，通过连续极限与 Euler–Maclaurin–Poisson 估计证明离散 Wigner–Smith 群延迟迹在长波极限中收敛到同一刻度，从而在离散宇宙模型中实现统一时间刻度。

在范畴层面，本文将满足统一刻度条件的散射–边界–QCA 宇宙模型组织为 2–范畴 $\mathbf{Univ}_\kappa$，并在 smallness 与 2–（弱）极限**及**存在具唯一入射态射泛性质的对象这一**附加范畴假设**下，得到**条件性**结论：存在满足终对象普适性质的对象 $\mathfrak{U}_\ast$。这一对象可被视为在统一时间刻度下物理宇宙结构的极大一致实现，将散射相位、边界熵、离散时间步长等量统一到单一刻度母尺之下。

---

## Acknowledgements, Code Availability

本文所使用的散射谱理论、Brown–York 准局域能量、QNEC 与 Dirac–QCA 连续极限等理论工具均基于相关领域的成熟研究。数值层面，可为一维 Dirac–QCA 散射玩具模型、Wigner–Smith 矩阵重建与 Euler–Maclaurin–Poisson 误差估计提供参考代码，用于重构统一刻度 $\kappa(\omega)$ 并在不同参数下进行可视化，这些代码可与完整技术附录一并提供。

---

## Appendix A: Scattering Time Scale and Spectral Shift

本附录补充定理 3.1 所需的标准谱理论背景。

### A.1 谱移函数与 trace 公式

设 $V:=H-H_0$ 为 trace–class 扰动。对足够光滑的测试函数 $f$，定义

$$
\operatorname{Tr}(f(H)-f(H_0))
=\int_{-\infty}^{+\infty} f'(\omega)\,\xi(\omega)\,\mathrm{d}\omega。
$$

取 $f(\lambda)=(\lambda-z)^{-1}$ 可将 $f(H)-f(H_0)$ 表示为 resolvent 的 Cauchy 积分，从而得到

$$
\xi'(\omega)
=-\frac{1}{\pi}\Im\operatorname{Tr}\Big((H-\omega-\mathrm{i}0)^{-1}
-(H_0-\omega-\mathrm{i}0)^{-1}\Big)。
$$

### A.2 Birman–Kreĭn 公式

在 trace–class 扰动假设下，散射算子可表示为某个 Fredholm 行列式的边界值。Birman–Kreĭn 公式给出

$$
\det S(\omega)
=\exp(-2\pi\mathrm{i}\,\xi(\omega))。
$$

对数求导得到

$$
\partial_\omega\log\det S(\omega)
=-2\pi\mathrm{i}\,\xi'(\omega)。
$$

### A.3 Wigner–Smith 矩阵与统一刻度

在纤维上定义

$$
Q(\omega)
=-\mathrm{i}\,S(\omega)^\dagger\partial_\omega S(\omega)，
$$

则

$$
\operatorname{tr}Q(\omega)
=-\mathrm{i}\operatorname{tr}(S(\omega)^\dagger\partial_\omega S(\omega))
=-\mathrm{i}\partial_\omega\log\det S(\omega)
=-2\pi\,\xi'(\omega)。
$$

再由 $\det S(\omega)=\exp(2\mathrm{i}\,\varphi(\omega))$ 得

$$
\operatorname{tr}Q(\omega)=2\,\varphi'(\omega)。
$$

从而

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=-\xi'(\omega)。
$$

---

## Appendix B: Boundary Time Geometry and QNEC

### B.1 Brown–York 准局域 Hamilton 量

在 Einstein–Hilbert 作用

$$
I[g]
=\frac{1}{16\pi G}\int_M R\sqrt{-g}\,\mathrm{d}^4x
+\frac{1}{8\pi G}\int_{\partial M} K\sqrt{\lvert h\rvert}\,\mathrm{d}^3x
$$

加 Gibbons–Hawking–York 边界项下，对固定边界度规 $h_{ab}$ 变分，得到 Brown–York 准局域应力张量

$$
T^{ab}_{\mathrm{BY}}
=\frac{2}{\sqrt{\lvert h\rvert}}
\frac{\delta I}{\delta h_{ab}}
=\frac{1}{8\pi G}(K^{ab}-Kh^{ab})+(\text{参照项})。
$$

选择边界上的时间向量场 $t^a$ 并进行 ADM 分解，可得到 Hamilton 面电荷

$$
H_{\partial M}[t]
=\int_{B_t}\big(N\,\epsilon - N^a j_a\big)\,\mathrm{d}\Sigma。
$$

### B.2 QNEC 与广义熵形变

在 holographic CFT 或满足 QNEC 的场论中，对 entangling cut 沿 null 方向的形变，广义熵 $S_{\rm gen}(\lambda)$ 的二阶导数与应力张量满足

$$
\langle T_{kk}(\lambda)\rangle
\ge \frac{1}{2\pi}\partial_\lambda^2 S_{\rm gen}(\lambda)。
$$

在 AdS/CFT 框架中，Koeller–Leichenauer 利用极小面与 Raychaudhuri 方程的几何性质给出 holographic QNEC 的证明。

### B.3 谱–几何对应的典型构造

在渐近 AdS 背景中，边界 CFT 的模 Hamiltonian $K$ 的谱与 bulk normal modes 的频率谱对应。通过 boundary-to-bulk Green 函数，将 entangling cut 的形变模式展开到能量基，可构造 $(\lambda,\mathbf{x})\mapsto\omega(\lambda,\mathbf{x})$。在小形变与给定能量窗口下，这一映射在局域上可逆。

在这一谱–几何对应下，定义

$$
\tau_\kappa(\lambda,\mathbf{x})
=\int^{\omega(\lambda,\mathbf{x})}
\kappa(\tilde{\omega})\,\mathrm{d}\tilde{\omega}，
$$

结合假设 2.1 与 QNEC，可得到命题 3.2 的刻度同一。

---

## Appendix C: Dirac–QCA Continuum Limit and Euler–Maclaurin Estimates

### C.1 split-step QCA 的色散关系

一维 split-step QCA 的动量空间单步演化算子

$$
U(k)
=S_+(k)C(\theta_2)S_-(k)C(\theta_1)
$$

的本征值为 $\mathrm{e}^{-\mathrm{i}\varepsilon(k)\Delta t}$，满足

$$
\cos(\varepsilon(k)\Delta t)
=\cos\theta_1\cos\theta_2\cos(ka)
-\sin\theta_1\sin\theta_2。
$$

在小 $k,a,\theta_i$ 极限下展开，可得到 Dirac 型色散关系 $\varepsilon(k)\approx\pm\sqrt{k^2+m^2}$。

### C.2 散射矩阵与离散群延迟

在有限区间 $[-L,L]$ 内改变 coin 角度，构造势垒散射。通过匹配自由区与散射区的 Bloch 波，可得到散射矩阵 $S_{\mathrm{QCA}}(\varepsilon)$ 的显式表达。对其行列式求导得到相位 $\varphi_{\mathrm{QCA}}(\varepsilon)$ 的导数，定义

$$
\operatorname{tr}Q_{\mathrm{QCA}}(\varepsilon)
=2\,\partial_\varepsilon\varphi_{\mathrm{QCA}}(\varepsilon)。
$$

### C.3 Euler–Maclaurin–Poisson 误差估计

对动量求和

$$
\sum_{k\in\mathrm{BZ}} f(k)
$$

使用 Euler–Maclaurin 公式

$$
\sum_{n=n_0}^{n_1} f(nh)
=\frac{1}{h}\int_{n_0h}^{n_1h} f(x)\,\mathrm{d}x
+\frac{f(n_0h)+f(n_1h)}{2}
+\sum_{r=1}^{p}
\frac{B_{2r}}{(2r)!}h^{2r-1}
\big(f^{(2r-1)}(n_1h)-f^{(2r-1)}(n_0h)\big)
+R_p,
$$

其中 $B_{2r}$ 为 Bernoulli 数。由 Euler–Maclaurin 公式，若 $f\in C^{2p}$，则余项满足 $|R_p|\le C h^{2p}$。因而

$$
\sum_{n=n_0}^{n_1} f(nh)=\frac{1}{h}\int_{n_0h}^{n_1h} f(x)\,\mathrm{d}x+\frac{f(n_0h)+f(n_1h)}{2}+\sum_{r=1}^{p}\frac{B_{2r}}{(2r)!}h^{2r-1}\left(f^{(2r-1)}(n_1h)-f^{(2r-1)}(n_0h)\right)+R_p,
$$

结合 Poisson 求和公式可控制高频贡献；**若** $f$ 及其所有奇阶导在端点消失**或** $f$ 按 BZ 作周期延拓使边界与低阶 Bernoulli 校正项为零，则有

$$
\sum_{k\in\mathrm{BZ}} f(k)=\frac{1}{h}\int f(x)\,\mathrm{d}x+\mathcal{O}(h^{2p})。
$$

上式用于估计 QCA–Dirac 差异时，可与能量导数与势的正则性假设共同给出 §3.3 与命题 3.3.1 所需的幂次上界。

---

## Appendix D: Categorical Construction of the Final Object

### D.1 标准化函子

对每个对象 $\mathfrak{U}\in\mathbf{Univ}_\kappa$，定义标准化函子

$$
N:\mathfrak{U}\mapsto\widehat{\mathfrak{U}}
$$

如下：

1. 在散射层，利用定理 3.1 的刻度母式重定义谱移函数、相位与群延迟；

2. 在边界时间几何层，用 $\tau_\kappa$ 替换原有时间函数；

3. 在 QCA 层，将时间步长与准能量拓扑重标度，使其满足推论 3.3。

这一过程在态射上对应于统一刻度保持下的规范变换，构成 2–函子 $N:\mathbf{Univ}_\kappa\to\mathbf{Univ}_\kappa$。

### D.2 终对象的泛性质刻画（条件性）

若存在对象 $\mathfrak{U}_\ast$ 满足：对任意对象 $\mathfrak{V}$，存在唯一（至 2–同构）刻度保持 1–态射 $\mathfrak{V}\to\mathfrak{U}_\ast$，则由命题 3.4 可知 $\mathfrak{U}_\ast$ 为 $\mathbf{Univ}_\kappa$ 的 2–终对象。若另有对象亦满足该泛性质，则两者在 2–范畴意义下等价。

---

## References

[1] M. Sh. Birman and M. G. Kreĭn, "On the theory of wave operators and scattering operators," Soviet Math. Dokl. 3, 740–744 (1962).

[2] A. Pushnitski, "The spectral shift function and the invariance principle," J. Funct. Anal. 183, 269–320 (2001).

[3] H. Neidhardt, "Scattering matrix and spectral shift of the pair of operators $(H_0,H)$," J. Math. Phys. 29, 1959–1973 (1988).

[4] J. D. Brown and J. W. York, "Quasilocal energy and conserved charges derived from the gravitational action," Phys. Rev. D 47, 1407–1419 (1993).

[5] S. Bose and N. Dadhich, "Brown–York quasilocal energy, gravitational charge, and black hole horizons," Phys. Rev. D 60, 064010 (1999).

[6] R. Bousso, Z. Fisher, J. Koeller, S. Leichenauer and A. C. Wall, "Proof of the Quantum Null Energy Condition," Phys. Rev. D 93, 024017 (2016).

[7] J. Koeller and S. Leichenauer, "Holographic proof of the quantum null energy condition," Phys. Rev. D 94, 024026 (2016).

[8] T. A. Malik and R. Lopez-Mobilia, "Proof of the quantum null energy condition for free fermionic field theories," Phys. Rev. D 101, 066028 (2020).

[9] T. Farrelly, "A review of quantum cellular automata," Quantum 4, 368 (2020).

[10] A. Mallick and C. M. Chandrashekar, "Dirac quantum cellular automaton from split-step quantum walk," Sci. Rep. 6, 25779 (2016).

[11] L. Mlodinow and T. A. Brun, "Quantum field theory from a quantum cellular automaton in one spatial dimension and a no-go theorem in higher dimensions," Phys. Rev. A 102, 042211 (2020).

[12] C. H. Alderete et al., "Quantum walks and Dirac cellular automata on a programmable trapped-ion quantum computer," Nat. Commun. 11, 3720 (2020).

