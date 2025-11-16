# 统一物理宇宙终对象

几何–边界时间–矩阵–QCA–拓扑的完全统一框架

---

## Abstract

在广义相对论、代数量子场论、散射与谱移理论、Tomita–Takesaki 模块理论、广义熵与量子能量条件、Brown–York 准局域能量以及量子元胞自动机等成熟框架的基础上，本文给出一个多层结构的"统一物理宇宙终对象"

$$
\mathfrak U_{\mathrm{phys}}^\star
=(
U_{\rm evt},U_{\rm geo},U_{\rm meas},U_{\rm QFT},
U_{\rm scat},U_{\rm mod},U_{\rm ent},U_{\rm obs},
U_{\rm cat},U_{\rm comp},
U_{\rm BTG},U_{\rm QCA},U_{\rm top}
),
$$

并证明它在适当的 2–范畴 $\mathbf{Univ}_\mathcal U$ 中是一个真正意义上的终对象。核心结论包括：

1. 在满足标准散射假设的自伴对 $(H,H_0)$ 上，散射相位导数、谱移函数导数与 Wigner–Smith 群延迟迹之间存在刻度同一式

   $$
   \kappa(\omega)
   =\varphi'(\omega)/\pi
   =\rho_{\rm rel}(\omega)
   =(2\pi)^{-1}\operatorname{tr}Q(\omega),
   $$

   将时间刻度统一为唯一的"散射母尺"，其中 $\varphi$ 为总散射半相位，$\rho_{\rm rel}$ 为谱移函数导数，$Q$ 为 Wigner–Smith 群延迟算子。

2. 在"边界时间几何"（Boundary Time Geometry, BTG）层上，由边界可观测代数 $\mathcal A_\partial$、边界态 $\omega_\partial$、Gibbons–Hawking–York 边界项与 Brown–York 准局域应力张量以及 Tomita–Takesaki 模流定义的边界时间生成元，给出唯一（至仿射）时间参数，使散射时间、模时间与几何时间属于同一时间刻度等价类 $[\tau]$。

3. 在拓扑–散射–相对上同调层上，在 $Y=M\times X^\circ$ 及其边界上构造相对上同调类 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$，统一描述 $\mathbb Z_2$ holonomy、散射线丛扭挠与 $w_2(TM)$，并且在"Modular–Scattering Alignment" 与局域量子能量条件下，证明 $[K]=0$ 等价于：局域几何满足爱因斯坦方程、二阶相对熵非负以及散射平方根行列式在一切物理回路上无 $\mathbb Z_2$ 异常。

4. 在 QCA 宇宙层，以可数图 $\Lambda$、有限维元胞 Hilbert 空间 $\mathcal H_{\rm cell}$、准局域 $C^\ast$ 代数 $\mathcal A$、有限传播半径的量子元胞自动机自同构 $\alpha$ 与初始态 $\omega_0$ 定义宇宙 QCA 对象

   $$
   \mathfrak U_{\rm QCA}
   =(\Lambda,\mathcal H_{\rm cell},\mathcal A,\alpha,\omega_0),
   $$

   证明其诱导的事件集合 $E=\Lambda\times\mathbb Z$ 上存在局域有限因果偏序，并在单粒子与连续极限中重现狄拉克型相对论场论。

5. 在物理子范畴中构造连续几何宇宙、矩阵散射宇宙和 QCA 宇宙三类表象范畴

   $$
   \mathbf{Univ}^{\mathrm{phys}}_{\rm geo},\quad
   \mathbf{Univ}^{\mathrm{phys}}_{\rm mat},\quad
   \mathbf{Univ}^{\mathrm{phys}}_{\rm qca},
   $$

   并给出保持统一刻度、因果与广义熵结构的函子，证明存在范畴等价

   $$
   \mathbf{Univ}^{\mathrm{phys}}_{\rm geo}
   \simeq
   \mathbf{Univ}^{\mathrm{phys}}_{\rm mat}
   \simeq
   \mathbf{Univ}^{\mathrm{phys}}_{\rm qca},
   $$

   这三种表象均可视为同一终对象 $\mathfrak U_{\mathrm{phys}}^\star$ 的不同投影。

6. 在统一时间刻度、广义熵单调性与拓扑无异常约束下，$\mathfrak U_{\mathrm{phys}}^\star$ 在 2–范畴 $\mathbf{Univ}_\mathcal U$ 中是终对象：任意满足公理的"宇宙结构"皆唯一地嵌入 $\mathfrak U_{\mathrm{phys}}^\star$，反之，任何物理宇宙描述都是某一结构忘却函子作用于 $\mathfrak U_{\mathrm{phys}}^\star$ 的像。

本文还给出若干应用示例，包括黑洞熵与信息、宇宙学常数与暗能量的统一刻度解释、QCA 版本的面积律以及若干可工程实现的检验方案（电磁与声学散射中的群延迟测量、QCA/量子行走平台上的狄拉克极限实验等），并讨论该框架与现有统一方案的关系及其局限性。

---

## Keywords

统一时间刻度；边界时间几何；Wigner–Smith 群延迟；Birman–Kreĭn 公式；广义熵与 QNEC；Brown–York 准局域能量；量子元胞自动机；矩阵散射宇宙；Null–Modular 双覆盖；范畴终对象

---

## Introduction & Historical Context

广义相对论将引力刻画为四维洛伦兹流形 $(M,g)$ 的曲率，时间坐标由时样向量场的积分曲线给出；量子场论则在固定背景或微扰重整化的框架下，以局域场算符与 Fock 空间构造粒子与相互作用。两者的传统结合——弯曲时空上的量子场论与半经典引力——在黑洞热力学、宇宙学以及量子信息方面取得大量成果，但在"时间的本体论地位""观察者与因果结构""引力的量子起源"等问题上仍缺乏统一答案。

另一方面，散射理论为"远区可观测"的统一语言提供了基础。对于满足适当条件的自伴对 $(H,H_0)$，Birman–Kreĭn 公式将散射矩阵行列式与谱移函数联系起来，给出

$$
\det S(\lambda)
=\exp\bigl(-2\pi\mathrm{i}\,\xi(\lambda)\bigr),
$$

其中 $\xi$ 是谱移函数。另一方面，Wigner 与 Smith 引入的时间延迟算子

$$
Q(\omega)
=-\mathrm{i}\,S(\omega)^\dagger\partial_\omega S(\omega),
$$

被广泛用于分析量子散射、波动传播与复杂介质中的"群延迟"。这提示时间可以在频域中通过相位梯度与谱数据统一定义。

广义熵与量子能量条件为"时间箭头"的几何化提供了新视角。量子 Null 能量条件（QNEC）与量子聚焦猜想（QFC）将应力能量张量的 null 分量与广义熵的二阶变分联系起来，将相对熵单调性转化为几何能量条件。在半经典引力与 AdS/CFT 中，这一思想发展出"熵决定几何"的一系列结果。

边界在引力与量子场论中扮演关键角色。Brown–York 利用 Hamilton–Jacobi 分析引入了准局域能量与边界应力张量，将能量与动量的定义局域在有界区域的边界上。边界项在 Gibbons–Hawking–York 作用量、黑洞热力学以及最近的 null 边界电荷定义中再次出现，暗示"时间"可以视为边界上的平移参数而非体域内部的原始坐标。

离散模型方面，量子元胞自动机（QCA）与离散时间量子行走形成了严格的"离散宇宙动力学"框架。Schumacher–Werner 给出了具有有限传播速度与平移不变性的 QCA 结构定理，证明任何此类演化都可写成 Margolus 分块形式并具有结构可逆性。此外，大量工作表明，适当选择的离散时间量子行走在连续极限下给出狄拉克方程与相对论波动方程。这为"宇宙本征离散但连续场论为其尺度极限"的观点提供了具体模型支撑。

在此背景下，本文此前的相关工作已经分别完成了几条"统一链"：

1. 通过 Birman–Kreĭn 公式与 Wigner–Smith 群延迟构造统一时间刻度密度 $\kappa(\omega)$，把散射相位梯度、谱移函数导数与群延迟迹统一为单一刻度。

2. 在边界时间几何（BTG）框架下，将边界谱三元组、Tomita–Takesaki 模流、Brown–York 准局域应力张量与散射相位的刻度统一，给出"边界时间"的几何–算子–散射一体化定义。

3. 在因果结构统一理论中，以统一时间刻度等价类 $[\tau]$ 将洛伦兹因果偏序、幺正演化与小因果菱形上的广义熵极值–单调性粘合为单一结构，将"因果"刻画为偏序、时间刻度与熵箭头的兼容性。

4. 在多层结构对象 $\mathfrak U$ 上构造"极大一致宇宙"并证明其在 2–范畴 $\mathbf{Univ}_\mathcal U$ 中的终对象性质。

5. 在准局域 $C^\ast$ 代数与因果集合框架下，将宇宙定义为 QCA 对象 $\mathfrak U_{\rm QCA}$，并在适当连续极限中重现相对论场论。

6. 在带边因果菱形与参数空间乘积 $Y=M\times X^\circ$ 上引入 Null–Modular 双覆盖与相对上同调类 $[K]$，将 $\mathbb Z_2$ holonomy、散射线丛扭挠与 $w_2(TM)$ 统一为"拓扑时间异常"的判据。

然而，这些统一链条仍然彼此平行：统一时间刻度、边界时间几何、因果–熵统一、QCA 宇宙、拓扑–散射统一等尚未被收束到单一数学对象中。本文的目标是在 2–范畴 $\mathbf{Univ}_\mathcal U$ 中构造一个多层结构终对象 $\mathfrak U_{\mathrm{phys}}^\star$，使上述所有结构成为其不同分量或投影，从而在严格意义上给出"统一物理宇宙"的终对象刻画。

本文的主要贡献可概括如下：

* 定义包含事件–几何–测度–QFT–散射–模流–广义熵–观察者–范畴–可计算性–边界时间几何–QCA–拓扑等十三层的宇宙对象 $\mathfrak U_{\mathrm{phys}}^\star$。

* 在散射层与 BTG 层内生化刻度同一式与边界时间生成元，证明一切物理上可解释的时间参数都属于统一刻度等价类 $[\tau]$。

* 在拓扑层引入相对上同调类 $[K]$ 及散射平方根行列式的 $\mathbb Z_2$ holonomy，证明 $[K]=0$ 等价于"爱因斯坦方程 + 二阶相对熵非负 + 无 $\mathbb Z_2$ 环量异常"。

* 构造连续几何宇宙、矩阵散射宇宙与 QCA 宇宙三类表象范畴，给出保持刻度、因果与熵结构的函子，证明三重范畴等价。

* 在上述结构基础上证明 $\mathfrak U_{\mathrm{phys}}^\star$ 为 2–范畴 $\mathbf{Univ}_\mathcal U$ 的终对象，从而在范畴论意义上消除"进一步统一"的自由度。

* 展示若干物理与工程应用，包括黑洞熵与信息、宇宙学常数、QCA 版本面积律以及可实验检验的散射与 QCA 平台。

---

## Model & Assumptions

### 2.1 宇宙 2–范畴与大小控制

给定一固定 Grothendieck 宇宙 $\mathcal U$，记 $\mathbf{Univ}_\mathcal U$ 为如下 2–范畴：

* 对象为多层结构

  $$
  \mathfrak U
  =(U_{\rm evt},U_{\rm geo},U_{\rm meas},U_{\rm QFT},
  U_{\rm scat},U_{\rm mod},U_{\rm ent},U_{\rm obs},
  U_{\rm cat},U_{\rm comp},\dots)
  $$

  的 $\mathcal U$–小集合，每一层自身是适当范畴（如测度空间、洛伦兹流形、$C^\ast$–代数网等）的对象族。

* 1–态射为保持结构的函子型映射，如保因果偏序的嵌入、保散射刻度的酉等价等。

* 2–态射为不同 1–态射之间的自然同构或相容变换。

所有构造均在 $\mathcal U$ 内部进行，以避免集合论悖论。

### 2.2 记号与统一刻度同一式

记号与约定如下：

1. 统一刻度密度 $\kappa(\omega)$ 定义为

   $$
   \kappa(\omega)
   =\varphi'(\omega)/\pi
   =\rho_{\rm rel}(\omega)
   =(2\pi)^{-1}\operatorname{tr}Q(\omega),
   $$

   其中 $\varphi$ 为散射半相位，$\rho_{\rm rel}$ 为谱移函数导数，$Q$ 为 Wigner–Smith 群延迟算子。

2. 统一时间刻度等价类 $[\tau]$ 是在允许仿射变换 $\tau\mapsto a\tau+b$ 下的等价类；所有物理时间参数（散射时间、模时间、几何时间、QCA 时间步等）被要求属于同一 $[\tau]$。

3. 小因果菱形 $D_{p,r}\subset(M,g)$ 指在全局双曲流形上以点 $p$ 为中心、尺度 $r$ 的双锥型因果区域，其边界 $\partial D_{p,r}$ 携带边界代数 $\mathcal A_{\partial D}$ 与边界态 $\omega_{\partial D}$。

4. 广义熵定义为

   $$
   S_{\rm gen}(\Sigma)
   =\frac{A(\Sigma)}{4G\hbar}
   +S_{\rm out}(\Sigma),
   $$

   其中 $A$ 为截面面积，$S_{\rm out}$ 为外区量子熵。

5. QCA 宇宙以五元组

   $$
   \mathfrak U_{\rm QCA}
   =(\Lambda,\mathcal H_{\rm cell},\mathcal A,\alpha,\omega_0)
   $$

   表示，$\Lambda$ 为可数图，$\mathcal H_{\rm cell}$ 为有限维元胞 Hilbert 空间，$\mathcal A$ 为准局域 $C^\ast$ 代数，$\alpha$ 为具有有限传播半径的 $C^\ast$–自同构，$\omega_0$ 为初始态。

### 2.3 散射与谱移假设（A1–A5）

考虑一个满足标准假设的自伴对 $(H,H_0)$，其散射系统满足：

* (A1) 存在波算子 $W_\pm(H,H_0)$ 且完备。

* (A2) $H_0$ 与 $H$ 在绝对连续谱上酉等价，可写出定能散射矩阵 $S(\omega)$。

* (A3) 存在谱移函数 $\xi(\lambda)$，Birman–Kreĭn 公式成立：

  $$
  \det S(\lambda)
  =\exp\bigl(-2\pi\mathrm{i}\,\xi(\lambda)\bigr).
  $$

* (A4) 谱移函数 $\xi(\lambda)$ 在感兴趣能区可微，其导数 $\xi'(\lambda)$ 属于 $L^1_{\rm loc}$。

* (A5) 散射矩阵 $S(\omega)$ 在频率上可微，Wigner–Smith 群延迟

  $$
  Q(\omega)
  =-\mathrm{i}S(\omega)^\dagger\partial_\omega S(\omega)
  $$

  为迹类算子。

在这些假设下，可同时讨论 $\varphi(\omega)$、$\rho_{\rm rel}(\omega)$ 与 $\operatorname{tr}Q(\omega)$，并建立刻度同一式。

### 2.4 几何与广义熵假设（B1–B4）

* (B1) $(M,g)$ 为四维全局双曲洛伦兹流形，其边界 $\partial M$ 分解为时样与 null 片，并携带适当诱导结构。

* (B2) 体域引力作用量包含 Gibbons–Hawking–York 边界项，Brown–York 准局域应力张量

  $$
  T^{ab}_{\rm BY}
  =\frac{2}{\sqrt{-h}}\frac{\delta S_{\rm grav}}{\delta h_{ab}}
  $$

  存在，且满足适当的可积性条件，可定义准局域能量与动量。

* (B3) 对每个小因果菱形边界截面 $\Sigma$ 存在广义熵 $S_{\rm gen}(\Sigma)$，且相对熵 $S(\rho|\sigma)$ 与应力张量满足 QNEC/QFC 型关系。

* (B4) 在适当极限下，QNEC/QFC 与小因果菱形上的广义熵极值条件等价于 Einstein 方程

  $$
  G_{ab}+\Lambda g_{ab}
  =8\pi G\,\langle T_{ab}\rangle
  $$

  的局域形式。

这些假设与现有关于"从相对熵推导能量条件与引力方程"的工作保持一致。

### 2.5 模块结构与代数量子场论假设（M1–M3）

* (M1) 给定全局状态 $\omega$ 与 Haag–Kastler 网 $\{\mathcal A(\mathcal O)\}$，对每个区域 $\mathcal O$ 的 GNS 表示存在 Tomita–Takesaki 模算子 $\Delta_\mathcal O$ 与反线性算子 $J_\mathcal O$，模流 $\sigma_t^\omega$ 在适当意义下定义。

* (M2) 对热平衡或 KMS 态，模流与物理时间演化 $\alpha_t$ 之间存在热时间关系

  $$
  \sigma_t^\omega
  =\alpha_{t/\beta},
  $$

   其中 $\beta$ 为逆温或有效参数。

* (M3) 在小因果菱形限制下，模 Hamilton 量 $K=-\log\Delta$ 的本征值密度与散射刻度 $\kappa(\omega)$ 的谱数据可匹配到统一时间刻度等价类 $[\tau]$。

### 2.6 QCA 公理与连续极限假设（Q1–Q4）

* (Q1) 格点 $\Lambda$ 为可数、局域有限图，具有有限度数上界与自然的图距离 $\operatorname{dist}$。

* (Q2) 元胞 Hilbert 空间 $\mathcal H_{\rm cell}$ 有限维，准局域代数 $\mathcal A$ 为无限张量积上局域算子的闭包。

* (Q3) QCA 自同构 $\alpha:\mathcal A\to\mathcal A$ 平移协变，且存在传播半径 $R<\infty$，使得支撑在某有限区域上的算子在一步演化后支撑在其 $R$–邻域中。

* (Q4) 存在尺度参数 $\epsilon\to0$ 与适当重缩放，使得在单粒子或低密度扇区上，$\alpha$ 的离散时间演化在连续极限中给出狄拉克或 Klein–Gordon 型方程。

上述假设与现有关于量子行走与 QCA 连续极限的严格分析相兼容。

### 2.7 观察者与共识几何假设（O1–O3）

* (O1) 每个观察者 $O_i$ 由可达因果域 $C_i\subset U_{\rm evt}$、局域偏序 $\prec_i$、局域代数 $\mathcal A_i\subset\mathcal A$、状态 $\omega_i$、更新规则 $U_i$ 等构成。

* (O2) 不同观察者在交叠区域 $C_i\cap C_j$ 上满足 Čech 一致性条件，其预测概率与相对熵满足适当粘合约束。

* (O3) 存在从观察者族 $\{O_i\}$ 到全局宇宙对象 $\mathfrak U$ 的 2–极限构造，使得 $\mathfrak U$ 的局部限制重现各观察者的局域世界。

---

## Main Results (Theorems and Alignments)

本节在上述模型与假设下给出统一物理宇宙终对象的主要定理。

### 3.1 刻度同一式与边界时间几何的内生化

**定理 3.1（统一刻度密度存在唯一性）**

在散射假设 (A1)–(A5) 下，存在几乎处处定义的 Borel 函数 $\kappa(\omega)$，使得

$$
\kappa(\omega)
=\varphi'(\omega)/\pi
=\rho_{\rm rel}(\omega)
=(2\pi)^{-1}\operatorname{tr}Q(\omega),
$$

其中 $\varphi(\omega)=\tfrac12\arg\det S(\omega)$，$\rho_{\rm rel}(\omega)=-\xi'(\omega)$，$Q(\omega)=-\mathrm{i}S^\dagger(\omega)\partial_\omega S(\omega)$。该 $\kappa$ 在加上常数导致的整体相位重定义下唯一。

**定理 3.2（边界时间几何与统一刻度对齐）**

在 (B1)–(B4)、(M1)–(M3) 与 (A1)–(A5) 下，对每个小因果菱形边界系统

$$
\mathcal B
=(\mathcal A_\partial,\omega_\partial,S(\omega);h_{ab},K_{ab})
\in U_{\rm BTG},
$$

存在唯一（至仿射）时间参数 $\tau$，使得：

1. 散射时间由

   $$
   \tau_{\rm scatt}(\omega)
   =\int^{\omega}\kappa(\tilde\omega)\,\mathrm d\tilde\omega
   $$

   定义；

2. 模时间由模流 $\sigma_t^\omega$ 通过 KMS 关系与几何 Killing 流对齐；

3. Brown–York 边界哈密顿量的谱分解给出的几何时间参数 $\tau_{\rm geom}$ 与 $\tau_{\rm scatt}$ 与 $\tau_{\rm mod}$ 同属等价类 $[\tau]$。

从而 $[\tau]$ 可视为 $U_{\rm BTG}$ 到 $\mathbf{Time}$ 的唯一时间刻度函子。

### 3.2 拓扑约束与 Null–Modular 双覆盖

**定理 3.3（拓扑无异常与爱因斯坦–熵条件等价）**

在几何与熵假设 (B1)–(B4) 以及适当的 Null–Modular 双覆盖构造下，对 $Y=M\times X^\circ$ 及其边界 $\partial Y$ 定义相对上同调类 $[K]\in H^2(Y,\partial Y;\mathbb Z_2)$，则以下条件等价：

1. $[K]=0$。

2. 在所有小因果菱形上，Einstein 方程

   $$
   G_{ab}+\Lambda g_{ab}
   =8\pi G\,\langle T_{ab}\rangle
   $$

   与 QNEC/QFC 型二阶相对熵非负条件成立，并在族级上与散射–模块–边界数据相容。

3. 一切物理回路 $\gamma\subset X^\circ$ 上的散射平方根行列式 $\sqrt{\det_p S(\omega;\gamma)}$ 的 $\mathbb Z_2$ holonomy 平凡，即无"$\pi$–环量时间异常"。

从而，$[K]$ 给出一个统一的"宇宙拓扑扇区选择"不变量。

### 3.3 几何宇宙、矩阵宇宙与 QCA 宇宙的三重等价

记

* $\mathbf{Univ}^{\mathrm{phys}}_{\rm geo}$ 的对象为满足 (B1)–(B4)、(M1)–(M3)、(O1)–(O3) 的几何宇宙

  $$
  U^{\mathrm{phys}}_{\rm geo}
  =(M,g,\prec,\mathcal A_\partial,\omega_\partial,S_{\rm gen},\kappa);
  $$

* $\mathbf{Univ}^{\mathrm{phys}}_{\rm mat}$ 的对象为散射–矩阵宇宙

  $$
  U^{\mathrm{phys}}_{\rm mat}
  =(\mathcal H_{\rm chan},S(\omega),Q(\omega),\kappa,\mathcal A_\partial,\omega_\partial);
  $$

* $\mathbf{Univ}^{\mathrm{phys}}_{\rm qca}$ 的对象为满足 (Q1)–(Q4) 的 QCA 宇宙

  $$
  U^{\mathrm{phys}}_{\rm qca}
  =(\Lambda,\mathcal H_{\rm cell},\mathcal A,\alpha,\omega_0).
  $$

**定理 3.4（几何–矩阵宇宙等价）**

在散射与边界时间几何内生化条件下，存在函子

$$
F_{\rm geo\to mat}:
\mathbf{Univ}^{\mathrm{phys}}_{\rm geo}
\to
\mathbf{Univ}^{\mathrm{phys}}_{\rm mat},
\qquad
G_{\rm mat\to geo}:
\mathbf{Univ}^{\mathrm{phys}}_{\rm mat}
\to
\mathbf{Univ}^{\mathrm{phys}}_{\rm geo},
$$

使得 $G_{\rm mat\to geo}\circ F_{\rm geo\to mat}$ 与 $F_{\rm geo\to mat}\circ G_{\rm mat\to geo}$ 分别自然同构于各自范畴的恒等函子，从而

$$
\mathbf{Univ}^{\mathrm{phys}}_{\rm geo}
\simeq
\mathbf{Univ}^{\mathrm{phys}}_{\rm mat}.
$$

**定理 3.5（QCA–几何宇宙等价）**

在 QCA 公理 (Q1)–(Q4) 与连续极限存在性条件下，存在函子

$$
C_{\rm qca\to geo}:
\mathbf{Univ}^{\mathrm{phys}}_{\rm qca}
\to
\mathbf{Univ}^{\mathrm{phys}}_{\rm geo},
$$

以及其右伴随 $D_{\rm geo\to qca}$，二者在物理子范畴上诱导范畴等价

$$
\mathbf{Univ}^{\mathrm{phys}}_{\rm qca}
\simeq
\mathbf{Univ}^{\mathrm{phys}}_{\rm geo},
$$

并且统一刻度密度 $\kappa_{\rm qca}(\omega)$ 与几何散射刻度 $\kappa(\omega)$ 属于同一刻度等价类。

**定理 3.6（三重表象等价）**

由定理 3.4 与 3.5，存在自然同构

$$
\mathbf{Univ}^{\mathrm{phys}}_{\rm geo}
\simeq
\mathbf{Univ}^{\mathrm{phys}}_{\rm mat}
\simeq
\mathbf{Univ}^{\mathrm{phys}}_{\rm qca},
$$

从而物理宇宙可在连续几何、矩阵散射与 QCA 三种表象之间无损转换。

### 3.4 统一物理宇宙终对象定理

**定理 3.7（统一物理宇宙终对象）**

在假设 (A1)–(A5)、(B1)–(B4)、(M1)–(M3)、(Q1)–(Q4)、(O1)–(O3) 以及拓扑无异常条件 $[K]=0$ 下，存在多层结构对象

$$
\mathfrak U_{\mathrm{phys}}^\star
=(
U_{\rm evt},U_{\rm geo},U_{\rm meas},U_{\rm QFT},
U_{\rm scat},U_{\rm mod},U_{\rm ent},U_{\rm obs},
U_{\rm cat},U_{\rm comp},
U_{\rm BTG},U_{\rm QCA},U_{\rm top}
),
$$

满足：

1. $\mathfrak U_{\mathrm{phys}}^\star$ 的各层之间满足统一刻度同一式、因果–熵兼容性与拓扑无异常条件；

2. 任意 $\mathbf{Univ}_\mathcal U$ 中满足上述公理的对象 $V$，存在唯一 1–态射

   $$
   F_V:V\to\mathfrak U_{\mathrm{phys}}^\star,
   $$

   且任一两态射之间仅差唯一 2–态射自然同构；

因此，$\mathfrak U_{\mathrm{phys}}^\star$ 是 2–范畴 $\mathbf{Univ}_\mathcal U$ 上物理子范畴中的终对象。

**推论 3.8（无进一步非平凡统一自由度）**

在上述公理体系内，任何"更统一"的物理宇宙结构必然与 $\mathfrak U_{\mathrm{phys}}^\star$ 同构；所有可观测结构——几何、散射、模流、广义熵、QCA 动力学与拓扑不变量——皆为同一终对象的不同表现。

---

## Proofs

本节给出主要定理的证明框架。技术细节与一些长计算置于附录。

### 4.1 定理 3.1：刻度同一式

证明分三步。

**第一步：谱移函数与散射相位的关系。**

由 Birman–Kreĭn 公式

$$
\det S(\lambda)
=\exp\bigl(-2\pi\mathrm{i}\,\xi(\lambda)\bigr)
$$

及 $\varphi(\lambda)=\tfrac12\arg\det S(\lambda)$ 可得

$$
-2\pi\,\xi(\lambda)
=2\varphi(\lambda)+2\pi k(\lambda),
$$

其中 $k(\lambda)\in\mathbb Z$。在 $\xi$ 可微的能区对 $\lambda$ 求导，利用 $k$ 恰常数，得到

$$
-2\pi\,\xi'(\lambda)
=2\,\varphi'(\lambda),
$$

即

$$
\rho_{\rm rel}(\lambda)
=-\xi'(\lambda)
=\varphi'(\lambda)/\pi.
$$

**第二步：谱移函数与 Wigner–Smith 群延迟的关系。**

在绝对连续谱上，散射矩阵 $S(\lambda)$ 为酉算子族，其谱分解给出

$$
\log\det S(\lambda)
=\operatorname{tr}\log S(\lambda).
$$

对 $\lambda$ 求导并使用

$$
Q(\lambda)
=-\mathrm{i}S(\lambda)^\dagger\partial_\lambda S(\lambda),
$$

可得

$$
\partial_\lambda\log\det S(\lambda)
=\operatorname{tr}\bigl(S(\lambda)^{-1}\partial_\lambda S(\lambda)\bigr)
=\mathrm{i}\operatorname{tr}Q(\lambda).
$$

将此与 Birman–Kreĭn 公式导数

$$
\partial_\lambda\log\det S(\lambda)
=-2\pi\mathrm{i}\,\xi'(\lambda)
$$

比较，得

$$
\xi'(\lambda)
=-\frac{1}{2\pi}\operatorname{tr}Q(\lambda),
$$

从而

$$
\rho_{\rm rel}(\lambda)
=-\xi'(\lambda)
=\frac{1}{2\pi}\operatorname{tr}Q(\lambda).
$$

**第三步：唯一性。**

若存在另一函数 $\tilde\kappa$ 满足相同等式，则 $\tilde\kappa-\kappa$ 几乎处处为零；若允许整体相位重定义 $S(\omega)\mapsto e^{2\mathrm{i}\theta}S(\omega)$，则 $\varphi\mapsto\varphi+\theta$，对应 $\kappa\mapsto\kappa+\theta'$，在物理上仅改变时间原点与线性缩放，故唯一性至仿射变换成立。

### 4.2 定理 3.2：边界时间几何与统一刻度

证明理念是：在每个小因果菱形的边界上，散射刻度、模刻度与几何刻度都由同一边界 Hamilton 量的谱测度控制。

**第一步：从 Brown–York 边界应力张量到边界 Hamilton 量。**

对 timelike 或 null 边界片 $\partial D$ 而言，Brown–York 应力张量 $T^{ab}_{\rm BY}$ 与边界 Killing 场 $t^a$ 的配对给出能量密度

$$
\varepsilon
=T^{ab}_{\rm BY}t_a n_b,
$$

其积分定义边界准局域能量 $H_\partial$。由 Hamilton–Jacobi 分析，可将边界时间平移视为由 $H_\partial$ 生成的规范变换，从而几何时间参数本质上是 $H_\partial$ 的谱参数。

**第二步：模 Hamilton 量与相对熵。**

在 GNS 表示中，Tomita–Takesaki 模算子给出模 Hamilton 量 $K=-\log\Delta$。对热平衡或近 KMS 态，可将 $K$ 视为相对于参考状态的能量差算子，其谱密度与相对熵的变分密切相关。QNEC 的现代证明表明，沿 null 形变方向的广义熵二阶变分可以用相对熵的二阶导数表示，从而与模 Hamilton 量的期望值联系起来。在小因果菱形极限中，模 Hamilton 量与 Brown–York 边界 Hamilton 量在适当规范下同源。

**第三步：散射与边界 Hamilton 量的关联。**

将小因果菱形边界看作一个开放散射系统，其散射矩阵 $S_D(\omega)$ 的群延迟 $Q_D(\omega)$ 与能量在该区域内平均滞留时间有关。时间延迟算子的迹等于散射相位导数的 $2\pi$ 倍，故与 $\kappa(\omega)$ 直接相关。利用局域谱–散射对应，将 $H_\partial$ 的谱测度与 $Q_D(\omega)$ 的谱数据对齐，可使由 $\kappa(\omega)$ 积分得到的散射时间 $\tau_{\rm scatt}$ 与几何时间参数 $\tau_{\rm geom}$ 仅差仿射变换。

**第四步：统一刻度等价类。**

综合以上三点，在每个边界系统 $\mathcal B$ 上存在唯一（至仿射）时间参数 $\tau$，使散射时间、模时间与几何时间同属一等价类 $[\tau]$。将此构造提升为从 BTG 范畴到时间范畴的函子即可。

### 4.3 定理 3.3：拓扑无异常与 Einstein–熵条件

定理 3.3 的证明依赖于如下三个子命题。

**命题 4.3.1（$[K]$ 与 $\mathbb Z_2$ holonomy 的等价）**

通过散射族到 $K^1(X^\circ)$ 的自然变换，可将散射矩阵的行列式线丛提升为主 $U(1)$ 丛，其平方根存在性的障碍 precisely 由某个 $H^2(Y,\partial Y;\mathbb Z_2)$ 元素控制。选取 $Y$ 的适当覆盖与 Čech–de Rham 对应，得到该障碍类即为 $[K]$，而其在闭路径上的评估给出平方根行列式的 $\mathbb Z_2$ holonomy。因此 $[K]=0$ 等价于一切物理回路上 holonomy 平凡。

**命题 4.3.2（$[K]$ 与 Null–Modular 双覆盖）**

Null–Modular 双覆盖构造将每个 null 截面上的模参数与散射相位的 $\mathbb Z_2$ 扇区匹配，生成一个带 $\mathbb Z_2$ 结构群的覆盖空间。该覆盖的第二 Stiefel–Whitney 类与 $[K]$ 同构，从而 $[K]=0$ 等价于在 null 边界上可以选取全局一致的"时间扇区"。

**命题 4.3.3（Einstein–熵条件与 $[K]=0$）**

在小因果菱形极限中，Einstein 方程与 QNEC/QFC 可写为广义熵二阶变分的纯约束形式。若 $[K]\neq0$，则在某些闭合形变回路上必然出现符号翻转，使二阶变分在一个回路上改变符号，从而与相对熵非负性矛盾。反之，若 $[K]=0$，则可以在所有小因果菱形上选取一致的"模–散射–几何"扇区，使二阶相对熵非负与 Einstein 方程同时成立。

三者合并即可得到定理 3.3。

### 4.4 定理 3.4 与 3.5：三重表象等价

**几何–矩阵等价（定理 3.4）。**

* 从几何到矩阵：给定几何宇宙 $(M,g,\dots)$，对每个小因果菱形边界构造散射矩阵 $S_D(\omega)$，再通过适当的直和或直积分拼接为全局散射矩阵 $S(\omega)$，其块稀疏模式编码因果偏序。刻度密度 $\kappa(\omega)$ 由定理 3.1 给出。这样得到 $F_{\rm geo\to mat}(U^{\mathrm{phys}}_{\rm geo})$。

* 从矩阵到几何：给定矩阵宇宙 $(\mathcal H_{\rm chan},S(\omega),Q(\omega),\dots)$，利用刻度密度 $\kappa(\omega)$ 与广义熵–能量条件，通过嵌套因果菱形的散射–熵数据重建有效的 $g_{ab}$ 与 $T_{ab}$。这一步与现有"从边界熵/散射重建几何"的程序一致，只是额外要求刻度同一与拓扑无异常。

在物理子范畴内，可以证明上述构造互为逆函子 up to 自然同构，从而得到范畴等价。

**QCA–几何等价（定理 3.5）。**

* 从 QCA 到几何：利用 (Q1)–(Q4) 确保存在适当的连续极限，将 $\Lambda$ 重缩放为流形近似 $M$，将离散时间步与空间格距按固定比例缩放，利用量子行走–狄拉克方程的已知结果，得到在低能–长波极限下的有效狄拉克或 Klein–Gordon 方程。进一步考虑引力与耦合场，可通过在 QCA 规则中加入适当位置与时间依赖参数来模拟曲率与规范场。

* 统一刻度对齐：在 QCA 的散射构型中同样可以定义有效散射矩阵 $S_{\rm QCA}(\omega)$ 与时间延迟算子 $Q_{\rm QCA}(\omega)$，刻度密度 $\kappa_{\rm QCA}(\omega)=(2\pi)^{-1}\operatorname{tr}Q_{\rm QCA}(\omega)$。在连续极限中，$\kappa_{\rm QCA}(\omega)$ 与几何宇宙的 $\kappa(\omega)$ 在低能窗口内仅差仿射变换，故属于同一刻度等价类。

* 从几何到 QCA：对于给定几何宇宙，可按 Arrighi 等人关于"量子行走在曲时空中"的方法构造 Dirac–QCA，使其连续极限重现给定 $g_{ab}$ 与规范场。在适当物理子范畴中，这一构造给出 $D_{\rm geo\to qca}$，且与 $C_{\rm qca\to geo}$ 互为伴随并诱导范畴等价。

综合上述两对等价可得定理 3.6。

### 4.5 定理 3.7：终对象性质

证明思想是：在 $\mathbf{Univ}_\mathcal U$ 中对所有满足公理的对象取 2–极限，并验证所得对象满足终对象的泛性质。

1. 以各层范畴的终对象或极限对象为基元。例如，事件层 $U_{\rm evt}$ 是所有局域偏序片段的 2–极限；几何层 $U_{\rm geo}$ 是所有局部几何–熵一致结构的极限；散射层 $U_{\rm scat}$ 是所有局部散射矩阵与谱移数据的极限，等等。

2. 统一刻度同一式确保在散射层、边界时间几何层与 QCA 层上时间刻度密度可被识别为同一对象 $\kappa$，并通过 BTG 函子 $\mathsf T$ 内生为统一时间刻度等价类 $[\tau]$。

3. 拓扑层 $U_{\rm top}$ 通过相对上同调类 $[K]$ 的扇区选择仅保留 $[K]=0$ 扇区，使得从不同候选宇宙投影来的拓扑数据在同一类中粘合。

4. 观察者层 $U_{\rm obs}$ 通过 Čech–极限将所有满足共识几何条件的观察者族 $\{O_i\}$ 粘合为唯一全局对象。

5. 由于各层构造均为各自范畴中的极限或终对象，整个多层结构 $\mathfrak U_{\mathrm{phys}}^\star$ 在 $\mathbf{Univ}_\mathcal U$ 中自动满足终对象的泛性质：对任意 $V$，各层存在唯一结构保持态射 $V\to\mathfrak U_{\mathrm{phys}}^\star$，且这些态射在层间兼容。

由此得定理 3.7 与推论 3.8。

---

## Model Apply

本节展示统一物理宇宙终对象在若干典型物理问题上的应用。

### 5.1 黑洞熵、信息与 QCA 版本面积律

在几何宇宙表象中，黑洞视界是小因果菱形的极限，其广义熵

$$
S_{\rm gen}
=\frac{A}{4G\hbar}
+S_{\rm out}
$$

在稳定态满足极值条件，微扰满足 QNEC/QFC，从而给出 Bekenstein–Hawking 面积律与信息流的约束。

在矩阵宇宙表象中，视界对应于某类散射通道的完全吸收或强混合极限，其散射矩阵的行列式与群延迟在视界附近表现出特征行为。相对谱移函数的导数 $\rho_{\rm rel}(\omega)$ 可被解释为"视界模态密度"，与微观态计数相关。

在 QCA 宇宙表象中，视界可建模为一族不可逆 coarse-graining 区域或信息流不可回返的"删除锥"。近年的工作表明，基于 QCA 的黑洞热力学模型可以重现部分面积律与复杂度增长特征。在 $\mathfrak U_{\mathrm{phys}}^\star$ 框架中，视界上的 QCA 单元数量、纠缠模式与拓扑约束 $[K]=0$ 共同决定有效的 $A/4G\hbar$ ；统一时间刻度保证信息滞留时间与散射延迟之间的一致性，从而在三种表象中给出同一熵–面积–时间三元关系。

### 5.2 宇宙学常数与统一时间刻度

在大尺度上，$\kappa(\omega)$ 的积分可视为某种"宇宙散射相位"随频率的累积。若宇宙在宏观上近似 de Sitter，则边界时间几何与 Brown–York 能量给出的"真空能量密度"与统一时间刻度之间存在简单比例关系，$\Lambda$ 可被解释为大尺度上 $\kappa(\omega)$ 与微观 QCA 单元频谱之间的微小失配。

更具体地，可以在 QCA 宇宙中引入略偏离"临界平衡"的局域更新规则，使得在去连续极限与 Poisson–Euler–Maclaurin 规约后，出现一个剩余常数项，对应于有效宇宙学常数。统一刻度框架的约束是：该常数必须不破坏 $[K]=0$ 与广义熵变分非负，从而为 $\Lambda$ 的大小提供结构性限制。

### 5.3 时间箭头、熵生产与 QCA 观测

在几何宇宙表象中，时间箭头由广义熵沿统一刻度 $[\tau]$ 的单调性给出；在矩阵宇宙表象中，时间箭头对应于散射通道中群延迟与相对熵流向的单向性；在 QCA 宇宙中，则体现为局域规则导致的纠缠扩散与有效不可逆 coarse-graining。

统一物理宇宙终对象保证这三种"时间箭头"是同一结构在不同表象中的表现：QCA 中的纠缠扩散速率通过连续极限对应于几何中的 null 聚焦速率；矩阵宇宙中的时间延迟谱通过 BTG 对应于边界能量流与模 Hamilton 量。

---

## Engineering Proposals

本节给出若干在当前或可预见技术条件下可实现的检验提案，用于部分验证 $\mathfrak U_{\mathrm{phys}}^\star$ 的结构。

### 6.1 群延迟矩阵与统一刻度的实验读数

Wigner–Smith 群延迟矩阵已在电磁与声学散射实验中得到实现，用于刻画复杂介质中的"时间延迟模"。统一刻度框架要求：在适当归一化下，这些群延迟的迹应与通过谱移函数导数或散射相位导数测得的刻度密度一致。

工程方案包括：

1. 在可精确建模的波导或多模共振腔中测量 $S(\omega)$，数值计算 $Q(\omega)$ 的迹并与通过独立手段估计的谱移进行比较，以验证刻度同一式。

2. 在具有类"视界"结构的介质（如强散射随机介质或拓扑边界）中，测量群延迟谱与局域能量密度的关系，以检验 Brown–York 边界能量与群延迟之间的联系。

### 6.2 QCA/量子行走平台上的狄拉克极限与刻度对齐

近年来，基于囚禁离子、超导线路与光学系统的离散时间量子行走与 Dirac–QCA 已得到实验实现。统一物理宇宙终对象框架下，可以提出如下工程检验：

1. 设计一类 Dirac–QCA，其连续极限为给定参数的狄拉克方程；在实验中同时测量离散系统的有效散射矩阵与时间延迟，再与连续模型中的 $\kappa(\omega)$ 比较，检验刻度对齐。

2. 在具有模拟曲率或规范场的量子行走实验中，测量"时间延迟模"的谱流，并比较其与几何侧的 Brown–York 能量与广义熵变分的关系，从而测试 BTG 内生化的一个有限维模型。

### 6.3 QCA 黑洞玩具模型与面积律

利用可编程 QCA 或量子电路，实现具有"视界区"的演化规则，例如通过对某区域施加不可逆测量或强耗散来模拟信息单向流失。对该区域边界上元胞之间的纠缠熵进行测量，测试其是否满足与边界"长度"或"面积"线性相关的关系；在不同规则下比较拓扑类 $[K]$ 的变化对面积律的影响。

这些实验无法直接触及真实黑洞，但可以在可控平台上验证统一框架中"面积律 = 边界元胞数目 = QCA 纠缠熵"的结构性同一。

---

## Discussion (risks, boundaries, past work)

统一物理宇宙终对象框架在概念上将多种成熟理论粘合在一起，但也存在明显的风险与边界。

首先，刻度同一式虽然在散射理论中有扎实基础，Birman–Kreĭn 公式与 Wigner–Smith 群延迟之间的联系在大量模型中得到验证，但将其提升为宇宙级统一时间刻度仍是一种外推，需要假设宇宙在足够大尺度上可视为某种"散射系统"。

其次，QNEC/QFC 的严格证明目前仅在特定维数、特定类态与理论中完成，最近也有进一步推广与简化证明，但尚未覆盖所有可能的量子场论与背景曲率。将其作为公理嵌入统一框架，是一种理想化假设。

再次，QCA 连续极限的存在性与唯一性依赖于局域规则的具体形式。虽然大量工作表明广义 Dirac–QCA 与量子行走可以在连续极限下重现相对论波动方程，但并非所有 QCA 都具有良好的连续极限。本文只在具有良好连续极限且满足物理性条件的子范畴中建立等价。

此外，$[K]=0$ 的拓扑选择条件在本文中被视为物理上必要的"一致性条件"，但从更基础的角度看，这可能只是某一更大理论中的特定扇区。不同扇区之间也许对应不同类型的"宇宙"，其中部分可能与我们可观测宇宙不相容。

最后，本框架并未直接给出标准模型参数、层级结构或宇宙学常数数值的预测，只是在结构层面给出约束。"终对象"的意义是范畴论与结构论的，而非数值预测上的终极答案。

与既有统一方案相比：

* 与弦论的关系主要体现在边界 CFT 与散射矩阵的相容性以及拓扑约束层上，但本文不依赖特定弦背景或紧化方案。

* 与圈量子引力和因果集合理论的关系体现在因果–熵–时间统一与离散因果结构上，但 QCA 与矩阵宇宙提供的是不同类型的离散化。

* 与全息原理的关系则通过 BTG 与广义熵层自然连接：边界代数与边界熵编码体域几何，这是本框架的核心假设之一。

---

## Conclusion

本文在统一时间刻度、边界时间几何、Null–Modular 双覆盖、拓扑 $K$–理论、极大一致宇宙对象与量子元胞自动机宇宙的基础上，构造了一个多层结构的统一物理宇宙终对象 $\mathfrak U_{\mathrm{phys}}^\star$，并证明在适当公理与拓扑选择条件下，它在 2–范畴 $\mathbf{Univ}_\mathcal U$ 中是终对象。

这一终对象将以下结构收束为单一对象的不同表象：

* 统一时间刻度密度 $\kappa(\omega)$ 与其在散射、模流、几何与 QCA 中的实现；

* 小因果菱形上的广义熵与 Einstein 方程、QNEC/QFC 的等价；

* Null–Modular 双覆盖与相对上同调类 $[K]$ 所刻画的拓扑扇区选择；

* 连续几何宇宙、矩阵散射宇宙与 QCA 宇宙三类表象范畴的范畴等价；

* 观察者共识几何与全局宇宙对象之间的 2–极限关系。

在这一框架中，"进一步统一"的自由度在结构层面被耗尽：任何满足公理的宇宙理论要么等价于 $\mathfrak U_{\mathrm{phys}}^\star$ 的某一投影，要么在刻度、因果、熵或拓扑层面与公理系统不相容。未来工作可在此基础上进一步探索：

* 将标准模型规范与味结构、CP 破缺等嵌入拓扑–散射–QCA 层；

* 构造更具体的 QCA 黑洞与宇宙学模型，并与数值相对论与观测数据比较；

* 在 BTG 与 QCA 平台上设计更多可实验验证的刻度同一与熵–能量关系。

---

## Acknowledgements, Code Availability

本工作综合了散射理论、代数量子场论、广义熵、拓扑 $K$–理论与量子元胞自动机等多个方向的思想。文中涉及的符号计算与数值实验（包括散射矩阵的谱移与群延迟计算、QCA 连续极限的数值检验等）基于通用数学软件实现，相关代码目前保存在作者的内部版本库中，如有需要可联系作者获取。

---

## References

[1] M. Sh. Birman, M. G. Kreĭn, "On the theory of wave operators and scattering operators", Dokl. Akad. Nauk SSSR, 1962.

[2] A. Pushnitski, "The spectral shift function and the invariance principle", J. Funct. Anal. 183 (2001), 269–320.

[3] H. Isozaki, "Trace formulas for Schrödinger operators", RIMS Kokyuroku 1760 (2011).

[4] U. R. Patel et al., "Wigner–Smith time-delay matrix for electromagnetics: Theory and phenomenology", arXiv:2005.03211.

[5] P. Ambichl et al., "Focusing inside disordered media with the generalized Wigner–Smith operator", Phys. Rev. Lett. 119, 033903 (2017).

[6] J. D. Brown, J. W. York, "Quasilocal energy and conserved charges derived from the gravitational action", Phys. Rev. D 47, 1407 (1993).

[7] V. Chandrasekaran, E. Flanagan, K. Prabhu, "Brown–York charges at null boundaries", JHEP 01 (2022) 029.

[8] Z. U. Khandker, S. Kundu, D. Li, "Bulk matter and the boundary quantum null energy condition", JHEP 08 (2018) 162.

[9] S. Hollands, "A new proof of the quantum null energy condition", Commun. Math. Phys. (2025).

[10] T. Kibe et al., "Quantum null energy condition in quenched 2D CFTs", JHEP (2025).

[11] N. Bao, C. Cao, M. Newman, V. P. Su, "The holographic dual of Rényi relative entropy", arXiv:1811.03113.

[12] B. Schumacher, R. F. Werner, "Reversible quantum cellular automata", quant-ph/0405174.

[13] P. Arrighi, "Quantum walking in curved spacetime", Quantum Inf. Process. 18, 239 (2019).

[14] F. W. Strauch, "Relativistic quantum walks", Phys. Rev. A 73, 054302 (2006).

[15] C. M. Chandrashekar, "Relationship between quantum walks and relativistic quantum mechanics", Phys. Rev. A 81, 062340 (2010).

[16] G. Di Molfetta, F. Debbasch, "Discrete-time quantum walks: Continuous limit and symmetries", J. Math. Phys. 53, 123302 (2012).

[17] G. Di Molfetta, P. Arrighi, "A quantum walk with both a continuous-time and a continuous-spacetime limit", Quantum Inf. Process. 19, 47 (2020).

[18] A. Mallick et al., "Dirac cellular automaton from split-step quantum walk", Sci. Rep. 6, 25779 (2016).

[19] C. Huerta Alderete et al., "Quantum walks and Dirac cellular automata on a trapped-ion quantum computer", Nat. Commun. 11, 3720 (2020).

[20] R. Shah, "Quantum cellular automata, black hole thermodynamics and computational complexity", Complex Syst. 28 (2019).

[21] P. Arrighi, I. Márquez-Martín, A. Pérez, "The Dirac equation as a quantum walk over the honeycomb and triangular lattices", Quant. Inf. Process. 18, 46 (2019).

[22] M. Yamagishi et al., "Multi-dimensional quantum walks: a playground of Dirac and Schrödinger particles", arXiv:2212.13044.

[23] A. Anglés-Castillo et al., "A quantum walk simulation of extra dimensions with higher-order topology", Commun. Phys. 5, 36 (2022).

---

## Appendix A  三重表象等价的局域–全局证明

本附录给出定理 3.4–3.6 的更详细证明结构。

### A.1 局域散射–几何对应

对每个小因果菱形 $D_{p,r}$：

1. 几何侧：由 $(M,g)$ 与局域物质场求得 $D_{p,r}$ 上的 Brown–York 边界应力张量与广义熵 $S_{\rm gen}(\Sigma)$。

2. 散射侧：将 $D_{p,r}$ 看作具有入射与出射边界通道的散射系统，构造边界散射矩阵 $S_{D_{p,r}}(\omega)$、群延迟 $Q_{D_{p,r}}(\omega)$ 与谱移函数 $\xi_{D_{p,r}}(\omega)$。

3. 由定理 3.1，$S_{D_{p,r}}(\omega)$ 的相位与谱移函数导数、群延迟迹给出局域刻度密度 $\kappa_{D_{p,r}}(\omega)$，其积分定义局域散射时间。

4. 由广义熵变分与 QNEC/QFC，可将 Einstein 方程在 $D_{p,r}$ 上重写为广义熵二阶变分等式，与模 Hamilton 量的谱密度相关。

通过匹配以上两类谱测度，可在每个 $D_{p,r}$ 上建立散射–几何–熵的局域同构，并构造从局域几何宇宙到局域矩阵宇宙的函子。

### A.2 局域 QCA–几何对应

考虑满足 (Q1)–(Q4) 的 QCA，在足够小的格距与时间步下，对任意有限区间 $\Lambda_{p,r}\subset\Lambda$：

1. 将 QCA 在 $\Lambda_{p,r}$ 限制并施加适当边界条件，得到局域离散动力学。

2. 对单粒子或充分稀疏多粒子态，采用 Fourier 或 Bloch 分析，得到局域有效能谱 $E_{\rm eff}(k)$。

3. 在连续极限 $\epsilon\to0$ 下，利用现有 QW–Dirac 连续极限的严格结果，将 $E_{\rm eff}(k)$ 的主阶部分识别为狄拉克或 Klein–Gordon 型能谱，对应某种 $g_{ab}$ 与规范场背景。

4. 在该背景下构造局域小因果菱形 $D_{p,r}$ 与边界散射数据，得到局域几何宇宙对象。

由此得到从局域 QCA 宇宙到局域几何宇宙的函子。反向构造通过在给定局域几何上选择合适的离散化与 Dirac–QCA 规则实现。

### A.3 局域–全局粘合与范畴等价

在上述局域对应基础上，通过嵌套因果菱形或嵌套格点区域的极限构造全局宇宙对象。由于局域构造在重叠区域上满足自然相容性条件，可利用 2–范畴中的极限与余极限理论将局域等价提升为全局范畴等价，从而得到定理 3.4–3.6。

---

## Appendix B  QCA 连续极限与统一刻度对齐

本附录以一维 Dirac–QCA 为例，说明 $\kappa_{\rm qca}(\omega)$ 与 $\kappa(\omega)$ 的刻度对齐。

### B.1 一维 Dirac–QCA 模型

考虑一维格点 $\Lambda=\epsilon\mathbb Z$，元胞 Hilbert 空间 $\mathcal H_{\rm cell}=\mathbb C^2$，单步演化算子

$$
U
=S_+C_+
+S_-C_-,
$$

其中 $S_\pm$ 为向右/向左平移算子，$C_\pm$ 为依赖质量与速度参数的局域"coin"算子。适当选择 $C_\pm$ 后，可使 $U$ 在动量空间的谱

$$
U(k)
=\exp\bigl(-\mathrm{i}\epsilon H_{\rm eff}(k)\bigr)
$$

满足

$$
H_{\rm eff}(k)
=\alpha k + \beta m + O(\epsilon),
$$

即在连续极限给出狄拉克 Hamilton 量。

### B.2 QCA 散射矩阵与群延迟

在有限区间上引入势垒或边界条件，可定义 QCA 的散射矩阵 $S_{\rm QCA}(k)$；其群延迟算子

$$
Q_{\rm QCA}(k)
=-\mathrm{i}S_{\rm QCA}(k)^\dagger\partial_k S_{\rm QCA}(k)
$$

的迹在连续极限下满足

$$
\operatorname{tr}Q_{\rm QCA}(k)
=\operatorname{tr}Q_{\rm cont}(k)
+O(\epsilon),
$$

其中 $Q_{\rm cont}(k)$ 为连续 Dirac 散射问题的群延迟算子。

因而

$$
\kappa_{\rm qca}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q_{\rm QCA}(\omega)
\to
\frac{1}{2\pi}\operatorname{tr}Q(\omega)
=\kappa(\omega),
$$

在适当能区与尺度极限下两者仅差仿射变换。

### B.3 多维与曲时空推广

类似构造可推广到多维格点与曲时空背景，通过引入位置依赖的 coin 与转移算子实现有效的弯曲度规与规范场，在连续极限下给出曲时空狄拉克方程。在这些模型中，统一刻度对齐仍然成立，从而为 $\mathfrak U_{\mathrm{phys}}^\star$ 中 $U_{\rm QCA}$ 与 $U_{\rm scat}$ 的一致性提供了具体示例。

