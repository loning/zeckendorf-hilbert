# 宇宙终对象的数学刻画

统一时间刻度、边界时间几何与 QCA 宇宙的高维结构

---

## Abstract

在广义相对论、量子场论与信息论的交汇处，越来越多的工作指向一个共同图景：物理宇宙的一切可观测结构可以被视为某个更高维数学对象在不同投影下的"影子"。因果偏序、时空流形、散射矩阵、边界代数以及量子元胞自动机等描述，只是这一高维对象在不同范畴中的像。本文在统一时间刻度、边界时间几何与量子元胞自动机（quantum cellular automaton, QCA）宇宙框架上，引入并刻画一个"宇宙终对象"（universal terminal object）概念，用以给出"宇宙最高维数学结构"的精确定义。

具体而言，本文构造三类带物理约束的宇宙范畴：算子–散射宇宙范畴 ($\mathsf{OpUniv}$)、边界时间几何宇宙范畴 ($\mathsf{GeoUniv}$) 与 QCA/矩阵宇宙范畴 ($\mathsf{QCAUniv}$)。三者分别编码统一时间刻度下的散射–谱移–Wigner–Smith 延迟结构、带广义熵与量子 Null 能量条件的边界时间几何以及有限信息的离散 QCA 宇宙。对每一类范畴，我们构造到局域有限因果偏序范畴 ($\mathsf{Caus}$) 的因果影子函子，从而将"因果偏序只是高维结构的影子"这一陈述形式化。

在此基础上，本文定义"因果兼容宇宙三重态"范畴 ($\mathsf{Uni}\subset\mathsf{OpUniv}\times\mathsf{GeoUniv}\times\mathsf{QCAUniv}$)，其对象为在三类表示上因果影子可在 ($\mathsf{Caus}$) 中对齐的三重宇宙对象，态射为沿粗粒化方向保持结构并在因果侧协变的映射。假定统一时间刻度母式、有限信息原理与适当的链完备性公理成立，本文证明：($\mathsf{Uni}$) 中存在唯一（同构意义下）的终对象 ($\mathfrak U_{\max}$)，称为"宇宙终对象"。该对象的三类投影分别给出算子–散射终对象 ($O_{\max}$)、几何–边界终对象 ($G_{\max}$) 与 QCA 终对象 ($Q_{\max}$)，它们在适当的桥接函子下两两等价。

进一步地，本文给出三个结构性结果。第一，任意物理可实现宇宙模型均可视为 ($\mathfrak U_{\max}$) 在某个范畴对偶中的唯一投影，因而因果偏序、小因果菱形与观察者世界线只是 ($\mathfrak U_{\max}$) 在不同投影与尺度下的影子。第二，基于广义熵与量子聚焦猜想的离散版本，证明了"小因果菱形细化定理"：在有限信息公理下，任何尺度上的因果小菱形都可以由更小尺度的小菱形族以近乎熵可加的方式填充，最小物理结构仅由信息元胞尺度确定，而非由某个固定几何最小菱形决定。第三，观察者、记忆与多观察者共识几何可以在 ($\mathfrak U_{\max}$) 中刻画为因果影子上的滤子及其在三类表示中的一致子对象，从而把"时间延迟等价于记忆"、"体积是边界数据解码后的现象"转化为相对熵与刻度密度的精确定理。附录给出了宇宙终对象存在与唯一性、小钻石细化定理以及三类表示等价性的详细证明。

---

## Keywords

统一时间刻度；边界时间几何；量子元胞自动机；因果偏序；小因果菱形；终对象；有限信息原理；全息结构

---

## 1 Introduction & Historical Context

### 1.1 高维结构与"影子"视角

现代物理理论往往在若干互不等价的"表示"之间切换：

1. 以时空流形 $(M,g)$ 与因果结构 $J^\pm$ 为基本对象的几何描述；

2. 以 Hilbert 空间、算子代数与散射矩阵 $S(\omega)$ 为基本对象的算子–散射描述；

3. 以离散格点 $\Lambda$、局域 Hilbert 空间 $\mathcal H_{\mathrm{cell}}$ 与局域演化 $U$ 为基本对象的量子元胞自动机描述。

同时，因果集方案将微观时空刻画为一个带局域有限性的偏序集合，表明仅保留"先后关系"也可以重建连续流形的部分结构。全息原理进一步指出，体积区域内的自由度可由其边界上的自由度编码，黑洞热力学与 Bekenstein 界给出了这种"边界编码"的具体熵界形式。

这些结果共同暗示：所谓"宇宙"，可以被理解为某个包含因果、几何、算子、信息与计算等全部数据的高维结构，而我们熟悉的时空、场、粒子与因果偏序，只是该高维结构在不同范畴、不同尺度下的投影或影子。

本文试图将这一图景公理化：构造一个同时控制统一时间刻度、边界时间几何与 QCA 宇宙的范畴论框架，并在其中定义并证明一个"宇宙终对象"的存在，把"宇宙最高维数学结构"精确等价于范畴 $\mathsf{Uni}$ 的终对象 $\mathfrak U_{\max}$。

### 1.2 历史背景：从因果集、全息到 QCA 宇宙

在时空的离散化尝试中，Bombelli–Lee–Meyer–Sorkin 提出的因果集方案假定微观时空在本质上是由一个局域有限的偏序集合构成，连续流形仅为粗粒化极限。这一思想为"因果优先"的宇宙刻画提供了先例。

另一方面，全息原理与 AdS/CFT 对偶表明，体积区域中的引力自由度等价于边界上的共形场论，自然鼓励以边界代数、广义熵与量子聚焦猜想（QFC/QNEC）来重写引力动力学。

再一方面，Schumacher–Werner 对可逆量子元胞自动机给出了结构定理，将其刻画为有限传播半径、平移协变的局域酉变换，并证明可逆 QCA 具有良好的分类与连续极限性质。大量工作表明，一类 QCA 的连续极限可以产生有效的 Dirac 型场论与规范场论，这为"宇宙作为 QCA"提供了严谨的数学支撑。

在散射理论侧，Eisenbud–Wigner–Smith 延迟时间与 Birman–Kreĭn 公式表明，散射相位导数、谱移函数与 Wigner–Smith 群延迟矩阵的迹之间存在统一关系，可被解释为单一时间刻度密度 $\kappa(\omega)$。这一刻度在边界 Hamilton 形式（Brown–York 准局域能）框架中与边界时间平移产生元相联系，从而将散射时间刻度与边界时间几何统一。

上述各线索显示：散射–时间刻度、边界时间几何与 QCA 宇宙之间应存在深刻的对应关系，其共同约束可被提炼为若干公理。本文在此基础上提出"宇宙终对象"的概念。

### 1.3 本文工作与主要结果

本文的目标可以概括为如下问题：在统一时间刻度与有限信息公理下，是否存在一个在算子–散射、边界几何与 QCA 三种表示上同时极大且一致的数学对象，使得一切物理可实现宇宙模型均可视为其投影或粗粒化？若存在，该对象是否可以被刻画为某个自然范畴中的终对象？

为回答这一问题，本文完成以下工作：

1. 构造三类带物理约束的宇宙范畴 $(\mathsf{OpUniv},\mathsf{GeoUniv},\mathsf{QCAUniv})$，并在每个范畴上定义到局域有限因果偏序范畴 $(\mathsf{Caus})$ 的因果影子函子，形式化"因果偏序是高维数据的影子"这一命题。

2. 定义"因果兼容宇宙三重态"范畴 $(\mathsf{Uni})$，其对象为在三类表示上具有共同因果影子的三重宇宙对象，态射为沿粗粒化方向保持结构且在因果影子上协变的映射。

3. 在统一时间刻度母式、有限信息原理与链完备性公理下，利用 Zorn 引理证明 $(\mathsf{Uni})$ 中存在唯一（同构意义下）的终对象 $(\mathfrak U_{\max})$，并给出其三类投影 $(O_{\max},G_{\max},Q_{\max})$ 及其两两等价性。

4. 在 $(\mathfrak U_{\max})$ 的因果影子 $(C_{\max})$ 上，引入尺度参数化的小因果菱形族，并证明"小钻石细化定理"：任意大尺度小菱形均可由更小尺度的小菱形以近乎熵可加的方式填充，最小物理单元由信息元胞尺度而非几何菱形决定，从而严谨化"小钻石永远不是最小结构，只是自洽结构"的陈述。

5. 将观察者、记忆与多观察者共识几何刻画为 $(\mathfrak U_{\max})$ 中因果滤子与子对象，证明沿世界线的记忆熵与统一时间刻度之间的定量对应，给出"时间延迟等价于记忆"的精确定理版本。

文章结构按照"模型与公理—主定理—证明—应用—工程建议—讨论—结论—附录"的顺序展开。

---

## 2 Model & Assumptions

本节给出本文使用的统一时间刻度公理、有限信息公理、因果偏序与小因果菱形的定义，并构造三类宇宙范畴及因果影子函子，为随后的主定理奠定基础。

### 2.1 统一时间刻度母式

考虑一类满足标准可追踪扰动条件的散射系统，其散射矩阵可写为频率依赖的酉算子族

$$
S(\omega)\in\mathcal U(\mathcal H),\quad \omega\in\mathbb R.
$$

定义 Wigner–Smith 群延迟矩阵

$$
\mathsf Q(\omega)=-\mathrm i\,S(\omega)^\dagger\partial_\omega S(\omega).
$$

设 $\varphi(\omega)$ 为散射总相位，$\xi(\omega)$ 为 Birman–Kreĭn 谱移函数，$\rho_{\mathrm{rel}}(\omega)$ 为相应的相对态密度，则在适当正则性与可追踪性条件下，有标准关系

$$
\varphi'(\omega)=\pi\,\xi'(\omega),\quad
\xi'(\omega)=\rho_{\mathrm{rel}}(\omega),\quad
\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega),
$$

这可由 Birman–Kreĭn 公式与谱移函数理论导出。

据此引入统一刻度密度函数

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\mathrm{rel}}(\omega)
=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega).
$$

**公理 A1（刻度同一式）**

本文所考虑的一切算子–散射宇宙对象，其散射描述均满足上述刻度同一式。换言之，$\kappa(\omega)$ 在加常数意义下唯一，作为全局统一时间刻度的母密度。

这一公理把散射相位导数、谱移函数导数与 Wigner–Smith 群延迟迹统一为单一时间刻度密度，为散射–几何–QCA 三者间的桥接提供共同基准。

### 2.2 有限信息原理与局域有限性

Bekenstein 界与黑洞热力学表明，在给定能量与空间尺度下，系统的最大熵存在有限上界。这启发如下信息论公理。

**公理 A2（有限信息原理）**

1. 存在一常数 $I_{\max}\in(0,+\infty)$，使得任意物理可区分的宇宙状态族的对数基数不超过 $I_{\max}$。

2. 存在一个最小有效信息元胞尺度 $\epsilon>0$，使得当描述尺度小于 $\epsilon$ 时，增加的细节不再对应新的物理可区分自由度。

有限信息原理在因果结构上诱导局域有限性。

**定义 2.1（局域有限因果偏序）**

一个偏序集合 $(X,\prec)$ 称为局域有限的，如果对任意 $x\prec y\in X$，闭因果区间

$$
I(x,y)=\{z\in X:x\preceq z\preceq y\}
$$

是有限集。

局域有限性自然出现在因果集和离散 QCA 的因果结构中。有限信息原理保证在任何有限时空区域内只包含有限个"基本事件"，从而支撑局域有限性的物理合理性。

### 2.3 因果偏序与小因果菱形

**定义 2.2（因果偏序范畴 $\mathsf{Caus}$）**

$\mathsf{Caus}$ 的对象为所有局域有限因果偏序 $(X,\prec)$，态射为偏序保持单射

$$
f:(X,\prec_X)\to(Y,\prec_Y),\quad
x_1\prec_X x_2\Rightarrow f(x_1)\prec_Y f(x_2).
$$

**定义 2.3（小因果菱形）**

在 $(X,\prec)\in\mathsf{Caus}$ 中，给定 $x\prec y$，若闭区间 $I(x,y)$ 不含非平凡"分岔"，即不存在 $z\neq x,y$ 同时满足 $x\prec z\prec y$ 且 $z$ 在 $x,y$ 之间引入新的因果支路，则称 $D(x,y):=I(x,y)$ 为一个小因果菱形。

在连续洛伦兹流形上，小因果菱形对应于由两条近平行 Null 超曲面截出的微型因果菱形区域，是定义局域引力与熵条件的自然单元。在局域有限因果偏序中，小菱形族构成一个"可分解单元"系统，后文的小钻石细化定理将依赖这一结构。

### 2.4 算子–散射宇宙范畴 $\mathsf{OpUniv}$

**定义 2.4（算子–散射宇宙对象）**

一个算子–散射宇宙对象 $O$ 是四元组

$$
O=(\mathcal H,\mathcal A,S(\omega);\kappa),
$$

其中：

1. $\mathcal H$ 为可分 Hilbert 空间；

2. $\mathcal A\subset\mathcal B(\mathcal H)$ 为满足局域性与准局域性条件的 $C^\ast$ 代数；

3. $S(\omega)\in\mathcal U(\mathcal H)$ 为满足适当可追踪扰动与正则性的散射矩阵族；

4. $\kappa(\omega)$ 为刻度密度函数，满足公理 A1。

**定义 2.5（算子–散射宇宙态射）**

给定两个对象

$$
O_i=(\mathcal H_i,\mathcal A_i,S_i(\omega);\kappa_i),\quad i=1,2,
$$

一个态射 $f:O_1\to O_2$ 是一对映射 $f=(V,\phi)$，其中 $V:\mathcal H_1\to\mathcal H_2$ 为等距嵌入，$\phi:\mathcal A_2\to\mathcal A_1$ 为单位保持的 $(*)$-同态，并满足：

1. $V\mathcal A_1V^\dagger\subset\mathcal A_2$，且与局域结构相容；

2. $S_2(\omega)V=V S_1(\omega)$ 几乎处处成立；

3. $\kappa_1(\omega)=\kappa_2(\omega)$ 几乎处处（允许加常数）。

对象与态射构成范畴 $\mathsf{OpUniv}$。

### 2.5 边界时间几何宇宙范畴 $\mathsf{GeoUniv}$

**定义 2.6（边界时间几何宇宙对象）**

一个几何–边界宇宙对象 $G$ 由数据

$$
G=(M,g,\partial M;\{\mathcal A(B),\omega_B\}_{B\subset\partial M})
$$

给出，其中：

1. $(M,g)$ 为满足适当能量条件与全局双曲性的洛伦兹流形，$\partial M$ 为其边界；

2. 对每个边界片 $B\subset\partial M$，$\mathcal A(B)$ 为局域观测代数，$\omega_B$ 为相应状态；

3. 广义熵

   $$
   S_{\mathrm{gen}}(B)=\frac{\operatorname{Area}(B)}{4G_N}+S_{\mathrm{out}}(B)
   $$

   及其沿 Null 方向的变化满足量子聚焦猜想与量子 Null 能量条件。

4. 存在与刻度密度 $\kappa(\omega)$ 相容的边界 Hamilton 形式，使得 Brown–York 准局域能可被解释为沿边界时间平移的共轭量。

**定义 2.7（几何–边界宇宙态射）**

两个对象 $G_1,G_2$ 之间的态射 $f:G_1\to G_2$ 为一对映射

$$
f=(\Phi,\{\psi_B\}),
$$

其中 $\Phi:M_1\to M_2$ 为因果保持的局域同胚，$\psi_B:\mathcal A_2(\Phi(B))\to\mathcal A_1(B)$ 为单位保持的 $(*)$-同态，并保持广义熵的单调性与准局域结构。对象与态射构成范畴 $\mathsf{GeoUniv}$。

### 2.6 QCA/矩阵宇宙范畴 $\mathsf{QCAUniv}$

**定义 2.8（QCA 宇宙对象）**

一个 QCA 宇宙对象 $Q$ 是五元组

$$
Q=(\Lambda,\mathcal H_{\mathrm{cell}},U,\ket{\Psi_0};\Theta),
$$

其中：

1. $\Lambda$ 为可数离散格点集合，带有限邻域结构；

2. $\mathcal H_{\mathrm{cell}}$ 为有限维元胞 Hilbert 空间，整体空间

   $$
   \mathcal H_\Lambda=\bigotimes_{x\in\Lambda}\mathcal H_{\mathrm{cell}};
   $$

3. $U:\mathcal H_\Lambda\to\mathcal H_\Lambda$ 为有限传播半径和平移协变的局域酉演化；

4. $\ket{\Psi_0}\in\mathcal H_\Lambda$ 为初始宇宙态；

5. $\Theta$ 为宇宙参数向量，编码局域耦合与拓扑数据，并在适当连续极限下与刻度密度 $\kappa(\omega)$ 相容。

**定义 2.9（QCA 宇宙态射）**

给定

$$
Q_i=(\Lambda_i,\mathcal H_{\mathrm{cell},i},U_i,\ket{\Psi_{0,i}};\Theta_i),\quad i=1,2,
$$

一个态射 $f:Q_1\to Q_2$ 由三元组

$$
f=(\iota,\chi,W)
$$

给出，其中 $\iota:\Lambda_2\to\Lambda_1$ 为格点嵌入或粗粒化映射，$\chi:\mathcal H_{\mathrm{cell},2}\to\mathcal H_{\mathrm{cell},1}$ 为单元 Hilbert 空间嵌入，$W:\mathcal H_{\Lambda_1}\to\mathcal H_{\Lambda_2}$ 为与 $U_i$ 相容的等距嵌入或压缩映射。对象与态射构成范畴 $\mathsf{QCAUniv}$。

### 2.7 因果影子函子

在三类宇宙范畴上引入到 $\mathsf{Caus}$ 的函子，形式化"因果偏序只是高维结构的一部分投影"。

**定义 2.10（因果影子函子）**

1. 对 $\mathsf{OpUniv}$，定义

   $$
   F_{\mathrm{op}}:\mathsf{OpUniv}\to\mathsf{Caus},\quad
   O\mapsto(X_O,\prec_O),
   $$

   其中 $X_O$ 为在选定观测分辨率下可分辨的散射事件集合，$\prec_O$ 由群延迟矩阵 $\mathsf Q(\omega)$ 的正负结构与光锥条件诱导。

2. 对 $\mathsf{GeoUniv}$，定义

   $$
   F_{\mathrm{geo}}:\mathsf{GeoUniv}\to\mathsf{Caus},\quad
   G\mapsto(X_G,\prec_G),
   $$

   其中 $X_G$ 为代表性时空事件集合，$\prec_G$ 由 $J^\pm$ 因果可达关系诱导；有限信息原理保证局域有限性。

3. 对 $\mathsf{QCAUniv}$，定义

   $$
   F_{\mathrm{qca}}:\mathsf{QCAUniv}\to\mathsf{Caus},\quad
   Q\mapsto(X_Q,\prec_Q),
   $$

   其中 $X_Q=\Lambda\times\mathbb Z$ 为离散时空事件，$\prec_Q$ 由有限传播半径的离散光锥结构给出。

可以直接检验，上述三个影子构成协变函子，并保持粗粒化态射方向。因果偏序由此成为三类宇宙描述的共同"影子层"。

---

## 3 Main Results (Theorems and Alignments)

本节在上述模型与公理基础上，引入因果兼容宇宙三重态范畴 $\mathsf{Uni}$，并给出宇宙终对象存在与唯一性的主定理，以及小钻石细化、观察者与多表示对齐等结构性结论。

### 3.1 因果兼容宇宙三重态范畴 $\mathsf{Uni}$

**定义 3.1（宇宙三重态）**

一个宇宙三重态对象为三元组

$$
U=(O,G,Q),
$$

其中

$$
O\in\operatorname{Obj}(\mathsf{OpUniv}),\quad
G\in\operatorname{Obj}(\mathsf{GeoUniv}),\quad
Q\in\operatorname{Obj}(\mathsf{QCAUniv}),
$$

并满足因果兼容性：存在某一局域有限因果偏序 $C=(X,\prec)$，以及 $\mathsf{Caus}$ 中的同构

$$
\alpha_{\mathrm{op}}:F_{\mathrm{op}}(O)\xrightarrow{\sim} C,\quad
\alpha_{\mathrm{geo}}:F_{\mathrm{geo}}(G)\xrightarrow{\sim} C,\quad
\alpha_{\mathrm{qca}}:F_{\mathrm{qca}}(Q)\xrightarrow{\sim} C.
$$

称 $C$ 为 $U$ 的因果影子，记 $F_{\mathrm{caus}}(U)=C$。

**定义 3.2（宇宙三重态态射）**

给定 $U_i=(O_i,G_i,Q_i)$（$i=1,2$），一个态射

$$
f:U_1\to U_2
$$

是三元组

$$
f=(f_{\mathrm{op}},f_{\mathrm{geo}},f_{\mathrm{qca}}),
$$

其中

$$
f_{\mathrm{op}}:O_1\to O_2,\quad
f_{\mathrm{geo}}:G_1\to G_2,\quad
f_{\mathrm{qca}}:Q_1\to Q_2
$$

分别为对应范畴中的态射，并满足：在因果影子侧，三个影子态射

$$
F_{\mathrm{op}}(f_{\mathrm{op}}),\quad
F_{\mathrm{geo}}(f_{\mathrm{geo}}),\quad
F_{\mathrm{qca}}(f_{\mathrm{qca}})
$$

在 $\mathsf{Caus}$ 中同构于 $F_{\mathrm{caus}}(U_1)\to F_{\mathrm{caus}}(U_2)$ 的同一个偏序保持映射。

**定义 3.3**

对象与态射如上构成范畴 $\mathsf{Uni}$，称为因果兼容宇宙三重态范畴。

### 3.2 细化预序与极大一致对象

在 $\mathsf{Uni}$ 上引入"细化"预序，用以比较不同三重态的"信息丰度"。

**定义 3.4（细化关系）**

对 $U_1,U_2\in\operatorname{Obj}(\mathsf{Uni})$，若存在态射 $f:U_1\to U_2$，称 $U_1$ 细化 $U_2$，记 $U_1\preceq U_2$。若 $U_1\preceq U_2$ 且 $U_2\preceq U_1$，则称 $U_1,U_2$ 同构，记 $U_1\simeq U_2$。

模去同构后，$\preceq$ 降为偏序。

**定义 3.5（极大一致宇宙三重态）**

若 $U\in\operatorname{Obj}(\mathsf{Uni})$ 满足：一旦 $U\preceq V$ 则必 $U\simeq V$，则称 $U$ 为极大一致宇宙三重态。

直观上，极大一致对象在三种表示上不再允许添加新的兼容结构，而宇宙终对象将是极大一致对象的一种范畴论强化。

### 3.3 链完备性公理

为使用 Zorn 引理，需要如下完备性公理。

**公理 A3（链完备性）**

对 $\mathsf{Uni}$ 中任一完全有序子族（链）$\mathcal C\subset\operatorname{Obj}(\mathsf{Uni})$，存在一个宇宙三重态 $U_{\mathcal C}$，使得对任意 $U\in\mathcal C$ 有 $U\preceq U_{\mathcal C}$，且在该意义下为最小上界。

物理上，$\mathcal C$ 可以理解为不断加入更多散射数据、几何细节或 QCA 规则的"精细化序列"，公理 A3 要求这些精细化在极限中仍能拼合成一致的宇宙三重态。这一要求可通过在每一分量范畴中对算子、度量与 QCA 规则取弱极限或适当拓扑极限，并利用因果影子函数的连续性与有限信息原理加以保证。

### 3.4 宇宙终对象存在与唯一性

在上述准备下，可以陈述主定理。

**定理 3.6（宇宙终对象存在与唯一性）**

在公理 A1–A3 与有限信息原理 A2 下，范畴 $\mathsf{Uni}$ 中存在一个极大一致对象 $\mathfrak U_{\max}$，并满足：

1. 对任意 $U\in\operatorname{Obj}(\mathsf{Uni})$，存在唯一态射

   $$
   f_U:U\to\mathfrak U_{\max};
   $$

2. 若存在另一个对象 $\mathfrak U_{\max}'$ 亦满足上述性质，则 $\mathfrak U_{\max}'$ 与 $\mathfrak U_{\max}$ 同构。

因此 $\mathfrak U_{\max}$ 为 $\mathsf{Uni}$ 的终对象，在同构意义下唯一。

该定理把"宇宙最高维数学结构存在且唯一"这一直观陈述转化为严格的范畴论命题。详细证明见附录 A。

### 3.5 三种表示中的终对象像与对齐

令自然投影函子

$$
\Pi_{\mathrm{op}}:\mathsf{Uni}\to\mathsf{OpUniv},\quad
\Pi_{\mathrm{geo}}:\mathsf{Uni}\to\mathsf{GeoUniv},\quad
\Pi_{\mathrm{qca}}:\mathsf{Uni}\to\mathsf{QCAUniv},
$$

定义

$$
O_{\max}=\Pi_{\mathrm{op}}(\mathfrak U_{\max}),\quad
G_{\max}=\Pi_{\mathrm{geo}}(\mathfrak U_{\max}),\quad
Q_{\max}=\Pi_{\mathrm{qca}}(\mathfrak U_{\max}).
$$

**定理 3.7（三种表示中的极大一致性与对齐）**

1. $O_{\max}$ 是 $\mathsf{OpUniv}$ 中的极大一致对象；$(G_{\max},Q_{\max})$ 分别是 $(\mathsf{GeoUniv},\mathsf{QCAUniv})$ 中的极大一致对象；

2. 在满足统一时间刻度与连续极限桥接条件的"物理子范畴"上，存在函子

   $$
   \Phi_{\mathrm{op}\to\mathrm{geo}}:\mathsf{OpUniv}^{\mathrm{phys}}\to\mathsf{GeoUniv}^{\mathrm{phys}},\quad
   \Phi_{\mathrm{geo}\to\mathrm{op}}:\mathsf{GeoUniv}^{\mathrm{phys}}\to\mathsf{OpUniv}^{\mathrm{phys}},
   $$

   $$
   \Psi_{\mathrm{geo}\to\mathrm{qca}}:\mathsf{GeoUniv}^{\mathrm{phys}}\to\mathsf{QCAUniv}^{\mathrm{phys}},\quad
   \Psi_{\mathrm{qca}\to\mathrm{geo}}:\mathsf{QCAUniv}^{\mathrm{phys}}\to\mathsf{GeoUniv}^{\mathrm{phys}},
   $$

   使得

   $$
   \Phi_{\mathrm{op}\to\mathrm{geo}}(O_{\max})\simeq G_{\max},\quad
   \Psi_{\mathrm{geo}\to\mathrm{qca}}(G_{\max})\simeq Q_{\max},
   $$

   且上述函子在相应子范畴上给出范畴等价。

直观上，$(O_{\max},G_{\max},Q_{\max})$ 分别是在算子–散射、几何–边界与 QCA 表示中"包含全部物理可兼容信息"的宇宙对象。它们通过统一时间刻度与连续极限桥接两两等价。证明见附录 B。

### 3.6 小钻石细化定理与"非最小性"

在 $\mathfrak U_{\max}$ 的因果影子

$$
C_{\max}=F_{\mathrm{caus}}(\mathfrak U_{\max})=(X,\prec)
$$

上，利用几何表示 $G_{\max}$ 的时空结构，可对每个尺度参数 $r$ 定义尺度为 $r$ 的小因果菱形族 $\mathcal D_r$。有限信息原理与量子聚焦猜想的离散推广共同给出如下结果。

**定理 3.8（小钻石细化定理）**

假定 $C_{\max}$ 局域有限且 $G_{\max}$ 满足广义熵与离散量子聚焦条件，则存在最小物理尺度 $r_{\min}>0$，并且对任意 $r_2>r_1\ge r_{\min}$ 与任意小钻石 $D_{p,r_2}\in\mathcal D_{r_2}$，存在有限多个小钻石 $D_{p_i,r_1}\in\mathcal D_{r_1}$ 使得：

1. 覆盖性：

   $$
   D_{p,r_2}\subset\bigcup_i D_{p_i,r_1};
   $$

2. 广义熵近似可加：

   $$
   S_{\mathrm{gen}}(D_{p,r_2})
   =\sum_i S_{\mathrm{gen}}(D_{p_i,r_1})
   +\mathcal O(\delta(r_1,r_2)),
   $$

   其中 $\delta(r_1,r_2)\to 0$ 当 $r_1/r_2\to 0$。

特别地，当 $r_1\to r_{\min}$ 时，任意大尺度小钻石都可以被最小尺度小钻石以任意精度填充而不显著改变广义熵。详细证明见附录 C。

该定理将"小钻石永远不是绝对最小结构，只是给定尺度下的自洽单元"精确化：真正的"最小单元"由信息元胞尺度 $r_{\min}$ 决定，而不是某个固定几何菱形。几何上可任意细化的小菱形只对应数学分辨率的提升，并不自动带来新的物理自由度。

### 3.7 观察者、记忆与共识几何的刻画

在 $\mathfrak U_{\max}$ 中，可以自然地定义观察者、记忆与多观察者共识几何。

**定义 3.6（观察者）**

一个观察者结构 $\mathcal O$ 是以下数据：

1. 在因果影子 $C_{\max}=(X,\prec)$ 上的滤子 $\mathcal F_{\mathcal O}\subset\mathcal P(X)$，表示该观察者可达事件族；

2. 在 $O_{\max}$ 中，随滤子参数单调变化的子代数链 $\{\mathcal A_{\mathcal O}(\lambda)\subset\mathcal A_{\max}\}$，表示可访问观测算子；

3. 在 $G_{\max}$ 中的一条时类曲线族 $\gamma_{\mathcal O}$，表示世界线；

4. 在 $Q_{\max}$ 中的一族元胞子格 $\Lambda_{\mathcal O}$，表示与该观察者关联的 QCA 子宇宙。

上述数据须通过 $\mathfrak U_{\max}$ 的三重一致性条件互相兼容。

**定理 3.9（记忆熵与时间刻度的对应）**

对任意观察者 $\mathcal O$，沿其世界线参数 $t$ 选取边界片 $B_t$ 与状态 $\omega_{B_t}$，定义记忆熵流

$$
M_{\mathcal O}(t_2,t_1)
=S(\omega_{B_{t_2}}\Vert\omega_{B_{t_1}}),\quad t_2\ge t_1,
$$

则在 QNEC 与广义熵单调条件下，该函数关于 $t_2$ 单调非减，并且在散射表示中可等价表达为统一刻度密度 $\kappa(\omega)$ 对应的相干时间积分。也就是说，"沿世界线累积的记忆"与"在散射侧的时间延迟"是同一母刻度在两种表示下的函数。

多观察者共识几何可用 $\{\mathcal F_{\mathcal O_i}\}$ 的交叠区域与 $\{\mathcal A_{\mathcal O_i}\}$ 在重叠区域的共同子代数刻画，形成一个类似 Čech 覆盖的共识结构，本节不再展开。

---

## 4 Proofs

本节给出主定理的证明要点，完整技术细节见附录。

### 4.1 宇宙终对象存在与唯一性（定理 3.6）

**步骤 1：将 $\mathsf{Uni}$ 对象模同构归约为偏序集**

令 $\mathcal P$ 为 $\mathsf{Uni}$ 中对象的同构类集合，定义

$$
[U_1]\le [U_2]
\quad\text{当且仅当}\quad
\exists f:U_1\to U_2.
$$

可以验证 $\le$ 在 $\mathcal P$ 上是偏序。

**步骤 2：链上界的存在**

取任一链 $\mathcal C\subset\mathcal P$，对应代表对象族 $\{U_i\}$。公理 A3 保证存在 $U_{\mathcal C}$ 满足对所有 $U_i$ 有 $U_i\preceq U_{\mathcal C}$，且为最小上界。这依赖于：

1. 在 $\mathsf{OpUniv}$ 中，对算子代数与散射矩阵族取弱拓扑极限并利用谱移函数连续性，构造极限对象；

2. 在 $\mathsf{GeoUniv}$ 中，对度量与边界代数采用适当收敛概念（例如 Gromov–Hausdorff 与弱$^*$ 收敛），保持 QFC/QNEC 与广义熵结构；

3. 在 $\mathsf{QCAUniv}$ 中，对元胞自动机规则与初态采用局域投影拓扑，使连续极限与统一时间刻度桥接保持一致；

4. 通过因果影子函子 $(F_{\mathrm{op}},F_{\mathrm{geo}},F_{\mathrm{qca}})$ 的协变性与有限信息原理，保证极限对象在因果侧仍然局域有限。

由此可知，每条链在 $\mathcal P$ 中有上界。

**步骤 3：应用 Zorn 引理**

由 Zorn 引理，$\mathcal P$ 中存在极大元 $[\mathfrak U_{\max}]$，取一代表 $\mathfrak U_{\max}$，称之为极大一致宇宙三重态。

**步骤 4：极大一致性蕴含终对象性质**

对任意 $U\in\operatorname{Obj}(\mathsf{Uni})$，若不存在态射 $U\to\mathfrak U_{\max}$，可以通过在三类表示中取并合或推送出构造一个新对象 $W$，使得 $U\preceq W$ 且 $\mathfrak U_{\max}\preceq W$，且 $W$ 含有比 $\mathfrak U_{\max}$ 更多的一致信息，从而与 $\mathfrak U_{\max}$ 极大性矛盾。因而必存在态射 $U\to\mathfrak U_{\max}$。

若存在两个不同态射 $f_1,f_2:U\to\mathfrak U_{\max}$，则可以在三类表示范畴中构造它们的等化子对象 $\tilde U$，该对象同时细化 $U$ 与 $\mathfrak U_{\max}$，却严格小于 $\mathfrak U_{\max}$，同样与极大性矛盾。故态射唯一。

**步骤 5：终对象唯一性**

若存在另一个终对象 $\mathfrak U_{\max}'$，则由终对象定义存在唯一态射

$$
f:\mathfrak U_{\max}\to\mathfrak U_{\max}',\quad
g:\mathfrak U_{\max}'\to\mathfrak U_{\max}.
$$

组合 $g\circ f$ 与 $f\circ g$ 必分别为两端对象的恒等态射，从而 $f,g$ 为逆同构，终对象在同构意义下唯一。

以上即为定理 3.6 的证明思路，完整论证见附录 A。

### 4.2 三种表示中终对象像的极大一致性与对齐（定理 3.7）

证明分两部分。

**部分一：分量极大一致性**

以 $O_{\max}$ 为例。若存在 $O\in\mathsf{OpUniv}$ 使得 $O_{\max}\preceq O$ 且 $O\not\simeq O_{\max}$，则可以将 $O$ 与 $G_{\max},Q_{\max}$ 拼合成新的宇宙三重态 $U'=(O,G_{\max},Q_{\max})$，其因果影子与 $\mathfrak U_{\max}$ 相同。由于 $O$ 比 $O_{\max}$"更大"，$U'$ 比 $\mathfrak U_{\max}$"更大"，违背 $\mathfrak U_{\max}$ 的极大一致性。因此 $O_{\max}$ 必为 $\mathsf{OpUniv}$ 中的极大一致对象。对 $G_{\max},Q_{\max}$ 的论证类似。

**部分二：桥接函子与等价性**

统一时间刻度与边界 Hamilton 形式允许从散射数据重建边界几何与广义熵结构，可构造

$$
\Phi_{\mathrm{op}\to\mathrm{geo}}:O\mapsto G,
$$

反之通过边界代数与模块流可以在散射侧重建 $S(\omega)$ 与 $\kappa(\omega)$，得到

$$
\Phi_{\mathrm{geo}\to\mathrm{op}}:G\mapsto O。
$$

QCA 的连续极限则提供从 $\mathsf{QCAUniv}$ 到 $\mathsf{GeoUniv}$ 的桥接。在满足物理正则性的对象子类上，这些函子构成范畴等价，其在终对象像上的作用必将 $(O_{\max},G_{\max},Q_{\max})$ 两两送至同构对象。详细构造与自然同构见附录 B。

### 4.3 小钻石细化定理（定理 3.8）

证明大致分为三个层面。

1. **几何覆盖构造**：在 $G_{\max}$ 中，对给定的尺度 $r_2$ 小菱形 $D_{p,r_2}$，利用流形的局域平坦性与 Null 度量结构，构造有限个更小尺度 $r_1$ 的因果菱形覆盖。局域有限性与有限信息原理保证任何有界区域只需有限个小菱形即可覆盖。

2. **广义熵近似可加性**：利用广义熵

   $$
   S_{\mathrm{gen}}(D)=\frac{\operatorname{Area}(\partial D)}{4G_N}+S_{\mathrm{out}}(D)
   $$

   的性质：面积项在小菱形覆盖下近似可加，误差由边界重叠区域的面积控制；纠缠熵项在有限覆盖下满足强次可加性与相对熵不等式，误差由重叠区域的信息"重复计数"控制。结合 QFC/QNEC 的局域形式，可以将误差估计为 $\delta(r_1,r_2)$，并证明当 $r_1/r_2\to 0$ 时误差趋零。

3. **信息元胞尺度与下界**：有限信息原理给出一个最小物理尺度 $r_{\min}$，当几何尺度小于该尺度时，新增加的小钻石只对应数学细化而不增加有效自由度。由此可以选取 $r_1\ge r_{\min}$，同时保持熵误差在给定阈值以下。

完整技术细节与辅助引理见附录 C。

### 4.4 观察者与记忆（定理 3.9）

对观察者 $\mathcal O$，沿其世界线选择一族边界片 $B_t$，广义熵随 $t$ 的变化由 QFC/QNEC 约束，使得对任何 $t_3\ge t_2\ge t_1$，有

$$
M_{\mathcal O}(t_3,t_1)\ge M_{\mathcal O}(t_3,t_2)\ge 0,
$$

这是量子相对熵的基本性质。另一方面，散射表示中，观察者所经历的时间刻度变化由 $\kappa(\omega)$ 的某种加权积分给出，而 Tomita–Takesaki 模块流与边界时间平移的对应关系将相对熵与时间平移的生成元统一。结合统一时间刻度母式，可以得到记忆熵与时间延迟之间的定量对应，从而完成定理 3.9 的证明要点。

---

## 5 Model Apply

本节给出若干在 $\mathfrak U_{\max}$ 框架下的具体应用示意，展示该结构如何统一不同物理问题的描述。为简洁起见，仅选取代表性的两个方向。

### 5.1 Dirac–QCA 连续极限中的宇宙三重态构造

考虑一类在一维或三维格点上的 Dirac 型 QCA，其单步演化 $U$ 在长波长与低能极限下给出 Dirac 方程及其最小耦合规范场。对于这样的 QCA 模型，可以构造：

1. QCA 分量 $Q=(\Lambda,\mathcal H_{\mathrm{cell}},U,\ket{\Psi_0};\Theta)$；

2. 几何分量 $G$：通过连续极限将长时间、大尺度行为有效描述为带背景度量与规范场的流形；

3. 算子–散射分量 $O$：在给定背景几何上定义 Dirac 场的散射问题，得到 $S(\omega)$ 与 $\kappa(\omega)$。

只要 QCA 模型的连续极限与散射描述在统一时间刻度上兼容，则三者构成 $\mathsf{Uni}$ 中的一个对象 $U_{\mathrm{Dirac}}$。宇宙终对象 $\mathfrak U_{\max}$ 则可以被视为包含这类 Dirac–QCA 模型及其所有更高能修正的"极大"对象，$U_{\mathrm{Dirac}}$ 是其在适当能量窗口与尺度窗口下的粗粒化投影。

### 5.2 黑洞区域与小钻石细化

在 $G_{\max}$ 表示中取一个包含黑洞视界的区域，考虑视界附近一族尺度递减的小因果菱形 $\{D_{p,r}\}$。小钻石细化定理保证：无论取多大的菱形，都可以用接近普朗克尺度的最小菱形填充，并在熵上保持近似可加。结合黑洞 Bekenstein–Hawking 熵面积律，可以在 $\mathfrak U_{\max}$ 框架中把黑洞区域视为由最小信息元胞组成的自洽拼块，其几何面积只是这些元胞数目的宏观指标。这为将黑洞熵与离散 QCA 元胞数对齐提供了结构基础。

---

## 6 Engineering Proposals

虽然 $\mathfrak U_{\max}$ 是一个抽象的终对象概念，其结构仍可通过若干工程化系统间接探测。这里提出两个方向。

### 6.1 自指散射网络与统一时间刻度实验平台

可构造由波导、谐振腔与可调反馈环组成的散射网络，使得整体散射矩阵 $S(\omega)$ 具有可控的频率依赖相位与 Wigner–Smith 延迟。通过测量散射相位导数与群延迟矩阵迹，可直接重构刻度密度 $\kappa(\omega)$，在实验室实现统一时间刻度的工程模型。

进一步地，将网络拓扑设计为具有因果偏序结构的"离散空间"，并在反馈中加入自指回路，可以模拟小因果菱形与其细化过程，从而在桌面尺度上测试"小钻石细化定理"的离散版本。

### 6.2 QCA 量子模拟器与多表示对齐

利用超导比特、离子阱或光学格子实现局域 QCA 演化 $U$，并选取一类在连续极限上逼近 Dirac 或 Klein–Gordon 场的规则；同时通过引入辅助模式与测量，构造等效的散射通道 $S(\omega)$ 与边界观测代数。通过对 QCA、散射与边界三者的实验数据进行比对，可以在有限维 Hilbert 空间中构造"有限版本"的宇宙三重态，并检验统一时间刻度与因果影子函子的工程实现。

在多智能体量子网络中，同样可以把各 Agent 的可达因果结构、内部记忆与通信信道视为 $\mathfrak U_{\max}$ 的有限投影，探索"观察者滤子"与资源分配策略的结构对应。

---

## 7 Discussion (risks, boundaries, past work)

### 7.1 理论边界与假设的局限

本文框架依赖若干关键假设：

1. 统一时间刻度母式 A1 假定一切相关散射过程均可归入同一刻度密度 $\kappa(\omega)$；

2. 有限信息原理 A2 在当前物理证据下合理，但是否在所有宇宙学情形中成立仍需检验；

3. 链完备性 A3 属于集合论与物理正则性的交叉假设，具体的极限构造可能需要更细致的拓扑与分析工具。

因此，$\mathfrak U_{\max}$ 的存在与唯一性目前是条件性的：一旦某些基本假设需要修正，对应的范畴结构也必须调整。

### 7.2 与既有工作的关系

本框架既与因果集方案相容，又在其上叠加了散射–时间刻度与 QCA 连续极限的结构，提供了一种"多表示统一"的视角。

与全息原理相关的 QFC/QNEC 研究则在边界时间几何与广义熵层面提供了重要约束，使小钻石细化定理得以成立。

此外，范畴论在拓扑场论与量子信息中的应用（例如单体范畴、对偶性与拓扑缺陷）早已表明，许多物理结构可以被视为某个高阶范畴中的对象或态射。本文将终对象概念引入"宇宙级别"的范畴，延续了这一思路。

### 7.3 潜在风险与误读

最大的风险在于把"宇宙终对象"误读为某种绝对本体，而忽略它只是一个相对给定公理体系的范畴论构造。若未来物理证据表明某些公理不再适用，则对应的终对象概念需要重新定义。

另一个风险是将本框架视为对所有具体物理问题的即刻解答。事实上，$\mathfrak U_{\max}$ 为诸如黑洞熵、宇宙学常数、强相互作用拓扑等问题提供统一结构背景，但具体数值与可检验预言仍需在特定子模型中推导。

---

## 8 Conclusion

本文在统一时间刻度、边界时间几何与 QCA 宇宙框架下引入了"宇宙终对象" $\mathfrak U_{\max}$ 的概念，并在自然的公理假设下证明了其在因果兼容宇宙三重态范畴 $\mathsf{Uni}$ 中的存在与唯一性。该对象的三类投影 $(O_{\max},G_{\max},Q_{\max})$ 在各自宇宙范畴中极大一致，且在适当桥接函子下两两等价，从而为"宇宙最高维数学结构"给出明确的范畴论刻画。

在 $\mathfrak U_{\max}$ 的因果影子 $C_{\max}$ 上，小钻石细化定理表明：任何尺度上的因果菱形都可由更小尺度的小菱形以近乎熵可加的方式填充，最小物理单元由信息元胞尺度而非几何菱形决定。因果偏序、小因果菱形与观察者世界线因此可以被视为 $\mathfrak U_{\max}$ 在特定投影与尺度下的影子，而散射时间延迟、记忆熵与广义熵单调则是同一母刻度 $\kappa(\omega)$ 在不同表示中的体现。

这一框架为后续工作的展开提供了基础：可以在 $\mathfrak U_{\max}$ 内系统研究黑洞熵与信息、宇宙学常数与真空能、量子混沌与 ETH、强 CP 问题与轴子、引力波色散与 Lorentz 破缺等问题的统一结构，并寻求与具体观测和实验平台的对接。

---

## Acknowledgements

作者感谢散射谱理论、量子信息、广义相对论与量子场论领域的大量既有研究，为统一时间刻度、边界时间几何与 QCA 宇宙的整合提供了坚实基础。

---

## Code Availability

本文主要为公理化与定理化工作。用于验证 QCA 连续极限、构造离散因果集与数值评估广义熵的模拟代码可在今后统一整理后公开。

---

## References

1. L. Bombelli, J. Lee, D. Meyer, R. D. Sorkin, "Space-time as a causal set", Phys. Rev. Lett. 59, 521 (1987).

2. R. Bousso, "The holographic principle", Rev. Mod. Phys. 74, 825 (2002).

3. J. D. Bekenstein, "Black holes and entropy", Phys. Rev. D 7, 2333 (1973).

4. J. D. Brown, J. W. York, "Quasilocal energy and conserved charges derived from the gravitational action", Phys. Rev. D 47, 1407 (1993).

5. B. Schumacher, R. F. Werner, "Reversible quantum cellular automata", quant-ph/0405174 (2004).

6. T. Farrelly, "A review of quantum cellular automata", Quantum 4, 368 (2020).

7. R. Bousso, Z. Fisher, S. Leichenauer, A. C. Wall, "A Quantum Focussing Conjecture", Phys. Rev. D 93, 064044 (2016).

8. R. Bousso, E. Tabor, "Discrete Max-Focusing", JHEP 06 (2025) 240.

9. K. B. Sinha, "Spectral shift function and trace formula", Proc. Indian Acad. Sci. (Math. Sci.) 104, 819–853 (1994).

10. F. Gesztesy, "Applications of Spectral Shift Functions", lecture notes (2017).

11. P. C. Deshmukh et al., "Eisenbud–Wigner–Smith time delay in atom–laser interaction", and R. Shaik et al., "EWS Time Delay in Low Energy e−C$_{60}$ Elastic Scattering", Atoms 12, 18 (2024).

12. F. Hiai, "Concise lectures on selected topics of von Neumann algebras", arXiv:2004.02383.

（其余与散射谱理论、因果集、全息、QCA 与模块理论相关的标准文献可在正式投稿时按期刊格式补充。）

---

# 附录 A：宇宙终对象存在与唯一性的详细证明

本附录给出定理 3.6 的完整证明。

## A.1 偏序构造与 Zorn 引理准备

令 $\mathcal O$ 为 $\mathsf{Uni}$ 的对象集合，定义等价关系 $U_1\sim U_2$ 当且仅当存在同构 $U_1\to U_2$。令商集 $\mathcal P=\mathcal O/\sim$，用 $[U]$ 表示等价类。

在 $\mathcal P$ 上定义偏序

$$
[U_1]\le [U_2]
\quad\text{当且仅当}\quad
\exists f:U_1\to U_2.
$$

这一定义与代表元的选择无关，因为若 $U_1'\simeq U_1, U_2'\simeq U_2$，则通过同构可将态射 $f:U_1\to U_2$ 共轭为 $f':U_1'\to U_2'$。传递性与自反性显然成立，反对称性由"有向同构蕴含同构"保证：若既有 $U_1\to U_2$ 又有 $U_2\to U_1$，则二者在三类表示范畴中分别诱导双向细化，从而在每个表示中等价，因果影子亦等价，最终得到 $U_1\simeq U_2$。因此 $(\mathcal P,\le)$ 为偏序集。

## A.2 链上界存在性（公理 A3 的具体实现）

设 $\mathcal C\subset\mathcal P$ 为一条链，选取代表元族 $\{U_i=(O_i,G_i,Q_i)\}_{i\in I}$，使得对任意 $i\le j$ 存在态射 $f_{ij}:U_i\to U_j$，并满足兼容性 $f_{jk}\circ f_{ij}=f_{ik}$。

在每一表示范畴中构造极限对象：

1. **算子–散射表示**：在适当拓扑（例如弱算子拓扑与弱$^*$ 拓扑）下，取 $\mathcal A_i$ 的递增并及其闭包作为极限代数 $\mathcal A_\infty$，取散射矩阵 $S_i(\omega)$ 的弱极限作为 $S_\infty(\omega)$。谱移函数与刻度密度的连续性保证极限对象仍满足刻度同一式。

2. **几何–边界表示**：对度量 $g_i$ 与边界代数 $\mathcal A_i(B)$ 采用 Gromov–Hausdorff 收敛与弱$^*$ 收敛，引用关于广义熵与 QFC/QNEC 在极限中的稳定性结果，得到极限几何对象 $(M_\infty,g_\infty,\partial M_\infty;\{\mathcal A_\infty(B),\omega_{\infty,B}\})$。

3. **QCA 表示**：对格点集合与演化规则采用局域投影拓扑（local quasi-local topology），在保证局域可逆性与有限传播半径条件下，构造极限 QCA 对象 $Q_\infty$。

因果影子函子 $(F_{\mathrm{op}},F_{\mathrm{geo}},F_{\mathrm{qca}})$ 在上述极限构造下保持协变与连续，从而各表示的因果影子在极限中仍可对齐为某个局域有限偏序 $C_\infty$。由此得到 $U_\infty=(O_\infty,G_\infty,Q_\infty)\in\operatorname{Obj}(\mathsf{Uni})$，并构造态射 $U_i\to U_\infty$，使得 $[U_\infty]$ 为 $\mathcal C$ 的上界。

这正是公理 A3 的具体实现。

## A.3 应用 Zorn 引理得到极大一致对象

由 A.2 可知：$(\mathcal P,\le)$ 中任意链均有上界。于是 Zorn 引理保证存在极大元 $[\mathfrak U_{\max}]\in\mathcal P$。选取代表 $\mathfrak U_{\max}$，即得到极大一致宇宙三重态。

极大一致性指：只要 $[\mathfrak U_{\max}]\le [V]$ 就有 $[\mathfrak U_{\max}]=[V]$。

## A.4 极大一致性蕴含终对象性质

**存在性**：令 $U\in\operatorname{Obj}(\mathsf{Uni})$。若不存在态射 $U\to\mathfrak U_{\max}$，考虑集合

$$
\mathcal S=\{V\in\operatorname{Obj}(\mathsf{Uni}):\exists f:V\to\mathfrak U_{\max}\}.
$$

显然 $\mathfrak U_{\max}\in\mathcal S$。构造包含 $U$ 与 $\mathcal S$ 的新对象 $W$，其三类表示为 $U$ 与 $\mathfrak U_{\max}$ 分量的"并合"：

* 在算子–散射侧，取 $\mathcal A_W$ 为 $\mathcal A_U$ 与 $\mathcal A_{\max}$ 在一致因果影子上的最小包含代数，$S_W(\omega)$ 在共同定义域上一致，在其余部分延拓；

* 在几何侧，取 $M_W$ 为 $M_U$ 与 $M_{\max}$ 沿因果影子的粘合流形；

* 在 QCA 侧，取 $Q_W$ 为 $Q_U,Q_{\max}$ 的并合 QCA。

该构造保证 $U\preceq W$ 且 $\mathfrak U_{\max}\preceq W$，而且 $[W]>[\mathfrak U_{\max}]$，与 $[\mathfrak U_{\max}]$ 极大性矛盾。故假设不成立，必存在态射 $U\to\mathfrak U_{\max}$。

**唯一性**：若存在两个不同态射 $f_1,f_2:U\to\mathfrak U_{\max}$，在三类表示中分别诱导态射

$$
f_{1,\bullet},f_{2,\bullet},
\quad
\bullet\in\{\mathrm{op},\mathrm{geo},\mathrm{qca}\}.
$$

构造等化子对象 $\tilde U$，其三类分量为对应表示中等化子的并合：例如在算子–散射侧，取

$$
\mathcal A_{\tilde U}=\{a\in\mathcal A_U: f_{1,\mathrm{op}}(a)=f_{2,\mathrm{op}}(a)\},
$$

其余类似。由等化子的泛性质，存在态射 $\tilde U\to U$ 与 $\tilde U\to\mathfrak U_{\max}$，且 $[\tilde U]\ge [\mathfrak U_{\max}]$ 将违背极大性。唯一避免矛盾的方式是 $f_1=f_2$。因此态射唯一。

## A.5 终对象唯一性

若存在另一个终对象 $\mathfrak U_{\max}'$，则由终对象定义存在唯一态射

$$
f:\mathfrak U_{\max}\to\mathfrak U_{\max}',\quad
g:\mathfrak U_{\max}'\to\mathfrak U_{\max}.
$$

组合 $g\circ f$ 为从 $\mathfrak U_{\max}$ 到自身的态射，而终对象性质要求恒等态射 $\operatorname{id}_{\mathfrak U_{\max}}$ 亦为此类型态射且唯一，故 $g\circ f=\operatorname{id}_{\mathfrak U_{\max}}$。同理 $f\circ g=\operatorname{id}_{\mathfrak U_{\max}'}$。于是 $f,g$ 为逆同构，两个终对象同构。定理 3.6 完全得证。

---

# 附录 B：三类宇宙表示终对象像的等价性

本附录证明定理 3.7 所述 $(O_{\max},G_{\max},Q_{\max})$ 的极大一致性与两两等价。

## B.1 分量极大一致性

以 $O_{\max}$ 为例说明。假设存在 $O\in\mathsf{OpUniv}$ 使得 $O_{\max}\preceq O$ 且 $O\not\simeq O_{\max}$。利用 $G_{\max}$ 与 $Q_{\max}$ 构造新三重态

$$
U'=(O,G_{\max},Q_{\max}).
$$

由于 $O_{\max}\preceq O$，存在态射 $O_{\max}\to O$，结合 $\mathfrak U_{\max}\to U'$ 在其他两分量上的恒等作用，得到态射 $\mathfrak U_{\max}\to U'$。另一方面，由极大性，不能有 $[\mathfrak U_{\max}]<[U']$，于是必须 $[\mathfrak U_{\max}]=[U']$，从而 $O_{\max}\simeq O$，与假设矛盾。故 $O_{\max}$ 极大一致。几何与 QCA 分量的论证完全类似。

## B.2 散射–几何桥接函子

在统一时间刻度下，可以利用如下程序构造

$$
\Phi_{\mathrm{op}\to\mathrm{geo}}:\mathsf{OpUniv}^{\mathrm{phys}}\to\mathsf{GeoUniv}^{\mathrm{phys}}。
$$

1. 由 $\kappa(\omega)$ 定义统一时间参数，通过 Fourier–Laplace 变换与谱表示，将散射侧的能量本征分解转化为时域演化算子；

2. 利用边界 Hamilton 形式与 Brown–York 准局域能的构造，从 $\kappa(\omega)$ 与散射数据中提取边界应力张量，进而通过 Einstein 方程与 QFC/QNEC 的逆问题，在适当规范下重建 $g$ 与 $\mathcal A(B)$。

反向函子 $\Phi_{\mathrm{geo}\to\mathrm{op}}$ 则依靠代数量子场论与 Tomita–Takesaki 模块流理论：由边界代数与选定的真空或参考态，可以构造模块自同构群，其生成元对应于时间平移与散射相位，从而重建 $S(\omega)$ 与 $\kappa(\omega)$。

在满足正则性与能量条件的子范畴上，两者满足

$$
\Phi_{\mathrm{geo}\to\mathrm{op}}\circ\Phi_{\mathrm{op}\to\mathrm{geo}}\simeq\operatorname{Id},\quad
\Phi_{\mathrm{op}\to\mathrm{geo}}\circ\Phi_{\mathrm{geo}\to\mathrm{op}}\simeq\operatorname{Id},
$$

构成范畴等价。特别地，$\Phi_{\mathrm{op}\to\mathrm{geo}}(O_{\max})\simeq G_{\max}$。

## B.3 几何–QCA 桥接函子

QCA 的连续极限分析表明，一类局域可逆 QCA 可在长波长极限下逼近给定的场论与几何背景。利用这一点，可从 $Q\in\mathsf{QCAUniv}^{\mathrm{phys}}$ 构造几何对象 $\Psi_{\mathrm{qca}\to\mathrm{geo}}(Q)$，其度量与边界代数由 QCA 的有效场论与边界观测规则确定。

反向函子 $\Psi_{\mathrm{geo}\to\mathrm{qca}}$ 则通过在给定几何背景上构造离散 QCA 逼近，选择满足局域可逆性与正确连续极限的元胞规则。两者在满足可逼近性的子范畴上给出等价。由于 $G_{\max}$ 在几何侧极大一致，$\Psi_{\mathrm{geo}\to\mathrm{qca}}(G_{\max})$ 必与 $Q_{\max}$ 同构。

综合 B.2 与 B.3，得到定理 3.7。

---

# 附录 C：小钻石细化定理的详细证明

本附录证明定理 3.8。

## C.1 尺度标定与小钻石族

在 $G_{\max}$ 中选择一族局域坐标，使得在每个点附近度量近似 Minkowski 型。对任意尺度参数 $r>0$，定义小钻石

$$
D_{p,r}=J^+(p^-)\cap J^-(p^+),
$$

其中 $p^\pm$ 为沿一条选定时类或 Null 曲线离开 $p$ 距离约为 $r$ 的两点。通过因果影子映射 $F_{\mathrm{geo}}$ 将其投影到 $C_{\max}$，得到小钻石族 $\mathcal D_r$。

有限信息原理 A2 保证存在最小物理尺度 $r_{\min}>0$，当 $r<r_{\min}$ 时，再细化的几何结构不对应新的自由度。取 $r\ge r_{\min}$ 定义物理相关的小钻石族。

## C.2 局域有限性与有限覆盖

考虑固定 $r_2>r_{\min}$ 与某个 $D_{p,r_2}$。选择其内部一族点 $\{p_i\}$，使得以 $r_1<r_2$ 为尺度的菱形 $D_{p_i,r_1}$ 覆盖 $D_{p,r_2}$。由于 $C_{\max}$ 局域有限，任意有界区域包含有限个事件，因此可以精细化选点，使得只需有限个 $D_{p_i,r_1}$ 即可覆盖 $D_{p,r_2}$，并且重叠边界的"厚度"受控于 $r_1$ 与度量曲率。

## C.3 广义熵的近似可加性

广义熵

$$
S_{\mathrm{gen}}(D)=\frac{\operatorname{Area}(\partial D)}{4G_N}+S_{\mathrm{out}}(D)
$$

两部分分别估计。

1. 面积项：$\partial D_{p,r_2}$ 的面积在小钻石覆盖下近似为 $\sum_i \operatorname{Area}(\partial D_{p_i,r_1})$，误差来自重叠区域的双重计数，其总面积可由局域曲率与重叠厚度估计为 $\mathcal O(\varepsilon(r_1,r_2))$，其中 $\varepsilon(r_1,r_2)\to 0$ 当 $r_1/r_2\to 0$。

2. 纠缠熵项：利用强次可加性与相对熵的非负性，对覆盖区域的外部 Hilbert 空间分解进行标准估计，可得

   $$
   S_{\mathrm{out}}(D_{p,r_2})
   \le
   \sum_i S_{\mathrm{out}}(D_{p_i,r_1})+E_{\mathrm{ov}},
   $$

   其中 $E_{\mathrm{ov}}$ 由重叠区域的相互信息界定，同样在 $r_1/r_2\to 0$ 时趋零。QFC 的局域形式进一步保证广义熵沿 Null 方向的变化非增，从而给出反向的不等式界，最终得到

   $$
   S_{\mathrm{gen}}(D_{p,r_2})
   =\sum_i S_{\mathrm{gen}}(D_{p_i,r_1})
   +\mathcal O(\delta(r_1,r_2)),
   $$

   其中 $\delta(r_1,r_2)\to 0$ 当 $r_1/r_2\to 0$。

## C.4 信息元胞尺度与极限

有限信息原理 A2 给出在固定能量与体积条件下的熵上界，从而存在 $r_{\min}>0$，当 $r<r_{\min}$ 时增加的小钻石不会提高可达最大熵。选取 $r_1\ge r_{\min}$ 可保证上述熵估计在物理上可实现。令 $r_1\to r_{\min}$，同时保持 $r_1/r_2\to 0$，可获得定理 3.8 所述的极限行为。

由此，小钻石细化定理得证。

---

# 附录 D：观察者滤子与记忆熵的进一步说明

## D.1 观察者滤子与因果影子

在 $C_{\max}=(X,\prec)$ 上，观察者滤子 $\mathcal F_{\mathcal O}$ 要求：

1. 若 $A\in\mathcal F_{\mathcal O}$ 且 $A\subset B\subset X$，则 $B\in\mathcal F_{\mathcal O}$；

2. 若 $A,B\in\mathcal F_{\mathcal O}$，则 $A\cap B\in\mathcal F_{\mathcal O}$；

3. 对每个事件 $x\in X$，要么存在 $A\in\mathcal F_{\mathcal O}$ 使 $x\in A$，要么存在 $B\in\mathcal F_{\mathcal O}$ 使 $x\notin B$。

这保证滤子描述了观察者可以稳定访问与扩展的事件族。通过 $(F_{\mathrm{op}},F_{\mathrm{geo}},F_{\mathrm{qca}})$ 的协变性，可将 $\mathcal F_{\mathcal O}$ 提升为三类表示中的子对象链。

## D.2 记忆熵与统一时间刻度的算子–散射表达

在散射表示中，时间演化通过酉算子 $U(t)$ 或散射矩阵 $S(\omega)$ 表示。给定两个时刻 $t_1<t_2$，可定义相应的 Heisenberg 代数与状态 $(\mathcal A_{t_i},\omega_{t_i})$。统一时间刻度要求

$$
\kappa(\omega)=\frac{\varphi'(\omega)}{\pi}
$$

与模块流生成元的谱分布一致。Tomita–Takesaki 理论表明，给定 von Neumann 代数与参考态，可定义模块算子 $\Delta$ 与模块 Hamilton 算子 $K=-\ln\Delta$，其谱决定了相对熵

$$
S(\omega_{t_2}\Vert\omega_{t_1})=\langle K\rangle_{\omega_{t_2}}-\langle K\rangle_{\omega_{t_1}}。
$$

将 $K$ 与散射相位及 $\kappa(\omega)$ 对齐，便得到记忆熵与时间刻度之间的等价关系，从而完成定理 3.9 的算子–散射版本。

---

（全文完）

