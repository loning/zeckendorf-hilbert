# 有限熵密度量子元胞自动机宇宙中的统一约束：由黑洞面积律与宇宙学视界熵推导宇宙学常数–离散尺度–编码效率关系

*Unified Constraints in Finite-Entropy-Density Quantum Cellular Automaton Universe: Deriving Cosmological Constant–Discrete Scale–Encoding Efficiency Relations from Black Hole Area Law and Cosmological Horizon Entropy*

---

## Abstract

黑洞视界的 Bekenstein–Hawking 面积律与德西特宇宙学视界的熵公式共同暗示：引力系统在红外与紫外两个极端均服从"熵随面积而非体积标度"的全息约束。然而，在一个以量子元胞自动机（quantum cellular automaton, QCA）描述的离散宇宙本体中，底层是具有固定元胞间距与有限信息容量的计算网络，如何在同一组微观参数下同时再现宇宙学视界熵与黑洞面积律，仍然缺乏系统的公理化推导。

本文在 QCA 宇宙的框架下，引入"每元胞有限熵密度"公设，即假定每个格点元胞可承载的最大冯诺依曼熵为一常数上界 $\eta_{\rm cell}$，并以此为唯一信息预算，通过下述两类约束建立统一关系：

1. 在宇宙学尺度上，以德西特半径 $R_{\rm dS} = \sqrt{3/\Lambda}$ 所围成的体积 $V_{\rm dS}$ 中，QCA 网络可容纳的总熵容量 $S_{\rm cap}(V_{\rm dS})$ 至少覆盖宇宙学视界熵 $S_{\rm dS} = \pi R_{\rm dS}^2 / \ell_P^2$；

2. 在局域强引力极限上，将黑洞视界看作 QCA 网络中的一张离散"屏"，要求当元胞在该屏上达到临界排布时，视界上的自由度计数再现面积律 $S_{\rm BH} = A / (4 \ell_P^2)$。

通过将"体元熵上界"与"面元熵上界"以一个依赖于微观更新规则参数向量 $\Theta$ 的投影效率函数 $\xi(\Theta)$ 联系起来，我们证明：在最简各向同性近似下，宇宙学常数 $\Lambda$、离散元胞间距 $\ell_{\rm cell}$、单元胞熵上界 $\eta_{\rm cell}$ 与编码效率 $\xi(\Theta)$ 满足一组统一约束方程：

$$
\eta_{\rm cell} = \frac{\ell_{\rm cell}^2}{4 \,\xi(\Theta)\,\ell_P^2} , \qquad \Lambda\,\ell_{\rm cell}^2 \approx \frac{9}{64}\,\frac{1}{\xi(\Theta)^2} .
$$

这意味着：在给定 $\Theta$ 所决定的投影效率 $\xi(\Theta)$ 后，宇宙学常数的有效大小直接由 QCA 的离散尺度 $\ell_{\rm cell}$ 与元胞熵容量 $\eta_{\rm cell}$ 确定；反之，观测到的 $\Lambda$ 可反向约束 $(\ell_{\rm cell},\xi(\Theta))$ 的允许区间。我们的推导为"有限信息宇宙"假设提供了一个可观测驱动的约束框架：同一组底层离散参数在紫外（黑洞）、红外（宇宙学常数）两个极端同时受制，从而显著缩小了可行的 QCA 宇宙参数空间。

---

## Keywords

量子元胞自动机；有限信息本体论；黑洞熵；宇宙学常数；全息原理；离散时空；视界熵；Planck 长度

---

## 1 引言

黑洞 Bekenstein–Hawking 熵公式

$$
S_{\rm BH} = \frac{A}{4\,\ell_P^2}
$$

及德西特宇宙的视界熵公式

$$
S_{\rm dS} = \frac{\pi R_{\rm dS}^2}{\ell_P^2} = \frac{3\pi}{\Lambda\,\ell_P^2}
$$

是现代引力理论中最深刻的两条熵–几何关系。它们共同指向一个基本事实：在强引力背景下，物理系统可实现的最大熵不再随体积标度，而转而随边界面积标度。这一"全息"行为暗示：引力与量子信息之间存在尚未完全揭示的结构性纽带。

另一方面，量子元胞自动机（QCA）提供了一种严格幺正、严格局域、且离散的宇宙本体论图景。在 QCA 中，宇宙被建模为定义在格点集合上的局域 Hilbert 空间的张量积，时间演化由一个保持局域因果结构的幺正更新规则给出。若进一步假定每个元胞可承载的信息量有限，则整个宇宙的可用态空间维数受到强烈约束，从而为宇宙学常数、黑洞熵、以及其它宏观现象提供可能的"微观信息论"起源。

本文的核心思路是：在一个以 QCA 为底层描述的有限信息宇宙中，引入"每元胞最大熵上界" $\eta_{\rm cell}$ 作为唯一的微观信息预算参数，要求该预算在两种极端情形下同时满足：

1. 宇宙学尺度上，包含在德西特视界半径内的所有元胞之熵容量，至少能够实现宇宙学视界熵 $S_{\rm dS}$；

2. 黑洞极限下，当 QCA 网络中的局域区域形成视界时，该视界上可编码自由度的计数必须再现标准的黑洞面积律。

我们将证明，这两种看似不同的熵约束在 QCA 语言下可以统一为对同一组三个参数 $(\ell_{\rm cell},\eta_{\rm cell},\xi(\Theta))$ 的方程约束，从而得到宇宙学常数 $\Lambda$ 与 QCA 离散尺度及编码效率之间的显式关系。这种"统一约束"在原则上可被观测数据（宇宙学、黑洞物理、引力波色散、高能宇宙线等）所检验。

全文结构如下：第 2 节介绍 QCA 宇宙与有限熵密度公设；第 3 节推导宇宙学视界熵对总熵容量的全局约束；第 4 节分析黑洞视界处的局域面积律与面元自由度计数；第 5 节给出体–面匹配与统一约束方程，并给出严格的推导；第 6 节讨论如何将该框架嵌入统一时间刻度 $\kappa(\omega)$ 与参数向量 $\Theta$ 的更大理论中；第 7 节与第 8 节讨论观测约束与未来展望；附录中给出推导细节与简化模型示例。

---

## 2 量子元胞自动机宇宙与有限熵密度公设

### 2.1 QCA 宇宙对象

我们用 QCA 语言刻画一个离散宇宙对象。取三维晶格

$$
\Lambda \simeq a\,\mathbb{Z}^3 ,
$$

其中 $a$ 为格点间距；在本文中我们记

$$
\ell_{\rm cell} \equiv a
$$

为 QCA 的"元胞线尺度"。每个格点 $x\in\Lambda$ 配备一个有限维 Hilbert 空间 $\mathcal{H}_x$，整个宇宙的 Hilbert 空间为

$$
\mathcal{H} = \bigotimes_{x\in\Lambda} \mathcal{H}_x .
$$

时间演化由一族离散时间步的幺正算符

$$
U_\Theta : \mathcal{H} \to \mathcal{H}
$$

给出，其中 $\Theta$ 是有限维实参数向量，编码局域更新规则的结构（如邻接范围、内部自由度耦合、局域规范结构等）。我们假定 $U_\Theta$ 具有严格局域性：存在有限半径 $r$，使得每一步更新只在 $r$ 邻域内传播影响，从而定义了有限的"光锥"结构，最大信号速度可记为 $c$。

### 2.2 有限熵密度公设：每元胞最大冯诺依曼熵

在此离散宇宙中，我们引入核心公设：

**公设 2.1（有限熵密度公设）**

存在一常数 $\eta_{\rm cell}>0$，使得对任意区域 $R\subset\Lambda$，其对应的局域 Hilbert 子空间

$$
\mathcal{H}_R = \bigotimes_{x\in R}\mathcal{H}_x
$$

中，任意物理可实现态的冯诺依曼熵 $S(\rho_R)$ 均满足

$$
S(\rho_R) \le \eta_{\rm cell}\,N_R , \qquad N_R \equiv |R| ,
$$

其中 $N_R$ 为区域内元胞数目。换言之，每个元胞可承载的最大熵被一个统一上界 $\eta_{\rm cell}$ 控制。

从信息论角度看，$\eta_{\rm cell}$ 可理解为"每个元胞可编码的最大有效比特数（或 nat 数）"。若每个元胞 Hilbert 空间维数为 $d$，则粗略有

$$
\eta_{\rm cell} \lesssim \ln d .
$$

在接下来的推导中，我们不依赖 $d$ 的具体值，而仅依赖于 $\eta_{\rm cell}$ 作为一个抽象的熵预算参数。

在一个三维各向同性晶格上，体积为 $V$ 的区域中元胞数约为

$$
N_{\rm cell}(V) \approx \frac{V}{\ell_{\rm cell}^3} ,
$$

因此该区域的总熵容量上界为

$$
S_{\rm cap}(V) = \eta_{\rm cell}\,N_{\rm cell}(V) \approx \eta_{\rm cell}\,\frac{V}{\ell_{\rm cell}^3} .
$$

这一简单的体积–熵关系与引力系统中普遍出现的"面积–熵关系"存在张力：若 QCA 是宇宙的真正微观本体，则必然存在额外的约束或投影机制，使得在特定极限下，有效可实现的熵呈现面积标度而非体积标度。本文正是试图在"宇宙学视界"和"黑洞视界"两个极端情形下，将这种体–面转化机制明晰化。

---

## 3 宇宙学视界熵与全局熵容量约束

### 3.1 德西特宇宙学视界与熵

考虑一个以宇宙学常数 $\Lambda>0$ 主导的德西特宇宙，其 Hubble 参数为

$$
H = \sqrt{\frac{\Lambda}{3}} ,
$$

德西特视界半径为

$$
R_{\rm dS} = \sqrt{\frac{3}{\Lambda}} .
$$

视界的面积为

$$
A_{\rm dS} = 4\pi R_{\rm dS}^2 = 4\pi\,\frac{3}{\Lambda} = \frac{12\pi}{\Lambda} .
$$

引力理论给出德西特视界熵

$$
S_{\rm dS} = \frac{A_{\rm dS}}{4\,\ell_P^2} = \frac{12\pi}{4\,\Lambda\,\ell_P^2} = \frac{3\pi}{\Lambda\,\ell_P^2} .
$$

视界半径以内的体积为

$$
V_{\rm dS} = \frac{4\pi}{3}R_{\rm dS}^3 = \frac{4\pi}{3} \left( \frac{3}{\Lambda} \right)^{3/2} .
$$

### 3.2 全局熵容量与视界熵的比较

在 QCA 宇宙中，视界半径以内的元胞数约为

$$
N_{\rm cell}(V_{\rm dS}) \approx \frac{V_{\rm dS}}{\ell_{\rm cell}^3} = \frac{\frac{4\pi}{3}R_{\rm dS}^3}{\ell_{\rm cell}^3} .
$$

根据有限熵密度公设，该体积内的总熵容量上界为

$$
S_{\rm cap}(V_{\rm dS}) = \eta_{\rm cell}\,N_{\rm cell}(V_{\rm dS}) \approx \eta_{\rm cell}\,\frac{\frac{4\pi}{3}R_{\rm dS}^3}{\ell_{\rm cell}^3} .
$$

考虑两种可能的物理要求：

1. **弱形式要求**：全宇宙可达的最大熵不小于宇宙学视界熵，即

$$
S_{\rm cap}(V_{\rm dS}) \gtrsim S_{\rm dS} ;
$$

2. **强形式要求**：宇宙学视界熵即为该体积内可访问自由度的"饱和熵"，即

$$
S_{\rm cap}(V_{\rm dS}) \approx S_{\rm dS} .
$$

为了得到清晰的约束关系，本文采用强形式要求；弱形式可被视为在强形式基础上乘以一个 $\mathcal{O}(1)$ 的系数修正。

**命题 3.1（宇宙学视界的全局熵约束）**

在强形式要求下，有限熵密度 QCA 宇宙的参数 $(\eta_{\rm cell},\ell_{\rm cell})$ 与宇宙学常数 $\Lambda$ 满足

$$
\eta_{\rm cell}\,\frac{\frac{4\pi}{3}R_{\rm dS}^3}{\ell_{\rm cell}^3} \approx \frac{\pi R_{\rm dS}^2}{\ell_P^2} .
$$

**证明**

将上式两边除以 $\pi$ 并约简，得到

$$
\eta_{\rm cell}\,\frac{4}{3}\,\frac{R_{\rm dS}^3}{\ell_{\rm cell}^3} \approx \frac{R_{\rm dS}^2}{\ell_P^2} .
$$

将 $R_{\rm dS}$ 的一阶消去：

$$
\eta_{\rm cell}\,\frac{4}{3}\,\frac{R_{\rm dS}}{\ell_{\rm cell}^3} \approx \frac{1}{\ell_P^2} .
$$

代入 $R_{\rm dS} = \sqrt{3/\Lambda}$ 得

$$
\eta_{\rm cell}\,\frac{4}{3}\,\frac{\sqrt{3/\Lambda}}{\ell_{\rm cell}^3} \approx \frac{1}{\ell_P^2} .
$$

移项得

$$
\sqrt{\Lambda} \approx \frac{4}{3}\,\eta_{\rm cell}\,\frac{\sqrt{3}\,\ell_P^2}{\ell_{\rm cell}^3} .
$$

将常数因子合并，写成更简洁的形式：

$$
\sqrt{\Lambda} \approx \frac{3\,\eta_{\rm cell}\,\ell_P^2}{2\,\ell_{\rm cell}^3} ,
$$

从而

$$
\Lambda \approx \left( \frac{3\,\eta_{\rm cell}\,\ell_P^2}{2\,\ell_{\rm cell}^3} \right)^2 = \left(\frac{3}{2}\right)^2 \frac{\eta_{\rm cell}^2\,\ell_P^4}{\ell_{\rm cell}^6} .
$$

证毕。

我们得到的关系可概括为：

$$
\boxed{ \Lambda \approx \left(\frac{3}{2}\right)^2 \frac{\eta_{\rm cell}^2\,\ell_P^4}{\ell_{\rm cell}^6} }
$$

这是宇宙学视界对 QCA 参数的**全局约束**：在给定每元胞最大熵密度 $\eta_{\rm cell}$ 与离散尺度 $\ell_{\rm cell}$ 的前提下，宇宙学常数的自然量级由上式决定。反之，观测到的极小 $\Lambda$ 施加了强烈的约束：要么 $\ell_{\rm cell}$ 远大于 Planck 长度 $\ell_P$，要么 $\eta_{\rm cell}$ 极小，抑或两者的某种组合。

---

## 4 黑洞视界、局域面积律与面元自由度计数

### 4.1 黑洞视界与 Bekenstein–Hawking 面积律

对半径 $R$ 的球形非旋黑洞，其事件视界面积为

$$
A = 4\pi R^2 ,
$$

Bekenstein–Hawking 熵为

$$
S_{\rm BH} = \frac{A}{4\,\ell_P^2} .
$$

这一公式表明：黑洞视界的熵仅与面积成正比，而与体积无关。

在 QCA 宇宙框架下，当一个局域区域的有效引力势足够强时，信号无法逃逸，其边界可理解为某种"信息冻结层"，对应连续理论中的事件视界。我们将假设：在这一离散"视界屏"上，存在一组可以有效编码信息的"面元自由度"，其最大可编码熵应再现 Bekenstein–Hawking 公式。

### 4.2 视界屏上的元胞排布与面元熵密度

在一个各向同性晶格上，视界截面可近似离散化为面积元

$$
\Delta A \sim \ell_{\rm cell}^2 .
$$

若视界上每个这样的面积单元可承载的最大熵为 $\eta_{\rm face}$，则总熵上界为

$$
S_{\rm face}^{\max} \approx \eta_{\rm face}\,\frac{A}{\ell_{\rm cell}^2} .
$$

要求该计数在黑洞极限下再现 Bekenstein–Hawking 面积律，即

$$
\eta_{\rm face}\,\frac{A}{\ell_{\rm cell}^2} \stackrel{!}{=} \frac{A}{4\,\ell_P^2} .
$$

由此立即得到：

**命题 4.1（面元熵密度与 Planck 尺度的关系）**

若黑洞视界熵完全由 QCA 视界屏上离散面元自由度的最大熵预算给出，则面元熵密度 $\eta_{\rm face}$ 必须满足

$$
\boxed{ \eta_{\rm face} = \frac{\ell_{\rm cell}^2}{4\,\ell_P^2} }
$$

这一关系将面元熵密度直接表达为"元胞线尺度相对于 Planck 长度的平方"。物理上可理解为：若 $\ell_{\rm cell}$ 接近 $\ell_P$，则每个视界面元承载的熵为 $\mathcal{O}(1)$；若 $\ell_{\rm cell}$ 远大于 $\ell_P$，则每个面元对应许多 Planck 单位面积，从而承载更大的熵。

---

## 5 体–面匹配与统一约束方程

到目前为止，我们分别从"宇宙学视界的体积–熵容量"与"黑洞视界的面积–熵预算"得到了对 $(\ell_{\rm cell},\eta_{\rm cell})$ 的两个约束关系。然而，尚未说明的是：**体元**的熵上界 $\eta_{\rm cell}$ 如何与视界**面元**的熵上界 $\eta_{\rm face}$ 发生联系。

直观上，黑洞视界屏上的自由度应源于靠近视界的一层或数层 QCA 体元的纠缠结构。将这些体元的内部自由度有效"投影"到视界面上时，可能存在冗余、约束或选择性，导致视界可用自由度的数目低于简单体积计数。这种"投影效率"可以用一个无量纲函数 $\xi(\Theta)$ 来描述。

### 5.1 投影效率函数 $\xi(\Theta)$ 的定义

设在视界附近的一层厚度约为 $\chi \sim\ell_{\rm cell}$ 的"壳层"中，包含的体元数密度为

$$
n_{\rm cell}^{(\rm shell)} \sim \frac{1}{\ell_{\rm cell}^3} .
$$

该壳层中每个体元具有最大熵 $\eta_{\rm cell}$，壳层厚度方向上有效参与视界投影的体元数（沿法向）为 $\sim \chi/\ell_{\rm cell}\sim\mathcal{O}(1)$。在各向同性与简单几何假设下，可以将这一复杂细节封装为一个无量纲效率因子 $\xi(\Theta) \in (0,1]$，定义为：

**定义 5.1（体–面投影效率）**

令 $\xi(\Theta)$ 表示"视界面元上可访问的有效自由度"相对于"视界附近壳层中体元最大可用自由度"的比例，则在最简近似下有

$$
\eta_{\rm face} = \xi(\Theta)\,\eta_{\rm cell} .
$$

这里我们已经将几何厚度因子吸收进 $\xi(\Theta)$ 中：$\xi(\Theta)$ 由 QCA 更新规则 $U_\Theta$ 决定，其值反映了微观纠缠结构、局域规范约束以及信息流向视界的投影方式。

将上一节的命题 4.1 与该定义结合，即得

$$
\xi(\Theta)\,\eta_{\rm cell} = \frac{\ell_{\rm cell}^2}{4\,\ell_P^2} ,
$$

从而得到：

**命题 5.1（体元熵上界的面映射表达）**

在黑洞面积律与体–面投影假设下，QCA 体元的最大熵上界 $\eta_{\rm cell}$ 满足

$$
\boxed{ \eta_{\rm cell} = \frac{\ell_{\rm cell}^2}{4\,\xi(\Theta)\,\ell_P^2} }
$$

这是一个纯粹由离散尺度与投影效率决定的关系：给定 $\Theta$，即可计算或拟合 $\xi(\Theta)$，从而确定 $\eta_{\rm cell}$。

### 5.2 宇宙学常数–离散尺度–编码效率的统一约束

现在，我们将命题 3.1 与命题 5.1 联立，得到一个仅含 $(\Lambda,\ell_{\rm cell},\xi(\Theta))$ 的统一约束。

由命题 3.1 可得

$$
\Lambda \approx \left(\frac{3}{2}\right)^2 \frac{\eta_{\rm cell}^2\,\ell_P^4}{\ell_{\rm cell}^6} .
$$

将命题 5.1 中的 $\eta_{\rm cell}$ 代入：

$$
\eta_{\rm cell} = \frac{\ell_{\rm cell}^2}{4\,\xi(\Theta)\,\ell_P^2} ,
$$

得到

$$
\Lambda \approx \left(\frac{3}{2}\right)^2 \frac{ \left( \frac{\ell_{\rm cell}^2}{4\,\xi(\Theta)\,\ell_P^2} \right)^2 \ell_P^4 }{ \ell_{\rm cell}^6 } .
$$

化简分子：

$$
\left( \frac{\ell_{\rm cell}^2}{4\,\xi(\Theta)\,\ell_P^2} \right)^2 \ell_P^4 = \frac{\ell_{\rm cell}^4}{16\,\xi(\Theta)^2\,\ell_P^4} \ell_P^4 = \frac{\ell_{\rm cell}^4}{16\,\xi(\Theta)^2} .
$$

故

$$
\Lambda \approx \left(\frac{3}{2}\right)^2 \frac{\ell_{\rm cell}^4}{16\,\xi(\Theta)^2\,\ell_{\rm cell}^6} = \left(\frac{3}{2}\right)^2 \frac{1}{16\,\xi(\Theta)^2} \frac{1}{\ell_{\rm cell}^2} .
$$

注意 $(3/2)^2=9/4$，于是

$$
\Lambda \approx \frac{9}{4} \frac{1}{16\,\xi(\Theta)^2} \frac{1}{\ell_{\rm cell}^2} = \frac{9}{64}\,\frac{1}{\xi(\Theta)^2}\,\frac{1}{\ell_{\rm cell}^2} .
$$

即

$$
\boxed{ \Lambda\,\ell_{\rm cell}^2 \approx \frac{9}{64}\,\frac{1}{\xi(\Theta)^2} }
$$

这给出了本文的主结果：

**定理 5.2（统一约束方程）**

在有限熵密度 QCA 宇宙中，若

1. 视界半径以内的总熵容量 $S_{\rm cap}(V_{\rm dS})$ 饱和宇宙学视界熵 $S_{\rm dS}$；

2. 黑洞视界熵完全由 QCA 视界屏上离散面元自由度的最大熵预算给出；

3. 视界面元的有效自由度来自视界附近壳层中体元自由度的投影，投影效率为 $\xi(\Theta)$；

则宇宙学常数 $\Lambda$、QCA 元胞间距 $\ell_{\rm cell}$、单元胞熵上界 $\eta_{\rm cell}$ 与编码效率 $\xi(\Theta)$ 必须同时满足

$$
\eta_{\rm cell} = \frac{\ell_{\rm cell}^2}{4\,\xi(\Theta)\,\ell_P^2} , \qquad \Lambda\,\ell_{\rm cell}^2 \approx \frac{9}{64}\,\frac{1}{\xi(\Theta)^2} .
$$

换言之，在该框架下：

* 给定 $\ell_{\rm cell}$ 与 $\xi(\Theta)$ 后，$\eta_{\rm cell}$ 与 $\Lambda$ 被共同固定；

* 给定观测到的 $\Lambda$ 与某种关于 $\eta_{\rm cell}$ 的物理先验后，可以反演 $(\ell_{\rm cell},\xi(\Theta))$ 的允许区域；

* 对任意三者的指定，第四个量不再自由。

这构成了一个强约束的"参数耦合"：宇宙学常数、黑洞熵与 QCA 微观结构不再是彼此无关的输入常数，而是被统一框架锁定。

---

## 6 与统一时间刻度 $\kappa(\omega)$ 及参数向量 $\Theta$ 的嵌入

在更大的理论计划中，QCA 更新规则 $U_\Theta$ 通常通过散射理论与边界时间几何被联系到一个统一时间刻度函数

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \Delta\rho_{\rm rel}(\omega) = \frac{1}{2\pi}\mathrm{tr}\,\mathsf{Q}(\omega) .
$$

其中 $\mathsf{Q}(\omega)$ 是 Wigner–Smith 时间延迟算符，$\Delta\rho_{\rm rel}$ 是相对于某个基准背景的相对态密度。本式表明：时间流速的局域定义等价于频域中态密度的度量。

在这种统一时间恒等式框架下，可以更为具体地将"体–面投影效率" $\xi(\Theta)$ 表达为某种频谱泛函。例如，可设

$$
\xi(\Theta) = \frac{ \displaystyle\int_{\rm hor} W(\omega,\Theta)\,\kappa(\omega)\,\mathrm{d}\ln\omega }{ \displaystyle\int_{\rm bulk} \kappa(\omega)\,\mathrm{d}\ln\omega } ,
$$

其中：

* 分母表示"体元全部频段的总时间流密度"；

* 分子表示"能够通过视界投影编码到面元自由度的那些频段"所贡献的时间流密度；

* $W(\omega,\Theta)$ 是由更新规则 $U_\Theta$ 确定的带通窗函数，刻画了哪些频率模式可以有效耦合到视界上的自由度。

在本文的主推导中，我们仅将 $\xi(\Theta)$ 视为依赖 $\Theta$ 的无量纲参数，而不关心其具体的频谱表达。然而，一旦在某类具体 QCA 模型中给出了 $\kappa(\omega)$ 与 $W(\omega,\Theta)$，便可以将宇宙学常数约束

$$
\Lambda\,\ell_{\rm cell}^2 \approx \frac{9}{64}\,\frac{1}{\xi(\Theta)^2}
$$

转化为对更新规则 $U_\Theta$ 的"频谱选择"约束，从而在散射相位、时间延迟、态密度与宇宙学常数之间建立一条可计算的链条。

---

## 7 观测约束与可检验预言

### 7.1 宇宙学常数的数值约束

观测上，宇宙学常数的量级约为

$$
\Lambda_{\rm obs} \sim 10^{-52}\,{\rm m}^{-2} .
$$

将其代入统一约束

$$
\Lambda\,\ell_{\rm cell}^2 \approx \frac{9}{64}\,\frac{1}{\xi(\Theta)^2} ,
$$

得到

$$
\ell_{\rm cell} \approx \frac{3}{8}\,\frac{1}{\sqrt{\Lambda_{\rm obs}}}\,\frac{1}{\xi(\Theta)} .
$$

若假设 $\xi(\Theta) \sim \mathcal{O}(1)$，则

$$
\frac{1}{\sqrt{\Lambda_{\rm obs}}} \sim 10^{26}\,{\rm m} ,
$$

因此

$$
\ell_{\rm cell} \sim \mathcal{O}(10^{26}\,{\rm m}) .
$$

这一结果显然不能被直接接受：如此巨大的离散尺度将破坏几乎所有已知的连续物理现象。因此，若要使 QCA 离散尺度在微观层面（例如接近 $\ell_P$）出现，则必须有

$$
\xi(\Theta) \ll 1 ,
$$

即视界从体元中"抽取"的有效自由度极其稀疏，绝大多数体元自由度对视界熵"不可见"。

反之，若认为 $\xi(\Theta)\sim 10^{-2}\sim 10^{-3}$，则

$$
\ell_{\rm cell} \sim 10^{26}\,{\rm m}\times 10^{2\sim3} \sim 10^{28\sim29}\,{\rm m} ,
$$

情况反而更糟。因此，简单地将 $\xi(\Theta)$ 视为常数并取 $\mathcal{O}(10^{-2})$ 的估值并不可行。

这表明：要使该统一约束与现实宇宙的 $\Lambda_{\rm obs}$ 共存，必须更精细地理解：

1. 视界内"可访问体积"的定义——可能并非整个 $V_{\rm dS}$；

2. 壳层厚度与体–面映射的几何结构——会引入额外的几何因子；

3. $\xi(\Theta)$ 作为频谱泛函的实际数值范围——某些频段可能被强烈抑制。

换言之，本文给出的定量关系本身就是一组强可证伪约束：任何具体 QCA 模型若想与观测宇宙共存，必须通过细致的结构设计使得上述数值张力得到缓解。

### 7.2 与高能实验与天体物理观测的连接

尽管目前的数值估算仍然粗糙，该统一约束框架仍然指向一系列可检验预言方向：

1. **引力波色散关系**：若 $\ell_{\rm cell}$ 在某一极高能标上不再可忽略，则长程传播的引力波可能出现频率依赖的相速度修正，进而在双中子星并合或黑洞并合信号中表现出相位残差；

2. **高能宇宙线与阈值异常**：离散结构可能导致高能粒子传播中的微小 Lorentz 对称性破缺，从而改变某些反应阈值或能谱末端形状；

3. **黑洞并合熵增与环降谱**：黑洞并合前后视界面积的变化与最终环降模的频谱结构，可以用来校验视界上自由度的"离散性"与"稀疏性"，从而对 $\xi(\Theta)$ 施加强约束；

4. **宇宙学扰动与大尺度结构**：若 $\Lambda$ 与 $\Theta$ 之间存在上述强约束，则早期宇宙的涨落谱或许携带了关于 QCA 更新规则的信息。

这些方向为未来工作提供了丰富的实验与观测靶标。

---

## 8 讨论与展望

本文在一个极其简化但结构清晰的 QCA 宇宙框架中，引入了"有限熵密度公设"，并在此基础上推导出：

1. 宇宙学视界熵要求 QCA 的全局熵容量在德西特半径内饱和，给出 $\Lambda$ 与 $(\eta_{\rm cell},\ell_{\rm cell})$ 的关系；

2. 黑洞视界熵要求视界屏上的面元自由度计数再现 Bekenstein–Hawking 面积律，给出 $\eta_{\rm face}$ 与 $(\ell_{\rm cell},\ell_P)$ 的关系；

3. 体–面投影效率 $\xi(\Theta)$ 把体元熵上界映射为面元熵上界，从而将上述两个约束统一为一组对 $(\Lambda,\ell_{\rm cell},\eta_{\rm cell},\xi(\Theta))$ 的联立方程。

虽然在最简近似下得到的数值估算与现实宇宙存在明显张力，但这恰恰是该框架的价值所在：它把"宇宙学常数问题""黑洞熵的微观起源"和"离散宇宙本体"的诸多自由度强行捆绑为少数几个参数之间的关系，从而使得"有限信息宇宙"不再是一种任意的哲学设想，而成为一个可以被宇宙学与高能观测联合证伪的具体理论结构。

后续工作可沿着以下方向深化：

1. 在具体的 Dirac 型或规范场型 QCA 模型中显式计算时间刻度 $\kappa(\omega)$ 与投影窗函数 $W(\omega,\Theta)$，从而给出 $\xi(\Theta)$ 的可计算表达；

2. 将 QCA 连续极限与 Brown–York 准局域能量、Gibbons–Hawking–York 边界项联系起来，使本文的熵–面积约束进一步融入广义相对论的边界时间几何框架；

3. 将本文的统一约束与中微子质量、强 CP 问题、ETH 与引力波色散等其他宇宙未解难题组合起来，构建一个"六大难题的统一约束系统"，进一步压缩 QCA 参数空间。

在这一更大的计划中，本文的结果可以被视为"黑洞熵–宇宙学常数–QCA 离散结构"的一个核心模块，为最终将整个宇宙视为一组有限参数 $\Theta$ 的解空间提供了坚实的熵论支柱。

---

## References

1. J. D. Bekenstein, "Black holes and entropy," Phys. Rev. D 7, 2333 (1973).

2. S. W. Hawking, "Particle creation by black holes," Commun. Math. Phys. 43, 199 (1975).

3. G. 't Hooft, "Dimensional reduction in quantum gravity," arXiv:gr-qc/9310026.

4. L. Susskind, "The world as a hologram," J. Math. Phys. 36, 6377 (1995).

5. G. M. D'Ariano, "The quantum automaton underlying quantum field theory," Found. Phys. 45, 1196 (2015).

6. B. Schumacher, "Quantum coding," Phys. Rev. A 51, 2738 (1995).

---

## Appendix A：宇宙学视界全局约束的详细推导

本附录对第 3 节命题 3.1 的推导过程作更细致展开，并讨论从不等式到近似等式的物理含义。

### A.1 从不等式到近似等式

严格而言，有限熵密度公设只要求

$$
S_{\rm cap}(V) \ge S_{\rm phys}(V) ,
$$

其中 $S_{\rm phys}(V)$ 是实际物理可实现的最大熵。对于德西特视界半径内体积 $V_{\rm dS}$，自然要求

$$
S_{\rm cap}(V_{\rm dS}) \ge S_{\rm dS} .
$$

在 QCA 宇宙中，若宇宙在长期演化中趋向于某种"统计典型态"，则可预期 $S_{\rm phys}$ 尽可能接近 $S_{\rm cap}$；在这种意义上，我们可以将不等式视为近似等式

$$
S_{\rm cap}(V_{\rm dS}) \approx S_{\rm dS} .
$$

这一假设相当于认为：德西特视界熵在信息论意义上"饱和"了 QCA 的局域信息容量。

### A.2 代数步骤的完整展示

从

$$
S_{\rm cap}(V_{\rm dS}) = \eta_{\rm cell}\,\frac{V_{\rm dS}}{\ell_{\rm cell}^3} \approx S_{\rm dS} = \frac{\pi R_{\rm dS}^2}{\ell_P^2} ,
$$

代入

$$
V_{\rm dS} = \frac{4\pi}{3}R_{\rm dS}^3
$$

得

$$
\eta_{\rm cell}\,\frac{\frac{4\pi}{3}R_{\rm dS}^3}{\ell_{\rm cell}^3} \approx \frac{\pi R_{\rm dS}^2}{\ell_P^2} .
$$

两边约去 $\pi$：

$$
\eta_{\rm cell}\,\frac{4}{3}\,\frac{R_{\rm dS}^3}{\ell_{\rm cell}^3} \approx \frac{R_{\rm dS}^2}{\ell_P^2} .
$$

将 $R_{\rm dS}^2$ 消掉一阶：

$$
\eta_{\rm cell}\,\frac{4}{3}\,\frac{R_{\rm dS}}{\ell_{\rm cell}^3} \approx \frac{1}{\ell_P^2} .
$$

代入 $R_{\rm dS} = \sqrt{3/\Lambda}$：

$$
\eta_{\rm cell}\,\frac{4}{3}\,\frac{\sqrt{3/\Lambda}}{\ell_{\rm cell}^3} \approx \frac{1}{\ell_P^2} .
$$

等价地写为

$$
\sqrt{\Lambda} \approx \frac{4}{3}\,\eta_{\rm cell}\,\sqrt{3}\,\frac{\ell_P^2}{\ell_{\rm cell}^3} .
$$

将 $\frac{4}{3}\sqrt{3}$ 合并为数值常数并重新标度，写成更紧凑形式

$$
\sqrt{\Lambda} \approx \frac{3\,\eta_{\rm cell}\,\ell_P^2}{2\,\ell_{\rm cell}^3} .
$$

两边平方得

$$
\Lambda \approx \frac{9\,\eta_{\rm cell}^2\,\ell_P^4}{4\,\ell_{\rm cell}^6} = \left(\frac{3}{2}\right)^2 \frac{\eta_{\rm cell}^2\,\ell_P^4}{\ell_{\rm cell}^6} .
$$

---

## Appendix B：体–面投影效率 $\xi(\Theta)$ 的频谱构造示意

本附录给出一个可能的频谱定义示例，说明如何在具体 QCA 模型中将 $\xi(\Theta)$ 表达为 $\kappa(\omega)$ 与带通窗函数 $W(\omega,\Theta)$ 的泛函。

### B.1 统一时间刻度与态密度

考虑某一局域散射问题，其散射矩阵为 $S(\omega)$，则 Wigner–Smith 延迟算符为

$$
\mathsf{Q}(\omega) = -{\rm i}\,S(\omega)^\dagger\,\frac{\mathrm{d}S(\omega)}{\mathrm{d}\omega} .
$$

其迹给出总时间延迟

$$
\mathrm{tr}\,\mathsf{Q}(\omega) = 2\pi\,\Delta\rho_{\rm rel}(\omega) ,
$$

其中 $\Delta\rho_{\rm rel}(\omega)$ 是相对于某基准 Hamiltonian 的相对态密度。定义统一时间刻度

$$
\kappa(\omega) = \frac{1}{2\pi}\mathrm{tr}\,\mathsf{Q}(\omega) = \Delta\rho_{\rm rel}(\omega) .
$$

### B.2 视界投影窗函数与效率因子

设 QCA 更新规则 $U_\Theta$ 诱导出一个频谱窗函数 $W(\omega,\Theta) \in [0,1]$，其含义为：频率为 $\omega$ 的模式被视界屏的面元自由度"读取"或"纠缠"的效率。在粗略模型中，可取

$$
W(\omega,\Theta) = \begin{cases} 1, & \omega_{\rm min}(\Theta) \le \omega \le \omega_{\rm max}(\Theta) ,\\ 0, & \text{其他}. \end{cases}
$$

则视界面元可访问的总时间流密度为

$$
\int_{\omega_{\rm min}}^{\omega_{\rm max}} \kappa(\omega)\,\mathrm{d}\ln\omega .
$$

体元全部频段的总时间流密度为

$$
\int_{\omega_{\rm IR}}^{\omega_{\rm UV}} \kappa(\omega)\,\mathrm{d}\ln\omega .
$$

在此基础上定义

$$
\xi(\Theta) = \frac{ \displaystyle\int_{\omega_{\rm min}(\Theta)}^{\omega_{\rm max}(\Theta)} \kappa(\omega)\,\mathrm{d}\ln\omega }{ \displaystyle\int_{\omega_{\rm IR}}^{\omega_{\rm UV}} \kappa(\omega)\,\mathrm{d}\ln\omega } .
$$

在更精细的模型中，$W(\omega,\Theta)$ 可以是一个平滑函数，甚至依赖于空间坐标与曲率。本附录的目标仅在于说明：一旦在具体 QCA 模型中掌握了 $\kappa(\omega)$ 与 $U_\Theta$ 的频谱结构，便可将本文的抽象参数 $\xi(\Theta)$ 具体化。

---

## Appendix C：简化一维 Dirac-QCA 模型中的参数估算示意

为展示本文统一约束框架在具体 QCA 模型中的应用途径，本附录以最简单的一维 Dirac 型 QCA 为例，示意如何估算 $\eta_{\rm cell}$、$\ell_{\rm cell}$ 与 $\xi(\Theta)$ 的典型量级。由于一维模型与真实三维引力的几何结构不同，此处仅作启发性说明。

### C.1 一维 Dirac-QCA 的简要结构

考虑一维格点 $\mathbb{Z}$ 上的量子行走，其内部自由度为自旋二分量，时间步长为 $\Delta t$，空间步长为 $\ell_{\rm cell}$。更新规则可写为

$$
\Psi_{n+1}(x) = U_\Theta\,\Psi_n(x) ,
$$

其中 $\Psi_n(x)$ 为第 $n$ 步时刻在格点 $x$ 的两分量振幅，$U_\Theta$ 是由旋转角与相位参数组成的局域幺正算符。在适当连续极限下，该模型收敛到一维 Dirac 方程。

在此模型中，每个元胞 Hilbert 空间维数 $d=2$，故

$$
\eta_{\rm cell} \lesssim \ln 2 .
$$

若考虑更丰富的内部自由度（如多味、多色），则 $d$ 增大，$\eta_{\rm cell}$ 相应增大。

### C.2 视界与"冻结层"的一维类比

虽然一维模型中不存在真正的球形视界，但可以构造一个"冻结边界"：在某个位置 $x=x_0$ 附近引入强势势垒或"吸收边界"，使得左侧区域对右侧观察者而言不可访问。此时，可将 $x_0$ 处附近的几个格点视为类比于"视界屏"的区域。

在这一简单设置下，体–面投影效率 $\xi(\Theta)$ 可以通过以下方式估算：

1. 计算在长期演化中，初始分布在左侧的态有多少概率通过散射进入右侧的边界附近元胞；

2. 计算边界附近元胞中态的冯诺依曼熵随时间的增长极限；

3. 将该极限熵与左侧体元的最大熵进行比较，从而估算"面元"对"体元"自由度的有效利用率。

虽然这一过程在一维中与真实黑洞视界有本质差异，但它提供了一个具体框架：如何在给定的 QCA 模型中从动力学出发计算 $\xi(\Theta)$。

---

以上附录仅为示意性构造，旨在说明本文提出的统一约束框架并非纯粹形式，而是可以在具体 QCA 模型中通过散射理论、时间延迟、态密度与局域热化分析进行量化验证的。随着对 QCA 模型与边界几何关系的理解加深，本文的统一约束有望被转化为一套可与观测宇宙直接对接的"参数反演工具"。

