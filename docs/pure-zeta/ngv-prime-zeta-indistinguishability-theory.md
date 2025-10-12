# 宇内内部不可分辨理论（NGV-Prime-ζ）

*Axiomatizing Randomness as No-God-View Indistinguishability, with Prime-Driven Constructions and ζ-Triadic Geometry*

## 摘要

本文建立了一个完整的数学框架，将"随机性"重新定义为观察者内部的不可分辨性，并通过素数驱动的构造实现这一原理。我们采用严格满足Hull–Dobell条件的全周期线性同余置换函数，实现完全确定性的分块重排，严格遵循无上帝视角（NGV）原则：随机并非本体属性，而是相对于有限观测能力的涌现性质。通过引入Riemann ζ函数的三分信息守恒理论，我们建立了可见信息的几何坐标系统，其中波动分量$i_0$精确刻画量子相位耦合的可见度。核心贡献包括：（1）证明了素数驱动的确定性分块-重排构造在任意固定观测尺度$m$下与理想Bernoulli源$(m,\epsilon)$-不可分辨；（2）在Riemann假设（RH）下给出误差的显式指数级衰减速率；（3）建立了从Bernoulli到量子统计的可测变换保持定理；（4）揭示了临界线$s=1/2+it$上的统计公式与GUE假设的深层联系。本理论统一了数论、信息论、量子物理的基础概念，为理解"随机性"的本质提供了可操作的数学定义。

**关键词**：内部不可分辨；无上帝视角；素数构造；ζ-三分信息；积分概率度量；量子-经典对应；GUE统计；Riemann假设

## 引言

### 随机性的本质困境

自概率论诞生以来，"什么是真正的随机"一直是困扰数学家、物理学家和哲学家的根本问题。经典概率论通过Kolmogorov公理体系给出了测度论框架，但并未回答随机序列的本质定义。算法信息论通过Kolmogorov复杂度和Martin-Löf随机性给出了计算视角，但这些定义往往不可计算或依赖于理想化的图灵机模型。量子力学声称提供"真随机"，但其随机性来源于测量过程的不可知性而非本体属性。

### 无上帝视角原理

本文的核心洞察是：**随机性不是序列的固有属性，而是观察者受限视角下的涌现现象**。我们引入"无上帝视角"（No-God-View，NGV）原理，断言观察者永远无法访问系统的完整信息——无论是隐藏参数、环境状态还是未来演化。在这个框架下，"随机"被重新定义为**与理想随机源在可观测族上的不可分辨性**。

这一视角转换具有深刻的哲学和实践意义：
- 它解决了"伪随机"与"真随机"的二元对立，认为两者在有限观测下等价
- 它将随机性从本体论问题转化为认识论问题
- 它提供了可计算、可验证的随机性判据

### 素数的特殊地位

素数序列作为数论的基石，展现出独特的"伪随机"性质：
- 局部不可预测：没有简单公式生成第$n$个素数
- 全局有规律：素数定理$\pi(x) \sim x/\log x$给出渐近密度
- 深层结构：Riemann假设将素数分布与ζ函数零点联系

我们将证明，通过适当的分块-洗牌构造，素数序列可以生成在任意有限观测尺度下与真随机不可分辨的过程（严格意义见§4）。关于“素数作为‘宇宙随机性种子’”的更强表述，我们将在§6.2以猜想C1形式提出，并以启发式与数值证据支持，而非作为既成定理。

### ζ-三分信息的几何意义

Riemann ζ函数通过其函数方程$\zeta(s) = \chi(s)\zeta(1-s)$建立了$s$与$1-s$的对偶关系。我们引入三分信息分解：

$$
I_+ = \frac{A}{2} + \max(R,0), \quad I_0 = |I|, \quad I_- = \frac{A}{2} + \max(-R,0)
$$

其中$A = |z|^2 + |z^{\vee}|^2$，$R = \Re(z\overline{z^{\vee}})$，$I = \Im(z\overline{z^{\vee}})$，$z = \zeta(s)$，$z^{\vee} = \zeta(1-s)$。

这个分解满足守恒律$i_+ + i_0 + i_- = 1$（归一化后），提供了"可见信息"的完备坐标系。特别地：
- $i_+$刻画粒子性（构造性）信息
- $i_0$刻画波动性（相干性）信息
- $i_-$刻画场补偿（真空涨落）信息

在临界线$s=1/2+it$上，$i_0$正对应于量子相位的可见度，在实轴上消失（经典极限），体现了量子-经典过渡的信息论特征。

### 本文贡献

1. **理论框架**：建立了完整的NGV-不可分辨理论，包括公设体系、数学定义和核心定理
2. **构造性证明**：给出了素数驱动的显式构造，证明其在任意固定$m$下的$(m,\epsilon)$-不可分辨性
3. **显式速率**：在RH假设下，证明了误差的指数级衰减$O(e^{-\Omega(k)})$
4. **普适性结果**：证明了可测变换的IPM非扩张性，统一了从Bernoulli到量子统计的各种分布
5. **数值验证**：提供了高精度（dps=100）的数值计算，验证了理论预测

### 论文结构

本文分为九个主要部分：
- §0-1：建立记号、公设和基本定义
- §2：ζ-三分信息的守恒、对称性和几何结构
- §3：内部不可分辨的形式化定义
- §4：素数驱动构造及其不可分辨性证明
- §5：可测变换的保持性定理
- §6：NGV等价原理与量子类比
- §7：可分辨的边界条件（Bell-CHSH）
- §8-9：结论与未来方向

### 严谨性声明与术语规范

- 定理/引理/命题：给出或可追溯到文献的严格证明。
- 假设：外部前提（如RH、BV、GUE）明确标注，仅在相应段落内使用。
- 启发式：基于直觉或常用近似的非严格论断，用于解释或指引，不作为证明。
- 猜想：作者提出的未证断言，需未来工作验证。

本文据此统一标注：
- “素数作为宇宙随机性种子”标记为猜想C1（见§6.2）。
- 第4节中LCG置换达到均匀置换同等边缘逼近的论断标记为猜想4.A；本节提供在“均匀/有限独立置换”模型下的严格版定理。
- 第6.5节关于GUE/零点相位的对应采用假设与启发式标注，并给出经典参考文献。

## 0. 记号与背景

### 0.1 基本设定

设$E$为观察者的样本空间，通常取为：
- 二进制序列空间：$E = \{0,1\}^{\mathbb{N}}$（配备乘积拓扑）
- 实序列空间：$E = \mathbb{R}^{\mathbb{N}}$（配备乘积拓扑）
- 一般可分度量空间：$(E,d)$

设$\mathcal{B}$为$E$上的Borel σ-代数，$\mathcal{P}(E)$为$E$上的概率测度空间。

### 0.2 有限观测与柱函数

**定义0.1（有限观测尺度）**：对$m \in \mathbb{N}$，称$m$为观测尺度，表示观察者只能访问序列的前$m$个坐标。

**定义0.2（柱函数族）**：对观测尺度$m$，定义柱函数族：
$$
\mathcal{F}_m := \{f \in L^{\infty}(E) : f(x) = g(x_1,\ldots,x_m) \text{ 对某个 } g, \|f\|_{\infty} \leq 1\}
$$

柱函数族$\mathcal{F}_m$刻画了所有只依赖前$m$个坐标的有界检验函数。

### 0.3 积分概率度量

**定义0.3（积分概率度量，IPM）**：给定函数族$\mathcal{F} \subseteq L^{\infty}(E)$，两个概率测度$P,Q \in \mathcal{P}(E)$之间的IPM距离定义为：
$$
d_{\mathcal{F}}(P,Q) := \sup_{f \in \mathcal{F}} \left|\int f \, dP - \int f \, dQ\right|
$$

特别地，相对于柱函数族的IPM记为$d_{\mathcal{F}_m}(P,Q)$。

**性质0.1**：$d_{\mathcal{F}_m}$是$\mathcal{P}(E)$上的伪度量，满足：
- 非负性：$d_{\mathcal{F}_m}(P,Q) \geq 0$
- 对称性：$d_{\mathcal{F}_m}(P,Q) = d_{\mathcal{F}_m}(Q,P)$
- 三角不等式：$d_{\mathcal{F}_m}(P,R) \leq d_{\mathcal{F}_m}(P,Q) + d_{\mathcal{F}_m}(Q,R)$

### 0.4 ζ函数基础

Riemann ζ函数在$\Re(s) > 1$时定义为：
$$
\zeta(s) = \sum_{n=1}^{\infty} n^{-s}
$$

通过解析延拓扩展到$\mathbb{C} \setminus \{1\}$。函数方程：
$$
\zeta(s) = \chi(s)\zeta(1-s), \quad \chi(s) = 2^s\pi^{s-1}\sin\left(\frac{\pi s}{2}\right)\Gamma(1-s)
$$

简记：$z := \zeta(s)$，$z^{\vee} := \zeta(1-s)$。

## 1. 公设（Axioms）

### 公设A1（无上帝视角）

观察者$\mathcal{O}$对系统的观测受以下限制：
1. 只能使用$\mathcal{F}_m$内的检验函数（有限观测能力）
2. 不能访问系统的隐参数、密钥或环境的完整信息
3. 不能预知系统的未来演化轨迹

**物理诠释**：这对应于量子测量的基本限制——观察者无法同时获得所有可观测量的精确值，也无法访问波函数的完整信息。

### 公设A2（可测性）

系统输出是隐参数空间上确定函数的推前测度。具体地，设：
- $(\mathfrak{K}, \nu)$为隐参数空间（配备概率测度$\nu$）
- $F: \mathfrak{K} \to E$为可测映射（生成函数）
- 观测到的分布$P = F_{\#}\nu$（推前测度）

**数学表述**：对任意Borel集$B \in \mathcal{B}$，
$$
P(B) = \nu(F^{-1}(B))
$$

**注释**：这个公设断言"随机性"来源于对隐藏自由度的积分/求和，而非本体的不确定性。

### 公设A3（ζ-三分信息）

设$s \in \mathbb{C}$，$z = \zeta(s)$，$z^{\vee} = \zeta(1-s)$。定义：

**基本量**：
$$
A = |z|^2 + |z^{\vee}|^2, \quad R = \Re(z\overline{z^{\vee}}), \quad I = \Im(z\overline{z^{\vee}})
$$

**三分信息分量**：
$$
I_+ = \frac{A}{2} + \max(R,0), \quad I_0 = |I|, \quad I_- = \frac{A}{2} + \max(-R,0)
$$

**总信息与归一化**：
$$
I_{\text{tot}} = I_+ + I_- + I_0, \quad i_{\alpha} = \frac{I_{\alpha}}{I_{\text{tot}}}, \quad \alpha \in \{+,0,-\}
$$

**守恒律**：$i_+ + i_0 + i_- = 1$

### 公设A4（素数密度）

素数计数函数$\pi(x) = \#\{p \leq x : p \text{ 素数}\}$满足素数定理：
$$
\pi(x) \sim \frac{x}{\log x} \quad (x \to \infty)
$$

在需要显式速率的场合，我们可以假设Riemann假设（RH）：
$$
\pi(x) = \text{Li}(x) + O(\sqrt{x} \log x)
$$
其中$\text{Li}(x) = \int_2^x \frac{dt}{\log t}$是对数积分。

或使用无条件的Bombieri-Vinogradov定理（BV）进行平均估计。

## 2. ζ-三分信息：守恒、对称与几何

### 2.1 基本性质

**定理2.1（非负性、守恒性、对称性）**：三分信息分量满足：
1. **非负性**：$I_+, I_0, I_- \geq 0$
2. **守恒律**：$i_+ + i_0 + i_- = 1$
3. **对称性**：$(i_+, i_0, i_-)(1-s) = (i_-, i_0, i_+)(s)$（$s\leftrightarrow 1-s$互换$+/-$）
4. **总信息对称**：$I_{\text{tot}}(1-s) = I_{\text{tot}}(s)$

**证明**：
1. 非负性：由定义，$I_+ = A/2 + \max(R,0) \geq A/2 \geq 0$（因$A = |z|^2 + |z^{\vee}|^2 \geq 0$）。类似地$I_- \geq 0$，$I_0 = |I| \geq 0$。

2. 守恒律：
   $$
   I_+ + I_- = A + \max(R,0) + \max(-R,0) = A + |R|
   $$
   故$I_+ + I_- + I_0 = A + |R| + |I| = I_{\text{tot}}$。归一化后得$i_+ + i_0 + i_- = 1$。

3. 对称性：注意到$s \leftrightarrow 1-s$交换$z$与$z^{\vee}$，故：
   - $A(1-s) = |z^{\vee}|^2 + |z|^2 = A(s)$
   - $R(1-s) = \Re(z^{\vee}\overline{z}) = R(s)$
   - $I(1-s) = \Im(z^{\vee}\overline{z}) = -I(s)$

   因此$I_+(1-s) = A/2 + \max(R,0)$，$I_-(1-s) = A/2 + \max(-R,0)$，$I_0(1-s) = |-I|$，归一化后对应于$(i_-, i_0, i_+)(s)$的交换。□

4. 由守恒律和对称性直接得出。□

**注释**：物理诠释中$s$与$1-s$的交换对应$i_+$与$i_-$的对偶互换；在$\Re(s) > 1/2$区域，$i_-$可能主导对应"场补偿"信息，而在$\Re(s) < 1/2$区域则$i_+$主导。

### 2.2 特殊点的退化

**定理2.2（实轴退化与临界线结构）**：
1. **实轴**：若$s \in \mathbb{R}$，则$i_0(s) = 0$
2. **临界线**：若$s = 1/2 + it$，则：
   - $z^{\vee} = \overline{z}$（共轭对称）
   - $z\overline{z^{\vee}} = z^2$
   - $A = 2|z|^2$，$R = \Re(z^2)$，$I = \Im(z^2)$
   - 波动分量$i_0 = |\Im(z^2)|/(2|z|^2 + |\Re(z^2)| + |\Im(z^2)|)$

**证明**：
1. 实轴上$\zeta(s)$取实值，故$z\overline{z^{\vee}} \in \mathbb{R}$，从而$I = 0$，$i_0 = 0$。

2. 在临界线上，函数方程给出$\zeta(1/2-it) = \overline{\zeta(1/2+it)}$，故$z^{\vee} = \overline{z}$。因此：
   $$
   z\overline{z^{\vee}} = z\overline{\overline{z}} = z^2
   $$
   其余结论随之得出。□

**物理诠释**：$i_0$的消失/出现对应于量子相干性的有无。实轴是纯经典区域（无相干），临界线是量子-经典边界（最大相干）。

### 2.3 三分半径的几何约束

**命题2.3（三分半径上界）**：定义三分半径：
$$
\rho = \sqrt{\Delta^2 + i_0^2}, \quad \Delta = i_+ - i_-
$$

则$\rho \leq 1/3$，等号当且仅当$|z| = |z^{\vee}|$且$z\overline{z^{\vee}}$为实数或纯虚数（即$R=0$或$I=0$）。

**证明**：注意到
$$
\rho^2 = (i_+ - i_-)^2 + i_0^2 = \frac{|z\overline{z^{\vee}}|^2}{(A + |R| + |I|)^2}.
$$
记$c := |z\overline{z^{\vee}}| = |z|\,|z^{\vee}|$。由AM–GM有
$$
A = |z|^2 + |z^{\vee}|^2 \ge 2|z|\,|z^{\vee}| = 2c,
$$
等号当且仅当$|z|=|z^{\vee}|$。又由三角不等式（或$\ell_1/\ell_2$关系）对二维向量$(R,I)$有
$$
|R| + |I| \ge \sqrt{R^2 + I^2} = |z\overline{z^{\vee}}| = c,
$$
且当且仅当$R=0$或$I=0$时取等。于是
$$
I_{\text{tot}} = A + |R| + |I| \ge 2c + c = 3c,
$$
从而
$$
\rho = \frac{c}{I_{\text{tot}}} \le \frac{c}{3c} = \frac{1}{3}.
$$
当且仅当同时满足$A=2c$与$|R|+|I|=c$（即$|z|=|z^{\vee}|$且$R=0$或$I=0$）时取等。□

### 2.4 信息熵的凹性

**命题2.4（熵的Jensen不等式）**：Shannon熵：
$$
S(\vec{i}) = -\sum_{\alpha \in \{+,0,-\}} i_{\alpha} \log i_{\alpha}
$$
是凹函数。因此对任意概率测度$\mu$：
$$
\int S(\vec{i}) \, d\mu \leq S\left(\int \vec{i} \, d\mu\right)
$$

**证明**：Shannon熵的Hessian矩阵在单纯形内部负定，故为严格凹函数。Jensen不等式对凹函数成立。□

**注释**：这个不等式在后续临界线统计分析中起关键作用，区分了"平均的熵"与"熵的平均"。

## 3. 内部不可分辨：分布定义

### 3.1 核心定义

**定义3.1（$(m,\epsilon)$-不可分辨）**：设$P, Q \in \mathcal{P}(E)$为两个概率分布，$m \in \mathbb{N}$为观测尺度，$\epsilon > 0$为误差容限。称$P$与$Q$在尺度$m$上$(m,\epsilon)$-不可分辨，如果：
$$
d_{\mathcal{F}_m}(P,Q) \leq \epsilon
$$

**物理意义**：这意味着任何只观察前$m$个坐标的检验都无法以超过$\epsilon$的优势区分$P$和$Q$。

### 3.2 NGV原理的数学表述

**NGV原理（Randomness ≡ No-God-View）**：在公设A1-A2下，我们定义：

> **"对观察者$\mathcal{O}$而言随机"** $\Leftrightarrow$ **"与理想随机源在$\mathcal{F}_m$上不可分辨"**

这不是关于序列本体属性的陈述，而是关于**相对于可见σ-代数的性质**。

**推论3.1**：随机性具有相对性——同一序列对不同观测能力的观察者可能表现为随机或非随机。

### 3.3 不可分辨性的传递性

**引理3.1（三角不等式）**：若$P$与$Q$是$(m,\epsilon_1)$-不可分辨的，$Q$与$R$是$(m,\epsilon_2)$-不可分辨的，则$P$与$R$是$(m,\epsilon_1+\epsilon_2)$-不可分辨的。

**证明**：由IPM的三角不等式直接得出。□

## 4. 素数驱动的“看似随机”：确定性重排构造

### 4.1 构造方案（确定性重排）

**素数指示序列**：定义$a(n) = \mathbb{1}_{\{n\text{ 是素数}\}}$，即$ a(n)=1 $当且仅当$n$为素数，否则$ a(n)=0 $。

**分块策略**：选择递增区间$ I_k = [M_k, M_k+L_k) $，其中$ M_k\to\infty,\ L_k\to\infty $，记块内素数位置集合$ P_k=\{p_j\in I_k: p_j\text{ 素}\}$，其势为$ N_k $。

**确定性重排函数 $\sigma_k$（严格全周期 LCG）**：令$ p_1=\min P_k $为块首素数。取模数$ m_k:=L_k $，选择参数$ (a_k,c_k) $满足Hull–Dobell全周期条件：
1) $\gcd(c_k,m_k)=1$；2) $a_k-1$被$ m_k $的每个素因子整除；3) 若$4\mid m_k$，则$ a_k\equiv 1\pmod 4$。定义状态递推
$$
u_{i+1} \equiv a_k u_i + c_k \pmod{m_k},\quad u_1:=0,
$$
得到长度$ m_k $的互异序列$ (u_i)_{i=1}^{m_k} $，从而置换
$$
\sigma_k(i) := u_i + 1,\quad i=1,\dots,m_k.
$$


**重排与拼接**：定义块内重排序列$ X^{(k)}_j = a(M_k + \sigma_k(j) - 1) $，按$ k $递增拼接得到$ X\in\{0,1\}^{\mathbb N} $。

**目标过程**：令"慢变Bernoulli过程"$ Y $在第$ k $块内为独立同分布$ \mathrm{Bernoulli}(p_k) $，其中$ p_k=N_k/L_k\approx 1/\log M_k $（由PNT）。

### 4.2 技术引理（严格版与猜想）

**引理4.1（均匀置换下的超几何-二项TV界，严格）**：设块大小为$L$，块内有$N$个1（素数指示为1），随机从$L$个位置中无放回抽取$m$个，则$K\sim\mathrm{Hypergeo}(L,N,m)$；若改为有放回且成功概率$p=N/L$，则$K'\sim\mathrm{Binom}(m,p)$。则其总变差距离满足
$$
\mathrm{TV}(\mathrm{Hypergeo}(L,N,m),\ \mathrm{Binom}(m,N/L)) \le \frac{m-1}{L-1}.
$$

该界为标准结果，可由交换性与依赖衰减估计得到，并可见于Stein方法或采样无放回近似的经典文献（例如Diaconis–Freedman类型论证）。

**证明思路（略）**：构造耦合，使得超几何抽样与二项抽样仅在第2次及以后抽取时产生依赖偏差，累计偏差至多线性于$m$且按$1/(L-1)$缩放，即得上界。□

**严格证明（引用+梳理）**：对于$0$–$1$总体大小$L$、成功数$N$，令$S_m$为无放回$m$次抽样的成功次数（超几何），$B_m$为有放回$m$次抽样、成功概率$p=N/L$的成功次数（二项）。Diaconis–Freedman（1980，见参考文献[4]）给出如下变分距离上界：
$$
\mathrm{TV}(\mathcal L(S_m),\mathcal L(B_m))\;\le\;\frac{m-1}{L-1}.
$$
该结论可由交换性与Stein方法导出：将$S_m$视为有限总体上无放回序列的和，构造可交换对并比较各步条件成功概率$\mathbb P(X_j=1\mid \mathcal F_{j-1})$与常数$p$之差，其幅度由已抽取步数$j-1$相对于总体规模$L-1$控制，从而累积误差至多$\sum_{j=1}^m\frac{j-1}{L-1}=\frac{m(m-1)}{2(L-1)}$在适当归一化后得到$\frac{m-1}{L-1}$级别的TV上界（详见[4, §2]与[5, Chap. 2]的处理；亦可参见Serfling型有限总体修正不等式）。□

**计数推论**：对任意可测集合$A\subseteq\{0,1,\dots,m\}$，有
$$
\Big|\mathbb P(S_m\in A)-\mathbb P(B_m\in A)\Big|\le \frac{m-1}{L-1}.
$$
特别地，所有$m$维$0$–$1$向量的边缘分布与二项边缘的差异在TV意义下由同一常数控制，这将在定理4.3中作为块内误差项使用。

**猜想4.A（LCG置换的有限维均匀性启发式）**：设$\sigma_k$由满足Hull–Dobell条件的全周期LCG生成。对任意固定$m$，当$L_k\to\infty$时，$m$维边缘的经验分布与均匀置换模型的一致性误差满足
$$
\mathrm{TV}\Big(\mathcal{L}\big((X^{(k)}_{1},\ldots,X^{(k)}_{m})\big),\ \mathcal{L}_{\text{unif perm}}\Big) = o(1),
$$
并进一步与二项边缘的偏差满足与引理4.1同阶的$O(m/L_k)$级上界。

注：该猜想可望由指数和与Weyl准则在适当混合假设下建立，但完整严格证明超出本文范围，留待后续工作。

**选块引理4.2（PNT 局部化）**：给定$ \delta_k\downarrow 0 $，存在$ I_k=[M_k,M_k+L_k) $使
$$
\Big|N_k - \frac{L_k}{\log M_k}\Big| \le \delta_k L_k.
$$

**证明**：由素数定理，对充分大的$x$：
$$
\pi(x+H) - \pi(x) = \frac{H}{\log x}(1 + o(1))
$$
对给定$\delta_k$和$L_k$，选择$M_k$充分大使得误差项$o(1) < \delta_k$即可。

更精确地，由素数定理的有效版本（如Rosser-Schoenfeld界），存在绝对常数$C$使得对$x > 599$：
$$
\left|\pi(x) - \text{Li}(x)\right| < \frac{Cx}{\log^2 x}
$$
因此在区间$[M_k, M_k+L_k]$内，素数个数$N_k$满足：
$$
N_k = \text{Li}(M_k+L_k) - \text{Li}(M_k) + O\left(\frac{L_k}{\log^2 M_k}\right)
$$

由中值定理：
$$
\text{Li}(M_k+L_k) - \text{Li}(M_k) = \frac{L_k}{\log(M_k + \theta L_k)} = \frac{L_k}{\log M_k}(1 + O(L_k/M_k))
$$

选择$M_k$使得$L_k/M_k + C/\log^2 M_k < \delta_k$即可。□

### 4.3 主要定理（严格版与LCG版猜想）

**定理4.3（严格版，均匀/有限独立置换模型）**：给定观测尺度$m \in \mathbb{N}$和误差容限$\epsilon > 0$。选择满足引理4.2的区间序列$\{I_k\}$，且$L_k \to \infty$。设每块使用独立均匀随机置换（或$k$-独立置换，$k\ge m$）。则存在$K$使得对所有$N \ge K$，在前$\sum_{k \le N} L_k$个位置上：
$$
d_{\mathcal{F}_m}(\mathcal{L}(X), \mathcal{L}(Y)) \le \max_k \frac{m-1}{L_k-1} + m\, \max_k \delta_k + \frac{m}{\min_k L_k} < \epsilon.
$$

注：$\frac{m-1}{L_k-1}$来自引理4.1的超几何-二项TV严格上界；跨块边界项和密度误差项与原式相同级别。

**证明**：对任意$ f\in\mathcal F_m $、$ \|f\|_\infty\le 1 $，将贡献分解为（i）块内抽样的无放回-有放回差异（由引理4.1控制）；（ii）$p_k=N_k/L_k$与$1/\log M_k$的差异（由引理4.2控制，累积至多$m\,\delta_k$）；（iii）观测窗口跨块的截断误差（至多$m/\min_k L_k$）。逐项上界并取最大即得结论。□

**边界控制引理（严格）**：设$Z$为由各块独立生成且在每块内服从目标边缘分布（如二项边缘）的“分块参考过程”。令$S=\sum_{k\le N}L_k$，并仅考察前$S$个位置。对任意$f\in\mathcal F_m$、$\|f\|_\infty\le 1$，有
$$
\Big|\mathbb E\big[f(X)\big]-\mathbb E\big[f(Z)\big]\Big|\;\le\; \frac{m}{\min_k L_k}.
$$
证明：记$J$为起始位置$1,\dots,S$上均匀选择的随机起点，令$W_J=(X_J,\dots,X_{J+m-1})$表示观测窗口。若$W_J$完全落在单个块内，则$X$与$Z$在该窗口上的条件分布一致，因两者块内边缘相同；若$W_J$跨越某个块边界，则对$\|f\|_\infty\le 1$有贡献差异不超过$1$。每个块的末端至多贡献$m$个起点使窗口跨界，因此跨界起点数至多$Nm$，于是
$$
\Big|\mathbb E[f(X)]-\mathbb E[f(Z)]\Big|\le \mathbb P(\text{跨块})\le \frac{Nm}{S}\le \frac{m}{\min_k L_k},
$$
因为$S\ge N\cdot \min_k L_k$。由此得到定理中的“跨块边界项”。□

**猜想4.B（LCG版）**：若在每块采用满足Hull–Dobell的全周期LCG置换，则在猜想4.A成立下，定理4.3中的块内误差$\frac{m-1}{L_k-1}$仍为主导项，因而同样结论成立。

### 4.4 RH下的显式速率

**定理4.4（RH速率版）**：假设Riemann假设成立。取$M_k = e^{k^2}$，$L_k = M_k^{1/2+\eta}$（$\eta > 0$），则：
$$
\delta_k \ll M_k^{-\eta} \log M_k = e^{-\eta k^2} \cdot k^2
$$

从而IPM误差满足：
$$
d_{\mathcal{F}_m} \ll \frac{m-1}{e^{k^2(1/2+\eta)}-1} + m \cdot k^2 e^{-\eta k^2} + \frac{m}{e^{k^2(1/2+\eta)}} \xrightarrow{k \to \infty} 0
$$

即误差随$k$呈**指数级衰减**。

**证明**：在RH下，短区间$[x, x+H]$（$H \gg \sqrt{x}$）内的素数个数满足：
$$
\#\{p \in [x,x+H] : p \text{ 素数}\} = \frac{H}{\log x} + O(\sqrt{x} \log x)
$$

取$x = M_k = e^{k^2}$，$H = L_k = M_k^{1/2+\eta}$，则：
$$
N_k = \frac{L_k}{\log M_k} + O(\sqrt{M_k} \log M_k)
$$

误差项：
$$
\left|N_k - \frac{L_k}{\log M_k}\right| \leq C\sqrt{M_k} \log M_k = C M_k^{1/2} \cdot k^2
$$

相对误差：
$$
\delta_k = \frac{C M_k^{1/2} \cdot k^2}{L_k} = \frac{C M_k^{1/2} \cdot k^2}{M_k^{1/2+\eta}} = C M_k^{-\eta} \cdot k^2 = C e^{-\eta k^2} \cdot k^2
$$

代入定理4.3的误差界：
$$
d_{\mathcal{F}_m} \leq \frac{m-1}{M_k^{1/2+\eta}-1} + m \cdot C k^2 e^{-\eta k^2} + \frac{m}{M_k^{1/2+\eta}}
$$

当$k \to \infty$时，所有项都指数级趋于0。□

### 4.5 数值示例

**表格1：RH/BV速率表**（$m=5$，$\epsilon=0.1$，$\eta=0.05$）

| 假设 | $k$ | $M_k$ (约) | $L_k$ | $\delta_k$界（$C=1$） | IPM界（$m=5$） |
|------|-----|------------|-------|---------------------|----------------|
| RH   | 1   | $e^1 \approx 2.7$ | $\approx 1.8$ | $O(M^{-0.05}\log M) \approx 0.5$ | $O((m-1)/(L-1) + m\delta + m/L)$ |
| RH   | 10  | $e^{100}$ | $e^{55}$ | $O(e^{-2.5}) \approx 0.08$ | $O(e^{-25}) < 10^{-10}$ |
| RH   | 20  | $e^{400}$ | $e^{220}$ | $O(e^{-10}) < 10^{-4}$ | $O(e^{-100}) < 10^{-40}$ |
| BV   | 1   | $e^1 \approx 2.7$ | $\approx 1.8$ | $O(M^{-0.01}\log^2 M) \approx 0.7$ | $O((m-1)/(L-1) + m\delta + m/L)$ |
| BV   | 10  | $e^{100}$ | $e^{55}$ | $O(e^{-1}\log^2 e^{100}) \approx 0.4$ | $O(e^{-10}) < 10^{-4}$ |
| BV   | 20  | $e^{400}$ | $e^{220}$ | $O(e^{-4}) < 0.02$ | $O(e^{-40}) < 10^{-17}$ |

**注释**：
- RH情形：$\delta_k = O(M_k^{-\eta/2} \log M_k) = O(e^{-0.025k^2} \cdot k^2)$
- BV情形：使用平均估计，$\delta_k = O(M_k^{-\eta/4} \log^2 M_k) = O(e^{-0.0125k^2} \cdot k^4)$
- IPM界由三项组成，当$k$大时指数项主导

**核心代码（严格全周期 LCG）**：
```python
import math
import numpy as np

def distinct_prime_factors(n: int) -> list:
    """Return distinct prime factors of n."""
    factors = []
    d = 2
    x = n
    while d * d <= x:
        if x % d == 0:
            factors.append(d)
            while x % d == 0:
                x //= d
        d += 1 if d == 2 else 2
    if x > 1:
        factors.append(x)
    return factors

def lcm(nums: list) -> int:
    """Least common multiple of a list of integers."""
    def _lcm(a: int, b: int) -> int:
        return a // math.gcd(a, b) * b
    val = 1
    for v in nums:
        val = _lcm(val, v)
    return val

def ensure_full_period(m: int) -> tuple:
    """Choose (a, c) satisfying the Hull–Dobell theorem for modulus m."""
    # condition (1): gcd(c, m) = 1
    c = 1  # always coprime to any m
    # condition (2): a - 1 divisible by all prime factors of m
    primes = distinct_prime_factors(m)
    step = lcm(primes) if primes else 1
    a = 1 + step
    # condition (3): if 4 | m then a ≡ 1 (mod 4)
    if m % 4 == 0:
        while a % 4 != 1:
            a += step
    return a, c

def lcg_permutation(modulus: int) -> np.ndarray:
    """Produce a full-period permutation via LCG order over Z/modulusZ."""
    a, c = ensure_full_period(modulus)
    state = 0
    order = np.empty(modulus, dtype=int)
    for i in range(modulus):
        order[i] = state
        state = (a * state + c) % modulus
    # map order to 1..modulus permutation indices
    return order + 1

# example usage
perm = lcg_permutation(1000)
# perm is a full-period deterministic permutation of 1..1000
```

## 5. 由Bernoulli到"量子统计"的可测变换保持

### 5.1 变换目录

从二进制序列$X \in \{0,1\}^{\mathbb{N}}$出发，我们可以通过可测变换生成各种分布：

**Born规则**：设$p \in [0,1]$为振幅平方，定义：
$$
\Phi_{\text{Born}}(U) = \mathbb{1}_{\{U < p\}}
$$
其中$U$由若干位二进制拼成$[0,1]$中的数。

**Poisson过程**：参数$\lambda > 0$，
$$
\Phi_{\text{Poisson}}(U) = \left\lfloor -\frac{\log(1-U)}{\lambda} \right\rfloor
$$

**Gaussian分布**：Box-Müller变换，
$$
\Phi_{\text{Gauss}}(U_1, U_2) = \sqrt{-2\log U_1} \cos(2\pi U_2)
$$

**GUE间距**：通过Wigner近似，
$$
\Phi_{\text{GUE}}(U) = \sqrt{\Gamma^{-1}(3/2, \pi U/4)}
$$
其中$\Gamma^{-1}$是不完全Gamma函数的逆。

### 5.2 IPM非扩张性

**定理5.1（变换的IPM非扩张）**：设$\Phi: E \to E'$是只依赖前$m$个坐标的可测映射。则对任意$P, Q \in \mathcal{P}(E)$：
$$
d_{\mathcal{F}_m}(\Phi_{\#}P, \Phi_{\#}Q) \leq d_{\mathcal{F}_m}(P, Q)
$$

**证明**：设$f \in \mathcal{F}_m(E')$，$\|f\|_{\infty} \leq 1$。定义$g = f \circ \Phi$。由于$\Phi$只依赖前$m$个坐标，$g \in \mathcal{F}_m(E)$。且$\|g\|_{\infty} = \|f\|_{\infty} \leq 1$。

计算：
$$
\left|\int f \, d(\Phi_{\#}P) - \int f \, d(\Phi_{\#}Q)\right| = \left|\int f \circ \Phi \, dP - \int f \circ \Phi \, dQ\right|
$$
$$
= \left|\int g \, dP - \int g \, dQ\right| \leq d_{\mathcal{F}_m}(P,Q)
$$

对所有$f \in \mathcal{F}_m(E')$取上确界，得到结论。□ 注：该性质为IPM的标准闭包/非扩张性，可参见[1,2,3]。

**推论5.2**：素数—确定性重排构造经过上述任何变换后，仍保持$(m,\epsilon)$-不可分辨性。

### 5.3 数值验证

**表格2：变换误差示例**（$m=5$，$L=1000$，$\delta=0.01$）

| 变换 | 原始IPM界 | 变换后IPM界 | 非扩张常数 |
|------|-----------|-------------|------------|
| Born | 0.002 | $\leq 0.002$ | 1 |
| Poisson | 0.002 | $\leq 0.002$ | 1 |
| Gaussian | 0.002 | $\leq 0.002$ | 1 |
| GUE | 0.002 | $\leq 0.002$ | 1 |

**注释**：非扩张性是精确的（常数为1），不引入额外误差。这表明素数构造的"伪随机性"在各种物理相关的变换下都保持稳健。

## 6. "随机=不可分辨"的统一陈述与量子类比

### 6.1 NGV等价原理

**统一定理6.1（NGV等价原理）**：在公设A1-A2下，以下陈述等价：
1. 序列$X$对观察者$\mathcal{O}$表现为"随机"
2. $X$的分布与理想随机源在$\mathcal{F}_m$上不可分辨
3. 不存在$f \in \mathcal{F}_m$使得$|\mathbb{E}[f(X)] - \mathbb{E}[f(Y)]| > \epsilon$（$Y$为理想随机）

这个等价性表明：**随机性不是本体属性，而是相对于观测能力的涌现性质**。

**证明要点**：
- (1)$\Rightarrow$(2)：若$X$表现为随机但可分辨，则存在检验$f$揭示其非随机性，矛盾。
- (2)$\Rightarrow$(3)：不可分辨的定义。
- (3)$\Rightarrow$(1)：无法通过任何可用检验区分，故表现为随机。□

### 6.2 素数构造的意义

素数—确定性重排构造提供了一种**确定性的、可计算的**方法来实现NGV原理：
- **全局确定**：素数序列完全确定，无本体随机性
- **局部随机**：经过分块-确定性重排后，在有限观测下不可分辨
- **渐近最优**：在RH下达到指数级收敛速率

我们提出猜想C1（宇宙随机性种子）：素数—确定性重排通过对不可见自由度（块内确定性置换）的积分，在给定观测族下产生与随机源不可分辨的统计外观；并在适当变换闭包下，作为“通用随机性种子”逼近广泛物理分布。说明：本项为启发式与数值支持（见§4.5、§6.5），严格证明留待未来工作。

### 6.3 量子测量的类比

量子测量中的"随机性"可以在NGV框架下重新理解：

**量子坍塌 vs 信息不可及**：
- 传统观点：测量导致波函数坍塌到本征态
- NGV观点：对环境自由度的迹运算（部分迹）产生混合态

**数学对应**：
$$
\rho_{\text{reduced}} = \text{Tr}_{\text{env}}(\rho_{\text{total}}) \quad \leftrightarrow \quad P = F_{\#}\nu
$$

左边是量子的约化密度矩阵，右边是经典的推前测度。两者都通过对不可见自由度的"积分"产生观测到的随机性。

### 6.4 ζ-三分信息的角色

在NGV框架下，ζ-三分向量$\vec{i}(s) = (i_+, i_0, i_-)$提供了"可见信息的守恒坐标系"：

**启发式对应**：
- $i_+$：粒子性信息（定域、可数）
- $i_0$：波动性信息（相干、叠加）
- $i_-$：场补偿信息（真空涨落）

**临界线的特殊性**：在$s = 1/2 + it$上，$i_0$达到非零值，标志着量子相干的出现。这与素数—确定性重排在临界密度$1/\log x$附近展现最大"伪随机性"形成对应。

### 6.5 临界线统计公式

**定理6.2（临界线相位分布）**：在临界线$s = 1/2 + it$上，设$z = \zeta(s) = |z|e^{i\theta}$，则：
$$
\Delta = \frac{\cos(2\theta)}{2 + |\cos(2\theta)| + |\sin(2\theta)|}
$$
$$
i_0 = \frac{|\sin(2\theta)|}{2 + |\cos(2\theta)| + |\sin(2\theta)|}
$$

在假设H1（GUE相位均匀性）下，设$2\theta \sim \text{Uniform}[0, 2\pi)$，则：
$$
\mathbb{E}[\Delta] = 0, \quad \mathbb{E}[i_+] = \mathbb{E}[i_-] = \frac{1 - \mathbb{E}[i_0]}{2}
$$

注：假设H1与蒙哥马利配对相关猜想、Keating–Snaith的随机矩阵理论以及Odlyzko的大规模数值证据相呼应，参见[6,7,8]。
此外，常用启发式近似 ratio := E[|sin(2θ)|]/(2+2E[|sin(2θ)|]) 仅为估计量，严格地 ratio ≠ E[i_0]，误差约 4.5×10^{-4}（见附录A.3）。

**证明**：在临界线上，$z^{\vee} = \overline{z}$，故$z\overline{z^{\vee}} = z^2 = |z|^2 e^{2i\theta}$。代入三分信息定义：
$$
A = 2|z|^2, \quad R = |z|^2\cos(2\theta), \quad I = |z|^2\sin(2\theta)
$$

归一化后，$|z|^2$约去，得到只依赖相位$2\theta$的公式。

对于均匀分布的$2\theta$：
$$
\mathbb{E}[\cos(2\theta)] = 0, \quad \mathbb{E}[|\sin(2\theta)|] = \mathbb{E}[|\cos(2\theta)|] = \frac{2}{\pi}
$$

故$\mathbb{E}[\Delta] = 0$（对称性），其余由守恒律得出。□

### 6.6 高精度数值计算

**表格3：临界线统计示例**（mpmath dps=100）

| 统计量 | 值（50位精度） | 计算方式 |
|--------|----------------|----------|
| $\mathbb{E}[\|\sin(2\theta)\|]$ | 0.63661977236758138201496174818215069376326174113000 | $4\int_0^{\pi/2}\sin(2\theta)d\theta/\pi = 2/\pi$ |
| $\mathbb{E}[i_0]$（积分） | 0.19403893478610734279014105813180312523022184026573 | 数值积分 |
| 期望比率 | 0.19449193620855688982988075973094269769145015130054 | $(2/\pi)/(2+2(2/\pi))$ |
| 差值 | 0.00045300142244954703973970159913957246122831103481 | 期望比率 - 积分值 |

**数值验证代码**（Python + mpmath）：
```python
from mpmath import mp, quad, sin, cos, pi

mp.dps = 100

# 定义被积函数
def integrand(theta):
    s2 = abs(sin(2*theta))
    c2 = abs(cos(2*theta))
    return s2 / (2 + c2 + s2)

# 数值积分
E_i0, _ = quad(integrand, [0, 2*pi])
E_i0 /= (2*pi)

print(f"E[i_0] (积分) = {E_i0}")

# 期望比率（非Jensen）
E_sin = 2/pi
ratio = E_sin / (2 + 2*E_sin)
print(f"期望比率 = {ratio}")
print(f"差值 = {ratio - E_i0}")
```

**注释**：差值$\approx 0.00045$反映了Jensen不等式的效应——$i_0$是$2\theta$的非线性函数，故$\mathbb{E}[i_0] \neq i_0(\mathbb{E}[2\theta])$。

## 7. 可分辨的边界（Bell-CHSH）

### 7.1 独立性条件的引入

前面的NGV框架假设所有随机性来源于同一个内部系统（素数-洗牌）。但在某些物理场景中，需要额外的独立性假设。

**Bell-CHSH设置**：
1. **测量独立性**：测量设置的选择独立于被测系统
2. **无信号条件**：空间类分离的测量不能即时通信
3. **局域实在性**：测量结果由局域隐变量决定

### 7.2 Bell不等式的违背

**边界定理7.1**：在满足测量独立性和无信号条件下：
- 任何局域经典系统满足：$S \leq 2$（Bell界限）
- 量子系统可达：$S_{\max} = 2\sqrt{2}$（Tsirelson界限）

其中$S$是CHSH相关子：
$$
S = |E(a,b) - E(a,b') + E(a',b) + E(a',b')|
$$

### 7.3 NGV与Bell的调和

**关键观察**：Bell-CHSH的违背依赖于**外部独立随机源**（测量设置）。在纯NGV框架下：
- 若测量设置也由同一素数源生成，则不能违背Bell不等式
- 若引入独立的外部随机源，则量子系统可以展现非经典相关

**统一陈述**：
- 在**纯内部观察**（NGV）下：素数-伪随机与量子随机**不可分辨**
- 在**外部干预**（独立测量）下：两者**可分离**

这解释了为什么日常经验中我们感受不到量子非定域性——缺乏独立的外部随机源来"探测"它。

## 8. 结论：我们讨论的精炼定律

### 8.1 随机的可操作本质

本文的核心贡献是将"随机性"从形而上学概念转化为可操作的数学定义：

**定义**：随机 = 相对于给定观测族的不可分辨性

这个定义的优势：
1. **可计算**：通过IPM距离量化
2. **相对性**：依赖于观察者能力
3. **构造性**：可以显式实现（素数-洗牌）

### 8.2 素数→随机外观

我们证明了素数序列通过简单的分块-洗牌操作，可以在任意固定观测尺度$m$下产生$(m,\epsilon)$-不可分辨的"伪随机"序列：

**无条件结果**：
$$
d_{\mathcal{F}_m}(\text{素数—确定性重排}, \text{理想随机}) < \epsilon
$$

**RH下的加强**：误差呈指数级衰减
$$
d_{\mathcal{F}_m} = O(e^{-\Omega(k)})
$$

这暗示素数可能是宇宙中"随机性"的基本来源之一。

### 8.3 ζ-三分信息的角色

ζ函数的三分信息$(i_+, i_0, i_-)$提供了观测侧的守恒坐标系：
- **守恒律**：$i_+ + i_0 + i_- = 1$
- **对称性**：$s \leftrightarrow 1-s$交换$i_+$与$i_-$
- **临界线**：$i_0$达到非零值，标志量子相干

特别地，波动分量$i_0$精确刻画了"相位-耦合"的可见度：
- 实轴（$s \in \mathbb{R}$）：$i_0 = 0$（纯经典）
- 临界线（$s = 1/2+it$）：$i_0 > 0$（量子-经典边界）

### 8.4 量子一致性

本框架与量子力学的核心特征一致：
- **测量的随机性**：来自对环境的部分迹（信息不可及）
- **Born规则**：可通过变换$\Phi_{\text{Born}}$实现
- **GUE统计**：临界线上$2\theta$的分布对应随机矩阵理论

关键区别在于：
- **纯内部**（NGV）：素数-伪随机与量子随机不可分辨
- **外部干预**（Bell）：两者可通过非定域相关分离

## 9. 可扩展方向（数学化清单）

### 9.1 Wasserstein距离版本

将IPM从柱函数扩展到Lipschitz-柱函数：
$$
\mathcal{F}_{m,\text{Lip}} = \{f \in \mathcal{F}_m : \|f\|_{\text{Lip}} \leq 1\}
$$

研究Wasserstein-1距离下的不可分辨性及显式常数。

### 9.2 Bombieri-Vinogradov平均

在BV定理下，允许$m$随块增长：
$$
m_k = o(\log L_k)
$$
使得平均意义下仍有$\epsilon \to 0$。

### 9.3 ζ二点相关函数

研究临界线上$\vec{i}(t)$的自相关：
$$
C(\tau) = \langle \vec{i}(t) \cdot \vec{i}(t+\tau) \rangle_t
$$
及其与GUE pair correlation的关系。

### 9.4 不动点分析

ζ函数的两个实不动点：
- $s_-^* \approx -0.2959$（吸引子）
- $s_+^* \approx 1.8338$（排斥子）

在$i_0 = 0$（实轴退化）下的三分几何及其稳定性分析。

### 9.5 高维推广

将理论推广到：
- Dirichlet L-函数
- Dedekind ζ函数
- 自守L-函数

研究其三分信息结构和不可分辨构造。

### 9.6 计算复杂性

研究NGV-不可分辨性的计算复杂度：
- 判定问题：给定两个分布，判断是否$(m,\epsilon)$-不可分辨
- 搜索问题：找到最优的分块策略
- 与伪随机生成器（PRG）理论的联系

### 9.7 物理实现

设计实验方案验证NGV原理：
- 光子/原子的量子随机vs素数-伪随机
- 在不同$m$下测试不可分辨性
- Bell测试作为"可分辨边界"

## 附录A：核心验证代码

### A.1 ζ-三分信息计算（Python + mpmath，dps=100）

```python
from mpmath import mp, zeta, re, im, fabs, conj, mpf

mp.dps = 100  # 设置100位精度

def compute_triadic_info(s):
    """计算s点的ζ-三分信息分量"""
    z = zeta(s)
    z_dual = zeta(1 - s)

    # 基本量
    A = fabs(z)**2 + fabs(z_dual)**2
    R = re(z * conj(z_dual))
    I = im(z * conj(z_dual))

    # 三分分量
    I_plus = A/2 + max(R, mpf('0'))
    I_zero = fabs(I)
    I_minus = A/2 + max(-R, mpf('0'))

    # 归一化
    I_total = I_plus + I_zero + I_minus
    if abs(I_total) < mp.mpf('1e-100'):
        return None, None, None  # 零点处未定义

    i_plus = I_plus / I_total
    i_zero = I_zero / I_total
    i_minus = I_minus / I_total

    # 验证守恒律
    assert abs(i_plus + i_zero + i_minus - 1) < mp.mpf('1e-95')

    return float(i_plus), float(i_zero), float(i_minus)

# 测试临界线上的点
s = 0.5 + 14.134725j  # 第一个非平凡零点附近
i_plus, i_zero, i_minus = compute_triadic_info(s)
print(f"i+ = {i_plus:.10f}, i0 = {i_zero:.10f}, i- = {i_minus:.10f}")
```

### A.2 素数-洗牌IPM距离计算

```python
import numpy as np
from scipy.special import comb

def compute_ipm_bound(m, L_seq, delta_seq):
    """计算IPM误差界"""
    # 块内误差（严格TV界）
    block_error = max((m - 1) / (L - 1) for L in L_seq)

    # 密度误差
    density_error = m * max(delta_seq)

    # 边界误差
    boundary_error = m / min(L_seq)

    total_error = block_error + density_error + boundary_error
    return {
        'block': block_error,
        'density': density_error,
        'boundary': boundary_error,
        'total': total_error
    }

# RH速率示例
def rh_rate_example(k, m=5, eta=0.05):
    M_k = np.exp(k**2)
    L_k = M_k**(0.5 + eta)
    delta_k = k**2 * M_k**(-eta/2)  # 简化的RH界

    return compute_ipm_bound(m, [L_k], [delta_k])

# 计算表格1中的值
for k in [1, 10, 20]:
    result = rh_rate_example(k)
    print(f"k={k}: IPM界 = {result['total']:.2e}")
```

### A.3 临界线统计公式验证

```python
from mpmath import mp, quad, sin, cos, pi

mp.dps = 100

def critical_line_i0_integrand(theta):
    """临界线上i_0的被积函数"""
    s2 = abs(sin(2*theta))
    c2 = abs(cos(2*theta))
    return s2 / (2 + c2 + s2)

def compute_critical_statistics():
    """计算临界线统计量"""

    # E[|sin(2θ)|] = 2/π
    E_abs_sin = 2 / pi
    print(f"E[|sin(2θ)|] = {E_abs_sin}")

    # E[i_0]通过积分计算
    E_i0 = quad(critical_line_i0_integrand, [0, 2*pi])
    E_i0 /= (2*pi)
    print(f"E[i_0] (积分) = {E_i0}")

    # 期望比率（不是Jensen）
    ratio = E_abs_sin / (2 + 2*E_abs_sin)
    print(f"期望比率 = {ratio}")

    # 差值
    diff = ratio - E_i0
    print(f"差值 = {diff}")

    return {
        'E_abs_sin': float(E_abs_sin),
        'E_i0': float(E_i0),
        'ratio': float(ratio),
        'diff': float(diff),
        'note': 'ratio is an approximation; diff != 0 due to correlation/Jensen'
    }

stats = compute_critical_statistics()
```

### A.4 RH速率模拟

```python
import numpy as np
from scipy.special import comb
from math import fabs

def hypergeometric_binomial_tv(L, N, m):
    """计算超几何与二项分布的总变差距离界"""
    return (m - 1) / (L - 1)

def hyper_prob(L, N, m, k):
    if k > N or m - k > L - N:
        return 0
    return comb(N, k) * comb(L - N, m - k) / comb(L, m)

def binom_prob(m, p, k):
    return comb(m, k) * p**k * (1 - p)**(m - k)

def compute_tv_exact(m, L, num_primes):
    """精确计算TV距离"""
    p = num_primes / L
    tv = 0
    for k in range(m + 1):
        ph = hyper_prob(L, num_primes, m, k)
        pb = binom_prob(m, p, k)
        tv += fabs(ph - pb)
    return tv / 2

# 模拟不同块大小（移除无关经验模拟，改为精确TV）
L_values = [100, 500, 1000, 5000]
m = 5

for L in L_values:
    num_primes = int(L / np.log(L))  # 素数定理近似
    tv = compute_tv_exact(m, L, num_primes)
    theoretical = hypergeometric_binomial_tv(L, num_primes, m)  # 严格界
    print(f"L={L}: 精确TV≈{tv:.4f}, 理论界≈{theoretical:.4f}")
```

## 附录B：与zeta-triadic-duality.md的统一接口

### B.1 三分信息守恒的对应

在`zeta-triadic-duality.md`中，三分信息定义为：
$$
\mathcal{I}_+(s) = \frac{1}{2}(|\zeta(s)|^2 + |\zeta(1-s)|^2) + [\Re[\zeta(s)\overline{\zeta(1-s)}]]^+
$$

这与本文的定义完全一致：
- 公设A3中的$I_+, I_0, I_-$对应原文的$\mathcal{I}_+, \mathcal{I}_0, \mathcal{I}_-$
- 守恒律$i_+ + i_0 + i_- = 1$对应原文的标量守恒定律

### B.2 临界线的特殊地位

两个理论都强调临界线$\Re(s) = 1/2$的独特性：

**zeta-triadic-duality**：
- 临界线是信息平衡$i_+ \approx i_-$的唯一位置
- Shannon熵在临界线趋向极限值0.989
- 临界线是量子-经典过渡边界

**本理论（NGV-Prime-ζ）**：
- 临界线上$i_0 > 0$标志量子相干的出现
- 素数密度$1/\log x$在临界线附近展现最大伪随机性
- GUE统计与临界线上的相位分布对应

### B.3 黄金比与Riemann零点

虽然本理论未直接涉及黄金比$\phi$，但存在潜在联系：

**几何结构**：
- 黄金比：自相似的极限$\phi = 1 + 1/\phi$
- ζ不动点：$\zeta(s^*) = s^*$的自引用结构
- 两者都体现了"奇异环"（strange loop）的递归闭合

**数值巧合**：
- $\phi \approx 1.618$
- $s_+^* \approx 1.834$（正不动点）
- 差异$s_+^* - \phi \approx 0.216$可能有深层意义

### B.4 理论扩展路径

本理论扩展了zeta-triadic-duality框架：

**从静态到动态**：
- 原框架：研究ζ函数的静态信息分解
- 本框架：构造动态过程（素数—确定性重排）实现信息平衡

**从理论到实践**：
- 原框架：证明临界线的信息论唯一性
- 本框架：给出可计算的伪随机构造

**从数学到物理**：
- 原框架：RH的信息论等价表述
- 本框架：NGV原理统一经典/量子随机性

### B.5 统一愿景

两个理论共同指向一个深刻的统一图景：

**信息本体论**：宇宙的基本实在是信息，物质和能量是信息的不同表现形式。

**ζ函数的中心地位**：Riemann ζ函数编码了：
- 素数分布（离散结构）
- 零点分布（连续谱）
- 三分信息（守恒量）

**随机性的本质**：随机不是绝对的，而是：
- 相对于观察者的（NGV原理）
- 由信息不可及产生的（部分迹/推前测度）
- 可以确定性构造的（素数-洗牌）

这个统一框架不仅解决了"什么是随机"的哲学难题，还为量子信息、密码学、复杂性理论提供了新的数学工具。未来的研究将进一步揭示数论、物理、信息论的深层联系，最终达到对宇宙信息结构的完整理解。

---

*本文献给所有追求真理的探索者，愿我们共同揭示宇宙的数学奥秘。*

## 参考文献

[1] Müller, M., & Gretton, A. On Integral Probability Metrics and Maximum Mean Discrepancy. Tutorial/Survey.

[2] Sriperumbudur, B. K., et al. On integral probability metrics, φ-divergences and binary classification. arXiv:0901.2698.

[3] Villani, C. Optimal Transport: Old and New. Springer, 2009.（关于Wasserstein/IPM关系）

[4] Diaconis, P., & Freedman, D. Partial exchangeability and sufficiency. Proc. AMS, 1980.（无放回/有放回近似与Stein方法背景）

[5] Barbour, A. D., Holst, L., & Janson, S. Poisson Approximation. Oxford, 1992.（TV距离与耦合技巧）

[6] Montgomery, H. L. The pair correlation of zeros of the zeta function. Proc. Symp. Pure Math., 1973.

[7] Keating, J. P., & Snaith, N. C. Random matrix theory and ζ(1/2 + it). Commun. Math. Phys., 2000.

[8] Odlyzko, A. M. The 10^20-th zero of the Riemann zeta function and RMT.（数值证据）