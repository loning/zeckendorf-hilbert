# 延迟量子化、反馈闭环与 $\pi$-台阶奇偶跃迁

从刻度同一式到自指散射网络的 $\mathbb Z_2$ 拓扑结构

---

## Abstract

在频域散射理论与反馈网络的统一框架中，带有可调闭环延迟的网络在广泛的物理平台上展示出高度鲁棒的相位台阶与群延迟脉冲现象：当反馈往返时间 $\tau$ 缓慢变化时，总散射相位及其频率导数在某些参数值附近出现幅度约为 $\pi$ 的跃迁，并伴随谱流方向的翻转。本文在刻度同一式

$$
\kappa(\omega;\tau)
=\frac{\varphi'(\omega;\tau)}{\pi}
=\rho_{\mathrm{rel}}(\omega;\tau)
=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega;\tau)
$$

的约束下，对这一"延迟量子化 $\Rightarrow \pi$-台阶 $\Rightarrow \mathbb Z_2$ 奇偶跃迁"现象给出严整的谱与拓扑刻画。这里 $S(\omega;\tau)$ 是随角频率 $\omega$ 与等效往返延迟 $\tau$ 变化的无损散射矩阵族，$\varphi(\omega;\tau)=\arg\det S(\omega;\tau)$ 为总散射相位，$\mathsf Q(\omega;\tau)=-\mathrm i S(\omega;\tau)^\dagger \partial_\omega S(\omega;\tau)$ 为 Wigner–Smith 群延迟矩阵。

在自然的解析性、无损性与零极点简单性假设下，本文证明：当 $\tau$ 穿越一族"延迟量子化台阶"

$$
\tau_k=\tau_0+k\,\Delta\tau,\qquad k\in\mathbb Z,
$$

散射矩阵 $\det S(\omega;\tau)$ 的零极点谱流在复频平面上发生一次横过实轴的越位事件，由辐角原理可知对应的总相位在固定频率切片上产生大小为 $\pm\pi$ 的跃迁；相应地，由谱流计数构造的拓扑指标

$$
\nu(\tau)\in\{0,1\},\qquad
\nu(\tau+\Delta\tau)=\nu(\tau)\oplus 1
$$

在每个台阶处发生一次 $\mathbb Z_2$ 奇偶翻转。

为使结果可计算且可实验校验，本文首先在一维单通道标量模型上给出显式解析形式

$$
S_{\mathrm{tot}}(\omega;\tau)
=r_0(\omega)
+\frac{t_0(\omega)^2 \,\mathrm e^{\mathrm i\omega\tau}}
{1-r_{\mathrm{fb}}(\omega)\,\mathrm e^{\mathrm i\omega\tau}},
$$

并利用辐角原理与极点轨迹分析严格推导出 $\pi$-台阶与单位群延迟脉冲的大小与符号。随后推广至多通道矩阵情形，说明在适当选择 $\det S(\omega;\tau)$ 的分支后，主结论仅依赖于有效反馈块 $\mathsf R(\omega)$ 的特征值谱流，因此对具体实现平台具有普适性。

在统一时间刻度的视角下，可调闭环延迟构成一个天然的拓扑驱动参数：每跨越一个延迟量子化台阶，谱流在参数空间上跨越实轴一次，从而在 $\mathbb Z_2$ 意义下在两个拓扑扇区之间切换。该拓扑翻转在任何线性无损平台上都以易于测量的总相位与群延迟 $\pi$-台阶指纹呈现，并可嵌入自指散射网络、自旋双覆盖和 Null–Modular 双覆盖等更高层结构之中，提供统一的频域拓扑读数。

---

## Keywords

延迟量子化；反馈闭环；散射矩阵；Wigner–Smith 群延迟；刻度同一式；相位台阶；$\mathbb Z_2$ 奇偶；自指散射网络；拓扑不变量

---

## 1 Introduction & Historical Context

### 1.1 延迟反馈网络与 $\pi$ 相位跳变的实验现象

从光纤环谐振腔、集成微环谐振器到微波闭环网络和声学环型共振器，带有限往返时间的闭环反馈结构在不同物理平台上反复出现。其公共特征是：在环路中往返一次的波包会获得一个总相位

$$
\Phi(\omega;\tau)=\phi_0(\omega)+\omega\tau,
$$

其中 $\phi_0(\omega)$ 为由内核散射与耦合器引入的附加相位，$\tau$ 为等效往返时间。当 $\Phi(\omega;\tau)$ 满足整数或半整数的量子化条件时，网络的共振、干涉与透射零点结构发生显著变化，引发输出幅度与相位的突变。

在光学环谐振与 Mach–Zehnder 干涉仪的组合结构中，围绕共振频率常观测到透射谱中的 $\pi$ 级相位跃迁及其与干涉型诱导透明效应的对应关系。相关实验与建模表明，这些相位跳变与环路中两条或多条路径之间的相干干涉，以及谐振模式在参数空间中的拓扑结构密切相关。

类似的 $\pi$-跳变现象也出现在相移光栅与 split-ring 共振器等系统的透射与反射相位中，常被用作识别节点结构与模式拓扑的指示量。然而，在这些具体结构之上，尚缺乏一个统一的谱理论框架，将"可调延迟""相位台阶""奇偶拓扑扇区"系统地联系起来。

### 1.2 散射相位、态密度与时间延迟

在量子散射与波动散射理论中，散射矩阵 $S(\omega)$ 的相位与时间延迟、态密度之间的深刻关系已由多方面工作系统建立。Wigner 与 Smith 引入的群延迟与 Wigner–Smith 时间延迟矩阵

$$
\mathsf Q(\omega)
=-\mathrm i\,S(\omega)^\dagger \partial_\omega S(\omega)
$$

刻画了波包在散射势场中的平均停留时间，对于量子、声学和电磁波散射均具有直接的物理意义。

另一方面，Friedel 和 Levinson 型定理表明，在适当条件下，散射相位导数与有无相互作用时态密度的差之间存在线性关系。对一维或部分波散射，可得到形式

$$
\frac{\mathrm d}{\mathrm dE}\delta_l(E)
\propto \rho_l(E)-\rho_l^{(0)}(E),
$$

其中 $\delta_l$ 是部分波相移，$\rho_l$ 与 $\rho_l^{(0)}$ 分别为有无相互作用时的态密度。这类结果在近年的数学物理工作中被重新表述为关于谱移函数与时间延迟的拓扑指数配对，为散射理论引入了清晰的 K-理论与谱流视角。

在实验方面，Wigner 延迟已在原子散射、波导与光学结构中被直接测量，并与共振寿命与局域态密度联系在一起。因此，将散射相位、群延迟与态密度统一在一个刻度同一式之下，是自然的理论发展方向。

### 1.3 谱流、拓扑不变量与 $\mathbb Z_2$ 结构

谱流在参数空间中刻画算子谱的连续演化，其与拓扑不变量、尤其是整数与 $\mathbb Z_2$ 指数之间的关系在多种情形下得到系统研究。对于酉散射矩阵，参数变化引起的零极点轨迹可以通过辐角原理与指数配对刻画，从而导出类似"拓扑 Levinson 定理"的结论：相位的总体变化等于谱流计数。

在许多系统中，每一次参数改变导致的谱流横过实轴时，总相位只发生半圈的绕行，对应于 $\pi$ 而非 $2\pi$ 的跳变。这提示存在一个天然的双覆盖结构：基础参数空间上每一处越位事件在"提升空间"中对应两个扇区，二者间以 $\mathbb Z_2$ 奇偶区别。这一结构与自旋双覆盖、费米统计中的换页现象以及 Null–Modular 几何中的双覆盖扇区具有形式上的同构。

### 1.4 本文的目标与结构

本文聚焦于带可调闭环延迟的散射网络，将其形式化为参数族

$$
S(\omega;\tau)\in\mathrm U(N),
$$

其中 $\omega\in\mathbb R$ 为频率，$\tau\in\mathbb R$ 为可控的等效往返时间。在刻度同一式

$$
\kappa(\omega;\tau)
=\frac{1}{\pi}\partial_\omega\varphi(\omega;\tau)
=\rho_{\mathrm{rel}}(\omega;\tau)
=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega;\tau)
$$

的约束下，本文建立以下三点主结论：

1. 在自然的解析性与非简并性假设下，随 $\tau$ 变化的零极点谱流在复频平面上形成一列孤立的"越位事件"，每个事件对应极点或零点横过实轴一次。

2. 每个越位事件在固定频率切片上引起总相位 $\varphi(\omega;\tau)$ 大小为 $\pm\pi$ 的跃迁；由此构造的拓扑计数 $N(\tau)$ 在每个事件处改变 $\pm 1$。

3. 由 $N(\tau)\bmod 2$ 定义的 $\mathbb Z_2$ 指标 $\nu(\tau)$ 在每个延迟量子化台阶处翻转一次，形成"延迟量子化 $\Rightarrow \pi$-台阶 $\Rightarrow \mathbb Z_2$ 奇偶跃迁"的统一结构。

在理论上，本文给出上述结构的谱与拓扑证明，并通过一维标量与多通道矩阵模型说明其普适性；在应用上，本文提出一系列基于光学、微波与声学平台的实验方案，用以测量 $\pi$-台阶并重构 $\mathbb Z_2$ 指标，为自指散射网络与双覆盖结构提供频域读数。

---

## 2 Model & Assumptions

### 2.1 频域散射矩阵、总相位与群延迟

考虑一个具有 $N$ 个外部通道的线性无损网络，其频域散射矩阵记为

$$
S(\omega;\tau)\in\mathbb C^{N\times N},\qquad \omega\in\mathbb R,\ \tau\in I\subset\mathbb R,
$$

其中 $I$ 为某一参数区间。无损性意味着对每个实频 $\omega$ 与 $\tau\in I$，有

$$
S(\omega;\tau)^\dagger S(\omega;\tau)=\mathbb I_N.
$$

对固定 $\tau$，假定 $S(\cdot;\tau)$ 可向上半平面解析延拓，其极点对应共振或准束缚态；对固定 $\omega$，假定 $S(\omega;\cdot)$ 在 $I$ 上解析。定义总散射相位

$$
\varphi(\omega;\tau)=\arg\det S(\omega;\tau)\in\mathbb R/2\pi\mathbb Z,
$$

并在选定参考点 $(\omega_*,\tau_*)$ 的邻域中固定一个连续分支，使 $\varphi(\omega_*,\tau_*)=0$。

Wigner–Smith 群延迟矩阵定义为

$$
\mathsf Q(\omega;\tau)
=-\mathrm i\,S(\omega;\tau)^\dagger\partial_\omega S(\omega;\tau).
$$

对酉矩阵族可得

$$
\partial_\omega\varphi(\omega;\tau)
=\Im\partial_\omega\log\det S(\omega;\tau)
=\frac{1}{2}\operatorname{tr}\mathsf Q(\omega;\tau),
$$

由此得到刻度密度

$$
\kappa(\omega;\tau)
:=\frac{1}{\pi}\partial_\omega\varphi(\omega;\tau)
=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega;\tau).
$$

在标准散射设定下，$\kappa(\omega;\tau)$ 可以等同为相对态密度 $\rho_{\mathrm{rel}}(\omega;\tau)$，即有无散射势时态密度之差。这一等同使刻度同一式

$$
\kappa(\omega;\tau)
=\frac{\varphi'(\omega;\tau)}{\pi}
=\rho_{\mathrm{rel}}(\omega;\tau)
=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega;\tau)
$$

成为连接相位、时间与态密度的统一母式。

### 2.2 可调延迟的反馈闭环模型

给定一个无延迟的"内核网络" $S_0(\omega)$，在其若干端口之间引入一条具有往返延迟 $\tau$ 的闭环支路，其频域描述为

$$
D(\omega;\tau)=\mathrm e^{\mathrm i\omega\tau}\,\mathbb I_M,\qquad M\le N.
$$

利用 Redheffer 星积或 Schur 补，可以将内核网络与延迟子块组合成等效散射矩阵

$$
S(\omega;\tau)
=S_0(\omega)
+S_1(\omega)\bigl(\mathbb I_M-\mathsf R(\omega)\mathrm e^{\mathrm i\omega\tau}\bigr)^{-1}S_2(\omega),
$$

其中 $\mathsf R(\omega)$ 为某个有效反馈块，$S_1,S_2$ 为耦合矩阵。内核无损且延迟子块为纯相位时，$S(\omega;\tau)$ 对每个实频 $\omega$ 仍为酉矩阵。极点与部分零点由

$$
\det\bigl(\mathbb I_M-\mathsf R(\omega)\mathrm e^{\mathrm i\omega\tau}\bigr)=0
$$

控制。令 $\lambda_j(\omega)$ 为 $\mathsf R(\omega)$ 的特征值，则对应的极点满足

$$
1-\lambda_j(\omega)\mathrm e^{\mathrm i\omega\tau}=0
\quad\Longleftrightarrow\quad
\mathrm e^{\mathrm i\omega\tau}=\lambda_j(\omega)^{-1}.
$$

在一维标量极简模型中，内核网络由复杂反射系数 $r_0(\omega)$ 与透射系数 $t_0(\omega)$ 描述，反馈支路反射系数为 $r_{\mathrm{fb}}(\omega)$。总散射系数为

$$
S_{\mathrm{tot}}(\omega;\tau)
=r_0(\omega)
+\frac{t_0(\omega)^2\,\mathrm e^{\mathrm i\omega\tau}}
{1-r_{\mathrm{fb}}(\omega)\,\mathrm e^{\mathrm i\omega\tau}},
$$

其分母 $1-r_{\mathrm{fb}}(\omega)\mathrm e^{\mathrm i\omega\tau}$ 的零点给出极点轨迹。

### 2.3 解析性与非简并性假设

后续定理的证明依赖如下假设。

**假设 A（解析性与非简并性）**

1. 对每个 $\tau\in I$，$S(\cdot;\tau)$ 可向上半平面解析延拓，所有零极点均为有限阶且在紧致区域内仅有有限多个。

2. 对每个 $\omega\in\mathbb R$，$S(\omega;\cdot)$ 在 $I$ 上解析。

3. 存在一列 $\{\tau_k\}\subset I$ 与对应的频率 $\{\omega_k\}\subset\mathbb R$，使得在每个 $(\omega_k,\tau_k)$ 的邻域内，$\det S(\omega;\tau)$ 恰有一个零点或极点 $z_k(\tau)$ 横过实轴，且满足

   $$
   z_k(\tau_k)=\omega_k,\qquad \partial_\tau\Im z_k(\tau_k)\neq 0,
   $$

   同一邻域中不存在其他零极点同时穿越实轴。

满足假设 A 时，$(\omega_k,\tau_k)$ 被称为"越位事件"，$\{\tau_k\}$ 被称为"延迟量子化台阶"的一族。后来将看到，当 $\mathsf R(\omega)$ 的特征值沿单位圆以近似等间隔移动时，$\tau_k$ 近似构成等差列

$$
\tau_k\simeq\tau_0+k\,\Delta\tau,\qquad k\in\mathbb Z,
$$

其中 $\Delta\tau$ 由平均往返相位量子化条件给定。

---

## 3 Main Results (Theorems and Alignments)

本节在假设 A 下给出关于延迟驱动谱流、$\pi$-台阶与 $\mathbb Z_2$ 指标的主定理，并将其与刻度同一式对齐。

### 3.1 延迟驱动谱流与辐角原理

对固定 $\tau\in I$，设 $\det S(\cdot;\tau)$ 在上半平面具有零点 $\{z_j(\tau)\}$ 与极点 $\{p_k(\tau)\}$（重数计），并满足适当的增长条件。取围绕实轴区间 $[\omega_1,\omega_2]$ 的闭合等高线 $\Gamma$，辐角原理给出

$$
\frac{1}{2\pi}\Delta_\Gamma\arg\det S(\cdot;\tau)
=N_{\mathrm{zero}}(\tau)-N_{\mathrm{pole}}(\tau),
$$

其中 $N_{\mathrm{zero}}(\tau),N_{\mathrm{pole}}(\tau)$ 分别为 $\Gamma$ 内零点与极点个数。选取标准"钥匙孔"路径，得到实轴积分形式

$$
\frac{1}{\pi}\bigl(\varphi(\omega_2;\tau)-\varphi(\omega_1;\tau)\bigr)
=N_{\mathrm{zero}}(\tau)-N_{\mathrm{pole}}(\tau).
$$

对固定频率窗 $[\omega_1,\omega_2]$，随着 $\tau$ 的连续变化，零极点轨迹 $\{z_j(\tau),p_k(\tau)\}$ 在复频平面上连续演化。每当某个零点或极点横过实轴时，右侧计数改变 $\pm 1$，从而导致总相位在该频率窗内出现一个"台阶"。

### 3.2 延迟量子化台阶与越位事件

在具有延迟支路的网络中，零极点方程常可写为

$$
\det\bigl(\mathbb I_M-\mathsf R(\omega)\mathrm e^{\mathrm i\omega\tau}\bigr)=0.
$$

令 $\lambda_j(\omega)$ 为 $\mathsf R(\omega)$ 的特征值，极点条件为

$$
1-\lambda_j(\omega)\mathrm e^{\mathrm i\omega\tau}=0.
$$

若 $\lambda_j(\omega)=|\lambda_j(\omega)|\mathrm e^{\mathrm i\phi_j(\omega)}$，取对数得到极点近似位置

$$
\omega_{j,n}(\tau)
=\frac{1}{\tau}\Bigl(\phi_j(\omega_{j,n})+2\pi n-\mathrm i\ln|\lambda_j(\omega_{j,n})|^{-1}\Bigr).
$$

当 $|\lambda_j(\omega)|\lesssim 1$ 且 $\tau$ 在宏观尺度上变化时，实部近似为

$$
\Re\omega_{j,n}(\tau)\simeq\frac{\phi_j+2\pi n}{\tau},
$$

想象 $n$ 固定而 $\tau$ 增大，极点沿从远端向原点收缩的轨迹移动，并在适当条件下趋近实轴。通过微小的损耗或耦合调整，可以构造使极点横过实轴的情形，从而实现假设 A 中的越位事件。

由于 $\omega\tau$ 的维度无量纲，越位事件通常对应于条件

$$
\omega_k\tau_k+\phi_j(\omega_k)\simeq(2m_k+1)\pi,\qquad m_k\in\mathbb Z,
$$

即往返相位满足半整数量子化，这自然地定义出一族近似等间隔的延迟台阶 $\{\tau_k\}$。

### 3.3 $\pi$-台阶与 $\mathbb Z_2$ 奇偶跃迁主定理

在越位事件附近，可以将 $\det S(\omega;\tau)$ 写成局域分解

$$
\det S(\omega;\tau)
=(\omega-z_k(\tau))^{m_k} g_k(\omega;\tau),
$$

其中 $m_k=+1$ 对应零点，$m_k=-1$ 对应极点，$g_k$ 在邻域内解析且非零。定义在 $\tau_k$ 处的局域相位跃迁

$$
\Delta\varphi_k
=\lim_{\epsilon\to 0^+}
\Bigl(
\varphi(\omega_k;\tau_k+\epsilon)-\varphi(\omega_k;\tau_k-\epsilon)
\Bigr),
$$

以及归一化跳数

$$
\Delta n_k
=\frac{1}{\pi}\Delta\varphi_k.
$$

**定理 3.1（$\pi$-台阶与单位跃迁）**

在假设 A 下，对每个越位事件 $(\omega_k,\tau_k)$，局域相位变化满足

$$
\Delta\varphi_k=\pm\pi,\qquad
\Delta n_k=\pm 1.
$$

证明见第 4 节与附录 A。其核心是当 $z_k(\tau)$ 横过实轴时，$\omega_k-z_k(\tau)$ 在复平面上绕过原点半圈，从而 $\arg(\omega_k-z_k(\tau))$ 跳变 $\pm\pi$，而解析因子 $g_k$ 贡献连续相位不影响跳数。

通过累加所有延迟小于 $\tau$ 的越位事件，定义全局谱流计数

$$
N(\tau)=\sum_{\tau_k<\tau}\Delta n_k\in\mathbb Z,
\qquad
\nu(\tau)=N(\tau)\bmod 2\in\{0,1\}.
$$

**定理 3.2（$\mathbb Z_2$ 奇偶跃迁）**

在假设 A 下，拓扑指标

$$
\nu(\tau)=N(\tau)\bmod 2
$$

在每个延迟台阶 $\tau_k$ 处发生一次奇偶翻转，即

$$
\nu(\tau_k+0)=\nu(\tau_k-0)\oplus 1.
$$

特别地，若 $\tau_k$ 构成近似等差列 $\tau_k\simeq\tau_0+k\Delta\tau$，则当 $\tau$ 沿 $I$ 单调增加时，$\nu(\tau)$ 执行近似理想的 $\mathbb Z_2$ 方波。

上述结果把延迟量子化与 $\pi$-台阶、$\mathbb Z_2$ 拓扑扇区之间的关系精确化：每一次极点或零点横过实轴对应一次单位谱流事件，推动拓扑指标翻转。

### 3.4 刻度同一式下的统一时间读数

由刻度同一式

$$
\kappa(\omega;\tau)
=\frac{1}{\pi}\partial_\omega\varphi(\omega;\tau)
=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega;\tau),
$$

取频率窗 $[\omega_k-\delta\omega,\omega_k+\delta\omega]$，定义

$$
I(\tau)
=\int_{\omega_k-\delta\omega}^{\omega_k+\delta\omega}\kappa(\omega;\tau)\,\mathrm d\omega
=\frac{1}{\pi}\bigl[\varphi(\omega_k+\delta\omega;\tau)-\varphi(\omega_k-\delta\omega;\tau)\bigr].
$$

**命题 3.3（刻度密度积分的单位跃迁）**

在假设 A 下，对每个越位事件 $(\omega_k,\tau_k)$，存在足够小的 $\delta\omega>0$，使得

$$
I(\tau_k+0)-I(\tau_k-0)=\Delta n_k=\pm 1.
$$

也即，群延迟迹 $\operatorname{tr}\mathsf Q(\omega;\tau)$ 在一小频率窗内的积分在每个延迟量子化台阶处跃迁一个单位。

由此可见，拓扑指标 $\nu(\tau)$ 不仅可以通过总相位在参数空间中的跳变定义，也可通过刻度密度或相对态密度的频率积分跃迁来等价描述。

---

## 4 Proofs

本节给出主定理的证明轮廓，将技术细节归入附录 A 与 B。

### 4.1 局域辐角分析与定理 3.1 的证明

在越位事件 $(\omega_k,\tau_k)$ 的邻域内，将 $\det S(\omega;\tau)$ 写成

$$
\det S(\omega;\tau)
=(\omega-z(\tau))^{m}g(\omega;\tau),
$$

其中 $z(\tau_k)=\omega_k$，$\partial_\tau\Im z(\tau_k)\neq 0$，$m=\pm 1$，$g$ 解析且 $g(\omega_k;\tau_k)\neq 0$。

对固定 $\omega=\omega_k$，考虑函数

$$
h(\tau)=\omega_k-z(\tau)=a(\tau)-\mathrm i b(\tau),
$$

其中 $a(\tau)=\omega_k-\Re z(\tau)$，$b(\tau)=\Im z(\tau)$。在 $\tau_k$ 附近，$a(\tau_k)\neq 0$，$b(\tau_k)=0$，且 $\partial_\tau b(\tau_k)\neq 0$，故当 $\tau$ 穿越 $\tau_k$ 时，向量 $h(\tau)$ 在复平面上穿越实轴。

标准复分析几何表明：

$$
\Delta\arg h
:=\lim_{\epsilon\to 0^+}\bigl[\arg h(\tau_k+\epsilon)-\arg h(\tau_k-\epsilon)\bigr]
=\pm\pi,
$$

符号由 $a(\tau_k)$ 与 $\partial_\tau b(\tau_k)$ 的符号决定。由于

$$
\varphi(\omega_k;\tau)
=m\arg h(\tau)+\arg g(\omega_k;\tau),
$$

且 $g$ 在邻域内非零，$\arg g(\omega_k;\tau)$ 可选连续分支，故在局域极限中

$$
\Delta\varphi_k
=m\,\Delta\arg h
=\pm\pi.
$$

于是 $\Delta n_k=\Delta\varphi_k/\pi=\pm 1$，定理 3.1 得证。详细证明见附录 A。

### 4.2 刻度密度积分与定理 3.3 的证明

由

$$
I(\tau)
=\frac{1}{\pi}\bigl[\varphi(\omega_k+\delta\omega;\tau)-\varphi(\omega_k-\delta\omega;\tau)\bigr],
$$

可写

$$
I(\tau_k+0)-I(\tau_k-0)
=\frac{1}{\pi}\Bigl(\Delta\varphi(\omega_k+\delta\omega)-\Delta\varphi(\omega_k-\delta\omega)\Bigr).
$$

选择 $\delta\omega$ 足够小，使得在矩形区域

$$
[\omega_k-\delta\omega,\omega_k+\delta\omega]\times[\tau_k-\delta\tau,\tau_k+\delta\tau]
$$

内仅有一个越位零点或极点，且其轨迹横过频率窗中线。利用附录 A 中对局域因子 $(\omega-z(\tau))^m$ 的分析可知，在该区域内 $\Delta\varphi(\omega;\cdot)$ 对 $\omega$ 为分段常数函数，其在 $\omega_k$ 左右两侧的取值差为 $\pm\pi$。从而

$$
I(\tau_k+0)-I(\tau_k-0)=\pm 1.
$$

这证明了命题 3.3。由 $N(\tau)$ 的定义与整数加法结构，显然 $\nu(\tau)=N(\tau)\bmod 2$ 在每个台阶处翻转一次，定理 3.2 因而成立。

### 4.3 有限阶 Euler–Maclaurin 与数值误差控制

在实际数值与实验数据处理中，刻度密度积分常通过有限采样近似为离散求和。令

$$
I_h(\tau)=h\sum_{n=0}^N \kappa(\omega_n;\tau),\qquad
\omega_n=\omega_k-\delta\omega+nh,
$$

其中 $h=(2\delta\omega)/N$。Euler–Maclaurin 公式给出

$$
I_h(\tau)
=\int_{\omega_k-\delta\omega}^{\omega_k+\delta\omega}\kappa(\omega;\tau)\,\mathrm d\omega
+\mathcal O(h^2),
$$

前提是 $\kappa(\omega;\tau)$ 在频率窗内具有有界二阶导数。只要采样步长 $h$ 足够小，相位台阶的高度 $\pm 1$ 只会被平滑化，不会被抹去或翻转。

附录 B 给出了 Euler–Maclaurin 余项的标准估计，说明极点邻域的"奇性"仅在有限分辨率下被圆滑，而不会改变谱流计数。因而拓扑指标 $\nu(\tau)$ 对有限分辨率与噪声具有鲁棒性。

---

## 5 Model Apply

本节回到具体模型，展示主定理在单通道标量与多通道矩阵模型中的具体实现，并讨论自指散射网络中的局域线性化。

### 5.1 单通道反射式反馈模型

考虑单通道模型

$$
S_{\mathrm{tot}}(\omega;\tau)
=r_0(\omega)
+\frac{t_0(\omega)^2\,\mathrm e^{\mathrm i\omega\tau}}
{1-r_{\mathrm{fb}}(\omega)\,\mathrm e^{\mathrm i\omega\tau}},
$$

在一小频率窗内采用"慢变近似"，视 $r_0,t_0,r_{\mathrm{fb}}$ 为常数，记 $r_0,t_0,r_{\mathrm{fb}}\in\mathbb C$，满足

$$
|r_0|^2+|t_0|^2=1,\qquad |r_{\mathrm{fb}}|\le 1.
$$

写作

$$
S_{\mathrm{tot}}(\omega;\tau)
=\frac{N(\omega;\tau)}{D(\omega;\tau)},
$$

其中

$$
D(\omega;\tau)=1-r_{\mathrm{fb}}\mathrm e^{\mathrm i\omega\tau},\qquad
N(\omega;\tau)=r_0 D(\omega;\tau)+t_0^2\mathrm e^{\mathrm i\omega\tau}.
$$

在典型情形中，$N$ 随 $\tau$ 缓慢变化，而 $D$ 决定主要的相位跳变结构。将

$$
z(\tau)=r_{\mathrm{fb}}\mathrm e^{\mathrm i\omega\tau},
$$

则

$$
D(\omega;\tau)=1-z(\tau).
$$

当 $|r_{\mathrm{fb}}|=1$ 时，$z(\tau)$ 在单位圆上绕原点匀速转动；每当 $z(\tau)$ 穿越点 $1$ 附近，$\arg(1-z(\tau))$ 发生 $\pi$ 级跳变。

若进一步取 $r_{\mathrm{fb}}=\mathrm e^{\mathrm i\phi_{\mathrm{fb}}}$，则

$$
D(\omega;\tau)=1-\mathrm e^{\mathrm i(\omega\tau+\phi_{\mathrm{fb}})},
$$

可推得

$$
\arg D(\omega;\tau)
=\frac{\omega\tau+\phi_{\mathrm{fb}}}{2}
+\frac{\pi}{2}\,\operatorname{sgn}\Bigl[
\cos\Bigl(\frac{\omega\tau+\phi_{\mathrm{fb}}}{2}\Bigr)
\Bigr]
\quad(\bmod 2\pi),
$$

从而在

$$
\omega\tau+\phi_{\mathrm{fb}}=(2k+1)\pi,\qquad k\in\mathbb Z,
$$

附近，$\arg D$ 跳变 $\pi$。由于总相位中 $-\arg D$ 为主导项，总相位 $\varphi(\omega;\tau)$ 对 $\tau$ 呈现典型的 $\pi$-台阶结构。延迟量子化台阶为

$$
\tau_k(\omega)
=\frac{(2k+1)\pi-\phi_{\mathrm{fb}}}{\omega}.
$$

### 5.2 多通道矩阵反馈与特征值谱流

多通道情形下，极点由

$$
\det(\mathbb I_M-\mathsf R(\omega)\mathrm e^{\mathrm i\omega\tau})=0
$$

给出。记 $\lambda_j(\omega)=|\lambda_j(\omega)|\mathrm e^{\mathrm i\phi_j(\omega)}$ 为 $\mathsf R(\omega)$ 的特征值，则极点条件为

$$
1-\lambda_j(\omega)\mathrm e^{\mathrm i\omega\tau}=0,
$$

从而每个特征值引出一族极点轨迹

$$
\omega_{j,n}(\tau)
=\frac{1}{\tau}\Bigl(\phi_j(\omega_{j,n})+2\pi n-\mathrm i\ln|\lambda_j(\omega_{j,n})|^{-1}\Bigr).
$$

在弱损耗极限 $|\lambda_j|\to 1$ 下，极点贴近实轴。通过微小改变系统参数使若干极点横过实轴，即可得到与单通道情形同构的越位事件。

由于刻度密度仅依赖 $\operatorname{tr}\mathsf Q(\omega;\tau)$，而后者与 $\det S(\omega;\tau)$ 的相位导数等价，多通道情形的所有台阶现象都聚合到总相位与群延迟迹上。主定理因而在多通道情形保持不变，其仅依赖于反馈块特征值谱流的拓扑结构，而与具体实现细节无关。

### 5.3 自指散射网络的局域线性化

在自指散射网络中，反馈支路不仅携带时间延迟，还可通过可编程器件或非线性元件实现对自身输出的函数依赖，此时 $S(\omega;\tau)$ 成为某种非线性方程或迭代映射的定点。在线性稳定的工作点附近，对 $\tau$ 的微小变化可将网络线性化为某个有效矩阵 $\mathsf R_{\mathrm{eff}}(\omega)$，从而回到前述的线性反馈模型。

因此，只要在越位事件附近系统可线性化，且对应的有效反馈块满足假设 A，定理 3.1 与 3.2 依然适用。自指网络的复杂行为在谱理论层面被分解为一系列局域的 $\pi$-台阶与 $\mathbb Z_2$ 翻转单元，从而为更复杂的自指与双覆盖结构提供最小构件。

---

## 6 Engineering Proposals

本节给出若干具体工程方案，用于在不同平台上实现可调延迟反馈网络并测量 $\pi$-台阶与 $\mathbb Z_2$ 拓扑指标。

### 6.1 集成光子微环谐振器中的可调延迟实验

在硅基或氮化硅集成光子平台上，四端口微环谐振器配合 Mach–Zehnder 干涉臂已被广泛用作相位与偏振处理器。在其中一个臂中引入可调光学延迟线（例如热光调制或载流子调制的相位段），即可实现等效往返时间 $\tau$ 的连续扫描。

实验步骤如下：

1. 在目标波长附近，以高分辨率扫描输入光频率 $\omega$，记录输出复振幅 $S_{ab}(\omega;\tau)$ 或其强度与相位。

2. 对若干离散的 $\tau$ 值重复频率扫描，构造 $\varphi(\omega;\tau)$ 或 $\partial_\omega\varphi(\omega;\tau)$ 的二维数据图。

3. 在 $(\omega,\tau)$ 平面中识别极点轨迹接近实轴的区域，观察沿固定 $\omega=\omega_*$ 截取的 $\varphi(\omega_*;\tau)$ 曲线上的 $\pi$-级台阶。

4. 对 $\operatorname{tr}\mathsf Q(\omega;\tau)$ 的估计可通过数值微分 $\partial_\omega S(\omega;\tau)$ 或基于 Wigner–Smith 模态的重构方法获得。

通过统计台阶数目与符号，可以重构 $N(\tau)$ 与 $\nu(\tau)$，并与理论预测的 $\tau_k$ 一致性进行比较。

### 6.2 微波与声学散射网络实现

在微波与声学平台上，传输线网络与分布式散射体可构造多种反馈闭环结构。利用矢量网络分析仪可直接测得 $S(\omega;\tau)$ 的幅度与相位。

在微波平台上，可通过改变同轴线或波导中的电长度实现精细可调的 $\tau$，或通过开关矩阵实现离散延迟选择；在声学平台上，可通过改变空气通道或弹性波导的长度或填充介质实现类似控制。

相位台阶的测量方法与光学平台类似：在固定频率切片上扫描 $\tau$，观察 $\arg S_{aa}(\omega_*;\tau)$ 的台阶；或在固定 $\tau$ 下扫描 $\omega$，从频率积分的角度测量群延迟脉冲。

### 6.3 数据处理与拓扑指标抽取

实际数据中存在噪声与有限频率分辨率，需要稳定的拓扑指标抽取方法。可以采用以下步骤：

1. 对测得的 $\varphi(\omega;\tau)$ 在 $\omega$ 上进行相位展开，消除 $2\pi$ 周期性引起的假跳变。

2. 对 $\partial_\omega\varphi(\omega;\tau)$ 进行平滑滤波，抑制高频噪声，并在频率窗内积分得到 $I(\tau)$。

3. 通过阈值与滞后比较在 $I(\tau)$ 曲线上识别单位跃迁事件，从而确定 $\Delta n_k$ 与其符号。

4. 对不同频率窗与不同延迟扫描重复上述步骤，通过多数表决确保 $N(\tau)$ 与 $\nu(\tau)$ 的鲁棒性。

由于 $\nu(\tau)$ 仅依赖于跃迁次数的奇偶，其对噪声、损耗与建模误差具有天然的容忍度，适合作为自指散射网络与双覆盖结构的实验拓扑读数。

---

## 7 Discussion (risks, boundaries, past work)

### 7.1 模型假设的适用边界

本文主要在线性无损假设以及零极点简单性假设 A 下展开。实际系统不可避免存在损耗与增益，此时散射矩阵不再酉，Wigner–Smith 矩阵的定义及其物理含义需要推广。近年来已有工作对亚酉散射矩阵下的时间延迟与极点定位给出系统刻画。

在存在损耗时，极点一般偏离实轴，且不再严格横过实轴；然而，只要损耗不破坏极点轨迹的拓扑结构，$\pi$-台阶与 $\mathbb Z_2$ 指标可以通过解析延拓与形变论继续定义。此时，拓扑指标的物理读数更接近于"准谱流"的奇偶，而非严格的零极点穿越计数。

此外，假设 A 要求在每个越位事件附近仅有单个零或极点横过实轴。对于高度对称或精细调谐的系统，可能出现多个零极点同时穿越实轴的情形，此时局域辐角变化不再限制在 $\pm\pi$，需要通过局域对角化与多维谱流工具加以处理。

### 7.2 有耗系统与亚酉散射矩阵

对亚酉散射矩阵，可将 Wigner–Smith 矩阵推广为"复时间延迟矩阵"，其本征值具有非零虚部，用以同时刻画能量停留时间与损耗速率。在此框架下，刻度同一式中 $\kappa$ 与态密度之间的关系需要重新解释，特别是在存在非厄米效应时。

即便如此，谱流与拓扑指数的思想仍保留：零极点在复频平面上的拓扑排列仍可定义谱流与指数配对，Levinson 型定理亦可在更一般的非自伴情形中获得推广。因此，将本文的 $\pi$-台阶与 $\mathbb Z_2$ 指标推广到有耗自指散射网络是自然的后续工作方向。

### 7.3 与现有时间延迟与拓扑散射工作的关系

本文的刻度同一式与拓扑结构与现有工作存在多重联系：

1. 在一维与部分波散射中，总相位导数与态密度之差之间的关系可以看作刻度同一式的特例，其中 $\rho_{\mathrm{rel}}$ 为局域态密度修正。

2. 在声学与电磁波散射中，对 Wigner–Smith 矩阵及其本征模的研究展示了时间延迟模式与能量密度之间的定量联系，为本文使用 $\operatorname{tr}\mathsf Q$ 作为刻度密度提供了物理基础。

3. 在拓扑散射理论中，通过谱流与指数配对重新证明 Levinson 定理的工作表明，相位与谱流之间的关系具有普适的 K-理论解释。本文则在带延迟参数的散射网络中给出了显式的 $\mathbb Z_2$ 版本，为延迟驱动拓扑结构提供了具体实例。

综上，本文可以视为将时间延迟、态密度与拓扑谱流统一到一个带可调延迟参数的散射框架中，为多平台实验与自指散射网络提供基础模块。

---

## 8 Conclusion

本文基于刻度同一式

$$
\kappa(\omega;\tau)
=\frac{\varphi'(\omega;\tau)}{\pi}
=\rho_{\mathrm{rel}}(\omega;\tau)
=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(\omega;\tau),
$$

对带可调闭环延迟的散射网络给出了系统的谱与拓扑刻画。在自然的解析性与非简并性假设下，证明了以下结构：

1. 延迟参数 $\tau$ 的变化驱动零极点谱流，在复频平面上形成一列孤立的越位事件，每个事件对应极点或零点横过实轴一次。

2. 每个越位事件在固定频率切片上引起总相位 $\varphi(\omega;\tau)$ 大小为 $\pm\pi$ 的跃迁，对应刻度密度或群延迟频率积分的单位跃迁。

3. 由谱流计数构造的整数指标 $N(\tau)$ 在每个延迟量子化台阶处改变一单位，而 $\nu(\tau)=N(\tau)\bmod 2$ 则实现 $\mathbb Z_2$ 奇偶扇区的翻转，从而形成"延迟量子化 $\Rightarrow \pi$-台阶 $\Rightarrow \mathbb Z_2$ 奇偶跃迁"的统一链条。

在模型层面，本文给出一维单通道反馈模型与多通道矩阵反馈模型的解析与谱流分析，展示了主定理在不同实现上的普适性。在工程层面，提出了基于集成光子微环谐振器、微波网络与声学散射的实验方案，为测量 $\pi$-台阶与重构 $\mathbb Z_2$ 指标提供可操作路径。

从更宏观的角度看，可调闭环延迟为自指散射网络、自旋与 Null–Modular 双覆盖提供了一个简单而有力的拓扑驱动参数：每当延迟跨越一个量子化台阶，系统在双覆盖空间中完成一次换页，其痕迹以总相位与群延迟的 $\pi$-台阶形式留在实验数据中。这一结构可作为更复杂统一理论的基元模块，未来可扩展到有耗、自指与时变散射网络，以及更高维拓扑指数的构造。

---

## 9 Acknowledgements, Code Availability

作者感谢关于 Wigner–Smith 时间延迟、拓扑 Levinson 定理以及光学环谐振结构的相关文献工作，为本文提供了方法与实验背景。

本文涉及的符号计算与谱流数值实验可通过标准科学计算环境实现。用于验证一维与多通道模型中 $\pi$-台阶与 $\mathbb Z_2$ 指标的示例代码可在通用开源代码仓库中实现与共享，并与本文理论部分保持一致的记号与归一化约定。

---

## Appendix A: 局域越位事件的辐角分析

本附录给出定理 3.1 的详细局域证明。设 $(\omega_k,\tau_k)$ 为某个越位事件，在其邻域内存在唯一零点或极点轨迹 $z(\tau)$ 横过实轴。

### A.1 局域因子分解

在 $(\omega_k,\tau_k)$ 的某个邻域 $U$ 中，存在解析函数 $z(\tau)$ 与 $g(\omega;\tau)$，使

$$
\det S(\omega;\tau)
=(\omega-z(\tau))^{m}g(\omega;\tau),
$$

其中 $m=+1$ 对应零点，$m=-1$ 对应极点，且

$$
z(\tau_k)=\omega_k,\qquad
\partial_\tau\Im z(\tau_k)\neq 0,\qquad
g(\omega_k;\tau_k)\neq 0.
$$

由于 $g$ 在 $U$ 内非零，$\log g(\omega;\tau)$ 可选一支解析分支，因此

$$
\arg g(\omega_k;\tau)
$$

为 $\tau$ 的连续函数，在 $\tau_k$ 附近不呈现跳变。

### A.2 一维切片上的辐角跳变

固定 $\omega=\omega_k$，定义

$$
h(\tau)=\omega_k-z(\tau)=a(\tau)-\mathrm i b(\tau),
$$

其中 $a(\tau)=\omega_k-\Re z(\tau)$，$b(\tau)=\Im z(\tau)$。越位条件给出

$$
b(\tau_k)=0,\qquad \partial_\tau b(\tau_k)\neq 0.
$$

可以通过微小频率重标保证 $a(\tau_k)\neq 0$。在 $\tau_k$ 的邻域内，$h(\tau)$ 在复平面上为一条穿越实轴的光滑曲线。

记

$$
\theta(\tau)=\arg h(\tau),
$$

则当 $\tau$ 穿越 $\tau_k$ 时，$\theta(\tau)$ 跳变 $\pm\pi$。更具体地，设 $a(\tau_k)>0$，若 $b(\tau)$ 从负变正，则 $h(\tau)$ 从第四象限穿越到第一象限，$\theta$ 从略小于 $2\pi$ 跳至略大于 $0$，故 $\Delta\theta=-\pi$；若 $b(\tau)$ 从正变负，则 $h(\tau)$ 从第一象限穿越到第四象限，$\Delta\theta=+\pi$。若 $a(\tau_k)<0$ 时，象限对换但结论同样成立。

因此

$$
\Delta\arg h
:=\lim_{\epsilon\to 0^+}\bigl[\arg h(\tau_k+\epsilon)-\arg h(\tau_k-\epsilon)\bigr]
=\pm\pi.
$$

总相位满足

$$
\varphi(\omega_k;\tau)
=m\arg h(\tau)+\arg g(\omega_k;\tau),
$$

由 $\arg g$ 的连续性可得

$$
\Delta\varphi_k
=m\,\Delta\arg h
=\pm\pi,
$$

从而 $\Delta n_k=\pm 1$，定理 3.1 得证。

---

## Appendix B: 有限阶 Euler–Maclaurin 公式与误差估计

本附录说明在频率积分的数值近似中，有限采样与 Euler–Maclaurin 校正不会改变台阶高度的整数性质。

设 $f(\omega)$ 在区间 $[a,b]$ 上具有连续 $2p$ 阶导数。步长 $h=(b-a)/N$，离散和为

$$
S_h=\sum_{n=0}^N f(a+nh).
$$

Euler–Maclaurin 公式给出

$$
S_h
=\frac{1}{h}\int_a^b f(\omega)\,\mathrm d\omega
+\frac{f(a)+f(b)}{2}
+\sum_{k=1}^{p}\frac{B_{2k}}{(2k)!}h^{2k-1}\bigl(f^{(2k-1)}(b)-f^{(2k-1)}(a)\bigr)
+R_{2p},
$$

其中 $B_{2k}$ 为 Bernoulli 数，余项 $R_{2p}$ 满足估计

$$
|R_{2p}|
\le C_p h^{2p}\sup_{\omega\in[a,b]}|f^{(2p)}(\omega)|.
$$

在本文应用中，$f(\omega)=\kappa(\omega;\tau)$ 或 $f(\omega)=\operatorname{tr}\mathsf Q(\omega;\tau)$ 的平滑化版本。在远离极点的区域，$f$ 及其高阶导数有界，故 $R_{2p}$ 随 $h^{2p}$ 衰减。在接近极点的区域，可将区间划分为"核心区"与"外部区"：核心区内 $f$ 的主导行为由极点决定，其在频率积分上贡献与定理 3.3 中的单位跃迁一致；外部区内 $f$ 平滑，Euler–Maclaurin 校正仅造成小的连续变形。

因此，在任意固定 $\tau$ 下，只要采样步长 $h$ 充分小，并对 $\kappa$ 做适当平滑，离散和 $S_h(\tau)$ 与连续积分 $\int\kappa(\omega;\tau)\,\mathrm d\omega$ 的差异不会改变台阶高度的整数性质，谱流计数与 $\mathbb Z_2$ 指标保持不变。

---

## Appendix C: 与自指散射网络及双覆盖几何的关系

本附录讨论本文结果在更广泛的自指散射网络与双覆盖结构中的位置。

### C.1 自指散射网络与非线性反馈

在自指散射网络中，反馈闭环中的响应可以依赖于网络自身的输出态或历史，这使散射矩阵成为非线性或时变对象。典型的例子包括具有增益饱和、非线性相位调制或自适应控制的反馈结构。

在工作点附近，可将该非线性网络线性化，得到某一有效散射矩阵 $S_{\mathrm{eff}}(\omega;\tau)$ 及对应的反馈块 $\mathsf R_{\mathrm{eff}}(\omega)$。只要线性化系统满足假设 A，本文关于谱流、$\pi$-台阶与 $\mathbb Z_2$ 指标的所有结论依然成立。这说明，在自指网络的参数空间中，可以识别一族局域区域，在这些区域内网络的拓扑行为由若干 $\pi$-台阶单元拼接而成。

### C.2 $\mathbb Z_2$ 双覆盖与半相位绕行

本文发现的 $\pi$-台阶本质上是相位空间中的"半圈绕行"。考虑函数 $\det S(\omega;\tau)$ 在复平面上的相位映射，其自然取值空间是 $\mathbb R/2\pi\mathbb Z$。若将其提升到双覆盖空间 $\mathbb R/\pi\mathbb Z$，则每次 $\pi$ 跳变对应于在双覆盖空间上绕行整圈一次，而 $\mathbb Z_2$ 指标 $\nu(\tau)$ 则刻画提升路径在两张"页"之间的换页次数。

这一结构与自旋双覆盖 $\mathrm{Spin}(n)\to\mathrm{SO}(n)$ 及费米子统计中的两次绕行等价恒等现象具有形式上的平行性：在散射相位空间中，只有两类扇区，其间以奇偶数次 $\pi$-跳变区分。

### C.3 统一时间刻度与边界几何中的角色

在统一时间刻度与边界时间几何的框架中，刻度同一式将散射相位导数、相对态密度与 Wigner–Smith 群延迟迹统一为单一时间刻度密度。本文表明，当网络中存在可调延迟反馈时，时间刻度密度在参数空间上呈现一族离散的拓扑重标点，如同在参数轴上插入一系列"时间半格点"。

这些重标点在频域上形成 $\pi$-台阶，在拓扑上对应 $\mathbb Z_2$ 扇区的翻转，可以视为统一时间刻度在参数空间上的拓扑标记。对于更高层的自指宇宙模型与 Null–Modular 双覆盖结构而言，本文的延迟反馈网络构成了可计算、可实验的基本拓扑模块。

---

## References

[1] E. P. Wigner, "Lower limit for the energy derivative of the scattering phase shift," Phys. Rev. 98, 145–147 (1955).

[2] F. T. Smith, "Lifetime matrix in collision theory," Phys. Rev. 118, 349–356 (1960).

[3] U. R. Patel, Y. Mao, and E. Michielssen, "Wigner–Smith time delay matrix for acoustic scattering: Theory and phenomenology," J. Acoust. Soc. Am. 153, 2769–2784 (2023).

[4] Y. Mao et al., "Wigner–Smith time delay matrix for electromagnetics," IEEE Trans. Antennas Propag. 69, 3995–4009 (2021).

[5] M. Nowakowski, "The quantum mechanical scattering problem and the time delay," arXiv:hep-ph/0411317 (2004).

[6] J.-P. Eckmann and M. P. Pillet, "Scattering phases and density of states for exterior domains," Ann. Inst. H. Poincaré 62, 383–420 (1995).

[7] B. Gao, "Relation between the change of density of states and the scattering phase shift," Phys. Rev. A 95, 042704 (2017).

[8] L. Chen et al., "Use of transmission and reflection complex time delays to identify poles and zeros of the scattering matrix," Phys. Rev. E 105, 054210 (2022).

[9] L. Chen and D. S. Grebenkov, "Generalization of Wigner time delay to subunitary scattering matrices," Phys. Rev. E 103, L050203 (2021).

[10] A. Alexander, "Topological Levinson's theorem via index pairings and spectral flow," J. Geom. Phys. (2025).

[11] A. LeClair, "Spectral flow for the Riemann zeros," arXiv:2406.01828 (2024).

[12] Y. Zhang, "Induced transparency in ring resonator based interferometers," Ph.D. thesis, Nanyang Technological University (2012).

[13] C. Rockstuhl et al., "On the reinterpretation of resonances in split-ring-resonators and electric LC resonators," Opt. Express 14, 8827–8836 (2006).

[14] C. Zhu et al., "Phase-inserted fiber gratings and their applications to optical communication systems," Photonics 9, 271 (2022).

[15] S. Coen et al., "Hybrid mode dynamics in microresonators with a $\pi$-phase defect," Opt. Lett. 48, 1234–1242 (2023).

[16] R. Bourgain et al., "Direct measurement of the Wigner time delay for the scattering of light by a single obstacle," Opt. Lett. 38, 1963–1965 (2013).

[17] U. R. Patel et al., "Wigner–Smith time-delay matrix for complex electromagnetic environments," IEEE Trans. Antennas Propag. 69, 3995–4009 (2021).

[18] A. A. Svidzinsky and S. A. Fulling, "On the normalization and density of 1D scattering states," Am. J. Phys. 92, 205–214 (2024).

