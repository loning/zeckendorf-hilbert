# 宇宙的数学结构（UMS）

**—— 有限窗口协变的"散射—信息—几何"统一理论（正式学术论文，含完整证明）**

**作者**：Auric（S-series / EBOC 体系）
**版本**：v2.5（由 v2.4 递增）

---

## 摘要

本文以**相位—密度刻度**、**窗口化读数**与**信息几何**为三根主轴，把"态—测量—概率—指针—散射相位—群延迟—采样/帧—误差学—通道容量"焊接为一个可验证的**范畴化**统一理论（UMS）。核心统一式采用**同一刻度的三种密度表达**：

$$
\boxed{\, d\mu_{\varphi}(E)\ :=\ \frac{\varphi'(E)}{\pi}\,dE\ =\ \frac{1}{2\pi}\,\operatorname{tr}\mathsf Q(E)\,dE\ =\ \rho_{\mathrm{rel}}(E)\,dE\ }\ \ \text{（a.c. 谱上 a.e.）}\,
$$

（上式在 a.c. 谱上 a.e. 成立，$\operatorname{Arg}\det S$ 取**连续分支**；跨阈值/原子点以 $\Delta\mu_\varphi=\mu_\varphi(\{E_*\})$ **跳跃拼接**，对应谱移函数 $\xi(E)$ 的跳跃与束缚态/阈值多重度一致——在 Levinson 型定理语境下，谱移 $\xi$ 的跳跃量等于该能量处的束缚态/半束缚态个数。）

其中 $\mathsf Q(E)=-i\,S^\dagger(E)\,S'(E)$ 为 Wigner–Smith 群延迟矩阵，$\rho_{\mathrm{rel}}(E)=-\xi'(E)$ 为 Birman–Kreĭn 谱移密度（采用 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 的约定）。在多通道情形，总相位定义为 $\varphi(E):=\frac{1}{2}\operatorname{Arg}\det S(E)$（取连续分支）。

**规范化说明（统一）**：本文将 $\mu_\varphi$ 视为**局部有限的有符号 Radon 测度**，作 Lebesgue 分解 $\mu_\varphi=\mu_\varphi^{\mathrm{ac}}+\mu_\varphi^{\mathrm{s}}+\mu_\varphi^{\mathrm{pp}}$，并作 Jordan 分解 $\mu_\varphi=\mu_+-\mu_-$（$\mu_\pm\ge0$）。当 $\mu_\varphi$ 为非负 Borel 测度且满足 Herglotz 表示的标准增长/可积条件（例如 $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$，超出部分吸收到 $a+bz$ 项）时，存在 Herglotz 函数 $m$ 使 $\pi^{-1}\Im m(E+i0)=\rho_{\mathrm{rel}}(E)$（a.e.），并在恰当规范化下（消去 $a+bz$ 自由度）由**trace-normed** DBK 规范系统实现**全局**表示；若 $\mu_\varphi$ 含负部，仅能在 $\rho_{\mathrm{rel}}>0$ 的 a.c. 分段建立**局部**表示。其**绝对连续部分**满足

$$
\boxed{\ d\mu_\varphi^{\mathrm{ac}}(E)=\rho_{\mathrm{rel}}(E)\,dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE=\frac{\varphi'(E)}{\pi}\,dE\ \ \text{(a.e.)}\ }\,.
$$

若存在奇异/原子部分，则分别记为 $\mu_\varphi^{\mathrm{s}}, \mu_\varphi^{\mathrm{pp}}$，并在跨阈值/原子能级时通过 $\Delta\mu_\varphi=\mu_\varphi(\{E_*\})$ 体现跳跃。

**说明**：在一般散射对下，$\rho_{\mathrm{rel}}(E)$ 为与自由系之**相对**态密度，可能**变号**（负群延迟与谱移密度变号在多类波动散射中可观测，与脉冲整形/共振背景有关，见电磁与非厄米散射体系中的负 Wigner–Smith 延迟与复延迟实测/数值报道），故 $d\mu_{\varphi}$ **一般为符号测度（signed measure）**。本文的主要定理（定理 3.1、3.2）要求 $\mu_\varphi$ **全体无负部**时给出**全局** DBK 表示，符号测度情形仅能在 $\rho_{\mathrm{rel}}>0$ 的 a.c. 分段上得到**局部**表示。

**参考根据**：Herglotz 表示与 trace-normed 规范系统的一一对应建立在非负测度上；对任意 Herglotz 函数存在唯一（至自然等价）trace-normed 规范系统。

该式把散射相位导数、相对谱密度与群延迟统一到同一刻度；测量读数以**窗—核**谱积分表示，并以 **Nyquist–Poisson–Euler–Maclaurin（EM）** 三分解给出**有限阶、非渐近**误差闭合；概率唯一性由 Naimark 扩张与 Gleason 定理保障；采样/帧门槛由 Landau 必要密度、Wexler–Raz 双正交与 Balian–Low 不可能性刻画；开放系统的信息单调与容量上界由 GKSL 主方程、量子相对熵在**正迹保持**映射下的单调（DPI）以及 HSW 定理控制。

**关键词**：散射相位；Wigner–Smith 群延迟；Birman–Kreĭn；de Branges / Herglotz；Naimark 扩张；Gleason；Landau 密度；Wexler–Raz；Balian–Low；Euler–Maclaurin；Poisson；GKSL；DPI；HSW。

---

## 0. 预备与号记

**0.1 散射与群延迟。** 设 $S(E)\in U(N)$ 在 a.c. 谱上具**弱导数**或**有界变差**，Wigner–Smith 群延迟矩阵定义为 $\mathsf Q(E)=-i\,S^\dagger(E)\,S'(E)$，其中 $S'(E)$ 按**分布导数**理解。对酉 $S$ 有 $S^\dagger S'=(S^{-1}S')$ 反厄米，故迹纯虚。由 Jacobi 公式 $\tfrac{d}{dE}\log\det S=\operatorname{tr}(S^{-1}S')$，且 $S^{-1}=S^\dagger$（酉），得 $\tfrac{d}{dE}\operatorname{Arg}\det S=\Im\,\operatorname{tr}(S^\dagger S')$；于是

$$
\operatorname{tr}\mathsf Q(E)=-i\,\operatorname{tr}\!\big(S^\dagger S'(E)\big)=\Im\,\operatorname{tr}\!\big(S^\dagger S'(E)\big)=\frac{d}{dE}\operatorname{Arg}\det S(E)\ \ \text{（取连续分支，a.c. 谱上 a.e. 成立）},
$$

单通道 $S(E)=e^{2i\varphi(E)}$ 时 $\operatorname{tr}\mathsf Q(E)=2\,\varphi'(E)$。跨阈值/原子点时不要求处处可微，而是通过跳跃 $\Delta\mu_\varphi$ 拼接。

**记号约定**：下文中"a.c."表绝对连续谱区；"a.e."指相对于 Lebesgue 测度的几乎处处。$\mathsf Q$ 的定义域为 a.c. 谱区的 a.e. 点集，在该区间外（阈值、原子点）用谱测度的跳跃部分 $\mu_\varphi^{\mathrm{pp}}$ 描述。

**多通道刻度化相位**：令 $\varphi(E):=\frac{1}{2}\operatorname{Arg}\det S(E)$（选取连续分支，a.c. 谱上 a.e. 可导），则

$$
d\mu_\varphi(E)=\frac{\varphi'(E)}{\pi}\,dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE.
$$

单通道退化为 $S=e^{2i\varphi}$。$\operatorname{Arg}\det S$ 取局部连续分支，仅在 a.c. 谱上 a.e. 可微；跨越阈值与原子点时以跳跃补偿。

**单位说明**：本文取 $\mathsf Q(E)=-i\,S^\dagger(E)S'(E)$，其量纲为**能量$^{-1}$**（$S'(E)$ 对能量求导产生 $1/\text{能量}$ 的量纲）；在**酉散射**情形，物理时间延迟取**Wigner–Smith 延迟**：$\tau=\hbar\,\mathrm{eig}(\mathsf Q)$；**非酉/耗散**时 $\mathsf Q$ 一般非自伴（特征值可为复数），$\tau$ 的定义需按 §6.2 指定（例如取 $\Re\,\mathrm{eig}(\mathsf Q)$ 作为驻留相关量），本文不将二者混同。在孤立 Breit–Wigner 共振处，由 $\tau(E)=2\hbar\,\delta'(E)$ 与 $\delta'(E_0)=2/\Gamma$ 得 $\tau_{\max}(E_0)=4\hbar/\Gamma$，而寿命 $\tau_{\text{life}}=\hbar/\Gamma$，二者**相差因子 4**。**宽度记号说明**：本文统一以极点 $E_0-i\Gamma/2$ 计宽度；若参考采用 $E_0-i\Gamma$ 的文献，请将本文 $\tau$ 数值整体乘以 $1/2$ 对齐（峰值由 $4\hbar/\Gamma$ 变为 $2\hbar/\Gamma$）。该约定与电磁及量子散射文献一致（与 §6.2 的非厄米扩展照应）。

**0.2 谱移与 Birman–Kreĭn。** 采用 BK 的**负号约定**：$\ \det S(E)=e^{-2\pi i\,\xi(E)}$。

**行列式约定（BK/Fredholm）**：本文中的 $\det S(E)$ 指 **Birman–Kreĭn 意义下的 Fredholm 行列式** $\det_{\mathrm F}S(E)$。在 $(H-z)^{-1}-(H_0-z)^{-1}\in\mathfrak S_1$（等价地，a.e. $E$ 上 $S(E)-I\in\mathfrak S_1$）的前提下，$\det_{\mathrm F}S(E)$ 良定义，$\operatorname{Arg}\det_{\mathrm F}S(E)$ 可选取**连续分支**并在 a.c. 谱上 **a.e. 可导**，从而

$$
\frac{d}{dE}\operatorname{Arg}\det_{\mathrm F}S(E)=-2\pi\,\xi'(E),\qquad \rho_{\mathrm{rel}}(E):=-\xi'(E),
$$

因此 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$（a.e.）。负群延迟与谱移密度变号在多类波动散射中可观测，与脉冲整形/共振背景有关（见电磁与非厄米散射体系中的负 Wigner–Smith 延迟与复延迟实测/数值报道，含亚酉散射近作）。

**散射对前提（BK 公式适用性）**：上述 BK 恒等式 $\det S(E)=e^{-2\pi i\xi(E)}$ 及其导出关系 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}=-\xi'$ 在**自伴散射对** $(H,H_0)$ 下成立，其中 $H_0$ 为自由哈密顿量，$H=H_0+V$ 为全哈密顿量，并假设 $(H-z)^{-1}-(H_0-z)^{-1}$ 属 **trace class**（或等价的可加条件，如 $V(H_0-z)^{-1}$ 属 trace class），从而保证波算子 $W_\pm=\mathrm{s-lim}_{t\to\pm\infty}e^{iHt}e^{-iH_0 t}$ 存在、完备，散射算子 $S=W_+^\dagger W_-$ 酉，且谱移函数 $\xi$ 定义良好；非厄米/耗散情形需在最大耗散扩张或自伴扩张框架下单列（参见 Pushnitski, A., arXiv:1006.0639；Behrndt–Malamud–Neidhardt, arXiv:0712.3120）。

**0.3 DBK 规范系统与 Herglotz 词典。** 一维 de Branges–Kreĭn 规范系统 $JY'(t,z)=zH(t)Y(t,z)$ 的 Weyl–Titchmarsh 函数 $m:\mathbb C^+\to\mathbb C^+$ 为 Herglotz 函数，其标准表示 $m(z)=a+bz+\int\!\big(\frac{1}{t-z}-\frac{t}{1+t^2}\big)\,d\nu(t)$ 中 $d\nu\ge0$ 为非负 Borel 测度且满足 $\int (1+t^2)^{-1}\,d\nu(t)<\infty$（超出部分吸收到 $a+bz$ 项），边界虚部给出绝对连续谱密度 $\rho_{\mathrm{ac}}(E)=\pi^{-1}\Im m(E+i0)=\pi^{-1}\frac{d\nu^{\mathrm{ac}}}{dE}$（a.e.）；此处 $\rho_{\mathrm{ac}}$ 指**被考察算子的绝对连续谱部分**的谱密度（此 $\rho_{\mathrm{ac}}$ 非本文的相对谱密度 $\rho_{\mathrm{rel}}$），若存在奇异/原子部分，其贡献体现在相应的谱测度分解中。在恰当规范化下（消去 $a+bz$ 自由度），**trace-normed** 规范系统与 Herglotz 函数及 de Branges 空间存在**一一对应且唯一**（至自然等价）（参见 Remling, C., Hur, I., arXiv:1501.01268；de Branges, L., Hilbert Spaces of Entire Functions）。

**符号测度情形的分段拼接**：当 $\mu_\varphi$ 含负部（即 $\rho_{\mathrm{rel}}$ 变号）时，仅能在 $\rho_{\mathrm{rel}}>0$ 的各 a.c. 分段 $I_j$ 上分别构造 trace-normed 规范系统 $(H_j,J_j)$ 与对应 Herglotz 函数 $m_j$，使 $\pi^{-1}\Im m_j(E+i0)=\rho_{\mathrm{rel}}(E)$ a.e. 在 $I_j$ 上成立；各分段按谱测度 $\mu_\varphi$ 的 Lebesgue 分解与 Jordan 分解逐段拼接，唯一性与一致性在**每个分段内**由 trace-normed 规范保证，但**全局不存在单一规范系统**的 Herglotz 表示。

**0.4 采样、帧与门槛。** Paley–Wiener 类的稳定采样/插值服从 Landau 必要密度（Landau 1967，见参考文献 [4]）；Gabor 系的对偶窗满足 Wexler–Raz 双正交（Daubechies–Landau–Landau 1995，见参考文献 [5]）；临界密度下满足 Balian–Low 不可能性（见参考文献 [6]）。

**0.5 测量与概率唯一性。** 任一 POVM 可由更大空间中的 PVM 压缩得到（Naimark 扩张）；当 $\dim\mathcal H\ge 3$ 时，满足可加性的概率测度必为 $\operatorname{Tr}(\rho\,\cdot)$（Gleason 定理）。二能级体系可用 Busch–Gleason 的 POVM 版补足，但本文不需涉及。

**0.6 开放系统与信息界。** 马尔可夫开放演化由 GKSL（Lindblad）主方程描述；量子相对熵在**正迹保持**映射下单调不增（DPI）；量子信道的无助理经典容量由 HSW 正则化公式给出。

**0.7 Nyquist–Poisson–EM（有限阶非渐近误差学）。** 带限信号在**理想采样与理想重构滤波**前提下，当采样率 $f_s\ge 2B$ 时别名项消失；工程稳健通常取 $f_s>2B$。Euler–Maclaurin（EM）用于离散—连续换序时，取 $m\in\mathbb N$ 使被积/被和函数 $F\in C^{2m}$ 且 $F^{(2m)}$ 有界或具有限总变差，则余项具**显式积分上界**。EM 余项采用 Archive of Formal Proofs (AFP-Isabelle) 条目 **The Euler–MacLaurin Formula** 的形式化上界（Eberl, M., 见参考文献 [11]），在实现中显式指明所取阶数 $m$ 与被积/被和函数的正则性（$C^{2m}$ 或有限总变差）以复现上界。

**选择 $m$ 的经验指引**（实现可操作性）：
- $m=1$（2 阶校正）：被积函数 $F\in C^2$，适用于分段线性窗或低光滑度核；
- $m=2$（4 阶校正）：$F\in C^4$，适用于多数光滑窗函数（如高斯窗、Hann 窗）与谱积分；
- $m=3$（6 阶校正）：$F\in C^6$，适用于高精度要求或需控制尾部振荡的情形。
实践中先验证 $F^{(2m)}$ 的 $L^\infty$ 范数或总变差有限，再将其代入 AFP-Isabelle 的余项界公式得可执行上界。

---

## 1. 公理体系（Axioms）

**A1（双表象与协变）。** $\mathcal H(E)$（能量表象）与 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$（相位—尺度表象，其中 $a>0$ 由所用 Mellin 权确定）等距等价；离散—连续换序使用**有限阶** EM，按 0.7 的光滑与（有界或有限变差）前提控制余项。此"等距等价"系指在所用 DBK 规范系统/Weyl–Mellin 变换**已构造到位**时的单位算子实现；读者不应将其理解为任意系统之间的无条件同构。**实施前提**：当 $\mu_\varphi$ 为非负 Borel 测度且满足 Herglotz 条件（标准增长/可积性，例如 $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$）时，存在 Herglotz 函数 $m$ 使得在恰当规范化下（消去 $a+bz$ 自由度）由**trace-normed** DBK 规范系统实现**全局** DBK 表示与等距等价；此时 $\mu_\varphi^{\mathrm{ac}}$ 满足 $\rho_{\mathrm{rel}}=\pi^{-1}\Im m$（a.e.）。若 $\mu_\varphi$ 含负部，则仅在 $\rho_{\mathrm{rel}}>0$ 的 a.c. 分段逐段实现等距等价，**不**保证单一规范系统的全局实现。（**括注**：$\rho_{\mathrm{rel}}=-\xi'$ 为相对态密度，**一般可变号**；故 $\mu_\varphi$ 常为**符号测度**，仅其非负情形可由 Herglotz–DBK **全局**表示，参见定理 3.1。）

**A2（有限窗口读数）。** 任一次"可实现读数"写作窗—核谱积分 $K_{w,h}=\int h(E)\,w_R(E)\,d\Pi_A(E)$。为确保 $K_{w,h}$ 在**所有密度算子** $\rho$ 上的期望值 $\operatorname{Tr}(\rho K_{w,h})$ 良定义并一致有界，本文**限定** $g(E):=h(E)w_R(E)\in L^\infty(\mathbb R;\mathbb R)$ 且为 Borel 可测，据此 $K_{w,h}$ 为**有界自伴**算子；误差以"别名（Poisson）+ 伯努利层（EM）+ 截断"三项**非渐近闭合**（理想采样下带限且 $f_s\ge 2B$ 时别名为 0）。一次"读数"的数值为 $\operatorname{Tr}(\rho K_{w,h})$。**记号约定**：下文一律用 $\Pi_A$ 表示投影值谱测度（避免与能量变量 $E$ 产生符号歧义）。

**A3（概率—信息一致性）。** 对 PVM $\{P_j\}$ 与态 $\rho$，线性约束 $p_j=\operatorname{Tr}(\rho P_j)$ 使可行集为单点 $\{p^\star\}$，任意严格凸 Bregman/KL 的 I-projection 唯一取于 $p^\star$；POVM 情形先作 Naimark 扩张到 PVM 再回推。Gleason（$\dim\mathcal H\ge3$）确保此概率形式的唯一性。**维度条件**：二能级体系（$\dim\mathcal H=2$）需用 Busch–Gleason 的 POVM 版补足（Busch, P., Phys. Rev. Lett., 2003）。

**A4（指针子空间 / 光谱极小的下确界版）**。

**（记号约定）** 对任意 $r\in\mathbb N$：
1. $U:\mathbb C^r\to\mathcal H$ 表示**等距嵌入**（柱向量 $(u_1,\dots,u_r)$ 正交归一），故 $U^\dagger U=I_r$，且 $\mathrm{tr}(U^\dagger K_{w,h}U)=\sum_{j=1}^r\langle u_j,K_{w,h}u_j\rangle$。
2. $P_M$ 为 $\mathcal H$ 上到 $r$ 维子空间 $M$ 的**正交投影**，并有 $\mathrm{tr}_M(P_M K_{w,h}P_M)=\mathrm{tr}(U^\dagger K_{w,h}U)$（$U$ 的像即 $M$）。

于是以下"压缩迹/变分式"完全等价。

令 $K_{w,h}=\int g(E)\,d\Pi_A(E)$ 为**有界自伴**。对任意 $r\in\mathbb N$，记谱投影 $P_t:=\mathbf{1}_{(-\infty,t]}(K_{w,h})$。定义
$$
m_r:=\inf_{U^\dagger U=I_r}\mathrm{tr}\!\big(U^\dagger K_{w,h}U\big).
$$
（**迹约定**：此处 $\mathrm{tr}(P_M K_{w,h}P_M)$ 为 $M$ 上的**有限维迹** $\mathrm{tr}_M$，与 $\mathrm{tr}(U^\dagger K_{w,h}U)$ 等价，其中 $U:\mathbb C^r\to\mathcal H$ 为 $M$ 的等距嵌入。）
则对任意 $t\in\mathbb R$ 与任意 $r$ 维子空间 $M\subset\mathrm{Ran}\,P_t$ 有 $\mathrm{tr}_M(P_M K_{w,h}P_M)\le r\,t$，且
$$
m_r=\inf_{t\in\mathbb R}\ \inf_{\substack{M\subset\mathrm{Ran}\,P_t \\ \dim M=r}}\mathrm{tr}_M(P_M K_{w,h}P_M),
$$
**一般仅取得下确界**（不保证取到）。**若** $K_{w,h}$ 为**紧**或在**有限维截断**上（**或**其底谱阈值 $t_0:=\inf\sigma(K_{w,h})$ 处存在至少 $r$ 个**本征值**，可为**嵌入**本征值，计重数），则该下确界**可达**，且极小子空间由**最小 $r$** 个本征值的本征向量张成。

**A5（相位—密度—延迟刻度）。** 采用 BK 约定，

$$
\boxed{\, \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}\ \ \text{(a.e.)}\ }\,.
$$

**前提**：见 §0.2『散射对前提（BK 公式适用性）』。

**A6（采样—帧门槛）。** 稳定采样满足 Landau 必要密度；多窗对偶由 Wexler–Raz 描述；临界密度触发 Balian–Low 不可能性。

**A7（通道—单调—容量）。** 演化受 GKSL 主方程；量子相对熵在**正迹保持（PTP）**映射下单调（DPI）；经典容量由 HSW 定理给出（需**完全正且迹保持（CPTP）**信道）。

---

## 2. UMS 的范畴化定义

**定义 2.1（对象）。**
$U=(\mathcal H,\ \mathcal C,\ \mathscr O,\ \mathbb W,\ \mathcal S,\ D)$，其中
(i) $\mathcal H$：由 $\mathcal H(E)/\mathcal H_a$ 纤维化的希尔伯特丛；
(ii) $\mathcal C$：闭/开放演化（含 GKSL 半群）；
(iii) $\mathscr O$：可观测与谱测度 $\Pi_A$；
(iv) $\mathbb W$：窗—核系统与 Nyquist–Poisson–EM 误差账本；
(v) $\mathcal S$：散射函子 $E\mapsto(S,\mathsf Q,\xi)$；
(vi) $D$：信息散度（KL/Bregman）与其诱导几何。

**定义 2.2（态与刻度）。** 纯态/混合态分别为向量/密度算子；定义**相位—密度刻度**

$$
d\mu_{\varphi}(E)\ :=\ \frac{\varphi'(E)}{\pi}\,dE\ =\ \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE\ =\ \rho_{\mathrm{rel}}(E)\,dE\quad\text{（一般为符号测度）}\,.
$$

（上式在 a.c. 谱上 a.e. 成立，$\operatorname{Arg}\det S$ 取**连续分支**；跨阈值/原子点以 $\Delta\mu_\varphi=\mu_\varphi(\{E_*\})$ **跳跃拼接**。）

**规范化说明（统一）**：本文将 $\mu_\varphi$ 视为**局部有限的有符号 Radon 测度**，作 Lebesgue 分解 $\mu_\varphi=\mu_\varphi^{\mathrm{ac}}+\mu_\varphi^{\mathrm{s}}+\mu_\varphi^{\mathrm{pp}}$，并作 Jordan 分解 $\mu_\varphi=\mu_+-\mu_-$（$\mu_\pm\ge0$）。当 $\mu_\varphi$ 为非负 Borel 测度且满足 Herglotz 表示的标准增长/可积条件（例如 $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$，超出部分吸收到 $a+bz$ 项）时，存在 Herglotz 函数 $m$ 使 $\pi^{-1}\Im m(E+i0)=\rho_{\mathrm{rel}}(E)$（a.e.），并在恰当规范化下（消去 $a+bz$ 自由度）由**trace-normed** DBK 规范系统实现**全局**表示；若 $\mu_\varphi$ 含负部，仅能在 $\rho_{\mathrm{rel}}>0$ 的 a.c. 分段建立**局部**表示。其**绝对连续部分**满足

$$
d\mu_\varphi^{\mathrm{ac}}(E)=\rho_{\mathrm{rel}}(E)\,dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE=\frac{\varphi'(E)}{\pi}\,dE\ \ \text{(a.e.)}\,.
$$

若存在奇异/原子部分，则分别记为 $\mu_\varphi^{\mathrm{s}}, \mu_\varphi^{\mathrm{pp}}$，并在跨阈值/原子能级时通过 $\Delta\mu_\varphi=\mu_\varphi(\{E_*\})$ 体现跳跃。

**定义 2.3（态射）。** 对象间态射为保持 (i)–(vi) 的结构映射；态间态射默认取 **CPTP（量子信道）**；仅当陈述 DPI 时，可放宽为**正迹保持（PTP）**映射（DPI 在此范围内仍成立，但 HSW 容量定理需要 CPTP）。

---

## 3. 主定理与完整证明

### 定理 3.1（UMS 表示定理，非负测度情形）

**命题。** 在 $\mu_\varphi$ **全体无负部**（等价地，其 Lebesgue 分解的每一部分均非负）的情形，任何满足 A1–A7 的有限窗口测量理论与某个 DBK 规范系统（及其 Herglotz 函数 $m$）所确定的 $U\in\mathbf{UMS}$ 等价；若 $\mu_\varphi$ 为符号测度，则仅能在 $\rho_{\mathrm{rel}}>0$ 的 a.c. 分段上得到**局部**表示，**不能**保证单一 DBK 系统的**全局**表示。在此等价下

$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}\quad\text{(a.e.)},
$$

测量侧 $K_{w,h}$ 与信息侧（I-projection）满足 A2–A3；帧与门槛满足 A6；等价唯一至相位重参数化与酉变换。

**证明。**
(1) **散射—相位—密度统一。** 由 0.1 得 $\operatorname{tr}\mathsf Q=\tfrac{d}{dE}\operatorname{Arg}\det S$；由 0.2 得 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$；单通道再与 $\operatorname{tr}\mathsf Q=2\varphi'$ 合并，得统一刻度。
(2) **Herglotz—规范系统—de Branges。** 当 $\mu_{\varphi}$ 为非负 Borel 测度且满足 Herglotz 表示的标准增长/可积条件（例如 $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$，超出部分吸收到 $a+bz$ 项）时，存在 Herglotz $m$ 使 $\pi^{-1}\Im m=\rho_{\mathrm{rel}}$（a.e.），并在恰当规范化下（消去 $a+bz$ 自由度）由 de Branges–Kreĭn 规范系统确定该刻度；de Branges 理论在 Herglotz $m$、trace-normed 规范系统与 de Branges 空间间建立等价。**一般情形**下 $d\mu_{\varphi}$ 为符号测度，可在 $\rho_{\mathrm{rel}}>0$ 的 a.c. 分段上分别构造并按相应分片拼接。**参考根据**：DBK 逆谱理论对满足 Herglotz 条件的非负测度给出全局（trace-normed）表述与唯一性。
(3) **窗口化读数与有限阶闭合。** 在**闭集带限且理想滤波**前提下 $f_s\ge2B$ 可使基带别名为 0；工程稳健通常取 $f_s>2B$（见定理 4.1）；EM 在 0.7 假设下给出伯努利层与余项上界，故 A2 成立。
(4) **概率一致性。** POVM 由 Naimark 扩张为 PVM；Gleason 保证 Born 形式唯一；严格凸散度的 I-projection 在单点可行集上退化为 Born。
(5) **帧与门槛。** Landau 必要密度、Wexler–Raz 双正交与 Balian–Low 不可能性分别给出阈值、对偶与临界障碍。
综上得证。**若 $\mu_\varphi$ 含负部，以下结论按分段解释**（见 §0.3/A1）。∎

---

### 定理 3.2（刻度唯一性）

**命题。** （**在 $\mu_\varphi$ 全体无负部且满足 Herglotz 条件的情形**；所用 BK 约定为 $\det S=e^{-2\pi i\xi}$，参见 0.2）若两套构形具有相同 $\operatorname{tr}\mathsf Q(E)$（a.e.）且其测量的 Naimark 扩张同型，并约定 $m$ 取与 trace-normed 规范系统一致的规范化（消去 $a+bz$ 自由度），$\operatorname{Arg}\det S$ 取同一连续分支（差常数），则二者于 $\mathbf{UMS}$ 中酉等价；于是

$$
d\mu_\varphi(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE
$$

为读数几何的**唯一刻度**（至零测集与单调重参数化）。

**前提说明**：本定理要求 $\mu_\varphi$ 全体无负部且满足 Herglotz 表示的标准增长/可积条件（例如 $\int (1+E^2)^{-1}\,d\mu_\varphi(E)<\infty$，超出部分吸收到 $a+bz$ 项）；所用 Herglotz 函数 $m$ 取与 trace-normed 规范系统一致的规范化（消去 $a+bz$ 自由度）；$\operatorname{Arg}\det S$ 取同一连续分支（差常数）。

**证明。** $\operatorname{tr}\mathsf Q$ 相同 $\Rightarrow$ $\operatorname{Arg}\det S$ 差常数；由 BK 得同一 $\xi'$ 与 $\rho_{\mathrm{rel}}$。在 $\mu_\varphi$ 全体无负部且满足 Herglotz 条件、扩张同型、规范化一致的前提下，酉等价为**充分条件**；由 **trace-normed** 规范系统的逆谱理论得到唯一确定（至自然重参数化）的 $m$，进而确定规范系统与 de Branges 空间；Naimark 同型确保 POVM 层一致，故存在酉等价。若去除此同型假设，仅能得局部等价。∎

---

### 定理 3.3（三位一体）

**(i) Born = I-projection（严格）。** 在 PVM $\{P_j\}$ 下，可行集为单点 $\{p^\star\}$；任意严格凸 Bregman/KL 的 I-projection 唯一取于 $\,p^\star$。POVM 先作 Naimark 扩张，再回推。∎

**(ii) Pointer = 光谱极小（谱投影版 Ky Fan，含可达性）**。设 $K_{w,h}$ 为有界自伴，$P_t:=\mathbf{1}_{(-\infty,t]}(K_{w,h})$。对任意 $r\in\mathbb N$，
$$
\inf_{U^\dagger U=I_r}\mathrm{tr}(U^\dagger K_{w,h}U)=\inf_{t\in\mathbb R}\ \inf_{\substack{M\subset\mathrm{Ran}\,P_t \\ \dim M=r}}\mathrm{tr}_M(P_M K_{w,h}P_M),
$$
**一般仅为下确界**；**若** $K_{w,h}$ 为**紧**或在**有限维截断**上（**或**其底谱阈值 $t_0:=\inf\sigma(K_{w,h})$ 处存在至少 $r$ 个**本征值**，可为**嵌入**本征值，计重数），则该下确界**可达**，并等价于
$$
\min_{U^\dagger U=I_r}\mathrm{tr}(U^\dagger K_{w,h}U)=\sum_{k=1}^{r}\lambda^{\uparrow}_k(K_{w,h}),
$$
其中 $\lambda^{\uparrow}_1\le\lambda^{\uparrow}_2\le\cdots$ 为（含重数的）**升序**本征值序列。**有限维特例**：若 $K_{w,h}$ 为 $n\times n$ 矩阵且按降序 $\lambda_1\ge\cdots\ge\lambda_n$ 记谱，则 $\sum_{k=1}^{r}\lambda^{\uparrow}_k=\sum_{k=n-r+1}^{n}\lambda_k$。

极小子空间由最小 $r$ 个本征值的本征向量张成。上述两种表述在各自适用域内等价。

**参考根据**：Ky Fan 变分原理（"最小 $r$ 个本征值之和 = 压缩迹的极小"）适用于有限维/紧算子情形；一般有界自伴算子采用谱投影表述。见 Horn, R. A. & Johnson, C. R., *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013，第 4 章定理 4.3.4（Ky Fan 极大极小原理）与推论 4.3.3（迹极小）；或等价教材对 Fan 最大/最小原理的系统表述。∎

**(iii) Windows = 极大极小（带限最坏情形，良定版）。** 设

$$
\mathcal F=\{f\in L^2(\mathbb R):\operatorname{supp}\widehat f\subset[-B,B]\},\quad \|f\|_2=1.
$$

取**目标窗** $w_{\mathrm{tar}}\in L^2(\mathbb R)$（如 $w_{\mathrm{tar}}=\mathbf{1}_{[-R,R]}/\sqrt{2R}$），并将**设计窗**限制为 $w\in\mathcal F$, $\|w\|_2=1$。定义

$$
\mathcal E(w):=\sup_{f\in\mathcal F}\big|\langle f,w_{\mathrm{tar}}\rangle-\langle f,w\rangle\big|=\|P_{\mathcal F}(w_{\mathrm{tar}}-w)\|_2.
$$

则极小值当且仅当

$$
w^\star=\frac{P_{\mathcal F}w_{\mathrm{tar}}}{\|P_{\mathcal F}w_{\mathrm{tar}}\|_2}\quad(\|P_{\mathcal F}w_{\mathrm{tar}}\|_2\neq 0)
$$

取得；若 $P_{\mathcal F}w_{\mathrm{tar}}=0$，则任意 $w\in\mathcal F$, $\|w\|_2=1$ 皆为极小解，最小误差为 1。该等式由 Riesz 表示与 $P_{\mathcal F}$ 的正交投影性质直接得出，极值由 $f^\star=P_{\mathcal F}(w_{\mathrm{tar}}-w)/\|P_{\mathcal F}(w_{\mathrm{tar}}-w)\|_2$ 达成（当分母非 0 时）。多窗情形的最优对偶窗仍由 Wexler–Raz 双正交刻画。∎

---

### 定理 3.4（采样—帧门槛的相位化）

**命题。** 定义

$$
\boxed{\ T(E)\ :=\ \mu_\varphi\big((E_0,E]\big)\ }\,.
$$

在**a.c. 区间**上有

$$
T'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}\quad\text{(a.e.)},
$$

**跨原子点**按跳跃量 $\Delta T=\mu_\varphi(\{E_*\})$ 拼接；等价地，若无奇异/原子部分，则

$$
T(E)=\int_{E_0}^E \rho_{\mathrm{rel}}(u)\,du=\frac{\varphi(E)-\varphi(E_0)}{\pi}.
$$

当 $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 在所考察区间 a.e. **非负**时，$T$ **单调不减**并可作（可能退化的）重参数化；当其在该区间 a.e. **严格为正**时，$T$ **严格单调**并给出**可逆**的重参数化。

**Landau 密度的尺度传递条件**：Landau 必要密度（见参考文献 [4]，Landau, H. J., Acta Math. 117, 37–52, 1967）原本针对**等距线性尺度** $E$ 轴上的 Paley–Wiener 空间。若 $E\mapsto T$ 重参数化为**非线性**，则在下列**附加正则条件**下 Landau 阈值在 $T$ 轴与 $E$ 轴间等价：
(i) $T$ 在所考察 a.c. 区间上**绝对连续**且**双 Lipschitz**（即存在 $0<c\le C<\infty$ 使 $c\le T'(E)\le C$ a.e.），或更一般地，
(ii) $T'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$ 在该区间上下有**正界**：$\inf_{E\in I}T'(E)>0$ 且 $\sup_{E\in I}T'(E)<\infty$。

在此正则条件下，$E$ 轴的带宽 $B_E$ 与 $T$ 轴的带宽 $B_T$ 经拉回/推前保持等价（至有界因子），从而 Landau 密度阈值不失真。若不满足上述正则性（如 $T'$ 可任意趋零或发散），则仅能保证**单调性诱导的序关系**，不能无条件继承 Landau 阈值的定量表述。

多窗可重构性由帧算子与 Wexler–Raz 双正交刻画；临界密度下满足 Balian–Low 不可能性。∎

---

## 4. 有限阶非渐近误差学（Nyquist–Poisson–EM）

**定理 4.1（Poisson—Nyquist：基带无混叠）。** 设 $\operatorname{supp}\widehat f\subset[-B,B]$。在**理想采样与理想重构**前提下：
- 当 $f_s\ge 2B$ 时，Poisson 复制频带互不重叠，故在**基带/重构域**内仅 $k=0$ 贡献，别名项为 0；
- 当 $f_s<2B$ 时，越界频谱重叠产生混叠。∎

**定理 4.2（Euler–Maclaurin：有限阶伯努利层与余项）。** 当 $F\in C^{2m}([a,b])$ 且 $F^{(2m)}$ 有界或具有限总变差时，EM 给出到 $2m$ 阶的伯努利校正与**显式**积分余项；AFP-Isabelle 对余项与收敛条件给出形式化证明，由此可在实现中**择定有限阶 $m$** 并得到可执行上界。EM 余项采用 AFP-Isabelle 'Euler_MacLaurin' 的**形式化上界**，在实现中显式指明所取阶数 $m$ 与被积/被和函数的正则性（$C^{2m}$ 或有限总变差）以复现上界。∎

**定理 4.3（三分解闭合）。** $K_{w,h}$ 的实现可写为：离散求和（Nyquist）$+$ EM 有限阶校正（伯努利层）$+$ 余项（别名+截断）。在理想采样与重构下，当带限且 $f_s\ge 2B$ 时别名层为 0；EM 余项由 4.2 的上界控制，故得**有限阶、非渐近闭合**。∎

---

## 5. 信息单调与容量上界

**定理 5.1（DPI：相对熵在 **PTP** 映射下单调）。** 对任意**正迹保持（PTP）**映射 $\Phi$，

$$
D\!\left(\Phi(\rho)\,\middle\Vert\,\Phi(\sigma)\right)\le D(\rho\Vert\sigma).
$$

**证明要点。** Müller-Hermes–Reeb 以"夹态 Rényi 发散 + 复插值"证明 DPI 在**正迹保持**（不必 CP）下成立，并以 Petz 恢复映射刻画等号情形。

**（括注）** Umegaki 相对熵的 DPI **对任意正且迹保持的线性映射**皆成立；这是 Müller-Hermes–Reeb 的结果（Müller-Hermes & Reeb, 2015），并不要求 CP/2-positive/Schwarz 条件。本文在陈述 HSW 等容量结论时仍**限定信道为 CPTP**。∎

**定理 5.2（HSW：**CPTP** 信道的无助理经典容量）。** 量子**完全正且迹保持（CPTP）**信道 $\mathcal N$ 的无助理经典容量满足

$$
C(\mathcal N)=\lim_{n\to\infty}\frac{1}{n}\,\chi\!\left(\mathcal N^{\otimes n}\right),\qquad I_{\mathrm{acc}}\le \chi\,.
$$

因此**单次** Holevo 信息 $\chi(\mathcal N)$ 一般不足以给出容量（需正则化极限）。

**证明要点。** 参见 Watrous 教科书对编码、Holevo 界与强对偶的标准推导。∎

---

## 6. 派生结构与物理后果

**6.1 时间密度与延迟积分。** 见 §3.4 定义（并按原子点跳跃拼接）。在**a.c. 区间**上有

$$
T'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)\quad\text{(a.e.)}.
$$

当 $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 在所考察区间 a.e. **非负**时，$T$ **单调不减**并可作（可能退化的）重参数化；当其在该区间 a.e. **严格为正**时，$T$ **严格单调**并给出**可逆**的重参数化。当 $(2\pi)^{-1}\operatorname{tr}\mathsf Q\ge 0$ a.e. 时，$T$ 单调不减；**仅在 §3.4 的正则性条件（i）或（ii）成立**时，Landau 必要密度在 $T$ 与 $E$ 轴之间**定量等价**；若条件不满足，则仅保留由单调性诱导的序关系（见 §3.4『Landau 密度的尺度传递条件』及参考文献 [4]）。**单通道**时 $S=e^{2i\varphi}$，故 $T(E)=\dfrac{\varphi(E)-\varphi(E_0)}{\pi}$，表征可测群延迟并与部分密度态联系。

**6.2 非厄米/耗散与共振寿命。** 耗散（非酉）系统存在"修正 BK"与相应时间延迟推广。单通道 Breit–Wigner 近似下 $\delta'(E_0)=\tfrac{2}{\Gamma}$，以 $\tau=\hbar\,\mathrm{eig}(\mathsf Q)=2\hbar\,\delta'(E)$ 定义时间延迟，则 $\boxed{\tau_{\max}(E_0)=\tfrac{4\hbar}{\Gamma}}$。共振寿命为 $\tau_{\text{life}}=\hbar/\Gamma$，二者概念不同，不应混同。

**宽度记号的双约定对照**（避免文献换算歧义）：散射理论与共振物理中存在**两种常用极点记号**，对应不同的 $\tau_{\max}$ 公式：

| 极点记号 | 相位导数 $\delta'(E_0)$ | 峰值延迟 $\tau_{\max}(E_0)$ | 寿命 $\tau_{\text{life}}$ | 备注 |
|:--------:|:------------------------:|:---------------------------:|:-------------------------:|:-----|
| $E_0-i\Gamma/2$ | $2/\Gamma$ | $4\hbar/\Gamma$ | $\hbar/\Gamma$ | 本文统一采用 |
| $E_0-i\Gamma$ | $1/\Gamma$ | $2\hbar/\Gamma$ | $\hbar/\Gamma$ | 部分电磁/量子文献采用 |

二者差异源于 $S$-矩阵极点虚部的**归一化约定**：以 $E_0-i\Gamma/2$ 计宽度时 $\delta'(E_0)=2/\Gamma$，以 $E_0-i\Gamma$ 计宽度时 $\delta'(E_0)=1/\Gamma$；由 $\tau=2\hbar\delta'$ 即得上表第三列。**本文统一采用**极点 $E_0-i\Gamma/2$ 之记号，与量子散射及电磁散射多数文献一致（例如 Phys. Rev. E 103, L050203, 2021 以 $E_0-i\Gamma$ 记号得 $\tau_{\max}=2\hbar/\Gamma$；换算至本文记号即 $\Gamma_{\text{本文}}=\Gamma_{\text{该文}}/2$，峰值 $4\hbar/\Gamma_{\text{本文}}=2\hbar/\Gamma_{\text{该文}}$ 一致）。

**负群延迟与复时间延迟**：在非厄米/亚酉散射系统中，$\operatorname{tr}\mathsf Q$ 可变号并取复值，对应可观测的脉冲整形与超前/延迟效应。亚酉散射下可取 $\mathsf Q(E)=-i\,S^{-1}(E)\,S'(E)$（一般非自伴），此时 $\operatorname{tr}\mathsf Q$ 允许为复数；其**实部/虚部**分别刻画驻留与耗散相关量（具体选择依赖所用**最大耗散扩张/自伴扩张**，详见 §0.2 之框架）。非厄米/有耗系统的复时间延迟已在微波/光学平台实验与理论中系统研究；近年电磁超材料、光子晶体与开放量子系统的实验与数值研究（含亚波长阵列的负群延迟与复 Wigner 时间延迟统计）均证实此现象，并与谱移密度 $\rho_{\mathrm{rel}}$ 变号相互印证（例如 Phys. Rev. E 103, L050203, 2021；Patel et al., arXiv:2005.03211, 2020/2021）。

可在"**最大耗散扩张/耦合散射**"的框架下以谱移与广义 Weyl 函数精确表达。上述耗散/耦合情形可参见 **Behrndt–Malamud–Neidhardt** 对 BK 变体与迹公式的系统化表述（见参考文献 [12]），该框架把"谱移—Weyl 函数—散射矩阵"的关系与变体公式锚定到统一理论。

---

## 7. 可检清单（实验/数值）

1. **相位—延迟一致性**：计算 $\operatorname{Arg}\det S(E)$ 与 $\mathsf Q(E)$，验证 $\operatorname{tr}\mathsf Q(E)=\tfrac{d}{dE}\operatorname{Arg}\det S(E)$ 与单通道下 $\varphi'(E)$。单位验证：确认 $\mathsf Q$ 量纲为能量$^{-1}$，$\tau=\hbar\,\mathrm{eig}(\mathsf Q)$ 为时间量纲。**电磁散射算例**：对电磁散射体（如介质球、谐振腔、亚波长阵列），采用 Patel et al. (arXiv:2005.03211, 2020) 的 WS 群延迟矩阵定义 $\mathsf Q=-i S^\dagger S'$ 并与 $\det S$ 导数对比；对单极/多极散射的 $S$ 矩阵以频率 $\omega$ 或能量 $E=\hbar\omega$ 为自变量，验证 $\operatorname{tr}\mathsf Q$ 与相位导数一致性；数值/实验平台见 Phys. Rev. E 103, L050203 (2021) 等亚酉散射报道。
2. **刻度化采样**：以 $T(E)=\mu_\varphi((E_0,E])$（无原子时等于 $\int_{E_0}^E(2\pi)^{-1}\operatorname{tr}\mathsf Q$）重参数化能量，在 $T$ 轴执行 Landau 阈值检验与插值实验，再映回 $E$ 轴（参见定理 3.4 对 $T'(E)$ 的相位化表达）。**最小工作示例**：对单通道、单峰 $\operatorname{tr}\mathsf Q(E)$ 情形（如 Breit–Wigner 共振），绘制 $(E,T(E))$ 曲线并验证在 $T'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)>0$ 区间上的单调性。
3. **指针基极小性**：比较任意正交基与 $K_{w,h}$ 本征基的 Ky Fan 部分和。
4. **窗/核最优与 WR**：带限与归一约束下，用 KKT 条件求最优窗；验证与 Wexler–Raz 对偶一致。
5. **三分解误差闭合**：报告"别名 + 伯努利层 + 截断"三项；在带限+Nyquist 下别名 0；EM 余项给出显式上界。
6. **信息收支**：沿"制备 $\to$ 信道 $\to$ 读数"链记录 $D$ 的单调递减与 $I_{\mathrm{acc}}\le\chi\le C$。

---

## 参考文献（选）

1. Patel, U. R., et al., *Wigner–Smith Time-Delay Matrix for Electromagnetics*, arXiv:2005.03211, 2020。
2. Pushnitski, A., *An Integer-Valued Version of the Birman-Kreĭn Formula*, arXiv:1006.0639, 2010；Guillarmou, C., *Generalized Krein Formula…*, 2009。
3. Remling, C., Hur, I., *Density of Schrödinger Weyl-Titchmarsh m functions on Herglotz functions*, arXiv:1501.01268; de Branges, L., *Hilbert Spaces of Entire Functions*（Purdue）。
4. Landau, H. J., *Necessary Density Conditions for Sampling and Interpolation of Certain Entire Functions*, Acta Math. **117**, 37–52 (1967), https://doi.org/10.1007/BF02395039。
5. Daubechies, I., Landau, H. J., Landau, Z., *Gabor Time-Frequency Lattices and the Wexler–Raz Identity*, J. Fourier Anal. Appl. **1**(4), 437–478 (1995)。
6. Caragea, A., et al., *A Balian–Low Type Theorem for Gabor Riesz Sequences…*, 2023。
7. Naimark's Dilation（综述）与 Busch, P., *A Simple Proof of Gleason's Theorem*, PRL, 2003。
8. Manzano, D., *A Short Introduction to the Lindblad Master Equation*, 2019。
9. Müller-Hermes, A., Reeb, D., *Monotonicity of the Quantum Relative Entropy under Positive Maps*, arXiv:1512.06117, 2015。
10. Watrous, J., *The Theory of Quantum Information*, Cambridge University Press, 2018（HSW 章节）。
11. Eberl, M., *The Euler–MacLaurin Formula*, Archive of Formal Proofs (AFP-Isabelle), https://devel.isa-afp.org/entries/Euler_MacLaurin.html。
12. Behrndt, J., Malamud, M., Neidhardt, H., *Trace Formulae for Dissipative and Coupled Scattering Systems*, arXiv:0712.3120（及相关后续）。

---

## 附录 A：核心等式的自洽推导

**引理 A.1（$\operatorname{tr}\mathsf Q=\tfrac{d}{dE}\operatorname{Arg}\det S$）。** 由 Jacobi 公式 $\tfrac{d}{dE}\log\det S=\operatorname{tr}(S^{-1}S')$ 与酉性 $S^{-1}=S^\dagger$，得 $\tfrac{d}{dE}\log\det S=\operatorname{tr}(S^\dagger S')$；结合 $\mathsf Q=-i\,S^\dagger S'$ 得

$$
\operatorname{tr}\mathsf Q=-i\,\operatorname{tr}(S^\dagger S')=\Im\,\operatorname{tr}(S^\dagger S')=\frac{d}{dE}\operatorname{Arg}\det S\ \ (\text{a.e.}).
$$

∎

**引理 A.2（BK 链）。** $\det S=e^{-2\pi i\,\xi}\Rightarrow \tfrac{d}{dE}\operatorname{Arg}\det S=-2\pi\,\xi'$；令 $\rho_{\mathrm{rel}}:=-\xi'$，得 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$。∎

**推论 A.3（单通道回到相位导数）。** 若 $S=e^{2i\varphi}$，则 $\operatorname{tr}\mathsf Q=2\varphi'$；合并 A.2 得 $\varphi'/\pi=\rho_{\mathrm{rel}}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$。∎

---

## 附录 B：Ky Fan 变分与指针极小

令 $K$ 自伴，$\lambda^{\uparrow}_1\le\lambda^{\uparrow}_2\le\cdots$ 为（含重数的）**升序**本征值序列。Ky Fan 原理给出

$$
\sum_{k=1}^r\lambda_k=\max_{U^\dagger U=I_r}\operatorname{tr}(U^\dagger K\,U),\quad
\sum_{k=1}^{r}\lambda^{\uparrow}_k=\min_{U^\dagger U=I_r}\operatorname{tr}(U^\dagger K\,U).
$$

（此处第 1 式为降序记号：$\lambda_1\ge\cdots\ge\lambda_r\ge\cdots$；第 2 式用升序记号 $\lambda^{\uparrow}$。）

**有限维特例**：若 $K$ 为 $n\times n$ 矩阵且按降序 $\lambda_1\ge\cdots\ge\lambda_n$ 记谱，则 $\sum_{k=1}^{r}\lambda^{\uparrow}_k=\sum_{k=n-r+1}^{n}\lambda_k$。

最大迹取于由前 $r$ 个本征向量张成的子空间，最小迹取于由最小 $r$ 个本征向量张成的子空间。∎

---

## 附录 C：EM 余项的有限阶上界

在 0.7 的假设下（$F\in C^{2m}$ 及 $F^{(2m)}$ 有界/有限变差），EM 公式给出到 $2m$ 阶的伯努利层与**显式**积分余项；AFP–Isabelle 对余项的构造与收敛作了形式化验证，因而在数值实施中可据以选择有限阶 $m$ 并给出可执行上界。EM 余项采用 Archive of Formal Proofs (AFP-Isabelle) 条目 **The Euler–MacLaurin Formula** 的形式化上界（Eberl, M., https://www.isa-afp.org/entries/Euler_MacLaurin.html），在实现中显式指明所取阶数 $m$ 与被积/被和函数的正则性（$C^{2m}$ 或有限总变差）以复现上界。∎

---

## 附录 D：与 S15–S26 及 EBOC 体系的接口

**D.1 与 S15–S23（散射相位、Herglotz、Weyl–Mellin、框架）的接口。**
- S15–S17 的 Herglotz 表示与规范系统直接给出 UMS 中的 $\mathcal S$ 函子与 $d\mu_\varphi$。
- S18–S20 的 Weyl–Mellin 非平稳框架为 UMS 的多窗协变提供具体实现。
- S21–S23 的相位—尺度协变与 Euler–Maclaurin 有限阶误差学直接支撑 A1、A2 与定理 4.1–4.3。

**D.2 与 S24–S26（紧框架、非平稳框架、相位密度）的接口。**
- S24 的纤维 Gram 表征与 Wexler–Raz 双正交为 A6 与定理 3.3(iii) 提供具体计算框架。
- S25 的 Calderón sum 与 tight/dual 构造为 UMS 的多窗优化（定义 2.1(iv)）提供可操作方案。
- S26 的相位密度刻度 $\varphi'(x)=\pi\rho(x)$ 与 Landau 必要密度、Balian–Low 不可能性直接对应 A5、A6 与定理 3.4。

**D.3 与 EBOC-Graph 的接口。**
- EBOC-Graph 的 Born = I-projection（G1）与 UMS 的定理 3.3(i) 在离散谱情形下等价。
- EBOC-Graph 的指针基 = 谱极小（G2）与 UMS 的定理 3.3(ii) 在图拉普拉斯情形下一致。
- EBOC-Graph 的窗口极大极小（G3）与 UMS 的定理 3.3(iii) 在带限约束下共享同一优化结构。
- EBOC-Graph 的非渐近误差闭合（G4）与 UMS 的定理 4.3 均采用 Nyquist–Poisson–EM 三分解框架。

**D.4 与 CCS（协变多通道）及 WSIG-QM 的接口。**
- CCS 的窗化 Birman–Kreĭn 恒等式与 UMS 的核心统一式（定义 2.2）在多通道情形下完全一致。
- CCS 的 Wigner–Smith 群延迟矩阵 $\mathsf Q(E)$ 与 UMS 的 A5 采用相同定义与约定。
- WSIG-QM 的七大公理（A1–A7）与 UMS 的公理体系（§1）在概念与表述上高度对齐；WSIG-QM 可视为 UMS 在量子测量特定语境下的精细展开。
- WSIG-QM 的统一字典（§5）与 UMS 的范畴化定义（§2）共同支撑"态—测量—概率—指针—散射—延迟—帧—误差—容量"的全链条统一。

**D.5 保持"极点 = 主尺度"的有限阶 EM 纪律。**
- UMS 在所有离散—连续换序中均采用**有限阶** EM（A1、定理 4.2），确保不引入新奇点。
- 与 S15–S26、EBOC-Graph、CCS、WSIG-QM 保持一致：散射极点、共振极点、谱奇点始终为"主尺度"标记，EM 余项仅作有界扰动。

---

### 一句话总结

$$
\boxed{\ \textbf{UMS}\ \Longleftrightarrow
\big(\,d\mu_\varphi=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\,dE=\rho_{\mathrm{rel}}\,dE=\tfrac{\varphi'}{\pi}\,dE;
K_{w,h}\text{ 的 Nyquist–Poisson–EM 有限阶闭合};
\text{Born=I-proj,\ DPI,\ HSW};
\text{Landau/WR/BL};
\text{Pointer=Ky Fan 极小}\,\big). }
$$
