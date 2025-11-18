# 计算宇宙中的误差控制与谱窗化读数

统一时间刻度下 PSWF/DPSS 窗函数的时间–频率–复杂性角色

---

## 摘要

在此前关于计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 的系列工作中，我们已经建立了离散复杂性几何（复杂性距离、体积增长与离散 Ricci 曲率）、离散信息几何（任务信息流形 $(\mathcal S_Q,g_Q)$ 与嵌入 $\Phi_Q$）、统一时间刻度诱导的控制流形 $(\mathcal M,G)$ 以及时间–信息–复杂性联合变分原理。其中统一时间刻度由散射母尺

$$
\kappa(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

将物理时间密度、谱移函数导数与 Wigner–Smith 群延迟迹统一起来。

然而，上述结构仍然是"理想极限"：复杂性球 $B_T(x_0)$ 的半径 $T$ 可以任意大，控制流形上的测地线可以任意延伸，信息流形上的 Fisher 结构可以在无限数据下被完美辨识。在实际的计算宇宙中，一切读数与决策都在有限时间、有限复杂性预算与有限频带的约束下进行，因此必然带有**误差**。要在统一时间刻度–复杂性几何–信息几何的框架内对误差进行严格控制，需要一个系统的"谱窗化读数"理论。

本文在计算宇宙框架下引入读数算子与误差模型，并将其统一为统一时间刻度频域中的窗函数问题。我们证明：在统一时间刻度下，将读数算子写成对频域对象的积分

$$
\mathcal R(f) = \int_{\Omega} W(\omega)\,f(\omega)\,\mathrm d\omega,
$$

其中 $W(\omega)$ 为窗函数，$f(\omega)$ 为与宇宙演化相关的频域量（例如 $\kappa(\omega)$ 或其加权），可以自然引出一类时间–带限–复杂性限的联合极值问题。

在连续情形，我们证明：在给定时间截断区间 $[-T,T]$ 与频带 $[-W,W]$ 的约束下，Prolate Spheroidal Wave Functions（PSWF）是最优窗函数族：它们在 $[-T,T]$ 与 $[-W,W]$ 的双重限制下最大化能量集中度，从而在统一时间刻度–复杂性预算给定时，最小化"能量泄漏到复杂性球外"的最坏情形误差。

在离散情形，我们引入对应的 Discrete Prolate Spheroidal Sequences（DPSS），定义在有限长度复杂性链上的窗序列，证明它们在离散时间–频率限制下最大化能量集中度，从而在有限复杂性步数 $N$、有限带宽 $W$ 的约束下，给出了"有限阶读数"的最优误差控制结构。

在统一时间刻度–复杂性几何的语言下，我们得到如下结论：

1. 对统一时间刻度频带有限的计算宇宙读数（例如散射延迟谱），若复杂性预算仅允许 $2TW/\pi$ 级别的自由度，则 PSWF 窗函数给出了在该预算下最优的误差–复杂性折衷；
2. 在离散复杂性图 $G_{\mathrm{comp}}$ 上，DPSS 提供了在有限步长 $N$、有限频带 $W$ 下的最优读数序列，其误差衰减与谱集中度常数由 DPSS 特征值控制；
3. 这些结果可被嵌入时间–信息–复杂性联合变分原理中，将"选择读数窗函数"视为在联合流形 $\mathcal E_Q$ 上增加一层"谱窗化控制维度"，从而给出"有限资源下的最优观测策略"的变分刻画。

本文作为计算宇宙系列中的"误差控制"篇，在统一时间刻度–频域–复杂性几何的接口上，将 PSWF/DPSS 的经典时间–频率集中性结果提升为计算宇宙中的误差控制与可观测性理论，为后续构造 FRB/δ–环等具体物理–工程测试台上的统一读数设计提供理论基础。

---

## 1 引言

在任何实际物理或计算系统中，读数与决策都无法在无限时间、无限复杂性预算与无限频带上进行。统一时间刻度–复杂性几何–信息几何给出的是"无限理想宇宙"的几何结构：

* 复杂性球 $B_T(x_0)$ 可以随 $T \to \infty$ 扩大；
* 控制流形 $(\mathcal M,G)$ 上的 geodesic 世界线可以延伸至无穷远；
* 频域上的统一时间刻度密度 $\kappa(\omega)$ 可以在无限频带上被观测；
* 信息流形 $(\mathcal S_Q,g_Q)$ 的 Fisher 结构在无限数据下可以被完全辨识。

但在现实中，我们必须在如下限制下工作：

1. **时间–复杂性限制**：总复杂性预算 $T$ 有限，复杂性球外的区域在有限时间内不可达；
2. **频带限制**：统一时间刻度密度 $\kappa(\omega)$ 的有效频带有限，或实际读数设备仅能在有限频带内响应；
3. **读数阶数限制**：可实现的读数算子维度有限，例如只能采样有限个时刻或有限个频率点，或只能执行有限阶矩–滤波操作；
4. **误差容忍度**：系统必须保证在这些限制下误差不超过某个容许阈值。

在信号处理与时间–频率分析中，PSWF/DPSS 以其"在有限时间与有限频带下能量集中度最优"的性质成为经典工具。然而，这些结果多半是在纯信号空间（例如 $L^2([-T,T])$ 与 $L^2(\mathbb R)$ 中）讨论，尚未系统地嵌入统一时间刻度–复杂性几何框架。

本文的目的有三：

1. 将计算宇宙中的读数过程形式化为统一时间刻度频域上的窗函数问题；
2. 在统一时间刻度–复杂性预算约束下，给出 PSWF/DPSS 窗函数在误差控制意义上的最优性定理；
3. 将这些结果嵌入到时间–信息–复杂性联合变分原理中，构造一个"有限资源下最优观测"的理论框架。

全文组织如下：第 2 节定义计算宇宙中的读数算子与误差模型。第 3 节在统一时间刻度频域中引入谱窗化读数。第 4 节回顾并重述 PSWF/DPSS 的能量集中性与有限时间–频带最优性质，并将其翻译为"有限复杂性读数"的误差上界。第 5 节讨论计算宇宙中的"复杂性–时间–带宽"三重统一约束。第 6 节将窗函数选择纳入联合变分原理，给出"最优观测策略"的变分形式。附录中给出 PSWF/DPSS 定义、关键特征值性质与主要误差上界定理的详细证明。

---

## 2 计算宇宙中的读数算子与误差模型

本节在计算宇宙 $U_{\mathrm{comp}} = (X,\mathsf T,\mathsf C,\mathsf I)$ 上形式化读数算子，并定义误差与误差预算。

### 2.1 路径层读数算子

考虑从初态 $x_0$ 出发的一条演化路径

$$
\Gamma = (x_0,x_1,x_2,\dots), \quad (x_k,x_{k+1})\in\mathsf T.
$$

统一时间刻度下，每一步具有物理时间增量

$$
\Delta t_k = \mathsf C(x_k,x_{k+1})/\lambda,
$$

其中 $\lambda$ 为单位换算常数（在下文中可吸收进 $\mathsf C$ 中）。

**定义 2.1（路径读数算子）**

一个路径读数算子是映射

$$
\mathcal R: \{\text{路径}\ \Gamma\} \to \mathbb C^m,
$$

其可写为有限次线性泛函的组合，例如

$$
\mathcal R(\Gamma) = \big( \langle r_1,\Gamma\rangle,\dots,\langle r_m,\Gamma\rangle \big),
$$

其中每个 $r_j$ 是有限支撑的"核"，例如

$$
\langle r_j,\Gamma\rangle = \sum_{k} r_j(k,x_k).
$$

在连续极限下，可将 $\Gamma$ 视为控制流形与信息流形上的曲线 $(\theta(t),\phi(t))$，读数成为时间积分

$$
\langle r_j,\Gamma\rangle = \int_0^T R_j(\theta(t),\phi(t))\,w_j(t)\,\mathrm dt,
$$

其中 $w_j(t)$ 为权重函数（窗函数）。

### 2.2 理想读数与截断读数

理想情况下，我们希望对无限长路径或无限时间窗口进行读数：

$$
\mathcal R_{\mathrm{ideal}}(\Gamma) = \int_0^{\infty} R(\theta(t),\phi(t))\,\mathrm dt.
$$

然而在有限复杂性预算 $T_{\max}$ 中，只能在有限时间内读数：

$$
\mathcal R_{\mathrm{trunc}}(\Gamma) = \int_0^{T_{\max}} R(\theta(t),\phi(t))\,W(t)\,\mathrm dt,
$$

其中 $W(t)$ 是在 $[0,T_{\max}]$ 上支持的窗函数，用于在时间边缘平滑截断。

两者之间的差异定义了读数误差：

$$
\mathrm{Err}(\Gamma;W) = \mathcal R_{\mathrm{ideal}}(\Gamma) - \mathcal R_{\mathrm{trunc}}(\Gamma).
$$

在频域描述中，$W$ 的选择直接决定误差的衰减与能量泄漏性质，因此选择最优窗函数 $W$ 是误差控制的核心。

### 2.3 误差范数与最坏情况误差

为了进行统一讨论，我们引入路径空间上的一个半范数（例如由统一时间刻度频谱诱导的 $L^2$ 范数）。

设对每条路径 $\Gamma$ 存在一个对应频域对象 $f_\Gamma(\omega)$（例如由控制流形上散射数据与统一时间刻度密度组合而成），其满足

$$
|\Gamma|^2 = \int_{\Omega} |f_\Gamma(\omega)|^2\,\mathrm d\mu(\omega).
$$

读数误差可以写成频域窗口的形式（见第 3 节），其最坏情况范数定义为

$$
\mathcal E(W) = \sup_{\Gamma\ne 0} \frac{|\mathrm{Err}(\Gamma;W)|}{|\Gamma|}.
$$

我们关心的是在给定时间–带宽与复杂性预算约束下，找到窗函数族 $\{W\}$ 使得 $\mathcal E(W)$ 尽可能小。

---

## 3 统一时间刻度频域中的谱窗化读数

本节在统一时间刻度母尺下引入频域描述，将读数算子写成窗函数与频谱的内积。

### 3.1 统一时间刻度频域表示

在前文中，我们已经在物理宇宙侧将统一时间刻度与散射数据联系起来。将这一结构拉回计算宇宙，可认为每条路径 $\Gamma$ 对应一个频域对象

$$
f_\Gamma(\omega) = \kappa(\omega)\,\Phi(\Gamma;\omega),
$$

其中 $\kappa(\omega)$ 为统一时间刻度密度，$\Phi(\Gamma;\omega)$ 由控制–散射结构编码路径对该频率模式的响应。

对给定读数核，可在频域定义窗口

$$
W(\omega)
$$

使得

$$
\mathcal R(\Gamma) = \int_{\Omega} W(\omega)\,f_\Gamma(\omega)\,\mathrm d\omega.
$$

理想读数对应 $W_{\mathrm{ideal}}(\omega) \equiv 1$（或某个固定权重），而有限复杂性读数对应将 $W(\omega)$ 限制在有限带宽 $[-W,W]$ 或有限自由度空间中。

### 3.2 时间–频率双限制与窗函数设计问题

设我们仅能在时间区间 $[-T,T]$ 内读数，对应时间窗 $w_T(t)$（例如 $w_T(t)=1$ 在 $|t|\le T$ 上，其他为 0），并且只对频带 $[-W,W]$ 感兴趣。

在频域，读数对频带外的能量敏感度决定误差：若路径频谱中的成分离开 $[-W,W]$，则窗函数 $W(\omega)$ 需要尽量抑制它们；但同时在 $[-W,W]$ 内应保持尽可能好的通过特性。

因此我们得到典型的双限制窗函数设计问题：

* 时间限制：读数窗 $w_T(t)$ 支持在 $[-T,T]$ 上；
* 频率限制：读数窗的频谱 $\widehat w_T(\omega)$ 集中在 $[-W,W]$ 上；
* 目标：在给定约束下，最小化频带外能量或最坏情况误差。

在信号分析中，这正是 PSWF/DPSS 的经典问题；本文将其解释为统一时间刻度–复杂性几何下的"最佳有限复杂性读数"。

---

## 4 PSWF/DPSS 与能量集中性：从时间–频率到时间–复杂性

本节回顾连续 PSWF 与离散 DPSS 的定义与能量集中性，并将其翻译为计算宇宙中的误差控制结果。

### 4.1 连续 PSWF 的定义与时间–频带集中性

**定义 4.1（连续 PSWF）**

固定时间窗 $T>0$ 与带宽 $W>0$。定义积分算子

$$
(\mathcal K f)(t) = \int_{-T}^{T} \frac{\sin W(t-s)}{\pi(t-s)} f(s)\,\mathrm ds, \quad |t|\le T.
$$

该算子等价于"先限时于 $[-T,T]$，再限带于 $[-W,W]$"的组合。其特征函数 $\psi_n(t)$ 与特征值 $\lambda_n$ 满足

$$
\int_{-T}^{T} \frac{\sin W(t-s)}{\pi(t-s)} \psi_n(s)\,\mathrm ds = \lambda_n \psi_n(t), \quad |t|\le T.
$$

$\psi_n$ 称为时间窗口 $[-T,T]$、带宽 $[-W,W]$ 下的 Prolate Spheroidal Wave Functions。

**命题 4.2（PSWF 的能量集中性）**

PSWF 满足：

1. 它们在 $[-T,T]$ 上构成正交基；
2. 对每个 $\psi_n$，定义频域能量集中度

$$
\alpha_n = \frac{ \int_{-W}^{W} |\widehat\psi_n(\omega)|^2\,\mathrm d\omega }{ \int_{-\infty}^{\infty} |\widehat\psi_n(\omega)|^2\,\mathrm d\omega },
$$

则 $\alpha_n = \lambda_n$，且 $\lambda_0\ge\lambda_1\ge\dots$；
3. 对给定时间窗与带宽，$\{\psi_n\}$ 在"同时时间与频率限制下能量集中度"的意义上是最优基：任何其他同维度子空间的能量集中度总和不超过 PSWF 子空间的总和。

命题 4.2 的证明在附录 A 中给出。

### 4.2 离散 DPSS 的定义与有限步长–有限带宽

在离散情形，考虑长度为 $N$ 的序列 $x[0],\dots,x[N-1]$，其离散时间–频率限制问题可通过 DPSS（Discrete Prolate Spheroidal Sequences）刻画。

**定义 4.3（DPSS）**

固定序列长度 $N$ 与归一化带宽 $W \in (0,1/2)$。定义 Toeplitz 矩阵

$$
K_{mn} = \frac{\sin 2\pi W(m-n)}{\pi(m-n)}, \quad 0\le m,n\le N-1,
$$

对角线处定义 $K_{mm} = 2W$。求解特征值问题

$$
\sum_{n=0}^{N-1} K_{mn} v_n^{(k)} = \lambda_k v_m^{(k)}.
$$

归一化的特征向量 $v^{(k)}$ 即为 $(N,W)$ 下的 DPSS，特征值 $\lambda_k$ 为能量集中度：

$$
\lambda_k = \frac{ \sum_{|\omega|\le W} |\widehat v^{(k)}(\omega)|^2 }{ \sum_{|\omega|\le 1/2} |\widehat v^{(k)}(\omega)|^2 }.
$$

**命题 4.4（DPSS 的离散能量集中性）**

DPSS $\{v^{(k)}\}$ 在离散时间–频率双限制下最大化能量集中度：对任何维度为 $K$ 的子空间 $V \subset\mathbb C^N$，其在频带 $[-W,W]$ 内的能量集中度总和不超过由前 $K$ 个 DPSS 张成空间的集中度总和。

证明见附录 A。

### 4.3 计算宇宙中的"有限复杂性读数"解释

在计算宇宙中，长度 $N$ 的路径片段可视为复杂性步数限制 $N$；统一时间刻度下对应时间窗口 $T\approx N\Delta t$。频带 $W$ 对应为统一时间刻度密度 $\kappa(\omega)$ 的有效支持。

在这一视角下：

* PSWF 对应在给定复杂性窗口 $[-T,T]$ 与频带 $[-W,W]$ 下的最优连续窗函数；
* DPSS 对应在离散复杂性步长 $N$ 与频带 $W$ 下的最优离散读数序列。

因此，在有限复杂性预算下任何读数算子若希望尽可能保真地捕捉统一时间刻度频谱中的信息，其时间窗或序列应该尽可能接近 PSWF/DPSS。

---

## 5 复杂性–时间–带宽三重统一约束

本节讨论复杂性预算 $T$、时间窗口 $T$ 与频带 $W$ 之间的关系，给出"计算宇宙版的 Landau–Pollak–Slepian 限制"。

### 5.1 时间–频率–复杂性自由度计数

在经典时间–频率分析中，带宽为 $W$、时间限制为 $T$ 的信号子空间的有效自由度数量为

$$
N_{\mathrm{eff}} \approx \frac{2WT}{\pi}.
$$

该结果可通过 PSWF 特征值的渐近行为得到：特征值 $\lambda_n$ 在 $n<2WT/\pi$ 时接近 1，在 $n>2WT/\pi$ 时快速下降到 0。

在统一时间刻度–复杂性几何中，我们可将该自由度计数解释为：

* 对给定复杂性预算 $T$ 与统一时间刻度频带 $W$，可以可靠编码或读出的独立模式数量约为 $N_{\mathrm{eff}}$；
* 在任务信息流形上，这对应在有限复杂性预算下可辨识的 Fisher 模式数量。

### 5.2 复杂性–时间–带宽约束不等式

我们 formalize 一个计算宇宙版本：

**定理 5.1（复杂性–时间–带宽自由度上界）**

设计算宇宙中存在一个统一时间刻度频域表示 $f_\Gamma(\omega)$，其支持或有效能量集中在 $[-W,W]$ 上。对复杂性预算 $T$，将路径限制在复杂性球 $B_T(x_0)$ 内，考虑所有读数算子

$$
\mathcal R_j(\Gamma) = \int_{-W}^{W} W_j(\omega)\,f_\Gamma(\omega)\,\mathrm d\omega, \quad j=1,\dots,K,
$$

其中 $\{W_j\}$ 为在 $L^2([-W,W])$ 中的正交窗函数族。

则在误差容忍度 $\varepsilon$ 下，可存在一个最优窗函数族 $\{W_j^{\star}\}$（由前 $K$ 个 PSWF 频谱给出），使得对所有路径 $\Gamma$ 满足

$$
\bigg| f_\Gamma(\omega) - \sum_{j=1}^{K} \langle f_\Gamma,W_j^{\star}\rangle W_j^{\star}(\omega) \bigg|_{L^2([-W,W])} \le \varepsilon |f_\Gamma|_{L^2([-W,W])}
$$

仅当

$$
K \gtrsim \frac{2WT}{\pi} + \mathcal O\big(\log(1/\varepsilon)\big).
$$

即复杂性–时间–带宽三重约束下，可可靠分辨的自由度数目不超过 $\approx 2WT/\pi$。

证明见附录 B。

这一结果可以理解为"计算宇宙的 Nyquist–Slepian 限制"：统一时间刻度频带 $W$ 与复杂性预算 $T$ 一起决定了在有限时间内可读出的有效模式数量。

---

## 6 窗函数选择的变分原理：最优观测策略

本节将窗函数选择引入时间–信息–复杂性联合变分原理，构造"最优观测策略"的变分形式。

### 6.1 扩展联合流形与窗函数自由度

此前联合流形

$$
\mathcal E_Q = \mathcal M\times\mathcal S_Q
$$

中，曲线 $z(t)=(\theta(t),\phi(t))$ 描述控制–信息状态的演化。

现在加入窗函数自由度：令 $\mathcal W$ 为某个窗函数空间（例如 $L^2([-T,T])$ 中满足带限约束的子空间），对每个读数通道 $j$ 选择窗函数 $W_j \in \mathcal W$。

扩展联合配置为

$$
\widehat z(t) = (\theta(t),\phi(t),\{W_j\}_{j=1}^K).
$$

窗函数本身可以不显含时间演化（视为策略的静态部分），也可在慢变量尺度上更新。

### 6.2 扩展作用量

在原有时间–信息–复杂性作用量基础上加入"观测误差代价"项：

$$
\mathcal A_Q[z(\cdot),\{W_j\}] = \int_0^T \Big( \tfrac12 \alpha^2 G_{ab}\dot\theta^a\dot\theta^b + \tfrac12 \beta^2 g_{ij}\dot\phi^i\dot\phi^j - \gamma U_Q(\phi) \Big)\,\mathrm dt + \mu \,\mathcal E_{\mathrm{win}}(\{W_j\}),
$$

其中 $\mathcal E_{\mathrm{win}}(\{W_j\})$ 为观测误差函数，例如

$$
\mathcal E_{\mathrm{win}}(\{W_j\}) = \sup_{\Gamma\in\mathcal G_T} \frac{ \big| f_\Gamma - \sum_{j=1}^K\langle f_\Gamma,W_j\rangle W_j \big|_{L^2([-W,W])} }{ |f_\Gamma|_{L^2([-W,W])} },
$$

$\mathcal G_T$ 为复杂性预算 $T$ 内的路径族。

变分问题为

$$
\min_{z(\cdot),\{W_j\}} \mathcal A_Q[z(\cdot),\{W_j\}].
$$

### 6.3 窗函数方向的极小性条件

在窗函数自由度上求变分，可得到

$$
\frac{\partial}{\partial W_j} \mathcal E_{\mathrm{win}}(\{W_j\}) = 0, \quad j=1,\dots,K,
$$

在误差函数选择为 $L^2$ 均方误差或极大误差上界时，极小化条件的解正是 PSWF/DPSS 所张成的子空间：

**命题 6.2（PSWF/DPSS 作为观测窗的变分极值）**

在上述扩展作用量中，当 $\mathcal E_{\mathrm{win}}$ 取为"在带宽 $W$、时间窗 $T$ 和路径族 $\mathcal G_T$ 上的最坏情况 $L^2$ 误差"时，极小化 $\mathcal E_{\mathrm{win}}$ 的窗函数子空间由前 $K$ 个 PSWF（连续情形）或 DPSS（离散情形）张成。

证明见附录 C：其核心是利用 PSWF/DPSS 在时间–频率双限制下的能量集中最优性。

因此，在时间–信息–复杂性变分框架下，"最优观测策略"的窗函数选择具有明确的谱结构：

* 在连续复杂性–时间限制下，选择 PSWF 型窗；
* 在离散复杂性步长下，选择 DPSS 型窗。

---

## 附录 A：PSWF/DPSS 的能量集中性证明要点

### A.1 PSWF 的变分刻画

PSWF 的关键性质是对以下变分问题的解：

在 $L^2(\mathbb R)$ 中，给定带宽 $W$，在所有带限信号

$$
\mathcal B_W = \{ f\in L^2(\mathbb R) : \widehat f(\omega)=0\ \text{对}\ |\omega|> W \}
$$

中，寻找在区间 $[-T,T]$ 上能量集中度

$$
\alpha(f) = \frac{\int_{-T}^{T} |f(t)|^2\,\mathrm dt}{\int_{-\infty}^{\infty} |f(t)|^2\,\mathrm dt}
$$

最大的 $f$。

这个变分问题的 Euler–Lagrange 方程恰是 integral operator $\mathcal K$ 的特征值方程：

$$
\mathcal K f = \lambda f,
$$

特征值 $\lambda$ 即为能量集中度 $\alpha(f)$。更一般地，对有限维子空间 $V \subset \mathcal B_W$，总集中度

$$
\sum_{f\in\text{ONB}(V)} \alpha(f)
$$

的最大化问题的解是由前 $K$ 个特征函数 $\{\psi_0,\dots,\psi_{K-1}\}$ 张成的子空间。这是 PSWF 能量集中理论的核心结论。

### A.2 DPSS 的离散类比

DPSS 情形中，积分算子被 Toeplitz 矩阵替代，其特征向量是离散时间序列，特征值表示在离散频带 $[-W,W]$ 内的能量集中度。
证明思路与连续情形平行：将能量集中度写成 Rayleigh quotient，再利用矩阵谱分解与 Courant–Fischer 最小最大原理得到"前 $K$ 个特征向量的子空间最大化总集中度"的结论。

---

## 附录 B：复杂性–时间–带宽自由度上界的证明纲要

设 $f_\Gamma(\omega)$ 为路径频谱的带限表示，在 $[-W,W]$ 上非零。自 PSWF 理论知，$\mathcal B_W$ 限制在 $[-T,T]$ 上的函数空间的有效维数为

$$
N_{\mathrm{eff}} \approx \frac{2WT}{\pi}.
$$

更精确地，PSWF 特征值 $\lambda_n$ 对大 $WT$ 有如下性质：

* 若 $n < \frac{2WT}{\pi} - c\log WT$，则 $\lambda_n \approx 1 - \mathrm e^{-c' WT}$；
* 若 $n > \frac{2WT}{\pi} + c\log WT$，则 $\lambda_n \approx \mathrm e^{-c'' WT}$.

因此，任何以前 $K$ 个 PSWF 为基的有限维子空间，对带限信号族 $\mathcal B_W$ 提供良好近似，当且仅当 $K \gtrsim 2WT/\pi$。
计算宇宙中的路径族 $\mathcal G_T$ 在统一时间刻度频域下正好对应 $\mathcal B_W$ 中的某个子集，因此上述维数估计直接给出"可用窗函数自由度数"的下界，从而得到定理 5.1 中的形式。

---

## 附录 C：窗函数选择的变分极值性

在扩展作用量中，窗函数自由度仅进入误差项 $\mathcal E_{\mathrm{win}}$。若将 $\mathcal E_{\mathrm{win}}$ 定义为

$$
\mathcal E_{\mathrm{win}}(\{W_j\}) = \sup_{f\in\mathcal B_W} \frac{ | f - \sum_{j=1}^K \langle f,W_j\rangle W_j |_{L^2([-W,W])} }{ | f|_{L^2([-W,W])} },
$$

则这是一个典型的"最佳 K 维子空间逼近"问题，其解为 $\mathcal B_W$ 上投影到前 $K$ 个主方向，即 PSWF 频谱子空间。
离散情形下，类似命题成立，DPSS 的频谱子空间是最佳 K 维逼近。
因此在变分意义上，PSWF/DPSS 窗函数族是误差泛函的全局极小解。

---

本篇通过将 PSWF/DPSS 的时间–频率集中理论与统一时间刻度–复杂性几何–信息几何结合，给出了计算宇宙中有限资源读数与误差控制的统一谱窗化框架，为后续在具体物理–工程系统上实现"统一时间刻度读数"提供了理论基础。
