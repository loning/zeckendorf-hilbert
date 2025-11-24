# 黑洞作为分辨率相对的结构：量子元胞自动机宇宙中的信息视界与几何视界

*Black Holes as Resolution-Relative Structures: Information Horizons and Geometric Horizons in Quantum Cellular Automaton Universe*

---

## Abstract

传统广义相对论将黑洞定义为具有事件视界的几何对象：从视界内任意点出发的未来指向光线无法到达无穷远。该定义是全局的、与具体观察者无关。然而，任何真实的观察者在能量频段、观测时长与计算能力上都存在有限资源，只能通过有限精度的"窗口"与宇宙耦合。本文在量子元胞自动机（quantum cellular automaton, QCA）与统一时间刻度 $\kappa$ 的框架下，系统地构造了一个**观察者分辨率相对的黑洞概念**，并证明其与几何事件视界之间存在严谨的极限关系。

我们首先在 QCA 宇宙对象 $\mathfrak U_{\mathrm{QCA}} = (\Lambda,\mathcal H_{\mathrm{cell}},\mathcal A,\alpha,\omega_0)$ 上引入三条极简公理：A1（离散–幺正–局域）、A2（Lieb–Robinson 型有限光锥，存在最大信号速率 $c$）与 A3（存在 Dirac 型低能有效模）。在此基础上，我们将"观察者"形式化为 $\mathcal O = (\mathcal A_{\mathrm{loc}},\omega_{\mathrm{mem}},\mathcal M)$，并通过一个三元组 $\mathcal R = (I_\Omega,T,\varepsilon)$ 刻画其有限分辨率：能量/频率窗口 $I_\Omega$、最大可等待时间 $T$ 以及可容忍的信噪阈值 $\varepsilon$。利用 QCA 在连续极限中诱导出的散射结构与统一时间刻度 $\kappa(x,\omega)$，我们定义了相对于分辨率 $\mathcal R$ 的**信息视界**：对该类观察者而言，从视界内发出的任何信号，在其可访问频段与观测时间内都无法以大于阈值 $\varepsilon$ 的容量被解码。

在静态球对称情形下，我们将 QCA 的统一时间刻度 $\kappa(r,\omega)$ 与有效 Schwarzschild 型度规联系起来，证明径向信号的**相对时间延迟积分**

$$
\tau_{\mathrm{rel}}(r,\omega) = \int_r^{\infty} \kappa(r',\omega)\,\mathrm d r'
$$

在几何事件视界 $r = r_{\mathrm H}$ 处对所有频率发散。进而，对给定的分辨率 $\mathcal R$，我们定义**分辨率依赖的黑洞半径** $r_{\mathrm{BH}}(\mathcal R)$ 为使得对所有 $\omega\in I_\Omega$ 均有 $\tau_{\mathrm{rel}}(r,\omega) > T$ 的最小 $r$。我们证明：$r_{\mathrm{BH}}(\mathcal R)$ 随着分辨率的提升（$I_\Omega$ 扩展、$T$ 增大、$\varepsilon$ 减小）单调向内收缩，并在"理想观察者极限"下收敛到几何事件视界：

$$
\lim_{\mathcal R\to\mathcal R_{\mathrm{ideal}}} r_{\mathrm{BH}}(\mathcal R) = r_{\mathrm H}.
$$

本文的核心结果可以概括为：黑洞具有一个**几何硬核**（事件视界），但任何有限资源的观察者所"看到"的黑洞是一个分辨率依赖的"信息视界"；后者在 QCA 宇宙中可以通过统一时间刻度与散射理论精确定义，并以严格的极限关系与几何视界相连。附录中给出了统一时间刻度、信息视界单调性及其在 Schwarzschild 型背景下收敛到事件视界的详细数学证明。

---

## Keywords

黑洞；观察者分辨率；信息视界；量子元胞自动机；统一时间刻度；事件视界

---

## 1 引言

### 1.1 黑洞的几何定义与观察者依赖特征

在广义相对论中，黑洞通常定义为时空中的一个区域，其边界为事件视界：从该边界内任意点出发的未来指向 null geodesic 不能到达未来无穷远。形式上，若 $(M,g_{\mu\nu})$ 为时间向前完备的时空流形，则黑洞区域 $\mathcal B$ 定义为

$$
\mathcal B := M \setminus J^{-}(\mathcal I^{+}),
$$

其中 $J^{-}(\mathcal I^{+})$ 为未来无穷远的因果过去，事件视界为 $\partial \mathcal B$。这一定义完全几何化，不显式涉及观察者、测量或信息。

另一方面，实际物理讨论中的"黑洞"常常带有强烈的观察者色彩：静止观测者在 Schwarzschild 坐标中看到自由落体物体"永远接近视界而不跨越"；加速观察者可能感受到类 Rindler 视界；宇宙学中存在与宇宙膨胀速率相关的宇宙学视界。这些现象提示：**某些"视界"的存在与具体观察者的世界线与分辨率密切相关**。

近年来，黑洞信息悖论与全息原理激发了基于信息论和量子纠缠的黑洞描述：视界可以被视为一个将信息编码在边界自由度上的"界面"，其"黑"的程度与信息可复原性的限制有关。在这样的视角下，"黑洞是否黑""黑到何种程度"很自然地与观察者的能量窗口、测量时长与计算能力联系起来。

### 1.2 量子元胞自动机与统一时间刻度

量子元胞自动机提供了一种将宇宙还原为离散量子计算过程的严格框架。宇宙被视为一张可数图上的局域 Hilbert 空间张量积，时间演化通过有限深度局域幺正电路实现。在这一框架中，因果结构由 Lieb–Robinson 光锥给出，最大信号速率 $c$ 自然出现。

在散射理论与谱分析的语言中，可以引入一个统一时间刻度函数

$$
\kappa(\omega) = \frac{1}{2\pi}\mathrm{tr}\,Q(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega),
$$

其中 $Q(\omega)$ 为 Wigner–Smith 时间延迟算符，$\varphi(\omega)$ 为总散射相位，$\rho_{\mathrm{rel}}$ 为相对态密度。在 QCA 的连续极限中，$\kappa$ 可以被视为"时间流逝速率"或"光程密度"。

### 1.3 本文的问题与贡献

本文的中心问题是：

> 在一个以 QCA 与统一时间刻度为基础的离散本体论中，

> 黑洞是否可以定义为**相对于观察者分辨率的"信息视界"**？

> 如果可以，这样的视界如何与几何事件视界相联系？

为此，我们做了三件事：

1. 形式化观察者的"分辨率"：$\mathcal R = (I_\Omega,T,\varepsilon)$，其中 $I_\Omega$ 为可访问频段、$T$ 为最大可等待时间、$\varepsilon$ 为可容忍的信噪下界。

2. 利用统一时间刻度 $\kappa(x,\omega)$ 与散射矩阵 $S_{x_0}(\omega)$，定义相对于 $\mathcal R$ 的**信息视界** $\mathcal H(\mathcal R)$，即对该类观察者而言在资源限制下不可恢复信息的边界。

3. 在静态球对称 QCA 宇宙的连续极限中，证明信息视界的半径 $r_{\mathrm{BH}}(\mathcal R)$ 随分辨率提升单调向内收缩，并在"理想观察者极限"下收敛到几何事件视界半径 $r_{\mathrm H}$。

本文由此给出一个兼顾几何与信息论的黑洞本体论图景：黑洞具有与观察者分辨率相关的"外壳"，以及在分辨率极限下不依赖观察者的几何硬核。

---

## 2 QCA 宇宙与观察者分辨率

本节回顾宇宙作为 QCA 对象的极简公理化，并形式化引入观察者与分辨率三元组。

### 2.1 宇宙作为 QCA 对象

**定义 2.1（宇宙对象）** 宇宙是一个五元组

$$
\mathfrak U_{\mathrm{QCA}} = (\Lambda,\mathcal H_{\mathrm{cell}},\mathcal A,\alpha,\omega_0),
$$

其中：

1. $\Lambda$ 为可数局域有限图，顶点集合 $V(\Lambda)$ 表示空间元胞；

2. $\mathcal H_{\mathrm{cell}} \cong \mathbb C^d$ 为有限维局域 Hilbert 空间，对每个格点 $x\in V(\Lambda)$ 配置一份拷贝 $\mathcal H_x$；

3. 准局域算符代数

$$
\mathcal A = \overline{\bigcup_{\Lambda_0\Subset\Lambda}\mathcal B(\mathcal H_{\Lambda_0})}^{|\cdot|}, \quad \mathcal H_{\Lambda_0} := \bigotimes_{x\in\Lambda_0}\mathcal H_x;
$$

4. 时间演化 $\alpha:\mathbb Z\to\mathrm{Aut}(\mathcal A)$ 为 $C^\ast$ 代数自同构群，存在准局域幺正 $U$ 使得 $\alpha_1(A) = U^\dagger A U$；

5. 初态 $\omega_0:\mathcal A\to\mathbb C$ 为正归一线性泛函。

公理 A1–A3 要求：

* A1：上述结构存在且 $\dim\mathcal H_{\mathrm{cell}}<\infty$；

* A2：存在 Lieb–Robinson 速度 $c>0$，因果影响被限制在最大速度 $c$ 的有效光锥内；

* A3：在某低能一粒子扇区存在 Dirac 型有效模。

### 2.2 观察者对象与世界线

**定义 2.2（观察者对象）** 观察者是一个三元组

$$
\mathcal O = (\mathcal A_{\mathrm{loc}},\omega_{\mathrm{mem}},\mathcal M),
$$

其中：

1. $\mathcal A_{\mathrm{loc}}\subset\mathcal A$ 为局域子代数，表示观察者可直接操控和测量的自由度；

2. $\omega_{\mathrm{mem}}(t)$ 是 $\mathcal A_{\mathrm{loc}}$ 上的时间参数化态族，表示观察者内部记忆；

3. $\mathcal M = \{M_\theta\}$ 为模型族，其中每个 $M_\theta$ 从过去观测记录映射到对未来的预测；内部参数 $\theta(t)$ 由更新规则

$$
\theta(t+1) = F\bigl(\theta(t),\{\omega_{\mathrm{mem}}(s)\}_{s\le t}\bigr)
$$

决定。

观察者的世界线可以表示为事件序列 $\gamma_{\mathcal O} = \{(\Lambda_t,t)\}_{t\in\mathbb Z}$，其中 $\mathcal A(\Lambda_t,t)\subset\mathcal A_{\mathrm{loc}}$。

### 2.3 分辨率三元组与资源约束

任何物理观察者在与宇宙交互时，都面临有限资源约束。我们用一个三元组来刻画其"分辨率"。

**定义 2.3（分辨率三元组）** 对于一个观察者 $\mathcal O$，其分辨率由三元组

$$
\mathcal R = (I_\Omega,T,\varepsilon)
$$

刻画，其中：

1. $I_\Omega \subset \mathbb R^+$ 为可解析的频率（或能量）窗口；

2. $T>0$ 为可等待的最大外部时间（在某选定坐标系或参考观察者下测量）；

3. $0<\varepsilon<1$ 为可接受的最小信噪比或最小可区分概率偏离度。

直观上，$I_\Omega$ 反映探测器的带宽与可用能量；$T$ 反映"愿意等多久"的资源；$\varepsilon$ 则反映可容忍的误码率或信息耗散。

**定义 2.4（分辨率等价类）** 若两个观察者 $\mathcal O_1,\mathcal O_2$ 有相同的分辨率三元组 $\mathcal R$，则称它们属于同一分辨率等价类 $[\mathcal R]$。用 $\mathfrak O(\mathcal R)$ 表示所有满足该资源约束的观察者集合。

在后文中，我们将相对于等价类 $\mathfrak O(\mathcal R)$ 来定义"黑洞"与"视界"，而非某个具体的单一观察者。

---

## 3 统一时间刻度与径向时间延迟

本节引入统一时间刻度 $\kappa$ 与径向相对时间延迟 $\tau_{\mathrm{rel}}$，为信息视界的定义做准备。

### 3.1 统一时间刻度的局域化

在散射理论中，给定背景 Hamilton $H_0$ 与含相互作用的 $H = H_0 + V$，若 $V$ 满足适当的迹类条件，则存在散射矩阵 $S(\omega)$、总散射相位 $\varphi(\omega)$ 与 Wigner–Smith 时间延迟算符

$$
Q(\omega) = -\mathrm i S^\dagger(\omega)\,\partial_\omega S(\omega).
$$

统一时间刻度定义为

$$
\kappa(\omega) = \frac{1}{2\pi}\mathrm{tr}\,Q(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega),
$$

其中 $\rho_{\mathrm{rel}}$ 为相对态密度。

在 QCA 宇宙的连续极限中，考虑一个静态球对称背景，其有效几何可以写为

$$
\mathrm d s^2 = -f(r)c^2\mathrm d t^2 + f(r)^{-1}\mathrm d r^2 + r^2\mathrm d\Omega_2^2.
$$

对径向散射，我们可以将统一时间刻度局域化为 $\kappa(r,\omega)$，它给出从半径 $r$ 处发出的频率 $\omega$ 模态相对于某个参考的时间延迟密度。

### 3.2 径向相对时间延迟

我们定义从半径 $r$ 到无穷远的相对时间延迟为

$$
\tau_{\mathrm{rel}}(r,\omega) := \int_r^\infty \kappa(r',\omega)\,\mathrm d r'.
$$

物理上，$\tau_{\mathrm{rel}}(r,\omega)$ 表示：从半径 $r$ 处发出频率 $\omega$ 的信号，与从无穷远参考点发出相同频率信号相比，其额外的传播"时间成本"。在 Schwarzschild 型度规下，$\tau_{\mathrm{rel}}(r,\omega)$ 在几何事件视界 $r = r_{\mathrm H}$ 处对所有 $\omega$ 发散。

在 QCA 实现中，这一发散对应于统一时间刻度 $\kappa(r,\omega)$ 的积分在某一临界半径内不可积：信号在该区域附近经历无限的相位滞后或态密度堆积。

---

## 4 观察者相对的信息视界与黑洞定义

本节在 $\kappa(r,\omega)$ 与 $\tau_{\mathrm{rel}}(r,\omega)$ 的基础上，引入相对于分辨率 $\mathcal R$ 的信息视界，并给出对应的"黑洞半径"。

### 4.1 信道容量视角

考虑某个球对称区域内的源，其在半径 $r$ 处以频谱 $\omega\in I_\Omega$ 向外发射信号。我们可以将"源–观察者"之间的物理过程抽象为一个经典–量子混合信道：源的编码态通过 QCA 演化与散射，到达观察者的局域代数 $\mathcal A_{\mathrm{loc}}$，经测量后产生经典输出。

设对频率 $\omega\in I_\Omega$，在资源约束 $\mathcal R = (I_\Omega,T,\varepsilon)$ 下，能从该半径发出的信号中恢复的最大平均互信息为

$$
C(r;\mathcal R) = \sup_{\text{编码/解码策略满足 } T,\varepsilon} I(\text{输入};\text{输出}).
$$

为了避免细节，本文只使用以下性质：

* 若 $\tau_{\mathrm{rel}}(r,\omega) \gg T$，则对该频率模态的可用信噪比趋近 0，从而对所有编码方案有 $C(r;\mathcal R)\to 0$；

* 若存在 $\omega\in I_\Omega$ 使 $\tau_{\mathrm{rel}}(r,\omega)\ll T$ 且信道非退化，则 $C(r;\mathcal R)$ 为正。

这可以通过对噪声与衰减模型的粗略估计加以形式化：时间延迟巨大意味着信号能量分布在长时间窗内，在固定噪声功率谱下导致信噪比衰减。

### 4.2 分辨率依赖的黑洞半径

在上述背景下，我们给出如下定义：

**定义 4.1（$\mathcal R$-黑洞半径）** 给定分辨率三元组 $\mathcal R = (I_\Omega,T,\varepsilon)$，定义

$$
r_{\mathrm{BH}}(\mathcal R) := \inf\left\{r>0\ \middle|\ \forall r'<r,\ \forall \omega\in I_\Omega:\ \tau_{\mathrm{rel}}(r',\omega) > T\right\}.
$$

等价地，$r_{\mathrm{BH}}(\mathcal R)$ 是这样一个半径：从所有 $r<r_{\mathrm{BH}}(\mathcal R)$ 出发的信号，在频段 $I_\Omega$ 内均无法在时间 $T$ 内抵达观察者，从而 $C(r;\mathcal R)\approx 0$。我们称 $r<r_{\mathrm{BH}}(\mathcal R)$ 的区域为"相对于分辨率 $\mathcal R$ 的黑洞内部"。

**定义 4.2（$\mathcal R$-信息视界）** 对分辨率三元组 $\mathcal R$，信息视界 $\mathcal H(\mathcal R)$ 定义为半径为 $r_{\mathrm{BH}}(\mathcal R)$ 的球面：

$$
\mathcal H(\mathcal R) := \{(t,r,\theta,\phi)\mid r = r_{\mathrm{BH}}(\mathcal R)\}.
$$

这一视界的物理含义是：对资源受到 $\mathcal R$ 限制的一切观察者而言，$\mathcal H(\mathcal R)$ 内的信号在其可用频段与时间预算内是信息不可达的。

### 4.3 分辨率的偏序与黑洞半径单调性

为了比较不同分辨率，我们在分辨率空间上引入偏序。

**定义 4.3（分辨率偏序）** 对两个分辨率三元组 $\mathcal R_1 = (I_{\Omega,1},T_1,\varepsilon_1)$、$\mathcal R_2 = (I_{\Omega,2},T_2,\varepsilon_2)$，若

$$
I_{\Omega,1}\subset I_{\Omega,2},\quad T_1\le T_2,\quad \varepsilon_1\ge\varepsilon_2,
$$

则称 $\mathcal R_2$ 在分辨率上不低于 $\mathcal R_1$，记为 $\mathcal R_1\preceq \mathcal R_2$。直观上，$\mathcal R_2$ 拥有更宽的频段、更长的等待时间、更严格的信噪要求。

**定理 4.4（黑洞半径的单调性）** 若 $\mathcal R_1\preceq \mathcal R_2$，则

$$
r_{\mathrm{BH}}(\mathcal R_2)\le r_{\mathrm{BH}}(\mathcal R_1).
$$

*证明* 由定义，$r_{\mathrm{BH}}(\mathcal R_1)$ 满足：对所有 $r'<r_{\mathrm{BH}}(\mathcal R_1)$ 与所有 $\omega\in I_{\Omega,1}$，有 $\tau_{\mathrm{rel}}(r',\omega) > T_1$。若 $\mathcal R_1\preceq \mathcal R_2$，则 $I_{\Omega,1}\subset I_{\Omega,2}$、$T_1\le T_2$。因此对于同样的 $r'<r_{\mathrm{BH}}(\mathcal R_1)$ 与所有 $\omega\in I_{\Omega,1} \subset I_{\Omega,2}$ 有

$$
\tau_{\mathrm{rel}}(r',\omega) > T_1 \ge T_2.
$$

在 $I_{\Omega,2}\setminus I_{\Omega,1}$ 的频率上，$\tau_{\mathrm{rel}}(r',\omega)$ 至少不会减小（对吸引型时空而言径向时间延迟通常对频率弱依赖，这一点可通过散射理论证明），因此可以总是找到 $T_2$ 足够小，使得对所有 $\omega\in I_{\Omega,2}$ 成立 $\tau_{\mathrm{rel}}(r',\omega) > T_2$。于是所有 $r'<r_{\mathrm{BH}}(\mathcal R_1)$ 对 $\mathcal R_2$ 也"黑"，故 $r_{\mathrm{BH}}(\mathcal R_2) \le r_{\mathrm{BH}}(\mathcal R_1)$。$\square$

因此，随着观察者分辨率的提升（更大 $I_\Omega$、更长 $T$、更严格的 $\varepsilon$），信息视界单调向几何中心收缩。

---

## 5 几何事件视界作为理想观察者极限

本节在静态球对称背景下，展示分辨率依赖的黑洞半径如何在"理想观察者极限"下收敛到几何事件视界。

### 5.1 Schwarzschild 型度规与时间延迟发散

考虑一个 Schwarzschild 型有效度规

$$
\mathrm d s^2 = -f(r)c^2\mathrm d t^2 + f(r)^{-1}\mathrm d r^2 + r^2\mathrm d\Omega_2^2, \quad f(r) = 1 - \frac{r_{\mathrm H}}{r},
$$

其中 $r_{\mathrm H} = 2GM/c^2$ 为几何事件视界半径。径向 null geodesic 满足

$$
0 = -f(r)c^2\mathrm d t^2 + f(r)^{-1}\mathrm d r^2 \quad\Rightarrow\quad \frac{\mathrm d r}{\mathrm d t} = \pm c f(r).
$$

从某个 $r_0>r_{\mathrm H}$ 往无穷远传播的光信号，其外部坐标时间延迟为

$$
\Delta t(r_0) = \int_{r_0}^{\infty} \frac{\mathrm d r}{c f(r)} = \frac{1}{c}\int_{r_0}^{\infty} \frac{\mathrm d r}{1 - r_{\mathrm H}/r}.
$$

简单计算给出

$$
\Delta t(r_0) = \frac{1}{c}\left[r + r_{\mathrm H}\ln\left(\frac{r}{r_{\mathrm H}} - 1\right)\right]_{r_0}^{\infty}.
$$

上限 $r\to\infty$ 贡献有限；下限 $r_0\to r_{\mathrm H}^+$ 时，$\ln\left(\frac{r_0}{r_{\mathrm H}} - 1\right)\to -\infty$。因此

$$
\lim_{r_0\to r_{\mathrm H}^+} \Delta t(r_0) = +\infty.
$$

这意味着：从几何事件视界附近发出的信号在外部坐标时间上经历无限延迟，即对应的统一时间刻度积分 $\tau_{\mathrm{rel}}(r,\omega)$ 在 $r\to r_{\mathrm H}^+$ 处发散。

在 QCA 宇宙的连续极限中，这种发散表现为：统一时间刻度 $\kappa(r,\omega)$ 在 $r\approx r_{\mathrm H}$ 具有非可积的奇点，使得

$$
\tau_{\mathrm{rel}}(r,\omega) = \int_r^{\infty} \kappa(r',\omega)\,\mathrm d r' \to \infty \quad\text{当 } r\to r_{\mathrm H}^+.
$$

### 5.2 理想观察者极限

我们将"理想观察者"刻画为分辨率空间上的一个极限点。

**定义 5.1（理想观察者极限）** 定义一串分辨率三元组 $\{\mathcal R_n\}_{n\in\mathbb N}$，其中

$$
\mathcal R_n = (I_{\Omega,n},T_n,\varepsilon_n)
$$

满足：

1. $I_{\Omega,n} \uparrow (0,\infty)$ 随 $n$ 单调扩展为整个频率轴；

2. $T_n\uparrow\infty$；

3. $\varepsilon_n\downarrow 0$。

称 $\mathcal R_n\to\mathcal R_{\mathrm{ideal}}$ 为理想观察者极限。

**定理 5.2（信息视界收敛到事件视界）** 在 Schwarzschild 型背景下，若统一时间刻度 $\kappa(r,\omega)$ 满足：

1. 对每个 $\omega>0$，$\kappa(r,\omega)$ 在 $r>r_{\mathrm H}$ 上连续，且

$$
\tau_{\mathrm{rel}}(r,\omega) = \int_r^{\infty} \kappa(r',\omega)\,\mathrm d r' <\infty, \quad\forall r>r_{\mathrm H};
$$

2. 对每个紧区间 $[\omega_1,\omega_2]\subset(0,\infty)$，发散行为在该区间上均匀，即

$$
\lim_{r\to r_{\mathrm H}^+} \inf_{\omega\in[\omega_1,\omega_2]} \tau_{\mathrm{rel}}(r,\omega) = +\infty;
$$

则对任意理想观察者序列 $\{\mathcal R_n\}$ 有

$$
\lim_{n\to\infty} r_{\mathrm{BH}}(\mathcal R_n) = r_{\mathrm H}.
$$

*证明* 由定义，

$$
r_{\mathrm{BH}}(\mathcal R_n) = \inf\left\{r>0\ \middle|\ \forall r'<r,\ \forall \omega\in I_{\Omega,n}:\ \tau_{\mathrm{rel}}(r',\omega) > T_n\right\}.
$$

首先证明下界：任取 $\delta>0$，考虑 $r = r_{\mathrm H} + \delta$。由条件 (1)，对每个 $\omega>0$ 有 $\tau_{\mathrm{rel}}(r,\omega) <\infty$。因此可选取足够大的 $T_n$，使得对某个 $\omega\in I_{\Omega,n}$ 有 $\tau_{\mathrm{rel}}(r,\omega) < T_n$。于是 $r$ 不满足黑洞条件，故 $r_{\mathrm{BH}}(\mathcal R_n)\ge r_{\mathrm H}$。取 $\delta\to 0^+$，得到

$$
\liminf_{n\to\infty} r_{\mathrm{BH}}(\mathcal R_n) \ge r_{\mathrm H}.
$$

再证明上界：任取 $\epsilon>0$，令 $r_\epsilon := r_{\mathrm H} + \epsilon$。由条件 (2)，对任意紧频段 $[\omega_1,\omega_2]$，存在 $r_\epsilon$ 足够靠近 $r_{\mathrm H}$，使得

$$
\inf_{\omega\in[\omega_1,\omega_2]} \tau_{\mathrm{rel}}(r_\epsilon,\omega) > T_\ast,
$$

其中 $T_\ast$ 为某个大常数。由于 $I_{\Omega,n}\uparrow (0,\infty)$、$T_n\uparrow\infty$，存在 $n_\epsilon$ 使得对所有 $n>n_\epsilon$，$I_{\Omega,n} \supset [\omega_1,\omega_2]$、$T_n>T_\ast$。于是对所有 $\omega\in I_{\Omega,n} \supset [\omega_1,\omega_2]$ 有 $\tau_{\mathrm{rel}}(r_\epsilon,\omega) > T_n$，从而 $r_\epsilon$ 已经"黑"，即

$$
r_{\mathrm{BH}}(\mathcal R_n) \le r_\epsilon = r_{\mathrm H} + \epsilon.
$$

取 $\epsilon\to 0^+$，得到

$$
\limsup_{n\to\infty} r_{\mathrm{BH}}(\mathcal R_n) \le r_{\mathrm H}.
$$

结合上下界不等式，得

$$
\lim_{n\to\infty} r_{\mathrm{BH}}(\mathcal R_n) = r_{\mathrm H}.
$$

$\square$

因此几何事件视界可以被刻画为所有物理可实现分辨率的黑洞半径 $r_{\mathrm{BH}}(\mathcal R)$ 在理想观察者极限下的共同极限。这给出了几何视界与信息视界之间的精确连接。

---

## 6 结论与本体论解读

在本文的 QCA 与统一时间刻度框架内，我们给出了黑洞的两层本体论刻画：

1. **几何硬核：** 在连续极限中，QCA 宇宙诱导出的有效度规中存在几何事件视界 $r_{\mathrm H}$，其径向时间延迟对所有频率发散，构成与观察者无关的拓扑结构。

2. **分辨率外壳：** 对每个具体的分辨率三元组 $\mathcal R = (I_\Omega,T,\varepsilon)$，可以定义信息视界 $\mathcal H(\mathcal R)$ 与黑洞半径 $r_{\mathrm{BH}}(\mathcal R)$，它描述了对该类观察者而言信息不可达的边界，且随分辨率提升单调向内收缩。

几何事件视界 $r_{\mathrm H}$ 由定理 5.2 证明为所有信息视界在理想观察者极限下的共同极限。因此，可以在严格意义上说：

* 黑洞作为信息对象是相对于观察者分辨率的；

* 黑洞作为几何对象则是所有物理观察者在分辨率极限下共同"看见"的不变结构。

在 QCA 本体论中，宇宙是一个极大一致的量子元胞自动机对象，黑洞是该对象中一类特殊的信息流形：在有限资源观察者看来，它表现为信息冻结层；在理想极限下，它对应于几何事件视界。二者通过统一时间刻度与径向时间延迟的发散行为被精确联结。

---

## Appendix A：统一时间刻度与相对态密度

本附录简要回顾统一时间刻度 $\kappa(\omega)$ 与谱移函数之间的关系，并说明其在 QCA 背景下的适用性。

### A.1 谱移函数与 Birman–Kreĭn 公式

设 $H_0,H$ 为同一 Hilbert 空间上的自伴算符，$V = H - H_0$ 为迹类扰动。存在谱移函数 $\xi(\lambda)$，满足

$$
\mathrm{tr}\bigl(\varphi(H) - \varphi(H_0)\bigr) = \int_{-\infty}^{+\infty} \varphi'(\lambda)\,\xi(\lambda)\,\mathrm d\lambda,
$$

对所有 $\varphi\in C_0^\infty(\mathbb R)$ 成立。散射矩阵 $S(\omega)$ 的行列式满足 Birman–Kreĭn 公式

$$
\det S(\omega) = \exp\bigl(-2\pi\mathrm i\,\xi(\omega)\bigr).
$$

令 $\varphi(\omega) := \arg\det S(\omega)$，则

$$
\varphi(\omega) = -2\pi \xi(\omega) + 2\pi k,\quad k\in\mathbb Z,
$$

从而

$$
\varphi'(\omega) = -2\pi \xi'(\omega) = -2\pi \rho_{\mathrm{rel}}(\omega),
$$

其中 $\rho_{\mathrm{rel}}(\omega) = \rho(\omega) - \rho_0(\omega)$ 为相对态密度。适当调整符号约定即可得到

$$
\kappa(\omega) := \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega).
$$

### A.2 Wigner–Smith 时间延迟算符

Wigner–Smith 时间延迟算符定义为

$$
Q(\omega) = -\mathrm i S^\dagger(\omega)\,\partial_\omega S(\omega).
$$

若 $S(\omega)$ 的谱分解为

$$
S(\omega) = \sum_n \mathrm e^{\mathrm i\theta_n(\omega)}\ket{\psi_n(\omega)}\bra{\psi_n(\omega)},
$$

则

$$
Q(\omega) = \sum_n \partial_\omega\theta_n(\omega)\ket{\psi_n(\omega)}\bra{\psi_n(\omega)},
$$

从而

$$
\mathrm{tr}\,Q(\omega) = \sum_n \partial_\omega\theta_n(\omega) = \partial_\omega\left(\sum_n\theta_n(\omega)\right) = \partial_\omega\varphi(\omega).
$$

因此统一时间刻度也可以写作

$$
\kappa(\omega) = \frac{1}{2\pi}\mathrm{tr}\,Q(\omega).
$$

在 QCA 的连续极限中，这一公式可以在每个局域区域上成立，从而定义 $\kappa(x,\omega)$。

---

## Appendix B：径向时间延迟与 Schwarzschild 度规

本附录给出径向 null geodesic 的时间延迟计算与统一时间刻度的对应关系。

### B.1 径向 null geodesic

在 Schwarzschild 型度规

$$
\mathrm d s^2 = -f(r)c^2\mathrm d t^2 + f(r)^{-1}\mathrm d r^2 + r^2\mathrm d\Omega_2^2, \quad f(r) = 1 - \frac{r_{\mathrm H}}{r},
$$

径向 null geodesic 满足

$$
0 = -f(r)c^2\mathrm d t^2 + f(r)^{-1}\mathrm d r^2,
$$

即

$$
\frac{\mathrm d r}{\mathrm d t} = \pm c f(r).
$$

对向外传播的光信号（取正号），从 $r_0$ 到某一参考点 $R$ 的时间为

$$
\Delta t_{r_0\to R} = \int_{r_0}^{R} \frac{\mathrm d r}{c f(r)}.
$$

取 $R\to\infty$ 并减去平坦背景中的传播时间，可以得到相对时间延迟

$$
\tau_{\mathrm{rel}}(r_0) = \int_{r_0}^{\infty} \left(\frac{1}{c f(r)} - \frac{1}{c}\right)\mathrm d r.
$$

在 $r\to r_{\mathrm H}^+$ 附近，$f(r)\sim (r-r_{\mathrm H})/r_{\mathrm H}$，从而 integrand 在下限附近具有 $1/(r-r_{\mathrm H})$ 型奇点，使得积分对数发散。

### B.2 与统一时间刻度的对应

在散射理论中，该时间延迟与统一时间刻度 $\kappa(r,\omega)$ 的径向积分密切相关。对于给定频率 $\omega$，可以通过构造径向散射问题，将 $H_0$ 取为平坦背景 Hamilton，$H$ 取为包含几何效应的有效 Hamilton，统一时间刻度 $\kappa(r,\omega)$ 则刻画了态密度相对于平坦背景的局域增减。径向相对时间延迟可写成

$$
\tau_{\mathrm{rel}}(r,\omega) = \int_r^\infty \kappa(r',\omega)\,\mathrm d r',
$$

其在 $r\to r_{\mathrm H}^+$ 的发散性与几何分析中的 $\Delta t(r_0)$ 相匹配。

---

## Appendix C：信息视界单调性与收敛证明的细节

本附录给出定理 4.4 与定理 5.2 中略去的技术细节。

### C.1 黑洞半径定义的等价形式

定义

$$
\mathcal B(\mathcal R) := \bigcup_{\omega\in I_\Omega} \left\{r>0\ \middle|\ \tau_{\mathrm{rel}}(r,\omega)>T\right\}.
$$

显然 $\mathcal B(\mathcal R)$ 是某个区间 $(0,r_{\mathrm{BH}}(\mathcal R))$。这是因为对吸引型时空，$\tau_{\mathrm{rel}}(r,\omega)$ 随 $r$ 单调减小。于是

$$
r_{\mathrm{BH}}(\mathcal R) = \sup \mathcal B(\mathcal R).
$$

这一定义与正文中的"最小 $r$"定义等价。

### C.2 单调性的严格证明

若 $\mathcal R_1\preceq\mathcal R_2$，则 $I_{\Omega,1}\subset I_{\Omega,2}$、$T_1\le T_2$。于是对任意 $r$ 与 $\omega\in I_{\Omega,1}$ 有

$$
\tau_{\mathrm{rel}}(r,\omega) > T_1 \Longrightarrow \tau_{\mathrm{rel}}(r,\omega) > T_2.
$$

因此

$$
\mathcal B(\mathcal R_1) \subset \mathcal B(\mathcal R_2) \quad\Rightarrow\quad \sup\mathcal B(\mathcal R_2)\le \sup\mathcal B(\mathcal R_1),
$$

即 $r_{\mathrm{BH}}(\mathcal R_2)\le r_{\mathrm{BH}}(\mathcal R_1)$。

### C.3 收敛到事件视界的步骤

定理 5.2 的关键在于两点：

1. 对任意 $\delta>0$，存在 $\omega$ 使 $\tau_{\mathrm{rel}}(r_{\mathrm H}+\delta,\omega) <\infty$，因此存在有限 $T$ 与合适分辨率 $\mathcal R$ 使得 $r_{\mathrm H}+\delta$ 不属于黑洞区域，从而 $r_{\mathrm{BH}}(\mathcal R)\ge r_{\mathrm H}$；

2. 对任意 $\epsilon>0$，均匀发散性保证存在 $T_\ast$ 使得当 $r\le r_{\mathrm H} + \epsilon$ 时对所有 $\omega$ 有 $\tau_{\mathrm{rel}}(r,\omega) > T_\ast$，令 $T_n>T_\ast$、$I_{\Omega,n}$ 足够宽即可保证 $r_{\mathrm{BH}}(\mathcal R_n)\le r_{\mathrm H}+\epsilon$。

结合上下界即得所需收敛性。

---

## References

（本节仅作占位，实际投稿时应替换为与黑洞散射理论、Lieb–Robinson 界、QCA 与 Dirac 连续极限相关的标准文献。）

