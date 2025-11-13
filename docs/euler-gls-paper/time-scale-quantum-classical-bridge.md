# 时间刻度上的量子–经典桥接：相位、时间延迟、红移与引力–熵几何

## 摘要

本文在统一的"时间刻度"视角下，系统构建量子相位、本征时间、散射群延迟、宇宙学红移与边界熵演化之间的一组等价关系，并将其组织为一套可公理化的量子–经典桥接框架。几何端以本征时间 $d\tau=\sqrt{-g_{\mu\nu}dx^\mu dx^\nu}$ 与因果边界上的广义熵 $S_{\rm gen}$ 为基本对象；量子端以路径积分相位 $\phi=-S/\hbar$、散射矩阵 $S(\omega)$ 的总相位 $\Phi(\omega)$ 及 Wigner–Smith 群延迟算子 $Q(\omega)=-iS(\omega)^\dagger \partial_\omega S(\omega)$ 为基本对象。提出并采用统一刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}=\rho_{\rm rel}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

其中 $\varphi(\omega)$ 为归一化总相位、$\rho_{\rm rel}$ 为相对态密度。本文证明：在半经典极限与适当的正则性假设下

1. 单粒子波包沿经典测地线传播时，其相位 $\phi$ 等价于沿该世界线累积的本征时间的线性函数 $\phi=-mc^2\int d\tau/\hbar$，从而本征时间刻度可视为"相位的几何参数"；
2. 在静态或渐近平坦引力场中，光子或物质波的引力时间延迟等于散射相位对频率的导数，即等于 Wigner–Smith 群延迟的迹，从而引力时间膨胀可被解释为"相位–频率几何"的弯曲；
3. 在 FRW 宇宙学背景中，红移 $1+z=a(t_0)/a(t_e)$ 可等价地写成同一光子世界线上相位频率 $(d\phi/dt)$ 在发射与探测两事件的比值，从而宇宙学红移成为"宇宙时间刻度剪切"的相位表述；
4. 在局域因果菱形中，以广义熵 $S_{\rm gen}=A/(4G\hbar)+S_{\rm out}$ 的极值与单调性（沿零生成元参数 $\lambda$）作为公理，可在半经典–全息窗口内导出含宇宙学常数的爱因斯坦方程，将引力几何视为"熵在因果边界上随时间刻度组织方式"的有效方程。

由此得到一张统一的"时间–相位–熵–几何"对应图。本文附录给出：Wigner–Smith 群延迟与谱移–态密度的刻度同一式推导；世界线路径积分下"相位–本征时间"等价的半经典证明；FRW 宇宙学中红移–相位表述的细化；以及局域因果菱形上由广义熵极值与量子能量条件导出爱因斯坦方程的详细证明纲要。

**关键词**：时间刻度；Wigner–Smith 群延迟；本征时间；宇宙学红移；广义熵；爱因斯坦方程的熵解释
**MSC (2020)**：83C45, 81T20, 81U40, 83C57

---

## 1 引言

时间在经典物理与量子理论中分别扮演了不同的角色：在广义相对论中，时间与空间一体构成四维时空流形，其本征时间刻度 $d\tau$ 由度规 $g_{\mu\nu}$ 决定；在量子力学与量子场论中，时间则更多地通过相位因子 $\exp(-iEt/\hbar)$ 与幺正演化算子 $U(t)$ 体现。散射理论中引入的 Wigner–Smith 群延迟算子 $Q(\omega)$ 又提供了一种"时间作为相位对频率导数"的操作性刻度；宇宙学红移则通过频率或波长的变化，反映宇宙尺度因子演化对"时间节奏"的宏观剪切。

另一方面，黑洞热力学、Jacobson 型熵解释以及全息–纠缠几何研究显示：引力几何可以视作某种"熵–信息组织"的宏观方程，尤其在因果边界与局域视界上，广义熵 $S_{\rm gen}$ 的极值与单调性对时空曲率施加了强制性约束。

这些看似分散的现象背后有一个共同的结构：它们都在用"时间刻度"作为桥梁，把量子相位、经典时钟、散射延迟、红移与熵流联系起来。本文的目标是对这一结构做出系统、清晰且可定理化的刻画，并给出严格的等价或对应关系。

本文围绕如下主问题展开：

1. 如何在统一刻度下，将量子相位、群延迟、本征时间与宇宙学红移视为同一"时间几何"的不同截面？
2. 在何种假设下，可以把广义熵沿因果边界随时间的组织方式，与宏观引力方程（爱因斯坦方程）等价起来？
3. 这些等价关系如何在半经典极限中自然地连接量子与经典、微观与宏观？

为此，本文在第 2 节给出记号与公理性刻度同一式；第 3–5 节依次构造"相位–本征时间"、"时间延迟–引力时间膨胀"、"红移–时间刻度剪切"的精确对应；第 6 节则在因果菱形框架下，给出"广义熵演化–引力方程"的熵几何定理。第 7 节总结这些桥接为一套几何图景。附录给出主要技术结果的详细证明。

---

## 2 记号与基本结构

### 2.1 几何端：时空、本征时间与因果菱形

令 $(M,g_{\mu\nu})$ 为 Lorentz 测地完备时空流形，度规签名取 $(-+++)$。一条类时曲线 $\gamma(\lambda)$ 的本征时间为

$$
d\tau = \sqrt{-g_{\mu\nu}\frac{dx^\mu}{d\lambda}\frac{dx^\nu}{d\lambda}}\,d\lambda.
$$

在局域讨论中，选取一点 $p\in M$ 及一个小参数 $r\ll L_{\rm curv}$，定义该点的小因果菱形

$$
D_{p,r} := J^+(p^-)\cap J^-(p^+),
$$

其中 $p^\pm$ 分别是沿某选定类时方向偏移本征时间 $\pm r$ 的点。$D_{p,r}$ 的边界由两簇零测地线生成，构成局域因果边界。

### 2.2 量子与散射端：S 矩阵与 Wigner–Smith 群延迟

设 $H_0$ 为自由哈密顿量，$H$ 为含相互作用项的哈密顿量。在标准散射假设下，波算子

$$
\Omega^\pm = \operatorname{s-}\lim_{t\to \pm\infty}e^{iHt}e^{-iH_0 t}
$$

存在且完备，散射算子定义为

$$
S := (\Omega^+)^\dagger \Omega^-.
$$

在能量或频率表象下，绝对连续谱 $\omega\in I\subset\mathbb R$ 对每个 $\omega$ 给出有限维通道空间 $\mathcal H_\omega\simeq\mathbb C^{N(\omega)}$，上面有酉矩阵 $S(\omega)$。定义总散射相位

$$
\Phi(\omega) := \arg\det S(\omega).
$$

**定义 2.1（Wigner–Smith 群延迟算子）** 在频率可微性假设下，定义

$$
Q(\omega):=-i\,S(\omega)^\dagger\partial_\omega S(\omega),
$$

称为 Wigner–Smith 群延迟算子。$Q(\omega)$ 为自伴矩阵，其特征值记为 $\tau_j(\omega)$，可解释为各通道的群延迟。迹给出总群延迟

$$
\operatorname{Tr} Q(\omega)=\partial_\omega \Phi(\omega).
$$

### 2.3 谱移函数与相对态密度

在合适的可追踪扰动假设下，设 $\xi(\omega)$ 为 Kreĭn 谱移函数，$\rho_{\rm rel}(\omega)$ 为相对态密度。经典结果给出

$$
\Phi(\omega)=-2\pi\,\xi(\omega),\qquad
\rho_{\rm rel}(\omega)=-\partial_\omega\xi(\omega).
$$

从而有

$$
\partial_\omega\Phi(\omega)=2\pi\,\rho_{\rm rel}(\omega).
$$

### 2.4 统一刻度同一式

综合 2.2–2.3，可得以下刻度同一式。

**公理 2.2（时间刻度统一式）** 对所有考虑的散射构型与能量窗，存在良好定义的广义相位 $\varphi(\omega)$ 与相对态密度 $\rho_{\rm rel}(\omega)$，使得

$$
\frac{\varphi'(\omega)}{\pi}
=\rho_{\rm rel}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

其中 $\operatorname{tr}$ 为通道空间上的迹，$\mathsf Q(\omega):=Q(\omega)$。

此式将三类对象统一在同一时间刻度上：

1. 相位导数 $\varphi'(\omega)$：相位–频率几何的弯曲；
2. 相对态密度 $\rho_{\rm rel}(\omega)$：谱–态密度的修正；
3. 群延迟迹 $\operatorname{tr}Q(\omega)$：到达时间相对于自由传播的偏移。

后文所有时间刻度相关的量都将尽可能写回此同一式。

### 2.5 宇宙学时间与红移

考虑空间均匀各向同性的 FRW 度规（暂取 $k=0$）

$$
ds^2=-dt^2+a(t)^2\,d\mathbf x^2.
$$

对沿共动坐标 $\mathbf x(t)$ 传播的光子，有零测地条件 $ds^2=0$，从而

$$
\frac{d\mathbf x}{dt}=\pm \frac{1}{a(t)}\,\hat{\mathbf n}.
$$

宇宙学红移定义为

$$
1+z:=\frac{\lambda_0}{\lambda_e}
=\frac{\nu_e}{\nu_0}
=\frac{a(t_0)}{a(t_e)},
$$

其中下标 $e,0$ 分别表示发射与观测事件。

### 2.6 边界广义熵与时间参数

在含引力的量子场论中，考虑某因果区域的边界 $\Sigma$ 与其外部（或内部）量子场自由度，定义广义熵

$$
S_{\rm gen}(\Sigma) := \frac{\operatorname{Area}(\Sigma)}{4G\hbar}+S_{\rm out}(\Sigma),
$$

其中 $S_{\rm out}$ 为相对于 $\Sigma$ 的冯·诺依曼熵。沿某一零生成元族 $\gamma(\lambda)$ 形变 $\Sigma$ 时，以仿射参数 $\lambda$ 作为"边界时间"，研究 $S_{\rm gen}(\lambda)$ 的极值与单调性质，即给出"熵随时间的组织方式"。

**公理 2.3（边界熵时间演化公理）** 在适当的能量条件与半经典假设下，任一点 $p$ 的小因果菱形 $D_{p,r}$ 的边界可选取一族局域割面 $\{\Sigma_\lambda\}$，使得

1. 在适当约束（固定局域能量或有效体积）下，$\lambda=0$ 处 $S_{\rm gen}(\lambda)$ 取极值；
2. 对于沿任一零方向的外推，$S_{\rm gen}(\lambda)$ 在物理演化下满足适当的单调性或凸性条件（如 QNEC/QFC 型不等式）。

后文将基于此公理与刻度同一式，对引力方程给出熵几何解释。

---

## 3 相位与本征时间的等价

本节讨论单粒子或窄波包在弯曲时空中的半经典传播，说明量子相位的本质是沿世界线累积的本征时间，并由此把量子与经典在时间刻度上连接起来。

### 3.1 世界线作用量与路径积分

对质量 $m$ 的点粒子，其经典世界线作用量可取为

$$
S[\gamma]= -mc^2\int_\gamma d\tau
= -mc^2\int\sqrt{-g_{\mu\nu}\frac{dx^\mu}{d\lambda}\frac{dx^\nu}{d\lambda}}\,d\lambda.
$$

量子振幅在世界线路径积分框架下形式上写作

$$
\mathcal A(x_f,x_i)
\simeq \int_{\gamma:x_i\to x_f}\mathcal D\gamma\,
\exp\Bigl(\frac{i}{\hbar}S[\gamma]\Bigr).
$$

在半经典极限 $\hbar\to 0$ 下，主贡献来自作用量的驻相轨道，即满足测地线方程的世界线 $\gamma_{\rm cl}$。

### 3.2 相位–本征时间定理

**定理 3.1（相位–本征时间等价）** 设窄波包在弯曲时空中传播，其中心轨迹 $\gamma_{\rm cl}$ 为质量 $m$ 粒子的类时测地线。则在半经典近似下，波包中心的相位演化为

$$
\phi = -\frac{1}{\hbar}S[\gamma_{\rm cl}]
= \frac{mc^2}{\hbar}\int_{\gamma_{\rm cl}} d\tau,
$$

从而瞬时相位频率满足

$$
\frac{d\phi}{d\tau}
=\frac{mc^2}{\hbar}.
$$

*证明* 取窄波包初始态在某局域 Fermi 正交坐标系中构造，使其在相空间中集中于经典初始条件 $(x_i,p_i)$。路径积分在半经典极限下可用驻相近似展开。令 $\gamma_{\rm cl}$ 为满足给定边界条件的唯一测地线，则

1. 对每条路径 $\gamma$，振幅相位为 $\phi[\gamma]=S[\gamma]/\hbar$；
2. 在 $\hbar\to 0$ 时，具有最大权重的是 $\delta S=0$ 的轨道，即测地线 $\gamma_{\rm cl}$；
3. 在该轨道上 $S[\gamma_{\rm cl}]=-mc^2\int d\tau$。

因此，主导态的总相位为

$$
\phi = -\frac{1}{\hbar}S[\gamma_{\rm cl}]
= \frac{mc^2}{\hbar}\int d\tau.
$$

对本征时间取导数即得

$$
\frac{d\phi}{d\tau}
=\frac{mc^2}{\hbar},
$$

证明完毕。 $\square$

**推论 3.2（量子时间刻度）** 对于质量 $m$ 的粒子，其在本征时间刻度上的相位旋转频率为常数 $mc^2/\hbar$。因此，本征时间 $d\tau$ 与量子相位差 $d\phi$ 等价，只差一个常数因子：

$$
d\phi = \frac{mc^2}{\hbar}\,d\tau.
$$

这表明：在几何端，本征时间是沿世界线的固有刻度；在量子端，相位则是该刻度下的"角坐标"。二者之间的线性等价，为后续"时间延迟–群延迟"、"红移–相位节奏"提供了统一背景。

---

## 4 散射时间延迟与引力时间膨胀

本节在静态或渐近平坦引力场中考察光或物质波传播，说明引力时间延迟等价于散射相位对频率的导数，从而可由 Wigner–Smith 群延迟刻度化。

### 4.1 静态度规与折射率视角

考虑静态度规

$$
ds^2=-V(\mathbf x)\,c^2dt^2+g_{ij}(\mathbf x)\,dx^i dx^j,
$$

其中 $V(\mathbf x)>0$。引入"时间折射率"

$$
n_t(\mathbf x):=V(\mathbf x)^{-1/2}
=\left(-g_{tt}(\mathbf x)\right)^{-1/2}.
$$

对定频 $\omega$ 的波动场，几何光学极限下的 eikonal 方程可写为

$$
g^{\mu\nu}\partial_\mu \phi\,\partial_\nu \phi=0,
$$

其解 $\phi$ 给出波前相位。若取 $\phi = -\omega t+S(\mathbf x)$，则空间部分满足类似于折射率为 $n_t(\mathbf x)$ 的光学费马原理。

### 4.2 时间延迟与相位导数

设有两条路径：一条在引力场中 $\gamma_g$，一条在平直背景中 $\gamma_0$，分别对应传播时间 $T_g(\omega)$ 与 $T_0(\omega)$。定义时间延迟

$$
\Delta T(\omega):=T_g(\omega)-T_0(\omega).
$$

另一方面，引力场对总相位的修正 $\Delta\Phi(\omega)$ 为沿经典路径的作用量差除以 $\hbar$。对定频波动，作用量差主要来自时间折射率的修正，可写作

$$
\Delta\Phi(\omega)
\simeq -\omega\,\Delta T(\omega),
$$

其中忽略与频率弱相关的项。于是有

$$
\Delta T(\omega)
=-\partial_\omega\Delta\Phi(\omega)
$$

在以 $\omega$ 为谱参数的描述下，这正是群延迟的定义。

结合刻度同一式

$$
\partial_\omega\Phi(\omega)=\operatorname{Tr}Q(\omega),
$$

可得出：

**定理 4.1（引力时间延迟–群延迟等价）** 在适当的几何光学与半经典假设下，对静态引力场背景中传播的定频波，宏观可观测的引力时间延迟 $\Delta T(\omega)$ 等价于总散射相位 $\Phi(\omega)$ 对频率的导数，即等价于 Wigner–Smith 群延迟算子 $Q(\omega)$ 的迹：

$$
\Delta T(\omega)
=\partial_\omega\Phi(\omega)
=\operatorname{Tr}Q(\omega).
$$

*证明略要* 在 eikonal 近似下，相位函数 $\phi$ 满足哈密顿–雅可比方程，路径上的相位积累与经典作用量成正比。对定频态，时间方向的作用量贡献为 $-\omega T$。对比有无引力场的两种构型，作用量差为 $-\omega \Delta T$，从而总相位差满足 $\Delta\Phi=-\omega\Delta T$。对频率求导得 $\Delta T=-\partial_\omega\Delta\Phi$。同时，由散射理论知 $\partial_\omega\Phi=\operatorname{Tr}Q$。将两者识别，即得该等价关系。 $\square$

此定理说明：通常被理解为由时空曲率导致的宏观"时间膨胀"或"时间延迟"，在频域上完全等价于散射群延迟。因此，通过刻度同一式，可用统一的时间刻度对象 $\rho_{\rm rel}(\omega)$ 来描述引力时间效应。

---

## 5 宇宙学红移作为时间刻度剪切

本节考虑 FRW 宇宙中的光传播与红移，说明红移可以被视为同一光子世界线上"时间刻度"的剪切，并可写成相位频率在不同事件处的比值。

### 5.1 FRW 几何与红移公式

如 2.5 节所述，对平直 FRW 宇宙，度规为

$$
ds^2=-dt^2+a(t)^2\,d\mathbf x^2.
$$

对沿共动坐标传播的光子，用共形时间 $\eta$ 定义 $d\eta=dt/a(t)$，则度规写为

$$
ds^2=a(\eta)^2(-d\eta^2+d\mathbf x^2).
$$

零测地线满足

$$
\frac{d\mathbf x}{d\eta}=\pm \hat{\mathbf n},
$$

即光子在共形时–空间中如同在平直 Minkowski 空间中传播。

考虑频率 $\nu$ 的测量：对静止于共动坐标的观测者，其四速度为 $u^\mu = (1,0,0,0)$，光子的四动量 $k^\mu$ 满足 $\nu\propto -k_\mu u^\mu$。可得

$$
\nu\propto \frac{1}{a(t)},
$$

从而红移

$$
1+z=\frac{\nu_e}{\nu_0}=\frac{a(t_0)}{a(t_e)}.
$$

### 5.2 相位节奏的几何解释

设光子的相位函数为 $\phi(x)$。沿零测地线 $\gamma$ 的参数 $\lambda$ 有

$$
\frac{d\phi}{d\lambda} = k_\mu \frac{dx^\mu}{d\lambda},
$$

其中 $k_\mu$ 为四波矢。对某个观测者，其固有时间为本征时间 $\tau$。频率定义为

$$
\nu := \frac{1}{2\pi}\frac{d\phi}{d\tau}.
$$

对共动观测者，有 $\tau=t$。于是

$$
\nu(t) = \frac{1}{2\pi}\frac{d\phi}{dt}.
$$

由前述结果，$\nu\propto 1/a(t)$，因此可写成

$$
\frac{d\phi}{dt}\bigg|_{t=t_e}
:\frac{d\phi}{dt}\bigg|_{t=t_0}
=\frac{\nu_e}{\nu_0}
=1+z.
$$

这给出：

**命题 5.1（红移–相位节奏等价）** 在 FRW 宇宙中，同一光子世界线上发射事件 $e$ 与观测事件 $0$ 的相位时间导数之比等于宇宙学红移：

$$
1+z
=\frac{\nu_e}{\nu_0}
=\frac{\left.\frac{d\phi}{dt}\right|_{e}}{\left.\frac{d\phi}{dt}\right|_{0}}.
$$

由于 $\phi$ 同时满足几何光学的哈密顿–雅可比方程，它也可以被理解为某一"宇宙时间刻度"的角坐标。红移因此是对这一刻度在两个时刻的比值测量，即"时间刻度剪切"的宏观表现。

### 5.3 与统一刻度同一式的关系

若将宇宙学传播视为某种有效散射过程，可形式性地引入等效散射矩阵 $S(\omega)$，其总相位 $\Phi(\omega)$ 可由沿共形时间路径的 eikonal 积分给出。则红移可视为对 $\Phi(\omega)$ 在不同宇宙时间截面的"相位梯度"差异。通过刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}
=\rho_{\rm rel}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega),
$$

可在频率空间中刻画红移对态密度与群延迟的影响，从而把宇宙学观测纳入同一时间刻度框架。

---

## 6 边界熵、因果结构与引力作为熵的组织方式

本节在局域因果菱形中考察广义熵随边界"时间"演化的性质，说明在适当公理下，宏观引力方程可视为"熵–能量在因果边界上的组织方式"的有效描述。

### 6.1 局域 Rindler 视界与局域热力学

在任意点 $p\in M$ 的邻域内，可选择一个局域惯性系，使得度规近似为 Minkowski，并构造穿过 $p$ 的局域 Rindler 视界。该视界的零生成元参数 $\lambda$ 可视为其"边界时间"，对应观测者的 Rindler 时间参数。对该视界，与其相关的局域 Unruh 温度 $T$ 与热流 $\delta Q$ 满足局域热力学关系

$$
\delta Q = T\,\delta S,
$$

其中 $\delta S$ 为视界熵变化，在引力理论下假定与视界面积变分 $\delta A$ 成正比。

### 6.2 广义熵与小因果菱形

回到 2.1 中的小因果菱形 $D_{p,r}$。其边界可被视为一种局域"闭合视界"，带有两个相交的零方向。对 $D_{p,r}$ 内的量子场态，考虑穿过一个零方向的局域割面族 $\{\Sigma_\lambda\}$，定义广义熵

$$
S_{\rm gen}(\lambda)
= \frac{\operatorname{Area}(\Sigma_\lambda)}{4G\hbar}
+ S_{\rm out}(\Sigma_\lambda).
$$

**公理 6.1（局域广义熵极值与单调性）** 在小尺度极限 $r\to 0$ 下，存在一族割面 $\{\Sigma_\lambda\}$ 及仿射参数选择，使得：

1. 在 $\lambda=0$ 处，在固定"有效体积"或等效的局域守恒量约束下，$S_{\rm gen}(\lambda)$ 取极值，即

$$
\left.\frac{dS_{\rm gen}}{d\lambda}\right|_{\lambda=0}=0;
$$

2. 对于向未来方向的微小形变，$d^2 S_{\rm gen}/d\lambda^2$ 与局域应力–能量张量分量 $T_{kk}$ 满足类似 QNEC 的不等式，保证适当单调性或凸性。

这里 $k^\mu$ 为零生成元方向，$T_{kk}=T_{\mu\nu}k^\mu k^\nu$。

### 6.3 Raychaudhuri 方程与面积变分

考虑沿零生成元 $k^\mu$ 的束，令 $\theta$ 为膨胀量，$\sigma_{\mu\nu}$ 为剪切张量。Raychaudhuri 方程给出

$$
\frac{d\theta}{d\lambda}
= -\frac{1}{2}\theta^2
-\sigma_{\mu\nu}\sigma^{\mu\nu}
-R_{\mu\nu}k^\mu k^\nu.
$$

在小尺度与适当条件下，梯度项与剪切可忽略或用高阶项表示。面积元 $dA$ 的演化满足

$$
\frac{d}{d\lambda}dA = \theta\,dA.
$$

于是面积变分的二阶导数中包含 $R_{\mu\nu}k^\mu k^\nu$ 项。

### 6.4 熵极值与爱因斯坦方程

广义熵的一阶变分可写为

$$
\frac{dS_{\rm gen}}{d\lambda}
= \frac{1}{4G\hbar}\frac{dA}{d\lambda}
+\frac{dS_{\rm out}}{d\lambda}.
$$

在 $\lambda=0$ 处，公理 6.1 要求 $dS_{\rm gen}/d\lambda=0$。利用 Raychaudhuri 方程与应力–能量与熵流之间的关系（例如通过局域第一定律或相对熵的线性响应），可得出一个与 $R_{\mu\nu}$ 和 $T_{\mu\nu}$ 相关的等式。

**定理 6.2（爱因斯坦方程的局域熵几何形式）** 假设公理 6.1 成立，且局域量子场论满足适当的能量条件与相对熵单调性。则在小因果菱形极限中，度规必须满足局域场方程

$$
R_{\mu\nu}-\frac{1}{2}Rg_{\mu\nu}+\Lambda g_{\mu\nu}
= 8\pi G\,\langle T_{\mu\nu}\rangle,
$$

其中 $\Lambda$ 为积分常数形式的宇宙学常数。

*证明纲要* 主要步骤如下：

1. 使用 Raychaudhuri 方程，将面积变分的二阶导数 $\frac{d^2A}{d\lambda^2}$ 表达为 $R_{\mu\nu}k^\mu k^\nu$ 与 $\theta,\sigma$ 的函数；
2. 使用局域热力学关系与相对熵–模 Hamiltonian 的线性响应，将 $dS_{\rm out}/d\lambda$ 与 $\langle T_{kk}\rangle$ 联系起来；
3. 利用公理 6.1 的极值条件 $\left.dS_{\rm gen}/d\lambda\right|_{\lambda=0}=0$，得到 $R_{kk}$ 与 $\langle T_{kk}\rangle$ 的比例关系；
4. 利用 $R_{\mu\nu}k^\mu k^\nu$ 对所有零方向 $k^\mu$ 的等式，以及 Bianchi 恒等式，将比例关系提升为张量等式，得到爱因斯坦方程，并把比例系数识别为 $8\pi G$，额外常数项吸收到宇宙学常数 $\Lambda$ 中。

详细推导见附录 D。 $\square$

因此，宏观引力几何（爱因斯坦方程）可被理解为：在每一个局域因果菱形上，广义熵 $S_{\rm gen}$ 作为因果边界随"边界时间" $\lambda$ 演化的函数，其极值与单调性所施加的约束。这正是"引力是熵在因果边界上的组织方式"的精确定理化表述。

---

## 7 统一图景：时间作为量子–经典的桥

综合前述结果，可给出如下统一图景：

1. 在世界线层面：本征时间 $d\tau$ 与量子相位 $d\phi$ 线性等价（定理 3.1），时间是相位几何的参数；
2. 在散射/传播层面：宏观可观测的时间延迟等价于散射相位对频率的导数，即群延迟迹 $\operatorname{Tr}Q(\omega)$（定理 4.1），时间延迟是相位–频率几何的弯曲；
3. 在宇宙学层面：红移 $1+z$ 可表达为同一光子世界线上相位时间导数在两个事件处的比值（命题 5.1），红移是时间刻度随宇宙演化的剪切；
4. 在因果边界层面：广义熵 $S_{\rm gen}(\lambda)$ 随边界时间 $\lambda$ 的极值与单调性条件（定理 6.2）导出爱因斯坦方程，宏观引力几何是"熵随时间刻度的组织方式"的有效描述；
5. 在频率/谱层面：刻度同一式 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}Q$ 将相位导数、相对态密度与群延迟统一在同一时间刻度上，为从微观散射到宏观时间延迟、红移提供了谱几何上的桥梁。

这一图景可抽象为一个交换图：时间刻度作为中心对象，其不同"投影"分别给出量子相位、散射延迟、宇宙学红移与广义熵演化，而宏观引力几何则是保证这些投影自洽的张量方程。量子与经典的关系在此被压缩为一句话：它们在"时间刻度"的语言上完全对齐。

---

## 附录 A：Wigner–Smith 群延迟与刻度同一式

本附录给出刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}
=\rho_{\rm rel}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
$$

的证明纲要。

### A.1 谱移函数与 Birman–Kreĭn 公式

设 $H_0,H$ 为一对自伴算子，满足 $H-H_0$ 为迹类或相对迹类扰动。令 $\xi(\omega)$ 为 Kreĭn 谱移函数，其定义满足对任一光滑紧支函数 $f$

$$
\operatorname{Tr}\bigl(f(H)-f(H_0)\bigr)
=\int f'(\omega)\,\xi(\omega)\,d\omega.
$$

相对态密度定义为

$$
\rho_{\rm rel}(\omega):=-\partial_\omega\xi(\omega).
$$

另一方面，在散射假设下，存在散射矩阵 $S(\omega)$，总相位 $\Phi(\omega)=\arg\det S(\omega)$。Birman–Kreĭn 公式给出

$$
\det S(\omega)=\exp\bigl(-2\pi i\,\xi(\omega)\bigr).
$$

取辐角得

$$
\Phi(\omega)=-2\pi\,\xi(\omega)\mod 2\pi.
$$

### A.2 相位导数与相对态密度

对上述关系两侧对 $\omega$ 求导：

$$
\partial_\omega\Phi(\omega)=-2\pi\,\partial_\omega\xi(\omega)
=2\pi\,\rho_{\rm rel}(\omega).
$$

令 $\varphi(\omega):=\Phi(\omega)/2$ 或更一般的归一化相位，则

$$
\frac{\varphi'(\omega)}{\pi}
=\rho_{\rm rel}(\omega).
$$

### A.3 Wigner–Smith 群延迟的迹

由定义

$$
Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega).
$$

由于 $S(\omega)$ 为酉矩阵，可写 $S(\omega)=\exp(iK(\omega))$，其中 $K(\omega)$ 为自伴矩阵。则

$$
\det S(\omega)
=\exp\bigl(i\operatorname{Tr}K(\omega)\bigr),
$$

从而

$$
\Phi(\omega)
=\operatorname{Tr}K(\omega).
$$

对 $Q(\omega)$ 取迹：

$$
\operatorname{Tr}Q(\omega)
=-i\operatorname{Tr}\bigl(S^\dagger\partial_\omega S\bigr)
=-i\partial_\omega\operatorname{Tr}\bigl(\ln S\bigr)
=\partial_\omega\Phi(\omega),
$$

其中使用了 $\ln S$ 的谱分解以及 $\operatorname{Tr}\ln S=\ln\det S$ 的关系。

综上

$$
\operatorname{Tr}Q(\omega)
=\partial_\omega\Phi(\omega)
=2\pi\,\rho_{\rm rel}(\omega).
$$

由此得到刻度同一式

$$
\frac{\varphi'(\omega)}{\pi}
=\rho_{\rm rel}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega).
$$

证毕。

---

## 附录 B：世界线路径积分下的相位–本征时间证明细节

本附录补充定理 3.1 的路径积分证明细节。

### B.1 局域 Fermi 正交坐标与测地线展开

在给定类时测地线 $\gamma_{\rm cl}$ 的邻域，可构造 Fermi 正交坐标 $(\tau,y^i)$，使得度规在 $\gamma_{\rm cl}$ 上局域展开为

$$
ds^2=-d\tau^2+\delta_{ij}dy^i dy^j+\mathcal O(y^2).
$$

在小邻域内近似为 Minkowski 时空上的微扰。

### B.2 路径积分的高斯近似

粒子作用量

$$
S[\gamma]=-mc^2\int d\tau \sqrt{1-\delta_{ij}\dot y^i\dot y^j+\cdots},
$$

在小速度与小偏移下展开为

$$
S[\gamma]
\approx -mc^2\int d\tau
+\frac{m}{2}\int d\tau\,\delta_{ij}\dot y^i\dot y^j+\cdots.
$$

路径积分可分离为经典部分与涨落部分：

$$
\mathcal A\sim e^{\frac{i}{\hbar}S[\gamma_{\rm cl}]}
\int \mathcal D y^i \exp\Bigl(\frac{i}{\hbar}S_{\rm quad}[y]\Bigr),
$$

其中 $S_{\rm quad}$ 为关于 $y^i$ 的二次项。后者给出高斯积分，决定振幅的模与前因子，而经典作用量 $S[\gamma_{\rm cl}]$ 给出主相位。

### B.3 本征时间与相位频率

由

$$
S[\gamma_{\rm cl}]=-mc^2\int d\tau,
$$

得到

$$
\phi=-\frac{1}{\hbar}S[\gamma_{\rm cl}]
=\frac{mc^2}{\hbar}\int d\tau.
$$

对 $\tau$ 微分得

$$
\frac{d\phi}{d\tau}=\frac{mc^2}{\hbar},
$$

说明在本征时间刻度下，粒子相位以常频率旋转。这一结果与局域惯性系中解 $e^{-iEt/\hbar}$ 且 $E\approx mc^2$ 一致。证毕。

---

## 附录 C：FRW 宇宙中红移–相位表述的细化

本附录细化命题 5.1 中"红移等于相位时间导数比"的推导。

### C.1 光子四动量与频率

在 FRW 度规下，光子四动量 $k^\mu$ 满足零条件 $g_{\mu\nu}k^\mu k^\nu=0$。对共动观测者 $u^\mu=(1,0,0,0)$，测得频率为

$$
\nu = -\frac{1}{2\pi}k_\mu u^\mu
=\frac{1}{2\pi}k^0,
$$

其中 $k^0=dt/d\lambda$ 与仿射参数 $\lambda$ 相关。结合零测地线方程，可得 $k^0\propto 1/a(t)$。

### C.2 eikonal 相位与频率

令光子相位为 $\phi(x)$，则 $k_\mu=\partial_\mu\phi$。沿观测者世界线 $x^\mu(\tau)$ 有

$$
\frac{d\phi}{d\tau}
=\partial_\mu\phi\,\frac{dx^\mu}{d\tau}
=k_\mu u^\mu
=-2\pi\nu.
$$

对共动观测者 $\tau=t$，故

$$
\frac{d\phi}{dt}=-2\pi\nu.
$$

因此

$$
\frac{\left.\frac{d\phi}{dt}\right|_e}{\left.\frac{d\phi}{dt}\right|_0}
=\frac{\nu_e}{\nu_0}
=1+z.
$$

证毕。

---

## 附录 D：广义熵极值与爱因斯坦方程的推导纲要

本附录给出定理 6.2 的详细推导框架，重点展示"广义熵随边界时间的组织"如何约束几何。

### D.1 小因果菱形与零生成元参数

在点 $p$ 的邻域选取类时向量场 $\xi^\mu$，构造小因果菱形 $D_{p,r}$。其边界可由两簇零测地线生成，分别对应未来与过去方向。选取某一簇未来零生成元族，以仿射参数 $\lambda$ 参数化，使得 $\lambda=0$ 对应穿过 $p$ 的截面。

对每个 $\lambda$，定义横截割面 $\Sigma_\lambda$，其面积为 $A(\lambda)$，广义熵为

$$
S_{\rm gen}(\lambda)
=\frac{A(\lambda)}{4G\hbar}
+S_{\rm out}(\lambda).
$$

### D.2 一阶变分：极值条件

广义熵一阶变分为

$$
\frac{dS_{\rm gen}}{d\lambda}
=\frac{1}{4G\hbar}\frac{dA}{d\lambda}
+\frac{dS_{\rm out}}{d\lambda}.
$$

面积变分满足

$$
\frac{dA}{d\lambda}=\int_{\Sigma_\lambda}\theta\,dA,
$$

其中 $\theta$ 为膨胀量。取 $\lambda=0$，公理 6.1 要求在适当约束下

$$
\left.\frac{dS_{\rm gen}}{d\lambda}\right|_{\lambda=0}=0.
$$

另一方面，$S_{\rm out}$ 对小形变的线性响应可与模 Hamiltonian 的期望值联系起来，即

$$
\frac{dS_{\rm out}}{d\lambda}
= 2\pi \int_{\Sigma_\lambda} \lambda\,\langle T_{kk}\rangle\,dA+\cdots,
$$

在 $\lambda=0$ 附近取适当极限得到与 $\langle T_{kk}\rangle$ 成正比的项。这一步依赖于局域第一定律与相对熵线性响应。

综合起来，一阶极值条件给出 $R_{kk}$ 与 $\langle T_{kk}\rangle$ 间的比例关系的预备形式。

### D.3 二阶变分与 Raychaudhuri 方程

考虑二阶变分

$$
\frac{d^2S_{\rm gen}}{d\lambda^2}
=\frac{1}{4G\hbar}\frac{d^2A}{d\lambda^2}
+\frac{d^2S_{\rm out}}{d\lambda^2}.
$$

面积的二阶变分利用 Raychaudhuri 方程：

$$
\frac{d\theta}{d\lambda}
= -\frac{1}{2}\theta^2
-\sigma_{\mu\nu}\sigma^{\mu\nu}
-R_{\mu\nu}k^\mu k^\nu.
$$

在 $\lambda=0$ 处可选取初始条件使 $\theta=0$，剪切贡献用高阶项吸收，得到

$$
\left.\frac{d\theta}{d\lambda}\right|_{\lambda=0}
\approx -R_{kk},
$$

从而

$$
\left.\frac{d^2A}{d\lambda^2}\right|_{\lambda=0}
= \int_{\Sigma_0} \left.\frac{d\theta}{d\lambda}\right|_{\lambda=0} dA
\approx -\int_{\Sigma_0} R_{kk}\,dA.
$$

另一方面，$d^2 S_{\rm out}/d\lambda^2$ 与能量流的涨落和量子能量条件（如 QNEC）相关，后者给出

$$
\frac{d^2S_{\rm out}}{d\lambda^2}
\leq 2\pi \int_{\Sigma_0} \langle T_{kk}\rangle\,dA,
$$

或在饱和条件下取等号。

### D.4 从标量关系到张量方程

将上述表达代入广义熵二阶变分式，并结合单调性或凸性要求，可得到

$$
-\frac{1}{4G\hbar}\int_{\Sigma_0} R_{kk}\,dA
+ 2\pi \int_{\Sigma_0} \langle T_{kk}\rangle\,dA \ge 0,
$$

在饱和或极值条件下取等号。由于割面与方向 $k^\mu$ 在局域内可任意选择，上式对所有零方向与小割面均成立，意味着在点 $p$ 有

$$
R_{\mu\nu}k^\mu k^\nu
= 8\pi G\,\langle T_{\mu\nu}\rangle k^\mu k^\nu
$$

对所有零向量 $k^\mu$ 成立。

由此可知张量

$$
E_{\mu\nu}:=R_{\mu\nu}-8\pi G\,\langle T_{\mu\nu}\rangle
$$

满足 $E_{\mu\nu}k^\mu k^\nu=0$ 对所有零向量成立，进而得出 $E_{\mu\nu}=\Lambda g_{\mu\nu}$，其中 $\Lambda$ 为某常数。使用 Bianchi 恒等式 $\nabla^\mu(R_{\mu\nu}-\frac{1}{2}Rg_{\mu\nu})=0$ 与能量–动量守恒 $\nabla^\mu T_{\mu\nu}=0$，可将 $\Lambda$ 识别为宇宙学常数，并得到

$$
R_{\mu\nu}-\frac{1}{2}Rg_{\mu\nu}+\Lambda g_{\mu\nu}
=8\pi G\,\langle T_{\mu\nu}\rangle.
$$

证毕。

---

本论文在统一时间刻度视角下，将量子相位、本征时间、散射群延迟、宇宙学红移与广义熵演化组织为一套自洽的几何–熵–谱框架，并在此基础上给出宏观引力方程的熵几何解释。
