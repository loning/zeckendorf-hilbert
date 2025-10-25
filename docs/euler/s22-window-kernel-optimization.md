# S22. 窗/核最优化：带限—镜像一致下的变分原理、KKT 条件与"极点 = 主尺度"保持

**—— Nyquist–Poisson–EM 三分解误差的最小化、带限偶子空间的投影最优性与 BN–Bregman Γ-极限**

## 摘要（定性）

在 S15–S17 的表示—规范—散射统一框架与 S18 的"别名/伯努利层/截断"三分解误差准则上，把窗/核设计铸造成带限偶子空间上的凸—变分最优化问题。给出 L² 强凸版（唯一极小元与 Euler–Lagrange 条件）与 L¹ 稀疏版（弱式 KKT/频域弱式证书）。采用归一约束 $w(0)=1$。频域必要条件呈现为"多项式乘子 + 卷积核"的带限偶投影强式；时域 Euler–Lagrange 为带限偶投影下的非局部方程（"内/外区常系数 ODE + 界面条件"仅作启发性描述）。引入 BN–Bregman 软化并证明对硬约束的 Γ-极限收敛；在 S21 的阈值判据下，强凸或软化 + 小 Hilbert 正则情形获得极小元与最小值的李普希茨稳定，而纯 L¹ 情形保留最小值稳定与解集外半连续。全程坚持**有限阶** Euler–Maclaurin 与 Nyquist–Poisson–EM 三分解，不引入新奇点，保持"极点 = 主尺度"。离散图 Ihara ζ 给出并行模板。

---

## 0. 设定与可行类

### 0.1 傅里叶规范与缩放

$$
\widehat f(\xi)=\int_{\mathbb R} f(t)\,e^{-it\xi}\,dt,\qquad
f(t)=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\xi)\,e^{it\xi}\,d\xi.
$$

缩放 $w_R(t):=w(t/R)$ 满足

$$
(w_R)^{(k)}(t)=R^{-k}\,w^{(k)}(t/R),\qquad
\widehat{w_R}(\xi)=R\,\widehat w(R\xi).
$$

### 0.2 带限偶子空间与归一

$$
\mathsf{PW}_\Omega^{\mathrm{even}}
:=\{\,w\in L^2(\mathbb R):\ \operatorname{supp}\widehat w\subset[-\Omega,\Omega],\ w(t)=w(-t)\,\},
$$

$$
\mathcal W_\Omega:=\{\,w\in\mathsf{PW}_\Omega^{\mathrm{even}}:\ w(0)=1\,\}.
$$

必要时考虑指数窗类

$$
\mathcal W_{\exp}
:=\{\,w\in L^2:\ \sup_{t}e^{\kappa'|t|}|w^{(k)}(t)|<\infty\ (0\le k\le 2M),\ w\ \text{偶},\ w(0)=1\,\}.
$$

### 0.3 三分解误差与 Nyquist 条件

对 integrand $g$ 与参数 $\Delta>0$、$M\ge2$、$T>0$，置

$$
\mathfrak E(g;\Delta,M,T)
=\underbrace{\sum_{m\ne0}\big|\widehat g(2\pi m/\Delta)\big|}_{\text{alias}}
+\underbrace{\sum_{j=1}^{M-1}\frac{|B_{2j}|}{(2j)!}\,\Delta^{2j}\,|g^{(2j)}|_{L^1}}_{\text{EM 层}}
+\underbrace{\int_{|t|>T}|g(t)|\,dt}_{\text{tail}}.
$$

若 $\operatorname{supp}\widehat g\subset[-\Omega_g,\Omega_g]$ 且 $\Delta\le\pi/\Omega_g$，则 $\mathrm{alias}=0$；在临界 $\Delta=\pi/\Omega_g$ 亦成立（此处将 $\operatorname{supp}\widehat g$ 视为闭集；采样谐波 $|2\pi m/\Delta|\ge 2\Omega_g>\Omega_g$ 不落入闭支集 $[-\Omega_g,\Omega_g]$；忽略测度零边界点的潜在病态）。

---

## 1. 统一目标与误差鲁棒性

给定窗 $w$ 与试验核 $h$：

$$
g_{\mathrm{spec}}=(h\cdot w_R)\,\rho,\qquad
g_0=(h\cdot w_R)\,\phi_0,
$$

其中 $\rho=\pi^{-1}\mathrm{Im}\,m(\cdot+i0)$（此处 $m$ 指 Stieltjes 型函数或相应 Green 函数），$\phi_0$ 为几何主项密度；$\rho$ 与 $\phi_0$ 视为与 $w$ 无关的背景密度，进入 $\mathfrak E$ 仅线性作用于 $w_R$。取可检范数

$$
|h|_{\mathfrak H}:=\sum_{j=0}^{2M}|h^{(j)}|_{L^1}+|\widehat h|_{L^1},
$$

此范数确保 $\widehat h$、$h^{(j)}$ 的 $L^1$ 有界，从而 $\mathfrak E(\cdot)$ 中各项可界且对 $w$ 呈凸。并置

$$
\mathcal J(w)
:=\sup_{|h|_{\mathfrak H}\le1}\big\{\alpha\,\mathfrak E(g_{\mathrm{spec}};\Delta,M,T)+\beta\,\mathfrak E(g_0;\Delta,M,T)\big\},
\qquad \alpha,\beta>0.
$$

$\mathcal J$ 在 $\mathsf{PW}_\Omega^{\mathrm{even}}$ 上凸且下半连续。

---

## 2. L² 强凸版：存在唯一与一阶条件

### 2.1 主问题（$\mathcal J$ 的 Hilbert 代理）

**引理 2.0（代理上界）.** 在 $|h|_{\mathfrak H}\le1$、$\rho,\phi_0$ 具备基本界（例如有界或有限阶分布）的前提下，存在 $C(\Delta,M,T)>0$ 使

$$
\mathcal J(w)\ \le\ C(\Delta,M,T)\Big(\sum_{j=1}^{M-1}|w_R^{(2j)}|_{L^2}^2+|\mathbf 1_{|t|>T}w_R|_{L^2}^2\Big).
$$

从而 $\mathcal J_{\mathrm{BL}}$ 为 $\mathcal J$ 的可检上界/代理目标。

$$
\boxed{\ \min_{w\in\mathcal W_\Omega}\
\mathcal J_{\mathrm{BL}}(w)
:=\sum_{j=1}^{M-1}\gamma_j\,|w_R^{(2j)}|_{L^2}^2
+\lambda\,|\mathbf 1_{|t|>T}\,w_R|_{L^2}^2\quad(\gamma_j,\lambda>0)\ .}
\tag{2.1}
$$

$\mathcal J_{\mathrm{BL}}$ 作为 $\mathcal J$ 的可检上界/代理目标，构造强凸问题以确保唯一性与稳定性。

### 2.2 存在唯一

**定理 2.1.** (2.1) 在 $\mathcal W_\Omega$ 上存在唯一极小元 $w^\star$。

*要点*. $\mathsf{PW}_\Omega^{\mathrm{even}}$ 为闭线性子空间；二次目标严格凸且强制性（强 coercive）。由时频限制算子谱存在 $\lambda_0(\Omega/R,T)<1$ 使
$|\mathbf 1_{|t|>T}w_R|_{L^2}^2\ge(1-\lambda_0)|w_R|_{L^2}^2$（其中 $\lambda_0(\Omega/R,T)$ 为 PSWF 浓聚问题在 $[-T,T]$ 上的**最大特征值**，当 $T<\infty$ 时满足 $\lambda_0<1$；因此外区能量有统一下界）。配合导数项得强制性；约束 $w(0)=1$ 排除零解。

### 2.3 一阶必要条件：弱式与频域强式

**弱式.** 对任意 $\varphi\in\mathsf{PW}_{\Omega/R}^{\mathrm{even}}$（因 $w_R(t)=w(t/R)$ 使 $w_R\in\mathsf{PW}_{\Omega/R}^{\mathrm{even}}$），

$$
\Big\langle \sum_{j=1}^{M-1}\gamma_j\,\partial_t^{4j}w_R^\star
+\lambda\,\mathbf 1_{|t|>T}\,w_R^\star+\eta\,\delta_0,\ \varphi\Big\rangle=0,
$$

等价于 $\mathbf P_{\Omega/R}^{\mathrm{even}}\big[\sum_{j}\gamma_j\,\partial_t^{4j}w_R^\star
+\lambda\,\mathbf 1_{|t|>T}\,w_R^\star\big]=\eta\,\mathbf P_{\Omega/R}^{\mathrm{even}}\delta_0$（其中 $\eta$ 吸收常数与符号）。

**频域强式.**

$$
\boxed{\ \chi_{[-\Omega/R,\Omega/R]}(\xi)\Big(\sum_{j=1}^{M-1}\gamma_j\,\xi^{4j}\,\widehat{w^\star_R}(\xi)
+\tfrac{\lambda}{2\pi}\,(\widehat{\mathbf 1_{|t|>T}}*\widehat{w^\star_R})(\xi)\Big)=\eta\,\chi_{[-\Omega/R,\Omega/R]}(\xi)\ .}
\tag{2.2}
$$

其中导数项为点乘乘子 $\xi^{4j}$，尾部项为卷积。$\widehat{\mathbf 1_{|t|>T}}$ 含 $\delta$-型分量，应作温和分布卷积；指数窗时另见§4。

**显式分解与实现提示.** $\widehat{\mathbf 1_{|t|>T}}=2\pi\delta-\widehat{\mathbf 1_{[-T,T]}}=2\pi\delta-\tfrac{2\sin(T\xi)}{\xi}$，故**卷积中含显式可约项** $\tfrac{\lambda}{2\pi}\cdot 2\pi\delta*\widehat{w_R}=\lambda\widehat{w_R}$，其余为与 $\tfrac{\sin(T\xi)}{\xi}$ 的卷积。数值实现时需注意 $\tfrac{1}{2\pi}$ 因子（见 §0.1 规范），避免遗漏导致量纲错误。

投影核的显式形状为 $\mathbf P_{\Omega/R}\delta_0(t)=\tfrac{1}{2\pi}\int_{-\Omega/R}^{\Omega/R}e^{it\xi}\,d\xi=\tfrac{\sin(\Omega t/R)}{\pi t}$（$t=0$ 取极限），故频域右端为常数频带 $[-\Omega/R,\Omega/R]$。卷积项可能把能量带出 $[-\Omega/R,\Omega/R]$，但投影将带外成分抛弃。

### 2.4 时域投影方程

对任意 $\varphi\in\mathsf{PW}_{\Omega/R}^{\mathrm{even}}$，有

$$
\Big\langle \sum_{j=1}^{M-1}\gamma_j\,\partial_t^{4j}w_R^\star
+\lambda\,\mathbf 1_{|t|>T}\,w_R^\star+\eta\,\delta_0,\ \varphi\Big\rangle=0.
$$

等价地，$\mathbf P_{\Omega/R}^{\mathrm{even}}\!\Big[\sum_j\gamma_j\,\partial_t^{4j}w_R^\star
+\lambda\,\mathbf 1_{|t|>T}\,w_R^\star\Big]=\eta\,\mathbf P_{\Omega/R}^{\mathrm{even}}\delta_0$。

**说明.** 由于带限投影的存在，上式应理解为**非局部**的投影方程；"内/外区常系数 ODE + 界面条件"的描写仅作启发，避免将其当作在 $\mathcal S'$ 上的逐点/分段等式。由偶性仍有 $w^{(2k+1)}(0)=0$，且 $w_R$ 为带限函数因而解析，故在 $t=\pm T$ 处函数及各阶导数本身连续。**该连续性来自函数类而非 Euler–Lagrange 方程的分段 ODE 描述**（后者仅为启发性）。

---

## 3. L¹ 稀疏版：弱式 KKT 与频域弱式证书

### 3.1 主问题

$$
\boxed{\ \min_{w\in\mathcal W_\Omega}\
\sum_{j=1}^{M-1}\alpha_j\,|w_R^{(2j)}|_{L^1}
+\beta\,|\mathbf 1_{|t|>T}\,w_R|_{L^1}\quad(\alpha_j,\beta>0)\ .}
\tag{3.1}
$$

**注.** 以下 KKT/证书针对目标**有限**的可行 $w$（特别是 $|\mathbf 1_{|t|>T}w_R|_{L^1}<\infty$）陈述；若需存在性，可在可行类上加入轻度衰减或以 $L^2$ 尾项近似。

### 3.2 一阶条件

**弱式 KKT.** 存在 $\mu_j,\nu\in L^\infty(\mathbb R)$，$|\mu_j|_\infty\le1,\ |\nu|_\infty\le1$，且

$$
\mu_j(t)=\operatorname{sgn}\big((w_R^\star)^{(2j)}(t)\big)\ \text{a.e.于 }(w_R^\star)^{(2j)}\ne0,
$$

$$
\nu(t)=\operatorname{sgn}\big(w_R^\star(t)\big)\ \text{a.e.于 }|t|>T,
$$

使得对任意 $\varphi\in\mathsf{PW}_{\Omega/R}^{\mathrm{even}}$，

$$
\Big\langle \sum_{j=1}^{M-1}\alpha_j\,\partial_t^{2j}\mu_j
+\beta\,\mathbf 1_{|t|>T}\,\nu+\eta\,\delta_0,\ \varphi\Big\rangle=0.
$$

**频域弱式.**

$$
\boxed{\
\chi_{[-\Omega/R,\Omega/R]}(\xi)\Big(
\sum_{j=1}^{M-1}\alpha_j\,(-1)^j\,\xi^{2j}\,\widehat{\mu_j}(\xi)
+\tfrac{\beta}{2\pi}\,(\widehat{\mathbf 1_{|t|>T}}*\widehat{\nu})(\xi)\Big)
=\eta\,\chi_{[-\Omega/R,\Omega/R]}(\xi)\quad\text{in }\mathcal S'.}
\tag{3.2'}
$$

卷积按温和分布理解；在非零处对偶饱和（$|\mu_j|=1$ 或 $|\nu|=1$）决定稀疏/平滑拼接。

---

## 4. 指数窗与"极点 = 主尺度"保持

对 $w\in\mathcal W_{\exp}$ 的强凸问题

$$
\min_{w}\ \sum_{j=1}^{M-1}\gamma_j|w_R^{(2j)}|_{L^2}^2
+\lambda|e^{\kappa|\cdot|}w_R|_{L^2}^2,\qquad 0<\kappa<\kappa',
$$

**注.** 为保证加权项有限，需取权重指数 $\kappa<\kappa'$（可行类定义中的衰减指数）；或改为对可行类要求 $\kappa'+\varepsilon$ 余量假设。

Euler–Lagrange 的"尾部"项在时域变为 $e^{2\kappa|t|}w_R$ 的乘子；在频域表示仅在**形式上**可理解为带限投影后的卷积表达。为避免额外的分布层级假设，本文对指数窗保留**时域**表述；如需频域核，可改用 $e^{-\kappa|t|}$（此时卷积核为 $L^1$）并添加 $\tfrac{1}{2\pi}$ 因子。带限投影保证表达良定。由于仅用**有限阶** EM，卷积与带限投影不改变主尺度项，工作条带内奇性集合不增、极阶不升。

---

## 5. BN–Bregman 软化与 Γ-极限

取 Legendre 型信息势 $\Lambda$（$\mu$-强凸、$L$-平滑）与线性算子 $\mathcal T$（单射且范围稠密），考虑

$$
\min_{w}\ \mathcal J(w)+\tau\,\Lambda^\ast(\mathcal T w),\qquad \tau>0.
$$

**定理 5.1（Γ-极限）.** 若 $\{\mathcal J+\tau\Lambda^\ast\}$ 在可行类上**等势**（例如由 §2 的导数项与 §6 的小 Hilbert 正则给出统一下界），则当 $\tau_n\downarrow0$ 时，极小值
$\min(\mathcal J+\tau_n\Lambda^\ast)\downarrow\min\mathcal J$，且存在子列 $\tau_{n_k}\downarrow0$ 与相应极小元 $w_{\tau_{n_k}}\rightharpoonup w^\star$（弱收敛），其中 $w^\star$ 为硬问题（2.1）或（3.1）的极小元。若硬问题在极小处**强凸/唯一**，或在 $\tau>0$ 情形**叠加小的 Hilbert 正则**使其强凸，则**全序列** $w_{\tau_n}\to w^\star$ 且可提升为强收敛，解对数据李普希茨稳定。

---

## 6. 阈值邻域的稳健性（S21 接口）

阈值判据 $\varphi'=\pi\rho$、$\delta'=-2\pi\rho$ 与**有限阶** EM、Nyquist–Poisson–EM 纪律保证窗化不改变奇性集合与极阶。若数据扰动满足
$|\widehat F-\widehat F_0|_\infty\le\varepsilon$、$\operatorname{TV}(\widehat\nu,\nu)\le\delta$，则

**强凸/软化 + 小 Hilbert 正则.** 存在 $C>0$ 使

$$
|w^\star-\widetilde w^\star|_{L^2}\le C(\varepsilon+\delta),\qquad
\big|\min\mathcal J-\min\widetilde{\mathcal J}\big|\le C(\varepsilon+\delta).
$$

（其中"强凸"指 $\mathcal T$ 具有界下界或等价设定；"软化"指 §5 的 BN–Bregman 情形并**叠加小的 Hilbert 正则**。）

**纯 L¹.** $\min\mathcal J$ 李普希茨稳定，解集外半连续；增添微小强凸正则或选择规则可得解的李普希茨稳定。阈值位置与零集计数在 Rouché 半径内不变，其偏移受 $|\widehat{\varphi'}-\varphi'|_{L^1}$ 控制。

---

## 7. 离散图（Ihara ζ）并行模板

在 $(q+1)$-正则图 $G$ 上，非回溯算子与 Ihara ζ 的行列式恒等式诱导离散谱—轨道对偶。取离散"长度频率"侧带限偶窗，Nyquist 条件下别名闭消；伯努利层与尾项由长度截断与端点差分控制；必要条件在离散频域成为"多项式乘子 + 离散卷积核"的带限偶投影（或频域弱式）；对偶证书等价于加权回路测度饱和。

---

## 8. 失效边界

1. **无限阶 EM**：引入伪奇性，破坏"极点 = 主尺度"。
2. **镜像失配/偶性缺失**：散射—功能方程接口失效。
3. **非带限且衰减不足**：别名与尾项主导，应增大带宽或改用指数窗并增大 $T$。

---

## 9. 可检清单（最小充分条件）

1. **可行类**：偶；带限或指数衰减；$w(0)=1$。
2. **误差目标**：$\mathfrak E(\cdot;\Delta,M,T)$；$\Delta\le\pi/\Omega_g$ 时 $\mathrm{alias}=0$。
3. **L² 版**：强凸 (2.1)；弱式与频域强式（2.2）；时域投影方程（§2.4）。
4. **L¹ 版**：弱式 KKT 与频域弱式（3.2'）；对偶饱和决定稀疏拼接。
5. **软化与 Γ**：$\tau>0$ 唯一极小元；$\tau\downarrow0$ 回收硬约束解。
6. **稳定性**：强凸/软化 + 小 Hilbert 正则下解与最小值李普希茨；纯 L¹ 下最小值李普希茨、解集外半连续。
7. **卷积核**：频域卷积须携带 **$\mathbf{\tfrac{1}{2\pi}}$ 因子**（见§0.1 傅里叶规范，实现时切勿遗漏）；投影频带为 $[-\Omega/R,\Omega/R]$（而非 $[-\Omega,\Omega]$）；$\widehat{\mathbf 1_{|t|>T}}=2\pi\delta-\tfrac{2\sin(T\xi)}{\xi}$（含显式 $\delta$ 项）；指数窗权重指数需 $\kappa<\kappa'$。若改用 $e^{-\kappa|t|}$ 才得到 $L^1$ 卷积核。

---

## 10. 与既有篇章的接口

* **S15（Weyl–Heisenberg 酉表示）**：窗族 $U_\tau V_\sigma w$ 在相位—尺度群下的协变性保证带限偶子空间在群平均下闭合；等距性使目标函数在群作用下不变，支持对称化选优。
* **S16（de Branges–Krein 规范系统）**：窗/核应用于规范系统评估时，传递矩阵 $M(t,z)$ 的 $J$-酉性与偶对称性保证频域强式（2.2）的 Hermite 实化；有限阶 EM 不引入新极点，与 de Branges 相位 $\varphi'$ 的单调性相容。
* **S17（散射算子与功能方程）**：窗化散射相位 $\delta(x)=-2\varphi(x)+\text{常数}$ 的导数 $\delta'=-2\pi\rho$ 直接进入目标 $g_{\mathrm{spec}}$；偶窗保证散射矩阵实轴酉性不被破坏。
* **S18（轨道—谱窗化不等式）**：本文目标 $\mathcal J(w)$ 直接量化 S18 §3.3 的三分解误差；定理 2.1 与 3.1 的极小元给出 S18 "最优窗/核"的变分刻画。
* **S19（谱图与 Ihara ζ）**：§7 的离散图模板与 S19 §3 的离散轨道—谱窗化不等式对齐；Ihara ζ 的自倒数性对应离散频域的偶对称约束。
* **S20（BN 投影—KL 代价—灵敏度）**：§5 的 BN–Bregman 软化调用 S20 §3 的 Γ-极限定理；强凸条件下的李普希茨稳定性（§6）直接继承 S20 §4 的信息—能量链。
* **S21（连续谱阈值与奇性稳定性）**：§4 与 §6 的"极点 = 主尺度"保持依赖 S21 定理 21.6 的奇性不增原理；阈值邻域稳健性（§6）调用 S21 定理 21.9 的 Bregman–KL 灵敏度链。

---

## 参考文献

1. H. J. Landau, H. O. Pollak, "Prolate spheroidal wave functions, Fourier analysis and uncertainty—II," *Bell Syst. Tech. J.* **40** (1961), 65–84.
2. D. Slepian, H. O. Pollak, "Prolate spheroidal wave functions, Fourier analysis and uncertainty—I," *Bell Syst. Tech. J.* **40** (1961), 43–63.
3. A. Bonami, B. Demange, P. Jaming, "Hermite functions and uncertainty principles for the Fourier and the windowed Fourier transforms," *Rev. Mat. Iberoam.* **19** (2003), 23–55.
4. I. Daubechies, *Ten Lectures on Wavelets*, SIAM, 1992.
5. R. Rockafellar, R. Wets, *Variational Analysis*, Springer, 1998.
6. H. Attouch, G. Buttazzo, G. Michaille, *Variational Analysis in Sobolev and BV Spaces*, SIAM, 2006.
7. E. Candès, M. Wakin, "An introduction to compressive sampling," *IEEE Signal Process. Mag.* **25** (2008), 21–30.
8. B. Simon, *Orthogonal Polynomials on the Unit Circle*, Parts 1–2, AMS Colloquium, 2005.

---

## 结语

以带限偶子空间 $\mathsf{PW}_\Omega^{\mathrm{even}}$ 为几何基础，本文把 Nyquist–Poisson–EM 三分解误差的最小化铸造成 L² 强凸（唯一解与频域强式）与 L¹ 稀疏（弱式 KKT 与频域弱式证书）两条可检主线：频域必要条件为"多项式乘子 + 卷积核"的带限偶投影（投影频带 $[-\Omega/R,\Omega/R]$，卷积携带 $\tfrac{1}{2\pi}$ 因子），时域 Euler–Lagrange 为带限偶投影下的非局部方程；BN–Bregman 软化提供 Γ-极限通路（需等势性保证紧性），配合小 Hilbert 正则可得全序列收敛与李普希茨稳定；S21 阈值判据下奇性集合与极阶保持不变（"极点 = 主尺度"）。所建变分框架为自适应窗/核设计、多窗协同优化与算子级稳定域的后续研究提供统一且可验证的数学基础，并在离散图（Ihara ζ）上给出自然并行。