# 黎曼猜想的几何化与"有限窗—有限带宽—有限阶"子系统中的相对不可证

Version: 1.2

**MSC**：11M26；42A38；47B35；81U15；94A20
**关键词**：黎曼猜想几何化；显式公式正性；Toeplitz/Berezin 压缩；窗化 Helffer–Sjöstrand 迹公式；Nyquist–Poisson–Euler–Maclaurin 有限阶纪律；带限不可完备性；热流阈值

---

## 摘要

在"窗化散射—Toeplitz/Berezin 压缩—三位一体母尺"的统一语法下，将黎曼猜想等价地几何化为两种全域陈述：其一是由显式公式诱导的读数二次型在自卷正定核锥上的全域非负；其二是与之配准的生成子谱严格定位在临界轴。本文在仅允许有限窗、有限带宽与有限阶 Euler–Maclaurin 校正的公理化子系统中，建立两条相对不可证定理：（A）无论使用多少带内核与有限阶误差账本，均不能在该子系统内判定全域正性；（B）在热流阈值表述下，单点阈值同样在该子系统内不可判定。证明依赖母尺恒等式
$$
\frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\,\mathsf Q(E),
$$
窗化 Helffer–Sjöstrand 迹公式、Toeplitz/Berezin 压缩的保正准则与 Poisson—有限阶 Euler–Maclaurin（NPE）纪律。母尺恒等式由 Wigner–Smith 群延迟与 Kreĭn 光谱位移函数的 Birman–Kreĭn 关系串联而成，并与"相位—态密度—群延迟—迹公式"的标准文献一致。([arXiv][1])

---

## 0. 记号与公理

### 0.1 观测三元与母尺

取能量参数化的散射矩阵族 $S(E)\in\mathsf U(N)$（$E\mapsto S(E)$ 可微），记 Wigner–Smith 群延迟矩阵
$$
\mathsf Q(E)=-\,i\,S(E)^\dagger \partial_E S(E).
$$
设总散射相位 $\varphi(E)=\tfrac12\arg\det S(E)$ 与相对态密度 $\rho_{\rm rel}(E)$。本文以如下母尺恒等式为刻度：
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\,\mathsf Q(E)\ }.
$$
右端"$\operatorname{tr}\,\mathsf Q$ 等于（相对）态密度"的关系在量子散射与介质输运中广泛使用；左端则由 Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 与 $\rho_{\rm rel}=-\xi'$ 对齐。([Physical Review Links][2])

### 0.2 窗化迹公式

对 $f\in C_c^\infty(\mathbb R)$ 的窗化函数演算（Helffer–Sjöstrand）有
$$
\mathrm{Tr}\big(f(H)-f(H_0)\big)=\int_\mathbb R f'(E)\,\xi(E)\,dE,
$$
并可等价表述为
$$
\mathrm{Tr}\big(f(H)-f(H_0)\big)=\frac{1}{2\pi i}\int_{\mathbb R} f(E)\,\partial_E\log\det S(E)\,dE,
$$
由分部积分与 Birman–Kreĭn 关系 $\partial_E\log\det S=-2\pi i\,\xi'$ 得出。从而在窗化级别上，"迹—相位—位移—群延迟—态密度"同尺可测。([eudml.org][3])

### 0.3 Toeplitz/Berezin 压缩与保正

在 Hardy/Bergman 空间，以 $\Pi_w$ 表示与窗 $w$ 相关的投影与 $M_h$ 表示乘子，Toeplitz/Berezin 压缩定义为
$$
K_{w,h}:=\Pi_w M_h \Pi_w .
$$
当符号 $h\ge 0$ 且测度满足 Carleson 条件时，$K_{w,h}$ 为正算子；对应的线性读数泛函保持正性。([ScienceDirect][4])

### 0.4 NPE（Nyquist–Poisson–Euler–Maclaurin）有限阶纪律

离散—连续桥以 Poisson 求和与至多 $p$ 阶的 Euler–Maclaurin 校正衔接，尾项由窗衰减与高阶导数控制。有限带宽假设来自 Nyquist–Shannon 取样与 Landau 密度条件的经典框架。([webusers.imj-prg.fr][5])

---

## 1. 几何化命题与等价

### 1.1 自卷正定核锥与读数二次型

设
$$
\mathcal C_+:=\{\,k=\varphi\ast\tilde\varphi:\ \varphi\in\mathcal S(\mathbb R)\,\},\qquad
\widehat k(\omega)=|\widehat\varphi(\omega)|^2\ge 0.
$$
定义读数
$$
\mathcal D[k]:=\int_\mathbb R k(E)\,\rho_{\rm rel}(E)\,dE
=\frac{1}{2\pi i}\int_{\mathbb R} k(E)\,\partial_E\log\det S(E)\,dE
=-\frac{1}{2\pi i}\int_{\mathbb R} k'(E)\,\log\det S(E)\,dE.
$$
借窗化迹公式与分部积分，上述三种表述等价。([Physical Review Links][2])

### 1.2 几何化 RH 的两种表述

* **（P）全域正性表述**：对一切 $k\in\mathcal C_+$ 有 $\mathcal D[k]\ge 0$。
* **（S）谱定位表述**：存在生成子 $\mathcal D_{\rm geom}$ 的谱全落在 $\{\tfrac12+i\mathbb R\}$，并在窗化读数下与 $\rho_{\rm rel}$ 对齐。

这二者与 Weil 的显式公式正性判据等价：RH 等价于由显式公式构成的分布在测试函数卷积平方的锥上非负。([Wikipedia][6])

---

## 2. 有限资源子系统 $\mathsf T_{\rm win}(R,\Omega,p)$

### 2.1 定义

给定 $(R,\Omega,p)\in(0,\infty)^3$，$\mathsf T_{\rm win}(R,\Omega,p)$ 允许的原语如下：
(a) 仅使用有限组窗—核对 $\{(w_{R_j},h_j)\}_{j=1}^{m}$ 生成的核
$$
k_j:=w_{R_j}\!\ast \check h_j,\qquad \operatorname{supp}\widehat{k_j}\subset[-\Omega,\Omega];
$$
(b) 一切读数均由母尺与窗化迹公式实现；
(c) 离散—连续桥仅用 Poisson 与不超过 $p$ 阶的 Euler–Maclaurin，误差以统一上界封口。([Wikipedia][7])

### 2.2 解释

$\mathsf T_{\rm win}$ 能访问的证据只有有限个带内读数 $\{\mathcal D[k_j]\}_{j=1}^m$ 及其有限阶误差上界。故它无法区分在 $[-\Omega,\Omega]$ 上频谱一致而带外差异的两份"谱数据"。这正是带限不可完备性的核心。([Wikipedia][8])

---

## 3. 带限不可完备性

### 定理 3.1（带限不可完备性）

给定任意有限组 $\{k_j\}_{j=1}^m\subset\mathcal C_+$ 与 $\varepsilon>0$，存在两份窗化等价的谱密度 $\rho_{\rm rel}^{\pm}$ 满足对所有 $1\le j\le m$,
$$
\Bigl|\int k_j \rho_{\rm rel}^{+}-\int k_j \rho_{\rm rel}^{-}\Bigr|<\varepsilon,
$$
但存在某 $k_\star\in\mathcal C_+$ 使
$$
\int k_\star \rho_{\rm rel}^{+}>0,\qquad \int k_\star \rho_{\rm rel}^{-}<0.
$$
于是 $\mathsf T_{\rm win}(R,\Omega,p)$ 内无法以有限证据判定"对全体 $k\in\mathcal C_+$，$\mathcal D[k]\ge 0$"的真值。

#### 证明

设统一带宽 $\Omega=\max_j\mathrm{band}(\widehat{k_j})$。取 $\widehat\psi\in C_c^\infty(\mathbb R)$ 为实偶且非负，令
$$
\operatorname{supp}\widehat\psi\subset\{|\omega|\ge 2\Omega\},
$$
并记其反变换为 $\psi$。令 $\widehat\eta:=|\widehat\psi|^2$，记其反变换为 $\eta$。给定基准 $\rho_0\in\mathcal S'(\mathbb R)$ 与小参数 $\delta>0$，置
$$
\rho_{\rm rel}^{\pm}=\rho_0\pm\delta\,\eta.
$$
对每个带内核 $k_j$，由傅里叶支撑不交与 Parseval 恒等式得
$$
\int k_j \eta=\frac{1}{2\pi}\int \widehat{k_j}(\omega)\,\widehat\eta(\omega)\,d\omega=0,
$$
故
$$
\int k_j\rho_{\rm rel}^{+}=\int k_j\rho_{\rm rel}^{-}=\int k_j\rho_0 .
$$
此外，由 NPE 有限阶纪律，任意由 Poisson 与至多 $p$ 阶 Euler–Maclaurin 组合而成的误差账本只依赖于带内信息与端点导数，因此可调 $\delta$ 与窗参使两侧在所有可见证据上差异 $<\varepsilon$。([Wikipedia][7])

另一方面，取 $\varphi_\star=\psi$，并置 $k_\star=\varphi_\star\ast\tilde\varphi_\star\in\mathcal C_+$。则
$$
\int k_\star \eta=\frac{1}{2\pi}\int |\widehat\psi(\omega)|^4\,d\omega>0,
$$
从而
$$
\int k_\star \rho_{\rm rel}^{+}-\int k_\star \rho_{\rm rel}^{-}=2\delta\int k_\star \eta
=\frac{\delta}{\pi}\int |\widehat\psi(\omega)|^4\,d\omega\neq 0.
$$
令 $\delta$ 的符号合适，即得一正一负。定理证毕。

> 评注：上述构造本质上是 Paley–Wiener 与 Bochner 定理的并用：$\mathcal C_+$ 中核的傅里叶像非负，带外扰动可与之正交；而带限测量对带外微扰"盲视"。([Wikipedia][9])

---

## 4. 热流阈值的相对不可证

令对数频域热核 $h_\lambda=\exp(\lambda\partial_E^2)$（$\lambda\ge 0$），定义
$$
F(\lambda):=\inf_{\substack{k\in\mathcal C_+\\ \int_{\mathbb R}k(E)\,dE=1}}\ \int_{\mathbb R} (k\ast h_\lambda)(E)\,\rho_{\rm rel}(E)\,dE.
$$

### 引理 4.1（单调与强平滑极限）

记 $\mathcal K=\{k\in\mathcal C_+:\int k=1\}$。由于 $h_{\lambda+\tau}=h_\lambda\ast h_\tau$ 且 $\int h_\tau=1$，映射 $k\mapsto k\ast h_\tau$ 将 $\mathcal K$ 映回自身，故
$$
F(\lambda+\tau)=\inf_{k\in\mathcal K}\langle k\ast h_\tau,\rho\ast h_\lambda\rangle
\ \ge\ \inf_{k\in\mathcal K}\langle k,\rho\ast h_\lambda\rangle
\ =\ F(\lambda).
$$
若 $\int\rho_{\rm rel}=0$，则 $\rho\ast h_\lambda\to 0$，从而 $\lim_{\lambda\to\infty}F(\lambda)=0$。

### 定理 4.2（$\mathsf T_{\rm win}$ 中的热流单点阈值不可判定）

在 $\mathsf T_{\rm win}(R,\Omega,p)$ 中无法以有限证据判定 $F(0)\ge 0$ 的真值。

**证明**：沿用定理 3.1 的构造，取 $\rho_{\rm rel}^{\pm}=\rho_0\pm \delta\,\eta$ 且 $\operatorname{supp}\widehat\eta\subset\{|\omega|\ge 2\Omega\}$。对每个带内核 $k_j$ 与任意 $\lambda>0$，有
$$
\Bigl|\int (k_j\ast h_\lambda)\,\eta\Bigr|
=\Bigl|\frac{1}{2\pi}\int \widehat{k_j}(\omega)\,e^{-\lambda\omega^2}\,\widehat\eta(\omega)\,d\omega\Bigr|
\le C\,e^{-4\lambda\Omega^2},
$$
故当 $\lambda$ 足够大时，两份数据在$\mathsf T_{\rm win}$ 的可见证据上不可区分并给出相同非负极限（引理 4.1）。然而在 $\lambda=0$ 时，仍有
$$
\int k_\star \rho_{\rm rel}^{+}-\int k_\star \rho_{\rm rel}^{-}=\frac{\delta}{\pi}\int |\widehat\psi(\omega)|^4\,d\omega\neq 0,
$$
因而存在 $k_\star$ 使两份数据的读数在单点阈值处异号。由于 $\mathsf T_{\rm win}$ 只能访问带内证据，故无法在该子系统内以有限证据证成命题 $F(0)\ge 0$ 的真值。证毕。

> 评注：热核平滑的"不可增加可提取耗散"的倾向与量子散射的时间延迟—态密度、以及非平衡量子半群的熵产生单调性相协同。([arXiv][1])

---

## 5. 与几何化 RH 的闭合关系

不施加"有限窗—有限带宽—有限阶"约束，在全体 $\mathcal C_+$ 上工作时：

* 表述（P）的全域正性与 Weil 的显式公式正性判据等价，从而与 RH 等价；
* 表述（S）与"生成子谱位于临界轴"的散射—谱定位相对应，且在窗化读数下由母尺与迹公式一致地对齐。

本文定理表明：在 $\mathsf T_{\rm win}(R,\Omega,p)$ 的有限资源约束下，二者均仅表现为相对不可证命题。([Wikipedia][6])

---

## 6. 讨论与扩展

1. **带限不可完备性与取样密度**：$\mathsf T_{\rm win}$ 的"可见证据有限性"与 Landau 必要密度（Paley–Wiener 空间）同向：有限带内信息不足以唯一恢复带外特征，等价于取样—重建的病态性。([archive.ymsc.tsinghua.edu.cn][11])
2. **Toeplitz/Berezin 与 Carleson**：本文仅用到"非负符号 $\Rightarrow$ 压缩保正、Carleson $\Rightarrow$ 有界"的基本面，一切在大范围 Bergman/Hardy 空间上成立。([ScienceDirect][4])
3. **母尺的普适性**：$\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 与 $\varphi'=\pi\,\rho_{\rm rel}$ 通过 Wigner–Smith—Friedel—Birman–Kreĭn 体系闭合，是散射—DOS 对偶的核心。([arXiv][1])

---

## 附录 A：母尺恒等式的证明

令 $\xi(E)$ 为 Kreĭn 光谱位移，Birman–Kreĭn 公式给出 $\det S(E)=e^{-2\pi i\,\xi(E)}$，故
$$
\partial_E\log\det S(E)=-2\pi i\,\xi'(E).
$$
另一方面，Wigner–Smith 定义 $\mathsf Q(E)=-\,i\,S^\dagger S'$，于是
$$
\operatorname{tr}\,\mathsf Q(E)=-\,i\,\partial_E\log\det S(E)=\partial_E\arg\det S(E)=-\,2\pi\,\xi'(E).
$$
令 $\rho_{\rm rel}=-\xi'$，即得
$$
\frac{1}{2\pi}\operatorname{tr}\,\mathsf Q(E)=\rho_{\rm rel}(E),\qquad
\varphi'(E)=\tfrac12\partial_E\arg\det S(E)=\pi\,\rho_{\rm rel}(E).
$$
与 Friedel 规则"总相位导数—态密度"一致，从而确立母尺恒等式。([matcuer.unam.mx][10])

---

## 附录 B：窗化 Helffer–Sjöstrand 迹公式与读数同尺

Helffer–Sjöstrand 函数演算给出对 $f\in C_c^\infty(\mathbb R)$ 的
$$
f(H)=\frac{1}{\pi}\int_{\mathbb C}\bar\partial\tilde f(z)\,(z-H)^{-1}\,dx\,dy,
$$
因此
$$
\mathrm{Tr}\big(f(H)-f(H_0)\big)=\int f'(E)\,\xi(E)\,dE.
$$
取 $f'=k$ 属于由窗—核卷积产生的可测类，合并附录 A 之母尺恒等式，得到
$$
\int k(E)\,\rho_{\rm rel}(E)\,dE=\frac{1}{2\pi}\int k(E)\,\operatorname{tr}\,\mathsf Q(E)\,dE,
$$
即"读数＝谱测度线性泛函"。([Wikipedia][12])

---

## 附录 C：Toeplitz/Berezin 压缩的保正与 Carleson 条件

在 Bergman/Hardy 空间上，Toeplitz 算子 $T_\mu f=\Pi (f\,d\mu)$。若 $\mu$ 为正且为相应空间的 Carleson 测度，则 $T_\mu$ 有界且正；若符号 $h\ge 0$，则 $\Pi M_h\Pi\ge 0$。这保证了由 $(w_R\!\ast\check h)$ 诱导的读数二次型的正性。([Project Euclid][13])

---

## 附录 D：NPE 有限阶误差闭合

* **Poisson**：对 Schwartz 函数 $s$ 与其傅里叶变换 $S$，周期化—采样由 Poisson 公式严格连接。
* **Euler–Maclaurin（至多 $p$ 阶）**：差—积换算的余项以端点高阶导数与 Bernoulli 多项式给出，存在显式上界；有限阶账本不能"恢复"带外信息。
* **结论**：任意只依赖 $[-\Omega,\Omega]$ 带内频谱与有限阶端点校正的流程，对"支撑离带"的扰动 $\eta$ 均盲视。([Wikipedia][7])

---

## 附录 E：高频不可见扰动与分离超平面

设 $\eta$ 的傅里叶支撑与 $[-\Omega,\Omega]$ 不交。对任意带内核 $k$ 有 $\langle k,\eta\rangle=0$。同时取 $k_\star=\varphi_\star\ast\tilde\varphi_\star$，其中先写 $\widehat\eta=|\widehat\psi|^2$（$\widehat\psi\in C_c^\infty$ 实偶且非负，支撑离带），再置 $\varphi_\star=\psi$。于是
$$
\langle k_\star,\eta\rangle=\frac{1}{2\pi}\int |\widehat\psi(\omega)|^4\,d\omega>0.
$$
因而由 $\rho_{\rm rel}^{\pm}=\rho_0\pm\delta\,\eta$ 可在 $\mathcal C_+$ 上构建把手，使有限证据一致而全域正性给出相反结论。这一分离构造依赖于 Bochner 定理（$\widehat k\ge 0$）与 Paley–Wiener（可控支撑）。([Wikipedia][14])

---

## 附录 F：热流阈值极限与单调

记 $\mathcal K=\{k\in\mathcal C_+:\int k=1\}$。利用
$$
\int (k\ast h_\lambda)\rho=\int k\,(\rho\ast h_\lambda)
$$
与 $\int(k\ast h_\tau)=\int k$，得 $\mathcal K$ 在 $*h_\tau$ 下不变，故 $F(\lambda+\tau)\ge F(\lambda)$；若 $\int\rho_{\rm rel}=0$，则 $\rho\ast h_\lambda\to 0$，从而 $\lim_{\lambda\to\infty}F(\lambda)=0$。([matcuer.unam.mx][10])

---

## 参考文献（节选）

1. Birman, M. Sh.; Kreĭn, M. G. "On the theory of wave and scattering operators", 1962.
2. Yafaev, D. R. *Mathematical Scattering Theory*, AMS, 2010.
3. Helffer, B.; Sjöstrand, J. "Functional calculus via almost analytic extension", 1989；见 Dimassi–Sjöstrand, *Spectral Asymptotics in the Semi-classical Limit*, CUP, 1999.
4. Gesztesy, F.; Pushnitski, A.; Simon, B. "On the Koplienko Spectral Shift Function", 2007.
5. Cunden, F. D. "Statistical distribution of the Wigner–Smith time-delay matrix", *Phys. Rev. E* 91 (2015).
6. Texier, C. "Wigner time delay and related concepts", 2015。
7. Weil, A. "Sur les 'formules explicites'…", 1952；Conrey, B. "Weil's explicit formula and positivity criterion", 2019 讲义。
8. Zhao, X.; Zheng, D. "Positivity of Toeplitz operators via Berezin transform", 2014；Pau, J. 等 "Carleson measures and Toeplitz operators…", *Michigan Math. J.* 64 (2015).
9. Shannon, C. "Communication in the Presence of Noise", 1949；Landau, H. J. "Necessary density conditions…", *Acta Math.* 117 (1967)。
10. Miller, S. D.; Schmid, W. "Summation formulas, from Poisson and Voronoi to the trace formula", 2003。
11. Connes, A.; Consani, C. "Weil positivity and trace formula", 2021。

（以上条目与文内陈述对应之开放资料可参阅：Helffer–Sjöstrand 公式与函数演算；Birman–Kreĭn 公式与光谱位移；Wigner–Smith 群延迟—态密度关系；Toeplitz/Berezin 压缩与 Carleson 准则；Nyquist–Shannon 与 Landau 密度；Poisson 与 Euler–Maclaurin 公式等。）([Wikipedia][12])

---

### 致谢

本文所用"窗化散射—Toeplitz/Berezin 压缩—母尺"语法与若干锚点公式，均可在标准文献中以等价形式找到。文中关于"不可证"的术语，系相对于明确定义的有限资源子系统 $\mathsf T_{\rm win}(R,\Omega,p)$ 而言，不涉更强的元逻辑不可证性。

[1]: https://arxiv.org/pdf/1507.00075?utm_source=chatgpt.com "arXiv:1507.00075v6 [cond-mat.mes-hall] 5 Nov 2018"
[2]: https://link.aps.org/doi/10.1103/PhysRevE.91.060102?utm_source=chatgpt.com "Statistical distribution of the Wigner-Smith time-delay matrix ..."
[3]: https://eudml.org/doc/49140?utm_source=chatgpt.com "Kreǐn's trace formula and the spectral shift function."
[4]: https://www.sciencedirect.com/science/article/pii/S0022247X14002364?utm_source=chatgpt.com "Positivity of Toeplitz operators via Berezin transform"
[5]: https://webusers.imj-prg.fr/~antoine.chambert-loir/enseignement/2020-21/shannon/shannon1949.pdf?utm_source=chatgpt.com "Communication In The Presence Of Noise"
[6]: https://en.wikipedia.org/wiki/Weil%27s_criterion?utm_source=chatgpt.com "Weil's criterion"
[7]: https://en.wikipedia.org/wiki/Poisson_summation_formula?utm_source=chatgpt.com "Poisson summation formula"
[8]: https://en.wikipedia.org/wiki/Nyquist%E2%80%93Shannon_sampling_theorem?utm_source=chatgpt.com "Nyquist–Shannon sampling theorem"
[9]: https://en.wikipedia.org/wiki/Paley%E2%80%93Wiener_theorem?utm_source=chatgpt.com "Paley–Wiener theorem"
[10]: https://www.matcuer.unam.mx/VeranoAnalisis/Fritz-I.pdf?utm_source=chatgpt.com "Applications of Spectral Shift Functions. I: Basic Properties ..."
[11]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6020-11511_2006_Article_BF02395039.pdf?utm_source=chatgpt.com "Necessary density conditions for sampling and ..."
[12]: https://en.wikipedia.org/wiki/Helffer%E2%80%93Sj%C3%B6strand_formula?utm_source=chatgpt.com "Helffer–Sjöstrand formula"
[13]: https://projecteuclid.org/journals/michigan-mathematical-journal/volume-64/issue-4/Carleson-measures-and-Teoplitz-operators-for-weighted-Bergman-spaces-on/10.1307/mmj/1447878031.pdf?utm_source=chatgpt.com "Carleson Measures and Toeplitz Operators for Weighted ..."
[14]: https://en.wikipedia.org/wiki/Bochner%27s_theorem?utm_source=chatgpt.com "Bochner's theorem"
