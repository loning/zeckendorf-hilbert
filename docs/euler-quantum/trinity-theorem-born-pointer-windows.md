# 窗口化测量的三位一体定理

**—— Born = 信息投影（当且仅当），Pointer = 光谱极小（当且仅当），Windows = 极大极小最优**

**作者**：Auric
**版本**：v1.0（预印本）
**日期**：2025-10-25

---

## 摘要（定性）

在 **de Branges–Kreĭn（DBK）规范系统**、**散射—功能方程词典**与**Bregman/信息几何**的统一框架下，本文建立窗口化测量的"三位一体定理（Trinity Theorem）"。结论分三层：
**（I）Born = 信息投影（iff）**：在正交投影测量（及其到 POVM 的推广）下，由窗口化读数诱导的最优概率向量，等价于一族线性对齐约束上的 **I-投影（最小 KL/Bregman 代价）** 当且仅当它等于 Born 概率。
**（II）Pointer = 光谱极小（iff）**：对任意可分辨窗族，令"窗化迹二次型"的 **Ky Fan 部分和** 在所有正交基上极小，则且仅当该基为被测可观测量的 **光谱本征基**（模退化）。
**（III）Windows = 极大极小最优**：在带限偶窗并归一 $w(0)=1$ 的约束下，以 **Nyquist–Poisson–Euler–Maclaurin** 的"别名 + 伯努利层 + 截断"非渐近误差上界为对手，最优窗存在且（Hilbert 强凸代理下）唯一，并满足频域投影的 **KKT** 条件。关键桥梁是 **Birman–Kreĭn 公式**与 **Wigner–Smith** 延迟所给出的**相位导数 = 谱密度**，从而将窗化读数与相对态密度（LDOS）精确对接。

---

## 0. 记号、规范与基本设定

### 0.1 Hilbert 空间与测量

$\mathcal H$ 可分；纯态 $\psi\in\mathcal H$、$|\psi|=1$。PVM 情形取互斥完备投影 $\{P_i\}$（$P_iP_j=\delta_{ij}P_i$、$\sum_i P_i=I$），测量概率 $p_i=\langle\psi,P_i\psi\rangle$。POVM 情形以 $\{E_i\succeq0\}$、$\sum_i E_i=I$ 计，$p_i=\langle\psi,E_i\psi\rangle$。

### 0.2 DBK 规范系统与 Weyl–Titchmarsh

对一维通道，Weyl–Titchmarsh 函数 $m$ 为 Herglotz 函数，其边界虚部给出谱测度；DBK 理论在 Herglotz 类与规范系统之间给出光谱表示与评估嵌入。

### 0.3 散射—功能方程词典与相位—谱移

$$
\det S(E)=\exp\!\bigl(-2\pi i\,\xi(E)\bigr),\qquad
\frac{d}{dE}\arg\det S(E)=-2\pi\,\xi'(E).
$$

若规范 $\det S(E)=c_0\,e^{-2i\varphi(E)}$，则

$$
\boxed{\ \varphi'(E)=\pi\,\xi'(E)=\pi\,\rho_{\rm rel}(E)\ }.
$$

**规范声明**：我们固定 $\det S(E)=c_0e^{-2i\varphi(E)}$；据 Birman–Kreĭn，$\det S=e^{-2\pi i\xi}$，故 $\varphi'=\pi\xi'$；由 $Q=-iS^\dagger S'$ 与 $\frac{d}{dE}\arg\det S=\operatorname{tr}Q$，得 $\operatorname{tr}Q=-2\varphi'=-2\pi\xi'$。

### 0.4 Wigner–Smith 矩阵

$$
Q(E)=-\,i\,S^\dagger(E)\,\frac{dS}{dE}(E)\quad\text{为自伴（特征值一般不保证非负）},\qquad
\boxed{\ \frac{1}{2\pi}\operatorname{tr}Q(E)=-\xi'(E)\ }.
$$

与 §0.3 之 $\det S(E)=e^{-2\pi i\xi(E)}$ 相容，且由 $\operatorname{tr}Q=\frac{d}{dE}\arg\det S$ 得。

### 0.5 窗化迹、三分解误差与可分辨窗族

对偶窗/核 $(w,h)$ 的窗化功能

$$
\mathcal S(h;R)=\sum_j h(z_j)\,w_R(z_j)+\int_{\mathbb R} h(E)\,w_R(E)\,\rho_{\rm rel}(E)\,dE,
$$

其中 $\{z_j\}\subset\sigma_p(A)$ 为 $A$ 的点谱（本征能级），若无点谱则此和为空。本文把点谱原子并入 $\rho_{\rm rel}$ 的测度表示（即 $\rho_{\rm rel}$ 既含绝对连续部分也含原子部分），于是上式可统一写为 **Stieltjes 积分** $\int h(E)w_R(E)\,d\nu_{\rm rel}(E)$；§4 的写法正是此统一表达。数值实现的误差闭合为

$$
\text{alias（Poisson）}+\text{EM（有限阶伯努利层）}+\text{tail}.
$$

"可分辨窗族" $\mathcal W$ 指使得 $\{E\mapsto h(E)w_R(E): w\in\mathcal W\}\subset C_0(\sigma(A))$ 在谱上分离点的窗族；若该族复共轭封闭且连同常数函数生成的交换 $*$-代数在 $C_0(\sigma(A))$ 中稠密（Stone–Weierstrass），则可刻画谱结构。

### 0.6 Paley–Wiener 带限偶窗与 Fourier 规范

$$
\mathsf{PW}^{\rm even}_\Omega=\{\,w:\ \operatorname{supp}\widehat w\subset[-\Omega,\Omega],\ \mathbf{w(E)=w(-E)}\,\},\quad w(0)=1.
$$

本文采用**非角频率**规范，对**能量变量 $E$** 取 Fourier 变换（频率记为 $\xi$）：

$$
\widehat f(\xi)=\int_{\mathbb R} e^{-iE\xi}f(E)\,dE,\qquad
f(E)=\frac{1}{2\pi}\int_{\mathbb R} e^{iE\xi}\widehat f(\xi)\,d\xi,
$$

Parseval：$\langle f,g\rangle=\frac{1}{2\pi}\langle\widehat f,\widehat g\rangle$；乘法—卷积：$\widehat{fg}=\frac{1}{2\pi}\,\widehat f\ast\widehat g$。

**缩放窗定义**：令带限偶窗 $w\in\mathsf{PW}^{\rm even}_\Omega$，**缩放窗**定义为 $w_R(E):=w(E/R)$。于是 $\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$，其支撑位于 $[-\Omega/R,\Omega/R]$，即下文 KKT 中 $\chi_B$ 的 $B=[-\Omega/R,\Omega/R]$。

### 0.7 信息几何与 I-投影

负熵与 log-sum-exp 势互为 Fenchel 共轭；指数族的自然/期望参数由 Legendre 映射联系。在线性对齐子族上，I-投影存在唯一（KL 的严格凸性与可达性）；关于线性族上的 I-投影存在唯一与退化情形，参见 Csiszár (1975) 与后续综述。

---

## 1. Born = 信息投影（当且仅当）

设 $P_i$ 为 PVM 元，记

$$
\phi_i:=\frac{P_i\psi}{|P_i\psi|}\ (|P_i\psi|>0),\qquad
w_i:=|P_i\psi|^2.
$$

Born 概率为 $p_i^{\rm B}=w_i$。若 $w_i=0$，任选 $\phi_i\in\mathrm{Ran}(P_i)$ 并有 $\langle\psi,\phi_i\rangle=0$；此时所有涉及 $\langle\psi,\phi_i\rangle$ 的和式项为 0，不影响后续等式。

### 定理 1.1（几何与信息两种刻画的等价）

令

$$
X(p):=\sum_i \sqrt{p_i}\,\phi_i,\qquad
\mathcal D(p):=\tfrac12\lVert X(p)-\psi\rVert^2,
$$

则 $\mathcal D(p)$ 的唯一极小点为 $p=w$（即 Born 概率）。另一方面，在线性对齐族

$$
\mathcal M:=\Big\{\,p\in\Delta:\ \sum_i p_i\,\phi_i=\sum_i w_i\,\phi_i\,\Big\}
$$

上，I-投影

$$
p^\star=\arg\min_{p\in\mathcal M}D_{\rm KL}(p|w)
$$

存在唯一，且 $p^\star=w$。因而

$$
\boxed{\ \text{Born 概率}\ \Longleftrightarrow\ \text{I-投影（在线性对齐族上）}\ }.
$$

### 证明（提纲）

（1）几何版：$|X(p)|^2=\sum_i p_i=1$，故

$$
\mathcal D(p)=1-\langle\psi,X(p)\rangle
=1-\sum_i |P_i\psi|\sqrt{p_i}
$$

由 Cauchy–Schwarz 取等当且仅当 $\sqrt{p_i}\propto |P_i\psi|$；由 CS 等号条件与 $\sum p_i=1$ 唯一化常数，故 $p=w$。
（2）信息版：在线性对齐族 $\mathcal M$ 上，因 $\{\phi_i\}$ 正交且单位，约束 $\sum_i p_i\phi_i=\sum_i w_i\phi_i$ 逐系数给出 $p_i=w_i$，即 $\mathcal M=\{w\}$；因此 I-投影在本设定下**退化为单点**，$p^\star=w$。此处的"Born = I-投影"是把**几何最优**与**信息最优**对齐到**同一点**的**等价刻画**，并非一般意义下的非平凡投影问题。
（3）POVM 情形用 **Naimark 扩张**：存在等距嵌入 $V:\mathcal H\to\mathcal H\otimes\mathcal K$ 与扩张 PVM $\{\Pi_i\}$ 使 $E_i=V^\dagger\Pi_iV$。在 $\mathcal H\otimes\mathcal K$ 上对 $\{\Pi_i\}$ 与态 $V\psi$ 重复上述 PVM 论证即得结论，再投回原空间。∎

---

## 2. Pointer = 光谱极小（当且仅当）

令被测可观测量为自伴算子 $A$，谱投影族 $\Pi_A$。对偶窗/核 $(w_R,h)$ 定义

$$
K_{w,h}:=\int_{\mathbb R} h(E)\,w_R(E)\,d\Pi_A(E),
$$

则 $K_{w,h}$ 为**自伴**算子；当 $h(E)w_R(E)\ge 0$ 几乎处处时 $K_{w,h}\succeq0$。下文的极值论证仅需自伴。

对正交基 $\{e_k\}$ 与任意 $m\in\mathbb N$ 引入 **Ky Fan 部分和**

$$
\mathcal Q^{(m)}_{w,h}(\{e_k\}):=\sum_{k=1}^m\langle e_k,\,K_{w,h}\,e_k\rangle,
$$

记 $\lambda_1^{\uparrow}\le\lambda_2^{\uparrow}\le\cdots$ 为 $K_{w,h}$ 的特征值（非降序，按重数计）。

### 定理 2.1（Ky Fan–Rayleigh–Ritz）

假设 $K_{w,h}$ 自伴（已满足），并假设 $K_{w,h}$ 为**紧自伴**（例如 $A$ 具纯点谱且 $h(\cdot)w_R(\cdot)$ 使 $f(A)$ 紧）**或**以下"有限维谱投影极限"处理：先在有限谱投影 $P_\Lambda$ 上研究 $P_\Lambda K_{w,h}P_\Lambda$ 的 Ky Fan–Rayleigh–Ritz，再令 $\Lambda\uparrow\sigma(A)$。对每个 $m$,

$$
\inf_{\{e_k\},\text{正交基}}\ \mathcal Q^{(m)}_{w,h}(\{e_k\})
=\sum_{k=1}^m\lambda_k^{\uparrow}(K_{w,h}),
$$

**在紧/离散谱前提下**等号当且仅当 $\{e_k\}_{k\le m}$ 张成最小 $m$ 个特征值对应的特征子空间；若含连续谱，则只得到**下确界**版本。若存在一族可分辨窗 $\mathcal W$，使同一基 $\{e_k\}$ 对所有 $w\in\mathcal W$ 与所有 $m$ 上式均取到下确界，则 $\{e_k\}$ 同时对角化 $\{K_{w,h}:w\in\mathcal W\}$。当 $\{E\mapsto h(E)w_R(E):w\in\mathcal W\}$ 复共轭封闭且连同常数函数生成的交换 $*$-代数在 $C_0(\sigma(A))$ 中稠密（Stone–Weierstrass）时，$\{e_k\}$ 亦对角化 $\Pi_A$，即与 $A$ 的谱分解一致（直接积分意义；纯点谱时为"本征基（**模退化**，不能区分退化子空间内的基）"）。∎

---

## 3. Windows = 极大极小最优

### 3.1 误差对手与鲁棒目标

对

$$
g(E)=w_R(E)\cdot\big(h\ast\rho_{\rm rel}\big)(E),
$$

离散—连续差的非渐近上界为

$$
\sum_{m\ne0}\big|\widehat g(2\pi m/\Delta)\big|
+\sum_{j=1}^{M-1}\frac{|B_{2j}|}{(2j)!}\,\Delta^{2j}\!\int_{\mathbb R}\big|g^{(2j)}(E)\big|\,dE
+\int_{|E|>T}\!\!\big|g(E)\big|\,dE.
$$

此三项上界需 $g$ 至少具 $M$ 阶可积导数与足够衰减（Schwartz 情形最安全）；若 $\mathrm{supp}\,\widehat g\subset(-\pi/\Delta,\pi/\Delta)$（即 Nyquist 充分条件），则**别名项为零**。

据此定义对手—鲁棒目标

$$
\mathcal J(w):=\sup_{|h|_{\mathfrak H}\le1}\ \mathfrak E\!\big((h\ast\rho_{\rm rel})\cdot w_R\big),
\qquad w\in\mathsf{PW}^{\rm even}_\Omega,\ w(0)=1,
$$

其中 $\mathfrak E(\cdot)$ 为上式右端误差泛函，$|h|_{\mathfrak H}$ 为核函数的适当范数（例如取 $|h|_{\mathfrak H}=\sum_{j=0}^{M-1}\alpha_j|h^{(j)}|_{L^1}$ 或 $L^2$ 形式，以确保上确界良定）。**本节的鲁棒上界为构造性上界**，非最优上界；采样满足 Nyquist 时别名项可忽略。

### 3.2 强凸代理、存在唯一与 KKT

以强凸代理上确界 $\mathcal J$：

$$
\min_{w\in\mathsf{PW}^{\rm even}_\Omega}
\ \sum_{j=1}^{M-1}\gamma_j\,|w_R^{(2j)}|_{L^2}^2
+\lambda\,|\mathbf 1_{\{|E|>T\}}\,w_R|_{L^2}^2,
$$

存在唯一极小元 $w^\star$。其 Fourier 侧满足**带限投影—KKT**（$\chi_B:=\chi_{[-\Omega/R,\Omega/R]}$）：

$$
\boxed{
\chi_B(\xi)\!\cdot\!\Bigg(
\underbrace{2\sum_{j=1}^{M-1}\gamma_j\,\xi^{4j}\,\widehat{w_R^\star}(\xi)}_{\text{导数罚}}
+\underbrace{\tfrac{2\lambda}{2\pi}\,\big(\widehat{\mathbf 1_{|E|>T}}\!\ast\widehat{w_R^\star}\big)(\xi)}_{\text{尾部罚（单卷积）}}
\Bigg)
=\eta\,\chi_B(\xi)
}
$$

其中 $\eta$ 为归一约束的拉格朗日乘子常数，$B=[-\Omega/R,\Omega/R]$，且 $\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$。**常数规范**：在本文的非角频率规范下，导数项前有系数 $2$（来自 $L^2$ 泛函的梯度），尾部罚系数为 $\tfrac{2\lambda}{2\pi}$（来自时域指示函数乘积的频域单卷积与 Parseval）。
**意义**：前项为"曲率惩罚"$(2j)$ 阶导数的频域像（$\xi^{4j}$），"尾项罚"源于能量域乘法，故在频域表现为**单卷积**；带限约束通过频域投影 $\chi_B$ 表达。有限阶 EM 确保"奇性不增、极阶不升"。

---

## 4. 相位导数 = 谱密度与窗化读数

由 §0.3 之链条

$$
\det S(E)=\exp\!\bigl(-2\pi i\,\xi(E)\bigr),\qquad
\varphi'(E)=\pi\,\xi'(E)=\pi\,\rho_{\rm rel}(E),
$$

结合 §0.4 的 Wigner–Smith 关系 $\tfrac{1}{2\pi}\operatorname{tr}Q(E)=-\xi'(E)$，在本文规范下 $\operatorname{tr}Q=-2\varphi'(E)$。得"窗化读数方程"

$$
\mathcal S(h;R)
=\int_{\mathbb R} h(E)\,w_R(E)\,\rho_{\rm rel}(E)\,dE
+\text{alias}+\text{EM}+\text{tail},
$$

在"带限 + Nyquist + 有限阶 EM"纪律下实现非渐近闭合。这把 Born/I-投影与指针极小兼容到同一 **LDOS** 主项之上。

---

## 5. 推论与实例

### 5.1 延迟/驻留时间与 LDOS

$$
\boxed{\ \tfrac{1}{2\pi}\operatorname{tr}Q(E)=-\xi'(E)=-\rho_{\rm rel}(E)\ }.
$$

（与 $\varphi'=\pi\xi'$ 一致，因而 $\operatorname{tr}Q=-2\varphi'$；与 §0.3–0.4 的规范声明一致。）该等式对单通道与多通道的 $\operatorname{tr}Q$ 同样成立。由 §4 窗化读数主项即相对 LDOS；指针极小与能量/信息读数在本征基上最干净一致。

### 5.2 POVM 与噪声

POVM 情形先经 **Naimark 扩张** $E_i=V^\dagger\Pi_iV$ 至扩张空间的 PVM $\{\Pi_i\}$，在该空间复用 §1 的 PVM 论证，再投回原空间，故结论逐项成立。带噪场景可通过指数族—Bregman 对偶与鲁棒窗设计共同处理。

### 5.3 离散图/算子模型

对非回溯算子或离散散射，BK 链条与窗化迹公式形式平行；指针极小对应算子本征基，与 §2 之结论一致。

---

## 6. 三位一体定理（统一表述）

**定理 6.1（Trinity Theorem）**
在 DBK 光谱模型存在、Birman–Kreĭn 公式与 Wigner–Smith 矩阵关系成立、采用对偶窗/核与**有限阶** Euler–Maclaurin 换序，并在带限偶窗与 Nyquist/指数衰减等可行性条件下，对任意纯态 $\psi$、PVM（或 POVM）测量、可分辨窗族 $\mathcal W$ 与可检核 $h$，有：
（i）**Born = I-投影（iff）**：由窗口化读数诱导的最优概率 $p^\star$ 为线性对齐族上的 I-投影，当且仅当 $p^\star_i=\langle\psi,P_i\psi\rangle$（POVM 时 $p^\star_i=\langle\psi,E_i\psi\rangle$）。
（ii）**Pointer = 光谱极小（iff）**：使 $\mathcal Q^{(m)}_{w,h}$ 在所有正交基上对每个 $m$ 与每个 $w\in\mathcal W$ 取下确界的基，当且仅当为 $A$ 的光谱本征基（模退化）。
（iii）**Windows = 极大极小最优**：存在（Hilbert 强凸代理下唯一）$w^\star\in\mathsf{PW}^{\rm even}_\Omega$ 最小化鲁棒上界 $\mathcal J$，其 Fourier 侧满足带限投影—KKT 方程。∎

---

## 7. 与既有理论的接口

* **S15（Weyl–Heisenberg 酉表示）**：窗族 $U_\tau V_\sigma w$ 的协变性保证 Ky Fan 部分和在群作用下不变；等距性使信息势 $\Lambda$ 在群平均下保持。
* **S16（de Branges–Krein 规范系统）**：本文 $m$ 为 Herglotz–Nevanlinna 函数并与规范系统等价；传递矩阵 $M(t,z)$ 的 $J$-酉性保证 $\Im m>0$，从而 $\rho_m\ge 0$。
* **S17（散射算子与功能方程）**：§4 的 $\varphi'=\pi\rho_{\rm rel}$ 即 S17 散射相位导数判据；通道特征值等价给出 $\det S=c_0U$ 的相位—密度词典。
* **S18（轨道—谱窗化不等式）**：§3.1 的三分解误差与 S18 §3.3 统一非渐近上界对齐；Nyquist 条件下别名归零对应 S18 带限假设。
* **S19（谱图与 Ihara ζ）**：离散图的非回溯算子给出"离散相位导数 = 离散谱密度"；定理 2.1 的 Ky Fan 极小对应离散算子本征基。
* **S20（BN 投影—KL 代价—灵敏度）**：定理 1.1 的 I-投影直接调用 S20 §2 的 Bregman–KL 恒等式；几何—信息等价对应 S20 定理 2.2。
* **S21（连续谱阈值与奇性稳定性）**：§4 的 $\varphi'=\pi\rho_{\rm rel}$ 对应 S21 §0.2 相位—密度同一式；有限阶 EM 确保奇性不增依赖 S21 定理 21.6。
* **S22（窗/核最优化）**：§3.2 的 KKT 方程对应 S22 式（2.2）；强凸代理与存在唯一性继承 S22 定理 2.1。
* **S23（多窗/多核协同优化）**：本文单窗最优可推广至 S23 向量窗与帧算子层面；定理 2.1 的 Ky Fan 极小对应 S23 §5 的双帧结构。
* **量子读数理论（phase-derivative-spectral-density-windowed-readout.md）**：§4 的窗化读数方程即该文 §3 的定理 1.1；§0.3-0.4 的相位—谱移—延迟链条对应该文定理 2.1 与命题 4.2。
* **统一测量理论（unified-measurement-born-kl-pointer-basis.md）**：定理 1.1 的 Born = I-投影对应该文主定理 II；定理 2.1 的 Pointer = 光谱极小对应该文主定理 III 的指针基判据；§3 的 Windows 最优对应该文 §5 的窗/核最优化。

---

## 8. 结论

本文在**光谱—信息—数值**三重结构上，给出了窗口化测量的"Born = I-投影（iff）—Pointer = 光谱极小（iff）—Windows = 极大极小最优"的统一定理。Birman–Kreĭn 与 Wigner–Smith 提供相位—谱密度的物理-数学桥；Ky Fan 原理刻画指针极小与本征基的等价；Paley–Wiener 与 Nyquist–Poisson–Euler–Maclaurin 则保证有限带宽/有限时间实现的非渐近误差闭合。定理为现实测量中的概率读数、指针选择与窗/核设计给出严格且可操作的准则。

---

## 参考文献（选）

* de Branges, **Hilbert Spaces of Entire Functions**, Prentice-Hall, 1968.
* Wigner, **Lower Limit for the Energy Derivative of the Scattering Phase Shift**, Phys. Rev. 98, 145 (1955).
* Smith, **Lifetime Matrix in Collision Theory**, Phys. Rev. 118, 349 (1960).
* Birman–Kreĭn, **On the theory of wave operators and scattering operators**, Dokl. Akad. Nauk SSSR 144, 475 (1962).
* Ky Fan, **On a theorem of Weyl concerning eigenvalues of linear transformations I**, Proc. Natl. Acad. Sci. USA 35, 652 (1949).
* Csiszár, **I-divergence geometry of probability distributions and minimization problems**, Ann. Probab. 3, 146 (1975).
* Slepian–Pollak, **Prolate Spheroidal Wave Functions, I**, Bell Syst. Tech. J. 40, 43 (1961).

---

## 附录：术语索引与公式索引（便于检索）

* **DBK 光谱表示**、**Weyl–Titchmarsh**：Herglotz–Weyl 词典与规范系统。
* **Birman–Kreĭn 公式**：$\det S=e^{-2\pi i\,\xi}$，$\dfrac{d}{dE}\arg\det S=-2\pi\,\xi'$。
* **Wigner–Smith 延迟**：$Q=-\,i\,S^\dagger\dfrac{dS}{dE}$ 自伴，$\boxed{\tfrac{1}{2\pi}\operatorname{tr}Q=-\,\xi'(E)=-\,\rho_{\rm rel}(E)}$；与 §0.3 之 $\varphi'(E)=\pi\,\xi'(E)$ 一致，故 $\operatorname{tr}Q=-2\,\varphi'(E)$。
* **Ky Fan–Rayleigh–Ritz**：部分和极值与最小特征子空间（模退化）。
* **I-投影/指数族–Bregman 对偶**：线性对齐族上的存在唯一性；POVM 用 Naimark 扩张。
* **三分解误差**：alias + 有限阶 EM（伯努利层） + tail；带限 + Nyquist 下 alias 消失。
* **KKT（带限投影）**：$\chi_B(\xi)\!\cdot\!\Big( \underbrace{2\sum_{j=1}^{M-1}\gamma_j\,\xi^{4j}\,\widehat{w_R^\star}(\xi)}_{\text{导数罚}}+\underbrace{\tfrac{2\lambda}{2\pi}\,(\widehat{\mathbf 1_{|E|>T}}\!\ast\widehat{w_R^\star})(\xi)}_{\text{尾部罚（单卷积）}} \Big)=\eta\,\chi_B(\xi)$，其中 $B=[-\Omega/R,\Omega/R]$。

---

**关键词**：Birman–Kreĭn 公式；谱移函数；Wigner–Smith 延迟；de Branges–Kreĭn 规范系统；I-投影；Bregman 散度；Ky Fan 原理；Nyquist–Poisson–Euler–Maclaurin；Paley–Wiener 带限窗；窗化迹/LDOS

（全文完）
