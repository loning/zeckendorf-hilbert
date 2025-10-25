# EBOC-Graph：静态块宇宙的测量—提交统一理论

**（Born = 信息投影，Pointer = 光谱极小，Windows = 极大极小）**

**日期：** 2025-10-25

---

## 摘要（定性）

在**静态块宇宙（EBOC）**视角下，现实是一份一次性存在的图结构"块"；观测是对块的**叶读取**，而"提交"是带约束的信息最小化选择。本文以**图谱—凸优化—帧采样**为骨架，建立四个互锁的可证命题：（G1）**Born 概率 = KL 信息投影（充要）**；（G2）**指针基 = 光谱极小（充要）**；（G3）**窗/核设计 = 极大极小最优（充要）**；（G4）**非渐近误差闭合**＝谱泄露 + 采样帧误差 + 切比近似尾项。上述结论与图信号处理（谱滤波、切比多项式逼近）、等波纹最小极大准则、带限采样/帧理论、以及 I-投影/信息几何的经典结果一致，并在其上给出资源受限场景下的**可判性下界**。这些判据为 EBOC-Graph 的端到端可复核实现提供了严整的数学脊梁。

---

## 1. 引言与贡献

EBOC 把"块→叶→提交"的观测链条内化为图 $G=(V,E)$ 上的谱滤波与统计决策：块态是顶点信号 $X:V\to\mathbb C$，叶读取由图谱核 $H=\phi(L)$（$L$ 为图拉普拉斯或其规范化）和非负窗 $W$ 推前，提交则是在仿射矩约束下对分布作 KL/Bregman 最小化的 I-投影。该建模与图信号处理中"线性滤波 = 谱函数 $\phi(L)$"完全一致，且可由**切比多项式**在 $[-1,1]$ 归一化谱上快速实现；POVM-化的读数与 Born 规则提供物理诠释；带限采样与帧理论保障数值稳定与重构可行。

**本文贡献（均给出"充要/非渐近界/构造性实现"）**：

(i) **G1**：在叶上线性矩约束下，$\min\mathrm{KL}(p\|q)$ 的解与 Born 概率一致之**充要条件**（KKT 指数族 + Pythagorean 身份）；

(ii) **G2**：最稳读数等价于最小化 $\langle HX,\Psi HX\rangle$ 的**Rayleigh–Ritz**极小本征模；

(iii) **G3**：窗/核的频域极小极大最优之**等波纹**必要条件与切比实现；

(iv) **G4**：一次性**非渐近误差闭合**（谱泄露 + 帧误差 + 切比尾项 $O(\rho^{-m})$）；并在检验设定下给出 $N=\Omega(r^{-2})$ 的样本下界（Le Cam + Pinsker）。

---

## 2. 预备、记号与公设（图版）

* 图 $G=(V,E)$，度矩阵 $D$，（规范化）拉普拉斯 $L$ 或 $\mathcal L$。$\ell^2(V,w_V)$ 内积 $\langle f,g\rangle=\sum_{v\in V}\overline{f(v)}g(v)\,w_V(v)$。
* **谱滤波器**：$H=\phi(L)$；数值实现以切比展开 $H_m=\sum_{k=0}^m a_k T_k(\tilde L)$（$\tilde L$ 把谱仿射至 $[-1,1]$，$T_k$ 为**第一类切比多项式**）。
* **窗**：$W:V\to\mathbb R_{\ge0}$，$\Psi=\operatorname{diag}(W)\succeq0$。
* **带限类**：$\mathcal B_\Omega=\operatorname{span}\{u_\ell:\lambda_\ell\le\Omega\}$。
* **采样与帧**：$\mathsf P_S$ 在 $\mathcal B_\Omega$ 上满足帧界 $A\|X\|^2\le\|\mathsf P_S X\|^2\le B\|X\|^2$。
* **子归一化读数**：柔叶 $\{M_j\}_{j=1}^n$ 非负且 $\sum_j M_j=\mathbf1$。令 $E_j=\Psi^{1/2}M_j\Psi^{1/2}\succeq0$，$\sum_jE_j=\Psi$（**子归一化 effect 集**，经归一化获得 POVM 概率）。Born-型概率

$$
p_j(X)\coloneqq\frac{\langle HX,\ E_j\ HX\rangle}{\sum_i\langle HX,\ E_i\ HX\rangle}
=\frac{\|M_j^{1/2}\Psi^{1/2}HX\|_2^2}{\sum_i\|M_i^{1/2}\Psi^{1/2}HX\|_2^2}\in[0,1],\qquad p(X)\in\Delta_n.
$$

**公设（C0g–C5g）**：

(C0g) $\phi$ 连续有界，谱 $\sigma(L)\subset[0,\lambda_{\max}]$；(C1g) 相关和/内积可由 $\ell^1/\ell^2$ 主导；(C2g) 切比近似尾项服从**Bernstein 椭圆**界 $\lesssim C_\phi\rho^{-m}$；(C3g) $(S,\Omega)$ 构成带限帧；(C4g) 提交约束集仿射线性且 KL 在单纯形上严格凸，**约束集与单纯形内点相交**（相对内点）；(C5g) $\|W\|_{\infty}<\infty$ 保证 $\Psi$ 有界且 $H^\ast\Psi H$ 有定义，且对所有研究态 $X$，$\langle HX,\Psi HX\rangle>0$。

**约定**：本文所有 $\log$ 均指 $\ln$；所有内积与范数默认在 $\ell^2(V,w_V)$ 上。

---

## 3. 模型：块→叶→提交

**定义 3.1（叶读数）** 设柔叶 $\{M_j\}$，$\sum_j M_j=\mathbf1$，$M_j\succeq0$。令 $E_j=\Psi^{1/2}M_j\Psi^{1/2}\succeq0$，$\sum_jE_j=\Psi$。定义

$$
p_j(X)\coloneqq\frac{\langle HX,\ E_j\ HX\rangle}{\sum_i\langle HX,\ E_i\ HX\rangle}
=\frac{\|M_j^{1/2}\Psi^{1/2}HX\|_2^2}{\sum_i\|M_i^{1/2}\Psi^{1/2}HX\|_2^2}\in[0,1].
$$

**约定**：若 $\langle HX,\Psi HX\rangle=0$，则令 $p(X)=q$（或均匀）以作缺省；更一般地，$\{E_j\}$ 为**子归一化 effect 集**（$\sum_jE_j=\Psi$），上式给出**在窗事件上条件化**的 Born 概率。此缺省规则与公设 (C5g) 要求 $\langle HX,\Psi HX\rangle>0$ 并行不悖：(C5g) 确保正常情形下分母非零，而缺省规则处理边界或退化情形。

以上与量子 POVM 的 Born 规则一致，且与 4.节的能量型泛函保持一致性。

**定义 3.2（提交/选择 = I-投影）** 设参照分布 $q\in\Delta_n$，线性矩约束

$$
\mathcal C(X)=\{p\in\Delta_n:\ \sum_j a_{\ell j}p_j=b_\ell(X),\ \ell=1,\dots,L\}.
$$

**提交**定义为 I-投影

$$
\operatorname{Commit}(X)=\arg\min_{p\in\mathcal C(X)}\mathrm{KL}(p\|q).
$$

I-投影的存在唯一性、指数族形式与**Pythagorean 身份**来自 Csiszár 与信息几何。

---

## 4. 主定理与证明

### 定理 G1（Born = I-投影，充要）

**假设（G1-Q）**：$q\in\Delta_n$ 满支撑且 $\{p\in\Delta_n:Ap=b(X)\}$ 与单纯形内点相交（相对内点）。此时 I-投影存在唯一，且最优解满足 $p^\star_j\propto q_j\exp(\lambda^\top a_j)$ 与 Pythagorean 恒等式。

设矩阵 $A=[a_{\ell j}]$ 使 $\mathcal C(X)$ 非空且满足上述条件。记

$$
p^{\mathrm{Born}}_j(X)=\frac{\langle HX,\ E_j\ HX\rangle}{\sum_i\langle HX,\ E_i\ HX\rangle}.
$$

则

$$
\operatorname{Commit}(X)=p^{\mathrm{Born}}(X)
\iff
\Big(\,Ap^{\mathrm{Born}}(X)=b(X)\ \ \text{且}\ 
\log p^{\mathrm{Born}}-\log q\in \mathrm{span}\{a_\ell\}\oplus \mathbb R\mathbf 1\,\Big).
$$

等价地：存在 $\lambda$ 使 $p^{\mathrm{Born}}_j\propto q_j\exp\!\Big(\sum_{\ell=1}^L\lambda_\ell a_{\ell j}\Big)$ 且 $Ap^{\mathrm{Born}}=b(X)$。

**证明（提纲）**。KKT 条件给出任意最优解 $p^\star$ 的指数族形式 $p^\star_j\propto q_j\exp(\lambda^\top a_j)$。KL 的严格凸性与可识别性给唯一性。若存在 $\lambda$ 使上式由 $p^{\mathrm{Born}}$ 满足，则其既可行又最优；反向由信息几何的 Pythagorean 身份与 Bregman 对偶射影唯一性导出必要性。与 POVM-Born 读数之等价性由定义 3.1 直接得到。∎

**注**：唯一性由 KL 严格凸与相对内点保证（Csiszár；Amari–Nagaoka 的 Pythagorean 身份）。

**推论 4.1（稳健性）** 若 $b\mapsto\lambda(b)$ 在内点处可微，则 $p^\star(b)$ 对 $b$ Lipschitz 连续；对数势的强凸性常数给出模常数。

---

### 定理 G2（Pointer = 光谱极小，充要）

定义代价 $\mathfrak E(X;W,H)=\langle HX,\Psi HX\rangle=\langle X, H^\ast\Psi H\,X\rangle$。在 $\mathcal B_\Omega$ 且 $\|X\|=1$ 上极小化 $\mathfrak E$；极小点当且仅当属于 $H^\ast\Psi H$ 在 $\mathcal B_\Omega$ 的最小本征子空间；若最小与次小本征值间存在谱隙 $\delta>0$，则该子空间对有界扰动满足 Davis–Kahan 型稳定界。

**证明**。Rayleigh–Ritz 变分原理：$\min_{\|X\|=1,\,X\in\mathcal B_\Omega}\langle X, H^\ast\Psi H\,X\rangle$ 在 $H^\ast\Psi H$ 于 $\mathcal B_\Omega$ 的最小本征空间取得；必要性与充分性来自 Hermitian 情形的极值表征。∎

**注记**。当 $H=\phi(L)$ 且 $\Psi\succeq0$ 时，$H^\ast\Psi H$ 自伴 $\succeq0$。

**推论 4.2（扰动稳定性）** 设 $A=H^\ast\Psi H$。若 $\|E\|_2\le\varepsilon$，则 $|\lambda_{\min}(A+E)-\lambda_{\min}(A)|\le \varepsilon$（Weyl 不等式）；最小本征子空间与原子空间的夹角由 Davis–Kahan 型界控制（需谱隙 $\delta>0$）。

---

### 定理 G3（Windows = 极大极小最优，充要）

设目标带宽 $[0,\Omega]$、切比次数 $m$ 与固定权 $w_P,w_S\ge0$。定义

$$
\mathcal E(W,\phi,m;S)
=\sup_{\lambda\in[0,\Omega]} w_P(\lambda)\,|\phi(\lambda)-1|
+\sup_{\lambda\notin[0,\Omega]} w_S(\lambda)\,|\phi(\lambda)|
+\kappa(S,\Omega)+C_\phi\rho^{-m},
$$

其中 $\kappa(S,\Omega)=\sqrt{B/A}-1$，$\rho>1$ 为目标函数在 Bernstein 椭圆内的解析半径。在参数集取紧（如 $m\le m_{\max}$、窗幅与支撑有界、$S$ 取自有限候选集）时最优点存在。则存在最优 $(W^\ast,\phi^\ast,m^\ast,S^\ast)$ 使$^*$

> $^*$ 当参数集取为紧集时，最优点存在；否则存在下确界与极小序列。

$$
\mathcal E(W^\ast,\phi^\ast,m^\ast;S^\ast)
=\inf_{W,\phi,m,S}\ \sup_{X\in\mathcal B_\Omega}\mathcal E(W,\phi,m;S).
$$

对**固定** $S,\Omega,m$ 的 $\phi$-子问题，若将 $\phi$ 限定为次数 $\le m$ 的多项式（或切比展开截断），则**等波纹/交错**性质为极小极大解之**必要且充要**。总体最优仍由 $\kappa(S,\Omega)$ 与 $\rho^{-m}$ 的权衡决定。

**证明要点**。对固定 $S,\Omega,m$，$|\cdot|_\infty$ 极小极大逼近的 Chebyshev 等波纹定理给出 $\phi$-子问题的必要且充要条件；切比逼近的几何级尾项源自 Bernstein 椭圆，次数–精度关系 $m\sim \log\varepsilon^{-1}/\log\rho$；采样稳定性由带限帧界量化并可通过谱代理/贪心选点提升帧下界。∎

---

### 定理 G4（读数的非渐近误差闭合）

对任意 $X\in\mathcal B_\Omega$，以 $H_m$ 近似 $H$，并在采样集 $S$ 上读数与重构。令 $\Delta H=H_m-H$，$\mathfrak E(X;W,H)=\langle HX,\Psi HX\rangle$。则存在常数 $C_\phi,\rho>1$ 使

$$
\big|\ \mathfrak E(X;W,H_m)-\mathfrak E(X;W,H)\ \big|
\le \|\Psi\|\big(\|H\|+\|H_m\|\big)\,\|\Delta H\|\,\|X\|^2+\kappa(S,\Omega)\,\|HX\|^2,
$$

且 $\|\Delta H\|\le\|\phi_m-\phi\|_{L^\infty(\sigma(L))}\le C_\phi\rho^{-m}$。若 $X$ 非严格带限，则额外出现项 $\sup_{\lambda>\Omega}|\phi(\lambda)|\,\|P_{>\Omega}X\|^2$。

若某读数是 $\mathfrak E$ 的 1-Lipschitz 函数（如加权归一化），同阶界亦成立。

**证明**。算子范数逼近误差 $\|\Delta H\|$ 由 Chebyshev/Bernstein 椭圆界控制；帧误差由 $(A,B)$ 帧界量化；模型失配（若存在）源自超带能量。∎

---

## 5. 资源受限的可判性（下界）

对二元检验 $(H_0,H_1)$，任意流程在显著性 $\alpha$、功效 $1-\beta$ 下的样本需求满足

$$
\boxed{\quad N\ \ge\ \frac{\log\!\big(\tfrac{1}{2(\alpha+\beta)}\big)}{\,\mathrm{KL}(P\|Q)\,}\quad}
$$

（Bretagnolle–Huber，不等式对自然对数成立）。若仅掌握分离度的**总变差**指标，可用 Pinsker 给出**更弱的量级推断**

$$
\mathrm{KL}(P\|Q)\ \ge\ 2\,\mathrm{TV}(P,Q)^2\ \ \Rightarrow\ \ N\ \gtrsim\ \frac{\log\!\big(\tfrac{1}{2(\alpha+\beta)}\big)}{\ \mathrm{TV}(P,Q)^2\ } \ \ \text{（仅作尺度级别的保守估计）},
$$

因此应以 **KL 版**作为严格的分布无关下界；**TV 版不可与 KL 版"等价互换"**。

**证明提纲**。Le Cam 两点法把下界化为二分布检验；Bretagnolle–Huber 不等式给出 $\alpha+\beta \ge \tfrac12 e^{-N\,\mathrm{KL}(P\|Q)}$，等价重排得上述 KL-式下界；Pinsker 不等式 $\mathrm{KL}(P\|Q)\ge 2\,\mathrm{TV}(P,Q)^2$ 仅可用于把 KL-式下界松弛成 TV 的量级估计。∎

---

## 6. 进一步性质：稳定性与一致性

**命题 6.1（I-投影的连续依赖）** 若约束 $Ap=b$ 的右端 $b$ 与参照 $q$ 作小扰动，则 $\lambda(b)$ 和 $p^\star(b)$ 对 $b$ 连续（在内点为光滑），模常数由对数势的强凸性与 $A$ 的条件数界定。

**命题 6.2（Pointer 的矩阵扰动）** 设 $A=H^\ast\Psi H$。若扰动 $E$ 满足 $\|E\|_2\le \varepsilon$，则

$$
|\lambda_{\min}(A+E)-\lambda_{\min}(A)|\le \varepsilon \quad\text{（Weyl 不等式）}.
$$

最小本征子空间与原子空间的夹角由 Davis–Kahan 型界控制（与"推论 4.2"一致）。

**命题 6.3（图→经典的一致性）** 当 $G$ 的谱趋于连续谱且 $\mathcal B_\Omega$ 的图 Paley–Wiener 类在网格细化极限下收敛，采样—重构与误差闭合退化为经典带限信号论；帧常数与 Shannon 采样常数相容。

---

## 7. 实现蓝图（可复现实用要点）

* **核设计（切比—等波纹）**：把谱仿射至 $[-1,1]$，指定通/阻带与权重，按 Remez 交换求极小极大 $\phi^\ast$（Parks–McClellan 传统），次数 $m\sim \log(\varepsilon^{-1})/\log\rho$。
* **快速滤波**：用切比递推实现 $H_m=\sum_{k=0}^m a_k T_k(\tilde L)$ 的线性算子作用，无需特征分解。
* **采样集选择**：以谱代理最大化帧下界 $A$（或最小化 $\kappa=\sqrt{B/A}-1$）。
* **提交阶段**：把观测统计写成 $Ap=b$，参照 $q$ 取装置平衡；解 $p^\star_j\propto q_j\exp(\lambda^\top a_j)$ 并校验 G1 的充要条件。

---

## 8. 与现有文献的对应与拓展（择要）

* **图谱滤波与切比实现**：$H=\phi(L)$ 与切比逼近是 GSP 教程与"图小波"的标准做法；本文把其与极小极大准则及误差闭合拼装为端到端判据。
* **等波纹/极小极大**：Parks–McClellan 源自 Remez 与 Chebyshev 交错等幅定理（必要且充要）；本文把其搬到图谱域并与帧稳定性耦合。
* **带限采样与帧**：Paley–Wiener 图带限采样、帧重构与采样集选择给出稳定性与鲁棒性工具。
* **I-投影/信息几何**：Csiszár 的 I-投影几何与 Amari-Nagaoka 的 Pythagorean 身份支撑 G1 的充要性。
* **近似论尾项**：Bernstein 椭圆给出 $\rho^{-m}$ 衰减与明确常数，支撑 G3/G4。

---

## 9. 与前序理论的接口

### 9.1 与 Euler 理论系列（S15–S25）的联结

虽然 EBOC-Graph 理论主要基于图论框架，但与 Euler 系列（S15–S25）存在深刻的结构对应：

**与 S15（Weyl–Heisenberg）**：
- 图拉普拉斯 $L$ 的谱分解对应 S15 的 Weyl–Heisenberg 酉表示；
- 谱滤波器 $\phi(L)$ 对应 S15 的窗函数诱导的 RKHS 内积。

**与 S18（窗不等式）**：
- 定理 G3 的带限采样条件对应 S18 的 Nyquist 条件；
- 帧界 $[A,B]$ 对应 S18 的窗加权半范数等价常数。

**与 S20（BN–Bregman）**：
- 定理 G1 的 I-投影即 S20 的 KL 最小化（I-projection）；
- KKT 指数族形式对应 S20 的 Bregman 几何最优性条件。

**与 S21（奇性稳定）**：
- 定理 G4 的非渐近误差闭合对应 S21 的有限阶 EM 误差分解；
- 切比尾项 $O(\rho^{-m})$ 对应 S21 的"极点 = 主尺度"保持原则。

**与 S22（窗/核最优）**：
- 定理 G3 的等波纹极小极大条件对应 S22 的带限偶窗变分原理；
- Remez 交换算法对应 S22 的频域核型 Euler–Lagrange 方程。

**与 S24（紧框架）**：
- 采样帧条件 $A\|X\|^2\le\|\mathsf P_S X\|^2\le B\|X\|^2$ 对应 S24 的 Calderón–帧界判据；
- 图带限类 $\mathcal B_\Omega$ 对应 S24 的 Paley–Wiener 偶子空间。

**与 S25（非平稳框架）**：
- 分块谱滤波对应 S25 的分块非平稳 Weyl–Mellin 系统；
- 定理 G3 的谱泄露控制对应 S25 的"无混叠"条件。

### 9.2 与量子理论的联结

**与量子测量理论**：
- 定义 3.1 的 POVM-化读数与量子测量的 Born 规则一致；
- 定理 G1 的充要条件提供了 Born 概率与信息几何的统一框架。

**与指针基理论**：
- 定理 G2 的 Rayleigh–Ritz 极小本征模对应指针基的环境选择；
- $H^\ast\Psi H$ 的最小本征空间对应最稳定的测量基。

### 9.3 统一框架的可证性

本理论的所有主定理（G1–G4）均基于严格的数学证明：
- G1 基于 Csiszár 的 I-投影理论与信息几何的 Pythagorean 身份；
- G2 基于 Rayleigh–Ritz 变分原理与谱理论；
- G3 基于 Chebyshev 等波纹定理与 Bernstein 椭圆近似；
- G4 基于帧理论与函数逼近论的非渐近界。

这些结果为 EBOC-Graph 提供了与 S15–S25 理论体系一致的、可验证的数学基础。

---

## 10. 结论

本文在 EBOC-Graph 中把"块—叶—提交"统一到严整的**图谱—凸优化—帧采样**骨架：

$$
\text{Born = I-投影（充要）},\ \text{Pointer = 光谱极小（充要）},\ \text{Windows = 极大极小（充要）},
$$

并给出一次性的**非渐近误差闭合**与**样本下界**。上述判据与实现路径与 GSP、信息几何与等波纹经典理论相容且延伸，为静态块宇宙的图论表述提供了**可复核、可实现**的理论与算法基座。

---

## 参考文献（选）

1. Shuman, Narang, Frossard, Ortega, Vandergheynst, "The Emerging Field of Signal Processing on Graphs," *IEEE Signal Process. Mag.*, 2013（GSP 教程；谱滤波与多项式实现）。
2. Hammond, Vandergheynst, Gribonval, "Wavelets on Graphs via Spectral Graph Theory," *Appl. Comput. Harmon. Anal.*, 2011（图小波；切比近似快速算法）。
3. Csiszár, "I-Divergence Geometry of Probability Distributions and Minimization Problems," *Ann. Probab.*, 1975（I-投影/KKT/Pythagorean）。
4. Amari & Nagaoka, *Methods of Information Geometry*, 2000（信息几何；Bregman 对偶）。
5. Nielsen & Chuang, *Quantum Computation and Quantum Information*, 10th Anniversary Ed.（POVM 与 Born 规则）。
6. Parks & McClellan, "Chebyshev Approximation for Nonrecursive Digital Filters with Linear Phase," *IEEE Trans. Circuit Theory*, 1972（等波纹最优与 Remez 交换）。
7. Pesenson, "Sampling in Paley–Wiener Spaces on Combinatorial Graphs," *Trans. Amer. Math. Soc.*, 2008（图带限采样与帧）。
8. Chen, Varma, Sandryhaila, Kovačević, "Discrete Signal Processing on Graphs: Sampling Theory," *IEEE Trans. Signal Process.*, 2015。
9. Tsitsvero, Barbarossa, Di Lorenzo, "Signals on Graphs: Uncertainty Principle and Sampling," *IEEE Trans. Signal Process.*, 2016。
10. Horn & Johnson, *Matrix Analysis*, 2nd ed.（Rayleigh–Ritz/变分原理与矩阵扰动）。
11. Trefethen, *Approximation Theory and Approximation Practice*, SIAM, 2013（Bernstein 椭圆与误差界）。
12. Tulsiani 等课程讲义，"Pinsker 不等式与下界"（用于 Le Cam + Pinsker）。

---

### 附录 A：切比窗的构造性实现（提纲）

1. 谱归一化 $\tilde L\in[-1,1]$，指定通/阻带与权；
2. 以 Remez/等波纹准则在两带上求极小极大 $\phi^\ast$；
3. 用切比 $T_k$ 逼近 $\phi^\ast$，次数 $m\sim \log(\varepsilon^{-1})/\log\rho$；
4. 选 $S$ 以最大化 $A$（可用谱代理/贪心）。

**离散谱注记**：图拉普拉斯谱为离散点集；实现层采用加权离散极小极大（或对连续代理密度作加权），Remez 交换仍可用，交错点数满足"维度+1"的变体。

### 附录 B：I-投影的 KKT 与 Pythagorean 身份

$$
\min_{p\in\Delta_n}\{\mathrm{KL}(p\|q):Ap=b\}\Rightarrow p^\star_j\propto q_j\exp(\lambda^\top a_j),
$$

且

$$
\mathrm{KL}(p\|q)=\mathrm{KL}(p\|p^\star)+\mathrm{KL}(p^\star\|q).
$$

指数族形式与几何恒等式见 Csiszár 与 Amari–Nagaoka。

### 附录 C：Bernstein 椭圆与切比尾项

若 $f$ 在 Bernstein 椭圆 $E_\rho$ 内解析且 $|f|\le M$，则最佳 $n$ 次切比逼近误差 $\|f-p_n\|_\infty\le 4M\rho^{-n}/(\rho-1)$。据此得 $C_\phi\,\rho^{-m}$ 级的尾项上界。
