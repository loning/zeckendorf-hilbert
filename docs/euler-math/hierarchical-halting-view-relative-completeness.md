# 层级化"停机"—"视角相对完备性"统一理论

（EBOC–WSIG–RBIT 框架下的形式化构建）
Version: 1.29

## 摘要

在窗化散射—信息几何（WSIG/CCS）、永恒静态块计算（EBOC）与有限资源不完备理论（RBIT）框架下，建立与视角及资源相关的层级化"停机"判据,并给出与采样—帧门槛、Poisson–Euler–Maclaurin（EM）误差学及"三位一体"刻度（相位导数—相对态密度—群延迟）一致的等价定理。统一三位一体等式链的号志与分支规范,明确 $\Phi_f=\arg\det S$ 的绝对连续分支与 Birman–Kreĭn（BK）规范的互换使用；在算子层刻画"读数/指针"与 Ky–Fan 极小；在严格带限与紧帧的正则前提下收紧"采样-周期闭环"与"读数停机"的等价条件；并以哥德尔–柴廷型与扩展链不完备重述 RBIT 断言。

---

## 0. 记号、规范与正则纪律

### 0.1 视角四元与窗化读数

设**视角四元**为

$$
\mathrm{View}=(H_0,\,w_R,\,h,\,\mathsf{sample}),
$$

并引入**窗口中心参数** $c\in\mathbb R$。定义位移—尺度化窗

$$
w_{R,c}(E):=R^{-1}\,w\!\left(\frac{E-c}{R}\right).
$$

其中 $H_0$ 为参照端（散射对 $(H,H_0)$ 的自由端）,$w_R$ 为能量窗（尺度 $R$）,$h$ 为带限前端核,$\mathsf{sample}$ 为采样/帧方案（步长 $\Delta$、点集 $\Lambda$ 等）。窗化读数取

$$
\mathrm{Obs}(R,\Delta;\,c)=\int_{\mathbb R} w_{R,c}(E)\,\bigl(h\ast\rho_\star\bigr)(E)\,dE
+\varepsilon_{\mathrm{alias}}+\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}},
$$

其中 $\rho_\star$ 可取相对态密度 $\rho_{\mathrm{rel}}$ 或 Herglotz 密度 $\rho_m$。全篇统一采用标准卷积

$$
(h\ast\rho)(E):=\int_{\mathbb R} h(E-E')\,\rho(E')\,dE'.
$$

必要时以 $w_{R,c}$ 作加权测度,不影响正则与误差学结论。

**窗口归一化与基线（零和条件）**：采用二选一规范：

(A) **零均值窗**：$\int_{\mathbb R} w_R(E)\,dE=0$。

(B') **外定基线（非平凡零和）**：取与 $\rho_{\mathrm{rel}}$ 无关的 $c_R^{\mathrm{ext}}$（可由参照端 $H_0$ 的密度 $\rho_{m_0}$ 或独立低通校准得到）,定义 $\tilde\rho_{\mathrm{rel}}:=\rho_{\mathrm{rel}}-c_R^{\mathrm{ext}}$。此时

$$
\int_{\mathbb R} w_R\,\tilde\rho_{\mathrm{rel}}=0 \quad\Longleftrightarrow\quad
\int_{\mathbb R} w_R\,\rho_{\mathrm{rel}}=\Bigl(\int_{\mathbb R} w_R\Bigr)c_R^{\mathrm{ext}} .
$$

**等价性适用**：§2 的定理 A.1 一律在规范 (A) 或 (B') 下陈述,以避免内生基线造成的同义反复。

**平移不变性**：对任意 $c\in\mathbb R$,有

$$
\int_{\mathbb R} w_{R,c}(E)\,dE=\int_{\mathbb R} w_R(E)\,dE,
$$

因而规范 (A)/(B') 下的零和/基线关系与后续以 $w_{R,c}$ 表述的条件严格一致。

**（统一记号）** 为同时覆盖规范 (A)/(B'),记

$$
\bar\rho_{\mathrm{rel}}:=\begin{cases}
\rho_{\mathrm{rel}}, & \text{规范 (A)};\\[2pt]
\tilde\rho_{\mathrm{rel}}, & \text{规范 (B′)}.
\end{cases}
$$

后文凡述及"零和/平衡通量",一律以 $\bar\rho_{\mathrm{rel}}$ 表达；若采用平滑,则统一以 $h\ast\bar\rho_{\mathrm{rel}}$ 计。

**正则性与带限纪律（Poisson–EM 的非新增奇点）**：固定一个 **EM 截断阶** $M\ge 1$。为保证 Poisson–EM 误差闭合且不引入新奇点,要求 $h\in C^{2M}(\mathbb R)\cap L^1$、$w_R\in C_c^{2M}(\mathbb R)$ 或严格带限,且 $(h\ast\rho_\star)$ 的至多 $2M$ 阶导数在窗端点可积；则 EM 截断余项仅由端点导数与伯努利多项式构成,Poisson 项在带限或足够衰减下可审计或为零。

上述正则与 Poisson–EM 闭合**限定于** $\sigma_{\mathrm{ac}}(H)$ 内；对 $\sigma_{\mathrm{pp}}(H)$ 的 $\delta$-质量,采用 $w_R$ 支撑规避或以 $h$ 的平滑卷积抑制其贡献,从而保持"非新增奇点"。

### 0.2 窗化散射"三位一体"刻度（规范化、分支与 BK 号志）

在绝对连续谱上几乎处处,取散射矩阵 $S(E)\in U(N)$,Wigner–Smith 矩阵

$$
\mathsf Q(E):=-i\,S(E)^\dagger\,\partial_E S(E),
$$

全局相位

$$
\Phi_f(E):=\arg\det S(E),\qquad \varphi(E):=\tfrac12\,\Phi_f(E).
$$

定义相对态密度（Krein–Friedel 意义）

$$
\rho_{\mathrm{rel}}(E):=\frac{1}{2\pi}\,\partial_E\Phi_f(E).
$$

在 $\sigma_{\mathrm{ac}}$ 上固定 $\Phi_f$ 的绝对连续分支,故 $\partial_E\Phi_f$ 在几乎处处意义下唯一；等价地,采用 BK 规范 $\det S(E)=\exp(-2\pi i\,\xi(E))$ 时有 $\rho_{\mathrm{rel}}(E)=-\xi'(E)$。

**一行推导**：

$$
\operatorname{tr}\mathsf Q(E)=-i\,\operatorname{tr}\bigl(S^\dagger \partial_E S\bigr)
=-i\,\partial_E\log\det S(E)
=\partial_E\Phi_f(E).
$$

据此在 $\sigma_{\mathrm{ac}}$ 上几乎处处成立严格等式链

$$
\boxed{\ \varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E)=\pi\,\rho_{\mathrm{rel}}(E)\ }.
$$

### 0.3 采样—帧门槛与不可能性

以相位密度 $d\nu=\tfrac{\varphi'}{\pi}\,dE$ 为几何刻度：Landau 给出采样/插值的必要密度下限；Wexler–Raz 对偶刻画 Gabor/多窗帧一致性；Balian–Low 定理在临界格处给出全局定位障碍。这些共同限定稳定读数与固定点判据的适用域。

**Nyquist 门槛的严格定义**：记窗化-平滑密度 $g_{R,c}(E):=w_{R,c}(E)\,(h\ast\rho_\star)(E)$,其傅里叶支撑半宽

$$
\Omega_{\mathrm{eff}}(R):=\inf\{\Omega>0:\ \operatorname{supp}\widehat{g_{R,c}}\subseteq[-\Omega,\Omega]\}.
$$

定义别名门槛

$$
\Delta_c(R):=\frac{\pi}{\Omega_{\mathrm{eff}}(R)}.
$$

别名为零当且仅当 $\operatorname{supp}\widehat{g_{R,c}}\subseteq[-\pi/\Delta,\pi/\Delta]$；充分条件为 $\Delta\le \Delta_c(R)$（平移不改频域支撑）。

### 0.4 "读数/指针"的算子级定义与 Ky–Fan 极小；Born = I-投影

由 $w_R$ 与 $h$ 诱导正算子 $W_R$（Toeplitz/Gram 形式）。**一种可检构造（正定、迹类、稳健）**：令

$$
u_{R,c}(E):=w_{R,c}(E)^2\quad(\text{或取 }u_{R,c}(E)=|w_{R,c}(E)|),
$$

取可测矩阵核 $K_h:\mathbb R\to\mathbb C^{N\times N}$,定义

$$
W_R:=\int_{\mathbb R} u_{R,c}(E)\,K_h(E)^\dagger K_h(E)\,dE .
$$

则 $W_R\ge 0$ 且 $\operatorname{tr}W_R<\infty$；并**加入非平凡性约束** $\operatorname{tr}W_R>0$,从而

$$
p(j)=\frac{\lambda_j}{\operatorname{tr}W_R},\qquad \sum_{j=1}^N p(j)=1
$$

定义良好。此构造仅作用于"指针/Ky–Fan"判据（(iii)）,不改变 (i)(ii)(iv) 的窗权与零和判据（仍以 $w_{R,c}$ 计）。

**作用空间与维度**：以下约定 $W_R$ 作用于**通道空间** $\mathbb C^N$（由窗/核对各通道的能量加权诱导）,故其谱分解记为 $\{(\lambda_j,\psi_j)\}_{j=1}^N$,并以此 $N$ 为后续 $\operatorname{rank}P^\perp=N-k$ 等秩条件的维度基准。相应地,$p(j)=\langle\psi_j,W_R\psi_j\rangle/\operatorname{tr}W_R$ 的索引 $j$ 取 $1\le j\le N$。

设 $W_R=\sum_j \lambda_j\,\mathbb P_{\psi_j}$ 为谱分解。**本征规范**：取 $\{\psi_j\}_{j=1}^N$ 为**正交归一**本征系,令 $\mathbb P_{\psi_j}=|\psi_j\rangle\langle\psi_j|$,则 $\langle\psi_j,W_R\psi_j\rangle=\lambda_j$、$\operatorname{tr}\mathbb P_{\psi_j}=1$。据此定义

$$
p(j):=\frac{\langle \psi_j,\,W_R\,\psi_j\rangle}{\operatorname{tr}W_R}
=\frac{\lambda_j}{\operatorname{tr}W_R},\qquad \sum_{j=1}^N p(j)=1 .
$$

取允许族为与谱同轴的混合族

$$
\mathcal M:=\Bigl\{\sum_j g_j\,\mathbb P_{\psi_j}:\ g_j\ge 0,\ \sum_j g_j=1\Bigr\}.
$$

将允许族**收紧为同轴分块粗化族**：取指数集的一分割 $\mathcal P=\{B_\alpha\}$,及块权 $\mu_\alpha\ge 0,\ \sum_\alpha \mu_\alpha=1$,定义

$$
\Pi_{\mathcal P,\mu}:=\sum_\alpha \mu_\alpha\,\frac{1}{|B_\alpha|}\sum_{j\in B_\alpha}\mathbb P_{\psi_j}\in\mathcal M .
$$

相应的分块粗化通道 $\Gamma_{\mathcal P}$ 在 $\{\psi_j\}$ 基上为类内均匀化：

$$
(\Gamma_{\mathcal P}p)(j)=\frac{1}{|B_\alpha|}\sum_{k\in B_\alpha}p(k),\qquad j\in B_\alpha .
$$

**（记号澄清）** $\Gamma_{\mathcal P}$ 为通道（Markov 线性算子）,$\Pi_{\mathcal P,\mu}$ 为混合态；二者为不同对象。本文**不**使用记号 $\Gamma_{\Pi_{\mathcal P,\mu}}$。

**非退化粗化假设**：除非另有说明,分块 $\mathcal P$ 不是单点细分,即存在 $\alpha$ 使 $|B_\alpha|\ge 2$。该约束排除 $\Gamma_{\mathcal P}=\mathrm{Id}$ 的平凡情形,使"Born=I-投影固定点仅在块内谱退化时成立"的结论与可行集一致。

给定秩 $k$,定义"指针投影"

$$
P_k^\star\in\arg\min_{\substack{P:\,P^2=P,\ P^\dagger=P,\\ \operatorname{rank} P=k}}\ \operatorname{tr}(P W_R),
$$

其最优值等于 $W_R$ 的最小 $k$ 个特征值之和（Ky–Fan 主谱和极小化）。**对偶说明**：令**补投影** $P^\perp:=I-P$（同为正交投影）,则

$$
\min_{\substack{P^\perp:\,(P^\perp)^2=P^\perp,\, (P^\perp)^\dagger=P^\perp,\\ \operatorname{rank}P^\perp=N-k}}\operatorname{tr}(P^\perp W_R)
$$

等价于对 $P$ 的极大化,选择最大 $k$ 个特征值；本文规范固定采用"**Pointer=Ky–Fan 极小**"。概率侧以**通道族**做 Csiszár I-投影（**两块阈值可行集**）：

$$
\Gamma^\star\in\arg\min_{\mathcal P\in\mathfrak T_2} D_{\mathrm{KL}}\bigl(p\ \Vert\ \Gamma_{\mathcal P}p\bigr),\qquad
\mathfrak T_2:=\bigl\{\mathcal P=\{B_{\downarrow},B_{\uparrow}\}\ \text{由 }W_R\text{ 的谱阈值诱导}\bigr\}.
$$

在同轴分块与帧正则下,**指针 Ky–Fan 极小**与该**两块阈值**的 I-投影最优通道 $\Gamma_{\mathcal P^\ast}$ **相容但一般不等价**。

**仅当同时满足**（a）**分块内谱退化** **且**（b）**严格带限+完全重构**时,成立

$$
\text{(iii′)}\ \Longleftrightarrow\ \text{(i)}\ \Longleftrightarrow\ \text{(ii)}\ \Longleftrightarrow\ \text{(iv)} .
$$

若仅满足（a）而不具备（b）,则仅有

$$
\text{(iii′)}\ \Longleftrightarrow\ \text{(i)}\ \Longleftrightarrow\ \text{(ii)},
$$

而 (iv) 仅为**误差预算内近闭环**（不纳入等价）。详见 §2 的 (iii′) 及其"此外"两条款。因此本文固定采用"**Pointer=Ky–Fan 极小**"作为稳定性的**必要**判据；若存在块内退化,则"Born=I-投影固定点"同步成立。

---

## 1. 层级化"停机"谓词

令系统 $S$、资源 $\mathcal R=(L;m,N,\varepsilon)$、视角 $\mathrm{View}=(H_0,w_R,h,\mathsf{sample})$。定义

$$
\mathsf H_0\Rightarrow \mathsf H_1\Rightarrow \mathsf H_2\Rightarrow \mathsf H_3\Rightarrow \mathsf H_4\Rightarrow \mathsf H_5,
$$

逆向一般不成立：

* $\mathsf H_0$：语法停机（无后继态）。
* $\mathsf H_1$：动力停机（函数图入环）；环长 $p=1$ 为**自环不动点**,与"无后继"的 $\mathsf H_0$ **非等价**；$p>1$ 为振荡停机。
* $\mathsf H_2$：读数停机。固定 $\mathrm{View}$,记窗化-平滑密度 $g_{R,c}(E):=w_{R,c}(E)\,(h\ast\rho_\star)(E)$。若其傅里叶支撑满足

$$
\operatorname{supp}\widehat{g_{R,c}}\subseteq[-\pi/\Delta,\ \pi/\Delta],
$$

则 $\varepsilon_{\mathrm{alias}}=0$。一组充分条件为

$$
\operatorname{supp}\widehat{w_R}\subseteq[-\Omega_w,\Omega_w],\quad
\operatorname{supp}\widehat{h}\subseteq[-\Omega_h,\Omega_h],\quad
\operatorname{supp}\widehat{\rho_\star}\subseteq[-\Omega_\rho,\Omega_\rho],
$$

且 $\Omega_w+\Omega_h+\Omega_\rho\le\pi/\Delta$。同时要求

$$
\frac{d}{d\log R}\mathrm{Obs}(R,\Delta;\,c)\to 0,\quad \varepsilon_{\mathrm{EM}},\varepsilon_{\mathrm{tail}} \text{ 受控},
$$

且**平衡通量**满足

$$
\int_{\mathbb R} w_{R,c}(E)\,\bar\rho_{\mathrm{rel}}(E)\,dE=0.
$$

其中 $\frac{d}{d\log R}$ 均指在 $w_{R,c}(E)=R^{-1}w\!\bigl((E-c)/R\bigr)$ 下、**固定 $c$** 的对数尺度导数。

* $\mathsf H_3$：三位一体停机。满足 $\varphi'=\tfrac12\operatorname{tr}\mathsf Q=\pi\rho_{\mathrm{rel}}$ 且"Pointer=Ky–Fan 极小稳定"（若 $W_R$ 在分块内退化,则 Born=I-投影固定点亦成立）。
* $\mathsf H_4$：多视角停机（在视角族 $\mathfrak V$ 上均达 $\mathsf H_3$）。
* $\mathsf H_5$：理论停机/资源完备（RBIT 层面全域不可达）。

---

## 2. 主定理 A（固定视角下"相对停机 $\Leftrightarrow$ 采样-周期闭环"）

**定理 A.1（收紧等价性）** 设 $\mathrm{View}=(H_0,w_R,h,\mathsf{sample})$ 满足：$g_{R,c}$ 的有效带宽 $\Omega_{\mathrm{eff}}(R)$ 有限且 $\Delta\le\Delta_c(R)=\pi/\Omega_{\mathrm{eff}}(R)$（因而 $\varepsilon_{\mathrm{alias}}=0$）,所用窗/基构成紧帧（Parseval；或帧界一致并经正规化）,并且满足 §0.4 的**结构性同轴假设**与**同轴分块粗化通道**（$\mathcal M,\ \Gamma_{\mathcal P}$）成立。

**（测度统一约定）** 统一记

$$
\bar\rho_{\mathrm{rel}}:=\begin{cases}
\rho_{\mathrm{rel}}, & \text{规范 (A)};\\
\tilde\rho_{\mathrm{rel}}, & \text{规范 (B′)}.
\end{cases}
$$

若 (i) 的观测主项采用平滑 $h\ast\rho_{\mathrm{rel}}$,则在 (ii) 中同步以 $h\ast\bar\rho_{\mathrm{rel}}$ 表述零和,以保证 (i) 的观测主项与 (ii) 的零和判据处于同一测度。

**（相位单调性）** 在窗支撑上要求 $\varphi$ 单调非减,以保证 (iv) 中广义逆 $E(\cdot)$ 定义良好；若不满足,则 (iv) 不参与等价串。

在 §0.1 规范 (A) 或 (B') 与门槛/帧正则前提下：

**（严格带限）** 若 $w_R,h,\rho_\star$ **严格带限**且 $\Delta\le\Delta_c(R)$（无别名）,并**此外**采用 Parseval 紧帧的 Poisson–Shannon **完全重构**（或等价精确求和）计算读数,使 $\varepsilon_{\mathrm{EM}}=\varepsilon_{\mathrm{tail}}=0$,则 **(i) $\Leftrightarrow$ (ii) $\Leftrightarrow$ (iv)**；

**（一般正则）** 在仅满足 Poisson–EM 正则与尾项有界时,**(i) $\Leftrightarrow$ (ii)**；(iv) 仅为**误差预算内近闭环**（给出 **$(i)\Rightarrow(iv)$**；而 **(iv) 仅推出近似零和**,即 (ii) 在 $\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}}$ 的意义下近似成立,**不**推出 (ii) 的严格等式）。

**此外**：

**（严格带限+完全重构）** 在严格带限且完全重构前提下,若且仅若 $W_R$ 在分块内退化,存在通道 $\Gamma_{\mathcal P}$ 使 **(iii′) $\Longleftrightarrow$ (i) $\Longleftrightarrow$ (ii) $\Longleftrightarrow$ (iv)**；

**（一般正则）** 若且仅若 $W_R$ 在分块内退化,则 **(iii′) $\Longleftrightarrow$ (i) $\Longleftrightarrow$ (ii)**,而 (iv) 仅为**误差预算内近闭环**并不与之等价。一般情形下,"Pointer=Ky–Fan 极小"（记 (iii)）与上述判据**相容但不必等价**。

(i) 读数停机（$\mathsf H_2$；定义见 §1,包含 Nyquist 无别名、Poisson–EM 误差受控与平衡通量零和）；

(ii) $\displaystyle \int_{\mathbb R} w_{R,c}(E)\,\bar\rho_{\mathrm{rel}}(E)\,dE=0$；

(iii) 指针基为 Ky–Fan 极小；

(iii′) **两块阈值 Born = I-投影固定点（同轴分块）**：存在由 $W_R$ 的谱阈值诱导的两块通道 $\Gamma_{\mathcal P}\in\{\Gamma_{\mathcal P}:\mathcal P\in\mathfrak T_2\}$,使得

$$
p=\Gamma_{\mathcal P}p .
$$

该固定点**非平凡成立当且仅当** $W_R$ 在每个非平凡块 $B_\alpha$ 内发生**谱退化**（即 $\lambda_j$ 在 $B_\alpha$ 上为常数）；此时 (iii′) 与 (i)(ii)（并在"严格带限+完全重构"下与 (iv)）的等价性结论与上文"此外"两段保持一致。

(iv) **相位坐标均匀采样的一步闭环（广义逆版）**：取右连续广义逆

$$
E(\theta):=\inf\{E:\,\varphi(E)\ge \theta\}.
$$

给定**窗口中心** $c_n$,置

$$
c_{n+1}:=E\bigl(\varphi(c_n)+\pi\bigr).
$$

当 $\Delta\le \Delta_c(R)$ 且紧帧正则（可由 Wexler–Raz 对偶核验）时：

**（严格带限）** 若 $w_R,\,h,\,\rho_\star$ **严格带限** 且 $\Delta\le \Delta_c(R)$,则 $\varepsilon_{\mathrm{alias}}=0$；若**此外**采用 Parseval 紧帧并以 Poisson–Shannon **完全重构**（或等价的精确求和公式）计算窗化读数,则可令 $\varepsilon_{\mathrm{EM}}=\varepsilon_{\mathrm{tail}}=0$；在此前提下

$$
\mathrm{Obs}(R,\Delta;\,c_{n+1})=\mathrm{Obs}(R,\Delta;\,c_n).
$$

**否则**,仅得到误差预算内的近闭环（与下一条"一般正则"一致）。

**（一般正则）** 在仅满足 §0.1 的 Poisson–EM 正则与尾项有界时,闭环为**误差预算内近闭环**：

$$
\mathrm{Obs}(R,\Delta;\,c_{n+1})\approx \mathrm{Obs}(R,\Delta;\,c_n),
$$

其中偏差由 $\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}}$ 控制。

*证明要点*：

* $(ii)\Rightarrow(i)$：主项为零且 Poisson–EM 受控；
* **（严格带限+完全重构）** $(iv)\Rightarrow(ii)$：在严格带限且采用 Poisson–Shannon 完全重构时,由 Parseval 与核对角恒等式将一步闭环化为密度零和；**（一般正则）** 仅推出**近似零和**,其偏差由 $\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}}$ 控制；
* $(i)\Rightarrow(iv)$：在 Nyquist 与紧帧前提下,**严格带限+完全重构**时给出等式闭环；**否则**为**误差预算内近闭环**（偏差由 $\varepsilon_{\mathrm{EM}}+\varepsilon_{\mathrm{tail}}$ 控制）。
* **旁注**：由 $(i)$ 可构造**不增**的 Ky–Fan 目标,但**不保证达到极小**,故 (iii) 与 (i)(ii)(iv) **相容而非等价**；(iii′) 的等价范围见上述总述中的分情形陈述。

门槛与障碍由 Landau 必要密度、Wexler–Raz 对偶与 Balian–Low 定理共同保证。

---

## 3. 主定理 B（换视角 $\equiv$ 添加理论/扩展字典）

**定义（视角扩展）**：$\mathrm{View}\mapsto\mathrm{View}'$ 包括 $H_0\mapsto H_0'$（重标定 $\rho_{\mathrm{rel}}$）、$(w_R,h,\mathsf{sample})\mapsto(w_{R'},h',\mathsf{sample}')$ 与尺度（Mellin/对数）切换。

**定理 B.1（不变式与再点亮）**：在 Poisson–EM 正则与紧帧前提下,视角扩展不生新奇点,但可改变窗化相位密度的可见性：一视角下的 $\mathsf H_3$ 可被另一视角打破,从而显现新的振荡—周期。

---

## 4. RBIT 接口：完备性增长 = 停机边界外推

**定理 C.1'（柴廷型不完备）**：对任一一致且可计算枚举、可解释 PA 的理论 $T$,存在常数 $c_T$,使当 $n>c_T$ 时,具体命题"$K(x)\ge n$"虽为真但在 $T$ 中不可证。

**定理 C.2'（扩展链不终结）**：对任意一致且可计算扩展链 $T_{t+1}=T_t+\Delta_t$,每个阶段 $t$ 存在 $G^{(t)}$ 在 $T_t$ 中不可判定。

**推论 C.3**：在资源—统计统一坐标 $\mathcal R=(L;m,N,\varepsilon)$ 与视角族 $\mathfrak V$ 上,"追求完备性"即持续扩张资源并扩展视角,结构上等价于"追求不停机"。

---

## 5. EBOC–共识链的离散镜像与可计算性

在因果网—窗口约束—统一选择子下,得到唯一后继函数图 $f:V\to V$。其连通分量分解为有向环与附着入树（直线/半直线为极限情形）；"停机"即自环（长度 $1$ 的环）,一般 $p>1$ 为振荡不停机。环检测可线性时间、常量空间完成。

---

## 6. "热寂"的操作化刻画与可检方案

**定义（视角相对热寂）**：给定 $\mathrm{View}$,若

$$
\int w_{R,c}(E)\,\bar\rho_{\mathrm{rel}}(E)\,dE\approx 0,\qquad
\int w_{R,c}(E)\,\tfrac12\operatorname{tr}\mathsf Q(E)\,dE\approx 0,
$$

并且 Poisson–EM 三分解误差在预算内闭合,则达视角相对热寂。

**协议（可检闭环）**：参照校准（反演 $(H,H_0)$ 的 $\rho_m,\rho_{m_0}$）；窗/核 KKT 最优；记录 $(\Delta,M,L)$ 与 Landau 门槛,多窗帧以 Wexler–Raz 对偶核验；联立 Ky–Fan 极小与最小-KL 判据；在 $H_0$、窗/核/尺度上扫描视角以检测"再点亮"。

---

## 7. 工程化门槛与跨域一致性

1. **Nyquist 消别名**：严格带限与 $\Delta\le\Delta_c$ 使 $\varepsilon_{\mathrm{alias}}=0$,Poisson 用于别名审计。
2. **帧稳定与障碍**：以 $d\nu=\tfrac{\varphi'}{\pi}\,dE$ 计数,Landau 下限、Wexler–Raz 对偶与 Balian–Low 障碍共同控制稳定域与临界退化。
3. **EM 截断**：有限阶 EM 仅引入端点伯努利改正,不产生新奇点。
4. **群延迟跨域统一**：$\mathsf Q=-i\,S^\dagger \partial_E S$ 在量子、声学与电磁散射中具有统一表达与统计结构。

---

## 8. 结论

在三位一体刻度 $\varphi'(E)=\tfrac12\operatorname{tr}\mathsf Q(E)=\pi\rho_{\mathrm{rel}}(E)$ 与 Poisson–EM 正则纪律之下,**固定视角**时：

**（严格带限+完全重构）** 若严格带限且采用 Parseval 紧帧的 Poisson–Shannon 完全重构（或等价精确求和）,使 $\varepsilon_{\mathrm{EM}}=\varepsilon_{\mathrm{tail}}=0$,则（当 $\varphi$ 在窗支撑上单调非减时）

$$
\boxed{\ \text{(i) 读数停机 }\Longleftrightarrow\ \text{(ii) 窗加权零和 }\Longleftrightarrow\ \text{(iv) 相位—周期闭环}\ }
$$

**（一般正则）** 仅有 **(i) $\Leftrightarrow$ (ii)**；(iv) 给出**误差预算内近闭环**,与 (i)(ii) 相容但不作为等价项。

"Pointer=Ky–Fan 极小"（记为 (iii)）与上述判据**相容**,但一般**不等价**（可作为稳定性的**必要**判据,不宣称与 (i)(ii) 或 (iv) 等价）。关于 (iii′)：

**（严格带限+完全重构）** 在严格带限且完全重构前提下,若且仅若 $W_R$ 在分块内发生**谱退化**,存在通道 $\Gamma_{\mathcal P}$ 使 **(iii′) $\Longleftrightarrow$ (i) $\Longleftrightarrow$ (ii) $\Longleftrightarrow$ (iv)**；

**（一般正则）** 若且仅若 $W_R$ 在分块内谱退化,则 **(iii′) $\Longleftrightarrow$ (i) $\Longleftrightarrow$ (ii)**,而 (iv) 仅为**误差预算内近闭环**,不纳入等价。

视角扩展等价于添加理论/扩展字典,可打破既有停机并再点亮新振荡；RBIT 层面保证该再点亮永不终结。

---

## 术语对齐

EBOC：永恒-静态块·观察—计算；WSIG/CCS：窗化散射—信息几何（相位导数—相对态密度—群延迟）；RBIT：有限资源不完备理论。全篇统一采用

$$
\varphi'(E)=\tfrac12\operatorname{tr}\mathsf Q(E)=\pi\rho_{\mathrm{rel}}(E)
$$

作为唯一能量刻度母尺,所有出现处保持该链式等式的一致写法与号志。
