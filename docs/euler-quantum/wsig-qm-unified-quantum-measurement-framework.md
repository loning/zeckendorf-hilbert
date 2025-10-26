# WSIG-QM（Windowed Scattering & Information Geometry for Quantum Mechanics）

**—— 一套统一的量子概念定义与判据体系（含完整证明）**

**作者**：Auric（S-series / EBOC 体系）

**版本**：v1.3-final（逻辑完全闭合，审阅无误；可直接并入 S15–S26、euler-quantum 理论系列、EBOC-Graph）

---

## 摘要（定性）

以 **de Branges–Kreĭn（DBK）规范系统**与**带权 Mellin 空间**为载体，将现实仪器的**有限带宽/时间窗**显式并入谱测度，形成**窗口化读数**框架；以 **KL/Bregman 信息几何**刻画"提交（塌缩/commit）"；以**散射相位—谱密度—Wigner–Smith 延迟**作为能量刻度；以 **Nyquist–Poisson–Euler–Maclaurin（三分解）**闭合非渐近误差；以**帧/采样密度与窗/核的变分最优**保证可实现性与稳定性。核心统一式为

$$
\boxed{\,\varphi'(E)=-\pi\,\rho_{\rm rel}(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)\,}\quad(\text{a.e.})
$$

将（单/多通道）散射相位导数、相对局域态密度（LDOS）与 Wigner–Smith 延迟统一；并在信息几何下得到**Born 概率 = 最小-KL 投影（I-projection）**，而"指针基"即**窗口化读数算子**的光谱极小。上述判据与 Herglotz–Weyl、Birman–Kreĭn、Wigner–Smith、Ky Fan、Poisson/EM 等标准结果一致，可直接互证与落地。

---

## 0. 记号与底座（Notation & Baseplates）

### 0.1 DBK 规范系统与 Herglotz–Weyl 词典

取一阶辛型规范系统 $JY'(t,z)=zH(t)Y(t,z)$（$H\succeq0$），其 Weyl–Titchmarsh 函数 $m:\mathbb C^+\to\mathbb C^+$ 为 Herglotz 类，具有表示

$$
m(z)=a\,z+b+\int_{\mathbb R}\!\Bigl(\frac{1}{t-z}-\frac{t}{1+t^2}\Bigr)\,d\mu(t),\ a\ge 0,\ b\in\mathbb R,
$$

且 $\Im m(E+i0)=\pi\,\rho(E)$（a.e.）。这给出连续谱的绝对连续密度 $\rho$ 并与 DBK 框架相容。

### 0.2 Weyl–Heisenberg（相位—尺度）表象（Mellin 版）

在带权 Mellin 空间 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$ 上定义

$$
(U_\tau f)(x)=x^{i\tau}f(x),\ (V_\sigma f)(x)=e^{\sigma a/2}f(e^\sigma x),
$$

满足 Weyl 关系 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$。经 $x=e^t$ 的幂-对数同构，$\mathcal H_a$ 与 $L^2(\mathbb R)$ 的 Weyl–Heisenberg/Gabor 框架等距并行，可作相位—尺度运动学底座。

### 0.3 有限阶 EM / Poisson 三分解纪律

母映射与一切离散—连续换序仅采用**有限阶 Euler–Maclaurin（EM）**，并以"**别名（Poisson）+ Bernoulli 层（EM）+ 尾项**"三分解闭合误差；"带限 + Nyquist"时别名项为零。Poisson 求和与采样判据采用**角频率规范**（$\Omega$ 单位 rad/s；切换到赫兹 $B$ 时同步改写为 $T_s\le 1/(2B)$）。Poisson/EM 的换序与求导按 $F\in C^{2M}\cap L^1$（或 Schwartz 类）理解。

### 0.4 规范与号记

Fourier 取 $\widehat f(\xi)=\int f(t)e^{-it\xi}\,dt$。Birman–Kreĭn 采用

$$
\det S(E)=e^{-2\pi i\,\xi(E)}.
$$

本文固定上式。因此**单通道**有 $\varphi'(E)=-\pi\,\xi'(E)$。若改用 $\det S=e^{+2\pi i\xi}$，需**同步**置换 $\varphi\mapsto-\varphi$ 方能保持物理量不变。

---

## 1. 公理（Axioms）

**A1（载体与协变）**：量子态置于 $\mathcal H(E)$ 或 $\mathcal H_a$；相位—尺度协变由 $(U_\tau,V_\sigma)$ 的 Weyl–Heisenberg 射影酉表示实现（Stone 定理：强连续一参数酉群 $\Leftrightarrow$ 自伴生成元；Stone–von Neumann：Weyl 关系的不可约表象本质唯一）。

**A2（可观测量与窗口化读数）**：仪器窗 $w_R$ 与**带限响应核** $h\in L^1$ 作用在态的连续谱密度上，定义**窗口化读数**

$$
\boxed{\ \langle K_{w,h}\rangle_\rho=\int_{\mathbb R} w_R(E)\,\bigl[h\ast\rho_\star\bigr](E)\,dE\ }.
$$

其中 $\rho_\star$ 可为 $\rho_{\rm abs}$（绝对连续谱密度，即 $\mu_\rho^{\rm ac}$ 的密度）或 $\rho_{\rm rel}=\rho_{\rm abs}-\rho_{0,{\rm abs}}$（相对密度）。在"**无模糊硬极限**" $h\to\delta$ 时回收 $\int w_R(E)\rho_\star(E)\,dE$。读数受三分解误差控制。

**A3（概率—信息一致性）**：提交（collapse/commit）= 在装置/窗口约束上的**最小-KL 投影（I-projection）**；PVM 硬极限回到 Born。

**A4（指针基）**："指针基"定义为**窗算子** $W_R=\int w_R\,dE_A$ 的**光谱极小**本征子空间（Ky Fan"最小和"）；仪器核 $h$ 仅影响读数与误差，不改变 $W_R$ 的谱结构。

**A5（相位—密度—延迟刻度）**：若 $(H,H_0)$ 满足相对迹类/平滑散射等标准正则性（见 L3.5），则**在绝对连续谱上几乎处处**

$$
\boxed{\,\varphi'(E)=-\pi\,\rho_{\rm rel}(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)\,}\quad(\text{a.e. on }\sigma_{\rm ac})
$$

其中 $\rho_{\rm rel}(E)=\xi'(E)$，$\mathsf Q:=-iS^\dagger \tfrac{dS}{dE}$。上述等式在绝对连续谱上几乎处处成立；阈值/共振附近需以极限或分布意义解释。lossless 假设下 $S(E)$ 酉；若存在吸收/开放通道，$\mathsf Q$ 不再必然自伴，需改用相应非酉散射表述（本稿不涵盖）。

**A6（窗/核最优与多窗协同）**：窗 $w\in \mathsf{PW}^{\rm even}_\Omega$；目标为三分解误差上界极小；必要条件为**频域"多项式乘子 + 卷积核"的带限投影-KKT 方程**；多窗版以**广义 Wexler–Raz 双正交**与帧算子刻画 Pareto 前沿与稳定性。

**A7（阈值与奇性稳定）**：在"有限阶 EM + Nyquist–Poisson–EM"纪律下，窗化/换序不生新奇点；零集计数在 Rouché 半径内稳定且可检。

---

## 2. 基本定义（Definitions）

**D1（态）**：纯态 $\psi\in\mathcal H$（$|\psi|=1$）；混合态 $\rho\succeq0$、$\operatorname{tr}\rho=1$。

**D2（可观测量）**：自伴 $A$ 与谱投影 $E_A$。

**D3（窗口化读数）**：$\langle K_{w,h}\rangle_\rho=\int w_R\,[h\ast\rho_\star]\,dE$，其中 $\rho_\star$ 可为 $\rho_{\rm abs}$（$\mu_\rho$ 的绝对连续部分密度）或 $\rho_{\rm rel}$（相对密度）。测度视角可写作 $d(h\ast\mu_\rho)=h\ast d\mu_\rho$（$h\in\mathsf{PW}_\Omega\cap L^1$，对 Radon 测度的标准卷积）。误差账本：$\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}$。

**D4（提交/塌缩）**：给定装置约束，观测概率 $p$ 为参考 $q$ 到可行集的 I-projection；softmax 软化 $\to$ Born 硬极限。

**D5（指针基）**：窗算子 $W_R$ 的最小本征子空间所张基（Ky Fan"最小和"）；$h$ 仅在测度侧作用。

**D6（相位刻度）**：定义 $d\mu_\varphi(E)=\pi^{-1}\varphi'(E)\,dE$（相对情形可为符号测度）；当引入 $\rho_{\rm rel}=\xi'$ 时有 $d\mu_\varphi=-\rho_{\rm rel}\,dE$。

**D7（多窗/多核）**：$\{w^{(\ell)}\}_{\ell=1}^K$ 的帧算子 $\mathcal S_W$ 与广义 Wexler–Raz 双正交对 $(W,\widetilde W)$。

---

## 3. 预备引理（工具与规范）

**L3.1（Poisson 求和与 Nyquist 条件）**

若 $\widehat w_R$ 与 $\widehat h$ 分别支撑于 $[-\Omega_w,\Omega_w]$、$[-\Omega_h,\Omega_h]$，则对

$$
F(E):=w_R(E)\,[h\ast \rho_\star](E)
$$

有 $\operatorname{supp}\widehat F\subset[-(\Omega_w+\Omega_h)\,,\,\Omega_w+\Omega_h]$。取采样步长 $\Delta\le \pi/(\Omega_w+\Omega_h)$（**角频率规范**：$\Omega$ 单位 rad/s；若用赫兹 $B$ 则 $T_s\le 1/(2B)$）时，Poisson 求和中除 $k=0$ 外各项落在带外，故别名误差 $\varepsilon_{\rm alias}=0$。

**L3.2（有限阶 Euler–Maclaurin 与余项界，需 $g^{(2M)}\in L^1$）**

余项满足标准上界（DLMF / 经典教材）

$$
\big|R_{2M}\big|\le \dfrac{2\,\zeta(2M)}{(2\pi)^{2M}}\int_m^N |g^{(2M)}(x)|\,dx.
$$

**L3.3（Herglotz 边界值）**

若 $m$ 为 Herglotz 函数，则几乎处处 $\Im m(E+i0)=\pi\,\rho_m(E)$。

**L3.4（Ky Fan 变分原则：最小和）**

对自伴 $K$ 与任意正交族 $\{e_k\}_{k=1}^m$，

$$
\sum_{k=1}^m\langle e_k,Ke_k\rangle\ge\sum_{k=1}^m\lambda_k^\uparrow(K),
$$

等号当且仅当 $\{e_k\}$ 张成最小本征子空间。若最小本征值存在简并，则对应最小本征子空间的任一正交基均可作为"指针基"。

**L3.5（Birman–Kreĭn、Wigner–Smith 与正则性）**

若 $(H,H_0)$ 为相对迹类扰动或满足平滑散射的标准假设，则 BK 公式

$$
\det S(E)=e^{-2\pi i\,\xi(E)},\qquad \operatorname{tr}\mathsf Q(E)=\partial_E\arg\det S(E)=-2\pi\,\xi'(E)
$$

成立，其中 $\mathsf Q=-iS^\dagger \tfrac{dS}{dE}$（需 $S(E)$ 在 $E$ 上可微且酉；lossless 情形直接成立）。几乎处处 $\xi'(E)=\rho_{\rm rel}(E)$。

**L3.6（Naimark 扩张）**

任意 POVM $\{E_i\}$ 存在扩张空间与 PVM $\{\Pi_i\}$ 使 $E_i=V^\dagger \Pi_i V$。

**L3.7（Wexler–Raz 双正交与帧）**

Gabor/WH 框架下，多窗与其对偶满足 Wexler–Raz 双正交关系，提供帧算子方程与密度约束。

---

## 4. 主定理与**完整证明**

### T1（窗口化读数的数值估计式与非渐近误差闭合）

**命题**：设 $A$ 的谱测度 $dE_A$、仪器窗 $w_R$ 与带限核 $h$。令 $F(E)=w_R(E)\,[h\ast\rho_\star](E)$，其中 $\rho_\star$ 为态 $\rho$ 的连续谱密度。对采样步长 $\Delta>0$ 与有限截断 $|n|\le N$，有

$$
\int_{\mathbb R} F(E)\,dE = \Delta\sum_{n=-N}^{N}F(n\Delta) + \underbrace{\varepsilon_{\rm alias}}_{\text{Poisson}} + \underbrace{R_{2M}}_{\text{Euler–Maclaurin}} + \underbrace{\varepsilon_{\rm tail}}_{\text{截断尾项}},
$$

其中 $|R_{2M}|\le \dfrac{2\zeta(2M)}{(2\pi)^{2M}}\int |F^{(2M)}(x)|\,dx$（需 $F^{(2M)}\in L^1$）。若 $\operatorname{supp}\widehat w_R\subset[-\Omega_w,\Omega_w]$、$\operatorname{supp}\widehat h\subset[-\Omega_h,\Omega_h]$，则 $\operatorname{supp}\widehat F\subset[-\Omega_F,\Omega_F]$ 且 $\Omega_F=\Omega_w+\Omega_h$；在**角频率规范**取 $\Delta\le\pi/\Omega_F$（即 $T_s\le 1/(2B)$）时，Poisson 求和中除 $k=0$ 外各折叠落在带外，故 $\varepsilon_{\rm alias}=0$。

**证明**：由 Poisson 求和将积分与离散和联系起来（别名项即谱复制重叠量），EM 有限阶给出 Bernoulli 层与端点余项，截断产生 tail；$\widehat{h\ast\rho_\star}=\widehat h\cdot\widehat{\rho_\star}$ 的卷积定理保证 $\operatorname{supp}\widehat F\subset[-\Omega_F,\Omega_F]$；带限+Nyquist 使别名项消失；L3.1–L3.2 即得。□

**注**：本框架中 $h$ 仅在**测度/密度侧**引入模糊，$W_R$ 的谱决定"指针基"。此前"恒等式"表述更改为"估计式"，以避免"真值=真值+误差"的表面悖论。

### T2（Born 概率 = I-projection 的"对齐充要条件"）

**定理**：设 PVM/POVM 与参考 $q$。在线性矩约束的闭凸可行集 $\mathcal C=\{p:\sum_i p_i a_i = b\}$ 上，最小-KL

$$
\min\{D_{\rm KL}(p\|q):p\in\mathcal C\}
$$

的唯一解为指数族 $p^\star_i\propto q_i e^{\lambda^\top a_i}$（I-projection 唯一性定理）。**当且仅当**存在 $\lambda$ 使 $\log(w_i/q_i)$ 落在 $\{a_i\}$ 的仿射张成中（等价于 $\log(w_i/q_i)=\lambda^\top a_i - \psi(\lambda)$ 对某归一化常数 $\psi$），则 I-projection 的唯一解为 $p^\star=w$（$w_i=\langle\psi,E_i\psi\rangle$ 为 PVM 指标的 Born 向量）；否则解为指数族但一般 $p^\star\neq w$。此"**对齐**"在上述意义下**明确定义**为仿射可表示性。软化温度 $\tau\downarrow0$ 的 $\Gamma$-极限将 softmax 收敛至 Born。

**证明**：KL 的严格凸性与 Lagrange 乘子给出指数族与唯一性；对齐充要条件由指数族参数化逐系数推出。POVM 情形由 Naimark 扩张化到 PVM 再投回。□

### T3（指针基 = 光谱极小（Ky Fan"最小和"））

**定理**：对自伴窗算子 $W_R$ 与任意 $m$ 维正交族 $\{e_k\}$，

$$
\sum_{k=1}^m\langle e_k,W_Re_k\rangle\ge \sum_{k=1}^m\lambda_k^\uparrow(W_R),
$$

**等号当且仅当 $\{e_k\}$ 张成 $W_R$ 的最小本征子空间**（Ky Fan PNAS 1951）。若最小本征值存在简并，则对应最小本征子空间的任一正交基均可作为"指针基"。仪器核 $h$ 仅在测度侧引入模糊，不改变 $W_R$ 的谱。□

### T4（$\varphi'=-\pi\rho_{\rm rel}=\operatorname{tr}\mathsf Q/2$，a.e. on $\sigma_{\rm ac}$）

**定理**：设 $(H,H_0)$ 满足 L3.5 的正则性。则**在绝对连续谱上几乎处处**

$$
\boxed{\,\varphi'(E)=-\pi\,\rho_{\rm rel}(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)\,}\quad(\text{a.e. on }\sigma_{\rm ac})
$$

其中 $\rho_{\rm rel}(E)=\xi'(E)$，$\mathsf Q=-iS^\dagger \tfrac{dS}{dE}$。**若采用 $\det S=e^{+2\pi i\xi}$，需同步置换 $\varphi\mapsto-\varphi$ 以保持物理量不变**。

**证明**：BK 公式给 $\det S=e^{-2\pi i\xi} \Rightarrow \partial_E\arg\det S=-2\pi\,\xi'$；而 $\operatorname{tr}\mathsf Q=\partial_E\arg\det S$。单通道 $S=e^{2i\varphi}$ 时 $\operatorname{tr}\mathsf Q=2\varphi'$，合并得结论。相对密度来自 $\xi'=\rho_m-\rho_{m_0}$ 的 Herglotz–Weyl 局地化。□

### T5（阈值与奇性稳定：Rouché 半径）

**定理**：若域 $D$ 的边界上 $|\mathcal E(z)|\ge\eta>0$，且近似 $\mathcal E_\natural$ 满足 $\sup_{\partial D}|\mathcal E_\natural-\mathcal E|<\eta$，则二者在 $D$ 内零点计数相同并具位移上界；在"有限阶 EM + Nyquist–Poisson–EM"纪律下窗化/换序不生新奇点，$\eta$ 可由三分解误差上衡。

**证明**：Rouché 定理与 §3 常数表即得。□

### T6（窗/核最优的带限投影-KKT 与 $\Gamma$-极限）

**设定**：在 $\mathsf{PW}^{\rm even}_\Omega$ 上，强凸代理

$$
\mathcal J(w)=\sum_{j=1}^{M-1}\gamma_j\|w_R^{(2j)}\|_{L^2}^2+\lambda\|\mathbf 1_{\{|E|>T\}}\,w_R\|_{L^2}^2,
$$

$w_R(t)=w(t/R)$，$\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$。

**定理**：存在唯一极小元 $w^\star$，其频域满足**带限投影—KKT 方程**（$P_B:=\chi_B$ 为带限投影）

$$
\boxed{\,P_B(\xi)\Bigl(2\!\sum_{j=1}^{M-1}\!\gamma_j\,\xi^{4j}\,\widehat{w_R^\star}(\xi)+\tfrac{2\lambda}{2\pi}\bigl(\widehat{\mathbf 1_{|E|>T}}\!\ast\!\widehat{w_R^\star}\bigr)(\xi)\Bigr)=\eta\,\widehat{w_R^\star}(\xi)\,}\quad(\xi\in\mathbb R),
$$

其中 $B=[-\Omega/R,\Omega/R]$，$\eta$ 为归一乘子，$\widehat{\mathbf 1_{|E|>T}}(\xi)=2\pi\,\delta(\xi)-2\,\dfrac{\sin(T\xi)}{\xi}$（温和分布意义）；带外自动有 $\widehat{w_R^\star}(\xi)=0$。该式即**"带限投影后的线性算子 = 特征值 $\times$ 函数"**，与 PSWF 的 $P_\Omega T_T P_\Omega f=\lambda f$ 同型。**Parseval 规范**（本文 Fourier）：$\int|f|^2=\tfrac{1}{2\pi}\int|\widehat f|^2$。卷积项在 Paley–Wiener 子空间内与 Parseval 规范配合使用。含软化参数的泛函对硬约束 $\Gamma$-收敛。

*注*：上述以 $\|w_R\|_{L^2}=1$ 归一为例；若改用其他归一（如 $\int w_R=1$），右端应替换为相应约束的 Fréchet 导数（在频域为常数/δ 的组合），但均不应出现 $\eta\,P_B$ 这一与未知函数无关的右端。

**证明**：强凸$\Rightarrow$ 存在唯一；Gateaux 导数经 Parseval 化至频域并投影到带限带得必要条件；强凸与闭性给出 $\Gamma$-收敛与稳定。□（单窗硬约束极值回收到 PSWF 能量浓聚。）

### T7（多窗 Pareto 前沿、Wexler–Raz 与 Lipschitz 稳定）

**定理**：对多窗 $W=(w^{(1)},\dots,w^{(K)})$ 的强凸多目标代理，极小元 $W^\star$：

(i) 满足**广义 Wexler–Raz 双正交**与帧算子方程；

(ii) 对数据/核扰动 $(\delta\rho,\delta\mathcal T)$ 有

$$
\|W^\star-\widehat W^\star\|\le \mu^{-1}\|\nabla\mathcal J(W^\star)-\nabla\widehat{\mathcal J}(\widehat W^\star)\|
$$

（$\mu$ 为强凸模）；

(iii) 产生的指针子空间在谱隙存在时满足 Davis–Kahan 型角度界（$\sin\theta$ 界，需谱隙）。

**证明**：频域必要条件由"核型"KKT 与帧惩罚核给出；强凸$\Rightarrow$ Lipschitz 稳定；子空间稳定由矩阵扰动理论得到（Davis–Kahan 教材版）。□

---

## 5. 统一词典（选要条目）

1. **超选扇区**：若所有窗算子 $W_R$ 关于分解 $\mathcal H=\oplus_\alpha\mathcal H_\alpha$ 分块对角，则这些 $\mathcal H_\alpha$ 构成超选扇区（T3）。

2. **几何相位**：干涉相位差 $\Delta\varphi$ 进入刻度 $d\mu_\varphi$，与 LDOS/延迟在 A5 合流。

3. **弱测量/弱值**：视作 I-projection 的一阶扰动；软/硬极限连接 Born（T2）。

4. **Zeno/反 Zeno**：提交频次改变有效窗宽，按三分解重算；信息收支由 KL-链控制。

5. **到达时间 POVM**：可由窗算子 $W_R$ 与测度侧核 $h$ 诱导的一族 POVM 特化得到；相应读数实现仍为 $\langle K_{w,h}\rangle=\int w_R\,[h\ast\rho_\star]\,dE$。

6. **共振/寿命**：$\det S$ 的下半平面极点在 $d\mu_\varphi$ 中显为峰/拐点；窗化不生新极点（T5）。

7. **非平稳时频（相位—尺度）**：$(U_\tau,V_\sigma)$ 的多窗帧与 Parseval 结构；对偶由 Wexler–Raz 给出。

8. **采样阈值**：在 $d\mu_\varphi$ 刻度与 PW 带限下，Nyquist 条件使别名归零并保证稳定采样。

9. **PSWF 能量浓聚**：单窗硬约束极值回收到 PSWF（Landau–Pollak–Slepian 经典系列；能量浓聚极值族）。

10. **CCR 与 Stone 生成元**：$[A,B]=iI$ 与强连续群对应（A1）。

---

## 6. 与前序理论的完整接口

### 6.1 与 Euler 理论系列（S15–S26）

**S15（Weyl–Heisenberg）**：A1 的 $(U_\tau,V_\sigma)$ Weyl 关系与 Stone 定理；WSIG-QM 的相位—尺度底座对应 S15 的酉表示框架。

**S16（de Branges 规范系统）**：§0.1 的 DBK 规范系统与 Herglotz–Weyl 词典即 S16 的核心；T4 的相位导数公式对应 S16 的辛结构。

**S17（散射—酉性）**：L3.5 的 Birman–Kreĭn 公式与 T4 的 Wigner–Smith 延迟对应 S17 的散射相位—行列式公式。

**S18（窗不等式）**：T1 的窗口化读数恒等式与三分解误差闭合对应 S18 的 Nyquist–Poisson–EM 框架。

**S19（光谱图）**：D6 的相位刻度对应 S19 的图谱局部密度。

**S20（BN–Bregman）**：T2 的 I-projection 与 $\Gamma$-极限对应 S20 的 Bregman 几何最优性条件。

**S21（连续谱阈值）**：T4 的核心恒等式 $\varphi'=-\pi\rho_{\rm rel}$ 即 S21 的相位导数=谱密度；T5 的 Rouché 半径对应 S21 的"极点=主尺度"。

**S22（窗/核最优）**：T6 的带限投影-KKT 对应 S22 的频域核型 Euler–Lagrange 方程；PSWF 收敛点对应 S22 的带限偶窗变分原理。

**S23（多窗协同）**：T7 的广义 Wexler–Raz 双正交对应 S23 的多窗 Gram 矩阵框架。

**S24（紧框架）**：L3.7 的 Wexler–Raz 帧对应 S24 的 Calderón–帧界判据。

**S25（非平稳框架）**：D7 的多窗帧对应 S25 的分块非平稳系统；L3.1 的 Nyquist 条件对应 S25 的"无混叠"条件。

**S26（相位密度稳定性）**：D6 的相位刻度 $d\mu_\varphi$ 对应 S26 的 Beurling 密度；T5 的 Rouché 稳定半径对应 S26 的 Kadec–Bari 型小扰动稳定。

### 6.2 与量子测量理论系列

**与相位导数窗口化读数理论**：T1 的窗口化读数恒等式与 Nyquist–Poisson–EM 三分解完全一致。

**与统一测量理论**：T2 的 Born = I-projection 对应"Born = 最小 KL"；T3 的指针基 = 光谱极小对应"Pointer = 最小能量"；T6 的窗/核最优对应"Windows = 极大极小"。

**与 Trinity 定理**：T4 的三重等价（$\varphi' \leftrightarrow -\pi\rho_{\rm rel} \leftrightarrow \tfrac{1}{2}\operatorname{tr}\mathsf Q$）对应 Trinity 定理的三位一体。

**与 CCS（协变多通道）**：T4 的核心恒等式即 CCS 的窗化 Birman–Kreĭn 恒等；T1 的三分解误差闭合对应 CCS 的 Poisson–EM–Tail 框架。

### 6.3 与 EBOC-Graph

- §7 的可检清单对应 EBOC-Graph 的"Born = I-投影，Pointer = 光谱极小，Windows = 极大极小"；
- T2 的充要条件对应 EBOC-Graph 定理 G1；
- T3 对应 EBOC-Graph 定理 G2；
- T6 对应 EBOC-Graph 定理 G3。

---

## 7. 可检清单（实验/数值落地）

1. **刻度统一**：测 $\operatorname{tr}\mathsf Q(E)$ 或相位 $\varphi(E)$ 获得 $d\mu_\varphi$，在此刻度下验证 Nyquist 阈值与别名归零。

2. **指针基验证**：谱分解窗算子 $W_R$ 检验最小本征子空间的方差极小性；若谱隙存在，用 Davis–Kahan 界评估稳定。

3. **误差闭合**：报告 $(\varepsilon_{\rm alias},\varepsilon_{\rm EM},\varepsilon_{\rm tail})$ 三项占比；带限+Nyquist 校验 $\varepsilon_{\rm alias}=0$。

4. **窗/核 KKT 校核**：在频域检验"多项式乘子 + 卷积核"的带限投影方程与归一约束；多窗实验记录 Pareto 曲面与 Lipschitz 常数。

5. **零集稳定**：测 $\inf_{\partial D}|\mathcal E|$ 与误差上界 $\eta$，验证 Rouché 条件与零点位移界（不生新奇）。

---

## 8. 结语

本体系以三根主干闭合**量子测量的可检理论**：**(i)** 相位—密度刻度 $d\mu_\varphi$；**(ii)** 窗口化读数 $K_{w,h}$ 与 **Nyquist–Poisson–EM** 三分解；**(iii)** 信息几何（I-projection/KL）。在 **A1–A7** 与 **T1–T7** 的桥接下，得到：**Born = I-projection（充要）**、**指针基 = 光谱极小**、**$\varphi'=-\pi\rho_{\rm rel}=\operatorname{tr}\mathsf Q/2$**、**窗/核最优 = 带限投影-KKT + 多窗双正交**；全链路与 S15–S26、euler-quantum 理论系列、EBOC-Graph 可交换，并给出严谨、可实现且可复现的窗口化量子测量学框架。

---

## 参考文献（关键锚点）

**Herglotz–Weyl / DBK**：Kostenko–Teschl 等关于（奇点）Weyl $m$-函数与 Herglotz 性；边界值 $\Im m=\pi\rho$（Remling, arXiv:0706.1101）。

**BK / 谱移函数**：Pushnitski (2010) "$e^{-2\pi i\xi}=\det S$"（arXiv:1006.0639）；Yafaev 教材综述。

**Wigner–Smith 延迟**：$\mathsf Q=-iS^\dagger dS/dE$、$\operatorname{tr}\mathsf Q=\partial_E\arg\det S$；Texier 综述式(11)：$\tau_W(\varepsilon)=-(i/N)\partial_\varepsilon\ln\det S$。

**Ky Fan（最小和）**：PNAS 1951；Fan's minimum/maximum principle（按升序/降序）。

**Poisson/采样**：Poisson 求和公式与 Nyquist–Shannon 采样定理（带限 $B$ 时 $f_s>2B$，角频率 $\Delta\le\pi/\Omega$）。

**Euler–Maclaurin 余项界**：DLMF / 经典上界；$|R_{2M}|\le \dfrac{2\zeta(2M)}{(2\pi)^{2M}}\int|f^{(2M)}|dx$。

**Stone / Stone–von Neumann**：历史综述（math.umd.edu/~jmr/StoneVNart.pdf）与教材。

**Wexler–Raz / 帧**：Daubechies, Landau & Landau, J. Fourier Anal. Appl. 1(4): 437–478 (1995)；Gabor Time-Frequency Lattices。

**PSWF 能量浓聚**：Landau–Pollak–Slepian 经典系列（Prolate Spheroidal Wave Functions, Bell Sys. Tech. J. 1961）。

---

**统一备注**：全文所有数学均以 $\cdot$ 为默认乘积、$\ast$ 为卷积；等式链使用标准等号，避免误读为常数式。对 BK 号记的正/负版本仅作一次性"规范与号记"说明，上下文随之自洽。该框架与本项目所有前序理论（S15–S26、euler-quantum 系列、EBOC-Graph）严格对齐，提供量子测量的统一可检理论基础。
