# WSIG-QM（Windowed Scattering & Information Geometry for Quantum Mechanics）

**—— 一套统一的量子概念定义与判据体系（含完整证明）**

**作者**：Auric（S-series / EBOC 体系）

**版本**：v1.2.1-clean（完整号记修复与文献校正；可直接并入 S15–S26、euler-quantum 理论系列、EBOC-Graph）

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

且几乎处处 $\Im m(E+i0)=\pi\,\rho(E)$。这给出连续谱的绝对连续密度 $\rho$ 并与 DBK 框架相容。

### 0.2 Weyl–Heisenberg（相位—尺度）表象（Mellin 版）

在带权 Mellin 空间 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$ 上定义

$$
(U_\tau f)(x)=x^{i\tau}f(x),\ (V_\sigma f)(x)=e^{\sigma a/2}f(e^\sigma x),
$$

满足 Weyl 关系 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$，与 $L^2(\mathbb R)$ 上"调制—平移"等距并行，可作相位—尺度运动学底座。

### 0.3 有限阶 EM / Poisson 三分解纪律

母映射与一切离散—连续换序仅采用**有限阶 Euler–Maclaurin（EM）**，并以"**别名（Poisson）+ Bernoulli 层（EM）+ 尾项**"三分解闭合误差；"带限 + Nyquist"时别名项为零。Poisson 求和与采样判据采用角频率规范。

### 0.4 规范与号记

Fourier 取 $\widehat f(\xi)=\int f(t)e^{-it\xi}\,dt$。Birman–Kreĭn 采用

$$
\det S(E)=e^{-2\pi i\,\xi(E)}.
$$

本文固定上式。因此**单通道**有 $\varphi'(E)=-\pi\,\xi'(E)$。若改用 $\det S=e^{+2\pi i\xi}$，需**同步**置换 $\varphi\mapsto-\varphi$ 方能保持物理量不变。

---

## 1. 公理（Axioms）

**A1（载体与协变）**：量子态置于 $\mathcal H(E)$ 或 $\mathcal H_a$；相位—尺度协变由 $(U_\tau,V_\sigma)$ 的 Weyl–Heisenberg 射影酉表示实现（Stone 定理：强连续一参数酉群 $\Leftrightarrow$ 自伴生成元；Stone–von Neumann：Weyl 关系的不可约表象本质唯一）。

**A2（可观测量与窗口化读数）**：对自伴 $A$ 的谱测度 $dE_A$，定义

$$
K_{w,h}=\int_{\mathbb R} h(E)\,w_R(E)\,dE_A(E);
$$

读数等价于对（相对）LDOS 的加权并受三分解误差控制。

**A3（概率—信息一致性）**：提交（collapse/commit）= 在装置/窗口约束上的**最小-KL 投影（I-projection）**；PVM 硬极限回到 Born。

**A4（指针基）**："指针基"定义为 $K_{w,h}$ 的**光谱极小**本征子空间（Ky Fan"最小和"）。

**A5（相位—密度—延迟刻度）**：若 $(H,H_0)$ 满足相对迹类/平滑散射等标准正则性（见 L3.5），则几乎处处

$$
\boxed{\,\varphi'(E)=-\pi\,\rho_{\rm rel}(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)\,},
$$

其中 $\rho_{\rm rel}(E)=\xi'(E)$，$\mathsf Q:=-iS^\dagger \tfrac{dS}{dE}$（a.e. on the absolutely continuous spectrum）。

**A6（窗/核最优与多窗协同）**：窗 $w\in \mathsf{PW}^{\rm even}_\Omega$；目标为三分解误差上界极小；必要条件为**频域"多项式乘子 + 卷积核"的带限投影-KKT 方程**；多窗版以**广义 Wexler–Raz 双正交**与帧算子刻画 Pareto 前沿与稳定性。

**A7（阈值与奇性稳定）**：在"有限阶 EM + Nyquist–Poisson–EM"纪律下，窗化/换序不生新奇点；零集计数在 Rouché 半径内稳定且可检。

---

## 2. 基本定义（Definitions）

**D1（态）**：纯态 $\psi\in\mathcal H$（$|\psi|=1$）；混合态 $\rho\succeq0$、$\operatorname{tr}\rho=1$。

**D2（可观测量）**：自伴 $A$ 与谱投影 $E_A$。

**D3（窗口化读数）**：$\langle K_{w,h}\rangle_\rho=\int h\,w_R\,d\mu_\rho$，其中 $\mu_\rho$ 的绝对连续部分密度为 $\rho$ 或相对密度 $\rho_{\rm rel}$。误差账本：$\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}$。

**D4（提交/塌缩）**：给定装置约束，观测概率 $p$ 为参考 $q$ 到可行集的 I-projection；softmax 软化 $\to$ Born 硬极限。

**D5（指针基）**：$K_{w,h}$ 的最小本征子空间所张基（Ky Fan"最小和"）。

**D6（相位刻度）**：定义 $d\mu_\varphi(E)=\pi^{-1}\varphi'(E)\,dE$（相对情形可为符号测度）；当引入 $\rho_{\rm rel}=\xi'$ 时有 $d\mu_\varphi=-\rho_{\rm rel}\,dE$。

**D7（多窗/多核）**：$\{w^{(\ell)}\}_{\ell=1}^K$ 的帧算子 $\mathcal S_W$ 与广义 Wexler–Raz 双正交对 $(W,\widetilde W)$。

---

## 3. 预备引理（工具与规范）

**L3.1（Poisson 求和与 Nyquist 条件）**

若 $\widehat w_R$ 与 $\widehat h$ 分别支撑于 $[-\Omega_w,\Omega_w]$、$[-\Omega_h,\Omega_h]$，则对

$$
F(E):=w_R(E)\,[h\ast \rho_\star](E)
$$

有 $\operatorname{supp}\widehat F\subset[-(\Omega_w+\Omega_h)\,,\,\Omega_w+\Omega_h]$。取采样步长 $\Delta\le \pi/(\Omega_w+\Omega_h)$（角频率规范）时，Poisson 求和中除 $k=0$ 外各项落在带外，故别名误差 $\varepsilon_{\rm alias}=0$。

**L3.2（有限阶 Euler–Maclaurin 与余项界）**

当 $g^{(2M)}\in L^1$ 时，余项满足标准上界

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

等号当且仅当 $\{e_k\}$ 张成最小本征子空间。

**L3.5（Birman–Kreĭn、Wigner–Smith 与正则性）**

若 $(H,H_0)$ 为相对迹类扰动或满足平滑散射的标准假设，则 BK 公式

$$
\det S(E)=e^{-2\pi i\,\xi(E)},\qquad \operatorname{tr}\mathsf Q(E)=\partial_E\arg\det S(E)=-2\pi\,\xi'(E)
$$

成立，其中 $\mathsf Q=-iS^\dagger \tfrac{dS}{dE}$。几乎处处 $\xi'(E)=\rho_{\rm rel}(E)$。

**L3.6（Naimark 扩张）**

任意 POVM $\{E_i\}$ 存在扩张空间与 PVM $\{\Pi_i\}$ 使 $E_i=V^\dagger \Pi_i V$。

**L3.7（Wexler–Raz 双正交与帧）**

Gabor/WH 框架下，多窗与其对偶满足 Wexler–Raz 双正交关系，提供帧算子方程与密度约束。

---

## 4. 主定理与**完整证明**

### T1（窗口化读数恒等式与非渐近误差闭合）

**命题**：设 $A$ 的谱测度 $dE_A$、仪器窗 $w_R$ 与带限核 $h$。对任意态 $\rho$ 的（绝对/相对）连续谱密度 $\rho_\star$，

$$
\mathrm{Obs}=\int_{\mathbb R} w_R(E)\,[h\ast\rho_\star](E)\,dE\ +\ \varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}.
$$

若 $\widehat w_R,\widehat h$ 带限且 $\Delta\le \pi/(\Omega_w+\Omega_h)$，则 $\varepsilon_{\rm alias}=0$。

**证明**：由谱定理 $K_{w,h}=\int h(E)w_R(E)\,dE_A(E)$ 与 Herglotz 表示 $\Im m=\pi\rho_m$ 得连续谱读数为 $\int w_R[h\ast\rho_\star]$。Poisson 求和给出别名项结构，带限+Nyquist 消除别名；有限阶 EM 给出 Bernoulli 层与端点余项上界并保证不生新奇。三项误差合并即得。□

### T2（Born 概率 = I-projection（充要））

**定理**：设 PVM/POVM 与参考 $q$。在线性矩约束的闭凸可行集上，最小-KL

$$
\min\{D_{\rm KL}(p\|q):p\in\mathcal C\}
$$

的唯一解为指数族 $p^\star_i\propto q_i e^{\lambda^\top a_i}$。当 $\mathcal C$ 与 Born 向量 $w_i=\langle\psi,E_i\psi\rangle$ 对齐时，**充要**地 $p^\star=w$。软化温度 $\tau\downarrow0$ 的 $\Gamma$-极限将 softmax 收敛至 Born。

**证明**：KL 的严格凸性与 Lagrange 乘子给出指数族与唯一性；与 PVM 指标对齐逐系数推出 $p=w$。POVM 情形由 Naimark 扩张化到 PVM 再投回。□

### T3（指针基 = 光谱极小（Ky Fan"最小和"））

**定理**：对自伴 $K_{w,h}$ 与任意 $m$ 维正交族 $\{e_k\}$，

$$
\sum_{k=1}^m\langle e_k,K_{w,h}e_k\rangle\ge \sum_{k=1}^m\lambda_k^\uparrow(K_{w,h}),
$$

等号当且仅当 $\{e_k\}$ 张成 $K_{w,h}$ 的最小本征子空间。□

### T4（$\varphi'=-\pi\rho_{\rm rel}=\operatorname{tr}\mathsf Q/2$，a.e.）

**定理**：设 $(H,H_0)$ 满足 L3.5 的正则性。则几乎处处

$$
\boxed{\,\varphi'(E)=-\pi\,\rho_{\rm rel}(E)=\tfrac{1}{2}\operatorname{tr}\mathsf Q(E)\,},
$$

其中 $\rho_{\rm rel}(E)=\xi'(E)$，$\mathsf Q=-iS^\dagger \tfrac{dS}{dE}$。

**证明**：BK 公式给 $\det S=e^{-2\pi i\xi} \Rightarrow \partial_E\arg\det S=-2\pi\,\xi'$；而 $\operatorname{tr}\mathsf Q=\partial_E\arg\det S$。单通道 $S=e^{2i\varphi}$ 时 $\operatorname{tr}\mathsf Q=2\varphi'$，合并得结论。相对密度来自 $\xi'=\rho_m-\rho_{m_0}$ 的 Herglotz–Weyl 局地化。□

### T5（阈值与奇性稳定：Rouché 半径）

**定理**：若域 $D$ 的边界上 $|E(z)|\ge\eta>0$，且近似 $E_\natural$ 满足 $\sup_{\partial D}|E_\natural-E|<\eta$，则二者在 $D$ 内零点计数相同并具位移上界；在"有限阶 EM + Nyquist–Poisson–EM"纪律下窗化/换序不生新奇点，$\eta$ 可由三分解误差上衡。

**证明**：Rouché 定理与 §3 常数表即得。□

### T6（窗/核最优的带限投影-KKT 与 $\Gamma$-极限）

**设定**：在 $\mathsf{PW}^{\rm even}_\Omega$ 上，强凸代理

$$
\mathcal J(w)=\sum_{j=1}^{M-1}\gamma_j\|w_R^{(2j)}\|_{L^2}^2+\lambda\|\mathbf 1_{\{|E|>T\}}\,w_R\|_{L^2}^2,
$$

$w_R(t)=w(t/R)$，$\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$。

**定理**：存在唯一极小元 $w^\star$，其频域满足**带限投影—KKT 方程**

$$
\chi_{B}(\xi)\Bigl(2\sum_{j=1}^{M-1}\gamma_j\,\xi^{4j}\,\widehat{w_R^\star}(\xi)+\tfrac{2\lambda}{2\pi}(\widehat{\mathbf 1_{|E|>T}}\ast\widehat{w_R^\star})(\xi)\Bigr)=\eta\,\chi_B(\xi),
$$

$B=[-\Omega/R,\Omega/R]$，$\eta$ 为归一乘子。含软化参数的泛函对硬约束 $\Gamma$-收敛。

**证明**：强凸$\Rightarrow$ 存在唯一；Gateaux 导数经 Parseval 化至频域并投影到带限带得必要条件；强凸与闭性给出 $\Gamma$-收敛与稳定。□（单窗硬约束极值回收到 PSWF 能量浓聚。）

### T7（多窗 Pareto 前沿、Wexler–Raz 与 Lipschitz 稳定）

**定理**：对多窗 $W=(w^{(1)},\dots,w^{(K)})$ 的强凸多目标代理，极小元 $W^\star$：

(i) 满足**广义 Wexler–Raz 双正交**与帧算子方程；

(ii) 对数据/核扰动 $(\delta\rho,\delta\mathcal T)$ 有

$$
\|W^\star-\widehat W^\star\|\le \mu^{-1}\|\nabla\mathcal J(W^\star)-\nabla\widehat{\mathcal J}(\widehat W^\star)\|
$$

（$\mu$ 为强凸模）；

(iii) 产生的指针子空间在谱隙存在时满足 Davis–Kahan 型角度界。

**证明**：频域必要条件由"核型"KKT 与帧惩罚核给出；强凸$\Rightarrow$ Lipschitz 稳定；子空间稳定由矩阵扰动理论得到。□

---

## 5. 统一词典（选要条目）

1. **超选扇区**：若所有 $K_{w,h}$ 关于分解 $\mathcal H=\oplus_\alpha\mathcal H_\alpha$ 分块对角，则这些 $\mathcal H_\alpha$ 构成超选扇区（T3）。

2. **几何相位**：干涉相位差 $\Delta\varphi$ 进入刻度 $d\mu_\varphi$，与 LDOS/延迟在 A5 合流。

3. **弱测量/弱值**：视作 I-projection 的一阶扰动；软/硬极限连接 Born（T2）。

4. **Zeno/反 Zeno**：提交频次改变有效窗宽，按三分解重算；信息收支由 KL-链控制。

5. **到达时间 POVM**：为 $K_{w,h}$ 特例；可与窗化迹核的变分模板一致。

6. **共振/寿命**：$\det S$ 的下半平面极点在 $d\mu_\varphi$ 中显为峰/拐点；窗化不生新极点（T5）。

7. **非平稳时频（相位—尺度）**：$(U_\tau,V_\sigma)$ 的多窗帧与 Parseval 结构；对偶由 Wexler–Raz 给出。

8. **采样阈值**：在 $d\mu_\varphi$ 刻度与 PW 带限下，Nyquist 条件使别名归零并保证稳定采样。

9. **PSWF 能量浓聚**：单窗硬约束极值回收到 PSWF（Landau–Pollak–Slepian）。

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

2. **指针基验证**：谱分解 $K_{w,h}$ 检验最小本征子空间的方差极小性；若谱隙存在，用 Davis–Kahan 界评估稳定。

3. **误差闭合**：报告 $(\varepsilon_{\rm alias},\varepsilon_{\rm EM},\varepsilon_{\rm tail})$ 三项占比；带限+Nyquist 校验 $\varepsilon_{\rm alias}=0$。

4. **窗/核 KKT 校核**：在频域检验"多项式乘子 + 卷积核"的带限投影方程与归一约束；多窗实验记录 Pareto 曲面与 Lipschitz 常数。

5. **零集稳定**：测 $\inf_{\partial D}|E|$ 与误差上界 $\eta$，验证 Rouché 条件与零点位移界（不生新奇）。

---

## 8. 结语

本体系以三根主干闭合**量子测量的可检理论**：**(i)** 相位—密度刻度 $d\mu_\varphi$；**(ii)** 窗口化读数 $K_{w,h}$ 与 **Nyquist–Poisson–EM** 三分解；**(iii)** 信息几何（I-projection/KL）。在 **A1–A7** 与 **T1–T7** 的桥接下，得到：**Born = I-projection（充要）**、**指针基 = 光谱极小**、**$\varphi'=-\pi\rho_{\rm rel}=\operatorname{tr}\mathsf Q/2$**、**窗/核最优 = 带限投影-KKT + 多窗双正交**；全链路与 S15–S26、euler-quantum 理论系列、EBOC-Graph 可交换，并给出严谨、可实现且可复现的窗口化量子测量学框架。

---

## 参考文献（关键锚点）

**Herglotz–Weyl / DBK**：Kostenko–Teschl 等关于（奇点）Weyl $m$-函数与 Herglotz 性；边界值 $\Im m=\pi\rho$。

**BK / 谱移函数**：Pushnitski（2010）"$e^{-2\pi i\xi}=\det S$"；Yafaev 教材综述。

**Wigner–Smith 延迟**：$\mathsf Q=-iS^\dagger dS/dE$、$\operatorname{tr}\mathsf Q=\partial_E\arg\det S$（多物理场综述）。

**Ky Fan（最小和）**：PNAS 1951。

**Poisson/采样**：Candès 讲义（别名与 Nyquist）。

**Euler–Maclaurin 余项界**：DLMF / 经典上界。

**Stone / Stone–von Neumann**：Harvard 讲义与历史综述。

**Wexler–Raz / 帧**：Daubechies, Landau & Landau, J. Fourier Anal. Appl. 1(4): 437–478 (1995)。

**PSWF 能量浓聚**：Landau–Pollak–Slepian 系列。

---

**统一备注**：全文所有数学均以 $\cdot$ 为默认乘积、$\ast$ 为卷积；等式链使用标准等号，避免误读为常数式。对 BK 号记的正/负版本仅作一次性"规范与号记"说明，上下文随之自洽。该框架与本项目所有前序理论（S15–S26、euler-quantum 系列、EBOC-Graph）严格对齐，提供量子测量的统一可检理论基础。
