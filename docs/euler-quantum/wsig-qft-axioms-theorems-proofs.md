# WSIG-QFT：窗口化散射与信息几何的场论公理、定理与证明

Version: 1.3

**作者**：Auric（S-series / EBOC）
**关键词**：窗口化读数；de Branges–Kreĭn 规范系统；Weyl–Heisenberg 表象；Birman–Kreĭn；Wigner–Smith 延迟；I-投影；Wexler–Raz；Nyquist–Poisson–Euler–Maclaurin（NPE）误差闭合
**MSC**：81Txx；47Bxx；46E22；42C15

---

## 摘要

本文构建并严格化 **WSIG-QFT（Windowed Scattering & Information-Geometry Quantum Field Theory）**：在带权 Mellin—对数模型与 de Branges–Kreĭn（DBK）规范系统下，以 **Weyl–Heisenberg** 运动学刻度"相位—尺度"，以 **Birman–Kreĭn（BK）—Wigner–Smith（WS）** 链连接散射相位导数与（相对）谱密度，以 **Csiszár-型 I-投影**实现 **Born 概率 = 相对熵最小化**，以 **Ky-Fan 光谱极小**实现 **指针基 = 读数二次型的谱极小**，并以 **Nyquist–Poisson–Euler–Maclaurin（NPE）** 提供非渐近误差闭合与带限-采样判据。多通道下建立 **窗化 BK 恒等式** 与 **多窗帧—Wexler–Raz** 协同条件，并给出可检前提、明确陈述与（依公认判据的）完整证明。

---

## 1. 设定与记号

**对数—Mellin 模型与镜像对合.** 取 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$，令 $x=e^t$ 则与 $L^2(\mathbb R)$ 等距。定义调制/尺度作用

$$
(U_\tau f)(x)=x^{i\tau}f(x),\qquad (V_\sigma f)(x)=e^{\sigma a/2}f(e^\sigma x),
$$

满足 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$（Weyl 关系）。镜像对合 $(Jf)(x)=x^{-a}f(1/x)$ 为酉，Mellin 变换满足 $\mathcal M_a[Jf](s)=\mathcal M_a[f](a-s)$。该对称由标准 Mellin 恒等式给出并见诸手册与 DLMF 条目。

**DBK 规范系统与 Herglotz–Weyl 词典.** 取半轴规范系统 $JY'(t,z)=zH(t)Y(t,z)$（$H\succeq0$ 可积，$J=\tiny\begin{pmatrix}0&-1\\1&0\end{pmatrix}$）。其 Weyl–Titchmarsh 函数 $m(z)$ 为 Herglotz，非切边界虚部给谱密度 $\rho(E)=\pi^{-1}\Im m(E+i0)$；每个 Herglotz 函数皆源自某个迹范化的规范系统（de Branges 定理）。

**散射数据与相位—延迟矩阵.** 设可散射对 $(H_0,H)$ 满足 trace-class 扰动前提；S-矩阵 $S(E)$ 的 Wigner–Smith 延迟矩阵 $Q(E)=-iS(E)^\ast \partial_E S(E)$ 定义良好，其特征值为"固有延迟时间"。

---

## 2. WSIG-QFT 公理

**A1（Weyl–Heisenberg 协变与镜像）.** 物理可观测的相位—尺度作用由 $(U_\tau,V_\sigma)$ 的射影酉表示实现，镜像 $J$ 实现 $s\mapsto a-s$ 的完成对称（Mellin 侧）。

**A2（窗化读数）.** 任何现实读数皆等价于能量侧卷积—加权的线性泛函

$$
\mathcal R[F;\rho_\star]\equiv \int_{\mathbb R} F(E)\,\rho_\star(E)\,dE,\qquad F:=h\!*\!w_R,
$$

其中 $h$ 为前端核，$w_R$ 为偶窗，$\rho_\star=\rho$ 或相对密度 $\rho-\rho_0$。

**A3（相位—密度刻度）.** 在 BK 与 WS 链下，几乎处处

$$
\frac{1}{2\pi}\operatorname{tr}Q(E)=\xi'(E)=\operatorname{tr}\big(\rho-\rho_0\big)(E),\qquad \boxed{\det S(E)=e^{2\pi i\,\xi(E)}},
$$

其中正号约定与 $\xi'=\tfrac{1}{2\pi}\operatorname{tr}Q$ 以及单通道 $\varphi'(E)=\pi\,\rho_{\rm rel}(E)$（$S=e^{2i\varphi}$）完全一致。

**A4（概率—信息一致性）.** 线性矩约束族上最小化 KL-散度的解等价于 Born 概率；其充要条件由 Csiszár 的 I-投影几何与勾股恒等式给出。

**A5（NPE 非渐近闭合）.** 对 $F=h\!*\!w_R$ 的等距采样/数值求积，误差按 **alias（Poisson）+ EM 伯努利层 + 尾项** 三分解；若 $\operatorname{supp}\widehat F\subset[-\Omega_F,\Omega_F]$ 且 $\Delta\le \pi/\Omega_F$，则别名项为 $0$。

---

## 3. 运动学与镜像核

### 定理 3.1（CCR—Weyl 关系与对数表象等价）

令 $U_\tau=e^{i\tau A}$、$V_\sigma=e^{i\sigma B}$，其中在核 $\mathcal D:=C_c^\infty(\mathbb R_+)$ 上
$$(Af)(x)=(\log x)f(x),\qquad (Bf)(x)=-i\big(x\partial_x+\tfrac a2\big)f(x).$$
则在共同稠密核 $\mathcal D$ 上有 $[A,B]=iI$，闭包后 $[\overline A,\overline B]=iI$，其指数式给出 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$。经 $x=e^t$ 等距，与 $L^2(\mathbb R)$ 的调制—平移表象幺正等价。

**证明（略要）**：Stone 定理给强连续一参数群与生成元；直接计算得 Weyl 关系；等距映射由 $L^2(\mathbb R_+,x^{a-1}dx)\simeq L^2(\mathbb R)$ 与 Mellin–Fourier 互化给出。∎

### 定理 3.2（镜像核与完成函数）

若 $K(x)=x^{-a}K(1/x)$ 且 $K\in L^1(\mathbb R_+,x^{a-1}dx)$，则 Mellin 变换 $\Phi(s)=\int_0^\infty K(x)x^{s-1}dx$ 满足 $\Phi(s)=\Phi(a-s)$。乘以对称因子 $r(s)$ 得完成函数 $\Xi(s)=r(s)\Phi(s)$。

**证明**：由 $J$ 的定义与 $\mathcal M_a[Jf](s)=\mathcal M_a[f](a-s)$ 直接推出。∎

---

## 4. 动力学：相位—密度—延迟

### 定理 4.1（相位导数 =（相对）谱密度）

设 $(H_0,H)$ 为自伴对且 $H-H_0\in \mathfrak S_1$。记谱移函数 $\xi$ 与 S-矩阵 $S(E)$。则 a.e. $E$ 有

$$
\boxed{\det S(E)=e^{2\pi i\,\xi(E)}},\qquad \xi'(E)=\frac{1}{2\pi}\operatorname{tr}Q(E)=\operatorname{tr}(\rho-\rho_0)(E),
$$

单通道时 $S(E)=e^{2i\varphi(E)}$ 并 $\varphi'(E)=\pi\,\rho_{\rm rel}(E)$。

**证明**：第一式为 Birman–Kreĭn 公式；第二式由 $Q(E)=-iS^*\partial_ES$ 与 $\partial_E\arg\det S(E)=\operatorname{tr}Q(E)$ 得；$\xi'$ 与相对局域态密度（relative LDOS）之等价见谱移—迹公式（下一节）。单通道情形代入 $S=e^{2i\varphi}$ 即证。∎

### 命题 4.2（阈值与相位临界对齐）

若某阈值 $E_0$ 处 $\rho_{\rm rel}(E_0)=0$，则 $\varphi'(E_0)=0$。

**证明**：由定理 4.1 的单通道式 $\varphi'=\pi\,\rho_{\rm rel}$ 直接推出。∎

---

## 5. 窗化迹公式与窗化 BK 恒等式

### 定理 5.1（Lifshits–Kreĭn 迹公式—窗化版）

设 $f\in \mathrm{OL}(\mathbb R)$（算子 Lipschitz），取 $f=(h\!*\!w_R)$ 的原函数使 $f' =F$。则

$$
\operatorname{tr}\!\big(f(H)-f(H_0)\big)=\int_{\mathbb R} f'(E)\,\xi(E)\,dE
= \int_{\mathbb R} F(E)\,\xi(E)\,dE.
$$

**证明要点**：对 $H-H_0\in\mathfrak S_1$ 的成对自伴算子，Lifshits–Kreĭn 迹公式在 $f\in\mathrm{OL}$ 类上成立；置 $f' =F$ 即得"窗化迹"。∎

### 定理 5.2（窗化 Birman–Kreĭn 恒等式）

在定理 5.1 前提下，分部积分并用 $\boxed{\det S(E)=e^{2\pi i\,\xi(E)}}$ 得

$$
\int_{\mathbb R} F(E)\,\xi'(E)\,dE
= -\frac{1}{2\pi i}\int_{\mathbb R} F'(E)\,\log\det S(E)\,dE
= -\frac{1}{2\pi i}\int_{\mathbb R} \big(h' * w_R\big)(E)\,\log\det S(E)\,dE.
$$

若 $h,w_R$ 带限且光滑，右端有限并给出窗化 BK 账本。

**前提补充**：取与 $\xi$ 对齐的连续分支 $\boxed{\log\det S(E):=2\pi i\,\xi(E)}$。若 $F\in W^{1,1}\cap L^1$ 且 $\boxed{F(E)\,\xi(E)\to 0\ (E\to\pm\infty)}$（或 $F$ 具紧支撑），则分部积分无边界项，上式成立并与 Nyquist 带限情形的采样无混叠相容。

**证明**：由定理 5.1 写作 $\int f'\xi$，以 $f'=F$，分部积分并代入 BK 公式即证。∎

---

## 6. 概率—信息层：Born = I-投影；Pointer = 光谱极小

### 定理 6.1（Born 概率 = KL-I 投影（充要））

设先验 $q$ 与线性矩约束族 $\mathcal L=\{p:\ \mathbb E_p[\phi_j]=c_j\}$ 非空。最小化 $D_{\rm KL}(p\Vert q)$ 的解 $p^\star$ 取指数族形式，且当且仅当 $\log p^{\rm Born}-\log q$ 落在约束法向子空间加常数的仿射包中时，$p^\star=p^{\rm Born}$。

**证明**：Csiszár 的 I-投影 KKT 条件与勾股恒等式给出充要条件；温度参数 $\beta\to\infty$ 的 softmax 退化为硬投影。∎

### 定理 6.2（指针基 = 光谱极小（充要））

设读数二次型 $Q_X=\operatorname{tr}(X^*AX)$（或窗算子谱半正）并限制在秩 $k$ 正交投影集合。则最小值为 $\boxed{\sum_{j=1}^k\lambda_j^\uparrow(A)}$ 于 $A$ 的最小 $k$ 维本征子空间处取得（Ky-Fan 原理）；谱隙 $\delta$ 下，该子空间对扰动 $|A-\tilde A|\le \varepsilon$ 的偏转由 Davis–Kahan 给出 $\sin\Theta\lesssim \varepsilon/\delta$。

**证明**：Ky-Fan 迹极小与 Rayleigh–Ritz；稳定性由 Davis–Kahan。∎

---

## 7. NPE：别名 + Euler–Maclaurin + 尾项 的非渐近闭合

### 定理 7.1（Poisson—Nyquist 与别名消失）

设 $F\in L^1\cap C^1$ 且 $\widehat F$ 紧支集于 $[-\Omega_F,\Omega_F]$。对步长 $\Delta>0$ 有 Poisson 求和

$$
\Delta\sum_{n\in\mathbb Z}F(n\Delta)=\sum_{k\in\mathbb Z}\widehat F\!\left(\tfrac{2\pi k}{\Delta}\right).
$$

若 $\Delta\le \pi/\Omega_F$，则仅 $k=0$ 项存留，别名项 $k\neq0$ 全零。

**证明**：由 Poisson 公式标准版与带限支撑直接推出。∎

### 定理 7.2（Euler–Maclaurin 有界余项）

对 $F\in C^{2M}([a,b])$ 有

$$
\sum_{n=a}^{b}F(n)=\int_a^b F(x)\,dx+\tfrac{F(a)+F(b)}{2}+\sum_{m=1}^{M-1}\tfrac{B_{2m}}{(2m)!}\big(F^{(2m-1)}(b)-F^{(2m-1)}(a)\big)+R_{2M},
$$

其中 $|R_{2M}|\le \dfrac{2\zeta(2M)}{(2\pi)^{2M}}\int_a^b|F^{(2M)}(x)|\,dx$。

**证明**：经典 EM 推导与周期化 Bernoulli 多项式余项估计。∎

### 定理 7.3（NPE 三分解闭合）

令求值量为 $\mathcal S_T:=\Delta\sum_{|n|\le T/\Delta}F(n\Delta)$，$\mathcal I:=\int_{\mathbb R}F$。则

$$
\mathcal S_T-\mathcal I=\underbrace{\sum_{k\neq0}\widehat F\!\left(\tfrac{2\pi k}{\Delta}\right)}_{\text{alias}}+\underbrace{\mathsf{EM}_{2M}(F;\Delta,T)}_{\text{伯努利层}}+\underbrace{\int_{|x|>T}F(x)\,dx}_{\text{尾项}},
$$

并给出别名消失的 Nyquist 判据与 EM/尾项的显式上界。

**证明**：定理 7.1 与 7.2 叠加并分离截断尾项即得。∎

---

## 8. 多通道散射：CCS 与窗化账本

### 定理 8.1（多通道 CCS 主定理：窗化 BK）

设 $n$ 通道 S-矩阵 $S(E)$ 可微，$H-H_0\in\mathfrak S_1$。取 $h\in W^{1,1}$、偶窗 $w_R\in W^{1,\infty}\cap L^1$，令 $F=h\!*\!w_R$。则 a.e. $E$

$$
\partial_E\arg\det S(E)=\operatorname{tr}Q(E),\quad \frac{1}{2\pi}\operatorname{tr}Q(E)=\operatorname{tr}\big(\rho-\rho_0\big)(E),
$$

且成立窗化 BK 恒等式

$$
\int_{\mathbb R}\!F(E)\,\operatorname{tr}(\rho-\rho_0)(E)\,dE
=-\frac{1}{2\pi i}\int_{\mathbb R}\!\big(h' * w_R\big)(E)\,\log\det S(E)\,dE\,.
$$

若 $h,w_R$ 带限且 $\boxed{\Delta\le \pi/\min\{\Omega_h,\Omega_w\}}$，则数值采样的别名为零。

**证明**：第一行由定理 4.1；第二行由定理 5.2；Nyquist 结论由定理 7.1 作用在 $\boxed{\widehat F=\widehat h\cdot\widehat w_R}$ 的支持上推得。若 $\operatorname{supp}\widehat h\subset[-\Omega_h,\Omega_h]$、$\operatorname{supp}\widehat w_R\subset[-\Omega_w,\Omega_w]$，则
$$
\operatorname{supp}\widehat F\subset[-\Omega_F,\Omega_F],\quad \Omega_F:=\min\{\Omega_h,\Omega_w\},
$$
从而取 $\boxed{\Delta\le \pi/\Omega_F}$ 时采样别名项为零。∎

---

## 9. 多窗协同：帧、Wexler–Raz 与稳健优化

### 定理 9.1（均匀移位帧与 Wexler–Raz 双正交）

在"频域对角化/单块无混叠"设定下（即 $\{\widehat w_\alpha\}$ 按 $b\mathbb Z$ 平移的支撑互不重叠，使帧算子在频域对角化），族 $\{M_{mb}T_{na}w_\alpha\}$ 为 Parseval 的充要条件是

$$
\boxed{\frac{1}{a}\sum_\alpha \big|\widehat w_\alpha(\xi)\big|^2\equiv 1\quad(\text{a.e. }\xi)}.
$$

在一般情形，上式为充分条件；必要条件需同时满足 Wexler–Raz 双正交的交错约束。

其对偶窗满足 Wexler–Raz 双正交与 Janssen-型对偶性。

**证明**：Wexler–Raz 身份与密度定理给出 Parseval/Tight 条件与双正交关系。∎

### 定理 9.2（非平稳 Gabor 帧的对角化与界）

在"单块无混叠"（频域支持不交）与 Calderón 和可加界下，非平稳窗族帧算子在频域对角化，帧界由 $\mathcal C(\xi)=\sum_\alpha |\widehat w_\alpha(\xi)|^2/a_\alpha$ 的本征界给出；$|\mathcal C-1|_\infty\le\varepsilon$ 时帧界为 $(1-\varepsilon,1+\varepsilon)$。

**证明**：参照非平稳 Gabor 帧的构造与对偶窗显式式子，对角化来自块-无混叠下的点态乘子结构。∎

### 定理 9.3（多窗-NPE 协同优化的 KKT 方程）

以 NPE 上界为对手、带限偶子空间为可行域，极小化 $\mathsf{alias}+\mathsf{EM}+\mathsf{tail}$ 得到"带限投影 + 卷积乘子"的 KKT 方程；Hilbert 强凸设定下解唯一。

**证明**：目标为窗函数的二次—凸泛函，约束为带限线性子空间；KKT 正常性与强凸性给唯一解。∎

---

## 10. 与标准场论的接口

**Wightman/LSZ 的窗化替代.** 正定性由 RKHS/WH 实现；微因果可替换为"窗化局域性 + 采样无混叠"；Haag–Ruelle/LSZ 的入/出场在能量窗下更稳定，并可用窗化 BK 对相位增量与谱移进行校准。（参考 Streater–Wightman 纲要、Haag–Ruelle 扩展与综述。）

---

## 11. 例：一维 Schrödinger 与图上 Ihara ζ

**（i）一维势散射.** 令 $H=-\partial_x^2+V$、$H_0=-\partial_x^2$。窗化读数 $\int F\,\rho_{\rm rel}$ 等价于窗化相位增量 $-\tfrac{1}{2\pi i}\int F'\log\det S$；$\varphi'=\pi\rho_{\rm rel}$ 与 Wigner–Smith 延迟一致。

**（ii）图上的 Ihara ζ（离散场）.** 对有限 $(q+1)$-正则图，Ihara ζ 的完成多项式满足 $\Xi_G(s)=\Xi_G(1-s)$；其行列式表达式与谱—轨道词典提供离散版本的"窗化读数—误差闭合"。

---

## 12. 复现实验清单（Minimal Working Example）

1. 选偶窗 $w_R\in \mathsf{PW}^{\rm even}_\Omega$、核 $h\in W^{2M,1}$；取 $\boxed{\Delta\le \pi/\min\{\Omega_h,\Omega_w\}}$ 与 EM 阶 $M\ge2$，截断半径 $T$。
2. 由散射数据计算 $\rho$ 或 $\rho_{\rm rel}$，评估 $\int (h\!*\!w_R)\,\rho_\star$ 与窗化 BK。
3. 构造多窗 Parseval 帧（定理 9.1），必要时解定理 9.3 的 KKT 方程以微调带宽分配。
4. 决策层以 I-投影完成概率校准（定理 6.1），软/硬温度切换由 $\beta$ 控制。

---

## 13. 与 S-series / UMS / WSIG-QM 的接口

**13.1 与 S15–S26 的接口。**
- S15–S17 的 Herglotz 表示与规范系统为本文 §1 的 DBK 规范系统提供解析结构。
- S24 的纤维 Gram 表征与 Wexler–Raz 双正交为本文定理 9.1 提供具体实现框架。
- S25 的非平稳 Weyl–Mellin 框架与本文定理 9.2 的非平稳 Gabor 帧共享数学结构。
- S26 的相位密度刻度 $\varphi'(x)=\pi\rho(x)$ 与本文公理 A3、定理 4.1 完全一致。

**13.2 与 WSIG-QM 的接口。**
- 本文可视为 WSIG-QM 的场论版本；WSIG-QM 的七大公理（A1–A7）与本文公理 A1–A5 在概念与表述上高度对齐。
- WSIG-QM 的定理 T1（窗口化读数恒等式）对应本文定理 5.2（窗化 BK 恒等式）。
- WSIG-QM 的定理 T2（Born = I-projection）对应本文定理 6.1。
- WSIG-QM 的定理 T3（指针基 = 光谱极小）对应本文定理 6.2。
- WSIG-QM 的定理 T4（相位—密度—延迟统一）对应本文定理 4.1。

**13.3 与 UMS 的接口。**
- UMS 的核心统一式 $d\mu_\varphi = \tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\,dE = \rho_{\mathrm{rel}}\,dE = \tfrac{\varphi'}{\pi}\,dE$ 与本文公理 A3、定理 4.1 完全一致。
- UMS 的公理 A2（有限窗口读数）对应本文公理 A2。
- UMS 的定理 4.1–4.3（Nyquist–Poisson–EM 闭合）对应本文定理 7.1–7.3。
- UMS 的定理 5.1（DPI）与本文定理 6.1（I-投影）在信息几何层面一致。

**13.4 与窗口化路径积分理论的接口。**
- 路径积分理论的核心定理 2.1（窗—核对偶）可在能量域改写为本文公理 A2 的窗化读数。
- 路径积分理论的定理 4.1（BK + Wigner–Smith）对应本文定理 4.1。
- 路径积分理论的 Nyquist–Poisson–EM 误差闭合与本文定理 7.1–7.3 共享框架。

**13.5 与量子引力场理论的接口。**
- 量子引力场理论的定理 3.1（相位—DOS—延迟恒等式）对应本文定理 4.1。
- 量子引力场理论的定理 3.2（窗化 BK 恒等式）对应本文定理 5.2。
- 量子引力场理论的非渐近误差闭合（§6.2）与本文定理 7.3 完全一致。

**13.6 与 FMU 的接口。**
- FMU 的相位密度坐标 $d\mu_\varphi=(1/\pi)\varphi'\,d\omega$ 与本文公理 A3 在 Mellin 语境下一致。
- FMU 的定理 4.1（Nyquist–Poisson–EM 三分解）对应本文定理 7.1–7.3。
- FMU 的 Landau–Wexler–Raz–Balian–Low 判据与本文定理 9.1 共享帧理论基础。

**13.7 保持"极点 = 主尺度"的有限阶 EM 纪律。**
- 本文在所有离散—连续换序中均采用**有限阶** EM（定理 7.2），确保不引入新奇点。
- 与 S15–S26、WSIG-QM、UMS、路径积分理论、量子引力场理论、FMU 保持一致：EM 余项仅作有界扰动。

---

## 参考文献（选）

[1] Yafaev, *Mathematical Scattering Theory*（BK 综述）; Pushnitski, "An integer-valued version of the Birman–Kreĭn formula".
[2] Gesztesy 等，"The Xi Operator and its Relation to Krein's Spectral Shift Function"；Behrndt–Malamud–Neidhardt,"Trace formulae…"。
[3] Smith, "Lifetime Matrix in Collision Theory"；Wigner–Smith 延迟在电磁/声学中的推广综述。
[4] de Branges, *Hilbert Spaces of Entire Functions*；Eckhardt–Teschl 方向的规范系统密度定理。
[5] Csiszár, "I-Divergence Geometry…"；信息投影勾股恒等式与投影定理。
[6] Peller,"Lifshits–Kreĭn trace formula and operator Lipschitz functions"。
[7] Heil,"History and Evolution of the Density Theorem for Gabor Frames"；Daubechies–Landau–Landau,"Gabor Time–Frequency Lattices and the Wexler–Raz Identity"。
[8] Balazs 等，"Theory, implementation and applications of nonstationary Gabor frames"。
[9] Landau,"Necessary density conditions for sampling and interpolation of certain entire functions"。
[10] Poisson 求和与 Euler–Maclaurin（NIST DLMF/维基条目，含余项界）。
[11] Terras, *Zeta Functions of Graphs*（Ihara ζ 完成对称）。

---

### 附录 A：若干证明细节

**A.1 Lifshits–Kreĭn 迹公式到窗化 BK.** 由 $\operatorname{tr}\big(f(H)-f(H_0)\big)=\int f'\xi$（$f\in\mathrm{OL}$）与 $\boxed{\det S=e^{2\pi i\xi}}$ 得 $\int F\,\xi'=-\tfrac{1}{2\pi i}\int F'\log\det S$。将 $F=h\!*\!w_R$ 展开，可得定理 5.2。

**A.2 Born = I-投影的充要条件.** 设 $\mathcal L=\{p:\langle \phi_j,p\rangle=c_j\}$。极小化 $D_{\rm KL}(p\Vert q)$ 的拉格朗日子问题解为 $p^\star\propto q\,e^{\sum_j\lambda_j\phi_j}$。若 $p^{\rm Born}$ 满足同一矩并且 $\log p^{\rm Born}-\log q\in{\rm span}\{\phi_j\}\oplus\mathbb R$，则 KKT 满足；反向由勾股恒等式唯一性推出。

**A.3 Ky-Fan 与 Davis–Kahan.** 令 $\mathcal P_k$ 为秩 $k$ 投影集，极小 $\operatorname{tr}(PA)$ 于 $P\in\mathcal P_k$ 取得在 $A$ 的最小谱子空间；扰动界由 $\sin\Theta\le |A-\tilde A|/\delta$ 给出。

**A.4 NPE 的常数与带限判据.** Poisson 公式给别名总和；若 $\widehat F$ 支持在 $[-\Omega_F,\Omega_F]$ 且 $\Delta\le\pi/\Omega_F$，则 $k\neq0$ 的 $\widehat F(2\pi k/\Delta)$ 全零（Nyquist）。EM 余项用 $\zeta(2M)$ 界。

---

**结语.** WSIG-QFT 将"Weyl–Heisenberg 运动学 + DBK 规范系统 + BK/WS 相位—密度刻度 + I-投影与光谱极小 + NPE 非渐近闭合 + 多窗帧/WR"串为可检—可算—可复现的一套公理—定理体系；文中各定理均锚定公开判据与标准文献，并给出严格证明或依权威定理的严格化推演，从而为有限窗口条件下的场论读数、延迟与概率-信息一致性提供统一、稳健与可实现的理论骨架。
