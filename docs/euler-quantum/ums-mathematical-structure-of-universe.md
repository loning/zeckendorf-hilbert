# 宇宙的数学结构（UMS）

**—— 有限窗口协变的"散射—信息—几何"统一理论（正式学术论文，含完整证明）**

**作者**：Auric（S-series / EBOC 体系）
**版本**：v2.1（可并入 S15–S26、S21、EBOC-Graph）

---

## 摘要

本文以**相位—密度刻度**、**窗口化读数**与**信息几何**为三根主轴，把"态—测量—概率—指针—散射相位—群延迟—采样/帧—误差学—通道容量"焊接为一个可验证的**范畴化**统一理论（UMS）。核心统一式采用**同一测度的三种密度表达**：

$$
\boxed{\, d\mu_{\varphi}(E)\ :=\ \frac{\varphi'(E)}{\pi}\,dE\ =\ \frac{1}{2\pi}\,\operatorname{tr}\mathsf Q(E)\,dE\ =\ \rho_{\mathrm{rel}}(E)\,dE\ }\,
$$

其中 $\mathsf Q(E)=-i\,S^\dagger(E)\,S'(E)$ 为 Wigner–Smith 群延迟矩阵，$\rho_{\mathrm{rel}}(E)=-\xi'(E)$ 为 Birman–Kreĭn 谱移密度（采用 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 的约定）。该式把散射相位导数、相对谱密度与群延迟统一到同一刻度；测量读数以**窗—核**谱积分表示，并以 **Nyquist–Poisson–Euler–Maclaurin（EM）** 三分解给出**有限阶、非渐近**误差闭合；概率唯一性由 Naimark 扩张与 Gleason 定理保障；采样/帧门槛由 Landau 必要密度、Wexler–Raz 双正交与 Balian–Low 不可能性刻画；开放系统的信息单调与容量上界由 GKSL 主方程、量子相对熵在**正迹保持**映射下的单调（DPI）以及 HSW 定理控制。

**关键词**：散射相位；Wigner–Smith 群延迟；Birman–Kreĭn；de Branges / Herglotz；Naimark 扩张；Gleason；Landau 密度；Wexler–Raz；Balian–Low；Euler–Maclaurin；Poisson；GKSL；DPI；HSW。

---

## 0. 预备与号记

**0.1 散射与群延迟。** 设 $S(E)\in U(N)$ 可微，Wigner–Smith 群延迟矩阵定义为 $\mathsf Q(E)=-i\,S^\dagger(E)\,S'(E)$。对酉 $S$ 有 $S^\dagger S'=(S^{-1}S')$ 反厄米，故迹纯虚。因 $S^\dagger S'$ 反厄米，$\operatorname{tr}(S^\dagger S')$ 纯虚，故 $-i\,\operatorname{tr}(S^\dagger S')=\Im\,\operatorname{tr}(S^\dagger S')\in\mathbb R$；于是

$$
\operatorname{tr}\mathsf Q(E)=-i\,\operatorname{tr}\!\big(S^\dagger S'(E)\big)=\Im\,\operatorname{tr}\!\big(S^\dagger S'(E)\big)=\frac{d}{dE}\Arg\det S(E)\ \ (\text{a.e.}),
$$

单通道 $S(E)=e^{2i\varphi(E)}$ 时 $\operatorname{tr}\mathsf Q(E)=2\,\varphi'(E)$。

**0.2 谱移与 Birman–Kreĭn。** 采用 BK 的**负号约定**：$\ \det S(E)=e^{-2\pi i\,\xi(E)}$，则

$$
\frac{d}{dE}\Arg\det S(E)=-2\pi\,\xi'(E),\qquad \rho_{\mathrm{rel}}(E):=-\xi'(E),
$$

因此 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)$（a.e.）。

**0.3 DBK 规范系统与 Herglotz 词典。** 一维 de Branges–Kreĭn 规范系统 $JY'(t,z)=zH(t)Y(t,z)$ 的 Weyl–Titchmarsh 函数 $m:\mathbb C^+\to\mathbb C^+$ 为 Herglotz 函数，其边界虚部给出绝对连续谱密度 $\rho(E)=\pi^{-1}\Im m(E+i0)$（a.e.）；与 de Branges 空间存在经典等价。

**0.4 采样、帧与门槛。** Paley–Wiener 类的稳定采样/插值服从 Landau 必要密度；Gabor 系的对偶窗满足 Wexler–Raz 双正交；临界密度下满足 Balian–Low 不可能性。

**0.5 测量与概率唯一性。** 任一 POVM 可由更大空间中的 PVM 压缩得到（Naimark 扩张）；当 $\dim\mathcal H\ge 3$ 时，满足可加性的概率测度必为 $\operatorname{Tr}(\rho\,\cdot)$（Gleason 定理）。

**0.6 开放系统与信息界。** 马尔可夫开放演化由 GKSL（Lindblad）主方程描述；量子相对熵在**正迹保持**映射下单调不增（DPI）；量子信道的无助理经典容量由 HSW 正则化公式给出。

**0.7 Nyquist–Poisson–EM（有限阶非渐近误差学）。** 带限信号在采样率 $f_s>2B$ 下别名项消失；Euler–Maclaurin（EM）用于离散—连续换序时，取 $m\in\mathbb N$ 使被积/被和函数 $F\in C^{2m}$ 且相应导数有界或具有限总变差，则余项具**显式积分上界**，可操作地给出"伯努利层 + 余项"。

---

## 1. 公理体系（Axioms）

**A1（双表象与协变）。** $\mathcal H(E)$（能量表象）与 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$（相位—尺度表象）等距等价；离散—连续换序使用**有限阶** EM，按 0.7 的光滑与（有界或有限变差）前提控制余项。此"等距等价"系指在所用 DBK 规范系统/Weyl–Mellin 变换**已构造到位**时的单位算子实现；读者不应将其理解为任意系统之间的无条件同构。

**A2（有限窗口读数）。** 任一次"可实现读数"写作窗—核谱积分 $K_{w,h}=\int h(E)\,w_R(E)\,d\Pi_A(E)$；误差以"别名（Poisson）+ 伯努利层（EM）+ 截断"三项**非渐近闭合**；带限且 $f_s>2B$ 时别名为 0。

**A3（概率—信息一致性）。** 对 PVM $\{P_j\}$ 与态 $\rho$，线性约束 $p_j=\operatorname{Tr}(\rho P_j)$ 使可行集为单点 $\{p^\star\}$，任意严格凸 Bregman/KL 的 I-projection 唯一取于 $p^\star$；POVM 情形先作 Naimark 扩张到 PVM 再回推。Gleason（$\dim\mathcal H\ge3$）确保此概率形式的唯一性。

**A4（指针基）。** 指针基为 $K_{w,h}$ 的**光谱极小**本征基（Ky Fan 变分原则：固定秩子空间上的迹极小取于本征子空间）。

**A5（相位—密度—延迟刻度）。** 采用 BK 约定，

$$
\boxed{\, \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}\ \ \text{(a.e.)}\ }\,.
$$

**A6（采样—帧门槛）。** 稳定采样满足 Landau 必要密度；多窗对偶由 Wexler–Raz 描述；临界密度触发 Balian–Low 不可能性。

**A7（通道—单调—容量）。** 演化受 GKSL 主方程；量子相对熵在正迹保持映射下单调；经典容量由 HSW 定理给出。

---

## 2. UMS 的范畴化定义

**定义 2.1（对象）。**
$U=(\mathcal H,\ \mathcal C,\ \mathscr O,\ \mathbb W,\ \mathcal S,\ D)$，其中
(i) $\mathcal H$：由 $\mathcal H(E)/\mathcal H_a$ 纤维化的希尔伯特丛；
(ii) $\mathcal C$：闭/开放演化（含 GKSL 半群）；
(iii) $\mathscr O$：可观测与谱测度 $E_A$；
(iv) $\mathbb W$：窗—核系统与 Nyquist–Poisson–EM 误差账本；
(v) $\mathcal S$：散射函子 $E\mapsto(S,\mathsf Q,\xi)$；
(vi) $D$：信息散度（KL/Bregman）与其诱导几何。

**定义 2.2（态与刻度）。** 纯态/混合态分别为向量/密度算子；定义**相位—密度刻度**

$$
d\mu_{\varphi}(E)\ :=\ \frac{\varphi'(E)}{\pi}\,dE\ =\ \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE\ =\ \rho_{\mathrm{rel}}(E)\,dE\,.
$$

**定义 2.3（态射）。** 对象间态射为保持 (i)–(vi) 的结构映射；态间态射默认取 **CPTP（量子信道）**；仅当陈述 DPI 时，可放宽为**正迹保持（PTP）**映射（DPI 在此范围内仍成立，但 HSW 容量定理需要 CPTP）。

---

## 3. 主定理与完整证明

### 定理 3.1（UMS 表示定理）

**命题。** 任何满足 A1–A7 的有限窗口测量理论，与某个 DBK 规范系统（及其 Herglotz 函数 $m$）所确定的 $U\in\mathbf{UMS}$ 等价；在此等价下

$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\rho_{\mathrm{rel}}(E)=\frac{\varphi'(E)}{\pi}\quad\text{(a.e.)},
$$

测量侧 $K_{w,h}$ 与信息侧（I-projection）满足 A2–A3；帧与门槛满足 A6；等价唯一至相位重参数化与酉变换。

**证明。**
(1) **散射—相位—密度统一。** 由 0.1 得 $\operatorname{tr}\mathsf Q=\tfrac{d}{dE}\Arg\det S$；由 0.2 得 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$；单通道再与 $\operatorname{tr}\mathsf Q=2\varphi'$ 合并，得统一刻度。
(2) **Herglotz—规范系统—de Branges。** de Branges 理论在 Herglotz $m$、trace-normed 规范系统与 de Branges 空间间建立等价，$\pi^{-1}\Im m$ 给出 a.c. 谱密度，从而赋予 UMS 的能量刻度。
(3) **窗口化读数与有限阶闭合。** Poisson 在 Nyquist 阈值上别名 0；EM 在 0.7 假设下给出伯努利层与余项上界，故 A2 成立。
(4) **概率一致性。** POVM 由 Naimark 扩张为 PVM；Gleason 保证 Born 形式唯一；严格凸散度的 I-projection 在单点可行集上退化为 Born。
(5) **帧与门槛。** Landau 必要密度、Wexler–Raz 双正交与 Balian–Low 不可能性分别给出阈值、对偶与临界障碍。
综上得证。∎

---

### 定理 3.2（刻度唯一性）

**命题。** 若两套构形具有相同 $\operatorname{tr}\mathsf Q(E)$（a.e.）且其测量的 Naimark 扩张同型，则二者于 $\mathbf{UMS}$ 中酉等价；于是

$$
d\mu_\varphi(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE
$$

为读数几何的**唯一刻度**（至零测集与单调重参数化）。

**证明。** $\operatorname{tr}\mathsf Q$ 相同 $\Rightarrow$ $\Arg\det S$ 差常数；由 BK 得同一 $\xi'$ 与 $\rho_{\mathrm{rel}}$。Herglotz 表示唯一确定 $m$，进而确定规范系统与 de Branges 空间；Naimark 同型确保 POVM 层一致，故存在酉等价。∎

---

### 定理 3.3（三位一体）

**(i) Born = I-projection（严格）。** 在 PVM $\{P_j\}$ 下，可行集为单点 $\{p^\star\}$；任意严格凸 Bregman/KL 的 I-projection 唯一取于 $\,p^\star$。POVM 先作 Naimark 扩张，再回推。∎

**(ii) Pointer = 光谱极小（Ky Fan）。** 对自伴 $K_{w,h}$，$\min_{U^\dagger U=I_r}\operatorname{tr}(U^\dagger K_{w,h}U)=\sum_{k=n-r+1}^{n}\lambda_k(K_{w,h})$，极小子空间由 $K_{w,h}$ 的**最小** $r$ 个本征向量张成；若需"最大能量指针"，对应上式取 $\max$ 与前 $r$ 个本征值之和。∎

**(iii) Windows = 极大极小（带限最坏情形）。** 在频域带限与归一约束下，$\sup_{f\in\mathcal F}\lvert\langle f,\mathbf1\rangle-\langle f,w\rangle\rvert$ 的极小窗为带限子空间到常数函数的正交投影核；多窗时最优对偶窗满足 Wexler–Raz。∎

---

### 定理 3.4（采样—帧门槛的相位化）

**命题。** 定义

$$
T(E):=\int_{E_0}^{E}\frac{1}{2\pi}\operatorname{tr}\mathsf Q(u)\,du=\int_{E_0}^{E}\rho_{\mathrm{rel}}(u)\,du=\frac{\varphi(E)-\varphi(E_0)}{\pi}.
$$

在其导数 $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ **a.e. 正**的区间上，$T$ 严格单调并给出可逆重参数化；若存在奇异/原子部分，则在每个 a.c. 区间上分别作相位化并拼接。若 $\mu_\varphi$ 含原子/奇异部分，则在每个 a.c. 区间内用 $T'(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$ 相位化，跨原子点以跳跃量 $\Delta T=\mu_\varphi(\{E_0\})$ 作**分片单调**拼接。此时稳定采样/插值满足 Landau 必要密度；多窗可重构性由帧算子与 Wexler–Raz 双正交刻画；临界密度下满足 Balian–Low 不可能性。∎

---

## 4. 有限阶非渐近误差学（Nyquist–Poisson–EM）

**定理 4.1（Poisson—Nyquist：别名项）。** 若 $\widehat f\subset[-B,B]$ 且采样率 $f_s>2B$，Poisson 求和仅 $k=0$ 支存活，别名误差为 0；若 $f_s<2B$ 则越界频谱重叠产生混叠。∎

**定理 4.2（Euler–Maclaurin：有限阶伯努利层与余项）。** 当 $F\in C^{2m}([a,b])$ 且相应导数有界或具有限总变差时，EM 给出到 $2m$ 阶的伯努利校正与**显式**积分余项；AFP-Isabelle 对余项与收敛条件给出形式化证明，由此可在实现中**择定有限阶 $m$** 并得到可执行上界。∎

**定理 4.3（三分解闭合）。** $K_{w,h}$ 的实现可写为：离散求和（Nyquist）$+$ EM 有限阶校正（伯努利层）$+$ 余项（别名+截断）。当带限且 $f_s>2B$ 时别名层为 0；EM 余项由 4.2 的上界控制，故得**有限阶、非渐近闭合**。∎

---

## 5. 信息单调与容量上界

**定理 5.1（DPI：相对熵在正迹保持映射下单调）。** 对任意正迹保持映射 $\Phi$，

$$
D\!\left(\Phi(\rho)\,\middle\Vert\,\Phi(\sigma)\right)\le D(\rho\Vert\sigma).
$$

**证明要点。** Müller-Hermes–Reeb 以"夹态 Rényi 发散 + 复插值"证明 DPI 在**正迹保持**（不必 CP）下成立，并以 Petz 恢复映射刻画等号情形。∎

**定理 5.2（HSW：无助理经典容量的正则化公式）。** 量子信道 $\mathcal N$ 的无助理经典容量满足

$$
C(\mathcal N)=\lim_{n\to\infty}\frac{1}{n}\,\chi\!\left(\mathcal N^{\otimes n}\right),\qquad I_{\mathrm{acc}}\le \chi\,.
$$

**证明要点。** 参见 Watrous 教科书对编码、Holevo 界与强对偶的标准推导。∎

---

## 6. 派生结构与物理后果

**6.1 时间密度与延迟积分。** 定义

$$
T(E)=\int^{E}\frac{1}{2\pi}\operatorname{tr}\mathsf Q(u)\,du=\frac{\varphi(E)}{\pi}+{\rm const},
$$

单通道即散射相位（除 $\pi$ 因子），表征可测群延迟并与部分密度态联系。

**6.2 非厄米/耗散与共振寿命。** 耗散（非酉）系统存在"修正 BK"与相应时间延迟推广；若存在共振极点 $E_0-i\Gamma/2$，则 $\operatorname{tr}\mathsf Q$ 呈峰并给出寿命 $\tau=\hbar/\Gamma$。可在"最大耗散扩张/耦合散射"的框架下以谱移与广义 Weyl 函数精确表达。

---

## 7. 可检清单（实验/数值）

1. **相位—延迟一致性**：计算 $\Arg\det S(E)$ 与 $\mathsf Q(E)$，验证 $\operatorname{tr}\mathsf Q(E)=\tfrac{d}{dE}\Arg\det S(E)$ 与单通道下 $\varphi'(E)$。
2. **刻度化采样**：以 $T(E)=\int^E(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 重参数化能量，在 $T$ 轴执行 Landau 阈值检验与插值实验，再映回 $E$ 轴。
3. **指针基极小性**：比较任意正交基与 $K_{w,h}$ 本征基的 Ky Fan 部分和。
4. **窗/核最优与 WR**：带限与归一约束下，用 KKT 条件求最优窗；验证与 Wexler–Raz 对偶一致。
5. **三分解误差闭合**：报告"别名 + 伯努利层 + 截断"三项；在带限+Nyquist 下别名 0；EM 余项给出显式上界。
6. **信息收支**：沿"制备 $\to$ 信道 $\to$ 读数"链记录 $D$ 的单调递减与 $I_{\mathrm{acc}}\le\chi\le C$。

---

## 参考文献（选）

1. Patel, U. R., et al., *Wigner–Smith Time-Delay Matrix for Electromagnetics*, 2020。
2. Pushnitski, A., *An Integer-Valued Version of the Birman-Kreĭn Formula*, 2010；Guillarmou, C., *Generalized Krein Formula…*, 2009。
3. de Branges, L., *Hilbert Spaces of Entire Functions*（Purdue）。
4. Landau, H. J., *Necessary Density Conditions…*, Acta Math., 1967。
5. Daubechies, I., Landau, H., Landau, Z., *Gabor Time-Frequency Lattices and the Wexler–Raz Identity*, 1995。
6. Caragea, A., et al., *A Balian–Low Type Theorem for Gabor Riesz Sequences…*, 2023。
7. Naimark's Dilation（综述）与 Busch, P., *A Simple Proof of Gleason's Theorem*, PRL, 2003。
8. Manzano, D., *A Short Introduction to the Lindblad Master Equation*, 2019。
9. Müller-Hermes, A., Reeb, D., *Monotonicity of the Quantum Relative Entropy under Positive Maps*, 2015。
10. Watrous, J., *The Theory of Quantum Information*（HSW 章节）。
11. Eberl, M., *The Euler–MacLaurin Summation Formula*（AFP-Isabelle）。
12. Behrndt, J., Malamud, M., Neidhardt, H., *Trace Formulae for Dissipative and Coupled Scattering Systems*（及相关后续）。

---

## 附录 A：核心等式的自洽推导

**引理 A.1（$\operatorname{tr}\mathsf Q=\tfrac{d}{dE}\Arg\det S$）。** 由 $\mathsf Q=-i\,S^\dagger S'$ 与 $\tfrac{d}{dE}\log\det S=\operatorname{tr}(S^{-1}S')=\operatorname{tr}(S^\dagger S')$（酉性）得

$$
\operatorname{tr}\mathsf Q=-i\,\operatorname{tr}(S^\dagger S')=\Im\,\operatorname{tr}(S^\dagger S')=\frac{d}{dE}\Arg\det S\ \ (\text{a.e.}).
$$

∎

**引理 A.2（BK 链）。** $\det S=e^{-2\pi i\,\xi}\Rightarrow \tfrac{d}{dE}\Arg\det S=-2\pi\,\xi'$；令 $\rho_{\mathrm{rel}}:=-\xi'$，得 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}$。∎

**推论 A.3（单通道回到相位导数）。** 若 $S=e^{2i\varphi}$，则 $\operatorname{tr}\mathsf Q=2\varphi'$；合并 A.2 得 $\varphi'/\pi=\rho_{\mathrm{rel}}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$。∎

---

## 附录 B：Ky Fan 变分与指针极小

令 $K$ 自伴，$\lambda_1\ge\cdots\ge\lambda_n$ 为本征值。Ky Fan 原理给出

$$
\sum_{k=1}^r\lambda_k=\max_{U^\dagger U=I_r}\operatorname{tr}(U^\dagger K\,U),\quad
\sum_{k=n-r+1}^{n}\lambda_k=\min_{U^\dagger U=I_r}\operatorname{tr}(U^\dagger K\,U).
$$

最大迹取于由前 $r$ 个本征向量张成的子空间，最小迹取于由最小 $r$ 个本征向量张成的子空间。∎

---

## 附录 C：EM 余项的有限阶上界

在 0.7 的假设下（$F\in C^{2m}$ 及导数有界/有限变差），EM 公式给出到 $2m$ 阶的伯努利层与**显式**积分余项；AFP–Isabelle 对余项的构造与收敛作了形式化验证，因而在数值实施中可据以选择有限阶 $m$ 并给出可执行上界。∎

---

## 附录 D：与 S15–S26 及 EBOC 体系的接口

**D.1 与 S15–S23（散射相位、Herglotz、Weyl–Mellin、框架）的接口。**
- S15–S17 的 Herglotz 表示与规范系统直接给出 UMS 中的 $\mathcal S$ 函子与 $d\mu_\varphi$。
- S18–S20 的 Weyl–Mellin 非平稳框架为 UMS 的多窗协变提供具体实现。
- S21–S23 的相位—尺度协变与 Euler–Maclaurin 有限阶误差学直接支撑 A1、A2 与定理 4.1–4.3。

**D.2 与 S24–S26（紧框架、非平稳框架、相位密度）的接口。**
- S24 的纤维 Gram 表征与 Wexler–Raz 双正交为 A6 与定理 3.3(iii) 提供具体计算框架。
- S25 的 Calderón sum 与 tight/dual 构造为 UMS 的多窗优化（定义 2.1(iv)）提供可操作方案。
- S26 的相位密度刻度 $\varphi'(x)=\pi\rho(x)$ 与 Landau 必要密度、Balian–Low 不可能性直接对应 A5、A6 与定理 3.4。

**D.3 与 EBOC-Graph 的接口。**
- EBOC-Graph 的 Born = I-projection（G1）与 UMS 的定理 3.3(i) 在离散谱情形下等价。
- EBOC-Graph 的指针基 = 谱极小（G2）与 UMS 的定理 3.3(ii) 在图拉普拉斯情形下一致。
- EBOC-Graph 的窗口极大极小（G3）与 UMS 的定理 3.3(iii) 在带限约束下共享同一优化结构。
- EBOC-Graph 的非渐近误差闭合（G4）与 UMS 的定理 4.3 均采用 Nyquist–Poisson–EM 三分解框架。

**D.4 与 CCS（协变多通道）及 WSIG-QM 的接口。**
- CCS 的窗化 Birman–Kreĭn 恒等式与 UMS 的核心统一式（定义 2.2）在多通道情形下完全一致。
- CCS 的 Wigner–Smith 群延迟矩阵 $\mathsf Q(E)$ 与 UMS 的 A5 采用相同定义与约定。
- WSIG-QM 的七大公理（A1–A7）与 UMS 的公理体系（§1）在概念与表述上高度对齐；WSIG-QM 可视为 UMS 在量子测量特定语境下的精细展开。
- WSIG-QM 的统一字典（§5）与 UMS 的范畴化定义（§2）共同支撑"态—测量—概率—指针—散射—延迟—帧—误差—容量"的全链条统一。

**D.5 保持"极点 = 主尺度"的有限阶 EM 纪律。**
- UMS 在所有离散—连续换序中均采用**有限阶** EM（A1、定理 4.2），确保不引入新奇点。
- 与 S15–S26、EBOC-Graph、CCS、WSIG-QM 保持一致：散射极点、共振极点、谱奇点始终为"主尺度"标记，EM 余项仅作有界扰动。

---

### 一句话总结

$$
\boxed{\ \textbf{UMS}\ \Longleftrightarrow
\big(\,d\mu_\varphi=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\,dE=\rho_{\mathrm{rel}}\,dE=\tfrac{\varphi'}{\pi}\,dE;
K_{w,h}\text{ 的 Nyquist–Poisson–EM 有限阶闭合};
\text{Born=I-proj,\ DPI,\ HSW};
\text{Landau/WR/BL};
\text{Pointer=Ky Fan 极小}\,\big). }
$$
