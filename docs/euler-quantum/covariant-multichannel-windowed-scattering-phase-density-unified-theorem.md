# 协变多通道"窗化散射—相位—密度"统一定理（CCS）

## 摘要（定性）

在 de Branges–Kreĭn 规范系统与多通道散射理论下，建立一个把三类"可观测读数"严密缝合的统一账本：相位导数 $\partial_E\arg\det S$、Wigner–Smith 矩阵迹 $\frac{1}{2\pi}\operatorname{tr}Q$ 与相对谱密度 $\operatorname{tr}(\rho-\rho_0)$。核心结果是**窗化 Birman–Kreĭn 恒等式**及其**非渐近三分解误差闭合**（Poisson 折叠项 + Euler–Maclaurin 余项 + 截断尾项），并在"相位刻度"下给出采样/插值的 Landau 型必要密度、Balian–Low 不可能性、多窗—多通道的广义 Wexler–Raz 双正交与稳定半径；同时给出带限强式 KKT 条件与**最小实验闭环**的可检验判据。该体系全部锚定于公认判据与原始文献。

---

## 0. 设定、记号与规范

### 0.1 规范系统与 Weyl–Titchmarsh

考虑（矩阵/多通道）de Branges–Kreĭn 规范系统

$$
JY'(t,z)=z\,H(t)\,Y(t,z),\qquad
J=\begin{pmatrix}0&-I_n\\ I_n&0\end{pmatrix},\quad H(t)\succeq 0.
$$

其 Weyl–Titchmarsh 函数 $m:\mathbb C_+\to\mathbb C_+$ 属 Herglotz 类，非切边界值满足标准密度公式

$$
\operatorname{tr}\rho(E)=\frac{1}{\pi}\,\Im\operatorname{tr} m(E+i0)\quad\text{(a.e.)}.
$$

这是 de Branges 空间/规范系统与 Herglotz–Nevanlinna 理论的基本词典，见 Remling 与 de Branges 原著。

### 0.2 散射对、谱移与 Wigner–Smith

设 $(H,H_0)$ 为可散射对，且 $(H-i)^{-1}-(H_0-i)^{-1}\in\mathfrak S_1$。令 $S(E)\in U(n)$ 为散射矩阵、$\xi(E)$ 为谱移函数（SSF）。**Birman–Kreĭn 公式**给出

$$
\det S(E)=\exp\!\big(\pm 2\pi i\,\xi(E)\big),\qquad
\xi'(E)=\operatorname{tr}\!\big(\rho(E)-\rho_0(E)\big)\quad\text{(a.e.)},
$$

号记符号（$+$ 或 $-$）随文献约定而异；本文选取具体规范见下。

Wigner–Smith 矩阵定义为

$$
Q(E)=-\,i\,S(E)^\dagger\,\tfrac{dS}{dE}(E),
$$

在**酉散射**时 $Q(E)$ 为 Hermite，且 $\frac{1}{2\pi}\operatorname{tr}Q(E)=\xi'(E)$；存在耗散时需用**复时间延迟**推广（Chen–Anlage–Fyodorov, Phys. Rev. E, 2021），$Q$ 不再必为 Hermite/半正定。

**号记规范（统一取 $\hbar=1$）**：本文固定 **BK 正号**

$$
\det S(E)=\exp\!\big(2\pi i\,\xi(E)\big),\qquad
\xi'(E)=\operatorname{tr}(\rho-\rho_0)(E).
$$

令 **Wigner–Smith** $Q(E)=-\,i\,S(E)^\dagger \tfrac{dS}{dE}(E)$。则在**酉散射**下

$$
\frac{d}{dE}\arg\det S(E)=\operatorname{tr}Q(E),\qquad
\frac{1}{2\pi}\operatorname{tr}Q(E)=\xi'(E)=\operatorname{tr}(\rho-\rho_0)(E).
$$

若改用 **BK 负号** $\det S=e^{-2\pi i\xi}$，上式仅整体改号，等式结构不变。

### 0.3 窗与傅里叶规范

取带限偶窗 $w\in\mathsf{PW}^{\mathrm{even}}_{\Omega}$ 且 $w(0)=1$，缩放 $w_R(E)=w(E/R)$；前端核 $h$ 取 $C_c^m(\mathbb R)$ 或 $W^{2M,1}$（在需要时明确假设）。统一采用

$$
\widehat f(\xi)=\int_{\mathbb R} f(E)e^{-iE\xi}\,dE,\qquad
f(E)=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\xi)e^{iE\xi}\,d\xi.
$$

缩放窗的频域支撑为

$$
\widehat{w_R}(\xi)=R\,\widehat{w}(R\xi),\qquad
\operatorname{supp}\widehat{w_R}\subset\!\big[-\tfrac{\Omega}{R}\,,\,\tfrac{\Omega}{R}\big]
=: [-\Omega_w,\Omega_w].
$$

约定 $w_R^\star(E):=w_R(-E)=w_R(E)$（偶窗），故 $\widehat{w_R^\star}=\widehat{w_R}$。

Poisson 求和（DLMF §1.8(iv)）与 Euler–Maclaurin（DLMF §2.10(i)）公式按 NIST DLMF 规范引用。

---

## 1. 窗化谱差与相位增量

**定义 1（窗化泛函；矩阵/多通道）**

记迹密度差 $\operatorname{tr}(\rho-\rho_0)$ 与散射矩阵 $S(E)$。对给定 $(h,w_R)$ 定义

$$
\mathcal S_{\mathrm{spec}}(h;R)
:=\int_{\mathbb R} h(E)\,\operatorname{tr}(\rho-\rho_0)(E)\,w_R(E)\,dE,
$$

$$
\mathcal S_{\mathrm{scat}}(h;R)
:=\frac{1}{2\pi i}\int_{\mathbb R} h'(E)\,\log\det S(E)\,w_R(E)\,dE,
$$

其中 $\log\det S$ 取沿实轴的连续分支；阈值/共振点按分段与极限理解。因 $h\in C_c^1$（或 $W^{1,1}$）且 $w_R\in \mathrm{PW}\subset L^\infty$（带限 $L^2$ 函数按 Paley–Wiener/Bernstein 不等式天然有界），分部积分的两端边界项为 0。束缚态原子项可按 Lloyd–Kreĭn 正则化并入；束缚能级 $E_b$ 贡献为 $\sum_b h(E_b)w_R(E_b)$ 离散项。

---

## 2. 主定理（CCS）：窗化 Birman–Kreĭn 恒等与非渐近误差闭合

### 定理 A（窗化 CCS 恒等式与三分解）

在 §0 假设与带限窗设定下，并假设 $h\in C_c^1(\mathbb R)$（或 $W^{1,1}$）、$w_R\in L^\infty$、$(H-i)^{-1}-(H_0-i)^{-1}\in\mathfrak S_1$，则由 SSF/Lifshitz–Kreĭn 理论 $\int_{\mathbb R}\!|\operatorname{tr}(\rho-\rho_0)(E)|\,dE<\infty$，积分绝对收敛并有

$$
\boxed{\ \mathcal S_{\mathrm{spec}}(h;R)=\mathcal S_{\mathrm{scat}}(h;R)+\mathcal E_R\ },
$$

且几乎处处

$$
\boxed{\
\frac{d}{dE}\arg\det S(E)=2\pi\,\xi'(E)=2\pi\,\operatorname{tr}\big(\rho-\rho_0\big)(E)\ }.
$$

其中误差 $\mathcal E_R$ 具有**Poisson–EM–Tail 三分解**：

$$
\boxed{\ \mathcal E_R=\mathcal E_{\mathrm{alias}}+\mathcal E_{\mathrm{EM}}+\mathcal E_{\mathrm{tail}}.\ }
$$

**证明要点（提纲）**

(i) 谱侧：由 Herglotz 表示与非切边界值 $\operatorname{tr}\rho=\pi^{-1}\Im\operatorname{tr} m(\cdot+i0)$ 得 $\mathcal S_{\mathrm{spec}}$ 的 Stieltjes 形式。

(ii) 散射侧：由 Birman–Kreĭn $\det S=\exp(2\pi i\xi)$ 与 $\xi'=\operatorname{tr}(\rho-\rho_0)$ 对 $\int h'(E)\log\det S\,w_R$ 作分部；因 $h\in C_c^1$（或 $W^{1,1}$）且 $w_R\in L^\infty$，两端边界项为零，匹配即得主恒等式。

(iii) 误差闭合：等距采样 + Poisson 求和（DLMF §1.8(iv)）给出 alias 折叠项；有限阶 EM 公式（DLMF §2.10(i)）给出和–积之差；窗外截断给出尾项；带限与 Nyquist 条件下 $\mathcal E_{\mathrm{alias}}=0$。∎

### 命题 A.1（alias 消失的带宽判据）

本命题以下取 $h\in \mathrm{PW}_{\Omega_h}$（$\operatorname{supp}\widehat h\subset[-\Omega_h,\Omega_h]$）。若 $h\notin \mathrm{PW}$，则 $\mathcal E_{\mathrm{alias}}$ 仅能以 $\int_{|\xi|>\Omega_h}|\widehat h(\xi)|\,d\xi$ 计的尾项给出上界，不保证为 0（DLMF §1.8(iv)）。

**被观测量（前端滤波后）**：设 $g(E)=\operatorname{tr}(\rho-\rho_0)(E)$，$g_h:=h\!\star\!g$。离散采样与 Poisson-alias 分析针对

$$
F(E):=w_R(E)\,g_h(E)=w_R(E)\,(h\!\star\!g)(E).
$$

（连续积分的理论恒等式仍以 $h\cdot g$ 记，滤波仅作用于采样与 alias 判据。）若 $\operatorname{supp}\widehat{w_R}\subset[-\Omega_w,\Omega_w]$、$\operatorname{supp}\widehat h\subset[-\Omega_h,\Omega_h]$，则因 $\operatorname{supp}(\widehat h\cdot \widehat g)\subset\operatorname{supp}\widehat h\cap\operatorname{supp}\widehat g$，被观测量的频域支集满足

$$
\operatorname{supp}\widehat F
=\operatorname{supp}\!\big(\widehat{w_R}*\big(\widehat h\cdot \widehat g\big)\big)
\subset[-(\Omega_w+\Omega_h)\,,\,\Omega_w+\Omega_h].
$$

当采样间隔 $\Delta$ 满足

$$
\boxed{\ \Delta<\frac{\pi}{\Omega_w+\Omega_h}\ },
$$

（或"$\le$"且端点强零）则 $\mathcal E_{\mathrm{alias}}=0$。该 Nyquist 条件与 Poisson 折叠阈值 $|\xi|=\pi/\Delta$ 一致（DLMF §1.8(iv)）。

### 命题 A.2（EM 余项与尾项上界）

若 $F\in C^{2p}([a,b])$，则至 $2p$ 阶 EM 公式给出

$$
\bigl|\mathcal E_{\mathrm{EM}}\bigr|
\le C_{2p}\,\sup_{x\in[a,b]}\bigl|F^{(2p)}(x)\bigr|,\qquad
\bigl|\mathcal E_{\mathrm{tail}}\bigr|
\le \|h\|_{L^1}\,\|w_R\mathbf 1_{|E|>T}\|_{L^\infty}\,\|\operatorname{tr}(\rho-\rho_0)\|_{L^1(|E|>T)}.
$$

其中 $C_{2p}$ 由 Bernoulli 数给定（DLMF §2.10.E1）；Bernoulli 多项式与常数均取自 DLMF。

---

## 3. 相位—密度等价与 Wigner–Smith（矩阵/多通道）

### 定理 B（Weyl–de Branges 密度等价）

规范系统的 Weyl 函数满足

$$
\boxed{\ \operatorname{tr}\rho(E)=\frac{1}{\pi}\,\Im\operatorname{tr} m(E+i0)\ \text{(a.e.)}\ }.
$$

（Herglotz 表示 + 非切边界值；矩阵情形取迹。）

### 定理 C（Friedel/WS 链：相位导数 = 相对密度）

在 §0.2 条件与本文号记规范下，几乎处处

$$
\boxed{
\frac{1}{2\pi}\operatorname{tr}Q(E)=\xi'(E)=\operatorname{tr}\big(\rho-\rho_0\big)(E),\qquad
\partial_E\arg\det S(E)=\operatorname{tr}Q(E)=2\pi\,\operatorname{tr}\big(\rho-\rho_0\big)(E).
}
$$

注：酉散射下 $Q$ 为 Hermite，但不保证半正定；有耗散时需用复时间延迟推广（Chen–Anlage–Fyodorov, Phys. Rev. E, 2021），$Q$ 不再必为 Hermite/半正定。

---

## 4. 采样—插值—帧障碍：以"相位密度"计量

以**相位刻度**度量区间 $I$：

$$
L_\varphi(I):=\int_I \varphi'(E)\,dE=\pi\int_I \operatorname{tr}(\rho-\rho_0)(E)\,dE.
$$

**相位与正性假设**：定义 $\varphi(E)=\tfrac12\arg\det S(E)$，则 $\varphi'(E)=\pi\,\operatorname{tr}(\rho-\rho_0)(E)$。假设在所考察区间 $I$ 上 $\varphi'(E)\ge c_0\ge0$ 几乎处处；据此 $u=\varphi(E)/\pi$ 单调，Landau 阈值常数为 1（$\mathrm{PW}_\pi$ 模型）。

### 定理 D（Landau 必要密度：相位刻度版）

设 $\Lambda\subset I$。若 $\Lambda$ 为采样序列，则

$$
\underline D_\varphi(\Lambda)
:=\liminf_{r\to\infty}\inf_{\substack{J\subset I\\ L_\varphi(J)\ge r}}
\frac{\#(\Lambda\cap J)}{L_\varphi(J)}\ \ge\ 1;
$$

若 $\Lambda$ 为插值序列，则

$$
\overline D_\varphi(\Lambda)
:=\limsup_{r\to\infty}\sup_{\substack{J\subset I\\ L_\varphi(J)\ge r}}
\frac{\#(\Lambda\cap J)}{L_\varphi(J)}\ \le\ 1.
$$

这是 Landau 定理在相位坐标下的直推，其中"1"对应单位带宽。

### 推论 D.1（Balian–Low 不可能性与多窗必要性）

临界密度下（等价于 Gabor 条件 $ab=1$ 或 $\underline D_\varphi=1$）若要求单窗良好相位—频率局域，则不能形成 Riesz 基/紧框架；稳定采样需**多窗/超采样**或放宽局域性。该版本为**帧/基不可兼得**型 Balian–Low 定理（参见 Encyclopedia of Math；Heil–Powell 综述）。

---

## 5. 多窗—多通道扩展与稳定半径

### 结构定理 E（多窗帧与广义 Wexler–Raz）

在 $\mathsf{PW}^{\mathrm{even}}_{\Omega}$ 上取 $K$ 个窗 $W=(w^{(1)},\dots,w^{(K)})$。对应的分析/合成算子诱导 Gram 矩阵 $G$。存在对偶窗族 $\widetilde W$ 使得重构稳定，且满足广义 Wexler–Raz 双正交；当 $K=1$ 且仅施加带限与区间能量集中约束时，频域收敛到 Slepian–Pollak（PSWF）情形。

**稳定半径（奇性不增）**

**条带全纯前提（沿用 §2）**：由 $(H-i)^{-1}-(H_0-i)^{-1}\in\mathfrak S_1$ 得 $g(E)=\operatorname{tr}(\rho-\rho_0)(E)\in L^1(\mathbb R)$。又因 $h,w_R\in \mathrm{PW}$ 为指数型整函数，定义

$$
g_h(z):=\int_{\mathbb R}h(z-E')\,g(E')\,dE'
$$

于任意有界条带内收敛并给出 $g_h$ 的全纯延拓，$F(z)=w_R(z)\,g_h(z)$ 亦全纯；因此下述 **Rouché 型稳定半径** 适用于任意有界条带域 $D$。

在**有限阶** EM 与 Nyquist–Poisson–EM 纪律下，窗化与近似不引入新奇点，极阶不升；对被观测函数 $F$ 与扰动 $\delta F$，若 $|\delta F|_{L^\infty(\partial D)}<\min_{\partial D}|F|$，则 $D$ 内零点个数与位置仅作 Rouché 型小偏移，据此得到零/极点的**稳定半径**（可用于相位跃迁与谱线定位的鲁棒性评估）。

---

## 6. 窗/核优化的带限强式（KKT）

考虑目标"**最小化三分解误差** + 结构正则"的凸/变分问题。其频域必要条件（强式）具有**带限投影 ×（多项式乘子 + 卷积核）= 常数**的范式，例如

$$
\chi_{[-\Omega/R,\;\Omega/R]}(\xi)\!\left(
2\sum_{j=1}^{M-1}\gamma_j\,\xi^{4j}\,\widehat{w_R}(\xi)
+\frac{\lambda}{2\pi}\ \big(\widehat{\mathbf 1_{|E|>T}}\ast \widehat{w_R}\big)(\xi)
\right)=\eta\ \chi_{[-\Omega/R,\;\Omega/R]}(\xi),
$$

其中 $\eta$ 为约束 $w_R(0)=1$ 的乘子；傅里叶规范中的 $1/(2\pi)$ 因子须与 §0.3 保持一致。该式与广义 Wexler–Raz/帧定理接口良好，可作实际求解与正则化设计的 Euler–Lagrange 形式。

---

## 7. 可检验预测与最小实验闭环

**观测量（同步测量）**

（i）$\delta'(E)=\partial_E\arg\det S(E)$：由多端口 S 参数频扫与相位展开获得；

（ii）LDOS：$\mathrm{LDOS}_i(E)=-\frac{1}{\pi}\Im G^r_{ii}(E)$，由隧穿谱或场点读数获得（电/声/电磁体系适用）。此式为标准局部态密度公式，在多物理体系广泛使用；电磁/声学情形需按场型/规范做相应解释。LDOS 与散射矩阵/相位的关系可由 Green 函数或 S 参数两路核验（参见 Phys. Rev. B **65**, 115307 (2002)）。

**采样管线约定**：进行等距采样与 Poisson-alias 检验时，先构造 $g_h:=h\!\star\!\mathrm{LDOS}_{\mathrm{rel}}$，实际被采样函数为 $F=w_R\cdot g_h$。

**定义（相对 LDOS 的迹化/总和）**：设观测点（或通道）集合为 $\{x_i\}_{i=1}^N$。定义

$$
\mathrm{LDOS}_{\mathrm{rel}}(E)\ :=\ \sum_{i=1}^N\Big(\mathrm{LDOS}_i(E)-\mathrm{LDOS}_{0,i}(E)\Big),
$$

其中 $\mathrm{LDOS}_i(E)=-\tfrac{1}{\pi}\Im G^r_{ii}(E)$。在连续模型下等价地记

$$
\mathrm{LDOS}_{\mathrm{rel}}(E)\ :=\ -\tfrac{1}{\pi}\Im\,\operatorname{tr}\!\Big(G^r(E)-G_0^r(E)\Big).
$$

据此有 $\mathrm{LDOS}_{\mathrm{rel}}(E)=\operatorname{tr}\big(\rho(E)-\rho_0(E)\big)$，从而与定理 A 中的谱侧 integrand 完全一致。

**主等式验证（单/多通道）**

$$
\int h(E)\,\mathrm{LDOS}_{\mathrm{rel}}(E)\,w_R(E)\,dE
=\frac{1}{2\pi}\int h'(E)\,\arg\det S(E)\,w_R(E)\,dE\ +\ \mathcal E_R,
$$

并在（a）亚 Nyquist（有 alias）与（b）满足 Nyquist（无 alias）两端对比三分解误差的关断/收敛；"Wigner–Smith 均时延 = 开放体系 DOS"提供独立交叉核验。

**采样—帧判据（相位刻度）**

按定理 D 估计相位密度下界与插值上界：在临界密度验证单窗失败，改用多窗/超采样后恢复稳定（推论 D.1 与定理 E）。

---

## 8. 与前序理论的接口

### 8.1 与 Euler 理论系列（S15–S26）的联结

**与 S15（Weyl–Heisenberg）**：
- CCS 的相位刻度 $L_\varphi(I)=\pi\int_I\operatorname{tr}(\rho-\rho_0)$ 对应 S15 的 Weyl–Heisenberg 酉表示；
- 定理 D 的临界密度对应 S15 的格点面积约束。

**与 S16（de Branges 规范系统）**：
- 定理 B 的 Weyl 密度公式 $\operatorname{tr}\rho=\pi^{-1}\Im\operatorname{tr} m$ 即 S16 的规范系统基本词典；
- §0.1 的 Hamiltonian 形式 $JY'=zHY$ 对应 S16 的辛结构。

**与 S17（散射—酉性）**：
- 定理 A 的 Birman–Kreĭn 公式 $\det S=\exp(2\pi i\xi)$ 与 S17 的散射相位—行列式公式一致；
- 定理 C 的相位导数 $\partial_E\arg\det S=2\pi\operatorname{tr}(\rho-\rho_0)$ 对应 S17 的散射延迟时间。

**与 S18（窗不等式）**：
- 命题 A.1 的 Nyquist 条件 $\Delta\le\pi/(\Omega_w+\Omega_h)$ 即 S18 的带限乘积 alias 条件；
- 定理 A 的三分解误差对应 S18 的 Nyquist–Poisson–EM 框架。

**与 S19（光谱图）**：
- 相位密度刻度对应 S19 的图谱局部密度；
- 定理 D 的 Landau 型下界对应 S19 的非回溯算子谱分布。

**与 S20（BN–Bregman）**：
- §6 的 KKT 强式对应 S20 的 Bregman 几何最优性条件；
- 窗化泛函的变分问题对应 S20 的 I-投影框架。

**与 S21（连续谱阈值与奇性稳定）**：
- 定理 A 的相位导数 $\partial_E\arg\det S=2\pi\operatorname{tr}(\rho-\rho_0)$ 即 S21 的核心恒等式；
- 命题 A.2 的 EM 余项对应 S21 的有限阶 EM 奇性保持。

**与 S22（窗/核最优）**：
- §6 的带限强式 KKT 对应 S22 的频域核型 Euler–Lagrange 方程；
- 命题 A.1 的 Nyquist 条件对应 S22 的带限偶窗变分原理。

**与 S23（多窗协同）**：
- 定理 E 的广义 Wexler–Raz 对应 S23 的多窗双正交关系；
- 多通道扩展对应 S23 的多窗 Gram 矩阵框架。

**与 S24（紧框架）**：
- 定理 D 的采样/插值密度对应 S24 的帧界判据；
- 推论 D.1 的临界密度对应 S24 的 Parseval 紧帧条件。

**与 S25（非平稳框架）**：
- 定理 E 的多窗帧对应 S25 的分块非平稳系统；
- 命题 A.1 的 alias 消失对应 S25 的"无混叠"条件。

**与 S26（相位密度与稳定性）**：
- 定理 D 的相位密度刻度 $L_\varphi$ 即 S26 的 Beurling 密度 $D_\varphi^\pm$；
- 推论 D.1 的 Balian–Low 障碍即 S26 定理 5.1；
- 稳定半径对应 S26 定理 4.1 的 Kadec–Bari 型小扰动稳定。

### 8.2 与量子测量理论的联结

**与相位导数窗口化读数理论**：
- 定理 A 的窗化 Birman–Kreĭn 恒等与相位导数窗口化读数的 Nyquist–Poisson–EM 三分解一致；
- §7 的 LDOS 读数对应窗口化测量的 Born 概率。

**与统一测量理论**：
- 定理 C 的相位—密度—延迟三重等价对应统一测量的"Born = 最小 KL，Pointer = 最小能量"；
- §6 的 KKT 强式对应窗/核优化的变分原理。

**与 Trinity 定理**：
- CCS 的三重等价（相位导数 ↔ Wigner–Smith ↔ 相对密度）对应 Trinity 定理的三位一体；
- 定理 A 的非渐近误差闭合对应 Trinity 定理的误差分解框架。

### 8.3 与 EBOC-Graph 的联结

- §7 的可检验预测对应 EBOC-Graph 的"Born = I-投影，Pointer = 光谱极小，Windows = 极大极小"；
- 定理 D 的采样密度下界对应 EBOC-Graph 的资源下界 $N=\Omega(r^{-2})$；
- 窗化散射—相位—密度恒等式为 EBOC-Graph 提供图谱实现的连续谱对应。

---

## 9. 讨论与展望

* **相位导数 = 密度（S21）**：本文以 $\partial_E\arg\det S=2\pi\,\operatorname{tr}(\rho-\rho_0)$ 与 $\frac{1}{\pi}\Im m$ 的 Weyl 边界值为桥，统一"相位—密度"两端。
* **三分解误差闭合（S18）**：Poisson/EM/Tail 的非渐近误差模板与 Nyquist 判据对齐，实现"何时 alias 为零、何时只剩 EM/tail"。
* **窗/核最优（S22）与多窗帧（S23）**：频域强式/KKT、广义 Wexler–Raz 与 PSWF 极限回收在本文统一框架中直接调用。
* **读数三位一体（EBOC–Graph）**：在工程侧，"$\mathrm{Born}=$KL 投影、$\mathrm{Pointer}=$谱极小、$\mathrm{Windows}=$极大极小最优"与本文 CCS 的窗化散射—相位—密度恒等式自然拼合成可测—可控闭环。

---

## 参考文献（精选与可核对条目）

1. Louis de Branges, *Hilbert Spaces of Entire Functions*, Prentice-Hall, 1968（HB/EB 空间原典）。
2. Christian Remling, *Spectral Theory of Canonical Systems*, De Gruyter, 2018（规范系统现代教科书）。
3. A. Strohmaier 等, *The Birman–Kreĭn formula for differential forms and electromagnetic scattering*, Bull. London Math. Soc., 2023（BK 现代处理；含号记说明）。
4. D. Borthwick, *Birman–Kreĭn and scattering phase*, arXiv:2110.06370（BK 与相位/波迹联系）。
5. A. Grabsch, D.V. Savin, C. Texier, *Wigner–Smith time-delay matrix in chaotic cavities with non-ideal contacts*, Phys. Rev. E, 2018（WS 矩阵综述/统计与 DOS 关系）。
6. NIST DLMF, §1.8(iv)（Poisson）、§2.10（Euler–Maclaurin）。
7. H. J. Landau, *Necessary density conditions for sampling and interpolation of certain entire functions*, Acta Math., 1967（采样/插值必要密度）。
8. Encyclopedia of Mathematics, *Balian–Low theorem*；C. Heil, *History and evolution of the density theorem*, 2012（B–L 不可能性与 Gabor 密度）。
9. D. Slepian, H. O. Pollak, *Prolate Spheroidal Wave Functions, Fourier Analysis and Uncertainty*, Bell Syst. Tech. J., 1961（PSWF；能量集中与带限极值）。
10. A. Asatryan 等, *Two-dimensional Green's function and local density of states in photonic crystals*, Phys. Rev. E, 2001（$\mathrm{LDOS}=-(\pi)^{-1}\Im G^r_{ii}$ 实例）。
11. L. Chen, A. M. Fyodorov, S. M. Anlage, *Generalization of Wigner time delay to subunitary scattering systems*, Phys. Rev. E **103**, L050203 (2021)（耗散/非酉体系之复时间延迟）。
12. I. Daubechies, *Gabor Time-Frequency Lattices and the Wexler–Raz Identity*, J. Fourier Anal. Appl., 1995（广义 Wexler–Raz）。
13. Y. V. Fyodorov, D. V. Savin, *Resonance scattering of waves in chaotic systems*, in *The Oxford Handbook of Random Matrix Theory* (2011)（DOS–散射矩阵关系综述）。
14. T. Kottos, U. Smilansky, *Quantum Chaos on Graphs*, Phys. Rev. Lett. **79**, 4794 (1997)；A. A. Clerk 等, *Local density of states and scattering matrix in quasi-one-dimensional systems*, Phys. Rev. B **65**, 115307 (2002)（LDOS 与 S 矩阵/相位联系）。

---

## 结论

本文给出一个**可直接验证**的统一框架：

$$
\boxed{\ \partial_E\arg\det S(E)\ \Longleftrightarrow\ \frac{1}{2\pi}\operatorname{tr}Q(E)\ \Longleftrightarrow\ \operatorname{tr}\big(\rho(E)-\rho_0(E)\big)\ },
$$

并在**带限窗**与**Poisson–EM 三分解**的非渐近纪律下给出误差闭合、相位刻度的 Landau 必要密度、Balian–Low 不可能性、多窗—多通道广义 Wexler–Raz 与稳定半径，以及面向实验的最小闭环判据。其每一步均有公认判据作背书，亦与本项目 S15–S26 的 Euler 理论系列、量子测量理论（相位导数窗口化读数、统一测量、Trinity 定理）以及 EBOC-Graph 的工程—物理—数学三端接口严丝合缝。该框架将散射理论、规范系统、相位密度与窗化测量统一到协变多通道框架，为实验可检验预测与理论可复核判据提供完整的数学脊梁。
