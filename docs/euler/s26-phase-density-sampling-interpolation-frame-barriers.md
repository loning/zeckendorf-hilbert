# S26. 相位密度与稳定性：de Branges–Mellin 框架下的采样—插值—帧障碍

**—— 相位导数测度、Landau 型必要/充分准则、Balian–Low 类不可能性与小扰动稳定**

## 摘要（定性）

在 de Branges–Mellin 框架中，以相位导数 $\varphi'(x)$ 诱导的"相位密度"作为几何刻度，建立采样与插值序列的必要—充分密度准则；证明对由相位网格作小相位扰动得到的序列存在 Riesz 基/框架的稳定半径；在 Weyl–Heisenberg（Mellin）酉系统的格点情形，给出 Balian–Low 类不可能性：临界密度下紧局域窗不能生成 Riesz 基/紧框架。上述结论在"有限阶" Euler–Maclaurin（EM）与 Nyquist–Poisson–EM 三分解纪律下保持工作条带内的奇性集合不增与极阶不升，并与窗/核最优化的带限投影—卷积结构协同。全文定性陈述，避免对数值常数的最优化诉求。

---

## 0. 设定与相位密度

设 $E$ 为 Hermite–Biehler（HB）整函数，$\mathcal H(E)$ 为对应的 de Branges 空间。写

$$
E(x)=|E(x)|\,e^{-i\varphi(x)},\qquad
E^\sharp(z):=\overline{E(\bar z)},\qquad
U(x):=\frac{E^\sharp(x)}{E(x)}=e^{2i\varphi(x)}\ \ \text{(a.e. }x\in\mathbb R).
$$

Weyl–Titchmarsh 函数 $m$ 的边界虚部与谱密度 $\rho$ 满足

$$
\varphi'(x)=\Im m(x+i0)=\pi\,\rho(x),\qquad
\varphi'(x)=\frac{\pi\,K(x,x)}{|E(x)|^2}>0\ \ \text{(a.e.)},
$$

其中 $K$ 为 $\mathcal H(E)$ 的再生核。以上同一式统一了"相位导数—谱密度—核对角"的刻度。

**相位密度测度与 Beurling 密度.** 对区间 $I\subset\mathbb R$，定义

$$
\Phi(I):=\int_I \varphi'(x)\,dx=\pi\int_I \rho(x)\,dx,
$$

并对离散序列 $\Lambda=\{x_n\}\subset\mathbb R$ 定义

$$
D_\varphi^-(\Lambda):=\liminf_{R\to\infty}\ \inf_{x_0\in\mathbb R}\
\frac{\#\big(\Lambda\cap[x_0-R,x_0+R]\big)}{\Phi([x_0-R,x_0+R])/\pi},
$$

$$
D_\varphi^+(\Lambda):=\limsup_{R\to\infty}\ \sup_{x_0\in\mathbb R}\
\frac{\#\big(\Lambda\cap[x_0-R,x_0+R]\big)}{\Phi([x_0-R,x_0+R])/\pi}.
$$

当 $\varphi'\equiv T$（Paley–Wiener 情形）时，$D_\varphi^\pm$ 退化为经典 Beurling 密度与带宽 $T$ 的比值，从而与 Landau 密度阈值一致。

**窗与换序纪律.** 全文取非负偶窗 $w_R$（紧支或指数衰减，且 $\|w_R\|_\infty\le 1$），仅用**有限阶** EM 与 Nyquist–Poisson–EM 的三分解进行换序与局域化。由此 $M_{w_R}\ge0$ 且 $\operatorname{Tr}(M_{w_R}|_{\mathcal H(E)})<\infty$，换序所致误差层为整/全纯并可统一控制。

默认 $\varphi'(x)\,dx$ 为 doubling 测度（等价于底层模型空间由 one-component 内函数生成），据此可得 Landau 型必要/充分的相位密度刻度。

---

## 1. 采样与相位密度：Landau 型必要条件

记标准化再生核 $\kappa_x:=K(\cdot,x)/\sqrt{K(x,x)}$。称 $\Lambda$ 为**采样序列**，若存在常数 $A,B>0$ 使

$$
A\,\|F\|_{\mathcal H(E)}^2\ \le\ \sum_{x_n\in\Lambda}\frac{|F(x_n)|^2}{K(x_n,x_n)}\ \le\ B\,\|F\|_{\mathcal H(E)}^2,
\qquad \forall\,F\in\mathcal H(E).
$$

以下均取 $w_R\ge0$ 为紧支或快速衰减窗，并满足 $\int_{\mathbb R}w_R(x)\,\frac{K(x,x)}{|E(x)|^{2}}\,dx=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx<\infty$，从而 $M_{w_R}|_{\mathcal H(E)}$ 为迹类。此处 $M_{w_R}$ 记乘子在 $\mathcal H(E)$ 上的压缩（Toeplitz）算子 $P_{\mathcal H(E)}M_{w_R}P_{\mathcal H(E)}$。

### 引理 1.1（窗化迹恒等）

设 $M_{w_R}$ 为上述压缩乘子算子，则

$$
\operatorname{Tr}\!\left(M_{w_R}\big|_{\mathcal H(E)}\right)
=\int_{\mathbb R} w_R(x)\,\frac{K(x,x)}{|E(x)|^{2}}\,dx
=\frac{1}{\pi}\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx.
$$

*证明.* 取任一正交基 $\{e_n\}$，由 $\langle f,g\rangle_{\mathcal H(E)}=\int f\bar g\,|E|^{-2}dx$ 和再生核恒等式 $\sum_n |e_n(x)|^2=K(x,x)$ 得 $\operatorname{Tr}(M_{w_R})=\int w_R \sum_n|e_n|^2 |E|^{-2}dx$，再用 $K(x,x)=\frac{|E(x)|^2}{\pi}\varphi'(x)$ 即得。$\square$

**注记.** 对任意有界乘子 $M_{w}$，函数 $\widetilde w(x):=\langle M_{w}\kappa_x,\kappa_x\rangle$ 为 $w$ 的 Berezin 变换；一般有 $\widetilde w(x)\neq w(x)$。

### 定理 1.2（采样的相位密度下界）

若 $\Lambda$ 为采样序列，则 $D_\varphi^-(\Lambda)\ge 1$。

*证明（修订版）.* 设 $T_\Lambda=\sum_{x_n}|\kappa_{x_n}\rangle\langle\kappa_{x_n}|$，采样下界等价于 $A I\le T_\Lambda$。于是

$$
\operatorname{Tr}(M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2})
\ge A\,\operatorname{Tr}(M_{w_R})
=\frac{A}{\pi}\int_{\mathbb R} w_R\,\varphi'(x)\,dx.
$$

另一方面

$$
\operatorname{Tr}(M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2})
=\sum_{x_n}\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle.
$$

取单位质量的平移—缩放窗 $w_R$ 并令 $R\to\infty$，在相位导数 $\varphi'(x)\,dx$ 为 doubling 的假设下，引用 Marzo–Nitzan–Olsen 的 Landau 型定理，得

$$
\#(\Lambda\cap I)\ \ge\ \frac{1}{\pi}\int_I \varphi'(x)\,dx+o(\Phi(I)),
$$

故 $D_\varphi^-(\Lambda)\ge 1$。$\square$

---

## 2. Riesz 序列与相位密度：插值的上界

称 $\Lambda$ 为（标准化核）**Riesz 序列**，若 $\{\kappa_{x_n}\}_{x_n\in\Lambda}$ 在 $\mathcal H(E)$ 内为 Riesz 系列，即存在 $A',B'>0$ 使

$$
A'\sum |c_n|^2\ \le\ \left\|\sum c_n\,\kappa_{x_n}\right\|_{\mathcal H(E)}^2\ \le\ B'\sum |c_n|^2.
$$

记 $\Pi_\Lambda$ 为 $\operatorname{span}\{\kappa_{x_n}\}$ 的正交投影。

### 定理 2.1（插值的相位密度上界）

若 $\Lambda$ 为 Riesz 序列（因而为插值序列），则 $D_\varphi^+(\Lambda)\le 1$。

*证明（修订版）.* Riesz 性给出 $A'\Pi_\Lambda\le T_\Lambda\le B'\Pi_\Lambda$。于是

$$
\sum_{x_n}\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\rangle
=\operatorname{Tr}(M_{w_R}^{1/2}T_\Lambda M_{w_R}^{1/2})
\le B'\,\operatorname{Tr}(M_{w_R}^{1/2}\Pi_\Lambda M_{w_R}^{1/2})
\le B'\,\operatorname{Tr}(M_{w_R}).
$$

配合引理 1.1 与 Marzo–Nitzan–Olsen 的插值密度结论可得

$$
\#(\Lambda\cap I)\ \le\ \frac{1}{\pi}\int_I \varphi'(x)\,dx+o(\Phi(I)),
$$

即 $D_\varphi^+(\Lambda)\le 1$。$\square$

---

## 3. 相位网格与 Clark 基：充分性模板

对任意 $\theta\in\mathbb R$，定义"相位网格"

$$
X_\theta:=\{x\in\mathbb R:\ U(x)=e^{2i\theta}\}=\{x:\ \varphi(x)=\theta\ \ (\mathrm{mod}\ \pi)\}.
$$

在 HB/有界型与标准归一下，$\{\kappa_x\}_{x\in X_\theta}$ 构成 $\mathcal H(E)$ 的 Clark 基或 Riesz 基（依空间结构而定），且

$$
D_\varphi^\pm(X_\theta)=1.
$$

说明：在相应模型空间 $K_\Theta$（$\Theta=E^\sharp/E$ 为亚纯内函数）中，$\{k_x\}_{x\in X_\theta}$（适当归一）为正交核基，除至多一个使 $\Theta-e^{i\theta}\in L^2(\mathbb R)$ 的角度 $\theta$ 外；回推到 $\mathcal H(E)$ 得到上述模板与相位密度一致性。

---

## 4. 小扰动稳定与 Kadec 型定理

设 $\{x_n^{(0)}\}$ 为某 $\theta$ 的相位网格的递增枚举（$\varphi(x_n^{(0)})=\theta+n\pi$），令 $\Lambda=\{x_n\}$ 与之逐点对应，并满足

$$
\sup_n\big|\varphi(x_n)-\varphi(x_n^{(0)})\big|\ \le\ \delta,\qquad
\inf_{m\ne n}|\varphi(x_n)-\varphi(x_m)|\ge \Delta_\varphi>0.
$$

### 定理 4.1（Kadec–Bari 型稳定）

存在 $\delta_0>0$（在 Paley–Wiener 情形可取 $\delta_0=\pi/4$ 的相位阈值；一般 de Branges 空间中 $\delta_0$ 依赖于相位加倍/一分量性常数）。若上式中 $\delta<\delta_0$，则 $\{\kappa_{x_n}\}$ 与 $\{\kappa_{x_n^{(0)}}\}$ 等价，因而为 Riesz 基；框界常数仅依赖于 $\delta$ 与 $\Delta_\varphi$。

*证明.* 以 $\varphi$ 为坐标（将自变量由 $x$ 推前至相位轴）考察 Gram 矩阵 $G=(\langle \kappa_{x_m},\kappa_{x_n}\rangle)$。当 $\delta=0$ 时得到 Clark 构型的对角情形；小相位偏差使 $G$ 成为"对角 + 小范数偏差"的可逆紧扰动。由 Bari 定理与 Neumann 级数即得。窗化仅引入整/全纯误差层，不影响谱半径与可逆性。$\square$

---

## 5. Weyl–Mellin 格点与 Balian–Low 类不可能性

在带权 Mellin–Hilbert 空间 $\mathcal H_a=L^2(\mathbb R_+,x^{a-1}dx)$ 上，考虑 Weyl–Heisenberg 酉对

$$
(U_\tau f)(x)=x^{i\tau}f(x),\qquad (V_\sigma f)(x)=e^{\sigma a/2}f(e^\sigma x),
$$

满足 $V_\sigma U_\tau=e^{i\tau\sigma}U_\tau V_\sigma$。其 Stone 生成元

$$
A=\log x,\qquad B=-i\left(x\partial_x+\tfrac a2\right)
$$

在共同核心上满足 $[A,B]=iI$。取对数坐标 $t=\log x$ 的等距变换 $(\mathcal U f)(t)=e^{a t/2} f(e^t)$，则 $(U_\tau,V_\sigma)$ 化为 $\mathbb R$ 上的调制 $e^{i\tau t}$ 与平移 $T_\sigma$。临界密度对应 $\tau_0\sigma_0=2\pi$（若改用 $e^{2\pi i b t}$ 频率记号，则阈值写作 $ab=1$）。

给定格点 $\Gamma=\{(\tau_m,\sigma_n)=(m\tau_0,n\sigma_0)\}$，记

$$
\mathcal G(g;\Gamma):=\{\,U_{m\tau_0}V_{n\sigma_0}g:\ (m,n)\in\mathbb Z^2\,\}.
$$

### 定理 5.1（Balian–Low 类不可能性：临界密度）

若 $\tau_0\sigma_0=2\pi$ 且 $\mathcal G(g;\Gamma)$ 为 Riesz 基或紧框架，则必有

$$
A g\notin L^2(\mathbb R_+,x^{a-1}dx)\quad\text{或}\quad B g\notin L^2(\mathbb R_+,x^{a-1}dx).
$$

*证明思路.* 在对数模型中等价于 $\mathbb R$ 上的调制—平移临界情形。若同时 $Ag,Bg\in L^2$（分别对应时域与"频域"二阶矩有限），则可构造二阶矩有限的双正交对；结合 Wexler–Raz 双正交关系与 CCR，得到与"每个基本胞元一自由度"的密度事实矛盾，故断言成立。非临界密度时：$\tau_0\sigma_0<2\pi$（过采样）可构造紧框架；$\tau_0\sigma_0>2\pi$（欠采样）则不存在 Riesz 基，阈值与 §1–§2 的相位密度一致。$\square$

---

## 6. 窗化与奇性保持

在**有限阶** EM 与 Nyquist–Poisson–EM 三分解的窗化实现下，仅引入"别名/Bernoulli 层/截断"三类可控误差；带限偶投影与卷积核的频域强式保证：工作条带内不引入新奇点且极阶不升。由此，§1–§2 的密度估计与 §4 的可逆性判据在窗化实现中稳定成立。

---

## 7. 与前序理论的接口

### 7.1 S15：Weyl–Heisenberg 协变与窗函数诱导的内积

- S26 的 §5 采用 $(U_\tau,V_\sigma)$ 的 Weyl 关系与 $[A,B]=iI$，直接推广 S15 的酉表示框架；
- Balian–Low 不可能性对应 S15 中紧局域窗在临界密度下的 Riesz 基障碍。

### 7.2 S16：de Branges 规范系统与辛结构

- S26 的核心刻度 $\varphi'(x)=\pi K(x,x)/|E(x)|^2$ 即 S16 的相位—再生核公式；
- Clark 基模板对应 S16 中辛流沿相位坐标的自然采样。

### 7.3 S17：散射—酉性与相位—行列式公式

- 相位密度 $\rho(x)=\pi^{-1}\varphi'(x)$ 与 S17 的谱密度 $\rho_{\mathrm{rel}}(E)$ 联结；
- §3 的相位网格 $X_\theta$ 对应 S17 中散射相位的等间隔采样。

### 7.4 S18：窗不等式与半范数测度化

- 定理 1.2 与 2.1 的密度估计采用 S18 的窗化迹不等式框架；
- 引理 1.1 的窗化迹恒等对应 S18 的半范数测度化。

### 7.5 S19：光谱图与非回溯—邻接关系

- 离散序列的 Beurling 密度对应 S19 中图谱的局部密度；
- Riesz 序列的框界对应 S19 的非回溯算子谱分布。

### 7.6 S20：BN 投影、KL 代价与 Bregman 敏感度

- §4 的小扰动稳定性分析可调用 S20 的 Bregman 几何框架；
- Gram 矩阵的可逆性对应 S20 的 Hessian $\nabla^2\Lambda$ 的正定性。

### 7.7 S21：连续谱阈值与奇性稳定性

- §6 的"极点 = 主尺度"保持即 S21 的奇性非增定理在相位密度框架下的推广；
- 有限阶 EM 的端点层不引入新奇点，与 S21 的 Bregman–KL 敏感度链一致。

### 7.8 S22：窗/核最优化与变分原理

- §1–§2 的密度估计依赖 S22 的带限偶窗变分原理；
- 窗化迹恒等（引理 1.1）对应 S22 的频域核型 Euler–Lagrange 方程。

### 7.9 S23：多窗协同优化与 Pareto 前沿

- §4 的 Kadec 型稳定对应 S23 的多窗族小扰动稳定性；
- 相位密度阈值为 S23 的 Pareto 前沿提供必要边界。

### 7.10 S24：紧框架与对偶窗

- 定理 1.2 的采样下界对应 S24 的帧界判据；
- §3 的 Clark 基对应 S24 的 Parseval 紧帧充要条件。

### 7.11 S25：非平稳 Weyl–Mellin 框架

- §5 的格点密度阈值 $\tau_0\sigma_0=2\pi$ 对应 S25 的"无混叠"条件；
- Balian–Low 不可能性为 S25 的非平稳 tight 框架提供临界密度边界；
- §4 的小扰动稳定对应 S25 定理 4.2 的轻微非均匀步长稳定性。

---

## 8. 失效边界

1. **无限阶 EM**：将 EM 当无穷级使用会引入伪奇性并破坏"极阶不升"，从而无法保障密度估计与稳定性。
2. **非 HB/相位不正**：若失去 $\varphi'(x)=\pi K(x,x)/|E(x)|^2>0$ 的正性，则相位密度刻度失效，应退回一般 Carleson 型测度框架。
3. **相位非分离**：相位坐标上不分离使 Gram 矩阵不可逆，小扰动定理不适用。

---

## 9. 可检清单（最小充分条件）

1. **相位刻度**：验证 $\varphi'(x)=\pi\rho(x)=\pi K(x,x)/|E(x)|^2>0$，并计算 $\Phi(I)=\int_I\varphi'(x)\,dx$。

2. **采样下界**：对非负偶窗 $w_R$，检查

$$
\sum_{x_n\in\Lambda}\!\big\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\big\rangle\ \gtrsim\ \frac1\pi\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx,
$$

令 $R\to\infty$ 与平移平均，得 $D_\varphi^-(\Lambda)\ge1$。

3. **插值上界**：对非负偶窗 $w_R$，检查

$$
\sum_{x_n\in\Lambda}\!\big\langle M_{w_R}\kappa_{x_n},\kappa_{x_n}\big\rangle\ \lesssim\ \frac1\pi\int_{\mathbb R} w_R(x)\,\varphi'(x)\,dx,
$$

同理得 $D_\varphi^+(\Lambda)\le1$。

4. **相位网格充分性**：在 Clark/HB 正则下，$\{\kappa_x\}_{x\in X_\theta}$ 为（Riesz/正交）基，且 $D_\varphi^\pm(X_\theta)=1$。

5. **小扰动稳定**：若 $\sup_n|\varphi(x_n)-(\theta+n\pi)|\le\delta<\delta_0$ 且相位分离常数 $\Delta_\varphi>0$，用 Bari–Neumann 法得 Riesz 基稳定。

6. **Balian–Low**：在 $\tau_0\sigma_0=2\pi$ 下，若 $Ag,Bg\in L^2$ 则与 Wexler–Raz/CCR 矛盾，从而不可；非临界密度按注释分情形。

7. **窗化纪律**：所有离散—连续换序仅用**有限阶** EM；Nyquist 条件下别名项为 0；误差层整/全纯，极阶不升。

---

## 参考文献（选）

* L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice-Hall, 1968（HB 空间、相位与再生核）。
* J. Antezana, J. Marzo, J.-F. Olsen, *Zeros of Random Functions Generated with de Branges Kernels*, IMRN, 2016（$K(x,x)=\pi^{-1}\varphi'(x)|E(x)|^2$）。
* J. Marzo, S. Nitzan, J.-F. Olsen, *Sampling and interpolation in de Branges spaces with doubling phase*, J. Anal. Math., 2012（doubling 相位下的 Landau 型密度阈值，定理 1.2 与 2.1 所依赖）。
* K. Seip, *Interpolation and Sampling in Spaces of Analytic Functions*, Amer. Math. Soc., 2004（Beurling 密度与 Landau 型定理）。
* N. Makarov, A. Poltoratski, *Meromorphic Inner Functions, Toeplitz Kernels and the Uncertainty Principle*, Prog. Math., 2013（Clark 基与模型空间）。
* A. Baranov, *Stability of bases and frames of reproducing kernels in model spaces*, Ann. Inst. Fourier, 2005（模型空间核基的小扰动稳定，§4 所用）。
* S. Axler, *Berezin Transform and Invariant Subspaces*, Adv. Math., 1987（Berezin 变换与再生核关系）。
* I. Daubechies, *Ten Lectures on Wavelets*, SIAM, 1992（Balian–Low 定理与时—频局域）。
* C. Heil, D. Powell, *Gabor Schauder bases and the Balian-Low theorem*, J. Math. Phys., 2006（BLT 的综述与推广，§5 所引）。
* K. Gröchenig, *Foundations of Time–Frequency Analysis*, Birkhäuser, 2001（Weyl–Heisenberg 系统与 Kadec 定理）。
* A. Beurling, P. Malliavin, *On Fourier transforms of measures with compact support*, Acta Math., 1962（Beurling 密度）。
* N. Nikolski, *Operators, Functions, and Systems: An Easy Reading*, Amer. Math. Soc., 2002（Riesz 基与小扰动）。
* NIST DLMF, §2.10/§24.7（Bernoulli/Euler 多项式与 EM 配方）。

---

**结语**

以相位导数 $\varphi'$ 为核心刻度，本文在 de Branges–Mellin 框架中统一了采样—插值密度阈值、相位网格的充分模板、小扰动稳定半径与 Mellin–Weyl 格点下的 Balian–Low 类不可能性；并在严格的"有限阶" EM 与 Nyquist–Poisson–EM 纪律下确保窗化实现对奇性与极阶的控制。由此，S15–S25 的窗/核优化与帧构造获得密度—稳定层面的边界与可检准则，也为后续非齐次/多通道相位密度与自适应窗的算子化设计提供坚实基础。该框架与 S15–S25（Weyl–Heisenberg、de Branges 规范系统、散射—酉性、窗不等式、光谱图、BN 投影、连续谱阈值、窗/核最优、多窗协同、紧框架与非平稳框架）接口一致，将相位密度作为统一刻度，建立采样—插值—帧的必要/充分准则与稳定性边界。
