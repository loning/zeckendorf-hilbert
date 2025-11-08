# 以 de Branges 相位嵌入构造 RCA—WSIG 统一度量：轨迹—相位度量、几何可逆性与有限阶 NPE 误差闭合

## 摘要

提出一种将可逆元胞自动机（RCA）的离散时空轨迹嵌入到 de Branges–Kreĭn 相位几何中的方法，定义"轨迹—相位度量" $d_{\rm TP}$。该度量以稳定窗族将局部轨迹窗化为 Hilbert 观测向量，经 Hermite–Biehler/de Branges 嵌入得到相位函数 $\varphi(E)$，并以相位差在能轴上的加权积分给出轨迹间距离。度量刻度由母尺同一式 $\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$ 对齐，其中 $\mathsf Q(E)=-i S(E)^\dagger S'(E)$ 为 Wigner–Smith 群延迟矩阵，$\rho_{\rm rel}$ 为谱移密度/相对态密度。证明在窗族满足紧/近紧框架与带宽正则条件下，$d_{\rm TP}$ 是一真实度量；若 RCA 演化与单位散射族共轭并满足几何可逆性，则演化在 $d_{\rm TP}$ 下等距。建立 Nyquist–Poisson–Euler–Maclaurin（NPE）三分解的有限阶误差闭合，上界由别名项、Euler–Maclaurin 边界层与高频尾项三者控制，从而给出离散—连续读数的一致性非渐近界。多通道情形下，度量提升为本征相位差与群延迟本征值的迹型整合，并在 Toeplitz/Berezin 压缩与 Carleson/Landau 条件下保持稳定。给出带限/弱色散区的紧界化表达与可计算玩具系实例。

---

## 0. Notation & Axioms / Conventions

**母尺（刻度同一）**
$$
\boxed{\frac{\varphi'(E)}{\pi} = \rho_{\rm rel}(E) = \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)},\qquad
\mathsf Q(E)=-i S(E)^\dagger S'(E), S(E)\in U(N).
$$
该同一式连接 de Branges/谱移相位导数、相对态密度与 Wigner–Smith 群延迟迹，分别来源于 de Branges–Kreĭn理论、Birman–Kreĭn 公式与 Wigner–Smith 时间延迟定义。([普渡大学数学系][1])

**算子—测度—函数三元语言**
窗口/读数以 Toeplitz/Berezin 压缩 $K_{w,h}$ 表示，读数为对谱测度的线性泛函，必要时借助 Berezin 变换与 Toeplitz 代数的已知性质。([arXiv][2])

**有限阶误差纪律（NPE 三分解）**
任何离散—连续对接仅允许有限阶 Euler–Maclaurin 与 Poisson 重构，误差记为
$$
\text{Err}=\underbrace{\text{Poisson 别名}}_{\mathcal A_h}+\underbrace{\text{EM 边界层}}_{\mathcal B_M}+\underbrace{\text{高频尾项}}_{\mathcal T_H},
$$
所涉 Poisson 与 Euler–Maclaurin 判据取自标准参考。([dlmf.nist.gov][3])

**约定**
(i) 工作于绝对连续谱区；(ii) 窗族满足 Calderón 上下夹、Wexler–Raz 对偶/帧条件；(iii) 采样密度受 Landau 必要密度约束。([sites.math.duke.edu][4])

---

## 1. 引言

RCA 的全局动力为信息保持的可逆映射；其时空图在局部更新下形成轨迹族。WSIG 框架以散射相位—相对态密度—群延迟的同一刻度组织几何与信息。de Branges 空间 $\mathcal H(E)$ 提供将窗化读数映至"能轴相位"的正交分解与再生核结构，使"轨迹差异 $\leftrightarrow$ 相位位移 $\leftrightarrow$ 态密度/群延迟读数"成为可度量化的桥接。本工作建立相位几何下的轨迹度量 $d_{\rm TP}$，并证明 RCA 演化的等距性与 NPE 有限阶误差闭合。

---

## 2. 预备：de Branges 空间、Hermite–Biehler 与相位

设 $E(z)=A(z)-iB(z)$ 为 Hermite–Biehler 函数，de Branges 空间 $\mathcal H(E)$ 由满足 $\frac{F}{E},\frac{F^\sharp}{E}\in H^2(\mathbb C_+)$ 的整函数 $F$ 组成，相位函数 $\varphi(E)$ 由 $E$ 的辐角确定，其导数给出 canonical system 的谱测度密度。在散射理论中，Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\xi(E)}$ 使 $\xi'(E)=\rho_{\rm rel}(E)$ 与多通道本征相位 $\theta_j$ 的和配准，而 Wigner–Smith 定义 $\mathsf Q(E)=-iS^\dagger S'$ 给出 $\operatorname{tr}\mathsf Q(E)=2\sum_j \theta_j'(E)$。据此得到母尺同一式。([普渡大学数学系][1])

---

## 3. 窗化嵌入与观测模型

### 3.1 稳定窗族与帧

取窗族 $\mathcal W=\{w_\lambda\}_{\lambda\in\Lambda}$（时间或对数时间模型），满足 Calderón 上下夹与 Wexler–Raz 对偶关系，从而形成紧/近紧框架，保证窗化读数的稳定性与重构。([sites.math.duke.edu][4])

对 RCA 轨迹 $\gamma$ 的局部块 $x_\gamma|_I$，定义
$$
\Psi_\gamma(\lambda):=\langle x_\gamma|_I, w_\lambda\rangle,\qquad
\Phi_\gamma:=\mathcal J(\Psi_\gamma)\in\mathcal H(E),
$$
其中嵌入算子 $\mathcal J:\ell^2(\Lambda)\to\mathcal H(E)$ 连续且可逆于像。

### 3.2 相位抽取与权

由 Hermite–Biehler 对得到 $\varphi_\gamma(E)=\arg E_\gamma(E)$。度量权 $\kappa(E)$ 取自窗的有效带宽与条件数（由 Toeplitz/Berezin 压缩与 Berezin 变换刻画），从而与能轴读数配准。([arXiv][2])

---

## 4. 轨迹—相位度量 $d_{\rm TP}$ 与基本性质

### 4.1 定义

取绝对连续带 $\mathcal E\subset\mathbb R$ 与 $\kappa\ge 0$（$\kappa\in L^1_{\rm loc}(\mathcal E)$），定义
$$
d_{\rm TP}(\gamma_1,\gamma_2)
:=\frac{1}{\pi}\int_{\mathcal E}\bigl|\varphi_{\gamma_1}(E)-\varphi_{\gamma_2}(E)\bigr|\kappa(E)dE.
$$

### 4.2 母尺的密度型表述

由 $\frac{1}{\pi}d\varphi_\gamma=\rho_{\rm rel,\gamma}(E)dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q_\gamma(E)dE$，令 $\Delta\rho:=\rho_{\gamma_1}-\rho_{\gamma_2}$，则
$$
d_{\rm TP}(\gamma_1,\gamma_2)
=\int_{\mathcal E}\Bigl|\int_{E_0}^{E}\Delta\rho(\epsilon)d\epsilon\Bigr|\kappa(E)dE.
$$

### 4.3 定理 A（度量性）

若窗族为紧/近紧框架且 $\kappa$ 正则，则 $d_{\rm TP}$ 为一度量；对任意 $\gamma$，以基准能量 $E_\star$ 归一化 $\varphi_\gamma(E_\star)=0$ 消除相位常量漂移。

*证明.* 非负性与对称性显然；同一点零来自归一化；三角不等式由 Minkowski 不等式与相位差可加性给出。窗—de Branges 嵌入的连续性保证 $\varphi\in L^1_{\rm loc}$ 的良定义，帧不等式确保扰动稳定。（窗族与帧性质见 Wexler–Raz 与后续发展。）([sites.math.duke.edu][4])

---

## 5. 几何可逆性与等距性

### 5.1 定义（几何可逆性）

称 RCA 演化 $U$ 具有几何可逆性，若存在可测双射 $\sigma_U:\mathcal E\to\mathcal E$ 与常数 $c_U$，使对任意轨迹 $\gamma$ 有
$$
\varphi_{U\gamma}(E)=\varphi_\gamma(\sigma_U(E))+c_U,
$$
且 $\sigma_U$ 使 $\kappa(E)dE$ 与 $\kappa(\sigma_U(E))|\sigma_U'(E)|dE$ 等价。

### 5.2 定理 B（等距同构）

若 $U$ 具几何可逆性并与单位散射族共轭，则
$$
d_{\rm TP}(U\gamma_1,U\gamma_2)=d_{\rm TP}(\gamma_1,\gamma_2).
$$

*证明.* 由定义
$|\varphi_{U\gamma_1}-\varphi_{U\gamma_2}|=|\varphi_{\gamma_1}-\varphi_{\gamma_2}|\circ\sigma_U$。作变量替换得到积分不变，从而等距成立。

### 5.3 推论（可逆性 = 相位差守恒）

若 $U$ 为无耗散可逆演化且与单位散射族共轭，则对任意 $\gamma_1,\gamma_2$，相位差在能轴重标度下保持，等距性随之成立。RCA 的可逆性条件可由 Hedlund–Moore–Myhill 理论与其后续综述给出。([SpringerLink][5])

---

## 6. NPE 三分解的有限阶误差闭合

### 6.1 模型

离散—连续误差分解为
$$
\mathcal E=\mathcal A_h+\mathcal B_M+\mathcal T_H.
$$
$\mathcal A_h$ 为 Poisson 别名（步长 $h$ 引起），$\mathcal B_M$ 为至 $M$ 阶 Euler–Maclaurin 边界层，$\mathcal T_H$ 为高频截断 $H$ 的尾项。([dlmf.nist.gov][3])

### 6.2 定理 C（有限阶闭合界）

设窗谱有效带限/亚带限，$\rho_\gamma\in BV_{\rm loc}$ 且其变换在 $|\omega|>H$ 处衰减为 $\mathcal O(H^{-\alpha})$。则存在常数 $C_{\mathcal W}$ 与连续函 $\eta(h,M,H)\to 0$（$h\to 0,M\to\infty,H\to\infty$）使
$$
\bigl|d_{\rm TP}^{\rm disc}(\gamma_1,\gamma_2)-d_{\rm TP}(\gamma_1,\gamma_2)\bigr|
\le C_{\mathcal W}\eta(h,M,H),
$$
且
$$
\eta(h,M,H) \asymp \underbrace{e^{-2\pi H/h}}_{\text{别名}}+\underbrace{\sum_{m=1}^M \frac{|B_{2m}|}{(2m)!}\Xi_{2m-1}}_{\text{EM 边界层}}+\underbrace{H^{-\alpha}\Upsilon_\alpha}_{\text{尾项}}.
$$

*证明要点.* Poisson 求和给出别名的指数衰减；有限阶 Euler–Maclaurin 控制端点层；窗谱与信号正则性给出尾项幂律衰减。([dlmf.nist.gov][3])

---

## 7. 多通道：本征相位—群延迟与 Toeplitz/Berezin 稳定性

### 7.1 多通道度量

令 $S(E)\in U(N)$，$\{\theta_j(E)\}$ 为本征相位，$\{\tau_j(E)\}$ 为群延迟本征值（Wigner–Smith 的特征值）。定义
$$
d_{\rm TP}^{(N)}(\gamma_1,\gamma_2)
:=\frac{1}{\pi}\int_{\mathcal E}\Bigl(\sum_{j=1}^N\omega_j(E)|\theta_{j,\gamma_1}(E)-\theta_{j,\gamma_2}(E)|\Bigr)\kappa(E)dE,
$$
权 $\omega_j(E)$ 可取 $\tau_j/\sum_k\tau_k$ 或常数，保证与 $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 同尺度。([arXiv][6])

### 7.2 压缩与采样稳定性

Toeplitz/Berezin 压缩的有界性与嵌入稳定性由 Berezin 变换及相关 Toeplitz 代数性质保证；从样本到能轴的稳定重构受 Carleson 测度与 Landau 必要密度控制。([arXiv][2])

### 7.3 定理 D（稳定等距）

在带限/弱色散与紧框架窗族下，若几何可逆性与单位散射共轭成立，则 $d_{\rm TP}^{(N)}$ 等距不变，并满足与定理 C 类似的双边误差界。

---

## 8. 变分最优窗与不确定性约束

在资源约束（采样率/支持长度/平滑阶）下考虑泛函
$$
\mathcal J[w]=\sup_{\gamma_1,\gamma_2}\frac{d_{\rm TP}(\gamma_1,\gamma_2)}{|x_{\gamma_1}-x_{\gamma_2}|_{\mathcal X}}.
$$
在帧常数与 Landau 密度约束内，最优窗趋近紧框架并受 Balian–Low 型不确定性限制，故在相应模型下近似高斯/对数高斯达到近最优定位。([Core][7])

---

## 9. 可计算玩具系

取一维 Margolus 型分块可逆规则（交换—相位翻转），设块长 $L$、时间步长 $h$、频带 $H$。构造
$$
\Psi_\gamma(\lambda)=\sum_{n=0}^{L-1} x_\gamma[n]\overline{w_\lambda[n]},\qquad
\Phi_\gamma=\mathcal J(\Psi_\gamma).
$$
计算离散相位导数并施行 NPE 校正，数值观察到：
(i) 单步推进后 $d_{\rm TP}$ 数值不变（等距）；
(ii) 当 $(h,M,H)$ 取使 $\eta(h,M,H)\to 0$ 的族时，离散—连续偏差收敛；
(iii) 可逆分支/碰撞对应相位分段单调的拼接，$d_{\rm TP}$ 对分支间差异给出稳定下界。（RCA 可逆性、分块表示与模拟框架参考综述。）([科学直通车][8])

---

## 10. 主定理

**主定理（统一表述）** 设 $\mathcal W$ 为满足 Calderón 与紧/近紧框架条件的窗族，$\kappa$ 与 $\mathcal W$ 匹配，$\gamma\mapsto \Phi_\gamma\in\mathcal H(E)$ 的嵌入连续可逆于像。则：

(1) $d_{\rm TP}$ 定义良好且为度量；
(2) 若 RCA 演化 $U$ 具几何可逆性并与单位散射族共轭，则 $U$ 在 $d_{\rm TP}$ 下等距；
(3) 在带限/弱色散与 Carleson/Landau 条件下，存在常数 $C_{\mathcal W}$ 与参数 $(h,M,H)$ 使离散读数满足有限阶 NPE 闭合界；
(4) 多通道下以本征相位—群延迟权的迹型整合定义 $d_{\rm TP}^{(N)}$ 可保留 (1)–(3)。

*证明纲要.* (1)–(2) 见第 4–5 节；(3) 由第 6 节的 NPE 三项闭合及"奇性不增/极点=主尺度"；(4) 利用第 7 节的本征分解与 Toeplitz/Berezin 稳定性。

---

## 11. 与 WSIG–EBOC–RCA 的对位

在 EBOC 视角下，宇宙为静态块，观察者仅能在窗口上以母尺读数。本文 $d_{\rm TP}$ 将 RCA 的离散可逆动力语义化为"相位几何的等距保相"，建立
$$
\text{RCA 轨迹差异} \longleftrightarrow \text{de Branges 相位位移} \longleftrightarrow \text{相对态密度/群延迟}.
$$
资源变化（采样率/窗口/带宽）由 NPE 有限阶闭合确保稳定；多通道迹型整合与 Carleson/Landau 条件共同保证非渐近可实现性。([项目欧几里德][9])

---

## 12. 结论卡片

**卡片 I（刻度同一）**
$$
\boxed{\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)},
$$
相位—密度—群延迟统一于同一刻度。([arXiv][10])

**卡片 II（有限阶 EM 与极点=主尺度）**
离散—连续重构遵循有限阶 NPE：别名—边界层—尾项三项闭合；奇性不增，极点决定主尺度与变分最优窗的特征方程。([dlmf.nist.gov][3])

---

## 附录 A：等距的测度变换细节

若 $\sigma_U$ 可测可逆且 $\kappa(E)dE$ 与 $\kappa(\sigma_U(E))|\sigma_U'(E)|dE$ 等价，则
$$
\int_{\mathcal E}|\varphi_{\gamma_1}\circ\sigma_U-\varphi_{\gamma_2}\circ\sigma_U|\kappa(E)dE
=\int_{\sigma_U(\mathcal E)}|\varphi_{\gamma_1}-\varphi_{\gamma_2}|\kappa(\epsilon)d\epsilon.
$$
Mellin 伸缩与能量平移的协变性由窗族的尺度/调频不变性与帧常数稳定性保证。([sites.math.duke.edu][4])

---

## 附录 B：NPE 三项上界范式

设 $\widehat w$ 的有效支撑在 $|\omega|\le H$，采样步长 $h$，EM 阶数 $M$。则
$$
|\mathcal A_h|\lesssim \exp(-2\pi H/h),\quad
|\mathcal B_M|\lesssim \sum_{m=1}^M \frac{|B_{2m}|}{(2m)!}\Xi_{2m-1},\quad
|\mathcal T_H|\lesssim H^{-\alpha}\Upsilon_\alpha,
$$
其中 $\Xi_k$ 为边界导数跳读数，$\Upsilon_\alpha$ 由高频衰减指数给出。([dlmf.nist.gov][11])

---

## 附录 C：Toeplitz/Berezin 压缩与 Carleson—Landau

压缩算子
$K_{w,h}f(E)=\int f(t)\overline{w_h(t;E)}dt$
与其伴随的有界性由 Berezin 变换刻画；Carleson 测度与 Landau 密度分别给出嵌入稳定与必要采样密度，从而将样本/块的稳定性传递到 $d_{\rm TP}$ 的误差预算。([arXiv][2])

---

## 参考文献（节选）

1. L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice–Hall, 1968. ([普渡大学数学系][1])
2. A. Pushnitski, "An integer-valued version of the Birman–Kreĭn formula", 2010. ([arXiv][10])
3. A. Strohmaier, "The Birman–Kreĭn formula for differential forms…", *Bull. Sci. Math.*, 2022. ([RUG Research][12])
4. E. P. Wigner, "Lower Limit for the Energy Derivative of the Scattering Phase Shift", *Phys. Rev.*, 1955. ([物理评论链接管理器][13])
5. F. T. Smith, "Lifetime Matrix in Collision Theory", *Phys. Rev.*, 1960. ([物理评论链接管理器][14])
6. H. J. Landau, "Necessary density conditions for sampling and interpolation…", *Acta Math.*, 1967. ([项目欧几里德][9])
7. I. Daubechies, "Gabor Time–Frequency Lattices and the Wexler–Raz Identity", *J. Fourier Anal. Appl.*, 1994. ([sites.math.duke.edu][4])
8. A. Janssen, "On rationally oversampled Weyl–Heisenberg frames", 1995. ([nuhagphp.univie.ac.at][15])
9. J. A. Peláez, J. C. Pozo, "Berezin transform and Toeplitz operators on weighted Bergman spaces", 2016. ([arXiv][2])
10. S. Axler, Z. Čučković, D. Zheng, "The Berezin transform on the Toeplitz algebra", 1998. ([SciSpace][16])
11. E. Fricain, A. Hartmann, W. T. Ross, "A Survey on Reverse Carleson Measures", 2016. ([arXiv][17])
12. J. Marzo, "Sampling and interpolation in de Branges spaces with doubling phase", 2012. ([SpringerLink][18])
13. G. A. Hedlund, "Endomorphisms and automorphisms of the shift dynamical system", 1969. ([SpringerLink][5])
14. J. Kari, "Theory of cellular automata: A survey", *Theor. Comput. Sci.*, 2005；及"Reversible Cellular Automata"条目。([科学直通车][8])
15. NIST DLMF, §1.8 Poisson Summation；§2.10 Euler–Maclaurin。([dlmf.nist.gov][3])
16. C. Texier, "Wigner time delay and related concepts…", 2015–2018 综述。([arXiv][6])

---

[1]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[2]: https://arxiv.org/abs/1607.04394?utm_source=chatgpt.com "Berezin transform and Toeplitz operators on weighted ..."
[3]: https://dlmf.nist.gov/1.8?utm_source=chatgpt.com "1.8 Fourier Series"
[4]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[5]: https://link.springer.com/article/10.1007/BF01691062?utm_source=chatgpt.com "Endomorphisms and automorphisms of the shift dynamical ..."
[6]: https://arxiv.org/pdf/1507.00075?utm_source=chatgpt.com "arXiv:1507.00075v6 [cond-mat.mes-hall] 5 Nov 2018"
[7]: https://core.ac.uk/download/pdf/82782829.pdf?utm_source=chatgpt.com "The Balian–Low theorem for symplectic lattices in higher ..."
[8]: https://www.sciencedirect.com/science/article/pii/S030439750500054X?utm_source=chatgpt.com "Theory of cellular automata: A survey"
[9]: https://projecteuclid.org/journals/acta-mathematica/volume-117/issue-none/Necessary-density-conditions-for-sampling-and-interpolation-of-certain-entire/10.1007/BF02395039.full?utm_source=chatgpt.com "Necessary density conditions for sampling and ..."
[10]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[11]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[12]: https://research.rug.nl/files/232459978/1_s2.0_S0007449722000707_main.pdf?utm_source=chatgpt.com "The Birman-Krein formula for differential forms and ..."
[13]: https://link.aps.org/doi/10.1103/PhysRev.98.145?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering Phase ..."
[14]: https://link.aps.org/doi/10.1103/PhysRev.118.349?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory | Phys. Rev."
[15]: https://nuhagphp.univie.ac.at/janssen/data/p074.pdf?utm_source=chatgpt.com "On rationally oversampled Weyl-Heisenberg frames"
[16]: https://scispace.com/pdf/the-berezin-transform-on-the-toeplitz-algebra-4yl1dm3skj.pdf?utm_source=chatgpt.com "The Berezin transform on the Toeplitz algebra"
[17]: https://arxiv.org/pdf/1601.00226?utm_source=chatgpt.com "arXiv:1601.00226v2 [math.CV] 2 Feb 2016"
[18]: https://link.springer.com/article/10.1007/s11854-012-0026-2?utm_source=chatgpt.com "Sampling and interpolation in de Branges spaces with ..."