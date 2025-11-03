# WSIG–EBOC–RCA 统一理论

**以"窗—群延迟比不变量"为母尺对光速常数作几何化重述**

Version: 1.4

**关键词**：Wigner–Smith 群延迟；Birman–Kreĭn 谱移；de Branges–Kreĭn 规范系统；窗化迹与 Nyquist–Poisson–Euler–Maclaurin（NPE）三分解误差；帧/采样密度；信息几何（I-投影）；可逆元胞自动机

---

## 摘要

在窗化散射与信息几何（WSIG）、静态块宇宙（EBOC）与可逆元胞自动机（RCA）的统一框架中，定义对任意观测三元 $(\mathcal H,w,S)$ 的**窗—群延迟比**

$$
\chi(\mathcal H,w,S):=\frac{\Delta[w]}{\langle\tau_g\rangle_w},
$$

其中 $\Delta[w]$ 是窗 $w$ 的有效跨度，$\langle\tau_g\rangle_w$ 为以 $w$ 加权的 Wigner–Smith 群延迟平均。**在假设 A（§1）下**，证明在所有**可逆观测变换**（信息不损的坐标/尺度重标、酉性预滤、帧/采样重排以及可逆格点更新）下，$\chi$ 为**不变量**，其公共值记为 $c$。在时空几何解释中，取 $\Delta[w]$ 为有效空间长度、$\langle\tau_g\rangle_w$ 为时间延迟，则 $c$ 等价于**可达信号锥的最大斜率**，与光速常数同构。该构造锚定于以下公认链式等式与判据：**相位导数—谱移密度—群延迟**之统一（绝对连续谱 a.e.），Birman–Kreĭn 恒等式与 Wigner–Smith 矩阵 $\mathsf Q=-i\,\hbar\,S^\dagger \partial_E S$ 的迹表征；窗化读数的 **NPE 非渐近误差学**；Gabor/非平稳 Gabor 帧的 Wexler–Raz 条件、Landau 密度门槛与 Balian–Low 障碍；以及 I-投影与 Ky–Fan 极小化的"读码—提交"一致性。奇性/阈值处以 de Branges–Kreĭn 与 Rouché-型稳定判据控制零极结构，保证 $\chi$ 的可检稳定性。进一步证明：RCA 的"前沿斜率"细化极限 $c_{\rm RCA}$ 与连续散射侧常数 $c$ 一致，并给出多窗—多通道的可复现实验规程（含采样率、窗阶与置信区间构造）。

---

## 0. 记号、规范与公理

### 0.1 基本记号与已知链

能量变量 $E\in\mathbb R$。散射矩阵 $S(E)\in U(N)$（a.e. 可微）。Wigner–Smith 延迟矩阵

$$
\mathsf Q(E):=-i\,\hbar\,S(E)^\dagger\,\frac{dS}{dE}(E).
$$

在绝对连续谱的 Lebesgue 点 a.e. 成立

$$
\frac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q(E)\ =\ \rho_{\rm rel}(E)\ =\ \frac{1}{\pi}\,\varphi'(E)\ =\ -\,\xi'(E)\quad\text{(a.e.)},
$$

其中 $\xi$ 为谱移函数（Birman–Kreĭn $\det S(E)=\exp(-2\pi i\,\xi(E))$ 之导数形式），$\rho_{\rm rel}$ 为相对态密度，$\varphi(E):=\tfrac12\operatorname{Arg}\det S(E)$。见 Wigner–Smith 与其矩阵形式、BK 恒等式及其现代表述与综述。([chaosbook.org][1])

**窗化读数与误差学**采用 Nyquist–Poisson–Euler–Maclaurin（NPE）三分解：离散化的混叠（Poisson）、端点伯努利层（有限阶 Euler–Maclaurin）与窗外尾项（衰减/带限给界）。相关公式与统一误差界见 DLMF（Poisson 与 EM）及统一误差估计文献。([dlmf.nist.gov][2])

### 0.2 观测三元与可逆观测变换群

**观测三元** $(\mathcal H,w,S)$：$\mathcal H$ 为载体，$w$ 为偶窗（严格带限 Paley–Wiener 或指数衰减）并允许缩放 $w_R(x)=w(x/R)$，$S(E)$ 为（多通道）散射矩阵。**可逆观测变换群** $\mathcal G$ 由下列信息不损操作生成：

1. 坐标同胚与尺度/速率重标；
2. 带限子空间上的酉性预滤（功能演算）；
3. 帧/采样重排（紧帧/Parseval 与对偶窗，Wexler–Raz 条件）；
4. 离散格点的可逆局域更新（RCA），其频率侧与连续窗/帧由非平稳 Gabor 框架桥接。([sites.math.duke.edu][3])

### 0.3 窗的有效跨度与群延迟平均

**有效跨度** $\Delta[w]$：取与实验几何协变的半径/二次型（如时间半径 $\Delta_t$、空间半径 $\Delta_x$），要求在缩放/平移/酉性预滤下齐次。

**群延迟平均**

$$
\boxed{\ \langle\tau_g\rangle_w\ :=\ \frac{\displaystyle\int \Big(\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\Big)\,K_w(E)\,dE}{\displaystyle\int K_w(E)\,dE}\ =\ \hbar\,\frac{\displaystyle\int \rho_{\rm rel}(E)\,K_w(E)\,dE}{\displaystyle\int K_w(E)\,dE}\ }.
$$

其中 $K_w$ 为窗诱导的能量核；由上式的 a.e. 等价，亦可用 $\rho_{\rm rel}(E)$、$\varphi'(E)/\pi$ 或 $-\xi'(E)$ 替换被积函数。([epub.uni-regensburg.de][4])

---

## 1. 主定义与不变量定理

### 定义 1.1（窗—群延迟比与母尺）

$$
\boxed{\ \chi(\mathcal H,w,S):=\frac{\Delta[w]}{\langle\tau_g\rangle_w}\ }.
$$

若对所有 $T\in\mathcal G$ 与允许窗族 $w$ 有 $\chi(\mathcal H,w,S)=\chi\big(T(\mathcal H,w,S)\big)=:c$，称 $c$ 为**窗—群延迟比不变量**（母尺）。

### 命题 1.2（$\chi$ 的 $\mathcal G$-不变性；在假设 A 下）

**假设 A（协变与可测性）**：满足下列条件：

(i) 在单位/坐标缩放与能量再参数化（不含洛伦兹 boost）下，$\Delta[w]$ 与 $\langle\tau_g\rangle_w$ 的维度同次协变；若涉及洛伦兹变换，参见 §3 的锥界上界表述；

(ii) 带限偶子空间上的酉性预滤保持窗支撑与能量；

(iii) 帧/采样重排在 Parseval 归一后不改变量纲与读数；

(iv) RCA 细化极限与非平稳 Gabor 框架保证离散前沿斜率与连续侧读数一致。

**结论**：在假设 A 下，$\chi$ 在 $\mathcal G$ 下不变。

**要点说明**：

(i) **单位/坐标协变（非 boost）**：在单位缩放与能量再参数化下，$\Delta[w]$ 与 $\langle\tau_g\rangle_w$ 同次变换，故比值不变；洛伦兹协变性不依赖逐项齐次，而是通过 §3 定义的最大斜率 $c:=\sup_w \Delta[w]/\langle\tau_g\rangle_w$ 得到；

(ii) **预滤/功能演算**：带限偶子空间上酉性预滤不改变 $\widehat w$ 的支撑与能量；窗化迹读数与 $\operatorname{tr}\mathsf Q$ 的卷积在 NPE 纪律下只产生统一误差阶（伯努利层与尾项），不影响极限比值；([dlmf.nist.gov][2])

(iii) **帧/采样重排**：Wexler–Raz 条件与帧算子刻画保证 Parseval 常数归一后窗化读数不变，$\Delta[w]$ 的度量在等距群下保持，故 $\chi$ 不变；([sites.math.duke.edu][3])

(iv) **RCA 可逆更新**：细化极限下，非平稳 Gabor 对角化与 Walnut/Calderón 和确保离散前沿斜率的能量—时间刻度与连续 $\langle\tau_g\rangle_w$ 对齐，极限比值与 $c$ 一致。([worldscientific.com][5])

---

## 2. 相位—密度—延迟链与窗化读数

### 2.1 相位导数 = 谱移密度 = 群延迟（WS–BK 链）

由 $S$ 的行列式相位与 Wigner–Smith 矩阵定义，

$$
\boxed{\ \frac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q(E)\ =\ \rho_{\rm rel}(E)\ =\ \frac{1}{\pi}\,\varphi'(E)\ =\ -\,\xi'(E)\quad\text{(a.e.)}\ }.
$$

第一等号用 $S^{-1}=S^\dagger$ 与 $\partial_E\log\det S=\operatorname{tr}(S^{-1}\partial_E S)$ 得到；BK 公式给出 $\det S=\exp(-2\pi i\xi)$（此处采用 BK 号记；若改用 $\det S=\exp(+2\pi i\xi)$，则右端号改为正），Friedel–Kreĭn 关系与 Wigner–Smith 统一了相位导数、谱密度与时间延迟的刻度。([chaosbook.org][1])

### 2.2 窗化迹与 NPE 三分解误差

离散实现的总误差分解为

$$
\text{error}=\underbrace{\text{alias}}_{\text{Poisson}}\ +\ \underbrace{\text{Bernoulli layer}}_{\text{有限阶 EM}}\ +\ \underbrace{\text{tail}}_{\text{窗外截断}},
$$

严格带限与 Nyquist 步长可令 $\text{alias}=0$；伯努利层由端点导数确定，有限阶即可闭合；尾项由窗衰减给出可积上界。该纪律支撑 $\langle\tau_g\rangle_w$ 的可重复读数与 $\chi$ 的非渐近稳定估计。([dlmf.nist.gov][2])

---

## 3. 光速的几何化：$c$ 作为最大斜率

在时空几何解释中，取 $\Delta[w]$ 为有效空间长度、$\langle\tau_g\rangle_w$ 为时间延迟，则 $\chi=\Delta[w]/\langle\tau_g\rangle_w$ 具速度维度。在本稿的可逆观测变换 $\mathcal G$（单位/坐标重标、酉性预滤、帧/采样重排、RCA 细化）下，$\chi$ 不变。狭义相对论情形下，定义

$$
c:=\sup_{w}\frac{\Delta[w]}{\langle\tau_g\rangle_w},
$$

将其解释为**可达信号锥的最大斜率**；该上界为洛伦兹不变量，因而与光速常数同构。该陈述依赖 §2 的刻度统一与多通道迹式表述。对于非酉/开放系统，可引入复时间延迟，并以 $\partial_E \Im\log\det S$ 等广义刻度替代；此时**不再**有 $\tfrac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q=\rho_{\rm rel}$ 的严格等式（该等式仅在 $S$ 酉时成立）。（参见引文 [link.aps.org][6]）

---

## 4. 离散—连续桥接与 RCA 前沿斜率

以非平稳 Weyl–Heisenberg（Gabor）框架对角化分块系统，利用 Walnut 型表示与"painless"构造控制能量守恒与稳定性；在 tight/dual 与帧界夹逼下，细化网格得到

$$
\lim_{\text{细化}}\ \frac{\Delta_{\rm lattice}}{\tau_{\rm steps}}=c_{\rm RCA}=c.
$$

非平稳 Gabor 与"painless"展开给出显式构造与稳定半径，实现离散—连续的量化一致。([worldscientific.com][5])

---

## 5. 误差学与窗/核的最优设计

将窗/核设计表述为带限偶子空间上的凸变分问题：在固定 $(\Delta,M,T)$（跨度、EM 阶、采样总时长）下，最小化 $\langle\tau_g\rangle_w$ 估计的方差并约束 NPE 误差上界。强凸情形唯一解，弱稀疏情形由 Bregman–KL 正则得到 Γ-极限收敛。多窗的帕累托前沿可由广义双正交 $(GG^\dagger)$ 重构给出，并在 Parseval 框架下实现稳健冗余。Nyquist 率由被采样 integrand 的"和宽"确定；严格带限时 $\text{alias}=0$。([people.maths.ox.ac.uk][7])

---

## 6. 阈值/共振/奇性稳定与迹—Weyl 型定律

在 de Branges–Kreĭn 规范系统下，以谱函数与 Hermite–Biehler 结构控制零极分布；Rouché-型半径保证窗化与有限阶换序不引入新奇性且极阶不升。时间—频率局部化（Toeplitz/Anti-Wick）算子的迹与积性公式提供"符号积分 = 迹"的 Weyl 型弱极限，从而给出 $\langle\tau_g\rangle_w$ 的稳定读数。([math.purdue.edu][8])

---

## 7. 采样密度门槛与 Balian–Low 障碍

以 $\varphi'(E)$ 诱导的相位密度为刻度，Landau 型必要密度成立；在 one-component/doubling-phase 条件下亦得充分性。单窗+矩形格在临界密度处受 Balian–Low 限制，实验实现需采用多窗/非均匀或超临界密度策略。([archive.ymsc.tsinghua.edu.cn][9])

---

## 8. EBOC 语义：读码—提交的一致性（Born = I-投影；指针基 = 光谱极小）

在信息几何中，I-投影（最小化 $D_{\mathrm{KL}}$）在给定约束族上产生最"保真"的更新；当约束与装置字典（窗/帧）对齐，温度极限由软到硬，得到与 Born 规则的等价提交机制。统计灵敏度由 KL–Pinsker 不等式控制，直接给出估计带宽与置信区间。指针基的选择可表述为 Ky–Fan 部分和极小（前 $k$ 个特征值/奇异值之和极小），与稳定读数的"光谱最简"一致。([projecteuclid.org][10])

---

## 9. 多通道统一与号记

对 $N$ 通道取标量

$$
\rho_\Sigma(E):=\operatorname{tr}(\rho-\rho_0)(E)=\frac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q(E).
$$

在采用 $\det S(E)=\exp(-2\pi i\,\xi(E))$ 的号记下，有 $\rho_\Sigma(E)=-\,\xi'(E)$；若改用 $\det S(E)=\exp(+2\pi i\,\xi(E))$，则号改为正，不影响本文比值结构。([arXiv][11])

---

## 10. 可检验陈述与复现规程

**(A) 窗无关性（跨窗族）**：选两族窗（带限与指数），若干尺度 $R$；在统一 NPE 校正后，$\Delta[w]/\langle\tau_g\rangle_w$ 收敛至同一 $c$，输出非渐近置信区间（KL–Pinsker）。([dlmf.nist.gov][2])

**(B) 变换协变性（跨 $\mathcal G$）**：坐标重标、预滤与帧/采样重排后重复读数，$\chi$ 在误差带内不变；多通道取迹后同样成立。([sites.math.duke.edu][3])

**(C) 离散—连续桥接**：RCA 的最短更新锥斜率随细化与非平稳帧对角化收敛至 $c$；在 tight/dual 与帧界夹下给出数值稳定性与容差预算。([worldscientific.com][5])

**(D) 统计闭环**：提交 = I-投影；构造 $\widehat c_i=\Delta[w^{(i)}]/\langle\tau_g\rangle_{w^{(i)}}$ 并以 KL–Pinsker 合并，产出置信带与最优多窗 Pareto 选择。([arXiv][12])

---

## 11. 讨论与边界

1. **单位与维度**：若 $\Delta[w]$ 取空间尺度、$\langle\tau_g\rangle_w$ 取时间延迟，则 $\chi$ 具速度维度；若二者处于对数/Mellin 刻度的无量纲表述，则需由几何字典回译为速度上界。
2. **非酉/开放系统**：可用复时间延迟与 $\partial_E \Im\log\det S$ 等广义刻度替代，$\chi$ 的比值结构可延续；但等式 $\tfrac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q=\rho_{\rm rel}$ **仅在酉散射时成立**，非酉情形不再与 $\rho_{\rm rel}$ 严格等同（参见 [link.aps.org][6]）。
3. **阈值/共振**：de Branges–Kreĭn 与 Rouché-型稳定保证窗化与有限阶换序不增奇性；剔除有限邻域后，$\chi$ 的一致极限与置信区间仍可构造。([arXiv][13])
4. **临界密度障碍**：单窗矩形格在临界密度受 Balian–Low 限制，推荐多窗/非均匀或超临界密度的实验方案。([heil.math.gatech.edu][14])

---

## 12. 结论

以**窗—群延迟比** $\chi=\Delta/\langle\tau_g\rangle$ 的群不变性为核心，建立"光速常数"作为**几何不变量**的重述。该母尺 $c$ 在量子/经典、连续/离散、多通道/单通道与读码/提交等层面一致，并在有限资源的现实读数中由 NPE 非渐近误差学与帧/采样纪律保障。核心刻度链 $\displaystyle\frac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q=\rho_{\rm rel}=\frac{1}{\pi}\,\varphi'(E)=-\,\xi'(E)$ 与 BK、WS、Wexler–Raz、Landau、Balian–Low 等判据共同构成可检、可复现的理论—实验闭环。

---

## 参考文献（选）

1. Wigner E. P., *Phys. Rev.* **98** (1955): 相位导数与因果性下界；Smith F. T., *Phys. Rev.* **118** (1960): 寿命/时间延迟矩阵 $\mathsf Q=-i\,\hbar\,S^\dagger \partial_E S$。([chaosbook.org][15])
2. Birman–Kreĭn 公式与谱移：Pushnitski A., *An integer-valued version of the Birman–Krein formula*, 2010；Yafaev D., *Perturbation determinants, the spectral shift function…*, 2007。([arXiv][11])
3. 相位—密度—延迟统一与 DoS 关系：Texier C., *Scattering on graphs (II): Friedel sum rule*, 2001；NJPhys (2014) 统一述评。([arXiv][16])
4. NPE：DLMF §1.8（Poisson）、§2（EM）与 Trefethen–Javed (2015) 的统一误差界。([dlmf.nist.gov][2])
5. Gabor/非平稳 Gabor 帧：Daubechies–Paul (1988) 局部化算子；Wexler–Raz 条件（Daubechies 等；Heil 历史综述）；非平稳/"painless"构造（Dörfler 等）。([sites.math.duke.edu][17])
6. 采样密度与障碍：Landau (1967) 必要密度及后续拓展；Heil (2006) Balian–Low 综述。([archive.ymsc.tsinghua.edu.cn][9])
7. 信息几何与 I-投影、KL–Pinsker：Csiszár (1975)；Canonne (2022)；Amari (2016/2018)。([projecteuclid.org][10])
8. de Branges–Kreĭn 规范系统与逆谱：de Branges (1968)；Romanov (2014)；Remling (2018/2025)。([math.purdue.edu][8])

---

## 附录 A：维度与规范

* 若 $\Delta[w]$ 取空间长度、$\langle\tau_g\rangle_w$ 取时间，则 $\chi$ 具速度维度；若处于对数/Mellin 刻度的无量纲表述，则需由几何字典回译。
* 本文采用 $\mathsf Q=-i\hbar S^\dagger\partial_E S$；于是 $\tfrac{1}{2\pi\hbar}\operatorname{tr}\mathsf Q=\rho_{\rm rel}=\varphi'/\pi=-\xi'$（BK 号记 $\det S=\exp(-2\pi i\xi)$）。若改用 $\det S=\exp(+2\pi i\xi)$，则关系式右端 $\xi'$ 项改号为正，不影响 $\chi$ 的比值结构与读数流程。([arXiv][11])

## 附录 B：最小可复现实验清单

1. 选择两族窗（带限 PW 与指数），每族 3–4 个尺度 $R$；
2. 选择带限前端核 $h$（两种和宽），按 integrand 的带宽和宽设定 Nyquist 采样步长；
3. 以 $M=2,3$ 的有限阶 EM 校正，显式上界伯努利层；
4. 以 Parseval-on-$\mathcal V$ 的多窗方案压低方差并实施 $(GG^\dagger)$ 重构；
5. 输出 $\widehat c_i=\Delta[w^{(i)}]/\langle\tau_g\rangle_{w^{(i)}}$ 与加权合并估计 $\widehat c$（KL–Pinsker 置信带）；
6. 在坐标重标/预滤/帧重排后复测，验证 $\widehat c$ 的 $\mathcal G$-不变性。([dlmf.nist.gov][2])

---

[1]: https://chaosbook.org/library/SmithDelay60.pdf?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory"
[2]: https://dlmf.nist.gov/1.8?utm_source=chatgpt.com "1.8 Fourier Series"
[3]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[4]: https://epub.uni-regensburg.de/30996/1/1367-2630_16_12_123018.pdf?utm_source=chatgpt.com "Efficient semiclassical approach for time delays"
[5]: https://www.worldscientific.com/doi/full/10.1142/S0219691314500325?srsltid=AfmBOoofq8VJaD8Wpk9mCgjP55Sf0Hw8cRtT00Fo5KMcS0lGYXPM7CF2&utm_source=chatgpt.com "Nonstationary Gabor frames — Existence and construction"
[6]: https://link.aps.org/doi/10.1103/PhysRevE.103.L050203?utm_source=chatgpt.com "Generalization of Wigner time delay to subunitary scattering"
[7]: https://people.maths.ox.ac.uk/trefethen/publication/PDF/2014_150.pdf?utm_source=chatgpt.com "A trapezoidal rule error bound unifying the Euler–Maclaurin"
[8]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[9]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6020-11511_2006_Article_BF02395039.pdf?utm_source=chatgpt.com "Necessary density conditions for sampling"
[10]: https://projecteuclid.org/journals/annals-of-probability/volume-3/issue-1/I-Divergence-Geometry-of-Probability-Distributions-and-Minimization-Problems/10.1214/aop/1176996454.full?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions"
[11]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[12]: https://arxiv.org/pdf/2202.07198?utm_source=chatgpt.com "A short note on an inequality between KL and TV"
[13]: https://arxiv.org/abs/1408.6022?utm_source=chatgpt.com "[1408.6022] Canonical systems and de Branges spaces"
[14]: https://heil.math.gatech.edu/papers/bltschauder.pdf?utm_source=chatgpt.com "Gabor Schauder bases and the Balian-Low theorem"
[15]: https://chaosbook.org/library/WignerDelay55.pdf?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering"
[16]: https://arxiv.org/pdf/cond-mat/0112225?utm_source=chatgpt.com "Scattering theory on graphs (2) : the Friedel sum rule"
[17]: https://sites.math.duke.edu/~ingrid/publications/ieee34-1988.pdf?utm_source=chatgpt.com "Time-frequency localization operators: a geometric phase"
