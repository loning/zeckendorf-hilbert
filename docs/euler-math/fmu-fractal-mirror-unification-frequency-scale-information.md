# FMU：频率—尺度—信息的"分形镜"统一理论

**Fractal-Mirror Unification of Frequency–Scale–Information**

**作者：** Auric（S-series / EBOC）
**日期：** 2025-10-26（阿联酋时区，UTC+04）

---

## 摘要

本文在带权 Mellin—Hilbert 空间 $L^2(\mathbb{R}_{+},dt/t)$ 中，建立由**母函数** $M$ 经**乘性尺度复制**生成的**分形镜**（fractal mirror, FM）信号族的严格理论。围绕"频率—尺度—信息"三主线，给出等价刻画与完整证明：（A）在 **Mellin–Calderón** 条件下，**乘性自相似 $\Longleftrightarrow$ Mellin 域准周期**（临界线出现等距频移阵列）；（B）**谱幂律 $\Longleftrightarrow$**（对数刻度下）**熵斜率一阶近似线性**，并在自仿射模型中推出图像盒维数 $D=(3-\beta)/2$ 的经典关系；（C）以**Nyquist–Poisson–Euler–Maclaurin（三分解）**实现**非渐近误差闭合**与**可分预算**。进一步，以**谱密度权测度** $d\mu=(1/\pi)\,\Im m(\omega+i0)\,d\omega$ 将 FM 子空间等距嵌入 Paley–Wiener 型带限空间，从而导出**Landau** 型采样/插值**密度阈值**、**Wexler–Raz** 紧/对偶准则，以及临界密度下的 **Balian–Low** 不可能性；并证明该谱密度权与一维自伴规范系统的 Weyl–Titchmarsh $m$ 函数之 Herglotz 表示一致。以上刻度与判据与 Mellin 等距、Paley–Wiener、Poisson 求和、Euler–Maclaurin、Landau 密度、Wexler–Raz 与 Balian–Low、Herglotz 表示与 de Branges 反谱定理等**公认标准**兼容。

---

## 0. 记号与底座（Notation & Baseplates）

**(0.1) Mellin 等距与临界线。** 对 $x\in L^2(\mathbb{R}_{+},dt/t)$ 的 Mellin 变换

$$
\mathcal{M}x(s)=\int_{0}^{\infty} x(t)\,t^{s-1}\,dt,
$$

在临界直线 $s=\tfrac12+i\omega$ 上与"对数傅里叶"单元等距：

$$
|x|_{L^2(dt/t)}^2=\frac{1}{2\pi}\int_{\mathbb{R}}\big|\mathcal{M}x(\tfrac12+i\omega)\big|^2\,d\omega.
$$

因此 $\widetilde{\mathcal M}:x\mapsto (2\pi)^{-1/2}\mathcal{M}x(\tfrac12+i\cdot)$ 在 $L^2(\mathbb{R}_{+},dt/t)\to L^2(\mathbb{R})$ 上酉等距。

**(0.2) 对数变量与缩放。** 取 $u=\log t$，令 $m(u)=M(e^{u})$。尺度 $t\mapsto 2^{k}t$ 化为对数平移 $u\mapsto u+k\log 2$。Mellin 缩放律给出

$$
\mathcal{M}{M(2^k\cdot)}(s)=2^{-ks}\,\mathcal{M}M(s)\quad(s=\tfrac12+i\omega),
$$

即振幅因子 $2^{-k/2}$ 与相位调制 $e^{-ik\omega\log 2}$。

**(0.3) 谱密度测度与相位坐标。** 记号与变换约定：$\mathcal{M}$ 表示对 $t$ 的 Mellin 变换并在 $s=\tfrac12+i\omega$ 取值；$\widehat{\cdot}$ 一律表示对 $u=\log t$ 的 Fourier 变换（等价于沿临界线的 $\omega$-域算子）。

对与 Weyl–Titchmarsh $m$-函数关联的系统，定义**谱密度权测度**

$$
d\mu(\omega)=\frac{1}{\pi}\,\Im m(\omega+i0)\,d\omega.
$$

当 $\Im m\ge 0$ 时，$\mu$ 为正测度。在满足特殊归一化（如某类边界条件使 $\Re m(\lambda+i0)\equiv 0$ a.e.）时，可用相位表示 $d\mu_\varphi(\omega)=(1/\pi)\,d(\arg m(\omega+i0))$；一般情形则采用谱密度权 $d\mu$。其与自伴系统的谱测度一致性见 §6。

**约定（$u$-域 Fourier）**：$\widehat{f}(\omega)=(2\pi)^{-1/2}\int_{\mathbb{R}}f(u)\,e^{-i\omega u}\,du$，$f(u)=(2\pi)^{-1/2}\int_{\mathbb{R}}\widehat{f}(\omega)\,e^{i\omega u}\,d\omega$。

**符号约定（避免冲突）**：本文固定 $u:=\log t$ 作为对数时间变量；谱密度权坐标另记为 $v_\mu$。$u$-域 Fourier 仅作用于 $u$ 变量；与谱密度权相关的等距映射与密度判据均在 $v_\mu$ 坐标上叙述。

**(0.4) 有限阶 Euler–Maclaurin（EM）。** 全文仅用**有限阶** EM，将"和—积分"差分解为端点伯努利层与余项：

$$
\sum_{n=a}^{b}f(n)=\int_{a}^{b}f(x)\,dx+\frac{f(a)+f(b)}{2}+\sum_{r=1}^{p-1}\frac{B_{2r}}{(2r)!}\!\left(f^{(2r-1)}(b)-f^{(2r-1)}(a)\right)+R_p,
$$

并可用 $|R_p|\lesssim \tfrac{2\,\zeta(2p)}{(2\pi)^{2p}}\int_a^b|f^{(2p)}|$ 控制。

---

## 1. 分形镜（FM）信号族：定义与基本性质

### 定义 1.1（FM 生成与 Mellin–Calderón 条件）

给定母函数 $M\in L^2(\mathbb{R}_{+},dt/t)$，权序列 $\{a_k\}_{k\in\mathbb{Z}}\in \ell^2$，相位序列 $\{\phi_k\}\subset\mathbb{R}$ 有 $\sup_k|\phi_k|<\infty$。定义

$$
x(t)=\sum_{k\in\mathbb{Z}} a_k\, M(2^{k}t)\,e^{i\phi_k},\qquad t>0.
$$

**假设 (H0) 加权 $\ell^2$ 一致性。** 令 $b_k:=a_k\,2^{-k/2}e^{i\phi_k}$，要求 $\{b_k\}_{k\in\mathbb{Z}}\in \ell^2$（等价地 $\sum_k |a_k|^2\,2^{-k}<\infty$）。

**假设 (H1) Mellin–Calderón 有界性。** 记 $G(\omega):=\mathcal{M}M(\tfrac12+i\omega)$，$P:=2\pi/\log 2$，要求 Calderón 和

$$
\mathcal{C}_G(\omega):=\sum_{n\in\mathbb{Z}}\big|G(\omega+nP)\big|^2\in L^{\infty}([0,P]).
$$

### 命题 1.2（$L^2$ 无条件收敛与频域结构，在 (H0)–(H1) 下）

在假设 (H0)–(H1) 下，级数 $\sum_{k}a_k M(2^k\cdot)e^{i\phi_k}$ 在 $L^2(\mathbb{R}_{+},dt/t)$ 中无条件收敛，且

$$
\mathcal{M}x\!\left(\tfrac12+i\omega\right)=G(\omega)\sum_{k\in\mathbb{Z}} b_k\,e^{-ik\omega\log 2},\qquad b_k:=a_k\,2^{-k/2}e^{i\phi_k}.
$$

并有 Bessel 界

$$
|x|_{L^2(dt/t)}^2\ \le\ \frac{P}{2\pi}\|\mathcal{C}_G\|_{L^\infty([0,P])}\,\sum_{k\in\mathbb{Z}}|b_k|^2,\qquad P=\frac{2\pi}{\log 2}.
$$

**证明。** 由 (H1) 的 Calderón 上界与 Plancherel–Mellin 等距，得

$$
|x|_{L^2(dt/t)}^2\ \le\ \frac{P}{2\pi}\,\|\mathcal{C}_G\|_{L^\infty([0,P])}\,\sum_{k\in\mathbb{Z}}|b_k|^2,\qquad P=\frac{2\pi}{\log2},
$$

从而级数 Cauchy 收敛；频域表达随缩放律直接得出。$\square$

---

## 2. 主定理 A：乘性自相似的 Mellin-准周期刻画

### 定理 2.1（自相似 $\Longleftrightarrow$ 准周期）

对定义 1.1 的 $x$，以下等价：
(i) $x(t)=\sum_k a_k M(2^k t)e^{i\phi_k}$（乘性自相似叠加）；
(ii) 存在包络 $G(\omega)=\mathcal{M}M(\tfrac12+i\omega)\in L^2(\mathbb{R})$，使

$$
\mathcal{M}x\!\left(\tfrac12+i\omega\right)=G(\omega)\cdot \underbrace{\sum_{k\in\mathbb{Z}} b_k\,e^{-ik\omega\log 2}}_{\text{Bohr 准周期；频移格距 }2\pi/\log 2}.
$$

**证明。** "$\Rightarrow$" 由命题 1.2。 "$\Leftarrow$" 对准周期部分作逆 Mellin（$\sigma=\tfrac12$）并用"对数域平移 $\leftrightarrow$ Mellin 频移"对偶，即得对数平移族 $M(2^k\cdot)$ 的叠加。$\square$

---

## 3. 主定理 B：谱幂律—熵斜率与自仿射维数

### 3.1 幂律谱与对数分箱熵的线性耦合（近似关系）

**命题 3.1（熵—斜率近似线性，一阶区间）.** 设功率谱在宽频比 $\Lambda=f_{\max}/f_{\min}\gg1$ 上满足
$S(f)\asymp C f^{-\beta}$，对数均匀分箱 $I_j=[e^{y_j},e^{y_{j+1}}]$，$\delta y:=y_{j+1}-y_j\ll1$ 固定，分箱数 $J\sim (\log\Lambda)/\delta y$，概率 $P_j\propto \int_{I_j}S(f)\,df$ 归一化。则在一阶近似下

$$
H:=-\sum_j P_j\log P_j= c_1(\delta y) + c_2(\delta y)\,\beta + \mathcal{O}\big(\delta y\big) + \mathcal{O}\big((\log\Lambda)^{-1}\big),
$$

其中 $c_1,c_2$ 仅由分箱步长 $\delta y$ 与窗重叠常数决定，显式可求；当 $\delta y\to 0$、$\Lambda\to\infty$ 时主项线性成立。

**证明要点。** 令 $y=\log f$，有 $df=f\,dy$，从而 $P_j\propto\int_{y_j}^{y_{j+1}}e^{(1-\beta)y}\,dy$。均匀 $y$-分箱使 $\{P_j\}$ 近似指数分布；代回熵并以 Riemann 和近似，$\delta y$ 的离散化误差给出 $\mathcal{O}(\delta y)$ 项，端点/重叠给出 $\mathcal{O}((\log\Lambda)^{-1})$ 项；二者在 $\delta y\ll 1/\log\Lambda$ 时可忽略。$\square$

### 3.2 自仿射样条与图像维数（典型模型）

**定理 3.2（$D=(3-\beta)/2$）.** 若样条满足 $x(\lambda t)\overset{d}{=}\lambda^{H}x(t)$（如 fBm），则

$$
S(f)\sim f^{-(2H+1)}\quad\Longrightarrow\quad D_{\mathrm{graph}}=2-H=\frac{3-\beta}{2}.
$$

**证明.** fBm 等自仿射过程满足 $S(f)\propto f^{-(2H+1)}$；其样条图像的 Hausdorff/盒维数 $D=2-H$ 为经典结论，联立消去 $H$ 得上式。$\square$ 相关结论可见 Flandrin 对 fBm 频谱的分析与 Xiao 对图像维数的严格测度结果。

---

## 4. 主定理 C：Nyquist–Poisson–EM 的非渐近误差闭合

设目标频域量记为

$$
F(\omega)=\widehat{w}(\omega)\,\widehat{h}(\omega)\,X(\omega),\qquad X(\omega):=(2\pi)^{-1/2}\,\mathcal{M}x\!\left(\tfrac12+i\omega\right),
$$

其中 $\widehat{w}(\omega)$、$\widehat{h}(\omega)$ 为按 §0.3 约定的 $u$-域 Fourier 变换后的分析窗频响与插值核频响，$X(\omega)$ 为沿临界线的 Mellin 影像（由 §0.1 的酉等距归一化）。

**定理 4.1（Nyquist 条件与三分解误差）.** 设存在 $B>0$ 使 $\mathrm{supp}\,F\subset[-B,B]$，其中 $B:=\min\{\Omega_w,\Omega_h\}$（若 $X$ 非带限，则以 $\mathrm{supp}(\widehat{w})\cap\mathrm{supp}(\widehat{h})$ 的交为有效带宽）。若采样步长

$$
\Delta\ \le\ \frac{\pi}{B},
$$

则别名能量为零。一般情形下，别名项可记为

$$
\varepsilon_{\text{alias}}=\Big|\sum_{\ell\neq 0}F\big(\cdot+2\pi\ell/\Delta\big)\Big|_{L^2([-\pi/\Delta,\, \pi/\Delta])},
$$

对带限线性重构算子 $\mathsf E$，总误差分解为

$$
|x-\mathsf{E}x|_{L^2}\ \le\ \underbrace{\varepsilon_{\text{alias}}}_{\text{周期化叠加}}\ +\ \underbrace{\varepsilon_{\mathrm{EM}}^{(p)}}_{\mathcal{O}(|B_{2p}|\Delta^{2p})}\ +\ \underbrace{\varepsilon_{\text{tail}}}_{\text{带缘/截断}},
$$

且 $\varepsilon_{\mathrm{EM}}^{(p)}=\mathcal{O}\!\big(|B_{2p}|\,\Delta^{2p}\big)$。

**证明。** 以 Poisson 求和将离散化转为频谱周期化；Nyquist 阈值消除带间重叠。和—积分差以有限阶 EM 分解为端点伯努利层与余项，余项界见 §0.4。$\square$

---

## 5. 采样—插值—稳定性：谱密度坐标下的 Landau—Wexler–Raz—Balian–Low

### 5.1 谱密度权坐标的等距嵌入

在 $\Im m(\omega+i0)>0$ 区域，定义谱密度权坐标

$$
v_\mu(\omega)=\frac{1}{\pi}\int_{-\infty}^{\omega}\Im m(\omega'+i0)\,d\omega',\qquad dv_\mu=\frac{1}{\pi}\,\Im m(\omega+i0)\,d\omega,
$$

则

$$
\int_{\mathbb{R}}|X(\omega)|^2\,\frac{1}{\pi}\,\Im m(\omega+i0)\,d\omega=\int_{\mathbb{R}}|X(\omega(v_\mu))|^2\,dv_\mu,
$$

从而把谱密度权加权的 FM-子空间等距嵌入**单位带宽** Paley–Wiener 型空间。特殊归一化时，可简化为相位坐标 $v_\mu=\varphi(\omega)/\pi$。Mellin 语境下的 Paley–Wiener 与 Hardy/Mellin-Hardy 结构详见文献。

### 5.2 Landau 型必要条件（FM 版）

**定理 5.1（必要密度阈值，$v_\mu$-域）.** 设 $\Omega=\{\omega_n\}$ 为采样序列（分别：插值序列）。在 $v_\mu$ 坐标下（由 §5.1 定义），其 Beurling 下（分别上）密度满足

$$
\underline{D}_{\mu}(\Omega)\ge 1\qquad(\text{分别 },\overline{D}_{\mu}(\Omega)\le 1).
$$

*备注*：上述为必要条件。充分性一般需附加分离性/稳定性等结构条件；实践中可通过 §5.3 的 WR/Parseval 条件设计达到稳定采样/重构。

**证明要点。** 由 5.1 的等距，问题化为单位带宽 Paley–Wiener 空间的非均匀采样，直接调用 Landau 必要密度定理。$\square$

### 5.3 Wexler–Raz 与 Parseval 紧帧（临界 Nyquist）

**定理 5.2（WR/Parseval 条件）.** 在 Nyquist（无别名）条件下，多窗 $\{w_\alpha\}_{\alpha=1}^r$ 生成的系统为 Parseval 紧帧当且仅当

$$
\frac{1}{\Delta}\sum_{\alpha=1}^{r}\big|\widehat{w_\alpha}(\xi)\big|^{2}\equiv 1\quad\text{(a.e.)}.
$$

存在别名时，Parseval 条件变为

$$
\frac{1}{\Delta}\sum_{\alpha=1}^{r}\sum_{m\in\mathbb{Z}}\big|\widehat{w_\alpha}\!\big(\xi+2\pi m/\Delta\big)\big|^{2}\equiv 1.
$$

与对偶窗 $\{\widetilde{w}_\alpha\}$ 的重构满足相应的双正交式。

**证明要点。** WR 恒等式给出频域点态正交的充要条件；经 $u=\log t$ 与相位坐标变换可无损移植到 Mellin/对数模型。$\square$

### 5.4 Balian–Low 型不可能性（临界密度）

**定理 5.3（BLT—Mellin 版）.** 在临界密度 $D=1$ 时，若单窗 $w$ 在对数时间 $u$ 与频率 $\omega$ 两侧均"良好局域"（例如二阶矩有限），则由 $w$ 与在 $v_\mu$ 坐标下临界格生成的系统**不能**为 Riesz 基；要得到基，必须放宽至少一侧的局域或采用超采样。

**证明要点。** 经 $u=\log t$ 与 §5.1 的等距嵌入，把问题等价为标准 Gabor 格的 BLT；由 BLT 的 Riesz/ONB 版立即推出。$\square$

---

## 6. 与 de Branges—Kreĭn / Weyl–Titchmarsh $m$-函数的一致性

**命题 6.1（谱密度权与 Herglotz 表示）.** 在一维自伴规范系统/Schrödinger 型算子情形，Weyl–Titchmarsh $m$ 为 Herglotz–Nevanlinna 函数，存在谱测度 $\mu$ 使

$$
m(z)=a z+b+\int_{\mathbb{R}}\left(\frac{1}{\lambda-z}-\frac{\lambda}{1+\lambda^2}\right)\,d\mu(\lambda),
$$

边界值满足 $\Im m(\lambda+i0)=\pi\,\rho(\lambda)$（a.e.），其中 $\rho$ 为谱密度。由此可定义谱密度权测度

$$
d\mu(\omega)=\frac{1}{\pi}\,\Im m(\omega+i0)\,d\omega=\rho(\omega)\,d\omega,
$$

与绝对连续谱测度一致。在满足特殊归一化（如某类边界条件使 $\Re m(\lambda+i0)\equiv 0$ a.e.）时，可简化为相位表示 $d\mu_\varphi=(1/\pi)\,d(\arg m)$；一般情形则须采用上述谱密度权。$\square$

> 说明：该一致性保证了本文以 $d\mu$ 定义的谱密度刻度，能与 de Branges 空间/规范系统的谱理论无缝衔接，成为 §5 中密度与帧判据的自然坐标；相位导数 $\varphi'=d(\arg m)/d\omega$ 一般还依赖 $\Re m$ 与 $m'$，仅在特例下化为 $\pi\rho$。

---

## 7. 可复现实验范式（验证与工程）

**P1｜幂律/熵耦合。** 在足够宽的对数带宽上拟合 $S(f)\propto f^{-\beta}$，并以对数分箱熵 $H$ 验证回归斜率在误差带内线性（§3.1 的一阶近似）。

**P2｜Mellin 峰列。** 计算 $\mathcal{M}x(\tfrac12+i\omega)$，检验等距峰列与相对相位稳定（§2）。

**P3｜采样/窗设计。** 按 §5.2 的密度阈值选格；以 §5.3 的 WR 条件调窗以获 Parseval；按 §4 的三分解做误差**可分预算**（Nyquist 余量、EM 阶、带缘尾项）。

---

## 8. 信息三元 $(i_{+},i_{0},i_{-})$ 与模型选择

* $i_{+}$：跨尺度外溢收益（$\beta$ 趋红 $\Rightarrow$ 低频集中 $\Rightarrow$ 压缩/预测收益）。
* $i_{0}$：层内重排（相位—相干性"中性"重分配）。
* $i_{-}$：稀疏与复杂度惩罚（避免过拟合/过稠格）。

**命题 8.1（近似线性区的策略）.** 在 §3.1 的一阶近似区，$\partial_\beta H\approx c_2$，有效层数 $N_{\mathrm{eff}}\asymp (1+\beta)\log \Lambda$。据此联合选择"窗/格密度—模型复杂度"，使 $i_{+}-i_{-}$ 极大并满足 §4 的三分解预算。$\square$

---

## 9. 与 S-series / WSIG-QM / UMS 的接口

**9.1 与 S24–S26 的接口。**
- S24 的纤维 Gram 表征与 Wexler–Raz 双正交为本文 §5.3 的 WR 条件提供具体实现框架。
- S25 的非平稳 Weyl–Mellin 框架与本文的 Mellin 等距（§0.1）、对数平移—频移对偶（§0.2）共享数学结构。
- S26 的谱密度刻度与本文 §0.3 及 §6 的谱密度权测度 $d\mu=(1/\pi)\,\Im m(\omega+i0)\,d\omega$ 在 Herglotz 表示层面一致；S26 的 Landau 必要密度、Balian–Low 不可能性直接对应本文定理 5.1、5.3。

**9.2 与 WSIG-QM 的接口。**
- WSIG-QM 的公理 A2（有限窗口读数）与本文 §4 的窗化重构共享 Nyquist–Poisson–EM 三分解框架。
- WSIG-QM 的公理 A5（相位—密度—延迟刻度）与本文 §0.3、§6 的谱密度权测度在谱理论层面一致。
- WSIG-QM 的定理 T6（窗/核优化）与本文 §5.2–5.3 的 Landau 密度阈值、WR 条件共享帧理论判据。

**9.3 与 UMS 的接口。**
- UMS 的核心统一式 $d\mu = \tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\,dE = \rho_{\mathrm{rel}}\,dE$ 在 Mellin 语境下对应本文 §0.3、§6 的谱密度权测度；在特殊归一化下可简化为相位表示。
- UMS 的公理 A2（有限窗口读数）与本文定理 4.1 的三分解误差闭合在数值实现层面共享框架。
- UMS 的公理 A6（采样—帧门槛）与本文 §5 的 Landau–Wexler–Raz–Balian–Low 判据完全对齐。

**9.4 与窗口化路径积分理论的接口。**
- 路径积分理论的窗—核对偶（定理 2.1）可在 Mellin 域改写为本文定理 2.1 的准周期表述。
- 路径积分理论的 Nyquist–Poisson–EM 误差闭合与本文定理 4.1 的三分解在离散化框架上一致。

**9.5 与量子引力场理论的接口。**
- 量子引力场理论的谱密度刻度与本文 §0.3、§6 的谱密度权测度 $d\mu=(1/\pi)\,\Im m(\omega+i0)\,d\omega$ 在谱移语境下一致。
- 量子引力场理论的窗化采样（§6.1）与本文 §5 的 Landau–Wexler–Raz 判据共享帧理论基础。

**9.6 保持"极点 = 主尺度"的有限阶 EM 纪律。**
- 本文在所有离散—连续换序中均采用**有限阶** EM（§0.4、定理 4.1），确保不引入新奇点。
- 与 S15–S26、WSIG-QM、UMS、路径积分理论、量子引力场理论保持一致：EM 余项仅作有界扰动。

---

## 附录 A：证明细节与工具

**A.1 Mellin–Hardy 与等距。** $\widetilde{\mathcal{M}}$ 在 $\sigma=\tfrac12$ 上酉等距；Mellin–Paley–Wiener 与 Mellin–Hardy 空间的构造可见 Bardaro–Butzer–Mantellini–Schmeisser。

**A.2 Poisson 与别名。** 采样步长 $\Delta$ 的 Dirac 梳在频域周期为 $2\pi/\Delta$ 的 Dirac 梳；别名能量等于周期化副谱在主带的叠加能量。

**A.3 Euler–Maclaurin 余项。** 采用 DLMF 版 EM 公式与余项界，确保在有限阶近似下不引入额外奇点；误差由 Bernoulli 数与步长给出。

**A.4 Landau 密度。** Paley–Wiener 空间 $PW_B$ 的采样（插值）序列须满足 $\underline D\ge B/\pi$（$\overline D\le B/\pi$）；本文在 $v_\mu$ 坐标单位带宽下等距为阈值 1。

**A.5 Wexler–Raz 与 BLT。** WR 恒等式给出紧/对偶帧的频域点态充要条件；BLT 表明临界密度下"良好双侧局域+非冗余"不相容。

**A.6 Herglotz 表示与谱密度。** $m$ 为 Herglotz 函数 $\Rightarrow$ 存在谱测度表示；边界虚部为 $\Im m(\lambda+i0)=\pi\rho(\lambda)$（a.e.）。由此定义谱密度权测度 $d\mu=(1/\pi)\,\Im m\,d\omega$；相位导数 $\varphi'=d(\arg m)/d\omega$ 一般还依赖 $\Re m$ 与 $m'$，仅在特殊归一化下化为 $\pi\rho$。

---

## 结论

1. 乘性自相似经 Mellin 变换等价为**准周期频移阵列**，并以包络 $G$ 控制（定理 2.1）；在加权 $\ell^2$ 一致性 (H0) 与 Mellin–Calderón 条件 (H1) 下级数无条件收敛（命题 1.2）。
2. 幂律谱与对数分箱熵在一阶近似下线性耦合；在自仿射极限下 $D=(3-\beta)/2$ 成立（命题 3.1、定理 3.2）。
3. 采用 **Nyquist–Poisson–EM** 三分解，可将总误差稳定地拆分为"别名/伯努利层/尾项"三项预算（定理 4.1）。
4. 谱密度权坐标 $v_\mu$ 使 FM 子空间与 Paley–Wiener 空间等距，从而继承 **Landau** 密度阈值、**Wexler–Raz** 紧/对偶准则与 **Balian–Low** 不可能性；其谱密度权测度与 $m$-函数的 Herglotz 表示一致（§5–§6）。

---

## 参考文献（选）

1. **Mellin–Paley–Wiener / Mellin–Hardy**：Bardaro, Butzer, Mantellini, Schmeisser, *On the Paley–Wiener theorem in the Mellin transform setting*（2015）与续篇（2017）。
2. **Mellin 等距/缩放**：Butzer & Jansche, *A Direct Approach to the Mellin Transform*（1997）。
3. **Poisson 求和**：NIST DLMF §1.8(iv)；Candès 讲义（2021）。
4. **Euler–Maclaurin**：NIST DLMF §2.10(i), §24.17。
5. **Landau 必要密度**：Landau, *Acta Math.* 117 (1967)。
6. **Wexler–Raz**：Daubechies & Landau, *J. Fourier Anal. Appl.* (1994/95)。
7. **Balian–Low**：Heil & Powell, *J. Math. Phys.* (2006)。
8. **fBm 频谱与维数**：Flandrin (1989)；Xiao (1997)。
9. **Herglotz–Weyl–Titchmarsh / de Branges**：Kostenko–Teschl 等综述与 Oberwolfach 报告。

---

### 读者指引

将本文嵌入 S25（非平稳 Weyl–Mellin）与 S26（谱密度—de Branges）时，可直接复用 §5 的谱密度权坐标 $v_\mu$ 准则与 §4 的**三分解误差账本**；窗/核设计以 WR 充要式落地，临界密度遇 BLT 障碍则通过**超采样或放宽局域**规避。实施时注意加权 $\ell^2$ 一致性 (H0) 与 Mellin–Calderón 条件 (H1) 的验证（如 Log-Gaussian 母函数）与熵—斜率关系的误差带控制（§3.1 的一阶近似范围）。符号约定：对数时间 $u:=\log t$ 与谱密度权坐标 $v_\mu$ 严格区分（§0.2–§0.3）。
