# S27. 局部化算子、Carleson 测度与 Weyl 定律

**—— de Branges–Mellin 框架中的核论证、迹恒等与非渐近窗化误差**

Version: 1.12

## 摘要（定性）

在以 Hermite–Biehler 函数 $E$ 生成的 de Branges 空间 $\mathcal H(E)$ 中，本文建立三条互锁结构：其一，用**核论证（reproducing-kernel thesis, RKT）**刻画 $\mathcal H(E)$ 的上/下 Carleson 测度，并在"相位导数测度"下给出**采样/插值的密度律**；其二，给出**局部化（Toeplitz/Berezin）算子**的**迹恒等**与**Weyl 型谱分布**（弱极限），把"符号 $\times$ 窗 $\times$ 相位密度"的积分等同于算子迹；其三，数值实现严格遵循**有限阶** Euler–Maclaurin（EM）纪律，误差由"**别名（Poisson）+ 伯努利层（EM 余项）+ 截断**"三项**非渐近**封顶。上述结论与 de Branges 核对角公式、Weyl–Titchmarsh $m$-函数的相位—密度词典一致，并可与散射论中的 Birman–Kreĭn/相移公式互相接口。

---

## 0. 设定与记号

令 $E$ 为 Hermite–Biehler（HB）函数，$\mathcal H(E)$ 为对应的 de Branges 空间，其再生核 $K(z,w)$ 满足 $F(t)=\langle F, K(\cdot,t)\rangle_{\mathcal H(E)}$。写

$$
E(x)=|E(x)|e^{-i\varphi(x)},\qquad U(x):=\frac{E^\sharp(x)}{E(x)}=e^{2i\varphi(x)},\qquad x\in\mathbb R.
$$

其中 $E^\sharp(z):=\overline{E(\overline z)}$。

记 Weyl–Titchmarsh $m$-函数之边界值 $\Im m(x+i0)$ 与谱测度 $\mu$ 的绝对连续密度 $\rho(x)=\frac{d\mu_{\rm ac}}{dx}(x)$。标准恒等式为

$$
\boxed{\ \frac{K(x,x)}{|E(x)|^2}=\frac{\varphi'(x)}{\pi}=\rho(x)\ }\quad\text{(a.e.\ $x\in\mathbb R$)},
$$

亦即"核对角 = 相位导数 = 相对谱密度"。

以**相位密度测度**作为基准计量：

$$
d\nu_0(x):=\frac{\varphi'(x)}{\pi}\,dx.
$$

数值实现中，窗函数一律取**偶**、$0\le w\le 1$、$w(0)=1$，并满足 $w\in C^p(\mathbb R)$（$p\ge2$ 与 §3 的 EM 阶次一致），且尺度化 $w_R(t):=w(t/R)$。据此 $w_R(t)$ 满足 $0\le w_R\le 1$ 且当 $R\to\infty$ 时在每个有界区间上 $w_R\to 1$。离散—连续换序只使用**有限阶** EM 公式（余项显式可积表达），Poisson 召回"别名"项；三者合称"Nyquist–Poisson–EM 三分解"。

**记号约定**：写 $X\lesssim Y$ 表示存在常数 $C>0$，其仅依赖于（A）中的 Doubling 常数、离散序列的分离常数、固定 EM 阶次 $p$ 及所选窗族的固定正则性/支配常数，而**与** $(R,\Delta,T)$、区间 $I$ 与具体符号 $a$ **无关**；$X\gtrsim Y$ 同理；$X\simeq Y$ 指双边界。

> **说明（散射接口）**：在散射谱模型下 $\rho(x)=\pi^{-1}\Im m(x+i0)$ 即相移导数/谱移函数的密度表述，与 Birman–Kreĭn 轨迹公式兼容；近年在广义背景下仍有活跃发展。

---

## 1. Carleson 测度与核论证（RKT）

### 1.1 定义与基准

对正测度 $\nu$（$\mathbb R$ 上局部有限），称其为 $\mathcal H(E)$ 的**上 Carleson 测度**，若

$$
\int_{\mathbb R}|F(x)|^2\,d\nu(x)\ \le\ C\,\|F\|_{\mathcal H(E)}^2\qquad(\forall F\in\mathcal H(E)).
$$

称 $\nu$ 为**下 Carleson（逆 Carleson）**，若

$$
c\,\|F\|_{\mathcal H(E)}^2\ \le\ \int_{\mathbb R}|F(x)|^2\,d\nu(x)\qquad(\forall F\in\mathcal H(E)).
$$

基准测度 $d\nu_0=\frac{\varphi'}{\pi}dx$ 与核对角通过上式联动，见 §0。

### 1.2 上 Carleson的核测试（充分必要）

记 $K_t:=K(\cdot,t)$，$\,k_t:=K_t/\sqrt{K(t,t)}$。

**定理 1.1（RKT：上 Carleson $\Longleftrightarrow$ 核测试）.**
**假设（A）**：$\varphi'(x)\,dx$ 为 Doubling（例如关联内函数为一成分的典型情形）。

则对一切正测度 $\nu$，以下等价：

$$
\begin{aligned}
\text{(i)}\ &\ \nu\ \text{为上 Carleson；}\\
\text{(ii)}\ &\ \sup_{t\in\mathbb R}\ \int_{\mathbb R}\frac{|K(x,t)|^2}{K(t,t)}\,d\nu(x)\ <\ \infty.
\end{aligned}
$$

**若（A）不成立**，则 (i)$\Rightarrow$(ii) 仍成立，而反向蕴含一般不保证。

**证明要点（修订）.** 设嵌入 $J:\mathcal H(E)\to L^2(\nu)$。在 (ii) 下，定义
$$
Q(F,G):=\int_{\mathbb R}\langle F,k_x\rangle\,\overline{\langle G,k_x\rangle}\,d\nu(x)\qquad(F,G\in\mathcal H(E)),
$$
则 $Q$ 为有界正半双线性型，故存在唯一正有界算子 $S\in\mathcal B(\mathcal H(E))$ 使得 $\langle SF,G\rangle=Q(F,G)$。进一步可得 $J^*J=S$，并由此
$$
\|J\|^{2}=\|S\|=\sup_{\|f\|=1}\int_{\mathbb R}|\langle f,k_x\rangle|^{2}\,d\nu(x).
$$
在（A）下，$\{k_t\}$ 对应 $d\nu_0=\tfrac{\varphi'}{\pi}dx$ 构成连续帧，$\nu$ 的核测试控制嵌入算子 $J$ 的范数，故得等价；一般情形仅得必要性。∎

> **注**：在 $\varphi'(x)\,dx$ 为**Doubling** 的情形，真实轴采样/插值可得**密度刻画**，见 §4。

### 1.3 下 Carleson与逆核测试

**定理 1.2（逆 Carleson = 逆核测试，修订）.**
若 $\nu$ 为正测度且在每个有界区间内有限（可离散/绝对连续/混合），则存在 $c>0$ 使

$$
\int_{\mathbb R}\frac{|K(x,t)|^2}{K(t,t)}\,d\nu(x)\ \ge\ c\qquad(\forall t\in\mathbb R)
$$

当且仅当 $\nu$ 为下 Carleson。

**证略.** $J:\mathcal H(E)\to L^2(\nu)$ 有下界 $\Leftrightarrow\ S=\int |k_x\rangle\langle k_x|\,d\nu(x)\ge cI$。以 $F=k_t$ 代入即得上式；反向同理。∎

### 1.4 离散测度与分离序列

设 $X=\{x_n\}\subset\mathbb R$ 在相位度量 $d_\varphi(x,y):=|\varphi(x)-\varphi(y)|$ 下**分离**，写
$d\nu_X:=\sum_n \omega_n\,\delta_{x_n}$。
由 1.1–1.2：$\nu_X$ 上 Carleson $\Rightarrow$ $\{\sqrt{\omega_n}k_{x_n}\}$ 为 Bessel 系；上下皆成立 $\Leftrightarrow$ $\{\sqrt{\omega_n}k_{x_n}\}$ 为框架（即 $X$ 为采样集）；下 Carleson $\Rightarrow$ 下框架。此与模型子空间/Dirichlet-型空间中的结论并行。

---

## 2. 局部化算子：迹恒等与 Weyl 型谱分布

### 2.1 恒等分解与对角核

由 de Branges 边界模型 $\langle F,G\rangle=\int F(x)\overline{G(x)}\,|E(x)|^{-2}dx$ 与 §0 核对角式，得到

$$
\langle F,G\rangle_{\mathcal H(E)}
=\int_{\mathbb R}\frac{\langle F,K(\cdot,x)\rangle\,\overline{\langle G,K(\cdot,x)\rangle}}{K(x,x)}\ \frac{\varphi'(x)}{\pi}\,dx.\tag{2.1}
$$

$$
\boxed{\ \int_{\mathbb R}|k_x\rangle\langle k_x|\,d\nu_0(x)\ =\ I\ },\qquad d\nu_0(x)=\tfrac{\varphi'(x)}{\pi}\,dx.\tag{2.2}
$$

### 2.2 定义（局部化/Toeplitz–Berezin 型算子）

取有界**实值符号** $a\in L^\infty(\mathbb R)$ 与**实值偶窗** $w_R$，定义

$$
T_{a,R}\ :=\ \int_{\mathbb R} a(x)\,w_R(x)\ \frac{|K(\cdot,x)\rangle\langle K(\cdot,x)|}{K(x,x)}\ \frac{\varphi'(x)}{\pi}\,dx.
$$

则 $T_{a,R}$ 自伴。**若** $a\ge 0$ 且 $w_R\ge 0$（a.e.）**则** $T_{a,R}$ 为**正**（反向一般不保证）。
**若再有** $a,w_R\ge 0$，则 $T_{a,R}$ **迹类当且仅当** $a\,w_R\in L^1(d\nu_0)$，且 $\operatorname{Tr}T_{a,R}=\int a\,w_R\,d\nu_0$。
**在一般实值（可变号）情形**：$|a|\,w_R\in L^1(d\nu_0)\Rightarrow T_{a,R}\in\mathcal S_1$，且 $\operatorname{Tr}T_{a,R}=\int a(x)\,w_R(x)\,d\nu_0(x)$。

**在 §2.4–§2.5 中默认** $0\le a\le 1$、$0\le w_R\le 1$ 以合法使用 Ky Fan 与 Lidskii。

在 $0\le a\le 1$、$0\le w_R\le 1$ 下，由 (2.2) 得对任意 $F\in\mathcal H(E)$，
$$
0\ \le\ \langle T_{a,R}F,F\rangle
=\int_{\mathbb R} a(x)\,w_R(x)\,|\langle F,k_x\rangle|^2\,d\nu_0(x)\ \le\ \int_{\mathbb R}|\langle F,k_x\rangle|^2\,d\nu_0(x)=\|F\|^2,
$$
故 $0\le T_{a,R}\le I$，从而 $\lambda_j(T_{a,R})\in[0,1]$。

### 2.3 迹恒等

**定理 2.1（迹恒等）.** 若 $T_{a,R}$ 迹类，则

$$
\boxed{\ \operatorname{Tr}\,T_{a,R}\ =\ \int_{\mathbb R} a(x)\,w_R(x)\ \frac{\varphi'(x)}{\pi}\,dx\ }.\tag{2.3}
$$

**证明（修订）.** 当 $a,w_R\ge 0$ 时，$|k_x\rangle\langle k_x|$ 的迹为 1（此处 $|k_x\rangle:=K(\cdot,x)/\sqrt{K(x,x)}$），利用单调收敛与分解 $T_{a,R}=\int f(x)\,|k_x\rangle\langle k_x|\,d\nu_0$ 得 $\operatorname{Tr}T_{a,R}=\int f\,d\nu_0$。一般实值时，在 $|a|\,w_R\in L^1(d\nu_0)$ 下，$x\mapsto f(x)\,|k_x\rangle\langle k_x|$ 在迹范数下可积，故可按 Bochner/Fubini 换序并得同式。∎

### 2.4 Ky Fan 原理与层集上界

记 $\{\lambda_j(T_{a,R})\}$ 为特征值降序列。

**命题 2.2（Ky Fan 上界——修订）.**
*假设 $T_{a,R}\ge 0$。* 记 $f(x):=a(x)\,w_R(x)$，并以 $d\nu_0$ 为参照定义其非增重排 $f^*$ 于区间 $[0,M_R]$，其中 $M_R:=\int w_R\,\frac{\varphi'}{\pi}dx$。则对任意 $N\in\mathbb N$，

$$
\sum_{j=1}^{N} \lambda_j(T_{a,R})\ \le\ \int_{0}^{\min\{N,M_R\}} f^*(t)\,dt.
$$

**证意.** 用分解 $T_{a,R}=\int f(x)\,|k_x\rangle\langle k_x|\,d\nu_0$ 与连续帧的分辨率恒等式，结合 Ky Fan 最大化原理与 Hardy–Littlewood 重排不等式得之。∎

### 2.5 Weyl 型谱分布（弱极限）

**定理 2.3（Weyl 定律，弱收敛版）.** *在 $0\le a\le 1$、$0\le w_R\le 1$ 且 $M_R\to\infty$ 下成立。* 设 $a\in L^\infty$；$w_R\to 1$ 于每个有界区间且满足 §3 的有限阶 EM 纪律。记
$M_R:=\int w_R\,\frac{\varphi'}{\pi}dx$。由于对每个固定 $R$ 有 $M_R<\infty$，且 $\|a\|_\infty<\infty$，故 $\operatorname{Tr}T_{a,R}\le \|a\|_\infty M_R<\infty$，从而 $T_{a,R}\in\mathcal S_1$；由 $\phi(0)=0$ 且 $\phi$ 为 Lipschitz，得 $\phi(T_{a,R})\in\mathcal S_1$。则对任意满足 $\phi\in C([0,1])$、$\phi(0)=0$ 且 $\phi$ 为 Lipschitz 的函数，

$$
\frac{1}{M_R}\sum_{j\ge1}\phi\!\big(\lambda_j(T_{a,R})\big)\ \longrightarrow\
\frac{1}{M_R}\int_{\mathbb R}\phi\!\big(a(x)\big)\,w_R(x)\,\frac{\varphi'(x)}{\pi}\,dx\quad(R\to\infty).
$$

**证明思路.** 由 $\phi(0)=0$ 与 Lipschitz 得 $|\phi(s)|\le Ls$，故 $\phi(T_{a,R})$ 迹类且 $\operatorname{Tr}\phi(T_{a,R})=\sum_j\phi(\lambda_j(T_{a,R}))$（Lidskii）。结合定理 2.1 的迹恒等式、Ky Fan 原理与 $w_R$ 的近似恒等性质，得弱收敛。∎

> **散射接口**：在散射/完成函数等价下，$\varphi'=\pi\rho$ 为相位导数，故 $\operatorname{Tr}T_{a,R}$ 等价于"$a\cdot w_R$"对散射密度的加权积分，与 Birman–Kreĭn 公式一致。

---

## 3. 非渐近窗化误差：Nyquist–Poisson–EM 三分解

记对 (2.1)–(2.3) 的数值实现

$$
\mathsf{tr}_{\Delta,T}(a,R):=\Delta\sum_{|k|\le \lfloor T/\Delta\rfloor} a(k\Delta)\,w_R(k\Delta)\,\frac{\varphi'(k\Delta)}{\pi}.
$$

**定理 3.1（三分解上界，非渐近）.** 若 $a,w_R,\varphi'$ 平滑到阶 $p\ge2$，则

$$
\bigl|\operatorname{Tr}T_{a,R}-\mathsf{tr}_{\Delta,T}(a,R)\bigr|
\ \le\ \underbrace{\mathcal E_{\rm alias}}_{\text{Poisson}}\ +\ \underbrace{\mathcal E_{\rm EM}(p)}_{\text{伯努利层}}\ +\ \underbrace{\mathcal E_{\rm tail}}_{\text{截断}},
$$

其中
$\mathcal E_{\rm alias}$ 由 Poisson 公式的"离带镜像"项显式给出（Nyquist 条件下可为 0）；

$\mathcal E_{\rm EM}(p):=|R_p|$ 为 Euler–Maclaurin 余项的绝对值；$\mathcal E_{\rm tail}$ 取决于 $a,w_R,\varphi'$ 的支集与衰减。

取 $p=2m\ge2$，令 $f(x):=a(x)\,w_R(x)\,\frac{\varphi'(x)}{\pi}$。则
$$
R_p\ =\ -\frac{\Delta^{p}}{p!}\int_{\mathbb R} f^{(p)}(x)\,B_p\!\left(\left\{\frac{x}{\Delta}\right\}\right)dx,\qquad
|R_p|\ \le\ \frac{\Delta^{p}\|B_p\|_{L^\infty}}{p!}\|f^{(p)}\|_{L^1}.
$$
其中 $B_p(\{x/\Delta\})$ 为**周期化 Bernoulli 多项式**（$\{x/\Delta\}$ 为 $x/\Delta$ 的分数部分）；此处要求 $f^{(p)}\in L^1(\mathbb R)$。

> **实现建议**：保持 **有限阶** EM（严禁逐项无穷外推），并优先选择带限/指数衰减的偶窗以压低 $\mathcal E_{\rm alias},\mathcal E_{\rm tail}$。

---

## 4. 采样/插值的密度律（Landau 型）

设 $X=\{x_n\}\subset\mathbb R$ 为相位度量下分离序列，$I\subset\mathbb R$ 有界区间。记

$$
\nu_0(I)=\int_I\frac{\varphi'(x)}{\pi}\,dx.
$$

**定理 4.1（必要密度条件）.**
若 $X$ 为采样集（存在上/下框架常数），则

$$
\#\{x_n\in I\}\ \gtrsim\ \nu_0(I).
$$

若 $X$ 为插值集，则

$$
\#\{x_n\in I\}\ \lesssim\ \nu_0(I).
$$

**证明要点.** 以 $a=\mathbf 1_I$、$w_R\equiv1$ 代入迹恒等与命题 2.2，并用 §1 的上/下 Carleson 得计数与 $\nu_0(I)$ 的比较。∎

**定理 4.2（密度刻画：Doubling 情形）.** 若 $\varphi'(x)\,dx$ 为 Doubling，则**采样/插值**在实轴上的必要充分密度条件均以 $\nu_0$ 给出（几何密度阈值）。

---

## 5. 离散图对照（Ihara ζ 与非回溯算子）

在有限 $(q+1)$-正则图上，取 $\{\mathbf e_k\}$ 为所处 Hilbert 空间的**正交标准基**，构造"离散局部化算子"

$$
T^{\rm disc}_{a,R}:=\sum_{k\ge1} a(k)\,w_R(k)\,|\mathbf e_k\rangle\langle \mathbf e_k|.
$$

则 $\operatorname{Tr}T^{\rm disc}_{a,R}=\sum_{k\ge1} a(k)\,w_R(k)$，与 Ihara–Bass 行列式公式 $\zeta(u)^{-1}=(1-u^2)^{r-1}\det(I-Au+Qu^2)$ 的"长度频率计数"相呼应；图上之"密度—计数—迹"关系与连续情形平行，并可借 Poisson/EM 给出离散三分解误差。

---

## 6. 适用范围与失效边界

1. **EM 仅取有限阶**：无穷级外推会引入伪奇性与数值不稳定。
2. **窗/核正则性**：若窗非偶或衰减不足，需回退到一般 RKHS 的投影–卷积表达并以 RKT 重新估计。
3. **符号非界/支集过大**：$T_{a,R}$ 可能非迹类；可先在区间上截断符号并用 §3 的三分解闭合。
4. **RKT 充要性**：一般 RKHS 不总成立；在 $\mathcal H(E)$ 与模型子空间的若干类（含 $\varphi'$ Doubling、一成分情形、Dirichlet-型空间）成立。

---

## 7. 与 S15–S26 及量子理论的接口

**7.1 与 S15–S17（Herglotz、de Branges、规范系统）的接口。**
- S15–S17 的 Herglotz 表示与规范系统为本文 §0 的核对角公式 $K(x,x)=\tfrac{1}{\pi}\varphi'(x)|E(x)|^2$ 提供解析结构。
- S15–S17 的 Weyl–Titchmarsh $m$-函数之边界值 $\Im m(x+i0)=\pi\rho(x)$ 与本文相位密度测度 $d\nu_0=\frac{\varphi'}{\pi}dx$ 完全一致。

**7.2 与 S24–S26（框架、相位密度、采样）的接口。**
- S24 的纤维 Gram 表征与 Wexler–Raz 双正交为本文 §1.4 的离散测度与分离序列提供具体判据。
- S26 的相位密度刻度 $\varphi'(x)=\pi\rho(x)$ 与本文 §0、§1、§2 的相位密度测度 $d\nu_0$ 在 de Branges 语境下完全对齐。
- S26 的 Landau 必要密度条件与本文定理 4.1 在相位坐标下等价。

**7.3 与 WSIG-QM / UMS 的接口。**
- WSIG-QM 的公理 A5（相位—密度—延迟刻度）与本文 §0 的核对角公式在散射语境下一致。
- UMS 的核心统一式 $d\mu_\varphi = \tfrac{1}{2\pi}\operatorname{tr}\mathsf Q\,dE = \rho_{\mathrm{rel}}\,dE = \tfrac{\varphi'}{\pi}\,dE$ 与本文 §0、§2 的相位密度测度在 de Branges 空间语境下完全对齐。
- 本文定理 2.1（迹恒等）可视为 UMS 窗化读数在局部化算子语境下的具体实现。

**7.4 与 WSIG-QFT / 量子引力场的接口。**
- WSIG-QFT 的定理 5.2（窗化 BK 恒等式）与本文定理 2.1（迹恒等）在散射/规范系统等价下共享数学结构。
- 量子引力场理论的相位密度刻度 $\varphi'(E)=\pi\rho_{\mathrm{rel}}(E)$ 与本文 §0 在散射谱模型下一致。

**7.5 与窗口化路径积分理论的接口。**
- 路径积分理论的窗—核对偶可在能量域改写为本文 §2.2 的局部化算子 $T_{a,R}$。
- 路径积分理论的 Nyquist–Poisson–EM 误差闭合与本文定理 3.1 的三分解框架完全一致。

**7.6 与 FMU 的接口。**
- FMU 的相位密度坐标 $d\mu_\varphi=(1/\pi)\varphi'\,d\omega$ 与本文 §0 的相位密度测度 $d\nu_0$ 在 Mellin 语境下等价。
- FMU 的定理 4.1（Nyquist–Poisson–EM 三分解）对应本文定理 3.1。

**7.7 保持"极点 = 主尺度"的有限阶 EM 纪律。**
- 本文在所有离散—连续换序中均采用**有限阶** EM（定理 3.1），确保不引入新奇点。
- 与 S15–S26、WSIG-QM、UMS、WSIG-QFT、路径积分理论、量子引力场、FMU 保持一致：EM 余项仅作有界扰动。

---

## 附录 A：若干标准判据与引用式

* **核对角—相位导数**：$K(x,x)=\frac{1}{\pi}\varphi'(x)|E(x)|^2$。
* **Berezin/Toeplitz 与迹**：$\operatorname{Tr}\big(\int f(x)\,|k_x\rangle\langle k_x|\,d\mu(x)\big)=\int f\,d\mu$。
* **Ky Fan 最大化原理** 与 **Lidskii 定理**（迹类 $\Rightarrow$ 迹 = 特征值可求和）。
* **Poisson 公式**、**Nyquist–Shannon 采样** 与 **EM 余项显式表达**。
* **Toeplitz Weyl 律**（几何量化视角）。
* **Birman–Kreĭn/相移—谱移**（散射接口）。
* **Ihara–Bass 行列式公式**（离散图对照）。

---

## 参考文献（选）

1. J. Antezana, J. Marzo, J.-F. Olsen, *Zeros of Random Functions Generated with de Branges Kernels*, IMRN (2016)（含 $K(x,x)=\frac{1}{\pi}\varphi'(x)|E(x)|^2$）。
2. J. Marzo, S. Nitzan, J.-F. Olsen, *Sampling and interpolation in de Branges spaces with doubling phase*, arXiv:1103.0566。
3. E. Fricain, A. Hartmann, W. T. Ross, *A Survey on Reverse Carleson Measures*, arXiv:1601.00226。
4. G. R. Chacón, E. Fricain, M. Shabankhah, *Carleson Measures and Reproducing Kernel Thesis in Dirichlet-type Spaces*, arXiv:1009.1801；SPMJ (2013)。
5. L. A. Coburn, *Berezin Transform and Weyl-Type Unitary Invariants*, J. Funct. Anal.（综述性介绍）。
6. S. Axler, *The Berezin Transform*（讲义）。
7. R. Paoletti, *On the Weyl Law for Toeplitz Operators*, arXiv:0806.0225。
8. A. Strohmaier et al., *The Birman-Kreĭn Formula for Differential Forms…*, Adv. Math. (2022)。
9. H. Zhang, *The Birman–Kreĭn Formula and Scattering Phase on Product Space*, arXiv:2509.06372 (2025)。
10. DLMF §24（Euler–Maclaurin 及余项表达）；维基条 *Euler–Maclaurin Formula*（补充）。
11. L. N. Trefethen, J. A. C. Weideman, *The Exponentially Convergent Trapezoidal Rule*, SIAM Review (2014)。
12. 维基条 *Poisson Summation Formula*、*Nyquist–Shannon Sampling Theorem*。
13. Ihara–Bass 文献与综述（Deitmar；Rangarajan 等）。
14. Ky Fan 原理、Lidskii 定理综述与讲义。

---

### 致谢与接口

本文以 $\mathcal H(E)$ 的核对角—相位导数恒等式为计量基准，RKT 给出 Carleson/框架—采样/插值的可检判据；Toeplitz/Berezin 局部化把"符号 $\times$ 窗 $\times$ 相位密度"几何量化为**迹**，并导出 Weyl-型谱分布；严格的**有限阶** EM 纪律把数值误差非渐近地封装为"别名 + 伯努利层 + 截断"。在散射—完成函数—规范系统的统一接口下，这些结构可直接对接相移/谱移（Birman–Kreĭn）、以及离散图的 Ihara–Bass 计数。
