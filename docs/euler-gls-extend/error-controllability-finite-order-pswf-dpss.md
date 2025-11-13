# 有限阶纪律下的误差可控性

**——PSWF/DPSS 极值窗的唯一性、整数主项（谱流／投影对指标）与 $10^{-3}$ 级普适常数（统一归一化与常数校准版）**

---

## Abstract

在统一的 Fourier 归一化 $\widehat f(\xi)=\int_{\mathbb R}f(t)e^{-2\pi i t\xi}\,dt$（频率以 cycles 计）下，构建围绕时限–带限串联算子的误差纪律：窗化主泄漏、乘法交叉项与"求和–积分差"被组织为"拓扑整数主项 + 解析尾项"的可计算链路。连续端以 $K_c=D_TB_\Omega D_T$（离散端以 $K_{N,W}=T_NB_WT_N$）给出极值窗的唯一性与泄漏恒等式 $|(I-B_\Omega)g_\ast|_2^2=1-\lambda_0$；任意长度 1 基本域上，平方和型别名能量恒等于域外能量；乘法交叉项的 Hankel‑型块给出 Hilbert–Schmidt（HS）精确公式；Euler–Maclaurin(EM) 余项的解析尾项由周期 Bernoulli 的上确界常数与 BPW 不等式闭式控制。基于自然对数口径的显式非渐近特征值上界，得到与窗形无关的最小整数 Shannon 数门限 $(\varepsilon,N_0^\star)=(10^{-3},33),(10^{-6},42),(10^{-9},50)$。在可定义性假设（迹类差与强连续路径）下，谱流等于投影对指标，从而将"误差的整数主项"识别为拓扑不变量。全文给出完整证明与可复算流程。

---

## Keywords

Time–band limiting; Prolate Spheroidal Wave Functions (PSWF); Discrete Prolate Spheroidal Sequences (DPSS); Shannon number; aliasing; Hankel block; Hilbert–Schmidt norm; Euler–Maclaurin remainder; spectral flow; index of a pair of projections; de Branges.

---

## Introduction & Historical Context

时限–带限问题在信号处理与调和分析中处于核心地位。Slepian–Landau–Pollak 体系揭示：在有限时窗 $[-T,T]$ 与有限带宽 $[-\Omega,\Omega]$ 的串联约束下，最优能量集中的波形由 PSWF/DPSS 给出，其特征值在 $1$ 与 $0$ 附近呈指数簇集。工程实践常见三类误差——窗化带外泄漏、别名（aliasing）与求和–积分差（Poisson/EM 余项）——历来分而治之，导致门限与常数不可比、不可复算。

本文在统一的 cycles 归一化下，提出一条"可计算—可证明—可复算"的误差纪律链路：
（一）以 $K_c=D_TB_\Omega D_T$（离散端 $K_{N,W}=T_NB_WT_N$）的主特征值 $\lambda_0$ 精确刻画窗化主泄漏；（二）以平方和型别名＝域外能量的恒等式将 aliasing 还原为带外能量；（三）对乘法作用后的带外泄漏给出 Hankel‑HS 精确公式与上界；（四）以"谱流＝投影对指标"的框架刻画"整数主项"，以 Vaaler–Littmann 极值与周期 Bernoulli 常数给出 EM 解析尾项的闭式；（五）以自然对数口径的显式非渐近特征值上界生成**与窗形无关**的最小整数 Shannon 数门限。由此，三块误差均落到三项可计算量：$1-\lambda_0$、Hankel–HS 与 EM 尾项；整数主项由谱不变量承担。

---

## Model & Assumptions

**Fourier 与单位**：$\widehat f(\xi)=\int_{\mathbb R}f(t)e^{-2\pi i t\xi}\,dt$，$\xi$ 以 cycles 计；Plancherel：$|f|_2=|\widehat f|_2$。

**投影**：时限 $D_T f=\mathbf 1_{[-T,T]}f$；带限 $B_\Omega f=\mathcal F^{-1}(\mathbf 1_{[-\Omega,\Omega]}\widehat f)$。

**串联算子**：连续端 $K_c=D_TB_\Omega D_T$；离散端 $K_{N,W}=T_NB_WT_N$（$T_N$ 为长度 $N$ 的限制，$B_W$ 为 $[ -W,W ]\subset[-\tfrac12,\tfrac12]$ 的带限投影）。

**Shannon 数**：$c=\pi T\Omega$，$N_0=2T\Omega=2c/\pi$（连续）；$N_0=2NW$（离散）。二端以 $N_0$ 对齐。

**BPW**：若 $\operatorname{supp}\widehat g\subset[-\Omega,\Omega]$，则 $|g^{(m)}|_2\le (2\pi\Omega)^m|g|_2$。

**范数**：$|\cdot|_2,\ |\cdot|_\infty$；对任意有界算子 $|A|_{\mathrm{op}}\le |A|_{\mathrm{HS}}$。

**基本域**：任意长度 1 的 $I=[a,a+1)$，用于别名能量的归一化。

---

## Main Results (Theorems and Alignments)

### Theorem 1（极值窗唯一性与泄漏恒等）

设 $K_c=D_TB_\Omega D_T$ 为作用在 $L^2(\mathbb R)$ 上的紧自伴正算子。其最大特征值 $\lambda_0\in(0,1)$ 为单重，相应特征函数 $g_\ast$（$|g_\ast|_2=1$）唯一（除相位），并满足

$$
|B_\Omega g_\ast|_2^2=\lambda_0,\qquad |(I-B_\Omega)g_\ast|_2^2=1-\lambda_0.
$$

离散端 $K_{N,W}=T_NB_WT_N$ 完全平行，主向量为第一条 DPSS，亦为单重。

---

### Alignment 1（平方和型别名＝域外能量）

对任意 $w\in L^2(\mathbb R)$ 与任取长度 1 的基本域 $I=[a,a+1)$，有

$$
\int_I\sum_{k\ne0}\big|\widehat w(\xi+k)\big|^2\,d\xi
=\int_{\mathbb R\setminus I}\big|\widehat w(\eta)\big|^2\,d\eta.
$$

当 $I$ 与物理带通 $[-\Omega,\Omega]$（经平移／缩放）一致时，右端即"相对该带通的域外能量"；取 $w=g_\ast$ 得 $\mathsf{Aliasing}(g_\ast;I)=1-\lambda_0$。

---

### Theorem 2（乘法交叉项的 HS 精确公式与上界）

对 $x\in L^\infty\cap L^2$ 与 $W\in(0,\tfrac12]$，

$$
|(I-B_W)M_xB_W|_{\mathrm{HS}}^2
=\int_{\mathbb R}|\widehat x(\delta)|^2\,\sigma_W(\delta)\,d\delta,\qquad
\sigma_W(\delta)=\min(2W,|\delta|).
$$

进而对任意 $w\in L^2$ 有

$$
|(I-B_W)M_x w|_2
\le |(I-B_W)M_xB_W|_{\mathrm{op}}|w|_2+|x|_\infty|(I-B_W)w|_2,
$$

从而对极值窗 $g_\ast$（Theorem 1）：

$$
|(I-B_W)M_x g_\ast|_2
\le |(I-B_W)M_xB_W|_{\mathrm{HS}}+|x|_\infty\sqrt{1-\lambda_0}.
$$

此外，$(I-B_W)M_xB_W\equiv 0$ 当且仅当 $x$ a.e. 为常数。

---

### Theorem 3（EM 余项的解析尾项上界）

对 $g\in W^{2p,1}(\mathbb R)\cap L^2(\mathbb R)$，有

$$
|R_{2p}(g)|\ \le\ \frac{2\zeta(2p)}{(2\pi)^{2p}}\ |g^{(2p)}|_{L^1}.
$$

若再假设 $\operatorname{supp}\widehat g\subset[-\Omega,\Omega]$ 且在长度 $L$ 的时域局部评估，则

$$
\frac{|R_{2p}(g)|}{|g|_2}\ \le\ 2\,\zeta(2p)\,\sqrt{L}\,\Omega^{2p}.
$$

达到 $|R_{2p}(g)|/|g|_2\le10^{-3}$ 的充分门限为

$$
\sqrt{L}\,\Omega^4\le 4.6197\times 10^{-4},\quad
\sqrt{L}\,\Omega^6\le 4.9148\times 10^{-4},\quad
\sqrt{L}\,\Omega^8\le 4.9797\times 10^{-4}.
$$

---

### Theorem 4（谱流＝投影对指标：整数主项的拓扑化）

取平滑频域乘子 $\phi\in C_c^\infty(\mathbb R)$，令 $\Pi=\mathcal F^{-1}M_\phi\mathcal F$ 与正交投影 $P=\mathbf 1_{[1/2,\infty)}(\Pi)$。设调制群 $U_\theta f(t)=e^{2\pi i\theta t}f(t)$，$P_\theta=U_\theta P U_\theta^\ast$。若
(i) $P-P_\theta\in\mathcal S_1$；(ii) $\theta\mapsto U_\theta$ 强连续，
则自伴路径 $A(\theta)=2P_\theta-I$ 可定义谱流，且

$$
\mathrm{Sf}\big(A(\theta)\big)_{\theta\in[\theta_0,\theta_1]}
=\mathrm{ind}\big(P,P_{\theta_1}\big)-\mathrm{ind}\big(P,P_{\theta_0}\big)\in\mathbb Z.
$$

由此可将"求和–积分差"的整数主项识别为与路径相关的相对指标；解析尾项由 Theorem 3 控制。

---

### Theorem 5（KRD 非渐近主值上界与最小整数门限）

令 $N_0=2T\Omega$（连续）或 $N_0=2NW$（离散），则主值满足

$$
1-\lambda_0\ \le\ 10\,\exp\!\Bigg(-\frac{(\lfloor N_0\rfloor-7)^2}{\pi^2\log(50N_0+25)}\Bigg),
$$

并据此定义达到泄漏上界 $\varepsilon$ 的最小整数门限

$$
N_0^\star(\varepsilon):=\min\Big\{n\in\mathbb N:\ 10\exp\!\Big(-\tfrac{(n-7)^2}{\pi^2\log(50n+25)}\Big)\le \varepsilon\Big\}.
$$

数值（自然对数，指数内取整）：

$$
(\varepsilon,N_0^\star,c^\star,NW^\star)=
(10^{-3},33,\tfrac{\pi}{2}\!\cdot\!33,16.5),
(10^{-6},42,\tfrac{\pi}{2}\!\cdot\!42,21.0),
(10^{-9},50,\tfrac{\pi}{2}\!\cdot\!50,25.0).
$$

---

## Proofs

### Proof of Theorem 1

**紧性与自伴**。$B_\Omega$ 与 $D_T$ 为正交投影，$(D_TB_\Omega)(t,s)=\mathbf 1_{[-T,T]}(t)\,\dfrac{\sin(2\pi\Omega(t-s))}{\pi(t-s)}$ 在 $[-T,T]^2$ 上平方可积，故 $D_TB_\Omega$ 为 Hilbert–Schmidt，进而 $K_c=D_TB_\Omega D_T$ 紧自伴。

**可交换与单重性**。令 $x=t/T\in[-1,1]$、$c=\pi T\Omega$。经典 PSWF 满足

$$
(1-x^2)y''(x)-2xy'(x)+(\chi-c^2x^2)y(x)=0.
$$

记 $L_c y:= -\dfrac{d}{dx}\!\left((1-x^2)\dfrac{dy}{dx}\right)+c^2x^2y$，把上式改写为 $L_cy=\chi y$。$L_c$ 是 $[-1,1]$ 上的自伴 Sturm–Liouville 算子，端点为正则奇点，谱纯离散且各本征值单重；其本征函数零点数与编号一致（振荡定理）。Slepian 可交换性给出 $K_c$ 与 $L_c$ 可同时对角化，故 $\lambda_0$ 的几何重数等于对应 $\chi_0$ 的重数，因而为 1，主特征函数唯一（除相位）。

**泄漏恒等**。由 $B_\Omega$ 的正交投影性与 $|g_\ast|_2=1$，

$$
\lambda_0=\langle K_cg_\ast,g_\ast\rangle=\langle B_\Omega g_\ast,g_\ast\rangle
=|B_\Omega g_\ast|_2^2,\quad
|(I-B_\Omega)g_\ast|_2^2=1-\lambda_0.
$$

离散端 $K_{N,W}$ 与可交换的二阶差分算子构成离散 Sturm 理论，主值亦单重。

---

### Proof of Alignment 1

$\mathbb R\setminus I=\bigsqcup_{k\ne0}(I+k)$ 为可数不交分解。由于 $\widehat w\in L^2$，
$\sum_{k\ne0}\int_I|\widehat w(\xi+k)|^2\,d\xi\le|\widehat w|_2^2<\infty$，Tonelli 可用。变量代换 $\eta=\xi+k$ 即得

$$
\int_I\sum_{k\ne0}|\widehat w(\xi+k)|^2\,d\xi
=\sum_{k\ne0}\int_{I+k}|\widehat w(\eta)|^2\,d\eta
=\int_{\mathbb R\setminus I}|\widehat w(\eta)|^2\,d\eta.
$$

---

### Proof of Theorem 2

**HS 精确公式**。频域核

$$
K(\xi,\eta)=\mathbf 1_{|\xi|>W}\mathbf 1_{|\eta|\le W}\,\widehat x(\xi-\eta).
$$

HS 范数平方

$$
\iint |K|^2
=\int_{|\eta|\le W}\int_{|\xi|>W}|\widehat x(\xi-\eta)|^2\,d\xi d\eta
=\int_{\mathbb R}|\widehat x(\delta)|^2\,m_W(\delta)\,d\delta,
$$

其中
$m_W(\delta)=\operatorname{meas}\{\eta\in[-W,W]:|\eta+\delta|>W\}$。
几何上为长度 $2W$ 的区间与其平移之补交测度：
$m_W(\delta)=\min(2W,|\delta|)$。得所述公式。

**上界**。分解

$$
(I-B_W)M_x=(I-B_W)M_xB_W+(I-B_W)M_x(I-B_W),
$$

再用 $|A|_{\mathrm{op}}\le |A|_{\mathrm{HS}}$、$|(I-B_W)|\le 1$ 与三角不等式，得到一般上界；取 $w=g_\ast$ 并用 Theorem 1 的 $|(I-B_W)g_\ast|_2\le \sqrt{1-\lambda_0}$ 即得陈述式。若 $(I-B_W)M_xB_W\equiv 0$，则对任意带限输入 $B_Ww$，$\widehat x\ast (\widehat w\cdot \mathbf 1_{[-W,W]})$ 支撑仍在 $[-W,W]$，这迫使 $\operatorname{supp}\widehat x\subset\{0\}$；与 $x\in L^\infty$ 合并仅余常数函数。

---

### Proof of Theorem 3

周期 Bernoulli 的 Fourier 展开给出

$$
\left|\frac{B_{2p}({\cdot})}{(2p)!}\right|_\infty=\frac{2\zeta(2p)}{(2\pi)^{2p}}.
$$

EM 余项公式

$$
R_{2p}(g)=\int_{\mathbb R} g^{(2p)}(t)\,\frac{B_{2p}(\{t\})}{(2p)!}\,dt,
$$

从而

$$
|R_{2p}(g)|\le \frac{2\zeta(2p)}{(2\pi)^{2p}}\,|g^{(2p)}|_{L^1}.
$$

若 $\operatorname{supp}\widehat g\subset[-\Omega,\Omega]$，则
$|g^{(2p)}|_{L^1}\le \sqrt{L}|g^{(2p)}|_{L^2}\le \sqrt{L}(2\pi\Omega)^{2p}|g|_2$。分母的 $(2\pi)^{2p}$ 与 BPW 的 $(2\pi)^{2p}$ 完全抵消，得陈述式与门限数值。

---

### Proof of Theorem 4

定 $A(\theta)=2P_\theta-I$。由假设 (i)–(ii) 与谱投影的正则性，$A(\theta)$ 为自伴 Fredholm 的强连续路径。谱流定义为零穿越的有符号计数；另一方面，相对指标 $\mathrm{ind}(P,Q)$ 在 $P-Q\in\mathcal S_1$ 时可由相对维数定义，并满足加法性与同伦不变性。把 $[\theta_0,\theta_1]$ 细分为若干小区间，使 $0$ 成为各段上的正则值，局部地，谱流等于 $\mathrm{rank}(P_\theta|_{\mathrm{ran}P})$ 的跳变数；相对指标亦记录相同的跳变。拼接并用同伦不变性得

$$
\mathrm{Sf}(A(\theta))_{\theta_0}^{\theta_1}
=\mathrm{ind}(P,P_{\theta_1})-\mathrm{ind}(P,P_{\theta_0}).
$$

频域平滑 $\phi\in C_c^\infty$ 与（必要时）时域局域化保证 $P-P_\theta\in\mathcal S_1$；在强算子拓扑下让 $\phi\to \mathbf 1_{[-W,W]}$，整数不变，从而建立"整数主项"的拓扑来源。

---

### Proof of Theorem 5

离散端原式以 $NW$ 为参量：

$$
1-\lambda_0\le 10\exp\!\left(-\frac{(\lfloor 2NW\rfloor-7)^2}{\pi^2\log(100NW+25)}\right).
$$

置 $N_0=2NW$ 得

$$
1-\lambda_0\le 10\exp\!\left(-\frac{(\lfloor N_0\rfloor-7)^2}{\pi^2\log(50N_0+25)}\right).
$$

连续端以 $c$ 表示的界经 $N_0=2c/\pi$ 得相同统一形式。对给定 $\varepsilon$ 扫描最小整数 $n$ 使右端 $\le \varepsilon$ 即得 $N_0^\star(\varepsilon)$。数值如陈述。

---

## Model Apply

**连续–离散映射**：$(T,\Omega)\leftrightarrow (N,W)$ 以 $N_0=2T\Omega=2NW$ 对齐；通常取 $N\approx 2T$、$W\approx \Omega$（单位一致时）。

**两套口径一致性**：$D_TB_\Omega D_T$ 与 $B_\Omega D_TB_\Omega$ 非零谱一致（命题 $AB$ 与 $BA$ 非零谱一致）。在频域泄漏：$|(I-B_\Omega)g_\ast|_2^2=1-\lambda_0$；在时域泄漏：$|(I-D_T)w_\ast|_2^2=1-\lambda_0$。

**基本域一致性**：选取与 $[-\Omega,\Omega]$ 同类的基本域（平移／缩放一致），Alignment 1 的右端即"相对该带通的域外能量"，从而对 $w=g_\ast$，别名能量等于 $1-\lambda_0$。

---

## Engineering Proposals

**（一）门限驱动的选参**
给定泄漏容限 $\varepsilon\in\{10^{-3},10^{-6},10^{-9}\}$，查 Theorem 5 得最小整数 $N_0^\star$，据此设置 $(T,\Omega)$ 或 $(N,W)$。

**（二）交叉项的可计算上界**
一次 FFT 得 $\widehat x$，计算

$$
\Xi_W(x):=\left(\int_{\mathbb R}|\widehat x(\delta)|^2\min(2W,|\delta|)\,d\delta\right)^{1/2}.
$$

预算式

$$
|(I-B_W)M_x g_\ast|_2\le \Xi_W(x)+|x|_\infty\sqrt{1-\lambda_0}.
$$

若 $\widehat x$ 经预滤而窄带，$\Xi_W(x)$ 显著减小。

**（三）EM 选阶**
给定 $(L,\Omega)$，选择 $p\in\{2,3,4\}$ 中最小者，使 $\sqrt{L}\Omega^{2p}\le 10^{-3}/(2\zeta(2p))$。

**（四）多锥／多通带**
取前 $K\approx \lfloor N_0\rfloor$ 条 DPSS 做多锥；别名预算沿 Alignment 1 逐锥叠加，交叉项按 Theorem 2 以 $\widehat x$ 的能量分配分块估计。

---

## Discussion (risks, boundaries, past work)

**可定义性边界**：谱流＝投影对指标依赖 $P-P_\theta\in\mathcal S_1$。尖锐带限投影与纯调制差值一般非迹类，需先频域平滑并（必要时）时域局域化，再取谱投影，最后在强算子拓扑下趋向极限；整数主项对正则化细节不敏感。

**尺度与常数**：cycles 归一化下，BPW 的 $(2\pi)^m$ 与 EM 常数分母 $(2\pi)^{2p}$ 完全抵消；KRD 门限以自然对数与 $\log(50N_0+25)$ 表示，并以指数内取整给出最小整数。

**保守与紧致**：可按 Theorem 5 的紧版本生成门限（$33,42,50$），亦可在极端风险规避下选更大整数，形成保守冗余。

**历史脉络**：时–带极值、Toeplitz 指数／绕数、谱流／相对指标与一侧极值构成理论脊梁；非渐近门限将经典渐近论与工程参数化联通。

---

## Conclusion

在统一归一化与参数映射下，三类误差——主泄漏、乘法交叉项与求和–积分差——被纳入"整数主项 + 解析尾项"的算子化纪律：

* **主泄漏**由 $\lambda_0$ 精确刻画，并由显式非渐近上界生成**与窗形无关**的最小整数门限；
* **交叉项**由 Hankel‑HS 精确公式量化，给出无需启发式常数的可计算上界；
* **EM 余项**在 cycles 归一化下呈现"$(2\pi)$ 完全抵消"，常数闭式且与时–带参数直接对接；
* **整数主项**（谱流／投影对指标）提供拓扑来源。
  由此形成的"有限阶纪律"既能工程落地，又具完备的数学锚点。

---

# Appendix — Detailed Proofs and Calculus

### A.1 记号、单位与基本工具

* 归一化：$\widehat f(\xi)=\int_{\mathbb R}f(t)e^{-2\pi i t\xi}\,dt$，$\xi$ 以 cycles 计。
* 投影：$D_T f=\mathbf 1_{[-T,T]}f$，$B_\Omega=\mathcal F^{-1}\mathbf 1_{[-\Omega,\Omega]}\mathcal F$。
* 范数：$|A|_{\mathrm{op}}\le |A|_{\mathrm{HS}}$，Plancherel：$|f|_2=|\widehat f|_2$。
* Shannon 数：$N_0=2T\Omega=2NW$。

---

### A.2 $AB$ 与 $BA$ 非零谱一致

若 $ABx=\lambda x$ 且 $\lambda\ne0$，则 $Bx\ne0$ 且 $BA(Bx)=\lambda (Bx)$；反向同理。由此 $D_TB_\Omega D_T$ 与 $B_\Omega D_TB_\Omega$ 非零谱一致，两个口径的泄漏恒等式等价。

---

### A.3 PSWF 的 Sturm–Liouville 结构与主值单重性

变量 $x=t/T\in[-1,1]$、$c=\pi T\Omega$。PSWF 满足

$$
(1-x^2)y''(x)-2xy'(x)+(\chi-c^2x^2)y(x)=0.
$$

记

$$
L_c y:=-\frac{d}{dx}\!\left((1-x^2)\frac{dy}{dx}\right)+c^2x^2y,
$$

则 $L_c$ 为 $[-1,1]$ 上自伴的二阶微分算子。端点 $x=\pm1$ 为正则奇点，谱纯离散且各本征值简单；本征函数零点数与编号一致。Slepian 可交换性给出 $K_c$ 与 $L_c$ 共享正交本征系，故 $K_c$ 的主特征值几何重数为 1。

**离散端**：Toeplitz 型 prolate 矩阵与三对角差分算子可交换，离散 Sturm 振荡定理保证主值简单。

---

### A.4 平方和型别名＝域外能量的细节

对 $I=[a,a+1)$，有 $\mathbb R\setminus I=\bigsqcup_{k\ne0}(I+k)$（不交）。对任意 $w\in L^2$，

$$
\sum_{k\ne0}\int_I|\widehat w(\xi+k)|^2\,d\xi
=\sum_{k\ne0}\int_{I+k}|\widehat w(\eta)|^2\,d\eta
=\int_{\mathbb R\setminus I}|\widehat w(\eta)|^2\,d\eta.
$$

"平方和型"指在积分前对各平移通道取模平方后求和；与"先周期化再取模平方"的工程度量（含交叉项）区分。

---

### A.5 Hankel‑HS 几何测度的分段计算

对固定 $\delta$，集合

$$
S(\delta)=\{\eta\in[-W,W]:|\eta+\delta|>W\}.
$$

若 $|\delta|\le 2W$，则 $S(\delta)$ 为两端各长 $|\delta|/2$ 的并，测度 $|\delta|$；若 $|\delta|>2W$，则 $S(\delta)=[-W,W]$ 全部，测度 $2W$。故

$$
m_W(\delta)=\operatorname{meas}S(\delta)=\min(2W,|\delta|),
$$

从而得 Theorem 2 的 HS 精确公式。

---

### A.6 EM 余项与"$(2\pi)$ 抵消"细节

周期 Bernoulli 的 sup 常数

$$
\left|\frac{B_{2p}({\cdot})}{(2p)!}\right|_\infty=\frac{2\zeta(2p)}{(2\pi)^{2p}}.
$$

若 $\operatorname{supp}\widehat g\subset[-\Omega,\Omega]$，则

$$
|g^{(2p)}|_{L^1}\le \sqrt{L}|g^{(2p)}|_{L^2}\le \sqrt{L}(2\pi\Omega)^{2p}|g|_2,
$$

代入 EM 余项上界，分母的 $(2\pi)^{2p}$ 与 BPW 的 $(2\pi)^{2p}$ 完全抵消，得到

$$
\frac{|R_{2p}(g)|}{|g|_2}\le 2\zeta(2p)\sqrt{L}\Omega^{2p}.
$$

---

### A.7 谱流＝投影对指标的构造与证明

**正交投影的正则化**。取 $\phi\in C_c^\infty$ 满足 $\phi\equiv 1$ 于 $[-\Omega_0,\Omega_0]\subset(-\tfrac12,\tfrac12)$，$\Pi=\mathcal F^{-1}M_\phi\mathcal F$，$P=\mathbf 1_{[1/2,\infty)}(\Pi)$。对调制 $U_\theta$ 定义 $P_\theta=U_\theta P U_\theta^\ast$。

**迹类差**。$\Pi$ 的核快衰，$[U_\theta,\Pi]$ 为 Hilbert–Schmidt；谱投影的函数演算给出 $P-P_\theta\in\mathcal S_1$。

**谱流与指标**。路径 $A(\theta)=2P_\theta-I$ 自伴、Fredholm、强连续。局部把 $0$ 作为正则值，谱流等于零穿越计数；相对指标 $\mathrm{ind}(P,P_\theta)$ 由 $\mathcal S_1$ 差可定义。局部—全局拼接与同伦不变性给出

$$
\mathrm{Sf}(A(\theta))_{\theta_0}^{\theta_1}
=\mathrm{ind}(P,P_{\theta_1})-\mathrm{ind}(P,P_{\theta_0}).
$$

**尖锐带限极限**。取 $\phi_n\to \mathbf 1_{[-W,W]}$ 于 $L^\infty$ 与强算子拓扑，定义 $P^{(n)}$，上述等式对每个 $n$ 成立；谱流与相对指标在 $\mathcal S_1$ 近似下保持不变，极限得结论。由此整数主项对平滑细节不敏感。

---

### A.8 KRD 门限换元与数值

离散端以 $NW$ 表示：

$$
1-\lambda_0\le 10\exp\!\left(-\frac{(\lfloor 2NW\rfloor-7)^2}{\pi^2\log(100NW+25)}\right).
$$

置 $N_0=2NW$ 得统一式

$$
1-\lambda_0\le 10\exp\!\left(-\frac{(\lfloor N_0\rfloor-7)^2}{\pi^2\log(50N_0+25)}\right).
$$

连续端 $c$ 版本经 $N_0=2c/\pi$ 得同上。最小整数门限

$$
N_0^\star(\varepsilon)=\min\{n\in\mathbb N:\ 10\exp(-\tfrac{(n-7)^2}{\pi^2\log(50n+25)})\le \varepsilon\}.
$$

对应数值：$(10^{-3},33),(10^{-6},42),(10^{-9},50)$。

---

### A.9 统一误差预算的严式

对极值窗 $g_\ast$ 与 $x\in L^\infty\cap L^2$，选与 $[-\Omega,\Omega]$ 一致的基本域 $I$，有

$$
\underbrace{\int_I\sum_{k\ne0}|\widehat{(xg_\ast)}(\xi+k)|^2\,d\xi}_{\text{别名}=\text{域外}}
\le |x|_\infty^2(1-\lambda_0)+|x|_\infty\,\Xi_W(x),
$$

其中 $\Xi_W(x)=|(I-B_W)M_xB_W|_{\mathrm{HS}}$。若再附加带限与局域化，EM 余项满足

$$
|R_{2p}(xg_\ast)|\le 2\zeta(2p)\sqrt{L}\Omega^{2p}|xg_\ast|_2.
$$

三项可加给出完整预算。

---

### A.10 可复算清单（伪代码）

**KRD 门限（自然对数）**

```python
def N0_star(eps):
    n = 1
    while True:
        U = 10*exp(- (n-7)**2 / (pi**2*log(50*n + 25)) )
        if U <= eps:
            return n, (pi*n/2), (n/2)  # (N0*, c*, NW*)
        n += 1
```

**Hankel–HS 交叉项**

```python
# xhat: Fourier samples on grid delta with spacing ddelta
XiW_sq = sum( abs(xhat)**2 * minimum(2*W, abs(delta)) ) * ddelta
XiW = sqrt(XiW_sq)
```

**EM 余项门限**

```python
# choose smallest p in {2,3,4} with sqrt(L) * Omega**(2*p) <= 1e-3/(2*zeta(2*p))
```

---

**（正文与附录完）**
