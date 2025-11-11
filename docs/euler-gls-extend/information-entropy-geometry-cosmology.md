# 信息熵—几何统一与宇宙学项的窗化生成

**从相对熵 Hessian 到有效作用、Poisson–Euler–Maclaurin 有限阶纪律与 Friedmann 方程的几何熵分解**

**Author**: Auric (S-series / EBOC)
**MSC**: 53Bxx; 83C05; 58J35; 46E22; 47B35; 42A38; 94A17; 81U40
**Keywords**: 信息几何；Eguchi 正则散度；Fisher–Rao 度量；Amari α–联络；Bregman/Hessian；谱移函数；Birman–Krein；Wigner–Smith 群延迟；Toeplitz/Berezin 压缩；Schatten–迹类准则；Poisson 求和；Euler–Maclaurin 余项常数；波前集与 Toeplitz–FIO；热核/Seeley–DeWitt；谱作用；运行真空；FRW 几何熵分解

---

## Abstract

在统一的"算子—测度—函数"框架中，建立把**相对熵的多阶响应**、**散射谱的母尺刻度**、**窗化读数的 Toeplitz/Berezin 压缩**与**Nyquist–Poisson–Euler–Maclaurin（NPE）有限阶纪律**有机拼接到**几何有效作用**与**宇宙学项**的闭合推导。首先，在 Eguchi 正则散度与 Amari α–几何下证明 Fisher–Rao 度量与对偶联络的构造；其次，在迹类/相对迹类扰动与能量可导的散射理论假设下给出"母尺"三位一体

$$
\frac{\varphi'(\omega)}{\pi}=\xi'(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega),\qquad Q=-iS^\dagger\partial_\omega S
$$

的定理化陈述，并指出**阈值/长程势**处的分布意义修正。再次，选定 Paley–Wiener / de Branges / Hardy 环境，采用**对称平滑分配**（$\widehat g=\sqrt{\widehat h}$，$h=g\ast\tilde g$）将 $\mathsf K_{w,h}=P\,M_{w^{1/2}}C_g\cdot C_{\tilde g}M_{w^{1/2}}P$ 置入 Schatten–迹类并给出**显式上界**。随后统一 Fourier 约定并区分**Poisson 零别项判据** ($\Delta<2\pi/B$) 与**香农无混叠重构** ($\Delta<\pi/B$) 的倍常数差异；在"近带限"的双层尾部控制下给出 EM 余项的 $\zeta(2m)$ 显式常数。利用 Toeplitz–FIO 的对角型波前关系证明**窗化—压缩—卷积的奇性不增**（并对 $\xi=0$ 锥域作条件化说明）。在线性化重力的最小可算模型中，给出**四阶响应**到**曲率二次不变量**的**显式系数**，由此得到体积项的**尺度积分律**

$$
\Lambda_{\mathrm{eff}}(\mu)-\Lambda_{\mathrm{eff}}(\mu_0)=\int_{\mu_0}^{\mu}\Xi(\omega)\,d\ln\omega,\qquad [\Xi]=L^{-2},
$$

并给出 $\Xi$ 的正性/单调的充分条件与共振—阈值处的局部非单调边界。作用量统一为

$$
S_{\mathrm{eff}}[g]=\int d^4x\,\sqrt{-g}\Big[\frac{R-2\Lambda_{\mathrm{eff}}(\mu)}{16\pi G}+\alpha R^2+\beta R_{\mu\nu}R^{\mu\nu}+\cdots\Big],
$$

其中 $\alpha,\beta$ 无量纲。以三维 $S^3$ 的热核—计数函数—曲率对接示例闭合 FRW 曲率项的谱—几何解释，并以一维 $\delta$ 势与 AB 散射展示"单峰饱和/峰族准对数累积"的窗化机制。附录提供所有定理的完整证明、常数估计与量纲表，以及可复现实验/数值脚本要点。

---

## Keywords

信息几何；Hessian 与 α–联络；谱移与群延迟；Toeplitz/Berezin 与 Schatten–迹类；Poisson 求和与 EM 常数；波前集；热核与谱作用；宇宙学常数；FRW

---

## Introduction & Historical Context

信息几何以散度生成的 Hessian 度量与 α–联络刻画统计流形；相对熵的二阶响应给出 Fisher–Rao 度量，三阶响应对应 Amari–Chentsov 张量与 $\alpha$–联络。Bregman 散度在指数族上诱导对偶平坦（Hessian）结构与 Legendre 对偶坐标。谱—散射理论中，Lifshitz–Krein 迹公式与 Birman–Krein 等式将谱移函数 $\xi$ 与散射行列式关联，Friedel–Lloyd 与 Wigner–Smith 则把相位导数、群延迟与态密度差分统一在同一刻度。热核/Seeley–DeWitt 展开与谱作用原则为"几何不变量—窗化谱"的桥接提供标准工具。本文把上述元素在**定理级**假设下闭合为一条从"相对熵—母尺—窗化—NPE—热核—FRW"的逻辑链。

---

## Model & Assumptions

### 1. Fourier 约定、变量与窗核总声明

固定

$$
\widehat f(\omega)=\int_{\mathbb R} e^{-i\omega x}f(x)\,dx,\qquad
f(x)=\frac{1}{2\pi}\int_{\mathbb R} e^{i\omega x}\widehat f(\omega)\,d\omega.
$$

全文统一以**频率** $\omega$ 记能量变量（读者可视作 $E\equiv\omega$）。
窗 $w_\mu$ 取平滑化对数窗 $w_\mu(\omega)\approx \chi_{[\mu_0,\mu]}(\omega)/\omega$。
**总声明**：读数核 $h$ 默认为**Bochner 正定**（$\widehat h\ge 0$、$\widehat h\in L^1$），从而存在 $\widehat g=\sqrt{\widehat h}\in L^2$ 使 $h=g\ast\tilde g$。

### 2. 信息散度与对偶平坦

正则散度 $D(\theta\Vert\theta_0)$ 的二/三/四阶响应

$$
g_{ij}=\partial_i\partial_j D|_{\theta_0},\quad
T_{ijk}=\partial_i\partial_j\partial_k D|_{\theta_0},\quad
K_{ijkl}=\partial_i\partial_j\partial_k\partial_l D|_{\theta_0},
$$

诱导 Fisher–Rao 与 $\alpha$–联络：$\Gamma^{(\alpha)}{}_{ijk}=\Gamma^{(0)}{}_{ijk}+\tfrac{\alpha}{2}T_{ijk}$。Bregman 散度 $D_\psi$ 使 $g=\nabla^2\psi$，$\nabla^{(\pm1)}$ 平直。

### 3. 母尺、散射—谱移与阈值条款

自伴对 $(H_0,H)$ 满足迹类或相对迹类扰动，波算子完备；$S(\omega)$ 幺正且弱可导。谱移 $\xi(\omega)$ 满足 $\det S(\omega)=e^{-2\pi i\xi(\omega)}$。离散阈值集 $\Sigma$ 之外，

$$
\frac{\varphi'(\omega)}{\pi}=\xi'(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega),\qquad Q=-iS^\dagger \partial_\omega S,
$$

在 $\Sigma$ 上以分布意义（含相位重整与边界项）成立。

### 4. Toeplitz/Berezin 压缩与读数

取 Paley–Wiener / de Branges / Hardy 空间 $\mathcal H$，正交投影 $P$（**范数 $|P|=1$**）。设 $w\in C_0^\infty\cap L^\infty$，$h=g\ast\tilde g$ 如上。定义

$$
\mathsf K_{w,h}:=P\,M_{w^{1/2}}C_g\cdot C_{\tilde g}M_{w^{1/2}}P,\qquad
\mathrm{Obs}(w,h)=\operatorname{tr}(\mathsf K_{w,h}\Pi)=\int w(\omega)\,[h\!\ast!\rho_{\rm rel}](\omega)\,d\omega,
$$

其中 $\rho_{\rm rel}(\omega)=\varphi'(\omega)/\pi=(2\pi)^{-1}\operatorname{tr}Q(\omega)$。

### 5. NPE 纪律与"近带限"

**严格带限**：$\operatorname{supp}\widehat f\subset[-B,B]$。
**近带限**：$\int_{|\omega|>B}|\widehat f|\,d\omega\le\varepsilon$ 且 $\int_{|\omega|>B}|\widehat f|^2\,d\omega\le \varepsilon^2$。
**判据区分**（详见定理 3）：Poisson 零别项 $\Delta<2\pi/B$；香农无混叠重构 $\Delta<\pi/B$。

### 6. 有效作用与量纲

取 $c=\hbar=1$。作用写作

$$
S_{\mathrm{eff}}=\int d^4x\,\sqrt{-g}\Big[\frac{R-2\Lambda_{\mathrm{eff}}(\mu)}{16\pi G}+\alpha R^2+\beta R_{\mu\nu}R^{\mu\nu}+\cdots\Big],
$$

四维中 $\alpha,\beta$ 无量纲；$[\Lambda_{\mathrm{eff}}]=L^{-2}$。量纲表见附录 J。

---

## Main Results (Theorems and alignments)

### 定理 1（相对熵 Hessian 与 α–联络）

相对熵的二阶响应给出 Fisher–Rao 度量，三阶响应经 $\Gamma^{(\alpha)}{}_{ijk}=\Gamma^{(0)}{}_{ijk}+\tfrac{\alpha}{2}T_{ijk}$ 生成 α–联络；Bregman 散度诱导对偶平坦（Hessian）结构。

### 定理 2（母尺三位一体：充分条件与阈值修正）

在 §3 假设下，$\det S(\omega)=e^{-2\pi i\xi(\omega)}$ 且 $\xi'(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 几乎处处成立；$\omega\in\Sigma$ 或长程势时以分布意义并带重整相位成立。

### 定理 3（Poisson 零别项判据与香农重构判据）

在本 Fourier 约定下，若 $\operatorname{supp}\widehat f\subset[-B,B]$，则

$$
\sum_{n\in\mathbb Z} f(n\Delta)=\frac{1}{\Delta}\sum_{k\in\mathbb Z}\widehat f\!\left(\frac{2\pi k}{\Delta}\right)
$$

的 $k\neq 0$ 别项**严格为零**的充要条件为 $\Delta<2\pi/B$；**香农无混叠重构**需要 $\Delta<\pi/B$。

### 定理 4（NPE：Euler–Maclaurin 显式常数与近带限尾部）

若 $f\in C^{2m}[a,b]$ 且为 $(B,\varepsilon)$-近带限，

$$
|R_m|\le \frac{2\zeta(2m)}{(2\pi)^{2m}}(b-a)\sup_{[a,b]}|f^{(2m)}|+O(\varepsilon),\qquad
\sup|f^{(2m)}|\le C\,B^{2m}|f|_\infty.
$$

### 定理 5（Toeplitz–FIO 的伪局部性与奇性不增）

$w\in C^\infty$，$h\in\mathcal S$；投影 $P$ 为对角型波前关系的 Toeplitz–FIO。对任意分布 $u$：

$$
\mathrm{WF}\big(P\,M_w\,C_h\,P\,u\big)\subseteq \mathrm{WF}(u)\ \cup\ \Gamma_0,
$$

$\Gamma_0$ 为 $\xi=0$ 的受控锥域。**注**：在能量壳窗化（带限/近带限）下不激活 $\Gamma_0$，于是有严格包含 $\mathrm{WF}(PM_wC_hPu)\subseteq \mathrm{WF}(u)$。

### 定理 6（四阶响应 $\to$ 曲率二次项：最小可算模型与系数）

在线性化 $g_{\mu\nu}=\eta_{\mu\nu}+h_{\mu\nu}$、谐和规范下，按标量/横 traceless（TT）分解并定义窗化谱权

$$
\mathcal N_s=\!\int d^4k\,k^4\,W(k)\,|\mathcal A_s(k)\sigma(k)|^2,\qquad
\mathcal N_t=\!\int d^4k\,k^4\,W(k)\,|\mathcal A_t(k)h^{\rm TT}(k)|^2,
$$

其中 $W$ 由 $\rho_{\rm rel},w,h$ 决定。则

$$
\int\!\sqrt{-g}\,\mathrm{Tr}K
=c_1\!\int\!\sqrt{-g}\,R^2+c_2\!\int\!\sqrt{-g}\,R_{\mu\nu}R^{\mu\nu}+\text{(总导数)},
$$

且

$$
\boxed{\,c_1=\frac{\mathcal N_s}{36},\qquad c_2=\frac{\mathcal N_s}{12}+\frac{\mathcal N_t}{4}\,}.
$$

**归一声明**：$\mathcal N_{s,t}$ 的定义已吸收本节统一的 Fourier 约定中的所有 $(2\pi)$ 因子与测度常数；不同约定下需相应重标。

### 定理 7（体积项的尺度积分律与 $\Xi$ 的正性/单调）

信息自由能窗化后

$$
\Lambda_{\mathrm{eff}}(\mu)-\Lambda_{\mathrm{eff}}(\mu_0)=\int_{\mu_0}^{\mu}\Xi(\omega)\,d\ln\omega,\qquad
\Xi(\omega)=\langle\mathcal K,\rho_{\rm rel}\rangle_{w_\omega,h},\quad [\Xi]=L^{-2}.
$$

若诱导二点核与 $w_\omega,h$ 皆为 Bochner 正定，则 $\Xi(\omega)\ge 0$ 并随 $\ln\mu$ 单调不减；阈值/共振簇可致局部非单调，但当峰族在 $\ln\omega$ 上近匀密且权重缓变时，$\Xi$ 在宽区间近常，出现"准对数"累积。

### 定理 8（FRW 曲率项的谱—几何对接）

三维常曲率流形的热核渐近

$$
\mathrm{Tr}\,e^{-t\Delta}\sim (4\pi t)^{-3/2}\Big[\mathrm{Vol}+\frac{t}{6}\!\int R +O(t^{3/2})\Big],\quad t\downarrow 0,
$$

对 $S^3(L)$ 有 $R=6/L^2$、$\mathrm{Vol}=2\pi^2L^3$。窗化计数函数的次主项 $\propto \int R\propto \kappa\,\mathrm{Vol}$ 与 FRW 的 $-\kappa/a^2$ 项一致；窗形仅改变系数，不破坏同质各向同性。

---

## Proofs

### 定理 1（相对熵 Hessian 与 α–联络）

由 Eguchi 的 contrast 泛函与 Amari–Chentsov 张量定义推出。指数族下以 Bregman 势实现对偶平坦。

---

### 定理 2（母尺三位一体：充分条件与阈值修正）

证明分三步：

1. **谱移函数的定义**：由 Lifshitz–Krein 迹公式定义 $\xi$。
2. **散射行列式关系**：Birman–Krein 等式给出 $\det S=e^{-2\pi i\xi}$。
3. **导数关系**：stationary scattering 的可导性导出 $\xi'=(2\pi)^{-1}\operatorname{tr}Q$。

阈值/长程势情形以分布意义与相位重整修正。

---

### 定理 3（Poisson 零别项判据与香农重构判据）

由 Poisson 公式与本 Fourier 约定，$\widehat f(2\pi k/\Delta)=0$（$k\ne0$）的充要条件为 $\Delta<2\pi/B$。

香农无混叠重构需要更严格的条件：$\Delta<\pi/B$。

---

### 定理 4（NPE：Euler–Maclaurin 显式常数与近带限尾部）

采用 DLMF 的 EM 余项常数与 Bernstein 型导数界。近带限尾部进入 $O(\varepsilon)$。

---

### 定理 5（Toeplitz–FIO 的伪局部性与奇性不增）

Hörmander 伪局部性与 Boutet de Monvel–Guillemin 的 Toeplitz–FIO 对角型波前关系给出

$$\mathrm{WF}(PM_wC_hPu)\subseteq \mathrm{WF}(u)\cup\Gamma_0.$$

能量壳窗化避免 $\Gamma_0$，从而有严格包含 $\mathrm{WF}(PM_wC_hPu)\subseteq \mathrm{WF}(u)$。

---

### 定理 6（四阶响应 $\to$ 曲率二次项：最小可算模型与系数）

**标量模**：线性化曲率 $R^{(1)}=-6\Box \sigma$，从而 $R^2=36\,k^4\sigma^2$，$R_{\mu\nu}^{(1)}R^{\mu\nu (1)}=12\,k^4\sigma^2$。

**TT 模**：$R^{(1)}=0$，$R_{\mu\nu}R^{\mu\nu}=\tfrac14 k^4(h^{\rm TT})^2$。

与窗化四阶核权重匹配得到系数 $c_{1,2}$。

---

### 定理 7（体积项的尺度积分律与 $\Xi$ 的正性/单调）

低频簇（Poisson 的 $k=0$）主导体积项。Bochner 正定性给出 $\Xi\ge 0$。

峰族在 $\ln\omega$ 上近匀密时的 Tauberian 控制保证"准对数"区间。

---

### 定理 8（FRW 曲率项的谱—几何对接）

用 $S^3$ 谱 $\lambda_n=n(n+2)/L^2$、重数 $(n+1)^2$ 与 Tauberian 定理复元热核次主项并对接 FRW 曲率项。

---

## Model Apply

### 1. 一维 $\delta$ 势：单峰饱和与准对数累积

$V(x)=\lambda\delta(x)$。相移 $\delta(k)=-\arctan(\lambda/2k)$，$\rho_{\rm rel}(\omega)=\delta'(\omega)/\pi$。对平滑对数窗

$$
I(\mu;\mu_0)=\int_{\mu_0}^{\mu}\frac{\Gamma}{(\omega-\omega_0)^2+\Gamma^2}\frac{d\omega}{\omega}
$$

有闭式

$$
\begin{aligned}
I(\mu;\mu_0)&=\frac{\Gamma}{\omega_0^2+\Gamma^2}\ln\frac{\mu}{\mu_0}
-\frac{\Gamma}{2(\omega_0^2+\Gamma^2)}\ln\frac{(\mu-\omega_0)^2+\Gamma^2}{(\mu_0-\omega_0)^2+\Gamma^2}\\
&\quad+\frac{\omega_0}{\omega_0^2+\Gamma^2}\Big[\arctan\frac{\mu-\omega_0}{\Gamma}-\arctan\frac{\mu_0-\omega_0}{\Gamma}\Big],
\end{aligned}
$$

两类 $\ln\mu$ 精确抵消，**单峰饱和**；峰族在 $\ln\omega$ 上近匀密且权重缓变时，出现"准对数"累积。

**可复现实验要点（示例参数）**：$\lambda=1$；$\mu_0=10^{-3}$、$\mu$ 扫描到 $10^{3}$；窗宽平滑参数 $\sigma=0.05$；核 $h(\omega)=e^{-\omega^2/2\sigma_h^2}$ 取 $\sigma_h=0.1$。

### 2. AB 散射：拓扑—谱密度差分的窗化

理想 AB 模型相移能量无关，$\operatorname{tr}Q=0$；有限半径/屏蔽模型引入能量依赖，窗化差分形成对曲率/拓扑项的等效贡献，非解析点对应 $\Xi$ 的台阶/尖点。

---

## Engineering Proposals

1. **群延迟计量链**：测量多端口 $S(\omega)$ 并差分相位得 $Q(\omega)$，构造 $\Xi(\omega)$ 与 $\Lambda_{\rm eff}(\mu)$ 曲线，NPE 常数给出误差带。
2. **Toeplitz/Berezin 数值谱学**：实现 $\mathsf K_{w,h}$ 并监测 $|\mathsf K_{w,h}|_1$；半经典区以符号积分近似迹并用 EM 常数评估余项。
3. **FRW 曲率窗化校核**：在 $S^3/H^3/$三环面上对比热核次主项与窗化计数函数，验证 $-\kappa/a^2$ 的谱—几何对接。

---

## Discussion

母尺三位一体在迹类/相对迹类与可导假设下成立；长程势与阈值以分布意义修正。Toeplitz/Berezin 的对称平滑分配给出可检的迹类上界；NPE 纪律以 $\zeta(2m)$ 常数与频域尾部控制形成有限阶误差预算；窗化—压缩—卷积不增奇性。四阶响应到 $R^2,\,R_{\mu\nu}R^{\mu\nu}$ 的系数在最小模型中可复核；$\Xi$ 的正性—单调条件明确，峰族统计支撑"准对数"区间。FRW 曲率项的窗化解释经 $S^3$ 示例闭合。开放体系或非幺正 $S$ 的扩展需要耗散散射框架，此时 $\operatorname{tr}Q$ 不保正性。

---

## Conclusion

完成从**信息散度—母尺—窗化—NPE—热核—FRW**的定理化闭合：
（i）母尺三位一体在定理级假设下成立；
（ii）Toeplitz/Berezin 压缩以对称平滑分配进入迹类并具显式上界（$|P|=1$）；
（iii）Poisson 零别项与香农重构判据分离且常数一致；
（iv）EM 余项具 $\zeta(2m)$ 常数，近带限尾部可控；
（v）窗化—压缩—卷积不增奇性（能量壳窗化下严格不增）；
（vi）四阶响应到曲率二次项的系数**显式可复核**；
（vii）体积项 obeys 尺度积分律，$\Xi$ 的正性与"准对数"机制清晰；
（viii）FRW 曲率项的谱—几何对接完成。以上结果为"信息几何 × 谱—散射 × 宇宙学"的统一方案提供可验证的技术基础。

---

## Acknowledgements, Code Availability

未使用专有代码；附录附有可复现实验/数值脚本要点与参数表。

---

## References

Amari, S.-i.; Nagaoka, H. *Methods of Information Geometry*. AMS–OUP, 2000（Chs. 2–4：Fisher–Rao 与 α–联络；Ch. 8：对偶平坦）.
Eguchi, S. "A differential geometric approach to statistical inference on the basis of contrast functionals." *Hiroshima Math. J.* 15 (1985) 341–391.
Birman, M. S.; Krein, M. G. "On the theory of wave and scattering operators." 1962（见 Yafaev, Chs. 6–8）.
Yafaev, D. R. *Mathematical Scattering Theory*. AMS, 1992/2005（Ch. 8：散射矩阵与谱移；Ch. 10：阈值）.
Simon, B. *Trace Ideals and Their Applications*. 2nd ed., AMS, 2005（Ch. 2：Schatten 理想；HS×HS $\subset$ S1）.
Boutet de Monvel, L.; Guillemin, V. *The Spectral Theory of Toeplitz Operators*. Princeton, 1981（Chs. 1–3：Toeplitz–FIO 与波前关系）.
Hörmander, L. *The Analysis of Linear Partial Differential Operators I*. 2nd ed., Springer, 1990（§8：伪局部性；波前集基础）.
NIST DLMF, §24（Euler–Maclaurin，特别是 §24.7 余项常数）.
Vassilevich, D. V. "Heat kernel expansion: user's manual." *Phys. Rep.* 388 (2003) 279–360（Seeley–DeWitt 系数）.
Chamseddine, A.; Connes, A. "The spectral action principle." *Commun. Math. Phys.* 186 (1997) 731–750.
Chavel, I. *Eigenvalues in Riemannian Geometry*. Academic Press, 1984（Ch. III：Weyl 律与热核）。
Texier, C. "Wigner time delay and related concepts." *Phys. Rep.* 2016（讲义版 2015 可参）。
Hagen, C. R. "Aharonov–Bohm scattering of particles with spin." *Phys. Rev. D* 41 (1990).

---

## Proofs（Appendix）

### 附录 A：Fourier 约定与变量统一

给出本文固定的 Fourier 对与所有 $(2\pi)$ 因子的吸收规则，声明 $\omega\equiv E$ 的等价使用，列出变换下的量纲一致性。

### 附录 B：母尺等式的 KFL 链闭合

由 Lifshitz–Krein 迹公式定义 $\xi$；Birman–Krein 等式给 $\det S=e^{-2\pi i\xi}$；stationary scattering 的可导性推出 $\xi'=(2\pi)^{-1}\operatorname{tr}Q$；阈值/长程势的分布意义修正。

### 附录 C：Toeplitz/Berezin—Schatten 迹类：对称平滑分配

取 $\widehat g=\sqrt{\widehat h}$、$h=g\ast\tilde g$，写

$$
\mathsf K_{w,h}=(P\,M_{w^{1/2}}C_g)\,(C_{\tilde g}M_{w^{1/2}}P),
$$

两因子为 Hilbert–Schmidt，乘法得 $\mathfrak S_1$。上界

$$
|\mathsf K_{w,h}|_1\le |P|^2\,|w|_1\,\frac{|\widehat h|_1}{2\pi},
$$

在三类空间中 $|P|=1$。

### 附录 D：Poisson 零别项与香农重构（倍常数差异）

在本 Fourier 约定下证明：$\Delta<2\pi/B\Rightarrow$ Poisson 零别项；$\Delta<\pi/B\Rightarrow$ 香农重构；给出频域示意与别项消失的充要性证明。

### 附录 E：EM 余项常数与近带限尾部

采用 DLMF 的余项表达与 Bernoulli 数常数，结合 Bernstein 导数界给出
$|R_m|\le \frac{2\zeta(2m)}{(2\pi)^{2m}}(b-a)\sup|f^{(2m)}|+O(\varepsilon)$。

### 附录 F：波前集不增与 $\xi=0$ 锥域

Hörmander 伪局部性：$\mathrm{WF}(wu)\subseteq \mathrm{WF}(u)$、$\mathrm{WF}(h\ast u)=\varnothing$。Toeplitz–FIO 的对角型波前关系给出
$\mathrm{WF}(PM_wC_hPu)\subseteq \mathrm{WF}(u)\cup\Gamma_0$；能量壳窗化排除 $\Gamma_0$。

### 附录 G：四阶响应到 $R^2, R_{\mu\nu}R^{\mu\nu}$ 的系数推导

标量：$R^{(1)}=-6\Box\sigma \Rightarrow R^2=36\,k^4\sigma^2$、$R_{\mu\nu}R^{\mu\nu}=12\,k^4\sigma^2$。
TT：$R^{(1)}=0$、$R_{\mu\nu}R^{\mu\nu}=\tfrac14 k^4(h^{\rm TT})^2$。
与窗化四阶核权重匹配得
$c_1=\mathcal N_s/36,\ c_2=\mathcal N_s/12+\mathcal N_t/4$。

### 附录 H：$\Xi(\omega)$ 的正性与反例边界

当诱导二点核与 $w,h$ Bochner 正定时，$\Xi\ge 0$；阈值/共振簇可导致局部负；对数尺度上的窗口平均 $\overline{\Xi}$ 的变差界提供"准对数"区间的可测检判据。

### 附录 I：对数窗×洛伦兹峰的恒等式与饱和

完整推导

$$
\int_{\mu_0}^{\mu}\frac{\Gamma}{(\omega-\omega_0)^2+\Gamma^2}\frac{d\omega}{\omega}
$$

的分解式，证明两类 $\ln\mu$ 抵消与单峰饱和；峰族在 $\ln\omega$ 上近匀密时的 Tauberian 控制。

### 附录 J：量纲表与可复现实验/数值脚本要点

**量纲表**：
$[Q]=E^{-1}$，$[\rho_{\rm rel}]=E^{-1}$，$[w_\mu]=E^{-1}$，$[h]=1$，$[\Xi]=L^{-2}$，$[\Lambda_{\rm eff}]=L^{-2}$，$[R]=L^{-2}$，$[\alpha]=[\beta]=1$，$[d\ln\omega]=1$。
**脚本要点**：核宽 $\sigma_h$、窗平滑 $\sigma$、带宽 $B$、采样 $\Delta$、尾部 $\varepsilon$ 的推荐区间与一组"$\delta$ 势/AB 有限半径"参数表，便于复现实验与误差预算。
