# 量子引力场：以窗化散射相位—延迟—谱移为刻度的统一理论

*Quantum Gravitational Field as a Windowed Scattering Phase–Delay–Spectral-Shift Measure*

**Version v0.7, 2025-10-28**

---

## 摘要

本文提出一套**完全以可观测量刻度**的量子引力场理论：对给定时空几何 $g$ 与参考几何 $g_0$，以其定能散射矩阵 $S_g(E)$ 的能量导数所定义的 **Wigner–Smith 延迟算子** $Q_g(E)=-i\,S_g(E)^\dagger \partial_E S_g(E)$ 为核心，定义**相对态密度**（relative density of states, rDOS）

$$
\rho_{\mathrm{rel}}[g:g_0](E)\;=\;\frac{1}{2\pi i}\,\mathrm{tr}\!\big(S_g^\dagger \partial_E S_g\big)\;=\;\frac{1}{2\pi}\,\mathrm{tr}\,Q_g(E).
$$

在满足 Birman–Kreĭn（BK）公式 $\det S_g(E)=\exp[-2\pi i\,\xi_g(E)]$ 的**幺正散射**框架下，有 $\rho_{\mathrm{rel}}[g:g_0](E)=-\xi_g'(E)$，其中 $\xi_g$ 为 Kreĭn 谱移函数；这统一了**相位—延迟—谱移**三者的刻度关系，并与 Friedel/Smith 关系一致。**含吸收（非幺正）时**，改用**相位部分态密度** $\rho_{\mathrm{rel}}[g:g_0]^{(\mathrm{phase})}(E)=\frac{1}{2\pi}\partial_E\arg\det S_g(E)$，并以总复延迟 $\tau_{\mathrm{tot}}$ 的虚部刻画吸收强度。注：本文中 $Q=-iS^\dagger\partial_E S$ 的自然单位为能量$^{-1}$，物理时间延迟为 $\hbar Q$。我们以**窗化观测**实现实验分辨率内的可测读数：选取满足 Wexler–Raz 双正交与 Gabor 帧必要密度（$\Delta E\,\Delta t/(2\pi\hbar)\le 1$）的窗—对偶核 $(w,\tilde w)$，定义

$$
\mathcal N_{w}[g:g_0;E_0]\;=\;\int_{\mathbb R} w(E-E_0)\,\rho_{\mathrm{rel}}[g:g_0](E)\,dE,
$$

并给出**窗化 BK 恒等式**与**非渐近误差三分解**（混叠/Poisson＋伯努利层/Euler–Maclaurin＋截断）。在渐近平直/双曲流形的几何散射、定常弱场的 Shapiro 引力时延、及含吸收（如黑洞外区）的非幺正散射中，我们证明：(**不变性**) 对微分同胚/幺正等价不变；(**可加性**) 级联散射的 rDOS 可加；(**半经典极限**) 窗化 rDOS 由周期测地流长度谱控制，并在低频极限回到经典驻留时间与 Shapiro 时延。本文并给出面向数值的可复现实验流程与既有量子引力/S-matrix/几何散射文献的接口。

---

## 关键词

Wigner–Smith 延迟；Krein 谱移；Birman–Kreĭn 公式；Friedel/Smith 关系；窗化观测；Gabor/Weyl–Heisenberg 框架；Landau 采样密度；流形散射；Shapiro 延迟

---

## 1. 引言（以可观测量刻度）

散射相位与能量导数给出 DOS 的事实自 Beth–Uhlenbeck 与 Friedel 以来已广泛确立；在现代散射理论中，这由 BK 公式严格化为

$$
\det S(E)=e^{-2\pi i\,\xi(E)},\qquad
\xi'(E)=-\tfrac{1}{2\pi i}\mathrm{tr}\!\big(S^\dagger \partial_E S\big),
$$

因而 $\rho_{\mathrm{rel}}[g:g_0](E)=\frac{1}{2\pi i}\mathrm{tr}(S_g^\dagger \partial_E S_g)=-\xi_g'(E)$。这同时等价于以 Wigner–Smith 延迟算子 $Q_g=-iS_g^\dagger \partial_E S_g$ 计量的驻留时间总和。**限定**：上述等价链仅当 $S(E)$ 幺正（$S^\dagger S=I$）时成立；含吸收/泄露时，改用相位部分态密度 $\rho_{\mathrm{rel}}^{(\mathrm{phase})}=\tfrac{1}{2\pi}\partial_E\arg\det S$ 与总复延迟 $\tau_{\mathrm{tot}}=-i\,\partial_E\log\det S$（见 §5）。上述等价在数学物理中具有标准而严密的表述，在物理上与 Friedel/Smith 关系吻合。

几何散射方面，对渐近平直/长程度量/双曲几何之拉普拉斯–Beltrami（或 Klein–Gordon）算子存在完备的能量壳散射矩阵与微局部结构；散射矩阵在能量纤维上是与无穷远测地流相关的 Fourier 积分算子，这为将 DOS 的几何来源解释为**谱流**提供了严格基础。

本文主张：**量子引力场**可操作地定义为**窗化的相对态密度**，即 $\rho_{\mathrm{rel}}[g:g_0](E)$ 及其在仪器分辨率内的读数 $\mathcal N_w[g:g_0;E_0]$。该定义基于可观测的散射矩阵 $S_g(E)$，通过 $\arg\det S_g$ 的能量导数或 Wigner–Smith 延迟算子 $Q_g$ 的迹计量，天然具备：(i) 微分同胚/幺正等价下不变；(ii) 级联散射的可加性；(iii) 半经典极限与波迹/测地谱的 Poisson 关系；(iv) 非幺正散射（吸收）的复延迟推广。

---

## 2. 设定与记号

### 2.1 几何、算子与站立假设

设 $(M,g)$ 为带一个或多个非紧端的光滑流形，满足渐近 Euclid（或渐近双曲/长程）条件；令 $H_g=-\Delta_g$（或含合适短/长程势的自伴变体）。取参考几何 $(M,g_0)$ 与 $H_{g_0}$。

**站立假设（全文适用）**：假设成对 $(H_g,H_{g_0})$ 满足**相对迹类**条件，即存在 $z\in\rho(H_{g_0})$ 使

$$
(H_g-H_{g_0})(H_{g_0}-z)^{-1}\in\mathfrak{S}_1,
$$

其中 $\mathfrak{S}_1$ 为迹类算子理想。在此条件下，谱移函数 $\xi_g(E)$ 与能量壳散射矩阵 $S_g(E)$ 良定，且 BK 公式 $\det S_g(E)=e^{-2\pi i\xi_g(E)}$ 成立；此处 $\det S_g$ 为 BK 意义下的**扰动行列式**（Fredholm/det$_1$ 型）。**本文所有 BK 公式、谱移函数恒等式与相对迹表达式均在此假设下理解。** 对非迹类但可允许相对光滑/耗散扩展的情形，可采用相应的推广框架。

**参考几何 $g_0$ 的标定与选择**：实验/天文对接时，参考几何 $g_0$ 应选为**已知标准背景**（如 Minkowski 平直时空、Schwarzschild 解、或渐近平直流形的标准渐近锥）。关键原则：

(i) **相对迹类保证**：$g$ 与 $g_0$ 的差须满足上述迹类条件（或可追化/相对光滑条件）；

(ii) **可比性**：不同观测应对同一物理情形选用同一 $g_0$，确保 $\rho_{\mathrm{rel}}[g:g_0]$ 的**比较意义**；

(iii) **窗化标定**：窗对 $(w,\tilde w)$ 的带宽 $\Delta E$ 与时域宽度 $\Delta t$ 应与仪器分辨率/观测时标匹配（见 §2.3 与 §9）；

(iv) **相位基准**：对 $\arg\det S$ 执行相位解卷绕（附录 A 伪代码）时，需以 $E_{\min}$ 处相位为基准并累积跟踪，避免任意 $2\pi$ 跳变。

**不依赖性说明**：$\rho_{\mathrm{rel}}[g:g_0]$ 定义依赖于 $g_0$ 选择（"相对"概念固有），但在**窗化观测**与**级联可加性**（定理 3.3）下，不同 $g_0$ 选择的**差异可控**：背景平移恒等式为

$$
\boxed{\;\rho_{\mathrm{rel}}[g:g_0]-\rho_{\mathrm{rel}}[g:g_0']=\rho_{\mathrm{rel}}[g_0':g_0]\;},
$$

其中左侧为目标几何 $g$ 相对于两个不同参考 $g_0$ 与 $g_0'$ 的 rDOS 差，右侧为固定背景差项，在比较不同 $g$ 时系统性消除。实验中应固定 $g_0$ 为标准背景（如平直或已知解），使绝对标定可追溯。

### 2.2 以 rDOS 定义量子引力场

$$
\boxed{\;\rho_{\mathrm{rel}}[g:g_0](E)\;=\;\frac{1}{2\pi i}\,\mathrm{tr}\!\big(S_g^\dagger \partial_E S_g\big)\;=\;\frac{1}{2\pi}\,\mathrm{tr}\,Q_g(E)\;=\;-\xi_g'(E)\quad\text{（幺正）};}
$$

其中 $Q_g(E)=-iS_g^\dagger \partial_E S_g$ 为**能量导相延迟算子**（自然单位为能量$^{-1}$，**物理时间延迟为** $\hbar Q_g$），下标 $g$ 隐含相对于参考背景 $g_0$ 的散射矩阵。此定义等价于能量分辨的总驻留时间密度，亦即"几何相对 DOS"。

**适用性**：上述 $\rho_{\mathrm{rel}}[g:g_0]=-\xi_g'(E)$ 与 $\frac{1}{2\pi}\mathrm{tr}\,Q$ 的等价性**仅在 $S_g$ 幺正时成立**（要求 $S_g^\dagger S_g=I$，即无吸收散射）；含吸收时改用**相位部分态密度**
$$
\rho_{\mathrm{rel}}[g:g_0]^{(\mathrm{phase})}(E)=\frac{1}{2\pi}\,\partial_E\arg\det S_g(E)=\frac{1}{2\pi}\,\mathrm{Im}\,\partial_E\log\det S_g(E),
$$
并以 $\mathrm{Im}\,\tau_{\mathrm{tot}}(E)=-\partial_E\log|\det S_g|$ 刻画吸收强度（详见 §5）。

### 2.3 窗化观测与对偶窗

**Fourier 规范声明**：本文固定能量—时间 Fourier 对偶为

$$
\widehat{f}(t)=\frac{1}{2\pi\hbar}\int_{\mathbb R} f(E)\,e^{-iEt/\hbar}\,dE,\qquad
f(E)=\int_{\mathbb R}\widehat{f}(t)\,e^{iEt/\hbar}\,dt;
$$

凡涉及 $\widehat{w}$、Poisson 求和与 Gabor 密度的常数/相位，均以此规范计量。

取 $w\in\mathcal S(\mathbb R)\cap L^1$ 为能量窗（无量纲归一化），$\tilde w$ 为其 Gabor 对偶。在能量—时间 $(E,t)$ 表示中，取调制算子 $M_\tau f(E)=e^{i\tau E/\hbar}f(E)$。采用**规范化内积** $\langle f,g\rangle_{E}=\frac{1}{2\pi\hbar}\int_{\mathbb R}\overline{f(E)}g(E)\,dE$（带度量因子 $1/(2\pi\hbar)$，确保归一化常数无量纲）。

对窗对 $(w,\tilde w)$ 与格点步长 $(\Delta E,\Delta t)$，记平移算子 $T_a f(E)=f(E-a)$（$a$ 为**能量**参数），调制算子 $M_\tau f(E)=e^{i\tau E/\hbar}f(E)$（$\tau$ 为**时间**参数）。**Wexler–Raz 双正交**的无求和版本（在**对偶格点**上表述）为

$$
\boxed{\begin{aligned}
&\Big\langle \tilde w,\, M_{m\,\Delta t_\circ}\,T_{n\,\Delta E_\circ}\,w\Big\rangle_{E}
=\delta_{m0}\,\delta_{n0}, \\[4pt]
&\text{适用前提：}\;\boxed{\Delta E\,\Delta t=2\pi\hbar}\;\text{（临界密度）},\quad (w,\tilde w)\;\text{Riesz 双对偶基}; \\[4pt]
&\text{对偶格点：}\;\boxed{\Delta E_\circ=\frac{2\pi\hbar}{\Delta t}}\,(\text{能量}),\quad\boxed{\Delta t_\circ=\frac{2\pi\hbar}{\Delta E}}\,(\text{时间}).
\end{aligned}}
$$

其中 $T_a$ 的参数具**能量**维度（如 $n\,\Delta E_\circ$），$M_\tau$ 的参数具**时间**维度（如 $m\,\Delta t_\circ$），对偶格点 $(\Delta E_\circ,\Delta t_\circ)$ 由能量-时间 Fourier 对偶给出。

**与标准 $(a,b)$ 形式的对照**：在标准文献的 $(a,b)$ 表示（不带度量因子的内积）下，上式对应 $a=\Delta E$，$b=\Delta t/(2\pi\hbar)$，密度条件 $ab\le 1$（必要密度）与 $ab=1$（Riesz 基临界密度）。本文采用带度量因子 $1/(2\pi\hbar)$ 的规范化内积 $\langle\cdot,\cdot\rangle_E$，因此密度条件表为 $\Delta E\,\Delta t/(2\pi\hbar)\le 1$。对一般帧（$\Delta E\,\Delta t/(2\pi\hbar)<1$），应采用 Wexler–Raz 的**求和版恒等式**（对偶格点 $\Lambda^\circ$ 上的求和形式）：

$$
\boxed{\begin{aligned}
&\sum_{(m,n)\in\mathbb Z^2}\Big\langle \tilde w,\, M_{m\,\Delta t_\circ}\,T_{n\,\Delta E_\circ}\,w\Big\rangle_{E}\,e^{i(m\sigma+n\kappa)}
= \sum_{(k,\ell)\in\mathbb Z^2}\Big\langle w,\, M_{-k\,\Delta t}\,T_{-\ell\,\Delta E}\,\tilde w\Big\rangle_{E}\,e^{i(k\sigma^\circ+\ell\kappa^\circ)}, \\[4pt]
&\text{适用前提：}\;\boxed{\Delta E\,\Delta t/(2\pi\hbar)<1}\;\text{（稠密帧）}; \\[4pt]
&\text{格点参数：}\;\boxed{\Delta E,\,\Delta t}\;\text{（抽样步长）},\quad
\boxed{\Delta E_\circ=\frac{2\pi\hbar}{\Delta t},\,\Delta t_\circ=\frac{2\pi\hbar}{\Delta E}}\;\text{（对偶格点）}; \\[4pt]
&\text{无量纲相位变量：}\;\boxed{\sigma=\tau/\Delta t_\circ,\;\kappa=E/\Delta E_\circ,\;\sigma^\circ=\tau/\Delta t,\;\kappa^\circ=E/\Delta E};\;\text{（此处 $E$ 为能量变量，与本文固定的能量—时间 Fourier 规范一致）}.
\end{aligned}}
$$

该等式适用于 $\Delta E\,\Delta t/(2\pi\hbar)<1$ 的**稠密帧**情形，可作为数值实现时的稳定重建核；临界密度情形（$\Delta E\,\Delta t=2\pi\hbar$）回退为上述无求和版本的 $\delta_{m0}\delta_{n0}$ 恒等式。完整 Gabor 帧密度理论见参考文献 [13,14]。

$^{\mathrm{†}}$ **无量纲推导**：设 $u=E/E^*$、$v=t/t^*$，取 $E^* t^*=2\pi\hbar$。标准 WR 恒等式（无量纲）为 $\langle\tilde w,M_{m/\Delta v}T_{n/\Delta u}w\rangle_u=\delta_{m0}\delta_{n0}$（临界密度 $\Delta u\Delta v=1$）。取 $E^*=\Delta E$ 得 $t^*=\frac{2\pi\hbar}{\Delta E}$；由 $v=t/t^*$ 知 $v$-域的调制步长 $1/\Delta v$ 推回 $t$-域得到的是**无量纲比值** $\frac{t^*}{\Delta t}=\frac{2\pi\hbar}{\Delta E\,\Delta t}$。在**临界密度** $\Delta E\,\Delta t=2\pi\hbar$ 下有 $\frac{t^*}{\Delta t}=1$。对应的**对偶时间步长**为 $\Delta t_\circ=t^*=\frac{2\pi\hbar}{\Delta E}$。对称地，$u$-域平移步长 $1/\Delta u$ 推回 $E$-域给出对偶能量步长 $\Delta E_\circ=\frac{2\pi\hbar}{\Delta t}$。对偶格点 $(\Delta E_\circ,\Delta t_\circ)=(2\pi\hbar/\Delta t,\,2\pi\hbar/\Delta E)$ 即能量-时间 Fourier 对偶的标准结果。

**规范化注记**：在标准文献的 $(a,b)$ 表示（不带度量因子的内积）下，上式写为 $ab\le 1$（必要密度）与 $ab=1$（Riesz 基临界密度）。本文采用带度量因子 $1/(2\pi\hbar)$ 的规范化内积，因此密度条件表为 $\Delta E\,\Delta t/(2\pi\hbar)\le 1$；此处 $a=\Delta E$，$b=\Delta t/(2\pi\hbar)$。完整 Gabor 帧密度理论见参考文献 [13,14]。

窗化读数定义为

$$
\mathcal N_{w}[g:g_0;E_0]=\int_{\mathbb R} w(E-E_0)\,\rho_{\mathrm{rel}}[g:g_0](E)\,dE.
$$

Gabor 帧的**必要密度**条件为 $\Delta E\,\Delta t/(2\pi\hbar)\le 1$（帧的必要条件）；**Riesz 基**情形取等号（$=1$）并受 Balian–Low 限制（时—频同时紧支撑不可能）。

---

## 3. 主定理（刻度与不变性）

### 定理 3.1（相位—DOS—延迟恒等式，幺正情形）

在 2.1 的假设下，**当 $S_g(E)$ 幺正**（$S_g^\dagger S_g=I$）时，

$$
\rho_{\mathrm{rel}}[g:g_0](E)=\frac{1}{2\pi i}\,\mathrm{tr}\!\big(S_g^\dagger \partial_E S_g\big)
=\frac{1}{2\pi}\,\mathrm{tr}\,Q_g(E)=-\xi_g'(E)=\frac{1}{2\pi}\,\partial_E\arg\det S_g(E).
$$

**证明（要点）**：BK 公式给出 $\log\det S_g(E)=-2\pi i\,\xi_g(E)$。微分并用 $\partial_E\log\det S=\mathrm{tr}(S^{-1}\partial_E S)=\mathrm{tr}(S^\dagger\partial_E S)$（幺正时 $S^{-1}=S^\dagger$），即
$\mathrm{tr}(S^\dagger \partial_E S)=-2\pi i\,\xi_g'(E)$，得第一与第三等号；再由 $Q=-iS^\dagger \partial_E S$ 得中间等号；幺正性保证 $\log\det S=i\arg\det S$（模 $2\pi i$ 整数），微分给出最后等号。∎

**适用性**：本定理的等价链**仅在幺正散射时成立**；含吸收时改用定义 5.1 的相位 DOS $\rho_{\mathrm{rel}}^{(\mathrm{phase})}$ 与总复延迟 $\tau_{\mathrm{tot}}$。

### 定理 3.2（窗化 BK 恒等式，幺正情形）

对任意 $h\in\mathcal S(\mathbb R)$（或 $C_c^\infty(\mathbb R)$），

$$
\int h(E)\,\rho_{\mathrm{rel}}[g:g_0](E)\,dE
= \frac{1}{2\pi i}\int h(E)\,\partial_E\log\det S_g(E)\,dE
= -\frac{1}{2\pi}\int h'(E)\,\arg\det S_g(E)\,dE.
$$

**证明**：由定理 3.1（$\rho_{\mathrm{rel}}=\frac{1}{2\pi i}\mathrm{tr}(S^\dagger\partial_E S)$）与分部积分，端点由紧支撑或快速衰减（$\mathcal S$ 类）保证消失。幺正时 $\log\det S=i\,\arg\det S$，分部积分 $\int h\,\theta'\,dE=-\int h'\,\theta\,dE$ 给出负号。此处 $\log\det S$ 取连续解卷绕的 $\arg\det S$ 分支；阈值/束缚态处的跳变以分布意义计入窗化积分。窗函数的紧支撑与光滑性保证跳变项并入 $h'$ 的分布贡献；**在数值实现中需对 $\arg\det S$ 执行相位解卷绕处理：采用连续相位跟踪（逐步累加主值间相位变化，检测 $\pm\pi$ 跳变并累加 $2\pi$ 倍数修正）；阈值附近的跳变通过窗函数导数的分布项自然并入$^{\ddagger}$**（详见附录 A）。∎

$^{\ddagger}$ **相位解卷绕提示**：对离散能量序列 $\{E_j\}$，初始化累积相位 $\Theta_0=\arg\det S(E_0)$；迭代 $\Theta_{j+1}=\Theta_j+\mathrm{wrap}[\arg\det S(E_{j+1})-\arg\det S(E_j)]$，其中 $\mathrm{wrap}[\delta]=\delta+2\pi\,\mathrm{round}(-\delta/(2\pi))$ 将相位差折回 $(-\pi,\pi]$；数值导数 $\partial_E\arg\det S|_{E_j}\approx (\Theta_{j+1}-\Theta_{j-1})/(2\Delta E)$。阈值处的 $\delta$-型跃变由窗化积分的分部项自动吸收。

### 定理 3.3（级联可加性）

**适用前提**：
- (i) 相对于同一参考 $g_0$；
- (ii) $S(E)$ 作用于同一入/出通道空间且通道匹配（同边界接触结构）；
- (iii) 采用 BK/扰动行列式 $\det_1$，且满足 $\log\det_1(S_2S_1)=\log\det_1S_2+\log\det_1S_1+2\pi i\,k(E)$（$k(E)$ 为分段常数整数）。

若相对于同一参考 $g_0$，有能量壳级联 $S_{g_2\circ g_1}(E)=S_{g_2}(E)S_{g_1}(E)$，则

$$
\rho_{\mathrm{rel}}[g_2\circ g_1:g_0]=\rho_{\mathrm{rel}}[g_2:g_0]+\rho_{\mathrm{rel}}[g_1:g_0].
$$

**证明**：$\log\det(S_2S_1)=\log\det S_2+\log\det S_1+2\pi i\,k(E)$，其中 $k(E)$ 为**分段常数整数**（对应行列式的分支选择）。对 $E$ 微分后 $k'(E)=0$（作为分布，除非在相位跃迁/束缚态阈值处可能出现 $\delta$-型跃变）。在窗化 BK 恒等式（定理 3.2，幺正情形）中，分部积分使端点/跃变项由窗函数紧支撑消去或合并到 $h'$ 中；套用定理 3.2 即得。∎

### 定理 3.4（微分同胚/幺正不变性）

若 $g'=\phi^*g$ 为**保持渐近结构/散射边界接触结构**的微分同胚拖曳，则存在幺正 $U$ 使 $S_{g'}(E)=U^\dagger S_g(E)U$。因此 $\mathrm{tr}\,Q$ 与 $\rho_{\mathrm{rel}}$ 不变。

**证明**：在渐近平直/双曲流形上，散射矩阵是与无穷远测地流相关的 Fourier 积分算子（FIO），几何散射的函子性保证：当 $\phi$ 保持散射结构时，波算子/散射矩阵在能量纤维上以幺正（微局部）共轭方式变换；迹不变性即得。∎

---

## 4. 几何散射、半经典极限与波迹

### 4.1 几何散射的能量纤维结构

**假设（FIO 结构）**：在渐近平直流形或凸余紧双曲流形上，散射度量 $g$ 与参考度量 $g_0$ 的差满足以下条件：

(i) **衰减率**：度量扰动 $|g-g_0|+r|\partial(g-g_0)| = O(r^{-\rho})$，$\rho>1$（渐近平直情形）；或凸余紧双曲背景的长程衰减条件；

(ii) **正则性**：度量及势属 $C^\infty$ 且高阶导数满足配套衰减；

(iii) **陷波（trapping）处理**：**允许陷波/束缚连续谱**（如凸余紧双曲流形、存在稳定/不稳定流形的情形），采用 **$0$-trace 正则化**（Melrose–Zworski/Guillopé–Zworski 框架）确保散射算子的 Fredholm 性质与波迹公式的适用性；

(iv) **辐射边界条件**：在无穷远处波场满足 Sommerfeld 出射条件（或渐近圆柱端上的相应条件）。

在此假设下，散射矩阵 $S_g(E)$ 是与无穷远处测地流在时间 $\pi$（对应半波群 $e^{-i\pi\sqrt{\Delta}}$）的典范变换相关的 Fourier 积分算子（FIO）；此结构与 Melrose–Zworski 散射微积分框架（渐近平直/短程）、Vasy 的长程散射理论（长程情形需作相位/测地漂移修正）及相关微局部散射理论一致$^{[1,2]}$。该 FIO 结构保证了散射矩阵在能量纤维上的微局部性质与几何不变性。**陷波情形下的共振/极点结构通过窗化观测的能量阈值与误差项自然体现**（见 §6.2 与 §9 数值流程）。

### 4.2 波迹与周期测地流（Poisson 关系）

在双曲/凸余紧背景下，波群的正则化迹（$0$-trace）满足 Poisson/Selberg-型公式：闭合测地的长度谱控制波迹奇点位置与权重；因此窗化的 $\rho_{\mathrm{rel}}$ 在半经典极限 $\hbar\to 0$ 由周期测地贡献主导。

### 定理 4.1（半经典窗化极限）

假设流形为**双曲/凸余紧背景**或渐近平直流形且周期测地轨道为**清洁交会（clean）/非退化**。取 $w$ 为尺度 $\sigma$ 的平滑窗，令 $\widehat{w}$ 支撑于 $|t|\lesssim \sigma^{-1}$。当 $\hbar\to 0$ 且 $\sigma$ 与几何注入半径/弛豫时间匹配时，

$$
\mathcal N_{w}[g:g_0;E_0]\;=\;\sum_{\gamma\in\mathcal P}\,A_\gamma(E_0)\,\widehat{w}(T_\gamma)\,e^{i S_\gamma(E_0)/\hbar}\;+\;o(1),
$$

其中 $\mathcal P$ 为周期测地族，$T_\gamma$ 其周期，$S_\gamma$ 为经典作用量，$A_\gamma$ 含稳定子与 monodromy 的标准因子。**注**：在出现陷波/轨道簇集时需 $0$-trace/配分正则化处理。

**证明（要点）**：在上述几何假设下，波群的正则化迹（**0-trace**）满足 Poisson/Selberg-型公式：奇性支撑位于长度谱 $\{T_\gamma\}$。结合定理 3.2 与波迹公式，把 $\arg\det S$ 的能量导数转化到时间域后，以平稳相位法得到；正则化与非退化条件保证级数收敛与余项估计。该陈述在几何假设"清洁/非退化周期测地"与"凸余紧/渐近平直"下严格成立$^{[3,4,5]}$。∎

### 4.3 宏观极限与 Shapiro 延迟

定常弱场中，$\mathcal N_{w}$ 的低频极限回到 Shapiro 引力时延；具体地，$\partial_E\arg\det S$ 以平均群时延表示，等价于经典传播时间的引力增量。在参数化后牛顿（PPN）框架下，对单程近轴近似（$b\ll r_i$），Shapiro 时延公式为$^{[6,7]}$

$$
\Delta t \;\approx\; (1+\gamma)\frac{GM}{c^3}\log\frac{4r_1 r_2}{b^2},
$$

其中 $b$ 为最近逼近距（冲量参数），$r_1,r_2$ 为初/末位置的径向距离，$\gamma$ 为 PPN 参数（广义相对论中 $\gamma=1$）。一般形式为 $(1+\gamma)\frac{GM}{c^3}\ln\frac{r_1+r_2+R}{r_1+r_2-R}$（其中 $R$ 为收—发距离），在近轴极限 $b\ll r_i$ 时化为上式。Cassini 实验通过雷达回波精确测量了日面掠射引力时延，得到 $\gamma=1+(2.1\pm2.3)\times10^{-5}$，验证了广义相对论至 $10^{-5}$ 量级$^{[8]}$；此结果与本文窗化 rDOS 的低频极限相吻合。

---

## 5. 非幺正散射与复时间延迟

> **单位与符号约定**（重要提示）：本节复时间延迟 $\tau_{\mathrm{tot}}(E)$ 与延迟算子 $Q_g(E)$ 的**自然单位为能量$^{-1}$**；对应的**物理时间延迟**为 $\hbar\tau_{\mathrm{tot}}(E)$ 与 $\hbar Q_g(E)$，单位为时间。所有公式中未标注 $\hbar$ 的延迟量均采用能量倒数单位。

在存在吸收/泄露（如黑洞外区、耗散开口系统）时，$S_g(E)$ 非幺正（$S^\dagger S\neq I$），$S^{-1}\neq S^\dagger$。此时 §2.2 的幺正刻度 $\rho_{\mathrm{rel}}=-\xi_g'$ **不再成立**，改用以下定义：

### 定义 5.1（非幺正情形的相位 DOS 与总复延迟）

$$
\boxed{\;\rho_{\mathrm{rel}}[g:g_0]^{(\mathrm{phase})}(E)=\frac{1}{2\pi}\,\partial_E\arg\det S_g(E)=\frac{1}{2\pi}\,\mathrm{Im}\,\partial_E\log\det S_g(E),\;}
$$

$$
\boxed{\;\tau_{\mathrm{tot}}(E)\coloneqq-i\,\partial_E\log\det S_g(E)\;\in\mathbb C.\;}
$$

**若且仅当** $\det S_g(E)\neq 0$，有等价表示
$$
\boxed{\;\tau_{\mathrm{tot}}(E)=-i\,\mathrm{tr}\!\big(S_g^{-1}(E)\,\partial_E S_g(E)\big)\;}
$$

在 $\det S_g(E)=0$ 处（如 CPA 条件），采用 $\partial_E\log\det S_g$ 的分布/极限意义或基于 SVD 伪逆的正则化；吸收强度由 $\mathrm{Im}\,\tau_{\mathrm{tot}}=-\partial_E\log|\det S_g|$ 给出。此处 $\det S_g$ 为 BK 意义下的**扰动行列式**（det$_1$ 或其等价可追化定义，见 §2.1），在复平面上具有良定的解析延拓与分支结构。

**物理意义分解**：总复延迟的**实部** $\mathrm{Re}\,\tau_{\mathrm{tot}}=\partial_E\arg\det S$ 对应相位导数与驻留时间，**虚部** $\mathrm{Im}\,\tau_{\mathrm{tot}}=-\partial_E\log|\det S|$ 刻画吸收强度。$\rho_{\mathrm{rel}}^{(\mathrm{phase})}$ 仅刻画"相位"部分（排除吸收幅度信息）。

**关键差异**：非幺正情形下 $\rho_{\mathrm{rel}}^{(\mathrm{phase})}\neq -\xi_g'(E)$（BK 公式 $\det S=e^{-2\pi i\xi}$ 需幺正性或相应的自伴扩展假设）。在幺正极限 $S^\dagger S=I$ 时，$|\det S|=1$，$\mathrm{Im}\,\tau_{\mathrm{tot}}=0$，且 $\rho_{\mathrm{rel}}^{(\mathrm{phase})}$ 退化为定理 3.1 的 $\rho_{\mathrm{rel}}=-\xi'$。

**通道归一化**：对**有限通道**（多端口）散射系统，可定义**每通道平均延迟** $\tau_{\mathrm{avg}}(E)=\tau_{\mathrm{tot}}(E)/N$（$N$ 为通道数）；在**几何散射**的无限维情形下，应使用总量 $\tau_{\mathrm{tot}}$ 或基于相对迹的"单位立体角延迟"。

**CPA 条件与极点统计**：$\mathrm{Im}\,\tau_{\mathrm{tot}}$ 刻画吸收强度，与 $S$-矩阵极点/共振及**相干完美吸收**（CPA）条件直接相关。**CPA 条件**等价于 $\det S(E_0)=0$（$S$ 不可逆/存在零特征值，零—极互补$^{[9]}$），此时共振能量 $E_0$ 处 $\mathrm{Re}\,\tau_{\mathrm{tot}}$ 与 $\mathrm{Im}\,\tau_{\mathrm{tot}}$ 的峰—峰对齐指示共振吸收最大。rDOS $\rho_{\mathrm{rel}}^{(\mathrm{phase})}$ 与 $S$-矩阵极点/零点的统计分布存在定量联系，在随机矩阵理论与开口腔体系统中已有系统性结果$^{[10,11,12]}$。

---

## 6. 窗化采样与误差的非渐近闭合

### 6.1 采样可实现性：Wexler–Raz 与采样密度

选择 $(\Delta E,\Delta t)$ 与窗对 $(w,\tilde w)$ 使 Gabor 系形成帧/基，并满足 Wexler–Raz 双正交（见 §2.3）。对**能量窗化后的光滑带限近似**，可用 Landau 必要密度（Paley–Wiener 类）估计采样下界；对一般 Gabor 帧，**必要密度条件** $\Delta E\,\Delta t/(2\pi\hbar)\le 1$。**Riesz 基**情形取等号 $\Delta E\,\Delta t/(2\pi\hbar)=1$ 并受 Balian–Low 约束（时—频同时集中不可能）；稠密帧情形 $\Delta E\,\Delta t/(2\pi\hbar)<1$ 较稳健且数值上更实用$^{[13,14]}$。这给出从离散能量网格对 $\rho_{\mathrm{rel}}$ 进行稳定估计的充分—必要准则。

### 6.2 误差三分解：混叠＋伯努利层＋截断

令采样步长为 $\Delta E$，截断到有限窗 $I=[E_{\min},E_{\max}]$。对平滑 $f=\rho_{\mathrm{rel}}\!*w$ 应用 Poisson 求和（在 §2.3 固定的 Fourier 规范下$^{\S}$）：

$$
\sum_{n\in\mathbb Z} f(E_0+n\Delta E)
= \frac{2\pi\hbar}{\Delta E}\sum_{k\in\mathbb Z}
e^{\,i2\pi k E_0/\Delta E}\,
\widehat{f}\!\left(\frac{2\pi\hbar k}{\Delta E}\right)
\quad\text{（Poisson）},
$$

其中 $\widehat{f}(t)=\frac{1}{2\pi\hbar}\int f(E)e^{-iEt/\hbar}\,dE$。非零 $k$ 项即**混叠**；对有限求和/积分差，Euler–Maclaurin（EM）给出**伯努利层**显式余项；截断带来第三类误差。三者相加即总误差的**非渐近闭合**。

**适用条件（有限阶 EM 纪律，与 §12.7 对接）**：
- 窗函数 $w\in\mathcal S(\mathbb R)$（Schwartz 类）保证所需阶可导与快速衰减；
- 对 $2m$ 阶 EM，要求 $f^{(2m)}\in L^\infty$ 且端点可导至 $2m-1$ 阶；
- EM 余项以伯努利数 $B_{2j}$ 与边界高阶导数表出至 $2m$ 阶，详见附录 B；
- EM 仅作**有界扰动**，不引入新奇点；散射极点（共振/束缚态能量）始终为"主尺度"标记。

$^{\S}$ **Fourier 规范与维度检查**：Fourier 对偶为 $\widehat{f}(t)=\frac{1}{2\pi\hbar}\int f(E)e^{-iEt/\hbar}\,dE$；频率栅点间距 $\frac{2\pi\hbar}{\Delta E}$ 具有时间维度，与能量采样步长 $\Delta E$ 互为对偶。前因子 $2\pi\hbar/\Delta E$ 由狄拉克梳 $\sum_n e^{in\Delta E\,t/\hbar}=(2\pi\hbar/\Delta E)\sum_k\delta(t-2\pi\hbar k/\Delta E)$ 导出，确保量纲正确。

---

## 7. 物理后果与可检验预测

1. **相位台阶与束缚态计数（Levinson/Friedel–Kreĭn 型）**：$\arg\det S$ 对 $E$ 的累计跳变与低能相移之和及束缚态数目相关；Friedel–Kreĭn 关系给出 $\Delta_E[\arg\det S/(2\pi)] = n_{\text{bound}} + \text{修正项}$，其中 $n_{\text{bound}}$ 为束缚态数。故 $\int^E \rho_{\mathrm{rel}}\,dE'$ 呈整数级跃迁，与拓扑相位联系紧密$^{[15]}$。关于计数式与谱移函数/相位台阶的联系及常见修正项（半束缚态、简并、多通道情形），见文末参考文献。
2. **共振与延迟峰值**：Breit–Wigner 近似下，$\mathrm{tr}\,Q(E)$ 在 $E_0$ 处出现峰值，半高宽 $\Gamma$ 与寿命由 $\mathrm{Re}\,\tau_{\mathrm{tot}}$ 定量关联；在非幺正系统中，$\mathrm{Im}\,\tau_{\mathrm{tot}}$ 还指示极点分布与 CPA 条件。
3. **引力透镜/脉冲时延**：多路径干涉在 $\mathcal N_w[g:g_0;E]$ 中留下能量依赖的相位—延迟纹理；对 FRB/脉冲星的多频测量可直接估计窗化 rDOS 的纹理。
4. **分支与可加性的防御性注记**：$\arg\det S$ 的分支改变只在离散能量产生 $\pi$ 跳变；对紧支测试函数或窗化读数 $\mathcal N_w$ 的影响为零测（分部积分吸收，见附录 A）。

---

## 8. 数学证明与技术细节

### 8.1 BK 公式与谱移函数

在相对迹类假设下（或适当的相对可追性/光滑假设），谱移函数 $\xi_g$ 由

$$
\mathrm{tr}\big(\varphi(H_g)-\varphi(H_{g_0})\big)=\int_{\mathbb R}\varphi'(E)\,\xi_g(E)\,dE,\qquad \forall \varphi\in C_c^\infty(\mathbb R),
$$

唯一决定。对能量壳散射矩阵 $S_g(E)$ 成立 BK 公式 $\det S_g(E)=e^{-2\pi i\xi_g(E)}$，且 $\xi_g$ 的绝对连续部分满足定理 3.1。

### 8.2 流形散射与能量纤维

渐近平直/长程背景下，散射理论与散射微积分保证 $S_g(E)$ 的良定、幺正性（无吸收时）及其与无穷远测地流的 FIO 关联；这使定理 4.1 的半经典陈述可由波迹–长度谱公式导出。

### 8.3 Wigner–Smith 延迟的算子表达

多通道情形 $Q(E)=-iS^\dagger \partial_E S$ 自然推广；在电磁/声学等波动系统亦成立并可转写为能量密度积分的体/边表示。具体地，**局域 DOS 表示**（Lloyd/Friedel–Kreĭn 关系）给出

$$
\boxed{\;\textbf{（幺正情形）}\quad \mathrm{tr}\,Q_g(E) = 2\pi\,\rho_{\mathrm{rel}}[g:g_0](E),\qquad \rho_{\mathrm{rel}}[g:g_0](E)=\int_{\Omega}\Delta\mathrm{LDOS}(E,\mathbf{r})\,d\mathbf{r},\;}
$$

**非幺正时**：$\mathrm{tr}\,Q_g$ 不再给出 $\rho_{\mathrm{rel}}$；应改用 $\rho_{\mathrm{rel}}^{(\mathrm{phase})}(E)=\tfrac{1}{2\pi}\partial_E\arg\det S_g(E)$，并以 $\mathrm{Im}\,\tau_{\mathrm{tot}}=-\partial_E\log|\det S_g|$ 描述吸收强度（与 §5 保持一致）。

其中 $\Delta\mathrm{LDOS}$ 为**相对**局域态密度（对参考背景 $g_0$ 的差），可由散射格林函数 $G(E,\mathbf{r},\mathbf{r}')$ 虚部给出；这避免绝对 DOS 的发散问题，便于数值实现与材料色散/损耗处理$^{[16]}$。**记号说明**：$\rho_{\mathrm{rel}}[g:g_0](E)$ 为能量处相对态密度（单位：能量$^{-1}$），累计计数记为 $\mathcal N[g:g_0](E)=\int^E\rho_{\mathrm{rel}}[g:g_0](\varepsilon)\,d\varepsilon$（无量纲），避免混淆。

### 8.4 非幺正推广与统计性质

对次幺正 $S$，定义总复延迟 $\tau_{\mathrm{tot}}$ 并建立与 $S$-矩阵极点分布的统计联系；在随机矩阵理论与开口腔体实验中，$\mathrm{Re}\,\tau_{\mathrm{tot}}$ 的分布与零点—极点统计存在定量关系$^{[10,11,12]}$。这些结果可用于从窗化 rDOS 推断共振寿命与吸收通道结构。

### 8.5 窗化采样与误差界

Wexler–Raz 身份刻画对偶窗；Landau 密度给出必要下界。Poisson 求和与 EM 余项一起构成误差的**非渐近闭合**：对 $2m$ 阶光滑窗，EM 余项界与 $|f^{(2m)}|_\infty$ 成正比，混叠项由 $\widehat f$ 在频域栅点的衰减控制。

---

## 9. 最小可复现实验：幺正与非幺正示例

本节给出解析可控的玩具模型，分别展示**幺正散射**（§9.1）与**非幺正散射**（§9.2）的 $\rho_{\mathrm{rel}}$ 计算流程与窗化读数实现。

### 9.1 幺正情形：两通道 Breit–Wigner 共振

**模型设定**：两通道对称系统（秩一耦合，部分宽度 $\Gamma_1=\Gamma_2=\Gamma/2$），散射矩阵为

$$
S(E)=\begin{pmatrix}
S_{11}(E) & S_{12}(E)\\
S_{12}(E) & S_{11}(E)
\end{pmatrix},\qquad z\equiv E-E_0.
$$

取**幺正** Breit–Wigner 形式（单个共振能量 $E_0$，总宽度 $\Gamma$）：

$$
\boxed{\;S_{11}(E)=\frac{z}{z+i\Gamma/2},\qquad
S_{12}(E)=\frac{-i\Gamma/2}{z+i\Gamma/2}\;}.
$$

**解析验证**：
- **幺正性（完整）**：验证 $S^\dagger S=I_2$。
  首先有 $|S_{11}|^2+|S_{12}|^2=\frac{z^2}{|z+i\Gamma/2|^2}+\frac{\Gamma^2/4}{|z+i\Gamma/2|^2}=1$。
  还需验证列间正交：
  $$
  S_{11}\overline{S_{12}}+S_{12}\overline{S_{11}}=2\,\mathrm{Re}\!\big(S_{11}\overline{S_{12}}\big)=0.
  $$
  由模型给定
  $$
  S_{11}=\frac{z}{z+i\Gamma/2},\qquad
  S_{12}=\frac{-i\Gamma/2}{z+i\Gamma/2}
  $$
  可得
  $$
  S_{11}\overline{S_{12}}=\frac{i(\Gamma/2) z}{z^2+(\Gamma/2)^2}\in i\mathbb{R}\quad\Rightarrow\quad\mathrm{Re}\!\big(S_{11}\overline{S_{12}}\big)=0.
  $$
  故 $S^\dagger S=I_2$，幺正成立。
- **行列式**：$\det S(E)=S_{11}^2-S_{12}^2=\frac{z^2-(-i\Gamma/2)^2}{(z+i\Gamma/2)^2}=\frac{z-i\Gamma/2}{z+i\Gamma/2}$；
- **相位（解卷绕与极限）**：令 $\theta(E)=\arg\det S(E)$ 取连续解卷绕分支并固定基线 $\theta(+\infty)=0$，则
$$
\boxed{\;\theta(E)=-2\arctan\frac{\Gamma}{2(E-E_0)}-2\pi\,\mathbf 1_{\{E<E_0\}}\;}
$$
  因而 $\theta(-\infty)=-2\pi$、$\theta(+\infty)=0$，与 $\displaystyle\int_{\mathbb R}\rho_{\mathrm{rel}}(E)\,dE=1$（单共振）一致。
- **rDOS**（Lorentz 峰型）：

$$
\boxed{\;\rho_{\mathrm{rel}}[g:g_0](E)=\frac{1}{2\pi}\,\partial_E\arg\det S_g
=\frac{1}{2\pi}\,\frac{\Gamma}{z^2+(\Gamma/2)^2}\;}.
$$

**数值验证代码**（可直接运行）：
```python
import numpy as np

def unitary_BW_S(E, E0, Gamma):
    """Unitary two-channel Breit-Wigner S-matrix"""
    z = E - E0
    S11 = z / (z + 1j*Gamma/2)
    S12 = -1j*Gamma/2 / (z + 1j*Gamma/2)
    S = np.array([[S11, S12], [S12, S11]], dtype=complex)
    return S

# Energy grid
E0, Gamma = 10.0, 0.5
E_grid = np.linspace(E0 - 2*Gamma, E0 + 2*Gamma, 500)
dE = E_grid[1] - E_grid[0]

# Compute S-matrix at all energies
S_list = [unitary_BW_S(E, E0, Gamma) for E in E_grid]
detS = np.array([np.linalg.det(S) for S in S_list])

# Method 1: log-det path (primary, robust)
theta = np.unwrap(np.angle(detS))
rho_phase = np.gradient(theta, E_grid) / (2*np.pi)

# Method 2: tr(Q) path (unitary-only, cross-check)
# Compute dS/dE via centered finite difference
dS_dE = []
for j in range(len(E_grid)):
    if j == 0:  # Forward difference at left boundary
        dS = (S_list[j+1] - S_list[j]) / dE
    elif j == len(E_grid) - 1:  # Backward difference at right boundary
        dS = (S_list[j] - S_list[j-1]) / dE
    else:  # Centered difference
        dS = (S_list[j+1] - S_list[j-1]) / (2*dE)
    dS_dE.append(dS)

Q_list = [-1j * S.conj().T @ dS for S, dS in zip(S_list, dS_dE)]
rho_trQ = np.array([np.trace(Q).real / (2*np.pi) for Q in Q_list])

# Analytical comparison (Lorentzian)
rho_analytic = (Gamma / (2*np.pi)) / ((E_grid - E0)**2 + (Gamma/2)**2)

# Unitarity check
unitarity_err = np.array([np.linalg.norm(S.conj().T @ S - np.eye(2)) for S in S_list])
print(f"max||S^† S - I|| = {np.max(unitarity_err):.2e}  (should be ~machine eps)")
print(f"max|rho_phase - rho_trQ| = {np.max(np.abs(rho_phase - rho_trQ)):.2e}")
print(f"max|rho_phase - rho_analytic| = {np.max(np.abs(rho_phase - rho_analytic)):.2e}")
```

### 9.2 非幺正情形：含吸收的双端口 CPA 示例（TCMT 秩一耦合）

**模型设定（记号统一）**：令 $\boldsymbol{\Gamma}_{\rm rad}={\rm diag}(\Gamma_1,\ldots,\Gamma_M)$，$\Gamma_{\rm rad}^{\Sigma}=\sum_{i=1}^{M}\Gamma_i$，$\Gamma_{\rm tot}=\Gamma_{\rm rad}^{\Sigma}+\Gamma_{\rm abs}$。单模共振腔与 $M=2$ 个辐射端口耦合，另有非辐射吸收通道（内禀损耗 $\Gamma_{\rm abs}$）。**可观测散射矩阵**仅定义在辐射端口子块上，采用 **Temporal Coupled-Mode Theory（TCMT）** 的秩一更新形式$^{[18]}$：

$$
\boxed{\;S_{\rm rad}(E)=I_M-\frac{i}{z+i\Gamma_{\rm tot}/2}\,\boldsymbol{\Gamma}_{\rm rad}^{1/2}\,\mathbf{1}\,\mathbf{1}^\top\,\boldsymbol{\Gamma}_{\rm rad}^{1/2},\quad z=E-E_\star,\;}
$$

其中 $\boldsymbol{\Gamma}_{\rm rad}={\rm diag}(\Gamma_1,\ldots,\Gamma_M)$ 为辐射耦合宽度矩阵，$\mathbf{1}=(1,\ldots,1)^\top$（$M$ 维全 $1$ 向量），$\Gamma_{\rm rad}^{\Sigma}$ 为总辐射宽度标量。

**CPA 充要条件**：该秩一更新使 $S_{\rm rad}$ 具有 $M-1$ 个特征值 $1$（非共振模）与一个"共振"特征值

$$
\lambda_\star(E)=1-\frac{i\,\Gamma_{\rm rad}^{\Sigma}}{z+i\Gamma_{\rm tot}/2}=\frac{z-\tfrac{i}{2}(\Gamma_{\rm rad}^{\Sigma}-\Gamma_{\rm abs})}{z+i\Gamma_{\rm tot}/2},
$$

故
$$\det S_{\rm rad}(E)=\lambda_\star(E),$$
$$\boxed{\;\det S_{\rm rad}(E_\star)=0\;\Longleftrightarrow\;\Gamma_{\rm abs}=\Gamma_{\rm rad}^{\Sigma}.\;}$$

**参数选择**（$M=2$ 情形）：取 $\Gamma_1=\Gamma_2=0.3$，$\Gamma_{\rm abs}=0.6$，则 $\Gamma_{\rm rad}^{\Sigma}=\Gamma_1+\Gamma_2=0.6=\Gamma_{\rm abs}$，满足 CPA 条件。此时 $E=E_\star$ 处 $\det S_{\rm rad}(E_\star)=0$（**可观测子空间**上共振能量处完美吸收）。

**数值验证代码**（含吸收情形，展示 $\rho_{\mathrm{rel}}^{(\mathrm{phase})}$ 与 $\mathrm{Im}\,\tau_{\mathrm{tot}}$ 峰位对齐）：
```python
import numpy as np

def nonunitary_CPA_S_rad(E, E_star, Gamma_rad_diag, Gamma_abs):
    """Radiative-port-only CPA scattering matrix (TCMT rank-one form)
    
    Args:
        E: Energy (scalar or array)
        E_star: Resonance energy
        Gamma_rad_diag: array of radiative widths [Gamma_1, ..., Gamma_M]
        Gamma_abs: Absorption (intrinsic) width
    Returns:
        S_rad: M×M observable scattering matrix on radiative ports
    """
    z = E - E_star
    M = len(Gamma_rad_diag)
    Gamma_rad_total = np.sum(Gamma_rad_diag)
    Gamma_tot = Gamma_rad_total + Gamma_abs
    
    # Rank-one update: S = I - (i/(z + i*Gamma_tot/2)) * sqrt(Gamma) @ 1 @ 1.T @ sqrt(Gamma)
    v = np.sqrt(Gamma_rad_diag)  # v = Γ_rad^{1/2} · 1
    rank_one = np.outer(v, v)    # v v^T
    S_rad = np.eye(M, dtype=complex) - (1j / (z + 1j*Gamma_tot/2)) * rank_one
    return S_rad

# Parameters satisfying CPA condition: Gamma_abs = Gamma_rad_total
E_star = 10.0
Gamma_rad_diag = np.array([0.3, 0.3])  # Two radiative ports
Gamma_abs = 0.6  # Absorption width = Gamma_1 + Gamma_2 (CPA condition)

E_grid = np.linspace(E_star - 1.5, E_star + 1.5, 500)
S_list = [nonunitary_CPA_S_rad(E, E_star, Gamma_rad_diag, Gamma_abs) for E in E_grid]
detS = np.array([np.linalg.det(S) for S in S_list])

# Phase rDOS (robust log-det path)
theta = np.unwrap(np.angle(detS))
rho_phase = np.gradient(theta, E_grid) / (2*np.pi)

# Absorption indicator (Im tau_tot = -d/dE log|det S|)
log_abs_detS = np.log(np.abs(detS) + 1e-15)  # Avoid log(0) at CPA
Im_tau_tot = -np.gradient(log_abs_detS, E_grid)

# Verify CPA condition
idx_min = np.argmin(np.abs(detS))
print(f"CPA condition check: Gamma_abs = {Gamma_abs:.2f}, Gamma_rad_total = {np.sum(Gamma_rad_diag):.2f}")
print(f"CPA at E = {E_grid[idx_min]:.4f}, |det S_rad| = {np.abs(detS[idx_min]):.2e}")
print(f"Peak alignment: rho_phase peak at E = {E_grid[np.argmax(rho_phase)]:.4f}")
print(f"                Im_tau_tot peak at E = {E_grid[np.argmax(Im_tau_tot)]:.4f}")

# Cross-check eigenvalue structure at E = E_star
S_at_CPA = nonunitary_CPA_S_rad(E_star, E_star, Gamma_rad_diag, Gamma_abs)
eigvals = np.linalg.eigvals(S_at_CPA)
print(f"Eigenvalues at E = E_star: {eigvals}")
print(f"  (expect one zero eigenvalue and M-1 eigenvalues ≈ 1)")

# Unitarity check (should fail for non-unitary)
unitarity_err = np.array([np.linalg.norm(S.conj().T @ S - np.eye(len(Gamma_rad_diag))) 
                          for S in S_list])
print(f"max||S^† S - I|| = {np.max(unitarity_err):.2e}  (non-unitary as expected)")
```

**关键区别**：
- **幺正**（§9.1）：$|\det S|=1$，无 CPA；$\rho_{\mathrm{rel}}=-\xi'=\tfrac{1}{2\pi}\mathrm{tr}\,Q$；
- **非幺正**（§9.2）：$|\det S_{\rm rad}|<1$，CPA 处 $\det S_{\rm rad}=0$（充要条件 $\Gamma_{\rm abs}=\Gamma_{\rm rad}^{\Sigma}$）；$\rho_{\mathrm{rel}}^{(\mathrm{phase})}=\tfrac{1}{2\pi}\partial_E\arg\det S_{\rm rad}$，$\mathrm{Im}\,\tau_{\mathrm{tot}}$ 刻画吸收强度并在 CPA 能量处峰值对齐。

**可观测子块 vs 扩展通道说明**：

> **端口定义区分**（实验/仿真对接）
>
> 散射读数仅定义在**辐射端口**上（本例 $M=2$），吸收通道 $\Gamma_{\rm abs}$ 作为**非端口参数**进入共振极点宽度 $\Gamma_{\rm tot}=\Gamma_{\rm rad}^{\Sigma}+\Gamma_{\rm abs}$。若需从扩展形式（包含吸收通道的 $(M+1)\times(M+1)$ 矩阵 $S_{\rm ext}$）提取可观测子块，可采用 **Schur 补投影**：
>
> $$
> S_{\rm rad}=S_{\rm ext,11}-S_{\rm ext,12}(S_{\rm ext,22})^{-1}S_{\rm ext,21},
> $$
>
> 其中下标 $1$ 对应辐射端口子块，$2$ 对应吸收通道。对本文 TCMT 秩一形式，扩展矩阵可取为
>
> $$
> S_{\rm ext}(E)=I_{M+1}-\frac{i}{z+i\Gamma_{\rm tot}/2}\,\Gamma_{\rm ext}^{1/2}\,\mathbf{1}_{M+1}\,\mathbf{1}_{M+1}^\top\,\Gamma_{\rm ext}^{1/2},
> $$
>
> 其中 $\Gamma_{\rm ext}={\rm diag}(\Gamma_1,\ldots,\Gamma_M,\Gamma_{\rm abs})$。Schur 补投影后回到上述 $S_{\rm rad}$ 的 $M\times M$ 形式，保证 CPA 条件 $\det S_{\rm rad}(E_\star)=0 \Leftrightarrow \Gamma_{\rm abs}=\Gamma_{\rm rad}^{\Sigma}$ 在扩展与子块表述下的等价性。

---

### 9.3 计算路线图（可复现实现清单）

本节给出从散射矩阵 $S_g(E)$ 到窗化读数 $\mathcal N_w[g:g_0;E_0]$ 的完整计算流程与伪代码，确保与 §3–§6 的理论规则一致。

**输入**：几何/折射率模型 $g$ 与参考 $g_0$，窗 $w$ 与对偶 $\tilde w$，采样步长 $\Delta E$。

**打勾清单**：

```
□ 步骤1：计算能量网格 {E_j} 上的散射矩阵 S_g(E_j)
    → PML/辐射边界条件或几何散射坐标
    → 检查数值收敛性（网格/截断/PML厚度）

□ 步骤2：幺正性判定
    → 计算 ||S_g^† S_g - I|| 对所有 E_j
    → 若 max || · || < ε_tol（如 1e-10）：幺正散射，进入步骤3a
    → 若 max || · || ≥ ε_tol：非幺正散射，进入步骤3b

□ 步骤3a：幺正情形 → rDOS 计算（双路径交叉校核）
    ├─ 路径1（log-det，主推）：
    │   ├─ 计算 det S_g(E_j)
    │   ├─ 相位解卷绕：θ_j = unwrap(arg(det S_g))（附录A伪代码）
    │   └─ rho_rel[g:g_0](E_j) = (1/2π) · d/dE θ|_{E_j}（中心差分）
    └─ 路径2（tr Q，幺正专用）：
        ├─ 计算 dS/dE|_{E_j}（复步差分或中心差分）
        ├─ Q_g(E_j) = -i S_g^† dS/dE
        ├─ rho_rel[g:g_0](E_j) = (1/2π) · tr Q_g(E_j)
        └─ 交叉校核：|路径1 - 路径2| < ε_cross（如 1e-6）

□ 步骤3b：非幺正情形 → 相位rDOS与吸收指示符
    ├─ 计算 det S_g(E_j)
    ├─ 相位解卷绕：θ_j = unwrap(arg(det S_g))
    ├─ rho_rel^(phase)[g:g_0](E_j) = (1/2π) · d/dE θ|_{E_j}
    ├─ 吸收强度：Im τ_tot(E_j) = -d/dE log|det S_g(E_j)|
    └─ CPA检测：若 |det S_g(E_k)| < ε_CPA，标记E_k为CPA能量

□ 步骤4：窗化读数
    ├─ 离散卷积：N_w[g:g_0;E_k] = Σ_j w(E_k - E_j) · rho_rel[g:g_0](E_j) · ΔE
    └─ 检查Gabor密度：ΔE·Δt/(2πħ) ≤ 1（必要条件）

□ 步骤5：误差预算（非渐近三分解，§6.2）
    ├─ 混叠项：(2πħ/ΔE) · Σ_{k≠0} |f̂(2πħk/ΔE)|（Poisson）
    ├─ 伯努利层：EM余项至 2m 阶（通常 m=2，见附录B）
    └─ 截断误差：窗衰减指数界 × [E_min, E_max] 外的积分

□ 步骤6：物理一致性检查
    ├─ 束缚态计数：∫ rho_rel dE 的跳变与 Levinson/Friedel-Krein 关系
    ├─ 低频极限：与 Shapiro 延迟公式比较（定常弱场情形）
    └─ 共振峰位：Re τ_tot 峰值与 Im τ_tot 峰值对齐（非幺正CPA）
```

**伪代码（核心循环）**：

```python
# Step 1: Solve S_g(E) on energy grid
E_grid = np.linspace(E_min, E_max, N_E)
S_list = [solve_scattering_matrix(E, geometry_g, ref_g0) for E in E_grid]

# Step 2: Unitarity check
unitarity_err = [np.linalg.norm(S.conj().T @ S - np.eye(M)) for S in S_list]
is_unitary = (max(unitarity_err) < eps_tol)

# Step 3a/b: Compute rDOS
detS = np.array([np.linalg.det(S) for S in S_list])
theta = unwrap_phase(E_grid, detS)  # Appendix A
rho_phase = np.gradient(theta, E_grid) / (2*np.pi)

if is_unitary:
    # Cross-check with tr(Q) path
    dS_dE = compute_derivative(S_list, E_grid)  # Complex-step or centered diff
    Q_list = [-1j * S.conj().T @ dS for S, dS in zip(S_list, dS_dE)]
    rho_trQ = np.array([np.trace(Q).real / (2*np.pi) for Q in Q_list])
    assert np.max(np.abs(rho_phase - rho_trQ)) < eps_cross
    rho_rel = rho_phase  # Use log-det path as primary
else:
    # Non-unitary: compute absorption indicator
    log_abs_detS = np.log(np.abs(detS) + eps_reg)
    Im_tau_tot = -np.gradient(log_abs_detS, E_grid)
    rho_rel = rho_phase  # Phase-only rDOS
    # Detect CPA
    CPA_indices = np.where(np.abs(detS) < eps_CPA)[0]
    if len(CPA_indices) > 0:
        print(f"CPA detected at E = {E_grid[CPA_indices]}")

# Step 4: Windowed readout
def windowed_readout(E_0, w, rho_rel, E_grid):
    dE = E_grid[1] - E_grid[0]
    w_vals = w(E_grid - E_0)
    return np.sum(w_vals * rho_rel) * dE

N_w = [windowed_readout(E_k, window_w, rho_rel, E_grid) for E_k in E_centers]

# Step 5: Error budget (§6.2)
# ... Poisson + EM + truncation (see text)

# Step 6: Consistency checks
# ... Bound-state count, low-freq limit, resonance alignment
```

**关键数值选择**（与理论对接）：

- **能量导数法**（步骤3）：
  - **首选**：复步差分 $\partial_E S(E) \approx \mathrm{Im}[S(E+ih)]/h$（$h\sim 10^{-8}$，零舍入误差，需支持复能量求解器）$^{[17]}$
  - **备选**：中心差分 $\partial_E S(E_j) \approx [S(E_j+\delta)-S(E_j-\delta)]/(2\delta)$（$\delta$ 需平衡截断与舍入，通常 $\delta\sim\sqrt{\epsilon_{\mathrm{mach}}}\,E$）

- **相位解卷绕**（附录A）：累积跟踪 + 边界单侧差分

- **行列式路径选择**（步骤3）：
  - 幺正：$\log|\det S|=0$，直接用 $\arg\det S$
  - 非幺正/近CPA：$\log|\det S|$ 通过 Cholesky/LU 的对数行列式稳定计算，避免直接 $S^{-1}$

- **Gabor密度**（步骤4）：$\Delta E\,\Delta t/(2\pi\hbar)\le 1$（必要条件），临界密度取等号（Riesz基，§2.3）

---

## 10. 数值实现（详细流程）

**输入**：几何/折射率模型 $g$ 与参考 $g_0$，窗 $w$ 与对偶 $\tilde w$，采样步长 $\Delta E$。

1. **定能散射求解**：在能量网格 $\{E_j\}$ 上求 $S_g(E_j)$（几何散射坐标或 PML 处理辐射条件）。**检查幺正性**：计算 $\|S_g^\dagger S_g-I\|$ 判定是否幺正散射；若非幺正，改用定义 5.1 的相位 DOS $\rho_{\mathrm{rel}}^{(\mathrm{phase})}$ 与总复延迟 $\tau_{\mathrm{tot}}$。

2. **能量导数与 rDOS 计算**：
   * **主推方法（复能量求解器）**：**前向虚步差分**（complex-step derivative）$\partial_E S_g(E_j)\approx \mathrm{Im}[S_g(E_j+ih)]/h$，零舍入消去误差，精度达机器精度且数值稳定$^{[17]}$；
   * **备选方法（实能量求解器）**：**实步中心差分** $\partial_E S_g(E_j)\approx [S_g(E_j+\delta)-S_g(E_j-\delta)]/(2\delta)$，需谨慎选择 $\delta$ 平衡截断与舍入误差。
   
   对于 rDOS，优先采用**log-det 路径**避免在 CPA/零点处数值不稳定：
   * **首选**：计算 $\det S_g(E_j)$ 的行列式模与幅角，$\log|\det S|=\tfrac{1}{2}\log\det(S^\dagger S)$ 通过 Cholesky/LU 分解微分获得，$\arg\det S$ 执行相位解卷绕（附录 A）；然后用数值导数得 $\partial_E\arg\det S$ 与 $\partial_E\log|\det S|$；
   * **备选（幺正情形）**：计算 $Q_g(E_j)=-iS_g^\dagger \partial_E S_g$；
   * **非幺正情形的稳健实现**：避免直接计算 $S^{-1}$（易在 $\det S\approx 0$ 处数值爆炸）。改用**SVD 截断伪逆或 Tikhonov 正则**：对 $S_g$ 做 SVD，取阈值 $\epsilon\sim 10^{-10}\sim 10^{-12}$。采用**截断伪逆**
$$
\Sigma^\#_{ii}=
\begin{cases}
1/\sigma_i,& \sigma_i\ge\epsilon,\\
0,& \sigma_i<\epsilon
\end{cases}
\quad\text{或 Tikhonov 正则}\quad
\Sigma^\#_{ii}=\frac{\sigma_i}{\sigma_i^2+\epsilon^2},
$$
   构造 $S^\#=V\Sigma^\#U^\dagger$ 以计算 $\mathrm{tr}(S^\#\partial_E S)$；在 $\det S\approx 0$ 或 CPA 邻域优先采用**log-det 路径**（$\partial_E\arg\det S$、$\partial_E\log|\det S|$）以保持数值稳定。
   
   **交叉校核**：同时计算 $\rho_{\mathrm{rel}}=\tfrac{1}{2\pi}\mathrm{tr}\,Q$（或 $\tfrac{1}{2\pi}\mathrm{Re}\,\tau_{\mathrm{tot}}$）与 $\rho_{\mathrm{rel}}=\tfrac{1}{2\pi}\partial_E\arg\det S$ 并比较差异，以排除数值噪声并检测异常（如 CPA 条件 $\det S\approx 0$）。

3. **rDOS 与窗化**：
   * **幺正**：$\rho_{\mathrm{rel}}(E_j)=\tfrac{1}{2\pi}\mathrm{tr}\,Q_g(E_j)$ 或 $\rho_{\mathrm{rel}}(E_j)=\tfrac{1}{2\pi}\partial_E\arg\det S_g(E_j)$；
   * **非幺正**：$\rho_{\mathrm{rel}}^{(\mathrm{phase})}(E_j)=\tfrac{1}{2\pi}\partial_E\arg\det S_g(E_j)$，并记录 $\mathrm{Im}\,\tau_{\mathrm{tot}}(E_j)=-\partial_E\log|\det S_g(E_j)|$ 刻画吸收。
   
   执行离散卷积 $\mathcal N_w[g:g_0;E_k]=\sum_j w(E_k-E_j)\rho_{\mathrm{rel}}[g:g_0](E_j)\Delta E$（或用 $\rho_{\mathrm{rel}}[g:g_0]^{(\mathrm{phase})}$）。

4. **采样与误差控制**：选 $\Delta E$ 小于窗主瓣带宽的 $1/5\sim 1/10$ 以满足 Nyquist 判据；检查 Gabor 帧密度 $\Delta E\,\Delta t/(2\pi\hbar)\le 1$（见 §2.3 与 §6.1，临界密度取等号）；以 $|\widehat f(2\pi\hbar k/\Delta E)|$ 估计混叠（§6.2 Poisson 公式）；用 $2m$ 阶 EM 余项界（取 $2m=4$ 为保守选择）与边界修正量化截断误差（见附录 B）。

---

## 11. 与现有量子引力/信息框架的接口

* **S-matrix 取向**：本文以 $S(E)$ 为原始对象，强调定能、低能与弯曲背景的一致可观测刻度，兼容 S-matrix 与天球全息的可观测性立场。
* **宏观极限**：$\mathcal N_w$ 的低频极限回到 Shapiro 时延/经典驻留时间；半经典区由测地谱控制。
* **信息论单调性**：窗化/粗粒化视为 CPTP/正保持映射下统计区分度的降低；量子相对熵的**数据处理不等式**保证任何后端读出与通道噪声只会降低可判别度，从而使本刻度**保守**（单调）且具有比较意义。

---

## 12. 与 WSIG-QM / UMS / S-series 的接口

**12.1 与 WSIG-QM 的接口。**
- WSIG-QM 的公理 A5（相位—密度—延迟刻度）与本文定理 3.1 采用完全一致的 BK 号记与 Wigner–Smith 定义：$\rho_{\mathrm{rel}}[g:g_0](E)=\tfrac{1}{2\pi}\mathrm{tr}\mathsf Q_g(E)$，$\varphi'(E)=\pi\rho_{\mathrm{rel}}[g:g_0](E)=\tfrac{1}{2}\mathrm{tr}\mathsf Q_g(E)$。
- WSIG-QM 的公理 A2（有限窗口读数）直接对应本文 2.3 的窗化观测 $\mathcal N_w[g:g_0;E_0]$。
- WSIG-QM 的定理 T1（窗口化读数恒等式与非渐近误差闭合）与本文 6.2 的误差三分解共享 Nyquist–Poisson–EM 框架。
- 本文的量子引力场定义 $\rho_{\mathrm{rel}}[g:g_0]$ 可视为 WSIG-QM 在几何散射语境下的具体实现。

**12.2 与 UMS 的接口。**
- UMS 的核心统一式 $d\mu_\varphi = \tfrac{1}{2\pi}\operatorname{tr}\mathsf Q_g\,dE = \rho_{\mathrm{rel}}[g:g_0]\,dE = \tfrac{\varphi'}{\pi}\,dE$ 与本文定理 3.1 完全一致。
- 本文的窗化 BK 恒等式（定理 3.2）为 UMS 的谱—窗化字典提供几何散射情形的具体表述。
- UMS 的公理 A7（通道—单调—容量）与本文 §11 的信息论单调性（DPI）共享数据处理不等式框架。

**12.3 与窗口化路径积分理论的接口。**
- **窗化—时间域字典（相对/0-trace 版，规范与量纲一致）**：在本文 §2.3 的 Fourier 规范下，

  $$
  \boxed{\;\mathcal N_w[g:g_0;E_0]
  =-\int_{\mathbb R}\widehat w(-t)\,e^{iE_0 t/\hbar}\,
  \operatorname{tr}^{(0)}\!\Big(e^{-iH_g t/\hbar}-e^{-iH_{g_0} t/\hbar}\Big)\,dt;\;}
  $$

  其中 $\widehat{w}(t)=\tfrac{1}{2\pi\hbar}\int w(E)e^{-iEt/\hbar}dE$。**等价写法**（便于使用 $\widehat w(t)$）：
  $$
  \mathcal N_w[g:g_0;E_0]
  =-\int_{\mathbb R}\widehat w(t)\,e^{-iE_0 t/\hbar}\,
  \operatorname{tr}^{(0)}\!\Big(e^{+iH_g t/\hbar}-e^{+iH_{g_0} t/\hbar}\Big)\,dt.
  $$
  两式等价，且对一般（不必偶对称）窗 $w$ 与非紧几何下的 $0$-trace 一致。
- 本文的定理 3.2（窗化 BK 恒等式）为路径积分理论的能量—时间对偶提供几何化表述。
- 两理论共享 Nyquist–Poisson–EM 误差闭合框架。

**12.4 与 S15–S26 的接口。**
- S15–S17 的 Herglotz 表示与规范系统为本文的谱移函数 $\xi_g(E)$ 提供解析结构。
- S24–S26 的 Wexler–Raz 双正交、Landau 必要密度与 Balian–Low 不可能性为本文 2.3 与 6.1 的窗化采样提供具体判据。
- S21–S23 的有限阶 EM 纪律直接支撑本文 6.2 的误差闭合框架。

**12.5 与 CCS（协变多通道）的接口。**
- CCS 的窗化 Birman–Kreĭn 恒等式与本文定理 3.2 在多通道散射情形下完全一致。
- CCS 的 Wigner–Smith 群延迟矩阵定义与本文 2.2 采用相同约定。
- 本文的非幺正推广（§5）可视为 CCS 在含吸收散射情形下的几何化版本。

**12.6 与 EBOC-Graph 的接口。**
- EBOC-Graph 的定理 G4（非渐近误差闭合）与本文 6.2 的三分解在离散谱/图信号情形下共享框架。
- 本文的几何散射可在图/格点系统上离散化，将连续能量谱替换为图拉普拉斯谱，与 EBOC-Graph 的图谱滤波统一。

**12.7 保持"极点 = 主尺度"的有限阶 EM 纪律。**
- 本文在所有离散—连续换序中均采用**有限阶** EM（§6.2），确保散射极点（共振/束缚态能量）始终为"主尺度"标记。
- 与 WSIG-QM、UMS、S15–S26 保持一致：EM 余项仅作有界扰动，不引入新奇点。

---

## 结论

以**窗化相对态密度** $\mathcal N_w[g:g_0;E_0]=\int w(E-E_0)\rho_{\mathrm{rel}}[g:g_0](E)\,dE$ 为核心刻度的量子引力场理论，为基于可观测散射矩阵的几何场提供了**完全操作性、比较性与重正化-无关**的定量框架：

(1) **刻度等价性（幺正情形）**：与 Birman–Kreĭn、Wigner–Smith、Friedel/Smith 的标准散射理论判据严格一致，$\rho_{\mathrm{rel}}[g:g_0](E)=\frac{1}{2\pi}\mathrm{tr}\,Q_g(E)=-\xi_g'(E)=\frac{1}{2\pi}\partial_E\arg\det S_g(E)$；

(2) **几何不变性与存在性**：在渐近平直/凸余紧双曲流形的 FIO 结构下具备微分同胚/幺正等价不变性，并以无穷远测地流对接；允许陷波情形的 $0$-trace 正则化；

(3) **级联散射可加性**：定理 3.3 确保相对 DOS 在级联几何下的可加性，分支处理清晰；

(4) **半经典-宏观对接**：半经典极限与波迹/测地长度谱的 Poisson 公式吻合，低频极限回到 Shapiro 引力时延；

(5) **实验可读出性**：可经满足 Wexler–Raz 双正交的 Gabor 窗化采样在实验上直接读出，并有明确的非渐近误差预算（Poisson 混叠 + EM 伯努利层 + 截断）；

(6) **非幺正推广（含吸收）**：定义相位部分态密度 $\rho_{\mathrm{rel}}^{(\mathrm{phase})}(E)=\frac{1}{2\pi}\partial_E\arg\det S$ 与总复延迟 $\tau_{\mathrm{tot}}=-i\partial_E\log\det S$，实部刻画驻留时间，虚部刻画吸收强度，并与 CPA 条件及共振极点统计对接。

该框架以**相位—延迟—谱移**为唯一主线，将经典-量子与几何-信息的刻度统一到一个可验证、可数值实现且可与天文/实验数据直接对接的体系中。**适用性分层明确**：幺正散射下 BK 公式与 $\xi_g'$ 等价；非幺正散射下改用相位 DOS 与复延迟的实/虚部分解。

---

## 附录 A：窗化 BK 恒等式的细化证明

取 $h\in C_c^\infty$。在幺正情形，由定理 3.1，

$$
\int h\,\rho_{\mathrm{rel}}\,dE
= \frac{1}{2\pi i}\int h\,\partial_E\log\det S\,dE
= -\frac{1}{2\pi i}\int h'\,\log\det S\,dE.
$$

将 $\log\det S$ 分解为实部 $\log|\det S|$ 与虚部 $i\arg\det S$；幺正时 $|\det S|=1$，得到

$$
\int h\,\rho_{\mathrm{rel}}\,dE = -\frac{1}{2\pi}\int h'\,\arg\det S\,dE.
$$

对非幺正情形，定义相位部分态密度为

$$
\rho_{\mathrm{rel}}^{(\mathrm{phase})}(E)=\frac{1}{2\pi}\,\partial_E\arg\det S(E)=\frac{1}{2\pi}\,\mathrm{Im}\,\partial_E\log\det S(E),
$$

并定义总复延迟

$$
\tau_{\mathrm{tot}}(E)=-i\,\partial_E\log\det S(E).
$$

相位部分态密度 $\rho_{\mathrm{rel}}^{(\mathrm{phase})}$ 仅保留相位导数部分，吸收率部分由 $\mathrm{Im}\,\tau_{\mathrm{tot}}=-\partial_E\log|\det S|$ 单独刻画。

**相位解卷绕伪代码**（与定理 3.2 配套）：
```
function unwrap_phase(E[], det_S[])
    Θ[0] = arg(det_S[0])
    for j = 1 to length(E) - 1
        δ = arg(det_S[j]) - arg(det_S[j-1])
        Θ[j] = Θ[j-1] + δ + 2π·round(-δ/(2π))  # wrap to (-π,π]
    return Θ
```
数值导数采用中心差分 $\partial_E\Theta|_{E_j}\approx(\Theta_{j+1}-\Theta_{j-1})/(2\Delta E)$；边界点用单侧差分。阈值处的 $\delta$-跃变由窗化分部积分自动并入。

## 附录 B：误差三分解的显式上界

令 $f=\rho_{\mathrm{rel}}\!*w$ 且 $f^{(2m)}\in L^\infty$、端点可导。对有限求和 $\sum_{n=a}^{b} f(E_0+n\Delta E)$ 与 $\Delta E\int_a^b f(x)\,dx$ 的差，**Euler–Maclaurin 公式**（到 $2m$ 阶）给出

$$
\Delta E\sum_{n=a}^{b} f(E_0+n\Delta E) - \int_{E_0+a\Delta E}^{E_0+b\Delta E} f(x)\,dx
=\sum_{j=1}^{m}\frac{B_{2j}}{(2j)!}(\Delta E)^{2j}\big(f^{(2j-1)}(b)-f^{(2j-1)}(a)\big)
+R_{2m},
$$

其中 $B_{2j}$ 为伯努利数，$|R_{2m}|\le C_m\,|f^{(2m)}|_\infty\,(\Delta E)^{2m}(b-a)$，常数 $C_m$ 可由伯努利周期多项式的 $L^1$ 范数界出。混叠项由 $\frac{1}{\Delta E}\sum_{k\neq0}|\widehat f(2\pi\hbar k/\Delta E)|$ 控制（§6.2 Poisson 公式）；截断项按窗衰减指数界定。

## 附录 C：非幺正情形的 rDOS 与复延迟

定义相位部分 DOS 为 $\rho_{\mathrm{rel}}^{(\mathrm{phase})}=\tfrac{1}{2\pi}\,\partial_E\arg\det S$（见 §5）。对非幺正 $S$，总复时间延迟 $\tau_{\mathrm{tot}}=-i\,\partial_E\log\det S$ 分为实部（相位导数，对应驻留时间）与虚部（吸收率导数）。$\mathrm{Re}\,\tau_{\mathrm{tot}}$ 的分布统计与 $S$-矩阵零点—极点结构存在定量联系，在随机矩阵理论与开口腔体中已有系统性实验验证$^{[10,11,12]}$。

**CPA 条件与双洛伦兹形**：在共振能量 $E_\star$ 附近，当 $\det S_{\rm rad}(E_\star)=0$（相干完美吸收，充要条件 $\boxed{\Gamma_{\rm abs}=\Gamma_{\rm rad}^{\Sigma}}$，零—极互补$^{[9]}$），$\tau_{\mathrm{tot}}(E)$ 展现**双洛伦兹**结构：$\mathrm{Re}\,\tau_{\mathrm{tot}}$ 在 $E_\star$ 处峰值（Breit–Wigner 型），$\mathrm{Im}\,\tau_{\mathrm{tot}}$ 在同一位置呈现吸收极大；此时 $S_{\rm rad}$-矩阵在复平面的零点与极点互补。

**复现实验指引**：对 $\det S_{\rm rad}(E)$ 的幅相同测，$\mathrm{Re}\,\tau_{\mathrm{tot}}$ 与 $\mathrm{Im}\,\tau_{\mathrm{tot}}$ 的峰-峰对齐指示 CPA/共振零极互补。数值上可通过测量 $S_{\rm rad}(E)$ 的幅相并以复步差分求 $\partial_E S_{\rm rad}$ 得到，或直接对 $\arg\det S_{\rm rad}$ 解卷绕后差分；二者可交叉校核稳健性。**完整可运行示例见 §9.2（双端口 TCMT-CPA 模型）**。

---

## 附录 D：符号对照与单位

**核心量定义**：

| 符号 | 定义 | 物理意义 | 单位 |
|------|------|----------|------|
| $S_g(E)$ | 能量壳散射矩阵 | 几何 $g$ 的定能散射算子 | 无量纲 |
| $Q_g(E)$ | $-iS_g^\dagger \partial_E S_g$ | 能量导相延迟算子（物理时间延迟为 $\hbar Q_g$） | 能量$^{-1}$ |
| $\xi_g(E)$ | 谱移函数，$\det S_g=e^{-2\pi i\xi_g}$ | 相对累积态密度（BK） | 无量纲 |
| $\rho_{\mathrm{rel}}[g:g_0](E)$ | $\tfrac{1}{2\pi i}\mathrm{tr}(S^\dagger\partial_E S)=-\xi_g'$ | 相对态密度 | 能量$^{-1}$ |
| $\tau_{\mathrm{tot}}(E)$ | $-i\,\partial_E\log\det S$（$\det S\neq 0$ 时等价于 $-i\,\mathrm{tr}(S^{-1}\partial_E S)$） | 总复延迟（物理时间延迟为 $\hbar\tau_{\mathrm{tot}}$） | 能量$^{-1}$ |
| $\tau_{\mathrm{avg}}(E)$ | $\tau_{\mathrm{tot}}(E)/N$ | 每通道平均延迟（仅有限通道情形） | 能量$^{-1}$ |
| $\mathcal N_w[g:g_0;E_0]$ | $\int w(E-E_0)\rho_{\mathrm{rel}}[g:g_0](E)\,dE$ | 窗化读数 | 无量纲 |
| $(w,\tilde w)$ | 窗-对偶核对 | Wexler–Raz 双正交（规范化内积下） | 无量纲 |
| $\Delta E,\Delta t$ | 采样步长/窗宽 | Gabor 格点尺度 | 能量, 时间 |

**单位与规范注记**：
- 物理时间延迟为 $\hbar Q_g(E)$ 与 $\hbar\tau_{\mathrm{tot}}(E)$，单位为时间；本文 $Q_g$ 与 $\tau_{\mathrm{tot}}$ 的自然单位为能量$^{-1}$。
- 窗-对偶核对 $(w,\tilde w)$ 满足能量—时间版本的 Wexler–Raz 双正交（§2.3 规范化内积 $\langle\cdot,\cdot\rangle_E$ 下，度量因子 $1/(2\pi\hbar)$ 确保归一化常数无量纲）。
- Fourier 规范固定为 $\widehat{f}(t)=\frac{1}{2\pi\hbar}\int f(E)e^{-iEt/\hbar}\,dE$（§2.3），所有相位因子与 Gabor 密度以此计量。

**关键恒等式**（**幺正情形，$S_g^\dagger S_g=I$**）：

$$
\rho_{\mathrm{rel}}[g:g_0](E) = \frac{1}{2\pi i}\mathrm{tr}(S_g^\dagger\partial_E S_g) = \frac{1}{2\pi}\mathrm{tr}\,Q_g = -\xi_g'(E) = \frac{1}{2\pi}\partial_E\arg\det S_g.
$$

上述等价链**仅在幺正散射时成立**。特别地，$-\xi_g'(E)$ 与 $\frac{1}{2\pi}\mathrm{tr}\,Q_g$ 的等价依赖于 BK 公式 $\det S_g=e^{-2\pi i\xi_g}$ 与 $S_g^\dagger=S_g^{-1}$。

**非幺正情形（含吸收，$S_g^\dagger S_g\neq I$）**：

$$
\rho_{\mathrm{rel}}[g:g_0]^{(\mathrm{phase})}(E) = \frac{1}{2\pi}\,\partial_E\arg\det S_g = \frac{1}{2\pi}\,\mathrm{Im}\,\partial_E\log\det S_g,\qquad
\tau_{\mathrm{tot}}(E) \coloneqq -i\,\partial_E\log\det S_g.
$$

**可逆时等价表示**：$\tau_{\mathrm{tot}}(E) = -i\,\mathrm{tr}(S_g^{-1}\partial_E S_g)$（仅在 $\det S_g(E)\neq 0$ 时成立）；

$$
\mathrm{Re}\,\tau_{\mathrm{tot}}=\partial_E\arg\det S_g,\qquad \mathrm{Im}\,\tau_{\mathrm{tot}}=-\partial_E\log|\det S_g|.
$$

**关键区别**：非幺正情形下 $\rho_{\mathrm{rel}}[g:g_0]^{(\mathrm{phase})}\neq -\xi_g'(E)$（BK 公式的 $\xi_g$ 定义需幺正性或相应的自伴扩展假设）；$\mathrm{Re}\,\tau_{\mathrm{tot}}$ 刻画相位/驻留时间，$\mathrm{Im}\,\tau_{\mathrm{tot}}$ 刻画吸收率。在 $\det S_g(E)=0$ 处应使用 log-det 或 SVD 伪逆的正则化（见定义 5.1）。

**Gabor 密度条件**：$\Delta E\,\Delta t/(2\pi\hbar)\le 1$ 为必要密度。

---

## 参考文献

[1] R. B. Melrose and M. Zworski, "Scattering metrics and geodesic flow at infinity," *Inventiones Mathematicae* **124**, 389–436 (1996). doi:10.1007/s002220050055

[2] T. J. Christiansen, "Scattering theory for manifolds with asymptotically cylindrical ends," *Annales de l'Institut Fourier* **50**, 1473–1498 (2000).

[3] J. J. Duistermaat and V. W. Guillemin, "The spectrum of positive elliptic operators and periodic bicharacteristics," *Inventiones Mathematicae* **29**, 39–79 (1975).

[4] Y. Colin de Verdière, "Spectre du laplacien et longueurs des géodésiques périodiques I, II," *Compositio Mathematica* **27**, 83–106, 159–184 (1973).

[5] D. Borthwick, "Spectral Theory of Infinite-Area Hyperbolic Surfaces," 2nd ed., Birkhäuser (2016).

[6] N. Ashby and T. Allison, "Canonical planetary equations for velocity-dependent forces, and the Lense–Thirring precession," *Physical Review D* **92**, 062001 (2015).

[7] N. Ashby, "Relativity in the Global Positioning System," *NIST Special Publication 1198* (2010).

[8] B. Bertotti, L. Iess, and P. Tortora, "A test of general relativity using radio links with the Cassini spacecraft," *Nature* **425**, 374–376 (2003). doi:10.1038/nature01997

[9] Y. D. Chong, L. Ge, H. Cao, and A. D. Stone, "Coherent Perfect Absorbers: Time-Reversed Lasers," *Physical Review Letters* **105**, 053901 (2010). doi:10.1103/PhysRevLett.105.053901

[10] P. W. Brouwer, K. M. Frahm, and C. W. J. Beenakker, "Quantum mechanical time-delay matrix in chaotic scattering," *Physical Review Letters* **78**, 4737–4740 (1997). doi:10.1103/PhysRevLett.78.4737

[11] C. Texier and S. N. Majumdar, "Wigner Time-Delay Distribution in Chaotic Cavities and Freezing Transition," *Physical Review Letters* **110**, 250602 (2013). doi:10.1103/PhysRevLett.110.250602

[12] F. D. Cunden, F. Mezzadri, N. Simm, and P. Vivo, "Correlations between zeros and supersymmetry," *Communications in Mathematical Physics* **341**, 903–932 (2015).

[13] I. Daubechies, "Ten Lectures on Wavelets," SIAM (1992).

[14] K. Gröchenig, "Foundations of Time-Frequency Analysis," Birkhäuser (2001).

[15] A. Martin, "Extension of the axiomatic analyticity domain of scattering amplitudes by unitarity," *Journal of Physics A: Mathematical and General* **39**, R625–R659 (2006). doi:10.1088/0305-4470/39/49/R01

[16] E. Akkermans and G. Montambaux, "Mesoscopic Physics of Electrons and Photons," Cambridge University Press (2007), §5.2.

[17] J. R. R. A. Martins, P. Sturdza, and J. J. Alonso, "The complex-step derivative approximation," *ACM Transactions on Mathematical Software* **29**, 245–262 (2003). doi:10.1145/838250.838251

[18] W. Suh, Z. Wang, and S. Fan, "Temporal coupled-mode theory and the presence of non-orthogonal modes in lossless multimode cavities," *IEEE Journal of Quantum Electronics* **40**, 1511–1518 (2004). doi:10.1109/JQE.2004.834773
— 单模 TCMT 及其在 CPA 条件推导中的应用见 Y. D. Chong et al., PRL **105**, 053901 (2010) [参考文献 9]。

**关于相对迹类与 BK 公式**：F. Gesztesy 讲义及 J. Behrndt, M. Malamud, H. Neidhardt 的综述提供了相对迹类/耗散扩展下的 BK/谱移函数框架。

**关于 Wigner–Smith 延迟与局域 DOS**：V. A. Gasparian, T. Christen, and M. Büttiker, "Partial densities of states, scattering matrices, and Green's functions," *Physical Review A* **54**, 4022–4031 (1996). doi:10.1103/PhysRevA.54.4022

**关于散射矩阵的 FIO 结构**：R. Melrose, *Geometric Scattering Theory*, Cambridge University Press (1995); A. Hassell, "Ergodic billiards that are not quantum unique ergodic," *Journal of Functional Analysis* **210**, 321–348 (2004).

**关于波迹公式与测地流**：S. Zelditch, "Spectral determination of analytic bi-axisymmetric plane domains," *Geometric and Functional Analysis* **10**, 628–677 (2000); L. Guilarmou and F. Naud, "Spectral gap and wave decay on convex co-compact hyperbolic manifolds," *Communications in Mathematical Physics* **347**, 619–673 (2016).

---

**注**：文中所有记号与号记遵循数学物理主流约定（例如 BK 取 $\det S=e^{-2\pi i\xi}$），以避免号差混淆。所有公式均在相应假设的适用条件下成立（见 §2.1 站立假设）。
