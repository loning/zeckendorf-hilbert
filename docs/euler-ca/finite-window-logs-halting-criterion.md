# 有限窗日志的停机判据：NPE 尾项熵通量、三位一体刻度与 WSIG–EBOC–RCA 统一框架

Version: 1.26

## 摘要

建立一套把"观察者是否停机（halting）"刻画为"有限窗重构误差的尾项熵通量可积性"的公理化理论。在 Toeplitz/Berezin 压缩、散射相位与 Wigner–Smith 群延迟的统一能标下，以三位一体刻度同一式 $\boxed{\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)}$ 为母尺，定义窗化读数、信息增量密度与尾项熵通量；以 Nyquist–Poisson–Euler–Maclaurin（NPE）三分解的有限阶误差学为闭合纪律，提出"停机当且仅当尾项熵通量在刻度趋细时可积并趋零"的判据。主要结果：其一，在紧框架窗族与被动通道假设下的停机存在性定理；其二，以远区衰减与奇性不增为枢纽的可积性—非可积性分界；其三，固定资源约束下最小化尾项熵通量的最优窗变分原理与群延迟—带宽乘积上界；其四，在 EBOC 静态块与 RCA 可逆动力之间，给出"停机≡日志完备性边界"的语义同构与可逆计算的刻度化刻画。附录给出有限阶 Euler–Maclaurin 与 Poisson 的具体配方、Carleson—Landau 稳定采样准则的窗化版本，以及 Toeplitz/Berezin 压缩的范数—迹—谱控制不等式。

---

## 0. 记号与公理 / 约定

**母刻度（Trinity）**：在绝对连续谱几乎处处，定义散射相位导数、相对态密度与群延迟迹的同一刻度
$$
\boxed{\ \varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)\ },\quad \mathsf Q(E)=-\,i\,S(E)^\dagger S'(E),\ S(E)\in U(N).
$$
Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\,\xi(E)}$，因此
$$
\xi'(E)=-\frac{1}{2\pi i}\operatorname{tr}\!\big(S^\dagger S'(E)\big)=-(2\pi)^{-1}\operatorname{tr}\mathsf Q(E),
$$
从而 $\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q=\varphi'(E)/\pi=-\xi'(E)$。([arXiv][1])

**WSIG（Wigner–Smith 信息规范）**：以 Wigner–Smith 矩阵 $\mathsf Q(E)=-\,i\,S(E)^\dagger S'(E)$ 的迹密度定义母尺规范，其自然测度为
$$
d\mu_{\rm WSIG}(E):=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)\,dE.
$$
该测度与散射相位导数、相对态密度满足三位一体同一式
$$
\frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E),
$$
因此文中的“WSIG–EBOC–RCA 统一框架”即以此母尺将 §6 的 EBOC 静态本体与 RCA 可逆动力语义对位。

**对象与窗**：Hilbert 空间 $\mathcal H$，观测三元 $(\mathcal H,w,S)$。窗 $w$ 诱导 Toeplitz/Berezin 压缩核 $K_{w,h}$（步长/刻度 $h>0$），并诱导对谱测度的连续线性读数泛函。Toeplitz/Berezin 参考文献见 Engliš 与 Boutet de Monvel–Guillemin。([users.math.cas.cz][2])

**窗剖面、能带与尾域**：设工作带 $\Omega\subset\mathbb R$ 为固定有界能带；记可能的阈值（或其他不可去奇性）集合为 $\{E_{{\rm th},j}\}_j$。定义**窗剖面** $\Psi_w:\mathbb R\to[0,\infty)$ 为由窗 $w$ 诱导的能量轴权函数（例如窗化投影的对角 $\Psi_w(E):=\langle \delta_E,\mathsf P_w\,\delta_E\rangle$ 的归一化版本），仅要求 $\Psi_w$ 可测、非负且在远区具有给定的可积/次可积衰减。给定**远区截断** $E_c:(0,h_\star)\to(0,\infty)$（随刻度单调增，且 $E_c(h)\uparrow\infty$），并为每个阈值点引入**奇性剥离半径** $r_j(h)\downarrow 0$。定义**修正工作域**
$$
\Omega_h^\circ:=\{\,|E|\le E_c(h)\,\}\setminus\bigcup_j \{\,E:\ |E-E_{{\rm th},j}|\le r_j(h)\,\},
$$
以及**尾域**
$$
\mathcal T(h):=\mathbb R\setminus\Omega_h^\circ=\{\,|E|>E_c(h)\,\}\ \cup\ \bigcup_j \{\,E:\ |E-E_{{\rm th},j}|\le r_j(h)\,\}.
$$
尾域 $\mathcal T(h)$ 同时捕捉远区高能贡献与阈值奇性邻域；随 $h\downarrow 0$，远区外推与奇性剥离同步收敛。§5.3 中的带内积分理解为对 $\Omega$ 的积分。

**NPE 三分解（有限阶）**：对任一可重构读数的离散—连续误差，采用
$$
\varepsilon(h)=\varepsilon_{\rm alias}(h)+\varepsilon_{\rm BL}(h)+\varepsilon_{\rm tail}(h),
$$
其中 $\varepsilon_{\rm alias}$ 来自 Poisson 混叠、$\varepsilon_{\rm BL}$ 来自有限阶 Euler–Maclaurin 边界层、$\varepsilon_{\rm tail}$ 为远区尾项。Euler–Maclaurin 与 Poisson 的精确配方取自 DLMF 与近期改进。([dlmf.nist.gov][3])

**窗族与稳定性**：窗族 $\{w_\lambda\}$ 为紧框架，存在 $0<A\le B<\infty$ 使所有工作带上读数稳定；通道被动（无源、幺正），$\mathsf Q(E)$ 为自伴。后文不假设 $(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 非负。框架稳定性与 Wexler–Raz 双正交关系、Landau 密度条件共同确保采样—重构稳定。([sites.math.duke.edu][4])

**有限阶纪律**：只使用有限阶 Euler–Maclaurin；在 Nyquist 条件下以 Poisson 去除带内混叠；"奇性不增/极点=主尺度"。

---

## 1. 窗化读数与熵学对象

### 1.1 窗化能谱读数

给定能量轴上的可测函数型读数 $f$，定义窗化总读数
$$
\mathcal R_{w,h}[f]:=\int_{\mathbb R} f(E)\,\rho_{w,h}(E)\,dE,\quad \rho_{w,h}(E):=\langle \delta_E, K_{w,h}\,\delta_E\rangle.
$$
在母刻度下，$\rho_{w,h}$ 是 $\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$ 的局部化近似。

下文默认读数符号 $f$ 有界：$|f|_{L^\infty(\mathbb R)}<\infty$。

### 1.2 信息增量与尾项熵通量

为避免仅归一化密度的限制，引入 Orlicz 型熵泛函（$L^1\log L$ 结构）：令 $\Upsilon(t):=t\log(1+t)$，对非负可测函数 $g$ 定义
$$
H^\natural[g]:=\int \Upsilon(g(E))\,dE.
$$
定义刻度二分细化 $h\mapsto h/2$ 的边际信息增量
$$
\Delta I(h):=H^\natural[\,|\rho_{w,h}|\,]-H^\natural[\,|\rho_{w,2h}|\,],
$$
与**尾项熵通量**
$$
\Phi_{\rm tail}(h):=H^\natural[g_h],\qquad g_h(E):=|f(E)|\,|\rho_{\rm rel}(E)|\,\Psi_w(E)\,\mathbf{1}_{\mathcal T(h)}(E).
$$
由 de la Vallée Poussin 与 Vitali 判据，若 $|f|_{L^\infty}<\infty$ 且 $\rho_{\rm rel}\Psi_w$ 满足所述局部 $L^{1+\delta}$ 与远区可积，则 **$\Phi_{\rm tail}(h)\xrightarrow[h\downarrow0]{}0$**，且族 $\{g_h\}$ 对 **$E$** 变量一致可积；**关于 $h$ 的 $L^1(0,h_\star)$ 可积性不由此推出**，并在 §3.1 中作为独立假设给出。([arXiv][5])

---

## 2. NPE 三分解的结构与控制

### 2.1 分解

对 $\mathcal R_{w,h}[f]-\mathcal R[f]$（$\mathcal R[f]:=\int f(E)\rho_{\rm rel}(E)\,dE$），写成
$$
\varepsilon_{\rm alias}(h)+\varepsilon_{\rm BL}(h)+\varepsilon_{\rm tail}(h).
$$
在 Nyquist 条件下，$\varepsilon_{\rm alias}$ 由 Poisson 重排抑制；$\varepsilon_{\rm BL}$ 由有限阶 Euler–Maclaurin 给出边界层多项式—余项控制；$\varepsilon_{\rm tail}$ 取决于远区 $\rho_{\rm rel}\Psi_w$ 的衰减与奇性。([dlmf.nist.gov][3])

### 2.2 尾项的 Orlicz 控制

在尾域 $\mathcal T(h)$ 上，有 $\Phi_{\rm tail}(h)=H^\natural[g_h]$。若 $\rho_{\rm rel}\Psi_w\in L^{1+\delta}_{\rm loc}$（奇点集外）且远区满足 $L^{1+\delta}$ 衰减，则 **$\Phi_{\rm tail}(h)\to0$**（DVP–Vitali 给出对 **$E$** 的一致可积与极限交换）。**关于 $h$ 的 $L^1(0,h_\star)$ 可积性需另加 §3.1 的假设**。([arXiv][5])

---

## 3. 停机判据与等价性

### 3.1 定义（Frame Halting）

存在 $h_\star>0$ 使对 $0<h<h_\star$ 成立
$$
\boxed{\ \lim_{h\to0}\Phi_{\rm tail}(h)=0,\quad \Phi_{\rm tail}\in L^1(0,h_\star),\quad \lim_{h\to0}\Delta I(h)=0\ },
$$
且 Nyquist 稳定（框架常数与带宽约束保证 $\varepsilon_{\rm alias}$ 有界）。则称**在 $h_\star$ 前停机**。

### 3.2 等价定理

**定理 3.1（停机—可积性等价）** 在 0 节公理及 2 节结构下，
$$
\text{停机}\iff \Phi_{\rm tail}\in L^1(0,h_\star)\ \text{且}\ \lim_{h\to 0}\Phi_{\rm tail}(h)=0.
$$

*证明梗概*：利用 Orlicz 函数 $\Upsilon(t)=t\log(1+t)$ 的超线性增长，$\Delta I(h)$ 的极限由均匀可积控制而与尾项等价；Poisson 与有限阶 EM 使非尾项贡献在 $h\downarrow 0$ 时可统一上界；反向方向改用 Orlicz–Bregman 发散 $D_{\Upsilon}(u\Vert v)=\Upsilon(u)-\Upsilon(v)-\Upsilon'(v)(u-v)$ 的**模凸性（半径依赖的强凸）**。为与 $\Delta I(h)$ 对应，令
$$
u(E):=|\rho_{w,h}(E)|,\qquad v(E):=|\rho_{w,2h}(E)|,
$$
并约定下述 $D_{\Upsilon}(u\Vert v)$ 与集合分解均在尾域 $\mathcal T(h)$ 上评估。由 $\Upsilon(t)=t\log(1+t)$ 得
$$
\Upsilon''(t)=\frac{d^2}{dt^2}\big(t\log(1+t)\big)=\frac{1}{1+t}+\frac{1}{(1+t)^2}\ge\frac{1}{1+t},
$$
故
$$
\begin{aligned}
D_{\Upsilon}(u\Vert v)
&=\int_{\mathcal T(h)}\!\left[\int_{0}^{1}(1-\theta)\,\Upsilon''\!\big(v+\theta(u-v)\big)\,(u-v)^2\,d\theta\right]dE\\
&\ge \frac{1}{2}\int_{\mathcal T(h)}\frac{(u-v)^2}{1+u+v}\,dE.
\end{aligned}
$$
该式给出 Orlicz–Bregman 发散的全程模凸性下界（半径依赖）。再把 $\mathcal T(h)$ 分解为 $\{u+v\le R\}\cup\{u+v>R\}$：
$$
D_{\Upsilon}\ \ge\ \tfrac{1}{2(1+R)}|u-v|_{L^2(\{u+v\le R\})}^2\ +\ \tfrac{1}{2}\int_{\{u+v>R\}}\frac{(u-v)^2}{1+u+v}\,dE.
$$
随 $h\downarrow0$，尾域收缩与 $\Phi_{\rm tail}\in L^1(0,h_\star)$ 带来的 Orlicz 一致可积共同推出 $\Delta I(h)\to0$。([people.lids.mit.edu][6])

### 3.3 完备追求与不停机

**推论 3.2** 若对任意小 $h$ 有 $\Delta I(h)\not\to 0$，则 $\Phi_{\rm tail}$ 不可积或不趋零，称**不停机**。于是"追求完备 $\Leftrightarrow$ 尾项熵通量持续外渗 $\Leftrightarrow$ 不停机"。

---

## 4. 存在性与非存在性：远区衰减的分界

### 4.1 停机存在性

**定理 4.1（存在性）** 设窗族为紧框架、通道被动，且存在 $\delta>0,E_0>0$ 使
$$
\rho_{\rm rel}\in L^{1+\delta}(|E|>E_0),\qquad \Psi_w\in L^{1+\delta}(\mathbb R),\qquad |\rho_{\rm rel}(E)|\,\Psi_w(E)\in L^{1}(|E|>E_0),
$$
并且读数符号 $f\in L^\infty(\mathbb R)$。则存在 $h_\star$ 使得停机成立。

*证明要点*：由 $|f|_\infty$ 与 $|\rho_{\rm rel}(E)|\,\Psi_w(E)\in L^1$ 得尾积分有界；再用 $L^{1+\delta}$ 与 de la Vallée Poussin–Vitali 给出均匀可积与趋零；有限阶 EM 与 Nyquist（见 7 节之 Landau 下界）消除别项。([archive.ymsc.tsinghua.edu.cn][7])

### 4.2 非停机的充分条件

**定理 4.2（非存在性）** 在 §0–§2 的公理与结构下，若存在常数 $c_0>0$ 与 $h_1\in(0,h_\star)$ 使得对所有 $0<h<h_1$，尾域 $\mathcal T(h)$ 中存在正测度子集且 $|f(E)|\ge c_0$，则下述任一条件成立时有 $\Phi_{\rm tail}\notin L^1(0,h_\star)$，因而**不停机**：

(a) **远区幂律**：$\big|\rho_{\rm rel}(E)\big|\,\Psi_w(E)\sim C\,|E|^{-\beta}$（$|E|\to\infty$），且 $\beta\le\tfrac{1}{2}$。

(b) **阈值奇性**：存在阈值点 $E_{\rm th}$，$\big|\rho_{\rm rel}(E)\big|\,\Psi_w(E)\sim C\,|E-E_{\rm th}|^{-\gamma}$（$E\to E_{\rm th}$），且 $\gamma\ge 1$。

*说明*：远区属小 $t$ 区域，$\Upsilon(t)\sim t^2$ 给出 $\int_{|E|>E_c}|E|^{-2\beta}$ 的临界 $\beta=\tfrac{1}{2}$；阈值属大 $t$ 区域，$\Upsilon(t)\sim t\log t$ 给出 $\int_{|x|\le r}x^{-\gamma}\log\!\tfrac{1}{x}$ 的临界 $\gamma=1$。

---

## 5. 变分原理与最优窗

### 5.1 资源约束与时频条件数

设带宽 $\mathsf{BW}$、窗长 $T$、步长 $h$ 给定，窗族框架常数为 $A,B_{\rm fr}$（与带宽符号区分），定义**有效时频条件数**
$$
\kappa_{\rm tf}:=\frac{B_{\rm fr}}{A}.
$$

### 5.2 目标泛函与欧拉方程

在可行集（框架与能量预算约束）上最小化
$$
\mathcal J[w]:=\int_0^{h_\star}\Phi_{\rm tail}(h;w)\,d\mu(h),
$$
$\mu$ 为刻度权。变分所得欧拉—拉格朗日方程表明最优对偶窗 $w^\ast$ 逼近最小不确定性形状并趋向紧框架极限（Gabor/Wexler–Raz 同步化）。([sites.math.duke.edu][4])

### 5.3 群延迟—带宽乘积上界

**定理 5.1** 在带限或弱色散区，存在常数 $C_{\rm uni}$（仅依赖窗族正则性与被动性）使
$$
\big|\mathcal R_{w,h}[1]\big|=\big|\operatorname{tr}K_{w,h}\big|\le C_{\rm uni}\,\kappa_{\rm tf}\,\int_{\Omega}\Psi_w(E)\,\Big|\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\Big|\,dE.
$$

*证明要点*：令 $d\mu_{\mathsf A}=(2\pi)^{-1}\operatorname{tr}\mathsf Q\,dE$。由 Toeplitz/Berezin 符号—算子比较与迹理想估计得
$$
|\operatorname{tr}K_{w,h}|\lesssim \int_{\Omega}\Psi_w(E)\,d|\mu_{\mathsf A}|(E),
$$
再以框架上下界折算为 $\kappa_{\rm tf}$ 因子，得所示不等式。([美国数学会][8])

---

## 6. EBOC 本体与 RCA 语义对位

### 6.1 静态块视角

EBOC 把宇宙视为静态块；窗口 $w$ 把"观测—计算"统一为算子—测度—函数三元。停机意指在母刻度上**边际信息密度**消失，尾项熵通量可积并趋零。

### 6.2 可逆元胞自动机（RCA）日志

在一维 RCA 的空间—时间图中，以群延迟诱导前沿速度刻度；经编码映射得到离散相对态密度 $\rho_{\rm rel}^{\rm RCA}$。窗化日志的 NPE 同构成立：若语言远区呈非可积尾（$\rho_{\rm rel}^{\rm RCA}\Psi_w\notin L^1$），则**不停机**；若满足 4.1 的可积衰减，则存在停机刻度 $h_\star$。

---

## 7. 稳定采样与可重构性

### 7.1 Landau 密度与 Nyquist 条件

在 Paley–Wiener 与其窗化变体上，Landau 给出采样—插值的必要密度下界；近年的推广适用于更广泛的谱子空间与椭圆算子谱子空间。窗化场景中，密度下界与框架常数共同给出 Nyquist 可达条件，使 $\varepsilon_{\rm alias}$ 在 NPE 中可控，尾项成为停机的主判别因子。([archive.ymsc.tsinghua.edu.cn][7])

### 7.2 Carleson—de Branges 视角

在 de Branges 空间与相关权下，采样—插值的 Carleson 类型准则在"相位导数可控/加倍"的假设下成立，从而为窗化稳定性提供泛函解析支架。([SpringerLink][9])

---

## 8. 操作化分界与例示

### 8.1 远区幂律

**远区幂律（在规范读数 $f\equiv1$，或更一般地 $f$ 在远区不消失的情形）**。若 $\big|\rho_{\rm rel}(E)\big|\,\Psi_w(E)\sim C|E|^{-\beta}$（$|E|\to\infty$），则：

* $\beta>\tfrac{1}{2}$：$\Phi_{\rm tail}$ 可积，存在 $h_\star$ 停机；
* $\beta=\tfrac{1}{2}$：临界慢衰减，**不停机**（在上述前提下，$\int_{|E|>E_c}|E|^{-1}dE$ 对任意 $E_c$ 发散，$\Phi_{\rm tail}\notin L^1$）；
* $\beta<\tfrac{1}{2}$：**不停机**。

### 8.2 阈值奇性

**阈值奇性** 设某阈值 $E_{\rm th}$ 处 $\big|\rho_{\rm rel}(E)\big|\,\Psi_w(E)\sim C\,|E-E_{\rm th}|^{-\gamma}$，**且存在 $c_0,\delta>0$ 使 $|f(E)|\ge c_0$ 于 $|E-E_{\rm th}|\le\delta$**。则：

* **$\gamma<1$**：$\Phi_{\rm tail}$ 在阈值剥离 $r(h)\downarrow0$ 下有限且趋零，存在 $h_\star$ 使**停机**；
* **$\gamma=1$**：临界慢奇性，$\Phi_{\rm tail}(h)=\infty$（任意 $h$），**不停机**；
* **$\gamma>1$**：$\Phi_{\rm tail}(h)=\infty$，**不停机**。

*说明*：若 $f$ 在阈值邻域消失，则上述"发散/不停机"结论不必成立，需改用 §4.2 的条件判断。与 §8.1 的远区分界 $\beta=\tfrac{1}{2}$ 互为"小 $t$/大 $t$"两种不同渐近。

---

## 9. 主定理与证明要点

* **定理 3.1**：停机 $\Leftrightarrow$ 尾项熵通量可积且趋零（de la Vallée Poussin 均匀可积判据 + Orlicz–Bregman 发散的模凸性（半径依赖的强凸））。([arXiv][5])
* **定理 4.1**：$L^{1+\delta}$ 衰减与紧框架—被动性给出停机存在性（Hölder—Young + NPE 有限阶闭合 + Nyquist）。([archive.ymsc.tsinghua.edu.cn][7])
* **定理 4.2**：远区幂律 $\beta\le \tfrac{1}{2}$ 或阈值奇性 $\gamma\ge 1$，且读数在尾域不消失 $\Rightarrow$ **不停机**（$\Phi_{\rm tail}$ 不可积/发散）。
* **定理 5.1**：群延迟—带宽乘积上界（Toeplitz/Berezin 迹—范数控制 + 迹理想 + 母刻度）。([美国数学会][8])
* **RCA 命题**：离散刻度下语言远区不可积 $\Rightarrow$ 不停机；可积 $\Rightarrow$ 存在停机刻度。

---

## 10. 讨论：规范不变的时间尺与资源密度

三位一体刻度把"时间—能量—信息"同一为 $\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$。时间尺由群延迟迹的积分给出，具有规范不变性；停机对应该母尺上边际信息密度的消失，而不停机对应对非可积尾的持续"开采"。由此，"追求完备 = 追求不停机"获得可检验的数理化定义。

---

## 附录 A：有限阶 Euler–Maclaurin 与 Poisson 配方

对充分光滑 $g$，有限阶 EM（至 $2m$ 阶）给出
$$
\sum_{n=a}^b g(n)=\int_a^b g(x)\,dx+\tfrac{g(a)+g(b)}{2}+\sum_{k=1}^m \tfrac{B_{2k}}{(2k)!}\big(g^{(2k-1)}(b)-g^{(2k-1)}(a)\big)+R_{2m},
$$
余项 $R_{2m}$ 由 $g^{(2m)}$ 的有界变差控制；Poisson 重排在 Nyquist 条件下消除带内混叠，二者合用形成有限阶闭合与奇性不增纪律。([dlmf.nist.gov][3])

---

## 附录 B：Landau 密度与窗化版本

Paley–Wiener 场景的采样/插值必要密度由 Landau 给出；Gröchenig 等对椭圆谱子空间给出近期推广。窗化情形下，下界常数与框架常数耦合，统一控制 $\varepsilon_{\rm alias}$ 并突显 $\Phi_{\rm tail}$ 的主导地位。([archive.ymsc.tsinghua.edu.cn][7])

---

## 附录 C：Toeplitz/Berezin 压缩与迹—范数—谱控制

令 $\mu_{\mathsf A}$ 为有符号测度：$d\mu_{\mathsf A}=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)\,dE$，其总变差为 $|\mu_{\mathsf A}|$。若 $K_{w,h}=\mathsf P_w\,\mathsf A\,\mathsf P_w$（$\mathsf P_w$ 为窗化投影，$\mathsf A$ 为观测算子），则
$$
|\operatorname{tr}K_{w,h}|\lesssim \int \Psi_w(E)\,d|\mu_{\mathsf A}|(E),\qquad |K_{w,h}|_{\mathfrak S_p}\lesssim |\Psi_w|_{L^p(d|\mu_{\mathsf A}|)},
$$
可由迹理想与 Berezin–Toeplitz 符号—算子比较给出。([美国数学会][8])

---

## 附录 D：Trinity 与相对态密度、群延迟、相位

Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 与 Wigner–Smith 矩阵 $\mathsf Q=-iS^\dagger S'$ 蕴含
$$
\xi'(E)=-\frac{1}{2\pi i}\operatorname{tr}(S^\dagger S'(E))=-(2\pi)^{-1}\operatorname{tr}\mathsf Q(E),
$$
因而
$$
\rho_{\rm rel}(E)=(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)=\frac{\varphi'(E)}{\pi}=-\xi'(E).
$$
由此确立本文母刻度的三位一体同一式。([arXiv][1])

---

## 参考文献（选）

[1] E. P. Wigner, "Lower Limit for the Energy Derivative of the Scattering Phase Shift," *Phys. Rev.* **98** (1955). ([物理评论链接管理器][10])
[2] F. T. Smith, "Lifetime Matrix in Collision Theory," *Phys. Rev.* **118** (1960). ([chaosbook.org][11])
[3] M. G. Kreĭn; M. Sh. Birman, Birman–Kreĭn 公式与谱移函数，综述见 A. Pushnitski, *arXiv:1006.0639* (2010). ([arXiv][1])
[4] D. Borthwick & Y. Wang, "Birman–Kreĭn formula and scattering phase," *arXiv:2110.06370* (2022). ([arXiv][12])
[5] H. J. Landau, "Necessary density conditions for sampling and interpolation…," *Acta Math.* **117** (1967)；及 K. Gröchenig 等近年推广，*APDE* **17** (2024). ([archive.ymsc.tsinghua.edu.cn][7])
[6] O. Christensen, *An Introduction to Frames and Riesz Bases*, 2nd ed.（框架理论与 Wexler–Raz）。([dlib.scu.ac.ir][13])
[7] I. Daubechies et al., "Gabor Time–Frequency Lattices and the Wexler–Raz Identity," *JFAA* (1995). ([sites.math.duke.edu][4])
[8] M. Engliš, "An excursion into Berezin–Toeplitz quantization…," 2011；L. Boutet de Monvel & V. Guillemin, *The Spectral Theory of Toeplitz Operators*, 1981。([users.math.cas.cz][2])
[9] NIST DLMF, §2.10 Euler–Maclaurin 及相关条目；并见 Trefethen 等关于梯形规则与 EM 统一误差。([dlmf.nist.gov][3])
[10] B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS (2005). ([美国数学会][8])
[11] de la Vallée Poussin 均匀可积判据及其现代表述（Vitali/Orlicz–$L^1\log L$ 观点）。([arXiv][5])
[12] Pinsker/Csizsár–Kullback 不等式及其推广，用以把熵差联结到总变差控制。([people.lids.mit.edu][6])

（文内未尽之标准事实均可由上述文献与相应教材处查证。）

[1]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "[PDF] arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[2]: https://users.math.cas.cz/~englis/81.pdf?utm_source=chatgpt.com "An excursion into Berezin-Toeplitz quantization and related ..."
[3]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[4]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[5]: https://arxiv.org/pdf/2004.12578?utm_source=chatgpt.com "arXiv:2004.12578v5 [math.OA] 27 Feb 2024"
[6]: https://people.lids.mit.edu/yp/homepage/data/LN_fdiv.pdf?utm_source=chatgpt.com "7.1 Definition and basic properties of f-divergences - People"
[7]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6020-11511_2006_Article_BF02395039.pdf?utm_source=chatgpt.com "Necessary density conditions for sampling and ..."
[8]: https://www.ams.org/books/surv/120/surv120-endmatter.pdf?utm_source=chatgpt.com "Trace Ideals and Their Applications, Second Edition"
[9]: https://link.springer.com/content/pdf/10.1007/s11854-012-0026-2.pdf?pdf=button&utm_source=chatgpt.com "sampling and interpolation in de branges spaces with doubling ..."
[10]: https://link.aps.org/doi/10.1103/PhysRev.98.145?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering Phase ..."
[11]: https://chaosbook.org/library/SmithDelay60.pdf?utm_source=chatgpt.com "[PDF] Lifetime Matrix in Collision Theory - ChaosBook.org"
[12]: https://arxiv.org/pdf/2110.06370?utm_source=chatgpt.com "[PDF] arXiv:2110.06370v3 [math.SP] 15 Aug 2022"
[13]: https://dlib.scu.ac.ir/bitstream/Hannan/310023/2/9783319256139.pdf?utm_source=chatgpt.com "An Introduction to Frames and Riesz Bases"
