# EBOC–WSIG 统一公理化：光速常数的窗口化群延迟定义与"时空/时间/空间"公理的融合

**Version: 3.17**

---

## 摘要

在仅假设因果前沿（光速常数 $c$）与时空几何 $(M,g)$ 的前提下，建立从几何—因果到可测—定标的无环体系：以散射相位导数 $\varphi'(E)$、相对态密度 $\rho_{\mathrm{rel}}(E)$、Wigner–Smith 群延迟迹 $\tfrac12\operatorname{tr}\mathsf Q(E)$ 的三位一体刻度作为能量轴的唯一母尺；以窗化读数实现非渐近测量并给出 Nyquist–Poisson–Euler–Maclaurin（NPE）三分误差闭合；在体系内部定义 $\hbar,e,k_{\mathrm B},G$ 四个桥接常数；据此封装导出量并给出力的三重等价（世界线非测地性 $=$ 动量通量散度 $=$ 对曲率/联络的最小耦合）。光速常数**不作重新定义**；以下给出**窗口化群延迟读数**作为与公理 A1 常数 $c$ 的**计量等值**，并与三位一体刻度、因果前沿与信息光锥、计量实现构成四重**对齐**。该体系保证存在、唯一与窗/核无关性，并以单位—定标的有向无环图（DAG）消除循环。

---

## 0. 记号与实现纪律

**术语与缩略语**：**WSIG**：指"基于窗口化相位/群延迟读数并配合 NPE 误差账本的操作性规约与计量对表"。**EBOC**：指"静态块 + 叶分解 + 悬挂流"的几何—动力框架（文中以二维子移位 $X\subset\mathcal A^{\mathbb Z^2}$ 的叶分解与诱导度规 $h$ 为其实现）。**RCA**：可逆元胞自动机，指 $Y\subset\mathcal B^{\mathbb Z}$ 与双射滑动块码 $F:Y\to Y$ 的离散可逆演化体系。记号区分：**$\mathsf Q$** 始终表示 Wigner–Smith 矩阵 $-iS^\dagger \partial_E S$（量纲 $E^{-1}$）；**$\mathcal Q$** 表示最小耦合中的"荷"，二者含义与量纲不同，严禁混用。（下文沿用上述定义与区分。）

**相位与群延迟**：设 $S(E)\in U(N)$，$\Phi(E):=\operatorname{Arg}\det S(E)$，$\varphi(E):=\tfrac12\,\Phi(E)$。定义 $\mathsf Q(E):=-\,i\,S(E)^\dagger\dfrac{dS}{dE}$，$\Phi'(E)=\operatorname{tr}\mathsf Q(E)$，$\varphi'(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E)$。

**相位支与导数约定**：$\Phi(E)=\operatorname{Arg}\det S(E)$ 取连续相位支；$\Phi'(E)$ 作为分布导数理解，与 $\operatorname{tr}\mathsf Q(E)$ 在绝对连续谱上几乎处处相等。

**三位一体母式**（绝对连续谱上几乎处处）：
$$
\varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E).
$$

**群延迟量纲（通道平均/单通道）**：通道平均群延迟 $\displaystyle \bar\tau_{\mathrm{WS}}(E):=\hbar\,\frac{1}{N}\operatorname{tr}\mathsf Q(E)$（时间）；单通道（特征相位 $\theta_\alpha$）$\displaystyle \tau_{g,\alpha}(E):=\hbar\,\partial_E\theta_\alpha(E)$。与半行列式相位 $\varphi(E):=\tfrac12\,\operatorname{Arg}\det S(E)$ 的关系：$\displaystyle \bar\tau_{\mathrm{WS}}(E)=\frac{2\hbar}{N}\,\varphi'(E)$。

**频率—能量映射与群折射率**：设 $E=\hbar\omega$，在各向同性、静态、局域线性介质中取色散关系 $k(\omega)=n(\omega)\,\omega/c$。定义群速度与群折射率
$$
v_g(\omega):=\Big(\partial_\omega k(\omega)\Big)^{-1}=\frac{d\omega}{dk},\qquad
n_g(\omega):=\frac{c}{v_g(\omega)}=n(\omega)+\omega\,\partial_\omega n(\omega).
$$
一般情形下 $n_g(\ell,E)$ 指能量 $E$ 下沿路径 $\gamma$ 在弧长坐标 $\ell$ 的局域群折射率，按 $\omega=E/\hbar$ 代入；若介质各向异性或非各向同性，应将 $n_g$ 理解为沿射线方向的投影群折射率（等效慢度）。本文 §4.4 的窗—核加权式即据此定义成立。

**傅里叶约定**：$\displaystyle \widehat f(\tau):=\int_{\mathbb R} f(E)\,e^{-i\tau E}\,dE,\quad f(E)=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\tau)\,e^{i\tau E}\,d\tau$。

**窗与核的规范化（含量纲）**：取无量纲原型 $W,K\in L^1(\mathbb R)$ 满足 $\int W=\int K=1$，定义
$$
w_R(E):=\frac{2\pi}{\Delta_w}\,W\!\Big(\frac{E}{\Delta_w}\Big),\qquad
\kappa(E):=\frac{1}{\Delta_\kappa}\,K\!\Big(\frac{E}{\Delta_\kappa}\Big),
$$
则 $\frac{1}{2\pi}\int w_R(E)\,dE=1$、$\int \kappa(E)\,dE=1$，且 $w_R,\kappa$ 量纲均为 $E^{-1}$。由归一性可得对常数 $c$ 有 $[\kappa\star c]\equiv c$、$\langle c\rangle_{w,\kappa;E_0}=c$。

**正则性假设与近似单位**：$w_R\in W^{1,1}(\mathbb R)$（**或紧支撑，或带限；两者不可兼得**），且 $w_R,w_R'\in L^1$、$w_R(\pm\infty)=0$；$\kappa\in L^1$、$\int\kappa=1$，并在分布意义下有 $[\kappa\star\partial_E\Phi]=\partial_E[\kappa\star\Phi]$。**近似单位条件**：$(w_R)_R$ 满足 $\sup_R\|w_R\|_{L^1}<\infty$、$\|w_R\|_{L^\infty}\to0$ 且 $\widehat w_R\xrightarrow{\ \mathcal S'\ }2\pi\delta_0$（$R\to\infty$）。

**注意**：严格带限与紧支撑不可同时成立（Paley–Wiener），本文仅以**频域有效支集**给出"别名为零"的**可检充分判据**，其余泄漏统一计入 $\mathcal E_{\mathrm{tail}}$。

**卷积定义**：$[\kappa\star f](E):=\int_{\mathbb R}\kappa(E-E')\,f(E')\,dE'$。

**加权平均记号（统一）**：对任意可积函数 $f$ 与中心能量 $E_0$，定义
$$
\boxed{\ \langle f\rangle_{w,\kappa;E_0}:=\frac{1}{2\pi}\int_{\mathbb R} w_R(E-E_0)\,[\kappa\star f](E)\,dE\ }.
$$
**若未指明，默认 $E_0=0$**。对常数 $c$ 且 $\int\kappa=1$，有 $\langle c\rangle_{w,\kappa;E_0}\equiv c$。（与 §4 统一。）

**记号**：$w_{R,E_0}(E):=w_R(E-E_0)$。**目标谱密度**：$\rho_\star\in\{\rho,\rho_{\mathrm{rel}}\}$（分别为绝对谱密度与相对态密度）。

**采样与 Nyquist 条件**：令 $f:=w_{R,E_0}\cdot(\kappa\star\rho_\star)$、$E_n:=E_0+n\Delta_E$、$\widehat f(\tau):=\int f(E)e^{-i\tau E}dE$。**Poisson 求和（含偏移，标准式）**：
$$
\boxed{\ \sum_{n\in\mathbb Z} f(E_0+n\Delta_E)=\frac{1}{\Delta_E}\sum_{m\in\mathbb Z}e^{i\frac{2\pi m}{\Delta_E}E_0}\,\widehat f\!\Big(\frac{2\pi m}{\Delta_E}\Big)\ }.
$$
无别名充要条件保持：$\operatorname{supp}\widehat f\subset(-\pi/\Delta_E,\pi/\Delta_E)$。（若需对照"未含偏移"形式，请在该处标注"此处取 $E_0=0$"。）
**有效支集宽度（修订）**：令 $\widehat f(\tau)=\widehat w_R(\tau)\,\ast\,\big(\widehat\kappa(\tau)\cdot\widehat\rho_\star(\tau)\big)$，定义
$$
\Omega_{\mathrm{eff}}\ :=\ \inf\Big\{\Omega>0:\ \operatorname{supp}\widehat f\subset[-\Omega,\Omega]\Big\}\ \le\ \Omega_w\ +\ \min\big(\Omega_\kappa,\Omega_\rho\big).
$$
其中 $\Omega_w,\Omega_\kappa,\Omega_\rho$ 分别界定 $\widehat w_R,\widehat\kappa,\widehat\rho_\star$ 的有效支集上界；**当三者支集对称且边界饱和时**取等号（此时同宽特例 $\Omega_{\mathrm{eff}}=2\Omega$ 亦随之成立）。据此，"别名为零"的**可检充分条件**统一为
$$
\Delta_E\ <\ \frac{\pi}{\Omega_{\mathrm{eff}}},\qquad\text{常用上界替代：}\ \Delta_E\ <\ \frac{\pi}{\Omega_w+\min(\Omega_\kappa,\Omega_\rho)}.
$$

**NPE 误差账本**：任何窗化读数分解为 $\mathcal E_{\mathrm{alias}}+\mathcal E_{\mathrm{EM}}+\mathcal E_{\mathrm{tail}}$。带限与 Nyquist 下 $\mathcal E_{\mathrm{alias}}=0$。仅允许有限阶 Euler–Maclaurin（EM）换序，以保证奇性与极阶不增。上述"三分误差"为**纯数学意义**下的解析余项与上界（含 Poisson 求和别名项、有限阶 EM 余项与带宽尾项），**不涉及实验噪声或仪器误差**。

---

## 1. 公理族

**A1（因果时空）**：$(M,g)$ 为时空流形，因果前沿由 $ds^2=0$ 与常数 $c$ 定标。

**A2（叶分解，局域/全局条件）**：在所考虑的时空域满足**全局双曲**（存在 Cauchy 叶）或处于**因果凸域**内，可选取时间函数 $t$ 使等时超曲面 $\Sigma_t$ 构成光滑叶分解，并诱导三维度规 $h$。当不具备全局双曲性时，以下关于"叶/雷达"的表述仅在该因果凸域内使用。

**A3（能量刻度）**：绝对连续谱上 $d\mu_\varphi(E)=\tfrac{\varphi'(E)}{\pi}\,dE=\rho_{\mathrm{rel}}(E)\,dE=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE$。

**A4（可实现性）**：任一仪器读数等价于"窗×核"对谱密度的加权，并服从 NPE 三分误差闭合。

**A5（概率与指针）**：Born 概率等价于最小相对熵（I-投影）；**设窗算子 $\mathcal W$ 自伴且 $\mathcal W\ge 0$**，指针基取 Ky-Fan 极大原则：给定窗算子 $\mathcal W$ 与维数 $k$，令 $P$ 为秩 $k$ 的投影，则 $\displaystyle \max_{\mathrm{rank}P=k}\operatorname{Tr}(P\mathcal W)=\sum_{i=1}^k\lambda_i^\downarrow(\mathcal W)$；指针子空间由 $\mathcal W$ 的前 $k$ 个特征向量张成。

**A6（换序纪律）**：一切离散—连续换序仅用有限阶 EM；奇性集合保持。

**A7（时间与空间的操作性定义）**：时间为因果偏序与最早可检互信息的联合刻度；**空间为等时叶 $\Sigma_t$ 内由度规 $h$ 的内在距离**；**雷达定标仅用于与 A1 中 $c$ 的对表，不作为长度的原始定义**。

---

## 2. 三位一体定理

**定理 2.1（相位—密度—延迟三位一体）**：对满足 Birman–Kreĭn 公式适用条件的自伴散射对 $(H,H_0)$，在绝对连续谱上几乎处处成立 $\varphi'(E)=\pi\,\rho_{\mathrm{rel}}(E)=\tfrac12\,\operatorname{tr}\mathsf Q(E)$。

**证明**：Weyl–Titchmarsh–Herglotz 定理给出谱密度表示 $\rho(E)=\pi^{-1}\Im m(E+i0)$，其中 $m(z)$ 为相应通道的 Weyl–Titchmarsh–Herglotz 函数，例如 $m(z)=\langle \psi,(H-z)^{-1}\psi\rangle$ 的边界值（$\psi$ 为适当边界向量/通道选择）；其非负虚部与绝对连续谱的 Radon–Nikodym 密度满足 $\rho(E)=\pi^{-1}\Im m(E+i0)$。Birman–Kreĭn 公式给出 $\det S(E)=\exp(-2\pi i\,\xi(E))$、$\rho_{\mathrm{rel}}(E)=-\xi'(E)$。由 $\mathsf Q(E)=-\,i\,S^\dagger\dfrac{dS}{dE}$ 与 Jacobi 恒等式得 $\partial_E\operatorname{Arg}\det S(E)=\operatorname{tr}\mathsf Q(E)$。合并得到结论。∎

**推论 2.2（阈值与奇性保持）**：带限+Nyquist 与有限阶 EM 下窗化不引入新奇性与极阶提升；阈值与共振由主尺度决定，可据"窗不变奇性"分辨物理结构与数值伪影。∎

---

## 3. 窗口化读数与 NPE 误差闭合

**定理 3.1（窗化读数恒等式）**：对带限窗 $w_R$ 与核 $\kappa$，任意可观测量的窗化读数表示为
$$
\boxed{\ \mathrm{Obs}=\frac{1}{2\pi}\int_{\mathbb R}w_R(E-E_0)\,[\kappa\star \rho_\star](E)\,dE+\mathcal E_{\mathrm{alias}}+\mathcal E_{\mathrm{EM}}+\mathcal E_{\mathrm{tail}}=\langle \rho_\star\rangle_{w,\kappa;E_0}+\mathcal E_{\mathrm{alias}}+\mathcal E_{\mathrm{EM}}+\mathcal E_{\mathrm{tail}}.\ }
$$
其中 $\rho_\star$ 取 $\rho$（绝对谱密度）或 $\rho_{\mathrm{rel}}$（相对态密度）。

**证明**：先引入加权平均记号 $\displaystyle \langle f\rangle_{w,\kappa;E_0}:=\frac{1}{2\pi}\int_{\mathbb R}w_R(E-E_0)\,[\kappa\star f](E)\,dE$。

**Case A（$\rho_{\mathrm{rel}}$）**：由三位一体关系 $\rho_{\mathrm{rel}}=\frac{1}{2\pi}\operatorname{tr}\mathsf Q=\frac{1}{\pi}\varphi'$ 且 $\varphi=\tfrac12\Phi$，有
$$
\langle \rho_{\mathrm{rel}}\rangle_{w,\kappa;E_0}
=\frac{1}{2\pi}\int w_R(E-E_0)\,[\kappa\star\tfrac{1}{\pi}\varphi'](E)\,dE
=-\frac{1}{2\pi^2}\int w_R'(E-E_0)\,[\kappa\star\varphi](E)\,dE
=-\frac{1}{4\pi^2}\int w_R'(E-E_0)\,[\kappa\star\Phi](E)\,dE,
$$
其中用到 $[\kappa\star\partial_E\Phi]=\partial_E[\kappa\star\Phi]$ 与分部积分（按分布理解），且 $\Phi(E):=\operatorname{Arg}\det S(E)$ 取 §0 的连续相位支。上式使用了分部积分与导数换序；在上述正则性与分布框架下边界项为零，故等式严格成立。

**Case B（$\rho$）**：由 Weyl–Titchmarsh–Herglotz 表示 $\rho(E)=\pi^{-1}\Im m(E+i0)$，直接有
$$
\langle \rho\rangle_{w,\kappa;E_0}=\frac{1}{2\pi}\int w_R(E-E_0)\,[\kappa\star\rho](E)\,dE.
$$

随后依 Poisson 求和（给出 $\mathcal E_{\mathrm{alias}}$）、有限阶 Euler–Maclaurin（给出 $\mathcal E_{\mathrm{EM}}$）与带宽截断（给出 $\mathcal E_{\mathrm{tail}}$）得到三分误差闭合。综上，两种情形均得到
$$
\boxed{\ \mathrm{Obs}=\langle \rho_\star\rangle_{w,\kappa;E_0}+\mathcal E_{\mathrm{alias}}+\mathcal E_{\mathrm{EM}}+\mathcal E_{\mathrm{tail}},\quad \rho_\star\in\{\rho,\rho_{\mathrm{rel}}\}\ },
$$
在带限+Nyquist 与有限阶 EM 下满足别名为零与奇性保持。∎

**非渐近上界**：存在常数 $C_{\mathrm{EM}}(k)$ 与 $C_{\mathrm{tail}}(R)$，使得 $|\mathcal E_{\mathrm{EM}}|\le C_{\mathrm{EM}}(k)\sup|\partial_E^{2k}(\cdot)|$、$|\mathcal E_{\mathrm{tail}}|\le C_{\mathrm{tail}}(R)|\cdot|_{L^1(E\notin[-\Omega,\Omega])}$，且随 $k$ 与带宽 $R$ 单调收敛。

---

## 4. 光速常数的窗口化群延迟读数与四重对齐

### 4.1 计量规约（读数）

**窗口化群延迟读数**定义为
$$
\boxed{\ \mathsf T[w_R,\kappa;L;E_0]:=\frac{\hbar}{2\pi}\int_{\mathbb R} w_R(E-E_0)\,\Big[\kappa\star \frac{1}{N}\operatorname{tr}\mathsf Q_L\Big](E)\,dE=\hbar\,\Big\langle \frac{1}{N}\operatorname{tr}\mathsf Q_L\Big\rangle_{w,\kappa;E_0}\ },
$$
其中 $L$ 为**等时叶 $\Sigma_t$ 内按度规 $h_{ij}$ 定义的端点内在距离**，$\frac{1}{N}\operatorname{tr}\mathsf Q_L$ 为链路每通道平均群延迟。**光速常数的窗化群延迟读数（计量规约）**记为
$$
\boxed{\ c^{\mathrm{read}}:=\lim_{\text{能量窗宽}\,\uparrow}\dfrac{L}{\mathsf T[w_R,\kappa;L;E_0]}\ },
$$
其中"能量窗宽$\uparrow$"等价于"$\tau$ 域频带宽 $\Omega_w(R)\downarrow 0$"，即 $\widehat w_R\Rightarrow 2\pi\delta$，而 $(2\pi)^{-1}\int w_R=1$ 始终成立。该极限与 $E_0$ 无关（见 §4.2）。并与 A1 中取作常数的 $c$ **等值**；此处**不构成对 $c$ 的重新定义**。

多端口链路可取 $\bar\tau(E):=\hbar\,\tfrac{1}{N}\operatorname{tr}\mathsf Q(E)$ 并先行能量依赖基线相消。

### 4.2 存在性、唯一性与窗/核无关性

**命题 4.2(a)（真空链路—恒等式）**：若 $S_L(E)=e^{iEL/(\hbar c)}I_N$，则 $q(E):=\tfrac1N\operatorname{tr}\mathsf Q_L(E)\equiv \tfrac{L}{\hbar c}$ 为常数，因而
$$
\mathsf T[w_R,\kappa;L;E_0]=\frac{\hbar}{2\pi}\int w_R(E-E_0)\,[\kappa\star q](E)\,dE=\frac{\hbar}{2\pi}\,\frac{L}{\hbar c}\int w_R(E-E_0)\,dE=\frac{L}{c},
$$
与 $(w_R,\kappa)$、带宽 $R$ 及 $E_0$ 无关。

**命题 4.2(b)（一般链路—极限形式，严谨版）**：设 $(w_R)_R$ 为 §0 之近似单位，满足 $\tfrac{1}{2\pi}\int w_R=1$、$\sup_R|w_R|_{L^1}<\infty$、$|w_R|_{L^\infty}\to0$ 且 $\widehat w_R\xrightarrow{\ \mathcal S'\ }2\pi\delta_0$；取 $\kappa\in L^1$ 且 $\int\kappa=1$。令
$$
q(E):=\frac{1}{N}\operatorname{tr}\mathsf Q_L(E)=q_0+\delta q(E),\qquad \delta q\in L^1(\mathbb R).
$$
则极限存在，且
$$
\boxed{\ \lim_{R\to\infty}\mathsf T[w_R,\kappa;L;E_0]=\hbar\left(q_0+\frac{1}{2\pi}\int_{\mathbb R}\delta q(E)\,dE\right)\ },
$$
与 $(w_R,\kappa,E_0)$ 无关。

**推论**（零均值情形）：若再加上
$$
\int_{\mathbb R}\delta q(E)\,dE=0,
$$
（例如先对真空链路作能量依赖基线相消后得到的相对读数），则
$$
\lim_{R\to\infty}\mathsf T[w_R,\kappa;L;E_0]=\hbar\,q_0.
$$

**证明略要**：写作 $\mathsf T=\hbar\big\langle q\big\rangle_{w,\kappa;E_0}$ 并代入 $q=q_0+\delta q$；第一项由 $\tfrac{1}{2\pi}\int w_R=1$ 给出 $\hbar q_0$。第二项在傅里叶域为 $\widehat w_R\cdot\widehat{(\kappa\star\delta q)}$，随 $R\to\infty$ 收敛到 $2\pi\delta_0\cdot\widehat{(\kappa\star\delta q)}$，反变换即取直流分量 $\tfrac{1}{2\pi}\int (\kappa\star\delta q)=\tfrac{1}{2\pi}\int\delta q$。∎

**注（修订）**：上式表明若不假设 $\int\delta q=0$，则**不可**简写为 $\frac{\hbar}{2\pi}\int q(E)\,dE$ 的常数倍；当且仅当 $\int\delta q=0$（或等价地，采用了"相对于真空链路"的零均值归一）时，方退化为 $\hbar q_0$。（真空链路对应 $\delta q\equiv0$，与 4.2(a) 一致。）

### 4.3 与三位一体刻度的等价

由 $\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q=\rho_{\mathrm{rel}}=\varphi'/\pi$ 得
$$
\mathsf T[w_R,\kappa;L;E_0]=\hbar\Big\langle \frac{1}{N}\operatorname{tr}\mathsf Q\Big\rangle_{w,\kappa;E_0}=\frac{2\hbar}{N}\langle \varphi'(E)\rangle_{w,\kappa;E_0}=\frac{\hbar}{N}\langle \Phi'(E)\rangle_{w,\kappa;E_0}.
$$

真空链路 $\Phi'(E)=\dfrac{NL}{\hbar c}$ 为常，故 $\mathsf T=L/c$ 与 $E_0$ 无关。

### 4.4 与因果前沿的等价

在 Kramers–Kronig 解析性与推迟格林函数支撑条件下，最早非零响应之前沿速度为 $c$。**对真空纯延迟链路**（$S_L(E)=e^{iEL/(\hbar c)}I_N$），由 4.1–4.3 知 $\mathsf T=L/c$；若测得 $\mathsf T\neq L/c$，则或破坏 NPE 封账，或破坏前沿因果。**对一般介质/几何链路**，前沿速度仍为 $c$。

**在纯传输且无显著反射/驻波，并满足几何光学（WKB）近似的链路条件下**，窗—核加权的群延迟可写为
$$
\boxed{\ \mathsf T[w_R,\kappa;L;E_0]=\frac{1}{c}\int_{\gamma}\big\langle n_g(\ell,E)\big\rangle_{w,\kappa;E_0}\,d\ell\ }.
$$
**一般情形**仅有严格恒等式
$$
\boxed{\ \mathsf T[w_R,\kappa;L;E_0]=\hbar\Big\langle \frac{1}{N}\operatorname{tr}\mathsf Q_L\Big\rangle_{w,\kappa;E_0}\ },
$$
其中右式由 §4.1–4.3 之定义与三位一体刻度直接给出；非在上述条件时不可无条件化为路径积分形式。窄带/弱色散极限下仍退化为 $\mathsf T\simeq \int_{\gamma} n_g(\ell)/c\,d\ell$。

**（修订）** 在被动、最小相位的**透明带**内，若该窗带上 $n(\omega)\ge 1$ 且 $\partial_\omega n(\omega)\ge 0$（正常色散）对 $\omega=E/\hbar$ 几乎处处成立，则带权平均满足
$$
\Big\langle n_g(\ell,E)\Big\rangle_{w,\kappa;E_0}\ \ge\ 1,
$$
从而 $\displaystyle \mathsf T[w_R,\kappa;L;E_0]\ \ge\ L/c$。一般情形**不作逐点 $n_g\ge 1$ 断言**；即使出现 $n_g<1$ 或 $n_g<0$ 的"快光/负群速"窗口，**前沿速度仍等于 $c$**，见本节首述的前沿—因果结论。

**适用域**：此前沿结论依赖于**微因果性**与**局域线性响应**（高频极限 $n(\omega)\to1$）及推迟格林函数的支撑性质；在非局域/强增益情形仅保证"最早非零响应不超出光锥"。

### 4.5 与信息光锥的等价

在接收端于阈前仅含独立噪声且无预共享携信变量的条件下，首次可检互信息的速度上确界等于 $c$。该上确界由前沿速度与三位一体刻度共同约束。

### 4.6 与计量实现的互逆

**以时定长**：取 $c$ 为常数，用 $\ell=c\,\Delta t$ 定义长度单位；**以延迟计长**：用 $\mathsf T$ 反算 $L$。真空链路严格互逆，弱色散下在 NPE 上界内一致。

---

## 5. 四个桥接常数的体系内定义

### 5.1 $\hbar$：Weyl–Heisenberg 中心荷（phase–time 2-cocycle 的物理尺）

**WSIG 定义（操作性）**：令 $U(\Delta t)$ 为物理时间平移、$V(\Delta E)$ 为能量调制的酉表示。其射影对易相位满足
$$
V(\Delta E)U(\Delta t)=\exp\!\Big(\tfrac{i}{\hbar}\Delta E\Delta t\Big)U(\Delta t)V(\Delta E).
$$
$\hbar$ 定义为把几何 2-余因子 $\exp(i\tau\sigma)$ 提升为物理量 $\exp\!\big(i\Delta E\Delta t/\hbar\big)$ 的**唯一比例尺**；并以**临界格** $\Delta t\Delta\omega=2\pi$ 锚定 $E=\hbar\omega$。Stone–von Neumann 唯一性定理保证该定标在正则类中唯一。

**EBOC 定义（结构性）**：在 EBOC 的时—频平移作用下，$\hbar$ 是 Weyl–Heisenberg 群的**中心荷**，把静态块上相位增量与时间叶参数的乘积映为能量刻度：$\Delta\Phi=\Delta E\Delta t/\hbar$。其值由 WSIG 定标唯一固定，因而在块—叶阅读中保持协变。

**RCA 定义（操作—计量）**：令一步演化 $U:=F=\exp(-iH_{\mathrm{CA}}\Delta t/\hbar)$，空间平移 $\sigma_a=\exp(iKa)$。Floquet 本征值 $U\psi=e^{-i\omega\Delta t}\psi$ 给出准能频率 $\omega$，据此读数 $E:=\hbar\omega$。$\hbar$ 由"步相 $\omega\Delta t$"到能量刻度的比例尺唯一确定。

**意义（三侧对照）**：$\hbar$ 是"相位—时间 2-cocycle"的中心荷：在 WSIG 中把 $\Delta E\Delta t$ 的几何相位提升为可计量相位；在 EBOC 中保证叶推进对 $E=\hbar\omega$ 的协变；在 RCA 中把离散步进的本征相位转为能标，实现三侧 $E\leftrightarrow\omega$ 的统一刻度。

**存在、唯一与窗/核无关性**：$\hbar$ 来自群表示的中心扩张，独立于 $(w_R,\kappa)$；对任意带限窗核，仅改变读数的收敛速率，不影响 $E=\hbar\omega$ 的比例尺。

### 5.2 $e$：$U(1)$ 规范 holonomy 的最小耦合量

**WSIG 定义（操作性）**：对**由最小基本 $U(1)$ 载荷**（如单电子，而非 Cooper 对）实现的闭合回路 $\mathcal C$，干涉相位
$$
\Delta\phi(\mathcal C)=\frac{q}{\hbar}\Phi_B(\mathcal C)\quad(\mathrm{mod}\ 2\pi).
$$
令 $\Phi_{0,B}$ 为该**基本载荷回路族**实现首个相位复现 $\Delta\phi=2\pi$ 的最小正磁通，定义
$$
e:=\frac{2\pi\hbar}{\Phi_{0,B}}.
$$
**Josephson 说明**：若观测到 $\Phi_0^{(J)}=h/(2e)$ 的周期，系由载荷 $2e$ 的复合态导致，其数据不可直接用于 $e$ 的原位定标；用于本定义时应以基本载荷回路的 $\Phi_{0,B}=h/e$ 为准。该定义仅用相位与磁通读数（在 WSIG 中以窗化相位实现），与传统电学单位无关。

**EBOC 定义（结构性）**：把 $U(1)$ 视为 EBOC 上的纤维联络。$e$ 是使回路 holonomy 的第一陈数实现**最小非平凡元素**时的耦合常数；其数值由 $\Phi_{0,B}$ 结合 $\hbar$ 唯一定标。

**RCA 定义（操作—计量）**：对局部更新引入 Peierls 相位 $\theta_{i+1/2}(n)$，闭合微回路的 Wilson 相位 $\oint\theta = 2\pi m$ 读出磁通量子 $\Phi_{0,B}$。定义 $e:=2\pi\hbar/\Phi_{0,B}$，其最小值对应**最小基本载荷**的回路。

**意义（三侧对照）**：$e$ 把"相位 holonomy $\leftrightarrow$ 规范耦合"统一：WSIG 以相位回路定标，EBOC 以联络的第一陈类定标，RCA 以离散 Wilson 回路定标；三侧共同保证 $\Phi_{0,B}=2\pi\hbar/e$ 的装置无关性。

**窗/核无关与稳定性**：在 Nyquist 与有限阶 EM 下，$\Phi_{0,B}$ 的确定不随 $(w_R,\kappa)$ 改变；跨装置基线相消保持 $\Phi_{0,B}$ 的不变性。

### 5.3 $k_{\mathrm B}$：信息温度到热温标的比例尺

**WSIG 定义（操作性）**：在能量约束的最大熵（最小 KL/I-投影）下，最优分布
$$
p^\star\propto \exp(-\beta E).
$$
把自然参数 $\beta$ 与热温标 $T$ 以
$$
T:=\frac{1}{k_{\mathrm B}\beta}
$$
对齐，**定义** $k_{\mathrm B}$ 为把"每能量的纳特"映到"每开尔文"的比例尺。谱斜率读数满足
$$
\partial_\omega\log\!\Big[\tfrac{I(\omega)}{\omega^3}\Big]
=-\frac{\hbar}{k_{\mathrm B}T}\cdot\frac{e^{\hbar\omega/(k_{\mathrm B}T)}}{e^{\hbar\omega/(k_{\mathrm B}T)}-1},
$$
在 **Wien 极限** $\hbar\omega\gg k_{\mathrm B}T$ 下近似为 $-\hbar/(k_{\mathrm B}T)$。据此以"精确公式 + Wien 极限近似"联合锚定 $k_{\mathrm B}$，与卡诺温标构成双锚定标，保证唯一性与无环化。

**EBOC 定义（结构性）**：在静态块的叶上，自由能密度 $F=U-TS$ 把能量测度与信息熵（KL/Bregman 对偶势）同构。$k_{\mathrm B}$ 是把对偶势的自然参数 $\beta$ 转为温标 $T$ 的唯一比例尺，确保自由能、涨落与响应的协变表述。

**RCA 定义（操作—计量）**：在固定能量预算与可见胞元窗口下，以 I-投影得到 $p^\star\propto\exp(-\beta E)$ 的离散能谱直方；由多窗合成的 Wien 区斜率读出 $\beta$，再以 $T:=1/(k_{\mathrm B}\beta)$ 锚定温标。

**意义（三侧对照）**：$k_{\mathrm B}$ 把"信息参数 $\beta$"转为"热温标 $T$"：WSIG 由谱斜率与卡诺温标双锚；EBOC 由自由能的对偶势锚定；RCA 由可见态数与能谱直方锚定，三侧合一。

### 5.4 $G$：曲率—能量密度的几何耦合系数

**WSIG 定义（操作性）**：以窗化群延迟与相位层析反演几何曲率（或弱场势），以能量窗读取 $T_{\mu\nu}$ 的能量—动量通量。定义 $G$ 为使
$$
G_{\mu\nu}=\frac{8\pi G}{c^4}T_{\mu\nu}
$$
在所测域内成立的**唯一比例系数**；牛顿极限 $\nabla^2\phi=4\pi G\rho_E/c^2$ 作为一致性约束。带限+Nyquist 与有限阶 EM 确保"延迟/偏折"与"能流"两侧的窗/核无关性。

**EBOC 定义（结构性）**：在静态块上，$G$ 把曲率泛函（测地偏差/光学度规）与能量密度测度配对为同一单位；其值由 WSIG 对表唯一定标，并在叶变换下协变。

**RCA 定义（操作—计量）**：以局域子步计划 $\mathcal S(i)$ 与占空比定义群折射率 $n_g(i):=\tau_g(i)/\Delta t$，以离散 Noether 读数得到能流张量 $T^{\mu\nu}_{\mathrm{CA}}$。定义 $G$ 使离散曲率（微回路并行输运相位）与能流密度在悬挂极限中对表 $\displaystyle G_{\mu\nu}\sim \frac{8\pi G}{c^4}T_{\mu\nu}$ 的单位配比。

**意义（三侧对照）**：$G$ 统一"几何$\leftrightarrow$能流"的量纲：WSIG 侧通过相位-延迟-密度三刻度把曲率读数转为能量密度；EBOC 侧以光学度规/测地偏差配对能流；RCA 侧以子步-能流读数对齐，三侧单位一致。

### 5.5 无环化与独立性

**命题 5.1（DAG）**：单位—定标依赖图为 L0$\to$L1$\to$L2$\to$L3 的有向无环图：

**L0**：$(M,g),c$ 与相位/计数读数；

**L1**：可观测比例类（$\Phi',\operatorname{tr}\mathsf Q,\rho_{\mathrm{rel}}$ 等）；

**L2**：$\hbar$（时间–频率锚）、$e$（holonomy 锚）、$k_{\mathrm B}$（温标与谱斜率双锚）、$G$（曲率—能流对表锚）；

**L3**：绝对标度的全部物理量。

四常数的定标锚彼此独立，且均不依赖待定常数本身；任何假设回路都会与三位一体刻度、NPE 误差闭合或相应的双锚校核矛盾，因而被排除。

---

## 6. 导出物理量及其在 EBOC 与可逆元胞自动机中的语义等价

设 EBOC 为二维子移位 $X\subset\mathcal A^{\mathbb Z^2}$，坐标记为 $(i,t)\in\mathbb Z\times\mathbb Z$ 或经悬挂流得到的 $(i,t)\in\mathbb Z\times\mathbb R$；每个时间叶 $\Sigma_t:=\{(i,t):i\in\mathbb Z\}$ 搭配诱导度规 $h$。设可逆元胞自动机（RCA）为一维子移位 $Y\subset\mathcal B^{\mathbb Z}$ 与双射滑动块码 $F:Y\to Y$，局部半径为 $r$，格点间距为 $a$，基准时隙为 $\Delta t$。定义最大传播锥（光锥）
$$
\Lambda:=\{(i,n)\in\mathbb Z^2:\ |i|\le rn\},
$$
并以悬挂流构造算符谱 $U:=\exp(-iH_{\mathrm{CA}}\Delta t/\hbar)$ 与位移谱 $\sigma_a:=\exp(iKa)$。本节给出物理量在 $\text{EBOC}\leftrightarrow\text{RCA}$ 的语义等价字典与读数式，均遵循统一母尺 $\varphi'(E)\Longleftrightarrow\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\Longleftrightarrow\rho_{\mathrm{rel}}(E)$。

### 6.1 语义接口：切片—悬挂与读数算子

**WSIG（窗化读数）**：在**真空基线链路**上以 $\mathsf T[w_R,\kappa;L;E_0]$ **验证** $L/\mathsf T=c$。**在纯传输且无显著反射/驻波，并满足几何光学（WKB）近似的链路条件下**，
$$
\boxed{\ \mathsf T[w_R,\kappa;L;E_0]=\frac{1}{c}\int_{\gamma}\big\langle n_g(\ell,E)\big\rangle_{w,\kappa;E_0}\,d\ell\ }.
$$
**一般情形**仅有严格恒等式
$$
\boxed{\ \mathsf T[w_R,\kappa;L;E_0]=\hbar\Big\langle \frac{1}{N}\operatorname{tr}\mathsf Q_L\Big\rangle_{w,\kappa;E_0}\ }.
$$
速度上界仍由 A1 的 $c$ 限定。所有观测量通过窗—核对 $(w_R,\kappa)$ 与中心能量 $E_0$ 的能量域读数实现，并服从 NPE 三分误差闭合。以 $\mathsf T[w_R,\kappa;L;E_0]$ 得到的 $c^{\mathrm{read}}$ 为 A1 常数 $c$ 的**计量等值**。

**EBOC（静态块）**：时间叶推进以叶索引 $t$ 表示，光锥上界为 $c$。叶内度规 $h_{ij}$ 给出空间长度刻度。

**RCA（离散步进）**：离散步进以 $n\in\mathbb Z$ 表示，通过悬挂流 $t:=n\Delta t$ 映为连续时间；格距 $a$、半径 $r$、步隙 $\Delta t$。由读数**唯一确定比值** $\displaystyle \frac{a}{\Delta t}$ 使 $c_{\mathrm{CA}}:=\tfrac{ra}{\Delta t}=c$；$a,\Delta t$ 分别在 **§6.4** 的"谱对齐"（$E=\hbar\omega,p=\hbar k$）中锁定。

**意义（三侧对照）**：三侧共享同一速度上界 $c$，并以窗化读数对齐时空参数；读数算子在三侧以相同的 NPE 误差账本闭合。

### 6.2 时—空—速—加速度

**时间**
- **WSIG**：以窗化群延迟 $\mathsf T[w_R,\kappa;L;E_0]$ 给出时间刻度。
- **EBOC**：因果偏序的参量 $t$。
- **RCA**：步进索引 $n$ 与 $t=n\Delta t$。

**空间与长度**
- **WSIG**：以 $c\mathsf T$ 给出长度单位（雷达法）。
- **EBOC**：$\ell(\gamma)=\int\sqrt{h_{ij}\dot\gamma^i\dot\gamma^j}\,ds$。
- **RCA**：图度量 $d_{\mathrm{CA}}(i,j):=|i-j|a$，雷达法 $\ell_{\mathrm{CA}}(\gamma):=N_{\mathrm{gate}}(\gamma)\tfrac{a}{2}$（最短往返门数 $N_{\mathrm{gate}}(\gamma)$）；经 $c_{\mathrm{CA}}=c$ 标定与 EBOC 一致。

**速度与上界**
- **WSIG**：速度上界 $c$ 由 $\mathsf T[w_R,\kappa;L;E_0]$ 定标。
- **EBOC**：$v=d\ell/dt$，$|v|\le c$。
- **RCA**：$v_{\mathrm{CA}}:=\lim_{n\to\infty}\frac{|i(n)-i(0)|a}{n\Delta t}\le \frac{ra}{\Delta t}=c$。

**加速度**
- **WSIG**：通过速度变化率的窗化读数给出。
- **EBOC**：$a=dv/dt$。
- **RCA**：定义离散位置 $x(n):=i(n)a$，加速度 $a_{\mathrm{CA}}:=\frac{x(n+1)-2x(n)+x(n-1)}{(\Delta t)^2}$，悬挂极限与 EBOC 一致。

**意义（三侧对照）**：时空量由 $c$ 与 $\mathsf T$ 统一定标；三侧速度上界一致；加速度在悬挂极限协变。

### 6.3 波—相—色散与群参数

**平面模态**
- **WSIG**：$\varphi'(E)=\tfrac12\operatorname{tr}\mathsf Q(E)$，色散由窗化相位读数给出。
- **EBOC**：波模 $\exp\bigl(i(k\cdot x-\omega t)\bigr)$，色散关系 $\omega=\omega(k)$。
- **RCA**：Koopman 模态 $\psi_{k,\omega}(j,n)=\exp\bigl(i(kaj-\omega n\Delta t)\bigr)$，$k\in[-\pi/a,\pi/a]$（第一布里渊区）；局部规则线性化给出离散 $\omega=\omega(k)$。

**相位与群速度**
- **WSIG**：先由窗化相位读数估计色散 $\omega(k)$，再取 $\displaystyle v_g=\frac{\partial\omega}{\partial k}$。能量域下用于校准的**通道平均**群延迟为 $\displaystyle \bar\tau_g(E)=\frac{\hbar}{N}\operatorname{tr}\mathsf Q(E)=\frac{2\hbar}{N}\,\varphi'(E)=\frac{2}{N}\,\partial_\omega\varphi(E)$；**单通道**（特征相位 $\theta_\alpha$）则有 $\displaystyle \tau_{g,\alpha}(E)=\hbar\,\partial_E\theta_\alpha(E)=\partial_\omega\theta_\alpha(E)$。与 $\omega(k)$ 联合校准。
- **EBOC**：由波模 $\exp\bigl(i(k\cdot x-\omega t)\bigr)$，**相位增量** $\boxed{\ \Delta\varphi=k\Delta\ell-\omega\Delta t\ }$，$v_g=\partial\omega/\partial k$。
- **RCA**：Koopman 模态 $\psi_{k,\omega}(j,n)=\exp\bigl(i(kaj-\omega n\Delta t)\bigr)$，**相位增量** $\boxed{\ \Delta\varphi=ka-\omega\Delta t\ }$，$\displaystyle v_g=\frac{\partial\omega}{\partial k}\le c$。亦可记无量纲斜率 $\partial_{(ka)}(\omega\Delta t)=v_g\Delta t/a$。

**群延迟（窗口化）**
- **WSIG**：通道平均 $\displaystyle \bar\tau_g=\frac{\hbar}{N}\operatorname{tr}\mathsf Q=\frac{2\hbar}{N}\,\partial_E\varphi=\frac{2}{N}\,\partial_\omega\varphi$，与 $\mathsf T[w_R,\kappa;L;E_0]$ 对表。
- **EBOC**：$\tau_g=\partial\varphi/\partial\omega$。
- **RCA**：由 Floquet $\omega(k)$ 读出，与 WSIG 对表。

**意义（三侧对照）**：三侧色散关系由同一相位母尺 $\varphi'(E)\Longleftrightarrow\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$ 统一；群延迟量纲为时间，含 $\hbar$ 因子，三侧一致。

### 6.4 能量—动量—质量—作用

**能量与动量**
- **WSIG**：$E=\hbar\omega$、$p=\hbar k$ 由窗化相位读数给出。
- **EBOC**：$E=\hbar\omega$、$p=\hbar k$。
- **RCA**：悬挂生成元 $U=\exp(-iH_{\mathrm{CA}}\Delta t/\hbar)$、位移生成元 $\sigma_a=\exp(iKa)$ 给出 $E=\hbar\omega$、$p=\hbar k$。

**质量**
- **WSIG**：静止能量 $E_0$ 由 $c$ 与 $\hbar$ 定标，$m:=E_0/c^2$。
- **EBOC**：$m:=E_0/c^2$。
- **RCA**：取 $k=0$ 的本征支 $\omega(0)$ 给出 $m=\hbar\omega(0)/c^2$。

**作用**
- **WSIG**：作用由相位读数给出。
- **EBOC**：$S=\int(pd\ell-Edt)$。
- **RCA**：离散作用 $S_{\mathrm{CA}}:=\sum_{n}\bigl(p_n\Delta \ell_n-E_n\Delta t\bigr)$，悬挂极限与 EBOC 一致。

**意义（三侧对照）**：$E,p,m,S$ 由 $\hbar,c$ 统一定标；三侧在 $E=\hbar\omega$ 与 $p=\hbar k$ 的锚定下对齐。

### 6.5 概率—指针—测量

**概率**
- **WSIG**：以 I-投影得到 $p^\star\propto\exp(-\beta E)$，约束由窗化能量读数 $\langle\rho_\star\rangle_{w,\kappa;E_0}$ 实现。
- **EBOC**：窗局域化的测度结构与 I-投影等价。
- **RCA**：有限胞元窗口下的 I-投影给出 $p^\star\propto\exp(-\beta E)$ 的离散能谱分布。

**指针基**
- **WSIG**：窗算子的 Ky-Fan 极大（选择 $\mathcal W$ 的前 $k$ 个特征值对应子空间）。
- **EBOC**：窗算子的 Ky-Fan 极大，在同一 $\rho_{\mathrm{rel}}$ 刻度上实现。
- **RCA**：有限柱集诱导的窗算子 $\mathcal W_{R,T}$ 的 Ky-Fan 极大。

**意义（三侧对照）**：三侧指针基与概率分布在同一 $\rho_{\mathrm{rel}}$ 刻度上等价，保证测量的一致性与 Born 规则的统一实现。

### 6.6 通量—应力—守恒

**四流与连续方程**
- **WSIG**：守恒律由窗化读数的谱密度守恒给出。
- **EBOC**：$\nabla_\mu J^\mu=0$。
- **RCA**：键流 $J_{i+1/2}(n):=\frac{1}{\Delta t}\bigl(N_{i\to i+1}(n)-N_{i+1\to i}(n)\bigr)$，离散散度 $\frac{Q_i(n+1)-Q_i(n)}{\Delta t}+ \frac{J_{i+1/2}(n)-J_{i-1/2}(n)}{a}=0$，窗口化极限与 EBOC 一致。

**应力—能量张量**
- **WSIG**：$T^{\mu\nu}$ 由窗化能量—动量读数给出。
- **EBOC**：$T^{\mu\nu}$ 由 Noether 定理给出，$\nabla_\nu T^{\mu\nu}=0$。
- **RCA**：局域能密度 $\varepsilon_i$、动量密度 $\pi_i$ 给出 $T^{00}_{\mathrm{CA}}:=\varepsilon$、$T^{01}_{\mathrm{CA}}:=c\pi$、$T^{11}_{\mathrm{CA}}$（压强/应力密度）；离散 Noether—Belinfante 得 $\nabla_\nu T^{\mu\nu}_{\mathrm{CA}}=0$。

**意义（三侧对照）**：守恒律与应力—能量张量在三侧以窗化读数统一，悬挂极限协变。

### 6.7 规范—电荷—Wilson 回路

**$U(1)$ 规范**
- **WSIG**：回路相位由窗化相位读数给出，$\Phi_{0,B}=2\pi\hbar/e$，电荷 $e$ 由首个相位复现定标。
- **EBOC**：最小耦合 $p\mapsto p-qA$，回路 holonomy 给出 $\oint A=\Phi_{0,B} m$。
- **RCA**：Peierls 替换引入边相位 $\theta_{i+1/2}(n)$，Wilson 回路相位 $\Phi_\square:=\theta_{i+1/2}(n)+\theta_{i+1}(n+1/2)-\theta_{i+1/2}(n+1)-\theta_{i}(n+1/2)$ 作为离散场强 $\mathcal F$；$\oint \theta =2\pi m$ 给出量子化通量。

**意义（三侧对照）**：三侧对同一 Wilson 回路相位读数给出一致的最小耦合单位 $\Phi_{0,B}=2\pi\hbar/e$ 与电荷守恒律；规范不变性在三侧等价。

### 6.8 曲率—几何—并行输运

**度规与光学等效**
- **WSIG**：曲率由窗化相位层析读数反演。
- **EBOC**：Gordon 光学度规 $g^{\mathrm{opt}}_{\mu\nu}=g_{\mu\nu}+(1-1/n^2)u_\mu u_\nu$。
- **RCA**：时钟占空比与局部子步数 $m(i)$ 表示介质效应，等效群折射率 $n_g(i):=\frac{\text{每格有效子步数}}{\text{基准子步数}}=\frac{\tau_g(i)}{\Delta t}$。**在（纯传输＋WKB）条件下的时间延迟**：
$$
\tau(\gamma)=\frac{1}{c}\int_{\gamma} n_g\,d\ell.
$$
**一般情形**采用
$$
\tau(\gamma)=\mathsf T[w_R,\kappa;L;E_0]=\hbar\Big\langle \frac{1}{N}\operatorname{tr}\mathsf Q_L\Big\rangle_{w,\kappa;E_0}.
$$

**离散曲率**
- **WSIG**：曲率测量由相位—延迟—密度统一刻度给出。
- **EBOC**：Riemann 曲率张量。
- **RCA**：联络为局部相位平移，微回路并行输运相位偏差为离散曲率；窗口化极限对应 EBOC 的 Riemann 曲率张量测量性不变量。

**意义（三侧对照）**：曲率与光学度规在三侧通过相位—延迟—密度统一刻度对齐；$G$ 统一几何↔能流的量纲。

### 6.9 折射率—介质密度—时钟重标

**相位折射率与群折射率**
- **WSIG**：$n,n_g$ 由窗化相位与群延迟读数给出。
- **EBOC**：$\lambda=c/(nf)$；**（纯传输＋WKB）条件下**
$$
\tau_g(\gamma)=\frac{1}{c}\int_{\gamma} n_g\,d\ell.
$$
**一般情形**：传播时间由
$$
\mathsf T[w_R,\kappa;L;E_0]=\hbar\Big\langle \frac{1}{N}\operatorname{tr}\mathsf Q_L\Big\rangle_{w,\kappa;E_0}
$$
给出。
- **RCA**：局部更新计划 $\mathcal S(i)$ 的子步安排给出 $n(i):=\frac{\text{相位子步周期}}{\text{基准周期}}$、$n_g(i):=\frac{\partial \varphi}{\partial \omega}\big/\Delta t$。

**介质效应**：介质密度升高导致局部等待子步数增加，$n,n_g$ 同向增大，对应传播时间刻度的等效伸长。

**意义（三侧对照）**：$n,n_g$ 在三侧以时间延迟与相位读数统一定标；介质密度对时钟重标的影响在三侧等价。

### 6.10 温度—熵—化学势

**温度与熵**
- **WSIG**：$T$ 由谱斜率与卡诺温标双锚定标（见 5.3），$S$ 由 I-投影与窗化能量读数给出。
- **EBOC**：$S=-k_{\mathrm B}\sum p\ln p$、$T^{-1}=\partial S/\partial E$。
- **RCA**：窗化能量直方与 I-投影给出相同形式；有效态数 $\Omega_{\mathrm{eff}}$ 定义 $S_{\mathrm{CA}}:=k_{\mathrm B}\ln \Omega_{\mathrm{eff}}$、$T^{-1}=\frac{\partial S_{\mathrm{CA}}}{\partial E}$。

**化学势与守恒族**
- **WSIG/EBOC/RCA**：若存在守恒计数 $N=\sum_i n_i$，三侧配分函数 $\mathcal Z=\sum_{\text{states}}\exp\bigl(-\beta(E-\mu N)\bigr)$，并以窗化读数校准 $(\beta,\mu)$。

**意义（三侧对照）**：温标、熵与化学势在三侧由 $k_{\mathrm B}$ 与 I-投影统一定标；有效态数在三侧对应。

### 6.11 力—非测地性—最小耦合（离散表达）

**统一定义**
- **WSIG**：力由窗化读数与最小耦合 $\langle \mathcal Q,\mathcal F\rangle$ 确定，荷符号 $\mathcal Q$ 区分于 Wigner–Smith 矩阵 $\mathsf Q$。
- **EBOC**：$f^\mu=mu^\nu\nabla_\nu u^\mu$（非测地性）$=-\nabla_\nu T^{\mu\nu}_{\mathrm{matter}}$（物质动量通量散度）$=\langle \mathcal Q,\mathcal F^{\mu}{}_{\nu}\rangle u^\nu$（最小耦合）。
- **RCA**：定义离散协变差分 $\nabla_\nu^{\mathrm{d}}$ 与四速度 $u^\mu_{\mathrm{d}}$，取 $f^\mu_{\mathrm{CA}}:=mu^\nu_{\mathrm{d}}\nabla^{\mathrm{d}}_\nu u^\mu_{\mathrm{d}}=-\nabla^{\mathrm{d}}_\nu T^{\mu\nu}_{\mathrm{CA},\mathrm{matter}}=\langle \mathcal Q,\mathcal F^{\mu}{}_{\nu}\rangle u^\nu_{\mathrm{d}}$。

**意义（三侧对照）**：三侧力的三重等价（非测地性$=$动量通量散度$=$最小耦合）在悬挂极限一致；荷 $\mathcal Q$ 与 Wigner–Smith $\mathsf Q$ 明确区分，保证物理含义与量纲清晰。

### 6.12 读数一致性与不变量

**WSIG 定义（窗化读数）**：对任意窗—核对 $(w_R,\kappa)$ 与中心能量 $E_0$，观测量以
$$
\boxed{\ \mathrm{Obs}=\frac{1}{2\pi}\int_{\mathbb R}w_R(E-E_0)[\kappa\star\rho_{\star}](E)dE=\langle \rho_\star\rangle_{w,\kappa;E_0}+\mathcal E_{\mathrm{alias}}+\mathcal E_{\mathrm{EM}}+\mathcal E_{\mathrm{tail}}\ }
$$
读取，并以 NPE 三分误差闭合。Trinity 保证 $\varphi'(E)\Longleftrightarrow\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\Longleftrightarrow\rho_{\mathrm{rel}}(E)$ 的统一刻度。

**EBOC 与 RCA**：两侧同名量在 WSIG 读数下量纲与数值对齐；读数算子服从相同的 NPE 误差账本。

**不可变性（三侧对照）**
- 在带限与 Nyquist 条件及有限阶 EM 纪律下，阈值、共振与奇性集合在三侧映射中保持。
- **信息/前沿速度**的上界由 $c$ 统一固定；**相速度与群速度/群延迟**在被动最小相位且无强反常色散时满足 $n_g\ge 1$ 的通常界，但在存在增益或强反常色散时可超光或为负，且不违背前沿因果（见 §4.4）。
- Wilson 回路相位的整数性不随窗—核改变。

**意义（三侧对照）**：三侧读数在同一母尺 $\varphi'(E)\Longleftrightarrow\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\Longleftrightarrow\rho_{\mathrm{rel}}(E)$ 下闭合，保证物理量的一致性、上界的一致性与不变量的一致性。

### 6.13 实施与校准步骤（最小足够集）

**步 1（速度对齐）**：以基线链路测得 $\mathsf T[w_R,\kappa;L;E_0]$ 并**验证** $L/\mathsf T=c$；在 RCA 侧选取 $(a,\Delta t)$ 使 $ra/\Delta t=c$。

**步 2（谱对齐）**：以多窗对 $\partial_E\operatorname{Arg}\det S$ 与 $\operatorname{tr}\mathsf Q$ 同步读数，校准 $E=\hbar\omega$、$p=\hbar k$ 与 $\omega(k)$。

**步 3（介质对齐）**：在 EBOC 侧用 $n,n_g$ 读出介质；在 RCA 侧以子步计划 $\mathcal S(i)$ 与占空比重现 $\tau_g$ 的空间分布。**一般情形**以严格恒等式
$$
\mathsf T[w_R,\kappa;L;E_0]=\hbar\Big\langle \frac{1}{N}\operatorname{tr}\mathsf Q_L\Big\rangle_{w,\kappa;E_0}
$$
对表；**仅在纯传输、无显著反射/驻波且满足几何光学（WKB）近似时**，再行验证
$$
\mathsf T[w_R,\kappa;L;E_0]=\frac{1}{c}\int_{\gamma}\big\langle n_g(\ell,E)\big\rangle_{w,\kappa;E_0}\,d\ell.
$$
（与 §4.4 保持一致。）

**步 4（规范—几何对齐）**：以 AB/Josephson 型相位与 Wilson 回路相位对齐 $e$；以微回路并行输运相位对齐离散曲率与 EBOC 曲率的层析读数。

上述等价保证所有导出物理量在 EBOC 静态块与 RCA 可逆演化之间的读数一致性、上界一致性与不变量一致性，且均以统一母尺 $\varphi'(E)\Longleftrightarrow\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\Longleftrightarrow\rho_{\mathrm{rel}}(E)$ 实现。

---

## 7. 力的统一定义与分类

**统一定义**：$f^\mu=\dfrac{D p^\mu}{D\tau}=m\,u^\nu\nabla_\nu u^\mu$。

**三重等价**：
$$
\text{力}=\underbrace{m\,u^\nu\nabla_\nu u^\mu}_{\text{非测地性}}=\underbrace{-\,\nabla_\nu T^{\mu\nu}_{\mathrm{matter}}}_{\text{物质部分的动量通量散度}}=\underbrace{\langle \mathcal Q,\ \mathcal F^{\mu}{}_{\nu}\rangle\,u^\nu}_{\text{最小耦合}}.
$$

**证明**：将总应力—能量张量分解为 $T^{\mu\nu}=T^{\mu\nu}_{\mathrm{matter}}+T^{\mu\nu}_{\mathrm{field}}$，由 $\nabla_\nu T^{\mu\nu}=0$ 得 $-\nabla_\nu T^{\mu\nu}_{\mathrm{matter}}=\nabla_\nu T^{\mu\nu}_{\mathrm{field}}=:f^\mu$，与最小耦合项对表一致。规范联络的最小耦合给出 $\langle \mathcal Q,\mathcal F\rangle$ 形式，自由落体满足 $f^\mu=0$。微观读数以 $\dot{\mathbf p}=\hbar\dot{\mathbf k}$、$\dot E=\hbar\dot\omega$ 实现，并与三位一体刻度及窗化恒等式相容。

**分类**：几何力（度规/联络）、规范力（$U(1)$/非阿贝尔）、有效力（自由能梯度、辐射压）。所有观测量落在 $\varphi'$、$\operatorname{tr}\mathsf Q$、$\rho_{\mathrm{rel}}$ 同一母尺上。

---

## 8. 新力的可定义性与最小对象

**判据**：以已知模型的 $\rho_{\mathrm{rel}}^{\mathrm{known}}(E)$ 为基线，构造残差 $r(E):=\varphi'(E)-\pi\,\rho_{\mathrm{rel}}^{\mathrm{known}}(E)$。若 $r$ 在多窗/多核、Nyquist 安全采样下稳健非零且超出 NPE 上界，并满足 Herglotz/KK 解析一致性，则定义新力 $\mathfrak F$ 为使 $r(E)\equiv \pi\,\rho_{\mathrm{rel}}^{\mathfrak F}(E)$ 的最小对象。

**构造**：以 $r/\pi$ 为边界密度建立 Herglotz 函数 $m_{\mathfrak F}(z)=\int\dfrac{d\mu_{\mathfrak F}(\lambda)}{\lambda-z}$ 得谱测度 $\mu_{\mathfrak F}$；由 $\mu_{\mathfrak F}$ 构造最小 de Branges 空间与再生核 $K$，使 $K(x,x)=\pi^{-1}\varphi'(x)\,|E(x)|^2$；以"窗不变奇性、阈值迁移、holonomy 周期、通量差"等不变量将 $m_{\mathfrak F}$ 归入几何/规范/有效类之一。有限阶 EM 保证奇性保持。

---

## 9. 无环化定理

**DAG 结构**：L0（基元 $(t,\Sigma_t,h,c)$+计数/相位）$\to$ L1（可观测比例类）$\to$ L2（双锚定标 $\hbar,e,k_{\mathrm B},G$）$\to$ L3（绝对量）。

**证明**：L1 仅由 L0 构造至比例；四常数定标锚两两独立（时间–频率、holonomy、卡诺温标与谱斜率、曲率–能流配对），无回边；任何闭环假设与三位一体刻度、NPE 封账或量子计量闭环矛盾，故被观测排除。∎

---

## 10. 工程实现与复现实验

**尺子校准**：同一装置内实现 $\hbar$（临界格）、$e$（首个 holonomy 复现）、$k_{\mathrm B}$（卡诺温标与谱斜率联合）、$G$（时延/偏折层析）。

**相位—延迟一致性**：并行获取 $\partial_E\operatorname{Arg}\det S$ 与 $\operatorname{tr}\mathsf Q$，以 $\rho_{\mathrm{rel}}$ 对表验证三位一体刻度。

**Nyquist 安全采样**：记录采样四元 $(\Omega,\Delta,T,M)$，验证 $\mathcal E_{\mathrm{alias}}=0$，$\mathcal E_{\mathrm{EM}}$ 与 $\mathcal E_{\mathrm{tail}}$ 满足上界。

**概率与指针**：I-投影（软到硬）与 Ky-Fan 极大并行验证。

**残差与新力**：在已知耦合拟合后计算 $r(E)$，越界则按第 8 节流程给出 $\mathfrak F$ 的最小对象与不确定度。

---

## 结论

以 $c$+时空几何为因果骨架，以 $\varphi'(E)\Longleftrightarrow \tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\Longleftrightarrow \rho_{\mathrm{rel}}(E)$ 为能量轴唯一刻度，以 WSIG 为读数学，以 $\hbar,e,k_{\mathrm B},G$ 为体系内定标，形成存在、唯一与窗/核无关的测量—定标链条。光速常数的窗口化群延迟定义与三位一体刻度、因果前沿与信息光锥、计量实现互相等价。导出量与力的表述在同一母尺上闭合；任何超出已知耦合的现象将以相位—密度—延迟残差的形式出现，并可通过 Herglotz–de Branges 的最小对象流程得到严格定义与测度。

---
