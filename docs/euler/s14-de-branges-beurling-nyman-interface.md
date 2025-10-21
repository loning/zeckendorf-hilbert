# S14. de Branges / Beurling–Nyman 界面

**—— 镜像核、Hilbert 子空间与信息—变分等价**

**作者**：Auric
**日期**：2025-10-21

---

## 摘要（定性）

在带权 Mellin–Hilbert 空间中，本文把功能方程的中心对称实现为酉镜像算子，并以满足自反性的核构造再生核 Hilbert 空间（RKHS），由此将完成函数写为内积评估且保持镜像对称。选取与显式/迹公式一致的窗—字典生成 Beurling–Nyman（BN）型子空间，给出最小能量 mollifier 的正交投影与谱（Gram）表示；在与软最大势一致的参数化（信息—几何对齐）下，证明该投影极小化与最小 KL/Bregman 代价**等价**。全流程严格采用**有限阶** Euler–Maclaurin（EM）与方向亚纯化纪律，确保"极点仅来自主尺度"；增长与窗条件与完成函数的 $\Gamma/\pi$ 正规化及方向支持函数上界一致。结构在 Riemann $\xi$、Dirichlet $L(\chi,\cdot)$、自守形式 $L$-函数等典型实例中统一成立。

---

## 0. 记号与前置

### 0.1 完成函数与中心轴

设 $L(s)=\sum_{n\ge1}a_n n^{-s}$ 可经标准 $\Gamma/\pi$ 因子正规化。给定 $Q>0$、实数 $a$，定义完成函数

$$
\Xi(s):=Q^{s/2}\,r(s)\,L(s),\qquad r(a-s)=r(s),\qquad \Xi(a-s)=\varepsilon\,\Xi(s),\ |\varepsilon|=1,
$$

称 $\Re s=\tfrac a2$ 为**中心轴**。

### 0.2 带权 Mellin–Hilbert 空间与 Plancherel–Mellin

置

$$
\mathcal H_a:=L^2\!\big(\mathbb R_+,x^{a-1}dx\big),\qquad
\langle f,g\rangle_a=\int_0^\infty f(x)\overline{g(x)}\,x^{a-1}dx.
$$

采用归一化 Mellin 变换

$$
\mathcal M_a[f](s):=\int_0^\infty f(x)\,x^{\,s}\,\frac{dx}{x},\qquad s\in\mathbb C.
$$

在直线 $\Re s=\tfrac a2$ 上有 Plancherel–Mellin 判据

$$
|f|_{\mathcal H_a}^2=\frac1{2\pi}\int_{\mathbb R}\Big|\mathcal M_a[f]\Big(\tfrac a2+it\Big)\Big|^2\,dt.
$$

### 0.3 乘法卷积与镜像算子

在 $(\mathbb R_+^\times,\frac{dx}{x})$ 上定义

$$
(f\ast g)(x):=\int_0^\infty f(y)\,g\!\left(\frac{x}{y}\right)\frac{dy}{y},\qquad
\mathcal M_a[f\ast g]=\mathcal M_a[f]\cdot\mathcal M_a[g].
$$

定义镜像算子

$$
(Jf)(x):=x^{-a}f(1/x).
$$

### 0.4 可采镜像核与条带 RKHS

称 $K$ 为**可采镜像核**，若满足：

$$
\begin{cases}
\text{(A1)}\ K\in \mathcal H_a\cap L^1_{\mathrm{loc}}(\mathbb R_+),\\[2pt]
\text{(A2)}\ K(x)=x^{-a}K(1/x)\quad(\text{自反}),\\[2pt]
\text{(A3)}\ \exists\ \text{含中心轴的开竖条 }\Sigma\ \text{，}\ \mathcal M_a[K]\ \text{在 }\Sigma\ \text{全纯，且在 }\Re s=\tfrac a2\ \text{几乎处处非零；}\\
\hphantom{\text{(A3)}}\ \text{使用 }\log|\mathcal M_a[K]|\ \text{的次调和性（对全纯函数自然成立），以引入竖条 }H^2\text{ 的 Poisson–Jensen 控制}\\
\hphantom{\text{(A3)}}\ \text{（此处仅作增长控制，不作内点零点排除的替代）；}\\[2pt]
\text{(A3′)}\ \Xi/\mathcal M_a[K]\in H^2(\Sigma)\text{；等价地，}\mathcal M_a[K]\ \text{在 }\Sigma\ \text{内部零点要么不存在，}\\
\hphantom{\text{(A3′)}}\ \text{要么 }\Xi\ \text{在这些点以不低于相同阶数消失（可去奇性）；}\\[2pt]
\text{(A4)}\ K\ \text{带限或指数衰减（与显式/迹公式核族一致）}.
\end{cases}
$$

为避免乘子有界性的额外假设，引入乘子加权条带空间

$$
\mathscr H_K:=\big\{\ \mathcal M_a[K]\cdot H\ :\ H\in H^2(\Sigma)\ \big\},\qquad
\langle \mathcal M_a[K]H_1,\ \mathcal M_a[K]H_2\rangle_{\mathscr H_K}:=\langle H_1,H_2\rangle_{H^2(\Sigma)}.
$$

$\mathscr H_K$ 为 $\Sigma$ 上的 RKHS，点值泛函一致有界。

---

## 1. 镜像与 Mellin 的酉对应

### 引理 14.1（酉性与镜像公式）

算子 $J:\mathcal H_a\to\mathcal H_a$ 酉且 $J^2=\mathrm{Id}$；并且

$$
\mathcal M_a[Jf](s)=\mathcal M_a[f](a-s).
$$

**证明。**
酉性：

$$
\langle Jf,Jg\rangle_a=\int_0^\infty\underbrace{x^{-2a}}_{\text{来自 }Jf,\ Jg}\,f(1/x)\,\overline{g(1/x)}\,x^{a-1}dx
=\int_0^\infty f(y)\overline{g(y)}\,y^{a-1}dy=\langle f,g\rangle_a.
$$

镜像：

$$
\mathcal M_a[Jf](s)=\int_0^\infty x^{-a}f(1/x)\,x^{s}\frac{dx}{x}
=\int_0^\infty f(y)\,y^{\,a-s}\frac{dy}{y}=\mathcal M_a[f](a-s).
$$

∎

**推论 14.2（功能方程的 Hilbert 表达）** 若 $JF=\varepsilon F$，则 $\mathcal M_a[F](a-s)=\varepsilon\,\mathcal M_a[F](s)$。

---

## 2. 镜像核的 RKHS 与完成函数的内积表示

定义

$$
T_K:\ \mathcal H_a\to \mathscr H_K,\qquad (T_KF)(s):=\mathcal M_a[K](s)\,\mathcal M_a[F](s).
$$

把 $T_K$ 定义在 $\mathrm{dom}(T_K):=\{F\in\mathcal H_a:\ \mathcal M_a[F]\in H^2(\Sigma)\}$ 上，则 $T_K$ 在此定义域内有界且 $T_KF\in\mathscr H_K$。为避免不必要的边界可积性讨论，以下均在 $\mathrm{dom}(T_K)$ 内工作；对更一般 $F$ 的 $L^2$ 边界乘子与 Poisson–Hardy 延拓仅作启发性说明，不在本文使用。记 $\mathscr H_K$ 的 reproducing kernel 为

$$
\mathbf K_{\mathscr H_K}(w,s)=\overline{\mathcal M_a[K](\bar w)}\,\mathcal M_a[K](s)\,\mathbf K_{H^2}(w,s),
$$

其中 $\mathbf K_{H^2}$ 为 $H^2(\Sigma)$ 的核。定义**点向量** $k_s\in\mathcal H_a$ 为 Riesz 表示向量，使得对所有 $F\in\mathrm{dom}(T_K)$ 有

$$
(T_KF)(s)=\langle F,k_s\rangle_a;
$$

在 $\mathrm{dom}(T_K)$ 稠密时亦可写作 $k_s=T_K^\ast\!\big(\mathbf K_{\mathscr H_K}(\cdot,s)\big)$。

### 定理 14.3（镜像对称）

对所有 $s\in\Sigma$，有

$$
k_{a-s}=Jk_s,\qquad (T_KJF)(s)=(T_KF)(a-s).
$$

**证明。** 由引理 14.1 与 (A2) 得 $\mathcal M_a[K](a-s)=\mathcal M_a[K](s)$。遂
$(T_KJF)(s)=\mathcal M_a[K](s)\mathcal M_a[Jf](s)=\mathcal M_a[K](s)\mathcal M_a[F](a-s)=(T_KF)(a-s)$。拉回至 $\mathcal H_a$ 得 $k_{a-s}=Jk_s$。∎

### 定理 14.4（完成函数的内积表示）

若完成函数 $\Xi$ 满足中心对称与 $\Re s=\tfrac a2$ 上的 $L^2$-边界增长，且 $\mathcal M_a[K](\tfrac a2+it)\neq0$（a.e.），则存在 $F\in\mathcal H_a$、常数 $C\neq0$ 使

$$
\Xi(s)=C\,\langle F,k_s\rangle_a,\qquad s\in\Sigma,
$$

并保持镜像 $\Xi(a-s)=\varepsilon\,\Xi(s)$。

**证明。** 令 $H(s):=\Xi(s)/\mathcal M_a[K](s)$。由 **(A3′)**（配合 $\Xi$ 在 $\Sigma$ 内解析）知 $H\in H^2(\Sigma)$。取 $F\in\mathcal H_a$ 使 $\mathcal M_a[F](\tfrac a2+it)=H(\tfrac a2+it)$（由 Plancherel–Mellin 存在且唯一）。按定义 $T_KF(s)=\mathcal M_a[K](s)\,H(s)\equiv \Xi(s)$（在 $\Sigma$ 内成立）。常数 $C$ 可由归一化自由选择。镜像由定理 14.3 传递。∎

---

## 3. Beurling–Nyman 子空间与最小能量投影

### 3.1 字典与 BN 子空间

取与 $K$ 相容、偶且带限/指数衰减的窗 $\psi$，并令 $\mathcal M_a[\psi](\tfrac a2)=0$（去 DC）。定义

$$
\phi_n(x):=\psi(nx),\qquad n\in\mathcal N\subset\mathbb N,\qquad
\mathcal M_a[\phi_n](s)=n^{-s}\,\mathcal M_a[\psi](s).
$$

由此生成

$$
\mathscr B:=\overline{\mathrm{span}}\{\phi_n:\ n\in\mathcal N\}\subset\mathcal H_a.
$$

### 3.2 最小能量 mollifier 与正交投影

给定 $s_0\in\Sigma$。称 $M^\star\in\mathscr B$ 为**最小能量 mollifier**（即满足 $\langle M,k_{s_0}\rangle_a=1$ 的最小范数元），若

$$
\langle M^\star,k_{s_0}\rangle_a=1,\qquad
|M^\star|_a=\min\{|M|_a:\ M\in\mathscr B,\ \langle M,k_{s_0}\rangle_a=1\}.
$$

记 $P_{\mathscr B}$ 为 $\mathcal H_a\to\mathscr B$ 的正交投影，则

$$
M^\star=\frac{P_{\mathscr B}k_{s_0}}{|P_{\mathscr B}k_{s_0}|_a^{\,2}},\qquad
|M^\star|_a^{\,2}=\frac{1}{|P_{\mathscr B}k_{s_0}|_a^{\,2}}.
$$

**谱（有限字典）形式。** 若 $\{\phi_{n_j}\}_{j=1}^m$ 有限，Gram 算子 $G=(\langle \phi_{n_i},\phi_{n_j}\rangle_a)$ 厄米正定，$c=(\langle \phi_{n_j},k_{s_0}\rangle_a)_j$，则

$$
M^\star=\sum_{j=1}^m \beta_j^\star\,\phi_{n_j},\qquad
\beta^\star=\frac{G^{-1}c}{c^\ast G^{-1}c},\qquad
|M^\star|_a^{\,2}=\frac{1}{c^\ast G^{-1}c}.
$$

**可行性（非退化）说明。** 为保证约束可行，需 $\mathcal M_a[\psi](s_0)\neq 0$。若采用 $\mathcal M_a[\psi](\tfrac a2)=0$ 去 DC，则应取 $s_0\neq\tfrac a2$，或在字典中加入一枚不消 DC 的向量专用于约束。同时需要求 $\mathcal M_a[K](s_0)\neq 0$，因为 $c_j=\langle\phi_{n_j},k_{s_0}\rangle_a=(T_K\phi_{n_j})(s_0)$ 包含因子 $\mathcal M_a[K](s_0)$。采用 §7 的对称化 $\mathcal M_a[K](s)=\big(r(s)r(a-s)\big)^{1/2}$ 时，在临界条带内该条件自然满足。

---

## 4. 投影误差的**信息—变分**等价

### 4.1 软最大势与 Bregman–KL 恒等式

取权 $w_j>0$、特征 $\beta_j\in\mathbb R^d$，定义

$$
\Lambda(\rho):=\log\sum_j w_j\,e^{\langle \beta_j,\rho\rangle},\qquad
p_j(\rho):=\frac{w_j\,e^{\langle \beta_j,\rho\rangle}}{\sum_\ell w_\ell\,e^{\langle \beta_\ell,\rho\rangle}}.
$$

则

$$
B_\Lambda(\rho'\mid\rho)=\Lambda(\rho')-\Lambda(\rho)-\langle\nabla\Lambda(\rho),\rho'-\rho\rangle
= D\!\big(p(\rho)\,\|\,p(\rho')\big).
$$

### 4.2 信息—几何对齐（IG-Align）与等价定理

假设存在参数嵌入 $\rho\mapsto c(\rho)\in\mathbb C^m$ 与字典归一，使在所选 $s_0$ 下

$$
\text{(A5)}\quad c_j(\rho)=\langle \phi_{n_j},k_{s_0}\rangle_a=\gamma\,w_j\,e^{\langle \beta_j,\rho\rangle}\ (\gamma\neq0),\qquad
\text{(A6)}\quad G_{ij}=g(\beta_i,\beta_j)\ \text{为信息核，使 }b^\ast G b=\mathrm{Var}_\pi\!\Big(\sum_j b_j\beta_j\Big),
$$

其中 $\pi\propto (w_j)$ 为基准权的概率化。（该对齐为**假设**，在"窗—频谱字典与母映射同源"的设置中自然成立。）

在本文所用 dilate 字典 $\phi_n(x)=\psi(nx)$ 下，$\langle\phi_n,k_{s_0}\rangle_a=\mathcal M_a[K](s_0)\,\mathcal M_a[\psi](s_0)\,e^{-\langle(\log n),s_0\rangle}$。令 $\beta_n:=-\log n$、取 $w_n>0$ 吸收常数因子，则 (A5) 具体化为 $c_n(\rho)=\gamma\,w_n\,e^{\langle\beta_n,\rho\rangle}$（可取 $\rho=\Re s_0$；若需考虑相位，则把 $\rho$ 扩展为二维向量 $(\Re s_0,\Im s_0)$）。由此 $u_0:=\nabla\Lambda(\rho^\star)$ 为对偶解 $\rho^\star$ 的软最大势梯度（期望充分统计），并用于右侧矩约束 $\mathbb E_q[\beta]=u_0$。

### 定理 14.6（BN 最小能量 $\Longleftrightarrow$ 最小 KL）

在 (A5)–(A6) 下，

$$
\min_{M\in\mathscr B}\ |M|_a^2\ \text{\rm s.t.}\ \langle M,k_{s_0}\rangle_a=1
\quad\Longleftrightarrow\quad
\min_{q\in\Delta}\ D(q\,\|\,\pi)\ \text{\rm s.t.}\ \mathbb E_q[\beta]=u_0,
$$

两侧极小值相等，极小解在 Fenchel–Legendre 对偶下互相对应，其中 $u_0$ 为约束矩条件，$\Delta$ 为概率单纯形。约束矩 $u_0$ 需落在 $\mathrm{ri}\,\mathrm{conv}\{\beta_j\}$（或其闭包）内，以保证右侧 $\inf_{q:\ \mathbb E_q[\beta]=u_0}D(q\,\|\,\pi)$ 的可行性与 Fenchel–Legendre 对偶无间隙；无限字典时以闭包/下极限理解。

**证明。** 有限字典时

$$
\inf_{b:\ \langle c,b\rangle=1} b^\ast G b=\frac{1}{c^\ast G^{-1}c}.
$$

由 (A5) 将 $c$ 写成指数族的充分统计，再由 (A6) 将 $b^\ast G b$ 重写为 $\Lambda$ 的共轭泛函，得到

$$
\inf_{b:\ \langle c,b\rangle=1} b^\ast G b
=\sup_{\rho}\big\{\langle u_0,\rho\rangle-\Lambda(\rho)\big\}
=\inf_{q:\ \mathbb E_q[\beta]=u_0} D(q\,\|\,\pi),
$$

其中右端等号是最大熵原理与 KL 的拉格朗日表示。∎

**推论 14.7（误差 = 信息代价）** 取 $\rho^\star$ 使 $\nabla\Lambda(\rho^\star)=u_0$，并以 $\rho_{\mathrm{ref}}$ 使 $\pi=p(\rho_{\mathrm{ref}})$（典型地 $\rho_{\mathrm{ref}}=0$）。则

$$
\boxed{\ |M^\star|_a^2=\frac{1}{|P_{\mathscr B}k_{s_0}|_a^2}
=\min_{q:\ \mathbb E_q[\beta]=u_0} D(q\,\|\,\pi)
=B_\Lambda\big(\rho^\star\ \big|\ \rho_{\mathrm{ref}}\big)\ }.
$$

---

## 5. 有限阶 EM 与"极点 = 主尺度"

### 定理 14.8（卷积与 EM 校正不改变奇性集合）

在 S4 的**有限阶** EM 与 S5 的方向亚纯化前提下：

(i) 用带限/指数核 $K$ 对 $F$ 作卷积/窗化，仅在 $s$ 上叠加整/全纯层，不引入新极点；若 $\mathcal M_a[K]$ 在极点处消零，则至多降低（含消除）该极点的阶，因此新极点集合包含于原集合。

(ii) $\mathcal M_a[K]$ 在 $\Sigma$ 全纯，作为乘子不会引入极点；其零点至多导致"乘以零"，不引入新极点；若 $\mathcal M_a[K]$ 在极点处消零，则至多降低（含消除）该极点的阶，因此新极点集合包含于原集合。有限阶 EM 的伯努利层与端点余项在参数上全纯/整，故 BN 投影与 RKHS 表示的解析结构保持不变。

**证明要点。** 乘子为全纯函数时，乘积的极点由被乘函数决定；有限阶 EM 的余项为受控 Stieltjes 型积分，对参数全纯。

上述"对参数全纯/整"均指对复变量 $s$ 的性质，且以固定有限阶 EM（不令阶数随 $s$ 变动）与端点正则条件为前提；条带 $\Sigma$ 的选取需避开 EM 端点参数潜在的离散奇性。∎

---

## 6. 与显式/迹公式核的一致性与增长控制

* **核—窗一致**：取 $K,\psi$ 属于显式公式（Weil 型）与 Selberg/Kuznetsov 的可检核族（偶、光滑、带限或指数衰减），则谱侧（零点/本征模）与几何侧（素数/闭测地/Kloosterman）和 Hilbert 侧窗形一致，误差常数可统一记账。
* **增长控制**：$\Gamma/\pi$ 正规化提供垂线指数衰减，S10 的方向支持函数上界控制向量增长；据此 $|k_s|_a$ 与 $\mathbf K_{\mathscr H_K}(s,s)$ 在 $\Sigma$ 内一致可控，点值与投影稳定。

---

## 7. 典型实例

### 7.1 Riemann $\xi$（$a=1$）

取 $r(s)=\pi^{-s/2}\Gamma(\tfrac s2)$，令 $\mathcal M_a[K](s)=\big(r(s)\,r(1-s)\big)^{1/2}$（在所选竖条 $\Sigma$ 内取连续外因子分支），于是 $\mathcal M_a[K](1-s)=\mathcal M_a[K](s)$ 成立。相应地

$$
\mathcal M_a[F](s)=\frac{\xi(s)}{\mathcal M_a[K](s)}=\Big(\frac{r(s)}{r(1-s)}\Big)^{1/2}\zeta(s),
$$

从而

$$
\xi(s)=\mathcal M_a[K](s)\,\mathcal M_a[F](s)=\langle F,k_s\rangle_1,\qquad k_{1-s}=Jk_s,
$$

并以 dilate 字典 $\{\psi(nx)\}$ 构造 $\mathscr B$，得到最小能量—KL 等价。

### 7.2 Dirichlet $L(\chi,\cdot)$（$a=1$）

就奇偶性选 $\Gamma_{\mathbb R}$ 因子 $r_\chi$，令 $\mathcal M_a[K_\chi](s)=\big(r_\chi(s)\,r_\chi(1-s)\big)^{1/2}$（在所选竖条 $\Sigma$ 内取连续外因子分支），于是 $\mathcal M_a[K_\chi](1-s)=\mathcal M_a[K_\chi](s)$ 成立。相应地

$$
\mathcal M_a[F_\chi](s)=\frac{\Xi_\chi(s)}{\mathcal M_a[K_\chi](s)}=\Big(\frac{r_\chi(s)}{r_\chi(1-s)}\Big)^{1/2}L(\chi,s),
$$

从而

$$
\Xi_\chi(s)=\mathcal M_a[K_\chi](s)\,\mathcal M_a[F_\chi](s)=\langle F_\chi,k^{(\chi)}_s\rangle_1,\qquad k^{(\chi)}_{1-s}=Jk^{(\chi)}_s,
$$

并在 BN–信息框架下获得同样等价。

### 7.3 自守形式的度 $2$

令 $\Xi_f(s)=Q_f^{s/2}\,r_f(s)\,L(f,s)$，其中 $r_f(s)$ 为标准阿基米德因子：
• 若 $f$ 为权 $k$ 的全纯新形式，则 $r_f(s)=(2\pi)^{-(s+\frac{k-1}{2})}\Gamma\!\big(s+\tfrac{k-1}{2}\big)$；
• 若 $f$ 为权 $0$ 的 Maaß 形式（谱参 $t$），则 $r_f(s)=\pi^{-s}\Gamma\!\big(\tfrac{s+it}{2}\big)\Gamma\!\big(\tfrac{s-it}{2}\big)$。
在本文框架中令 $\mathcal M_a[K_f](s)=\big(r_f(s)\,r_f(a-s)\big)^{1/2}$（在所选竖条 $\Sigma$ 内取连续外因子分支），于是 $\mathcal M_a[K_f](a-s)=\mathcal M_a[K_f](s)$ 成立。相应地

$$
\mathcal M_a[F_f](s)=\frac{\Xi_f(s)}{\mathcal M_a[K_f](s)}=\Big(\frac{r_f(s)}{r_f(a-s)}\Big)^{1/2}Q_f^{s/2}\,L(f,s),
$$

从而 $\Xi_f(s)=\mathcal M_a[K_f](s)\,\mathcal M_a[F_f](s)=\langle F_f,k^{(f)}_s\rangle_a$，镜像对称 $k^{(f)}_{a-s}=Jk^{(f)}_s$ 保持。与 Kuznetsov 核—窗一致的 $\mathscr B_f$ 给出投影—信息等价与增长控制。

---

## 8. 边界与反例

* **核不自反**：若 $K(x)\neq x^{-a}K(1/x)$，则 $k_{a-s}\neq Jk_s$，镜像失配；可对称化 $K\leftarrow \tfrac12\big(K+x^{-a}K(1/x)\big)$。
* **窗衰减不足**：若核/窗不带限且衰减不足，$\mathcal M_a[K]$ 的内部性质与点值有界性可能失效；应回到显式/迹公式核族。
* **EM 级数滥用**：把 EM 误作无穷级将引入伪奇性与非法换序；须固定有限阶并核查端点正则。
* **方向退化**：若大量谱点沿某方向同速聚集，$|k_s|_a$ 条件数恶化；需更换方向或采用多方向层析。

---

## 9. 可检清单（最小充分条件）

1. **完成函数模板**：给出 $(Q,a,r)$，验证 $\Xi(a-s)=\varepsilon\Xi(s)$。
2. **镜像 Hilbert 空间**：$\mathcal H_a=L^2(\mathbb R_+;x^{a-1}dx)$，$Jf=x^{-a}f(1/x)$ 酉；Plancherel–Mellin 于 $\Re s=\tfrac a2$ 成立。
3. **可采镜像核**：$K$ 满足 **(A1)–(A4) 与 (A3′)**，$\mathcal M_a[K]$ 在中心轴 a.e. 非零。
4. **RKHS 表示**：定义 $T_K$、$\mathscr H_K$ 与 $k_s=T_K^\ast\mathbf K_{\mathscr H_K}(\cdot,s)$；验证 $k_{a-s}=Jk_s$。
5. **BN 子空间**：以与显式/迹公式一致的窗 $\psi$ 生成 $\mathscr B$；构造 Gram 算子与 $M^\star$。
6. **信息对偶**：在 IG-Align（A5–A6）下建立 $|M^\star|_a^2=\min D(q|\pi)$。
7. **解析纪律**：仅用**有限阶** EM；确认卷积/窗与 EM 校正不改变奇性集合。
8. **增长与稳定**：与 $\Gamma/\pi$ 正规化、方向支持函数上界一致，确保点值与投影稳定。
9. **可行性检查**：选取 $s_0$ 与字典使 $\mathcal M_a[\psi](s_0)\neq0$（若去 DC，则 $s_0\neq\tfrac a2$ 或加入不消 DC 的约束向量）。

---

## 10. 与既有篇章的接口

- ↔ S3（完成函数与镜像）：本篇用酉算子 $J$ 实现 $s\mapsto a-s$ 的镜像，与完成函数模板完全一致；$\Gamma/\pi$ 正规化与中心轴 $a$ 的对称在条带与核选择中一致化。
- ↔ S6（信息刻度）：BN 最小能量投影与 KL/Bregman 的熵极小在自然度量（由 $\Lambda$ 的 Hessian 诱导）下等价，提供“误差=信息代价”的解释。
- ↔ S7（$L$-函数接口）：degree/conductor 通过 $(Q,a,r)$ 归入 $\mathcal M_a[K]$，对偶侧通过 $(L^\ast,r^\ast)$ 进入镜像核；与完成功能方程保持一致。
- ↔ S8（Nyquist–Poisson–EM）：带限/指数窗使 $\mathscr B$ 的有限字典可离散化；Nyquist 采样与有限阶 EM 控制别名与端点，保持“极点 = 主尺度”。
- ↔ S10（Amoeba 几何与增长）：支持函数上包与 Ronkin 凸性为窗方向与条带选择给出增长与稳定度量；与信息势几何对齐。
- ↔ S11（迹公式接口）：选用与显式/迹公式一致的核/窗（$\mathcal C,\mathcal B^{\pm}$）可将谱—几何两端与 Hilbert 侧 RKHS/BN 框架统一到同一变分视角。
- ↔ S12（AFE/放大器）：$\mathcal M_a[K]$ 与软窗 AFE 的核一致；谱形式 $G^{-1}c$ 与广义本征放大互补，支持“谱—Hilbert”双轨实现。

---

## 11. 结语

本文在带权 Mellin–Hilbert 空间中把中心对称实现为酉镜像算子 $J$，以自反核 $K$ 构造 RKHS 并获得完成函数的内积评估且保持镜像；在与显式/迹公式一致的窗—字典下，最小能量 BN 投影的 Hilbert 极小化与软最大势的 Fenchel 对偶**等价**，从而把**投影误差**识别为**KL/Bregman 信息代价**。在**有限阶** EM 与方向亚纯化约束下，"极点 = 主尺度"始终成立。该 Hilbert 界面为零密度（S15）、软窗矩与共振器极值（S16）、多方向层析（S17）等提供统一而可检的基础。
