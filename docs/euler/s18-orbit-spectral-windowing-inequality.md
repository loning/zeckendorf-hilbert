# S18. 轨道—谱窗化不等式

—— 迹公式的分布恒等式、镜像—规范系统接口与三分解误差

**作者**：Auric
**日期**：2025-10-21

---

## 摘要（定性）

在 Weyl–Heisenberg 酉体系（Mellin 侧"平移—权乘"表示）、de Branges–Krein 规范系统（传递矩阵与谱测度）与"功能方程 ↔ 散射算子酉/对称"的统一框架下，本文把抽象迹公式（轨道—谱对偶的分布恒等式）组织为**窗化不等式**。对任一满足带限或指数衰减的偶窗与可检试验核，在仅使用**有限阶** Euler–Maclaurin（EM）换序的前提下，轨道侧与谱侧在同一工作条带具有**相同奇性集合且阶不升**。在实际计算的**数值实现**中，两侧差异由一条**非渐近**的"**别名 + 伯努利层 + 截断**"三分解上界统一控制；当被采样的核满足带限并取 Nyquist 步长时，可将相应侧的别名项消除。连续谱项借助散射矩阵实轴酉性与镜像对称而正性可控；方向增长由指数—多项式的支持函数上包。全文保持纯数学体例。

---

## 0. 设定、记号与基本假设

### 0.1 Fourier 规范与卷积

固定

$$
\widehat f(\xi)=\int_{\mathbb R} f(x)\,e^{-i x \xi}\,dx,\qquad
f(x)=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\xi)\,e^{i x \xi}\,d\xi .
$$

则

$$
\widehat{f*g}=\widehat f\cdot\widehat g,\qquad
\widehat{fg}=\frac{1}{2\pi}\,\widehat f*\widehat g .
$$

对缩放 $w_R(x):=w(x/R)$ 有 $\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$。

### 0.2 试验核与窗：最小充分正则

记 $h:\mathbb R\to\mathbb C$ 为偶函数，满足

$$
\boxed{\ h\in W^{2M,1}(\mathbb R)\ \text{且}\ \widehat h\in L^1\ }
$$

（即 $h^{(j)}\in L^1$ 对所有 $0\le j\le 2M$ 成立）。窗 $w$ 亦取偶，并满足以下二选一的最小充分条件：

* **带限窗**：$\widehat w$ 紧支于 $[-\Omega,\Omega]$，且

$$
\widehat w\in L^1(\mathbb R)\cap C^{2M}(\mathbb R) .
$$

于是 $w\in L^\infty\cap C^{2M}$，并且对所有 $k\le 2M$ 有

$$
\|w_R^{(k)}\|_{L^\infty}
=R^{-k}\|w^{(k)}\|_{L^\infty}
\le \frac{R^{-k}}{2\pi}\int_{-\Omega}^{\Omega}|(i\xi)^k\widehat w(\xi)|\,d\xi<\infty.
$$

由 Leibniz 法则与 $h\in W^{2M,1}$、$w_R^{(k)}\in L^\infty$，得谱侧 $g_1:=h\cdot w_R$ 满足 $g_1^{(2M)}\in L^1$；轨道侧卷积核 $g_2:=\widehat h*\widehat w_R$ 可积且具所需平滑度。

* **指数窗**：存在 $\kappa'>0$ 使

$$
w\in C^{2M}(\mathbb R),\qquad
\boxed{\ \sup_{t\in\mathbb R}e^{\kappa'|t|}|w^{(k)}(t)|<\infty\quad(0\le k\le 2M)\ },
$$

从而 $w_R^{(k)}\in L^\infty$ 对所有 $0\le k\le 2M$ 成立，结合 $h\in W^{2M,1}$ 即得 $g_1^{(2M)}\in L^1$。

> **注**：对 $g_2=\widehat h*\widehat w_R$，由 $\widehat{g_2}(\xi)=(2\pi)^2 h(-\xi)w_R(-\xi)$ 知当 $\int_{\mathbb R}(1+|\xi|)^{2M}|h(\xi)|\,d\xi<\infty$ 且 $w_R\in L^\infty$ 时可保证 $(1+|\xi|)^{2M}\widehat{g_2}\in L^1$，从而 $g_2^{(2M)}\in C_0\cap L^\infty$；此为足够条件（非必要）。实践中对轨道和的离散求和无需应用 EM 层，故无需强制 $g_2^{(2M)}\in L^1$。

### 0.3 抽象迹公式（分布恒等式）

存在谱参数（离散 $\{z_j\}\subset\mathbb R\cup i\mathbb R$ 与连续部分 $\mu$）以及几何轨道数据 $\{\gamma\}$（长度 $\ell_\gamma>0$、权 $A_\gamma$），对所有可检 $h$ 成立

$$
\boxed{\;
\sum_{j} h(z_j)+\int_{\mathbb R} h(x)\,d\mu(x)
= I_0[h]+\sum_{\gamma\ne e} A_\gamma\,\widehat h(\ell_\gamma)\,.
\;}
\tag{TF}
$$

本文仅使用 (TF) 的**线性**结构与可检核类的闭合性，不涉及具体问题中的谱—几何细节。

**约定（Lebesgue 主项）**：假设几何主项具 Lebesgue 表示 $I_0[h]=\int_{\mathbb R} h(x)\,\phi_0(x)\,dx$，其中 $\phi_0\in L^1\cap L^\infty$ 为密度函数。下文统一按 §0.4 之绝对连续约定使用 $\mu$。

### 0.4 规范系统、谱测度与镜像接口（记号约定）

令完成函数 $E(z):=\Xi(\tfrac a2+iz)$。存在一阶辛型 de Branges–Krein 规范系统

$$
\mathbf J Y'(t)=z\,H(t)\,Y(t),\qquad
\mathbf J=\begin{pmatrix}0&-1\\[1pt]1&0\end{pmatrix},\quad H(t)=H(t)^{\!\top}\succeq0,
$$

其 Weyl–Titchmarsh 函数 $m(z)$ 为 Herglotz 函数。本文在全篇统一约定

$$
\boxed{\ d\mu(x)=\rho(x)\,dx,\qquad \rho(x)=\frac1\pi\,\Im m(x+i0)\ge 0\ \text{(a.e.)},\ }
$$

即 $\mu$ 仅表示**连续谱的绝对连续部分**；纯点谱一律并入 $\{z_j\}$。

### 0.5 有限阶 EM 纪律与方向增长

本文**仅使用有限阶** EM；伯努利层与端点余项在复参上整或全纯，从而不引入新奇点。轨道长度或指数权的方向增长以支持函数上包，保证窗化卷积绝对收敛。

---

## 1. 窗化迹式：精确恒等与数值实现

设谱窗 $w_R(x):=w(x/R)$ 与轨道窗 $\widehat w_R(\ell):=R\,\widehat w(R\ell)$。

### 1.1 精确窗化迹式

$$
\mathcal S_{\mathrm{spec}}(h;R)
:=\sum_j h(z_j)\,w_R(z_j)+\int_{\mathbb R} h(x)\,w_R(x)\,d\mu(x),
$$

$$
\mathcal S_{\mathrm{geo}}(h;R)
:= I_0[h\cdot w_R]+\frac{1}{2\pi}\sum_{\gamma\ne e} A_\gamma\,\bigl(\widehat h*\widehat w_R\bigr)(\ell_\gamma).
$$

由 (TF) 作用于 $h\cdot w_R$ 并用 $\widehat{h\,w_R}=\frac{1}{2\pi}\widehat h*\widehat w_R$ 得

$$
\boxed{\ \mathcal S_{\mathrm{spec}}(h;R)=\mathcal S_{\mathrm{geo}}(h;R)\ }\quad\text{（分布意义下精确）}.
\tag{1.1-exact}
$$

### 1.2 数值实现与"误差三分解"

在实际计算中，对 **Lebesgue 型积分**（谱侧连续谱项与几何侧 $I_0[\cdot]$）以步长 $\Delta>0$ 的采样和（在半径 $T>0$ 内截断）替代。记

$$
S_T(g;\Delta):=\Delta\sum_{|k|\le \lfloor T/\Delta\rfloor} g(k\Delta).
$$

由此得到数值实现的泛函 $\mathcal S_{\mathrm{spec}}^{\Delta,M,T}(h;R)$ 与 $\mathcal S_{\mathrm{geo}}^{\Delta,M,T}(h;R)$。记 $g_1:=h\cdot w_R$，定义**被采样的 integrand**：

$$
g_{\mathrm{spec}}:=g_1\cdot\rho,\qquad
g_0:=g_1\cdot\phi_0,
$$

其中 $\rho$ 为 §0.4 的谱密度、$\phi_0$ 为 §0.3 的几何主项密度。则：

* **谱侧**：纯点求和 $\sum_j h(z_j)w_R(z_j)$ 保持精确；连续谱 $\int h\,w_R\,d\mu=\int g_{\mathrm{spec}}(x)\,dx$ 以 $g_{\mathrm{spec}}$ 为核应用 $S_T(\cdot;\Delta)$；
* **几何侧**：$I_0[h\cdot w_R]=\int g_0(x)\,dx$ 以 $g_0$ 为核应用 $S_T(\cdot;\Delta)$；轨道和项 $\sum_{\gamma\ne e}A_\gamma(\widehat h*\widehat w_R)(\ell_\gamma)$ 作为对**离散测度** $\nu_{\mathrm{orb}}=\sum_\gamma A_\gamma\delta_{\ell_\gamma}$ 的积分**保持精确**（或按轨道计数函数给出显式截断，见 §3.4）。若按长度截断，误差优先用**采样无关**的 $\mathcal E_{\mathrm{orb}}(T)$（§3.4）控制；该项与 $\Delta,M$ 无耦合。

误差的非渐近三分解（术语对照：**别名 + 伯努利层 + 截断** $\equiv$ **Nyquist–Poisson–EM 三分解**）见第 3 节。

---

## 2. 连续谱的正性与镜像对称

若 $h\ge0$、$w_R\ge0$，由 §0.4 的约定与 Herglotz 表示得

$$
\int_{\mathbb R} h(x)\,w_R(x)\,d\mu(x)
=\frac1\pi\int_{\mathbb R} h(x)\,w_R(x)\,\Im m(x+i0)\,dx\ \ge 0.
\tag{2.1}
$$

只要 $h,w_R\ge0$ 且 $\rho=(1/\pi)\Im m(x+i0)\ge0$，即得 (2.1) 的非负性；镜像/相位不影响该结论。

---

## 3. 三分解误差：别名、伯努利层与截断

记

$$
I(g):=\int_{\mathbb R} g(u)\,du,\qquad
S_\infty(g;\Delta):=\Delta\sum_{k\in\mathbb Z} g(k\Delta),\qquad
S_T(g;\Delta):=\Delta\sum_{|k|\le \lfloor T/\Delta\rfloor} g(k\Delta).
$$

### 3.1 Poisson 求和与绝对值上界

在 §0.1 的规范下，

$$
\Delta\sum_{k\in\mathbb Z}g(k\Delta)
=\sum_{m\in\mathbb Z}\widehat g\!\left(\frac{2\pi m}{\Delta}\right)
$$

（等式在 $\mathcal S$ 或满足 Poisson 条件时成立；本文实际只用到**不等式**版，详见附录 A.1 注记），故

$$
I(g)-S_\infty(g;\Delta)
=\widehat g(0)-\sum_{m\in\mathbb Z}\widehat g\!\left(\frac{2\pi m}{\Delta}\right)
=-\sum_{m\ne0}\widehat g\!\left(\frac{2\pi m}{\Delta}\right),
$$

从而

$$
\bigl|I(g)-S_\infty(g;\Delta)\bigr|
\le \sum_{m\ne0}\left|\widehat g\!\left(\frac{2\pi m}{\Delta}\right)\right|.
\tag{3.1a}
$$

若 $\widehat g\subset[-\Omega,\Omega]$ 且 $\Delta<2\pi/\Omega$，则右端为零；在临界 $\Delta=2\pi/\Omega$ 时若 $\widehat g$ 在 $\pm\Omega$ 取零，亦得零别名。

### 3.2 有限阶 EM 层与截断

**使用条件**：以下界式在 $g\in C^{2M}$ 且 $g^{(2M)}\in L^1(\mathbb R)$（并按 §A.2 处理端点项）时成立。**仅当 $g^{(2M)}\in L^1$ 时使用有限阶 EM；否则不使用 EM 层**（可视作形式上 $M=0$），此时仅采用"别名+尾项"的两项上界。

定义**采样尾和**（对任意可积 $g$ 总成立）：

$$
\mathcal{T}_\Delta(g;T):=\Delta\sum_{|k|>\lfloor T/\Delta\rfloor}|g(k\Delta)|.
$$

若 $|g|$ 在外侧单调/BV/$W^{1,1}$，则采样尾和还可以内侧积分上包：$\mathcal{T}_\Delta(g;T)\le \int_{|u|>T-\Delta}|g(u)|\,du$。

以有限阶 EM 对 $S_\infty-S_T$ 的尾和作估计，有

$$
\boxed{\
\bigl|S_\infty(g;\Delta)-S_T(g;\Delta)\bigr|
\le \sum_{j=1}^{M-1}\frac{|B_{2j}|}{(2j)!}\,\Delta^{2j}\,\bigl|g^{(2j)}\bigr|_{L^1}
+\underbrace{C_M\,\Delta^{2M}\,\bigl|g^{(2M)}\bigr|_{L^1}}_{\text{EM 余项}}
+\mathcal{T}_\Delta(g;T),\quad C_M=\frac{2\,\zeta(2M)}{(2\pi)^{2M}}.}
\tag{3.1b}
$$

### 3.3 统一的非渐近上界

在满足 §3.2 的使用条件时，综合 (3.1a)–(3.1b) 有

$$
\boxed{\
\Bigl|I(g)-S_T(g;\Delta)\Bigr|
\le
\underbrace{\sum_{m\ne0}\left|\widehat g\!\left(\frac{2\pi m}{\Delta}\right)\right|}_{\mathrm{alias}}
+\underbrace{\sum_{j=1}^{M-1}\frac{|B_{2j}|}{(2j)!}\,\Delta^{2j}\,|g^{(2j)}|_{L^1}\ +\ C_M\,\Delta^{2M}\,|g^{(2M)}|_{L^1}}_{\mathrm{EM\ layer\ (含余项)}}
+\underbrace{\mathcal{T}_\Delta(g;T)}_{\mathrm{tail}} .
}\tag{3.1}
$$

若不满足 §3.2 的 EM 使用条件，则不使用 EM 层（形式上 $M=0$），此时仅用"别名 + $\mathcal{T}_\Delta$"两项。

> **注（Nyquist 常数规范）**：上式采用角频率 Fourier 规范 $\widehat g(\xi)=\int g(x)e^{-ix\xi}dx$，别名频率为 $2\pi m/\Delta$。零别名条件 $\mathrm{supp}(\widehat g)\subset[-\Omega,\Omega]$ 在 $2\pi/\Delta>\Omega$ 时成立（即 $\Delta<2\pi/\Omega$）；临界 $\Delta=2\pi/\Omega$ 时需边界取零。与普通频率规范 $\check g(f)=\int g(x)e^{-2\pi i xf}dx$ 的关系为 $\widehat g(\xi)=\check g(\xi/(2\pi))$，因而零别名阈值对应 $\Delta<1/B$（$B=\Omega/2\pi$），区别于 Shannon 的 $\Delta\le 1/(2B)$。此处只需 Poisson 求和中非零谐波的采样点落在带宽外（从而 $\widehat g(2\pi m/\Delta)=0$ 对 $m\ne0$），比"从样本重构 $g$"的 Shannon 条件更弱，故阈值不同。

### 3.4 轨道和截断误差

对几何侧轨道和项 $\sum_{\gamma\ne e}A_\gamma(\widehat h*\widehat w_R)(\ell_\gamma)$（离散测度 $\nu_{\mathrm{orb}}$），若需按长度截断，定义**加权计数函数**

$$
N_A(\ell):=\sum_{\ell_\gamma\le\ell}|A_\gamma|,
$$

则

$$
\mathcal E_{\mathrm{orb}}(T)
:=\left|\sum_{\ell_\gamma>T}A_\gamma(\widehat h*\widehat w_R)(\ell_\gamma)\right|
\le \sup_{\ell>T}\bigl|(\widehat h*\widehat w_R)(\ell)\bigr|\cdot \int_{T}^{\infty}|dN_A(\ell)|
=\sup_{\ell>T}\bigl|(\widehat h*\widehat w_R)(\ell)\bigr|\cdot\sum_{\ell_\gamma>T}|A_\gamma|.
$$

当 $\widehat h,\widehat w_R\in L^1$ 且轨道权满足 $\sum_\gamma|A_\gamma|<\infty$ 时，$\mathcal E_{\mathrm{orb}}(T)\to0$（$T\to\infty$）。在实践中若轨道数目有限或衰减充分快，可取 $\mathcal E_{\mathrm{orb}}=0$（保持精确）。

---

## 4. 窗化不等式与奇性保持

### 定理 18.1（数值窗化迹不等式：一般窗）

对 §0 假设与任意 $R>0$，按 §1.2 的数值约定（Lebesgue 型积分以采样和替代、轨道和保持精确或显式截断），有

$$
\boxed{\
\bigl|\mathcal S_{\mathrm{spec}}^{\Delta,M,T}(h;R)-\mathcal S_{\mathrm{geo}}^{\Delta,M,T}(h;R)\bigr|
\le \mathfrak E(g_{\mathrm{spec}};\Delta,M,T)+\mathfrak E(g_0;\Delta,M,T)+\mathcal E_{\mathrm{orb}}(T),
}\tag{4.1}
$$

其中 $g_{\mathrm{spec}}=g_1\cdot\rho$、$g_0=g_1\cdot\phi_0$（$g_1=h\cdot w_R$）为 §1.2 定义的**被采样 integrand**。下述 $\mathfrak E$ 取含 EM 或无 EM 版本，分别对应 §3.2 的两种正则情形；尾项统一记为采样尾和 $\mathcal{T}_\Delta$（在 $|g|$ 外侧单调/BV/$W^{1,1}$ 时可再以内侧积分尾界上包）。

$$
\boxed{\
\mathfrak E(g;\Delta,M,T)
=\sum_{m\ne0}\left|\widehat g\!\left(\frac{2\pi m}{\Delta}\right)\right|
+\sum_{j=1}^{M-1}\frac{|B_{2j}|}{(2j)!}\,\Delta^{2j}\,|g^{(2j)}|_{L^1}
+\ C_M\,\Delta^{2M}\,|g^{(2M)}|_{L^1}
+\mathcal{T}_\Delta(g;T),\quad C_M=\frac{2\,\zeta(2M)}{(2\pi)^{2M}},}
$$

并且 $\mathcal E_{\mathrm{orb}}(T)$ 为轨道和截断误差（若保持精确则取零；若按长度 $T$ 截断，则由 §3.4 给出上界）。

### 定理 18.2（Nyquist 锐化：被采样 integrand 带限时消去别名）

令

$$
\mathrm{bw}(\phi):=\sup\{|\xi|:\ \phi(\xi)\ne0\}.
$$

若 $\widehat{g_{\mathrm{spec}}}$ 和 $\widehat{g_0}$ 紧支（例如当 $\widehat h$、$\widehat w$、$\widehat\rho$、$\widehat\phi_0$ 均紧支时由卷积封闭性成立），记

$$
\Omega_{\mathrm{spec}}:=\mathrm{bw}(\widehat{g_{\mathrm{spec}}}),\qquad
\Omega_0:=\mathrm{bw}(\widehat{g_0}),
$$

取步长

$$
\Delta\le \frac{2\pi}{\max\{\Omega_{\mathrm{spec}},\Omega_0\}}
\quad\text{（临界时要求边界取零）},
$$

则 $\mathrm{alias}(g_{\mathrm{spec}})=\mathrm{alias}(g_0)=0$。记 $\mathfrak E_{\mathrm{EM+tail}}(g;\Delta,M,T):=\mathfrak E(g;\Delta,M,T)$ **去掉别名项后的两层**（EM 层 + $\mathcal{T}_\Delta$），从而

$$
\bigl|\mathcal S_{\mathrm{spec}}^{\Delta,M,T}-\mathcal S_{\mathrm{geo}}^{\Delta,M,T}\bigr|
\le \mathfrak E_{\mathrm{EM+tail}}(g_{\mathrm{spec}};\Delta,M,T)+\mathfrak E_{\mathrm{EM+tail}}(g_0;\Delta,M,T)+\mathcal E_{\mathrm{orb}}(T).
$$

> **注**：若密度 $\rho$ 或 $\phi_0$ 不带限，则即使 $\widehat h,\widehat w$ 紧支，$\widehat{g_{\mathrm{spec}}},\widehat{g_0}$ 亦未必紧支；此时需使用定理 18.1 的完整三分解上界。

### 定理 18.3（奇性保持与阶不升）

设 $\{h(\cdot;s)\}_{s\in\mathcal D}$ 为参数族（$\mathcal D\subset\mathbb C$ 为竖条），且参数仅进入 $h(\cdot;s)$；对任意紧子集 $K\subset\mathcal D$，假设

$$
\sup_{s\in K}\int_{\mathbb R}|h(x;s)|\,dx<\infty,\quad
\sup_{s\in K}\int_{\mathbb R}|\widehat h(\xi;s)|\,d\xi<\infty,\quad
\sup_{s\in K}|h^{(2j)}(\cdot;s)|_{L^1}<\infty\ (1\le j\le M),
$$

并且**密度 $\rho,\phi_0$ 与窗 $w_R$ 不依赖参数 $s$**（若依赖 $s$，需将其奇点并入"相同奇性集合"的比较基准）。

则 $\mathcal S_{\mathrm{spec}}(h(\cdot;s);R)$ 与 $\mathcal S_{\mathrm{geo}}(h(\cdot;s);R)$ 在 $\mathcal D$ 上具有**相同奇性集合且阶不升**；若窗在相应奇点处非零，则极点阶相同。

---

## 5. 规范系统视角：窗化能量与相位—密度比例

### 命题 5.1（Herglotz–Weyl 表示的窗化能量）

对任意非负偶窗 $w_R$ 与非负核 $h$,

$$
\int_{\mathbb R} h(x)\,w_R(x)\,d\mu(x)
=\frac{1}{\pi}\int_{\mathbb R} h(x)\,w_R(x)\,\Im m(x+i0)\,dx\ \ge 0.
\tag{5.1}
$$

### 命题 5.2（散射相位导数与密度：比例关系）

设散射矩阵通道特征值写作 $e^{\pm i\varphi(x)}$。在**单通道且选定合适的自由基准与归一化**下，有 $\det S=e^{-2\pi i\,\xi}$ 且 $\partial_x\arg\det S(x)=-2\pi\,\xi'(x)$。当所选规范使 $\rho$ 与 $\xi'$ 对应同一密度（或仅差常数因子）时，$\partial_x\arg\det S(x)=-2\pi\,\rho(x)$；在此匹配下存在常数 $c\ne0$（由通道归一与 $S$ 的定义唯一确定）使

$$
\boxed{\ \varphi'(x)=c\cdot \Im m(x+i0)\ }.
$$

比例常数不影响 §2 的非负性与 §4 的不等式结构。

> **注**：对多通道情形应理解为特征相位的**归一常数**可能不同；上式为单通道且基准归一化匹配时的典型情形。

---

## 6. 例示模板

**(i) Riemann $\xi$（$a=1,\ \varepsilon=+1$）**
取偶带限窗与高阶光滑偶核。若满足定理 18.2 的情形 (A)，可消去谱侧别名；否则按定理 18.1 进行三分解估计；连续谱由 (5.1) 非负控制。

**(ii) Dirichlet $L(\chi,\cdot)$（$a=1,\ |\varepsilon|=1$）**
镜像相位吸收于通道特征值；窗化与误差估计与 (i) 同步。

---

## 7. 失效边界与对策

* **无限阶 EM**：把 EM 当无穷级使用会引入伪奇性与非法换序，破坏定理 18.3 的奇性保持。应固定有限阶并使用 §3 的余项界。
* **被采样 integrand 不带限**：若 $g_{\mathrm{spec}}=g_1\cdot\rho$ 或 $g_0=g_1\cdot\phi_0$ 不带限（例如密度 $\rho,\phi_0$ 不带限），Nyquist 条件不能保证零别名；使用定理 18.1 的完整三分解上界。
* **散射侧对称失败**：若实轴酉性或镜像对称失配，(5.1) 的非负性与相位一致性不再保证；回退到一般变分不等式或强化规范系统正性。

---

## 8. 可检清单（最小充分条件）

1. **迹公式与密度**：核对 (TF) 在所选试验核类成立，给出 $I_0$、$\{A_\gamma,\ell_\gamma\}$、$\mu$ 的表达或上界；验证几何主项 $I_0[h]=\int h(x)\phi_0(x)\,dx$ 与谱密度 $\rho=\pi^{-1}\Im m$ 的 $L^1\cap L^\infty$ 性质。
2. **窗/核正则**：核 $h\in W^{2M,1}$ 且 $\widehat h\in L^1$；窗 $w$ 满足 $\widehat w\in L^1\cap C^{2M}$（带限，记带宽 $\Omega$）或 $\sup_t e^{\kappa'|t|}|w^{(k)}(t)|<\infty$ ($0\le k\le 2M$，指数型，记常数 $\kappa'$）。
3. **数值约定与误差结构**：
   - 被采样 integrand：$g_{\mathrm{spec}}=g_1\cdot\rho$、$g_0=g_1\cdot\phi_0$（$g_1=h\cdot w_R$）；
   - Lebesgue 型积分按 §3.1–§3.3 应用三分解误差 $\mathfrak E(g_{\mathrm{spec}};\Delta,M,T)$ 与 $\mathfrak E(g_0;\Delta,M,T)$；
   - 轨道和作为离散测度保持精确或按 §3.4（加权计数 $N_A$）给出截断误差 $\mathcal E_{\mathrm{orb}}(T)$。
4. **Nyquist 与采样**：仅当**被采样 integrand** $g_{\mathrm{spec}},g_0$ 频域带限时可消别名；步长 $\Delta\le 2\pi/\max\{\mathrm{bw}(\widehat{g_{\mathrm{spec}}}),\mathrm{bw}(\widehat{g_0})\}$（定理 18.2）。若密度不带限，即使 $\widehat h,\widehat w$ 紧支亦不能保证零别名。
5. **EM 阶与端点**：固定 $M$，验证 §3.2 的使用条件 $g^{(2M)}\in L^1$；不满足时不使用 EM 层（形式上 $M=0$），仅用"别名 + $\mathcal{T}_\Delta$"两项。
6. **连续谱**：以 Herglotz–Weyl 表示验证 $\rho=\pi^{-1}\Im m\ge0$，并核对镜像与根数相位。
7. **不等式输出（常数依赖）**：误差项常数依赖于 $\{|h^{(j)}|_{L^1}\}_{0\le j\le 2M}$、$|\widehat h|_{L^1}$、$|\rho|_{L^\infty}$、$|\phi_0|_{L^\infty}$、窗的平滑阶常数及缩放律。
8. **方向增长**：用支持函数上包控制轨道侧指数权增长，确保卷积绝对收敛。
9. **参数一致性**：当参数 $s$ 仅进入 $h(\cdot;s)$ 且满足一致可积的导数条件时，奇性"阶不升"成立；若密度 $\rho,\phi_0$、窗或几何数据依赖 $s$，需将其奇点并入"相同奇性集合"的比较基准。

---

## 9. 与相邻篇章的接口

* **↔ S15（Weyl–Heisenberg/采样—误差）**：窗化与"三分解误差"沿用 Nyquist–Poisson–EM 架构；Mellin 侧"平移—权乘"给出窗在谱侧与轨道侧的等价作用。
* **↔ S16（规范系统/谱测度）**：连续谱由 Herglotz 测度控制；$\rho=\pi^{-1}\Im m$ 把窗化能量与谱密度耦合。
* **↔ S17（散射—酉/对称）**：实轴酉性与镜像对称保证连续谱的正性与相位一致性；功能方程的根数体现为常相位。

---

## 附录 A：所用标准判据

### A.1 Poisson 求和与带限采样

对 $g\in\mathcal S(\mathbb R)$，

$$
\Delta\sum_{k\in\mathbb Z} g(k\Delta)
=\sum_{m\in\mathbb Z}\widehat g\!\left(\frac{2\pi m}{\Delta}\right),
$$

故

$$
\bigl|I(g)-S_\infty(g;\Delta)\bigr|
\le \sum_{m\ne0}\left|\widehat g\!\left(\frac{2\pi m}{\Delta}\right)\right|.
$$

若 $\widehat g\subset[-\Omega,\Omega]$ 且 $\Delta\le 2\pi/\Omega$（边界取零），则 $\Delta\sum_k g(k\Delta)=\int_{\mathbb R} g$。

> **注1**：本文实际只用到 $g,\widehat g\in L^1$ 情形的**不等式版**（而非恒等式在 $\mathcal S$ 中的充分条件）；上述 $\mathcal S$ 陈述仅为标准教科书参考形式。

> **注2（术语对齐）**：本文"带限/紧支"一律指**对应域**的紧支：频域带限指 $\mathrm{supp}(\widehat g)$ 紧；时域紧支指 $\mathrm{supp}(g)$ 紧。两者通过 Paley–Wiener 定理联系，但在迹公式应用中须分别验证。

### A.2 有限阶 Euler–Maclaurin 与余项界

若 $g^{(2M)}\in L^1(\mathbb R)$，则

$$
\sum_{n=m}^N g(n)=\int_m^N g(x)\,dx+\frac{g(m)+g(N)}{2}
+\sum_{j=1}^{M-1}\frac{B_{2j}}{(2j)!}\bigl(g^{(2j-1)}(N)-g^{(2j-1)}(m)\bigr)+R_{2M},
$$

且

$$
|R_{2M}|\le \frac{2\,\zeta(2M)}{(2\pi)^{2M}}\int_m^N |g^{(2M)}(x)|\,dx .
$$

### A.3 Herglotz–Weyl–Titchmarsh 表示

若 $m:\mathbb C^+\to\mathbb C$ 为 Herglotz 函数，则存在 $a\ge0$、$b\in\mathbb R$ 与正测度 $\nu$ 使

$$
m(z)=a z+b+\int_{\mathbb R}\Bigl(\frac{1}{t-z}-\frac{t}{1+t^2}\Bigr)\,d\nu(t),
$$

且 $(1/\pi)\Im m(x+i0)\,dx$ 即 $\nu$ 的绝对连续部分。对自伴二阶系统，$m$ 为 Weyl–Titchmarsh 函数。

### A.4 Birman–Krein 关系与相位导数

自伴散射系统的散射矩阵 $S(\lambda)$ 在实轴单位，谱移函数 $\xi(\lambda)$ 满足
$\det S(\lambda)=e^{-2\pi i \xi(\lambda)}$，并与密度或相位导数相联。

---

## 参考文献（选）

1. L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice–Hall, 1968.
2. N. I. Akhiezer, I. M. Glazman, *Theory of Linear Operators in Hilbert Space*, Dover.
3. E. C. Titchmarsh, *Eigenfunction Expansions Associated with Second-Order Differential Equations*, OUP.
4. C. Remling, Schrödinger operators and de Branges spaces, *J. Funct. Anal.* 196 (2002)；The absolutely continuous spectrum, *Math. Phys. Anal. Geom.* 10 (2007).
5. L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Springer.
6. E. M. Stein, R. Shakarchi, *Fourier Analysis*, Princeton.
7. F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §24.11.
8. T. M. Apostol, *Introduction to Analytic Number Theory*, Springer.
9. A. B. Aleksandrov, V. V. Peller, *Hankel Operators and Their Applications*, Springer.
10. D. Yafaev, *Mathematical Scattering Theory*, AMS.
11. H. Iwaniec, *Spectral Methods of Automorphic Forms*, AMS.
12. A. Selberg, Harmonic analysis and discontinuous groups, *J. Indian Math. Soc.* 20 (1956).
13. N. V. Kuznetsov, Petersson–Kuznetsov trace formula 综述（见 Iwaniec 书）。

---

## 结语

在镜像—规范—散射的统一接口下，窗化迹式在分布意义下给出**精确恒等**；其**数值实现**区分 Lebesgue 型积分与离散轨道和：前者以**被采样 integrand** $g_{\mathrm{spec}}=g_1\cdot\rho$（谱侧连续谱）与 $g_0=g_1\cdot\phi_0$（几何主项）为核，偏差由**别名 + 伯努利层 + 采样尾和**三项**非渐近**上界（$\mathfrak E(g_{\mathrm{spec}};\Delta,M,T)+\mathfrak E(g_0;\Delta,M,T)$）控制，仅当 $g_{\mathrm{spec}},g_0$ 频域带限并取 Nyquist 步长时可消去别名；后者作为离散测度保持精确或按加权计数函数 $N_A$ 给出显式截断误差（$\mathcal E_{\mathrm{orb}}(T)$，与 $\Delta,M$ 无耦合）。**有限阶** EM 纪律确保"**极点=主尺度**"与奇性保持；连续谱以 Herglotz 密度与酉对称给出非负与相位一致性。该结果为核与窗的优化、谱能量分配与数值基准提供逻辑闭合的支架，并与 S15–S17 无缝对齐。
