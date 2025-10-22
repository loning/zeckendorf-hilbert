# S16. de Branges–Krein 规范系统与完成函数的谱模型

—— RKHS → 规范系统（canonical system）→ 整函数零型的条件化框架

**作者**：Auric
**日期**：2025-10-21

---

## 摘要（定性）

在带权 Mellin–Hilbert 空间与镜像算子给出的评估结构之上，本文把完成函数 $\Xi$ 的内积评估 $\Xi(s)=\langle F,k_s\rangle$ 提升为一阶辛型 **de Branges–Krein 规范系统**

$$
\mathbf J\,Y'(t)=z\,H(t)\,Y(t),\qquad
\mathbf J=\begin{pmatrix}0&-1\\[1pt]1&0\end{pmatrix},\ \ H(t)\succeq0,
$$

的**谱模型**：在自反（镜像）与正性下，存在局部可积、实对称非负的哈密顿量 $H(t)$ 与传递矩阵 $M(t,z)$，其解族经 $H$-加权 $L^2$ 光谱变换与再生核 Hilbert 空间（S14）中的评估一致；功能方程 $\Xi(a-s)=\varepsilon \Xi(s)$ 等价于镜像算子本征关系 $JF=\varepsilon F$。进一步在"正定 + 增长可控"的条件下，得到关于中心轴的零点对称判据；若再满足 Hermite–Biehler（HB）对齐，则给出实轴（等价于 $s$-面的中心轴）零点落点与交错结论。解析层面始终采用**有限阶** Euler–Maclaurin（EM）与方向亚纯化，保持"**极点 = 主尺度**"；离散化误差按 **Nyquist–Poisson–EM** 三分解非渐近控制。

---

## 0. 记号与预设

### 0.1 完成函数与镜像

设

$$
\Xi(s)=Q^{s/2}\,r(s)\,L(s),\qquad r(a-s)=r(s),\qquad \Xi(a-s)=\varepsilon\,\Xi(s),\quad |\varepsilon|=1,
$$

中心轴为 $\Re s=\tfrac a2$。置

$$
E(z):=\Xi\left(\tfrac a2+iz\right),\qquad E^\sharp(z):=\overline{E(\bar z)},\qquad E(-z)=\varepsilon\,E(z).
$$

本文在需要时默认 $E(z)$ 为实型（即 $E(\bar z)=\overline{E(z)}$，由 S14 的自反核与实结构选取保证）；当根数 $\varepsilon\notin\{\pm1\}$ 时，$E(z)$ 在实轴一般非实值，且由 $E(-z)=\varepsilon E(z)$ 可知若 $\varepsilon\ne1$ 必有 $E(0)=0$（边界特例）。涉及实轴实值化需 Hardy–Z 型随 $z$ 的相位对齐。本文所称"HB 对齐"指存在常相位 $\theta_0$ 使 $e^{i\theta_0}E$ 为 Hermite–Biehler（HB）函数；涉及"随 $z$"的相位时明确称为 de Branges 相位函数 $\phi(x)$ 的对齐。

### 0.2 带权 Mellin–Hilbert 空间与镜像对合

$$
\mathcal H_a:=L^2(\mathbb R_+,x^{a-1}dx),\qquad (Jf)(x):=x^{-a}f(1/x),
$$

则 $J$ 为酉对合，$J^2=I$。经对数模型 $T:\mathcal H_a\to L^2(\mathbb R)$, $(Tf)(t):=e^{\tfrac a2 t} f(e^t)$ 化，得 $(TJT^{-1}g)(t)=g(-t)$。

*注*：下文 $\mathbf J$ 专指 $2\times2$ 斜对称矩阵，$J$ 专指 $\mathcal H_a$ 上的镜像对合。

### 0.3 再生核与评估

取 S14 的自反核 RKHS $\mathcal H(K)\subset\mathcal H_a$，评估向量 $k_s\in\mathcal H_a$ 满足

$$
\langle f,k_s\rangle_a=f^\ast(s),\qquad k_{a-s}=Jk_s.
$$

对 $F\in\mathcal H(K)$ 定义

$$
\Xi(s):=\langle F,k_s\rangle_a,\qquad \Xi(a-s)=\langle JF,k_s\rangle_a.
$$

于是

$$
JF=\varepsilon F\quad \Longleftrightarrow\quad \Xi(a-s)=\varepsilon\,\Xi(s).
$$

### 0.4 轴的对应关系

在 $z$-面与 $s$-面之间有

$$
z\in\mathbb R\quad \Longleftrightarrow\quad s=\tfrac a2+iz\ \text{位于中心轴 } \Re s=\tfrac a2.
$$

### 0.5 解析纪律与误差学

换序运算仅使用**有限阶** EM；伯努利层与余项在复参上整/全纯，所以**极点仅来自主尺度**。离散化误差按"**别名（Poisson/Nyquist） + 伯努利层（EM 校正） + 截断尾项**"三分解预算；若被积/被求和对象带限，则别名项为 0（Nyquist 条件）。

---

## 1. de Branges 空间与核表征

### 定义 1.1（de Branges 空间的 $\sharp$ 运算）

对整函数 $F$，置 $F^\sharp(z):=\overline{F(\bar z)}$。

### 命题 1.2（评估像空间）

令

$$
\mathcal E:=\bigl\{\,\mathcal V F:\, z\mapsto\langle F,k_{a/2+iz}\rangle_a\,\bigm|\,F\in\mathcal H(K)\,\bigr\}.
$$

则 $\mathcal E$ 是整函数 Hilbert 空间，核

$$
\mathsf K(z,w):=\langle k_{a/2+iw},k_{a/2+iz}\rangle_a
$$

在 $z$ 上全纯、在 $w$ 上反全纯，并满足

$$
\mathsf K(-z,-w)=\mathsf K(z,w),\qquad \mathsf K(\bar z,\bar w)=\overline{\mathsf K(z,w)}.
$$

### 定理 1.3（de Branges 公理）

空间 $\mathcal E$ 满足 de Branges 公理：
(i) 评估泛函 $F\mapsto F(w)$ 连续；
(ii) 若 $w\notin\mathbb R$ 且 $F(w)=0$，则

$$
\frac{z-\overline w}{z-w}\,F(z)\in\mathcal E,\qquad \Bigl|\frac{z-\overline w}{z-w}\,F\Bigr|=|F|;
$$

若 $w\in\mathbb R$ 且 $F(w)=0$，则 $\frac{F(z)}{z-w}\in\mathcal E$ 且 $\bigl|\frac{F}{z-w}\bigr|\le|F|$；
(iii) $F^\sharp\in\mathcal E$ 且 $|F^\sharp|=|F|$。

*证明.* 由 $k_{a-s}=Jk_s$ 与 $J$ 的酉性给出 (iii)。(i) 由 RKHS 评估连续性直接给出。对于 (ii)，核 $\mathsf K$ 由自反核与镜像算子诱导，对 $w\notin\mathbb R$ 有

$$
\frac{z-\bar w}{z-w}\,\mathsf K(z,w)
=\big\langle (I-\lambda J)k_{a/2+iw},\ (I-\lambda J)k_{a/2+iz}\big\rangle_a,\quad
\lambda:=\frac{w-\bar w}{z-w},
$$

从而为正核，因而 Möbius 乘子 $\frac{z-\bar w}{z-w}$ 保持空间与范数（等距），实零点处的除法 $\frac{F(z)}{z-w}$ 满足收缩性；这等价于 de Branges 型反射正性。

### 推论 1.4（Hermite–Biehler 生成与核公式）

存在 Hermite–Biehler（HB）函数 $E_0$（即 $|E_0(z)|>|E_0^\sharp(z)|$ 对 $\Im z>0$）使

$$
\mathcal E=\mathcal H(E_0),\qquad
\mathsf K(z,w)=\frac{E_0^\sharp(z)\,\overline{E_0^\sharp(w)}-E_0(z)\,\overline{E_0(w)}}{2\pi i\,(z-\bar w)}.
$$

*注*：当 $E_0$ 在实轴有零时，$\mathsf K$ 仍为正核，但需按 de Branges 约定忽略 $E_0$ 与 $E_0^\sharp$ 的共同实零（若有）或采取极限解释。

---

## 2. 规范系统与传递矩阵

如无特别说明，以下均在 $t\in[0,T)$（$T\le\infty$）上讨论。

### 定义 2.1（哈密顿量与规范系统）

称可测矩阵函数 $H:[0,T)\to\mathbb R^{2\times2}$ 为**哈密顿量**，若几乎处处 $H(t)=H(t)^\top\succeq0$ 且 $\operatorname{tr}H\in L^1_{\mathrm{loc}}[0,T)$。规范系统指

$$
\mathbf J\,Y'(t)=z\,H(t)\,Y(t),\qquad Y(t;z)\in\mathbb C^2.
$$

### 定义 2.2（传递矩阵）

传递矩阵 $M(t,z)$ 为满足

$$
\mathbf J\,\partial_t M(t,z)=z\,H(t)\,M(t,z),\qquad M(0,z)=I
$$

的矩阵解。

### 命题 2.3（行列式与辛结构）

对一切 $t,z$，有

$$
\det M(t,z)\equiv 1.
$$

对实 $z$，$M(t,z)\in \mathrm{Sp}(2,\mathbb R)$，即 $M(t,z)^\top \mathbf J\,M(t,z)=\mathbf J$。更一般地，对任意 $z\in\mathbb C$ 有 **$J$-幺正性**

$$
M(t,\bar z)^\ast\,\mathbf J\,M(t,z)=\mathbf J.
$$

*证明.* 由 $\mathbf J\,M' = zHM$ 得 $M'=-z\,\mathbf J H M$。则

$$
\frac{d}{dt}\log\det M=\mathrm{tr}(M^{-1}M')=\mathrm{tr}(-z\,\mathbf J H)= -z\,\mathrm{tr}(\mathbf JH)=0
$$

（因 $\mathbf J$ 斜对称、$H$ 对称），因此 $\det M(t,z)\equiv1$ 对一切 $t,z$ 成立。对 $z\in\mathbb R$，计算 $\frac{d}{dt}(M^\top \mathbf J M)=0$ 得辛性；对任意 $z$，计算 $\frac{d}{dt}\bigl(M(\bar z)^\ast \mathbf J M(z)\bigr)=0$ 得 $J$-幺正性。该恒等式对任意 $z\in\mathbb C$ 成立，起点 $t=0$ 取 $M(0,z)=I$ 保证常数为 $\mathbf J$。

### 定理 2.4（de Branges–Krein 光谱表示）

存在哈密顿量 $H\succeq0$ 与传递矩阵 $M(t,z)$，以及等距同构

$$
\mathcal U:\ L^2_H([0,T))\ \xrightarrow{\ \cong\ }\ \mathcal E=\mathcal H(E_0),
$$

使对每个 $F\in\mathcal H(K)$ 存在唯一 $f_F\in L^2_H$ 满足（线性依赖于 $F$）

$$
E_F(z)=\langle F,k_{a/2+iz}\rangle_a
=\int_0^T Y(t,\bar z)^\ast\,H(t)\,f_F(t)\,dt,
$$

其中 $Y(t,z):=M(t,z)\,v_0$，$v_0\in\mathbb C^2$ 为固定非零向量（例如 $v_0=(1,i)^\top$）。

*证明要点.* 由定理 1.3–推论 1.4，$\mathcal E$ 为某 HB 函数 $E_0$ 的 de Branges 空间。de Branges–Krein 理论给出：存在哈密顿量 $H$ 与随 $t$ 演化的空间链 $\mathcal H(E_t)$ 及传递矩阵 $M(t,z)$，使"顶端空间" $\mathcal H(E_0)$ 由规范系统的 Weyl–Titchmarsh 光谱变换与 $H$ 的 $L^2$ 内积实现。将 $\mathcal V:\mathcal H(K)\to \mathcal H(E_0)$ 与该光谱映射复合即得上述等距同构。

*记号提示.* 本节中的 $Y(t,z)=M(t,z)v_0$ 仅作光谱表示的核；自 §3 起，若无特别说明，$Y(\cdot;z)$ 专指 $L_H^2$-可积的 Weyl 解（并取 $Y^{(1)}(0;z)=1$）。

---

## 3. Weyl–Titchmarsh $m$-函数与 Herglotz 表示

### 定义 3.1（Weyl–Titchmarsh 函数）

在给定的规范系统上，定义

$$
m(z):=\frac{Y^{(2)}(0;z)}{Y^{(1)}(0;z)}.
$$

此处 $Y(\cdot;z)$ 指在 $[0,T)$ 上 $L_H^2$-可积的 Weyl 解，并取 $Y^{(1)}(0;z)=1$ 归一化。取同一 Weyl 解 $Y$ 定义 $E:=Y^{(1)}+iY^{(2)}$，则

$$
i\,\frac{E^\sharp(z)-E(z)}{E^\sharp(z)+E(z)}=\frac{Y^{(2)}(0;z)}{Y^{(1)}(0;z)}=m(z).
$$

这里的 $E$ 是由该 Weyl 解构造的 HB 生成函数（与 §1.4 的 HB 生成一致至常相位）。

*说明.* 由 $E=Y^{(1)}+iY^{(2)}$ 得 $E^\sharp=Y^{(1)}-iY^{(2)}$，代入上式即得 $m(z)=\frac{Y^{(2)}}{Y^{(1)}}$。令 $q(z):=E^\sharp(z)/E(z)$，由 HB 性质在上半平面有 $|q(z)|<1$，则 $m(z)=i\frac{1-q(z)}{1+q(z)}$ 映射上半平面到上半平面，便于与 Carathéodory/Herglotz 表示对齐。

### 定理 3.2（Herglotz–Nevanlinna 性）

若 $H\succeq 0$，则 $m$ 在上半平面为 Herglotz–Nevanlinna 函数，且存在唯一正测度 $\mu$、实常数 $\alpha\in\mathbb R$、$\beta\ge 0$ 使

$$
m(z)=\alpha+\beta z+\int_{\mathbb R}\!\Bigl(\frac{1}{x-z}-\frac{x}{1+x^2}\Bigr)\,d\mu(x),\qquad
\int_{\mathbb R}\frac{1}{1+x^2}\,d\mu(x)<\infty.
$$

*证明.* 令 $z=u+iv$ 且 $v>0$。由

$$
\frac{1}{2i}\frac{d}{dt}\bigl(Y(\bar z)^\ast \mathbf J Y(z)\bigr)
= Y(\bar z)^\ast\,\frac{z-\bar z}{2i}\,H\,Y(z)
=v\,Y(\bar z)^\ast H Y(z)\ \ge 0,
$$

因而 $\Im\bigl(Y(\bar z)^\ast \mathbf J Y(z)\bigr)$ 随 $t$ 单增。对 $L_H^2$-可积的 Weyl 解，$\lim_{t\uparrow T}Y(\bar z,t)^\ast\mathbf J Y(z,t)=0$，故由起点值 $Y(0;z)=(1,m(z))^\top$ 得 $\Im m(z)\ge 0$。Herglotz 表示定理给出积分型及参数约束 $(\alpha\in\mathbb R,\beta\ge0)$。

---

## 4. 功能方程、镜像与辛对称

### 定理 4.1（功能方程 ↔ 镜像本征）

$$
\Xi(a-s)=\varepsilon\,\Xi(s)\quad \Longleftrightarrow\quad JF=\varepsilon F
\quad \Longleftrightarrow\quad E_F(-z)=\varepsilon\,E_F(z).
$$

*证明.* 由 $k_{a-s}=Jk_s$ 与 $J$ 的酉性，$\Xi(a-s)=\langle JF,k_s\rangle_a$。其余等价性由 $z\leftrightarrow s$ 的参数化与 0.4 直接得到。

### 命题 4.2（传递矩阵的镜像共轭——充要条件）

若存在与 $t,z$ 无关的常矩阵 $\mathbf S\in GL(2,\mathbb R)$ 使

$$
\boxed{\ \mathbf S^\top\mathbf J\mathbf S=-\mathbf J\ }\quad\text{(反辛)}\qquad\text{且}\qquad
\boxed{\ \mathbf S\,H(t)\,\mathbf S^{-1}=H(t)\ \text{ a.e.}},
$$

则对一切 $t,z$ 有

$$
M(t,-z)=\mathbf S\,M(t,z)\,\mathbf S^{-1}.
$$

反之亦然。

*提示*：$\mathbf S^\top\mathbf J\mathbf S=-\mathbf J$ 为"反辛"条件，能把 $\mathbf J\,\partial_t$ 的符号翻转，与 $\mathbf S H\mathbf S^{-1}=H$ 联合给出所述结论。必要性方向由对 $t$ 求导与初值唯一性推出。

未假设反辛对齐时，仅能从 $JF=\varepsilon F$ 推出函数层面的 $E_F(-z)=\varepsilon E_F(z)$。

---

## 5. 零型对称与 HB 对齐

### 定理 5.1（零点对称）

设 $H\succeq0$ 且增长受控（S10 支持函数上界），并假设 $F$ 为镜像本征向量 $JF=\varepsilon F$（等价于 $\Xi(a-s)=\varepsilon\Xi(s)$，$|\varepsilon|=1$），则 $E_F$ 的零点集始终关于

$$
z\mapsto -z
$$

闭合，即若 $z_0$ 为零点，则 $-z_0$ 同为零点（计重数）。若进一步 $E_F$ 为实型（即 $E_F(\bar z)=\overline{E_F(z)}$），则零点对 $\{z_0,-z_0,\bar z_0,-\bar z_0\}$ 闭合。

*证明.* 由定理 4.1 的 $E_F(-z)=\varepsilon E_F(z)$ 得 $z\leftrightarrow -z$ 对称；实型条件给出 $E_F^\sharp(\bar z)=\overline{E_F(z)}$ 从而 $z\leftrightarrow\bar z$ 对称；EM 仅引入整/全纯修正，不改变奇性集合。

### 定理 5.2（HB 对齐与实轴落点）

若 $E_F$ HB 对齐且满足 $E_F(-z)=\pm E_F(z)$，则 $E_F$ 无非实零，因而其零点（若存在）全部落在 $z\in\mathbb R$（对应 $s$-面的中心轴）。

此时可写 $e^{i\theta_0}E_F=A-iB$（$\theta_0$ 为常数相位），其中 $A,B$ 为实整函数且零点全实且交错。一般情形要在实轴上引入随 $z$ 的相位 $\theta(z)$（Hardy–Z 对齐）来实现实值化；"$\Xi$ 等价于 $A$ 或 $B$"应理解为相位对齐后的实/虚部识别，而非恒等。

*证明.* HB 对齐保证上半平面 $|E_F|>|E_F^\sharp|$，故上半平面无零。镜像偶奇性 $E_F(-z)=\pm E_F(z)$ 保证若下半平面有零，则上半平面必有镜像零，与 HB 性质矛盾。由这两步排除，零点仅余实轴。de Branges 基本定理给出：HB 生成函数的实部与虚部零点全实且交错。由 0.4 把 $z\in\mathbb R$ 转写为 $\Re s=\tfrac a2$。

---

## 6. 窗化/卷积与奇性保持；非渐近误差

*说明*：本节结论针对 EM/离散化近似表达式的奇性来源分析；对原始 $\Xi$（整函数）其奇性集合为空。

### 定理 6.1（窗化不改变奇性集合）

取偶窗 $\psi$（紧支或指数衰减），令

$$
\Xi_\psi(s):=\langle F\ast\psi,\,k_s\rangle_a.
$$

在仅用**有限阶** EM 的处理下，$\Xi_\psi$ 与 $\Xi$ 在同一条带具有相同的奇性集合与阶。

*证明.* 卷积保留主尺度项；伯努利层与余项在 $s$ 上整/全纯，奇性集合不变。

*注*：此结论在仅用有限阶 EM 的前提下成立；若引入无穷阶展开或带支点的窗，需重新核对奇性来源。

### 定理 6.2（Nyquist–Poisson–EM 三分解）

设 $g$ 可积且分段光滑，步长 $\Delta>0$、EM 阶 $M$、截断 $T$。则

$$
\Bigl|\ \int_{\mathbb R} g(u)\,du-\Delta\sum_{k\in\mathbb Z} g(k\Delta)\ \Bigr|
\ \le \ \underbrace{\sum_{m\ne0}\bigl|\widehat g(2\pi m/\Delta)\bigr|}_{\text{别名}}
+\underbrace{\sum_{j=1}^{M-1}c_j\,\Delta^{2j}\,|g^{(2j)}|_{L^1}}_{\text{伯努利层}}
+\underbrace{\int_{|u|>T}|g(u)|\,du}_{\text{截断尾项}}.
$$

若 $g$ 带限且 $\Delta\le \pi/\Omega$（Nyquist），则"别名项 = 0"。

*证明.* Poisson 求和公式 + 有限阶 EM（到 $2M-2$ 阶）+ 截断估计。

---

## 7. 典型模板

* **Riemann $\xi$**：$a=1$、$\varepsilon=+1$，取 $E(z)=\xi(\tfrac12+iz)$。由定理 2.4 得 $H,M$ 及等距同构 $\mathcal U:L^2_H\to\mathcal E$（对应唯一 $f_F$ 的光谱表示），镜像条件由 $JF=F$ 编码。若进一步存在 HB 对齐，则零点位于 $z\in\mathbb R$（即 $\Re s=\tfrac12$）。

* **Dirichlet $L(\chi,\cdot)$**：$a=1$、$\varepsilon$ 为单位模相位。相同构造得到 $H,M$ 与光谱同构 $\mathcal U$，并有函数级镜像 $E(-z)=\varepsilon E(z)$；窗与误差由 S8/S11 的核选择和三分解统一控制。

---

## 8. 与相关篇章的接口

* **↔ S14（RKHS/BN 界面）**：由自反核 RKHS 出发，把"内积评估—镜像"转化为规范系统的解表示（定理 2.4）；BN 投影与窗选择在规范系统侧体现为对 $H$ 的能量汲取。
* **↔ S15（酉表示/镜像算子）**：$(\overline A,\overline B,J)$ 的 Weyl 关系给出 $t$-模型与镜像的算子化语义；功能方程与镜像本征等价（定理 4.1）。
* **↔ S4/S5（EM/方向亚纯化）**：奇性保持与极点定位由"有限阶 EM + 主尺度"与方向亚纯化保证（定理 6.1）。
* **↔ S8（Nyquist–Poisson–EM）**：非渐近误差与实现细则沿三分解执行（定理 6.2）。
* **↔ S13（谱半径阈值）**：窗内 Rayleigh 商的极值在规范系统侧对应传递矩阵条目的下界与稳定窗，可用于大值存在性的非渐近阈值化。

---

## 结语

本文把 S14 的**镜像核—Hilbert 子空间**与 S15 的**酉表示—镜像算子**缝合为**de Branges–Krein 规范系统**的谱模型：评估整函数由一阶辛系统的解线性生成；功能方程等价于镜像本征与函数级对称；在明确可检的正性与增长条件下，得到零型对称与 HB 对齐下的实轴落点。解析纪律由**有限阶** EM 与方向亚纯化保证"**极点 = 主尺度**"，增长与误差由 S10/S8 闭合，为后续 **散射—功能方程的算子化**与**谱窗化不等式**提供统一的算子与能量框架。
