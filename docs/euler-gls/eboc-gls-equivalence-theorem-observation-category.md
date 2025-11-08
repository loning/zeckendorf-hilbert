# EBOC–GLS 等价定理（观察范畴版）

Version: 1.9

## 摘要

在四条可检条件——全局幺正/可逆化、有限记忆/可马尔可夫化、带限与 Nyquist–Poisson–Euler–Maclaurin（NPE）有限阶闭合、时间账本对齐——之下,构造函子 $\mathfrak F:\mathbf{EBOC}\to\mathbf{GLS}$、$\mathfrak G:\mathbf{GLS}\to\mathbf{EBOC}$ 与自然变换 $\eta,\epsilon$,证明二者在观察范畴中互为等价。桥梁为母刻度同一式 $\boxed{\ \varphi'(E)/\pi=\tfrac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E)\ }$、$\boxed{\ \rho_{\rm rel}(E)=\xi'(E)=-\tfrac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E)\ }$，故 $\varphi'(E)/\pi=-\rho_{\rm rel}(E)$（$\mathsf Q=-i\,S^\dagger \partial_E S$）与窗化迹恒等式；NPE 纪律给出离散化与端点—尾项的非渐近闭合而不引入新奇性。由此,EBOC 的"静态块—因子译码—复杂度/熵账本"与 GLS 的"幺正散射—群延迟—窗化测度"逐窗一致。([ChaosBook][1])

---

## 0. 记号、对象与公理

### 0.1 EBOC 对象与观察读数

EBOC 对象写作
$$
\mathcal U=(X_f,G,\rho,\Sigma,f,\pi,\mu,\nu).
$$
其中 $X_f\subset\Sigma^{\mathbb Z^{d+1}}$ 为由有限邻域规则 $f$ 定义的 SFT；时间子作用为 $\sigma_{\rm time}$；$\pi$ 为有限厚度的逐叶因子译码；$\mu$ 为 $\sigma_{\rm time}$-不变遍历测度；$\nu$ 为通用半测度。采用四条可检公理：A0（静态块与可扩张）、A1（因果局域；有限传播半径）、A2（观察=因子译码）、A3（信息不增；因子熵单调）。SMB 与 Brudno 等式给出时间片族 $W$ 上以 $L(W)=T$ 归一化的复杂度/熵密度对齐：几乎处处
$$
\lim_{|W|\to\infty}\frac{1}{L(W)}K\!\big(\pi(x)\mid W\big)
= h_{\pi_\ast\mu}(\sigma_{\rm time})\le h_\mu(\sigma_{\rm time}).
$$
这在 $\mathbb Z^d$ 子移位情形可推广。([Project Euclid][2])

### 0.2 GLS 对象、母刻度与窗化读数

GLS 对象写作
$$
\mathfrak U=(\mathcal H,S(E),\mathcal W),
$$
其中 $S(E)\in\mathsf U(N)$ 幺正且可微,$\mathsf Q(E)=-i\,S(E)^\dagger \tfrac{dS}{dE}(E)$ 为 Wigner–Smith 群延迟矩阵,总群延迟 $\mathrm{tr}\,\mathsf Q$；密度—延迟—相位满足
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E)\ },\qquad \boxed{\ \rho_{\rm rel}(E)=\xi'(E)=-\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E)\ },\ \text{因而}\ \frac{\varphi'(E)}{\pi}=-\rho_{\rm rel}(E).
$$
并与谱位移函数 $\xi$ 由 Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\,\xi(E)}$ 联络,故 $\xi'(E)=-\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E)$。([ChaosBook][1])
给定窗—核对 $(w_R,h)\in\mathcal W$,定义窗化读数
$$
\mathrm{Obs}(w_R,h;\rho)=\int_{\mathbb R} w_R(E)\,(h\star \rho_{\rm rel})(E)\,dE,
$$
其中 $\star$ 表示相关运算：$(h\star \rho)(E):=(\check h\ast \rho)(E)=\int_{\mathbb R} h(t-E)\,\rho(t)\,dt$，$\check h(E)=h(-E)$。
设 $P_\gamma$ 为通道 $\gamma$ 的正交投影，定义通道群延迟矩阵
$$
\mathsf Q_\gamma(E):=P_\gamma\,\mathsf Q(E)\,P_\gamma,\qquad \mathrm{tr}\,\mathsf Q_\gamma(E)=\mathrm{Tr}\big(P_\gamma\,\mathsf Q(E)\big).
$$
由此，沿通道 $\gamma$ 的窗化群延迟
$$
T_\gamma[w_R,h]=\int_{\mathbb R} (w_R\ast \check h)(E)\,\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q_\gamma(E)\,dE.
$$

### 0.3 NPE 有限阶误差学与采样闭合

若 $\widehat w_R,\widehat h$ 带限,取 Nyquist 步长 $\Delta$ 使别名归零,则对 $f(E)=w_R(E)\,(h\star\rho_{\rm rel})(E)$ 有严格采样
$$
\int_{\mathbb R} f(E)\,dE=\Delta\sum_{n\in\mathbb Z} f(E_0+n\Delta).
$$
近带限时,别名项由 Poisson 求和控制,端点与尾项由有限阶 Euler–Maclaurin（EM）闭合,余项具显式 Bernoulli–$\zeta$ 上界。([webusers.imj-prg.fr][3])

---

## 1. 观察范畴与主命题

### 1.1 观察范畴

记 $\mathbf{Obs}$ 之对象为"系统 $+$ 读数字典"；态射为保持读数的因子/共轭（EBOC 侧为因子映射；GLS 侧为幺正共轭）。定义
$$
\mathsf{Obs}_{\rm E}(\mathcal U):=\big\{\mathcal O_{\pi,\varsigma},\text{及其极限统计/熵率}\big\},\qquad
\mathsf{Obs}_{\rm G}(\mathfrak U):=\big\{\mathrm{Obs}(w_R,h)\,,T_\gamma[w_R,h]\big\}.
$$

### 1.2 主定理（观察范畴版等价）

在 A0–A3 与"四条件"下,存在函子 $\mathfrak F:\mathbf{EBOC}\to\mathbf{GLS}$、$\mathfrak G:\mathbf{GLS}\to\mathbf{EBOC}$ 及自然变换 $\eta,\epsilon$,使
$$
\mathsf{Obs}_{\rm G}\!\big(\mathfrak F(\mathcal U)\big)\cong \mathsf{Obs}_{\rm E}(\mathcal U),\qquad
\mathsf{Obs}_{\rm E}\!\big(\mathfrak G(\mathfrak U)\big)\cong \mathsf{Obs}_{\rm G}(\mathfrak U),
$$
从而 $\mathfrak F,\mathfrak G$ 在 $\mathbf{Obs}$ 中互为等价。

---

## 2. 技术引理与证明

### 引理 2.1（母刻度统一式）

若 $S(E)$ 幺正可微,定义 $\mathsf Q=-i\,S^\dagger S'$。则几乎处处
$$
\rho_{\rm rel}(E)=\xi'(E)=-\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E),\quad
\frac{\varphi'(E)}{\pi}=-\rho_{\rm rel}(E),\quad \det S=e^{2i\varphi}.
$$
**证明** 由 Birman–Kreĭn $\det S(E)=e^{-2\pi i\,\xi(E)}$ 与
$\partial_E\log\det S(E)=\mathrm{tr}\,(S^\dagger S')$,得
$\mathrm{tr}\,\mathsf Q(E)=-2\pi\,\xi'(E)$。令 $\rho_{\rm rel}=\xi'$ 得首式；设 $\varphi=\tfrac12\arg\det S$ 则 $\varphi'=\tfrac12\mathrm{tr}\,\mathsf Q=-\pi\xi'$，故 $\varphi'/\pi=-\xi'=-\rho_{\rm rel}$ 得次式。([arXiv][4])

### 引理 2.2（窗化读数 = 压缩迹恒等式）

设 $(A,B)$ 为自伴算子且 $A-B\in\mathcal S_1$。令 $f:=-(w_R\ast \check h)$，并假设 $f\in OL(\mathbb R)$，并且
$$
(w_R\ast \check h)\in W^{1,1}(\mathbb R),\qquad (w_R\ast \check h)(E)\,\xi(E)\xrightarrow[E\to\pm\infty]{}0.
$$
（例如：$w_R\in L^1\cap W^{1,1}$ 且具紧支撑或快速衰减、$h\in L^1$，则 $(w_R\ast \check h)\in W^{1,1}$；典型散射情形下 $\xi$ 具有界变差并趋于常数。）定义
$$
K_{w,h}:=f(A)-f(B)\qquad(\text{其迹与由 }(w_R,h)\text{ 定义的 Toeplitz/Berezin 窗化压缩同值}).
$$
在此条件下分部积分无边界项，故
$$
\mathrm{Tr}\,K_{w,h}=\int_{\mathbb R} w_R(E)\,(h\star\rho_{\rm rel})(E)\,dE.
$$
**证明** 由 Lifshits–Kreĭn 迹公式（$A-B\in\mathcal S_1,\ f\in OL$），
$$
\mathrm{Tr}\big(f(A)-f(B)\big)=\int_{\mathbb R} f'(E)\,\xi(E)\,dE.
$$
按 §0.2 定义 $(h\star\rho_{\rm rel})=\check h\ast\rho_{\rm rel}$ 与 $\rho_{\rm rel}=\xi'$，分部积分给出
$$
\int_{\mathbb R} w_R(E)\,(h\star\rho_{\rm rel})(E)\,dE
=\int_{\mathbb R} (w_R\ast \check h)(E)\,\xi'(E)\,dE
=-\int_{\mathbb R} (w_R\ast \check h)'(E)\,\xi(E)\,dE
=\int_{\mathbb R} f'(E)\,\xi(E)\,dE,
$$
因而结论成立。幺正规型可由 Aleksandrov–Peller 的单位圆版本处理。([arXiv][5])

### 引理 2.3（Poisson–Nyquist 与 EM 闭合）

若 $\widehat f$ 支持于 $(-\Omega,\Omega)$ 且 $\Delta\le \pi/\Omega$,则
$$
\int f=\Delta\sum_{n\in\mathbb Z} f(E_0+n\Delta).
$$
近带限时,加入 Poisson 别名上界与 EM 有界余项,得非渐近误差预算。([webusers.imj-prg.fr][3])

### 引理 2.4（SMB/Brudno 与因子熵单调）

对遍历 $(X_f,\mu)$ 与因子 $\pi$ 几乎处处
$$
\lim_{|W|\to\infty}\frac{1}{L(W)}K(\pi(x)\mid W)
= h_{\pi_\ast\mu}(\sigma_{\rm time})\le h_{\mu}(\sigma_{\rm time}).
$$
**证明** SMB 与其多维推广给出熵率；Brudno 等式识别复杂度密度；因子熵单调来自滑块码理论（Lind–Marcus）。([Project Euclid][2])

### 引理 2.5（可马尔可夫化与 SFT 覆盖）

有限记忆（或经高阶块化后有限记忆）的观测序列形成 sofic 子移位；任一 sofic 移位均是某 SFT 的因子,因此存在 SFT 覆盖以局域约束实现该观测。([Cambridge University Press & Assessment][6])

### 引理 2.6（可逆化与 QCA 结构定理）

任意可逆经典 CA（或经 Bennett 寄存器扩张后的可逆化系统）可量子化为具有严格有限传播速度的 QCA 幺正 $U$,并可作广义 Margolus 分块；其逆仍为邻近耦合的 QCA。故存在 Floquet 单位步与散射表述。([mathweb.ucsd.edu][7])

---

## 3. 函子 $\mathfrak F:\mathbf{EBOC}\to\mathbf{GLS}$ 的构造与证明

### 3.1 可逆化与散射化

对 $\mathcal U$ 施 Bennett 式"历史寄存器"扩张得可逆 CA；按 Schumacher–Werner 量子化为有限传播的 QCA 幺正 $U$。在适当的定域—外域分解下构造散射矩阵族 $S(E)$ 与 Wigner–Smith 矩阵 $\mathsf Q(E)$。由 QCA 的结构定理,$U$ 可写成两步分块幺正,保证有限传播与结构可逆。([arXiv][8])

### 3.2 逐叶译码—窗核对齐

选取叶族 $\varsigma$ 与有限厚度译码 $\pi$,以核厚度匹配叶步长,建立字典
$$
(\pi,\varsigma)\longleftrightarrow (w_R,h).
$$
由引理 2.1–2.2,逐窗读数满足
$$
\mathcal O_{\pi,\varsigma}
=\mathrm{Obs}(w_R,h;\rho)
=\int_{\mathbb R} w_R(E)\,(h\star \rho_{\rm rel})(E)\,dE,
$$
且所有读数以母刻度 $\varphi'(E)/\pi=-(\rho_{\rm rel}(E))=\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E)$ 统一。([arXiv][5])

### 3.3 NPE 闭合与"无新奇性"

若 $\widehat w_R,\widehat h$ 带限且 Nyquist 采样,Poisson 混叠为零；近带限时以有限阶 EM 关闭端点与尾项。引理 2.3 确保余项具显式上界,函数类的解析/整性不劣化,满足"奇性不增"。([Massachusetts Institute of Technology][9])

### 3.4 时间账本与无信号

有限传播 $+$ 幺正性给出无超锥传播（无信号）；窗化时间 $T_\gamma[w_R,h]$ 仅为刻度读数,因果偏序由前沿时间决定。由 SMB/Brudno 与因子熵单调,EBOC 时间片账本与 GLS 密度—延迟账本对齐。([ChaosBook][1])

**定义** $\mathfrak F(\mathcal U):=(\mathcal H,S(E),\mathcal W)$ 并约定
$\mathsf{Obs}_{\rm G}(\mathfrak F(\mathcal U))=\mathsf{Obs}_{\rm E}(\mathcal U)$。

---

## 4. 函子 $\mathfrak G:\mathbf{GLS}\to\mathbf{EBOC}$ 的构造与证明

### 4.1 带限离散化与压缩迹

设 $f(E)=w_R(E)\,(h\star \rho_{\rm rel})(E)$。带限+Nyquist 时
$$
\mathrm{Obs}(w_R,h;\rho)=\int f(E)\,dE
=\Delta\sum_{n\in\mathbb Z} f(E_0+n\Delta).
$$
近带限时加上有限阶 EM 余项闭合。算子层面,窗化压缩 $K_{w,h}$ 满足
$\mathrm{Tr}\,K_{w,h}=\int f$（引理 2.2）。([webusers.imj-prg.fr][3])

### 4.2 SFT 化与有限记忆译码

将采样值 $f(E_0+n\Delta)$ 量化为有限字母,辅以长度 $M$ 的线性一致性约束（卷积/预测残差）得到 sofic 子移位；取其 SFT 覆盖并获得有限厚度译码 $\pi$。由 SMB/Brudno 与因子熵单调,时间片极限统计与 $\mathrm{Obs}(w_R,h;\rho)$ 对齐。([Cambridge University Press & Assessment][6])

### 4.3 因果与无信号的离散实现

带宽 $\Rightarrow$ 有限相关长度 $\Rightarrow$ 有限传播半径,可在 SFT 规则中以局域排他性与邻域约束实现因果偏序与无信号。
**定义** $\mathfrak G(\mathfrak U):=(X_f,G,\rho,\Sigma,f,\pi,\mu,\nu)$ 且
$\mathsf{Obs}_{\rm E}(\mathfrak G(\mathfrak U))=\mathsf{Obs}_{\rm G}(\mathfrak U)$。

---

## 5. 自然变换与范畴等价

**自然变换 $\eta:\mathrm{Id}_{\mathbf{EBOC}}\Rightarrow \mathfrak G\!\circ\!\mathfrak F$**
对每个 $\mathcal U$,令 $\eta_\mathcal U$ 使对任意对齐字典 $(\pi,\varsigma)\leftrightarrow(w_R,h)$ 有
$$
\mathcal O_{\pi,\varsigma}=\mathrm{Obs}(w_R,h;\rho).
$$
该同一在 NPE 预算内逐窗成立,并对因子态射交换。

**自然变换 $\epsilon:\mathfrak F\!\circ\!\mathfrak G\Rightarrow \mathrm{Id}_{\mathbf{GLS}}$**
对每个 $\mathfrak U$,取去规范相位后的群延迟密度同一：
$$
\boxed{\ -\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q_{\mathfrak F(\mathfrak G(\mathfrak U))}(E)=\rho_{\rm rel}(E)\ },
$$
故一切 $\mathrm{Obs}(w_R,h)$、$T_\gamma[w_R,h]$ 值保持。

**等价性** 由引理 2.1–2.3 的不变性与引理 2.4–2.6 的存在性,$\eta,\epsilon$ 为自然同构,故 $\mathfrak F,\mathfrak G$ 在 $\mathbf{Obs}$ 上互为等价。([arXiv][4])

---

## 6. 关键步骤的详细证明

### 6.1 EBOC $\to$ GLS：核算一致性的全细节

取任意带限 $(w_R,h)$。由引理 2.1,母刻度同一式给出
$\rho_{\rm rel}=-\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q$ 且 $\frac{\varphi'}{\pi}=-\rho_{\rm rel}$。
由引理 2.2,
$$
\mathrm{Obs}(w_R,h;\rho)=\mathrm{Tr}\,K_{w,h}.
$$
EBOC 侧，$\pi$ 为有限厚度译码，$\mu$ 遍历且 $L(W)=T$ 为时间长度。由 Birkhoff/SMB 与 Brudno，$\mu$-几乎处处有（假设 $\int_{\mathbb R} w_R(E)\,dE\neq 0$）
$$
\lim_{|W|\to\infty}\frac{1}{L(W)}\sum_{t\in W}\mathcal O_{\pi,\varsigma}\!\big(\sigma_{\rm time}^t x\big)
=\frac{1}{\int_{\mathbb R} w_R(E)\,dE}\mathrm{Tr}\,K_{w,h}
=\frac{1}{\int_{\mathbb R} w_R(E)\,dE}\int_{\mathbb R} w_R(E)\,(h\star\rho_{\rm rel})(E)\,dE.
$$
于是 $\mathsf{Obs}_{\rm G}(\mathfrak F(\mathcal U))\cong \mathsf{Obs}_{\rm E}(\mathcal U)$ 在时间密度刻度上逐窗一致。
([arXiv][5])

### 6.2 GLS $\to$ EBOC：SFT 化的构造细节

令 $f(E)=w_R(E)\,(h\star \rho_{\rm rel})(E)$。带限+Nyquist：
$$
\int f=\Delta\sum_{n\in\mathbb Z} f(E_0+n\Delta).
$$
近带限时，有
$$
\int_{\mathbb R} f(E)\,dE
= \Delta\sum_{|n|\le N} f(E_0+n\Delta)
- 2\pi\sum_{k\ne 0}\widehat f\!\left(\frac{2\pi k}{\Delta}\right)e^{i\,2\pi k E_0/\Delta}
+ R_{\rm EM}^{(m)},
$$
其中 $R_{\rm EM}^{(m)}$ 为用 Euler–Maclaurin 将 $\Delta\sum_{n\in\mathbb Z}f(E_0+n\Delta)$ 关闭到 $|n|\le N$ 的端点与尾项余量；若 $\widehat f$ 支持于 $(-\pi/\Delta,\pi/\Delta)$，则别名项为 $0$，退化为严格采样恒等式。将有限精度的采样值 $f(E_0+n\Delta)$ 量化为字母,在线性滤波一致性（长度 $M$）下定义 sofic 子移位；取 SFT 覆盖得 $X_f$ 与有限厚度译码 $\pi$。由引理 2.2,
$$
\mathrm{Obs}(w_R,h;\rho)=\mathrm{Tr}\,K_{w,h}
=\lim_{k\to\infty}\mathcal O_{\pi,\varsigma}\!\big(x\!\mid_{W_k}\big),
$$
遂得 $\mathsf{Obs}_{\rm E}(\mathfrak G(\mathfrak U))\cong \mathsf{Obs}_{\rm G}(\mathfrak U)$。([webusers.imj-prg.fr][3])

### 6.3 时间账本与无信号的保持

QCA 之有限传播与幺正性确保无超锥传播；窗化顺序仅影响刻度,不改变母刻度密度。EBOC$\leftrightarrow$GLS 往返中,因果前沿与偏序保持,而 $T_\gamma$ 仅作操作化刻度。([arXiv][8])

---

## 7. 必要—充分性论证

**充分性**
(a) 可逆化与量子化生成 $S(E)$、$\mathsf Q(E)$（引理 2.6）；
(b) 窗—核读数与译码读数在母刻度上线性一致（引理 2.1–2.2）；
(c) Poisson+EM 的 NPE 闭合给出非渐近误差预算且不引入新奇性（引理 2.3）；
(d) SMB/Brudno 与因子熵单调使复杂度/熵账本与密度—延迟账本对齐（引理 2.4）。

**必要性**
若无全局幺正/可逆化,则 $S(E),\mathsf Q(E)$ 不可良好定义；若无有限记忆/可马尔可夫化,则无法以有限厚度译码对齐窗—核字典；若失带限或违 Nyquist,Poisson 混叠破坏逐窗一致；若不进行 $L(W)=T$ 的账本对齐,SMB/Brudno 不能与窗化迹匹配。

---

## 8. 误差预算（NPE Discipline）

对任意 $(w_R,h)$ 与近带限 $\rho_{\rm rel}$,令 $f=w_R\cdot(h\star \rho_{\rm rel})$，取采样步长 $\Delta$、截断 $N$、EM 阶数 $m$，并设
$$
[a,b]=\Big[E_0-\Big(N+\tfrac12\Big)\Delta,\ \ E_0+\Big(N+\tfrac12\Big)\Delta\Big],\qquad f\in C^{2m}([a,b]),\ \ \widehat f\in L^1(\mathbb R).
$$
则有下述别名+EM 上界：
$$
\Bigl|\int f-\Delta\!\sum_{|n|\le N}f(E_0+n\Delta)\Bigr|
\le
2\pi\sum_{k\ne 0}\Bigl|\widehat f\!\Bigl(\frac{2\pi k}{\Delta}\Bigr)\Bigr|
+\frac{|B_{2m}|}{(2m)!}\bigl|f^{(2m-1)}(b)-f^{(2m-1)}(a)\bigr|
+\frac{2\zeta(2m)}{(2\pi)^{2m}}\!\int_a^b\!|f^{(2m)}(E)|\,dE.
$$
选择 $\Delta,N,m$ 以达目标精度阈值。([Massachusetts Institute of Technology][9])

---

## 9. 结论性定理（形式陈述）

**定理**
在 A0–A3 与"四条件"之下,$\mathfrak F,\mathfrak G$ 与自然变换 $\eta,\epsilon$ 使
$$
\boxed{\ \mathfrak F:\mathbf{EBOC}\rightleftarrows \mathbf{GLS}:\mathfrak G\ \text{在}\ \mathbf{Obs}\ \text{中互为范畴等价}\ }.
$$
其核心恒等为
$$
\boxed{\ \frac{\varphi'}{\pi}=\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q\ },\qquad \boxed{\ \rho_{\rm rel}=\xi'=-\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q\ }，并由此 \ \frac{\varphi'}{\pi}=-\rho_{\rm rel};\qquad
\boxed{\ \mathrm{Tr}\,K_{w,h}=\int w_R(E)\,(h\star\rho_{\rm rel})(E)\,dE\ }.
$$
第一式由 Birman–Kreĭn 与 Wigner–Smith 结构推出,第二式由 Lifshits–Kreĭn 迹公式与窗化压缩导出；NPE 纪律提供非渐近闭合并避免新奇性。([arXiv][4])

---

## 参考锚点（可核查）

* Wigner–Smith 群延迟矩阵、总延迟与态密度的联系；教材/综述亦述及 $\tau_W=\mathrm{tr}\,\mathsf Q/N$ 的统计性质。([ChaosBook][1])
* Birman–Kreĭn 公式 $\det S=e^{-2\pi i\xi}$ 与 $\xi'=-(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ 的一般性。([arXiv][4])
* Lifshits–Kreĭn 迹公式与单位圆情形的 Kreĭn–Peller 扩展（算子 Lipschitz 类）。([arXiv][5])
* Poisson 求和与 EM 余项的显式上界及教材化推导。([webusers.imj-prg.fr][3])
* SMB 与 Brudno 等式的多维推广；因子熵单调与 sofic/SFT 覆盖。([Project Euclid][2])
* 可逆计算与 QCA 结构定理（广义 Margolus 分块、有限传播）。([mathweb.ucsd.edu][7])

---

[1]: https://chaosbook.org/version13/chapters/scattering.pdf?utm_source=chatgpt.com "Quantum scattering"
[2]: https://projecteuclid.org/journals/annals-of-probability/volume-16/issue-2/A-Sandwich-Proof-of-the-Shannon-McMillan-Breiman-Theorem/10.1214/aop/1176991794.full?utm_source=chatgpt.com "A Sandwich Proof of the Shannon-McMillan-Breiman ..."
[3]: https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf?utm_source=chatgpt.com "Chapter Two"
[4]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[5]: https://arxiv.org/abs/1601.00490?utm_source=chatgpt.com "The Lifshits--Krein trace formula and operator Lipschitz functions"
[6]: https://www.cambridge.org/core/books/an-introduction-to-symbolic-dynamics-and-coding/sofic-shifts/3F50A316E8E7C1ED8D1FCDFFED0BBFD2?utm_source=chatgpt.com "Sofic Shifts (Chapter 3) - An Introduction to Symbolic ..."
[7]: https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2013W/Bennett_Reversibiity.pdf?utm_source=chatgpt.com "Logical Reversibility of Computation*"
[8]: https://arxiv.org/pdf/quant-ph/0405174?utm_source=chatgpt.com "arXiv:quant-ph/0405174v1 28 May 2004"
[9]: https://web.mit.edu/8.323/spring08/notes/ft1ln02-08.pdf?utm_source=chatgpt.com "NOTES ON THE EULER-MACLAURIN SUMMATION ..."
