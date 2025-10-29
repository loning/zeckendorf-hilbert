# S28. de Branges–Mellin 局部化算子的强型 Szegő–Widom 极限

Version: 1.8

**—— 对数行列式、二次型 $H^{1/2}$ 与有限阶 Euler–Maclaurin 的边界改正**

## 摘要（定性）

在 de Branges–Mellin 框架与"相位—密度"词典下，本文把 S27 的一阶迹公式（Weyl 型）推进为**强型 Szegő–Widom 极限**：对由符号 $a$ 与偶窗 $w_R$ 构成的局部化算子族 $T_{a,R}$，当尺度 $R\to\infty$ 时有

$$
\log\det\!\big(I+\lambda T_{a,R}\big)
= \int \!\log\!\big(1+\lambda a\, w_R\big)\,d\mu
+\tfrac12\,\mathcal Q_R\!\big(\log(1+\lambda a)\big) + o(1),
$$

其中 $d\mu=\frac{\varphi'}{\pi}\,dx$ 为相位体积测度，$M_R=\int w_R\,d\mu$，$\mathcal Q_R$ 为由窗化投影核诱导的二次型，并在相位坐标极限中收敛到**临界半阶能量** $H^{1/2}$。在"带限 + Nyquist"与**有限阶** Euler–Maclaurin（EM）纪律下，别名项消失，边界与伯努利层给出非渐近、可控的改正；全流程不引入新奇性并保持"极点 = 主尺度"。该结果与多窗/非平稳拼接、BN–Bregman 软化以及 de Branges–Kreĭn 规范系统的相位—密度刻度一致。本文的关键判据与证明步骤与强型 Szegő–Widom（Toeplitz/Wiener–Hopf）理论严格对齐。

---

## 0. 设定与记号（de Branges–Mellin 与相位—密度）

令 $E$ 为 Hermite–Biehler 整函数，$\mathcal H(E)$ 为对应的 de Branges 空间，核 $K$ 再生且在实轴上可写 $E(x)=|E(x)|e^{-i\varphi(x)}$。标准恒等式给出对角核

$$
K(x,x)=\frac{1}{\pi}\,\varphi'(x)\,|E(x)|^2,\qquad d\mu(x):=\frac{\varphi'(x)}{\pi}\,dx.
$$

相位函数 $\varphi$ 严增且 $E^\sharp/E=e^{2i\varphi}$。上述恒等式见 de Branges 文献与以相位标度写出的核公式（亦见 $\sin(\varphi(x)-\varphi(y))$-型归一式）。

**尺度与窗（强制设定）.** 设相位坐标 $u:=\varphi(x)/\pi$。取固定偶函数 $W\in L^\infty(\mathbb R)$ 满足 $0\le W\le 1$、$W(0)=1$，且 $\widehat W$ 紧支（带限）或 $W\in C_c^\infty$。定义随尺度的窗

$$
w_R(x):=W\!\big(u/R\big),\qquad M_R=\!\int w_R\,d\mu
=R\!\int_{\mathbb R}\!W(u)\,du+o(R)\to\infty.
$$

由 $W(0)=1$ 知在任意固定紧集上 $w_R\to 1$ 均匀成立。

**平均记号.** 对可积函数 $f$，定义随尺度的加权平均

$$
\langle f\rangle_{\mu,R}:=\frac{1}{M_R}\int f(x)\,w_R(x)\,d\mu(x),\qquad M_R=\int w_R\,d\mu.
$$

如不致混淆，可简记为 $\langle f\rangle_\mu$；所有平均均指上述 $R$ 依赖的加权平均。

**局部化算子与正则化行列式.** 给定**实值** $a\in L^\infty(\mathbb R)$ 与偶窗 $w_R\ge 0$（带限或指数衰减），定义

$$
T_{a,R}:=\int a(x)\,w_R(x)\ \frac{|K(\cdot,x)\rangle\langle K(\cdot,x)|}{K(x,x)}\,d\mu(x).
$$

当 $0\le a\le C$ 且 $w_R$ 有界紧支（或充分衰减），$T_{a,R}$ 为迹类；一般 $a$ 用 Carleman–Fredholm 正则化 $\det_2$ 定义 $\log\det(I+\lambda T_{a,R})$。关于 Fredholm/正则化行列式、迹级数展开与扰动理论的背景，详见文末"参考文献（选）"。

**行列式与可逆性约定.** 若 $T_{a,R}\in \mathfrak S_1$ 则取 Fredholm 行列式 $\det(I+\lambda T_{a,R})$；若 $T_{a,R}\in \mathfrak S_2\setminus \mathfrak S_1$ 则取 Carleman–Fredholm 行列式 $\det_2(I+\lambda T_{a,R})$。两者统一记为

$$
\mathrm{LDet}(I+\lambda T_{a,R}),
$$

且本文中出现的 $\log\det(I+\lambda T_{a,R})$ 一律理解为 $\log \mathrm{LDet}(I+\lambda T_{a,R})$。在 $\lambda\in\mathbb R$、$a$ 实值且 $\inf_x(1+\lambda a(x))>0$ 下，存在 $R_0$ 使对所有 $R\ge R_0$ 有 $-1\notin \lambda\,\sigma(T_{a,R})$（等价于 $I+\lambda T_{a,R}$ 可逆），从而 $\log$ 分支一致且良定。

**窗化核与相位标度.** 记规模 $M_R=\int w_R\,d\mu$，并设

$$
\Pi_R(x,y):=\int w_R(t)\,\frac{K(x,t)\,\overline{K(y,t)}}{\sqrt{K(x,x)K(y,y)}}\,d\mu(t).
$$

并约定 $0\le w_R\le 1$，从而 $\|\Pi_R\|\le 1$。$\Pi_R$ 为正算子核，**一般不是正交投影**。设相位坐标 $u=\varphi(x)/\pi$，定义带限正交投影核

$$
P_R^{\mathrm{BL}}(u,v):=\frac{\sin\!\big(\pi R(u-v)\big)}{\pi(u-v)}.
$$

设 $U:L^2(d\mu)\to L^2(du)$ 为保范同构 $(Uf)(u)=f(\varphi^{-1}(\pi u))$。当 $w_R(x)=\mathbf 1_{|u|\le R}$ 或其 $C^\infty$ 近似且 $R\to\infty$ 时，有

$$
\big\|\,U\Pi_R U^{-1}-P_R^{\mathrm{BL}}\,\big\|_{\mathfrak S_2}\xrightarrow[R\to\infty]{}0,\qquad
\operatorname{Tr}(\Pi_R-\Pi_R^{\,2})=O(1).
$$

因而"带限正交投影"对象与逼近意义均被固定。

在相位坐标 $u=\varphi(x)/\pi$ 中，$K$ 的局部极限与 Paley–Wiener/sine 核等价，从而 $\Pi_R$ 渐近为带宽与 $M_R$ 可比的带限投影核（de Branges–Paley–Wiener 的普适极限）。

---

## 1. 一阶主项（Szegő–Weyl 极限）

下文的 $\log\det(I+\lambda T_{a,R})$ 依"**行列式与可逆性约定**"解释。

**定理 28.1（主项极限）.** 取 $\lambda\in\mathbb R$，$a\in L^\infty(\mathbb R)$ 为**实值**，$0\le w_R\le1$，且 $\inf_x(1+\lambda a(x))>0$，从而 $h(x)=\log(1+\lambda a(x))$ 为实函数。并假设 $h\in L^\infty$ 且具最小正则性（如 $h\in C^{1,\alpha}$ 或 $h\in H^{1/2+\varepsilon}$）。若 $w_R$ 为偶窗并满足带限或充分衰减与有限阶 EM 换序纪律，则有

$$
\frac{1}{M_R}\,\log\det\!\big(I+\lambda T_{a,R}\big)
\ \longrightarrow\ \frac{1}{M_R}\int \log\!\big(1+\lambda a(x)w_R(x)\big)\,d\mu(x).
$$

*证明要点.* 设 $h=\log(1+\lambda a)$。用正则化行列式的**累积量**展开

$$
\log\det(I+\lambda T_{a,R})=\sum_{m\ge1}\frac{\kappa_m}{m!}.
$$

在 $0\le w_R\le 1$ 且满足**近投影估计**的假设下，有

$\displaystyle \kappa_1=\int \log\!\big(1+\lambda\,a(x)\,w_R(x)\big)\,d\mu(x)\,+\,o(1)$，

$\kappa_2=\mathcal Q_R(h)+o(1)$，

而 $\kappa_m=o(1)\ (m\ge3)$。故得主项与二阶结构。文中 $\langle\cdot\rangle_\mu$ 一律按"平均记号"定义，依赖于当前尺度 $R$ 与窗 $w_R$。这与强型 Szegő 的一阶结构一致（Toeplitz/Wiener–Hopf 的 $n\!\cdot\!\langle\log(1+\lambda a)\rangle$ 或区间长度 $\times$ 平均）。

---

## 2. 二阶修正（强型 Szegő–Widom）

定义对实函数 $h$ 的窗化二次型

$$
\mathcal Q_R(h):=\iint \frac{\big(h(x)-h(y)\big)^2}{2}\,|\Pi_R(x,y)|^2\,d\mu(x)\,d\mu(y).
$$

在相位坐标极限下，$\Pi_R$ 渐近为带限投影核 $\Pi^{\mathrm{BL}}$，从而

$$
\mathcal Q_R(h)\ \longrightarrow\ \mathcal Q(h):=\frac{1}{2\pi}\int_{\mathbb R} |\widehat{h\circ\varphi^{-1}}(\xi)|^2\,|\xi|\,d\xi,
$$

其中 $h\circ\varphi^{-1}$ 表示在相位坐标上的函数 $u\mapsto h(\varphi^{-1}(\pi u))$，$\xi$ 为其对应的傅里叶变量。

**归一化约定**：$\widehat f(\xi)=\int_{\mathbb R} f(u)\,e^{-i u\xi}\,du$。在此约定下，$\mathcal Q$ 与 $\dot H^{1/2}(\mathbb R)$ 的 Gagliardo 表达式常数一致。

即 $H^{1/2}$ 半范数（Fourier 型表述）。这与强型 Szegő 二项常数 $\sum_{k\ge1}k\,|h_k|^2$ 的等价在傅里叶侧完全一致。

**定理 28.2（强型 Szegő–Widom 极限）.** 取 $\lambda\in\mathbb R$ 且 $\inf_x(1+\lambda a(x))>0$，于是 $h(x)=\log(1+\lambda a(x))$ 为实函数。设 $a\in L^\infty$ 且 $h:=\log(1+\lambda a)\in C^{1,\alpha}\cap L^\infty$（某 $\alpha>0$），$w_R$ 为带限偶窗并满足 Nyquist 与有限阶 EM 纪律，且采用"**尺度与窗（强制设定）**"与"**窗化核与相位标度**"中的设定，则

$$
\log\det\!\big(I+\lambda T_{a,R}\big)
=\int \log(1+\lambda a\,w_R)\,d\mu+\frac12\,\mathcal Q_R\!\big(h\big)+o(1).
$$

若 $w_R\to 1$ 局部一致，则 $\mathcal Q_R\to\mathcal Q$，且

$$
\log\det\!\big(I+\lambda T_{a,R}\big)
= M_R\,\Big\langle \log\!\big(1+\lambda a\big)\Big\rangle_{\mu,R}
+\frac12\,\mathcal Q(h)+o(1),
$$

其中 $h=\log(1+\lambda a)$。当 $w_R$ 为硬窗指示时，上式主项亦等于 $\int_{w_R\equiv1}\log(1+\lambda a)\,d\mu$。

*证明思路.*（i）**Toeplitz/Wiener–Hopf 对齐**：在相位坐标中，$T_{a,R}$ 与截断投影—乘法—投影 $P_R\,M_a\,P_R$ 相差 $o_{\mathfrak S_2}(M_R^{1/2})$。对 $P_R\,M_a\,P_R$，经典 Wiener–Hopf 两项迹/行列式渐近与强型 Szegő（圆/直线）给出与上式等价的结构；二项常数即 $H^{1/2}$ 能量。（ii）**cumulant 公式**：以 $\Pi_R$ 为核的投影近似，$\log\det(I+\lambda T)=\sum_{m\ge1}\kappa_m/m!$。投影/近投影核的高阶累积量 $\kappa_m\ (m\ge3)$ 为 $o(1)$，$\kappa_2$ 由 $\|\Pi_R\|^2$ 表示并经"换元—插值"化为 $\mathcal Q_R(h)$。这一做法与确定性点过程（DPP）中线性统计方差的 $H^{1/2}$ 等价结论一致。（iii）**$H^{1/2}$ 标准化**：用分数 Sobolev 的傅里叶表述 $\int |\hat f(\xi)|^2|\xi|\,d\xi$ 与双重积分表述互证，得到极限二次型。

---

## 3. 有限阶 Euler–Maclaurin（EM）与数值边界

设 $\mathsf{tr}_{\Delta,M_{\mathrm{EM}},T}(\phi):=\Delta\sum_{|k|\le T/\Delta}\phi(k\Delta)$ 近似 $\int\phi$。对谱函数 $\phi_{a,\lambda,R}(t)=\log(1+\lambda t)$ 与 $\phi^2$ 有

$$
\big|\operatorname{Tr}\,\phi(T_{a,R})-\mathsf{tr}_{\Delta,M_{\mathrm{EM}},T}\big(\phi\circ\mathcal S_R\big)\big|
\ \le\ \underbrace{\mathrm{alias}}_{=0\ \text{(带限+Nyquist)}}+\underbrace{\mathrm{EM\ layer}}_{\text{$(M_{\mathrm{EM}})$ 阶伯努利}}+\underbrace{\mathrm{tail}}_{\text{截断}},
$$

其中 $\mathcal S_R$ 为相位坐标下被采样的 integrand。带限 + 采样步长满足 Nyquist 时别名项严格为零（见文末"参考文献（选）"），其余两项由有限阶 EM 给出非渐近界，整体为 $o(M_R)$。

**Nyquist 设定**：设相位坐标下被采样函数的频域支集包含于 $[-\Omega,\Omega]$，取步长 $\Delta\le (\pi\Omega)^{-1}$（或等价的 $\Delta<1/(2\Omega)$ 归一化），则别名项严格为 $0$。

---

## 4. 退化与奇点（Fisher–Hartwig 型）

若 $h=\log(1+\lambda a)$ 出现对数/幂次奇点（如触及分支 $-1/\lambda$ 或近零），二阶上方可能出现附加 $\gamma\log M_R$ 的边缘指数，系数由相位坐标中的局部指数与跳跃决定。Toeplitz/Hankel 强化结论与 Riemann–Hilbert 技术给出该项之精确系数判据；在本文假设 $h\in C^{1,\alpha}$ 下**无此项**。

---

## 5. 多窗与非平稳拼接

取偶多窗 $W=\{w_R^{(\ell)}\}_{\ell=1}^K$，令 $T_{a,W}:=\sum_\ell T_{a,R}^{(\ell)}$。若 $\sum_\ell w_R^{(\ell)}\to1$ 局部一致，且存在常数 $C$ 使得所有 $\ell\neq m$ 满足

$$
\big\|\,\Pi_R^{(\ell)}\Pi_R^{(m)}\,\big\|_{\mathfrak S_2}\le C\,o(1)\qquad(R\to\infty),
$$

（即多窗成 Parseval 紧帧或**近正交**，交叉项在 $\mathfrak S_2$ 可忽略），则有

$$
\log\det\big(I+\lambda T_{a,W}\big)
=\int \log(1+\lambda a)\,d\mu+\tfrac12\,\mathcal Q\!\big(\log(1+\lambda a)\big)+o(1).
$$

非 Parseval 情形以帧乘子 $\mathcal S_W$ 作符号等价替换后同理成立。参见帧理论与非平稳 Gabor 框架的乘子稳定性。

---

## 6. 软化与稳定（BN–Bregman 视角）

以熵/ KL 罚在符号端对 $h=\log(1+\lambda a)$ 作 BN–Bregman 软化，得到极小值与极小元的李普希茨稳定；当软化参数 $\tau\downarrow0$ 时，$\log\det$ 极限与二次型不变。有限阶 EM 的三分解误差（别名/伯努利层/尾项）以 Pinsker 链传递为 $\log\det$ 的非渐近上界（此节为方法性注记，与上文二阶主结论相容）。

---

## 7. 直接推论

**推论 28.3（自由能/互信息解释）.** 当 $0\le a\le1$ 时，$\log\det(I+\lambda T_{a,R})$ 可解释为一类"自由能/互信息"泛函：主项由相位体积平均贡献，二阶由 $H^{1/2}$ 能量给出**涨落惩罚**，与 Fisher–Bregman 结构相符（与强型 Szegő 的"常数项"角色一致）。

---

## 8. 适用范围与失效边界

1. **禁止无限阶 EM**：把 EM 当无穷级会制造伪奇点并破坏二次项可控性；本文仅用**有限阶**，余项整/全纯。
2. **符号退化**：若 $h\notin C^{1,\alpha}$ 或触及分支，出现 Fisher–Hartwig 型 $\log M_R$；本文排除。
3. **多窗非 Parseval**：以帧乘子配平符号；Parseval 近似下误差 $o(1)$。
4. **异常相位尺度**：若 $\varphi'$ 不正或非局部可积，则相位坐标退化，需回退到一般 RKHS/规范系统的局部谱逼近。

---

## 9. 可检清单（最小充分条件）

* **相位—密度**：核对 $K(x,x)=\frac{1}{\pi}\varphi'(x)|E(x)|^2>0$，取 $d\mu=\frac{\varphi'}{\pi}dx$。
* **算子可积/正则化**：$T_{a,R}$ 迹类或以 $\det_2$ 合理定义 $\log\det(I+\lambda T_{a,R})$。
* **一阶极限**：$\displaystyle \frac{1}{M_R}\log\det(I+\lambda T_{a,R})\ \to\ \frac{1}{M_R}\int \log(1+\lambda a\,w_R)\,d\mu$；在硬窗或 $w_R\to1$ 局部一致下，上式等于 $\langle \log(1+\lambda a)\rangle_{\mu,R}$。
* **二阶极限**：$\mathcal Q_R(h)\to \frac{1}{2\pi}\!\int |\widehat{h\circ\varphi^{-1}}(\xi)|^2|\xi|\,d\xi$。
* **EM 纪律**：带限+Nyquist $\Rightarrow$ 别名 $=0$；伯努利层与尾项按已选阶 $M_{\mathrm{EM}}$ 给出非渐近界。
* **多窗/非平稳**：Parseval 紧帧下多窗求和保持二次型极限；非 Parseval 以帧乘子修正，**误差为 $o(1)$**。
* **奇性保持**：窗化与有限阶换序不增工作条带内奇性与极阶。
* **核极限**：相位标度下核的局部极限与 Paley–Wiener/sine 核一致（普适性）。

---

## 参考文献（选）

* de Branges 空间、相位—密度与核：Antezana–Marzo–Olsen，给出 $K(x,x)=\frac{1}{\pi}\varphi'(x)|E(x)|^2$ 与相位公式。
* 强型 Szegő 与 Widom：百科综述与 Widom 的 Wiener–Hopf 痕迹/两项式结果。([encyclopediaofmath.org][1])
* Fisher–Hartwig：Deift–Its–Krasovsky 的 Annals 与 MSRI 章节。([数学年刊][8])
* 分数 Sobolev：$\dot H^{1/2}$ 的 Fourier/Gagliardo 等价（Di Nezza–Palatucci–Valdinoci）。([arXiv][4])
* DPP 线性统计与 $H^{1/2}$ 方差（Johansson；Soshnikov）。([Project Euclid][6])
* Fredholm 与正则化行列式：Bornemann（数值/理论），Simon（Trace Ideals）。([arXiv][2])
* Nyquist–Shannon 与别名消失（Jerri 综述）。([Buzsaki Lab][7])
* de Branges–Paley–Wiener 普适核极限（Lubinsky）。([lubinsky.math.gatech.edu][3])
* 帧与非平稳拼接（Christensen；Balazs–Dörfler 等）。([大里博物馆][9])

---

### 附：与经典强型 Szegő–Widom 的一致性说明（框架对齐）

在圆或实线的 Toeplitz/Wiener–Hopf 情形，强型 Szegő给出 $\log\det T_n(e^{h})=n\,h_0+\sum_{k\ge1}k\,h_k h_{-k}+o(1)$。我们在 de Branges 相位坐标中得到的二次型极限 $\frac12\,\mathcal Q(h)=\frac{1}{2\pi}\int |\widehat{h\circ\varphi^{-1}}|^2|\xi|\,d\xi$ 与 $\sum_{k\ge1}k\,|h_k|^2$ 等价（Fourier 权 $|\xi|$），从而二阶常数完全一致；这与 Widom 的 Wiener–Hopf 两项式在直线侧的陈述相匹配，亦与 DPP 线性统计的 $H^{1/2}$ 方差普适律一致。

---

**结语.** 本文在 de Branges–Mellin 的相位—密度刻度下建立了局部化算子对数行列式的**强型 Szegő–Widom 极限**：主项为符号的相位体积平均，二阶为 $H^{1/2}$ 能量；在带限 + Nyquist 与**有限阶** EM 纪律中，边界层次可非渐近量化，并与 Toeplitz/Wiener–Hopf 的经典二项式严格对齐，且在多窗/非平稳拼接与 BN–Bregman 软化下保持结构稳定。以上判据与步骤为后续的数值实现（Bornemann 型）与更高阶修正（含 Fisher–Hartwig）提供直接的、可检的路径。

[1]: https://encyclopediaofmath.org/wiki/Szeg%C3%B6_limit_theorems?utm_source=chatgpt.com "Szegö limit theorems"
[2]: https://arxiv.org/pdf/0804.2543?utm_source=chatgpt.com "Numerical Evaluation of Fredholm Determinants"
[3]: https://lubinsky.math.gatech.edu/Research%20papers/NahariyaProcAug2009.pdf?utm_source=chatgpt.com "an operator associated with de branges spaces and ..."
[4]: https://arxiv.org/pdf/1104.4345?utm_source=chatgpt.com "Hitchhiker's guide to the fractional Sobolev spaces"
[5]: https://link.springer.com/chapter/10.1007/978-3-0348-9144-8_46?utm_source=chatgpt.com "On Wiener-Hopf Determinants"
[6]: https://projecteuclid.org/journals/duke-mathematical-journal/volume-91/issue-1/On-fluctuations-of-eigenvalues-of-random-Hermitian-matrices/10.1215/S0012-7094-98-09108-6.full?utm_source=chatgpt.com "On fluctuations of eigenvalues of random Hermitian matrices"
[7]: https://buzsakilab.nyumc.org/datasets/PatelJ/_extra/Histology/jp-usb-1-data/data%20analysis/Data%20Analysis/Jerri_SamplingTheorem_Review_IEEE1977.pdf?utm_source=chatgpt.com "The Shannon Sampling Theorem-Its Various Extensions ..."
[8]: https://annals.math.princeton.edu/wp-content/uploads/annals-v174-n2-p12-p.pdf?utm_source=chatgpt.com "Asymptotics of Toeplitz, Hankel, and ..."
[9]: https://dlib.scu.ac.ir/bitstream/Hannan/310023/2/9783319256139.pdf?utm_source=chatgpt.com "An Introduction to Frames and Riesz Bases"
