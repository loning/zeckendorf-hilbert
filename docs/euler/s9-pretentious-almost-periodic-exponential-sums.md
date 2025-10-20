# S9. Pretentious—几乎周期—指数和

**—— 近零复访率、Pretentious 距离与方向化指数和的非渐近上界**

## 摘要

建立 Pretentious 距离、几乎周期信号与方向化指数和三者的统一框架：以母映射的一维切片为核心对象，给出非 Pretentious 区的统一上界与 Pretentious 区的大值（几乎周期）窗口；在有限观测窗内，结合 Nyquist/Poisson 与有限阶 Euler–Maclaurin（"伯努利层"）给出指数和的小球概率与近零复访率的非渐近控制，并以信息量刻度刻画"典型幅度"。全文的假设尽可能以可检条件表达，并与 S2 的横截几何、S4 的有限阶 EM、S5 的方向亚纯化、S6 的信息刻度、S7 的 $L$-函数接口、S8 的离散一致逼近逐一拼接。

---

## 0. 记号与框架（与 S1–S8 对齐）

设 $f:\mathbb N\to\mathbb C$ 为乘法函数且 $|f(n)|\le 1$。对 $s=\sigma+it$（$\sigma>1$）定义母映射切片（Dirichlet 级数与其截断）：

$$
F_f(s):=\sum_{n\ge1}\frac{f(n)}{n^{s}},\qquad
P_f(X;\sigma,t):=\sum_{n\le X}\frac{f(n)}{n^{\sigma+it}}.
$$

这是沿方向 $(\theta,\rho)=(-t,\sigma)$ 在离散谱 $\beta_n=-\log n$ 上的一元切片（S5 的"方向化"）。

**Pretentious 模型与距离**。设模型族

$$
\mathcal G:=\bigl\{g(n)=\chi(n)\,n^{i\tau}:\ \chi\ \text{狄利克雷特征},\ \tau\in\mathbb R\bigr\}.
$$

对 $X\ge2$ 定义 Pretentious 距离

$$
\mathbb D(f,g;X)^2:=\sum_{p\le X}\frac{1-\Re\!\bigl(f(p)\,\overline{g(p)}\bigr)}{p}.
$$

记

$$
\mathbb D_X(f):=\inf_{\chi,\tau}\mathbb D\bigl(f,\chi(\cdot)\,(\cdot)^{i\tau};X\bigr).
$$

**信息量刻度（S6）**。取

$$
p_n(\sigma):=\frac{n^{-\sigma}}{\zeta(\sigma)}\qquad(\sigma>1),
$$

定义参与率 $N_2(\sigma):=\Bigl(\sum_{n\ge1}p_n(\sigma)^2\Bigr)^{-1}=\zeta(\sigma)^2/\zeta(2\sigma)$。典型能量尺度

$$
A_\sigma(X):=\Bigl(\sum_{n\le X}n^{-2\sigma}\Bigr)^{1/2},\qquad A_\sigma(X)\nearrow \zeta(2\sigma)^{1/2},\ \ A_\sigma(X)\le \zeta(2\sigma)^{1/2}.
$$

**有限阶 EM 与 Nyquist/Poisson（S4+S8）**。全文所有"和–积/和–积–积分"换序仅使用**有限阶** Euler–Maclaurin（伯努利层），其余项在 $s$ 上整/全纯且可显式上界；频域交叉项以 Nyquist/Poisson 别名控制。为便于引用，列出本篇的**可检正则条件**：

* **C9.1**：固定 $\sigma>1$。涉及换序与边界项的所有操作满足 S1/S4 的管域与有限阶 EM 约束。
* **C9.2**（观测窗与截断）：窗 $[-T,T]$ 与截断 $X$ 满足下述之一：

  (a) **近对角计数/误差并入**：对满足 $|T(\log m-\log n)|<\Omega$ 的近零频对 $(m,n\le X)$，统一作为**受控误差项**按 A.2 的最后一项处理（或给出其**局部计数/上界**)；不要求全体 $m\ne n$ 的全局最小分离；或

  (b) **平滑窗抑制**：取 $W\in C^K_c(\mathbb R)$（$K$ 足够大）置换指示窗，存在 $\Omega>0$ 与 $\delta\in(0,1)$ 使 $|\widehat W(\xi)|\le \delta$（对所有 $|\xi|\ge \Omega$）。能量估计时仅对满足 $|T(\log m-\log n)|\ge \Omega$ 的交叉项使用该尾部小量；其余近零频项按 (a) 的近对角误差并入处理（见 A.2/A.2′）。
* **C9.3**：伯努利层阶数 $K$ 至少覆盖所用导数与端点项，余项由 S4 的整函数性与 S8 的窗尾上界控制。

---

## 1. Pretentious 预备：不变性与最拟合参数

### 引理 9.0（不变性与单调性）

(1) $\mathbb D(f,\chi(\cdot)\,(\cdot)^{i\tau};X)=\mathbb D\bigl(f\,\overline{\chi}(\cdot)\,(\cdot)^{-i\tau},1;X\bigr)$。

(2) $X\mapsto \mathbb D_X(f)$ 单调非减。

(3) 若 $(\chi^\star,\tau^\star)$ 令 $\mathbb D_X(f)$ 取到下确界，则称之为**最拟合参数**，并称 $f$ 在尺度 $X$ 上为 **Pretentious**（$\mathbb D_X(f)$ 小）或**非 Pretentious**（$\mathbb D_X(f)$ 大）。

**证明**。直接由定义与欧拉素因子分离得到。∎

**σ-加权 Pretentious 距离（本篇用）**。固定 $\sigma>1$ 与 $t\in\mathbb R$，定义

$$
\mathbb D_{\sigma,X}(f;t)^2:=\inf_{\chi,\tau}\sum_{p\le X}\frac{1-\Re\!\bigl(f(p)\,\overline{\chi(p)}\,p^{-i(t+\tau)}\bigr)}{p^{\sigma}}.
$$

（记号关系说明）对固定 $\sigma>1$ 与任意 $t$，有
$$
\mathbb D_{\sigma,X}(f;t)\ \le\ \mathbb D_X(f),
$$
因为 $p^{-\sigma}\le p^{-1}$。故以 $\mathbb D_X(f)\le D_0$ 的 Pretentious 假设强于以 $\mathbb D_{\sigma,X}$ 表述的版本，与定理 9.1 的使用相容。

---

## 2. 非 Pretentious 区的统一上界（Halasz–Pretentious 型）

下述定理给出对**截断指数和**的非渐近上界；其振幅尺度与 $\sum_{n\le X}n^{-\sigma}\sim \zeta(\sigma)$ 同阶，误差仅由有限阶 EM 与窗尾贡献。

### 定理 9.1（非 Pretentious 上界，$\sigma>1$ 固定）

存在仅依赖 $\sigma$ 的常数 $C_\sigma,c_\sigma,\eta_\sigma>0$，对任意 $X\ge2$、$t\in\mathbb R$，有

$$
\bigl|P_f(X;\sigma,t)\bigr|
\ \le\ C_\sigma\Bigl(\sum_{n\le X}n^{-\sigma}\Bigr)\exp\!\bigl(-c_\sigma\,\mathbb D_{\sigma,X}(f;t)^2\bigr)\ +\ C_\sigma\,X^{1-\sigma}.
\tag{9.1}
$$

**证明（纲要）**。先用硬截断—全级数桥（由尾和估计或 A.1 的有限阶 EM）得
$$
|P_f(X;\sigma,t)|\ \le\ |F_f(\sigma+it)|\ +\ O_\sigma(X^{1-\sigma}).
$$
对任意使 $\mathbb D_{\sigma,X}(f;t)$ 近取下确界的 $g(n)=\chi(n)\,n^{i\tau}\in\mathcal G$，由附录 A.4（欧拉因子比较，吸收 $p>X$ 的贡献于 $O(1)$）得到
$$
|F_f(\sigma+it)|\ \le\ C_\sigma\,\exp\!\Big(-c_\sigma\,\mathbb D_{\sigma,X}(f;t)^2\Big)\,|F_g(\sigma+it)|.
$$
再以
$$
|F_g(\sigma+it)|\ \le\ |P_g(X;\sigma,t)|\ +\ O_\sigma(X^{1-\sigma})\ \le\ \sum_{n\le X}n^{-\sigma}\ +\ O_\sigma(X^{1-\sigma}),
$$
合并即得（9.1）。∎

**注 2.1**。当 $f$ 来源于 $L$-函数欧拉积（S7），可借助完成函数的 $\Gamma/\pi$ 正规化（S3）获得更细的垂线增长配平；这仅改变常数与 $\sigma$-权重的具体形状，不改变“指数衰减/几乎周期/小球概率”三类结论的结构。

---

## 3. Pretentious 区的几乎周期与大值窗口

在 Pretentious 区，$f$ 与某模型 $g(n)=\chi^\star(n)\,n^{i\tau^\star}$ 在素数端相干，导致 $t\approx -\tau^\star$ 的**大值窗口**与**几乎周期**现象。

### 定理 9.2（Pretentious 大值窗口）

固定 $\sigma>1$。若存在 $X\ge2$、$(\chi^\star,\tau^\star)$ 使 $\mathbb D\bigl(f,\chi^\star(\cdot)\,(\cdot)^{i\tau^\star};X\bigr)\le D_0$，并且 C9.2 的 Nyquist 条件对 $|t+\tau^\star|\le T$ 成立，则存在常数 $c_\sigma,C_\sigma>0$ 与集合 $\mathcal T_{\mathrm{big}}\subset[-T,T]$（测度 $\ge c_\sigma T$），使

（括注：由 $\mathbb D_{\sigma,X}(f;t)\le \mathbb D_X(f)$（$\sigma>1$）知，此 Pretentious 假设强于定理 9.1 使用的 $\mathbb D_{\sigma,X}$ 版本。）

$$
\bigl|P_f(X;\sigma,t)\bigr|\ \ge\ c_\sigma\,A_\sigma(X)\,e^{-C_\sigma D_0^2}\qquad (t\in\mathcal T_{\mathrm{big}}).
$$

**证明（纲要）**。不必分解 $P_f=P_g+E$ 做点态误差。先对模型 $g(n)=\chi^\star(n)\,n^{i\tau^\star}$ 用 A.2/A.2′ 与 Paley–Zygmund 得到以 $t\approx-\tau^\star$ 为中心的**大值集合**；然后在同窗 $|t+\tau^\star|\le T$ 内使用**引理 A.5（窗内 $L^2$ 比较）**：
$$
\int_{\mathbb R} W\!\Big(\tfrac{t}{T}\Big)\,\big|P_f(X;\sigma,t)-P_g(X;\sigma,t)\big|^2 dt\ \le\ C_\sigma\,e^{-c_\sigma D_0^2}\,T\,A_\sigma(X)^2,
$$
其中 $D_0$ 为 Pretentious 距离上界，$W$ 来自 C9.2(b)。由此将 $P_g$ 的大值通过 $L^2$ 误差**稳健转移**到 $P_f$，得到窗内正比例的大值集合，其阈值为 $c_\sigma A_\sigma(X)\,e^{-C_\sigma D_0^2}$。上述阈值校正亦可由附录 A.4 的欧拉因子比较得到等价表述。∎

**注 3.1**。当 $f=\chi$ 或 $f(n)=\chi(n)\,n^{i\tau}$ 时为严格几乎周期；一般 Pretentious 情形等价于在此基础上的有界扰动。

---

## 4. 小球概率与近零复访率（有限窗，非渐近）

对有限窗 $[-T,T]$ 与截断多项式 $P_f(X;\sigma,t)$，定义"$\varepsilon$-小球"集合

$$
\mathcal Z_\varepsilon:=\Bigl\{t\in[-T,T]:\ |P_f(X;\sigma,t)|\le \varepsilon\,A_\sigma(X)\Bigr\}.
$$

为便于引用，记窗域下界距离
$$
\mathbb D^{\star}_{\sigma,X}(f;T):=\inf_{|t|\le T}\ \mathbb D_{\sigma,X}(f;t).
$$

### 定理 9.3（小球上界：正交 + Pretentious 稀释）

在 C9.2 下，存在常数 $C_{\sigma,\Omega},c_\sigma>0$ 使

$$
\operatorname{meas}\bigl(\mathcal Z_\varepsilon\bigr)\ \le\ C_{\sigma,\Omega}\,\Bigl(\varepsilon+\bigl(1-e^{-c_\sigma\,\bigl(\mathbb D^{\star}_{\sigma,X}(f;T)\bigr)^2}\bigr)\Bigr)\,T.
\tag{9.2}
$$

**证明（纲要）**。记 $a_n=f(n)n^{-\sigma}$。在 C9.2(b) 下，采用 A.2 的加窗能量恒等式：
$$
\int_{\mathbb R} W\!\Bigl(\frac{t}{T}\Bigr)\,\bigl|P_f(X;\sigma,t)\bigr|^2 dt
=T\!\!\sum_{m,n\le X}\! a_m\overline{a_n}\,\widehat W\!\bigl(T(\log m-\log n)\bigr).
$$
取 $W\in C_c^K$ 且 $W\ge c\,\mathbf{1}_{[-1,1]}$，则
$$
\int_{-T}^{T}\!|P_f|^2 dt\ \le\ c^{-1}\!\int_{\mathbb R}\! W\!\Bigl(\frac{t}{T}\Bigr)\,|P_f|^2 dt.
$$
交叉项在 $|T(\log m-\log n)|\ge\Omega$ 处由 $|\widehat W|$ 的尾部小量吸收（A.2），其余近零频项并入误差或用 C9.2(a) 处理。由此配合 A.2′ 与 Paley–Zygmund，得 $\operatorname{meas}\{t:\ |P_f|\le \varepsilon A_\sigma(X)\}\ll \varepsilon\, T$。另一方面，由（9.1）知对任意 $t$ 有统一阈值控制因子 $\exp\{-c_\sigma\,\mathbb D_{\sigma,X}(f;t)^2\}$；取窗内下确界 $\mathbb D^{\star}_{\sigma,X}(f;T)$ 得到 $e^{-c_\sigma(\mathbb D^{\star}_{\sigma,X}(f;T))^2}$ 的阈值修正。将其与前述能量—Paley–Zygmund 链接，得到（9.2）的 $\varepsilon+$ Pretentious 稀释结构。∎

### 推论 9.4（近零复访率）

在 C9.2 下，单位时间内 $P_f$ 落入相对半径 $\varepsilon$ 的小球的复访率 $\ll \varepsilon+\bigl(1-e^{-c_\sigma(\mathbb D^{\star}_{\sigma,X}(f;T))^2}\bigr)$。

其中隐常数仅依赖于 $(\sigma,\Omega)$ 与窗参数，不依赖 $T,X$。

---

## 5. 信息刻度与"典型幅度"

### 定理 9.5（信息刻度控制典型幅度）

在 C9.2 下，

$$
\frac{1}{2T}\int_{-T}^{T}\Bigl|\sum_{n\le X}\frac{f(n)}{n^{\sigma+it}}\Bigr|^2dt\ \asymp\ \sum_{n\le X}n^{-2\sigma}=A_\sigma(X)^2.
$$

因此"典型幅度"满足

$$
A_\sigma(X)=\Bigl(\sum_{n\le X}n^{-2\sigma}\Bigr)^{1/2}.
$$

进一步地，有统一上界与极限等式

$$
A_\sigma(X)\ \le\ \frac{\zeta(\sigma)}{\sqrt{N_2(\sigma)}}=\zeta(2\sigma)^{1/2},\qquad
\lim_{X\to\infty}A_\sigma(X)=\frac{\zeta(\sigma)}{\sqrt{N_2(\sigma)}}=\zeta(2\sigma)^{1/2}.
$$

这与定理 9.3 的 $\varepsilon$ 量级相容（有限窗能量由 $A_\sigma(X)^2$ 给出，Pretentious 稀释项另行单独计入）。

---

## 6. 与零集几何的一致性（S2 接口）

在 S2 的二项闭合局部，主导两项满足"幅度平衡 + 相位对径"的横截方程，零集在 $(\theta,\rho)$ 空间为余维 $2$ 的实解析流形；在一维 $t$-切片上给出离散且通常简单的零。定理 9.3 的频率分离/非退化前提正是该横截非退化性的可检替身：**Pretentious 稀释**将"稠密小值"排至 $e^{-c_\sigma\,(\mathbb D^{\star}_{\sigma,X}(f;T))^2}$ 级，**几乎周期窗口**在 Pretentious 端提供稳定大值，与零集局部结构兼容。

---

## 7. 边界族与反例（失效原因标注）

* **R9.1（严重别名）**：若 C9.2 失败，交叉能量不可忽略，小球估计可能偏大；需缩短窗长或采用高阶平滑窗抑制别名（S8）。
* **R9.2（无限伯努利层）**：误将 EM 作为无穷级数破坏一致可和，余项丧失整性，从而（9.1）–（9.2）的误差预算不可控；必须坚持**有限阶**。
* **R9.3（极端 Pretentious）**：$\mathbb D_X(f)$ 极小且 $f$ 几乎逐项匹配某 $g$ 时，小球概率以 $\varepsilon^2$ 主导，且在 $t\approx -\tau^\star$ 的邻域出现稳定大值平台（定理 9.2）。
* **R9.4（方向退化）**：若大量 $m\ne n$ 使 $\log m\approx\log n$（尺度退化），可能产生"零簇"；需以 S2 的退化分支处理或改用平滑窗以增大有效分离。

---

## 8. 统一"可检清单"（本篇最小充分条件）

1. **竖条与管域**：固定 $\sigma>1$，一切换序与边界仅用**有限阶 EM**（S4），余项整/全纯。
2. **Pretentious 距离**：计算 $\mathbb D_{\sigma,X}(f;t)$（用于（9.1））与 $\mathbb D_X(f)$（用于定理 9.2 的中心频率识别）。若 $\displaystyle \inf_{|t|\le T}\mathbb D_{\sigma,X}(f;t)\ge D$，则由（9.1）在整个窗内给出指数衰减；若 $\mathbb D_X(f)\le D_0$，则进入定理 9.2 的大值窗口情形（取 $t\approx-\tau^\star$）。
3. **Nyquist/Poisson**：验证 C9.2 的频率分离或平滑窗抑制；否则先行窗化或调整 $X,T$。
4. **信息刻度**：以 $A_\sigma(X)$ 与 $N_2(\sigma)$ 估算典型幅度与小球阈值，并与 $e^{-c_\sigma(\mathbb D^{\star}_{\sigma,X}(f;T))^2}$ 项合并（定理 9.3）。
5. **几何一致性**：在局部两项主导区核对 S2 的横截非退化；排除方向退化与零簇。
6. **完成函数（按需）**：当 $f$ 来自 $L$-函数欧拉积，使用 S3/S7 的 $\Gamma/\pi$ 正规化与显式公式选择试验核，改善垂线配平，不改变（9.1）–（9.2）的结构。

---

## 9. 与其它篇章的接口

* **↔ S2（零集几何）**：二项闭合—横截提供局部非退化与频率分离的几何解释。
* **↔ S4（有限阶 EM）**：保证端点/导数项仅作整函数修正，"极点=主尺度"不被误用至截断误差。
* **↔ S5（方向亚纯化）**：大尺度结构（极点/增长）由主尺度决定，小尺度窗内波动由 Pretentious vs 非 Pretentious 控制。
* **↔ S6（信息刻度）**：参与率 $N_2(\sigma)$ 与典型幅度 $A_\sigma(X)$ 一致进入小球与复访率。
* **↔ S7（$L$-函数接口）**：Pretentious 小值对应素数端相干不足；显式公式的谱—素数对偶可用于定向窗选择。
* **↔ S8（离散一致逼近）**：小球与复访率依赖 Nyquist/Poisson 与有限阶 EM 的误差三分解；Prony/矩方法用于数值检验几乎周期窗口与 Pretentious 稀释。

---

## 附录 A：技术引理与标准工具

### A.1（伯努利层版 EM）

设 $f\in C^{K}[1,\infty)$ 且适合的衰减与端点正则，则

$$
\sum_{n\le X}f(n)=\int_{1}^{X}f(x)\,dx+\frac{f(1)+f(X)}{2}
+\sum_{k=1}^{K-1}\frac{B_{2k}}{(2k)!}\bigl(f^{(2k-1)}(X)-f^{(2k-1)}(1)\bigr)+R_K,
$$

其中 $R_K$ 在参数 $s$ 上整/全纯（当 $f(\cdot;s)$ 全纯依赖 $s$）且 $|R_K|\ll_K \int_{1}^{X}|f^{(K)}(x)|\,dx$。

### A.2（平滑窗能量恒等式）

在本节固定傅里叶规范 $\widehat W(\xi):=\int_{\mathbb R}e^{-i\xi t}W(t)\,dt$。

（说明）本节使用**不含 $2\pi$** 的傅里叶规范；下式中的**$T$ 缩放因子**来自变量代换 $u=t/T$。

取 $W\in C_c^K(\mathbb R)$；记

$$
\mathcal I:=\int_{\mathbb R}\!W\!\Bigl(\frac{t}{T}\Bigr)\,\Bigl|\sum_{n\le X}a_n\,e^{-it\log n}\Bigr|^2 dt
:=T\sum_{m,n\le X}a_m\overline{a_n}\,\widehat W\!\bigl(T(\log m-\log n)\bigr).
$$

若存在 $\Omega>0,\delta\in(0,1)$ 使 $|\widehat W(\xi)|\le\delta$（对所有 $|\xi|\ge\Omega$），则
$$
\mathcal I
=T\widehat W(0)\sum_{n\le X}|a_n|^2
+O\!\Bigl(\delta T\sum_{n\le X}|a_n|^2\Bigr)
+O\!\Bigl(\!\!\sum_{\substack{m\ne n\\ |T(\log m-\log n)|<\Omega}}\!\!|a_m a_n|\Bigr).
$$
近对角项按 C9.2(a) 或并入误差处理；A.2′ 的四次能量同理以 $\Omega,\delta$ 吸收远离零频的四重交叉项。

### A.2′（平滑窗四次能量上界）

取与 A.2 同假设的 $W\in C_c^K(\mathbb R)$；记

$$
\mathcal I_4:=\int_{\mathbb R}\!W\!\Bigl(\frac{t}{T}\Bigr)\,\Bigl|\sum_{n\le X}a_n\,e^{-it\log n}\Bigr|^4 dt.
$$

则有

$$
\mathcal I_4\ \ll\ T\Bigl(\sum_{n\le X}|a_n|^2\Bigr)^{2},
$$

其中常数仅依赖 $\sigma,K$ 及 C9.2 的分离/窗参数。证明思路与 A.2 相同：展开四次和并使用 $\widehat W$（或 $\widehat{W\!*\!W}$）在非零频处的小量性，与振荡积分界 $\min\{T,1/|\sum\pm\log n|\}$ 吸收四重交叉项。

### A.3（Paley–Zygmund）

若 $Z\ge0$ 且 $\mathbb E[Z^2]\le C\,\mathbb E[Z]^2$，则 $\mathbb P(Z\ge \theta\,\mathbb E[Z])\ge (1-\theta)^2/C$（$0<\theta<1$）。

### A.4（Pretentious 欧拉积比较）

对 $\sigma>1$ 与 $g\in\mathcal G$，令本地因子 $E_p(f;s):=\sum_{k\ge0}f(p^k)p^{-ks}$ 与 $E_p(g;s):=(1-g(p)p^{-s})^{-1}$。则有

$$
\biggl|\prod_{p\le X}\frac{E_p(f;\sigma+it)}{E_p(g;\sigma+it)}\biggr|
\ \le\ \exp\!\Bigl(-c_\sigma\sum_{p\le X}\frac{1-\Re\!\bigl(f(p)\overline{g(p)}p^{-it}\bigr)}{p^{\sigma}}+O(1)\Bigr).
$$

与 A.1–A.2 合并给出定理 9.1 的指数衰减因子。

### A.5（窗内 $L^2$ 比较）

在 C9.2(b) 与 $\mathbb D\bigl(f,g;X\bigr)\le D_0$ 下，取与 A.2 同一平滑窗 $W\in C_c^K(\mathbb R)$，则对固定 $\sigma>1$ 有

$$
\int_{\mathbb R} W\!\Big(\tfrac{t}{T}\Big)\,\big|P_f(X;\sigma,t)-P_g(X;\sigma,t)\big|^2 dt
\ \le\ C_\sigma\,e^{-c_\sigma D_0^2}\,T\,A_\sigma(X)^2,
$$

其中常数仅依赖于 $\sigma$ 与窗/分离参数 $(\Omega,\delta)$。由此可将模型 $P_g$ 的大值窗口在同一观测窗内**稳健转移**到 $P_f$（见定理 9.2）。

（证明提要）写成素因子比较并用 A.4 在 $\sigma>1$ 竖条内给出点态对数型控制；截断误差由 A.1 的有限阶 EM 与 A.2 的能量恒等式吸收，得出上式。∎

---

## 结语

Pretentious 距离在素数端刻画了乘法信号的"相干—反相干"结构；与母映射方向化、信息量刻度与离散一致逼近结合，得到一套**非渐近、可检**的指数和行为框架：非 Pretentious 区的指数衰减上界、Pretentious 区的几乎周期大值窗口、有限窗的小球概率与近零复访率。该框架在 S2–S8 的几何—解析—信息—离散架构上闭合，并为 S10 之后的谱—素数混合问题与数值验证提供统一的语法与工具箱。
