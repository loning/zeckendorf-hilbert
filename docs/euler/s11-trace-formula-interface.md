# S11. 迹公式接口（Selberg / Kuznetsov）

**谱侧—几何侧的试验核范式、非渐近误差与母映射语法的统一**

**作者**：Auric
**日期**：2025-10-20

---

## 摘要

构建与 S2–S10 完全对齐的**迹公式接口化模板**：以满足可检条件的**偶核** $h$ 及其"几何侧变换" $\mathcal{K} h$ 为纽带，实现**谱侧**（离散本征模与连续谱）与**几何侧**（闭测地长度谱 / Kloosterman 和）的缝合。解析层面严格采用 S4 的**有限阶 Euler–Maclaurin（EM）**，保持"**极点 = 主尺度**"；方向—增长以 S5 的**方向亚纯化**与 S10 的**支持函数上界**统一控制；核选择由 S6 的**信息势 $\Lambda$** 与凸对偶给出变分准则；数值上用 S8 的**Nyquist–Poisson–EM 三分解**提供**非渐近**误差预算；并与 S7 的显式公式在"素数—零/谱—几何"两端实现**窗形一致**与**误差同源**。全文按**定义—引理—定理—证明要点—可检清单**组织。

---

## 0. 记号与前置（与 S2–S10 对齐）

### 0.1 母映射与方向化（承接 S2/S5）

固定母映射

$$
F(\theta,\rho)=\sum_{j} c_j\,e^{i\langle\alpha_j,\theta\rangle} e^{\langle\beta_j,\rho\rangle},
$$

沿方向切片 $\rho=\rho_\perp+s\mathbf{v}$ 的拉普拉斯–Stieltjes 变换在适当竖条内**亚纯**，其全部极点由**主尺度项**决定（S5）。一切换序、截断、端点仅以**有限阶** EM 执行（S4）。

### 0.2 双曲曲面与谱分解（Selberg 侧）

令 $\Gamma\subset \mathrm{PSL}_2(\mathbb{R})$ 为第一类余有限 Fuchs 群，$\Gamma\backslash\mathbb{H}$ 具有限体积（可含抛物端）。拉普拉斯算子 $\Delta$ 的谱为

$$
\mathrm{spec}(\Delta)=\bigl\{\tfrac{1}{4}+r_j^2\bigr\}_{j\ge1}\ \cup\ \mathrm{spec}_{\mathrm{cts}},\qquad
r_j\in \mathbb{R}_{\ge0}\ \cup\ i\,(0,\tfrac{1}{2}] .
$$

其中 $r_j\in i\,(0,\tfrac{1}{2}]$ 对应小本征值 $0\le \lambda_j<\tfrac{1}{4}$（含常值本征态 $\lambda=0$ 时 $r=i/2$）。

【归一声明（散射归一）】本文约定 $\phi(s)$ 为去除 $\Gamma/\pi$ 因子的散射行列式（纯算术部分）；相应地，在抛物项中保留 $\tfrac{\Gamma'}{\Gamma}$。因此本文的连续谱项号记为“正号 $\phi'/\phi$”，相应的 $\Gamma'/\Gamma$ 归并入抛物项 $P_{\mathrm{par}}[h]$。

### 0.3 Hecke–Kloosterman 与 Bessel（Kuznetsov 侧）

在 $\Gamma=\mathrm{SL}_2(\mathbb{Z})$（权 $0$）下，设 $\{u_j\}$ 为 Hecke–Maass 本征基（$|u_j|_2=1$），谱参数 $\tfrac{1}{4}+r_j^2$，Hecke 特征值 $\lambda_j(n)$ 取标准归一 $\lambda_j(1)=1$。Kloosterman 和

$$
S(m,n;c)=\sum_{\substack{d\bmod c\\ \gcd(d,c)=1}}
e\left(\frac{m\bar{d}+nd}{c}\right),
\quad e(x):=e^{2\pi i x},\ \bar{d} d\equiv 1\pmod c .
$$

Bessel 记号：第一类 $J_\nu$、修正第二类 $K_\nu$。

Maass 形式 $u_j$ 的 Fourier–Whittaker 展开系数记作 $\rho_j(n)$，满足
$$
\rho_j(n)=\rho_j(1)\,\lambda_j(n),\qquad |u_j|_2=1,\ \lambda_j(1)=1.
$$
此处 $n\ge1$。

### 0.4 核—变换对

设 $h:\mathbb{R}\to\mathbb{C}$ 为**偶**函数。Selberg 侧取余弦傅里叶变换

$$
(\mathcal{C} h)(\ell)=\frac{1}{2\pi}\int_{-\infty}^{\infty} h(r)\,e^{i r\ell}\,dr
=\frac{1}{\pi}\int_0^\infty h(r)\,\cos(r\ell)\,dr,
$$

Kuznetsov 侧取 Bessel 双变换（归一固定为）

$$
\begin{aligned}
(\mathcal{B}^{+}h)(x)&:=\frac{2i}{\pi}\int_0^\infty \frac{r\, h(r)}{\cosh(\pi r)}\,J_{2ir}(x)\,dr,\\[2pt]
(\mathcal{B}^{-}h)(x)&:=\frac{4}{\pi}\int_0^\infty r\, h(r)\,K_{2ir}(x)\,dr.
\end{aligned}
$$

### 0.5 信息势与增长（承接 S6/S10）

S6 的软最大势 $\Lambda(\rho)=\log\sum_j |c_j| e^{\langle\beta_j,\rho\rangle}$ 之 Hessian 给出**方向方差**；S10 的支持函数上界给出沿方向 $\mathbf{v}$ 的 Phragmén–Lindelöf 指标 $\le \max_j\langle\beta_j,\mathbf{v}\rangle$。

### 0.6 EM 纪律与"极点 = 主尺度"（承接 S4）

所有展开仅用**有限阶** EM；端点/伯努利层带来整/全纯修正，**不引入新极点**。由此在迹公式推导中保留"极点仅来自主尺度项"的解析纪律。

---

## 1. 可检试验核

**定义 11.1（$\mathcal{K}$-可检核族）**

记 $\mathcal{K}\in\{\mathcal{C},\mathcal{B}^{+},\mathcal{B}^{-}\}$。偶函数 $h$ 属于 $\mathscr{H}_{\mathcal{K}}(M,\sigma,\Omega)$（$M\ge2$，$\sigma>1$，带宽 $\Omega>0$），若：

* **(H1) 条带全纯与衰减**：$h$ 在 $|\Im r|<\sigma$ 全纯，且 $|h(r)|\ll (1+|r|)^{-2-\varepsilon}$（均匀于该条带；$\sigma>1$ 已覆盖如 $r=i/2$ 等纯虚点）；
* **(H2) 光滑与可积**：$h\in C^M(\mathbb{R})$，且 $h^{(k)}\in L^1(\mathbb{R})$ $(0\le k\le M)$；
* **(H3) 几何侧带限/指数衰减**：

$$
\operatorname{supp}(\mathcal{K} h)\subset[-\Omega,\Omega]\quad\text{或}\quad
|\mathcal{K} h(x)|\le C e^{-\mu|x|}\ (\mu>0);
$$

* **(H4) EM 相容**：涉及 $h$ 的和—积—积分与移线在固定竖条内可交换；EM 余项在参数上全纯/整。

**引理 11.2（变换良定与能量估计）**

若 $h\in \mathscr{H}_{\mathcal{K}}$，则 $\mathcal{C} h,\mathcal{B}^\pm h$ 连续，并有

$$
|\mathcal{C} h|_{L^\infty}\ll |h|_{L^1},\qquad
|\mathcal{B}^{\pm}h|_{L^\infty}\ll |h|_{W^{1,1}},\quad
|h|_{W^{1,1}}:=|h|_{L^1}+|h'|_{L^1}.
$$

特别地，若 $\mathcal{K}=\mathcal{C}$ 且 $\operatorname{supp}(\mathcal{C} h)\subset[-\Omega,\Omega]$，当采样步长 $\Delta\le \pi/\Omega$ 时离散重构**无别名误差**（Nyquist）。对 $\mathcal{K}=\mathcal{B}^{\pm}$，不存在精确的 Nyquist 消失律，仅能随 $|\mathcal{B}^{\pm}h|$ 的尾界与平滑度给出**快速衰减**的离散化误差控制。

*证明要点*：由 (H1)–(H2) 的分部积分与 Paley–Wiener 控制；(H3) 保证几何侧卷积/求和绝对收敛；(H4) 保障移线与 EM 换序的合法性。

---

## 2. Selberg 迹公式（接口范式）

采用标准测度归一：体积项为 $\dfrac{\mathrm{Area}(\Gamma\backslash\mathbb{H})}{4\pi}\int r\,h(r)\tanh(\pi r)\,dr$。

**定理 11.3（Selberg 迹公式 · 余有限群通式）**

令 $\Gamma$ 为第一类余有限 Fuchs 群，$h\in \mathscr{H}_{\mathcal{C}}(M,\sigma,\Omega)$ 为偶核，记 $g:=\mathcal{C} h$。则

$$
\boxed{
\begin{aligned}
&\sum_j h(r_j)\ +\ \frac{1}{4\pi}\int_{-\infty}^{\infty} h(r)\,\frac{\phi'(1/2+ir)}{\phi(1/2+ir)}\,dr \\
&=\ \underbrace{\frac{\mathrm{Area}}{4\pi}\int_{-\infty}^{\infty} r\,h(r)\tanh(\pi r)\,dr}_{\text{单位（体积）项}}
\ +\ \underbrace{\sum_{[\gamma]_{\mathrm{hyp}}}\ \sum_{k\ge1}\frac{\ell(\gamma_0)}{2\sinh\left(\tfrac{k \ell(\gamma_0)}{2}\right)}\,g\left(k \ell(\gamma_0)\right)}_{\text{双曲项}}\\
&\quad+\ \underbrace{E_{\mathrm{ell}}[h]}_{\text{椭圆项}}
\ +\ \underbrace{P_{\mathrm{par}}[h]}_{\text{抛物/散射项}}.
\end{aligned}}
$$

其中 $\phi(s)$ 为散射行列式。椭圆项与抛物项为

$$
\begin{aligned}
E_{\mathrm{ell}}[h]\ &=\ \sum_{[R]} \sum_{m=1}^{m_R-1}\frac{1}{2m_R\sin(\pi m/m_R)}
\int_{-\infty}^{\infty} h(r)\,\frac{\cosh\left((1-\tfrac{2m}{m_R}) \pi r\right)}{\cosh(\pi r)}\,dr,\\[2pt]
P_{\mathrm{par}}[h]\ &=\ \frac{\kappa}{4\pi}\int_{-\infty}^{\infty} h(r)\,\frac{\Gamma'}{\Gamma}\left(\tfrac{1}{2}+ir\right)\,dr\ +\ c_\kappa\,h(0),
\end{aligned}
$$

其中 $\kappa$ 为 cusp 数，$c_\kappa$ 为固定常数（依归一）。

*证明要点*：取与 $h$ 的 Harish–Chandra 变换对应的球对称核 $k$，构造算子 $Kf(z)=\int_{\Gamma\backslash\mathbb{H}}k(d(z,w))f(w)\,d\mu(w)$，两侧展开取迹：谱侧给出 $\sum h(r_j)+$ 连续谱积分；几何侧按共轭类分解为单位/双曲/椭圆/抛物贡献。换序、移线、端点由 (H4) 与有限阶 EM 保障；竖条增长以 $\tanh(\pi r)$ 与 S10 支持函数上界配平。

---

## 3. Kuznetsov（Bruggeman–Kuznetsov）公式（接口范式）

**定理 11.4（Kuznetsov 迹公式 · 权 0 · 级别 1）**

令 $h\in \mathscr{H}_{\mathcal{B}^\pm}(M,\sigma,\Omega)$ 为偶核。对任意 $m,n\ge1$，有

$$
\boxed{
\begin{aligned}
&\sum_j |\rho_j(1)|^2\,\lambda_j(m)\overline{\lambda_j(n)}\,h(r_j)\ +\ \frac{1}{4\pi}\int_{-\infty}^{\infty} \frac{\tau(m,r)\,\overline{\tau(n,r)}}{\bigl|\zeta(1+2ir)\bigr|^{2}}\,h(r)\,dr\\
&=\ \delta_{m=n}\,\mathcal{H}_0[h]\ +
\sum_{c\ge1}\frac{S(m,n;c)}{c}\,(\mathcal{B}^{+} h)\left(\tfrac{4\pi \sqrt{m n}}{c}\right)\\
&\quad+\ \sum_{c\ge1}\frac{S(m,-n;c)}{c}\,(\mathcal{B}^{-} h)\left(\tfrac{4\pi \sqrt{m n}}{c}\right).
\end{aligned}}
$$

其中 $\tau(n,r)=\sum_{ab=n}(a/b)^{ir}$ 为 Eisenstein 级联系数；$\mathcal{H}_0[h]$ 为对角（单位）项的线性泛函（仅由 $h$ 的低频决定）。

（实现提示）在本规范下，$\mathcal{H}_0[h]$ 可由 Poincaré 系列 $P_m$ 的零频项配平直接计算得到，实现时只需保留 $h$ 的低频矩。

*证明要点*：对 Poincaré 系列 $P_m$ 施加核 $h$ 的谱加权，一方面作 Hecke–Maass 谱展开得左侧；另一方面作几何展开，经 Poisson summation formula 与 Bessel–Fourier 分解得到右侧的 Kloosterman–Bessel 侧。换序与端点由 (H4) 与有限阶 EM 保证；$\mathcal{B}^\pm$ 的带限/指数窗控制模长 $c$ 的非渐近衰减。

---

## 4. 试验核的变分准则（与信息势对齐）

**命题 11.5（信息—变分核选择）**

给定**谱窗**与**几何窗**权函数 $W_{\mathrm{spec}},W_{\mathrm{geom}}\ge0$。对 $h\in \mathscr{H}_{\mathcal{K}}$ 定义泛函
$$
\mathcal{J}[h]=\int W_{\mathrm{spec}}(r)\,|h(r)|^2\,d\mu_{\mathrm{spec}}(r)\ -\ \lambda\int W_{\mathrm{geom}}(x)\,|\mathcal{K} h(x)|^2\,dx\ +\ \tau\int |h^{(M)}(t)|^2\,dt,
$$

其中 $d\mu_{\mathrm{spec}}$ 为相应谱测度（Selberg：$r\,\tanh\pi r\,dr$；Kuznetsov：$dr$）。则：

1. 当 $\tau>0$ 且 $0<\lambda<\lambda_\ast$ 时，$\mathcal{J}$ 在 $\mathscr{H}_{\mathcal{K}}$ 上**严格凸**，且唯一极小元为 $h_\star\equiv 0$，其中
$$
\lambda_\ast^{-1}=\Big\|\big(\mathcal{L}_{\mathrm{spec}}+\tau D^{2M}\big)^{-1/2}\,\mathcal{K}^*\,W_{\mathrm{geom}}\,\mathcal{K}\,\big(\mathcal{L}_{\mathrm{spec}}+\tau D^{2M}\big)^{-1/2}\Big\|_{\mathrm{op}}\,.
$$
2. 为获得**非零核**用于选择/设计，采用**约束式 Rayleigh 商**
$$
\mathcal{R}[h]:=\frac{\big\langle \mathcal{K}h,\ W_{\mathrm{geom}}\,\mathcal{K}h\big\rangle}{\big\langle h,\ \mathcal{L}_{\mathrm{spec}}h\big\rangle\ +\ \tau\,\|D^{M}h\|_{L^{2}}^{2}},\qquad h\neq 0,
$$
其极值问题等价于广义特征值问题
$$
\big(\mathcal{L}_{\mathrm{spec}}+\tau D^{2M}\big)h=\mu\,\mathcal{K}^*\left(W_{\mathrm{geom}}\cdot \mathcal{K} h\right),
$$
最大本征对 $(\mu_{\max},h_\star)$ 给出最优核，且 $\mu_{\max}=\sup_{h\neq0}\mathcal{R}[h]$；

3. 若以 S6 的信息势 $\Lambda$ 与对偶 $\Lambda^\ast$ 度量目标窗，则上式等价于**在信息预算约束下最大化几何灵敏度**的问题；$\nabla^2\Lambda$ 给出方向方差，S10 的"主导子和区"使 $\mathcal{L}_{\mathrm{spec}}$ 分段仿射近似良好。

---

## 5. 非渐近误差（Nyquist–Poisson–EM 三分解）

**定理 11.6（有限窗/离散化误差预算）**

以步长 $\Delta$ 对谱积分/和式离散化，截尾阈值 $T$ 截尾，EM 阶数 $M$ 处理端点。记被积核 $g$ 为 Selberg/Kuznetsov 展开中的窗口化对象，则有两类统一上界：

**(i) 余弦/傅里叶对（$\mathcal{K}=\mathcal{C}$）**

$$
\big|\text{真值}-\text{近似}\big|
\ \le\ \underbrace{\sum_{m\ne0}\big|\widehat{g}(2\pi m/\Delta)\big|}_{\text{别名（Poisson）}}
\ +\ \underbrace{\sum_{k=1}^{M-1} C_k\,\Delta^{2k}\cdot \max_{0\le j\le 2k-1} \big| g^{(j)} \big|}_{\text{伯努利层（有限阶 EM）}}
\ +\ \underbrace{\int_{|s|>T}|g(s)|\,ds}_{\text{截断（窗尾）}}.
$$

其中 $\widehat{g}(\xi):=\int_{\mathbb{R}} g(s)\,e^{-i s\xi}\,ds$（此处的傅里叶规范与 §0.4 的 $\mathcal{C}$ 记号无关）。

若 $\operatorname{supp}(\mathcal{C} h)\subset[-\Omega,\Omega]$ 且 $\Delta\le \pi/\Omega$，则**别名项为零**（Nyquist 达成）。

**(ii) Bessel 双变换（$\mathcal{K}=\mathcal{B}^\pm$）**

$$
\big|\text{真值}-\text{近似}\big|
\ \le\ \underbrace{C_q\,\Delta^{\,q}\,|h^{(q)}|_{L^1}}_{\text{离散化误差（平滑度控制）}}
\ +\ \underbrace{\int_{x>X}|\mathcal{B}^\pm h(x)|\,w(x)\,dx}_{\text{窗尾截断}}\ +\ \underbrace{\sum_{k=1}^{M-1} C_k\,\Delta^{2k}\cdot \max_{0\le j\le 2k-1}\big|g^{(j)}\big|}_{\text{伯努利层}},
$$

其中 $q\ge1$ 可选，权 $w(x)$ 为与所用求和/求积一致的正权（如 $x^{-1/2}$ 或常权）；若 $|\mathcal{B}^\pm h(x)|\ll e^{-\mu x}$ 或超多项衰减，则"窗尾截断"呈对应速率衰减。此处**无精确 Nyquist 消失律**，仅给出随平滑度与尾界的快速衰减控制。

*证明要点*：$\mathcal{C}$ 情形直接援引 Poisson 求和；$\mathcal{B}^\pm$ 情形用 Filon/渐近型求积或分部积分构造离散化误差上界，并以 $\mathcal{B}^\pm h$ 的尾界控制截断；S4 的有限阶 EM 仅引入整/全纯修正，不改变极点结构。

---

## 6. Pretentious—谱交互（与 S9 的接口）

**命题 11.7（相干/反相干的窗形效应）**

令 Pretentious 距离 $\mathbb{D}$ 衡量 $\{\lambda_j(\cdot)\}$ 在素数端的相干度。则：

* **非 Pretentious 区**（$\mathbb{D}\gtrsim 1$）：$\sum_j \lambda_j(m)\overline{\lambda_j(n)}h(r_j)$ 在窗口上**能量平均**，几何侧由 $\mathcal{B}^\pm h$ 的带限/指数窗对 Kloosterman 和**带宽抑制**；
* **Pretentious 区**（$\mathbb{D}\ll 1$）：存在 $|t-\tau^\star|\le \delta$ 的**大值窗口**（S9 的几乎周期效应），并在几何侧对应若干模长 $c$ 的**局部增强**，幅度受 $\mathcal{B}^\pm h$ 的窗形上界与 §5 的误差预算控制。

---

## 7. 失效边界与对策

* **核不合格**：偶性/衰减/光滑不足导致和式不绝对收敛或换序非法。对策：提升 $M$，改用带限/指数窗。
* **EM 误用为无穷级数**：无穷伯努利叠加可破坏可和性并伪造奇性。对策：仅用**有限阶** EM。
* **方向退化**：几何或谱参数等速导致识别退化。对策：改向或多方向层析（S10/S5/S8）。
* **竖条增长失控**：未施 $(\Gamma/\pi)$ 正规化配平即移线。对策：先正规化。
* **极端 Pretentious**：谱侧近完全相干使 $\mathcal{J}[h]$ 的有效凸性恶化。对策：重设权或增大正则 $\tau$。

---

## 8. 统一"可检清单"（最小充分条件）

1. **核**：$h\in\mathscr{H}_{\mathcal{K}}(M,\sigma,\Omega)$（偶性、条带全纯、衰减、带限/指数窗）。
2. **换序**：和—积—积分互换置于 S4 的**有限阶 EM** 框架；余项整/全纯，**极点仅来自主尺度**。
3. **增长**：施 $(\Gamma/\pi)$ 正规化与 S10 支持函数上界控制竖条/方向增长。
4. **方向**：选 $\mathbf{v}$ 并用 S5 的亚纯化识别极点位置/阶。
5. **误差**：按 §5 把误差分解为
   —（$\mathcal{K}=\mathcal{C}$）**别名 + 伯努利层 + 截断**；
   —（$\mathcal{K}=\mathcal{B}^\pm$）**离散化（平滑度） + 伯努利层 + 窗尾截断**。
6. **变分**：用 §4 的 $\mathcal{J}[h]$ 或 S6 的 $\Lambda$–$\Lambda^\ast$ 对偶挑选核（目标窗、正则、预算）。
7. **双轨对齐**：在同一核族上联用 S7 显式公式与本篇迹公式，保证"素数—零/谱—几何"的**窗形一致**与**误差同源**。

---

## 9. 与既有篇章的接口

* **↔ S2（零集几何）**：二项闭合与幅度平衡超平面提供长度谱/Kloosterman 的局部化骨架。
* **↔ S3（自反核/完成函数）**：$(\Gamma/\pi)$ 正规化用于竖线配平与镜像；与迹公式核相容。
* **↔ S4（有限阶 EM）**：保障推导中换序与端点仅生整/全纯层，维持"极点 = 主尺度"。
* **↔ S5（方向亚纯化）**：识别几何/谱变量方向上的极点与增长指标。
* **↔ S6（信息刻度）**：$\Lambda$ 与方差律指导核窗宽与灵敏度；Bregman–KL 为核更新的代价函数。
* **↔ S7（$L$-函数接口）**：显式公式与迹公式在同一核族互补使用，实现"素数—零/谱—几何"的双通道观测。
* **↔ S8（离散一致逼近）**：Nyquist–Poisson–EM 三分解提供非渐近误差常数与实现流程。
* **↔ S9（Pretentious/指数和）**：谱相干/反相干与 Pretentious 距离的接口化描述，指导 $(m,n)$ 与扭结策略。
* **↔ S10（Amoeba 几何与增长）**：支持函数上界与"主导子和区"的分段仿射性提升核选择的稳定性。

---

## 附：归一与等价写法速记

* Selberg 侧 $g=\mathcal{C} h$ 亦可写 $g(\ell)=\dfrac{1}{\pi}\int_0^\infty h(r)\cos(r\ell)\,dr$。
* 常用等价 $J$-窗写法（与 0.4 的 $\mathcal{B}^{+}$ 规范对齐说明）

$$
\widetilde{\mathcal{B}}(x)
=\frac{1}{\pi}\int_{0}^{\infty}\frac{r\,h(r)}{\sinh(\pi r)}\cdot\frac{J_{2ir}(x)-J_{-2ir}(x)}{2i}\,dr.
$$

并可用恒等式
$$
\frac{J_{2ir}(x)-J_{-2ir}(x)}{2i\,\sinh(\pi r)}
= i\,\sinh(\pi r)\,J_{2ir}(x)+\cosh(\pi r)\,Y_{2ir}(x),\qquad r\in\mathbb R,
$$
将其改写为
$$
\widetilde{\mathcal{B}}(x)
=\frac{1}{\pi}\int_{0}^{\infty} r\,h(r)\,\Big(i\,\sinh(\pi r)\,J_{2ir}(x)+\cosh(\pi r)\,Y_{2ir}(x)\Big)\,dr.
$$
（注：此写法需同时包含 $Y_{2ir}$ 项方与 0.4 节的规范一致；保持 0.4 节 $\mathcal{B}^{+}$ 的主定义不变最为简洁。）

切勿在实现中将上述 $\widetilde{\mathcal{B}}$ 与 §0.4 的 $\mathcal{B}^{+}$ 互代；两者需按各自规范选择核窗，参数可换算但表达式不可直接互替。

$K$-窗与 $\mathcal{B}^{-}$ 在相应规范下等价。

* Kloosterman 和的记号采用 $\gcd(d,c)=1$，$\bar{d}$ 为 $d$ 的模逆，$e(x)=e^{2\pi i x}$。

---
