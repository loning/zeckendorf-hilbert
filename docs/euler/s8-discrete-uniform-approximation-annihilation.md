# S8. 离散一致逼近与差分湮灭

**—— Poisson/Nyquist + 有限阶 EM 的误差三分解；指数–多项式序列的湮灭算子与 Prony/矩方法的可识别性**

## 摘要

建立一套与 S3–S7 完全对齐的**离散一致逼近—反演**框架：把**Poisson/Nyquist 别名**、**有限阶 Euler–Maclaurin（EM）伯努利层**与**窗化截断尾项**组成"**非渐近误差三分解**"，确保在有限样本与固定窗宽的工程情境下仍可给出可计算的上界。在谱为**有限指数–多项式**叠加（合流线谱）时，构造**有限阶差分湮灭算子**并给出**最小阶**与**唯一性**；在小噪声下建立**可识别性—稳定性**的定性上界，以**（合流）Vandermonde 条件数**与**模态间距**为核心指标。最后给出面向母映射的**程序化流程**与**可检清单**。该框架与 S3 的 $\Gamma/\pi$ 正规化与完成函数模板、S4 的"极点 = 主尺度"、S5 的方向亚纯化、S6 的信息刻度以及 S7 的显式公式接口可直接拼接。

---

## 0. 记号与前置（与 S3–S7 对齐）

* **方向切片与采样网格**。固定方向 $\mathbf v\in\mathbb S^{n-1}$、横向偏置 $\rho_\perp$，令

$$
\rho=\rho_\perp+s\mathbf v,\qquad f(s):=F\bigl(\theta,\rho_\perp+s\mathbf v\bigr).
$$

取步长 $\Delta>0$，记 $b:=e^{\Delta}$、采样点 $s_k:=k\Delta$（$k\in\mathbb Z$ 或有限段）。"乘法步长" $b$ 与"加法步长" $\Delta$ 的互换遵循 S4 的加法–乘法 EM 对偶。

* **Fourier 变换规范（Poisson 一致性）**。

$$
\widehat g(\xi):=\int_{\mathbb R} g(s)\,e^{-i\xi s}\,ds,\qquad
\Delta\!\sum_{k\in\mathbb Z} g(k\Delta)=\sum_{m\in\mathbb Z}\widehat g\!\Bigl(\tfrac{2\pi m}{\Delta}\Bigr).
$$

* **方向指数–多项式序列**。当谱满足 S5 的指数–多项式律，采样序列

$$
y_k:=f(s_k)=\sum_{\ell=1}^L\Bigl(\sum_{r=0}^{d_\ell} a_{\ell,r}\,k^r\Bigr)\lambda_\ell^{\,k},
\qquad \lambda_\ell:=e^{\langle\beta_\ell,\mathbf v\rangle\,\Delta},
$$

即为**有限指数–多项式**（合流线谱）序列。方向拉普拉斯–Stieltjes 变换的极点位置与阶由 $\{\langle\beta_\ell,\mathbf v\rangle,d_\ell\}$ 决定。
 
* **端点单边导数**。对后续使用到的端点 $\pm T$，记
 
$$
g^{(j)}(T_-):=\lim_{s\uparrow T}g^{(j)}(s),\qquad
g^{(j)}(-T_+):=\lim_{s\downarrow -T}g^{(j)}(s).
$$

* **完成函数与增长配平（可选）**。必要时以 S3 的 $a$-对称 $\Gamma/\pi$ 因子 $r(s)$ 构造完成函数

$$
\Xi(s):=r(s)\,F\bigl(\theta,\rho_\perp+s\mathbf v\bigr),
$$

以控制垂线增长；若 $r(s)$ 在工作竖条内**全纯且处处非零**，则不改变谱位置与阶；若 $r$ 含零/极点，应将其**并入** S5 的极点模板同步处理（抵消或新增）后再行离散逼近与反演。

* **显式公式接口**。S7 的试验核 $\widehat h$ 在尺度侧即窗函数；本文的采样与窗化误差度量与显式公式（EF）中素数—素幂端的求和换序兼容。

---

## 1. Poisson–EM 的非渐近误差三分解（统一定理）

对

$$
\mathcal Q_{\Delta,T}[g]\ :=\ \Delta\!\sum_{|k|\le \lfloor T/\Delta\rfloor}\! g(k\Delta),\qquad
\mathcal I[g]\ :=\ \int_{\mathbb R} g(s)\,ds,
$$

我们以**别名（Poisson）+ 伯努利层（有限阶 EM）+ 截断尾项**给出非渐近上界。

### 定理 8.1（误差三分解）

设 $g\in C^{2M}(\mathbb R)\cap L^1(\mathbb R)$，其 Fourier 变换 $\widehat g\in L^1(\mathbb R)$，且 $g^{(2M)}\in L^1(\mathbb R)$；并且对所选步长 $\Delta$ 有

$$
\sum_{m\in\mathbb Z\setminus\{0\}}\Bigl|\widehat g\!\Bigl(\tfrac{2\pi m}{\Delta}\Bigr)\Bigr|<\infty.
$$

则给定步长 $\Delta>0$ 满足上式（别名可和性），且在上述正则性假设下，对任意 $T>0$、$M\in\mathbb N$（记 $K:=\lfloor T/\Delta\rfloor$）成立

$$
\Bigl|\,\mathcal I[g]-\mathcal Q_{\Delta,T}[g]\,\Bigr|
\ \le\
\underbrace{\sum_{m\in\mathbb Z\setminus\{0\}}\Bigl|\widehat g\!\Bigl(\tfrac{2\pi m}{\Delta}\Bigr)\Bigr|}_{\textbf{别名 / Poisson}}
\ +
\underbrace{\tfrac{\Delta}{2}\bigl(|g(K\Delta)|+|g(-K\Delta)|\bigr)
\ +\ \sum_{m=1}^{M-1}\frac{|B_{2m}|}{(2m)!}\,\Delta^{2m}\!\Bigl(\bigl|g^{(2m-1)}((K\Delta)_{-})\bigr|+\bigl|g^{(2m-1)}((-K\Delta)_{+})\bigr|\Bigr)
\ +\ C_M\,\Delta^{2M}\!\!\int_{-K\Delta}^{K\Delta}\! |g^{(2M)}(s)|\,ds}_{\textbf{伯努利层（有限阶 EM）}}
\ +
\underbrace{\int_{|s|>K\Delta}\! |g(s)|\,ds}_{\textbf{截断尾项}}.
$$

其中 $C_M:=\tfrac{2\zeta(2M)}{(2\pi)^{2M}}$。

**说明**。

* 第一项由 Poisson 求和公式与 $\widehat g\in L^1$ 得来，是对"积分 ↔ 无穷采样和"差异的**尾和的绝对值上界**。
* 第二项是把无穷和换为有限和（区间 $[-K\Delta,\,K\Delta]$）时的**有限阶 EM 校正**（含端点半权、有限伯努利层与有限阶余项）；只用到至 $B_{2(M-1)}$ 的伯努利层，**不存在无穷伯努利级数**。
* 第三项是**窗化截断**的体积分尾项。三者叠加，给出**非渐近、可计算**的误差预算。

**推论 8.2（带限与准带限）**。
(i) 若 $\operatorname{supp}\widehat g\subset[-\Omega,\Omega]$ 且 $\Delta\le \pi/\Omega$（Nyquist），则别名项为零；误差仅由有限阶 EM 与截断项控制。
(ii) 若 $|\widehat g(\xi)|\le C e^{-\mu|\xi|}$，则

$$
\sum_{m\ne0}\Bigl|\widehat g\!\Bigl(\tfrac{2\pi m}{\Delta}\Bigr)\Bigr|
\ \le\ \frac{2C\,e^{-2\pi\mu/\Delta}}{1-e^{-2\pi\mu/\Delta}},
$$

呈**指数级**抗别名。两条结论与 S3 的垂线增长配平及 S7 的核窗选择相容。

---

## 2. 方向样本的指数–多项式模型与"极点 = 主尺度"

设 $f(s)=F(\theta,\rho_\perp+s\mathbf v)$ 来自离散谱。按 S5，方向拉普拉斯–Stieltjes 变换的极点位于 $s=\gamma_\ell$，阶 $\le d_\ell+1$。令 $y_k=f(k\Delta)$。

### 命题 8.3（指数–多项式采样序列）

存在有限集合 $\{\lambda_\ell\}$ 与多项式 $P_\ell(k)$ 使

$$
y_k=\sum_{\ell=1}^L P_\ell(k)\,\lambda_\ell^{\,k},\qquad
\lambda_\ell=e^{\gamma_\ell\,\Delta}.
$$

若对一切 $\ell\ne j$ 有 $\gamma_\ell\not\equiv\gamma_j\ (\mathrm{mod}\ 2\pi i/\Delta)$，则 $\lambda_\ell$ 两两不同；否则可能发生 $\lambda$ 折叠。若 $d_\ell=0$ 则为纯指数和。**若** 连续极点 $\{\gamma_\ell\}$ **本身互异，且** $\Delta$ **满足** $|\Im(\gamma_\ell-\gamma_j)|<\pi/\Delta$（或等价的带宽约束），**则** $\lambda_\ell$ **两两不同**；若存在合流（$\gamma_\ell=\gamma_j$），仍可能发生 $\lambda$ 折叠，应以多重性并入 $d_\ell$ 处理。该结构与定理 8.1 的误差三分解**正交**：别名、端点校正与截断**不改变** $\{\gamma_\ell,d_\ell\}$ 的解析地位，保持 S4 的"**极点 = 主尺度**"。

---

## 3. 差分湮灭：存在性、唯一性与最小阶

### 定理 8.4（指数–多项式序列的有限阶差分湮灭）

令

$$
y_k=\sum_{\ell=1}^L\Bigl(\sum_{r=0}^{d_\ell} a_{\ell,r}\,k^r\Bigr)\lambda_\ell^{\,k},
\qquad \lambda_\ell\ \text{两两不同}.
$$

设

$$
\Phi(z)=\prod_{\ell=1}^L (z-\lambda_\ell)^{d_\ell+1}
=\sum_{r=0}^{R}\phi_r\,z^r,\qquad
R:=\sum_{\ell=1}^L(d_\ell+1).
$$

则对一切 $k$ 有

$$
\sum_{r=0}^{R}\phi_r\,y_{k+r}=0,
$$

且 $R$ 为**最小阶**。任何再乘非常数多项式都不会降低湮灭阶。

**证明要点**。记前移算子 $E$ 满足 $(Ey)_k:=y_{k+1}$，差分算子 $(\Delta_{\lambda}y)_k:=y_{k+1}-\lambda\,y_k=(E-\lambda I)y_k$。对每个 $\ell$，$(E-\lambda_\ell I)^{d_\ell+1}(k^{d_\ell}\lambda_\ell^{\,k})\equiv 0$；并且 $\prod_\ell (E-\lambda_\ell I)^{d_\ell+1}y\equiv 0$。将前移算子 $E$ 视作形式变量 $z$ 得到湮灭多项式 $\Phi(z)=\prod_\ell(z-\lambda_\ell)^{d_\ell+1}$，其根**恰为** $\{\lambda_\ell\}$；最小性由合流指数–多项式空间的维数计数与根互异性给出。∎

**注（步长—尺度一致性）**。$\lambda_\ell=e^{\gamma_\ell\Delta}$ 把方向指数率与采样步长统一为离散特征根；$\Delta\to0$ 时 $\lambda_\ell\approx 1+\gamma_\ell\Delta$，与 S5 的极点位置—阶完全一致。

---

## 4. Prony/矩方法的可识别性与稳定性（小噪声）

记观测向量 $\mathbf y=(y_0,\dots,y_{N-1})^\top$，噪声上界 $|\varepsilon|\le \eta$。以 Hankel/Toeplitz 预测方程估计 $\Phi$ 的系数 $\{\phi_r\}$。

### 定理 8.5（可识别性与样本复杂度）

若 $\lambda_\ell$ 两两不同且取**连续的** $2R$ 个等距样本（或等价地构造满秩的 Hankel/Toeplitz 预测矩阵），则在无噪声下由 $\{y_k\}_{k=0}^{N-1}$（$N\ge 2R$）**唯一**确定 $\Phi$；为消除尺度不定性，取 $\Phi$ 为首一多项式（令 $\phi_R=1$）。否则仅唯一至非零整体尺度。进而可唯一恢复 $\{\lambda_\ell\}$ 与 $\{P_\ell\}$。在噪声存在且预测矩阵满秩时，最小二乘解存在且唯一。

**稳定性（定性上界）**。设 $V$ 为**（合流）Vandermonde** 矩阵，$\kappa(V)$ 其条件数，$\delta_{\mathrm{sep}}:=\min_{\ell\ne j}|\lambda_\ell-\lambda_j|$ 为最小根间距。对小噪声 $\eta$ 有

$$
\max_\ell \frac{|\Delta\lambda_\ell|}{|\lambda_\ell|}
\ \lesssim\ \kappa(V)\cdot \frac{\eta}{\|\mathbf y\|},
$$

并随 $\delta_{\mathrm{sep}}\downarrow 0$ 恶化。故**模态聚集**与**小样本**导致不适定；在信息刻度（S6）上，**有效模态数** $N_{\mathrm{eff}}$ 越小，所需样本越少。上式中 $\|\cdot\|$ 可取 $\ell_2$ 范数，$\eta$ 为对应范数下的噪声上界；亦可改为 $\ell_\infty$ 一致上界，常数相应变化。

**可检策略（与 S6/S7 对齐）**。
(i) 先用 S6 的 $H,\ N_{\mathrm{eff}},\ N_2$ 估计"有效模态数"，据此选 $N$ 与窗宽 $T$。
(ii) 采用多起点/子采样稳健化（ESPRIT/矩法变体）以缓解 $\kappa(V)$；必要时 Tikhonov 正则。
(iii) 通过调整 $\Delta$（等价改变 $\lambda_\ell$ 的相对间距）缓解聚集。

---

## 5. 程序化流程（伪代码）

**输入**：方向 $\mathbf v$、偏置 $\rho_\perp$、样本 $y_k=f(k\Delta)$（$|k|\le K$ 或 $0\le k<N$）、EM 阶 $M$、窗宽 $T=K\Delta$。
**输出**：$\{(\widehat\gamma_\ell,\widehat d_\ell,\widehat a_{\ell,r})\}$ 或重构 $\widehat f$。

1. **窗化与别名控制**：选偶窗 $w$（如高斯/带限 Paley–Wiener），令 $g(s)=w(s/T)f(s)$。计算 $\mathcal Q_{\Delta,T}[g]$，按定理 8.1 估计别名与截断；若别名项偏大，缩小 $\Delta$ 或改更陡窗。
2. **有限阶 EM 端点校正**：对 $\{g(k\Delta)\}$ 施行**有限阶 EM（至 $B_{2(M-1)}$）**并记录伯努利层误差份额；余项视为全纯/整函数层（S4）。
3. **构造湮灭方程**：由（校正后）样本组装 Hankel/Toeplitz 预测方程，求 $\Phi(z)=\sum_{r=0}^{R}\phi_r z^r$。
4. **根与阶估计**：取 $\{\widehat\lambda_\ell\}$ 为 $\Phi$ 之根，多重性给出 $\widehat d_\ell$；置 $\widehat\gamma_\ell=\Delta^{-1}\log \widehat\lambda_\ell$（取**主值分支**，并据 Nyquist 限制消除 $\tfrac{2\pi i}{\Delta}$ 的分支模糊；对实序列按共轭配对一致化根集合）。
5. **幅度与多项式系数回归**：解线性方程估计 $\{\widehat a_{\ell,r}\}$。
6. **一致化与验证**：
   * 用 S5 的极点模板（位置 $\widehat\gamma_\ell$、阶 $\le \widehat d_\ell+1$）校核方向亚纯性；
   * 用 S6 的 $\Lambda$–$\Lambda^\ast$ 对偶与 $N_{\mathrm{eff}},N_2$ 评估"信息充足度"。

---

## 6. 误差预算与配平策略（汇总）

$$
\boxed{
\text{总误差}\ \le\
\underbrace{\text{别名}}_{\text{Poisson}}\ +
\underbrace{\text{伯努利层}}_{\text{有限阶 EM}}\ +
\underbrace{\text{截断}}_{\text{窗尾}}\ +
\underbrace{\text{反演噪声}}_{\kappa(V)\cdot \text{信噪比}}
}
$$

* **别名**：由 $\sum_{m\ne0}\bigl|\widehat g(2\pi m/\Delta)\bigr|$ 度量；以小步长/带限窗控制。
* **伯努利层**：端点导数与 $\Delta^{2m}$ 权重控制；$M$ 增大时按端点正则衰减（S4）。
* **截断**：$\int_{|s|>T}|g(s)|\,ds$ 控制；增大 $T$ 或换更陡窗。
* **反演噪声**：$\kappa(V)$ 与 $|\varepsilon|/|\mathbf y|$ 控制；以冗余样本、调谐 $\Delta$、正则/子空间法配平。
* **完成函数配平（可选）**：选 S3 的 $r(s)$ 削减垂线增长，间接降低窗尾与别名项。

---

## 7. 反例与边界族（失效原因标注）

* **R8.1（无限伯努利和）**：将 EM 当作**无穷级数**使用会破坏一致可和并制造伪极点；须**固定有限阶**。
* **R8.2（准带限失效）**：$\widehat g$ 缓慢衰减而 $\Delta$ 过大，别名主导，Prony 恢复失稳。
* **R8.3（模态聚集）**：$\min_{\ell\ne j}|\lambda_\ell-\lambda_j|$ 极小致 $\kappa(V)$ 爆长；微噪声即引根簇分裂。
* **R8.4（方向退化）**：若 $\langle\beta_\ell-\beta_j,\mathbf v\rangle\equiv 0$，则一维模型退化（$\lambda_\ell=\lambda_j$）；需改方向或多方向/多相位联合估计（契合 S2 的横截性）。
* **R8.5（完成函数误用）**：把 $\Gamma/\pi$ 正规化当作逐项权重引入 $y_k$ 会破坏信息刻度与可识别性；正规化仅作**全局乘子**。

---

## 8. 统一"可检清单"（最小充分条件）

1. **有限阶 EM**：固定 $M$，仅使用至 $B_{2(M-1)}$ 的伯努利层；余项视作全纯/整函数层（S4）。
2. **Poisson 可交换性**：窗 $w$ 与 $g$ 使 $\widehat g\in L^1$；别名项 $\widehat g(2\pi m/\Delta)$ 可计算或可上界。
3. **指数–多项式模型**：验证样本可由 $\sum_\ell P_\ell(k)\lambda_\ell^k$ 生成（或以 S5 的指数率/极点阶为先验）。
4. **样本复杂度**：预估 $R=\sum_\ell(d_\ell+1)$；取 $N\ge 2R$ 并留冗余以稳健化。
5. **条件数/间距**：评估 $\kappa(V)$ 与 $\delta=\min|\lambda_\ell-\lambda_j|$；若失衡，调谐 $\Delta$、加冗余或用多方向。
6. **信息刻度一致性**：用 $N_{\mathrm{eff}},N_2$ 与 $\Lambda$–$\Lambda^\ast$ 评估"有效模态数"，指导 $N,T,\Delta$；正规化与相位操作不进入概率权（S6）。
7. **完成函数（可选）**：需要垂线增长配平时，采用 S3 的 $a$-对称 $\Gamma/\pi$ 因子，不改变谱位置与阶。

---

## 9. 与其它篇章的接口

* **← S2（加法镜像）**：二项闭合与横截为**多方向联合采样**的可识别性提供几何判据（避免方向退化）。
* **← S3（完成函数）**：$\Gamma/\pi$ 正规化提供垂线增长配平，不改变离散谱可识别信息。
* **← S4（有限阶 EM）**："伯努利层 + 全纯余项"直接支持误差三分解并保障"**极点 = 主尺度**"在离散逼近中不被污染。
* **↔ S5（方向亚纯化）**：湮灭特征根 $\lambda_\ell$ 与极点位置 $\gamma_\ell$ 满足 $\lambda_\ell=e^{\gamma_\ell\Delta}$；阶界 $\operatorname{ord}\le d_\ell+1$ 一致。
* **↔ S6（信息刻度）**：$N_{\mathrm{eff}},N_2$ 评估可识别的"有效模态数"，$\Lambda$–$\Lambda^\ast$ 对偶指导窗/带宽选择。
* **↔ S7（$L$-函数接口）**：显式公式中的核 $\widehat h$ 即窗函数；EF 的素数—素幂项在尺度侧为等距点列，可用本篇误差三分解与差分湮灭作数值核对与线谱抽取。

---

## 结语

本篇把 S3–S5 的**连续镜像—解析延拓**，落地为 S8 的**离散一致逼近—差分反演**：Poisson/Nyquist 控制别名，**有限阶 EM** 保证端点与换序的全纯合法性（"**极点 = 主尺度**"保持不变），窗化截断使误差**非渐近可计算**；当样本呈**指数–多项式**结构时，**有限阶差分湮灭**与 Prony/矩方法提供**可识别—稳定**的参数反演路径。配合 S6 的信息刻度与 S7 的显式公式接口，这一框架构成了后续数值验证与实验基准的**可检、可拼接、可移植**的理论—算法基线。
