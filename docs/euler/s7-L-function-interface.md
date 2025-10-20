# S7. $L$-函数接口

**—— degree / conductor / 完成函数 / 显式公式与试验核的统一模板**

## 摘要（定性）

在 S2–S6 的几何—解析—信息基座上，建立一般 $L$-函数（含 Dirichlet、椭圆曲线等）的接口化模板：以"欧拉积—完成函数—功能方程"为纲，给出 degree 与 conductor 的范畴化记账；在 S3 的 $\Gamma/\pi$ 正规化下构造完成函数并阐明"中心轴"参数 $a$ 的对称；以 S4 的有限阶 Euler–Maclaurin 作为技术底座，保证换序与端点处理的全纯/整函数性与"极点 = 主尺度"；给出 Weil 显式公式的统一陈述与可检试验核条件，将素数端局部数据 $\{\alpha_{p,j}\}$ 与零点侧谱 $\{\rho\}$ 在同一母映射语法下对偶化；最后以 Dirichlet $L$ 与椭圆曲线 $L$ 为模板实例。

---

## 0. 记号与前置（与 S2–S6 对齐）

**欧拉积与 Dirichlet 级数。** 设

$$
L(s)=\sum_{n\ge1}\frac{a_n}{n^s}\quad(\Re s>\sigma_0),\qquad
L(s)=\prod_{p}\prod_{j=1}^{d_p}\bigl(1-\alpha_{p,j}p^{-s}\bigr)^{-1},
$$

其中每个素点的局部因子由有限组复数 $\alpha_{p,j}$ 编码（允许有限个坏素点作惯常修正）。记**局部度上界** $d_{\mathrm{loc}}:=\sup_p d_p$（标准情形为常数），**conductor** $Q>0$ 作为抽象尺度参数。

**完成函数与中心轴。** 取 $a\in\mathbb R$。设存在由 $\Gamma/\pi$ 因子组成的

$$
r(s)=\prod_{j=1}^{r_1}\Gamma_{\mathbb R}(s+\lambda_j)\prod_{k=1}^{r_2}\Gamma_{\mathbb C}(s+\mu_k),
\quad
\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma\!\Big(\frac{s}{2}\Big),\ \
\Gamma_{\mathbb C}(s)=(2\pi)^{-s}\Gamma(s),
$$

使

$$
\Lambda_{L}(s):=Q^{s/2}\,r(s)\,L(s)\quad\text{满足}\quad
\boxed{\ \Lambda_{L}(s)=\varepsilon\,\Lambda_{\tilde L}(a-s),\qquad |\varepsilon|=1\ }.
$$

其中 $\tilde L$ 为 $L$ 的**对偶/伴随**对象（Dirichlet 场景为复共轭特征 $\bar\chi$；$\mathrm{GL}(d)$ 场景为对偶表示 $\tilde\pi$）。

称直线 $\Re s=\tfrac a2$ 为**中心轴**。必要时亦可采用对称化因子 $r_{\mathrm{sym}}(s):=r(s)r(a-s)$ 以实现 S3 的"自反核—完成函数"表征。为避免误解，$r_{\mathrm{sym}}$ 自身满足 $r_{\mathrm{sym}}(s)=r_{\mathrm{sym}}(a-s)$，可用于对称化估计；若需构造真正偶的对象，可取 $\boxed{\ \Xi_{\mathrm{sym}}(s):=Q^{a/2}r_{\mathrm{sym}}(s)\,L(s)\,\tilde L(a-s)\ }$（或直接使用完成功能方程），并不替代满足 $\Lambda_{L}(s)=\varepsilon\,\Lambda_{\tilde L}(a-s)$ 的标准完成因子 $r(s)$。

**有限阶 EM 与"极点 = 主尺度"。** 全流程仅使用**有限阶** Euler–Maclaurin（S4），确保端点与离散—连续桥的余项为整/全纯层，从而极点仅由主尺度项引入。

**方向化与增长。** 用 S5 的"沿方向亚纯化—指数–多项式律"控制竖线增长；$\Gamma/\pi$ 因子提供 Stirling 级的指数衰减配平（与 S3 对齐）。

**信息刻度与核选择。** S6 的 $\Lambda(\rho)$–$\Lambda^\ast$ 对偶为试验核的选取给出变分准则（定性）。

---

## 1. 欧拉积的母映射嵌入与度量参数

### 1.1 母映射嵌入（相位—尺度编码）

对每个素点 $p$ 与指数 $m\ge1$，局部项

$$
\sum_{j=1}^{d_p}\alpha_{p,j}^{\,m}\,p^{-ms}
$$

视为母映射离散谱的一族模态：尺度位移 $-m\log p$，相位权由 $\alpha_{p,j}^{\,m}$ 提供（若存在酉化，幅相可分）。于是 $\{p^m\}$ 在尺度空间形成等距点列 $\{\rho=-m\log p\}$，与 S2 的"幅度平衡超平面"及横截几何在局部二项闭合时兼容。乘法上的欧拉积因而转写为尺度上的离散谱叠加。

### 1.2 degree 与 conductor 的接口化定义

在接口层定义

$$
\deg L:=r_1+2r_2,\qquad
Q:=\text{有限处局部尺度的全局记账参数},
$$

其中 $\deg L$ 取自无穷处 $(\Gamma_{\mathbb R},\Gamma_{\mathbb C})$ 因子的记账（与 $\mathrm{GL}(d)$ 型的一般度一致），$Q$ 统一记录有限处（含坏素点）归一化后的"尺度密度"。为避免歧义，下文 degree 专指无穷处度 $\deg L=r_1+2r_2$；§0 中的 $d_{\mathrm{loc}}:=\sup_p d_p$ 仅作上界记号（标准 $\mathrm{GL}(d)$ 情形下二者相等）。此外，约定坏素点的尺度修正与范数归一并入全局 $Q$ 的记账（与 §3.2 中 $\widehat h(0)\log Q$ 的来源一致）。此定义与 S3 的 $a$-对称模板、S4 的"主尺度"原则一致。

---

## 2. 完成函数模板与垂线增长（与 S3 对齐）

### 定义 2.1（完成函数）

给定 $Q>0$、$a\in\mathbb R$ 与无穷处参数 $\{\lambda_j\},\{\mu_k\}$，定义

$$
\Lambda_{L}(s)=Q^{s/2}\Big(\prod_{j=1}^{r_1}\Gamma_{\mathbb R}(s+\lambda_j)\Big)
\Big(\prod_{k=1}^{r_2}\Gamma_{\mathbb C}(s+\mu_k)\Big)L(s),
$$

并要求存在 $|\varepsilon|=1$ 使 $\Lambda_{L}(s)=\varepsilon\,\Lambda_{\tilde L}(a-s)$。

### 定理 2.2（垂线增长配平）

假设 $\deg L=r_1+2r_2\ge 1$（存在至少一个 $\Gamma_{\mathbb R}$ 或 $\Gamma_{\mathbb C}$ 因子）。若 $L(s)$ 在任意闭竖条至多多项式增长，则对任意**避开 $\Lambda_{L}$ 极点的** $\sigma\in\mathbb R$（或更一般的不穿越 $\Lambda_{L}$ 极点的闭竖条）存在 $c(\sigma)>0$ 使

$$
\big|\Lambda_{L}(\sigma+it)\big|\ \ll_{\sigma}\ e^{-c(\sigma)|t|}\quad(|t|\to\infty),
$$

其中指数衰减由 $\Gamma/\pi$ 因子的 Stirling 估计提供。中心轴 $\Re s=\tfrac a2$ 上的对称由完成功能方程 $\Lambda_{L}(s)=\varepsilon\,\Lambda_{\tilde L}(a-s)$ 给出。

*证明要点。* Stirling 估计与至少一个 $\Gamma$ 因子相乘给出指数级配平；$L(s)$ 的多项式增长不改变指数主导；功能方程由局部—整体匹配成立。

---

## 3. Weil 显式公式（接口版）

### 3.1 试验核与 Fourier–Laplace 变换

取偶函数 $h:\mathbb C\to\mathbb C$，满足：

* (H1) $h$ 为偶函数，且在 $\mathbb C$ 上全纯（或至少在所有 $i(\rho-\tfrac a2)$ 所在带上全纯），并在实轴上满足 $|h(t)|\ll (1+|t|)^M$（某 $M\ge 0$）；
* (H2) 其 Fourier 变换

$$
\widehat h(x):=\frac{1}{2\pi}\int_{-\infty}^{\infty} h(t)e^{-itx}\,dt
$$

为紧支撑或指数衰减（Paley–Wiener 型）；
* (H3) 与 S4 的有限阶 EM 相容：一切求和—积分—移线均受 S1 的 C0–C3 与 S4 的主导/一致条件保障。

### 3.2 显式公式（统一模板）

设 $\Lambda_{L}(s)$ 满足 §2 的完成功能方程与增长条件（一般情形配对对象为 $\Lambda_{\tilde L}$）。默认 $\Lambda_{L}$ 在所用移线邻域全纯（或已知极点集与阶）；若存在极点，则 (EF) 右端需加上相应留数项（模板不改变其它项的记账方式）。记 $\mathcal Z$ 为 $\Lambda_{L}(s)$ 的所有非平凡零（按重数），则有恒等式

$$
\boxed{\
\sum_{\rho\in\mathcal Z} h\!\left(i\big(\rho-\tfrac a2\big)\right)
= \widehat h(0)\,\log Q\;+\;\sum_{\text{Arch}}\mathcal A_{r}[h]\;-
\sum_{p}\sum_{m\ge1}\frac{\log p}{p^{m a/2}}\Big(\sum_{j=1}^{d_p}\alpha_{p,j}^{\,m}\Big)\,\widehat h\!\big(m\log p\big)\ .
}
\tag{EF}
$$

若 $\Lambda$ 在积分移线所涉域内存在极点，则右端需另加对应留数项（随实例给出标准记账）；本项不影响 $\widehat h(0)\log Q$、$\mathcal A_r[h]$ 与素数端求和的结构。

其中 $\mathcal A_{r}[h]$ 为由 $r(s)$ 的 $\Gamma$-因子对数导数与 $h$ 诱导的无穷处项，可写作

$$
\mathcal A_{r}[h]
:=\frac{1}{2\pi}\int_{-\infty}^{\infty}h(t)\,\Re\!\left(\frac{r'}{r}\!\left(\tfrac a2+it\right)\right)dt
$$

的线性组合（按 $\Gamma_{\mathbb R},\Gamma_{\mathbb C}$ 分项记账）。素数端出现 von Mangoldt 型权 $\log p$ 与局部迹 $\sum_j\alpha_{p,j}^{\,m}$。

*证明要点。* 在 $\Re s=\sigma$ 上考虑

$$
\boxed{\ -\frac{\Lambda_{L}'}{\Lambda_{L}}(s)
:=-\frac{1}{2}\log Q-\frac{r'}{r}(s)+\sum_{p}\sum_{m\ge1}\frac{\Big(\sum_{j=1}^{d_p}\alpha_{p,j}^{\,m}\Big)\log p}{p^{ms}}\ },
$$

以核 $H(s):=h\!\big(i(s-\tfrac a2)\big)$ 乘上后沿竖线积分，并在有限阶 EM 与增长控制下移线至 $\Re s=\tfrac a2\pm\eta$，收集来自零点的留数得到左端；右端分别对应 $\log Q$ 项、无穷处 $\Gamma$-项与素数—素幂项，得 (EF)。

**注（与 S2–S6 的拼接）。** (EF) 的素数—素幂结构在尺度侧为等距点列；$\widehat h$ 的支撑/衰减给出沿尺度方向的窗函数；左端对零点的对称采样以中心轴为基准（S2 的横截、S5 的方向亚纯化），核选择可参照 S6 的变分准则。

---

## 4. 试验核选择的可检准则（接口版）

* **(K1) 中心对称。** $h$ 必为偶函数，使采样沿 $\Re s=\tfrac a2$ 对称，兼容功能方程。
* **(K2) 可交换性。** $\widehat h$ 的衰减/支撑应使 (EF) 中对 $(p,m)$ 的双和与无穷处项可在 S1+S4 的管域内**合法换序**。
* **(K3) 方向化匹配。** $\widehat h$ 的主质量中心与方差可按 S5 的"指数率—极点"与 S6 的方差律匹配，以增强特定谱带的灵敏度（定性）。
* **(K4) 二项局部化。** 欲突出某对局部共轭参数，可令 $\widehat h$ 于相应 $m\log p$ 邻域集中，利用 S2 的二项闭合形成"局部对消/增强"。

**常用族。** 高斯型 $h(t)=e^{-t^2/2}P(t^2)$（$\widehat h$ 同型指数衰减）；Paley–Wiener 型带限核（$\widehat h$ 紧支撑）；平滑窗的卷积封装便于 (K2)。

---

## 5. 接口化实例

### 5.1 Dirichlet $L(\chi,s)$（degree $1$）

取原始特征 $\chi$ 与模数 $q$。在 $a=1$ 归一化下

$$
\Lambda(\chi,s)=q^{s/2}\,\Gamma_{\mathbb R}(s+\lambda_\chi)\,L(\chi,s),\qquad
\lambda_\chi\in\{0,1\}\ \text{由奇偶性定},
$$

$$
\boxed{\ \Lambda(\chi,s)=\varepsilon(\chi)\,\Lambda(\bar\chi,1-s),\qquad |\varepsilon(\chi)|=1\ }.
$$

(EF) 专化为

$$
\sum_{\rho} h\!\left(i\big(\rho-\tfrac12\big)\right)
=\widehat h(0)\log q+\mathcal A_{\Gamma_{\mathbb R}}[h;\lambda_\chi]
-\sum_{p}\sum_{m\ge1}\frac{\log p}{p^{m/2}}\chi(p^m)\,\widehat h(m\log p).
$$

### 5.2 椭圆曲线 $L(E,s)$（degree $2$）

对 $E/\mathbb Q$ 的 Hasse–Weil 函数，取 $a=2$

$$
\Lambda(E,s)=N_E^{s/2}\,(2\pi)^{-s}\Gamma(s)\,L(E,s),\qquad
\Lambda(E,s)=\varepsilon(E)\,\Lambda(E,2-s),\ \ |\varepsilon(E)|=1,
$$

其中 $N_E$ 为 conductor。设局部迹 $a_{p^m}(E)$ 适当归一化，则

$$
\sum_{\rho} h\!\left(i\big(\rho-1\big)\right)
=\widehat h(0)\log N_E+\mathcal A_{\Gamma_{\mathbb C}}[h]
-\sum_{p}\sum_{m\ge1}\frac{\log p}{p^{m}}\,a_{p^m}(E)\,\widehat h(m\log p).
$$

度 $2$ 源于一个 $\Gamma_{\mathbb C}$ 因子，且与 S3–S4 的模板拼接一致。

---

## 6. 反例与边界族（失效原因标注）

* **R7.1（非有限阶 EM）。** 采用无穷阶伯努利展开将破坏一致可和并引入伪奇点；应坚持**有限阶**版本。
* **R7.2（非法换序）。** 若素数—素幂—无穷处三重求和/积分未受 S1+S4 约束，移线与留数计算即失合法性。
* **R7.3（核不对称/衰减不足）。** $h$ 非偶或 $\widehat h$ 衰减不足将破坏中心轴对称与素数端收敛。
* **R7.4（方向退化）。** 若归一化后 $\alpha_{p,j}$ 在尺度侧同速，方向化区分度下降（参见 S5 对退化的讨论）。

---

## 7. 统一"可检清单"（最小充分条件）

1. **完成功能方程。** 给出 $Q>0$、$a\in\mathbb R$、$r(s)$ 使 $\Lambda_{L}(s)=Q^{s/2}r(s)L(s)$ 且 $\Lambda_{L}(s)=\varepsilon\,\Lambda_{\tilde L}(a-s)$（$\tilde L$ 为 $L$ 的对偶/伴随）。
2. **欧拉积合法域。** 在 S1 管域/条带内明确绝对收敛与换序；素数端与 $\Gamma$-端求和/积分满足主导/一致条件。
3. **有限阶 EM。** 端点与离散—连续桥仅用**有限阶** EM；伯努利层与余项为整/全纯层，"极点 = 主尺度"。
4. **试验核。** $h$ 偶、带内全纯，$\widehat h$ 紧支撑或指数衰减；确保 (EF) 可交换与素数端可控。
5. **方向化/增长。** 用 $\Gamma/\pi$ 衰减与指数–多项式框架控制垂线增长与极点定位（S3+S5）。
6. **信息刻度（可选）。** 以 S6 的 $\Lambda$–$\Lambda^\ast$ 变分式指导核的谱带定位与窗宽选择（定性）。

---

## 8. 与其它篇章的接口

* **← S2（加法镜像与横截）。** 局部二项闭合与"平衡超平面"为素数端窗函数的局部化提供几何图像。
* **← S3（自反核—完成函数）。** $\Gamma/\pi$ 正规化与中心轴 $a$ 的对称构成完成函数模板。
* **← S4（有限阶 EM）。** 换序、端点与离散—连续桥均由**有限阶** EM 保障，"极点 = 主尺度"在 (EF) 的导出中自然呈现。
* **↔ S5（沿方向亚纯化）。** 方向化的极点/零结构与素数端的衰减/放大策略互补；指数–多项式律刻画极点阶与位置。
* **↔ S6（信息刻度）。** $\Lambda$ 的方差律与对偶为核选择与谱带定位提供信息—几何度量（定性）。

---

## 结语

本篇以母映射语法将"欧拉积—完成函数—显式公式"接口化：degree 与 conductor 在 $\Gamma/\pi$ 正规化与全局尺度 $Q$ 中得到统一记账；完成函数以中心轴 $a$ 的对称实现功能方程；显式公式把零集谱与素数端局部数据以同一核 $h$ 对偶缝合；有限阶 EM 保证解析合法性与"极点 = 主尺度"。与 S2–S6 的几何、对称、延拓、方向与信息结构共同构成面向一般 $L$-函数的**可检、可拼接、可移植**的统一接口。
