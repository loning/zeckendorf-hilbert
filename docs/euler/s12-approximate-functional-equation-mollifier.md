# S12. 近似功能方程、mollifier 与共振法

**完成函数模板下的变分—误差一体化与可检实现**

**作者**：Auric
**日期**：2025-10-20

---

## 摘要

在完成函数与母映射的统一语法下，构造以"软窗"权重为核心的近似功能方程（AFE），并以信息势—凸对偶为准则设计 mollifier 与共振器（resonator）的谱最优模板。全流程以有限阶 Euler–Maclaurin（EM）为纪律，实现非渐近、可检的误差预算，并在 pretentious 与非 pretentious 区分治给出阈值机制。几何（支持函数与零集局部化）、信息（$\mathcal{L}$–$\mathcal{L}^\ast$ 对偶）与谱（迹公式核与放大）三侧严格对齐，且始终保持"极点 = 主尺度"的结构不变性。

---

## 0. 记号与前置（与 S2–S11 对齐）

1. **完成函数与功能方程.** 设

$$
\Lambda(s)=Q^{s/2}\,r(s)\,L(s),\qquad
\Lambda(s)=\varepsilon\,\Lambda^\ast(a-s),\ \ |\varepsilon|=1,
$$

其中 $Q>0$ 为 conductor 记账，$r(s)$ 由 $\Gamma/\pi$ 因子组成，并与 $Q^{s/2}$ **配平**使完成功能方程 $\Lambda(s)=\varepsilon\,\Lambda^\ast(a-s)$ 成立；对偶完成函数写作
$$
\Lambda^\ast(s)=Q^{s/2}\,r^\ast(s)\,L^\ast(s).
$$
$\Re s=\tfrac{a}{2}$ 为中心轴。对偶对象 $L^\ast$ 的 Dirichlet 系数记为 $a_n^\ast$；在自对偶/实系数情形 $a_n^\ast=a_n$。本文默认工作于 $r$ 与 $r^\ast$ 的极点之外的开子域（以及 $a-s$ 的对应子域）。

2. **母映射与信息刻度.** 离散谱写作 $\sum_j c_j e^{i\langle\alpha_j,\theta\rangle}e^{\langle\beta_j,\rho\rangle}$。信息势

$$
\mathcal{L}(\rho)=\log\sum_j |c_j|\,e^{\langle\beta_j,\rho\rangle},
$$

其梯度—Hessian 给出"有效质心—方差"度量与自然度量；$\mathcal{L}^\ast$ 表示其 Fenchel 对偶（S6）。

3. **有限阶 EM 与结构不变性.** 一切"和—积—积分—移线"均在**有限阶** EM 纪律下操作；伯努利层与余项对 $u$ **整**（带限窗时），对 $s$ 在工作域 $D$（去掉 $r$ 与 $r^{\ast}$ 的极点及其在 $a-s$ 下的对应点的开集）上**全纯**，极点仅来自主尺度项（S4）。

4. **非渐近误差三分解.** 数值窗/截断/采样误差按**别名（Poisson）+ 伯努利层（有限阶 EM）+ 窗尾（截断）**三分解（S8）。

5. **Pretentious 与几乎周期.** Pretentious 距离控制截断指数和的非渐近上界与大值窗口（S9）。

6. **几何—增长与迹公式.** 方向增长由支持函数上界与 Ronkin 凸性控制（S10）；Selberg/Kuznetsov 迹公式侧的试验核与本文窗函数同属一范畴（S11）。

7. **零集局部几何.** 二项闭合与横截给出零集余维 $2$ 与尺度局部化（S2）。

---

## 1. 软窗型近似功能方程（AFE）

令 $h:\mathbb{R}\to\mathbb{C}$ 为偶窗，$\widehat{h}$ 或带限，或具指数衰减。为进行移线与 Poisson/EM 操作，设 $h$ 在实轴上具有一条包含积分路径的**开竖条**上的解析延拓 $H$（当 $\widehat h$ 带限时由 Paley–Wiener 可知 $H$ 为整函数）。下文一律以 $H$ 记其解析延拓；并在实轴上约定 $H|_{\mathbb R}\equiv h$（即对一切 $t\in\mathbb R$，$H(t)=h(t)$），且取 $H$ 为偶的解析延拓并归一化 $H(0)=1$。记

$$
\mathcal{H}_s(u):=H(u)\,\frac{r(s+u)}{r(s)},\qquad
\mathcal{H}_{a-s}^{\ast}(u):=H(u)\,\frac{r^{\ast}(a-s+u)}{r^{\ast}(a-s)}.
$$

定义

$$
V_{+}(x;s):=\frac{1}{2\pi i}\int_{(\sigma)} \frac{H(u)}{u}\,\frac{r(s+u)}{r(s)}\,x^{-u}\,du,\qquad
V_{-}(x;s):=\frac{1}{2\pi i}\int_{(\sigma)} \frac{H(u)}{u}\,\frac{r^{\ast}(a-s+u)}{r^{\ast}(a-s)}\,x^{-u}\,du,
$$

其中 $\Re u=\sigma$ 取在工作竖条内。

### 定理 12.1（AFE：完成函数模板 + 有限阶 EM）

若 $\Lambda$ 满足功能方程与垂线增长控制，且 $h,r$ 满足 S4 与 S7 的换序/移线可检条件，则对一切满足
$$
\boxed{\ r(s)\ne0,\ r^{\ast}(a-s)\ne0\ \text{且在所用移线竖条内 $r(\cdot)$ 与 $r^{\ast}(a-\cdot)$ 无零/极点}\ }
$$
的 $s$ 有

$$
\boxed{
\Lambda(s)=\sum_{n\ge1}\frac{a_n}{n^{s}}\,
V_{+}\!\Big(\frac{n}{Q^{1/2}};s\Big)\
+\ \varepsilon\sum_{n\ge1}\frac{a_n^\ast}{n^{a-s}}\,
V_{-}\!\Big(\frac{n}{Q^{1/2}};s\Big)\ +\ R(s;h).
}
$$

其中 $R(\cdot;h)$ 在 $D$ 上**全纯**；若 $\widehat{h}$ 带限，则 $R$ 在垂线方向具有由带宽控制的**指数型增长上界**（对紧致竖条一致）。当 $L$ 含极点（例如 $s=1$）时，其极点及其阶**完全由 $u=0$ 留数对应的主尺度项给出**；$R(s;h)$ 仅由移线与有限阶 EM 产生的全纯/整层组成，不引入新的极点。

*证明要点.* 对 $\Lambda(s+u)$ 插入 $H(u)/u$ 的 Mellin 核并移线至 $\Re u=\pm \eta$；跨越 $u=0$ 处的留数（因 $H(0)=1$ 且核含 $1/u$）产生主尺度项；功能方程将"上半窗"转化为"下半窗"，得到双窗结构。欧拉积与和—积—积分互换在 S7 的合法域与 S4 的有限阶 EM 纪律下成立；伯努利层与余项全纯/整，归入 $R$。

---

## 2. mollifier 的变分设计与能量准则

取长度 $X$，考虑 Dirichlet 多项式

$$
M(s)=\sum_{n\le X}\frac{b_n}{n^s}.
$$

沿直线 $\Re s=\sigma$ 定义加权内积（Fourier 规范固定为 $\widehat w(\xi):=\int_{\mathbb R} w(t)\,e^{-i\xi t}\,dt$，不含 $2\pi$）

$$
\langle f,g\rangle_{w}:=\int_{\mathbb{R}} f(\sigma+it)\,\overline{g(\sigma+it)}\,w(t)\,dt,
$$

其中权函数取
$$
w\in L^1(\mathbb R),\qquad w(t)\ge 0\ \text{a.e.},\ \ w:\mathbb R\to\mathbb R,\qquad \int_{\mathbb R} w(t)\,dt\in(0,\infty).
$$
其 Gram 矩阵

$$
G_{mn}:=\langle n^{-s},m^{-s}\rangle_{w}
=(nm)^{-\sigma}\,\widehat w\!\big(\log(n/m)\big).
$$

在上述假设下，$G=[G_{mn}]$ **半正定**。为确保可逆，增加可检假设

$$
\boxed{\ |\widehat w(\xi)|\ge c_w>0\quad\text{于 }|\xi|\le\log X\ }\quad\text{（或至少 $\widehat w(\log(n/m))\ne0$ 对所有 $1\le m,n\le X$）},
$$

据此 $G$ 正定且可逆。**能量预算**采用同一 $L^2(w)$ 范数：

$$
\langle b,G b\rangle\ \le\ 1.
$$

（此处 $G$ 由 $\widehat w$ 给定，尺度由 $\int w$ 统一，见“期望与内积的归一化”。）

### 定理 12.2（最优 mollifier 的谱准则）

在预算 $\langle b,G b\rangle\le 1$ 且 $G$ 正定（由上文 $\widehat w$ 的下界假设保证）下，

$$
\max_{b}\ \Re\sum_{n\le X} b_n\,\overline{c_n}
\ =\ \sqrt{\langle c,G^{-1}c\rangle},\qquad
b^\star=\frac{G^{-1}c}{\sqrt{\langle c,G^{-1}c\rangle}},
$$

其中 $c=(c_n(s;h))_{n\le X}$ 来自 AFE 双窗与局部因子。

*证明要点.* Riesz 表示与 Cauchy–Schwarz 取等；正定性由 $w$ 与窗化内积保证。

**信息—变分对应.** 在 S6 的条件（记作 (F6.*)：Fenchel–Legendre 对偶成立、度量由 $\mathcal{L}$ 的 Hessian 诱导等）下，"最小能量—单位响应"的二次极小与"最小 KL—定向质心"的熵极小存在**由对偶诱导的对应**，并在该度量的二阶近似意义下**等价**。

**非 pretentious 区的能量上界.** 当 pretentious 距离有下界且满足频率分离与平滑窗约束时，二次平均的改良至多带来常数级增益；典型规模由 $A_\sigma(X)$ 控制，阈值折扣呈 $\exp\{-c\,\mathbb{D}^2\}$。为便于引用，本文取
$$
\boxed{\ A_\sigma(X):=\sqrt{\langle c,\ G^{-1}c\rangle}\ },\qquad c=(c_n(s;h))_{n\le X}\ \text{来自定理 12.1 的双窗系数}.
$$

---

## 3. 共振器与放大器（amplifier）的谱—几何模板

令

$$
\mathcal R(s)=\sum_{n\le Y}\frac{r_n}{n^s},\qquad
\mathcal{Q}[r]\ :=\ \mathbb{E}_{w}\!\left[\,|L(s)\,\mathcal R(s)|^2\,\right]\ =\ \langle r,\ \mathsf{K}\, r\rangle,
$$

其中核 $\mathsf{K}$ 由 AFE 双窗与系数自相关决定；在 Selberg/Kuznetsov 接口下，$\mathsf{K}$ 亦可包含 Bessel/余弦窗贡献（S11）。预算采用同一范数 $\langle r,G r\rangle\le 1$。

**期望与内积的归一化.** 令

$$
\boxed{\ \mathbb{E}_w[F]:=\frac{1}{\int_{\mathbb{R}}w(t)\,dt}\int_{\mathbb{R}}F(\sigma+it)\,w(t)\,dt\ },
$$

则 $\langle f,g\rangle_{w}=\big(\!\int w\big)\cdot \mathbb{E}_w[f\,\overline{g}]$。由此固定 $\mathsf{K}$ 与 $G$ 的尺度，并使广义谱半径无歧义。

### 定理 12.5（最优共振器：广义本征问题）

设 $\mathsf K$ 关于 $\langle\cdot,\cdot\rangle_w$ 为**自伴随**（等价地 $G^{-1}\mathsf K$ 为厄米）且半正定。在预算 $\langle r,G r\rangle\le 1$ 且 $G$ 正定（由上文 $\widehat w$ 的下界假设保证）下，使 $\mathcal{Q}[r]$ 取极大的 $r^\star$ 满足

$$
\boxed{\ \mathsf{K}\,r^\star=\lambda_{\max}\,G\,r^\star\ },\qquad
\mathcal{Q}[r^\star]=\lambda_{\max}.
$$

*证明要点.* 由厄米性可用广义 Rayleigh 商极大化；Rayleigh–Ritz 原理在正定约束下给出广义本征问题。当 $G=I$ 时退化为"$\mathsf{K}$ 的主特征向量"。

**Pretentious 区的大值窗口与稳健性.** 当 pretentious 距离在某尺度小且中心频率 $t\approx -\tau^\star$ 时，存在与谱间隙成比例的**大值窗口**使 $|L(s)\,\mathcal R^\star(s)|$ 达到 $A_\sigma$ 级放大；稳健性由 $\mathsf{K}$ 的谱间隙与窗带宽联合控制。

**迹公式侧的联合放大.** 选同族核 $h$（或其 $\mathcal{K}h$）可把谱侧放大与几何侧局部化统一至同一变分框架，令"素数—零/谱—几何"的两端窗形一致（S11）。为防归一漂移，本文采用权 $0$、级别 $1$ 的标准归一：
$$
\boxed{\ (\mathcal B^{-}h)(x)=\frac{4}{\pi}\int_0^\infty t\,h(t)\,K_{2it}(x)\,dt\ },
$$
其余定义与 S11 的 $\mathcal B^{\pm}$、$\mathcal C$ 保持一致。

---

## 4. 非渐近误差预算与"极点 = 主尺度"

（Fourier 规范）本节沿用 §2 的傅里叶记号：$\widehat f(\xi)=\int_{\mathbb R} f(t) e^{-i\xi t}\,dt$（不含 $2\pi$），据此 Nyquist 判据写作 $\Delta\le \pi/\Omega$。

为统一误差判据，本文在竖线积分中使用的"窗口化 integrand" 定义为（令积分线 $\Re u=c$ 取在工作竖条内，避开 $r(\cdot)$、$r^\ast(a-\cdot)$ 的极点；此条件已在定理 12.1 中陈述）
$$
\boxed{
g_{+}(t;s,x;c):=\frac{H(c+it)}{c+it}\,\frac{r(s+c+it)}{r(s)}\,x^{-c}\,x^{-it},\qquad
g_{-}(t;s,x;c):=\frac{H(c+it)}{c+it}\,\frac{r^\ast(a-s+c+it)}{r^\ast(a-s)}\,x^{-c}\,x^{-it}
}
$$
其中 $H$ 为 $h$ 的解析延拓，用作 Mellin 因子；在实轴上 $H(t)=h(t)$（$t\in\mathbb R$）。下文凡提及 $g$，一律指上述 $g_{\pm}$ 类型在 $t$ 变量下的 integrand；别名与 EM 估计均以其傅里叶变换 $\widehat g$ 与 $t$-导数有界性为准。

### 定理 12.7（AFE + 放大器的三分解误差）

将“近似”具体取为：对 $\int_{\mathbb R} g(t)\,dt$ 采用**等距步长 $\Delta$ 的梯形求积**并**截断于 $[-T,T]$**，再加入**$M$ 阶 Euler–Maclaurin 端点校正**；记其结果为 $\mathcal A_{\Delta,T,M}[g]$。假设 $g\in C^{2M}(\mathbb R)$ 且导数满足给定的有界/衰减条件（例如 $g^{(j)}\in L^\infty$ 或按需要的有权 $L^1$ 可积，$0\le j\le 2M-1$）。对任意窗 $h$、采样步长 $\Delta$、截断 $T$ 与 EM 阶 $M$，AFE 展开与 $M,\mathcal R$ 的插入所致误差满足

$$
\Big|\int_{\mathbb R}g(t)\,dt\ -\ \mathcal A_{\Delta,T,M}[g]\Big|
\ \le
\underbrace{\sum_{m\ne0}\big|\widehat{g}(2\pi m/\Delta)\big|}_{\text{别名}}
+\underbrace{\sum_{k=1}^{M-1} C_k\Delta^{2k}\cdot\max_{0\le j\le 2k-1}\!|g^{(j)}|_{\infty}}_{\text{伯努利层}}
+\underbrace{\int_{|t|>T}\!|g(t)|\,dt}_{\text{窗尾}}.
$$

若 $\operatorname{supp}\widehat{g}\subset[-\Omega,\Omega]$ 且 $\Delta\le\pi/\Omega$，别名项消失。

（注）此处 $\widehat g$ 为关于 $t$ 的傅里叶变换。即便 $\widehat h$ 带限，因含有 $1/(c+it)$ 以及 $r(s+c+it)/r(s)$ 与 $r^{\ast}(a-s+c+it)/r^{\ast}(a-s)$ 的比值，$\widehat g$ 仍可能不具紧支撑；实际选取步长 $\Delta$ 时应结合 Stirling 型增长界与带宽上界。

### 命题 12.8（"极点 = 主尺度"的保持）

在含 $1/u$ 的软窗 AFE 与有限阶 EM 框架下，双窗、mollifier/共振器插入与 EM 端点校正仅改变全纯/整层；**一切极点及其阶完全由 $u=0$ 留数对应的主尺度项决定**，不被 $R$ 或离散化校正改变（S4, S5）。

---

## 5. 几何—增长—信息三重对齐

### 定理 12.9（窗宽/方向选择的几何—信息准则）

令方向 $\mathbf{v}$ 与窗参数（带宽/指数衰减率）可选。最小化

$$
\mathcal{J}(\mathbf{v},\text{窗})=\text{窗尾}\ +\ \text{别名}\ +\ \text{伯努利层}\ -\ \lambda\cdot\text{灵敏度}
$$

等价于在 S10 的支持函数上界与 S6 的方差律所诱导的自然度量下求解一个带约束的变分问题；在所述正则带与参数范围内，若误差泛函具有强凸下界（由 S10 与 S6 诱导），则 $\mathcal J$ 为**严格凸**。其 Euler–Lagrange 方程与 S11 的核选择方程一致。

**零集局部化与窗形协同.** 当需针对某尺度带增强灵敏度时，窗的主质量应沿 S2 的"幅度平衡超平面"邻域配置；此时二项闭合给出零的局部控制，AFE—mollifier 的窗形在该带上最"经济"。

---

## 6. 失效族与边界机制

* **无窗/衰减不足**：$\widehat{g}$ 带宽过大导致别名主导，AFE 失稳。对策：带限或指数窗并收紧步长。
* **误把 EM 当无穷级**：无穷伯努利叠加伪造奇性并破坏一致可和。对策：仅取**有限阶**。
* **极端 pretentious**：非定向 mollifier 造成"假放大/平台"。对策：定向窗与谱间隙控制。
* **方向退化**：若 $\langle\beta_j-\beta_k,\mathbf{v}\rangle\equiv0$，一维切片退化。对策：改向或多向联合。
  可检触发阈值：若 $\displaystyle \min_{j\ne k}\big|\langle\beta_j-\beta_k,\mathbf v\rangle\big|\le \varepsilon$，则启用多方向/改向方案。
* **完成函数误用**：将 $\Gamma/\pi$ 因子逐项并入系数破坏刻度与能量度量。对策：完成函数仅作全局乘子。

---

## 7. 可检清单（最小充分条件）

1. **完成函数与条带**：给出 $(Q,a,r)$，验证 $\Lambda(s)=Q^{s/2}r(s)L(s)$ 与 $\Lambda(s)=\varepsilon\Lambda^\ast(a-s)$。
2. **窗与可交换性**：取偶窗 $h$（带限或指数衰减），与 S4 的**有限阶 EM**及 S7 的换序条件相容。
3. **AFE 构造**：按定理 12.1 形成双窗；余项纳入 $R$ 并以 S8 三分解给出常数。
4. **mollifier/共振器**：建立 $G$ 与能量预算 $\langle\cdot,G\cdot\rangle\le1$；依定理 12.2/12.5 取 $G^{-1}c$ 或求解 $\mathsf{K} r=\lambda G r$。
5. **Pretentious 检测**：计算/上界 pretentious 距离，据阈值决定放大或上界策略（S9）。
6. **方向与几何**：按 S10 的支持函数与 S2 的平衡超平面选方向/尺度带。
7. **结构不变性**：核对"极点 = 主尺度"在 AFE 与放大器插入后保持（§4）。
8. **迹公式协同（可选）**：在 S11 接口上选同族核 $h$，统一谱—几何侧窗形与误差度量。

---

## 8. 与既有篇章的接口

* **↔ S2（零集几何）**：窗形围绕平衡超平面；二项闭合给出零的局部模板。
* **↔ S3（完成函数）**：$\Gamma/\pi$ 因子提供垂线指数衰减与中心轴配平，统一 AFE 正规化。
* **↔ S4（有限阶 EM）**：保证和—积—积分互换的全纯/整函数性，维持"极点 = 主尺度"。
* **↔ S5（方向亚纯化）**：方向窗与极点定位一致；mollifier/共振器不改变极点位置与阶。
* **↔ S6（信息刻度）**：能量—灵敏度权衡与 $\mathcal{L}$–$\mathcal{L}^\ast$ 对偶一致。
* **↔ S7（$L$-函数接口）**：AFE 与显式公式共享核—窗，素数—零侧数据对偶缝合。
* **↔ S8（非渐近误差）**：给出窗—采样—截断的三分解常数与复现实验流程。
* **↔ S9（pretentious/指数和）**：大值窗口与放大阈值由 pretentious 距离决定。
* **↔ S10（几何—增长）**：支持函数上界与主导子和区决定方向窗宽与稳定性。
* **↔ S11（迹公式接口）**：统一试验核选择与谱—几何侧灵敏度泛函，实现双端放大。

---

## 结语

以软窗 AFE 为核心，将 mollifier 的二次变分最优、共振器的广义本征极值与 Nyquist–Poisson–EM 的非渐近误差三分解组织为一个可检、稳健且可实现的统一工具链。该工具链在几何、信息与谱三侧严格对齐（信息侧以 $\mathcal{L}$–$\mathcal{L}^\ast$ 对偶为准），并全程保持"极点 = 主尺度"，为平均值、点值大值、零间距及谱—几何联合放大等研究提供标准化模板。

---
