# S24. 带限偶子空间上的紧框架与对偶窗

**——移位系统的谱 Gram（纤维）表征、Wexler–Raz 双正交与"极点 = 主尺度"的框架保持**

## 摘要（定性）

在 Paley–Wiener 带限偶子空间中，本文以**均匀移位**的多窗族为骨架，建立**分析—合成**的**谱侧（纤维）Gram 表征**与**紧帧（Parseval 帧）**充要条件；对任意步长给出**矩阵 Gram 的一致谱界**判据（含必要维数与秩条件），在 Nyquist 纪律下退化为**标量**判据。进一步，以 Wexler–Raz 型双正交关系（含矩阵等价形式）刻画对偶窗的存在与显式构造；在 Nyquist 条件下帧算子为有界乘子，对任意有界 Borel 函数的功能演算**不引入新的零集**；对全纯（或实解析）功能演算，若带内窗谱为解析，则相应解析性**得以保持**；在偶窗下与镜像对合可交换。最后，以 BN–Bregman 几何与 KL–Pinsker 链给出对**乘子与窗扰动**的**李普希茨稳定性**，并概述对数（Mellin）尺度与离散图（Ihara ζ）上的并行框架。全篇严格采用 Poisson—Nyquist—Euler–Maclaurin（有限阶）三分解纪律与 S18/S22 的 Fourier 规范与缩放记号。

---

## 0. 设定与记号

**Fourier 规范与卷积**（与 S18/S22 一致）

$$
\widehat f(\xi)=\int_{\mathbb R} f(t)\,e^{-it\xi}\,dt,\qquad
f(t)=\frac1{2\pi}\int_{\mathbb R}\widehat f(\xi)\,e^{it\xi}\,d\xi,
$$

$\widehat{f*g}=\widehat f\cdot\widehat g$，$\widehat{fg}=\tfrac1{2\pi}\widehat f*\widehat g$。

**带限偶子空间与缩放**

$$
\mathsf{PW}_\Omega^{\mathrm{even}}
:=\Bigl\{\,w\in L^2(\mathbb R):\ \operatorname{supp}\widehat w\subset[-\Omega,\Omega],\ \ w(t)=w(-t)\,\Bigr\}.
$$

缩放 $w_R(t):=w(t/R)$ 满足 $\widehat{w_R}(\xi)=R\,\widehat w(R\xi)$；当 $R>1$ 时，时域拉伸对应频域压缩，带宽缩小到 $\Omega/R$。

**Nyquist—Poisson 纪律**

本文核心等式（定理 24.1、24.4）基于**Poisson 求和公式**在带限条件下的精确恒等；若某带限函数满足 $\operatorname{supp}\widehat f\subset[-\Omega,\Omega]$ 且 $\Delta\le\pi/\Omega$（Nyquist 条件），则频域周期复制无 alias 混叠（边界 $|\xi|=\Omega$ 属零测集，可忽略）。数值近似与 Euler–Maclaurin（EM）配方的细节见附录 B。

**移位多窗族**

给定步长 $\Delta>0$ 与窗组 $\mathbf w=(w_1,\dots,w_r)\subset\mathsf{PW}_\Omega^{\mathrm{even}}$，记

$$
\mathcal W(\mathbf w,\Delta):=\bigl\{\,w_\alpha(\cdot-n\Delta):\ \alpha=1,\dots,r,\ n\in\mathbb Z\,\bigr\}.
$$

---

## 1. 纤维化与谱 Gram 判据（一般步长与 Nyquist 退化）

设分析算子 $T_{\mathbf w,\Delta}:L^2(\mathbb R)\to \ell^2(\mathbb Z\times[r])$，

$$
(T_{\mathbf w,\Delta}f)_{n,\alpha}:=\langle f,\ w_\alpha(\cdot-n\Delta)\rangle .
$$

设基本带 $\mathcal B_\Delta:=[-\tfrac{\pi}{\Delta},\tfrac{\pi}{\Delta})$。定义

$$
\mathbf F(\xi):=\bigl(\widehat f(\xi+\tfrac{2\pi m}{\Delta})\bigr)_{m\in\mathbb Z},\qquad
\mathbf c_\alpha(\xi):=\frac{1}{\sqrt{\Delta}}\bigl(\overline{\widehat w_\alpha(\xi+\tfrac{2\pi m}{\Delta})}\bigr)_{m\in\mathbb Z},
$$

$$
\mathbf G(\xi):=\sum_{\alpha=1}^r \mathbf c_\alpha(\xi)\,\mathbf c_\alpha(\xi)^{\!*}\quad(\text{纤维 Gram 矩阵}).
$$

### 定理 24.1（一般步长的纤维 Gram 表征）

对任意 $f\in\mathsf{PW}_\Omega^{\mathrm{even}}$，定义活动 alias 集

$$
\mathcal M_\Omega(\xi):=\bigl\{\,m\in\mathbb Z:\ \bigl|\xi+\tfrac{2\pi m}{\Delta}\bigr|\le \Omega\,\bigr\},\qquad M(\xi):=|\mathcal M_\Omega(\xi)|.
$$

令 $\mathbf G_\Omega(\xi)$ 为 $\mathbf G(\xi)$ 在坐标子空间 $\mathbb C^{\mathcal M_\Omega(\xi)}\subset\ell^2(\mathbb Z)$ 的压缩（即仅保留 $m\in\mathcal M_\Omega(\xi)$ 的行列），$\mathbf F_\Omega(\xi)$ 亦仅取 $\mathcal M_\Omega(\xi)$ 分量。则

$$
\sum_{\alpha=1}^{r}\sum_{n\in\mathbb Z}\bigl|\langle f,\ w_\alpha(\cdot-n\Delta)\rangle\bigr|^2
=\frac{1}{2\pi}\int_{\mathcal B_\Delta}\!\left\langle \mathbf G_\Omega(\xi)\,\mathbf F_\Omega(\xi)\,,\,\mathbf F_\Omega(\xi)\right\rangle d\xi .
$$

从而 $\mathcal W(\mathbf w,\Delta)$ 为 $\mathsf{PW}_\Omega^{\mathrm{even}}$ 的帧，当且仅当存在常数 $0<A\le B<\infty$ 使

$$
A\ \le\ \lambda_{\min}\bigl(\mathbf G_\Omega(\xi)\bigr)\ \le\ \lambda_{\max}\bigl(\mathbf G_\Omega(\xi)\bigr)\ \le\ B
\qquad\text{对 a.e. }\xi\in\mathcal B_\Delta .
$$

等价地，也可用 $r\times r$ 生成元 Gram

$$
\mathbf H(\xi):=\Big[\frac{1}{\Delta}\sum_{m\in\mathbb Z}\overline{\widehat w_\alpha\!\Bigl(\xi+\frac{2\pi m}{\Delta}\Bigr)}\,\widehat w_\beta\!\Bigl(\xi+\frac{2\pi m}{\Delta}\Bigr)\Big]_{\alpha,\beta=1}^r
$$

给出同样的本质谱界判据：令 $C(\xi)=[\mathbf c_1(\xi)\ \cdots\ \mathbf c_r(\xi)]$（取活动别名分量），则 $\mathbf H(\xi)=C(\xi)^{*}C(\xi)$、$\mathbf G_\Omega(\xi)=C(\xi)C(\xi)^{*}$；二者非零特征值一致（由 $C^{*}C$ 与 $CC^{*}$ 的奇异值一致性，见 Horn–Johnson 定理1.3.20），故本质谱界等价。

*必要条件*（一般步长）：应有

$$
\boxed{\ r\ \ge\ \operatorname*{ess\,sup}_{\xi\in\mathcal B_\Delta} M(\xi),\ }
$$

且 $C(\xi)$ 在活动别名子空间对 a.e. $\xi$ 列满秩；Nyquist 时 $M(\xi)\equiv1$ 自动满足。

*证明要点*：由
$\sum_{n\in\mathbb Z}e^{in\Delta(\xi-\eta)}=\tfrac{2\pi}{\Delta}\sum_{m\in\mathbb Z}\delta(\xi-\eta-\tfrac{2\pi m}{\Delta})$
的 Poisson 公式，将移位求和化为频域周期复制，得到基本带上的纤维化表达；二次型右端以纤维 Gram 的特征值界控制。

### 推论 24.2（Nyquist 条件下的标量判据）

若 $\Delta\le\pi/\Omega$，则对 a.e. $\xi\in[-\Omega,\Omega]$ 仅 $m=0$ 在 $\mathcal M_\Omega(\xi)$ 中，$\mathbf G_\Omega(\xi)$ 退化为标量

$$
\mathcal G_{\mathbf w,\Delta}(\xi)=\frac{1}{\Delta}\sum_{\alpha=1}^{r}\bigl|\widehat w_\alpha(\xi)\bigr|^2,\qquad |\xi|\le\Omega.
$$

在边界 $\Delta=\pi/\Omega$ 时，别名仅可能在 $|\xi|=\Omega$ 的零测集合发生；所有判据与恒等等式均以 a.e. 成立，故不受影响（端点 $|\xi|=\Omega$ 为零测，数值实现时无需特殊处理）。

*数值实现提示*：当 $\Delta=\pi/\Omega$ 时，建议在带内采用半开区间 $[-\Omega,\Omega)$ 的采样/积分约定，以避免对零测端点的重复计数；理论等式均以 a.e. 成立，结论不受影响。

并有

$$
\sum_{\alpha,n}\bigl|\langle f,\ w_\alpha(\cdot-n\Delta)\rangle\bigr|^2
=\frac{1}{2\pi}\int_{-\Omega}^{\Omega}\mathcal G_{\mathbf w,\Delta}(\xi)\,|\widehat f(\xi)|^2\,d\xi.
$$

从而 $\mathcal W(\mathbf w,\Delta)$ 为帧当且仅当

$$
0<A\ \le\ \operatorname{ess\,inf}_{|\xi|\le\Omega}\mathcal G_{\mathbf w,\Delta}(\xi),\qquad
\operatorname{ess\,sup}_{|\xi|\le\Omega}\mathcal G_{\mathbf w,\Delta}(\xi)\ \le\ B<\infty .
$$

### 定理 24.3（Parseval 紧帧）

在 Nyquist 条件 $\Delta\le\pi/\Omega$ 下，$\mathcal W(\mathbf w,\Delta)$ 为 Parseval 当且仅当

$$
\boxed{\ \frac{1}{\Delta}\sum_{\alpha=1}^{r}\bigl|\widehat w_\alpha(\xi)\bigr|^2\equiv 1
\quad\text{a.e. on }[-\Omega,\Omega].\ }
$$

一般帧的界可取

$$
A=\operatorname{ess\,inf}_{|\xi|\le\Omega}\frac{1}{\Delta}\sum_{\alpha}\bigl|\widehat w_\alpha(\xi)\bigr|^2,\quad
B=\operatorname{ess\,sup}_{|\xi|\le\Omega}\frac{1}{\Delta}\sum_{\alpha}\bigl|\widehat w_\alpha(\xi)\bigr|^2.
$$

所有判据与恒等等式均以 a.e. 成立，故端点 $|\xi|=\Omega$ 为零测集，不影响结论；数值实现时无需对端点特殊处理。

---

## 2. Wexler–Raz 双正交与对偶窗

设合成族 $\widetilde{\mathcal W}(\widetilde{\mathbf w},\Delta):=\{\widetilde w_\alpha(\cdot-n\Delta)\}$。

### 定理 24.4（Wexler–Raz 条件：一般与 Nyquist 版）

以下两者等价：

**(i) 重构公式**：对一切 $f\in\mathsf{PW}_\Omega^{\mathrm{even}}$,

$$
f=\sum_{\alpha=1}^{r}\sum_{n\in\mathbb Z}\langle f,\ w_\alpha(\cdot-n\Delta)\rangle\,\widetilde w_\alpha(\cdot-n\Delta)
\quad(\text{在 }L^2\text{ 中收敛}).
$$

**(ii-a) 一般纤维条件**（任意 $\Delta>0$）：对 a.e. $\xi\in\mathcal B_\Delta=[-\tfrac{\pi}{\Delta},\tfrac{\pi}{\Delta})$ 与一切 $m,n\in\mathcal M_\Omega(\xi)$，

$$
\frac{1}{\Delta}\sum_{\alpha=1}^{r}
\overline{\widehat w_\alpha\!\Bigl(\xi+\frac{2\pi m}{\Delta}\Bigr)}\,
\widehat{\widetilde w_\alpha}\!\Bigl(\xi+\frac{2\pi n}{\Delta}\Bigr)
=\delta_{mn}\qquad(\text{a.e. }\xi\in\mathcal B_\Delta).
$$

**(ii-b) Nyquist 特例**（$\Delta\le\pi/\Omega$）退化为：

$$
\boxed{\ \frac{1}{\Delta}\sum_{\alpha=1}^{r}
\overline{\widehat w_\alpha(\xi)}\,\widehat{\widetilde w_\alpha}(\xi)\equiv 1,\qquad |\xi|\le\Omega .}
$$

等价地，矩阵式 WR 条件为

$$
\boxed{\ C_\Omega(\xi)\,\widetilde C_\Omega(\xi)^{*}=I_{M(\xi)}\quad\text{(a.e. }\xi\text{)}\ }
$$

其中 $C_\Omega(\xi)=[\mathbf c_{1,\Omega}(\xi)\ \cdots\ \mathbf c_{r,\Omega}(\xi)]\in\mathbb C^{M(\xi)\times r}$、$\widetilde C_\Omega(\xi)=[\widetilde{\mathbf c}_{1,\Omega}(\xi)\ \cdots\ \widetilde{\mathbf c}_{r,\Omega}(\xi)]\in\mathbb C^{M(\xi)\times r}$ 仅取活动别名分量，其列向量分别为

$$
\mathbf c_{\alpha,\Omega}=\frac{1}{\sqrt{\Delta}}\bigl(\overline{\widehat w_\alpha(\xi+\tfrac{2\pi m}{\Delta})}\bigr)_{m\in\mathcal M_\Omega(\xi)},\quad
\widetilde{\mathbf c}_{\alpha,\Omega}=\frac{1}{\sqrt{\Delta}}\bigl(\overline{\widehat{\widetilde w}_\alpha(\xi+\tfrac{2\pi m}{\Delta})}\bigr)_{m\in\mathcal M_\Omega(\xi)};
$$

上式逐分量等价于

$$
\frac{1}{\Delta}\sum_{\alpha=1}^{r}
\overline{\widehat w_\alpha\!\Bigl(\xi+\tfrac{2\pi m}{\Delta}\Bigr)}\,\widehat{\widetilde w_\alpha}\!\Bigl(\xi+\tfrac{2\pi n}{\Delta}\Bigr)=\delta_{mn}.
$$

矩阵尺寸为 $M(\xi)\times M(\xi)$。Nyquist 时 $M(\xi)\equiv1$ 退化为标量式 $\frac{1}{\Delta}\sum_{\alpha=1}^{r}\overline{\widehat w_\alpha(\xi)}\,\widehat{\widetilde w_\alpha}(\xi)\equiv 1$。

**（Nyquist 版正则对偶）** 若 $\Delta\le\pi/\Omega$ 且

$$
G(\xi):=\sum_{\alpha=1}^{r}\bigl|\widehat w_\alpha(\xi)\bigr|^2,\qquad |\xi|\le\Omega,
$$

在带内有正下界，则**正则对偶**由

$$
\widehat{\widetilde w_\alpha}(\xi)=\frac{\Delta}{G(\xi)}\,\widehat w_\alpha(\xi)\qquad(|\xi|\le\Omega)
$$

给出；当 $G\equiv\Delta$ 时为 Parseval 紧帧且 $\widetilde w_\alpha=w_\alpha$。

**（一般步长提示）** 若 $\Delta>\pi/\Omega$，则需用纤维矩阵的（伪）逆给出正则对偶（由 $C_\Omega(\xi)\,\widetilde C_\Omega(\xi)^{*}=I_{M(\xi)}$ 推导），不再简化为标量 $G^{-1}$。

---

## 3. 紧帧的存在：谱分配与偶性

### 定理 24.5（谱分配构造）

给定带内正有界 $H\in L^\infty([-\Omega,\Omega])$ 且 $0<c\le H\le C$。存在 $\mathbf w\subset\mathsf{PW}_\Omega^{\mathrm{even}}$ 使

$$
\sum_{\alpha=1}^{r}\bigl|\widehat w_\alpha(\xi)\bigr|^2=\Delta\,H(\xi)\quad\text{a.e. }|\xi|\le\Omega.
$$

**在 Nyquist 条件 $\Delta\le \pi/\Omega$ 下**，取 $H\equiv 1$ 得 Parseval 紧帧；若 $\Delta>\pi/\Omega$，上述谱分配仅确定标量能量形状，**不足以**保证 Parseval（因存在别名耦合，需要矩阵级单位性判据）。若需 $w_\alpha\in\mathsf{PW}_\Omega^{\mathrm{even}}$，则应附加假设 $H(\xi)=H(-\xi)$ a.e.（或在构造中改用 $\tfrac{H(\xi)+H(-\xi)}{2}$ 的对称化）；在此前提下，取对称可测的单位分解 $\{p_\alpha\}_{\alpha=1}^r\subset L^\infty([-\Omega,\Omega])$ 使

$$
\sum_{\alpha=1}^r |p_\alpha(\xi)|^2\equiv 1,\qquad p_\alpha(\xi)=p_\alpha(-\xi),
$$

并令

$$
\widehat w_\alpha(\xi)=\sqrt{\Delta\,H(\xi)}\,p_\alpha(\xi)\quad(|\xi|\le\Omega),\qquad \widehat w_\alpha(\xi)=0\quad(|\xi|>\Omega).
$$

若需光滑性，可先取带内留边的分片光滑 $p_\alpha$ 并在带内归一化；避免在频域做会扩展支集的卷积操作，以保持 $\operatorname{supp}\widehat w_\alpha\subset[-\Omega,\Omega]$。

*证明要点*：在 $H$ 为偶函数前提下，对称单位分解保持带限与偶性；模平方汇总即得目标能量分配。

---

## 4. 镜像与乘子—功能演算的零/非零结构保持

设镜像对合 $Jf(t)=f(-t)$。令帧算子

$$
S_{\mathbf w,\Delta}:=T_{\mathbf w,\Delta}^{*}\,T_{\mathbf w,\Delta}.
$$

在 Nyquist 条件下，频域作用为带内**点态乘子**

$$
\widehat{(S_{\mathbf w,\Delta}f)}(\xi)=\frac{G(\xi)}{\Delta}\,\widehat f(\xi),\qquad |\xi|\le\Omega,\quad G(\xi)=\sum_{\alpha=1}^{r}\bigl|\widehat w_\alpha(\xi)\bigr|^2.
$$

**乘子—功能演算的稳定性**：Nyquist 下 $S_{\mathbf w,\Delta}=M_b$ 为乘子（符号函数 $b(\xi)=G(\xi)/\Delta\in L^\infty([-\Omega,\Omega])$）；对任意**有界 Borel** 函数 $\varphi$，有

$$
\varphi(S_{\mathbf w,\Delta})=M_{\varphi\circ b}.
$$

因此其**零集**满足

$$
\boxed{\ \{\xi:\ (\varphi\circ b)(\xi)=0\}=b^{-1}\bigl(Z_\varphi\bigr),\ }
$$

即仅由 $\varphi$ 的零集经 $b$ 的**原像**决定（不会出现与 $b$ 无关的"新"零集）。若再要求 $\varphi$ **全纯（或实解析）**且带内 $\widehat w_\alpha$ 解析，则 $\varphi\circ b$ **保持解析性**（与谱定理的**功能演算–复合律**一致）；在此限定下，功能演算满足复合律 $g(\varphi(S))=(g\circ\varphi)(S)$，在乘子模型中即 $g(M_{\varphi\circ b})=M_{(g\circ\varphi)\circ b}$。当讨论**有界可逆性**（例如 $\varphi(z)=z^{-1}$ 在 $\inf_{|\xi|\le\Omega}G(\xi)>0$ 下），$S_{\mathbf w,\Delta}$ 及其逆均不产生新的零/非零结构。

**镜像对易性**：因每个 $w_\alpha$ 为偶函数，故 $\widehat w_\alpha(\xi)$ 为偶，从而 $G(\xi)=\sum_\alpha|\widehat w_\alpha(\xi)|^2$ 为偶；频域镜像 $J$（对应 $\xi\mapsto-\xi$）与乘子 $G$ 对易，因此 $J S_{\mathbf w,\Delta}=S_{\mathbf w,\Delta}J$。

---

## 5. 稳定性：BN–Bregman 几何与谱 Gram 扰动

记 $G(\xi)=\sum_\alpha|\widehat w_\alpha(\xi)|^2$、$\widetilde G(\xi)=\sum_\alpha|\widehat{\widetilde w}_\alpha(\xi)|^2$，并设
$\inf_{|\xi|\le\Omega}G(\xi)\ge \gamma>0$。

由正则对偶 $\widehat{\widetilde w_\alpha}(\xi)=\Delta\,G^{-1}(\xi)\,\widehat w_\alpha(\xi)$，一阶变分为

$$
\delta\widehat{\widetilde w_\alpha}(\xi)
=\Delta\Bigl(G^{-1}(\xi)\,\delta\widehat w_\alpha(\xi)- G^{-2}(\xi)\,\delta G(\xi)\,\widehat w_\alpha(\xi)\Bigr),\qquad |\xi|\le\Omega.
$$

**限定情形（仅重权，不改窗）**

当 $w_\alpha$ 固定、仅 $G\mapsto G+\delta G$ 时（$\delta\widehat w_\alpha=0$），正则对偶满足

$$
\sum_{\alpha=1}^r\bigl\|\delta\widehat{\widetilde w_\alpha}\bigr\|_{L^2([-\Omega,\Omega])}
\ \le\ \Delta\,\bigl\|G^{-2}\bigr\|_{L^\infty([-\Omega,\Omega])}\,\bigl\|\delta G\bigr\|_{L^\infty([-\Omega,\Omega])}
\sum_{\alpha=1}^r\bigl\|\widehat w_\alpha\bigr\|_{L^2([-\Omega,\Omega])}.
$$

**一般情形（窗亦扰动）**

若 $w_\alpha\mapsto w_\alpha+\delta w_\alpha$ 同时发生，则由三角不等式与上述一阶变分：

$$
\sum_{\alpha=1}^r\bigl\|\delta\widehat{\widetilde w_\alpha}\bigr\|_{L^2([-\Omega,\Omega])}
\ \le\ \Delta\,\bigl\|G^{-1}\bigr\|_{L^\infty([-\Omega,\Omega])}\sum_{\alpha=1}^r\bigl\|\delta\widehat w_\alpha\bigr\|_{L^2([-\Omega,\Omega])}
+\Delta\,\bigl\|G^{-2}\bigr\|_{L^\infty([-\Omega,\Omega])}\,\bigl\|\delta G\bigr\|_{L^\infty([-\Omega,\Omega])}
\sum_{\alpha=1}^r\bigl\|\widehat w_\alpha\bigr\|_{L^2([-\Omega,\Omega])}.
$$

上述两条估计的**前提是** $\inf_{|\xi|\le\Omega}G(\xi)\ge\gamma>0$，保证正则对偶在**Nyquist 条件**下逐点成立。

*注*：在 BN–Bregman 软目标的强凸—平滑结构下，参数—解映射与值函数对数据的扰动李普希茨稳定；KL–Pinsker 链将统计侧的 KL/TV 偏差转译为窗/对偶窗的范数偏差，详见附录或 S20 的信息—能量—敏感度不等式链。

---

## 6. 相关并行框架（背景展望）

**Mellin/Weyl–Heisenberg 作用**：在对数变量 $x=\log t$ 下，尺度平移与相位调制生成的 Weyl–Heisenberg 系统 $\{V_{n\sigma_0}U_{m\tau_0}w\}$ 给出时—频格上的多窗帧。其纤维—Gram 判据与 Wexler–Raz 条件与本文平行；Walnut/Janssen 表达式提供帧算子的核/符号表示；Nyquist 型采样对应格点面积的临界约束。

**离散图（Ihara ζ）并行**：在 $(q+1)$-正则图上，非回溯算子与邻接算子的谱由 Bass 恒等式联结；长度变量的"移位—循环"结构诱导离散频域的周期复制，可在长度格上构造离散版的窗化迹与谱 Gram 判据；完成函数的自倒数性带来中心轴对称，与本文的镜像纪律一致。

这些并行结构的完整技术展开见相关专题文献（Gröchenig, Walnut, Casazza–Christensen–Janssen）。

---

## 7. 可检清单（最小充分条件）

1. **空间与窗**：$\mathbf w\subset\mathsf{PW}_\Omega^{\mathrm{even}}$；必要时用 $w_R(t)=w(t/R)$ 记录带宽 $\Omega$。
2. **采样纪律**：Poisson 求和公式在带限下精确；Nyquist（$\Delta\le\pi/\Omega$）时别名为零；边界处零测集不影响 a.e. 恒等。
3. **帧判据**：一般步长用纤维 Gram $\mathbf G_\Omega(\xi)$ 在活动 alias 子空间的特征值界（域 $\mathcal B_\Delta$）；必要条件 $r\ge M(\xi)$ 且 $C(\xi)$ 列满秩；Nyquist 退化为标量 $\mathcal G_{\mathbf w,\Delta}$ 的本质上下界。
4. **对偶窗**：Wexler–Raz 一般（$\delta_{mn}$ 矩阵形式 $\boxed{C_\Omega(\xi)\,\widetilde C_\Omega(\xi)^{*}=I_{M(\xi)}}$，$M\times M$）；Nyquist 特例（标量式 $\sum_\alpha\overline{\widehat w_\alpha}\widehat{\widetilde w_\alpha}\equiv\Delta$）；**（Nyquist 版）** 正则对偶 $\widehat{\widetilde w_\alpha}=\dfrac{\Delta}{G}\widehat w_\alpha$。一般步长下正则对偶需由纤维矩阵（伪）逆给出。
5. **镜像—功能演算**：**（Nyquist 版）** $S_{\mathbf w,\Delta}=M_{b}$ 为带内乘子（$b=G/\Delta$）；对任意有界 Borel 函数 $\varphi$，$\varphi(S)=M_{\varphi\circ b}$（不引入新零集）；对**全纯/实解析** $\varphi$ 保持解析性并满足复合律 $g(\varphi(S))=(g\circ\varphi)(S)$。**（一般步长）** $S$ 的纤维为矩阵，不是标量乘子。偶窗下与 $J$ 可交换。
6. **稳定性**：前提 $\inf_{|\xi|\le\Omega} G(\xi)\ge\gamma>0$；一阶变分 $\delta\widehat{\widetilde w_\alpha}=\Delta(G^{-1}\delta\widehat w_\alpha - G^{-2}\delta G\,\widehat w_\alpha)$；限定/一般两版扰动界含 $\Delta$ 因子；BN–Bregman 与 KL–Pinsker 链路可传递统计侧偏差（详见附录/S20）。
7. **并行框架**：Mellin/WH、离散图 Ihara ζ 可调用 Walnut/Janssen 与 Bass 表达式（见§6）。

---

## 附录 A：Poisson—纤维化与 Gram 恒等式（证明细节）

对 $(n,\alpha)$，

$$
\langle f,\ w_\alpha(\cdot-n\Delta)\rangle
=\frac{1}{2\pi}\int_{\mathbb R}\widehat f(\xi)\,\overline{\widehat w_\alpha(\xi)}\,e^{in\Delta\xi}\,d\xi .
$$

对 $n$ 求和并用 Poisson 公式

$$
\sum_{n\in\mathbb Z}e^{in\Delta(\xi-\eta)}=\frac{2\pi}{\Delta}\sum_{m\in\mathbb Z}
\delta\!\Bigl(\xi-\eta-\frac{2\pi m}{\Delta}\Bigr),
$$

得到纤维化表达。因 $f\in\mathsf{PW}_\Omega^{\mathrm{even}}$，仅当 $m\in\mathcal M_\Omega(\xi)$ 时分量 $\widehat f(\xi+\frac{2\pi m}{\Delta})$ 非零，故二次型可压缩到活动纤维子空间 $\mathbb C^{\mathcal M_\Omega(\xi)}$：

$$
\sum_{n}\langle f,w_\alpha(\cdot-n\Delta)\rangle\overline{\langle f,w_\beta(\cdot-n\Delta)\rangle}
=\frac{1}{2\pi}\int_{\mathcal B_\Delta}\!\left\langle \mathbf c_{\alpha,\Omega}(\xi),\mathbf F_\Omega(\xi)\right\rangle
\overline{\left\langle \mathbf c_{\beta,\Omega}(\xi),\mathbf F_\Omega(\xi)\right\rangle}d\xi,
$$

其中下标 $\Omega$ 表示仅取活动 alias 分量。对 $\alpha$ 求和即得定理 24.1 的纤维 Gram 表达。Nyquist 下 a.e. $\mathcal M_\Omega(\xi)=\{0\}$，退化为标量判据。

---

## 附录 B：Euler–Maclaurin 配方（数值近似的补充细节）

本文核心定理基于带限条件下的 Poisson 求和**精确恒等**，不依赖数值近似。当需要估计有限和 $\sum_{k=-N}^{N} g(k\Delta)$ 与积分 $\int g$ 的误差时，可用有限阶 EM：

$$
\sum_{k=-N}^{N} g(k\Delta;\zeta)
=\frac1{\Delta}\int g(t;\zeta)\,dt+\frac{g(N\Delta;\zeta)+g(-N\Delta;\zeta)}{2}
+\sum_{j=1}^{p}\frac{B_{2j}}{(2j)!}\Delta^{2j-1}\bigl(g^{(2j-1)}(N\Delta;\zeta)-g^{(2j-1)}(-N\Delta;\zeta)\bigr)+R_p(\zeta),
$$

其中 $B_{2j}$ 为 Bernoulli 数。若 $g(\cdot;\zeta)$ 关于参数 $\zeta$ 全纯且端点依赖多项式/指数有界，则端点层与余项 $R_p(\zeta)$ 对 $\zeta$ 全纯，不引入新奇点。此配方仅在数值计算或误差分析时使用（NIST DLMF §2.10、§24.7）。

---

## 9. 与前序理论的接口

### 9.1 S15：Weyl–Heisenberg 协变与窗函数诱导的内积

- S24 的移位多窗族 $\mathcal W(\mathbf w,\Delta)$ 在对数域上与 Weyl–Heisenberg 系统 $\{V_{n\sigma_0}U_{m\tau_0}w\}$ 平行；
- S15 中窗函数诱导的 RKHS 内积与 S24 的纤维 Gram 结构一致：帧算子 $S_{\mathbf w,\Delta}$ 的频域乘子对应于 S15 的再生核算子。

### 9.2 S16：de Branges 规范系统与辛结构

- 帧算子 $S_{\mathbf w,\Delta}$ 的频域点态乘子 $G(\xi)/\Delta$ 为有界函数；若窗函数 $\widehat w_\alpha$ 在工作条带内解析，则 $G(\xi)$ 亦解析，此时与 S16 中 Hamiltonian 在规范系统下的辛流保持解析性一致；
- 镜像对合 $J$ 与 S16 的共轭对称 $\sigma_2J$ 相容：偶窗保证 $[S_{\mathbf w,\Delta},J]=0$。

### 9.3 S17：散射—酉性与相位—行列式公式

- 若将 $S_{\mathbf w,\Delta}$ 视为散射算子的"测量实现"，则其频域乘子 $G/\Delta$ 对应于 S17 中散射相位 $\delta(E)$ 的导数密度；
- Wexler–Raz 的重构条件 $\frac{1}{\Delta}\sum_\alpha\overline{\widehat w_\alpha}\widehat{\widetilde w_\alpha}\equiv 1$ 类似于 S17 的酉性条件 $S^\dagger S=I$。

### 9.4 S18：窗不等式与半范数测度化

- S24 的 Nyquist 条件 $\Delta\le\pi/\Omega$ 确保别名消失，对应 S18 中带限乘积 $F=wR\cdot(h\star\rho)$ 的别名条件 $\Delta\le\pi/(\Omega_w+\Omega_h)$；
- 帧界 $A,B$ 的本质上下确界判据即 S18 的窗加权半范数 $\|f\|_{w,\Delta}$ 的等价常数。

### 9.5 S19：光谱图与非回溯—邻接关系

- 离散图上的长度—循环框架（§6）与 S19 的 Ihara ζ 函数通过 Bass 恒等式联结；
- 频域周期复制（纤维化）对应于 S19 中非回溯算子谱在单位圆周的分布。

### 9.6 S20：BN 投影、KL 代价与 Bregman 敏感度

- S24 的稳定性分析（§5）直接调用 S20 的 BN–Bregman 软目标：正则对偶的扰动界由 $G^{-1}$ 与 $G^{-2}$ 控制，对应 S20 的 Hessian $\nabla^2\Lambda$ 的逆与二阶导数；
- KL–Pinsker 链将统计侧的 KL/TV 偏差转译为窗/对偶窗的 $L^2$ 范数偏差，与 S20 的信息—能量—敏感度不等式链一致。

### 9.7 S21：连续谱阈值与奇性稳定性

- S24 的"功能演算零/非零结构保持"（§4）即 S21 的奇性非增定理：帧算子的频域乘子 $G/\Delta\in L^\infty$ 仅以有界 Borel 函数叠加，故功能演算不引入新零集；若 $\widehat w_\alpha$ 解析则保持解析性；
- 扰动稳定性（§5）对应 S21 的 Bregman–KL 敏感度链在阈值邻域的稳定半径。

### 9.8 S22：窗/核最优化与变分原理

- S24 的 Parseval 紧帧条件 $\frac{1}{\Delta}\sum_\alpha|\widehat w_\alpha|^2\equiv 1$ 即 S22 中带限偶窗的"总能量守恒"约束；
- 谱分配构造（定理 24.5）对应 S22 的 L² 强凸变分问题：给定目标 $H(\xi)$，通过对称单位分解与带内平滑实现最优窗组，与 S22 的频域核型 Euler–Lagrange 方程一致。

### 9.9 S23：多窗协同优化与 Pareto 前沿

- S24 的 Wexler–Raz 双正交条件（定理 24.4）推广了 S23 的广义 Wexler–Raz 关系：当窗族线性无关时退化为 $\delta$-型正交，冗余时保留 $GG^\dagger$-型；
- 纤维 Gram 矩阵 $\mathbf G(\xi)$ 的特征值界对应 S23 的帧算子 Gram 矩阵 $G$ 的条件数监控 $\kappa(G)$；
- S24 的谱分配构造可作为 S23 的 Pareto 前沿搜索算法的初始点：通过调整 $H(\xi)$ 的形状实现不同窗族间的协同最优。

---

## 参考文献（选）

* A. Ron, Z. Shen, *Frames and Stable Bases for Shift-Invariant Subspaces of $L^2(\mathbb R^d)$*, Canad. J. Math. **47** (1995), 1051–1094.
* K. Gröchenig, *Foundations of Time–Frequency Analysis*, Birkhäuser, 2001.
* I. Daubechies, *Gabor Time–Frequency Lattices and the Wexler–Raz Identity*, J. Fourier Anal. Appl. **1** (1995), 437–478.
* D. Walnut, *Continuity Properties of the Gabor Frame Operator*, J. Math. Anal. Appl. **165** (1992), 479–504.
* E. M. Stein, R. Shakarchi, *Fourier Analysis: An Introduction*, Princeton Univ. Press, 2003.
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge Univ. Press, 2013.
* NIST DLMF, §2.10/§24.7（Bernoulli/Euler 多项式与 EM 配方）。

---

**结语**

本文以**纤维化的 Gram 判据**（含必要维数与秩条件）统一刻画带限偶子空间中**均匀移位**多窗族的帧/紧帧结构，并以 **Wexler–Raz** 条件（一般步长的 $\delta_{mn}$ 矩阵形式 $C_\Omega\widetilde C_\Omega^{*}=I_{M(\xi)}$（$M\times M$ 矩阵）与 Nyquist 的标量特例）给出对偶窗的存在与显式表达；在 Nyquist 纪律下，所有判据与构造退化为**标量**的"带内能量分配"，可直接以 $\sum_\alpha |\widehat w_\alpha|^2$ 控制。整个分析基于 **Poisson 求和公式**在带限条件下的精确恒等，保证**镜像与零/非零结构保持**；Borel 功能演算不引入新零集，全纯/实解析功能演算下（在带内窗谱解析前提）解析性**得以保持**（复合律 $g(\varphi(S))=(g\circ\varphi)(S)$）；稳定性则由正则对偶的微扰分析给出，可与 BN–Bregman 与 KL–Pinsker 链路结合。该框架与 S15–S23（Weyl–Heisenberg、de Branges 规范系统、散射—酉性、窗不等式、光谱图、BN 投影、连续谱阈值、窗/核最优与多窗协同）接口一致，并可自然推广至对数（Mellin）尺度与离散图谱情形（见§6）。
