# S31. Fisher–Hartwig 型奇性与边缘放大

**—— de Branges–Mellin 局部化行列式的 $\log M_R$ 修正、局部参数矩阵与相位坐标的普适性**

Version: 1.1

## 摘要(定性)

在 de Branges 空间的相位—密度刻度下,考虑以窗 $w_R$ 局部化的投影型算子与符号 $a$ 所定义的对数行列式 $\mathscr F_R(\lambda)=\log\det(I+\lambda T_{a,w,R})$。在"带限 + Nyquist 取样 + 有限阶 Euler–Maclaurin (EM)"的换序纪律中,证明:当 $\log(1+\lambda a)$ 在有限多个相位点出现 Fisher–Hartwig(FH)型奇性(跳跃、根型尖点、相位扭转,及其叠加)时,除了强型 Szegő–Widom 极限的一阶平均与二阶 $H^{1/2}$ 能量项外,还出现由局部奇性驱动的 $\log M_R$ 级别修正。该 $\log M_R$ 项的系数仅由奇性处的局部指数—跳跃—扭转数据经一**二次型**给出,具有**相位坐标普适性**(不显含背景 de Branges 结构,背景仅通过相位体积 $M_R$ 接入)。多重奇性、多窗或非平稳拼接时,该修正满足**逐点/逐块可加**原则;在相位—密度阈值附近发生**边缘放大**,即 $M_R$ 的缩放改变但系数结构不变。中心化并剔除确定性项后,线性统计的涨落仍由 $H^{1/2}$ 能量控制并满足 CLT/MDP/LDP 与(在典型设定下的)模高斯型极限。上述结构在 Toeplitz/Wiener–Hopf 场景与 Riemann–Hilbert 的局部参数矩阵理论中得到印证。([Annals of Mathematics][1])

---

## 0. 设定与记号

### 0.1 de Branges 基线与相位—密度

取 Hermite–Biehler 整函数 $E$ 与 de Branges 空间 $\mathcal H(E)$。设
$$
E(x)=|E(x)|e^{-i\varphi(x)},\qquad \varphi'(x)>0,
$$
再生核 $K(\cdot,\cdot)$ 满足
$$
\frac{\varphi'(x)}{\pi}=\frac{K(x,x)}{|E(x)|^2} \quad \text{(a.e.)},
$$
据此以
$$
d\mu(x):=\frac{\varphi'(x)}{\pi}\,dx
$$
为基准测度,并以**相位坐标**
$$
u=\frac{\varphi(x)}{\pi}
$$
作同胚化;此时 $d\mu=du$。以上事实见 de Branges 原著与后续综述。([Purdue Mathematics][2])

### 0.2 局部化算子与对数行列式

给定偶窗 $w_R(t)=w(t/R)$(带限或指数型衰减),相位体积
$$
M_R:=\int_{\mathbb R} w_R(u)\,du.
$$
定义投影型局部化算子
$$
T_{a,w,R}=\int_{\mathbb R} a(x(u))\,w_R(u)\;\frac{|K(\cdot,x(u))\rangle\langle K(\cdot,x(u))|}{K(x(u),x(u))}\,du,
$$
并记生成函数
$$
\mathscr F_R(\lambda):=\log\det\bigl(I+\lambda T_{a,w,R}\bigr).
$$
在相位坐标中,$K$ 的**局部极限**为 sinc 型核,从而可视为带限投影的扰动;该"sine-kernel 普适性"在 de Branges 体系中已被系统阐述。([ScienceDirect][3])

### 0.3 FH 型奇性与窗口角点

在有限点集 $\mathcal S=\{u_p\}\subset\mathbb R$ 允许**Fisher–Hartwig 型奇性**,将
$$
\log\!\bigl(1+\lambda a(x(u))\bigr)=H(u)+\sum_{p\in\mathcal S} g_p(u;u_p),
$$
其中 $H\in C^{1,\alpha}(\mathbb R)$ 为平滑主部,$g_p$ 为以下原子之一或其乘积的对数:
$$
\text{跳跃: } g_p(u)=\Delta_p\,\mathbf 1_{(u>u_p)},\quad
\text{根型: } g_p(u)=\alpha_p\log|u-u_p|,\quad
\text{扭转: } g_p(u)= i\,\beta_p\,\mathrm{sgn}(u-u_p).
$$
若窗 $w_R$ 在若干 $u_b$ 处有台阶/角点,则此类效应不并入 $G$,而在 §4 单独记为窗角点贡献 $\Gamma^{(w)}_b\log M_R$,并与符号奇性可加。在 Toeplitz 与 Wiener–Hopf 情形,FH 奇性的指数—扭转载荷提供 $\log$-级修正是经典结论。([Annals of Mathematics][1])

### 0.4 取样与换序纪律

采用"带限 + Nyquist + 有限阶 EM"纪律:窗 $w_R$ 与核之卷积的频带被有效限制;在相位格点的 Nyquist 取样下别名(aliasing)为零;积分—求和换序仅用有限阶 Euler–Maclaurin,余项以伯努利层估计控制为 $o(1)$。相关背景参见 Poisson 求和/采样与 EM 余项估计。([buzsakilab.nyumc.org][4])

---

## 1. 平滑—奇性分离

**引理 1.1(分解与耦合小量)**
令
$$
H(u):=\text{平滑主部},\qquad G(u):=\sum_{p\in\mathcal S} g_p(u;u_p).
$$
则
$$
\mathscr F_R(\lambda)=\mathscr F_R\!\big|_{H}+\mathscr F_R\!\big|_{G}+\mathcal I_R(H,G),
$$
其中 $\mathcal I_R(H,G)=o(1)$,且在本节假设下
$$
\mathscr F_R\!\big|_{H}=M_R\langle H\rangle+\frac12\,\mathcal Q_R(H)+o(1),
$$
记 $\langle H\rangle:=M_R^{-1}\int_{\mathbb R} H(u)\,w_R(u)\,du$ 为窗平均零模,$\mathcal Q_R(H)$ 为投影二次型;其极限为相位坐标上的 $H^{1/2}$ 能量:
$$
\mathcal Q(H)=\frac{1}{4\pi^2}\iint_{\mathbb R^2}\frac{\big(H(u)-H(v)\big)^2}{(u-v)^2}\,du\,dv.
$$

*证明要点.* 对数行列式的 cumulant 展开
$$
\log\det(I+\lambda T)=\sum_{k\ge1}\frac{(-1)^{k+1}}{k}\lambda^k\operatorname{Tr}(T^k)
$$
在带限投影近似下将 $H$ 的贡献规约为 Toeplitz/Wiener–Hopf 型的强 Szegő 二次项,给出 $H^{1/2}$ 能量表示;$G$ 的贡献由局部参数矩阵主导,于第 2 节展开。耦合项 $\mathcal I_R$ 由核的局域性与有限阶 EM 控制为 $o(1)$。强型 Szegő 的二次项与其 $H^{1/2}$ 表示可参见 Simon 及相关综述。([math.caltech.edu][5])

---

## 2. 主定理:FH 型 $\log M_R$ 修正

**定理 2.1(一般形式)**
在第 0 节与第 1 节的假设下,有
$$
\boxed{\
\mathscr F_R(\lambda)=
M_R\,\langle H\rangle+\frac12\,\mathcal Q_R(H)
+\sum_{p\in\mathcal S}\Gamma_p(\lambda)\,\log M_R
+\mathcal C(\lambda;\mathcal S)+o(1)\,\ }
$$
其中 $\Gamma_p(\lambda)$ 为作用在局部数据的二次型,$\mathcal C$ 为常数级项。

**(i)可加性与局部性**
$\Gamma_p$ 仅依赖奇性点 $u_p$ 的局部数据 $(\alpha_p(\lambda),\beta_p(\lambda),\Delta_p(\lambda))$,与背景 $E$ 的全局信息无关;不同 $p$ 的贡献相加。

**(ii)相位坐标普适性**
$\Gamma_p$ 不显含 $\varphi'(x_p)$;背景几何仅通过 $M_R=\int w_R\,du$ 进入。

**(iii)窗角点**
若 $w_R$ 在 $u_b$ 含台阶/角点,则出现额外项 $\Gamma^{(w)}_b\log M_R$;其参数由台阶高度/角度给出,并与符号奇性可加。

*证明思路.* 采用 Riemann–Hilbert 方法对相位点 $u_p$ 建立局部参数矩阵(confluent hypergeometric/Bessel 型),与外解匹配得到 $\log$-级主项与常数项;该机制与 Toeplitz/Wiener–Hopf 的 FH 理论一致,其中 $\log\det$ 的 $\log n$ 系数由 FH 指数—扭转参数的二次型给出。对 Toeplitz 矩阵 $T_n(f)$ 有
$$
\log \det T_n(f)=n\,\widehat V_0+\sum_{k\ge1}k\,|\widehat V_k|^2
+\sum_j\big(\alpha_j^2-\beta_j^2\big)\log n + C + o(1),
$$
而 Wiener–Hopf 情形亦有完全平行的 $\log$-级别。将 $n$ 与本文的相位体积 $M_R$ 对应,即得陈述。([Annals of Mathematics][1])

> **注.** 在**自伴**情形(无纯相位扭转)二次型为正定;含**扭转**(单位模因子)时,经典 FH 公式显示 $\beta$-方向具**负符号**($\alpha^2-\beta^2$),故整体二次型呈 $(+,-)$ 的签名结构;本文所有"正定"表述均指对**幅度参数子空间**(无扭转)之正定,与 Toeplitz/Wiener–Hopf 文献一致。([Annals of Mathematics][1])

---

## 3. 三类原子奇性的系数结构

以下用 $\Gamma_p(\lambda)$ 的**二次型**(忽略可与模型标准化有关的常数归一)。

### 3.1 跳跃(phase step)

若 $g_p(u)=\Delta_p\,\mathbf 1_{(u>u_p)}$,则
$$
\Gamma_p(\lambda)=\mathsf Q_{\mathrm{st}}\!\big(\Delta_p(\lambda)\big),
\qquad \Delta_p(\lambda)\ \text{为}\ \log(1+\lambda a)\ \text{在}\ u_p\ \text{处的跳跃幅}.
$$
直观上,跳高越大,边界层匹配产生的相位不连续越强,$\log M_R$ 的"惩罚"越大;与 Toeplitz/Wiener–Hopf 的分段常数符号一致。([ScienceDirect][6])

### 3.2 根型(root/尖点)

若 $g_p(u)=\alpha_p\log|u-u_p|$,则
$$
\Gamma_p(\lambda)=\mathsf Q_{\mathrm{rt}}\!\big(\alpha_p(\lambda)\big),
$$
对应 Toeplitz FH 的 $\alpha^2$ 贡献。([Annals of Mathematics][1])

### 3.3 相位扭转(twist)

若 $g_p(u)= i\,\beta_p\,\mathrm{sgn}(u-u_p)$,则
$$
\Gamma_p(\lambda)= -\,\mathsf Q_{\mathrm{tw}}\!\big(\beta_p(\lambda)\big),
$$
负号对应 FH 公式中的 $-\beta^2$。([Annals of Mathematics][1])

### 3.4 组合奇性与交叉项

若上述原子叠加于同一点 $u_p$,则
$$
\Gamma_p(\lambda)=\mathsf Q_{\mathrm{FH}}\!\big(\alpha_p(\lambda),\beta_p(\lambda),\Delta_p(\lambda)\big),
$$
一般含交叉项(如"跳跃 × 扭转"),但在若干对称规范下可对角化。合并与**并合**(merging)奇性时,该系数在 Painlevé V 控制的转变区间中保持一致的二次依赖结构。([Project Euclid][7])

---

## 4. 边界层与窗角点的贡献

若窗 $w_R$ 在 $u_b$ 含台阶/角点,其对 $\mathscr F_R$ 的贡献与"符号跳跃"同型,可写作
$$
\Gamma^{(w)}_b\,\log M_R,\qquad
\Gamma^{(w)}_b=\mathsf Q_{\mathrm{st}}^{(w)}(\text{台阶/角度参数}).
$$
这是 Wiener–Hopf/反卷积框架中"截断+不连续符号"导致的边界修正之 1D 版本;在更高维截断区域可见 Widom–Sobolev 型两项公式与边界积分项。([arXiv][8])

---

## 5. 与二阶能量、涨落与偏差的耦合

**定理 5.1(中心化后之涨落普适性)**
记
$$
\widetilde{\mathscr F}_R(\lambda)
:=\mathscr F_R(\lambda)
- M_R\langle H\rangle-\tfrac12\,\mathcal Q_R(H)
-\sum_{p\in\mathcal S}\Gamma_p(\lambda)\log M_R
-\mathcal C(\lambda;\mathcal S).
$$
则在 $R\to\infty$ 时,高阶($\ge3$)累积量为 $o(M_R)$;在 $M_R^{-1/2}$ 归一后,$\widetilde{\mathscr F}_R(\lambda)$ 满足中心极限定理与中/大偏差原理;在适用场景下,还满足 mod-$\varphi$(含模高斯)框架的尾偏差精化。方差由 $H^{1/2}$ 能量给出。

*证明要点.* determinantal(或 biorthogonal)结构下的线性统计可用累积量计数与有限递推/带限投影分析,平滑部分的二次型给出协方差;FH 项仅改变确定性中心项。参见 Soshnikov、Breuer–Duits 与 Lambert 等的 CLT/累积量技术;mod-$\varphi$ 的精化参见 Féray–Méliot–Nikeghbali。([arXiv][9])

---

## 6. 多窗与非平稳拼接:可加原则

设 $\{w_R^{(\ell)}\}$ 构成 Parseval 紧帧拼接,$\sum_\ell w_R^{(\ell)}\to1$ 局部一致。则
$$
\sum_\ell \Gamma^{(\ell)}_p(\lambda)=\Gamma_p(\lambda),\qquad
\sum_\ell \mathcal Q_R^{(\ell)}(H)=\mathcal Q_R(H)+o(1).
$$
非 Parseval 情形可用帧乘子作等效符号修正后同式成立。帧与时频局部化算子(Daubechies)提供了上述分块—相加结构的抽象背景。([SpringerLink][10])

---

## 7. 证明框架(提要)

1. **cumulant 展开与可交换性**:$\log\det(I+\lambda T)$ 的迹级数在带限+Nyquist+有限阶 EM 下合法换序,余项 $o(1)$。([buzsakilab.nyumc.org][4])
2. **相位坐标化与核局域性**:由 de Branges 相位化得到近似带限投影(sinc 模型),据此得到强型 Szegő 的均值与 $H^{1/2}$ 二次项。([ScienceDirect][3])
3. **局部参数矩阵**:在每个 $u_p$ 处建立 confluent hypergeometric/Bessel 型参数矩阵,匹配外解获得 $\log M_R$ 主项与常数项。([Annals of Mathematics][1])
4. **并合与稳健性**:奇性并合由 Painlevé V 控制,$\log$ 系数保持二次依赖。([Project Euclid][7])
5. **Wiener–Hopf 与窗角点**:截断/角点的 FH 同型贡献给出额外的 $\log M_R$ 项。([ScienceDirect][6])

---

## 8. 例与模板

**例 1(单跳跃)**
$\log(1+\lambda a)=H+\Delta\,\mathbf 1_{(u>0)}$。则
$$
\mathscr F_R(\lambda)=M_R\langle H\rangle+\tfrac12\,\mathcal Q_R(H)
+\mathsf Q_{\mathrm{st}}(\Delta)\,\log M_R+\mathcal C+o(1).
$$
与分段常数符号的 Wiener–Hopf/Toeplitz 公式一致。([ScienceDirect][6])

**例 2(根型尖点)**
$\log(1+\lambda a)=H+\alpha\log|u|$。则
$$
\mathscr F_R(\lambda)=M_R\langle H\rangle+\tfrac12\,\mathcal Q_R(H)
+\mathsf Q_{\mathrm{rt}}(\alpha)\,\log M_R+\mathcal C+o(1).
$$
对应 FH 的 $\alpha^2$ 指数。([Annals of Mathematics][1])

**例 3(窗角点)**
平滑符号 + 台阶窗。则
$$
\mathscr F_R(\lambda)=M_R\langle H\rangle+\tfrac12\,\mathcal Q_R(H)
+\Gamma^{(w)}\,\log M_R+\mathcal C+o(1).
$$
$\Gamma^{(w)}$ 由台阶高度给出。([arXiv][8])

**例 4(组合奇性并合极限)**
在 $u_0$ 叠加跳跃+扭转+尖点并令两奇性并合:
$$
\Gamma_{u_0}=\mathsf Q_{\mathrm{FH}}(\alpha,\beta,\Delta)
\quad\text{(并合区间中保持二次依赖)}.
$$
可与 Painlevé V 转换相接。([Project Euclid][7])

---

## 9. 适用范围与失效边界

1. **无限阶 EM 禁用**:无穷级 EM 会引入伪奇性并放大边界层;本文仅用有限阶,余项 $o(1)$。([dlmf.nist.gov][11])
2. **非局部奇性**:若奇性沿区间连续分布,需将离散和替换为密度化积分,$\log M_R$ 项转化为相位积分。
3. **饱和/退化符号**:若 $a$ 在正测度区域饱和,需在非饱和域计算二阶能量;FH 项仍由局部数据给出。
4. **度量退化**:若 $\varphi'$ 退化,不使用相位化而回到一般 RKHS 的局部谱逼近。
5. **扭转项的符号**:含纯扭转时二次型的 $\beta$-方向为负(Toeplitz/Wiener–Hopf 经典符号);需按自伴/非自伴分别陈述。([Annals of Mathematics][1])

---

## 10. 可检清单

1. **相位—密度**:验证 $\varphi'(x)=\pi K(x,x)/|E(x)|^2>0$,取 $d\mu=du$。([Purdue Mathematics][2])
2. **奇性分解**:写 $\log(1+\lambda a)=H+\sum_p g_p$,记录 $(\alpha_p,\beta_p,\Delta_p)$。
3. **窗口规范**:带限或指数窗,Nyquist 取样,有限阶 EM;若有角点,记其等效跳跃。([buzsakilab.nyumc.org][4])
4. **主式与二阶**:算 $M_R\langle H\rangle$ 与 $\mathcal Q_R(H)$,核对 $H^{1/2}$ 极限。([math.caltech.edu][5])
5. **FH 修正**:逐点计算 $\Gamma_p=\mathsf Q_{\mathrm{st/rt/tw/FH}}$。([Annals of Mathematics][1])
6. **中心化涨落**:剔除主项 + 二阶 + $\sum_p\Gamma_p\log M_R+\mathcal C$ 后做 CLT/MDP/LDP/模$\varphi$ 检验。([arXiv][9])
7. **多窗拼接**:Parseval 紧帧下逐块相加;一般帧用帧乘子修正。([SpringerLink][10])

---

## 参考文献(选)

[1] P. Deift, A. Its, I. Krasovsky, *Asymptotics of Toeplitz, Hankel, and Toeplitz+Hankel determinants with Fisher–Hartwig singularities*, Ann. of Math. 174 (2011), 1243–1299. ([Annals of Mathematics][1])
[2] P. Deift, A. Its, I. Krasovsky, *On the asymptotics of a Toeplitz determinant with singularities*, MSRI Publ. 65 (2014). ([library.slmath.org][12])
[3] E. Basor, *Toeplitz and Wiener–Hopf determinants with piecewise continuous symbols*, J. Math. Anal. Appl. 96 (1983), 483–506. ([ScienceDirect][6])
[4] E. Basor, *Wiener–Hopf determinants with Fisher–Hartwig symbols*, arXiv:math/0205198. ([arXiv][13])
[5] B. Fahs, *Uniform Asymptotics of Toeplitz Determinants with Fisher–Hartwig Singularities*, Comm. Math. Phys. 383 (2021), 685–730. ([SpringerLink][14])
[6] T. Claeys, I. Krasovsky, *Toeplitz determinants with merging singularities*, Duke Math. J. 164 (2015), 2897–2987. ([Project Euclid][7])
[7] L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice–Hall, 1968. ([Purdue Mathematics][2])
[8] D. S. Lubinsky, *Universality limits for random matrices and de Branges spaces of entire functions*, J. Funct. Anal. 256 (2009), 3688–3729. ([ScienceDirect][3])
[9] B. Simon, *The Sharp Form of the Strong Szegő Theorem*, preprint; 以及专著 *Szegő's Theorem and Its Descendants*, Princeton, 2011. ([math.caltech.edu][5])
[10] I. Daubechies, *Time–Frequency Localization Operators*, IEEE TIT 34 (1988), 605–612. ([sites.math.duke.edu][15])
[11] P. Balazs et al., *Multipliers for continuous frames in Hilbert spaces*, J. Phys. A 45 (2012);以及 O. Christensen, *An Introduction to Frames and Riesz Bases*, 2nd ed., 2016. ([arXiv][16])
[12] A. Soshnikov, *Gaussian limit for determinantal random point fields*, arXiv:math/0006037;J. Breuer, M. Duits, *CLT for biorthogonal ensembles*, arXiv:1309.6224;G. Lambert, *Limit theorems for biorthogonal ensembles*, arXiv:1511.06121. ([arXiv][9])
[13] A. J. Jerri, *The Shannon sampling theorem—its various extensions and applications*, 1977;DLMF §2.10 *Euler–Maclaurin*;Poisson Summation 综述。([buzsakilab.nyumc.org][4])
[14] A. V. Sobolev 等,*On the Szegő formulas for truncated Wiener–Hopf operators*;*The Widom–Sobolev formula for discontinuous matrix-valued symbols*(2025 预印本)。([arXiv][8])

---

## 附:与经典理论的对照与解释

* 与 Toeplitz/Wiener–Hopf:本文的 $M_R$ 对应矩阵规模 $n$;FH 二次型的符号($\alpha^2-\beta^2$)与经典公式一致,窗角点的 $\log$-级别等价于不连续符号引入的 FH。([Annals of Mathematics][1])
* 与 Riemann–Hilbert:局部参数矩阵在奇性点采用合流超几何函数刻写;匹配外解给出 $\log M_R$ 系数与常数项(DIK)。([Annals of Mathematics][1])
* 与 de Branges 相位普适性:相位坐标下核趋于 sinc,二阶 $H^{1/2}$ 能量与 FH $\log$ 项分离,从而系数不显含 $\varphi'$(仅经 $M_R$ 入式)。([ScienceDirect][3])

---

**结论.**
在 de Branges–Mellin 的局部化行列式中,FH 型奇性以 $\log M_R$ 级别显影,系数由局部指数—跳跃—扭转数据经二次型给出,并对背景几何呈相位坐标普适性;二阶 $H^{1/2}$ 能量继续刻画涨落。该结构与 Toeplitz/Wiener–Hopf 的 FH 理论及 Riemann–Hilbert 局部参数矩阵完全同调,为多窗/非平稳框架与边缘放大的统一处理提供了可检与可拼装的公式体系。([Annals of Mathematics][1])

[1]: https://annals.math.princeton.edu/wp-content/uploads/annals-v174-n2-p12-p.pdf?utm_source=chatgpt.com "Asymptotics of Toeplitz, Hankel, and ..."
[2]: https://www.math.purdue.edu/~branges/Hilbert%20Spaces%20of%20Entire%20Functions.pdf?utm_source=chatgpt.com "Hilbert Spaces of Entire Functions - Purdue Math"
[3]: https://www.sciencedirect.com/science/article/pii/S0022123609000846/pdf?md5=cb07c57d051c8581122a1a67804f822d&pid=1-s2.0-S0022123609000846-main.pdf&utm_source=chatgpt.com "Universality limits for random matrices and de Branges ..."
[4]: https://buzsakilab.nyumc.org/datasets/PatelJ/_extra/Histology/jp-usb-1-data/data%20analysis/Data%20Analysis/Jerri_SamplingTheorem_Review_IEEE1977.pdf?utm_source=chatgpt.com "The Shannon Sampling Theorem-Its Various Extensions ..."
[5]: https://math.caltech.edu/SimonPapers/R43.pdf?utm_source=chatgpt.com "The Sharp Form of the Strong Szegő Theorem"
[6]: https://www.sciencedirect.com/science/article/pii/0022123683900101?utm_source=chatgpt.com "Toeplitz and Wiener-Hopf determinants with piecewise ..."
[7]: https://projecteuclid.org/journals/duke-mathematical-journal/volume-164/issue-15/Toeplitz-determinants-with-merging-singularities/10.1215/00127094-3164897.full?utm_source=chatgpt.com "Toeplitz determinants with merging singularities"
[8]: https://arxiv.org/abs/1801.02520?utm_source=chatgpt.com "On the Szegő formulas for truncated Wiener-Hopf operators"
[9]: https://arxiv.org/pdf/math/0006037?utm_source=chatgpt.com "Gaussian Limit for Determinantal Random Point Fields"
[10]: https://link.springer.com/book/10.1007/978-3-319-25613-9?utm_source=chatgpt.com "An Introduction to Frames and Riesz Bases"
[11]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[12]: https://library.slmath.org/books/Book65/files/140410-Deift.pdf?utm_source=chatgpt.com "On the asymptotics of a Toeplitz determinant with ..."
[13]: https://arxiv.org/abs/math/0205198?utm_source=chatgpt.com "Wiener-Hopf determinants with Fisher-Hartwig symbols"
[14]: https://link.springer.com/content/pdf/10.1007/s00220-021-03943-0.pdf?utm_source=chatgpt.com "Uniform Asymptotics of Toeplitz Determinants with Fisher– ..."
[15]: https://sites.math.duke.edu/~ingrid/publications/ieee34-1988.pdf?utm_source=chatgpt.com "Time-frequency localization operators: a geometric phase ..."
[16]: https://arxiv.org/pdf/1111.2440?utm_source=chatgpt.com "arXiv:1111.2440v2 [math.FA] 7 Feb 2012"
