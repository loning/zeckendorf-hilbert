# S21. 连续谱阈值与奇性稳定性

—— Weyl–Titchmarsh 相位—密度、散射通道与窗化误差的阈值判据

## 摘要（定性）

在一阶辛型规范系统与 de Branges—Herglotz—Clark 词典下，本文把**阈值**刻画为 Weyl–Titchmarsh 函数的边界虚部（谱密度）与散射总相位导数的退化点；把**稳定性**刻画为在**有限阶** Euler–Maclaurin（EM）换序与 Nyquist–Poisson–EM 三分解（"别名/伯努利层/截断"）纪律下，奇性集合（含极点/零点）与其阶在窗化与近似中保持不变或仅作可定界的局部位移。核心同一式

$$
\varphi'(x)=\Im m(x+i0)=\pi\,\rho(x)
$$

把 de Branges 相位导数、Weyl–Titchmarsh 函数的边界虚部与绝对连续谱密度统一；由散射—内函数—功能方程词典得

$$
\partial_x\arg\det S(x)=-2\,\varphi'(x)=-2\pi\,\rho(x),
$$

从而阈值即散射相位的临界点。本文进一步以 Rouché 定理给出零集的定量**稳定半径**，并在 Bregman–KL 灵敏度框架下给出窗化近似对 $\rho$ 与 $\varphi'$ 的**可检偏差界**。全文坚持"**极点 = 主尺度**"的纪律与纯数学体例。

---

## 0. 设定与预备

### 0.1 规范系统、Weyl 函数与谱密度

设 $J=\begin{psmallmatrix}0&-1\\1&0\end{psmallmatrix}$，取一阶辛型规范系统

$$
J\,Y'(t,z)=z\,H(t)\,Y(t,z),\qquad H(t)=H(t)^{!*}\succeq0,\quad t\in[0,\infty),
$$

并假定 $\int_0^\infty \mathrm{tr}\,H(t)\,dt=+\infty$。对每个 $z\in\mathbb C^+$ 存在唯一（至常数）Weyl 解，Weyl–Titchmarsh 函数 $m:\mathbb C^+\to\mathbb C^+$ 属 Herglotz 类，具有表示

$$
m(z)=a\,z+b+\!\int_{\mathbb R}\Big(\frac{1}{t-z}-\frac{t}{1+t^2}\Big)\,d\mu(t),\qquad a\ge0,~b\in\mathbb R,
$$

其中 $\mu$ 为非负 Borel 测度。绝对连续谱密度

$$
\rho(x)=\frac{d\mu_{\rm ac}}{dx}(x)=\frac{1}{\pi}\,\Im m(x+i0)\quad\text{（a.e.\ }x\in\mathbb R).
$$

### 0.2 de Branges—Herglotz 词典与相位—密度同一

取 Hermite–Biehler（HB）整函数 $E$，使 de Branges 空间 $\mathcal H(E)$ 与上节规范系统等价。写

$$
E^\sharp(z):=\overline{E(\overline{z})},\qquad U(z):=\frac{E^\sharp(z)}{E(z)},\qquad E(x)=|E(x)|\,e^{-i\varphi(x)}.
$$

> 注（Clark–Cayley 与 $M$ 函数、测度区分）：令 $E=A-iB$（$A,B$ 为实整函数），则
>
> $$
> U=\frac{A+iB}{A-iB},\qquad M(z):=i\,\frac{1+U(z)}{1-U(z)}=-\frac{A(z)}{B(z)}
> $$
>
> 亦为 Herglotz/Nevanlinna 函数。但因 $|U(x)|=1$ a.e.，故 $M(x)\in\mathbb R$ a.e.，$\Im M(x+i0)=0$。$M$ 的 Aleksandrov–Clark 测度 $\sigma_\alpha$ 一般纯奇或奇/绝对连续混合，不等于 Weyl–Herglotz 表示中的 $\mu$；二者仅在特殊规范与正则性下可比较。本文所用的谱测度 $\mu$ 与密度 $\rho$ 来自下述 Weyl–Titchmarsh 函数 $m$ 的 Herglotz 表示，**一律以 $\mu$ 定义 $\rho$，不以 $M$ 定义**。

在与所给规范系统配对的**标准 de Branges 生成元** $E$ 下，存在 Weyl–Titchmarsh 函数 $m\in\mathcal N$（Nevanlinna/Herglotz 类，$\Im m(z)>0$ 于 $\mathbb C^+$），其非切边界值满足

$$
\boxed{~\varphi'(x)=\Im m(x+i0)=\pi\,\rho(x)\quad\text{（a.e.\ }x).~}
\tag{0.1}
$$

**当且仅当** $E$ 来自该规范系统的**标准归一**且在 $\mathbb R$ 上无零时，有 $m(z)=-E'(z)/E(z)$；否则仅在实轴上有 $\Im(-E'/E)(x)=\varphi'(x)$ 的边界关系，不能据此认定 $-E'/E$ 为 Herglotz。更换 Weyl 边界将使 $m$ 发生 Möbius 变换 $m\mapsto(\alpha m+\beta)/(\gamma m+\delta)$，本同一式需随规范重申。

并且由再生核 $K(\cdot,\cdot)$ 的经典公式得到

$$
\boxed{~\varphi'(x)=\frac{\pi\,K(x,x)}{|E(x)|^2}>0~,}
\tag{0.2}
$$

从而相位在非奇异区间严格单调，并有 $\delta'(x)=-2\pi\rho(x)\le0$（**物理上相位随能量非增**）。

### 0.3 散射矩阵与总相位（单通道归一）

**假设**：与自由参照系构成**短程散射对**（如一维 Schrödinger 短程势，或等价的迹类/限制性条件），并以 Jost 解归一，使 Wronskian 与通量归一一致。则存在与 $x$ 无关的 unimodular 常数 $c_0$（**与能量无关的相位常数**），使二维散射矩阵 $S(x)\in\mathrm U(2)$ 满足

$$
\boxed{~\det S(x)=c_0\,U(x)^{-1}=c_0\,e^{-2i\varphi(x)}~}\qquad\text{（a.e.\ }x\in\mathbb R).
\tag{0.3}
$$

（注：由 §0.2 的定义 $U:=E^\sharp/E$ 及 $E(x)=|E(x)|e^{-i\varphi(x)}$，得 $U(x)=e^{+2i\varphi(x)}$，故 $U^{-1}=e^{-2i\varphi}$）

上式在上述短程性/限制性条件与 Wronskian 归一下成立；在更一般场景中应改用谱移函数 $\xi$ 表述：$\det S=e^{-2\pi i\xi}$、$\xi'=\rho$，从而仍得 $\delta'=-2\pi\rho$。

> **多通道推广**：多通道情形下 $\partial_x\arg\det S=-2\pi\,\mathrm{tr}\,\rho$（或用 $\xi'=\mathrm{tr}\,\rho$），其余结论逐点沿用。

### 0.4 窗化与**有限阶** EM 三分解

取偶窗/偶核 $\psi$（带限或指数衰减），尺度 $R>0$，设 $\psi_R(x)=\psi(x/R)$。连续—离散换序仅使用**有限阶** EM：

$$
\sum_{n=a}^{b} f(n)=\int_a^b f(x)\,dx+\sum_{k=1}^{M}\frac{B_{2k}}{(2k)!}\!\left(f^{(2k-1)}(b)-f^{(2k-1)}(a)\right)+\mathcal R_M,
$$

由此得到**非渐近**误差三分解

$$
\boxed{~\text{error}=\text{alias}+\text{Bernoulli layer}+\text{tail}~},
\tag{0.4}
$$

在"带限 + Nyquist"条件下 $\text{alias}=0$。

### 0.5 信息几何与灵敏度

在 BN–Bregman 框架中，引入势 $\Lambda$（$\mu$-强凸、$L$-平滑），软目标

$$
g(X)=\frac12|X-F|^2+\Lambda^\ast(X),
$$

并以**Pinsker（单侧上界）**不等式 $\mathrm{TV}\le \sqrt{\mathrm{KL}/2}$ 作为 KL–TV 链接的度量桥；若需由 TV 估计 KL，应显式声明只能得到**单侧**结论。

---

## 1. 阈值与共振：定义与基本性质

**定义 21.1（连续谱阈值）**
$x_0\in\mathbb R$ 为**阈值**，若 $\rho(x_0)=0$，且 $\rho$ 在 $x_0$ 以有限阶 $\kappa\ge0$（**实数**）消失：存在邻域与常数 $c>0$ 使 $\rho(x)\sim c\,|x-x_0|^\kappa$（$x\to x_0$）。称 $\kappa$ 为阈值阶，定义为**最小非负实数**使得 $\limsup_{x\to x_0}|x-x_0|^{-\kappa}\rho(x)>0$。

**定义 21.2（函数级共振）**
$z_0\in\mathbb C$ 为**共振**，若 $E(z_0)=0$ 且 $\Im z_0<0$；当 $z_0\to\mathbb R$ 的极限点存在时称**临界共振**。

**命题 21.3（相位—密度—阈值）**
$\varphi'(x)=\pi\,\rho(x)$ a.e.。故 $x_0$ 为阈值 $\Longleftrightarrow\ \varphi'(x_0)=0$，阈值阶等于 $\varphi'$ 的零阶。
*证明*：由 (0.1)。$\square$

---

## 2. 散射判据与相位单调性（单通道归一）

**定理 21.4（散射相位导数判据）**
令 $\delta(x):=\arg\det S(x)$ 取连续分支。则

$$
\boxed{~\delta'(x)=\partial_x\arg\det S(x)=-2\,\varphi'(x)=-2\pi\,\rho(x)~}.
$$

因此 $x_0$ 为阈值 $\Longleftrightarrow\ \delta'(x_0)=0$。
*证明*：由 (0.3)，$\det S(x)=c_0 U(x)^{-1}=c_0 e^{-2i\varphi(x)}$，故 $\delta(x)=\arg(c_0)-2\varphi(x)$，从而 $\delta'(x)=-2\varphi'(x)=-2\pi\rho(x)$（由 (0.1)）。亦可由 Birman–Krein 公式 $\det S=e^{-2\pi i\,\xi}$、$\xi'=\rho$ 推出。$\square$

**推论 21.5（单调与临界）**
若开区间 $I$ 上 $\rho>0$，则 $\delta$ 在 $I$ 上严格单调；若 $\rho$ 在 $x_0$ 为二阶（及以上）接触，则 $\delta$ 在 $x_0$ 为平坦临界。

---

## 3. "极点 = 主尺度"与窗化不改奇性

令 $\Xi(s)$ 为解析母对象（如轨道/谱侧配对 $\langle F,k_s\rangle$），窗化后

$$
\Xi_\psi(s):=\langle F\ast\psi_R,\,k_s\rangle.
$$

**定理 21.6（奇性不增与极阶不升）**
**假设**：(1) 窗/核 $\psi$ 取 Paley–Wiener 带限（带宽 $B$）或有指数型整函数衰减；(2) 采样率 $f_s\ge 2B$（Nyquist）；(3) 连续—离散换序固定为**有限阶** $M$ 的 EM。

则在工作条带内，$\Xi_\psi$ 与 $\Xi$ 具有相同的奇性集合（极点/本性/分支不增），且极点阶不升；若 $\psi$ 在奇点处非零，则极阶保持不变。

*证明*：有限阶 EM 仅引入有限个端点差分（伯努利层）与整函数余项；带限 + Nyquist 使 $\text{alias}=0$；指数衰减使 alias 进入整函数误差并给出显式上界。故 $\Xi_\psi-\Xi$ 在**同一工作条带**内解析；当输入窗/核与母对象在 $s$ 上为整时，差值才为整。因而**奇性集合不增、极阶不升**的结论在工作条带内成立。由洛朗首项不变性得极阶结论。$\square$

> **EM 纪律强调**：将 EM 误作无穷级并逐项外推会引入伪奇性并破坏"极点不增"。本文固定有限阶 $M$，并统一用 (0.4) 给出非渐近上界。**严禁把 EM 当作渐近无穷级逐项外推**。在可检清单中需记录所用阶数 $M$ 与端点导数阶。

**命题 21.7（窗化非负性）**
若 $\psi\ge0$、$h\ge0$，则

$$
\int h(x)\psi_R(x)\,d\mu_{\rm ac}(x)=\frac{1}{\pi}\int h(x)\psi_R(x)\,\Im m(x+i0)\,dx\ge0,
$$

并且 $\int h\psi_R\,d\mu\ge \int h\psi_R\,d\mu_{\rm ac}\ge0$。从而窗化不会生成伪负谱或虚阈值。
*证明*：等号在绝对连续部分成立由 (0.1)；不等式由 $\mu=\mu_{\rm ac}+\mu_{\rm s}$ 与逐点非负。$\square$

---

## 4. Rouché 型零集稳定半径

设 $D\subset\mathbb C$ 为有界单连通域，$|E(z)|\ge\eta>0$ 于 $\partial D$。

**定理 21.8（稳定半径）**
若近似 $E_\natural$ 满足 $\sup_{\partial D}|E_\natural-E|<\eta$，则 $E$ 与 $E_\natural$ 在 $D$ 中零点计数（含重数）相同，且零点位移由 $\eta$ 可控。并有可检上界

$$
\eta\ \le\ C\cdot\big(\mathrm{alias}+\mathrm{Bernoulli\ layer}+\mathrm{tail}\big),
$$

其中 $C=C(\inf_{\partial D}|E|,\,|\psi|_{L^1\cap L^\infty},\,\text{条带宽度},\,\text{EM 阶 }M)$ 为显式常数。端点导数到伯努利层的具体常数可引用 S18 的三分解常数表。
*证明*：Rouché 定理结合 (0.4)。$\square$

> 注（可检操作性）：$\inf_{\partial D}|E|$ 可由**带限窗 + 最大模估计 + 采样阈值检验**给出下界；三分解三项均可逐项给出显式上界。推荐检查步骤：(1) 选择条带边界 $\partial D$；(2) 对 $E$ 在 $\partial D$ 上采样，计算 $\inf|E|$；(3) 用窗范数、核 Sobolev 界与尾截断距离分别估计别名、伯努利层与截断项（引用 S18 §3.3 的统一非渐近上界）；(4) 验证 $\eta<\inf|E|$ 以确保 Rouché 条件。

---

## 5. Bregman–KL 灵敏度与阈值稳定

令 $X^\ast=\arg\min g(X)$。窗化/数据扰动给出 $\widehat F,\widehat\nu$、极小元 $\widehat X$。

**归一化假设**：将窗化谱密度在工作区间 $I$ 上归一化为概率密度；若存在截断尾项，则 KL/TV 在同一截断支撑上计算，并计入尾项占比 $\epsilon_{\text{tail}}$ 的校正常数。

**定理 21.9（信息—能量—阈值稳定链）**
在上述归一化与 $(\mu,L)$-凸平滑条件下，存在常数 $C_j=C_j(\mu,L,\mathcal C)$ 使

$$
|\,\widehat X-X^\ast\,|\ \le\ C_1|\,\widehat F-F\,|+C_2\,\mathrm{TV}(\widehat\nu,\nu),\qquad
\mathrm{KL}(p_{\widehat X}|p_{X^\ast})\ \le\ C_3\big(|\,\widehat F-F\,|^2+\mathrm{TV}^2\big).
$$

从而

$$
|\,\widehat\rho-\rho\,|_{L^1(I)}+|\,\widehat\varphi'-\varphi'\,|_{L^1(I)}\ \le\ C_4\big(|\,\widehat F-F\,|+\mathrm{TV}+\epsilon_{\text{tail}}\big),
$$

并且阈值集合在任意紧区间 $I$ 内的局部 Hausdorff 偏移满足同阶上界（尾项质量 $\epsilon_{\text{tail}}$ 进入最终上界的线性加项）。
*证明*：强凸—平滑给出 Bregman–欧氏等价与扰动 Lipschitz 界；由 Pinsker 的**单侧界** $\mathrm{TV}\le\sqrt{\mathrm{KL}/2}$，并结合 $(\mu,L)$-强凸—平滑给出的 Bregman–欧氏等价，得到文中所需的 $\mathrm{KL}\le C\,\mathrm{TV}^2$ 形式（此上界来自强凸—平滑，而**非** Pinsker 本身）；再由 Herglotz 表示传递到 $\rho,\varphi'$。$\square$

---

## 6. 阈值正规形与共振靠近

**定理 21.10（边界正规形与阈值阶）**
设 $\mu$ 在 $x_0$ 的 Lebesgue 分解具有密度 $\rho\in C^{\kappa,\alpha}(I)$（某邻域 $I$），且奇异部分在 $x_0$ 无原子。则当 $x\to x_0$（实轴非切）时，

$$
\Im m(x+i0)\sim c\,|x-x_0|^\kappa,\qquad
\Re m(x+i0)=\mathcal H[\Im m(\cdot+i0)](x)+\text{平滑项},
$$

其中 $\mathcal H$ 为 Hilbert 变换。阈值阶即 $\kappa$。**有限阶**窗化与 EM 不改变 $\kappa$。
*证明*：Herglotz—Nevanlinna 类局部结构与 (0.1)，结合定理 21.6。$\square$

**命题 21.11（临界共振靠近与计数不变）**
设 $z_j$ 为下半平面共振，若 $\rho$ 在 $x_0$ 一阶接触且 $\rho'(x_0)\neq0$，则在任一 Rouché 圆盘 $D$（$\partial D$ 与实轴交角非零）内，

$$
\mathrm{dist}(z_j,\mathbb R)\ \ll\ \sup_{\partial D}\frac{|E_\natural-E|}{|E|},
$$

并保持计数不变。若存在边界吸收或非自伴扰动，此'共振靠近'仅作上界，不保证极限点沿法线靠近实轴。
*证明*：最大模估计与参数连续性，结合定理 21.8。$\square$

---

## 7. 例示模板

**(i) 完成的 $\xi$ 函数**（如 $\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(\tfrac s2)\zeta(s)$）：由于 $\xi(\tfrac12+iz)$ 的零点（若 RH 成立）位于**实轴**，其并非严格 HB 函数（HB 需上半平面内 $|E^\sharp|<|E|$、**无实零**）。可采用**偏移正则化** $E_\varepsilon(z)=\xi(\tfrac12+\varepsilon+iz)$（$\varepsilon>0$），此时由 (0.1)(0.2) 得 $\varphi'(x)=\pi\rho(x)>0$，由 (0.3) 得 $\delta'=-2\pi\rho$。定理 21.6–21.8 与 21.9 给出窗化稳定与零集的可检稳定半径。极限 $\varepsilon\downarrow0$ 的边界过程只在**边界值层面**继承 (0.1)，非严格 HB。或直接以**规范系统生成的** de Branges 链 $E_t$ 为例，而非直接取 $\xi$。

**(ii) Dirichlet $L(\chi,\cdot)$**：完成后根数吸收入通道特征值，仍满足 $\delta'=-2\pi\rho$。在带限/采样达 Nyquist 时别名项消失，伯努利层与尾项提供显式误差。

**(iii) 离散图对照**：$(q+1)$-正则图的 Ihara–Bass 行列式给出离散"完成函数"与自倒数镜像；"离散阈值"由谱多项式零—极结构指示（等价于谱多项式的接触/重零点），窗化误差结构沿用 (0.4)。端点（$\pm 2\sqrt q$）处的'阈值阶'等价于 Chebyshev 型因子的重合阶。

---

## 8. 边界与适用范围

* **EM 阶数**：必须固定有限阶；无穷级展开会引入伪奇性。
* **散射对称**：若实轴酉性或镜像对称未满足，需改用谱移函数 $\xi$ 的一般形式；结论以 $\xi'=\rho$ 取代。
* **度量校准**：Bregman–KL 链需 $\Lambda$ 的强凸—平滑与 Pinsker 链接；否则仅得单侧界。

---

## 9. 可检清单（最小充分条件）

1. **Weyl–Herglotz**：
   - 说明采用的 $E$ 与规范系统的对应方式（引用具体的 $H(t)$/初值规范）
   - 给出 Weyl–Titchmarsh 函数 $m$ 与 $\rho=\pi^{-1}\Im m(\cdot+i0)$
   - 若使用 $m=-E'/E$，注明"满足**无实零**与**标准归一**，因此 $-E'/E\equiv m$"
   - 验证 $\varphi'(x)=\Im m(x+i0)$
2. **相位正性**：用 $\varphi'(x)=\pi K(x,x)/|E(x)|^2>0$ 校验单调性与符号。
3. **散射相位**：构造 $S(x)$ 并核对 $\boxed{\det S(x)=c_0U(x)^{-1}}$（单通道归一 + 短程假设），从而 $\partial_x\arg\det S=-2\pi\rho$。
4. **窗化纪律**：
   - 偶窗/偶核 + **有限阶** EM（记录阶数 $M$ 与端点导数阶）
   - 记录 $\psi$ 的带宽 $B$、采样率 $f_s$，验证 Nyquist $f_s\ge 2B$
   - 按 (0.4) 给出"别名/伯努利层/截断"的非渐近上界
5. **Rouché 半径**：
   - 在所选域 $\partial D$ 上给出 $|E|$ 下界与误差上界 $\eta$
   - 给出 $\eta$ 的数值估计表（按 alias、伯努利层、tail 三项拆分）
   - 验证零集计数不变
6. **信息几何**：在 $(\mu,L)$ 条件下给出 $\widehat X$ 稳定，并把偏差（含尾项 $\epsilon_{\text{tail}}$）传递至 $\widehat\rho,\widehat\varphi'$。
7. **阈值正规形**：在邻域内给出 $\Im m(\cdot+i0)$ 的消失阶 $\kappa$（含非整数阶），并核对窗化不改阶。

---

## 10. 与既有篇章的接口

* **S15（Weyl–Heisenberg 酉表示）**：相位算子 $A=\log x$、尺度算子 $B=-i(x\partial_x+\frac a2)$ 的生成元性质保证 $\varphi'$ 在坐标变换下的协变性；等距性使 Herglotz 核在群平均下保持实值性。
* **S16（de Branges–Krein 规范系统）**：在**标准归一**且 $E$ 在 $\mathbb R$ 上**无实零**的前提下，本文 $m=-E'/E$ 的 Herglotz 表示与 S16 §3 的 HB 生成函数对齐；传递矩阵 $M(t,z)$ 的 $J$-酉性保证 $\Im m>0$，从而 $\varphi'>0$。
* **S17（散射算子与功能方程）**：§0.3 的 $\det S=c_0U^{-1}$ 即 S17 §2 的通道特征值等价；本文定理 21.4 的 $\delta'=-2\pi\rho$ 给出 S17 相位导数定理的实频版本。
* **S18（轨道—谱窗化不等式）**：本文 §0.4 的三分解与 S18 §3.3 的统一非渐近上界对齐；定理 21.6 的"奇性不增"确保 S18 窗化后主项极点保持不变。
* **S19（谱图与 Ihara ζ）**：离散图的 Ihara–Bass 行列式给出"离散 $E$"；本文 §7(iii) 的离散阈值与 S19 §2 的完成函数镜像对称对应。
* **S20（BN 投影—KL 代价—灵敏度）**：定理 21.9 的信息—能量链直接调用 S20 §4 的 KL—$g$-gap 不等式与 Pinsker 桥；本文 $\rho$ 的扰动界与 S20 软/硬极小元的稳定性定理对齐。

---

## 参考文献

1. L. de Branges, *Hilbert Spaces of Entire Functions*, Prentice–Hall, 1968.
2. D. N. Clark, "One-dimensional perturbations of restricted shifts," *J. Anal. Math.* **25** (1972), 169–191.
3. C. Remling, "Canonical systems and de Branges spaces," *J. Funct. Anal.* **196** (2002), 323–394.
4. A. Poltoratski, "Boundary behavior of pseudocontinuable functions," *St. Petersburg Math. J.* **5** (1994), 389–406.
5. M. Sh. Birman, M. G. Krein, "On the theory of wave and scattering operators," *Dokl. Akad. Nauk SSSR* **144** (1962), 475–478.
6. D. R. Yafaev, *Mathematical Scattering Theory: General Theory*, AMS, 1992.
7. G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS, 2014.
8. B. Simon, *Orthogonal Polynomials on the Unit Circle*, Parts 1–2, AMS Colloquium, 2005.

---

## 结语

以 $\varphi'(x)=\Im m(x+i0)=\pi\rho(x)$ 为主轴，本文把**阈值**与**共振**的谱—散射判据、**窗化—采样**的非渐近误差控制、以及**Bregman–KL** 的灵敏度不等式统一成可检的判据体系：阈值位置与阶在明确的技术纪律下稳定，零集在 Rouché 半径内计数不变，"极点 = 主尺度"在窗化流程中保持不变。上述结构为阈值处共振生成/消失的分岔、最优窗/核设计与算子级稳定域的后续研究提供了统一且可验证的数学基础。
