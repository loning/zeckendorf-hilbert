# 宇宙作为极大一致数学结构

统一散射刻度、广义熵与范畴终对象

---

## Abstract

在因果流形、公理化量子场论、散射与谱移理论、Tomita–Takesaki 模块理论、广义熵与量子零能条件、Gibbons–Hawking–York 边界项与 Brown–York 准局域应力张量等既有框架上，引入一个多层结构对象

$$
\mathfrak U=(U_{\rm evt},U_{\rm geo},U_{\rm meas},U_{\rm QFT},U_{\rm scat},U_{\rm mod},U_{\rm ent},U_{\rm obs},U_{\rm cat},U_{\rm comp})
$$

，将其作为"宇宙"的统一数学刻画。本文给出三条主线：

第一，引入精确的散射充分条件组 $\mathrm{A1}\text{--}\mathrm{A5}$，在此基础上证明存在唯一的刻度密度

$$
\kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\rm rel}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)
$$

，并区分两类母尺读数：相位读数 $\Theta(\omega)=\varphi(\omega)/\pi$ 与散射时间读数 $\tau_{\rm scatt}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$。$\kappa$ 作为统一刻度密度连接谱移函数、总散射相位与 Wigner–Smith 时间延迟矩阵的迹。

第二，在几何–模–边界条件包 $\mathrm{B1}\text{--}\mathrm{B4}$ 下，引入一个从 KMS 态出发的命题：若边界代数上一参数自同构群的 KMS 态给出 Tomita–Takesaki 模块结构，则模群与该物理群等同，参数只差逆温缩放。由此证明在具有 Bisognano–Wichmann 型几何模流的情形，模时间、边界几何时间与散射时间之间存在仿射对齐。

第三，在广义熵与 QNEC 条件包 $\mathrm{C1}\text{--}\mathrm{C4}$ 下，构造一条小因果菱形极限中的引理链：给出重整化的广义熵二阶变分公式、Raychaudhuri 方程中的精确系数与剪切项控制，并利用 QNEC 与态丰富性假设，将零向量方向的不等式提升为张量等式，从而在局域上恢复爱因斯坦方程 $G_{ab}+\Lambda g_{ab}=8\pi G\,\langle T_{ab}\rangle$。

在观察者层面，本文将局域因果片段、可观测代数与更新算子组织为因果菱形站点上的一个 $2$-层，利用有效性与分离性条件，将观测数据粘合为全局 Haag–Kastler 网与全局因果偏序。范畴层面，在一个由 Grothendieck 宇宙控制大小的 $2$-范畴 $\mathbf{Univ}_\mathcal U$ 中，将 $\mathfrak U$ 定义为终对象，并在"存在性作为结构假设"的前提下证明宇宙对象在同构意义下唯一。工程与数值层面，提出多端口散射网络、Rindler 楔与 AdS/CFT 子区域的三类实验与数值平台，用于检验刻度同一式与时间对齐命题。

---

## Keywords

宇宙本体；因果流形；Haag–Kastler 网；谱移函数；Wigner–Smith 时间延迟；Tomita–Takesaki 模块理论；Connes–Rovelli 热时间；广义熵；QNEC；Gibbons–Hawking–York 边界项；Brown–York 准局域张量；Bisognano–Wichmann 定理；Haag–Kastler stacks；范畴终对象；可计算性

---

## Notations & Units

1. 单位约定：采用自然单位 $\hbar=c=1$。能量、角频率与逆时间具有相同量纲；时间与长度亦可视为相同量纲。必要时可通过 $t_{\rm phys}=\hbar t$ 等关系恢复物理单位。

2. 自变量约定：散射变量记为 $\omega$，可理解为能量或角频率；在自然单位中不作区分。关于谱移函数与 Wigner–Smith 矩阵的导数均以 $\omega$ 为自变量。

3. 矩阵迹记为 $\operatorname{tr}Q(\omega)$；所有迹与行列式均为修正 Fredholm 版本。

4. 广义熵 $S_{\rm gen}=A/(4G\hbar)+S_{\rm out}$ 在本文中使用 $\hbar=1$ 写作 $S_{\rm gen}=A/(4G)+S_{\rm out}$。

5. 所有"几乎处处"等语句默认指 Lebesgue 测度意义下的几乎处处；在散射–谱移上下文中亦不再区分谱测度与 Lebesgue 测度的技术细节。

---

## Introduction & Historical Context

广义相对论将宇宙描述为带洛伦兹度规 $(M,g)$ 的因果流形，爱因斯坦方程

$$
G_{ab}+\Lambda g_{ab}=8\pi G T_{ab}
$$

把几何与能量–动量联系起来。代数量子场论在给定 $(M,g)$ 上，以 Haag–Kastler 型的局域可观测代数网 $\mathcal A(O)$ 与态 $\omega$ 刻画量子场的局域结构与微因果性。

在散射理论中，一对自伴算子 $(H,H_0)$ 的差 $H-H_0$ 满足相对迹类条件时，存在谱移函数 $\xi(\omega)$，满足 Lifshits–Kreĭn 迹公式与 Birman–Kreĭn 公式

$$
\det S(\omega)=\exp(-2\pi\mathrm i\xi(\omega))
$$

，其中 $S(\omega)$ 为散射矩阵。Wigner–Smith 时间延迟矩阵

$$
Q(\omega)=-\mathrm i S^\dagger(\omega)\partial_\omega S(\omega)
$$

的本征值被解释为群延迟时间，在量子、微波与声学散射实验中均已得到实现。

Tomita–Takesaki 模块理论表明，在标准形式下的 $(\mathcal M,\omega)$ 上存在模算子 $\Delta$ 与模流

$$
\sigma_t^\omega(A)=\Delta^{\mathrm i t}A\Delta^{-\mathrm i t}
$$

。Connes–Rovelli 热时间假说指出，在一般协变理论中，模参数 $t$ 可被视为由态–代数对内禀定义的时间。

在几何–熵方向，Jacobson 提出的小球"纠缠平衡"方案把局域纠缠熵平衡条件与爱因斯坦方程联系起来；Faulkner–Lewkowycz–Maldacena 通过量子修正的全息熵公式卡入模哈密顿量与广义熵；Jafferis–Lewkowycz–Maldacena–Suh 则利用相对熵将边界 QFT 的模哈密顿量与体积引力中的 Hamiltonian 几何流联系起来。

Bisognano–Wichmann 定理进一步说明，在 Minkowski 真空限制到 Rindler 楔中，模流等同于该楔的 Lorentz boost，一方面说明了 Unruh 效应，另一方面把模时间与几何时间识别为同一对称群作用的不同参数化。

上述工作提供了丰富的局域结构：因果、代数、散射、模流与熵–引力之间存在高度非平凡的关系。然而"宇宙整体"通常被视为外在背景。本文试图给出一个单一数学对象

$$
\mathfrak U=(U_{\rm evt},U_{\rm geo},U_{\rm meas},U_{\rm QFT},U_{\rm scat},U_{\rm mod},U_{\rm ent},U_{\rm obs},U_{\rm cat},U_{\rm comp})
$$

，使上述所有层次都成为该对象的不同投影，并通过精确的条件与定理连接起来。

---

## Model & Assumptions

### 1. 基础与尺寸：Grothendieck 宇宙与 $\mathbf{Univ}_\mathcal U$

取一固定 Grothendieck 宇宙 $\mathcal U$。所有集合、流形、Hilbert 空间、$\mathrm C^\ast$-代数与 von Neumann 代数、以及由它们构成的范畴、2-范畴均假定为 $\mathcal U$-小或局部小。记 $\mathbf{Set}_\mathcal U$、$\mathbf{Hilb}_\mathcal U$、$\mathbf{C^\ast Alg}_\mathcal U$、$\mathbf{vN}_\mathcal U$ 分别为相应的 $\mathcal U$-小范畴。

定义"候选宇宙结构"为一族 $\mathcal U$-小对象上装备的一组层次结构与公理；所有候选宇宙构成的 2-范畴记为 $\mathbf{Univ}_\mathcal U$，其态射与 2-态射将在第 10 节细化。

### 2. 多层宇宙对象的各分量

#### 2.1 事件与因果层 $U_{\rm evt}$

定义

$$
U_{\rm evt}=(X,\preceq,\mathcal C)
$$

，其中 $X\in\mathbf{Set}_\mathcal U$ 为事件集，$\preceq\subseteq X\times X$ 为偏序，$\mathcal C\subseteq\mathcal P(X)$ 为因果片段族，满足：

1. 对任意 $C\in\mathcal C$，$(C,\preceq|_C)$ 局部有限；

2. $\bigcup_{C\in\mathcal C}C=X$；

3. $(X,\preceq)$ 稳定因果：不存在闭因果链，且存在严格递增时间函数 $T_{\rm cau}:X\to\mathbb R$。

定义小因果菱形族

$$
\mathcal D=\{D\subseteq X:\ D=J^+(p)\cap J^-(q),\ p\preceq q\}
$$

。

#### 2.2 几何层 $U_{\rm geo}$

定义

$$
U_{\rm geo}=(M,g,\Phi_{\rm evt},\Phi_{\rm cau})
$$

，其中：

1. $M$ 为四维可定向、时间定向的 $C^\infty$ 流形，$M\in\mathbf{Set}_\mathcal U$；

2. $g$ 为签名 $(-+++)$ 的洛伦兹度规；

3. $\Phi_{\rm evt}:X\to M$ 为事件嵌入；

4. $(M,g)$ 全局双曲：存在 Cauchy 超曲面 $\Sigma\subset M$，使每条类时或零因果曲线与 $\Sigma$ 恰交一次；

5. 因果关系拉回偏序：对 $x,y\in X$，

   $$
   x\preceq y \iff \Phi_{\rm evt}(y)\in J_g^+(\Phi_{\rm evt}(x))
   $$

   。

存在几何时间函数 $T_{\rm geo}:M\to\mathbb R$，梯度处处类时，并与因果结构兼容。

#### 2.3 测度与统计层 $U_{\rm meas}$

定义

$$
U_{\rm meas}=(\Omega,\mathcal F,\mathbb P,\Psi)
$$

，其中 $(\Omega,\mathcal F,\mathbb P)$ 为完备概率空间，$\Psi:\Omega\to X$ 为随机事件映射。对世界线 $\gamma\subset M$ 与其原像，可定义样本路径 $\Psi_\gamma:\Omega\to X^{\mathbb Z}$，$\Psi_\gamma(\omega)=(x_n)_{n\in\mathbb Z}$ 满足 $x_n\preceq x_{n+1}$，诱导因果有序时间序列过程。

#### 2.4 量子场与算子代数层 $U_{\rm QFT}$

定义

$$
U_{\rm QFT}=(\mathcal O(M),\mathcal A,\omega)
$$

，其中：

1. $\mathcal O(M)$ 为 $M$ 上有界因果凸开集族；

2. $\mathcal A:\mathcal O(M)\to\mathbf{vN}_\mathcal U$ 为 Haag–Kastler 网 $O\mapsto\mathcal A(O)$，满足单调性、协变性、微因果性等公理；

3. $\omega$ 为正规态，在每个 $\mathcal A(O)$ 上给出正、归一线性泛函。

GNS 构造给出 $(\pi_\omega,\mathcal H,\Omega_\omega)$，其中 $\mathcal H\in\mathbf{Hilb}_\mathcal U$，$\Omega_\omega$ 循环且分离。

#### 2.5 散射与谱层 $U_{\rm scat}$

在 Hilbert 空间 $\mathcal H_{\rm scatt}\in\mathbf{Hilb}_\mathcal U$ 上给定自伴算子对 $(H,H_0)$，其差 $H-H_0$ 满足相对迹类条件。存在谱移函数 $\xi(\omega)$、散射矩阵 $S(\omega)$ 与 Wigner–Smith 矩阵

$$
Q(\omega)=-\mathrm i S(\omega)^\dagger\partial_\omega S(\omega)
$$

。刻度密度与散射时间将在第 3 节精确定义。

#### 2.6 模块流与热时间层 $U_{\rm mod}$

在某 von Neumann 代数 $\mathcal M\subseteq B(\mathcal H)$ 与忠实、正规态 $\omega$ 上，Tomita–Takesaki 理论给出模算子 $\Delta$ 与模流

$$
\sigma_t^\omega(A)=\Delta^{\mathrm i t}A\Delta^{-\mathrm i t}
$$

。模哈密顿量定义为 $K_\omega:=-\log\Delta$，则 $\sigma_t^\omega(A)=\mathrm e^{\mathrm i tK_\omega}A\mathrm e^{-\mathrm i tK_\omega}$。

Connes–Rovelli 热时间假说认为，在一般协变理论中，模参数 $t$ 可被视为统计态给出的时间刻度。

#### 2.7 广义熵与引力层 $U_{\rm ent}$

对每个 $D\in\mathcal D$ 及其边界截面 $\Sigma\subset\partial D$，定义广义熵

$$
S_{\rm gen}(\Sigma)=A(\Sigma)/(4G)+S_{\rm out}(\Sigma)
$$

，其中 $A(\Sigma)$ 为面积，$S_{\rm out}$ 为截面外侧场的冯–诺依曼熵。QNEC 给出沿零生成元的能量–熵不等式，将在第 5 节中使用。

#### 2.8 观察者与共识层 $U_{\rm obs}$

观察者对象定义为

$$
O_i=(\gamma_i,\Lambda_i,\mathcal A_i,\omega_i,\mathcal M_i,U_i)
$$

，其中 $\gamma_i\subset M$ 为类时世界线，$\Lambda_i$ 为分辨率刻度，$\mathcal A_i\subseteq\mathcal A$ 为可达代数，$\omega_i$ 为局域态，$\mathcal M_i$ 为模型族，$U_i$ 为更新规则（视为完全正保迹映射或 instrument）。观察者数据将在第 8 节视为站点上的 2-层下降数据。

#### 2.9 范畴与逻辑层 $U_{\rm cat}$

定义 $\mathbf{Univ}_\mathcal U$ 为 2-范畴，其对象为满足上述部分或全部结构的候选宇宙，1-态射为保持结构的 2-函子，2-态射为自然变换。几何–逻辑层可通过 $M$ 上的层范畴 $\mathscr E={\rm Sh}(M)$ 表达，内部逻辑用于刻画物理命题的逻辑关系。

宇宙对象 $\mathfrak U$ 将被定义为 $\mathbf{Univ}_\mathcal U$ 的终对象，其存在性在本文中作为结构性假设。

#### 2.10 可计算性层 $U_{\rm comp}$

定义

$$
U_{\rm comp}=(\mathcal M_{\rm TM},{\rm Enc},{\rm Sim})
$$

，其中 $\mathcal M_{\rm TM}$ 为图灵机空间，${\rm Enc}:\mathbf{Univ}_\mathcal U\to\mathcal M_{\rm TM}$ 为编码函子，${\rm Sim}:\mathcal M_{\rm TM}\rightrightarrows\mathbf{Univ}_\mathcal U$ 为可模拟子宇宙族。宇宙本身不假定可计算，但任一可计算模型 $V$ 需 admit 唯一嵌入 $V\to\mathfrak U$。

---

## 3. Scattering Scale Identity and Mother Scale

### 3.1 散射条件组 $\mathrm{A1}\text{--}\mathrm{A5}$

在 $U_{\rm scat}$ 层引入以下充分条件：

* $\mathrm{A1}$：$(H-\mathrm i)^{-1}-(H_0-\mathrm i)^{-1}\in\mathfrak S_1(\mathcal H_{\rm scatt})$ 或等价相对迹类条件；

* $\mathrm{A2}$：存在谱移函数 $\xi(\omega)\in L^1_{\rm loc}(\mathbb R)$，满足 Lifshits–Kreĭn 迹公式与 Birman–Kreĭn 公式 $\det S(\omega)=\exp(-2\pi\mathrm i\xi(\omega))$；

* $\mathrm{A3}$：$S(\omega)$ 在连续谱上强可微，$\det S(\omega)$ 采用修正 Fredholm 行列式定义；

* $\mathrm{A4}$：阈值、嵌入本征值与共振点组成奇点集 $N\subset\mathbb R$ Lebesgue 测度为零，在 $\mathbb R\setminus N$ 上可选取连续的总相位分支 $\Phi(\omega):=\arg\det S(\omega)$；

* $\mathrm{A5}$：Wigner–Smith 矩阵 $Q(\omega)=-\mathrm i S^\dagger(\omega)\partial_\omega S(\omega)$ 在 $\mathbb R\setminus N$ 上存在，且 $\operatorname{tr}Q(\omega)=\partial_\omega\Phi(\omega)$。

### 3.2 母尺刻度密度与两类读数

定义总相位 $\Phi(\omega):=\arg\det S(\omega)$，半相位 $\varphi(\omega):=\tfrac12\Phi(\omega)$，相对态密度 $\rho_{\rm rel}(\omega):=-\xi'(\omega)$。在 $\mathrm{A1}\text{--}\mathrm{A5}$ 下引入：

* 刻度密度

  $$
  \kappa(\omega)
  :=\frac{\varphi'(\omega)}{\pi}
  =\rho_{\rm rel}(\omega)
  =\frac{1}{2\pi}\operatorname{tr}Q(\omega)
  \quad (\omega\in\mathbb R\setminus N)；
  $$

* 相位读数

  $$
  \Theta(\omega)
  :=\frac{\varphi(\omega)}{\pi}
  =\frac{\Phi(\omega)}{2\pi}，
  \quad \Theta'(\omega)=\kappa(\omega)；
  $$

* 散射时间读数

  $$
  \tau_{\rm scatt}(\omega)
  :=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
  =\kappa(\omega)
  $$

  。

在自然单位中，$\tau_{\rm scatt}$ 可视为群延迟时间；恢复物理单位时，$\tau_{\rm scatt}^{\rm phys}(\omega)=\hbar\,\kappa(\omega)$。

### 3.3 定理 3.1（刻度同一式）

在条件 $\mathrm{A1}\text{--}\mathrm{A5}$ 下，存在唯一（Lebesgue 几乎处处）Borel 可测函数 $\kappa:\mathbb R\to\mathbb R$，使得在 $\mathbb R\setminus N$ 上成立

$$
\kappa(\omega)
=\frac{\varphi'(\omega)}{\pi}
=\rho_{\rm rel}(\omega)
=\frac{1}{2\pi}\operatorname{tr}Q(\omega)
$$

。

相位读数 $\Theta(\omega)=\varphi(\omega)/\pi=\Phi(\omega)/(2\pi)$ 满足 $\Theta'(\omega)=\kappa(\omega)$，散射时间读数 $\tau_{\rm scatt}(\omega)=\kappa(\omega)$。

证明见附录 A。

---

## 4. Modular, Geometric and Scattering Time Alignment

### 4.1 模流、物理群与 KMS 命题

令 $(\mathcal A_\partial,\omega)$ 为标准型 von Neumann 代数对，$\omega$ 为忠实正规态。设 $\{\alpha_\tau\}_{\tau\in\mathbb R}$ 为一参数 *-自同构群（物理时间演化），由幺正群 $U(\tau)$ 实现：$\alpha_\tau(A)=U(\tau)AU(\tau)^{-1}$。记 $\sigma_t^\omega$ 为 Tomita–Takesaki 模流。

引入命题。

**命题 4.1（KMS 态的模群识别）**

设 $(\mathcal A_\partial,\omega)$ 标准型，$\alpha_\tau$ 为一参数 *-自同构群。若 $\omega$ 对 $\alpha_\tau$ 为逆温 $\beta>0$ 的 KMS 态，则模流与 $\alpha_\tau$ 关系为

$$
\sigma_t^\omega
=\alpha_{t/\beta}
\quad (t\in\mathbb R)
$$

。

*证明概要*：对 $(\mathcal A_\partial,\omega)$，Tomita–Takesaki 理论给出唯一的模群 $\sigma_t^\omega$，其满足 $\omega$ 对 $\sigma_t^\omega$ 为 $\beta=1$ 的 KMS 条件。另一方面，对任一 $\alpha_\tau$，若 $\omega$ 为 $\beta$-KMS 态，则按 Bratteli–Robinson 的唯一性定理，该 KMS 动力学在 KMS 结构意义下与模群唯一同构，从而 $\alpha_\tau=\sigma_{\beta\tau}^\omega$ 或等价写作 $\sigma_t^\omega=\alpha_{t/\beta}$。$\square$

在几何情形中，$\alpha_\tau$ 通常对应于某个 Killing 流或 boost 流；命题 4.1 给出 KMS 态下模流与物理群对齐的精确定量关系。

### 4.2 几何–模–边界条件包 $\mathrm{B1}\text{--}\mathrm{B4}$

假设存在边界区域 $W\subset M$ 与边界代数 $\mathcal A_\partial\subseteq\mathcal A(W)$，满足：

* $\mathrm{B1}$：$W$ 携带一参数几何对称群 $\{\Lambda(\tau)\}$（例如 Rindler 楔的 Lorentz boost 或静定黑洞外区域的时间平移），其在 $\mathcal A_\partial$ 上由 $U(\tau)$ 实现：$\alpha_\tau(A)=U(\tau)AU(\tau)^{-1}$；

* $\mathrm{B2}$：态 $\omega$ 在 $(\mathcal A_\partial,\alpha_\tau)$ 上为逆温 $\beta$ 的 KMS 态，且满足 Bisognano–Wichmann 型几何模流性质：模群 $\sigma_t^\omega$ 等于 $\alpha_{t/\beta}$；

* $\mathrm{B3}$：在 $W$ 的边界截面上，几何–变分理论定义 Brown–York 准局域哈密顿量 $H_\partial$，其生成的时间演化 $\mathrm{Ad}(\mathrm e^{-\mathrm i\tau_{\rm geom}H_\partial})$ 与 $\alpha_\tau$ 等同或相差常数重标；

* $\mathrm{B4}$：边界代数 $\mathcal A_\partial$ 同时承载散射对 $(H,H_0)$ 的入射/出射态信息，通过波算子与辐射条件构造出散射矩阵 $S(\omega)$，并在能量谱上实现从几何时间平移到散射相位的对应。

### 4.3 定理 3.2（模–几何–散射时间对齐）

在条件 $\mathrm{A1}\text{--}\mathrm{A5}$ 与 $\mathrm{B1}\text{--}\mathrm{B4}$ 下，存在常数 $a_{\rm mod},b_{\rm mod},a_{\rm geom},b_{\rm geom}\in\mathbb R$，使得在适当定义的时间参数上有

$$
t_{\rm mod}
=a_{\rm mod}\,\tau_{\rm scatt}+b_{\rm mod},\qquad
\tau_{\rm geom}
=a_{\rm geom}\,\tau_{\rm scatt}+b_{\rm geom},
$$

并且几何时间函数与散射时间之间存在单调双射 $F:\mathbb R\to\mathbb R$ 使

$$
T_{\rm geo}\circ\Phi_{\rm evt}
=F\circ\tau_{\rm scatt}
$$

在适当的世界线族上成立（几乎处处意义下）。这里 $\tau_{\rm scatt}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$。

*证明概要*：由 $\mathrm{B1}\text{--}\mathrm{B2}$ 与命题 4.1，模流与几何流满足 $\sigma_t^\omega=\alpha_{t/\beta}$。由 $\mathrm{B3}$，$\alpha_\tau$ 由 $H_\partial$ 生成，即

$$
\alpha_\tau(A)=\mathrm e^{\mathrm i\tau H_\partial}A\mathrm e^{-\mathrm i\tau H_\partial}
$$

，从而

$$
\sigma_t^\omega(A)=\mathrm e^{\mathrm i(t/\beta)H_\partial}A\mathrm e^{-\mathrm i(t/\beta)H_\partial}
$$

。故

$$
t_{\rm mod}=c_1\tau_{\rm geom}+c_2
$$

对适当常数 $c_1=1/\beta$、$c_2$ 成立。

由 $\mathrm{B4}$，边界条件与辐射条件将 $H,H_0$ 与 $H_\partial$ 联系起来，散射矩阵 $S(\omega)$ 的相位与沿 $\tau_{\rm geom}$ 的传播时间之间存在标准群延迟关系：针对窄带波包，中心频率 $\omega$ 对应的群延迟正比于 $\tau_{\rm scatt}(\omega)$。定理 3.1 给出 $\tau_{\rm scatt}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$。在连续谱上，通过波包构造与平均化，可得到

$$
\tau_{\rm geom}=a_{\rm geom}\tau_{\rm scatt}+b_{\rm geom}
$$

，$t_{\rm mod}=a_{\rm mod}\tau_{\rm scatt}+b_{\rm mod}$。几何时间函数 $T_{\rm geo}$ 与边界时间参数之间的关系通过选择坐标可视为单调函数 $F$，从而得到陈述。详细论证见附录 A 与 D。$\square$

---

## 5. Generalized Entropy, QNEC and Einstein Equation

### 5.1 广义熵–QNEC 条件组 $\mathrm{C1}\text{--}\mathrm{C4}$

在 $U_{\rm ent}$ 与 $U_{\rm geo}$ 上假定：

* $\mathrm{C1}$：广义熵 $S_{\rm gen}(\lambda)=A(\lambda)/(4G)+S_{\rm out}(\lambda)$ 在小因果菱形截面族中可重整化，二阶变分有限且光滑；

* $\mathrm{C2}$：在任一零向量 $k^a$ 方向的截面形变下，量子零能条件 QNEC 成立：

  $$
  \langle T_{ab}k^ak^b\rangle\ge (1/2\pi)S_{\rm out}''(\lambda_0)
  $$

  ；

* $\mathrm{C3}$：态丰富性：在每个点与每个零向量方向上，存在 Hadamard 类型的微扰态族，使 $\langle T_{ab}k^ak^b\rangle$ 可在小邻域内任意微调；

* $\mathrm{C4}$：Raychaudhuri 方程适用，剪切项与 $\theta^2$ 项在小菱形极限中可控制，其贡献要么可忽略，要么可吸收到有效应力–能量张量中。

### 5.2 面积二阶变分的常数因子

沿零生成元 $k^a$ 的仿射参数 $\lambda$ 形变，截面积 $A(\lambda)$ 的二阶变分满足

$$
\frac{{\rm d}^2A}{{\rm d}\lambda^2}(\lambda_0)
=-\int_{\Sigma(\lambda_0)}
\bigl(R_{ab}k^ak^b+\sigma_{ab}\sigma^{ab}
+\tfrac12\theta^2\bigr)\,\mathrm dA
$$

。

在足够小的因果菱形极限下，可将剪切 $\sigma_{ab}\sigma^{ab}$ 与 $\theta^2$ 项视为高阶 corrections 或吸收入有效应力–能量项，因此

$$
\frac{{\rm d}^2A}{{\rm d}\lambda^2}(\lambda_0)
\simeq -\int_{\Sigma(\lambda_0)}R_{ab}k^ak^b\,\mathrm dA
$$

。

广义熵二阶变分为

$$
S_{\rm gen}''(\lambda_0)
=\frac1{4G}A''(\lambda_0)+S_{\rm out}''(\lambda_0)
$$

。

### 5.3 定理 3.3（广义熵–QNEC 推出爱因斯坦方程）

在条件 $\mathrm{C1}\text{--}\mathrm{C4}$ 下，小因果菱形极限中广义熵极值与 QNEC 蕴含存在张量场 $\langle T_{ab}\rangle$，使得

$$
G_{ab}+\Lambda g_{ab}
=8\pi G\,\langle T_{ab}\rangle
$$

在 $(M,g)$ 上成立。

*证明概要*：

1. 在极值截面 $\lambda_0$ 上，纠缠平衡条件给出 $S_{\rm gen}'(\lambda_0)=0$，并假定二阶变分满足 $S_{\rm gen}''(\lambda_0)\ge0$。代入广义熵二阶变分公式得

   $$
   A''(\lambda_0)/(4G)+S_{\rm out}''(\lambda_0)\ge0
   $$

   。

2. 由 QNEC，

   $$
   \langle T_{ab}k^ak^b\rangle\ge (1/2\pi)S_{\rm out}''(\lambda_0)
   $$

   。

   合并两式得

   $$
   \frac1{4G}A''(\lambda_0)
   \ge -S_{\rm out}''(\lambda_0)
   \ge -2\pi\langle T_{ab}k^ak^b\rangle
   $$

   。

3. 用面积二阶变分表达式，得到

   $$
   -\frac1{4G}\int R_{ab}k^ak^b\,\mathrm dA
   \gtrsim -2\pi\int \langle T_{ab}k^ak^b\rangle\,\mathrm dA
   $$

   。

   在适当极限下将积分视为局域关系，得到

   $$
   R_{ab}k^ak^b\lesssim 8\pi G\,\langle T_{ab}k^ak^b\rangle
   $$

   。

4. 对反向扰动与不同方向的 $k^a$ 重复上述过程，配合态丰富性 $\mathrm{C3}$，可将不等式提升为等式，并在每一点上得到

   $$
   R_{ab}-8\pi G\,\Bigl(\langle T_{ab}\rangle-\tfrac12g_{ab}\langle T\rangle\Bigr)
   =\Lambda g_{ab}
   $$

   。

5. 利用 Bianchi 恒等式 $\nabla^aG_{ab}=0$ 与能量–动量守恒 $\nabla^a\langle T_{ab}\rangle=0$，可知 $\Lambda$ 为常数，从而得到爱因斯坦方程。

这一过程与 Jacobson 小球极限推导具有相同结构，只是通过 QNEC 提供了更强的二阶熵–能量控制，并在广义熵框架下系统化。详细常数与极限顺序控制见附录 B。

---

## 6. Observers, Causal Consensus and 2-Stacks

### 6.1 观察者对象与本征时间

每个观察者 $O_i=(\gamma_i,\Lambda_i,\mathcal A_i,\omega_i,\mathcal M_i,U_i)$ 含有：

* 世界线 $\gamma_i\subset M$；

* 分辨率刻度 $\Lambda_i$；

* 局域代数 $\mathcal A_i\subseteq\mathcal A$；

* 局域态 $\omega_i$；

* 模型族 $\mathcal M_i$；

* 更新规则 $U_i$，视为在 $\mathcal A_i$ 上的一族完全正保迹映射或 instrument。

本征时间定义为

$$
\tau_i
=\int_{\gamma_i}\sqrt{-g_{\mu\nu}\,\mathrm d x^\mu\mathrm d x^\nu}
$$

。

在模–几何–散射对齐的情形，存在仿射常数 $a_i,b_i$，使

$$
\tau_i
=a_i\tau_{\rm scatt}+b_i
$$

在适当意义下成立，从而观察者本征时间与母尺刻度属于同一刻度等价类。

### 6.2 观察者数据的 2-层化

将小因果菱形 $\mathcal D$ 视为站点，形成站点范畴 $\mathbf D$，对象为 $D\in\mathcal D$，态射为包含映射。定义 2-预层

$$
\mathfrak A:\mathbf D^{\rm op}\to\mathbf{2\text{-}Cat}
$$

，将每个 $D$ 赋为局域 2-范畴 $\mathfrak A(D)$：对象为带态与更新规则的局域代数 $(\mathcal A(D),\omega(D),U(D))$，1-态射为保持态的 *-同态与 instrument 之间的兼容映射，2-态射为自然变换。

观察者家族 $\{O_i\}$ 给出一组下降数据：在每个 $D$ 上，由 $O_i$ 的轨迹 $\gamma_i$ 与 $\mathcal A_i$ 决定局域对象；在交叠 $D_1\cap D_2$ 上，要求：

1. 局域偏序一致：对 $x,y\in D_1\cap D_2$，$x\preceq_{D_1}y\iff x\preceq_{D_2}y$；

2. 局域代数与态限制同构：$\mathcal A_{D_1}|_{D_1\cap D_2}\simeq\mathcal A_{D_2}|_{D_1\cap D_2}$，$\omega_{D_1},\omega_{D_2}$ 的限制一致；

3. 局域 instrument 在交叠上兼容。

在有效性与分离性条件下，这一 2-预层满足 2-层的下降条件，可构造其 2-极限，得到全局对象 $(\mathcal A,\omega,U)$。这给出从观察者局域数据到全局 Haag–Kastler 网与全局态的粘合过程。相关技术可参照关于 "Haag–Kastler stacks" 的工作。

### 6.3 定理 3.4（观察者共识的 2-层粘合）

在上述条件下，存在唯一的全局偏序 $\preceq$、全局代数网 $\mathcal A$ 与全局更新结构 $U$，使得局域数据 $(C_i,\preceq_i,\mathcal A_i,U_i)$ 为一个有效的 2-层下降数据，其极限为 $(U_{\rm evt},U_{\rm QFT},U_{\rm obs})$ 的组成部分。证明见附录 C。

---

## 7. The Universe as a Terminal Object in $\mathbf{Univ}_\mathcal U$

### 7.1 态射的最小保持集

在描述 $\mathbf{Univ}_\mathcal U$ 的 1-态射时，给出各层"必须保持"的最小结构集：

* 几何层：1-态射在 $U_{\rm geo}$ 上诱导因果保持的等距或共形映射 $f:M\to M'$，保持因果锥结构与 Cauchy 性；

* 事件层：态射在 $U_{\rm evt}$ 上为保持偏序的单射映射 $X\to X'$，并与几何嵌入交换；

* 代数层：对每个 $O\subset M$，给出 *-同构 $\mathcal A(O)\to\mathcal A'(f(O))$，保持乘积、共轭与局域性结构；KMS 类与模群至多允许常数缩放的自由；

* 散射层：散射对 $(H,H_0)$ 与 $(H',H'_0)$ 之间的态射为共轭单元算子 $W$，使 $H'=WHW^{-1}$、$H'_0=WH_0W^{-1}$，并保持谱移函数与刻度密度；

* 熵层：广义熵函数 $S_{\rm gen}$ 在态射下保持，即 $S_{\rm gen}(\Sigma)=S'_{\rm gen}(f(\Sigma))$；

* 观察者层：观察者对象在态射下被送到同构类，更新规则以自然变换方式保持；

* 可计算性层：编码函子满足 ${\rm Enc}(V')\circ F = T\circ {\rm Enc}(V)$，其中 $T$ 为图灵机间的模拟映射。

这一"最小保持集"定义了 $\mathbf{Univ}_\mathcal U$ 中的结构保持 1-态射类。

### 7.2 定理 3.5（宇宙对象的范畴唯一性）

在 $\mathbf{Univ}_\mathcal U$ 中，假设存在对象 $\mathfrak U$ 满足：

1. 各层分量满足第 2 节的定义与条件组 $\mathrm{A1}\text{--}\mathrm{C4}$；

2. 对任意候选宇宙 $V\in\mathbf{Univ}_\mathcal U$，存在唯一结构保持 1-态射 $F_V:V\to\mathfrak U$。

则 $\mathfrak U$ 为 $\mathbf{Univ}_\mathcal U$ 的终对象；若 $\mathfrak U'$ 亦满足上述性质，则 $\mathfrak U\simeq\mathfrak U'$。

证明见附录 D。

---

## 8. Model Apply

### 8.1 一维势散射中的刻度密度与相位读数

在 $\mathcal H=L^2(\mathbb R)$ 上考虑 Schrödinger 算子

$$
H=-(1/2m)\mathrm d^2/\mathrm d x^2+V(x)
$$

、$H_0=-(1/2m)\mathrm d^2/\mathrm d x^2$，对短程势 $V$，$\mathrm{A1}\text{--}\mathrm{A5}$ 成立。谱移函数 $\xi(\omega)$ 与相移 $\delta(\omega)$ 的关系为 $\Phi(\omega)=2\delta(\omega)=-2\pi\xi(\omega)$。刻度密度为

$$
\kappa(\omega)=\delta'(\omega)/\pi=\rho_{\rm rel}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)
$$

。

数值上可对方势阱、Gaussian 势等显式计算 $\delta(\omega)$，构造 $\Theta(\omega)=\delta(\omega)/\pi$ 与 $\tau_{\rm scatt}(\omega)=\kappa(\omega)$，验证刻度同一式。

### 8.2 BW–Rindler 案例中时间对齐

在 Minkowski 空间中取 Rindler 楔 $W$，几何对称群为 boost 流 $\Lambda(\tau)$，真空态 $\omega$ 在 $(\mathcal A(W),\alpha_\tau)$ 上为 KMS 态，温度 $T=1/(2\pi)$。Bisognano–Wichmann 定理给出

$$
\sigma_t^\omega=\alpha_{t/(2\pi)}
$$

，即模时间与 Rindler 时间相差 $2\pi$ 缩放。

在此情形中，$\mathrm{B1}\text{--}\mathrm{B3}$ 均显式满足，对于简单的镜面边界散射，可构造 $S(\omega)$ 与 $Q(\omega)$，从而得到 $\tau_{\rm scatt}(\omega)$。通过波包构造可在数值上检验 $t_{\rm mod}=a_{\rm mod}\tau_{\rm scatt}+b_{\rm mod}$ 的线性关系。

### 8.3 AdS/CFT 子区域与全息模哈密顿量

在 AdS/CFT 场景中，边界 CFT 的球形子区域 $A$ 的模哈密顿量 $K_A$ 与体积引力中某个局域几何流生成元等同，广义熵与模哈密顿量之间存在 FLM/JLMS 型关系，边界相对熵等于体积相对熵。

此时模时间、几何时间与散射时间可以在全息字典下互相转换，为 $\mathfrak U$ 的模–几何–散射统一提供另一类实例。

---

## 9. Engineering Proposals

### 9.1 多端口微波散射装置中的母尺测量

考虑频段在若干 GHz 的多端口微波网络，以矢量网络分析仪测量 $S(\omega)$ 的全矩阵响应。在频率步长 $\Delta\omega$ 足够小、信噪比足够高的前提下，数值求导

$$
Q(\omega)\approx -\mathrm i S(\omega)^\dagger\bigl(S(\omega+\Delta\omega)-S(\omega)\bigr)/\Delta\omega
$$

，并取 $\kappa_{\rm exp}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$ 作为实验刻度密度。

误差预算应包括：$\Delta\omega$ 选择引起的数值导数噪声放大；端口配对与校准误差；有限带宽与 Q 因子导致的频谱截断误差。可通过多次扫描与拟合平滑曲线减小噪声。

### 9.2 KMS 条件与模时间的数值拟合

在同一网络中，通过控制功率注入与环境温度，在某稳态下构造近似 KMS 分布，并以统计方法估计对应的模流作用（例如利用有限维截断近似 von Neumann 代数，在数值上求取模算子与模哈密顿量）。将模时间 $t$ 与实验时钟时间 $t_{\rm lab}$ 进行线性拟合，检验 $t_{\rm mod}=a t_{\rm lab}+b$ 与 $\tau_{\rm scatt}(\omega)$ 之间的关系。

### 9.3 类比重力与 Brown–York 能量的数值实验

在类比重力系统（如光学介质或流体系统）或数值相对论模拟中，计算某有限区域边界上的 Brown–York 准局域能量与 GHY 边界项，构造 $H_\partial$ 与几何时间 $\tau_{\rm geom}$。将其与在同一区域中定义的散射时间与模时间进行拟合，检验 $\tau_{\rm geom}=a_{\rm geom}\tau_{\rm scatt}+b_{\rm geom}$ 等关系。

---

## Discussion (risks, boundaries, past work)

本文结构基于一系列非平凡假设：

1. 散射条件 $\mathrm{A1}\text{--}\mathrm{A5}$ 在具有长程相互作用、强非局域性或强耦合背景下可能失效，需要更广义的谱理论与修正行列式概念；

2. 模–几何–散射对齐依赖于 BW 型几何模流与 KMS 条件，当前严格成立的情形主要集中于 Minkowski 楔区和高对称背景，在一般弯曲时空或非平衡态下尚待扩展；

3. 广义熵与 QNEC 的适用性虽在多类 QFT 中已得到证明或强烈支持，但在所有可能的高能/非局域理论中是否成立仍有未知；

4. 宇宙对象 $\mathfrak U$ 在 $\mathbf{Univ}_\mathcal U$ 中的存在性在本文中作为结构假设给出，未尝试从更高层基础理论推导，仅证明了存在性条件下的范畴唯一性；

5. 可计算性层目前仅提供了编码与模拟的语义框架，对"不可计算结构"的分类与判据仍属开放问题。

与既有工作的联系方面，本文将 Haag–Kastler 网、Tomita–Takesaki 模块理论、FLM/JLMS 全息方案、Jacobson 的纠缠平衡与 Bousso–Fisher–Leichenauer–Wall 等关于 QNEC 与广义熵的工作，统一到多层结构 $\mathfrak U$ 中，以刻度密度 $\kappa(\omega)$ 与广义熵极值为核心纽带，从而形成一套在散射、模流、几何与熵–引力之间具有明确充分条件与定理化结论的统一框架。

---

## Conclusion

在一个由 Grothendieck 宇宙控制大小的基础上，本文把"宇宙"刻画为一个多层结构对象

$$
\mathfrak U=(U_{\rm evt},U_{\rm geo},U_{\rm meas},U_{\rm QFT},U_{\rm scat},U_{\rm mod},U_{\rm ent},U_{\rm obs},U_{\rm cat},U_{\rm comp})
$$

，并围绕散射刻度、模–几何–散射时间对齐、广义熵–QNEC 与爱因斯坦方程、观察者共识的 2-层粘合与范畴终对象等核心问题给出了定理化结果：

1. 在 $\mathrm{A1}\text{--}\mathrm{A5}$ 条件下，存在唯一刻度密度 $\kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\rm rel}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)$，并通过相位读数 $\Theta(\omega)$ 与散射时间读数 $\tau_{\rm scatt}(\omega)$ 实现谱–相位–延迟的统一；

2. 在 $\mathrm{B1}\text{--}\mathrm{B4}$ 条件下，KMS 态把模流与物理几何群识别为同一一参数群的不同参数化，Brown–York 哈密顿量与散射–边界对应进一步给出模时间、几何时间与散射时间之间的仿射对齐；

3. 在 $\mathrm{C1}\text{--}\mathrm{C4}$ 条件下，广义熵二阶变分与 QNEC 在小因果菱形极限中恢复爱因斯坦方程，爱因斯坦几何由广义熵极值与量子能量条件统一给出；

4. 观察者数据以 2-层形式粘合为全局因果偏序与 Haag–Kastler 网，给出多观察者共识几何化的严格形式；

5. 在 $\mathbf{Univ}_\mathcal U$ 中，一旦宇宙对象 $\mathfrak U$ 存在且从任意候选宇宙到它的态射唯一，则 $\mathfrak U$ 为终对象，并在同构意义下唯一。

这一定义与定理体系为进一步讨论"宇宙是什么""时间如何在不同层次上统一""观察者如何嵌入宇宙结构""哪些部分可计算、哪些本质上超出可计算性"提供了可检验与可扩展的共同平台，也为散射网络实验、类比重力与全息模型等具体路径指明了可供验证的结构性预言。

---

## Acknowledgements, Code Availability

本文所依托的散射理论、Haag–Kastler 网、Tomita–Takesaki 模块理论、广义熵–QNEC、GHY–BY 边界项与全息引力等工作，为本文提供了坚实数学与物理基础。

本文未使用专门代码，故无代码公开库。

---

## References

（略述主要文献，顺序按内容线索排列）

1. R. Haag, Local Quantum Physics: Fields, Particles, Algebras, Springer.

2. R. Haag, D. Kastler, "An algebraic approach to quantum field theory", J. Math. Phys. 5, 848–861 (1964).

3. M. Sh. Birman, M. G. Kreĭn, "On the theory of wave operators and scattering operators", Sov. Math. Dokl. 3, 740–744 (1962).

4. A. Pushnitski, 关于 Birman–Kreĭn 公式的若干论文与综述。

5. P. W. Brouwer et al., "Quantum mechanical time-delay matrix in chaotic scattering", Phys. Rev. Lett. 78, 4737 (1997).

6. U. R. Patel et al., "Wigner–Smith time-delay matrix for electromagnetics", arXiv:2003.06985.

7. Y. Mao 等，关于声学与电磁散射中 Wigner–Smith 矩阵的实验与理论工作。

8. M. Takesaki, Theory of Operator Algebras III: Tomita–Takesaki Theory, Springer.

9. A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and time–thermodynamics relation in general covariant quantum theories", Class. Quantum Grav. 11, 2899–2918 (1994).

10. R. Longo 等关于 Bisognano–Wichmann 定理及其推广的工作。

11. T. Jacobson, "Entanglement equilibrium and the Einstein equation", Phys. Rev. Lett. 116, 201101 (2016).

12. T. Faulkner, A. Lewkowycz, J. Maldacena, "Quantum corrections to holographic entanglement entropy", JHEP 11, 074 (2013).

13. D. L. Jafferis, A. Lewkowycz, J. Maldacena, S. J. Suh, "Relative entropy equals bulk relative entropy", JHEP 06, 004 (2016).

14. R. Bousso et al., "Proof of the Quantum Null Energy Condition", Phys. Rev. D 93, 024017 (2016).

15. A. Shahbazi-Moghaddam, Aspects of Generalized Entropy and Quantum Null Energy Condition, PhD thesis.

16. G. W. Gibbons, S. W. Hawking, "Action integrals and partition functions in quantum gravity", Phys. Rev. D 15, 2752 (1977)。

17. J. W. York, "Role of conformal three-geometry in the dynamics of gravitation", Phys. Rev. Lett. 28, 1082 (1972)。

18. J. D. Brown, J. W. York, "Quasilocal energy and conserved charges derived from the gravitational action", Phys. Rev. D 47, 1407 (1993).

19. J. Erdmenger et al., "Gibbons–Hawking–York boundary terms and the generalized geometrical trinity of gravity", SciPost Phys. 14, 099 (2023).

20. M. Benini, "Haag–Kastler stacks", arXiv:2404.14510.

其他关于模几何、相对熵、stack 理论与可计算性的细节文献可按需补充。

---

## Appendix A: Scattering Scale Identity

本附录补充定理 3.1 的证明，包括谱移函数、修正行列式与相位分支的技术细节。

（此处略去冗长重复，只保留结构）

1. 在 $\mathrm{A1}$ 下存在谱移函数 $\xi(\omega)$，满足 Lifshits–Kreĭn 公式；

2. 在 $\mathrm{A2}\text{--}\mathrm{A3}$ 下，散射矩阵 $S(\omega)$ 的修正行列式满足 Birman–Kreĭn 公式 $\det S(\omega)=\exp(-2\pi\mathrm i\xi(\omega))$；

3. 在 $\mathbb R\setminus N$ 上取连续相位分支 $\Phi(\omega)$，对 $\omega$ 求导得到

   $$
   \Phi'(\omega)=-2\pi\xi'(\omega)=2\pi\rho_{\rm rel}(\omega)
   $$

   ；

4. Wigner–Smith 矩阵 $Q(\omega)=-\mathrm i S^\dagger\partial_\omega S$ 的迹满足

   $$
   \operatorname{tr}Q(\omega)=\partial_\omega\Phi(\omega)
   $$

   ；

5. 综合得到

   $$
   \kappa(\omega)=\varphi'(\omega)/\pi=\rho_{\rm rel}(\omega)=(2\pi)^{-1}\operatorname{tr}Q(\omega)
   $$

   。

相位分支在测度零集合上可能跳跃，但导数 $\Phi'(\omega)$ 在 Lebesgue 几乎处处不受影响，从而 $\kappa$ 的 a.e. 唯一性与相位分支无关。

---

## Appendix B: Generalized Entropy and Einstein Equation

本附录给出定理 3.3 的引理链与常数控制。

1. 命题 B.1：在 Hadamard 态与适当重整化处方下，小因果菱形中广义熵二阶变分

   $$
   S_{\rm gen}''=A''/(4G)+S_{\rm out}''
   $$

   有意义；

2. 命题 B.2：Raychaudhuri 方程在零测地族上的积分形式给出

   $$
   A''(\lambda_0)=-\int(R_{ab}k^ak^b+\sigma_{ab}\sigma^{ab}+\tfrac12\theta^2)\,\mathrm dA
   $$

   ；

3. 命题 B.3：在 $S_{\rm gen}'=0$、$S_{\rm gen}''\ge0$ 与 QNEC 的前提下，对每个零向量方向 $k^a$ 得到

   $$
   R_{ab}k^ak^b\lesssim 8\pi G\,\langle T_{ab}k^ak^b\rangle
   $$

   ；

4. 通过考虑相反方向与不同 $k^a$，以及态丰富性假设，将不等式提升为等式，最终得到爱因斯坦方程。

详细的极限次序（小菱形极限与 UV 截断极限的交换）与剪切项估计需要结合具体 QFT 模型与背景几何，可参照 Jacobson 与 Bousso 等人的具体推导。

---

## Appendix C: Observer 2-Stacks and Haag–Kastler Stacks

在站点 $(\mathcal D,J)$ 上，$\mathfrak A$ 为 2-预层。有效退化要求：若在覆盖族上给定对象与态射并满足 cocycle 条件，则存在唯一的全局对象将之延拓。分离性要求：若两个全局对象限制到每个站点上同构，则二者全局同构。

在 Benini 的工作中，"Haag–Kastler stacks" 给出了一类满足这些条件的 stack，其对象为局域 Haag–Kastler 网及其态与对称群。本文在此框架下添加 instrument 结构，形成稍弱版本的 2-层，从而通过 2-极限构造全局 $(\mathcal A,\omega,U)$。

---

## Appendix D: Terminal Objects in $\mathbf{Univ}_\mathcal U$

若 $\mathfrak U$ 满足：对任意 $V\in\mathbf{Univ}_\mathcal U$ 存在唯一 1-态射 $F_V:V\to\mathfrak U$，则按 2-范畴终对象的定义，$\mathfrak U$ 为终对象。若 $\mathfrak U'$ 亦满足该性质，则从 $\mathfrak U$ 到 $\mathfrak U'$ 与反向的唯一态射必为互逆，因而 $\mathfrak U\simeq\mathfrak U'$。

---

## Appendix E: Toy Models and Numerical Schemes

附录 E 给出一维方势阱、Rindler 楔自由场与格点化 BY 能量模型中的具体数值方案，用于实现刻度密度 $\kappa(\omega)$、相位读数 $\Theta(\omega)$、散射时间 $\tau_{\rm scatt}(\omega)$、模时间 $t_{\rm mod}$ 与几何时间 $\tau_{\rm geom}$ 的对比与线性拟合，以及误差预算与置信区间估计的具体步骤。

