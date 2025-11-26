# 信息速率的普适守恒：从量子元胞自动机到相对论、质量与引力的统一

Version: 1.0

## Abstract

在量子元胞自动机（quantum cellular automaton, QCA）与有限信息本体论框架下，引入统一公理：对任一局域激发，其外部群速度 $v_{\mathrm{ext}}$ 与内部态演化速度 $v_{\mathrm{int}}$ 满足信息速率守恒

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}.
$$

以内部演化参数定义固有时间 $\tau$，可从该公理直接导出狭义相对论的时间膨胀、四速度规范化与 Minkowski 线元。在线性 Dirac 型 QCA 的连续极限中，内部 Hamilton 算符 $H_{\mathrm{int}}$ 给出内部频率 $\omega_{\mathrm{int}}$，质量获得信息论定义

$$
m c^{2}=\hbar\omega_{\mathrm{int}},
$$

并满足 Zitterbewegung 频率关系

$$
\omega_{\mathrm{ZB}}=2\omega_{\mathrm{int}}.
$$

结合 QCA 的绕数与指数不变量，可将 massive 激发解释为拓扑非平凡自指回路中被束缚的光程配额。在多体层面，引入局域信息处理密度 $\rho_{\mathrm{info}}(x)$，从局域信息体积守恒导出光学度规

$$
ds^{2}=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j},
$$

其中 $\eta(x)$ 决定局域有效光速

$$
c_{\mathrm{eff}}(x)=\eta^{2}(x)c,
$$

与折射率

$$
n(x)=\eta^{-2}(x).
$$

在弱场极限下，该结构恢复 Schwarzschild 度规的一阶展开及标准光线偏折角，并可通过信息–引力变分原理得到形式上等价于爱因斯坦方程的场方程。进一步引入信息质量 $M_{I}$，结合 Landauer 原理分析高信息质量主体的渐近静止行为与最小耗散功率，给出质量、引力与复杂能动结构的统一信息论刻画，并提出基于超导量子电路与量子模拟平台的可检验预言。

## Keywords

量子元胞自动机；信息速率守恒；光学度规；狭义相对论；广义相对论；拓扑质量；Zitterbewegung；信息质量；Landauer 原理

---

## Introduction & Historical Context

狭义与广义相对论将宇宙刻画为带 Lorentz 签名的四维流形 $(M,g_{\mu\nu})$。度规张量 $g_{\mu\nu}$ 决定时空因果结构与测地线，场方程

$$
R_{\mu\nu}-\tfrac12 R g_{\mu\nu}=8\pi G T_{\mu\nu}
$$

将应力–能量张量 $T_{\mu\nu}$ 与曲率联系起来。引力红移、光线偏折、引力波探测等实验检验高度支持这一几何叙事。

量子理论则在 Hilbert 空间 $\mathcal H$ 中表述，态为向量或密度算符，可观测量为自伴算符，时间演化由幺正群或半群生成。统计解释建立在 Born 规则之上，叠加、相位与纠缠构成核心结构。两类理论在量子场论中通过“场算符定义在背景流形上”的方式拼接，但本体论起点仍然分离：一侧是可弯曲的几何舞台，另一侧是概率振幅的线性空间。

当接近普朗克尺度时，流形与经典度规的连续性假设失去经验支撑，而 Hilbert 空间结构本身并不依赖连续时空。这促使以离散、有限信息结构为基础的本体论成为自然候选。量子元胞自动机（QCA）在可数格点上定义局域、因果且幺正的演化，已被证明可以在适当极限下涌现 Dirac、Weyl 以及 Maxwell 等场方程，并具有完备的结构与分类理论，是“宇宙作为量子计算”框架的精确算子实现之一〔见文献 [1,2]〕。

另一方面，引力透镜理论中广泛使用“光学度规”的几何方法，将光线视为光学几何中的测地线，通过 Gauss–Bonnet 定理计算偏折角，由此建立“引力弯曲光线”与“非均匀折射率介质中的几何光学”之间的等价〔见文献 [3,4]〕。

信息热力学通过 Landauer 原理把逻辑不可逆与热耗散联系起来：在温度为 $T$ 的热浴中擦除一比特信息至少耗散热量 $k_{B}T\ln 2$，表明信息更新是受物理定律约束的资源消耗过程〔见文献 [5]〕。

本文提出：在 QCA 与有限信息本体的统一视角下，可以以“信息速率守恒”作为唯一微观公理。宇宙中每个局域激发在每个微观时间步拥有有限的“信息速率预算”，该预算对应最大传播速度 $c$，并在“位移”（外部运动）与“内部演化”（局域 Hilbert 空间自指更新）之间以勾股方式分配。本文将证明，这一公理足以导出狭义相对论几何、质量–频率关系、弱场引力的光学结构以及信息质量与耗散的基本约束，从而为质量、引力与复杂能动结构提供统一的信息论刻画。

---

## Model & Assumptions

### QCA 宇宙与有限信息性

设 $\Lambda$ 为可数连通图，其节点代表“空间元胞”。每个节点 $x\in\Lambda$ 携带有限维 Hilbert 空间 $\mathcal H_{x}\simeq\mathbb C^{d}$。对任意有限子集 $F\Subset\Lambda$ 定义局域 Hilbert 空间

$$
\mathcal H_{F}=\bigotimes_{x\in F}\mathcal H_{x},
$$

局域算符代数为 $\mathcal B(\mathcal H_{F})$。全局准局域 $C^{\ast}$ 代数为

$$
\mathcal A=\overline{\bigcup_{F\Subset\Lambda}\mathcal B(\mathcal H_{F})}.
$$

量子元胞自动机由 $\ast$-自同构 $\alpha:\mathcal A\to\mathcal A$ 指定，要求存在幺正算符 $U$ 使

$$
\alpha(A)=U^{\dagger}AU,\qquad A\in\mathcal A,
$$

并存在有限传播半径 $R<\infty$，使对任意支撑于 $F$ 的局域算符 $A$ 有

$$
\mathrm{supp}\,\alpha(A)\subset B_{R}(F),
$$

其中 $B_{R}(F)$ 为 $F$ 在图距离意义下的 $R$ 邻域。给定初始态 $\omega_{0}$ 后，离散时间演化为

$$
\omega_{n}=\omega_{0}\circ\alpha^{n},\qquad n\in\mathbb Z.
$$

假设 $\Lambda$ 可嵌入三维欧氏空间，具有有效格距 $a$，单步演化对应物理时间 $\Delta t$。若 $R=1$，则最大传播速率为

$$
c=\frac{a}{\Delta t}.
$$

有限局域维数与有限传播半径意味着，在任意有限时空窗内可区分物理态数目有限，宇宙在任意有限区域内的信息容量存在上界。

### 单激发有效空间与外部/内部速度

考虑一个局域“单激发”模式，在适当近似下其有效 Hilbert 空间可表示为

$$
\mathcal H_{\mathrm{eff}}\simeq\mathcal H_{\mathrm{COM}}\otimes\mathcal H_{\mathrm{int}},
$$

其中 $\mathcal H_{\mathrm{COM}}$ 描述中心坐标或波包包络，$\mathcal H_{\mathrm{int}}$ 描述内部自由度。

在连续极限下，$\mathcal H_{\mathrm{COM}}$ 上存在近似位置算符 $X$ 与动量算符 $P$，有效 Hamilton 算符 $H_{\mathrm{eff}}$ 生成粗粒化时间演化。定义外部（群）速度

$$
v_{\mathrm{ext}}=\frac{d}{dt}\langle X\rangle
=\frac{1}{\mathrm i\hbar}\langle[X,H_{\mathrm{eff}}]\rangle.
$$

内部态 $\ket{\psi_{\mathrm{int}}(t)}\in\mathcal H_{\mathrm{int}}$ 可视为射影空间 $\mathbb C P^{D_{\mathrm{int}}-1}$ 上的点，装备 Fubini–Study 度量

$$
ds_{\mathrm{FS}}^{2}=4\bigl(1-|\langle\psi\mid\psi+d\psi\rangle|^{2}\bigr).
$$

定义内部速度

$$
v_{\mathrm{int}}:=\frac{ds_{\mathrm{FS}}}{dt}\ge 0.
$$

### 信息速率向量与普适守恒公理

在二维“信息速率空间”

$$
\mathbb R^{2}_{\mathrm{info}}=\mathrm{span}\{e_{\mathrm{ext}},e_{\mathrm{int}}\}
$$

中，定义信息速率向量

$$
\mathbf u=v_{\mathrm{ext}}e_{\mathrm{ext}}+v_{\mathrm{int}}e_{\mathrm{int}},
\qquad
|\mathbf u|^{2}=v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}.
$$

**信息速率守恒公理**：存在常数 $c>0$，使对任意局域激发与任意时间 $t$ 均有

$$
v_{\mathrm{ext}}^{2}(t)+v_{\mathrm{int}}^{2}(t)=c^{2}.
$$

定义信息相角

$$
\theta(t):=\arctan\frac{v_{\mathrm{int}}(t)}{v_{\mathrm{ext}}(t)}\in[0,\pi/2].
$$

$\theta=0$ 对应类光模式，$\theta=\pi/2$ 对应完全局域内部模式，$0<\theta<\pi/2$ 对应 massive 模式。

### 固有时间与内部演化

对任一激发世界线定义固有时间 $\tau$ 满足

$$
v_{\mathrm{int}}\,dt=c\,d\tau,
$$

即

$$
v_{\mathrm{int}}=c\,\frac{d\tau}{dt}.
$$

将其代入信息速率守恒

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2},
$$

令 $v:=v_{\mathrm{ext}}=|d\mathbf x/dt|$，得到

$$
\Bigl(\frac{d\tau}{dt}\Bigr)^{2}=1-\frac{v^{2}}{c^{2}},
$$

取正根

$$
\frac{d\tau}{dt}=\sqrt{1-\frac{v^{2}}{c^{2}}},
$$

即狭义相对论时间膨胀关系。固有时间可以理解为“内部信息路程”的自然参数，其相对于坐标时间的缩减是外部运动占用光程配额的直接结果。

### 局域信息处理密度与光学度规

在多体情形下，引入粗粒化的局域信息处理密度 $\rho_{\mathrm{info}}(x)$，代表单位时间单位体积内局域 Hilbert 空间在 Fubini–Study 度量下走过的平均路径长度，或等价地，内部 Hamilton 密度的有效期望值。高 $\rho_{\mathrm{info}}(x)$ 区域可视为“内部计算高度活跃”的区域。

允许在坐标系 $(t,x^{i})$ 下对时间与空间刻度进行局域重标度，引入尺度因子 $\eta_{t}(x)$、$\eta_{x}(x)$，使

$$
dt_{\mathrm{eff}}=\eta_{t}(x)\,dt,\qquad
d\ell_{\mathrm{eff}}=\eta_{x}(x)\,d\ell.
$$

底层 QCA 的幺正性意味着全局 Hilbert 体积在演化中保持不变。将这一要求局域化并简化为“单位坐标体积对应的物理 Hilbert 体积不随时间变化”，可以用约束

$$
\eta_{t}(x)\,\eta_{x}^{3}(x)=1
$$

来模拟。

在各向同性近似下，取

$$
\eta_{t}(x)=\eta(x),\qquad
\eta_{x}(x)=\eta^{-1}(x),
$$

则四维线元可写为

$$
ds^{2}=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j},
$$

其中 $\gamma_{ij}(x)$ 为三维空间度规。

在各向同性且 $\gamma_{ij}=\delta_{ij}$ 的情形下，对零测地线 $ds^{2}=0$ 有

$$
0=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\,d\mathbf x^{2},
$$

从而坐标光速

$$
\Bigl|\frac{d\mathbf x}{dt}\Bigr|
=\frac{\eta_{t}(x)}{\eta_{x}(x)}\,c
=\eta^{2}(x)c
=:c_{\mathrm{eff}}(x),
$$

等效折射率

$$
n(x):=\frac{c}{c_{\mathrm{eff}}(x)}=\eta^{-2}(x).
$$

高 $\rho_{\mathrm{info}}(x)$ 意味着局域内部演化更频繁，由信息速率守恒可知外部传播被抑制；因此 $\eta(x)$ 越小，局域有效光速 $c_{\mathrm{eff}}(x)=\eta^{2}(x)c$ 越小，对应折射率 $n(x)=\eta^{-2}(x)$ 越大。这与弱场引力中

$$
n(r)\simeq 1-\frac{2\phi(r)}{c^{2}}
$$

（$\phi<0$ 为牛顿势）的结果相容，在 $\phi(r)=-GM/r$ 时给出 $n(r)>1$，从而 $c_{\mathrm{eff}}(r)<c$。

---

## Main Results (Theorems and alignments)

在上述模型与假设基础上，归纳本文的主要数学结果与物理对应关系。

### 定理 1（狭义相对论的涌现）

在信息速率守恒公理

$$
v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}
$$

与固有时间定义

$$
v_{\mathrm{int}}\,dt=c\,d\tau
$$

下，有：

1. 固有时间满足

   $$
   \Bigl(\frac{d\tau}{dt}\Bigr)^{2}=1-\frac{v^{2}}{c^{2}},
   \qquad
   v:=v_{\mathrm{ext}}=\Bigl|\frac{d\mathbf x}{dt}\Bigr|.
   $$

2. 世界线 $x^{\mu}(\tau)=(ct(\tau),\mathbf x(\tau))$ 的四速度

   $$
   u^{\mu}=\frac{dx^{\mu}}{d\tau}
   =\gamma(v)\,(c,\mathbf v),
   \qquad
   \gamma(v)=\frac{1}{\sqrt{1-v^{2}/c^{2}}},
   $$

   在 Minkowski 度规 $\eta_{\mu\nu}=\mathrm{diag}(-1,1,1,1)$ 下满足规范化

   $$
   u^{\mu}u_{\mu}=-c^{2}.
   $$

3. 线元素

   $$
   ds^{2}:=-c^{2}d\tau^{2}=-c^{2}dt^{2}+d\mathbf x^{2}
   $$

   与 Minkowski 时空度规一致。

从而，狭义相对论动力学在本框架中作为信息速率守恒与固有时间定义的直接推论出现。

### 定理 2（质量作为内部频率）

在内部 Hilbert 空间 $\mathcal H_{\mathrm{int}}$ 上引入 Hamilton 算符

$$
\mathrm i\hbar\,\partial_{\tau}\ket{\psi_{\mathrm{int}}(\tau)}
=H_{\mathrm{int}}\ket{\psi_{\mathrm{int}}(\tau)}.
$$

若存在定态 $\ket{\psi_{\mathrm{int}}}$ 满足

$$
H_{\mathrm{int}}\ket{\psi_{\mathrm{int}}}=E_{0}\ket{\psi_{\mathrm{int}}},
$$

则内部态演化为

$$
\ket{\psi_{\mathrm{int}}(\tau)}
=\mathrm e^{-\mathrm i E_{0}\tau/\hbar}\ket{\psi_{\mathrm{int}}},
$$

定义内部频率

$$
\omega_{\mathrm{int}}:=\frac{E_{0}}{\hbar}.
$$

以 $E_{0}=m c^{2}$ 识别静止能量，得到质量–频率关系

$$
m=\frac{\hbar\omega_{\mathrm{int}}}{c^{2}}.
$$

### 命题 1（Zitterbewegung 频率与内部频率）

在一维 Dirac 型 QCA 的连续极限中，有效 Hamilton 算符

$$
H_{\mathrm{eff}}(k)\simeq c\hbar k\,\sigma_{z}
+m c^{2}\sigma_{x},
$$

本征值

$$
E_{\pm}(k)=\pm\sqrt{(c\hbar k)^{2}+m^{2}c^{4}}.
$$

Heisenberg 图像下位置算符 $X(t)$ 的演化包含频率

$$
\omega_{\mathrm{ZB}}=\frac{2E}{\hbar}
$$

的快速振荡项（Zitterbewegung）。在静止极限 $k=0$ 下，$E=m c^{2}$，故

$$
\omega_{\mathrm{ZB}}(0)=\frac{2m c^{2}}{\hbar}=2\omega_{\mathrm{int}}.
$$

### 定理 3（拓扑稳定性与非零信息相角）

考虑一维平移不变 QCA，其单步幺正算符 $U(k)\in\mathrm U(N)$ 在动量空间上定义一条闭合曲线。绕数

$$
\mathcal W[U]
=\frac{1}{2\pi\mathrm i}\int_{-\pi/a}^{\pi/a}
\partial_{k}\log\det U(k)\,dk\in\mathbb Z
$$

在有限深度局域幺正变换下保持不变。

1. 若 $\mathcal W[U]=0$，则存在连续变形将 QCA 化为仅含无质量传播模式的形式，其内部频率 $\omega_{\mathrm{int}}$ 可以为零，对应 $v_{\mathrm{int}}=0$、$\theta=0$。

2. 若 $\mathcal W[U]\neq 0$，则存在携带非零拓扑荷的局域激发，任何有限深度局域幺正均无法将其连续变形为拓扑平凡真空。为维持拓扑相位绕行，此类激发的内部 Hamilton 必须具有非零本征频率 $\omega_{\mathrm{int}}>0$，从而 $v_{\mathrm{int}}>0$、$\theta>0$。

因此，非零信息相角 $\theta$ 与质量的存在由 QCA 的拓扑结构稳定，massive 激发可被解释为拓扑非平凡自指回路所束缚的光程配额的宏观表现。

### 定理 4（光学度规与弱场引力）

在各向同性假设下，取

$$
\eta_{t}(x)=\eta(x),\qquad
\eta_{x}(x)=\eta^{-1}(x),
$$

构造光学度规

$$
ds^{2}=-\eta^{2}(x)c^{2}dt^{2}
+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j}.
$$

在弱场极限

$$
\eta(x)=1+\epsilon(x),\qquad
|\epsilon(x)|\ll 1,
$$

一阶展开得到

$$
g_{00}\simeq-(1+2\epsilon)c^{2},
\qquad
g_{ij}\simeq(1-2\epsilon)\gamma_{ij}.
$$

在静态、球对称情形下取各向同性坐标并识别

$$
\epsilon(r)=\frac{\phi(r)}{c^{2}},
$$

其中 $\phi(r)$ 为牛顿势，则

$$
g_{00}\simeq-\bigl(1+2\phi/c^{2}\bigr)c^{2},
\qquad
g_{ij}\simeq\bigl(1-2\phi/c^{2}\bigr)\delta_{ij},
$$

与 Schwarzschild 度规在各向同性坐标下的一阶展开一致。折射率

$$
n(r)=\eta^{-2}(r)\simeq 1-\frac{2\phi(r)}{c^{2}},
$$

若 $\phi(r)=-GM/r$，则

$$
n(r)\simeq 1+\frac{2GM}{c^{2}r}>1,
\qquad
c_{\mathrm{eff}}(r)=\frac{c}{n(r)}<c.
$$

在该度规下求解零测地线，得到光线偏折角

$$
\Delta\theta=\frac{4GM}{c^{2}b},
$$

其中 $b$ 为冲量距，与广义相对论标准结果一致。

### 定理 5（信息–引力变分原理）

考虑作用量

$$
S_{\mathrm{tot}}[g,\rho_{\mathrm{info}}]
=\frac{1}{16\pi G}\int_{M}\sqrt{-g}\,R[g]\,d^{4}x
+\int_{M}\sqrt{-g}\,\mathcal L_{\mathrm{info}}[\rho_{\mathrm{info}},g]\,d^{4}x.
$$

对 $g^{\mu\nu}$ 变分（忽略边界项）得到

$$
R_{\mu\nu}-\tfrac12 R g_{\mu\nu}
=8\pi G\,T^{(\mathrm{info})}_{\mu\nu},
$$

其中

$$
T^{(\mathrm{info})}_{\mu\nu}
:=-\frac{2}{\sqrt{-g}}\,
\frac{\delta(\sqrt{-g}\,\mathcal L_{\mathrm{info}})}{\delta g^{\mu\nu}}.
$$

若选择 $\mathcal L_{\mathrm{info}}$ 使 $T^{(\mathrm{info})}_{\mu\nu}$ 在低能极限下与标准物质的应力–能量张量一致，则该方程形式上等价于爱因斯坦场方程。

### 定理 6（信息质量与渐近静止）

对具有内部模型与自指机制的系统，引入信息质量

$$
M_{I}(\sigma)
=f\bigl(K(\sigma),D(\sigma),S_{\mathrm{ent}}(\sigma)\bigr),
$$

其中 $K$ 为 Kolmogorov 复杂度，$D$ 为逻辑深度，$S_{\mathrm{ent}}$ 为内部纠缠熵，$f$ 为单调增函数。假设维持给定 $M_{I}$ 需要的平均内部信息速率 $v_{\mathrm{int}}(M_{I})$ 单调递增且有界于 $c$。由信息速率守恒得

$$
v_{\mathrm{ext}}^{2}(M_{I})
=c^{2}-v_{\mathrm{int}}^{2}(M_{I}).
$$

若

$$
\lim_{M_{I}\to\infty}v_{\mathrm{int}}(M_{I})=c,
$$

则

$$
\lim_{M_{I}\to\infty}v_{\mathrm{ext}}(M_{I})=0,
$$

即高信息质量主体在外部几何中趋于渐近静止。

### 命题 2（维持信息质量的 Landauer 代价）

设系统以速率 $R_{\mathrm{upd}}$ 更新内部模型，每次更新平均擦除 $\Delta I$ 比特旧信息，则单位时间擦除信息量

$$
\dot I_{\mathrm{erase}}
=R_{\mathrm{upd}}\Delta I.
$$

在温度 $T$ 的热浴中，根据 Landauer 原理，擦除一比特信息至少耗散热量 $k_{B}T\ln 2$，最小功耗为

$$
P_{\min}
=k_{B}T\ln 2\,\dot I_{\mathrm{erase}}
=k_{B}T\ln 2\,R_{\mathrm{upd}}\Delta I.
$$

---

## Proofs

本节给出上述主要结果的推导结构，详细计算在附录中展开。

### 定理 1 的证明

由固有时间定义

$$
v_{\mathrm{int}}\,dt=c\,d\tau
\quad\Rightarrow\quad
v_{\mathrm{int}}=c\,\frac{d\tau}{dt},
$$

代入

$$
v^{2}+v_{\mathrm{int}}^{2}=c^{2},
\qquad
v:=v_{\mathrm{ext}},
$$

得到

$$
v^{2}+c^{2}\Bigl(\frac{d\tau}{dt}\Bigr)^{2}=c^{2},
$$

即

$$
\Bigl(\frac{d\tau}{dt}\Bigr)^{2}
=1-\frac{v^{2}}{c^{2}}.
$$

取正根得到时间膨胀关系

$$
\frac{d\tau}{dt}
=\sqrt{1-\frac{v^{2}}{c^{2}}}.
$$

定义洛伦兹因子

$$
\gamma(v)=\frac{dt}{d\tau}
=\frac{1}{\sqrt{1-v^{2}/c^{2}}},
$$

四速度

$$
u^{\mu}=\frac{dx^{\mu}}{d\tau}
=\gamma(v)\,(c,\mathbf v).
$$

在 Minkowski 度规 $\eta_{\mu\nu}=\mathrm{diag}(-1,1,1,1)$ 下，

$$
u^{\mu}u_{\mu}
=-\gamma^{2}c^{2}+\gamma^{2}v^{2}
=-\gamma^{2}c^{2}\Bigl(1-\frac{v^{2}}{c^{2}}\Bigr)
=-c^{2}.
$$

定义线元素 $ds^{2}=-c^{2}d\tau^{2}$，将

$$
d\tau^{2}
=dt^{2}-\frac{d\mathbf x^{2}}{c^{2}}
$$

代入，得到

$$
ds^{2}=-c^{2}dt^{2}+d\mathbf x^{2},
$$

即 Minkowski 度规。

### 定理 2 与命题 1 的证明概要

内部演化方程

$$
\mathrm i\hbar\,\partial_{\tau}\ket{\psi_{\mathrm{int}}(\tau)}
=H_{\mathrm{int}}\ket{\psi_{\mathrm{int}}(\tau)}
$$

的定态解满足

$$
\ket{\psi_{\mathrm{int}}(\tau)}
=\mathrm e^{-\mathrm i E_{0}\tau/\hbar}\ket{\psi_{\mathrm{int}}},
\qquad
H_{\mathrm{int}}\ket{\psi_{\mathrm{int}}}=E_{0}\ket{\psi_{\mathrm{int}}}.
$$

定义

$$
\omega_{\mathrm{int}}=\frac{E_{0}}{\hbar},
$$

若以 $E_{0}=m c^{2}$ 识别静止能量，则得到

$$
m=\frac{\hbar\omega_{\mathrm{int}}}{c^{2}},
$$

即定理 2。

在 Dirac 型 QCA 的连续极限中，有效 Hamilton 算符

$$
H_{\mathrm{eff}}(k)\simeq c\hbar k\sigma_{z}
+m c^{2}\sigma_{x},
$$

本征值

$$
E_{\pm}(k)=\pm\sqrt{(c\hbar k)^{2}+m^{2}c^{4}}
$$

与 Dirac Hamilton 完全一致。Heisenberg 画幅下，位置算符 $X(t)$ 满足

$$
\frac{dX}{dt}
=\frac{\mathrm i}{\hbar}[H,X]
=c\,\alpha,
\qquad
\frac{d\alpha}{dt}
=\frac{\mathrm i}{\hbar}[H,\alpha],
$$

其中 $\alpha$ 一般记作 Dirac 矩阵。积分得到

$$
X(t)=X(0)+c^{2}H^{-1}Pt
+\frac{\mathrm i\hbar c}{2}H^{-1}
\bigl(\mathrm e^{-2\mathrm i H t/\hbar}-1\bigr)
\bigl(\alpha(0)-cH^{-1}P\bigr),
$$

第二项为匀速运动，第三项为频率 $2E/\hbar$ 的快速振荡，即 Zitterbewegung，其中

$$
E=+\sqrt{(cP)^{2}+m^{2}c^{4}}.
$$

静止极限 $P=0$ 时 $E=m c^{2}$，振荡频率

$$
\omega_{\mathrm{ZB}}(0)
=\frac{2m c^{2}}{\hbar}
=2\omega_{\mathrm{int}},
$$

从而得到命题 1。

### 定理 3 的证明思路

对平移不变 QCA，可将单步幺正写为

$$
U=\int^{\oplus}U(k)\,dk,
$$

绕数

$$
\mathcal W[U]
=\frac{1}{2\pi\mathrm i}\int\partial_{k}\log\det U(k)\,dk
$$

是从 Brillouin 区到 $\mathrm U(N)$ 的映射的同伦不变量，在有限深度局域幺正变换下保持不变。拓扑平凡扇区 $\mathcal W[U]=0$ 中存在变形将 $U(k)$ 化为仅含无质量模式的形式，其内部频率可为零。拓扑非平凡扇区 $\mathcal W[U]\neq 0$ 中，存在不可消除的 Berry 相位绕行；要实现该绕行，内部 Hamilton 必须具有非零频率本征值，从而 $v_{\mathrm{int}}>0$。这一论证可借助 QCA index 理论与 $K$ 理论严格化，详见文献 [1,2]。

### 定理 4 与定理 5 的证明思路

定理 4 起点为光学度规

$$
ds^{2}=-\eta^{2}(x)c^{2}dt^{2}
+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j}.
$$

弱场下取

$$
\eta(x)=1+\epsilon(x),\qquad
|\epsilon(x)|\ll 1,
$$

展开得到

$$
g_{00}\simeq-(1+2\epsilon)c^{2},
\qquad
g_{ij}\simeq(1-2\epsilon)\gamma_{ij}.
$$

在静态球对称情形下，选取各向同性坐标并识别

$$
\epsilon(r)=\frac{\phi(r)}{c^{2}},
\qquad
\phi(r)=-\frac{GM}{r},
$$

结果与 Schwarzschild 度规弱场展开一致。折射率定义为

$$
n(r)=\eta^{-2}(r)\simeq 1-\frac{2\phi(r)}{c^{2}},
$$

由此

$$
c_{\mathrm{eff}}(r)=\frac{c}{n(r)}.
$$

将该折射率分布代入基于 Gauss–Bonnet 定理的引力透镜方法，可求得光线偏折角 $\Delta\theta=4GM/(c^{2}b)$，见文献 [3,4]。

定理 5 使用 Einstein–Hilbert 项

$$
\int\sqrt{-g}\,R\,d^{4}x
$$

的标准变分公式以及

$$
\delta(\sqrt{-g}\,\mathcal L_{\mathrm{info}})
=\tfrac12\sqrt{-g}\,T^{(\mathrm{info})}_{\mu\nu}\delta g^{\mu\nu},
$$

可得

$$
\delta S_{\mathrm{tot}}
=\frac{1}{16\pi G}\int\sqrt{-g}
\bigl(R_{\mu\nu}-\tfrac12 R g_{\mu\nu}\bigr)
\delta g^{\mu\nu}\,d^{4}x
+\frac12\int\sqrt{-g}\,T^{(\mathrm{info})}_{\mu\nu}
\delta g^{\mu\nu}\,d^{4}x.
$$

令 $\delta S_{\mathrm{tot}}=0$ 对任意紧支撑 $\delta g^{\mu\nu}$ 成立，即得

$$
R_{\mu\nu}-\tfrac12 R g_{\mu\nu}
=8\pi G\,T^{(\mathrm{info})}_{\mu\nu}.
$$

### 定理 6 与命题 2 的证明思路

假设 $v_{\mathrm{int}}(M_{I})$ 单调递增且

$$
\lim_{M_{I}\to\infty}v_{\mathrm{int}}(M_{I})=c。
$$

由信息速率守恒有

$$
v_{\mathrm{ext}}^{2}(M_{I})
=c^{2}-v_{\mathrm{int}}^{2}(M_{I}),
$$

当 $M_{I}\to\infty$ 时，$v_{\mathrm{ext}}(M_{I})\to 0$，得到渐近静止。

命题 2 源自 Landauer 原理：擦除一比特信息最少耗散 $k_{B}T\ln 2$ 的热量。若单位时间擦除

$$
\dot I_{\mathrm{erase}}
=R_{\mathrm{upd}}\Delta I
$$

比特，则最小功耗

$$
P_{\min}
=k_{B}T\ln 2\,\dot I_{\mathrm{erase}}
=k_{B}T\ln 2\,R_{\mathrm{upd}}\Delta I,
$$

独立于系统的具体物理实现，仅依赖擦除信息量与环境温度。

---

## Model Apply

### 自由粒子与狭义相对论极限

在单粒子 QCA 模型中，假设连续极限下有效 Hamilton 具有相对论色散关系

$$
E^{2}=p^{2}c^{2}+m^{2}c^{4},
$$

则四动量

$$
p^{\mu}=m u^{\mu}
$$

自动满足

$$
p^{\mu}p_{\mu}=-m^{2}c^{2}.
$$

由于定理 1 已经规范化四速度 $u^{\mu}$，能量–动量关系与 Lorentz 变换性质自然随之出现。对无质量模式（拓扑平凡 QCA 中的类光激发），内部频率可为零，$v_{\mathrm{int}}=0$、$v_{\mathrm{ext}}=c$，内部演化被冻结，与光子作为无静止质量激发的性质一致。

### 多体体系与天体物理

在恒星、星系与星系团等宏观体系中，能量密度、粒子数密度与信息处理密度在统计意义上高度相关：高能量密度通常意味着大量自由度参与高频相互作用，从而 $\rho_{\mathrm{info}}(x)$ 较大、$\eta(x)$ 较小、折射率 $n(x)$ 较大、几何更弯曲。在这一尺度上，$\rho_{\mathrm{info}}(x)$ 与应力–能量张量 $T_{\mu\nu}$ 的差异可视为重整化与粗粒化效应，在观测上难以区分。因此，本框架在经典天体物理检验上的预言与广义相对论基本一致。

具有区分度的检验应集中在信息结构可变而总能量近乎不变的体系，例如具有不同纠缠结构的量子介质或拓扑相。

### 黑洞熵与信息速率饱和

在黑洞视界附近，Bekenstein–Hawking 熵与视界面积成正比，暗示单位面积可容纳的信息自由度数目受到普适上界约束。本框架下，视界可理解为 $\rho_{\mathrm{info}}(x)$ 达到饱和值的区域：此处 $\eta(x)$ 接近某一极限，导致外部传播严重受抑制，内部自由度占用几乎全部光程配额。黑洞熵可解释为视界上“可承载内部自指结构的最大信息速率积分”。要将

$$
S_{\mathrm{BH}}=\frac{A}{4G}
$$

从 QCA 信息参数严格推导，需要结合具体 QCA 模型与重整化分析。

### 宇宙学与有效宇宙学常数

在宇宙学尺度上，可定义粗粒化的宇宙学平均信息处理密度 $\rho_{\mathrm{info}}^{\mathrm{cosmo}}(t)$。其平滑分量可通过 $\mathcal L_{\mathrm{info}}$ 吸收到有效“信息真空能”项中，在 Friedmann 方程中扮演类似宇宙学常数或暗能量的角色；若 $\rho_{\mathrm{info}}^{\mathrm{cosmo}}(t)$ 随时间缓慢变化，则可产生类似动力学暗能量的观测特征。这一方向需要在具体宇宙学背景下引入 QCA 模型和重整化方案。

---

## Engineering Proposals

### 超导微波腔中的“人造高折射率”实验

考虑高品质因数的超导微波腔或电路 QED 平台，其体积 $V$ 固定，内部存在若干可控电磁场模。通过外部驱动与反馈，可在腔体内制备多种量子态，并通过量子层析表征其纠缠结构。设通过反馈控制，将腔体总能量 $E_{\mathrm{tot}}$ 固定在某一值。

设计两类内部态：

* 态 A：在给定 $E_{\mathrm{tot}}$ 下，各模近似非纠缠或弱纠缠，拓扑平凡，对应“低信息结构态”；

* 态 B：在同一 $E_{\mathrm{tot}}$ 下，制备高度纠缠、可能具有非平庸拓扑序的多模量子态，对应“高信息结构态”。

在标准广义相对论中，引力源由应力–能量张量 $T_{\mu\nu}$ 决定，而 Maxwell 场在该设定下的 $T_{\mu\nu}$ 在宏观上只依赖能量密度与压力，纠缠结构不进入源项。因此，只要 $E_{\mathrm{tot}}$ 与宏观空间分布相同，态 A 与态 B 对外部几何的影响应相同，通过腔附近的 Shapiro 延迟也应相同。

在本文框架中，高纠缠或拓扑有序态意味着更高的 $\rho_{\mathrm{info}}(x)$，即单位时间内内部 Hilbert 空间中发生更多“路径长度”，即使总能量不变。这导致 $\eta(x)$ 与折射率 $n(x)=\eta^{-2}(x)$ 的变化。若在腔体附近布置高灵敏干涉仪，使探测光束多次穿越该区域，则在态 A 与态 B 切换时，将在干涉条纹中测量到差分相位延迟

$$
\Delta\phi_{\mathrm{info}}
\sim\frac{\omega}{c}\int_{\mathrm{path}}\Delta n(\mathbf x)\,d\ell,
$$

其中 $\omega$ 为光频，$\Delta n(\mathbf x)$ 为由信息结构差异引起的折射率变化。

在标准广义相对论中，由于宏观 $T_{\mu\nu}$ 不变，预言 $\Delta\phi\approx 0$；在本文框架中，预言 $\Delta\phi\neq 0$。若在控制系统误差与噪声的前提下观测到稳定的差分相位延迟，将构成“纠缠引力”相对于“能量引力”的直接证据。

### 量子模拟平台中的 Dirac-QCA 实验

多种平台（如离子阱、光学格点、光子线路）已实现离散时间量子行走与 Dirac 型 QCA，并观测到 Zitterbewegung 等相对论特征。通过调节模型参数可实现不同有效质量与拓扑结构；若进一步能够表征内部态演化速率（例如通过对自旋自由度的相干操控与层析），则可在实验上检验近似关系

$$
v_{\mathrm{ext}}^{2}(k)+v_{\mathrm{int}}^{2}(k)\simeq c^{2}
$$

是否成立，并观察 $v_{\mathrm{int}}(k)$ 如何随质量与拓扑不变量变化。这将为“光程配额在内部与外部分配”的图像提供量子模拟支持。

---

## Discussion (risks, boundaries, past work)

现有 QCA 研究已系统展示如何从离散模型涌现自由量子场论与部分相互作用场论，并对 QCA 的 index 理论与拓扑分类给出严谨描述〔参见文献 [1,2]〕。本文在此基础上引入信息速率守恒公理，将 Minkowski 几何与狭义相对论视为信息速率约束的几何表达，并将 Dirac-QCA 中的 Zitterbewegung 解释为内部频率结构在外部坐标上的显现。

光学度规与 Gauss–Bonnet 定理在引力透镜理论中的应用已表明“引力弯曲光线”与“变化的折射率”之间的等价关系〔参见文献 [3,4]〕。本文通过 $\rho_{\mathrm{info}}(x)$ 给折射率 $n(x)$ 赋予微观含义，将宏观光学度规与微观 QCA 信息处理联系起来。

信息视角的引力理论亦有其他方案，例如从局域热力学与 Clausius 关系推导爱因斯坦方程的工作，以及各种“熵引力”方案；Landauer 原理则从不可逆计算的角度提供信息–能量关系的普适下界〔参见文献 [5]〕。本文的特点在于：从离散 QCA 本体出发，以信息速率守恒为微观强约束，再通过 Hilbert 空间几何与拓扑结构导出连续几何与质量的诠释，并给出以 $\rho_{\mathrm{info}}(x)$、$\eta(x)$、$n(x)$ 为核心的光学引力图像。

需要强调的风险包括：从 QCA 到连续流形与度规的粗粒化一般不唯一，$\rho_{\mathrm{info}}(x)$ 的定义需要避免对内部自由度选择的规范依赖；信息质量 $M_{I}$ 的可计算性问题限制了其在具体系统中的定量应用；在实验上实现“纠缠引力”检验的技术挑战显著。这些问题界定了本文框架的适用边界。

---

## Conclusion

在量子元胞自动机与有限信息本体论框架下，引入信息速率（光程）守恒这一单一公理，可对狭义相对论、质量、引力以及信息质量之间的关系给出统一描述。主要结论包括：

1. 信息速率守恒与固有时间定义足以导出 Minkowski 几何与狭义相对论的时间膨胀与四速度规范化；

2. 质量可以解释为内部自指频率 $\omega_{\mathrm{int}}$ 的比例系数 $m=\hbar\omega_{\mathrm{int}}/c^{2}$，并在 Dirac-QCA 中通过 Zitterbewegung 频率 $\omega_{\mathrm{ZB}}=2\omega_{\mathrm{int}}$ 得到体现；

3. 局域信息处理密度 $\rho_{\mathrm{info}}(x)$ 与光学度规

   $$
   ds^{2}=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j}
   $$

   的组合在弱场极限下恢复 Schwarzschild 度规的一阶展开与正确的光线偏折因子；

4. 信息–引力变分原理给出形式上等价于爱因斯坦场方程的几何–信息统一表达，其中 $T^{(\mathrm{info})}_{\mu\nu}$ 概括了信息处理对几何的源项作用；

5. 信息质量 $M_{I}$ 及其 Landauer 代价为高复杂度能动系统的引力与耗散特性提供统一刻画，高 $M_{I}$ 主体在外部几何中趋于渐近静止，并必然伴随持续的熵流输出。

未来工作包括：在具体 QCA 模型中构造显式的 $\mathcal L_{\mathrm{info}}$，并验证其与标准量子场论应力–能量张量的一致性；在黑洞与宇宙学背景下，将 $\rho_{\mathrm{info}}$ 与面积熵、宇宙学常数、暗能量等问题联系起来；在人工量子系统中设计可行实验，直接测量有效光速或时钟频率随纠缠熵与信息密度的变化行为。若这些方向取得进展，信息速率守恒有望成为连接微观计算本体与宏观几何叙事的一条统一路径。

---

## Acknowledgements, Code Availability

本研究建立在量子元胞自动机、离散引力、引力透镜几何方法与信息热力学等领域的既有成果之上，尤其依赖于关于 QCA–量子场论连续极限、QCA 拓扑分类、基于 Gauss–Bonnet 的引力透镜方法以及 Landauer 原理的系统研究〔见文献 [1–5]〕。

本文未使用数值模拟代码，所有推导均为解析形式。若未来在具体 QCA 模型与数值验证方面有进一步工作，相应代码将另行整理与公开。

---

## References

[1] T. Farrelly, “A Review of Quantum Cellular Automata”, Quantum 4, 368 (2020).

[2] A. Bisio, G. M. D’Ariano, A. Tosini, “Dirac Quantum Cellular Automaton in One Dimension: Zitterbewegung and Scattering from Potential”, Phys. Rev. A 88, 032301 (2013).

[3] G. W. Gibbons, M. C. Werner, “Applications of the Gauss–Bonnet Theorem to Gravitational Lensing”, Class. Quantum Grav. 25, 235009 (2008).

[4] M. Halla, “Application of the Gauss–Bonnet Theorem to Lensing in Static Spherically Symmetric Spacetimes”, Gen. Relativ. Gravit. 52, 95 (2020).

[5] R. Landauer, “Irreversibility and Heat Generation in the Computing Process”, IBM J. Res. Dev. 5, 183–191 (1961).

[6] 更多关于 QCA 拓扑分类、量子模拟平台与广义光学度规方法的文献综述，可参见文献 [1–4] 及其所引参考文献。

---

# 附录 A：一维 Dirac-QCA 的连续极限与信息速率守恒

本附录给出一维 Dirac 型 QCA 的具体定义及其连续极限，并说明如何在该模型中显式实现信息速率守恒关系。

## A.1 模型定义

考虑一维格点 $\Lambda=a\mathbb Z$，每个格点 $x$ 携带双组分自旋

$$
\psi_{x}=
\begin{pmatrix}
\psi_{x,\mathrm L}\\[2pt]
\psi_{x,\mathrm R}
\end{pmatrix}.
$$

定义条件平移算符 $S$ 为

$$
(S\psi)_{x,\mathrm L}=\psi_{x+a,\mathrm L},\qquad
(S\psi)_{x,\mathrm R}=\psi_{x-a,\mathrm R},
$$

内部旋转

$$
W(\theta)=
\begin{pmatrix}
\cos\theta & -\mathrm i\sin\theta\\[2pt]
-\mathrm i\sin\theta & \cos\theta
\end{pmatrix}.
$$

单步 QCA 演化为

$$
\psi(t+\Delta t)=U(\theta)\psi(t),
\qquad
U(\theta):=W(\theta)S.
$$

在动量表象中，

$$
\psi_{k}=\sum_{x}\mathrm e^{-\mathrm i k x}\psi_{x},
$$

有

$$
S(k)=\mathrm e^{\mathrm i k a\sigma_{z}},
\qquad
U(\theta;k)=W(\theta)S(k).
$$

## A.2 有效 Hamilton 与 Dirac 方程

取 $a,\Delta t,\theta$ 同时趋小，定义有效 Hamilton 算符

$$
H_{\mathrm{eff}}(k)
=\frac{\mathrm i\hbar}{\Delta t}\,\log U(\theta;k).
$$

对小参数展开得

$$
\log U(\theta;k)
\simeq\mathrm i k a\sigma_{z}-\mathrm i\theta\sigma_{x},
$$

从而

$$
H_{\mathrm{eff}}(k)
\simeq\frac{\hbar}{\Delta t}(k a\sigma_{z}+\theta\sigma_{x}).
$$

令

$$
c=\frac{a}{\Delta t},
\qquad
m c^{2}=\frac{\hbar\theta}{\Delta t},
$$

得到

$$
H_{\mathrm{eff}}(k)
\simeq c\hbar k\sigma_{z}+m c^{2}\sigma_{x},
$$

其位置空间形式为一维 Dirac 方程

$$
\mathrm i\hbar\,\partial_{t}\psi(x,t)
=\bigl(-\mathrm i\hbar c\sigma_{z}\partial_{x}
+m c^{2}\sigma_{x}\bigr)\psi(x,t).
$$

色散关系为

$$
E_{\pm}(k)
=\pm\sqrt{(c\hbar k)^{2}+m^{2}c^{4}},
$$

群速度

$$
v_{\mathrm{ext}}(k)
=\frac{1}{\hbar}\frac{\partial E_{+}}{\partial k}
=\frac{c^{2}k}{\sqrt{k^{2}+(m c/\hbar)^{2}}}
<c.
$$

## A.3 内部速度与信息速率守恒

对固定 $k$，内部态为二维自旋空间的本征态 $\ket{u_{\pm}(k)}$，其内部相位以频率 $E_{\pm}(k)/\hbar$ 演化。采用 Fubini–Study 度量，可将内部演化速度定义为

$$
v_{\mathrm{int}}(k)
=\alpha\,\frac{E_{+}(k)}{\hbar},
$$

其中 $\alpha$ 为无量纲归一化常数。通过条件

$$
v_{\mathrm{int}}(0)=c
$$

确定 $\alpha$，得到

$$
v_{\mathrm{int}}(k)
=c\,\frac{\sqrt{k^{2}+(m c/\hbar)^{2}}}{m c/\hbar}
=c\sqrt{1-\frac{v_{\mathrm{ext}}^{2}(k)}{c^{2}}},
$$

从而满足

$$
v_{\mathrm{ext}}^{2}(k)+v_{\mathrm{int}}^{2}(k)=c^{2}.
$$

这一构造在 Dirac-QCA 模型中显式实现了信息速率守恒，为本文公理提供了具体模型支撑。

---

# 附录 B：光学度规、局域体积守恒与光线偏折

本附录推导光学度规的构造以及弱场极限下的引力光线偏折，并统一 $c_{\mathrm{eff}}$、$n(r)$、$\eta(r)$、$\phi(r)$ 之间的关系。

## B.1 局域体积元与缩放因子约束

在度规

$$
ds^{2}=-\eta^{2}(x)c^{2}dt^{2}
+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j}
$$

下，四体积元

$$
dV_{4}=\sqrt{-g}\,d^{4}x.
$$

在各向同性假设下，可将三维空间度规写为

$$
\gamma_{ij}dx^{i}dx^{j}
=\Psi^{4}(x)\,d\mathbf x^{2},
$$

此时

$$
\sqrt{-g}
\propto\eta(x)\,\eta^{-3}(x)\Psi^{6}(x)
=\eta^{-2}(x)\Psi^{6}(x).
$$

局域 Hilbert 体积守恒可简化为“单位坐标体积对应的物理 Hilbert 体积不变”，用约束

$$
\eta_{t}(x)\,\eta_{x}^{3}(x)=1
$$

表达。在各向同性下取

$$
\eta_{t}(x)=\eta(x),\qquad
\eta_{x}(x)=\eta^{-1}(x),
$$

得到光学度规形式

$$
ds^{2}=-\eta^{2}(x)c^{2}dt^{2}
+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j}.
$$

## B.2 弱场展开与 Schwarzschild 度规

在静态、球对称情形下，Schwarzschild 度规在各向同性坐标 $(t,r,\theta,\varphi)$ 中可写成

$$
ds^{2}
=-\Bigl[\frac{1-\frac{GM}{2c^{2}r}}{1+\frac{GM}{2c^{2}r}}\Bigr]^{2}c^{2}dt^{2}
+\Bigl(1+\frac{GM}{2c^{2}r}\Bigr)^{4}(dr^{2}+r^{2}d\Omega^{2}).
$$

在弱场近似 $\frac{GM}{c^{2}r}\ll 1$ 下展开得

$$
g_{00}\simeq-\Bigl(1-\frac{2GM}{c^{2}r}\Bigr)c^{2}
=-(1+2\phi/c^{2})c^{2},
$$

$$
g_{ij}\simeq\Bigl(1+\frac{2GM}{c^{2}r}\Bigr)\delta_{ij}
=(1-2\phi/c^{2})\delta_{ij},
$$

其中

$$
\phi(r)=-\frac{GM}{r}
$$

为牛顿势。

以光学度规为起点，取

$$
\eta(r)=1+\frac{\phi(r)}{c^{2}},
\qquad
\gamma_{ij}=\delta_{ij},
$$

展开得

$$
g_{00}=-\eta^{2}c^{2}
\simeq-(1+2\phi/c^{2})c^{2},
$$

$$
g_{ij}=\eta^{-2}\delta_{ij}
\simeq(1-2\phi/c^{2})\delta_{ij},
$$

与 Schwarzschild 度规弱场展开一致。

## B.3 折射率与光线偏折角

在光学度规下对零测地线 $ds^{2}=0$ 有

$$
\eta^{2}(r)c^{2}dt^{2}
=\eta^{-2}(r)\,d\mathbf x^{2},
$$

坐标光速

$$
c_{\mathrm{eff}}(r)
=\Bigl|\frac{d\mathbf x}{dt}\Bigr|
=\eta^{2}(r)c.
$$

折射率定义为

$$
n(r):=\frac{c}{c_{\mathrm{eff}}(r)}=\eta^{-2}(r).
$$

在弱场极限

$$
\eta(r)=1+\frac{\phi(r)}{c^{2}},
\qquad
\Bigl|\frac{\phi(r)}{c^{2}}\Bigr|\ll 1,
$$

一阶展开得

$$
n(r)=\eta^{-2}(r)
\simeq 1-\frac{2\phi(r)}{c^{2}}.
$$

取 $\phi(r)=-GM/r$ 得

$$
n(r)\simeq 1+\frac{2GM}{c^{2}r}>1,
\qquad
c_{\mathrm{eff}}(r)=\frac{c}{n(r)}<c,
$$

与弱场引力中光线减速的物理图像一致。

在 Gibbons–Werner 方法中，可将光学度规视为二维 Riemann 曲面，将光线轨迹视为该曲面上的测地线，通过 Gauss–Bonnet 定理计算偏折角。弱偏折极限下，得到

$$
\Delta\theta
\simeq\frac{4GM}{c^{2}b},
$$

与爱因斯坦预测一致。若只修改 $g_{00}$ 而保持空间度规平坦，对应折射率仅为

$$
n(r)\simeq 1-\frac{\phi(r)}{c^{2}},
$$

偏折角将只有上述值的一半，说明同时变形时间与空间刻度（即引入光学度规）对恢复正确偏折因子至关重要。

---

# 附录 C：Dirac 理论中 Zitterbewegung 与内部频率

本附录给出 Dirac 理论中 Zitterbewegung 频率与内部频率的标准推导，并与本文的质量–频率关系相对照。

## C.1 Dirac 方程与平面波解

考虑一维 Dirac 方程

$$
\mathrm i\hbar\,\partial_{t}\psi
=(c\alpha p+\beta m c^{2})\psi,
$$

取表示

$$
\alpha=\sigma_{z},\qquad
\beta=\sigma_{x},
\qquad
p=-\mathrm i\hbar\,\partial_{x}.
$$

平面波解为

$$
\psi_{k,\pm}(x,t)
=u_{\pm}(k)\,\mathrm e^{\mathrm i(kx-\omega_{\pm}t)},
$$

$$
\omega_{\pm}
=\pm\sqrt{(c k)^{2}+\frac{m^{2}c^{4}}{\hbar^{2}}}.
$$

一般波包可写为

$$
\psi(x,t)
=\int\bigl(a_{+}(k)\psi_{k,+}(x,t)
+a_{-}(k)\psi_{k,-}(x,t)\bigr)\,dk.
$$

## C.2 Heisenberg 图像下的位置算符

在 Heisenberg 画幅中，位置算符随时间演化

$$
X(t)
=\mathrm e^{\mathrm i H t/\hbar}X(0)\mathrm e^{-\mathrm i H t/\hbar},
\qquad
H=c\alpha p+\beta m c^{2}.
$$

Heisenberg 方程给出

$$
\frac{dX}{dt}
=\frac{\mathrm i}{\hbar}[H,X]
=c\alpha,
\qquad
\frac{d\alpha}{dt}
=\frac{\mathrm i}{\hbar}[H,\alpha].
$$

解出 $\alpha(t)$ 并代回 $X(t)$ 得

$$
X(t)
=X(0)+c^{2}H^{-1}Pt
+\frac{\mathrm i\hbar c}{2}H^{-1}
\bigl(\mathrm e^{-2\mathrm i H t/\hbar}-1\bigr)
\bigl(\alpha(0)-cH^{-1}P\bigr),
$$

其中第二项为匀速运动，第三项为频率 $2E/\hbar$ 的快速振荡项，即 Zitterbewegung，$E=+\sqrt{(c P)^{2}+m^{2}c^{4}}$ 为正能量分支。在静止极限 $P=0$ 时 $E=m c^{2}$，振荡频率为

$$
\omega_{\mathrm{ZB}}(0)
=\frac{2m c^{2}}{\hbar}.
$$

在本文框架中，内部频率定义为

$$
\omega_{\mathrm{int}}=\frac{m c^{2}}{\hbar},
$$

从而

$$
\omega_{\mathrm{ZB}}(0)=2\omega_{\mathrm{int}},
$$

与正能量分支与负能量分支之间干涉的标准解释相吻合。

---

# 附录 D：信息质量、Landauer 原理与最小功耗

本附录讨论维持固定信息质量所需的最小热力学代价，展示 Landauer 原理如何限制高信息质量系统的物理实现。

## D.1 信息擦除与最小耗散

设某系统内部状态为 $\sigma$，其信息质量 $M_{I}(\sigma)$ 与内部模型规模及复杂度有关。为了保持模型的时效性，系统必须定期用新观测更新内部表示，这一过程必然涉及对部分旧信息的擦除。

假设系统以速率 $R_{\mathrm{upd}}$ 进行模型更新，每次更新平均擦除 $\Delta I$ 比特旧信息，则单位时间内擦除信息量为

$$
\dot I_{\mathrm{erase}}
=R_{\mathrm{upd}}\Delta I.
$$

在温度为 $T$ 的热浴中，根据 Landauer 原理，擦除一比特信息至少要将热量 $k_{B}T\ln 2$ 散入环境；最小耗散功率为

$$
P_{\min}
=k_{B}T\ln 2\,\dot I_{\mathrm{erase}}
=k_{B}T\ln 2\,R_{\mathrm{upd}}\Delta I。
$$

这一结果独立于系统的具体物理实现，只依赖于擦除信息的比特数与环境温度，是对任何实现高信息质量系统所需功耗的普适下界。

## D.2 高信息质量与高耗散

若信息质量 $M_{I}(\sigma)$ 随内部模型规模、结构复杂度和更新频率增大而增大，则更大的 $M_{I}$ 通常需要更大的 $R_{\mathrm{upd}}$ 与 $\Delta I$，以持续剔除过时信息并引入新信息。因此，一般情形下

$$
P_{\min}(M_{I})
=k_{B}T\ln 2\,R_{\mathrm{upd}}(M_{I})\Delta I(M_{I})
$$

将随 $M_{I}$ 增大而增大。

结合本文的信息速率守恒公理，可以得到统一图景：

1. 为维持高 $M_{I}$，系统必须将大量光程配额用于内部演化（$v_{\mathrm{int}}$ 大），从而外部运动速度 $v_{\mathrm{ext}}$ 受到限制，表现为渐近静止；

2. 同时，内部频繁更新与擦除导致持续的熵流向外界，系统成为显著热源，表现为强耗散特性；

3. 在宏观上，这两种效应往往出现在引力势阱较深的区域：恒星内部通过核反应维持高信息密度与复杂结构，同时向外发射巨量辐射；生命系统与神经系统通过代谢维持低熵结构，同时向环境输出热量。

因此，在信息速率守恒的视角下，质量、引力与复杂能动结构之间的关联可统一理解为：要在内部维持高度有序、拓扑稳定的结构，就必须持续消耗光程配额并向外输出熵与能量，而这一过程在几何上表现为曲率，在动力学上表现为引力。



