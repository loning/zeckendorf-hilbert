# 信息速率的普适守恒：从量子元胞自动机到相对论、质量与引力的统一

Version: 2.0

## Abstract

在量子元胞自动机（quantum cellular automaton, QCA）与有限信息本体论框架下，构造单粒子长波激发的有效描述，证明一个基于 Hilbert 空间几何与幺正性的核心结果：对于任意由局域幺正演化与平移不变性定义、在连续极限中涌现一维 Dirac 型 Hamilton 的离散量子游走/QCA，其长波单粒子本征模的外部群速度 ($v_{\mathrm{ext}}$) 与内部态演化速度 ($v_{\mathrm{int}}$) 必然满足信息速率守恒定理

$$v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2},$$

其中 $c$ 为格点系统的最大因果传播速率。该定理并非附加公理，而是由 QCA 的局域幺正性与内部自由度的反对易代数在 Fubini–Study 射影度规下的正交分解所强制的几何结果。

以内部演化参数定义固有时间 ($\tau$)，可从信息速率守恒定理直接导出狭义相对论的时间膨胀、四速度规范化与 Minkowski 线元。在 Dirac 型 QCA 的连续极限中，内部 Hamilton 算符 ($H_{\mathrm{int}}$) 给出内部频率 ($\omega_{\mathrm{int}}$)，质量获得信息论定义

$$m c^{2}=\hbar\omega_{\mathrm{int}},$$

并满足 Zitterbewegung 频率关系

$$\omega_{\mathrm{ZB}}=2\omega_{\mathrm{int}}.$$

结合 QCA 的绕数与指数不变量，可将 massive 激发解释为拓扑非平凡自指回路中被束缚的光程配额。在多体层面，引入局域信息处理密度 ($\rho_{\mathrm{info}}(x)$)，从局域信息体积守恒导出光学度规

$$ds^{2}=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j},$$

其中 $\eta(x)$ 决定局域有效光速

$$c_{\mathrm{eff}}(x)=\eta^{2}(x)c,$$

与折射率

$$n(x)=\eta^{-2}(x).$$

在弱场极限下，该结构恢复 Schwarzschild 度规的一阶展开及标准光线偏折角，并可通过信息–引力变分原理得到形式上等价于爱因斯坦方程的场方程。进一步引入信息质量 ($M_{I}$)，结合 Landauer 原理分析高信息质量主体的渐近静止行为与最小耗散功率，给出质量、引力与复杂能动结构的统一信息论刻画，并提出基于超导量子电路与量子模拟平台的可检验预言。

## Keywords

量子元胞自动机；信息速率守恒；Fubini–Study 度规；光学度规；狭义相对论；广义相对论；拓扑质量；Zitterbewegung；信息质量；Landauer 原理

---

## Introduction & Historical Context

狭义与广义相对论将物理世界刻画为带 Lorentz 签名的四维流形 ($(M,g_{\mu\nu})$)。度规张量 ($g_{\mu\nu}$) 决定因果结构与测地线，场方程

$$R_{\mu\nu}-\tfrac12 R g_{\mu\nu}=8\pi G T_{\mu\nu}$$

将应力–能量张量 ($T_{\mu\nu}$) 与曲率联系起来，引力红移、光线偏折、双星脉冲计时与引力波探测等实验检验高度支持这一几何叙事。相对论在建构上以光速不变与相对性原理为公理，引入 Minkowski 线元与 Lorentz 变换，其几何结构通常被视为先验背景。

量子理论则在 Hilbert 空间 ($\mathcal H$) 中表述，态为向量或密度算符，可观测量为自伴算符，时间演化由幺正群生成。统计解释建立在 Born 规则之上，叠加、内禀相位与纠缠构成核心结构。两类理论在量子场论中通过"场算符定义在背景流形上"的方式拼接，但本体论起点仍然分离：一侧是连续可弯曲的时空流形，另一侧是抽象的线性 Hilbert 空间。

当接近普朗克尺度时，连续流形与经典度规的假设失去经验支撑，而 Hilbert 空间结构本身并不依赖连续时空。量子元胞自动机（quantum cellular automaton, QCA）提供一种以离散结构为本体的替代表述：在可数格点上定义有限维局域 Hilbert 空间与局域幺正演化，要求严格因果性与有限传播半径。已有研究表明，在适当的连续极限下，Dirac、Weyl 以及 Maxwell 方程可以从 QCA 的局域幺正演化中涌现，并且 QCA 具有系统的拓扑分类与 index 理论。

另一方面，Hilbert 空间本身具有自然的射影几何结构。射影 Hilbert 空间 ($\mathbb C P^{n}$) 装备 Fubini–Study 度规，其弧长给出量子态之间的自然距离。对于由时间无关 Hamilton ($H$) 驱动的幺正演化，态矢量在 Fubini–Study 度规下的"速度"由能量不确定度 ($\Delta H$) 决定，量子演化的"路径长度"可视为一种信息更新量。

本文尝试将上述三条线索统一在一个信息论视角下：

1. 假定宇宙在微观上由局域幺正、平移不变的 QCA 描述，具有最大传播速率 ($c$)；

2. 将单粒子长波激发视为 QCA 中的一类有效模式，其外部运动由群速度 ($v_{\mathrm{ext}}$) 描述，内部态的自指演化由射影 Hilbert 空间中的几何速度 ($v_{\mathrm{int}}$) 描述；

3. 证明在 Dirac 型 QCA 连续极限下，由 Hamilton 的反对易结构与 Fubini–Study 度规诱导的正交分解必然给出信息速率守恒定理

   $$v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2},$$

   从而将"光程守恒"从假设提升为定理。

在这一基础上，可以不再将狭义相对论视为独立公理，而是视为 QCA 幺正性与 Hilbert 几何的涌现结果；可以将质量解释为内部频率 ($\omega_{\mathrm{int}}$) 的系数，将引力几何解释为局域信息处理密度与光学度规结构的表现；并可以将复杂能动系统的"信息质量"与 Landauer 原理联系起来，给出质量、引力与复杂性的统一图景。

---

## Model & Assumptions

### QCA 宇宙与局域幺正性

设 $\Lambda$ 为可数连通图，其节点代表"空间元胞"。每个元胞 ($x\in\Lambda$) 携带有限维 Hilbert 空间 ($\mathcal H_{x}\simeq\mathbb C^{d}$)。对任意有限子集 ($F\Subset\Lambda$) 定义局域 Hilbert 空间

$$\mathcal H_{F}=\bigotimes_{x\in F}\mathcal H_{x},$$

局域算符代数为 ($\mathcal B(\mathcal H_{F})$)。全局准局域 ($C^{\ast}$) 代数为

$$\mathcal A=\overline{\bigcup_{F\Subset\Lambda}\mathcal B(\mathcal H_{F})}.$$

量子元胞自动机由 ($\ast$)-自同构 ($\alpha:\mathcal A\to\mathcal A$) 指定，要求存在幺正算符 ($U$) 使

$$\alpha(A)=U^{\dagger}AU,\qquad A\in\mathcal A,$$

并存在有限传播半径 ($R<\infty$)，使对任意支撑于 ($F$) 的局域算符 ($A$) 有

$$\mathrm{supp},\alpha(A)\subset B_{R}(F),$$

其中 ($B_{R}(F)$) 为 ($F$) 在图距离意义下的 ($R$) 邻域。给定初始态 ($\omega_{0}$) 后，离散时间演化为

$$\omega_{n}=\omega_{0}\circ\alpha^{n},\qquad n\in\mathbb Z.$$

假设 ($\Lambda$) 可嵌入三维欧氏空间，具有有效格距 ($a$)，单步演化对应物理时间 ($\Delta t$)。若 ($R=1$)，则最大传播速率为

$$c=\frac{a}{\Delta t}.$$

有限局域维数与有限传播半径意味着，在任意有限时空窗内可区分物理态数目有限，宇宙在任意有限区域内的信息容量存在上界。

### 单激发有效空间与外部速度

考虑一个局域"单激发"模式，在适当近似下其有效 Hilbert 空间可表示为

$$\mathcal H_{\mathrm{eff}}\simeq\mathcal H_{\mathrm{COM}}\otimes\mathcal H_{\mathrm{int}},$$

其中 ($\mathcal H_{\mathrm{COM}}$) 描述中心坐标或波包包络，($\mathcal H_{\mathrm{int}}$) 描述内部自由度。

在连续极限下，($\mathcal H_{\mathrm{COM}}$) 上存在近似位置算符 ($X$) 与动量算符 ($P$)，有效 Hamilton 算符 ($H_{\mathrm{eff}}$) 生成粗粒化时间演化。定义外部（群）速度

$$v_{\mathrm{ext}}=\frac{d}{dt}\langle X\rangle=\frac{1}{\mathrm i\hbar}\langle[X,H_{\mathrm{eff}}]\rangle.$$

在对称情形下，长波单粒子本征模可按动量标记，($|\psi_{p}\rangle$) 满足

$$H_{\mathrm{eff}}|\psi_{p}\rangle=E(p)|\psi_{p}\rangle,$$

该模的群速度为

$$v_{\mathrm{ext}}(p)=\frac{dE}{dp}.$$

### 内部 Hilbert 空间与 Fubini–Study 度规

内部态 ($|\psi_{\mathrm{int}}(t)\rangle\in\mathcal H_{\mathrm{int}}$) 可视为射影空间 ($\mathbb C P^{D_{\mathrm{int}}-1}$) 上的点。Fubini–Study 度量

$$ds_{\mathrm{FS}}^{2}=4\bigl(1-|\langle\psi\mid\psi+d\psi\rangle|^{2}\bigr)$$

给出射影 Hilbert 空间中两态之间的自然距离。对时间无关 Hamilton ($H$) 的幺正演化

$$\mathrm i\hbar,\partial_{t}|\psi(t)\rangle=H|\psi(t)\rangle,$$

可定义 Fubini–Study 速度

$$v_{\mathrm{FS}}:=\frac{ds_{\mathrm{FS}}}{dt}.$$

对一般态 ($v_{\mathrm{FS}}$) 与能量不确定度 ($\Delta H$) 相关，而对能量本征态 ($v_{\mathrm{FS}}=0$)。在本文框架中，重点不在于全局 ($\mathcal H$) 上的 ($v_{\mathrm{FS}}$)，而在于将 ($H$) 分解为对应外部平移与内部自指的两个互相正交的生成元，由此在内部射影空间上定义"内部演化速度"

$$v_{\mathrm{int}}:=\frac{ds_{\mathrm{FS}}^{(\mathrm{int})}}{dt}\ge 0。$$

这一速度刻画内部态在 ($\mathbb C P^{D_{\mathrm{int}}-1}$) 中的几何运动速率，其定义依赖于对 Hamilton 的正交分解。

### Dirac 型 QCA 与 Hamilton 的正交分解

以一维 Dirac 型 QCA 为具体模型。在长波极限下，其有效 Hamilton 算符可写为

$$H_{\mathrm{eff}}(p)=c,\hat p,\sigma_{z}+m c^{2}\sigma_{x},$$

其中 ($\sigma_{x},\sigma_{z}$) 为 Pauli 矩阵，($\hat p=-\mathrm i\hbar\partial_{x}$)，($m$) 为有效质量参数。

将其分解为

$$H_{T}=c,\hat p,\sigma_{z},\qquad H_{M}=m c^{2}\sigma_{x},\qquad H=H_{T}+H_{M}.$$

($H_{T}$) 生成外部平移，($H_{M}$) 生成内部自指旋转。Pauli 矩阵满足反对易关系

$${\sigma_{z},\sigma_{x}}=\sigma_{z}\sigma_{x}+\sigma_{x}\sigma_{z}=0,$$

以及 ($\sigma_{x}^{2}=\sigma_{z}^{2}=\mathbb I$)。因此

$$H^{2}=H_{T}^{2}+H_{M}^{2}=(c^{2}\hat p^{2}+m^{2}c^{4})\mathbb I。$$

这给出相对论能量–动量关系

$$E^{2}=p^{2}c^{2}+m^{2}c^{4}$$

的算符起源。

在 Bloch 球描述中，内部态对应 ($S^{2}$) 上的单位矢量，Hamilton ($H_{\mathrm{eff}}(p)$) 对应 Bloch 球上的角速度向量

$$\boldsymbol\Omega(p)=\frac{2}{\hbar}\bigl(m c^{2},,0,,c p\bigr),$$

其模长

$$|\boldsymbol\Omega(p)|=\frac{2E(p)}{\hbar}$$

给出内部射影空间中的总几何速度。由于 ($\sigma_{x}$) 与 ($\sigma_{z}$) 在 Lie 代数中对易子与反对易子结构的正交性，可将 ($H_{T}$) 与 ($H_{M}$) 对应的"速度分量"理解为两条互相正交的方向，其平方和给出总速率的平方。

这一结构是后文信息速率守恒定理的代数与几何基础。

---

## Main Results (Theorems and alignments)

在上述模型框架下，本文给出以下主要结果。

### 定理 1（信息速率守恒定理）

在任意满足局域幺正性和平移不变性且在长波极限中涌现一维 Dirac 型有效 Hamilton 的离散量子游走/QCA 系统中，对任意正能量单粒子本征模，记外部群速度为

$$v_{\mathrm{ext}}(p)=\frac{dE}{dp},$$

在内部射影 Hilbert 空间中定义内部演化速度

$$v_{\mathrm{int}}(p):=c,\frac{m c^{2}}{E(p)},$$

则必有

$$v_{\mathrm{ext}}^{2}(p)+v_{\mathrm{int}}^{2}(p)=c^{2},$$

其中 ($c$) 为 QCA 的最大因果传播速率。

该定理由 Hamilton 的反对易分解与 Fubini–Study 度规下生成元的正交性共同保证，是局域幺正与 Dirac 结构的必然结果，而非附加假设。

### 推论 1（狭义相对论的涌现）

以内部演化参数 ($\tau$) 定义固有时间，使

$$v_{\mathrm{int}},dt=c,d\tau。$$

由定理 1 得到

$$\Bigl(\frac{d\tau}{dt}\Bigr)^{2}=1-\frac{v^{2}}{c^{2}},\qquad v:=v_{\mathrm{ext}}。$$

定义四速度

$$u^{\mu}=\frac{dx^{\mu}}{d\tau}=\gamma(v),(c,\mathbf v),\qquad \gamma(v)=\frac{1}{\sqrt{1-v^{2}/c^{2}}},$$

则在 Minkowski 度规 ($\eta_{\mu\nu}=\mathrm{diag}(-1,1,1,1)$) 下有规范化条件

$$u^{\mu}u_{\mu}=-c^{2},$$

相应线元

$$ds^{2}=-c^{2}d\tau^{2}=-c^{2}dt^{2}+d\mathbf x^{2}。$$

狭义相对论的时间膨胀与速度规范化由信息速率守恒直接涌现。

### 定理 2（质量作为内部频率）

在内部 Hilbert 空间 ($\mathcal H_{\mathrm{int}}$) 上引入 Hamilton

$$\mathrm i\hbar,\partial_{\tau}|\psi_{\mathrm{int}}(\tau)\rangle=H_{\mathrm{int}}|\psi_{\mathrm{int}}(\tau)\rangle。$$

若存在定态 ($|\psi_{\mathrm{int}}\rangle$) 满足

$$H_{\mathrm{int}}|\psi_{\mathrm{int}}\rangle=E_{0}|\psi_{\mathrm{int}}\rangle,$$

内部态演化为

$$|\psi_{\mathrm{int}}(\tau)\rangle=\mathrm e^{-\mathrm i E_{0}\tau/\hbar}|\psi_{\mathrm{int}}\rangle,$$

定义内部频率

$$\omega_{\mathrm{int}}=\frac{E_{0}}{\hbar}。$$

将 ($E_{0}$) 识别为静止能量 ($m c^{2}$)，得到

$$m=\frac{\hbar\omega_{\mathrm{int}}}{c^{2}}。$$

质量由内部频率给出，表达为内部自指结构占用光程配额的程度。

### 命题 1（Zitterbewegung 频率与内部频率）

在一维 Dirac 型 QCA 的连续极限中，有效 Hamilton

$$H_{\mathrm{eff}}(k)=c\hbar k\sigma_{z}+m c^{2}\sigma_{x},$$

本征值

$$E_{\pm}(k)=\pm\sqrt{(c\hbar k)^{2}+m^{2}c^{4}}。$$

Heisenberg 图像下位置算符 ($X(t)$) 的演化包含频率

$$\omega_{\mathrm{ZB}}(k)=\frac{2E_{+}(k)}{\hbar}$$

的快速振荡项。静止极限 ($k=0$) 下，($E_{+}(0)=m c^{2}$)，故

$$\omega_{\mathrm{ZB}}(0)=\frac{2m c^{2}}{\hbar}=2\omega_{\mathrm{int}}。$$

Zitterbewegung 频率为内部频率的两倍。

### 定理 3（拓扑稳定性与非零信息相角）

考虑一维平移不变 QCA，其单步幺正算符 ($U(k)\in\mathrm U(N)$) 在动量空间上定义闭合曲线。绕数

$$\mathcal W[U]=\frac{1}{2\pi\mathrm i}\int_{-\pi/a}^{\pi/a}\partial_{k}\log\det U(k),dk\in\mathbb Z$$

在有限深度局域幺正变换下保持不变。

若 ($\mathcal W[U]\neq 0$)，则存在携带非零拓扑荷的局域激发，任何有限深度局域幺正均无法将其连续变形为拓扑平凡真空。为维持拓扑相位绕行，此类激发的内部 Hamilton 必须具有非零本征频率 ($\omega_{\mathrm{int}}>0$)，从而 ($v_{\mathrm{int}}>0$)，信息相角 ($\theta=\arctan(v_{\mathrm{int}}/v_{\mathrm{ext}})$) 非零。质量的存在因此由 QCA 的拓扑结构稳定。

### 定理 4（光学度规与弱场引力）

在多体情形下，引入粗粒化的局域信息处理密度 ($\rho_{\mathrm{info}}(x)$)，代表单位时间单位体积内内部 Hilbert 空间在 Fubini–Study 度量下走过的平均路径长度。允许在坐标系 ($(t,x^{i})$) 下对时间与空间刻度进行局域重标度，引入尺度因子 ($\eta(x)$) 使线元可写为

$$ds^{2}=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j},$$

其中 ($\gamma_{ij}(x)$) 为三维空间度规。定义坐标光速

$$c_{\mathrm{eff}}(x):=\Bigl|\frac{d\mathbf x}{dt}\Bigr|=\eta^{2}(x)c,$$

折射率

$$n(x):=\frac{c}{c_{\mathrm{eff}}(x)}=\eta^{-2}(x)。$$

在静态、球对称、弱场极限

$$\eta(x)=1+\epsilon(x),\qquad |\epsilon(x)|\ll 1,$$

取 ($\epsilon(r)=\phi(r)/c^{2}$)，($\phi(r)=-GM/r$) 为牛顿势，得到

$$g_{00}\simeq-(1+2\phi/c^{2})c^{2},\qquad g_{ij}\simeq(1-2\phi/c^{2})\delta_{ij},$$

与 Schwarzschild 度规在各向同性坐标下的一阶展开一致。折射率

$$n(r)\simeq 1-\frac{2\phi(r)}{c^{2}}\simeq 1+\frac{2GM}{c^{2}r}>1,$$

在基于 Gauss–Bonnet 定理的引力透镜理论中给出光线偏折角

$$\Delta\theta=\frac{4GM}{c^{2}b},$$

其中 ($b$) 为冲量距，与广义相对论标准结果一致。

### 定理 5（信息–引力变分原理）

考虑作用量

$$S_{\mathrm{tot}}[g,\rho_{\mathrm{info}}]=\frac{1}{16\pi G}\int_{M}\sqrt{-g},R[g],d^{4}x+\int_{M}\sqrt{-g},\mathcal L_{\mathrm{info}}[\rho_{\mathrm{info}},g],d^{4}x。$$

对 ($g^{\mu\nu}$) 变分（忽略边界项）得到

$$R_{\mu\nu}-\tfrac12 R g_{\mu\nu}=8\pi G,T^{(\mathrm{info})}*{\mu\nu},$$

其中

$$T^{(\mathrm{info})}*{\mu\nu}:=-\frac{2}{\sqrt{-g}},\frac{\delta(\sqrt{-g},\mathcal L_{\mathrm{info}})}{\delta g^{\mu\nu}}。$$

若在低能极限下 ($\mathcal L_{\mathrm{info}}$) 的选择使 ($T^{(\mathrm{info})}_{\mu\nu}$) 与标准物质的应力–能量张量一致，则该方程形式上等价于爱因斯坦场方程。

### 定理 6（信息质量与渐近静止）

对具有内部模型与自指机制的系统，引入信息质量

$$M_{I}(\sigma)=f\bigl(K(\sigma),D(\sigma),S_{\mathrm{ent}}(\sigma)\bigr),$$

其中 ($K$) 为 Kolmogorov 复杂度，($D$) 为逻辑深度，($S_{\mathrm{ent}}$) 为内部纠缠熵，($f$) 为单调增函数。假设维持给定 ($M_{I}$) 需要的平均内部信息速率 ($v_{\mathrm{int}}(M_{I})$) 单调递增且有界于 ($c$)。由定理 1 得

$$v_{\mathrm{ext}}^{2}(M_{I})=c^{2}-v_{\mathrm{int}}^{2}(M_{I})。$$

若

$$\lim_{M_{I}\to\infty}v_{\mathrm{int}}(M_{I})=c,$$

则

$$\lim_{M_{I}\to\infty}v_{\mathrm{ext}}(M_{I})=0,$$

高信息质量主体在外部几何中趋于渐近静止。

### 命题 2（维持信息质量的 Landauer 代价）

设系统以速率 ($R_{\mathrm{upd}}$) 更新内部模型，每次更新平均擦除 ($\Delta I$) 比特旧信息，则单位时间擦除信息量

$$\dot I_{\mathrm{erase}}=R_{\mathrm{upd}}\Delta I。$$

在温度 ($T$) 的热浴中，根据 Landauer 原理，擦除一比特信息至少耗散热量 ($k_{B}T\ln 2$)，最小功耗为

$$P_{\min}=k_{B}T\ln 2,\dot I_{\mathrm{erase}}=k_{B}T\ln 2,R_{\mathrm{upd}}\Delta I。$$

高信息质量系统的持续存在必然伴随非零最小功耗与熵流输出。

---

## Proofs

本节对主要定理给出证明或证明思路。详细计算与模型细节置于附录。

### 定理 1 的证明（信息速率守恒定理）

考虑长波极限的一维 Dirac 型 QCA，其有效 Hamilton

$$H(p)=H_{T}(p)+H_{M},\qquad H_{T}(p)=c,p,\sigma_{z},\qquad H_{M}=m c^{2}\sigma_{x},$$

其中 ($p$) 为动量。Pauli 矩阵满足

$$\sigma_{x}^{2}=\sigma_{z}^{2}=\mathbb I,\qquad {\sigma_{z},\sigma_{x}}=0。$$

因此

$$H^{2}(p)=H_{T}^{2}(p)+H_{M}^{2}=(c^{2}p^{2}+m^{2}c^{4})\mathbb I。$$

对正能量本征模 ($|\psi_{p}\rangle$) 有

$$H(p)|\psi_{p}\rangle=E(p)|\psi_{p}\rangle,\qquad E^{2}(p)=c^{2}p^{2}+m^{2}c^{4}。$$

外部群速度定义为

$$v_{\mathrm{ext}}(p)=\frac{dE}{dp}。$$

由 ($E^{2}=c^{2}p^{2}+m^{2}c^{4}$) 得

$$2E,\frac{dE}{dp}=2c^{2}p,$$

故

$$v_{\mathrm{ext}}(p)=\frac{dE}{dp}=\frac{c^{2}p}{E(p)}。$$

内部部分由 ($H_{M}=m c^{2}\sigma_{x}$) 给出，其对应的"能量份额"相对于总能量 ($E(p)$) 的比例为

$$\frac{E_{M}}{E}=\frac{m c^{2}}{E(p)}。$$

定义内部速度为

$$v_{\mathrm{int}}(p):=c,\frac{E_{M}}{E}=c,\frac{m c^{2}}{E(p)}。$$

这一定义可理解为：在总信息速率预算 ($c$) 中，内部演化所占的分量按"质量能量份额"加权。

由此有

$$\frac{v_{\mathrm{ext}}^{2}(p)}{c^{2}}=\frac{c^{4}p^{2}}{c^{2}E^{2}(p)}=\frac{c^{2}p^{2}}{E^{2}(p)},\qquad \frac{v_{\mathrm{int}}^{2}(p)}{c^{2}}=\frac{m^{2}c^{4}}{E^{2}(p)}。$$

相加得到

$$\frac{v_{\mathrm{ext}}^{2}(p)}{c^{2}}+\frac{v_{\mathrm{int}}^{2}(p)}{c^{2}}=\frac{c^{2}p^{2}+m^{2}c^{4}}{E^{2}(p)}=1,$$

即

$$v_{\mathrm{ext}}^{2}(p)+v_{\mathrm{int}}^{2}(p)=c^{2}。$$

代数上，这是 Hamilton 分解为两项反对易算符导致能量平方呈勾股形式的直接结果。几何上，在内部两维 Hilbert 空间上，Hamilton 可写为

$$H(p)=\boldsymbol n(p)\cdot\boldsymbol\sigma,\qquad \boldsymbol n(p)=(m c^{2},0,c p),$$

其对应 Bloch 球上的角速度向量

$$\boldsymbol\Omega(p)=\frac{2}{\hbar}\boldsymbol n(p)=\frac{2}{\hbar}\bigl(m c^{2},0,c p\bigr)。$$

Fubini–Study 度规下的总速度与 ($|\boldsymbol\Omega(p)|$) 成正比，而 ($\boldsymbol n(p)$) 的两个正交分量分别对应内部与外部生成元。由于 ($\sigma_{x}$) 与 ($\sigma_{z}$) 在 Lie 代数中正交，($\boldsymbol\Omega(p)$) 的平方模即为两分量平方和，从而内部与外部信息速率的平方和固定为常数 ($c^{2}$)。

对更一般的局域幺正、平移不变 QCA，只要长波单粒子激发在适当基底与重标后可写成 Dirac 型 ($2\times 2$) 有效 Hamilton，以上证明立即适用。因此，信息速率守恒定理在这一类 QCA 中是直接由幺正性与 Hilbert 空间几何导出的结果。

### 推论 1 与定理 2 的证明

由定理 1，取

$$v_{\mathrm{int}},dt=c,d\tau$$

定义固有时间。代入

$$v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}$$

得

$$v^{2}+c^{2}\Bigl(\frac{d\tau}{dt}\Bigr)^{2}=c^{2},\qquad v:=v_{\mathrm{ext}},$$

即

$$\Bigl(\frac{d\tau}{dt}\Bigr)^{2}=1-\frac{v^{2}}{c^{2}}。$$

取正根，可得时间膨胀关系

$$\frac{d\tau}{dt}=\sqrt{1-\frac{v^{2}}{c^{2}}}。$$

定义洛伦兹因子

$$\gamma(v)=\frac{dt}{d\tau}=\frac{1}{\sqrt{1-v^{2}/c^{2}}},$$

四速度

$$u^{\mu}=\frac{dx^{\mu}}{d\tau}=\gamma(v),(c,\mathbf v)。$$

在 Minkowski 度规下

$$u^{\mu}u_{\mu}=-\gamma^{2}c^{2}+\gamma^{2}v^{2}=-\gamma^{2}c^{2}\Bigl(1-\frac{v^{2}}{c^{2}}\Bigr)=-c^{2},$$

从而得到规范化条件以及线元素

$$ds^{2}=-c^{2}d\tau^{2}=-c^{2}dt^{2}+d\mathbf x^{2}。$$

狭义相对论结构由此涌现。

定理 2 的证明直接来自内部演化方程

$$\mathrm i\hbar,\partial_{\tau}|\psi_{\mathrm{int}}(\tau)\rangle=H_{\mathrm{int}}|\psi_{\mathrm{int}}(\tau)\rangle。$$

对本征态

$$H_{\mathrm{int}}|\psi_{\mathrm{int}}\rangle=E_{0}|\psi_{\mathrm{int}}\rangle$$

有

$$|\psi_{\mathrm{int}}(\tau)\rangle=\mathrm e^{-\mathrm i E_{0}\tau/\hbar}|\psi_{\mathrm{int}}\rangle,$$

定义 ($\omega_{\mathrm{int}}=E_{0}/\hbar$)。取 ($E_{0}=m c^{2}$) 即得

$$m=\frac{\hbar\omega_{\mathrm{int}}}{c^{2}}。$$

### 命题 1 的证明概要

在附录 C 中对 Dirac Hamilton 的标准 Zitterbewegung 推导进行回顾，这里仅给出关键步骤。取一维 Dirac Hamilton

$$H=c\alpha p+\beta m c^{2},$$

在表示 ($\alpha=\sigma_{z}$)、($\beta=\sigma_{x}$) 下，有

$$H=c\sigma_{z}p+\sigma_{x}m c^{2}。$$

Heisenberg 图像中位置算符演化满足

$$\frac{dX}{dt}=\frac{\mathrm i}{\hbar}[H,X]=c\alpha,\qquad \frac{d\alpha}{dt}=\frac{\mathrm i}{\hbar}[H,\alpha]。$$

解得

$$X(t)=X(0)+c^{2}H^{-1}Pt+\frac{\mathrm i\hbar c}{2}H^{-1}\bigl(\mathrm e^{-2\mathrm i H t/\hbar}-1\bigr)\bigl(\alpha(0)-cH^{-1}P\bigr),$$

第二项为匀速运动，第三项为频率 ($2E/\hbar$) 的振荡项，($E=\sqrt{(cP)^{2}+m^{2}c^{4}}$)。静止极限 ($P=0$) 下 ($E=m c^{2}$)，振荡频率

$$\omega_{\mathrm{ZB}}(0)=\frac{2m c^{2}}{\hbar}。$$

结合定理 2 中 ($\omega_{\mathrm{int}}=m c^{2}/\hbar$)，得到

$$\omega_{\mathrm{ZB}}(0)=2\omega_{\mathrm{int}}。$$

### 定理 3 的证明思路

平移不变 QCA 的单步幺正可写为

$$U=\int^{\oplus}U(k),dk,$$

其拓扑绕数

$$\mathcal W[U]=\frac{1}{2\pi\mathrm i}\int\partial_{k}\log\det U(k),dk$$

是从 Brillouin 区到 ($\mathrm U(N)$) 的映射的同伦不变量，在任意有限深度局域幺正变换下保持不变。若 ($\mathcal W[U]\neq 0$)，则对岸存在以本征态形式体现的非平凡拓扑相位绕行，无法通过局域幺正"平滑抹去"。为实现该绕行，内部 Hamilton 必须具有非零本征频率，从而 ($v_{\mathrm{int}}>0$)，信息相角 ($\theta>0$)。具体数学细节可通过 QCA index 理论与 ($K$) 理论严谨化，见附录 A 与相关文献。

### 定理 4 与定理 5 的证明思路

定理 4 起点为光学度规

$$ds^{2}=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j}。$$

在各向同性、静态、球对称情况下，取 ($\gamma_{ij}=\delta_{ij}$)，弱场展开 ($\eta(x)=1+\epsilon(x)$) 得

$$g_{00}\simeq-(1+2\epsilon)c^{2},\qquad g_{ij}\simeq(1-2\epsilon)\delta_{ij}。$$

比较 Schwarzschild 度规在各向同性坐标下的弱场展开，可选取 ($\epsilon(r)=\phi(r)/c^{2}$)，其中 ($\phi(r)=-GM/r$)。折射率

$$n(r)=\eta^{-2}(r)\simeq 1-\frac{2\phi(r)}{c^{2}}\simeq 1+\frac{2GM}{c^{2}r}>1,$$

由此得到 ($c_{\mathrm{eff}}(r)=c/n(r)<c$)。在 Gibbons–Werner 等提出的光学几何–Gauss–Bonnet 方法中，可将光线视为二维 Riemann 曲面上的测地线，通过高斯曲率积分得到偏折角

$$\Delta\theta=\frac{4GM}{c^{2}b}。$$

定理 5 使用 Einstein–Hilbert 项

$$\int\sqrt{-g},R,d^{4}x$$

的标准变分公式以及

$$\delta(\sqrt{-g},\mathcal L_{\mathrm{info}})=\tfrac12\sqrt{-g},T^{(\mathrm{info})}*{\mu\nu}\delta g^{\mu\nu},$$

可得

$$\delta S*{\mathrm{tot}}=\frac{1}{16\pi G}\int\sqrt{-g},\bigl(R_{\mu\nu}-\tfrac12 R g_{\mu\nu}\bigr)\delta g^{\mu\nu},d^{4}x+\frac12\int\sqrt{-g},T^{(\mathrm{info})}*{\mu\nu}\delta g^{\mu\nu},d^{4}x。$$

令 ($\delta S*{\mathrm{tot}}=0$) 对任意紧支撑 ($\delta g^{\mu\nu}$) 成立，即得

$$R_{\mu\nu}-\tfrac12 R g_{\mu\nu}=8\pi G,T^{(\mathrm{info})}_{\mu\nu}。$$

### 定理 6 与命题 2 的证明思路

定理 6 直接来自定理 1：假设 ($v_{\mathrm{int}}(M_{I})$) 随 ($M_{I}$) 单调增加并趋向 ($c$)，则

$$v_{\mathrm{ext}}^{2}(M_{I})=c^{2}-v_{\mathrm{int}}^{2}(M_{I})$$

在 ($M_{I}\to\infty$) 时趋向 0，因此高信息质量主体在几何上表现为越来越"静止"。

命题 2 则是 Landauer 原理的直接应用。擦除一比特信息最少耗散 ($k_{B}T\ln 2$) 的热量，若单位时间擦除

$$\dot I_{\mathrm{erase}}=R_{\mathrm{upd}}\Delta I$$

比特，则最小耗散功率

$$P_{\min}=k_{B}T\ln 2,\dot I_{\mathrm{erase}}=k_{B}T\ln 2,R_{\mathrm{upd}}\Delta I。$$

这给出了维持固定信息质量的不可约功耗下界。

---

## Model Apply

### 自由粒子与狭义相对论极限

对单粒子 Dirac 型 QCA，长波极限下的色散关系

$$E^{2}=p^{2}c^{2}+m^{2}c^{4}$$

与狭义相对论一致。由推论 1 与定理 2 可将四动量写为

$$p^{\mu}=m u^{\mu},\qquad p^{\mu}p_{\mu}=-m^{2}c^{2}。$$

无质量模式对应内部频率可以为零的拓扑平凡 QCA，本征模满足 ($v_{\mathrm{int}}=0$)、($v_{\mathrm{ext}}=c$)，信息速率预算全部用于外部传播，与光子等无静止质量激发的性质一致。

### 多体体系与天体物理

在恒星、星系与星系团等宏观体系中，能量密度、粒子数密度与信息处理密度在统计意义上高度相关：高能量密度通常意味着大量自由度参与高频相互作用，从而 ($\rho_{\mathrm{info}}(x)$) 较大、($\eta(x)$) 较小、折射率 ($n(x)$) 较大、几何更弯曲。在这一尺度上，($\rho_{\mathrm{info}}(x)$) 与应力–能量张量 ($T_{\mu\nu}$) 的差异可视为重整化与粗粒化效应，在观测上难以区分，因此本框架在经典天体物理检验上的预言与广义相对论基本一致。

具有区分度的检验应集中在信息结构可变而总能量近乎不变的体系，例如具有不同纠缠结构的量子介质或拓扑相。此时，本框架预言几何与有效光速对纠缠结构敏感，而标准广义相对论预言仅对能量–动量分布敏感，从而提供可观测差异。

### 黑洞熵与信息速率饱和

在黑洞视界附近，Bekenstein–Hawking 熵与视界面积成正比，暗示单位面积可容纳的信息自由度数目存在普适上界。本框架下，视界可理解为 ($\rho_{\mathrm{info}}(x)$) 达到饱和值的区域：此处 ($\eta(x)$) 接近某一极限，导致外部传播受强烈抑制，内部自指结构占用几乎全部光程配额。黑洞熵可解释为视界上"可承载内部自指结构的最大信息速率积分"。

要将

$$S_{\mathrm{BH}}=\frac{A}{4G}$$

从 QCA 信息参数严格推导，需要结合具体 QCA 模型与重整化分析，在附录与后续工作中可进一步展开。

### 宇宙学与有效宇宙学常数

在宇宙学尺度上，可定义粗粒化的宇宙学平均信息处理密度 ($\rho_{\mathrm{info}}^{\mathrm{cosmo}}(t)$)。其平滑分量可通过 ($\mathcal L_{\mathrm{info}}$) 吸收到有效"信息真空能"项中，在 Friedmann 方程中扮演类似宇宙学常数或暗能量的角色；若 ($\rho_{\mathrm{info}}^{\mathrm{cosmo}}(t)$) 随时间缓慢变化，则可产生类似动力学暗能量的观测特征。这一方向需要在具体宇宙学背景下引入 QCA 模型、重整化与观测约束。

---

## Engineering Proposals

### 超导微波腔中的"信息折射率"实验

考虑高品质因数的超导微波腔或电路 QED 平台，其体积 ($V$) 固定，内部存在若干可控电磁场模。通过外部驱动与反馈，可在腔体内制备多种量子态，并通过量子层析表征其纠缠结构。设通过反馈控制，将腔体总能量 ($E_{\mathrm{tot}}$) 固定在某一值。

设计两类内部态：

1. 态 A：在给定 ($E_{\mathrm{tot}}$) 下，各模近似非纠缠或弱纠缠，拓扑平凡，对应低信息结构态；

2. 态 B：在同一 ($E_{\mathrm{tot}}$) 下，制备高度纠缠、可能具有非平庸拓扑序的多模量子态，对应高信息结构态。

在标准广义相对论中，引力源由应力–能量张量 ($T_{\mu\nu}$) 决定，而此处 Maxwell 场的 ($T_{\mu\nu}$) 在宏观上只依赖能量密度与压力，纠缠结构不进入源项。因此，只要 ($E_{\mathrm{tot}}$) 与空间分布相同，态 A 与态 B 对外部几何的影响应相同，通过腔附近的 Shapiro 延迟也应相同。

在本文框架中，高纠缠或拓扑有序态意味着更高的 ($\rho_{\mathrm{info}}(x)$)，即单位时间内内部 Hilbert 空间中发生更多"路径长度"，即使总能量不变。这导致 ($\eta(x)$) 与折射率 ($n(x)=\eta^{-2}(x)$) 的变化。若在腔体附近布置高灵敏干涉仪，使探测光束多次穿越该区域，则在态 A 与态 B 切换时，将在干涉条纹中测量到差分相位延迟

$$\Delta\phi_{\mathrm{info}}\sim\frac{\omega}{c}\int_{\mathrm{path}}\Delta n(\mathbf x),d\ell,$$

其中 ($\omega$) 为光频，($\Delta n(\mathbf x)$) 为由信息结构差异引起的折射率变化。

标准广义相对论预言 ($\Delta\phi\approx 0$)；本文框架预言 ($\Delta\phi\neq 0$)。若在控制系统误差与噪声的前提下观测到稳定的差分相位延迟，将构成"信息引力"相对于"能量引力"的直接证据。

### 量子模拟平台中的 Dirac-QCA 信息速率测量

在离子阱、光学格点、光子线路等平台上，已实现离散时间量子行走与 Dirac 型 QCA，并观测到 Zitterbewegung 等相对论特征。通过调节模型参数可实现不同有效质量与拓扑结构；若进一步能够表征内部态演化速率（例如通过对自旋自由度的相干操控与层析），则可在实验上检验

$$v_{\mathrm{ext}}^{2}(k)+v_{\mathrm{int}}^{2}(k)\simeq c^{2}$$

是否近似成立，并观察 ($v_{\mathrm{int}}(k)$) 如何随质量与拓扑不变量变化。这将为"光程配额在内部与外部分配"的图像提供量子模拟支持。

---

## Discussion (risks, boundaries, past work)

已有 QCA 研究系统展示了从离散模型涌现自由量子场论与部分相互作用场论的机制，并发展了 QCA 的拓扑分类与 index 理论。本文在此基础上引入以 Hilbert 空间几何与局域幺正性为出发点的信息速率守恒定理，将 Minkowski 几何与狭义相对论视为信息速率约束的几何表达，将 Dirac-QCA 中的 Zitterbewegung 解释为内部频率结构在外部坐标上的显现。

光学度规与 Gauss–Bonnet 定理在引力透镜中的应用表明，引力弯曲光线与非均匀折射率介质中的几何光学之间存在对应关系。本文通过 ($\rho_{\mathrm{info}}(x)$) 给折射率 ($n(x)$) 赋予微观含义，将宏观光学度规与微观 QCA 信息处理联系起来。

信息视角的引力理论亦有其他方案，例如从局域热力学与 Clausius 关系推导爱因斯坦方程的工作，以及多种基于熵与纠缠的引力方案；Landauer 原理则从不可逆计算的角度提供信息–能量关系的普适下界。本文的特点在于：从离散 QCA 本体出发，以信息速率守恒为核心定理，通过 Hilbert 空间几何与拓扑结构导出连续几何与质量的诠释，并给出以 ($\rho_{\mathrm{info}}(x)$)、($\eta(x)$)、($n(x)$) 为核心的光学引力图像。

需要强调的边界包括：从具体 QCA 到连续流形与度规的粗粒化一般不唯一，($\rho_{\mathrm{info}}(x)$) 的定义需要避免对内部自由度选择的规范依赖；信息质量 ($M_{I}$) 的可计算性问题限制了其在具体系统中的定量应用；实验上实现"信息引力"检验的技术挑战显著。这些问题界定了本文框架的适用范围。

---

## Conclusion

在量子元胞自动机与有限信息本体论框架下，本文证明了一个信息速率守恒定理：在 Dirac 型 QCA 连续极限中，单粒子长波激发的外部群速度 ($v_{\mathrm{ext}}$) 与内部态演化速度 ($v_{\mathrm{int}}$) 必然满足 ($v_{\mathrm{ext}}^{2}+v_{\mathrm{int}}^{2}=c^{2}$)。这一关系源自 Hamilton 的反对易结构与 Hilbert 空间 Fubini–Study 几何下生成元的正交分解，是局域幺正与有限传播速率的必然结果，而非附加假设。

以内部演化参数定义固有时间，可从信息速率守恒定理直接导出狭义相对论的时间膨胀、四速度规范化与 Minkowski 线元；内部 Hamilton 的本征频率给出质量 ($m=\hbar\omega_{\mathrm{int}}/c^{2}$)，Zitterbewegung 频率与内部频率满足 ($\omega_{\mathrm{ZB}}=2\omega_{\mathrm{int}}$)，质量由拓扑不变量稳定。引入局域信息处理密度与光学度规，在弱场极限下恢复 Schwarzschild 度规的一阶展开与标准光线偏折；通过信息–引力变分原理得到形式上等价于爱因斯坦方程的几何–信息统一表达。信息质量与 Landauer 代价统一刻画了高复杂度能动系统的引力与耗散特性，高 ($M_{I}$) 主体在外部几何中趋于渐近静止，并必然伴随持续熵流输出。

未来工作包括：在具体 QCA 模型中构造显式的 ($\mathcal L_{\mathrm{info}}$)，并验证其与标准量子场论应力–能量张量的一致性；在黑洞与宇宙学背景下，将 ($\rho_{\mathrm{info}}$) 与面积熵、宇宙学常数与暗能量等问题联系起来；在人工量子系统中设计可行实验，直接测量有效光速或时钟频率随纠缠熵与信息密度的变化行为。若这些方向得到验证，信息速率守恒有望成为连接微观计算本体与宏观几何叙事的一条统一路径。

---

## Acknowledgements, Code Availability

本研究建立在量子元胞自动机、离散引力、引力透镜几何方法与信息热力学等领域的既有成果之上，尤其依赖于关于 QCA–量子场论连续极限、QCA 拓扑分类、基于 Gauss–Bonnet 的引力透镜方法以及 Landauer 原理的系统研究。

本文未使用数值模拟代码，所有推导均为解析形式。若未来在具体 QCA 模型与数值验证方面有进一步工作，相应代码将另行整理与公开。

---

## References

[1] T. Farrelly, "A Review of Quantum Cellular Automata", Quantum 4, 368 (2020).

[2] A. Bisio, G. M. D'Ariano, A. Tosini, "Dirac Quantum Cellular Automaton in One Dimension: Zitterbewegung and Scattering from Potential", Phys. Rev. A 88, 032301 (2013).

[3] G. W. Gibbons, M. C. Werner, "Applications of the Gauss–Bonnet Theorem to Gravitational Lensing", Class. Quantum Grav. 25, 235009 (2008).

[4] M. Halla, "Application of the Gauss–Bonnet Theorem to Lensing in Static Spherically Symmetric Spacetimes", Gen. Relativ. Gravit. 52, 95 (2020).

[5] R. Landauer, "Irreversibility and Heat Generation in the Computing Process", IBM J. Res. Dev. 5, 183–191 (1961).

[6] 其他关于 QCA 拓扑分类、量子模拟平台与光学度规方法的文献综述，可参见 [1–4] 及其所引参考文献。

---

# 附录 A：一维 Dirac-QCA 的连续极限与信息速率守恒

## A.1 模型定义

考虑一维格点 ($\Lambda=a\mathbb Z$)，每个格点 ($x$) 携带双组分自旋

$$\psi_{x}=\begin{pmatrix}\psi_{x,\mathrm L}\\\psi_{x,\mathrm R}\end{pmatrix}.$$

定义条件平移算符 ($S$) 为

$$(S\psi)*{x,\mathrm L}=\psi*{x+a,\mathrm L},\qquad (S\psi)*{x,\mathrm R}=\psi*{x-a,\mathrm R},$$

内部旋转

$$W(\theta)=\begin{pmatrix}\cos\theta & -\mathrm i\sin\theta\\-\mathrm i\sin\theta & \cos\theta\end{pmatrix}.$$

单步 QCA 演化为

$$\psi(t+\Delta t)=U(\theta)\psi(t),\qquad U(\theta):=W(\theta)S。$$

在动量表象中，定义

$$\psi_{k}=\sum_{x}\mathrm e^{-\mathrm i k x}\psi_{x},$$

有

$$S(k)=\mathrm e^{\mathrm i k a\sigma_{z}},\qquad U(\theta;k)=W(\theta)S(k).$$

## A.2 有效 Hamilton 与 Dirac 方程

取 ($a,\Delta t,\theta$) 同时趋小，定义有效 Hamilton

$$H_{\mathrm{eff}}(k)=\frac{\mathrm i\hbar}{\Delta t},\log U(\theta;k)。$$

对小参数展开得

$$\log U(\theta;k)\simeq\mathrm i k a\sigma_{z}-\mathrm i\theta\sigma_{x},$$

从而

$$H_{\mathrm{eff}}(k)\simeq\frac{\hbar}{\Delta t}(k a\sigma_{z}+\theta\sigma_{x})。$$

令

$$c=\frac{a}{\Delta t},\qquad m c^{2}=\frac{\hbar\theta}{\Delta t},$$

得到

$$H_{\mathrm{eff}}(k)\simeq c\hbar k\sigma_{z}+m c^{2}\sigma_{x},$$

其位置空间形式为一维 Dirac 方程

$$\mathrm i\hbar,\partial_{t}\psi(x,t)=\bigl(-\mathrm i\hbar c\sigma_{z}\partial_{x}+m c^{2}\sigma_{x}\bigr)\psi(x,t)。$$

色散关系为

$$E_{\pm}(k)=\pm\sqrt{(c\hbar k)^{2}+m^{2}c^{4}}。$$

群速度

$$v_{\mathrm{ext}}(k)=\frac{1}{\hbar}\frac{\partial E_{+}}{\partial k}=\frac{c^{2}k}{\sqrt{k^{2}+(m c/\hbar)^{2}}}<c。$$

## A.3 内部速度与信息速率守恒的显式实现

对固定 ($k$)，内部态为二维自旋空间的本征态 ($|u_{+}(k)\rangle$)，其内部相位以频率 ($E_{+}(k)/\hbar$) 演化。在 Bloch 球表象中，比特态对应单位矢量 ($\boldsymbol r\in S^{2}$)，Hamilton ($H_{\mathrm{eff}}(k)=\boldsymbol n(k)\cdot\boldsymbol\sigma$) 生成围绕 ($\boldsymbol n(k)$) 的匀速旋转，角速度大小

$$|\boldsymbol\Omega(k)|=\frac{2|\boldsymbol n(k)|}{\hbar}=\frac{2E_{+}(k)}{\hbar}。$$

Fubini–Study 度规在 ($\mathbb C P^{1}$) 上与 Bloch 球上的标准度规等价，因此内部几何速度与 ($|\boldsymbol\Omega(k)|$) 成正比。

在 Dirac 型 QCA 中

$$\boldsymbol n(k)=(m c^{2},0,c\hbar k)。$$

可写为

$$|\boldsymbol n(k)|^{2}=(m c^{2})^{2}+(c\hbar k)^{2}。$$

将总"角速度矢量"分解为

$$\boldsymbol\Omega(k)=\boldsymbol\Omega_{M}(k)+\boldsymbol\Omega_{T}(k),\qquad \boldsymbol\Omega_{M}(k)=\frac{2}{\hbar}(m c^{2},0,0),\qquad \boldsymbol\Omega_{T}(k)=\frac{2}{\hbar}(0,0,c\hbar k)。$$

两分量正交，($|\boldsymbol\Omega(k)|^{2}=|\boldsymbol\Omega_{M}(k)|^{2}+|\boldsymbol\Omega_{T}(k)|^{2}$)。

将内部速度 ($v_{\mathrm{int}}(k)$) 归一化为

$$\frac{v_{\mathrm{int}}(k)}{c}=\frac{|\boldsymbol\Omega_{M}(k)|}{|\boldsymbol\Omega(k)|}=\frac{m c^{2}}{E_{+}(k)}，$$

而外部速度 ($v_{\mathrm{ext}}(k)$) 由群速度给出

$$\frac{v_{\mathrm{ext}}(k)}{c}=\frac{c\hbar k}{E_{+}(k)}。$$

于是

$$\frac{v_{\mathrm{ext}}^{2}(k)}{c^{2}}+\frac{v_{\mathrm{int}}^{2}(k)}{c^{2}}=\frac{c^{2}\hbar^{2}k^{2}+m^{2}c^{4}}{E_{+}^{2}(k)}=1,$$

即

$$v_{\mathrm{ext}}^{2}(k)+v_{\mathrm{int}}^{2}(k)=c^{2}。$$

这在 Dirac-QCA 模型中显式实现了定理 1 所述的信息速率守恒。

---

# 附录 B：光学度规、局域体积守恒与光线偏折

## B.1 局域体积元与缩放因子约束

在度规

$$ds^{2}=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j}$$

下，四体积元

$$dV_{4}=\sqrt{-g},d^{4}x。$$

在各向同性假设下，可将三维空间度规写为

$$\gamma_{ij}dx^{i}dx^{j}=\Psi^{4}(x),d\mathbf x^{2},$$

此时

$$\sqrt{-g}\propto\eta(x),\eta^{-3}(x)\Psi^{6}(x)=\eta^{-2}(x)\Psi^{6}(x)。$$

局域 Hilbert 体积守恒可简化为"单位坐标体积对应的物理 Hilbert 体积不变"，用约束

$$\eta_{t}(x),\eta_{x}^{3}(x)=1$$

表达。在各向同性下取

$$\eta_{t}(x)=\eta(x),\qquad \eta_{x}(x)=\eta^{-1}(x),$$

得到光学度规形式

$$ds^{2}=-\eta^{2}(x)c^{2}dt^{2}+\eta^{-2}(x)\gamma_{ij}(x)dx^{i}dx^{j}。$$

## B.2 弱场展开与 Schwarzschild 度规

在静态、球对称情形下，Schwarzschild 度规在各向同性坐标 ($(t,r,\theta,\varphi)$) 中可写为

$$ds^{2}=-\Bigl[\frac{1-\frac{GM}{2c^{2}r}}{1+\frac{GM}{2c^{2}r}}\Bigr]^{2}c^{2}dt^{2}+\Bigl(1+\frac{GM}{2c^{2}r}\Bigr)^{4}(dr^{2}+r^{2}d\Omega^{2})。$$

弱场近似 ($\frac{GM}{c^{2}r}\ll 1$) 下展开得

$$g_{00}\simeq-(1-\frac{2GM}{c^{2}r})c^{2}=-(1+2\phi/c^{2})c^{2},$$

$$g_{ij}\simeq(1+\frac{2GM}{c^{2}r})\delta_{ij}=(1-2\phi/c^{2})\delta_{ij},$$

其中 ($\phi(r)=-GM/r$) 为牛顿势。

以光学度规为起点，取

$$\eta(r)=1+\frac{\phi(r)}{c^{2}},\qquad \gamma_{ij}=\delta_{ij},$$

展开得

$$g_{00}=-\eta^{2}c^{2}\simeq-(1+2\phi/c^{2})c^{2},$$

$$g_{ij}=\eta^{-2}\delta_{ij}\simeq(1-2\phi/c^{2})\delta_{ij},$$

与 Schwarzschild 度规弱场展开一致。

## B.3 折射率与光线偏折角

在光学度规下对零测地线 ($ds^{2}=0$) 有

$$\eta^{2}(r)c^{2}dt^{2}=\eta^{-2}(r),d\mathbf x^{2},$$

坐标光速

$$c_{\mathrm{eff}}(r)=\Bigl|\frac{d\mathbf x}{dt}\Bigr|=\eta^{2}(r)c。$$

折射率

$$n(r):=\frac{c}{c_{\mathrm{eff}}(r)}=\eta^{-2}(r)。$$

在弱场极限

$$\eta(r)=1+\frac{\phi(r)}{c^{2}},\qquad \Bigl|\frac{\phi(r)}{c^{2}}\Bigr|\ll 1,$$

一阶展开得

$$n(r)=\eta^{-2}(r)\simeq 1-\frac{2\phi(r)}{c^{2}}。$$

取 ($\phi(r)=-GM/r$) 得

$$n(r)\simeq 1+\frac{2GM}{c^{2}r}>1,\qquad c_{\mathrm{eff}}(r)=\frac{c}{n(r)}<c,$$

与弱场引力中光线减速的物理图像一致。

在 Gibbons–Werner 方法中，可将光学度规视为二维 Riemann 曲面，将光线轨迹视为该曲面上的测地线，通过 Gauss–Bonnet 定理计算偏折角。弱偏折极限下，得到

$$\Delta\theta\simeq\frac{4GM}{c^{2}b},$$

与爱因斯坦预测一致。若只修改 ($g_{00}$) 而保持空间度规平坦，对应折射率仅为

$$n(r)\simeq 1-\frac{\phi(r)}{c^{2}},$$

偏折角将只有上述值的一半，说明同时变形时间与空间刻度（即引入光学度规）对恢复正确偏折因子至关重要。

---

# 附录 C：Dirac 理论中 Zitterbewegung 与内部频率

## C.1 Dirac 方程与平面波解

考虑一维 Dirac 方程

$$\mathrm i\hbar,\partial_{t}\psi=(c\alpha p+\beta m c^{2})\psi,$$

取表示 ($\alpha=\sigma_{z}$)、($\beta=\sigma_{x}$)，($p=-\mathrm i\hbar,\partial_{x}$)。平面波解为

$$\psi_{k,\pm}(x,t)=u_{\pm}(k),\mathrm e^{\mathrm i(kx-\omega_{\pm}t)},$$

$$\omega_{\pm}=\pm\sqrt{(c k)^{2}+\frac{m^{2}c^{4}}{\hbar^{2}}}。$$

一般波包可写为

$$\psi(x,t)=\int\bigl(a_{+}(k)\psi_{k,+}(x,t)+a_{-}(k)\psi_{k,-}(x,t)\bigr),dk。$$

## C.2 Heisenberg 图像下的位置算符

在 Heisenberg 画幅中，位置算符随时间演化

$$X(t)=\mathrm e^{\mathrm i H t/\hbar}X(0)\mathrm e^{-\mathrm i H t/\hbar},\qquad H=c\alpha p+\beta m c^{2}。$$

Heisenberg 方程给出

$$\frac{dX}{dt}=\frac{\mathrm i}{\hbar}[H,X]=c\alpha,\qquad \frac{d\alpha}{dt}=\frac{\mathrm i}{\hbar}[H,\alpha]。$$

解出 ($\alpha(t)$) 并代回 ($X(t)$) 得

$$X(t)=X(0)+c^{2}H^{-1}Pt+\frac{\mathrm i\hbar c}{2}H^{-1}\bigl(\mathrm e^{-2\mathrm i H t/\hbar}-1\bigr)\bigl(\alpha(0)-cH^{-1}P\bigr),$$

其中第二项为匀速运动，第三项为频率 ($2E/\hbar$) 的快速振荡项，即 Zitterbewegung，($E=\sqrt{(cP)^{2}+m^{2}c^{4}}$) 为正能量分支。在静止极限 ($P=0$) 时 ($E=m c^{2}$)，振荡频率为

$$\omega_{\mathrm{ZB}}(0)=\frac{2m c^{2}}{\hbar}。$$

在本文框架中，内部频率定义为

$$\omega_{\mathrm{int}}=\frac{m c^{2}}{\hbar},$$

从而

$$\omega_{\mathrm{ZB}}(0)=2\omega_{\mathrm{int}}。$$

---

# 附录 D：信息质量、Landauer 原理与最小功耗

## D.1 信息擦除与最小耗散

设某系统内部状态为 ($\sigma$)，其信息质量 ($M_{I}(\sigma)$) 与内部模型规模及复杂度有关。为了保持模型的时效性，系统必须定期用新观测更新内部表示，这一过程必然涉及对部分旧信息的擦除。

假设系统以速率 ($R_{\mathrm{upd}}$) 进行模型更新，每次更新平均擦除 ($\Delta I$) 比特旧信息，则单位时间内擦除信息量为

$$\dot I_{\mathrm{erase}}=R_{\mathrm{upd}}\Delta I。$$

在温度为 ($T$) 的热浴中，根据 Landauer 原理，擦除一比特信息至少要将热量 ($k_{B}T\ln 2$) 散入环境；最小耗散功率为

$$P_{\min}=k_{B}T\ln 2,\dot I_{\mathrm{erase}}=k_{B}T\ln 2,R_{\mathrm{upd}}\Delta I。$$

这一结果独立于系统的具体物理实现，只依赖擦除信息的比特数与环境温度，是对任何实现高信息质量系统所需功耗的普适下界。

## D.2 高信息质量与高耗散

若信息质量 ($M_{I}(\sigma)$) 随内部模型规模、结构复杂度和更新频率增大而增大，则更大的 ($M_{I}$) 通常需要更大的 ($R_{\mathrm{upd}}$) 与 ($\Delta I$)，以持续剔除过时信息并引入新信息。因此，一般情形下

$$P_{\min}(M_{I})=k_{B}T\ln 2,R_{\mathrm{upd}}(M_{I}),\Delta I(M_{I})$$

将随 ($M_{I}$) 增大而增大。

结合本文的信息速率守恒定理，可以得到统一图景：

1. 为维持高 ($M_{I}$)，系统必须将大量光程配额用于内部演化（($v_{\mathrm{int}}$) 大），从而外部运动速度 ($v_{\mathrm{ext}}$) 受到限制，表现为渐近静止；

2. 同时，内部频繁更新与擦除导致持续的熵流向外界，系统成为显著热源，表现为强耗散特性；

3. 在宏观上，这两种效应往往出现在引力势阱较深的区域：恒星内部通过核反应维持高信息密度与复杂结构，同时向外发射巨量辐射；生命系统与神经系统通过代谢维持低熵结构，同时向环境输出热量。

因此，在信息速率守恒的视角下，质量、引力与复杂能动结构之间的关联可统一理解为：要在内部维持高度有序、拓扑稳定的结构，就必须持续消耗光程配额并向外输出熵与能量，而这一过程在几何上表现为曲率，在动力学上表现为引力。

