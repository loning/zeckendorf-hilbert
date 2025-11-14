# 边界即时钟:时间作为相位—谱移—模块流的统一翻译算子

---

## Abstract

以一般 $C^\ast$-代数与算子散射理论为背景,构造一种"时间＝边界翻译"的刻画框架。时间不被视为体域内预先给定的流逝参数,而被定义为由边界谱数据生成、在相位—谱移—模块流三重读数之间保持自洽的唯一翻译标度。具体而言,首先在满足 Birman–Kreĭn 条件的散射体系中,以总散射相位 $\Phi(\omega)=\arg\det S(\omega)$、谱移函数 $\xi(\omega)$、相对态密度 $\Delta\rho(\omega)$ 与 Wigner–Smith 算子 $Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega)$ 为核心,建立刻度同一式

$$
\frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{Tr}Q(\omega),
\qquad \varphi(\omega):=\tfrac12\Phi(\omega),
$$

并将其解释为"以边界相位梯度刻度时间"的谱论标尺。其次,对给定的边界可观测代数 $\mathcal A_{\partial}$ 与忠实态 $\omega$ 的 GNS 表象,引入 Tomita–Takesaki 模块算子 $\Delta$ 与模块流 $\sigma_t^\omega$,在一类"散射—KMS 一致"假设下证明:由 $S(\omega)$ 与 $Q(\omega)$ 反推的时间参数 $t$ 与模块时间参数在适当归一化下同一。最后提出"时间等价原理"与"刻度同一公理":任意体域—外域数据对的物理演化,可等价重写为边界生成元 $H_{\partial}$ 所生成的翻译 $U(t)=\mathrm e^{-itH_{\partial}}$,而 $t$ 由边界谱测度的读数函数 $\mathcal T$ 唯一确定。在自然的单调性与正则性假设下,证明满足这些公理的时间刻度在加法与正比例变换意义下是唯一的。由此,在纯算子—几何及散射信息层面上,时间被刻画为"相位—谱移—模块流三重读取自洽的边界翻译参数",为从边界信息重建时空与动力学提供了可检验的理论基础。

## Keywords

时间本质;散射相位;谱移函数;Wigner–Smith 算子;模块流;边界代数;KMS 态;时间等价原理

**MSC 2020**:81U40, 81Q10, 46L55, 58J40

---

## Introduction & Historical Context

经典力学将时间视为绝对均匀流逝的外在参数;广义相对论中,时间嵌入为带有因果锥结构的坐标函数;标准量子理论则多以内参—外参分裂的方式,将时间作为薛定谔方程的连续参数。相较之下,算子代数与量子统计力学的发展表明:在给定可观测代数 $\mathcal A$ 与态 $\omega$ 的前提下,可由 Tomita–Takesaki 模块理论构造一族内在的自同构群 $\sigma_t^\omega$,被自然解释为"模块时间"。这一结构在 KMS 条件与平衡态理论中扮演核心角色。

另一方面,在散射理论中,Wigner 与 Smith 提出的时间延迟观念将总散射相位随能量的导数解释为粒子在势场中经历的平均"驻留时间";这一观念在随机介质、混沌散射、电磁、声学等多类体系中被大量推广与验证。在严格的算子散射框架下,Birman–Kreĭn 公式用谱移函数 $\xi(\lambda)$ 将散射行列式与谱测度联系起来,给出

$$
\det S(\lambda) = \exp\bigl(-2\pi i\,\xi(\lambda)\bigr),
$$

而 Kreĭn 迹公式则将两算子间的谱移函数与测试函数差的迹联系在一起。这两条链路把"相位—谱移—相对态密度"统一为同一对象的不同侧面。

Connes 与 Rovelli 的"热时间假设"进一步提出:在一般协变的量子理论中,物理时间流不应由预设的外在参数给出,而应由系统所在的统计态与可观测代数共同确定,即时间流由态的模块自同构群实现。这使得"时间＝模块流"成为一种有力的候选答案。

上述三条线索分别回答"如何由散射相位读出时间""如何由谱移函数刻度态密度"与"如何由态与代数构造时间流"。本文的目标是:在单一的、几何上最少结构的框架内,将这三者统一起来,并给出严格的存在性与唯一性结论。核心思想是引入一个边界代数 $\mathcal A_{\partial}$ 作为"体内—体外"信息的接口,要求:

1. 所有可观测输出最终落在 $\mathcal A_{\partial}$ 上;
2. 在给定忠实态 $\omega$ 与散射数据 $S(\omega)$ 的条件下,存在唯一(至仿射)时间翻译群 $\alpha_t$ 使得

   * $\alpha_t$ 在 GNS 表象中由某个自伴算子 $H_{\partial}$ 生成;
   * $\alpha_t$ 与 $\sigma_t^\omega$ 一致;
   * $\alpha_t$ 下的时间标尺由刻度同一式
     $$
     \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{Tr}Q(\omega)
     $$
     归一化。

从这个角度看,时间不再是"体域内的流逝变量",而被刻画为"在边界谱数据与模块流之间实现对准的唯一翻译参数"。这种刻画与热时间假设保持精神上的连续性,但要求额外的可观测散射数据作为刻度锚点,使时间具有直接的实验读数。

历史上,谱移函数与 Birman–Kreĭn 公式在自伴算子扰动理论中得到系统发展,而 Wigner–Smith 延迟矩阵与其迹恒等式则广泛应用于量子与波动散射。Tomita–Takesaki 模块理论则成为算子代数与代数量子场论的基础工具,贯穿 KMS 条件、类型 III 因子结构以及几何—代数桥接。本文在这些成熟理论之上引入"边界即时钟"的统一视角,将它们组织为关于时间本质的一个可检主张:**时间是由边界相位—谱移—模块流共同校准的翻译算子**。

---

## Model & Assumptions

本节在尽量抽象的框架下给出模型结构与基本假设。目标是在不依赖具体时空几何的前提下,获得足以应用 Birman–Kreĭn 公式、谱移函数与模块理论的最小条件族。

### Boundary algebra and state

令 $\mathcal A_{\partial}$ 为可分 $C^\ast$-代数,代表"边界可观测"。选定一忠实态 $\omega:\mathcal A_{\partial}\to\mathbb C$,其 GNS 表象记为 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$,满足

$$
\omega(A)=\langle\Omega_\omega,\pi_\omega(A)\Omega_\omega\rangle,\qquad A\in\mathcal A_{\partial},
$$

$\Omega_\omega$ 为循环且分离向量。

假设存在一族强连续的 $C^\ast$-自同构

$$
\alpha_t:\mathcal A_{\partial}\to\mathcal A_{\partial},\qquad t\in\mathbb R,
$$

在 GNS 空间上由酉群 $U(t)$ 实现:

$$
\pi_\omega(\alpha_t(A))=U(t)\pi_\omega(A)U(t)^{-1},\qquad U(t)\Omega_\omega=\Omega_\omega.
$$

生成元 $H_{\partial}$ 为自伴算子,满足 $U(t)=\mathrm e^{-itH_{\partial}}$。

后文将 $(\mathcal A_{\partial},\omega,\alpha_t)$ 称为**边界动力系统**。

### Scattering system and Birman–Kreĭn setting

设 $H_0,H$ 为可分 Hilbert 空间 $\mathcal H$ 上的自伴算子,满足典型的散射假设:

1. $V:=H-H_0$ 为迹类扰动;
2. $H_0$ 的绝对连续谱在能量轴 $I\subset\mathbb R$ 上占优;
3. 存在波算子 $W_\pm$,使得
   $$
   W_\pm=\operatorname*{s-lim}_{t\to\pm\infty}\mathrm e^{itH}\mathrm e^{-itH_0}P_{\mathrm{ac}}(H_0),
   $$
   且是偏等距同构;
4. 散射算子 $S:=W_+^\ast W_-$ 为在 $P_{\mathrm{ac}}(H_0)\mathcal H$ 上的酉算子。

在能量表象下,$S$ 可分解为一族固定能量散射矩阵

$$
S(\lambda):\mathcal K(\lambda)\to\mathcal K(\lambda),\qquad \lambda\in I,
$$

其中 $\mathcal K(\lambda)$ 为每个能量上的通道空间。假定 $\lambda\mapsto S(\lambda)$ 在 $I$ 上足够可微。

在这些假设下,存在谱移函数 $\xi(\lambda)\in L^1_{\mathrm{loc}}(I)$,满足 Kreĭn 迹公式

$$
\operatorname{Tr}\bigl(f(H)-f(H_0)\bigr) = \int_I f'(\lambda)\,\xi(\lambda)\,\mathrm d\lambda
$$

对足够大的函数类成立。

同时,Birman–Kreĭn 公式给出散射行列式与谱移函数的关系:

$$
\det S(\lambda) = \exp\bigl(-2\pi i\,\xi(\lambda)\bigr) \quad\text{几乎处处于 }I.
$$

### Relative density of states, scattering phase and Wigner–Smith operator

定义总散射相位

$$
\Phi(\lambda):=\arg\det S(\lambda),\qquad \varphi(\lambda):=\tfrac12\Phi(\lambda).
$$

由 Birman–Kreĭn 公式可得

$$
\Phi(\lambda)\equiv -2\pi\xi(\lambda)\pmod{2\pi},
$$

因而在局部连续代表上

$$
\Phi'(\lambda)=-2\pi\xi'(\lambda).
$$

定义相对态密度(DOS 差)

$$
\Delta\rho(\lambda):=\rho(\lambda)-\rho_0(\lambda),
$$

其中 $\rho,\rho_0$ 为 $H,H_0$ 的态密度函数。在标准设置下,$\Delta\rho$ 与谱移函数导数满足

$$
\Delta\rho(\lambda)=-\xi'(\lambda) \quad\Rightarrow\quad \frac{1}{2\pi}\Phi'(\lambda)=\Delta\rho(\lambda),
$$

从而得到

$$
\frac{\varphi'(\lambda)}{\pi}=\Delta\rho(\lambda).
$$

另一方面,对每个能量,定义 Wigner–Smith 延迟算子

$$
Q(\lambda):=-iS(\lambda)^\dagger\partial_\lambda S(\lambda)
$$

在 $\mathcal K(\lambda)$ 上。$Q(\lambda)$ 为自伴算子,其迹

$$
\operatorname{Tr}Q(\lambda)
$$

在标准散射框架下等于总散射相位的导数:

$$
\Phi'(\lambda)=\operatorname{Tr}Q(\lambda).
$$

这一恒等式在量子散射、混沌散射、电磁与声学散射中被系统使用。

合并上述关系得到刻度同一式

$$
\frac{\varphi'(\lambda)}{\pi} = \Delta\rho(\lambda) = \frac{1}{2\pi}\operatorname{Tr}Q(\lambda).
$$

为避免符号混淆,后文将能量变量统一记为 $\omega$,刻度同一式写为

$$
\frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{Tr}Q(\omega),
$$

其中 $\rho_{\mathrm{rel}}(\omega):=\Delta\rho(\omega)$。

### Modular flow, KMS condition and thermal time

在 GNS 表象 $(\pi_\omega,\mathcal H_\omega,\Omega_\omega)$ 上,定义 Tomita 算子

$$
S_0\pi_\omega(A)\Omega_\omega=\pi_\omega(A)^\ast\Omega_\omega, \qquad A\in\mathcal A_{\partial},
$$

其闭包记为 $S$,极分解 $S=J\Delta^{1/2}$ 给出共轭反线性酉算子 $J$ 与模块算子 $\Delta$。Tomita–Takesaki 定理断言存在一族模块自同构

$$
\sigma_t^\omega(A):=\Delta^{it}A\Delta^{-it},\qquad t\in\mathbb R,
$$

构成 $\mathcal A_{\partial}$ 上的一参数自同构群,且 $\omega$ 对 $\sigma_t^\omega$ 满足 KMS 条件。

形式上可写模块生成元

$$
K_\omega:=-\log\Delta,\qquad \sigma_t^\omega(A) = \mathrm e^{itK_\omega}A\mathrm e^{-itK_\omega}.
$$

Connes–Rovelli 热时间框架提出:在一般协变场论中,物理时间流可由给定态与可观测代数决定,具体为模块流 $\sigma_t^\omega$。本文将这一思想限制在边界代数 $\mathcal A_{\partial}$ 上,并要求模块时间与由散射相位—谱移—Wigner–Smith 算子刻度得到的时间参数保持一致。

### Boundary compression and interior–exterior data

设 $\mathcal H_{\mathrm{in}},\mathcal H_{\mathrm{out}}$ 为体内与外域的 Hilbert 空间,$\mathcal H_\partial$ 为边界 Hilbert 空间。体内、外域可观测 $O_{\mathrm{in}},O_{\mathrm{out}}$ 通过压缩算子

$$
K_{\partial}^{\mathrm{in}}:\mathcal H_{\mathrm{in}}\to\mathcal H_\partial, \qquad K_{\partial}^{\mathrm{out}}:\mathcal H_{\mathrm{out}}\to\mathcal H_\partial
$$

投影到边界上,得到

$$
\widetilde O_{\mathrm{in}} := K_{\partial}^{\mathrm{in}}O_{\mathrm{in}}K_{\partial}^{\mathrm{in},\ast}, \qquad \widetilde O_{\mathrm{out}} := K_{\partial}^{\mathrm{out}}O_{\mathrm{out}}K_{\partial}^{\mathrm{out},\ast}.
$$

假定存在嵌入 $\iota:\mathcal H_\partial\hookrightarrow\mathcal H_\omega$ 与 $\mathcal A_{\partial}$ 的表示,使得 $\widetilde O_{\mathrm{in}},\widetilde O_{\mathrm{out}}$ 可视为 $\mathcal A_{\partial}$ 的元素或适当扩张中的可观测。时间将通过"使这些边界压缩对齐的翻译参数"来定义。

---

## Main Results (Theorems and alignments)

本节提出"时间等价原理""刻度同一公理"与"模块一致性公理",并给出统一时间刻度的存在与唯一性定理。

### Time equivalence principle and boundary generator

**公理 1(时间等价原理).**
考虑可实现的体内—外域数据对 $(D_{\mathrm{in}},D_{\mathrm{out}})$,视为 $\mathcal H_{\mathrm{in}},\mathcal H_{\mathrm{out}}$ 中的向量或态。存在边界 Hilbert 空间 $\mathcal H_\partial$、自伴算子 $H_{\partial}$ 与酉群

$$
U(t)=\mathrm e^{-itH_{\partial}},\qquad t\in\mathbb R,
$$

使得对任意可实现数据对,存在实数 $t$ 满足

$$
K_{\partial}^{\mathrm{out}}D_{\mathrm{out}} = U(t)\,K_{\partial}^{\mathrm{in}}D_{\mathrm{in}}.
$$

**公理 2(边界生成元公理).**
存在 $C^\ast$-代数 $\mathcal A_{\partial}$ 与忠实态 $\omega$,使上述 $U(t)$ 在 $\mathcal H_\omega$ 上实现边界动力学

$$
\alpha_t(A) = U(t)AU(t)^{-1},\qquad A\in\mathcal A_{\partial},
$$

且 $U(t)\Omega_\omega=\Omega_\omega$。

以下称 $(\mathcal A_{\partial},\omega,U(t))$ 为**边界即时钟**数据。

### Gauge fixing by phase–spectral-shift–WS trace

**公理 3(刻度同一公理).**
设散射系统满足前述 Birman–Kreĭn 与 Wigner–Smith 条件。在某个能窗 $I$ 内,存在相位 $\varphi(\omega)$、相对态密度 $\rho_{\mathrm{rel}}(\omega)$ 与 Wigner–Smith 算子 $Q(\omega)$,满足

$$
\frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{Tr}Q(\omega), \qquad \omega\in I.
$$

定义时间微元为

$$
\mathrm d t := \frac{1}{2\pi}\operatorname{Tr}Q(\omega)\,\mathrm d\omega.
$$

在给定参考点 $\omega_0,t_0$ 的情况下,时间刻度由

$$
t(\omega)-t_0 = \int_{\omega_0}^{\omega}\frac{1}{2\pi}\operatorname{Tr}Q(\tilde\omega)\,\mathrm d\tilde\omega = \int_{\omega_0}^{\omega}\frac{\varphi'(\tilde\omega)}{\pi}\,\mathrm d\tilde\omega = \int_{\omega_0}^{\omega}\rho_{\mathrm{rel}}(\tilde\omega)\,\mathrm d\tilde\omega
$$

确定。

刻度同一公理将频率轴上的散射谱结构转化为时间轴上的边界翻译刻度。

### Modular consistency and unified time flow

**公理 4(模块一致性公理).**
对边界动力系统 $(\mathcal A_{\partial},\omega,\alpha_t)$,假定存在常数 $c>0$ 使得对所有 $A\in\mathcal A_{\partial}$ 有

$$
\alpha_t(A)=\sigma_{ct}^\omega(A),
$$

其中 $\sigma_t^\omega$ 为 Tomita–Takesaki 模块流。将 $c$ 吸收到时间单位中,可无损失地改写为

$$
\alpha_t(A)=\sigma_t^\omega(A).
$$

由此,边界生成元 $H_{\partial}$ 与模块生成元 $K_\omega$ 仅差常数偏移:

$$
H_{\partial} = K_\omega+\lambda\mathbf 1,\qquad \lambda\in\mathbb R.
$$

### Existence theorem for boundary time scale

引入如下定义。

**定义 3.1(时间结构).**
称四元组

$$
\mathscr T = (\mathcal A_{\partial},\omega,\alpha_t,S(\omega))
$$

为一时间结构,若满足:

1. $\omega$ 为 $\mathcal A_{\partial}$ 的忠实正常态;
2. $\alpha_t$ 在 GNS 表象上由 $U(t)=\mathrm e^{-itH_{\partial}}$ 实现,$H_{\partial}$ 自伴;
3. 存在散射矩阵族 $S(\omega)$ 与对应的 $\varphi(\omega),Q(\omega),\rho_{\mathrm{rel}}(\omega)$,满足刻度同一式;
4. $\alpha_t=\sigma_t^\omega$ 作为自同构群相一致。

**定理 3.2(时间刻度的存在性).**
设 $\mathscr T$ 为时间结构,且假定在能窗 $I$ 内 $\rho_{\mathrm{rel}}(\omega)$ 为可积的连续函数且在某区间上非零。则存在局部双射

$$
\omega\longleftrightarrow t(\omega)
$$

由刻度同一公理给出,使得:

1. 对所有 $A\in\mathcal A_{\partial}$,有
   $$
   \alpha_{t(\omega)}(A) = \sigma_{t(\omega)}^\omega(A) = \Delta^{it(\omega)}A\Delta^{-it(\omega)};
   $$
2. 对散射侧,可将 $S(\omega)$ 视为 $S(t)$,且满足
   $$
   \frac{\mathrm d}{\mathrm d t}\varphi\bigl(\omega(t)\bigr) = \pi\,\rho_{\mathrm{rel}}\bigl(\omega(t)\bigr) = \tfrac12\operatorname{Tr}Q\bigl(\omega(t)\bigr),
   $$
   将相位梯度、相对态密度与 Wigner–Smith 迹改写为时间导数。

换言之,存在一时间参数 $t$ 同时参数化模块流与散射时间读数,使后者成为前者的"可观测刻度"。

### Uniqueness theorem up to affine transformations

**定理 3.3(刻度的加法—比例唯一性).**
在定理 3.2 的假设下,进一步假定:

1. $\rho_{\mathrm{rel}}(\omega)$ 在所考虑能窗内严格正或严格负;
2. 模块流 $\sigma_t^\omega$ 非平凡,即不存在非零时间 $t$ 使 $\sigma_t^\omega$ 为恒等。

若另有时间参数 $\tilde t$ 与映射 $\omega\mapsto\tilde t(\omega)$,使得:

1. $\alpha_{\tilde t}$ 亦实现为模块流:$\alpha_{\tilde t}=\sigma_{\tilde t}^\omega$;
2. 刻度同一式在 $\tilde t$ 下保持成立,即
   $$
   \frac{\mathrm d}{\mathrm d\tilde t}\varphi\bigl(\omega(\tilde t)\bigr) = \pi\,\rho_{\mathrm{rel}}\bigl(\omega(\tilde t)\bigr) = \tfrac12\operatorname{Tr}Q\bigl(\omega(\tilde t)\bigr),
   $$
   在同一能窗内成立。

则存在常数 $a>0$ 与 $b\in\mathbb R$,使得

$$
\tilde t = a t + b.
$$

也即,满足公理体系的时间刻度在仿射变换意义下唯一,时间反向 $(a<0)$ 被排除。

---

## Proofs

本节给出主定理的证明结构,并将技术性的算子散射与模块理论细节集中到附录中。

### Birman–Kreĭn identity and phase–spectral-shift relation

在前述假设下,谱移函数 $\xi(\lambda)$ 满足 Kreĭn 迹公式

$$
\operatorname{Tr}\bigl(f(H)-f(H_0)\bigr) = \int_{\mathbb R}f'(\lambda)\,\xi(\lambda)\,\mathrm d\lambda
$$

对一大类 $C^1$ 测试函数成立。

取 $f(\lambda)=\chi_{(-\infty,E]}(\lambda)$ 的平滑逼近,可得

$$
\xi(E) = \operatorname{Tr}\bigl(P_H((-\infty,E])-P_{H_0}((-\infty,E])\bigr),
$$

从而

$$
\xi'(\lambda) = -(\rho(\lambda)-\rho_0(\lambda)) = -\Delta\rho(\lambda)
$$

在分布意义成立。另一方面,Birman–Kreĭn 公式给出

$$
\det S(\lambda) = \exp\bigl(-2\pi i\,\xi(\lambda)\bigr),
$$

取连续支并对 $\lambda$ 求导,得到

$$
\Phi'(\lambda) = -2\pi\xi'(\lambda) = 2\pi\Delta\rho(\lambda),
$$

也即

$$
\frac{1}{2\pi}\Phi'(\lambda)=\Delta\rho(\lambda).
$$

以 $\varphi=\Phi/2$ 得

$$
\frac{\varphi'(\lambda)}{\pi}=\Delta\rho(\lambda).
$$

### Wigner–Smith trace and relative density of states

Wigner–Smith 延迟算子定义为

$$
Q(\lambda)=-iS(\lambda)^\dagger\partial_\lambda S(\lambda).
$$

在动量或通道基下,$Q(\lambda)$ 为有限或可数维矩阵,满足

$$
\operatorname{Tr}Q(\lambda) = -i\operatorname{Tr}\bigl(S(\lambda)^\dagger\partial_\lambda S(\lambda)\bigr).
$$

另一方面,$\det S(\lambda)$ 的对数导数满足

$$
\partial_\lambda\log\det S(\lambda) = \operatorname{Tr}\bigl(S(\lambda)^{-1}\partial_\lambda S(\lambda)\bigr) = \operatorname{Tr}\bigl(S(\lambda)^\dagger\partial_\lambda S(\lambda)\bigr),
$$

利用 $S(\lambda)$ 的酉性。取虚部得到

$$
\partial_\lambda\Phi(\lambda) = \operatorname{Im}\partial_\lambda\log\det S(\lambda) = \operatorname{Im}\operatorname{Tr}\bigl(S(\lambda)^\dagger\partial_\lambda S(\lambda)\bigr) = \operatorname{Tr}Q(\lambda),
$$

从而

$$
\Delta\rho(\lambda) = \frac{1}{2\pi}\operatorname{Tr}Q(\lambda).
$$

这在严格散射理论中可通过对 $H,H_0$ 的谱表示与 $S(\lambda)$ 的构造直接验证,在多物理背景的应用中亦被广泛使用。

### Proof of Theorem 3.2 (existence)

刻度同一式给出

$$
\frac{\mathrm d t}{\mathrm d\omega} = \frac{1}{2\pi}\operatorname{Tr}Q(\omega) = \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega).
$$

在能窗 $I$ 内,假设 $\rho_{\mathrm{rel}}(\omega)$ 连续且在某区间上非零,则 $t(\omega)$ 由

$$
t(\omega)-t_0=\int_{\omega_0}^{\omega}\rho_{\mathrm{rel}}(\tilde\omega)\,\mathrm d\tilde\omega
$$

给出 $C^1$ 函数。$\rho_{\mathrm{rel}}(\omega)\neq0$ 保证 $\mathrm d t/\mathrm d\omega$ 在局部不为零,从而反函数 $\omega(t)$ 存在且可微,局部给出频率—时间的双射。

在散射侧,将所有依赖于 $\omega$ 的对象写成依赖 $t$:

$$
S_t:=S\bigl(\omega(t)\bigr),\qquad Q_t:=Q\bigl(\omega(t)\bigr),\qquad \varphi_t:=\varphi\bigl(\omega(t)\bigr).
$$

链式法则与刻度同一式给出

$$
\frac{\mathrm d}{\mathrm d t}\varphi_t = \frac{\mathrm d\varphi}{\mathrm d\omega}\frac{\mathrm d\omega}{\mathrm d t} = \frac{\varphi'(\omega)}{\rho_{\mathrm{rel}}(\omega)} \cdot \frac{\varphi'(\omega)}{\pi} = \pi\rho_{\mathrm{rel}}(\omega) = \tfrac12\operatorname{Tr}Q_t,
$$

从而相位梯度与 Wigner–Smith 迹可以视为时间导数读数。

在边界代数侧,公理 4 保证存在模块算子 $\Delta$ 与自同构群 $\sigma_t^\omega$,使得

$$
\alpha_t=\sigma_t^\omega,\qquad \alpha_t(A)=\Delta^{it}A\Delta^{-it}.
$$

因此,$t$ 同时为模块流参数与散射刻度时间,得到统一时间流。定理 3.2 成立。

### Proof of Theorem 3.3 (uniqueness)

设 $\tilde t$ 为另一时间刻度,对应映射 $\omega\mapsto\tilde t(\omega)$,同样满足

$$
\frac{\mathrm d\tilde t}{\mathrm d\omega} = \rho_{\mathrm{rel}}(\omega),
$$

因为刻度同一式被假设在两种刻度下都成立。于是

$$
\frac{\mathrm d}{\mathrm d\omega}\bigl(\tilde t(\omega)-t(\omega)\bigr) = 0,
$$

故存在常数 $b$ 使 $\tilde t(\omega)=t(\omega)+b$。这说明在频率—时间变换层面,时间刻度至多有加法自由度。

另一方面,设存在非零常数 $a$ 与新参数 $\hat t=a t$,则

$$
\sigma_{\hat t}^\omega=\sigma_{a t}^\omega
$$

仍为模块流的重标度。Tomita–Takesaki 理论保证模块流对 $\omega$ 唯一,参数仅在比例意义下未定;若要求 $\alpha_t=\sigma_t^\omega$ 与 $\alpha_{\tilde t}=\sigma_{\tilde t}^\omega$ 同时成立,则必有 $\tilde t=a t+b$。

最后,若 $a<0$,则时间参数反向,意味着存在 $t\neq0$ 使 $\sigma_t^\omega$ 为非平凡自同构而 $\sigma_{-t}^\omega$ 的物理解释为"反向时间流"。在本文公理体系中,时间刻度的方向由 $\rho_{\mathrm{rel}}(\omega)$ 的符号固定;当其在能窗内符号固定时,时间反向对应 $\rho_{\mathrm{rel}}$ 符号翻转,与物理定义不相容,故排除 $a<0$,从而 $a>0$。定理 3.3 得证。

---

## Model Apply

本节给出若干具体模型,说明"边界即时钟"在不同物理场景中的实现。

### One-dimensional Schrödinger scattering

考虑一维 Schrödinger 算子

$$
H_0=-\frac{\mathrm d^2}{\mathrm d x^2},\qquad H=-\frac{\mathrm d^2}{\mathrm d x^2}+V(x)
$$

在 $\mathcal H=L^2(\mathbb R)$ 上,假设 $V\in L^1(\mathbb R,(1+|x|)\mathrm dx)$ 且实值。此时散射理论完全可解,存在反射、透射振幅 $r(k),t(k)$,能量 $E=k^2$,散射矩阵可写为

$$
S(k)= \begin{pmatrix} t(k) & r'(k)\\ r(k) & t(k) \end{pmatrix},\qquad |t(k)|^2+|r(k)|^2=1.
$$

总散射相位 $\Phi(k)$ 由 $\det S(k)=\mathrm e^{i\Phi(k)}$ 定义,Wigner–Smith 算子为

$$
Q(k)=-iS(k)^\dagger\frac{\mathrm d}{\mathrm d k}S(k),
$$

其迹

$$
\operatorname{Tr}Q(k)=\frac{\mathrm d\Phi(k)}{\mathrm d k}.
$$

谱移函数 $\xi(E)$ 与 $\Phi(E)$ 满足一维 Birman–Kreĭn 公式,态密度差 $\Delta\rho(E)$ 给出散射态与自由态之间的 DOS 改变。

选择边界 Hilbert 空间为动量空间通道

$$
\mathcal H_\partial\simeq L^2(\mathbb R_k)\oplus L^2(\mathbb R_k),
$$

边界代数 $\mathcal A_{\partial}$ 为其中的有界乘法算子与有限秩扰动的闭包,$\omega$ 为某一平衡态(例如 Fermi–Dirac 或 Boltzmann 权重)。在适当的热平衡极限下,$\mathcal A_{\partial}$ 与 $\omega$ 的模块流可与 Schrödinger 演化对应,从而模块时间与散射时间刻度在某能窗内实现一致。时间读数 $t$ 则由

$$
t(k)-t_0 = \int_{k_0}^{k} \frac{1}{2\pi}\operatorname{Tr}Q(\tilde k)\,\frac{\mathrm d E}{\mathrm d\tilde k}\,\mathrm d\tilde k = \int_{E_0}^{E}\Delta\rho(\tilde E)\,\mathrm d\tilde E
$$

给出,将能量轴转化为边界时间轴。

### Local algebras and Rindler wedge

在代数量子场论中,对 Minkowski 空间的楔形区域 $W$ 关联的 von Neumann 代数 $\mathcal A(W)$ 在真空态下的模块流由 Bisognano–Wichmann 定理给出,是沿楔形保持的洛伦兹 Boost。这意味着:对 Rindler 观察者,其固有时间流与 $\mathcal A(W)$ 上的模块时间成比例;Connes–Rovelli 热时间假设将此推广为一般协变场论中"时间即模块流"的范式。

在该背景下,可将楔形边界(或更一般的双锥边界)视为本文的边界代数 $\mathcal A_{\partial}$,散射矩阵由远区场的入射/出射模式构造,Wigner–Smith 延迟矩阵刻画场在楔形附近的驻留时间。通过刻度同一式,可将"几何上定义的固有时间"与"散射相位导数"对齐,从而在具体量子场论模型中实现边界即时钟。

### Boundary CFT and AdS scattering

在 AdS/CFT 场景中,AdS 体域中的场散射在边界 CFT 中体现为算子插入之间的相关函数相位结构;在许多模型中,边界 CFT 的时间平移由其哈密顿量或模块哈密顿量生成。本文的框架将这两点统一地视为边界即时钟的两种实现:散射相位—谱移—延迟矩阵给出边界谱数据的"几何读数",而模块流提供由态决定的"热读数"。二者在刻度同一式的归一化下被强制一致。

---

## Engineering Proposals

本节提出若干实验与工程方案,用于在可控平台上检验"边界即时钟"的关键等式与刻度同一构造。

### Microwave network with vector network analyzer

在微波工程中,复杂网络(波导、谐振腔、耦合器等)常通过多端口散射矩阵 $S(\omega)$ 描述,可由矢量网络分析仪(VNA)直接测量。

构建一多端口网络,使其在工作频带内近似无耗散且满足散射理论的正则性要求。步骤如下:

1. 以 VNA 测得 $S(\omega)$,数值求导得到 $\partial_\omega S(\omega)$;
2. 构造 Wigner–Smith 矩阵
   $$
   Q(\omega)=-iS(\omega)^\dagger\partial_\omega S(\omega),
   $$
   并计算 $\operatorname{Tr}Q(\omega)$;
3. 通过适当的能量—频率归一化,将 $\omega$ 轴映射为时间轴
   $$
   t(\omega)-t_0 = \int_{\omega_0}^{\omega}\frac{1}{2\pi}\operatorname{Tr}Q(\tilde\omega)\,\mathrm d\tilde\omega;
   $$
4. 将网络视为边界代数的具体实现:各端口模式张成 $\mathcal H_\partial$,网络内部的"体内—外域"动力学投影到端口上给出 $S(\omega)$;
5. 在统计稳态下,对端口激励与输出构造经验态 $\omega_{\mathrm{exp}}$,通过能量流守恒与平衡条件近似恢复一个有效模块流,检验其与由 $t(\omega)$ 定义的时间翻译在相关函数上的一致性。

若实测 $\operatorname{Tr}Q(\omega)$ 的频率积分与网络内部平均驻留时间及能量储存率满足刻度同一式,可视为对"边界相位梯度刻度时间"的工程级验证。

### Acoustic scattering in complex cavities

声学散射系统中,同样存在 Wigner–Smith 时间延迟矩阵,其与腔体几何、介质参数与损耗紧密相关。

构造一个多麦克风、多喇叭驱动的声学腔体,测量多端口声散射矩阵,重复上述步骤计算 $Q(\omega)$ 与 $\operatorname{Tr}Q(\omega)$。将声学腔体内部的能量驻留时间与外部散射相位读数对比,可在经典波动背景下检验刻度同一式及其"边界即时钟"解释。

### Integrated photonic circuits

在集成光子学中,耦合环谐振器阵列提供高度可控的散射网络。通过测量输出相位与群延迟,可以以较小的系统误差验证 "相位导数＝ Wigner–Smith 迹" 与 DOS 关系,从而在微尺度上实现边界即时钟。

---

## Discussion (risks, boundaries, past work)

本节讨论"边界即时钟"框架的适用域、潜在风险与与既有工作的关系。

1. **对散射正则性的依赖**:刻度同一式依赖 Birman–Kreĭn 公式与谱移函数的良好定义,这要求 $H-H_0$ 至少为迹类扰动,且散射矩阵在能窗内可微。对于强耦合、多体纯点谱占主导的体系,该框架需经修正或推广。

2. **模块流的动力学解释**:热时间假设的批评指出,模块流未必总能获得自然的动力学解释,特别是在缺乏几何背景或平衡态假设时。本文通过要求模块流与散射时间刻度一致,实际上选择了一族具有良好动力学意义的态与代数;然而,这一选择本身需要额外的物理输入与实验校准。

3. **局域性与因果结构**:本文未显式引入时空因果结构,只在边界代数与散射通道层面工作。要将"边界即时钟"提升为完备的"时间几何",需进一步引入局域子代数、因果镶嵌与宏观几何的重建程序。这与代数量子场论中通过局域代数重建时空结构的研究密切相关。

4. **时间箭头与不可逆性**:刻度同一式只刻画时间参数的尺度与方向,不直接说明时间箭头的来源。将时间箭头与相对熵单调性、广义熵条件或量子聚焦条件绑定,是进一步工作的自然方向。

5. **与热时间假设的关系**:Connes–Rovelli 框架提出时间由模块流给出,而本文将模块流与散射谱数据的刻度统一,形成"边界即时钟"。两者在"时间由态与代数决定"这一点上一致,但本文强调:时间不仅由模块流存在性决定,还由散射谱数据提供的标尺固定;后者具有直接的实验可读性。

6. **工程实现的复杂度**:在微波、声学、光子平台上,测量 $S(\omega)$ 与 $\operatorname{Tr}Q(\omega)$ 已相对成熟;然而要在同一平台上构造合理的"有效模块流"以比较时间刻度,仍需引入统计平衡态建模与噪声分析。这在实践中构成不小的工程挑战。

总体而言,"边界即时钟"框架将一系列看似分散的理论工具——谱移函数、Wigner–Smith 延迟矩阵、模块流、热时间假设——组织为统一的"边界时间"图景,其适用域由散射正则性与模块流的可几何解释共同约束。

---

## Conclusion

在纯算子—几何与散射谱论的框架下,构造了一种"时间＝边界翻译"的统一刻度。核心成果包括:

1. 在 Birman–Kreĭn 与 Wigner–Smith 条件下,散射相位导数、相对态密度与 Wigner–Smith 延迟矩阵迹满足刻度同一式
   $$
   \frac{\varphi'(\omega)}{\pi} = \rho_{\mathrm{rel}}(\omega) = \frac{1}{2\pi}\operatorname{Tr}Q(\omega),
   $$
   由此将频率轴转化为时间轴。

2. 在边界代数 $\mathcal A_{\partial}$ 与忠实态 $\omega$ 的 GNS 表象中,引入模块算子 $\Delta$ 与模块流 $\sigma_t^\omega$,通过模块一致性公理将边界动力学 $\alpha_t$ 与 $\sigma_t^\omega$ 统一,从而将时间刻度固定为"模块时间"。

3. 定义时间结构 $\mathscr T=(\mathcal A_{\partial},\omega,\alpha_t,S(\omega))$,证明在自然的正则性与单调性假设下,存在唯一(至仿射)时间刻度 $t$,同时参数化模块流与散射时间读数。这一时间刻度被解释为"边界即时钟"的读数。

4. 在一维 Schrödinger 散射、楔形局域代数以及微波/声学/光子散射网络中展示了模型化实现与工程级验证路径。

在此框架下,时间不再被看作体域内预设的连续参数,而是边界谱数据与模块流之间协调的一种翻译标度,是"相位—谱移—模块流"三重读取自洽的唯一参数。这为从边界信息出发展开时空与动力学的重建,提供了严谨且可检验的理论基点。

---

## Acknowledgements, Code Availability

作者感谢算子代数、散射理论与代数量子场论领域的大量前人工作,为本文提供了坚实的数学与物理基础。本文未使用数值代码,因而无代码可提供。

---

## References

1. M. Sh. Birman, M. G. Kreĭn, "On the theory of wave operators and scattering matrix for a pair of selfadjoint operators", Dokl. Akad. Nauk SSSR 144 (1962), 475–478.
2. M. G. Kreĭn, "On the trace formula in perturbation theory", Mat. Sbornik 33 (1953), 597–626.
3. F. Gesztesy, B. Simon, "The xi operator and its relation to Krein's spectral shift function", J. Anal. Math. 73 (1997), 267–297.
4. D. R. Yafaev, *Mathematical Scattering Theory*, AMS, 1992.
5. E. P. Wigner, "Lower limit for the energy derivative of the scattering phase shift", Phys. Rev. 98 (1955), 145–147.
6. F. T. Smith, "Lifetime matrix in collision theory", Phys. Rev. 118 (1960), 349–356.
7. P. W. Brouwer, K. M. Frahm, C. W. J. Beenakker, "Quantum mechanical time-delay matrix in chaotic scattering", Phys. Rev. Lett. 78 (1997), 4737–4740.
8. U. R. Patel, E. Michielssen et al., "Wigner–Smith time-delay matrix for electromagnetics and acoustics", 多篇文章,见 arXiv:2003.06985 等。
9. O. Bratteli, D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics*, Vols. 1–2, Springer.
10. S. J. Summers, "Tomita–Takesaki modular theory", arXiv:math-ph/0511034.
11. I. M. Burbano Aldana, "KMS states and Tomita–Takesaki theory", MSc thesis, 2018.
12. A. Connes, C. Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics relation in general covariant quantum theories", Class. Quantum Grav. 11 (1994), 2899–2918.
13. P. Martinetti, C. Rovelli, "Diamond's temperature: Unruh effect for bounded trajectories and thermal time hypothesis", Class. Quantum Grav. 20 (2003), 4919–4932.
14. N. Swanson, "Can quantum thermodynamics save time?", Philos. Sci. 88 (2021), 1041–1052.
15. N. Swanson, *Modular Theory and Spacetime Structure in QFT*, PhD thesis, Princeton University, 2014.
16. K. Hersent, "Thermal aspects of noncommutative Minkowski", CIRM slides (2025).
17. J. van Neerven, P. Portal, "Thermal time as an unsharp observable", arXiv:2306.13774.
18. X. Gutiérrez de la Cal, "Quantum measurements and delays in scattering by zero range potentials", Entropy 26 (2024), 75.

---

## 附录 A:算子散射与刻度同一式的严格框架

本附录给出刻度同一式所依赖的算子散射与谱移函数理论框架的进一步细化。

1. **波算子与散射算子**:在 $H-H_0\in\mathfrak S_1$ 假设下,波算子 $W_\pm$ 存在且完全性成立,散射算子 $S=W_+^\ast W_-$ 为在 $P_{\mathrm{ac}}(H_0)\mathcal H$ 上的酉算子,并与 $H_0$ 对易。由此可在 $H_0$ 的谱分解上将 $S$ 写为能量直积分。

2. **谱移函数的存在性**:Kreĭn 证明在 $H-H_0\in\mathfrak S_1$ 条件下存在 $\xi(\lambda)\in L^1(\mathbb R)$ 使得迹公式成立,且 $\xi$ 在分布意义下为 DOS 差的原函数。

3. **Birman–Kreĭn 公式**:通过分析散射算子与相对行列式的关系,可证明对几乎所有 $\lambda$,
   $$
   \det S(\lambda) = \exp\bigl(-2\pi i\,\xi(\lambda)\bigr),
   $$
   详见 Yafaev、Gesztesy–Simon 等教材。

4. **Wigner–Smith 恒等式**:利用 $S(\lambda)^\dagger S(\lambda)=\mathbf 1$ 与行列式恒等式
   $$
   \partial_\lambda\log\det S(\lambda) = \operatorname{Tr}\bigl(S(\lambda)^{-1}\partial_\lambda S(\lambda)\bigr),
   $$
   再使用酉性 $S^{-1}=S^\dagger$,可得
   $$
   \partial_\lambda\Phi(\lambda) = \operatorname{Im}\operatorname{Tr}\bigl(S(\lambda)^\dagger\partial_\lambda S(\lambda)\bigr) = \operatorname{Tr}Q(\lambda).
   $$
   这一步仅依赖于 $S(\lambda)$ 的可微与酉性。

5. **DOS 与 Wigner–Smith 迹的关系**:将 DOS 定义为 $H$ 与 $H_0$ 的谱测度对 Lebesgue 测度的 Radon–Nikodym 导数,可由 Kreĭn 迹公式与 Birman–Kreĭn 公式联合推出
   $$
   \Delta\rho(\lambda) = \frac{1}{2\pi}\Phi'(\lambda) = \frac{1}{2\pi}\operatorname{Tr}Q(\lambda),
   $$
   构成刻度同一式的算子级基础。

---

## 附录 B:模块流与 KMS 条件

1. **Tomita–Takesaki 定理**:对任一带有循环分离向量 $\Omega$ 的 von Neumann 代数 $\mathcal M$,Tomita 算子 $S_0$ 的闭包 $S$ admits 极分解 $S=J\Delta^{1/2}$。模块算子 $\Delta$ 生成自同构群
   $$
   \sigma_t^\Omega(A)=\Delta^{it}A\Delta^{-it},\qquad A\in\mathcal M,
   $$
   被称为模块自同构群。

2. **KMS 条件**:态 $\omega(A)=\langle\Omega,A\Omega\rangle$ 对 $\sigma_t^\Omega$ 满足 KMS 条件,即对 $A,B\in\mathcal M$,存在解析函数 $F_{A,B}(z)$ 在条带 $0<\operatorname{Im}z<1$ 内解析,边界值满足
   $$
   F_{A,B}(t) = \omega\bigl(A\sigma_t^\Omega(B)\bigr), \qquad F_{A,B}(t+i) = \omega\bigl(\sigma_t^\Omega(B)A\bigr).
   $$

3. **时间流的唯一性**:若存在另一自同构群 $\alpha_t$ 使得 $\omega$ 为 $\alpha_t$ 的 KMS 态,则 $\alpha_t$ 与 $\sigma_t^\Omega$ 在外自同构群中属于同一类,仅差内自同构与时间重标度。对本文的边界代数设定,可用此唯一性将物理时间流 $\alpha_t$ 与模块流 $\sigma_t^\omega$ 统一。

4. **热时间——模块流解释**:Connes–Rovelli 热时间假设提出:给定态 $\omega$ 与可观测代数 $\mathcal A$,模块流 $\sigma_t^\omega$ 所给的 $t$ 即为物理时间参数;当该流与时空几何的某一等距流相关时,二者的速度比率给出温度。本文在边界代数层面沿用这一解释,并以散射—谱移刻度固定时间单位。

---

## 附录 C:一维 Schrödinger 模型中时间刻度的显式计算

以一维短程势散射为例说明时间刻度的显式计算。

1. **Jost 解与散射相位**:对 $H=-\mathrm d^2/\mathrm d x^2+V(x)$ 构造 Jost 解 $f_\pm(x,k)$,满足
   $$
   f_\pm(x,k)\sim\mathrm e^{\pm ikx},\qquad x\to\pm\infty.
   $$
   透射、反射振幅可由 Wronskian 表达式给出,总散射相位 $\Phi(k)$ 可由 $\det S(k)$ 计算。

2. **谱移函数与 DOS**:谱移函数 $\xi(E)$ 与散射相位满足
   $$
   \xi(E)=\frac{1}{\pi}\delta(E)+\sum_n\theta(E-E_n),
   $$
   其中 $\delta(E)$ 为相移,$E_n$ 为束缚态能级;态密度差
   $$
   \Delta\rho(E) = \frac{1}{2\pi}\frac{\mathrm d\Phi(E)}{\mathrm d E} + \sum_n\delta(E-E_n),
   $$
   在连续谱区间内简化为
   $$
   \Delta\rho(E) = \frac{1}{2\pi}\Phi'(E).
   $$

3. **Wigner–Smith 延迟时间**:Wigner–Smith 延迟矩阵在一维双通道中简化为 $2\times 2$ 矩阵,其迹
   $$
   \operatorname{Tr}Q(E) = \frac{\mathrm d\Phi(E)}{\mathrm d E},
   $$
   从而
   $$
   \Delta\rho(E) = \frac{1}{2\pi}\operatorname{Tr}Q(E).
   $$

4. **时间刻度**:选定参考能量 $E_0$ 与时间 $t_0$,定义
   $$
   t(E)-t_0 = \int_{E_0}^{E}\Delta\rho(\tilde E)\,\mathrm d\tilde E = \int_{E_0}^{E}\frac{1}{2\pi}\operatorname{Tr}Q(\tilde E)\,\mathrm d\tilde E.
   $$
   对于布里渊区等周期结构,可将 $E$ 替换为准动量 $k$ 并引入适当的能量—频率变换,从而在一维晶格或波导阵列中实现相同的边界时间刻度。

通过这一显式模型,可以在解析可控的情形下检查"相位—谱移—Wigner–Smith 迹"三者的等价性与时间刻度定义,为更复杂体系中的数值与实验验证提供基准。
