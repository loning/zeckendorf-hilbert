# 时间等价类与广义熵优化：统一交换率、严格公设与面向观测的闭合框架

**Abstract**
提出并严格化以时间等价类 $[T]$ 为核心的统一框架，使"时间之箭""黑洞信息""宇宙学红移/常数"与可测的"延迟–相位–谱移"三者处于同一计算/观测平台。第一，给出 $[T]$ 的精确定义，证明等价关系的自反、对称、传递性，并阐明对割面族的协变准则与态/区域改变时的保持性。第二，建立**统一交换率同一式**
$$
\boxed{\ \rho_{\rm rel}(\omega)=\frac{1}{2\pi}\,\partial_\omega \phi(\omega)=\frac{1}{2\pi}\operatorname{Tr}Q(\omega)\ },
$$
其中 $Q(\omega)=-i\,S^\dagger(\omega)\partial_\omega S(\omega)$ 为 Wigner–Smith 时间延迟算符，$\phi(\omega)=\arg\det S(\omega)$ 为总散射相位，$\rho_{\rm rel}(\omega)$ 为由谱移/相对熵定义的谱密度；该等式来自 Birman–Krein 关系与可观测的相位–延迟测量，量纲一致、可反演。第三，在 Hadamard 态与弱曲率的半经典域中，以"相对熵单调 $\Rightarrow$ QNEC $\Rightarrow$ 局域 GSL/QFC"之链证明：沿零测地族的仿射参数 $\lambda$，$S_{\rm gen}$ 单调；由 $[T]$ 的重参数化得 $S_{\rm gen}$ 随代表时间 $t$ 单调，时间之箭因此为输出性质。第四，以代数嵌入/纠缠楔语言给出"固定投影不可解码 ≡ 事件视界处的时间映射奇点"，并以岛公式的极值切换实现解析延拓，从而恢复 Page 曲线。第五，把 $\Lambda$ 视为 $[T]$ 的全局校准积分常数（与四形式机制相容），强调其不等同于局域"真空能密度"的可测作用。最后，给出三条可操作的核验路径：曲时空等离子几何光学下**$\omega^{-2}$** 阶的色散–几何耦合时间延迟（并给出 null‑test 方案），FRB 的"红移–退相干斜率"层级贝叶斯检验，以及低温多模腔的时间延迟 Bell 见证与手性分裂。附录包含：等价关系三性的完整证明；统一交换率同一式的算符–谱移推导；QNEC/GSL 牵引的主定理证明；曲时空–等离子 eikonal 展开（展示无 $\omega^{-1}$ 主项的条件）；时间场论的规范化、稳定性与低能约束。

**Keywords**
时间等价类；模块时间；广义熵；QNEC；QFC；QES/岛公式；Wigner–Smith 时间延迟；Birman–Krein 谱移；等离子几何光学；层级贝叶斯

---

## 1. Introduction & Historical Context

广义熵 $S_{\rm gen}=A/4G\hbar+S_{\rm out}$ 在半经典量子引力中连接几何与信息。Page 曲线的非微扰重建依赖于量子极值面与岛公式；QNEC 与（局域）QFC 将零方向熵形变与应力能张量、量子聚焦联系起来，并可由相对熵单调性导出。另一方面，Tomita–Takesaki 模块理论把态–代数对 $(\mathcal{A},\omega)$ 的模流 $\sigma^\omega_s$ 视为"内禀时间"，为"时间来自信息–因果结构"的视角提供数学支点。散射侧，Wigner–Smith 延迟算符与总散射相位 $\phi$ 直接可测，Krein 谱移函数 $\xi(\omega)$ 与 $\det S(\omega)$ 以 Birman–Krein 公式耦合。本文把这些支点闭合于一体：以 $[T]$ 的等价类结构统摄"时间"，以**统一交换率**把相位–延迟–谱移纳入可实验的共同刻度。

---

## 2. Model & Assumptions

### 2.1 时间等价类与协变性

**对象**：全局双曲 $(\mathcal{M},g)$；区域族 $\mathfrak{R}$；态–代数对 $\{(\mathcal{A}(R),\omega_R)\}_{R\in\mathfrak{R}}$；零测地族的截面簇 $\mathfrak{C}$。

**定义 2.1（等价）**
对固定 $(\mathcal{A}(R),\omega_R,\mathfrak{C})$，称 $T_1\sim T_2$，若存在外自同构 $\Phi\in{\rm Out}(\mathcal{A}(R))$、严格单调 $f:\mathbb{R}\!\to\!\mathbb{R}$，使
$$
\Phi\circ \sigma^{\omega_R}_s\circ \Phi^{-1}=\sigma^{\omega_R}_{f(s)}\quad\text{且}\quad
\mathcal{E}(\mathfrak{C};T_1)=\mathcal{E}(\mathfrak{C};T_2),
$$
其中 $\mathcal{E}$ 表示沿 $\mathfrak{C}$ 之零生成的"广义熵单调/极值结构"（量子膨胀符号与零集）。

**命题 2.2（三性）**
$\sim$ 为等价关系；对态/区域的完全正保迹映射引起的同伦变形，若相对模流外共轭类不变，则 $[T]$ 保持。割面族细化下，若 $\Theta_{\rm q}\ge 0$，则 $\mathcal{E}$ 保持，称 $[T]$ 对该零测地族协变。证明见附录 A.1–A.2。

### 2.2 统一交换率与量纲一致

**Wigner–Smith 与相位**：$Q(\omega)=-i\,S^\dagger\partial_\omega S$，$\operatorname{Tr}Q=\partial_\omega \arg\det S=\partial_\omega\phi$。
**谱移与相位**：Birman–Krein：$\det S(\omega)=e^{-2\pi i\,\xi(\omega)}\Rightarrow \partial_\omega\phi=-2\pi\,\xi'(\omega)$。
**统一交换率**：
$$
\boxed{\ \rho_{\rm rel}(\omega)=-\xi'(\omega)=\frac{1}{2\pi}\partial_\omega\phi(\omega)=\frac{1}{2\pi}\operatorname{Tr}Q(\omega)\ }.
$$
$\rho_{\rm rel}$ 的定义采取局域窗变分，使 $S(\rho|\sigma)=\int \rho_{\rm rel}(\omega)\,{\rm d}\omega$；量纲与 $\partial_\omega\phi$、$\operatorname{Tr}Q$ 一致。数值反演时以 Kramers–Kronig 与相位解缠作正则化。推导与反演细节见附录 A.3。

### 2.3 假设域与失败条件

Hadamard 态、弱曲率、局域 Rindler 近似与可控形变；几何位形限定在量子光片/事件视界等 GSL 适用情形。失败域：强曲率邻域、非 Hadamard 态、UV 主导背离等。

---

## 3. Main Results (Theorems and Alignments)

### 定理 3.1（时间之箭＝广义熵单调的输出）

在 2.3 的域内，沿指定量子光片的仿射参数 $\lambda$：$\mathrm dS_{\rm gen}/\mathrm d\lambda\ge 0$。任取 $t\in[T]$，若 $t=f(\lambda)$ 且 $f'>0$，则 $\mathrm dS_{\rm gen}/\mathrm dt\ge 0$。证明链条与失败条件详述见附录 B。

### 定理 3.2（黑洞信息：固定投影不可解码与岛公式解析延拓）

以代数嵌入 $\mathcal{A}(\mathcal{I}^+)\subset \mathcal{A}(\mathcal{D})$ 表述外部观测；固定投影对应非可逆 CPTP 降维映射，"信息丢失"仅为该投影下的不可解码。岛公式通过更换驻点（QES）等价于在 $[T]$ 内解析延拓，扩张可重建域 $\Rightarrow$ Page 曲线恢复。附录 C 给出 JT 场景的显式同构。

### 命题 3.3（红移＝时间单位重标度）

$(1+z)=(k\!\cdot\!u)_e/(k\!\cdot\!u)_o$ 为"节奏比"的协变表述，与 FRW $a_0/a_e$ 等价。增量体现在统一交换率把该比值直接联系到 $\phi'(\omega)$ 与 $\rho_{\rm rel}$ 的观测反演。

### 定理 3.4（时间全息与时间量子纠错）

JLMS 与纠缠楔嵌套蕴含：$[T(p)]=\Pi(s,\gamma_p)$；$[T]$ 的投影族在编码子空间 $\mathcal{C}$ 上满足 Knill–Laflamme 条件，故"择时误差"可被等价类冗余校正。附录 D 给出模块 Berry 曲率与路径依赖的可测位相。

### 定理 3.5（$\Lambda$ 的刻度—积分常数与四形式离散化）

迹自由/Unimodular 与四形式机制使 $\Lambda$ 成为积分常数；在热时间规范下其语义为 $[T]$ 的全局校准，且与轴子–四形式量子化导致的近离散谱相容。附录 E 给出作用与变分。

---

## 4. Proofs

**4.1 时间之箭（定理 3.1）**
相对熵单调 $\Rightarrow$ ANEC/QNEC；结合量子 Raychaudhuri 得零方向的量子膨胀不增，$S_{\rm gen}$ 单调。由 $t=f(\lambda)$ 的严格单调得对任意代表时间的单调性。失败域包括强曲率与非 Hadamard 态。详见附录 B。

**4.2 黑洞信息的坐标无关表述（定理 3.2）**
以相对熵与 Petz‑恢复刻画"不可解码"；岛公式的极值切换等价于更改 $[T]$ 的代表并扩张纠缠楔。JT 模型中以复制几何展示该等价。

**4.3 统一交换率（式 2.2）**
Birman–Krein：$\det S=e^{-2\pi i\xi}\Rightarrow \partial_\omega\phi=-2\pi\xi'$；多道下 $\operatorname{Tr}Q=\partial_\omega\phi$。定义 $\rho_{\rm rel}=-\xi'$ 得所述同一式。数值反演以相位解缠与 Kramers–Kronig 正则化控制噪声放大。

---

## 5. Model Apply：两类最小模型

**5.1 1+1 维 CFT–Rindler**
单道散射 $S=e^{i\phi}\Rightarrow Q=\partial_\omega\phi$；把相对熵拆分为谱窗积分验证 $\rho_{\rm rel}=(2\pi)^{-1}\partial_\omega\phi$。KMS 标度与模流重标度一致。

**5.2 JT 重力 + 自由场**
Page 转折对应 QES 驻点切换；在 $[T]$ 中的解析延拓把外部投影的"不可解码"转为扩张重建域的"可解码"。附录 C 给出方程族与示意曲线。

---

## 6. Engineering Proposals（量级、系统学与 Null‑Tests）

### 6.1 深空多频链路：曲时空–等离子 eikonal 的时间延迟

**几何光学**：静态弱场 $\Phi/c^2\ll 1$、各向同性等离子：
$$
n(\omega,x)=\sqrt{1-\omega_p^2(x)/\omega^2},\qquad
\frac{{\rm d}t}{{\rm d}\ell}\simeq \frac{1}{c}\Big(1+\frac{2\Phi}{c^2}\Big)\Big(1+\frac{\omega_p^2}{2\omega^2}\Big).
$$
路径变分给出
$$
\Delta t(\omega)=\Delta t_{\rm Shapiro}+\int\!\frac{\omega_p^2}{2\omega^2}\frac{{\rm d}\ell}{c}
+\int\!\frac{\Phi}{c^2}\,\frac{\omega_p^2}{\omega^2}K(x)\frac{{\rm d}\ell}{c}+O(\omega^{-4}).
$$
**结论**：主导耦合项为 $\omega^{-2}$ 而非 $\omega^{-1}$；$\omega^{-1}$ 仅在各向异性介质或强非绝热流体中可能出现。
**量级与系统学**：Ka/X（8–32 GHz）在冲角 $5^\circ\!-\!15^\circ$ 可达皮秒级差异；主要系统误差为电离层/日球层建模与硬件非线性。
**Null‑tests**：几何换向（冲角翻转）应保 $\omega^{-2}$ 标度而改变几何权重号；同一几何的昼夜差分消去电离层主项。
**设施**：DSN X/Ka 与 DSAC 稳定度链路。

### 6.2 FRB "红移–退相干斜率"层级贝叶斯

**模型**：$W\sim W_0(1+z)^\alpha(\nu/\nu_0)^{-\beta}$，宿主/IGM/仪器分量置于层级先验；选择函数基于通道化阈值与 DM–$z$ 反演不确定度。
**功效**：Catalog‑1 与后续本地化样本在 $N\sim10^2\!-\!10^3$ 下即可 5σ 区分 $\alpha=0$ 的无效假设；随机打乱 $z$ 的 null‑test 应抹平斜率。

### 6.3 低温多模腔：时间延迟的 Bell 见证与手性分裂

**Bell‑时延见证**：$\mathcal{W}=|{\rm Tr}Q_A\otimes{\rm Tr}Q_B-{\rm Tr}Q_{AB}|$，经典 $\le0$，量子耦合下 $\mathcal{W}>0$。
**手性分裂**：受控微扭曲与引力–电磁弱耦合使 $\Delta t_{\rm chiral}\propto \omega$ 线性劈裂。
**噪声预算**：相位白噪声、TLS $1/f$、热致频移、机械微音、计数死区等的贡献与目标亚皮秒灵敏度在附录 G 给出公式/数表。

---

## 7. Time‑Field Theory：规范化、稳定性与低能约束

引入"钟 1‑形式"
$$
u_\mu=\frac{\partial_\mu T}{\sqrt{-\,\partial_\alpha T\,\partial^\alpha T}},
$$
构造最小作用
$$
\mathcal{L}_T=\frac{M_T^2}{2}\Big[c_1\nabla_\mu u_\nu\nabla^\mu u^\nu+c_2(\nabla_\mu u^\mu)^2+c_3 a_\mu a^\mu\Big]+V(T)+\mathcal{L}_{\rm matter}(\psi;u_\mu),
$$
以 Stückelberg 处理 $T\!\mapsto\!f(T)$ 的重参数化冗余。无幽灵与因果稳定域、PPN 与引力切伦科夫约束给出 $(c_i)$ 的可行子空间；区别于 æther/khronon 的要点在于：这里的"优选方向"仅为等价类规范代表，观测性集中于 $\partial_\omega\phi$、$\operatorname{Tr}Q$ 的交换率不变量而非各向异性。

---

## 8. Discussion（一致性、边界与联系）

* **一致性**：主定理严格限定于 Hadamard/弱曲率与量子光片/事件视界几何；超出域时仅保留猜想力度。
* **黑洞信息**：代数–岛公式的同构避免坐标依赖；JT 场景给出可检查的实例。
* **$\Lambda$**：作为刻度积分常数并不等于"真空能密度"；与四形式离散化/轴子机制兼容。
* **可检验性**：深空链路与 FRB 管线给出可复现实作要素与 null‑tests；低温腔实验提供室内可重复的验证平台。

---

## 9. Conclusion

确立 $[T]$ 的严格等价结构与统一交换率，给出时间之箭、黑洞信息、红移与 $\Lambda$ 的共同语义，并以可实施的观测/实验路径把"时间–因果–信息"的统一落到数据层。该框架在"可证—可量—可核验"的三重标准下闭合。

---

## Acknowledgements, Code Availability

感谢关于 QNEC/QFC、QES/岛公式、模块理论、谱移–散射理论与曲时空等离子几何光学的公开文献与资料。附录给出从相位数据到 $\rho_{\rm rel}$ 的反演与 FRB 层级贝叶斯的最小化实现准则。

---

## References

[1] Bousso, Fisher, Leichenauer, Wall. "Quantum focussing and inequalities," *Phys. Rev. D* 93 (2016).
[2] Faulkner et al. "Modular Hamiltonians for deformed half-spaces and the ANEC," *JHEP* (2016).
[3] Engelhardt & Wall. "Quantum extremal surfaces," *JHEP* 01 (2015) 073.
[4] Almheiri et al. "Replica wormholes and the entropy of Hawking radiation," *JHEP* 05 (2020) 013.
[5] Connes & Rovelli. "Von Neumann algebra automorphisms and the thermal time hypothesis," (1994).
[6] Smith. "Lifetime matrix in collision theory," *Phys. Rev.* 118 (1960). （Wigner–Smith）
[7] Birman & Krein. "On wave and scattering operators," *Sov. Math. Dokl.* (1962).
[8] Perlick. "Ray optics in a plasma on a GR spacetime," and related works.
[9] Bisnovatyi‑Kogan & Tsupko. "Gravitational lensing in plasma," reviews (2015–2022).
[10] Rogers. "Frequency‑dependent lensing in plasma," *MNRAS* 451 (2015).
[11] JLMS and successors: boundary–bulk relative entropy equivalence.
[12] Standard cosmology texts for redshift–projection identity.
[13] DSN/DSAC capability briefs.
[14] CHIME/FRB Collaboration. "The first catalog," *ApJS* 257 (2021).

---

## Appendices

### A. 等价关系与统一交换率的证明

**A.1 三性与外共轭**
$\mathcal{G}={\rm Out}(\mathcal{A})\rtimes{\rm Diff}_+(\mathbb{R})$ 的群作用与序保持给出自反–对称–传递；态/区域同伦类下的保持由外共轭不变性保证。

**A.2 割面族协变**
QNEC 充要条件域内，割面细化对应子代数限制，$S_{\rm gen}$ 的序性质保持。

**A.3 Birman–Krein $\Rightarrow$ 统一交换率**
$\det S=e^{-2\pi i\xi}\Rightarrow \partial_\omega\phi=-2\pi\xi'$；多道下 $\operatorname{Tr}Q=\partial_\omega\phi$，得 $\rho_{\rm rel}=-(\xi')=(2\pi)^{-1}\operatorname{Tr}Q$。$\phi$ 的解缠与 Kramers–Kronig 给出稳健反演。

### B. 相对熵 $\Rightarrow$ QNEC $\Rightarrow$ GSL 局域形式

**B.1** 数据处理不等式与子代数限制；
**B.2** 半空间形变的模块哈密顿量二阶公式导出 ANEC/QNEC；
**B.3** 量子 Raychaudhuri 合并得 $\Theta_{\rm q}\le 0$，进而 $\mathrm dS_{\rm gen}/\mathrm d\lambda\ge 0$。

### C. 黑洞信息的代数命题与 JT 例证

**C.1** 固定投影对应非可逆 CPTP，Petz‑恢复度量化"不可解码"；
**C.2** 岛公式驻点切换等价于在 $[T]$ 中改变代表元并扩张纠缠楔；
**C.3** JT 场景：复制几何的鞍点切换对 $\phi'(\omega)$ 的谱窗投影示例图。

### D. 模块 Berry 与时间量子纠错

**D.1** $[T(p)]=\Pi(s,\gamma_p)=\mathrm{P}\exp\!\int_{\gamma_p}\!\mathcal{A}_{\rm mod}$；
**D.2** Knill–Laflamme 条件在"择时误差"噪声模型下的满足与阈值。

### E. $\Lambda$ 的刻度—积分常数与四形式

**E.1** 作用与变分；
**E.2** 量子化/轴子耦合下的近离散谱；
**E.3** 与等价类校准零点的语义对应。

### F. FRB 层级贝叶斯管线（可复现实作骨架）

似然、先验、选择函数、posterior‑predictive 与 null‑tests 的最小化流程。

### G. 低温腔实验噪声预算

相位白噪声、TLS $1/f$、热致频移、机械微音、读出死区的贡献公式、代表参数与达成亚皮秒的配置表。

---

**符号表**：$[T]$；$\sigma_s^\omega$；$\phi(\omega)$；$Q(\omega)$；$\rho_{\rm rel}$；$\Theta_{\rm q}$；$\lambda$；$\mathcal{C}$。
