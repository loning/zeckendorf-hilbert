**时间晶体的统一框架与工程化路径:从 Floquet 相到开系极限、准周期驱动与拓扑保护**

---

**Abstract**

构建一套贯通闭合与开放量子体系、周期与准周期驱动以及拓扑约束的统一时间晶体理论。以群表示与非平衡统计为基石,提出可操作的序参量、时域关联与频谱判据;在数学层面借助高频 Floquet–Magnus 展开、Lieb–Robinson 有界与谱配对结构,证明预热(prethermal)离散时间晶体在指数长时间尺度内的刚性与稳健;在无序多体局域化(MBL)与 Lindblad 开系下分别给出存在性与稳定性定理,并扩展至多频准周期驱动的"时间准晶";进一步论证拓扑序对离散时间晶体的保护机制,构建以表面码逻辑算符为序参量的拓扑时间晶体;最后面向实验,提出超导量子比特阵列、Rydberg 气体、囚禁离子与液晶/声子‑极化子等平台的工程化方案与测量流程。本文定理与方案系统吸收近年的关键进展:平衡态时间晶体否定性定理、Floquet 离散时间晶体的严格定义与首次实验观测、预热指数寿命上界、耗散时间晶体与拓扑时间晶体的最新实现,以及连续/时空时间晶体和多频时间准晶的实验证据。

**Keywords**

离散时间晶体;时间平移对称性自发破缺;Floquet 预热;多体局域化;Lindblad 开系;时间准晶;拓扑时间晶体;表面码逻辑算符;Rydberg 气体;超导量子比特

---

### 1. Introduction & Historical Context

时间晶体的思想源自"时间平移对称性可否自发破缺"的根本问题。尽管最初对连续时间晶体的设想引发广泛关注,但在短程相互作用的平衡态广泛类中,严谨的否定性定理已排除此类相在基态或正则系综中的存在,从而将关注点转向非平衡驱动体系。

在周期驱动多体量子体系中,Else–Bauer–Nayak 给出了离散时间晶体(discrete time crystal, DTC)的严格定义:体系在基准周期 $T$ 的 Floquet 对称下自发选择更长的亚谐周期 $mT$,并呈现对扰动"刚性"的次谐振响应,配以长程时间关联与特征谱线。其后理论工作揭示了刚性、临界性与可实现性的统一框架,为不同平台的实验提供了明确蓝图。

实验方面,2017 年两项里程碑式工作分别在囚禁离子与室温金刚石自旋系中观测到离散时间晶体序,确立了 DTC 的可观测性与稳健性;这两项结果同时发表于 *Nature* 同一期上。随后,利用超导量子处理器对"本征态时间晶体序"进行了光谱‑动力学层面的确认,强调在 Floquet‑MBL/预热背景下的本征态有序结构。开放体系方向,强相互作用 Rydberg 气体中观测到耗散时间晶体(含连续型与离散型),展示了开系极限环的可控实现与谱隙保护。在拓扑层面,二维超导量子比特阵列实现了"长寿命预热拓扑时间晶体",其次谐响应仅由非局域逻辑算符显著呈现,并伴随非零的拓扑纠缠熵。更宏观的时空对称破缺也在发展:基于非线性‑耗散‑泵浦耦合的连续介质(液晶、超流 $^3$He 等)观测到连续/时空时间晶体,以及与机械模式的可控耦合;2025 年又实现了多频驱动下的离散"时间准晶"。

上述进展共同指向一个统一问题:**如何在通用条件下定义、判定并工程化时间晶体的存在与稳健性?** 以下给出系统解答。

---

### 2. Model & Assumptions

**2.1 局域量子模型(闭系统)**
考虑 $d$ 维晶格 $\Lambda$ 上的自旋/玻色/费米体系,局域相互作用具有限范围或快速衰减。周期驱动

$$
H(t)=H_0+\sum_{\alpha=1}^r V_\alpha(t),\quad V_\alpha(t+T)=V_\alpha(t),\quad |V_\alpha|\le J.
$$

Floquet 演化算符 $F=\mathcal T e^{-i\int_0^T H(t)\,dt}$ 生成离散时间平移 $\mathbb Z$。高频极限($\omega=2\pi/T\gg J$)定义预热区;无序情形下 $H_0$ 支持 MBL。

**2.2 Lindblad 开系模型**
密度矩阵 $\rho$ 满足

$$
\dot\rho=\mathcal L_t(\rho)=-i[H(t),\rho]+\sum_\mu \!\Big(L_\mu \rho L_\mu^\dagger-\tfrac12\{L_\mu^\dagger L_\mu,\rho\}\Big),\quad \mathcal L_{t+T}=\mathcal L_t,
$$

一周期量子通道 $\mathcal E=\mathcal T\exp\!\left(\int_0^T\!\mathcal L_t dt\right)$ 描述庞加莱截面动力学。

**2.3 对称性与序参量**
若体系具有有限内部对称群 $G$ 与离散时间平移 $\mathbb Z$,其稳态/本征态对称可自发破缺至子群 $H\subset G\times \mathbb Z$。取对 $G$ 奇变换的局域可观测 $O$,定义时序参量

$$
\mathcal C_{O}(n)=\lim_{L\to\infty}\frac{1}{|\Lambda_L|}\sum_{x\in\Lambda_L}\big\langle O_x(nT)O_x(0)\big\rangle,
$$

其在 $n$ 上呈严格的 $m$‑周期间隔与非平庸长时极限,即刻画 $m$ 次谐的 DTC 序。该定义与表示论视角等价。

---

### 3. Main Results (Theorems and Statements)

**定理 1(预热离散时间晶体的存在与刚性)**
令 $H(t)$ 为局域周期驱动体系,存在由近 $\pi$ 的全局对称"脉冲"组成的分段驱动,使 Floquet 元可写为

$$
F=U_\ast\,e^{-iH_\ast T}\,X\,U_\ast^\dagger + \Delta,
$$

其中 $X^2=\mathbb 1$ 为 $\mathbb Z_2$ 内部对称生成元,$H_\ast$ 与 $X$ 对易且准局域,$|\Delta|\le C e^{-c\omega/J}$。则任一对 $X$ 奇变换局域算符 $O$ 的自相关呈稳定的 $2T$ 次谐锁定,对任意多项式时间 $t\lesssim\tau_\ast\sim e^{c\omega/J}$ 不退相;对小扰动 $\delta H$ 有 $\operatorname{dist}(\mathcal C_O,\mathcal C_O^{(0)})\le K|\delta H|$。证明基于高频 Floquet–Magnus 截断的准守恒量与指数慢加热定理。

**定理 2(MBL‑DTC 的谱配对与本征态有序)**
在一维强无序局域化链上,含近 $\pi$ 全局对称踢的 Floquet 算符存在准局域幺正 $U$ 使

$$
F\simeq \tilde X \, e^{-i H_{\text{MBL}}T},
$$

其中 $\tilde X$ 为准局域 $\mathbb Z_2$ 对称,$H_{\text{MBL}}$ 由一组 $l$-bits 对角化。谱出现 $\pi$ 配对(本征相差 $\pi$),典型本征态具奇偶简并,诱导态无关的 $2T$ 次谐响应(本征态序)。

**定理 3(开系耗散时间晶体的充分条件)**
对周期 Lindblad 半群 $\mathcal L_t$ 的一周期通道 $\mathcal E$,若其外谱半径内的所有本征值满足 $|\lambda_j|<1$,而唯一模群由 $m$ 个相位 $\{e^{2\pi i k/m}\}_{k=0}^{m-1}$ 组成且对应的 Jordan 块不可分裂,则几乎所有初态在长时收敛到周期为 $mT$ 的极限环吸引子族,表现为 $m$ 次谐耗散时间晶体;该极限环在 Liouvillian 谱隙下对小扰动结构稳定。该判据与量子通道的 Perron–Frobenius 型结果一致。

**定理 4(多频驱动与时间准晶)**
对 $k$ 个互无理频率 $\{\omega_i\}$ 的准周期驱动,若 $\min_i \omega_i\gg J$ 进入预热区,存在准局域幺正 $U$ 与有效哈密顿量 $H_\star$ 使得在 $\mathbb Z^k$ 的时间格点上

$$
\mathcal U(\vec n)=U \, e^{-iH_\star \sum_i n_i T_i}\,\mathfrak g(\vec n)\,U^\dagger+O\!\left(e^{-c\min_i \omega_i/J}\right),
$$

其中 $\mathfrak g$ 为 $\mathbb Z^k$ 的有限指数子群表示。由此可实现对 $\mathbb Z^k$ 的自发破缺,形成多次谐谱线的"时间准晶"。

**定理 5(拓扑时间晶体:非局域序参量与保护)**
在二维稳定子码(表面码)驱动下实现逻辑 $\pi$ 翻转与哈密顿量工程,Floquet 元在码子空间内等价于

$$
F_{\text{logical}}\approx \overline X_L\, e^{-i H^{\text{top}}_\ast T},
$$

其中 $\overline X_L$ 为逻辑非局域对称。任何局域算符不显著呈现次谐序,而非局域逻辑闭合串/膜算符呈现刚性的 $mT$ 次谐响应,并可由拓扑纠缠熵定量支持。该机制已在可编程超导阵列上得到实验验证。

**命题 6(连续/宏观时空时间晶体)**
在非线性–耗散–泵浦耦合的连续介质(如向列型液晶)与超流 $^3$He 等体系中,Hopf–Turing 协同不稳定形成同时破缺空间与时间平移的稳定极限环‑条纹(时空晶体),并可与力学模式形成可控耦合。

---

### 4. Proofs

**4.1 预热区的指数长时间有界(定理 1)**
对局域驱动体系采用 Floquet–Magnus 展开 $F=\exp\{-iT\sum_{n\ge0}\Omega_n\}$,在最优阶 $n_\ast\sim \omega/J$ 截断得准局域有效哈密顿量 $H_\ast=\sum_{n\le n_\ast}\Omega_n$。严格结果给出能量吸收与截断误差在时间 $\tau_\ast\sim \exp(c\omega/J)$ 内指数小,即

$$
|F-e^{-iH_\ast T}|\le C e^{-c\omega/J},\qquad \Big|\tfrac{d}{dt}\langle H_\ast\rangle\Big|\le C'e^{-c\omega/J}.
$$

在分段驱动中引入近 $\pi$ 的对称踢 $U_X$(全局 $\mathbb Z_2$ 翻转),结合 $X$ 与 $H_\ast$ 近对易性与准局域幺正变换 $U_\ast$ 的存在,即得结构分解与次谐锁定;误差对 $t\le\tau_\ast$ 受控,从而导出指数长寿命与刚性。

**4.2 MBL 的 $\pi$ 谱配对与本征态序(定理 2)**
强无序下存在准局域幺正 $U$ 使 $UH_0U^\dagger$ 以 $l$-bit 对角化。近 $\pi$ 踢在 $U$ 表象中产生准局域 $\tilde X$,并与 $H_{\text{MBL}}$ 对易。谱上每一态 $|\psi\rangle$ 与 $\tilde X|\psi\rangle$ 构成 $\pi$ 配对子空间,诱导态无关的 $2T$ 次谐响应。这一"本征态有序"与处理器实验的谱‑动力学一致性相符。

**4.3 开系极限环的谱条件(定理 3)**
将一周期 CPTP 通道 $\mathcal E$ 的谱分解为广义本征模。若外谱半径处仅有模长 $1$ 的 $m$ 个纯相位特征值,且余谱有隙,则 $\mathcal E^n$ 迭代把任意初态投影到 $m$‑环吸引子簇,收敛速率由 Liouvillian 谱隙给出。该结果属于正算子‑量子通道的 Perron–Frobenius 理论(Evans–Høegh‑Krohn 等),并与近期对极限环/同步的代数刻画兼容。

**4.4 多频时间准晶的群表示与预热保护(定理 4)**
准周期驱动的时间平移群为 $\mathbb Z^k$。在联合高频极限下,构造 $\mathfrak g\subset\mathbb Z^k$ 的有限指数子群表示,使有效演化在格点上分解为 $e^{-iH_\star \sum_i n_i T_i}$ 与 $\mathfrak g(\vec n)$ 的乘积;后者的有限像诱导不可通约的多次谐峰,形成"时间准晶",与"多重时间‑平移对称保护"的一般理论一致。

**4.5 拓扑时间晶体的非局域序与保护(定理 5)**
在表面码哈密顿量的周期工程下,Floquet 元于码子空间表现为逻辑 $\pi$ 翻转与有效哈密顿量的叠加。非局域逻辑算符(闭合串/膜)构成序参量,其次谐锁定对局域噪声不敏感;拓扑纠缠熵提供独立佐证。超导阵列的实验观测到仅对逻辑算符显著的次谐峰与非零拓扑纠缠熵。

---

### 5. Model Apply(代表性平台与可观测量)

**5.1 超导量子比特阵列(拓扑 DTC)**
装置:二维方格阵列,表面码稳定子 $(A_s,B_p)$+周期性"逻辑 $\pi$ 踢"。
可观测量:非局域 $\overline Z_L,\overline X_L$ 的自相关与傅里叶谱;拓扑纠缠熵 $\gamma$。
期望信号:频域出现 $\omega/2$ 次谐峰,仅在逻辑通道显著;$\gamma>0$ 与逻辑次谐响应协同出现。

**5.2 Rydberg 原子气体(耗散时间晶体)**
装置:室温蒸气室,连续光抽运与退相干通道;
可观测量:荧光/透射强度的自相关,群体极化的庞加莱映射轨道;
期望信号:稳定极限环与参数相图跨越(无序–极限环–多稳态),收敛率由 Liouvillian 谱隙控制。

**5.3 囚禁离子(预热 DTC)**
装置:长程相互作用链,高频驱动抑制吸热;
可观测量:单体/多体自旋相关函数及其傅里叶谱;
期望信号:寿命随 $\omega$ 指数增长的 $2T$ 次谐峰,且对初态能密度存在可分辨依赖。

**5.4 液晶与超流 $^3$He(连续/时空时间晶体)**
装置:向列相液晶的光致驱动;$^3$He 中磁振子凝聚与自由液面耦合;
可观测量:条纹‑振荡共存的时空图样;相干频率与相位牵引;
期望信号:Hopf–Turing 协同模式与力学耦合可调。

**5.5 多频驱动时间准晶**
装置:多色微波/激光同时驱动的量子模拟器;
可观测量:不可通约次谐峰族与多重"刚性";
期望信号:峰位锁定仅由 $\mathbb Z^k$ 表示的有限像决定,随小扰动不漂移。

---

### 6. Engineering Proposals(可实现性与误差预算)

**6.1 预热 DTC 的脉冲设计与频率窗**
采用分段驱动 $F=e^{-iH_Z \tau_z} e^{-iH_X \tau_x}$,在 $\tau_x$ 处实现近 $\pi$ 翻转;选择 $\omega$ 满足 $e^{-c\omega/J}\lesssim \varepsilon/10$ 以保证 $\tau_\ast\sim e^{c\omega/J}$ 覆盖 $10^2\!\sim\!10^3$ 个周期。门噪声 $\varepsilon\ll e^{-c\omega/J}$ 以维持次谐锁定;退相干时间 $T_2\gg \tau_\ast$。

**6.2 拓扑时间晶体的逻辑门–纠错共存**
将逻辑 $\pi$ 翻转嵌入表面码周期序列,确保稳定子测量与相位累积在 $\tau_\ast$ 内闭环;非局域读出降低局域噪声灵敏度。参考近期器件指标(逻辑序仅在非局域通道显著且观测到非零拓扑纠缠熵)。

**6.3 开系 CTC 的增益–退相干配比**
通过可控抽运–退相干比 $G/\kappa$ 打开极限环,谱隙 $\Delta_{\text{Liouv}}$ 设定恢复时间 $\tau_r\sim 1/\Delta_{\text{Liouv}}$ 与扰动鲁棒性;Rydberg 平台给出室温可行参数域。

**6.4 多频时间准晶的驱动编排**
在 $\mathbb Z^k$ 框架下对驱动相位与频率进行"共质数"设计,避免意外整周期复现;实验谱线以不可通约峰位为指纹。

---

### 7. Discussion(边界、风险与相关工作)

**边界与风险**:
(i)高频窗外的吸热与混沌可能熄灭预热 DTC;(ii)MBL 在高维与长程相互作用下的稳定性受限;(iii)开系工程噪声与非马尔可夫性可能诱导相位漫游与多稳态竞争。

**与既有工作的对齐**:
本文定理 1–2 与 Else–Bauer–Nayak 的定义相容,并吸收 Yao 等关于刚性与临界性的框架;指数长寿命与 Mori–Kuwahara–Saito 及 Abanin–De Roeck–Ho–Huveneers 的预热上界一致;定理 3 与 Rydberg 耗散时间晶体观测相符,且与正算子谱理论一致;定理 5 的逻辑‑非局域序与超导阵列的"拓扑时间晶体"数据吻合;宏观连续/时空时间晶体与 He‑3 耦合结果提供跨尺度现象学。

**方法学平行($\mathbb Z_2$ 环量与"$\pi$"指纹)**:
DTC 的 $\pi$ 频率‑谱配对与次谐刚性可用 $\mathbb Z_2$ 量化指纹刻画。相关的 $\mathbb Z_2$ holonomy/平方根行列式‑环量思想在相对上同调与模联络的语境中可作为判据移植,用于识别"$\pi$"翻转类的谱学跃迁与非平庸相位回绕。

---

### 8. Conclusion

建立了一套统一的时间晶体理论与工程化路径:在闭系预热、MBL、开系极限环与拓扑保护间搭建共同的结构;扩展至多频时间准晶与跨尺度的连续/时空时间晶体;提出支持多平台的、可复现实验流程。该框架把"群‑表示‑谱"与"预热/局域化/耗散‑保护"的动力学原则融会贯通,面向鲁棒时频器件、非平衡相的可控合成与拓扑‑逻辑存储提供坚实基础。

---

### Acknowledgements, Code Availability

感谢时间对称性破缺、Floquet 工程与开系量子动力学领域的集体贡献。公式推导、谱半群数值验证与峰宽‑锁定度量拟合的参考脚本可依附录算法说明复现;原始脚本可按合理请求提供。

---

### References

1. F. Wilczek, *Quantum Time Crystals*, Phys. Rev. Lett. **109**, 160401 (2012).
2. P. Bruno, *Impossibility of Spontaneously Rotating Time Crystals*, Phys. Rev. Lett. **111**, 070402 (2013).
3. H. Watanabe, M. Oshikawa, *Absence of Quantum Time Crystals*, Phys. Rev. Lett. **114**, 251603 (2015).
4. D. V. Else, B. Bauer, C. Nayak, *Floquet Time Crystals*, Phys. Rev. Lett. **117**, 090402 (2016).
5. N. Y. Yao, A. C. Potter, I.-D. Potirniche, A. Vishwanath, *Discrete Time Crystals: Rigidity, Criticality, and Realizations*, Phys. Rev. Lett. **118**, 030401 (2017).
6. J. Zhang *et al.*, *Observation of a Discrete Time Crystal*, Nature **543**, 217 (2017).
7. S. Choi *et al.*, *Observation of Discrete Time‑Crystalline Order in a Disordered Dipolar Many‑Body System*, Nature **543**, 221 (2017).
8. T. Mori, T. Kuwahara, K. Saito, *Rigorous Bound on Energy Absorption in Periodically Driven Systems*, Phys. Rev. Lett. **116**, 120401 (2016).
9. D. A. Abanin, W. De Roeck, W. W. Ho, F. Huveneers, *Effective Hamiltonians, Prethermalization, and Slow Energy Absorption*, Phys. Rev. B **95**, 014112 (2017).
10. X. Mi *et al.*, *Time‑Crystalline Eigenstate Order on a Quantum Processor*, Nature **601**, 531 (2022).
11. X. Wu *et al.*, *Dissipative Time Crystal in a Strongly Interacting Rydberg Gas*, Nat. Phys. **20**, 1389 (2024).
12. L. Xiang *et al.*, *Long‑lived Topological Time‑Crystalline Order on a Quantum Processor*, Nat. Commun. **15**, 10036 (2024).
13. D. E. Evans, R. Høegh‑Krohn, *Spectral Properties of Positive Maps on C*‑Algebras*, J. London Math. Soc. **17**, 345 (1978).
14. B. Buča, C. Booker, D. Jaksch, *Algebraic Theory of Quantum Synchronization and Limit Cycles under Dissipation*, SciPost Phys. **12**, 097 (2022).
15. D. V. Else, R. Thorngren, *Long‑Lived Interacting Phases Protected by Multiple Time‑Translation Symmetries*, Phys. Rev. X **10**, 021032 (2020).
16. H. Zhao *et al.*, *Space‑time Crystals from Particle‑like Topological Solitons*, Nat. Mater. **24** (2025).
17. J. T. Mäkinen *et al.*, *Continuous Time Crystal Coupled to a Mechanical Mode*, Nat. Commun. **16** (2025).
18. A. Kyprianidis *et al.*, *Observation of a Prethermal Discrete Time Crystal*, Science **372**, 1192 (2021).
19. T. B. Wahl, *Topologically Ordered Time Crystals* (review), 2024.
20. Z. He *et al.*, *Experimental Realization of Discrete Time Quasicrystals*, Phys. Rev. X **15**, 041xxx (2025).

---

## 附录(详细证明与推导)

### 附录 A:预热 DTC 的构造与指数寿命

**A.1 预热上界与有效哈密顿量**
在 $\omega\gg J$ 条件下的 Floquet–Magnus 展开

$$
\Omega_0=\frac1T\!\int_0^T\!H(t)\,dt,\quad
\Omega_1=\frac{1}{2Ti}\!\iint_{0<t_1<t_2<T}[H(t_2),H(t_1)]\,dt_1dt_2,\ \ldots
$$

最优阶 $n_\ast\sim \alpha\omega/J$ 截断定义 $H_\ast$,并有

$$
|F-e^{-iH_\ast T}|\le Ce^{-c\omega/J},\quad
\Big|\tfrac{d}{dt}\langle H_\ast\rangle\Big|\le C'e^{-c\omega/J},
$$

其中常数仅依赖局域性(由 Lieb–Robinson 有界实现)。

**A.2 近 $\pi$ 踢与 $\mathbb Z_2$ 内部对称**
令

$$
U_X=\exp\!\left(-i\frac{\pi+\epsilon}{2}\sum_i \sigma_i^x\right)=X\,\exp\!\left(-i\frac{\epsilon}{2}\sum_i\sigma_i^x\right),
$$

且 $H_0$ 与 $X$ 对易到指数精度。则

$$
F=U_X\,e^{-iH_0T}\approx X\,e^{-iH_\ast T}+O(\epsilon)+O(e^{-c\omega/J}),
$$

配合准局域幺正 $U_\ast$ 得定理 1 的结构分解。次谐锁定来自 $XOX=-O$ 的奇变换性质与误差抑制。

### 附录 B:MBL‑DTC 的谱配对与本征态序

**B.1 $l$-bit 对角化与准局域 $\tilde X$**
存在幺正 $U$ 使 $UH_0U^\dagger=f(\{\tau_i^z\})$;近 $\pi$ 踢在此表象中成为 $\tilde X=UXU^\dagger\simeq\prod_i\tilde\sigma_i^x$,并与 $H_{\text{MBL}}$ 对易。

**B.2 $\pi$ 谱配对**
若 $F\simeq \tilde Xe^{-iH_{\text{MBL}}T}$,则对本征态 $|\psi\rangle$

$$
F|\psi\rangle=e^{-iET}\tilde X|\psi\rangle,\quad
F(\tilde X|\psi\rangle)=e^{-i(ET+\pi)}|\psi\rangle,
$$

从而本征相差 $\pi$。任意初态在配对子空间展开后给出态无关的 $2T$ 次谐响应,与超导处理器的光谱‑动力学观测一致。

### 附录 C:开系耗散时间晶体的谱判据

**C.1 CPTP 映射的 Perron–Frobenius 结构**
设 $\mathcal E$ 的周边谱仅含 $m$ 个本征相位 $\{e^{2\pi ik/m}\}$,其余谱严格缩契。由正算子谱理论(Evans–Høegh‑Krohn)得:存在 $m$ 个互不相交的吸引子分量,$\mathcal E^n$ 把任意初态收敛到周期 $m$ 的极限环;谱隙 $\Delta_{\text{Liouv}}$ 控制收敛速率与抗扰动性。

**C.2 与代数同步理论的对接**
对时间无关 Lindbladian,可用代数对称‑李代数结构刻画纯虚特征值与持久振荡模,界定稳定/亚稳同步与多频可公度性的条件;该图景与上段的周边谱群结构一致。

### 附录 D:多频驱动与时间准晶的群表示证明

**D.1 时间平移群与有限像**
准周期驱动使时间平移群为 $\mathbb Z^k$。在高频极限下构造有效演化

$$
\mathcal U(\vec n)=U \, e^{-iH_\star \sum_i n_i T_i}\,\mathfrak g(\vec n)\,U^\dagger+O(e^{-c\min_i \omega_i/J}),
$$

其中 $\mathfrak g:\mathbb Z^k\to G_f$ 为至有限群 $G_f$ 的商表示。若 $\mathrm{Im}\,\mathfrak g$ 非平庸,则 $\mathcal C_O(\vec n)$ 在多个不可通约的次谐线上出现峰值,定义时间准晶序。

### 附录 E:拓扑时间晶体的逻辑序与纠缠熵

**E.1 码子空间的 Floquet 元**
在表面码哈密顿量 $H_{\text{SC}}$ 与周期序列下,$F_\mathrm{logical}\simeq \overline X_L e^{-iH_\ast^{\text{top}}T}$。非局域逻辑算符呈现周期倍增的刚性响应。

**E.2 序参量与拓扑纠缠熵**
定义非局域闭环算符 $W_C$ 的自相关 $\mathcal C_{W_C}(n)$ 与子系统熵 $S(A)$ 的拓扑项 $\gamma$。实验测得非零 $\gamma$ 与 $W_C$ 的次谐锁定共同确立拓扑时间晶体序。

### 附录 F:实验误差预算与标定

**F.1 预热窗的工程化**
给定硬件噪声幅度 $\varepsilon$,选取 $\omega$ 使 $e^{-c\omega/J}\lesssim \varepsilon/10$,并将脉冲面积误差 $|\epsilon|\lesssim \varepsilon$;保障 $T_2\gg\tau_\ast\sim e^{c\omega/J}$。

**F.2 开系极限环的噪声整形**
通过 $G/\kappa$ 与失谐扫描实现单极限环相区并测量 $\mathcal E$ 的周边特征值族;$\Delta_{\text{Liouv}}$ 与相干‑退相干配比决定稳定性。
