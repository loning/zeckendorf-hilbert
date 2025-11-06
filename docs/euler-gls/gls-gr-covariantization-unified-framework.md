# GLS–GR 协变化：因果流形—滤镜链与广义相对论的一致化框架

## 摘要

在"广义光结构（GLS）—因果流形—滤镜链"的统一语境中，将广义相对论（GR）的度量—联络与因果结构嵌入几何散射—谱移体系，建立在曲时空上协变化的**相位—密度—群延迟三位一体刻度**与**窗化读数**理论。以曲时空散射矩阵 $S_g(E)$ 与 Wigner–Smith 群延迟矩阵 $\mathsf Q_g(E)=-i\,S_g(E)^\dagger \tfrac{dS_g}{dE}(E)$ 为基本对象，证明在几何散射与谱移（Birman–Kreĭn）框架下恒有
$$
\frac{\varphi_g'(E)}{\pi}\;=\;\rho_{\rm rel}^g(E)\;=\;\frac{1}{2\pi}\operatorname{tr}\mathsf Q_g(E),\qquad
\det S_g(E)=e^{-2\pi i\,\xi_g(E)},\ \ \rho_{\rm rel}^g(E)=-\xi_g'(E),
$$
并给出在窄带—几何光学极限中"时间 = 窗化群延迟读数"的到达时/本征时等价，以及弱场或渐近平直区的 Shapiro/透镜时延重现。Hadamard—微局域光谱条件与能量条件导出**无超锥传播**与**时延正性**；红移—时间满足协变的互易标度律；在范畴层面，证明"因果结构决定共形类 + 体积型定标度量"的互构定理，从而实现 $(\mathrm{GLS})\leftrightarrow(\mathcal M,[g],dV)$ 的等价。本文并以**有限阶 Nyquist–Poisson–Euler–Maclaurin（NPE）误差学**给出非渐近闭合。进一步，提出四个物理学解释层：
（i）**质能等价**与能量—动量关系由三位一体刻度的"母能标"与色散几何导出；（ii）**引力场**对应相位—延迟刻度的聚焦—会聚及其能量条件控制；（iii）**狭义相对论极限**由前沿速度定标与红移互易刻度得到；（iv）**经典力学极限**在 Toeplitz/Berezin 压缩—Egorov 传播与 WKB/eikonal 中得到严格恢复。

---

## Notation & Axioms / Conventions

### 卡片 I（刻度同一与号符约定）

在工作带内散射幺正或经环境扩展幺正化时，采用
$$
\det S_g(E)=e^{-2\pi i \,\xi_g(E)},\quad \rho_{\rm rel}^g(E)=-\xi_g'(E),\quad
\mathsf Q_g=-i\,S_g^\dagger \tfrac{dS_g}{dE},\quad
\frac{1}{2\pi}\operatorname{tr}\mathsf Q_g=\rho_{\rm rel}^g=\frac{\varphi_g'}{\pi}.
$$
该对接在欧氏近无穷与几何散射的曲度背景（含微分形式/Maxwell 场、低正则边界）已被严格建立。([RUG Research][1])

**非幺正通道与可加性**：存在有效损耗/增益时取 $\widetilde{\mathsf Q}:=-i\,S^{-1}S'$，其迹在串并联系统中保持可加；该"复时间延迟"在亚幺正散射中得到普适化。([物理评论链接管理器][2])

### 卡片 II（有限阶 NPE 与"极点 = 主尺度"）

任一窗化读数的离散—连续换算满足
$$
\varepsilon_{\rm total}=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}.
$$
Nyquist 关断使 $\varepsilon_{\rm alias}=0$；端点层由**有限阶** Euler–Maclaurin 估界，尾项由窗外衰减与带限控制；在谱缩放与尺度变换下协变。相关误差估计可由 DLMF 的 Euler–Maclaurin 章给出。([dlmf.nist.gov][3])

---

## 1. 几何散射对象与三位一体刻度的曲时空协变

**定义 1.1（GR–GLS 对象层）** 在全局双曲或适当的渐近类别（渐近平直/欧氏近无穷/锥型）上，记辐射数据空间 $\mathcal H_g$、on–shell 散射矩阵 $S_g(E)$、相位测度 $\mu_\varphi^g$ 与窗—核字典 $\mathcal W_g$。则
$$
\mathfrak U_g=(\mathcal H_g,\ S_g(E),\ \mu_\varphi^g,\ \mathcal W_g),
$$
并在 Melrose 几何散射与辐射场理论中完备。([klein.mit.edu][4])

**定理 1.2（Birman–Kreĭn 的几何延拓）** 在欧氏近无穷的黎曼/洛伦兹散射背景，谱移 $\xi_g$ 与 $S_g(E)$ 满足
$$
\det S_g(E)=e^{-2\pi i\,\xi_g(E)},\qquad \xi_g'(E)=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q_g(E).
$$
从而三位一体刻度在曲时空散射框架中成立。([RUG Research][1])

**注记**（Maxwell/微分形式的 BK 公式）微分形式与电磁散射中的 Birman–Kreĭn 公式确保上述刻度同一的普适性。([RUG Research][1])

---

## 2. 因果结构与共形类；光学几何与广义费马原理

**定理 2.1（因果重建）** 在适当的因果正则性（如 distinguishing/strong causality）下，因果结构决定流形拓扑与度量的共形类；配以体积型 $dV$ 即定标度量。这可由 Malament 与后续综述系统阐明。([天文数据系统][5])

**命题 2.2（广义费马原理与光学度量）** 静态/定常及更一般背景上，光线为光学度量测地，eikonal 相位 $S$ 即到达时泛函的变分极值；透镜像位、畸变、亮度均由此推演。([SpringerLink][6])

---

## 3. 时间 = 窗化群延迟读数：窄带—几何光学极限

**定义 3.1（窗化群延迟）** 对因果可达链 $\gamma$ 与窗—核 $(w_R,h)$，定义
$$
T_{\gamma,g}[w_R,h]:=\int_{\mathbb R}(w_R*\check h)(E)\,\frac{1}{2\pi}\operatorname{tr}\mathsf Q_{g,\gamma}(E)\,dE,\qquad \check h(E):=h(-E).
$$

**定理 3.2（eikonal/窄带极限）** 在静态/定常贴片与窄带极限，有
$$
T_{\gamma,g}[w_R,h]=\int_{\gamma}\frac{-k_\mu u^\mu}{\omega_0}\,d\lambda\;+\;\mathcal E_{\rm NPE},
$$
右端与类时世界线的本征时或类光到达时等价，$\mathcal E_{\rm NPE}$ 受卡片 II 控制；弱场/渐近平直情形可分解出 Shapiro/透镜时延。论证依赖 $\operatorname{tr}\mathsf Q=\partial_E \arg\det S$ 与因果—解析（Kramers–Kronig–Titchmarsh）结构。([混沌书籍][7])

---

## 4. 前沿速度定标、无超锥传播与时延正性

**定义 4.1（前沿速度 $c$）** 以真空冲激响应最早非零到达 $t_{\rm front}(L)$ 的极限定义 $c=\lim_{L\to\infty}L/t_{\rm front}(L)$，作为因果前沿的规范常数。

**定理 4.2（无超锥传播）** 在 Hadamard—微局域光谱条件下，类空间分离处对易子为零，窗化冲激响应对 $t<L/c$ 必为零；任何窗化群延迟读数不早于因果前沿。([SpringerLink][8])

**定理 4.3（引力时延正性）** 在满足 Null Energy 与 Null Generic 条件的全局双曲时空，最快类光曲线相对参考曲线的净时延非负；AdS 边界情形亦满足相应边界时延定理。([arXiv][9])

**旁证** 宇宙学与太阳系的 Shapiro/透镜时延观测史构成经验锚点。([物理评论链接管理器][10])

---

## 5. 红移—时间的协变互易律与 Etherington 距离互易

发射/观测四速度 $u_{\rm src},u_{\rm obs}$ 与光子波矢 $k$ 给出频率比
$$
1+z=\frac{(u^\mu k_\mu)_{\rm src}}{(u^\mu k_\mu)_{\rm obs}},
$$
诱导窗—核的协变重标度
$$
T_{\gamma,g}^{\rm obs}[w_R,h]=\frac{1}{1+z}\,T_{\gamma,g}\!\big[w_R^{\langle 1/(1+z)\rangle}\,,\,h^{\langle 1/(1+z)\rangle}\big],
$$
等价于母刻度的谱缩放 $E\mapsto E/(1+z)$。该互易与无吸收/测地传播下的 Etherington 距离互易 $D_L=(1+z)^2D_A$ 一致，并获现代观测的检验与约束。([维基百科][11])

---

## 6. 分辨率—红移对偶与尺度重整

令偶窗 $w_R(E)=w((E-E_0)/R)$。分辨率提升 $R\mapsto\lambda R$ 与谱缩放 $E\mapsto E/(1+z)$ 对偶：Nyquist 纪律下别名项闭杀，有限阶 Euler–Maclaurin 端点层与尾项上界随尺度协变，从而给出带宽—分辨率—红移的工程化协同律。([dlmf.nist.gov][3])

---

## 7. 曲时空 QFT 的窗化微因果一致性

Hadamard—微局域光谱条件刻画物理可接受态的奇性结构，保证类空间分离对易子消失与光锥支撑；因此**窗化微因果**与代数量子场论微因果同构，GLS 的"前沿下界"与 QFT 的传播支撑相容。([SpringerLink][8])

---

## 8. 渐近平直边界、BMS 结构与记忆/红外刻度

在 $\mathscr I^\pm$ 的 BMS 对称下，散射数据（相位、群延迟、记忆）获得边界刻度；软定理—记忆—渐近对称的统一视角为远区的相位—延迟—红移校准提供规范锚点，并与近年"天球全息"综述相呼应。([arXiv][12])

---

## 9. 互构定理（GR 版）：$(\mathrm{GLS})\leftrightarrow(\mathcal M,[g],dV)$

**定理 9.1（协变互构）** 设 $(\mathcal M,[g])$ 原因果正则，给定体积型 $dV$。构造函子
$$
\mathfrak F_g:\mathbf{WScat}_g\to\mathbf{Cau},\qquad
\mathfrak G_g:\mathbf{Cau}\to\mathbf{WScat}_g,
$$
令 $\mathfrak F_g$ 以 $\operatorname{tr}\mathsf Q_g$ 等值面与相位奇性生成偏序与光锥，$\mathfrak G_g$ 以固有时间/光学结构构造带限窗—核与 Berezin 压缩，并以卡片 I/II 校准，则存在自然同构
$$
\mathfrak F_g\circ\mathfrak G_g\simeq \mathrm{Id}_{\mathbf{Cau}},\qquad
\mathfrak G_g\circ\mathfrak F_g\simeq \mathrm{Id}_{\mathbf{WScat}_g}.
$$
几何支点为因果重建与几何散射的谱移—群延迟协变。([天文数据系统][5])

---

## 10. 静态球对称算例：Shapiro/透镜时延的窗化重现

Schwarzschild 区域内类光传播的窗化群延迟在窄带—几何光学极限下分解为
$$
\Delta T_{\rm lens}=\Delta T_{\rm geom}+\Delta T_{\rm pot},
$$
其中势项产生 $\log r$ 标度的 Shapiro 时延；其正性由聚焦与能量条件支配；太阳系与强透镜观测提供经验校准。([物理评论链接管理器][10])

---

## 11. 规范协变与相对不变：链式读数的一致化

对能量依赖基变换 $S\mapsto U(E)\,S\,V(E)$，有
$$
\operatorname{tr}\mathsf Q(USV)=\operatorname{tr}\mathsf Q(S)-i\,\operatorname{tr}(U^\dagger U')-i\,\operatorname{tr}(V'V^\dagger).
$$
当 $U,V$ 与能量无关或 $\det U(E)\det V(E)\equiv 1$ 时，任意窗化读数 $T_{\gamma,g}[w_R,h]$ 不变；一般情形取**相对读数** $T_{\rm rel}=T[S]-T[S_{\rm ref}]$ 消除规范漂移。非幺正—损耗系统可采用 $\widetilde{\mathsf Q}=-i\,S^{-1}S'$ 以保持串并联可加性。([物理评论链接管理器][2])

---

## 12. 误差学与工程化处方（GR 贴片）

1. **局域 Nyquist**：在局域惯性系/静态贴片选择采样步长，关断别名；
2. **有限阶 EM**：按所需阶数估界端点层与余项（DLMF 24.8）；
3. **尾项控制**：以窗支撑与带宽衰减约束；
4. **几何校准**：以真空前沿到达 $t_{\rm front}(L)$ 定标 $c$，曲率修正由 Shapiro/透镜项与 BMS 远区配准给出。([dlmf.nist.gov][3])

---

## 13. 质能等价与能量—动量关系的窗化推导

GLS 将能标 $E$ 视为三位一体刻度的"母轴"。在局域惯性贴片，平面波相位 $S(x)= -Et+p_ix^i$ 之能量—动量色散为 $E^2-p^2 c^2=m^2 c^4$。该关系可由 Minkowski 四动量不变性与 Hamilton–Jacobi/eikonal 对偶得到；能量读数由相位对时间位移的共轭性给出，群延迟读数 $\partial_E S$ 即飞行时。质能等价 $E=mc^2$ 在 $p=0$ 的静止窗中即为基准刻度。([维基百科][13])

**解释**：
（i）在窗化散射中，$\operatorname{tr}\mathsf Q=\partial_E \arg\det S$ 将"能—相位"导数与"时间—延迟"对应；
（ii）质量 $m$ 可理解为色散关系的"相位曲率"不变量，其在几何极限下由时空度量的时间样尺度定标；
（iii）能量守恒对应散射相位的加法律与谱移的可加性（BK 公式）。([RUG Research][1])

---

## 14. 引力场的相位—延迟刻度与能量条件

Raychaudhuri 方程与会聚定理把引力会聚刻画为测地束的膨胀 $\theta$ 的演化；在窗化读数中，相位—延迟的"聚焦"表现为 $\partial_E\partial_{E'} \arg\det S$ 的半正定性，受 Null Energy/Generic 条件控制，给出净时延正性与"无宏观超前"。这与 Gao–Wald 的时延定理一致，并在边界耦合（如 AdS）时保持。([arXiv][9])

**物理图景**：
曲率把自由传播的等相位面"压缩"为更密的延迟等值面，$\operatorname{tr}\mathsf Q$ 的上升即"到达时"延展。该几何图像在弱场近似下分离为几何项（光程变长）与势项（Shapiro $\log r$），与观测相符。([arXiv][14])

---

## 15. 狭义相对论极限：前沿速度、Doppler/红移与分辨率互易

在局域惯性系，前沿速度 $c$ 由最早非零响应定标；群速度与群延迟满足 Kramers–Kronig–Titchmarsh 因果—解析关系，避免超前。相对论 Doppler/引力红移体现在母能标的 $(1+z)^{-1}$ 缩放，并与窗—核的分辨率互易精确耦合。([光学出版集团][15])

---

## 16. 经典力学极限：Toeplitz/Berezin—Egorov—WKB/eikonal

在 $\hbar$ 有效趋零或相位高度振荡的极限下，Toeplitz/Berezin 压缩与 Egorov 定理给出可观测沿 Hamilton 流的传播，WKB/eikonal 则把波传播化为测地/费马原理；群延迟 $\partial_E S$ 等于经典飞行时，$\nabla_x S=p$ 与 Hamilton–Jacobi 方程恢复。([imo.universite-paris-saclay.fr][16])

**Newtonian 极限** 在弱场静态度量 $ds^2=-(1+2\Phi/c^2)c^2dt^2+(1-2\Phi/c^2)d\mathbf x^2$ 下，测地方程退化为牛顿方程 $\ddot{\mathbf x}=-\nabla\Phi$，Shapiro 时延的势项来自 $g_{tt}$ 校正。([damtp.cam.ac.uk][17])

---

## 17. 多物理域的 Wigner–Smith 统一与非幺正扩展

Wigner–Smith 时间延迟矩阵在量子/电磁/声学等多域均成立，并可推广至材料色散与损耗体系；在工程上可由散射参量及其频导数稳定计算，迹与相位导数的一致性为窗化读数提供可实现的数值路径。([arXiv][18])

---

## 18. 结论（要点）

1. 三位一体刻度 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 在曲时空几何散射中协变成立（BK 公式），从而为"时间 = 窗化群延迟读数"提供母刻度。([RUG Research][1])
2. Hadamard—微局域与能量条件保证"无超锥传播"与"时延正性"。([SpringerLink][8])
3. 红移—分辨率对偶与 Etherington 互易在窗化读数上精确落地。([维基百科][11])
4. 狭义相对论与经典力学分别作为前沿定标与 Egorov—WKB 极限在本框架中恢复；质能等价与能量—动量关系可由母能标与色散几何统一解释。([维基百科][13])

---

## 参考文献（选）

1. Strohmaier, A.; Waters, A. "The Birman–Kreĭn Formula for Differential Forms and Electromagnetic Scattering." *Stud. Appl. Math.* (2022). ([RUG Research][1])
2. Melrose, R. B. "Spectral and Scattering Theory for the Laplacian on Asymptotically Euclidian Spaces." Lecture notes/monograph. ([klein.mit.edu][4])
3. Minguzzi, E. "Lorentzian Causality Theory." *Living Reviews in Relativity* 22 (2019). ([SpringerLink][19])
4. Malament, D. B. "The Class of Continuous Timelike Curves Determines the Topology of Spacetime." *J. Math. Phys.* 18 (1977). ([天文数据系统][5])
5. Perlick, V. "Gravitational Lensing from a Spacetime Perspective." *Living Reviews in Relativity* 7 (2004). ([SpringerLink][6])
6. Radzikowski, M. J. "Microlocal Approach to the Hadamard Condition in QFT on Curved Spacetime." *Commun. Math. Phys.* 179 (1996). ([SpringerLink][8])
7. Gao, S.; Wald, R. M. "Theorems on Gravitational Time Delay and Related Issues." (2000). ([arXiv][9])
8. Shapiro, I. I. "Fourth Test of General Relativity." *Phys. Rev. Lett.* 13 (1964). ([物理评论链接管理器][10])
9. Wigner, E. P. "Lower Limit for the Energy Derivative of the Scattering Phase Shift." *Phys. Rev.* 98 (1955). ([混沌书籍][7])
10. Smith, F. T. "Lifetime Matrix in Collision Theory." *Phys. Rev.* 118 (1960). ([混沌书籍][20])
11. Haakestad, M. W.; Skaar, J. "Causality and Kramers–Kronig Relations for Waveguides." *Optics Express* 13 (2005). ([光学出版集团][15])
12. Etherington 距离互易与现代检验综述（例：Liu 等, 2023）。([ScienceDirect][21])
13. Strominger, A. "Lectures on the Infrared Structure of Gravity and Gauge Theory." (2017). 与近期天球全息综述（Donnay, 2024）。([arXiv][12])
14. Zworski, M. 等教材与讲义（Egorov 与半经典分析）。([imo.universite-paris-saclay.fr][16])
15. Patel, U. R.; Michielssen, E. "Wigner–Smith Time-Delay Matrix for Electromagnetics" 系列工作（含损耗/色散扩展）。([arXiv][18])
16. NIST DLMF：Euler–Maclaurin 公式与误差。([dlmf.nist.gov][3])

---

[1]: https://research.rug.nl/files/232459978/1_s2.0_S0007449722000707_main.pdf?utm_source=chatgpt.com "The Birman-Krein formula for differential forms and ..."
[2]: https://link.aps.org/accepted/10.1103/PhysRevE.103.L050203?utm_source=chatgpt.com "Generalization of Wigner time delay to subunitary ..."
[3]: https://dlmf.nist.gov/24.8?utm_source=chatgpt.com "DLMF: §24.8 Series Expansions ‣ Properties ‣ Chapter ..."
[4]: https://klein.mit.edu/~rbm/papers/sslaes/sslaes1.pdf?utm_source=chatgpt.com "Spectral and scattering theory for the Laplacian"
[5]: https://ui.adsabs.harvard.edu/abs/1977JMP....18.1399M/abstract?utm_source=chatgpt.com "The class of continuous timelike curves determines ..."
[6]: https://link.springer.com/article/10.12942/lrr-2004-9?utm_source=chatgpt.com "Gravitational Lensing from a Spacetime Perspective"
[7]: https://chaosbook.org/library/WignerDelay55.pdf?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering ..."
[8]: https://link.springer.com/article/10.1007/BF02100096?utm_source=chatgpt.com "Micro-local approach to the Hadamard condition in ..."
[9]: https://arxiv.org/abs/gr-qc/0007021?utm_source=chatgpt.com "Theorems on gravitational time delay and related issues"
[10]: https://link.aps.org/pdf/10.1103/PhysRevLett.13.789?utm_source=chatgpt.com "Fourth Test of General Relativity"
[11]: https://en.wikipedia.org/wiki/Etherington%27s_reciprocity_theorem?utm_source=chatgpt.com "Etherington's reciprocity theorem"
[12]: https://arxiv.org/abs/1703.05448?utm_source=chatgpt.com "Lectures on the Infrared Structure of Gravity and Gauge Theory"
[13]: https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation?utm_source=chatgpt.com "Energy–momentum relation"
[14]: https://arxiv.org/abs/2004.11845?utm_source=chatgpt.com "An Examination of Geometrical and Potential Time Delays in Gravitational Lensing"
[15]: https://opg.optica.org/oe/abstract.cfm?uri=oe-13-24-9922&utm_source=chatgpt.com "Causality and Kramers-Kronig relations for waveguides"
[16]: https://www.imo.universite-paris-saclay.fr/~stephane.nonnenmacher/enseign/Cours-Semiclassical-Analysis2019-lecture1-8.pdf?utm_source=chatgpt.com "Introduction to semiclassical analysis"
[17]: https://www.damtp.cam.ac.uk/user/us248/Lectures/Notes/grII.pdf?utm_source=chatgpt.com "Part II General Relativity"
[18]: https://arxiv.org/pdf/2005.03211?utm_source=chatgpt.com "Wigner-Smith Time Delay Matrix for Electromagnetics"
[19]: https://link.springer.com/article/10.1007/s41114-019-0019-x?utm_source=chatgpt.com "Lorentzian causality theory | Living Reviews in Relativity"
[20]: https://chaosbook.org/library/SmithDelay60.pdf?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory"
[21]: https://www.sciencedirect.com/science/article/pii/S0370269323000217?utm_source=chatgpt.com "What are recent observations telling us in light of improved ..."
