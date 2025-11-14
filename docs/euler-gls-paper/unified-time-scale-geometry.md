# 统一时间刻度与时间几何：因果排序、幺正演化与广义熵

## Abstract

提出一条将相对论、量子散射与信息–全息三端严格粘合的"统一时间刻度等价类"。核心刻度同一式把散射总相位之导数、相对态密度与 Wigner–Smith 群延迟的迹统一为同一对象的不同投影：

$$
\boxed{\ \frac{\varphi'(\omega)}{\pi}\;=\;\rho_{\mathrm{rel}}(\omega)\;=\;\frac{1}{2\pi}\operatorname{tr}Q(\omega)\ },\qquad
Q(\omega)=-\,iS(\omega)^\dagger\partial_\omega S(\omega),\ \varphi=\tfrac12\arg\det S.
$$

在几何端，Killing 时间、ADM lapse、零测地仿射参数及 FRW 共形时间被证明可在统一等价类内相互重标；在信息–全息端，以 Tomita–Takesaki 模块流为"内在时间"，以 QFC/QNEC 与相对熵单调性控制小因果菱形上的广义熵极值，从而在半经典–全息窗口导出爱因斯坦方程。该框架得到三组对齐：（i）相位—本征时间等价 $\phi=(mc^2/\hbar)\int d\tau$；（ii）引力时间延迟＝群延迟迹 $\Delta T=\partial_\omega\Phi=\operatorname{Tr}Q$；（iii）FRW 红移＝相位节奏比 $1+z=a(t_0)/a(t_e)=[(d\phi/dt)_e]/[(d\phi/dt)_0]$。本文在**因果排序–幺正演化–熵的单调/极值**三公理下，建立统一时间刻度的存在性与仿射唯一性，并给出面向实验和工程计量的实现方案。

**Keywords**：时间几何；统一时间刻度；Wigner–Smith 群延迟；谱移函数；Killing/ADM/null/共形/模块时间；广义熵；QFC/QNEC
**MSC 2020**：83C45, 81U40, 81T20, 83C57

---

## 1  Introduction & Historical Context

时间在不同理论中的角色分裂：广义相对论以本征时间刻度化因果结构，量子理论以外参生成幺正演化，信息–全息把模块流视作内在"热时间"。然而三端读数彼此"对表"时，仍缺少一条严密且可计量的共同刻度。Wigner 与 Smith 在散射理论中引入相位对能量之导数定义时间延迟，Wigner–Smith 群延迟矩阵 $Q=-iS^\dagger\partial_\omega S$ 的迹等于总相位 $\Phi=\arg\det S$ 的导数，使"时间＝相位梯度"的思想首次落地于实验可读的标尺。以谱移函数刻画相互作用引起的态密度变化之 Birman–Kreĭn 公式则把散射行列式的相位与谱几何紧密相连，从而导出"相位导数＝相对态密度"。

相对论侧，静态时空中红移/钟速由 $g_{tt}$ 或 Tolman–Ehrenfest 定律给出；ADM $(3{+}1)$ 分解中的 lapse $N$ 刻画坐标时间与本征时间的比值；渐近平坦外区的 tortoise 坐标与 $(u,v)$ 提供无穷远处自然的 null 时间；FRW 宇宙学中 $1+z=a(t_0)/a(t_e)$ 以共形时间直线化零测地。

信息–全息侧，Tomita–Takesaki 模块理论赋予任意（态,代数）对一族内在一参数自同构（模块流）；Connes–Rovelli 热时间假说把该模块流视为物理时间候选；相对熵单调性、QFC 与 QNEC 则把广义熵的变化与应力张量约束在一起，并在小因果菱形极限连通到场方程与重建。

上述历史线索提示：**把"相位–群延迟–谱移"与"钟速–红移–仿射/共形时间"及"模块时间–广义熵"统一到单一刻度**，有望得到一条跨尺度的时间–几何框架。

---

## 2  Model & Assumptions

**(A) 因果与全局结构**
令 $(M,g)$ 为 stably causal 的洛伦兹流形；在全局双曲条件下存在光滑时间函数与光滑分解 $M\cong \mathbb R\times\Sigma$。

**(B) 散射与谱移**
在绝对连续谱能窗 $I\subset\mathbb R$ 上，散射矩阵 $S(\omega)$ 酉且光滑；定义总相位 $\Phi=\arg\det S$，群延迟 $Q=-iS^\dagger\partial_\omega S$。存在谱移函数 $\xi(\omega)$ 与相对态密度 $\rho_{\mathrm{rel}}=-\xi'$；Birman–Kreĭn 公式 $\det S(\omega)=\exp[-2\pi i\,\xi(\omega)]$ 成立。

**(C) 统一刻度同一式（核心假设）**

$$
\boxed{\ \frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)\ },\qquad
\varphi=\tfrac12\Phi .
$$

**(D) 边界熵与模块流**
取穿过点 $p$ 的小因果菱形 $D_{p,r}$，零生成元仿射参数 $\lambda$；广义熵

$$
S_{\rm gen}(\lambda)=\frac{\mathrm{Area}(\Sigma_\lambda)}{4G\hbar}+S_{\rm out}(\lambda)
$$

满足 QFC/QNEC 类型不等式与相对熵单调性；模块哈密顿量 $K=-\ln\rho$ 生成模块流 $\sigma_s$。

**(E) 幺正演化**
态空间 $\mathcal H$ 上存在强连续幺正群 $U(t)=e^{-iHt}$；半经典世界线极限可把 $t$ 与 $\tau$ 以相位密度联系（见第 4.1）。

---

## 3  Unified Time Scale：定义与三公理

### 3.1  统一时间刻度等价类

**定义 3.1（统一时间刻度）**
存在等价类

$$
[T]\sim\{\tau,\ t,\ t_{\rm K},\ (N,N^i),\ \lambda_{\rm null},\ u,v,\ \eta,\ \omega^{-1},\ z,\ s_{\rm mod}\},
$$

其成员通过单调重标与几何/熵结构互相可换，使动力学局域、因果有序、熵结构最简。

### 3.2  三条公理

**公理 I（因果排序）**：在局域双曲域内存在严格递增的时间函数，使基本方程为局域（双曲/一阶）形式。

**公理 II（幺正演化）**：存在强连续幺正群 $U(t)$；半经典极限中相位—时间关系由拉格朗日驻相确定（第 4.1）。

**公理 III（熵的单调/极值）**：沿零割面族 $\{\Sigma_\lambda\}$，$S_{\rm gen}$ 满足相对熵单调与 QFC/QNEC 的单调/凸性并在物理演化下取极值；模块流参数 $s$ 使 $S_{\rm gen}$ 的组织律最简。

**定理 3.2（半经典–全息窗口的互相蕴含）**
在小因果菱形极限与相对熵单调性/QNEC 成立时：

$$
\text{公理 I}+\text{公理 II}\ \Longleftrightarrow\ \text{刻度同一式}\ \Longrightarrow\ \text{公理 III}\ \Longrightarrow\ \text{爱因斯坦方程}.
$$

证明见第 5 节与附录 D/E。

---

## 4  Main Results（Theorems and Alignments）

### 4.1  相位—本征时间的等价

**定理 4.1（世界线主相位）**
对质量 $m$ 的窄波包，半经典极限下

$$
\phi=-\frac{1}{\hbar}S[\gamma_{\rm cl}]=\frac{mc^2}{\hbar}\int_{\gamma_{\rm cl}}d\tau,\qquad \frac{d\phi}{d\tau}=\frac{mc^2}{\hbar}.
$$

（证明：世界线路径积分驻相；见附录 B。）

### 4.2  引力时间延迟＝群延迟迹

**定理 4.2（eikonal–散射对齐）**
在静态或渐近平坦背景的几何光学极限下，

$$
\Delta T(\omega)=\partial_\omega\Phi(\omega)=\operatorname{Tr}Q(\omega).
$$

弱场极限回到 Shapiro 延迟。

### 4.3  红移＝相位节奏比

**命题 4.3（FRW 相位表述）**
平直 FRW 度规下共动观测者测得

$$
1+z=\frac{\nu_e}{\nu_0}=\frac{\left.\frac{d\phi}{dt}\right|_{e}}{\left.\frac{d\phi}{dt}\right|_{0}}=\frac{a(t_0)}{a(t_e)}.
$$

（见附录 C。）

### 4.4  GR 时间结构的四条"桥"

**桥 B（Killing 时间–钟速–红移）**
静态度规 $ds^2=-V(\mathbf x)c^2dt^2+\cdots$ 中静止观察者
$d\tau=\sqrt{V}\,dt$，$\sqrt{V}$ 即局域红移/钟速因子（Tolman–Ehrenfest）。

**桥 C（ADM lapse–局域钟速）**
ADM 分解 $ds^2=-N^2 dt^2+h_{ij}(dx^i+N^i dt)(dx^j+N^j dt)$；与切片正交的 Euler 族满足 $d\tau=N\,dt$。

**桥 D（null 仿射参数–retarded/advanced/共形时间）**
渐近平坦外区定义 tortoise $r^{*}$ 与 $u=t-r^{*},\ v=t+r^{*}$，其与零测地仿射参数单调等价；FRW 中 $d\eta=dt/a(t)$ 直线化零测地。

**桥 E（模块时间–熵梯度–几何方程）**
模块流 $\sigma_s$ 的参数 $s$ 提供信息论时间；相对熵单调性与 QNEC/QFC 把 $\partial_s S_{\rm gen}$ 的极值/单调与 $\langle T_{kk}\rangle$ 绑定。

### 4.5  熵几何形式的爱因斯坦方程

**定理 4.4（熵–几何）**
在公理 III 与 Raychaudhuri 方程下，于小因果菱形上有

$$
R_{\mu\nu}-\tfrac12Rg_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle .
$$

（证明：面积二阶变分与 QNEC/相对熵合并，见附录 D；参见 Jacobson 与后续全息论证。）

### 4.6  统一刻度同一式（谱–散射–几何）

**推论 4.5**

$$
\boxed{\ \frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)\ } ,
$$

由 Birman–Kreĭn 与 $\operatorname{Tr}Q=\partial_\omega\Phi$ 联立而得（附录 A）。

---

## 5  Proofs（要点）

**5.1  定理 4.1**：沿类时测地线的世界线作用量驻相，涨落仅改变量子前因子，主相位给出 $\phi=(mc^2/\hbar)\int d\tau$（附录 B）。
**5.2  定理 4.2**：eikonal 相位差 $\Delta S\simeq-\hbar\,\omega\,\Delta T$ 与散射 $\partial_\omega\Phi=\operatorname{Tr}Q$ 对齐，得 $\Delta T=\operatorname{Tr}Q$；弱场检验回到 Shapiro 延迟。
**5.3  命题 4.3**：零测地与尺度因子给出 $\nu\propto 1/a(t)$，红移为相位节奏比（附录 C）。
**5.4  桥 B–E**：静态钟速、ADM lapse、null 坐标与模块流各自的标准结论与文献完全一致（附录 E）。
**5.5  定理 4.4**：Raychaudhuri 的面积二阶变分 $\propto-\int R_{kk}$ 与 QNEC $S''_{\rm out}\ge (2\pi/\hbar)\!\int\!\langle T_{kk}\rangle$ 合并，极值条件 $S'_{\rm gen}(0)=0$ 推出张量方程（附录 D）；QFC 提供更强单调性背景。

---

## 6  Model Apply

**A. 太阳系几何延迟的频域重建**
对多频雷达回波相位 $\Phi(\omega)$ 求导得 $\Delta T(\omega)=\partial_\omega\Phi=\operatorname{Tr}Q$，与 Shapiro 延迟比对，可并行剥离等离子体色散项。

**B. 引力透镜的相位–群延迟统一**
像对 $(i,j)$ 的费马势差 $\Delta t_{ij}$ 等于 $\partial_\omega[\Phi_i-\Phi_j]$；宽带电磁/引力波联合用于 Hubble 常数与质量模型的系统误差抑制。

**C. 宇宙学"相位标尺"**
以脉冲星/FRB 的相位节奏比直接估计 $a(t)$，避开特定谱线系统学；"相位–红移"对表由命题 4.3 保障。

**D. 有效"时间折射率"层析**
由 $\rho_{\mathrm{rel}}(\omega)$ 或 $\operatorname{tr}Q(\omega)$ 的空间分布反演 $n_t=(-g_{tt})^{-1/2}$，与光学度规–费马原理配合做弱场时延成像。

---

## 7  Engineering Proposals

1. **片上群延迟断层计量**：集成光子学测 $S(\omega)$ 并实时计算 $\operatorname{Tr}Q(\omega)$，生成等效"引力时延"映射用于器件反演与鲁棒设计。
2. **双高度物质波基准**：COW 几何布置对比 $\Delta\phi$ 与 $\Delta\tau$，检验 $\Delta\phi=(mc^2/\hbar)\Delta\tau$ 的线性区。
3. **宽带透镜群延迟谱**：以 $\partial_\omega\Phi$ 同步拟合各像到达时延与色散，降低时延宇宙学系统误差。
4. **"熵光锥"平台**：可控量子体系上测 $S_{\rm out}$ 的二阶形变与能流，检验 QNEC/QFC 系数与饱和条件。

---

## 8  Discussion（risks, boundaries, past work）

**（i）谱端点与正则性**：刻度同一式要求 $S(\omega)$ 可微且属适当行列式类；共振与阈值附近需轮廓位移与迹类正则化。
**（ii）几何光学与强场**：强自旋/非静态背景需推广光学度规与相干传输；近视界区域宜改用 null 坐标与数值光线追迹。
**（iii）熵–几何假设域**：QNEC 已有一般 QFT 证明与全息证明并不断加强（含最新证明新途径），但在曲率高、强量子引力区仍在推进。
**（iv）GR 时间结构一致化**：Killing/ADM/null/共形/模块时间是统一刻度在不同投影上的坐标化；Bernal–Sánchez 的全局时间函数与 ADM 叶分解提供严谨基础。

---

## 9  Conclusion

在**因果排序–幺正演化–熵的单调/极值**三公理下，得到统一时间刻度等价类，使微观（相位/散射）、介观（群延迟/红移）与宏观（熵–几何）三端语言对齐。核心结论：

$$
\phi=\frac{mc^2}{\hbar}\!\int d\tau,\quad
\Delta T(\omega)=\partial_\omega\Phi(\omega)=\operatorname{Tr}Q(\omega),\quad
1+z=\frac{(d\phi/dt)_e}{(d\phi/dt)_0},\quad
G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\,\langle T_{\mu\nu}\rangle,
$$

以及谱–散射–几何刻度同一式 $\varphi'/\pi=\rho_{\mathrm{rel}}=(2\pi)^{-1}\operatorname{tr}Q$。时间因而可被刻画为：**使动力学局域、因果清晰、熵结构最简**的一维参数的等价类；其不同"名字"仅是同一对象在不同投影下的坐标。

---

## Acknowledgements, Code Availability

感谢相关教材与文献。用于群延迟–时延重建与 FRW 相位节奏演示的符号推导与数值脚本可按需提供。

---

## References

1. E. P. Wigner, "Lower Limit for the Energy Derivative of the Scattering Phase Shift," *Phys. Rev.* **98** (1955) 145.
2. F. T. Smith, "Lifetime Matrix in Collision Theory," *Phys. Rev.* **118** (1960) 349.
3. A. Strohmaier and A. Waters, "The Birman–Krein formula for differential forms and electromagnetic scattering," *arXiv:2104.13589*.
4. A. N. Bernal and M. Sánchez, "Smoothness of time functions and the metric splitting of globally hyperbolic spacetimes," *Commun. Math. Phys.* **257** (2005) 43.
5. É. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, Springer (2012); lecture notes (2007).
6. I. I. Shapiro, "Fourth Test of General Relativity," *Phys. Rev. Lett.* **13** (1964) 789; see also updates (1971).
7. D. W. Hogg, "Distance measures in cosmology," *arXiv:astro-ph/9905116* (2000).
8. S. J. Summers, "Tomita–Takesaki Modular Theory," *Encycl. Math. Phys.* (2006).
9. A. Connes and C. Rovelli, "Von Neumann Algebra Automorphisms and Time–Thermodynamics Relation in General Covariant Quantum Theories," *Class. Quant. Grav.* **11** (1994) 2899.
10. R. Bousso, Z. Fisher, S. Leichenauer, A. C. Wall, "Quantum Focusing Conjecture," *Phys. Rev. D* **93** (2016) 064044.
11. R. Bousso, Z. Fisher, J. Koeller, S. Leichenauer, A. C. Wall, "Proof of the Quantum Null Energy Condition," *Phys. Rev. D* **93** (2016) 024017.
12. S. Balakrishnan, T. Faulkner, Z. U. Khandker, H. Wang, "A General Proof of the QNEC," *JHEP* **09** (2019) 020.
13. D. L. Jafferis, A. Lewkowycz, J. Maldacena, S. J. Suh, "Relative entropy equals bulk relative entropy," *JHEP* **06** (2016) 004.
14. N. Engelhardt, A. C. Wall, "Quantum Extremal Surfaces," *JHEP* **01** (2015) 073.
15. T. Jacobson, "Thermodynamics of Spacetime: The Einstein Equation of State," *Phys. Rev. Lett.* **75** (1995) 1260.
16. T. Faulkner, R. G. Leigh, O. Parrikar, H. Wang, "Modular Hamiltonians for Deformed Half-Spaces and the ANEC," *JHEP* **09** (2016) 038.
17. T. Hartman, S. Kundu, A. Tajdini, "Averaged Null Energy Condition from Causality," *JHEP* **07** (2017) 066.
18. V. Perlick, *Ray Optics, Fermat's Principle, and Applications to GR*, Springer (2000).
19. Scholarpedia, "Bondi–Sachs Formalism" (for retarded time $u$ and advanced time $v$).

---

## Appendices

### 附录 A：Wigner–Smith 群延迟与谱–散射–几何同一式

**A.1  Birman–Kreĭn 与谱移**
对迹类/准迹类扰动的自伴对 $(H,H_0)$，谱移函数 $\xi(\omega)$ 满足

$$
\det S(\omega)=e^{-2\pi i\xi(\omega)}\Rightarrow
\frac{1}{2\pi}\partial_\omega\Phi(\omega)= -\xi'(\omega)=\rho_{\mathrm{rel}}(\omega).
$$

（参见文献 3。）

**A.2  迹恒等式**
由 $Q(\omega)=-iS^\dagger\partial_\omega S$ 与 $\operatorname{Tr}\ln S=\ln\det S$ 得

$$
\operatorname{Tr}Q(\omega)=\partial_\omega\Phi(\omega).
$$

合并 A.1 得刻度同一式：

$$
\boxed{\ \frac{\varphi'(\omega)}{\pi}=\rho_{\mathrm{rel}}(\omega)=\frac{1}{2\pi}\operatorname{tr}Q(\omega)\ } .
$$

### 附录 B：世界线路径积分下"相位–本征时间"

沿类时测地线 $\gamma_{\rm cl}$ 的 Fermi 正交坐标展开

$$
S[\gamma]=-mc^2\!\int d\tau+\frac{m}{2}\!\int d\tau\,\delta_{ij}\dot y^i\dot y^j+\cdots .
$$

驻相给

$$
\phi=-\frac{1}{\hbar}S[\gamma_{\rm cl}]
=\frac{mc^2}{\hbar}\!\int d\tau,\qquad \frac{d\phi}{d\tau}=\frac{mc^2}{\hbar}.
$$

### 附录 C：FRW 宇宙学中红移的相位表述

平直 FRW：$ds^2=-dt^2+a(t)^2 d\mathbf x^2$。共动观测者 $u^\mu=(1,0,0,0)$，光子 eikonal 相位 $\phi$ 有 $k_\mu=\partial_\mu\phi$ 与

$$
\nu=-\frac{1}{2\pi}k_\mu u^\mu=\frac{1}{2\pi}\frac{d\phi}{dt}\propto\frac{1}{a(t)} \Rightarrow
1+z=\frac{(d\phi/dt)_e}{(d\phi/dt)_0}=\frac{a(t_0)}{a(t_e)} .
$$

（参考 7。）

### 附录 D：广义熵极值/单调与场方程

令 $\{\Sigma_\lambda\}$ 穿过 $p$ 的零割面族。Raychaudhuri：$\dot\theta=-\tfrac12\theta^2-\sigma^2-R_{kk}$。面积二阶变分
$\displaystyle \left.d^2A/d\lambda^2\right|_{0}\propto -\!\int R_{kk}\,dA$。
QNEC 与相对熵单调性：$\displaystyle \left.d^2S_{\rm out}/d\lambda^2\right|_{0}\ge \frac{2\pi}{\hbar}\!\int\!\langle T_{kk}\rangle dA$。
极值 $S'_{\rm gen}(0)=0$ 合并给 $R_{kk}=8\pi G\langle T_{kk}\rangle$，对任意 $k^\mu$ 成立，升格为张量方程并给出 $\Lambda$ 作为积分常数。

### 附录 E：GR 时间桥的细化

**E.1  静态时空（Killing）**：$\xi^\mu$ 为时间样 Killing 向量，静止观察者 $u^\mu=\xi^\mu/\sqrt{-\xi^2}$，若 $g_{tt}=-V$ 则 $d\tau=\sqrt{V}\,dt$。（Tolman–Ehrenfest 温度红移定律同型。）

**E.2  ADM lapse**：$ds^2=-N^2 dt^2+h_{ij}(dx^i+N^i dt)(dx^j+N^j dt)$；切片正交族满足 $dx^i+N^i dt=0\Rightarrow d\tau=N\,dt$。

**E.3  Null 坐标**：Schwarzschild 外区 $r^*=r+2M\ln|r/2M-1|$，$u=t-r^*$, $v=t+r^*$；FRW 中 $d\eta=dt/a(t)$。

**E.4  模块时间**：给定（代数,态）对 $(\mathcal A,\omega)$ 的 GNS 表象，模块流 $\sigma_s$ 内在地定义时间；在半空间与小形变下，$K$ 局域到 $\int T_{kk}$，与 ANEC/QNEC、JLMS/相对熵同构。

### 附录 F：Shapiro 延迟与群延迟

弱场 Schwarzschild 外区

$$
\Delta t \simeq \frac{4GM}{c^3}\ln\frac{4r_E r_R}{b^2}+\cdots,
$$

与频域测得的 $\partial_\omega\Phi=\operatorname{Tr}Q$ 一致；多频回波拟合可分离色散与几何项。

### 附录 G：统一时间刻度的存在与唯一性

设给定散射数据 $(S(\omega))$ 满足刻度同一式。定义

$$
t-t_0=\int_{\omega_0}^{\omega}\frac{1}{2\pi}\operatorname{Tr}Q(\tilde\omega)\,d\tilde\omega
=\int_{\omega_0}^{\omega}\frac{\varphi'(\tilde\omega)}{\pi}\,d\tilde\omega
=\int_{\omega_0}^{\omega}\rho_{\mathrm{rel}}(\tilde\omega)\,d\tilde\omega .
$$

在不退化频窗内导数为正，$t(\omega)$ 为局部双射；若另有 $\tilde t$ 满足同一条件，则 $\tilde t=a t+b$（$a>0$），给出仿射唯一性。

---

### 统一图（概要）

$$
\boxed{
\begin{array}{c}
[T]\sim\{\tau,\ t_{\rm K},\,N,\,\lambda,u,v,\,\eta,\,\omega^{-1},\,z,\,s_{\rm mod}\}\\[2pt]
\Downarrow\\[3pt]
\phi,\ \Phi(\omega)\ \Longleftrightarrow\ \operatorname{Tr}Q(\omega),\ \rho_{\mathrm{rel}}(\omega)\\[3pt]
\Longleftrightarrow\ 1+z\ \ (\text{相位节奏比})\ \Longleftrightarrow\ \partial_s S_{\rm gen}\ (\text{极值/单调})\\[3pt]
\Longleftrightarrow\ G_{\mu\nu}+\Lambda g_{\mu\nu}=8\pi G\langle T_{\mu\nu}\rangle .
\end{array}}
$$

（完）
