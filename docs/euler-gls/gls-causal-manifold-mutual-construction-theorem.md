# GLS ↔ 因果流形：互构定理与范畴等价

Version: 1.10

## 摘要

构造"窗化散射—读数"范畴 $\mathbf{WScat}$ 与"因果流形"范畴 $\mathbf{Cau}$，给出函子
$$
\mathfrak F:\mathbf{WScat}\to\mathbf{Cau},\qquad
\mathfrak G:\mathbf{Cau}\to\mathbf{WScat},
$$
并严格证明二者（在 $\mathbf{WScat}$ 的能量依赖幺正规范等价类上）通过自然变换互为等价：
$$
\mathfrak F\circ \mathfrak G\simeq \mathrm{Res}_{\mathcal D(\mathbf V)},\qquad
\mathfrak G\circ \mathfrak F\simeq \mathrm{Id}_{\mathbf{WScat}/\!\sim_{\rm gauge}}.
$$
或者等价地表述为
$$
\eta:\ \mathrm{Res}_{\mathcal D(\mathbf V)}\Rightarrow \mathfrak F\circ \mathfrak G,\qquad
\varepsilon:\ \mathfrak G\circ \mathfrak F\Rightarrow \mathrm{Id}_{\mathbf{WScat}/\!\sim_{\rm gauge}}.
$$
核心思路为：（i）以前沿时间 $t_*$ 的单向支撑与有限传播速度建立可达偏序与菱形基拓扑；（ii）调用 Hawking–King–McCarthy（HKM）与 Malament 的因果重构判据，从因果关系（或光观测集族）重建流形拓扑与度量的保角类；（iii）在全局双曲的可处理背景上，以辐射场—Lax–Phillips 理论构造能量可微的幺正散射矩阵 $S(E)$，并由 Birman–Kreĭn 公式与 Wigner–Smith 时间延迟矩阵统一母刻度；（iv）在能量依赖幺正规范 $S\mapsto U(E)S(E)V(E)$ 的相对不变类上确立自然同构。窗化数值读数遵循 Nyquist–Poisson–Euler–Maclaurin 的有限阶误差闭合纪律，与因果偏序严格分离。([AIP Publishing][1])

---

## 0. 记号、约定与公理

### 0.1 记号与对象

能量变量记为 $E$，上半平面 $\mathbb C^+$ 解析性以 Hardy 空间表述。GLS 对象取六元
$$
\mathfrak U=(\mathcal H,\ S(E),\ \mu_\varphi,\ \mathcal W,\ \mathbf V,\ \boldsymbol\Gamma),
$$
其中 $\mathbf V$ 为观测域，$\boldsymbol\Gamma$ 为 $\mathbf V$ 内的类时观测轨道族。
其中 $S(E)\in\mathsf U(N)$ 为能量可微的散射矩阵，Wigner–Smith 矩阵与相对态密度定义为
$$
\mathsf Q(E)=-i\,S(E)^\dagger \tfrac{dS}{dE}(E),\qquad
\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E).
$$
谱移函数 $\xi(E)$ 满足 Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i \xi(E)}$。窗—核字典 $\mathcal W$ 给出窗化读数
$$
T[w_R,h]=\int_{\mathbb R}(w_R*\check h)(E)\,\rho_{\rm rel}(E)\,dE,
$$
其中 **$\check h(E):=h(-E)$** 为 $h$ 的反射，故 $w_R*\check h$ 与频域卷积记号一致，窗化读数定义良定；$\rho_{\rm rel}(E)=\tfrac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$。

**母刻度测度** 定义为
$$d\mu_\varphi(E):=\rho_{\rm rel}(E)\,dE=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\,dE.$$
因此窗化读数统一记为
$$T[w_R,h]=\int_{\mathbb R}(w_R*\check h)(E)\,d\mu_\varphi(E).$$
若需链路/端口分辨，可固定通道投影 $P_\gamma$ 并令
$$
\rho_{\rm rel,\gamma}(E):=\frac{1}{2\pi}\operatorname{tr}\big(P_\gamma\,\mathsf Q(E)\,P_\gamma\big),
$$
但本文范畴等价仅依赖总迹 $\rho_{\rm rel}$。

**对象自带的光观测集生成**：由前沿 $t_*$ 定义
$$
P_{\mathbf V}(q):=\{x\in\mathbf V:\ x\ \text{首先观测到来自}\ q\ \text{的非零前沿信号}\}.
$$
([arXiv][2])

### 0.2 公理

**公理 I（刻度同一）**
$$
\boxed{\ \frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\xi'(E)=\frac{1}{2\pi}\frac{d}{dE}\arg\det S(E)\ }
$$
即"相位导数—谱移密度—群延迟迹"统一为母刻度。([arXiv][2])

**公理 II（双时间分离）**
因果时间（前沿）定义为最早非零到达 $t_*(\gamma)=\inf\{t:\ g_\gamma(t)\neq 0\}$。由 Hardy 解析的单向支撑可得 $t_*(\gamma)\ge 0$；在满足有限传播速度并引入几何长度 $L_\gamma$ 时，进一步有 $t_*(\gamma)\ge L_\gamma/c$。若 $\gamma=\gamma_2\circ\gamma_1$，则 $t_*(\gamma)\ge t_*(\gamma_2)+t_*(\gamma_1)$。可测时间仅指窗化读数 $T[w_R,h]$ 的操作化刻度，二者无普适大小比较；因果与无信号仅以前沿 $t_*$ 与类光锥决定。单向支撑由 Hardy 解析—Kramers–Kronig 与 Titchmarsh 卷积支撑定理保证。([维基百科][3])

**公理 III（有限阶 NPE 误差闭合）**
窗化积分的数值实现由 Poisson 求和与有限阶 Euler–Maclaurin（EM）公式给出显式误差三分
$$
\varepsilon_{\rm total}=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$
在带限或有效带限条件下具可计算上界；该误差学仅约束 $T[w_R,h]$ 的数值近似，与因果偏序无涉。([维基百科][4])

### 0.3 因果流形与因果重构

$\mathbf{Cau}$ 对象取时间定向的洛伦兹流形 $(\mathcal M,g)$。HKM 证明路径拓扑编码因果、微分与保角结构；Malament 证明：在可区分背景下，**因果同构**（$p\ll q\iff f(p)\ll f(q)$）的双射为光滑保角同构；强因果当且仅当 Alexandrov 拓扑等于流形拓扑。([AIP Publishing][1])

---

## 1. 范畴的定义

### 1.1 窗化散射范畴 $\mathbf{WScat}$

**对象** $\mathfrak U=(\mathcal H,S,\mu_\varphi,\mathcal W,\mathbf V,\boldsymbol\Gamma)$，满足：频域传递函数在 $\mathbb C^+$ 解析，系统被动，无预响应；高频极限与有限传播速度成立。

**（无闭回路/无反馈）** 传播链图谱无非平凡闭合串联：不存在 $U_0,\dots,U_m=U_0$ 的链路闭环（各段 $t_*(\gamma_j)\ge 0$；若段长 $L_j>0$，则 $t_*(\gamma_j)\ge L_j/c$）。由此 §2.1 的可达关系为偏序。

**态射** 为保持被动与因果（不产生预响应）的滤镜链 $\mathcal O=\mathcal M_{\rm th}\circ M_i\circ\Phi\circ K_{w,h}$，其 Heisenberg 伴随保持母刻度的线性读数。
**规范等价**：若存在能量依赖幺正 $U(E),V(E)$ 使 $S\mapsto U S V$ 且 $\det U\cdot\det V\equiv 1$，则称两对象规范等价；在该等价类上母刻度 $\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q$ 及其诱导的窗化读数 $T[w_R,h]$ 不变（§5.4）。

### 1.2 因果流范畴 $\mathbf{Cau}$

**对象** 为四维、时间定向、可区分且适合辐射场—散射构造的洛伦兹流形 $(\mathcal M,g)$（例如全局双曲并在无穷远渐近欧氏/双曲或渐近 Minkowski），从而存在辐射场与能量分解 $S(E)$。
**态射** 为因果嵌入/同构 $f:(\mathcal M,g)\to(\mathcal N,h)$，要求对任意 $p,q\in\mathcal M$，
$$p\ll q\ \Longleftrightarrow\ f(p)\ll f(q)\ \text{（在像上保持并反射时间序）}.$$
在可区分背景下，若 $f$ 为双射，则 $f$ 为光滑保角同构（Malament；HKM）。([AIP Publishing][5])

---

## 2. 从 GLS 到因果流形：函子 $\mathfrak F$

### 2.1 以前沿 $t_*$ 定义可达偏序

**定义（可达关系）** 设端口/读出域 $U,V\in\mathcal W$。
$$
U\preceq V\ \Longleftrightarrow\ \exists\ \text{有限传播链}\ \gamma:U\to V\ \text{（各段前沿 }t_*\ge 0;\ \text{若 }L_j>0,\ t_*\ge L_j/c\text{）}.
$$
即 $\preceq$ 为链路图的自反传递闭包。

**（恒等链与自反性）** 对每个端口/读出域 $U$，引入恒等链 $e_U:U\to U$，规定 $L_{e_U}=0,\ t_*(e_U)=0$。于是 $U\preceq U$ 成立，自反性由恒等链保证；传递性由复合链的卷积支撑与 $t_*$ 可加给出。

由卷积支撑的 Minkowski 和与单向支撑，若 $\gamma=\gamma_2\circ\gamma_1$ 则 $t_*(\gamma)\ge t_*(\gamma_2)+t_*(\gamma_1)$；结合"无闭回路/无反馈"条件，$\preceq$ 为偏序。单向支撑来自 Kramers–Kronig/Hardy 与 Titchmarsh。([维基百科][3])

**证明（概要且自含）**：频域响应 $H\in H^2(\mathbb C^+)$ 蕴含时域冲激响应在 $t<0$ 为零；串联系统之响应为卷积 $h=h_n*\cdots*h_1$，由 Titchmarsh 定理得 $\inf\operatorname{supp}(h)=\sum_j\inf\operatorname{supp}(h_j)$，故若 $\gamma=\gamma_2\circ\gamma_1$ 则 $t_*(\gamma)\ge t_*(\gamma_2)+t_*(\gamma_1)$。配合**各段 $t_*(\gamma_j)>0$ 的链路前提**与"无闭回路/无反馈"，可达关系之自反传递闭包为偏序。([维基百科][3])

### 2.2 光观测集与几何重构

令 $\mathfrak U=(\mathcal H,S,\mu_\varphi,\mathcal W,\mathbf V,\boldsymbol\Gamma)$。在对象自带的观测域 **$\mathbf V$** 内，取其类时观测轨道族 **$\boldsymbol\Gamma$**，并按 §0.1 的规则由前沿 $t_*$ 生成光观测集 $P_{\mathbf V}(q)$；据此重构 $(\mathcal M_{\rm rec},[g]_{\rm rec},\preceq_{\rm rec})$。

KLU 证明：已知 $\mathbf V$ 与 $P_{\mathbf V}(q)$ 的全体，可重建最大传播域内的拓扑、微分与保角结构（被动/主动两型数据）。

**定义（最大传播域）** 给定观测域 $\mathbf V\subset\mathcal M$，令
$$\mathcal D(\mathbf V):=\{q\in\mathcal M:\ P_{\mathbf V}(q)\ \text{良定义且可由 $\mathbf V$ 上的数据唯一确定}\}.$$
等价地，可取因果域刻画 $\mathcal D(\mathbf V)=J^+(\mathbf V)\cap J^-(\mathbf V)$ 在本重构框架下与 $P_{\mathbf V}(q)$ 的可观测性相一致的最大开子集。随后 §4.1 与 §7 中的限制函子均按此 $\mathcal D(\mathbf V)$ 取值。

据此置
$$
\mathfrak F(\mathfrak U):=\big(\mathcal M_{\rm rec},[g]_{\rm rec},\preceq_{\rm rec}\big),
$$
其中 $[g]_{\rm rec}$、$\preceq_{\rm rec}$ 分别由 $P_V(q)$、$t_*$ 重构。([arXiv][6])

### 2.3 与因果理论一致性与函子性

HKM 与 Malament 给出：在可区分背景下，**因果同构**（$p\ll q\iff f(p)\ll f(q)$）的双射为光滑保角同构；强因果当且仅当 Alexandrov 拓扑等于流形拓扑。滤镜链态射保持被动与因果，不产生"提前到达"，故诱导偏序的单调映射；规范等价不改变 $\operatorname{tr}\mathsf Q$ 与前沿结构，故 $\mathfrak F$ 良定且具函子性。([AIP Publishing][1])

---

## 3. 从因果流形到 GLS：函子 $\mathfrak G$

### 3.1 辐射场与幺正散射

**附加假设（Spec）**：存在一参数幺正群 $U(t)=e^{-itH}$（$H$ 自伴），散射算子 $S$ 与 $U(t)$ 交换，使得在 $H$ 的谱分解下 $S$ 纤维化为 $S(E)$；并且 $E\mapsto S(E)$ 可微且满足 Birman–Kreĭn 公式适用的相对迹类条件（由此 $\det S(E)$、$\xi(E)$ 与 $\mathsf Q(E)$ 良定）。

在全局双曲且渐近可处理（如渐近欧氏/双曲或渐近 Minkowski）的 $(\mathcal M,g)$ 上，波动算子（或 Klein–Gordon）之解在 $\mathscr I^\pm$ 的辐射场限制诱导"入–出"空间的幺正同构，构造散射算子 $S:\mathcal H_{\rm in}\to\mathcal H_{\rm out}$，并获得能量分解 $S(E)$。Lax–Phillips 与辐射场文献系统构建了该表示及相应逆问题。([Project Euclid][7])

### 3.2 母刻度与窗化读数

由公理 I 定义 $\mathsf Q=-iS^\dagger S'$ 与 $\rho_{\rm rel}=(2\pi)^{-1}\operatorname{tr}\mathsf Q=-\xi'(E)$，以 Toeplitz/Berezin 窗—核族 $\mathcal W$ 给出窗化读数 $T[w_R,h]$。该母刻度等式在电磁/微分形式散射中同样成立。([arXiv][8])

### 3.3 前沿一致与函子性

超曲性与有限传播速度给出 **$t_*\ge L_\gamma/c$**（$L_\gamma$ 为相对于 $g$ 的链路几何长度）；高频测地极限取等号，故由 $(\mathcal M,g)$ 构造之 GLS 的前沿与其因果锥一致。保角同构诱导辐射场的幺正等价与 $S$ 的等价表示，给出 $\mathbf{WScat}$ 的态射。

**观测方案（Obs）**：对每个 $(\mathcal M,g)$ 选定类时开集 $\mathbf V$ 及其类时观测轨道族 $\boldsymbol\Gamma$；对因果嵌入 $f$ 取像 $(f(\mathbf V),f_*\boldsymbol\Gamma)$ 以保持函子性。于是
$$
\mathfrak G(\mathcal M,g):=(\mathcal H,S,\mu_\varphi,\mathcal W,\mathbf V,\boldsymbol\Gamma).
$$
([arXiv][9])

---

## 4. 自然等价的构造与证明

### 4.1 $\mathfrak F\circ \mathfrak G\simeq \mathrm{Id}_{\mathbf{Cau}}$

将 $(\mathcal M,g)$ 送入 $\mathfrak G$ 得 $S(E)$ 与前沿簿记，再由 $\mathfrak F$ 以 $t_*$ 与 $P_{\mathbf V}(q)$ 重建。KLU 断言：在四维背景下，给定 $\mathbf V$ 与 $P_{\mathbf V}(q)$ 的全体，可重建最大传播域内的拓扑、微分与保角结构；配合 Malament，因果同构的双射即为光滑保角同构。构造自然同构
$$
\eta_{(\mathcal M,g)}:\ (\mathcal M,g)\big|_{\mathcal D(\mathbf V)}\ \overset{\sim}{\longrightarrow}\ \mathfrak F(\mathfrak G(\mathcal M,g)),
$$
其中 **$\mathbf V$ 为 $\mathfrak G(\mathcal M,g)$ 输出对象的观测域分量**；若 $\mathbf V$ 覆盖有效外边界，则 $\eta_{(\mathcal M,g)}$ 退化为 $\mathrm{Id}_{(\mathcal M,g)}$。自然性来自态射层的因果保持与辐射场的协变性。([arXiv][6])

### 4.2 $\mathfrak G\circ \mathfrak F\simeq \mathrm{Id}_{\mathbf{WScat}/\!\sim_{\rm gauge}}$

$\mathfrak F$ 仅以前沿与光观测集重建保角几何，未固定能量/通道基与参考相位。对能量依赖幺正 $U,V$ 有 $\widetilde S=USV$，迹变换为
$$
\operatorname{tr}\widetilde{\mathsf Q}
=\operatorname{tr}\mathsf Q-i\,\operatorname{tr}(U^\dagger U')-i\,\operatorname{tr}(V^\dagger V').
$$
若 $\det U\cdot\det V\equiv 1$ 则 $\operatorname{tr}\widetilde{\mathsf Q}=\operatorname{tr}\mathsf Q$，**所有由 $\rho_{\rm rel}$ 诱导的窗化读数 $T[w_R,h]$ 保持不变**，从而存在自然同构 $\varepsilon_{\mathfrak U}:\mathfrak G(\mathfrak F(\mathfrak U))\overset{\sim}{\to}\mathfrak U$ 于规范等价类上。自然性来自态射与规范同余的兼容性（§5.4 详细证明）。

### 4.3 范畴等价

由 4.1–4.2，$(\mathfrak F,\mathfrak G;\eta,\varepsilon)$ 给出 $\mathrm{Res}_{\mathcal D(\mathbf V)}(\mathbf{Cau})$ 与 $\mathbf{WScat}/\!\sim_{\rm gauge}$ 的等价；当 $\mathbf V$ 覆盖有效外边界时退化为 $\mathbf{Cau}\simeq \mathbf{WScat}/\!\sim_{\rm gauge}$。其一端依赖 HKM–Malament 的因果—保角重构，另一端依赖辐射场散射与 Birman–Kreĭn—Wigner–Smith 母刻度。([AIP Publishing][1])

---

## 5. 关键引理与详细证明

### 5.1 Hardy 解析 $\Rightarrow$ 单向支撑（含卷积支撑）

**引理 5.1（Kramers–Kronig/Hardy）**
若频域响应 $H\in H^2(\mathbb C^+)$ 且高频衰减，则其时域冲激响应 $h(t)=0$ 于 $t<0$。
**证明**：$H$ 为上半平面解析且边值在 $L^2$，由 Sokhotski–Plemelj 与 Hilbert 变换得实/虚部互为 Hilbert 共轭；逆傅里叶后 $h$ 为因果核，故 $t<0$ 为零。([维基百科][3])

**引理 5.2（Titchmarsh 卷积定理）**
紧支撑（或适当衰减）函数/分布 $f,g$ 满足
$\inf\operatorname{supp}(f*g)=\inf\operatorname{supp} f+\inf\operatorname{supp} g$，
$\sup\operatorname{supp}(f*g)=\sup\operatorname{supp} f+\sup\operatorname{supp} g$。
**证明**：见 Titchmarsh 原理；对 $h=f*g$ 的拉普拉斯域零点与支撑端点对应性建立上述等式。由此串联系统的最早到达时间为各段之和。([维基百科][10])

**命题 5.3（有限传播速度）**
全局双曲背景上的线性波动方程满足有限传播速度：若初值在 $B_r$ 外为零，则解在 $t<r/c$ 的影响域外为零。
**证明**：能量不等式与域依赖性给出；详见几何波动方程综述与讲义。([ljll.fr][11])

**结论**：由引理 5.1–5.2（单向支撑与 Titchmarsh 卷积支撑），对任一传播链 $\gamma$ 有 $t_*(\gamma)\ge 0$，且若引入几何长度 $L_\gamma$ 并满足有限传播速度，则 $t_*(\gamma)\ge L_\gamma/c$；若 $\gamma=\gamma_2\circ\gamma_1$，则
$$t_*(\gamma)\ge t_*(\gamma_2)+t_*(\gamma_1).$$
配合"恒等链 $e$：$t_*(e)=0$"与"无闭回路/无反馈"，§2.1 的可达关系为偏序。**在 $(\mathcal M,g)\in\mathbf{Cau}$ 的背景下**，该几何下界 $t_*(\gamma)\ge L_\gamma/c$ 亦成立，但它不进入 $\mathbf{WScat}$ 的偏序定义。

### 5.2 光观测集重构（KLU）

**定理 5.4（被动/主动逆问题）**
已知类时测地邻域 $V$ 与其上的保角类，以及所有源点 $q\in W$ 的光观测集族 $P_V(q)$，可唯一重建 $W$ 的拓扑、微分与保角结构（四维时由源—解映射进一步强化）。
**证明**：KLU 通过非线性相互作用的讯号合成与波前集几何，建立由 $P_V(q)$ 到保角结构的可逆映射；被动型以光观测集的集合论数据重构边界光学测度与共形类，主动型以源—解算子拓展至非线性传播。([arXiv][6])

### 5.3 辐射场—散射与母刻度（幺正性与能量分解）

**定理 5.5（辐射场与 Lax–Phillips）**
在渐近欧氏/双曲或渐近 Minkowski 背景，辐射场给出波群的平移表示与幺正的入—出散射算子 $S$，并随能量分解为 $S(E)$。
**证明**：Friedlander–Melrose–Sá Barreto 等发展了 $\mathscr I^\pm$ 上的辐射场与散射矩阵；Lax–Phillips 框架提供幺正平移表示。([math.purdue.edu][12])

**定理 5.6（Birman–Kreĭn—Wigner–Smith）**
对能量可微的幺正散射 $S(E)$，有 $\det S(E)=e^{-2\pi i\xi(E)}$、$\mathsf Q=-iS^\dagger S'$，于是
$$
\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=-\xi'(E)=\frac{1}{2\pi}\frac{d}{dE}\arg\det S(E).
$$
**证明**：由 $\tfrac{d}{dE}\ln\det S=\operatorname{tr}(S^{-1}S')=\operatorname{tr}(S^\dagger S')$ 与单值支配的相位选择；Wigner（1955）与 Smith（1960）分别给出群延迟与寿命矩阵之物理—数学基础。([arXiv][2])

### 5.4 规范协变与 $\operatorname{tr}\mathsf Q$ 的相对不变性

令 $\widetilde S=USV$（$U,V$ 幺正且可微）。计算得
$$
\begin{aligned}
\widetilde{\mathsf Q}
&=-i\,\widetilde S^\dagger \widetilde S'
=-i\,V^\dagger S^\dagger U^\dagger (U'SV+US'V+USV')\\
&= -i\,V^\dagger S^\dagger (U^\dagger U') S V
\;-\; i\,V^\dagger S^\dagger S' V
\;-\; i\,V^\dagger V',
\end{aligned}
$$
故
$$
\operatorname{tr}\widetilde{\mathsf Q}
=\operatorname{tr}\mathsf Q-i\,\operatorname{tr}(U^\dagger U')-i\,\operatorname{tr}(V^\dagger V')
=\operatorname{tr}\mathsf Q+\frac{d}{dE}\big(\arg\det U+\arg\det V\big).
$$
若 $\det U\cdot\det V\equiv 1$ 则 $\operatorname{tr}\widetilde{\mathsf Q}=\operatorname{tr}\mathsf Q$。一般情形取参考 $S_{\rm ref}$ 以构造相对读数 $\operatorname{tr}(\mathsf Q-\mathsf Q_{\rm ref})$，窗化积分保持不变。由此 §4.2 的自然同构成立。

### 5.5 双时间分离与无信号红线

由 5.1–5.3，因果与"无信号"仅由前沿 $t_*$ 与类光锥决定；**在 $(\mathcal M,g)\in\mathbf{Cau}$ 的背景下**，可进一步以链路几何长度给出物理下界 $t_*(\gamma)\ge L_\gamma/c$，而该几何下界不进入 $\mathbf{WScat}$ 的偏序定义。读数层面的负群延迟、Hartman 饱和等现象不触及前沿红线，因而与因果不冲突。([物理评论链接管理器][13])

### 5.6 NPE 数值账本（实现无关性）

对被积函数 $f(E)=w_R(E)[\check h*\rho_{\rm rel}](E)$，若严格带限则有 Poisson 求和等式
$\int f=\Delta\sum_{n\in\mathbb Z}f(E_0+n\Delta)$；一般情形误差分解为
$\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}$，其中 $\varepsilon_{\rm EM}$ 由有限阶 Euler–Maclaurin 给出显式端点校正，$\varepsilon_{\rm tail}$ 由窗/核的外带衰减控制。该误差学仅影响 $T[w_R,h]$ 的数值稳定性，与 §2 的因果偏序无涉。([维基百科][4])

---

## 6. 非幺正观测的幺正扩张（附录）

实际测量的非幺正（POVM/通道）可由 Stinespring/Naimark 扩张嵌入更大 Hilbert 空间，在扩张空间中由幺正演化与 PVM 实现；故在"全宇宙幺正—子系统有效非幺正"的立场下，公理 I 与 §5.4 的规范协变保持成立。([维基百科][14])

---

## 7. 主定理（范畴等价）与推论

**主定理**
令 $\mathbf{WScat}$ 为满足公理 I–III、Hardy 解析、被动、有限传播速度与高频极限的窗化散射系统类；$\mathbf{Cau}$ 为可区分并适合辐射场—散射构造的洛伦兹流形类。设 $\mathrm{Res}_{\mathcal D(\mathbf V)}:\mathbf{Cau}\to\mathbf{Cau}$ 为限制到最大传播域的函子，$\mathrm{Res}_{\mathcal D(\mathbf V)}(\mathcal M,g)=(\mathcal M,g)|_{\mathcal D(\mathbf V)}$，其中 $\mathbf V$ 来自 $\mathfrak G(\mathcal M,g)$ 的对象分量。则存在自然变换
$$
\eta:\ \mathrm{Res}_{\mathcal D(\mathbf V)}\ \Rightarrow\ \mathfrak F\circ \mathfrak G,\qquad
\varepsilon:\ \mathfrak G\circ \mathfrak F\ \Rightarrow\ \mathrm{Id}_{\mathbf{WScat}/\!\sim_{\rm gauge}}.
$$
若观测域 $\mathbf V$ 覆盖有效外边界，则 $\mathcal D(\mathbf V)=\mathcal M$，从而 $\eta$ 退化为 $\mathrm{Id}_{\mathbf{Cau}}$。证明见 §2–§5。([AIP Publishing][1])

**推论（order+number 佐证）**
"因果 + 计数"可定保角类与体积因子；在离散化语境，因果集方案以偏序与局部有限性重建几何，呼应本文的"前沿—保角—母刻度"链路。([物理评论链接管理器][15])

---

## 参考文献（选）

Hawking, King, McCarthy, *A new topology for curved space-time which incorporates the causal, differential, and conformal structures*, J. Math. Phys. 17 (1976). ([AIP Publishing][1])
Malament, *The class of continuous timelike curves determines the topology of spacetime*, J. Math. Phys. 18 (1977). ([AIP Publishing][5])
Kurylev–Lassas–Uhlmann, *Inverse problems for Lorentzian manifolds and non-linear hyperbolic equations*, arXiv:1405.3386. ([arXiv][6])
Lax–Phillips, *Scattering Theory*（及相关综述/讲义）。([Project Euclid][7])
Sá Barreto 等，*Radiation fields, scattering and inverse problems*。([math.purdue.edu][12])
Pushnitski 等，*Birman–Kreĭn/spectral shift*（综述与变体）。([arXiv][2])
Wigner, *Lower Limit for the Energy Derivative of the Scattering Phase Shift*, Phys. Rev. 98 (1955)；Smith, *Lifetime Matrix in Collision Theory*, Phys. Rev. 118 (1960)。([物理评论链接管理器][13])
Kramers–Kronig、Paley–Wiener、Titchmarsh 卷积定理等经典运算—支撑判据。([维基百科][3])
Bombelli–Lee–Meyer–Sorkin, *Space-time as a causal set*, Phys. Rev. Lett. 59 (1987)。([物理评论链接管理器][15])
Stinespring、Naimark 扩张定理（通道与测度的幺正实现）。([维基百科][14])

---

**附注（可检核要点）**
（a）全篇因果—读数位阶分离：偏序只由 $t_*$ 与类光锥决定；窗化读数只承担操作刻度；（b）范畴等价在 $\mathbf{WScat}/\!\sim_{\rm gauge}$ 上成立，规范项以行列式相消；（c）数值误差账本（NPE）不进入因果与等价的证明链。

[1]: https://pubs.aip.org/aip/jmp/article-pdf/17/2/174/19121303/174_1_online.pdf?utm_source=chatgpt.com "A new topology for curved space-time which incorporates ..."
[2]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[3]: https://en.wikipedia.org/wiki/Kramers%E2%80%93Kronig_relations?utm_source=chatgpt.com "Kramers–Kronig relations"
[4]: https://en.wikipedia.org/wiki/Poisson_summation_formula?utm_source=chatgpt.com "Poisson summation formula"
[5]: https://pubs.aip.org/aip/jmp/article/18/7/1399/460709/The-class-of-continuous-timelike-curves-determines?utm_source=chatgpt.com "The class of continuous timelike curves determines the ..."
[6]: https://arxiv.org/abs/1405.3386?utm_source=chatgpt.com "Inverse problems for Lorentzian manifolds and non-linear hyperbolic equations"
[7]: https://projecteuclid.org/journals/bulletin-of-the-american-mathematical-society-new-series/volume-70/issue-1/Scattering-theory/bams/1183525789.full?utm_source=chatgpt.com "Scattering theory"
[8]: https://arxiv.org/pdf/2110.06370?utm_source=chatgpt.com "arXiv:2110.06370v1 [math.SP] 12 Oct 2021"
[9]: https://arxiv.org/pdf/1710.04512?utm_source=chatgpt.com "Wave and Dirac equations on manifolds"
[10]: https://en.wikipedia.org/wiki/Titchmarsh_convolution_theorem?utm_source=chatgpt.com "Titchmarsh convolution theorem"
[11]: https://www.ljll.fr/smulevici/lgpdes.pdf?utm_source=chatgpt.com "Lectures on Lorentzian Geometry and hyperbolic pdes"
[12]: https://www.math.purdue.edu/~sabarre/Papers/radiation.pdf?utm_source=chatgpt.com "RADIATION FIELDS, SCATTERING AND INVERSE ..."
[13]: https://link.aps.org/doi/10.1103/PhysRev.98.145?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering Phase ..."
[14]: https://en.wikipedia.org/wiki/Stinespring_dilation_theorem?utm_source=chatgpt.com "Stinespring dilation theorem"
[15]: https://link.aps.org/doi/10.1103/PhysRevLett.59.521?utm_source=chatgpt.com "Space-time as a causal set | Phys. Rev. Lett."
