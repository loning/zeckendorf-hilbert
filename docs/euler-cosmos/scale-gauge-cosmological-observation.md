# 尺度规范化宇宙观测理论

**——"膨胀≡分辨率提升"的严格等价、公理化读数、相对论重述、信息边界与图灵语义**

Version: 1.15

## 摘要

建立一套以尺度规范（scale gauge, 记作 $a(t)$）与内部观测尺标（c-lock, 记作 $R(t)$）对偶为核心的宇宙观测理论。设 $a(t)=R(t)^{-1}$、$\kappa(t):=\dot a/a=-\dot R/R$，则宇宙学红移与时间伸长统一为能量轴上的 Mellin 伸缩：$1+z=a(t_0)/a(t_e)=R(t_e)/R(t_0)$、$\nu_0=\nu_e/(1+z)$、$\Delta t_0=(1+z)\Delta t_e$。读数全部在"母尺"上对齐：

$$
\boxed{\ \rho(E)=-\xi'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\frac{1}{2\pi i}\,\partial_E\log\det S(E)=\frac{\varphi'(E)}{2\pi}\ ,\ \mathsf Q:=-i\,S^\dagger S'\ },
$$

其中 $\rho$ 为相对态密度，$\mathsf Q$ 为 Wigner–Smith 群延迟矩阵，$\varphi$ 为总散射相位。母尺由 Birman–Kreĭn 公式与群延迟定义等价刻画，给出跨装置可比的刻度统一（单位固定；量纲 $E^{-1}$）。读数误差遵循"Nyquist–Poisson–Euler–Maclaurin（NPE）有限阶闭合"：Nyquist 关断别名、Poisson 求和桥接离散—连续、有限阶 Euler–Maclaurin（EM）以伯努利层与尾项确界封装端点误差。在 Landau 密度门槛与 Wexler–Raz 对偶的帧条件下，缩窗 $r\downarrow$ 保持**奇性不增**；而 Fisher 信息对 $r$ 的单调性与标度**依赖于噪声模型与归一化选择**，一般不存在普适单调或 $r^{-2}$ 下界。保持"光锥 + 母尺"不变的线性稳定子唯一对应洛伦兹群；在 FRW 背景下的统一频移律 $1+z=((k_\mu u^\mu)_e)/((k_\mu u^\mu)_o)$ 导出 Etherington 距离对偶 $D_L=(1+z)^2D_A$ 与 Tolman 面亮度 $(1+z)^{-4}$ 的自然成立。借助可逆因果自动机（RCA/QCA）语义，给出"光""红移""共享主频"及"注意力/行动力资源的 $c$-限速分配"的统一表述。本文区分"规范"与"真动力学"，提出可证伪判据与工程化"分辨率分配矩阵"方法。

---

## 0. 记号、公理与约定（Notation & Axioms / Conventions）

### 0.1 观测对象与散射几何

1. 背景希尔伯特空间 $\mathcal H$；能量参量 $E\in\mathbb R$。
2. 散射矩阵 $S(E)$ 与 Wigner–Smith 矩阵 $\mathsf Q(E)=-i\,S^\dagger(E)\,\partial_E S(E)$。
3. 总散射相位 $\varphi(E)=\arg\det S(E)$。
4. **三位一体母尺**：
   $$
   \rho(E):=-\xi'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\frac{1}{2\pi i}\partial_E\log\det S(E)=\frac{\varphi'(E)}{2\pi}\,,
   $$
   其等价来自 Birman–Kreĭn 公式 $\det S(E)=e^{-2\pi i\,\xi(E)}$（其中 $\xi(E)$ 为谱位移函数）与群延迟定义；因此 $\rho(E)=-\xi'(E)$ 成立。上述关系在广义散射与几何设置中成立。([arXiv][1])

### 0.2 尺度规范 / c-lock

外部尺度因子 $a(t)$ 与内部观测尺标 $R(t)$ 满足

$$
a(t)=R(t)^{-1},\qquad \kappa(t):=\frac{\dot a}{a}=-\frac{\dot R}{R}.
$$

设内部主频 $f_{\rm clk}(t):=\dfrac{c}{\ell_{\rm clk}(t)}=\dfrac{c}{R(t)\,\ell_*}$，其中 $\ell_*$ 为固定母尺长度常数、$R(t)$ 为无量纲内部尺标且满足 $a(t)=R(t)^{-1}$。任何"提分辨率"操作指 $r\downarrow$ 或采样密度 $\mathrm{dens}(\Lambda)\uparrow$。

### 0.3 NPE 有限阶闭合（非渐近）

* **Nyquist**：带限目标在采样率超过两倍带宽时别名项为零；非带限情形下别名项显式入账。([维基百科][2])
* **Poisson**：离散—连续桥接以 Poisson 求和式实现，允许将格点和卷积切换到频域的梳状谱。([dlmf.nist.gov][3])
* **Euler–Maclaurin（有限阶）**：以伯努利多项式给出端点层与尾项界，截断阶 $p$ 固定、误差上界可审计。([dlmf.nist.gov][4])

**误差记号定义**：记 $\varepsilon_{\rm alias}(r)\ge 0$ 为经 Poisson 求和式引入之**别名项**的 $L^1$-上界；当满足 Nyquist 条件时 $\varepsilon_{\rm alias}(r)=0$。记 $\varepsilon_{\rm EM}(\delta;r;p)\ge0$ 为以固定阶 $p$ 截断 Euler–Maclaurin 公式后的"端点层+尾项"账本（$\delta$ 为采样步长/等效网格间距）。存在常数 $C_{2p}(r)$ 使

$$
\varepsilon_{\rm EM}(\delta;r;p)\ \le\ C_{2p}(r)\,\delta^{2p}.
$$

一般情形**不主张**与 $r$ 的普适幂次关系；若进一步给出 $w\in W^{2p,1}$、$h*\rho\in L^1_{\rm loc}$ 等正则性，则可推出 $C_{2p}(r)\lesssim r^{-2p}$，因而 $\varepsilon_{\rm EM}(\delta;r;p)=O(\delta^{2p}r^{-2p})$ 为**模型依赖**结论。下文若未显式给出 $p$，均指固定有限阶。上述阶次界成立需假设 $h*\rho$ 在工作紧域的厚化 $K^\uparrow$（其中 $K^\uparrow:=K+\operatorname{supp}(w_r*h)$）上为分片 $C^{2p}$ 且相应导数有界；**或**在较弱的 $BV$ 假设下，将**全部跳跃**贡献并入伯努利端点层后再作估计（此时仅能得到 $BV$ 版本的上界，**不与分片 $C^{2p}$ 等价**）。超出该正则性范围时，本文不主张该阶次。

### 0.4 帧与密度门槛

采用 Gabor/Weyl–Heisenberg 框架：对窗 $w$ 与格点 $\Lambda$，要求 Landau 必要密度与 Wexler–Raz 对偶以保证稳定可逆重建。([numdam.org][5])

---

## 1. 膨胀≡分辨率提升：Mellin 伸缩与统一频移

### 定义 1（尺度规范）

称 $(a,R)$ 满足 $a(t)=R(t)^{-1}$ 的选择为**尺度规范**。在该规范下，外部"膨胀"与内部"分辨率提升"严格等价为能量轴的 Mellin 伸缩。

### 定理 1（红移—伸长等价）

对同一光子在发射 $t_e$ 与观测 $t_0$ 的读数，有

$$
1+z=\frac{a(t_0)}{a(t_e)}=\frac{R(t_e)}{R(t_0)},\qquad
\nu_0=\frac{\nu_e}{1+z},\qquad
\Delta t_0=(1+z)\Delta t_e .
$$

**证明要点**：在 FRW 度规中，频率为 $\omega=-k_\mu u^\mu$，故 $1+z=((k_\mu u^\mu)_e)/((k_\mu u^\mu)_o)$；而 $k^\mu$ 沿零测地方向平行移动给出 $\omega\propto a^{-1}$。代入 $a=R^{-1}$ 即得。([arXiv][6])

### 命题 1（Etherington 对偶与 Tolman 衰减）

若光子数守恒、几何由度规引力描述且光行唯一零测地，则

$$
D_L=(1+z)^2D_A,\qquad I_{\rm obs}=\frac{I_{\rm em}}{(1+z)^4}.
$$

该结论与尺度规范选择无关，属几何—计数不变式。([维基百科][7])

---

## 2. 相对论的窗化重述：光锥 + 母尺的稳定子

### 定理 2（洛伦兹群 = 稳定子）

保持 Minkowski 光锥结构与母尺不变的**线性**变换群同构于 $SO^+(1,3)$。

**论证**：固定原点（去除平移自由度）后，保因果序的线性自同构群由 $\mathbb R_{+}\times SO^+(1,3)$ 生成；再要求母尺不变（排除整体伸缩），仅余 $SO^+(1,3)$。该结论与 Alexandrov–Zeeman 型定理一致。([math.tecnico.ulisboa.pt][8])

### 命题 2（GR 局域协变化与统一频移）

在流形各点局部平直化"光锥 + 母尺"，由 $\omega=-k_\mu u^\mu$ 得统一频移律

$$
1+z=\frac{(k_\mu u^\mu)_e}{(k_\mu u^\mu)_o},
$$

与测地方程的稳相条件相容，并与 SR/GR 运动学之标准处理一致。([arXiv][9])

---

## 3. 提升分辨率的本质：信息几何与奇性守恒

设**归一化窗** $w_r(x):=\tfrac{1}{r}w(x/r)$，其中 $w\ge0,\ w\in W^{1,1}(\mathbb R)$、$\int_{\mathbb R}w=1$（可选：$\int x\,w(x)\,dx=0$），卷积核 $h$，观测量

$$
g_r(E)=(w_r*h*\rho)(E).
$$

### 命题 3（梯度响应的尺度界与收敛）

设 $w\ge0,\ w\in W^{1,1}(\mathbb R),\ \int w=1$，并且 **$h*\rho\in L^1_{\rm loc}$（或 $BV$）**，令 $g_r=w_r*h*\rho$。对紧域 $K$ 有

$$
|\partial_E g_r|_{L^1(K)}\ \le\ \frac{|w'|_{L^1}}{r}\,|h*\rho|_{L^1(K^\uparrow)}.
$$

**收敛分情形：**

（i）若 $h*\rho\in W^{1,1}(K^\uparrow)$ 且 $w\ge0,\ \int w=1$，则

$$
\lim_{r\downarrow 0}\ |\partial_E g_r-(h*\rho)'|_{L^1(K)}=0,\qquad
|\partial_E g_r|_{L^1(K)}\le |(h*\rho)'|_{L^1(K^\uparrow)}.
$$

（ii）若 $h*\rho\in BV(K^\uparrow)$（不必在 $W^{1,1}$），则

$$
g_r\ \xrightarrow[r\downarrow0]{}\ h*\rho\quad\text{于 }L^1(K),\qquad
|\partial_E g_r|_{L^1(K)}\le \mathrm{TV}(h*\rho;K^\uparrow),
$$

且 $\partial_E g_r\ \stackrel{*}{\rightharpoonup}\ D(h*\rho)$ 于测度空间（弱$^\ast$）意义下。此时不主张 $|\partial_E g_r-(h*\rho)'|_{L^1}$ 收敛。

**NPE 估计器版**（用于离散实现 $\widehat g_r$）：

$$
|\partial_E \widehat g_r|_{L^1(K)}\ \le\ \frac{|w'|_{L^1}}{r}\,|h*\rho|_{L^1(K^\uparrow)}\ +\ \varepsilon_{\rm alias}(r)\ +\ \varepsilon_{\rm EM}(\delta;r;p).
$$

若满足 Nyquist 条件，则 $\varepsilon_{\rm alias}(r)=0$，仅余 EM 端点—尾项账本。

上式体现：减小$r$提高边缘**逼近度**，但不产生普适的$1/r$**下界**增长。其中 $K^\uparrow := K + \operatorname{supp}(w_r * h)$ 表示对紧域 $K$ 按卷积核的有效支撑做的厚化。([dlmf.nist.gov][4])

### 命题 4（Fisher 信息的模型依赖性）

在满足 Nyquist 与 NPE 误差账本（$\varepsilon_{\rm alias},\varepsilon_{\rm EM}$）可审计的前提下，$\mathcal I_r(\theta)$ 对$r$的单调性与标度**依赖于噪声模型与归一化选择**；一般情形下**不存在普适的$r^{-2}$下界或单调性结论**。当噪声统计（如 AWGN/Poisson）与窗归一化（如$\int w=1$或$|w_r|_2$固定）明确后，方可据该模型导出相应的$r$-标度与比较结论。([维基百科][2])

### 定理 3（奇性不增）

合法换窗（$w\mapsto w_r$ 与固定阶 EM 账本）对应的平滑不会**新增**$h*\rho$的奇性；因此在 alias 受控与 EM 误差可审计的条件下，提分辨率不会"制造伪峰"。奇性的**位置与阶次**可能受平滑影响，本文不作不变性主张。([dlmf.nist.gov][3])

---

## 4. 稳定重建与帧门槛

### 定理 4（Landau 必要密度）

带限类 Paley–Wiener 空间的稳定采样需下 Beurling 密度不低于带宽体积常数；若不足，重建条件数爆炸。([numdam.org][5])

### 定理 5（Wexler–Raz 对偶与紧框架）

对 Gabor 系，Wexler–Raz 双正交关系刻画了对偶窗的正交条件；存在参数域使紧框架成立，重建稳健。多窗融合在统计独立近似下将估计方差从 $\sigma^2$ 近似降至 $\sigma^2/K$。([sites.math.duke.edu][10])

### 备注（Balian–Low 障碍）

临界密度的正交基无法同时实现良好时频局域（Balian–Low），提示需用冗余帧而非临界基。([heil.math.gatech.edu][11])

---

## 5. 规范 vs. 真动力学：可证伪指纹

定义宇宙学**状态指纹**：减速 $q:=-\ddot a a/\dot a^2$、jerk $j:=\dddot a/(aH^3)$。定义

$$
\eta(z):=\frac{D_L}{(1+z)^2D_A}.
$$

**判据**：若 $\eta(z)\equiv 1$，且在 NPE 账本闭合与母尺不变下**无新增奇性/伪峰**，则属**规范层一致**；若出现 $\eta(z)\neq 1$ 或**新增奇性/伪峰**，则指向**真动力学/新物理**（如光学深度、非度规效应或光子非守恒）。([arXiv][12])

---

## 6. RCA/QCA 语义：光锥、红移与 $c$-限速分配

### 定义 2（因果锥与"光"）

局域可逆更新的格点动力学满足 Lieb–Robinson 上界，诱导有效"光锥"；饱和该上界的最小记号流称为"光"。([维基百科][13])

### 命题 6（红移的离散表述）

以主频 $f_{\rm clk}(t)=\dfrac{c}{R(t)\,\ell_*}$ 计时，同一码元流观测的离散周期满足

$$
P_0=(1+z)P_e,\qquad \nu_0=\nu_e/(1+z),
$$

即宇宙学红移的离散时间伸长，与连续表述一致。（由 §1 的统一频移律在离散时序上的直接化。）

### 命题 7（注意力/行动力的 $c$-限速分配）

设资源密度—流对 $(\rho,J)$ 满足守恒式 $\partial_t\rho+\nabla\!\cdot J=s$ 与约束 $|J|\le c\,\rho$，则影响仅能在因果锥内以不超过 $c$ 的速度传播；该"调度光速"与 Lieb–Robinson 速度一致。([link.aps.org][14])

---

## 7. 信息边界与速度极限

### 命题 8（处理速率上界：量子速度极限）

Mandelstam–Tamm 与 Margolus–Levitin 界给出最短演化时间与最大状态变更率；因此在给定能量/功率预算下，任何"分辨率提升—处理速率"均受其限制，不因尺度规范而放宽。([pubs.aip.org][15])

---

## 8. 观测—重建—对偶一致性的操作学规程

**流程 A（母尺三重闭合）**：对同一对象同时计算 $\varphi'(E)/(2\pi)$、$(2\pi)^{-1}\operatorname{tr}\mathsf Q(E)$、$\rho(E)$，要求曲线与方向极点一致，以验证刻度统一与 Birman–Kreĭn—Wigner–Smith 的互证。([arXiv][1])

**流程 B（NPE 账本）**：对每条数据管线报告"alias=0/≠0、EM 阶次 $p$、尾项上界"；在 Nyquist 满足且噪声/归一化已定的前提下，$r\downarrow$ **降低偏差**但**方差通常上升**（需带宽优化），**无新增奇性、无伪峰**由 §3"奇性不增"与 alias/EM 账本保障。([维基百科][2])

**流程 C（几何对偶校验）**：构造 $\eta(z)=D_L/[(1+z)^2D_A]$ 并做 Tolman 指数回归（期望 $n=4$），作为"规范 vs. 动力学"的一致性证据。([维基百科][7])

**流程 D（分辨率分配矩阵）**：在时/频/角/尺度–相位坐标上，取

$$
M^\star=\arg\max_{M\succeq 0,\ \operatorname{tr}M=\chi}\ \big\langle M,\ \nabla_{\mathbf r}\mathcal I\,\nabla_{\mathbf r}\mathcal I^\top\big\rangle,
$$

其中 $\chi>0$ 为固定资源预算常数（与 $\kappa(t)=\dot a/a$ 无关），$\mathbf r=(t,\omega,\vartheta,s)$ 收集时域/频域/角域/尺度–相位坐标（可按任务裁剪）。报告 Fisher 信息增益与条件数改善。

---

## 9. 理论之最小充分性

1. **尺度规范 $a=R^{-1}$**：把"外部膨胀"与"内部提分辨率"统一为同一 Mellin 伸缩，不改变本体奇性。
2. **母尺刻度**：以 $\rho=-\xi'=\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q=\frac{1}{2\pi i}\partial_E\log\det S=\frac{\varphi'}{2\pi}$ 统一读数，跨装置可比。([arXiv][1])
3. **NPE 有限阶闭合**：以 Poisson–EM 的有限阶纪律关闭误差账本，Nyquist 消灭别名。([dlmf.nist.gov][3])
4. **帧门槛**：Landau 必要密度与 Wexler–Raz 对偶保证稳定可逆重建。([msp.org][16])
5. **相对论一致性**：光锥 + 母尺的稳定子给出洛伦兹群；FRW 中统一频移律、Etherington 与 Tolman 自然成立。([math.tecnico.ulisboa.pt][8])

---

## 附：若干标准结果与本文结构的对应

* **Wigner–Smith 群延迟与"密度—相位导数"三等价**：群延迟矩阵定义与实验可测性、以及 $\det S$ 与谱位移函数的 Birman–Kreĭn 关系，支撑母尺刻度。([chaosbook.org][17])
* **红移的协变表述**：$\omega=-k_\mu u^\mu$ 与 $1+z=((k_\mu u^\mu)_e)/((k_\mu u^\mu)_o)$；宇宙学距离量的标准复合与对偶关系。([arXiv][9])
* **Tolman $(1+z)^{-4}$ 与对偶检验**：观测校准与方法学指引。([arXiv][18])
* **Alexandrov–Zeeman 定理**：因果结构决定（至多差整体伸缩的）洛伦兹—庞加莱群，缩去整体伸缩即得洛伦兹群。([math.tecnico.ulisboa.pt][8])
* **Landau 密度、Wexler–Raz、Balian–Low**：稳定采样—对偶—不可兼得局域性的三点平衡。([numdam.org][5])
* **Lieb–Robinson 与 QCA**：格点上的"有效光速"与可逆更新的因果锥。([维基百科][13])
* **量子速度极限**：分辨率提升与处理速率受 MT/ML 类界统一约束。([pubs.aip.org][15])

---

## 证明附录（选）

### A. Birman–Kreĭn—群延迟—相位导数三位一体

令可逆 $S(E)$ 单位散射矩阵。由 Smith 定义 $\mathsf Q(E)=-i\,S^\dagger S'$，则

$$
\operatorname{tr}\mathsf Q=-i\,\operatorname{tr}(S^\dagger S')=-i\,\partial_E\log\det S\,,
$$

其中用到 $\partial_E\log\det S=\operatorname{tr}(S^{-1}S')=\operatorname{tr}(S^\dagger S')$（因 $S$ 单位）。由 $\det S(E)=e^{-2\pi i\xi(E)}$ 与 $\operatorname{tr}\mathsf Q=-i\,\partial_E\log\det S$ 得 $\frac{1}{2\pi}\operatorname{tr}\mathsf Q=-\xi'(E)$。又 $\varphi(E)=\arg\det S(E)=-2\pi\xi(E)$ 故 $\varphi'(E)=-2\pi\xi'(E)$。于是

$$
\rho(E)=-\xi'(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)=\frac{1}{2\pi i}\partial_E\log\det S(E)=\frac{\varphi'(E)}{2\pi}\,.
$$

([arXiv][1])

### B. Etherington 与 Tolman 的几何来源

在唯一零测地、光子数守恒且度规引力下，测角面元与固有光度的变换给出 $D_L=(1+z)^2D_A$；结合单位时间—单位面积通量与光子能量/到达率的 $(1+z)^{-1}\times(1+z)^{-1}$ 因子，再与视角面积缩放的 $(1+z)^{-2}$ 合成 Tolman 面亮度衰减 $(1+z)^{-4}$。([维基百科][7])

### C. Alexandrov–Zeeman 稳定子到洛伦兹群

固定原点后，保因果序的线性映射由 $\mathbb R_{+}\times SO^+(1,3)$ 生成；再引入母尺的不变性即可去除整体伸缩，余下 $SO^+(1,3)$。([math.tecnico.ulisboa.pt][8])

### D. Landau—Wexler–Raz—Balian–Low 的帧三角

Landau 下界给出采样点的必要密度；Wexler–Raz 刻画对偶窗使重建算子为恒等；Balian–Low 宣告临界密度正交基无法同时良好局域，故工程上以冗余紧框架替代。([msp.org][16])

---

## 工具性定义与符号索引

* $a(t)$：尺度因子；$R(t)=a(t)^{-1}$：内部尺标；$\kappa=\dot a/a$。
* $S(E)$, $\mathsf Q(E)$, $\varphi(E)$, $\rho(E)$：三位一体母尺对象。([arXiv][1])
* NPE：Nyquist（别名入账/关断）–Poisson（求和桥接）–Euler–Maclaurin（有限阶伯努利层与尾项）。([维基百科][2])
* 帧密度与对偶：Landau 必要密度、Wexler–Raz 对偶、Balian–Low 限制。([numdam.org][5])
* 统一频移：$1+z=((k_\mu u^\mu)_e)/((k_\mu u^\mu)_o)$。([arXiv][9])

---

[1]: https://arxiv.org/pdf/1804.09580?utm_source=chatgpt.com "Wigner-Smith time-delay matrix in chaotic cavities with non"
[2]: https://en.wikipedia.org/wiki/Nyquist%E2%80%93Shannon_sampling_theorem?utm_source=chatgpt.com "Nyquist–Shannon sampling theorem"
[3]: https://dlmf.nist.gov/1.8?utm_source=chatgpt.com "1.8 Fourier Series"
[4]: https://dlmf.nist.gov/24.2?utm_source=chatgpt.com "24.2(i) Bernoulli Numbers and Polynomials"
[5]: https://www.numdam.org/item/10.1016/j.crma.2012.05.003.pdf?utm_source=chatgpt.com "Revisiting Landau's density theorems for Paley–Wiener"
[6]: https://arxiv.org/abs/astro-ph/9905116?utm_source=chatgpt.com "Distance measures in cosmology"
[7]: https://en.wikipedia.org/wiki/Etherington%27s_reciprocity_theorem?utm_source=chatgpt.com "Etherington's reciprocity theorem"
[8]: https://www.math.tecnico.ulisboa.pt/~jnatar/nonarxivpapers/Zeeman1964.pdf?utm_source=chatgpt.com "Causality Implies the Lorentz Group"
[9]: https://arxiv.org/pdf/gr-qc/9712019?utm_source=chatgpt.com "Lecture Notes on General Relativity"
[10]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[11]: https://heil.math.gatech.edu/papers/bltschauder.pdf?utm_source=chatgpt.com "Gabor Schauder bases and the Balian-Low theorem"
[12]: https://arxiv.org/pdf/1210.2642?utm_source=chatgpt.com "Cosmic distance duality and cosmic transparency"
[13]: https://en.wikipedia.org/wiki/Lieb%E2%80%93Robinson_bounds?utm_source=chatgpt.com "Lieb–Robinson bounds"
[14]: https://link.aps.org/doi/10.1103/PhysRevLett.102.017204?utm_source=chatgpt.com "Lieb-Robinson Bounds and the Speed of Light"
[15]: https://pubs.aip.org/aip/jmp/article-pdf/doi/10.1063/1.1897164/14813474/052108_1_online.pdf?utm_source=chatgpt.com "Mathematical analysis of the Mandelstam–Tamm time"
[16]: https://msp.org/apde/2024/17-2/apde-v17-n2-p06-p.pdf?utm_source=chatgpt.com "Necessary density conditions for sampling"
[17]: https://chaosbook.org/library/WignerDelay55.pdf?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering Phase Shift"
[18]: https://arxiv.org/abs/astro-ph/0102213?utm_source=chatgpt.com "The Tolman Surface Brightness Test for the Reality of the Expansion"
