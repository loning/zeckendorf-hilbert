# MCCI：思维漏洞—因果—选择架构的统一理论

**（含定义—判据—定理—证明—可检流程，与 WSIG / EBOC / RCA–CID 兼容）**

**作者**：Auric（S-series / EBOC）
**版本**：v1.7（2025-11-05，Asia/Singapore）
**关键词**：思维漏洞；因果图（SCM）；选择架构（默认/框架/顺序）；偏差—噪声分解；损失厌恶；参考点；CATE；I-投影（KL/Bregman）；WSIG；EBOC；RCA–CID
**MSC**：62Cxx；62Pxx；68Txx；91Bxx；94Axx

---

## 摘要

构造一套在概率—效用—因果三重规范下可校验的"思维漏洞"理论：给定理性基准策略与可见架构变量的嵌入，定义总体偏离泛函与四维分解（偏差、噪声、因果错配、架构敏感），并给出后门/前门/工具变量/断点/双重差分等识别判据与最小实验设计；在 I-投影与 Bregman 几何下证明"Pythagoras—解耦"结构，导出可实现的估计—审计管线（DQC）。在 WSIG 词典中，将理性约束族的 I-投影视为"读数规范"，把偏离写成 KL/Bregman 距离；于 EBOC 中把管线实现为"窗口选择叶"的规则；在 RCA–CID 中用可逆日志保证干预的可回放与外部审计。并以"关切权重×断裂系数"指标 $L=\eta(\lambda-1)$ 给出"损失厌恶—爱"的模型内判定准则。核心证明依循 Csiszár 的 I-投影与 Bregman-Pythagoras、Pearl 的因果判据与现代估计理论。([projecteuclid.org][1])

---

## Notation & Axioms / Conventions（WSIG–EBOC–RCA 统一体）

**A1（测度—策略—读数）**：观测三元 $(\mathcal H,w,\mathcal D)$ 诱导窗化读数；所有策略与分布在标准单纯形上以 Bregman 发散 $D_\phi(\cdot\Vert\cdot)$ 与 KL 做度量；理性基准由约束族上的 I-投影给定。([projecteuclid.org][1])
**A2（刻度同一式，WSIG 卡片）**：在散射—信息几何的统一刻度下，采用母刻度 $\varphi'(E)/\pi=\rho_{\rm rel}(E)=(2\pi)^{-1}\,\mathrm{tr}\,\mathsf Q(E)$，其中 $\mathsf Q:=-\mathrm i\, S^\dagger \partial_E S$ 为 Wigner–Smith 群延迟矩阵；作为与本体系连接的测度坐标。([link.aps.org][2])
**A3（有限阶 NPE 纪律）**：所有离散—连续换元与窗化积分一律采用"有限阶 Euler–Maclaurin + Poisson"三项闭合误差学，声明奇性不增与极点=主尺度。
**A4（RCA–CID 可逆性）**：实现与审计一律映射到 Bennett 可逆计算与 Zeckendorf-编码日志；保证干预与估计版本的可逆回放。([users.cs.duke.edu][3])

---

## 1. 模型与基线规范

**变量**：情境 $X$，行动 $A\in\mathcal A$，结局 $Y$，未观测扰动 $U$；**架构变量** $C=(F,D,S)$ 分别为表述框架、默认选中、呈现顺序。
**SCM**：有向无环图 $G$ 与结构方程 $V_i:=f_i(\mathrm{Pa}(V_i),U_i)$。
**理性基准**：在已识别的干预分布 $P(Y\mid do(A=a),X)$ 与效用 $u$ 下，贝叶斯—决策最优策略
$$
\pi^\star(\cdot\mid x)\in\arg\max_\pi\,\mathbb E\left[u(Y)\mid do(A\sim \pi(\cdot\mid x)),X=x\right].
$$
**实际策略**：$\pi(\cdot\mid x,c)$ 可显式依赖 $c$。
**发散度**：取 KL 或一般 Bregman 发散 $D_\phi$。

---

## 2. 定义：思维漏洞的偏离泛函与四维分解

**定义 2.1（总体偏离—重复评审一致化）**
对每个情境 $X=x$，固定一份**基线呈现** $c_0$；令第 $r$ 次评审的策略为 $\pi^{(r)}(\cdot\mid x,c_0)$。定义
$$
\mathcal L:=\mathbb E_X\,\mathbb E_r\big[D_\phi\big(\pi^\star(\cdot\mid X)\Vert\pi^{(r)}(\cdot\mid X,c_0)\big)\big].
$$
（架构敏感性单独由 $\mathrm{AS}$ 与其正则项 $\mathcal R_{\mathrm{AS}}$ 度量；见定理4.1。）

**定义 2.2（同案重复与四元量）**
对同一案件 $x$，重复评审 $A^{(r)}\sim\pi^{(r)}(\cdot\mid x,c)$。这里的 $\pi^{(r)}(\cdot\mid x,c)$ 指第 $r$ 次评审（或评审者）的行动分布；其 Bregman-重心
$$
\bar\pi_\phi(\cdot\mid x,c):=(\nabla\phi)^{-1}\big(\mathbb E_r[\nabla\phi(\pi^{(r)}(\cdot\mid x,c))]\big).
$$
定义
$$
\begin{aligned}
\mathrm{Bias}(x)&:=D_\phi\big(\pi^\star(\cdot\mid x)\Vert\bar\pi_\phi(\cdot\mid x,c)\big),\\
\mathrm{Noise}(x)&:=\mathbb E_r\big[D_\phi\big(\bar\pi_\phi(\cdot\mid x,c)\Vert\pi^{(r)}(\cdot\mid x,c)\big)\big],\\
\mathrm{CM}(x)&:=\Big(\mathbb E[u(Y)\mid A\sim \bar\pi_\phi(\cdot\mid x,c),X=x]-\mathbb E[u(Y)\mid do(A\sim \bar\pi_\phi(\cdot\mid x,c)),X=x]\Big)^{2}\ge 0,\\
\mathrm{AS}(x)&:=\sup_{c,c'}D_\phi\big(\pi(\cdot\mid x,c)\Vert\pi(\cdot\mid x,c')\big).
\end{aligned}
$$

**定义 2.3（强度指标）**
给定权重 $\omega\succ0$，定义
$$
\mathrm{Defect}:=\mathbb E_X\Big[\omega_b\,\mathrm{Bias}(X)+\omega_n\,\mathrm{Noise}(X)+\omega_c\,\mathrm{CM}(X)+\omega_a\,\mathrm{AS}(X)\Big].
$$
注：此处 $\mathrm{Defect}$ 的四项与第4.1节中的 $\mathcal B,\mathcal N,\mathcal C,\mathcal R_{\mathrm{AS}}$ 一一对应，其中 $\mathcal C=\mathbb E_X[\mathrm{CM}(X)]$、$\mathcal R_{\mathrm{AS}}$ 为 $\mathrm{AS}$ 的惩罚泛函。

---

## 3. 因果嵌入与识别判据

**架构嵌入**：将 $C$ 作为 $A$ 的父或共同父映入 $G$：$C\to A\to Y$；允许 $C$ 改变信息呈现与观测通道，但不改变潜在结局 $Y(a)$ 的结构方程。
**后门判据**：若存在 $Z\subset X$ 阻断所有自 $A$ 至 $Y$ 的后门路径，则 $P(y\mid do(a))=\sum_z P(y\mid a,z)P(z)$。([fitelson.org][4])
**前门/工具/断点/DiD**：未观测混杂时分别用前门变量、合格工具变量（相关性、排除性、单调性）、回归断点与现代多期 DiD（含错位处理时序与连续强度）。([arXiv][5])

---

## 4. 三个核心定理与证明

### 定理 4.1（Bregman–Pythagoras 双分解 + 正则项）

对每个 $x$，对 $r$ 取期望得
$$
\mathbb E_r\Big[D_\phi\big(\pi^\star\Vert \pi^{(r)}\big)\Big]
= D_\phi\big(\pi^\star\Vert\bar\pi_\phi\big)+\mathbb E_r\Big[D_\phi\big(\bar\pi_\phi\Vert\pi^{(r)}\big)\Big].
$$
再对 $X$ 取期望，按定义2.1得
$$
\mathcal L=\underbrace{\mathbb E_X\big[D_\phi(\pi^\star\Vert\bar\pi_\phi)\big]}_{\mathcal B}
+\underbrace{\mathbb E_X\big[\mathbb E_r D_\phi(\bar\pi_\phi\Vert\pi^{(r)})\big]}_{\mathcal N}.
$$
若引入正则项以惩罚因果错配与架构敏感，定义
$$
\mathcal L_{\rm aug}:=\mathcal L+\underbrace{\mathbb E_X[\mathrm{CM}(X)]}_{\mathcal C}+\underbrace{\Psi_{\mathrm{AS}}}_{\mathcal R_{\mathrm{AS}}}\quad\Rightarrow\quad
\mathcal L_{\rm aug}=\mathcal B+\mathcal N+\mathcal C+\mathcal R_{\mathrm{AS}},
$$
其中 $\mathcal C,\mathcal R_{\mathrm{AS}}\ge0$。
**证明**：Bregman 三点恒等式
$\ D_\phi(x_1\Vert x_3)=D_\phi(x_1\Vert x_2)+D_\phi(x_2\Vert x_3)+\langle x_1-x_2,\nabla\phi(x_3)-\nabla\phi(x_2)\rangle$，
取 $x_1=\pi^\star,x_2=\bar\pi_\phi,x_3=\pi^{(r)}$ 并对 $r$ 取条件期望，利用 $\bar\pi_\phi=(\nabla\phi)^{-1}\mathbb E[\nabla\phi(\pi^{(r)})]$ 令交叉项为 0（Bregman-重心的一阶条件），得第一式与基线恒等式；$\mathrm{CM}(X)$ 已按定义2.2取为非负平方差，$\Psi_{\mathrm{AS}}$ 是 $\mathrm{AS}$ 的惩罚泛函，两者作为正则项扩展得 $\mathcal L_{\rm aug}$。([jmlr.org][6])

### 定理 4.2（架构等价与架构效应）

若两种呈现 $c,c'$ 仅作用于信息通道而不改变 $Y(a)$ 的结构，则
$$
\mathrm{AS}(x)=0\iff \pi(\cdot\mid x,c)=\pi(\cdot\mid x,c')\ \text{几乎处处}.
$$
若 $\mathrm{AS}(x)>0$，则存在纯呈现差异诱发的**架构效应** $P(a\mid x,c)\neq P(a\mid x,c')$。
**证明**：由发散正定性与定义即得。

### 定理 4.3（"损失厌恶—爱"的模型内判定）

令 $s\in\{0,1\}$，参考点 $s^\ast=1$，对方福利权重 $\eta\ge0$，断裂损失系数 $\lambda>1$，
$$
U(x,y,s)=u(x)+\eta\, u(y)+v(s-s^\ast),\qquad
v(z)=
\begin{cases}
\alpha\, z,& z\ge 0,\\[2pt]
-\lambda\,\beta(-z),& z<0.
\end{cases}
$$
其中 $\beta(\cdot)>0,\ \beta(0)=0$。将"爱"操作化为：把分离概率从 $\varepsilon\downarrow0$ 降到 $0$ 的 $\mathrm{WTP}$ 超过仅由 $u$ 的风险厌恶所蕴含的基准。则在 $\lambda>1$ 前提下
$$
\text{爱}\ \Longleftrightarrow\ \eta>0,\qquad
L:=\eta(\lambda-1)>0.
$$
**证明**：一阶近似下
$$
\mathrm{WTP}\ \sim\ \varepsilon\Big(\eta\cdot\Delta u+(\lambda-1)\cdot\beta(1)\Big).
$$
其中 $\Delta u$ 表示对方福利在 $s=1$ 与 $s=0$ 下的边际差异；若 $\eta=0$，该项消失；若 $\lambda=1$，不存在对分离的损失厌恶校正。两者共同为正即给出正的 $\mathrm{WTP}$ 超额。

---

## 5. 识别与估计（DQC：记录—对照—因果—审计）

**D1 记录**：案卷包含 $(X,C,\mathcal A,\text{目标},\text{约束})$。
**D2 对照（Counter-framing）**：同案卷施行两种以上 $C$（收益/损失框架、默认切换、顺序打乱），计算
$$
\widehat{\mathrm{AS}}(x)=\max_{c,c'} D_\phi\big(\hat\pi(\cdot\mid x,c),\hat\pi(\cdot\mid x,c')\big),
$$
高于门限即标记"架构敏感"。
**D3 因果（Causalization）**：绘制 DAG 并按后门/前门/IV/断点/DiD 判识；可随机化者优先小流量随机化。估计
$\mathrm{ATE}=\mathbb E[Y(1)-Y(0)]$、$\mathrm{CATE}(x)=\mathbb E[Y(1)-Y(0)\mid X=x]$。
观测数据采用 IPW/DR/TMLE 及因果森林；并做未观测混杂的 $\Gamma$-敏感性分析。([math.mcgill.ca][7])
**D4 审计（Noise audit）**：同案多评估计 $\mathrm{Noise}$ 并汇总
$$
\widehat{\mathrm{Defect}}=\omega_b\widehat{\mathcal B}+\omega_n\widehat{\mathcal N}+\omega_c\widehat{\mathcal C}+\omega_a\widehat{\mathrm{AS}}.
$$
在报告中区分"水平噪声/情景噪声/模式噪声"，并给出"决策卫生"规程（独立评判、聚合、多源证据）。([维基百科][8])

---

## 6. 识别判据与最小实验设计（速查）

**后门**：选择 $Z$ 阻断所有带入 $A$ 的箭头路径，利用 $\sum_z P(y\mid a,z)P(z)$。([fitelson.org][4])
**前门**：存在完全中介 $M$ 且 $A\to M$ 无后门、$M\to Y$ 可后门调节时可识别 $P(y\mid do(a))$。([arXiv][5])
**工具变量（IV）**：$Z$ 相关于 $A$、与 $Y(a)$ 独立、仅经 $A$ 影响 $Y$，在单调性下识别 LATE。([math.mcgill.ca][9])
**回归断点（RD）**：阈值处连续性假设保证局部平均因果效应识别。([NBER][10])
**多期 DiD**：错位处理与异质效应下采用 Callaway–Sant'Anna / Sun–Abraham 家族与扩展到连续处理强度。([file-lianxh.oss-cn-shenzhen.aliyuncs.com][11])

---

## 7. 估计器与误差学（非渐近执行）

**IPW / DR**：利用倾向得分与结果回归的双重稳健性；报告小样本修正与截尾稳健性。([math.mcgill.ca][7])
**TMLE**：两步替代估计，尊重目标泛函的效率影响函数，便于与 ML 集成；给出影响函数标准误。([De Gruyter Brill][12])
**因果森林 / 广义随机森林**：估计 CATE 与不确定度，处理簇集误差。([arXiv][13])
**敏感性分析**：Rosenbaum $\Gamma$ 界、边缘敏感性模型与其锐化变体。([pages.cs.wisc.edu][14])
**NPE 误差预算**：对所有离散—连续换元报告别名、边界层（Bernoulli）、尾项三部分与总界。

---

## 8. 与 WSIG / EBOC / RCA–CID 的同构对接

**WSIG（I-投影=Born 读数）**：理性约束族 $\mathcal Q$ 上的 I-投影 $q^\star=\arg\min_{q\in\mathcal Q}\mathrm{KL}(p\Vert q)$ 为"规范读数"，总体偏离 $\mathcal L=\mathrm{KL}(q^\star\Vert p_\pi)$ 即读数—策略相对偏离；Bregman-Pythagoras 给出"偏差+噪声"的可加结构。([projecteuclid.org][1])
**EBOC（静态块）**：案卷与随机化设计是对静态块测度的窗口选择规则，不改变全局测度；时间被视为对块的叶读取，其序由选择规则诱导。
**RCA–CID（可逆日志）**：将 DQC 管线嵌入可逆元胞自动机，全部干预—估计版本以 Zeckendorf 规范形编码的 CID 日志记录，并以 Bennett 可逆嵌入保证可回放与外部审计。([users.cs.duke.edu][3])
**刻度对齐**：在需要与能谱刻度合流的场景，引用 $\varphi'/\pi=\rho_{\rm rel}=(2\pi)^{-1}\,\mathrm{tr}\,\mathsf Q$ 作为通用坐标，群延迟—带宽的资源约束成为 DQC 的全局预算。([link.aps.org][2])

---

## 9. 实验蓝图与可复现清单

**A/B（默认效应）**：随机化 $D\in\{\text{opt-in},\text{opt-out}\}$；测 $\Delta\mathrm{ATE}$ 与 $\widehat{\mathrm{AS}}$。
**双框架复核**：同一告知以收益/损失两版呈现；以 TMLE 估计 $\mathrm{CATE}$。([De Gruyter Brill][12])
**噪声审计**：同案多评；区分水平/情景/模式噪声并报告降噪后幅度与稳定性。([维基百科][8])
**"爱"指标**：在自愿样本上构造小概率分离的保险-型选择，估 $\widehat L=\hat\eta(\hat\lambda-1)$ 并联动满意度/互惠性次级终点。
**治理与公平**：对重点子群报告 $\mathrm{CATE}$、$\widehat{\mathrm{AS}}$，设置"架构公平"门限与告知规范。

---

## 10. 进一步性质与推论

**推论 10.1（按后门集调整 $\Rightarrow$ 因果错配项消失）**
若存在 $Z$ 满足后门判据，且计算 $\mathrm{CM}$ 时按 $Z$ 进行完全调整，则 $\mathcal C=0$。([fitelson.org][4])

**推论 10.2（KL 特例的重心）**：当 $D_\phi=\mathrm{KL}$ 且第一参数在单纯形上，$\bar\pi_\phi$ 为几何-均值型重心，保证定理 4.1 的交叉项消失。([projecteuclid.org][1])

**推论 10.3（决策卫生的充分性）**：独立评判与去同温层聚合在 Bregman 平台上等价于最小化 $\mathbb E_r[D_\phi(\bar\pi_\phi\Vert\pi^{(r)})]$，从而直接降低 $\mathcal N$。([barrons.com][15])

**推论 10.4（群延迟预算）**：在以 $\mathrm{tr}\,\mathsf Q$ 为刻度的系统中，窗口化评估的总复杂度受群延迟—带宽乘积上界约束，可作为 DQC 的资源预算。([link.aps.org][2])

---

## 11. 证明细节（择要）

**（I）Bregman-Pythagoras**：Banerjee 等对 Bregman 三点恒等式与聚类重心的一般处理，配合 Csiszár I-投影几何，给出 $\bar\pi_\phi=(\nabla\phi)^{-1}\mathbb E[\nabla\phi(\pi^{(r)})]$ 的一阶条件，故交叉项为 0。([jmlr.org][6])
**（II）因果识别**：Pearl 的后门/前门；Angrist–Imbens–Rubin 的 IV 与 LATE；Hahn–Todd–van der Klaauw 的 RD；Callaway–Sant'Anna（以及后续扩展）的多期与连续处理 DiD。([archive.illc.uva.nl][16])
**（III）估计理论**：Bang–Robins 的 DR；van der Laan–Rubin 的 TMLE；Athey–Wager 的因果森林与广义随机森林；Rosenbaum 及近年的敏感性回顾。([math.mcgill.ca][7])
**（IV）WSIG 刻度**：Wigner–Smith 群延迟与 Birman–Kreĭn 公式提供刻度—相位—谱的等价坐标，用作与本理论合流的测度坐标。([link.aps.org][2])
**（V）RCA–CID 可逆性**：Bennett 的逻辑可逆性与 Zeckendorf 定理保证日志的可逆回放与唯一分解，从而对干预—估计版本进行外审。([users.cs.duke.edu][3])

---

## 12. 实施蓝图（工程最小集）

1）绘图与判据：每条上线决策流先绘 DAG 并标明后门集/可用工具/可能阈值与时序错位。
2）上线 DQC：案卷模板＋双框架问卷＋小流量随机化；自动化 IPW/DR/TMLE/因果森林；附带 Rosenbaum $\Gamma$ 报告。([jstatsoft.org][17])
3）审计与治理：对重点子群报告 $\mathrm{CATE}$、$\widehat{\mathrm{AS}}$ 与 $\widehat{\mathrm{Defect}}$（含 $\widehat{\mathcal B},\widehat{\mathcal N},\widehat{\mathcal C},\widehat{\mathrm{AS}}$）；设置"架构公平"门限与复核频率。
4）RCA–CID：以 Zeckendorf-日志承载版本，并声明可逆回放接口与审计 API。

---

## 参考文献（选）

Csiszár I. *I-Divergence Geometry of Probability Distributions and Minimization Problems*. Ann. Probab. 1975. ([projecteuclid.org][1])
Banerjee A., Merugu S., Dhillon I., Ghosh J. *Clustering with Bregman Divergences*. JMLR 2005. ([jmlr.org][6])
Pearl J. *Causality*（2009）与相关论文（Back-door/Front-door）. ([archive.illc.uva.nl][16])
Angrist J., Imbens G., Rubin D. *Identification of Causal Effects Using Instrumental Variables*. JASA 1996. ([tandfonline.com][18])
Hahn J., Todd P., van der Klaauw W. *Identification and Estimation with RD*. Econometrica 2001. ([onlinelibrary.wiley.com][19])
Callaway B., Sant'Anna P. *DiD with Multiple Time Periods* 2021；及连续处理扩展 2024. ([file-lianxh.oss-cn-shenzhen.aliyuncs.com][11])
Bang H., Robins J. *Doubly Robust Estimation in Missing Data and Causal Inference*. 2005. ([math.mcgill.ca][7])
van der Laan M., Rubin D. *Targeted Maximum Likelihood Learning*. 2006. ([De Gruyter Brill][12])
Athey S., Tibshirani J., Wager S. *Generalized Random Forests*. Ann. Stat. 2019. ([projecteuclid.org][20])
Rosenbaum P. *Sensitivity Analysis* 及后续综述. ([PMC][21])
Kahneman D., Sibony O., Sunstein C. *Noise*（2021）与噪声三分（水平/情景/模式）. ([维基百科][8])
Wigner E. P.（1955）；Smith F. T.（1960）群延迟—寿命矩阵。([link.aps.org][22])
Birman–Kreĭn 光谱移位与迹公式（综述与现代化处理）。([arXiv][23])
Bennett C. H. *Logical Reversibility of Computation*（1973）. ([users.cs.duke.edu][3])
Zeckendorf 定理与唯一分解编码。([维基百科][24])

---

## 一句话

"思维漏洞"即策略相对理性基准的可分解偏离；以因果判据与 I-投影化为可测指标，用 DQC 把怀疑转化为制度化改进，并在 WSIG / EBOC / RCA–CID 的同一语言内保证可复核与可移植。

[1]: https://projecteuclid.org/journals/annals-of-probability/volume-3/issue-1/I-Divergence-Geometry-of-Probability-Distributions-and-Minimization-Problems/10.1214/aop/1176996454.full?utm_source=chatgpt.com "$I$-Divergence Geometry & Minimization Problems"
[2]: https://link.aps.org/doi/10.1103/PhysRev.118.349?utm_source=chatgpt.com "Lifetime Matrix in Collision Theory | Phys. Rev."
[3]: https://users.cs.duke.edu/~reif/courses/complectures/AltModelsComp/Bennett/LogRevComp.pdf?utm_source=chatgpt.com "Logical Reversibility of Computation"
[4]: https://fitelson.org/woodward/pearl_95.pdf?utm_source=chatgpt.com "Causal diagrams for empirical research (w,t~-; di>cu>5>ion~)"
[5]: https://www.arxiv.org/pdf/2412.10600?utm_source=chatgpt.com "The Front-door Criterion in the Potential Outcome Framework"
[6]: https://www.jmlr.org/papers/volume6/banerjee05b/banerjee05b.pdf?utm_source=chatgpt.com "Clustering with Bregman Divergences"
[7]: https://www.math.mcgill.ca/dstephens/SISCR2018/Articles/bang_robins_2005.pdf?utm_source=chatgpt.com "Doubly Robust Estimation in Missing Data and Causal ..."
[8]: https://en.wikipedia.org/wiki/Noise%3A_A_Flaw_in_Human_Judgment?utm_source=chatgpt.com "Noise: A Flaw in Human Judgment"
[9]: https://www.math.mcgill.ca/dstephens/AngristIV1996-JASA-Combined.pdf?utm_source=chatgpt.com "Identification of Causal Effects Using Instrumental Variables"
[10]: https://www.nber.org/system/files/working_papers/w13039/w13039.pdf?utm_source=chatgpt.com "Regression Discontinuity Designs: A Guide to Practice"
[11]: https://file-lianxh.oss-cn-shenzhen.aliyuncs.com/Refs/2025-08-Yang/Callaway_2021_Difference-in-Differences_with_multiple_time_periods.pdf?utm_source=chatgpt.com "Difference-in-Differences with multiple time periods"
[12]: https://www.degruyterbrill.com/document/doi/10.2202/1557-4679.1043/html?lang=en&srsltid=AfmBOoqnAKscia9K3crjBtBMWTZtyjy1MdcjXYImJ4OHSFz6gDJ011pu&utm_source=chatgpt.com "Targeted Maximum Likelihood Learning"
[13]: https://arxiv.org/abs/1510.04342?utm_source=chatgpt.com "Estimation and Inference of Heterogeneous Treatment Effects using Random Forests"
[14]: https://pages.cs.wisc.edu/~hyunseung/stat992_sp25/RosenbaumSens.html?utm_source=chatgpt.com "Rosenbaum's Sensitivity Analysis (For Matched Pairs)"
[15]: https://www.barrons.com/articles/economist-daniel-kahneman-says-noise-is-wrecking-your-judgment-heres-why-and-what-to-do-about-it-51622228892?utm_source=chatgpt.com "Daniel Kahneman Says Noise Is Wrecking Your Judgment. Here's Why, and What to Do About It."
[16]: https://archive.illc.uva.nl/cil/uploaded_files/inlineitem/Pearl_2009_Causality.pdf?utm_source=chatgpt.com "Causality"
[17]: https://www.jstatsoft.org/article/view/v051i13/653?utm_source=chatgpt.com "An R Package for Targeted Maximum Likelihood Estimation"
[18]: https://www.tandfonline.com/doi/abs/10.1080/01621459.1996.10476902?utm_source=chatgpt.com "Identification of Causal Effects Using Instrumental Variables"
[19]: https://onlinelibrary.wiley.com/doi/pdf/10.1111/1468-0262.00183?utm_source=chatgpt.com "Identification and Estimation of Treatment Effects with a ..."
[20]: https://projecteuclid.org/journals/annals-of-statistics/volume-47/issue-2/Generalized-random-forests/10.1214/18-AOS1709.full?utm_source=chatgpt.com "Generalized random forests"
[21]: https://pmc.ncbi.nlm.nih.gov/articles/PMC3800481/?utm_source=chatgpt.com "An Introduction to Sensitivity Analysis for Unobserved ..."
[22]: https://link.aps.org/doi/10.1103/PhysRev.98.145?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering Phase ..."
[23]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
[24]: https://en.wikipedia.org/wiki/Zeckendorf%27s_theorem?utm_source=chatgpt.com "Zeckendorf's theorem"
