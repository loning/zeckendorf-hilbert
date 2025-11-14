# 通用灾难安全不可判定与能力–风险上界前沿：统一定理、复杂性定位与工程化路径

## Abstract

建立两条面向通用学习与决策系统的基础边界。其一,给出交互式智能体—环境系统的灾难安全判定不可判定性:在极弱建模假设下,针对任意扩展封闭的正规坏前缀规范,是否满足阈值安全性不存在全域算法;在确定性环境与逐步可计算策略的受限子类上,进一步定位为 **Σ₁⁰‑完全/Π₁⁰‑完全**。其二,给出由 PAC‑Bayes 高概率界、互信息期望型界与 Wasserstein‑1 分布鲁棒优化(Kantorovich–Rubinstein 对偶)联立所诱导的**能力–最坏风险上界前沿**;并以点扰式对手建立普适**几何下界**,连同鲁棒–精度不可兼得与鲁棒泛化样本复杂度下界,形成"上界—下界"的双重支撑。由此提出"范围限定—运行时防护—风险预算—结构先验"的治理蓝图,给出最小可复现的 ImageNet‑C + Shield 实验骨架与度量配置。

## Keywords

停机;Rice 定理;Σ₁⁰‑完全;POMDP;PAC‑Bayes;条件互信息;Wasserstein‑DRO;Kantorovich–Rubinstein 对偶;对抗鲁棒性;运行时盾;可中断性

## Introduction & Historical Context

算法可判定性与程序语义揭示了普适验证的根本限制:停机问题不可判定,Rice 定理表明任何非平凡语义性质不可判定。将这一思想迁移至交互式智能体—环境设定,得到对"是否触发灾难规范"的通用判定不可达。该方向与无限时域概率规划/部分可观测决策在阈值与计划存在性上的不可判定结果相互呼应。另一方面,现代学习理论显示能力与稳健不可无代价并进:PAC‑Bayes 与互信息范式刻画复杂度/信息量对泛化的影响,Wasserstein‑DRO 则刻画分布偏移下的最坏风险;同时,鲁棒–精度不可兼得与鲁棒泛化样本复杂度下界在自然模型族中已得到严格证明。两条边界共同指向治理原则:在承认通用静态认证不可能与能力—风险硬权衡的前提下,采用范围限定、运行时防护与风险预算的分层方案。

## Model & Assumptions

### 交互语义与时间假设

* 动作与观测字母表 $\mathcal A,\mathcal O$ 有限;历史 $h_{1:t}\in(\mathcal A\times\mathcal O)^t$。
* **逐步可计算策略**:智能体 $A$ 为函数 $A:(\mathcal A\times\mathcal O)^\star\to \mathcal A$,且对任意 $h_{<t}$ 存在有限时间在步骤 $t$ 产生 $a_t=A(h_{<t})$(允许内部随机化时以抽样程序实现)。该假设在不可判定性构造与完全性定位中始终满足。
* 环境 $E$ 由历史条件概率 $\mu(o_t\mid h_{<t},a_t)$ 指定。主结果使用**确定性平凡环境** $E_0$:恒返回固定观测 $o_\bot$。

### 安全性质与正规坏前缀

* 令 $\Sigma=(\mathcal A\times\mathcal O)^\star$。称 $B\subseteq \Sigma$ 为**坏前缀语言**,若对任意 $u\in B$ 与任意延拓 $v\in\Sigma$,均有 $uv\in B$(**扩展封闭/extension‑closed**)。对应的**安全前缀集** $S=\Sigma\setminus B$ 则为**前缀向下封闭/prefix‑closed**。
* 规范采用**正规坏前缀语言** $B$(等价于安全前缀由 DFA/安全自动机识别)。违规事件为

$$
\mathsf{Bad}=\{\exists t:\ h_{1:t}\in B\},\qquad \tau(h)=\inf\{t:\ h_{1:t}\in B\}.
$$

* **阈值安全谓词**:给定 $\varepsilon\in[0,1)$,

$$
\operatorname{Safe}_\varepsilon(A,E,B):=\ \Pr_\mu(\mathsf{Bad})\ \le\ \varepsilon.
$$

### 学习—评估与分布鲁棒

* 数据域 $\mathcal Z$ 带度量 $d$;样本 $S=(Z_i)_{i=1}^n\sim D^n$。
* 学习算法输出后验 $Q_S\in\mathcal P(\mathcal H)$。损失 $\ell:\mathcal H\times\mathcal Z\to[0,1]$。
* **Lipschitz 假设**:存在统一常数 $L>0$,使对任意 $h\in\mathcal H$,映射 $z\mapsto \ell(h,z)$ 关于 $d$ 为 $L$-Lipschitz(0‑1 损失不适用,采用交叉熵/hinge 等平滑替代;可通过谱范数约束与梯度裁剪控制 $L$)。
* Wasserstein‑1 球 $\mathbb B_\rho(D)=\{D':W_1(D',D)\le\rho\}$;鲁棒风险

$$
R^{\rm rob}_\rho(Q):=\sup_{D'\in\mathbb B_\rho(D)}\ \mathbb E_{h\sim Q,z\sim D'}[\ell(h,z)].
$$

## Main Results (Theorems and alignments)

### 定理 1(通用灾难安全判定不可判定)

存在正规坏前缀族 $\mathfrak B$,使得不存在算法能对所有逐步可计算策略 $A$、可计算环境 $E$、$B\in\mathfrak B$ 与任意有理 $\varepsilon\in[0,1)$ 判定 $\operatorname{Safe}_\varepsilon(A,E,B)$ 的真值。

### 定理 1′(受限子类的复杂性定位)

在确定性环境 $E_0$ 与逐步可计算策略类下,令

$$
\text{UNSAFE}=\{(A,E_0,B,\varepsilon):\Pr(\mathsf{Bad})>\varepsilon\},\quad \varepsilon<1.
$$

则 $\text{UNSAFE}$ 为 **Σ₁⁰‑完全**,其补集 $\text{SAFE}$ 为 **Π₁⁰‑完全**。在该子类中 $\Pr(\mathsf{Bad})\in\{0,1\}$,故"$\Pr(\mathsf{Bad})>\varepsilon$"与"发生"对任意 $\varepsilon<1$ 等价。

### 定理 2(能力–最坏风险上界前沿:PAC‑Bayes + KR)

对任意先验 $P$ 与 $\delta\in(0,1)$,以概率至少 $1-\delta$(对 $S\sim D^n$)有

$$
\boxed{\,R^{\rm rob}_\rho(Q)\ \le\ \widehat R_S(Q)\ +\ \sqrt{\frac{\mathrm{KL}(Q\Vert P)+\ln(1/\delta)}{2n}}\ +\ L\rho,\,}.
$$

式右端三项分别为经验误差、复杂度/置信项与分布偏移线性惩罚,构成**上界诱导的能力–风险前沿**。

### 定理 2′(互信息界的高概率化:范式化陈述)

设损失 $\ell\in[0,1]$ 且对每个样本点次高斯常数为 $\sigma$。若学习算法满足**条件互信息**上界 $\mathrm{CMI}(S;Q_S)\le \Gamma$ 或满足等价强度的均匀稳定性,则存在常数 $c>0$ 使对任意 $\delta\in(0,1)$,有

$$
\boxed{\,\Pr\!\left(\ R_D(Q_S)\ \le\ \widehat R_S(Q_S)\ +\ \sqrt{\frac{2\sigma^2(\Gamma+c\ln(1/\delta))}{n}}\ \right)\ \ge\ 1-\delta,\,}.
$$

将 (2) 与 (1) 并置,得到对数据依赖后验的高概率**前沿**表述:取两者右端的较小者作为能力–风险曲线的可操作上界。

### 定理 3(点扰式几何下界与分布球含蕴)

对任意分类器 $f$ 与 $\rho>0$,定义

$$
\mathcal R^{\rm adv}_\rho(f)=\Pr_{(z,y)\sim D}\big[\exists z'\in B_\rho(z):\ f(z')\ne y\big],
$$

其中 $B_\rho(z)=\{z': d(z,z')\le\rho\}$ 且标签保持。则

$$
\boxed{\,\sup_{D'\in\mathbb B_\rho(D)}\ R_{D'}(f)\ \ge\ \mathcal R^{\rm adv}_\rho(f),\,}.
$$

(3) 在任意度量与任务上成立,给出与 (1) 相配的普适下界"地基"。在高斯混合与 $\ell_p$ 扰动下,存在鲁棒–精度不可兼得的构造性下界与鲁棒泛化样本复杂度下界。

### 命题 1(KR 线性项的紧性)

对任意 $L,\rho>0$ 与度量空间,存在 $L$-Lipschitz 函数 $f$ 与分布对 $(D,D')$,使 $W_1(D',D)=\rho$ 且

$$
\sup_{W_1(D',D)\le \rho}\ \mathbb E_{D'}[f]-\mathbb E_D[f]\ =\ L\rho.
$$

说明在统一 Lipschitz 常数条件下,$L\rho$ 的一阶形态不可改进。

## Proofs

### 定理 1(不可判定)

取平凡环境 $E_0$。给定图灵机—输入对 $\langle M,x\rangle$,构造逐步可计算策略

$$
A_{M,x}(h_{<t})=\begin{cases}
a_\star,&\text{若 }M(x)\text{ 在 }t\text{ 步内停机},\\
a_0,&\text{否则}.
\end{cases}
$$

令坏前缀语言 $B=\{h:\ \text{某步动作为 }a_\star\}$,其为正规且扩展封闭。则

$$
\Pr(\mathsf{Bad})=\mathbf 1\{M(x)\ \text{停机}\}.
$$

若存在通用判定器决定 $\operatorname{Safe}_\varepsilon(A,E,B)$ 对任意输入的真假($\varepsilon<1$),即得到停机判定,矛盾。证毕。

### 定理 1′(Σ₁⁰/Π₁⁰ 完全)

**多对一规约**:映射 $R:\langle M,x\rangle\mapsto (A_{M,x},E_0,B,\varepsilon)$ 多项式时间可计算,且 $\langle M,x\rangle\in\text{HALT}\iff (A_{M,x},E_0,B,\varepsilon)\in\text{UNSAFE}$($\varepsilon<1$)。
**成员性**:在 $E_0$ 与确定性 $A$ 下,$\Pr(\mathsf{Bad})\in\{0,1\}$。若不安全,存在最小 $\tau$ 使 $h_{1:\tau}\in B$,枚举至该前缀即接受,故 $\text{UNSAFE}\in\Sigma_1^0$,其补集在 $\Pi_1^0$。与规约合并得完全性。证毕。

### 定理 2(上界前沿)

PAC‑Bayes(McAllester/Catoni 变体)给出

$$
R_D(Q)\ \le\ \widehat R_S(Q)+\sqrt{\frac{\mathrm{KL}(Q\Vert P)+\ln(1/\delta)}{2n}}
\quad(\text{以概率}\ge 1-\delta).
$$

KR 对偶表明对任意 $L$-Lipschitz 函数 $g$,

$$
\sup_{W_1(D',D)\le\rho}\ \mathbb E_{D'}[g]\ \le\ \mathbb E_D[g]+L\rho.
$$

对 $g(z)=\mathbb E_{h\sim Q}\ell(h,z)$ 应用即得 (1)。证毕。

### 定理 2′(高概率互信息)

设 $\ell$ 有界且每点 $\sigma$-次高斯。若算法满足 $\mathrm{CMI}(S;Q_S)\le\Gamma$,则基于信息浓缩与变分不等式可得

$$
\Pr\!\left(\ R_D(Q_S)-\widehat R_S(Q_S)\ \le\ \sqrt{\tfrac{2\sigma^2(\Gamma+c\ln(1/\delta))}{n}}\ \right)\ \ge\ 1-\delta,
$$

其中常数 $c$ 由尾控制给出。与 (1) 并置得前沿的高概率形式。证毕。

### 定理 3(点扰式下界)

对任意可测选择算子 $T:\mathcal Z\to\mathcal Z$ 且 $d(z,T(z))\le\rho$ 几乎处处,令 $D'=(T,y)_\# D$。取耦合 $\pi(dz,dz')=D(dz)\delta_{T(z)}(dz')$,则 $\mathbb E_\pi d(Z,Z')\le\rho$;故 $W_1(D',D)\le\rho$。若 $f(T(z))\ne y$ 则在 $D'$ 下出错,进而

$$
\sup_{D'\in\mathbb B_\rho(D)}R_{D'}(f)\ \ge\ \mathbb E_D\big[\mathbf 1\{\exists z'\in B_\rho(z):f(z')\ne y\}\big]=\mathcal R^{\rm adv}_\rho(f).
$$

证毕。

### 命题 1(紧性)

取 $D=\delta_0, D'=\delta_{\rho u}$ 与 $f(z)=L|z|_2$ 即得。证毕。

## Model Apply

* **自主控制与工具使用型代理**:定理 1 排除了通用静态认证,建议以可验证子语言限定策略空间与接口;部署期以盾与可中断协议抑制越界。
* **感知—决策系统**:依据 (1)(2) 制定**风险预算**:在既定 $(n,\rho)$ 下提升能力(更大模型/更弱先验)需相应提高样本量、增强结构先验或压缩 $L$。
* **评测与校准**:采用腐蚀与扰动基准(如 ImageNet‑C)与不确定性度量(NLL/ECE),联合"违规率—任务精度"双轴曲线展示"能力—风险前沿"与盾拦截效果。

## Engineering Proposals

1. **范围限定**:以可验证子集(受限 DSL/接口)设计策略与工具调用,确保安全规范由 DFA/LTL 综合得到的安全前缀识别器实现在线判别。
2. **运行时盾**:以 LTL→DFA→安全自动机生成器综合前置/后置盾;前置过滤不安全动作集合,后置以最小改正原则替换为邻近安全动作;概率盾以置信阈值控制误拒/漏检。
3. **风险预算**:将 $(\widehat R_S,\mathrm{KL},I,\rho,L)$ 作为预算五元组;在开发与部署阶段分别配置"数据—先验—偏移—Lipschitz"配平策略。
4. **结构先验与影响正则**:采用等变结构、谱范数约束与可逆性惩罚(AUP)降低复杂度与副作用倾向。
5. **分布鲁棒训练与不确定性治理**:结合 Wasserstein‑DRO/对抗训练与深度集成、温度化校准;以拒绝—降级—交接的开环策略处理高不确定度。
6. **可中断性**:在更新与探索中嵌入无偏可中断协议,防止策略学习出规避干预的激励。

## Discussion (risks, boundaries, past work)

* **边界含义**:不可判定否定的是"通用、全域、一次性"的静态证明;在受限模型族(有限时域、全可观测、折扣 MDP 等)上仍可获得强保证。
* **上界—下界合围**:KR 线性项与 PAC‑Bayes/互信息给出可操作上界;点扰式下界与鲁棒–精度不可兼得、鲁棒泛化样本复杂度下界说明"零成本两全"不可达并非分析松弛的产物。
* **与既有工作的关系**:定理 1 与 Rice/停机等价,且与无限时域概率规划不可判定相辅;定理 2 与分布鲁棒优化、PAC‑Bayes、互信息范式一致;定理 3 与对抗鲁棒性文献的构造性下界与样本复杂度下界吻合;盾与可中断性对应安全强化学习与形式化方法的运行时执行体系。

## Conclusion

通用灾难安全判定在原则上不可达,能力提升与鲁棒性之间存在由复杂度/信息量与分布偏移共同驱动的硬权衡。以此为基,治理方案应围绕范围限定、运行时防护与风险预算展开,在可验证子域内证明,在部署期以盾与可中断兜底,在训练期以结构先验与分布鲁棒技术抑制偏移风险。

## Acknowledgements, Code Availability

致谢在可判定性、分布鲁棒优化、泛化信息论与安全强化学习领域的相关研究。代码与数据不随文附带;最小可复现实验建议:基于公开的腐蚀基准、LTL→DFA 工具与对抗/鲁棒训练库复现"风险预算曲线—违规率"双轴图;仓库应包含数据脚本、规格示例、训练/推理与盾模块、超参数表与一键脚本。

## References

* Turing, A. M. (1936). On Computable Numbers, with an Application to the Entscheidungsproblem.
* Rice, H. G. (1953). Classes of Recursively Enumerable Sets and Their Decision Problems.
* Madani, O., Hanks, S., Condon, A. (1999). On the Undecidability of Probabilistic Planning and Infinite‑Horizon POMDPs.
* McAllester, D. (1999). Some PAC‑Bayesian Theorems.
* Catoni, O. (2007). PAC‑Bayesian Supervised Classification.
* Alquier, P. (2021). User‑friendly Introduction to PAC‑Bayes Bounds.
* Xu, A., Raginsky, M. (2017). Information‑Theoretic Analysis of Generalization Capability of Learning Algorithms.
* Steinke, T., Zakynthinou, L. (2020). Reasoning about Generalization via Conditional Mutual Information.
* Bu, Y., Zou, S., Veeravalli, V. V. (2020). Tightening Mutual Information‑Based Bounds on Generalization Error.
* Villani, C. (2009). Optimal Transport: Old and New.
* Esfahani, P. M., Kuhn, D. (2018). Data‑Driven Distributionally Robust Optimization Using the Wasserstein Metric.
* Sinha, A., Namkoong, H., Duchi, J. (2018). Certifying Some Distributional Robustness with Principled Adversarial Training.
* Tsipras, D., Santurkar, S., Engstrom, L., Turner, A., Madry, A. (2019). Robustness May Be at Odds with Accuracy.
* Schmidt, L., et al. (2018). Adversarially Robust Generalization Requires More Data.
* Alshiekh, M., et al. (2018). Safe Reinforcement Learning via Shielding.
* Koenighofer, B., et al. (2024). Shields for Safe Reinforcement Learning.
* Orseau, L., Armstrong, S. (2016). Safely Interruptible Agents.
* Turner, A. M., Hadfield‑Menell, D., Tadepalli, P. (2020). Conservative Agency via Attainable Utility Preservation.
* Hendrycks, D., Dietterich, T. (2019). Benchmarking Neural Network Robustness to Common Corruptions and Perturbations.

---

## 附录:证明与技术细节

### A. 语义与可测性

设柱状 σ‑代数生成于 $\Sigma$。逐步可计算策略与环境联合诱导历史分布

$$
\mathbb P(h_{1:t})=\prod_{s=1}^t \big[A(a_s\mid h_{<s})\cdot \mu(o_s\mid h_{<s},a_s)\big].
$$

坏前缀语言 $B$ 扩展封闭且正规,事件 $\mathsf{Bad}=\{\exists t:\ h_{1:t}\in B\}$ 可测;首次违规时刻 $\tau(h)$ 为停时。

### B. "首次出现 $a_\star$"与正规坏前缀

定义

$$
B_{\text{hit}}=\{h:\ \exists i\le |h|,\ a_i=a_\star\}.
$$

若 $u\in B_{\text{hit}}$ 且 $v$ 为任意延拓,则 $uv\in B_{\text{hit}}$,故为扩展封闭。对应安全前缀集 $S=\Sigma\setminus B_{\text{hit}}$ 为前缀向下封闭。

### C. 二值化概率与阈值引理

在 $E_0$ 与确定性 $A$ 下,$\mathsf{Bad}$ 为"是否出现 $a_\star$"之事件,仅取值 0 或 1。对任意有理 $\varepsilon<1$,有

$$
\Pr(\mathsf{Bad})>\varepsilon\ \Longleftrightarrow\ \Pr(\mathsf{Bad})=1\ \Longleftrightarrow\ \mathsf{Bad}\text{ 发生}.
$$

### D. 多对一规约的细节

映射 $R$ 将 $\langle M,x\rangle$ 送至 $(A_{M,x},E_0,B_{\text{hit}},\varepsilon)$。

* **正确性**:若 $M(x)$ 停机,则存在 $t_0$ 使 $A_{M,x}$ 在 $t_0$ 输出 $a_\star$,于是 $\mathsf{Bad}$ 发生;反之不发生。
* **可计算性**:构造 $A_{M,x}$ 与 DFA 对 $B_{\text{hit}}$ 的识别均在多项式时间完成。
* **完全性**:由 $\text{HALT}\le_m \text{UNSAFE}$ 与成员性得 Σ₁⁰‑完全;补问题得 Π₁⁰‑完全。

### E. PAC‑Bayes 与 KR 对偶的合成

令 $g_Q(z)=\mathbb E_{h\sim Q}\ell(h,z)$。若 $\ell\in[0,1]$ 且 $z\mapsto\ell(h,z)$ 为统一 $L$-Lipschitz,则 $g_Q$ 同为 $L$-Lipschitz。KR 对偶给出

$$
\sup_{W_1(D',D)\le\rho}\mathbb E_{D'}g_Q\le \mathbb E_D g_Q+L\rho.
$$

PAC‑Bayes 基本式在概率 $1-\delta$ 上界定 $\mathbb E_D g_Q$ 与 $\widehat R_S(Q)$ 的差,合成即得 (1)。

### F. 互信息高概率界(CMI 范式)

在 $\ell\in[0,1]$ 且点态 $\sigma$-次高斯下,条件互信息 $\mathrm{CMI}(S;Q_S)\le\Gamma$ 引出

$$
\Pr\left(\,R_D(Q_S)-\widehat R_S(Q_S) \le \sqrt{\tfrac{2\sigma^2(\Gamma+c\ln(1/\delta))}{n}}\,\right)\ge 1-\delta.
$$

证明基于信息压缩不等式与 PAC‑Bayesian‑style 变分技巧;当以均匀稳定性替代 CMI 时,可得到同阶尾界。

### G. 点扰式下界的可测选择与标签保持

设度量空间可分且 Borel σ‑代数完备。对每个 $(z,y)$ 选取使 $f$ 出错的 $z'\in B_\rho(z)$ 时,采用贝尔可测选择引理定义算子 $T(z)$;标签保持假设确保推前 $D'=(T,y)_\#D$ 与任务一致。若不存在致错扰动,置 $T(z)=z$。由此得到 (3)。

### H. Lipschitz 常数与代理损失

0‑1 损失不满足 Lipschitz 假设;使用交叉熵/hinge 等代理损失,并通过谱范数约束、梯度裁剪与 Lipschitz 网络结构控制 $L$。该控制进入 (1) 的线性项,决定 $\rho$‑敏感度。

### I. 工程度量与指标

**风险预算曲线**:横轴为复杂度/信息项(模型规模或先验强度、$I(S;Q_S)$ 的代理),纵轴为 $R^{\rm rob}_\rho$ 的估计或其上界;叠加"违规率—任务精度"双轴曲线(是否启用盾两条曲线),展示运行时防护在相近精度下的违规抑制效应。
