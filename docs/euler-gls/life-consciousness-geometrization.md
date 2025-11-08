# 生命—意识几何化：开放系统几何热力学与信息几何的统一

Version: 1.6

**MSC**：80A17；82C05；53D10；62B10；92C42；68Q85
**关键词**：开放系统；接触几何；信息几何；Wasserstein 流；自然梯度；热力学长度；热力学不确定性关系；速度极限；马尔可夫毯；Jarzynski–Sagawa–Ueda；Landauer 界；自指测量；复制子动力学

## 摘要

建立以开放系统几何热力学与信息几何为核心的统一框架：将生命刻画为由持续负熵通量支撑的几何结构，将意识刻画为具有马尔可夫毯分解的自指测量—控制过程，将进化刻画为在 Fisher/Shahshahani 与 Wasserstein 度量上受能量—信息预算制约的最小耗散路径。框架以接触几何刻画非平衡开放系统的势—流与熵产生，以信息几何的 I/m-投影与自然梯度统一推断与学习，以 JKO 变分方案将 Fokker–Planck 动力学表述为自由能的最速下降流；在随机热力学层面，以 Jarzynski 等式及其含互信息的广义形式、热力学不确定性关系与速度极限给出功—精度—时间的普适下界。引入窗化读数与母刻度，将能量—信息—延迟的计量同位化，并提出开放系统有效群延迟与 Toeplitz/Berezin 压缩的操作化读数。给出生命、意识、进化的可检判据与若干主定理，并在附录中给出证明链条。

---

## 0 记号、对象与公理

### 0.1 窗化读数与母刻度

* 逆温记号：$\beta:=(k_{\rm B}T)^{-1}$。文中功—信息等式与连续监测鞅 $\Gamma_t=\exp[-\beta W_t+\beta\Delta F_t-I_t]$（§5）、$\langle e^{-\beta W+\beta\Delta F-I}\rangle=1$（附录 E）皆以此为统一热参量约定。
* 能谱窗核与时间窗分别记为 $w(E)$、$h(t)$；窗化读数记为线性泛函 $\langle f\rangle_{w,h}=\int W(E)\,f(E)\,d\mu(E)$，其中 $W$ 由 $w,h$ 卷合诱导的权。
* **以散射—谱移母刻度同一式作为全局刻度（母尺）**：令散射矩阵 $\mathsf S(E)$ 的**总散射相位** $\varphi(E):=\arg\det \mathsf S(E)$（等价于谱移函数 $\xi(E)=\varphi(E)/(2\pi)$），并定义 Wigner–Smith **群延迟矩阵** $\mathsf Q(E):=-i\,\mathsf S^\dagger(E)\,\partial_E\mathsf S(E)$。则

  $$\boxed{\ \frac{\varphi'(E)}{2\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\mathrm{tr}\,\mathsf Q(E)\ }.$$

  上式在本文中用作能量—信息—延迟的共同刻度（在开放系统推广处用 $\mathsf Q_{\rm eff}$ 代替）。

### 0.2 接触几何—开放系统

* 接触流形 $(\mathcal C,\alpha)$ 取 Darboux 坐标 $(x^i,y_i,z)$ 满足 $\alpha=dz-y_i\,dx^i$。接触哈密顿量 $H$ 确定向量场 $X_H$ 由 $\iota_{X_H}\alpha=-H$、$\iota_{X_H}d\alpha=dH-(\mathcal R H)\alpha$ 给出，其中 $\mathcal R$ 为 Reeb 向量场，满足 $\alpha(\mathcal R)=1$、$\iota_{\mathcal R}d\alpha=0$；以此统一势—力—流与熵产生的几何描述，用于非平衡开放系统的端口耦合。

### 0.3 信息几何—自然梯度

* 概率流形 $\mathcal P=\{p_\theta\}$ 装备 Fisher–Rao 度量 $g_{ij}(\theta)=\mathbb E_\theta[\partial_i\log p_\theta\,\partial_j\log p_\theta]$。自然梯度记为 $\widetilde\nabla f=g^{-1}\nabla f$。**I（information）/e（exponential）-投影最小化 $D_{\rm KL}(p\Vert q)$，m（mixture/M）-投影最小化 $D_{\rm KL}(q\Vert p)$。**

### 0.4 Wasserstein–JKO 与梯度流

* $W_2$–Wasserstein 空间上，自由能泛函 $\mathcal F[p]=\int p\log p+\int Vp$ 的最速下降流对应 Fokker–Planck 方程；离散化由 JKO 方案 $p_{k+1}=\arg\min_p\{\mathcal F[p]+\tfrac{1}{2h}W_2^2(p,p_k)\}$ 给出。

### 0.5 观测—计算与误差纪律

* 读数算子采用 Toeplitz/Berezin 压缩 $\mathsf K_{w,h}=\Pi_w M_W \Pi_w$，保证正定与半经典一致。
* 误差预算遵循"Nyquist–Poisson–Euler–Maclaurin（NPE）"有限阶纪律：$\varepsilon_{\rm tot}=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail}$，并以尾项熵通量 $\mathscr T_R$ 设停机判据（见附录 F）。

### 0.6 马尔可夫毯与自指测量

* 将系统变量划分为内部 $s_{\rm int}$、外部 $s_{\rm ext}$、感受野 $o$、动作 $a$，满足条件独立与遮蔽性质；自指测量—控制以变分自由能 $\mathcal F=\mathbb E_{q_\phi}[\log q_\phi(s\mid o)-\log p_\theta(s,o)]$ 为势函数。

---

## 1 开放系统的几何热力学结构

接触几何为热力学状态空间提供天然的 $(2n\!+\!1)$ 维结构，热力学第一/第二定律对应接触变换下的不变量与散度项；开放系统可通过端口（供—耗）与环境耦合，形成稳态通量网络并在非平衡下维持有序结构。该几何化方案与"端口-Hamilton/Dirac 结构"一致，并已系统用于非平衡热力学与工程系统建模。上述观点与形式在现有文献中得到系统阐述与统一综述。([MDPI][1])

随机热力学将功、热与熵产生提升到单轨道层级，给出普适的涨落定理与等式（Jarzynski 等式）；在含测量—反馈的开放系统中，互信息修正项刻画"信息即资源"的可提取功，对应的广义等式给出功—信息预算闭合。([Terpconnect][2])

---

## 2 信息几何与自由能梯度流

在统计流形上，Fisher–Rao 度量诱导的自然梯度为推断与学习提供最速下降方向；其与变分贝叶斯的 ELBO 最小化一致。另一方面，Fokker–Planck 动力学可视作 $W_2$ 空间上自由能的最速下降流（JKO 方案），从而把"扩散—势景"与"最优传输—下降"合一。两者共同给出"从数据到动力学"的几何桥。([Vielbein][3])

在有限时间驱动下，线性响应近似中可定义摩擦张量与热力学度量，耗散功的下界由热力学长度刻画，最小耗散协议为该度量上的测地。该结果在分子尺度驱动与信息加工中具有直接可检性。([物理评论链接管理器][4])

---

## 3 概念刻画

**定义 1（生命 = 负熵几何结构）**：设开放系统由接触系统 $(\mathcal C,\alpha,H)$ 与概率流形 $\mathcal P$ 耦合。系统熵满足 $\dot S_{\rm sys}=\dot S_{\rm e}+\dot S_{\rm i}$、$\dot S_{\rm i}\ge 0$。若存在持久的负熵通量 $J_N:=-\dot S_{\rm e}>0$ 使 $\sup_{t}S_{\rm sys}(t)<\infty$，并且接触流在给定端口约束下是输入—状态稳定与可达，则称处于生命态。该生命态由负熵通量支撑的几何结构维持。

**定义 2（意识 = 自指测量过程）**：设生成模型 $p_\theta(s,o)$、识别密度 $q_\phi(s\mid o)$ 在马尔可夫毯 $(s_{\rm int},s_{\rm ext};o,a)$ 的遮蔽条件下演化，其更新由 **m-投影（最小化 $D_{\rm KL}(q_\phi\Vert p_\theta)$）/自然梯度** 实现对 $\mathcal F(\phi,\theta)$ 的下降；测量—反馈引入互信息 $I$，功—自由能差满足 $\langle W\rangle\ge \Delta F-k_{\rm B}T\langle I\rangle$。称该最小化—控制闭环为意识的抽象。([Nature][5])

**定义 3（进化 = 几何优化路径）**：在策略单纯形 $\Delta^{n-1}$ 上，**若存在势函数 $V(\mathbf x)$ 使 $f_i=\partial_{x_i}V$（潜在博弈/可积）**，则复制子动力学 $\dot x_i=x_i(f_i-\bar f)$ 是 Shahshahani/Fisher 度量的**梯度流**；进化轨道是给定预算与环境约束下，Fisher 或 Wasserstein 度量上最小化热力学长度与熵产生的曲线。([arXiv][6])

---

## 4 主定理与可检判据

### 定理 A（生命的负熵—稳态判据）

**陈述**：开放接触—随机耦合系统存在生命态当且仅当满足：
(i) $\dot S_{\rm i}\ge 0$；(ii) 存在 $J_N>0$ 使 $\limsup_{t\to\infty}S_{\rm sys}(t)<\infty$；(iii) 端口约束下接触流对小扰动输入—状态稳定（ISS）且可达。

**证明概述**：从控制体熵平衡式与 $\dot S_{\rm i}\ge 0$ 出发，$\int_0^T(\dot S_{\rm i}-J_N)\,dt$ 有界推出 $S_{\rm sys}$ 有界；接触系统的守恒—产生分解与端口能量守恒给出稳态通量网络；ISS 与可达确保稳态在小扰动下维持。详见附录 A。

### 定理 B（意识的功—信息下界与自然梯度闭合）

**陈述**：在马尔可夫毯成立的自指测量—反馈过程中，平均功满足 $\langle W\rangle \ge \Delta F-k_{\rm B}T\langle I\rangle$。当识别/参数的更新取 Fisher 自然梯度（步长受几何约束）时，$\mathcal F$ 的下降率在局部最优，并与能量代价通过 Landauer 界、热力学度量共同约束。

**证明概述**：由含互信息的广义 Jarzynski 等式经 Jensen 不等式得功—信息下界；自然梯度是 Fisher 度量下最速下降方向，结合 Landauer 最小散热与有限时间擦除代价得闭合预算。详见附录 B、E。([物理评论链接管理器][7])

### 定理 C（进化的最小耗散与速度极限）

**陈述**：控制参数 $\lambda(t)$ 驱动非平衡过程于时长 $\tau$ 内转移时，线性响应下额外耗散功下界为 $\langle W_{\rm ex}\rangle\ge \mathcal L^2/\tau$，其中热力学长度 $\mathcal L=\int_0^\tau \sqrt{\dot\lambda^\top \zeta(\lambda)\dot\lambda}\,dt$，最小耗散协议为测地；马尔可夫过程的转移速度受熵产生与动力活度的速度极限约束。**在潜在博弈/可积条件下**，复制子动力学为 Shahshahani 度量的梯度流，并与上述"测地—最优协议"一致。

**证明概述**：由热力学度量构造与 Cauchy–Schwarz 给出 $\langle W_{\rm ex}\rangle$ 下界；速度极限由动力活度—熵产生权衡不等式给出；复制子—自然梯度同构见附录 C。([物理评论链接管理器][4])

### 定理 D（热力学不确定性关系的生命—计量界）

**陈述**：稳态生化/信号网络中，任意可数流的相对方差—均值精度受下界 $\mathrm{Var}(J_t)/\langle J_t\rangle^2 \ge 2/(t\,\Sigma)$（或等价形式）约束，其中 $\Sigma$ 为熵产生速率；故给定精度 $\epsilon$ 至少需要代价 $\gtrsim 2k_{\rm B}T/\epsilon^2$。

**证明概述**：由大型偏差与涨落定理导出 TUR，下界与稳态马尔可夫网络普适，形成"能量—精度"的生命—感知计量极限。详见附录 G。([物理评论链接管理器][8])

---

## 5 窗化读数、有效群延迟与实验协议

**开放系统有效群延迟**：约定 $A^\sharp:=A^\dagger$。当响应/散射函数 $\mathsf G(\omega)$ 非酉时，取其极分解 $\mathsf G(\omega)=\mathsf U(\omega)\mathsf H(\omega)$（$\mathsf U$ 酉、$\mathsf H$ 正定），并以酉因子定义

$$\boxed{\ \mathsf Q_{\rm eff}(\omega):=-i\,\mathsf U^\dagger(\omega)\,\partial_\omega \mathsf U(\omega)\ }.$$

因而 $(2\pi)^{-1}\mathrm{tr}\,\mathsf Q_{\rm eff}\in\mathbb R$，并与 $\rho_{\rm rel}$ 同位；配合窗化取迹 $\big\langle (2\pi)^{-1}\mathrm{tr}\,\mathsf Q_{\rm eff}\big\rangle_{w,h}$ 可进行跨尺度标定。
**读数算子与误差纪律**：以 $\mathsf K_{w,h}$ 实现窗化算子读数，误差预算由 NPE 有限阶纪律控制；尾项熵通量 $\mathscr T_R$ 的收敛性给出停机准则（附录 F）。
**协议与可检性**：（i）连续监测构造鞅 $\Gamma_t=\exp[-\beta W_t+\beta\Delta F_t-I_t]$ 检验功—信息等式；（ii）比较行为/神经读数与 $\langle (2\pi)^{-1}\mathrm{tr}\,\mathsf Q_{\rm eff}\rangle_{w,h}$ 的协变性；（iii）在微系统上以最小耗散测地协议验证热力学长度界。广义等式与度量—测地的实验可行性已在统计物理与生物物理语境中反复论证。([物理评论链接管理器][7])

---

## 6 意识的几何：马尔可夫毯、m-投影与连续测量

意识视为自指测量—控制：内部生成模型与识别密度在马尔可夫毯遮蔽下以 **m-投影（逆向 KL）/自然梯度** 最小化 $\mathcal F$，行动作为策略控制以最小化预期自由能。该过程的物理可达界由 Landauer 最小散热、Jarzynski–Sagawa–Ueda 功—信息不等式与热力学度量共同决定；若观测为连续型，可在 Belavkin 过滤下得到后验态的随机主方程，实现意识—观测的连续时间闭合。([Nature][5])

---

## 7 进化的几何：自然选择与自然梯度的一致性

**在潜在博弈（存在 $V$ 使 $f_i=\partial_{x_i}V$）条件下**，复制子动力学是 Shahshahani（亦即 Fisher 在单纯形上的限制）度量的**梯度流**；因而"适应度上升"与在 Fisher 度量下的最速上升/下降（视势函数定义而定）等价。将变异—选择—迁移写为 Wasserstein 空间上的自由能下降流，可与 JKO 方案统一，并在热力学长度与速度极限的框架下给出"代价—时间—精度"的三重权衡。([arXiv][6])

---

## 8 生命—意识的母刻度同位化

将母刻度 $\varphi'/(2\pi)=\rho_{\rm rel}=(2\pi)^{-1}\mathrm{tr}\,\mathsf Q$ 推广到开放系统，以 $\mathsf Q_{\rm eff}$ 替换 $\mathsf Q$，在代谢—信号—神经—行为多层上以窗化读数实现能量—信息—延迟的同位量纲；与 Toeplitz/Berezin 压缩的算子读数兼容，为跨尺度数据同化与反演提供统一刻度。配合 Zeckendorf 可逆日志对窗化载荷做整数化记账，保证跨窗可复算与一致对接。

---

## 附录 A：开放系统熵收支与定理 A 的证明

对控制体 $\Omega$ 与边界 $\partial\Omega$，熵平衡为
$$
\frac{d S_{\rm sys}}{dt}=\int_\Omega \sigma(\mathbf x)\,d\mathbf x-\int_{\partial\Omega}\frac{\mathbf J_q\!\cdot\!\mathbf n}{T}\,dA+\sum_k\int_{\partial\Omega}\frac{\mu_k}{T}\,\mathbf J_k\!\cdot\!\mathbf n\,dA,
$$
其中 $\sigma\ge 0$。令 $\dot S_{\rm e}=-\int_{\partial\Omega}\big(\mathbf J_q/T-\sum_k\mu_k\mathbf J_k/T\big)\cdot\mathbf n\,dA$，则 $\dot S_{\rm sys}=\dot S_{\rm e}+\dot S_{\rm i}$、$\dot S_{\rm i}=\int_\Omega \sigma\ge 0$。若存在 $J_N=-\dot S_{\rm e}>0$ 使 $\int_0^\infty(\dot S_{\rm i}-J_N)\,dt$ 有界，则 $\sup_t S_{\rm sys}(t)<\infty$。接触系统写作 $X_H=X_{\rm cons}+X_{\rm prod}$，其中 $X_{\rm prod}$ 的散度等于 $\sigma$；端口功率平衡与 ISS 给出稳态可达性，故生命态与三条件互为充要。参考接触热力学与耗散结构之稳定性的一般论证。([MDPI][1])

---

## 附录 B：m-投影、自然梯度与 ELBO 单调性

在指数族近似与光滑约束下，ELBO 的欧氏梯度经 Fisher 预条件化得到自然梯度步 $\Delta\theta=-\eta\,g^{-1}\nabla_\theta \mathcal F$。由于 $g$ 正定，取足够小的 $\eta$ 可保证 $\mathcal F$ 在每步下降且下降率在局部意义下最优；这等价于统计流形上的最速下降。信息几何的标准结果保证 I/m-投影的正交分解与唯一性（在适当凸性假设下）。([Vielbein][3])

---

## 附录 C：复制子动力学的 Shahshahani 几何证明

在单纯形 $\Delta^{n-1}$ 上取 Shahshahani 度量 $g_{ij}=\delta_{ij}/x_i$。令势函数 $V(\mathbf x)$ 的欧氏梯度为 $f_i=\partial_{x_i}V$。在单纯形约束 $\sum_i x_i=1$ 下，自然梯度需先投影到切空间：

$$\mathrm{grad}_g V=\Pi_x\,g^{-1}\nabla V,\qquad \Pi_x:\ T_x\mathbb R^n\to T_x\Delta^{n-1}.$$

因 $g^{-1}\nabla V=(x_i f_i)_i$，故

$$(\mathrm{grad}_g V)_i=x_i f_i - x_i\sum_j x_j f_j=x_i\big(f_i-\bar f\big),\ \ \bar f=\sum_j x_j f_j,$$

从而得到复制子方程 $\dot x_i=x_i(f_i-\bar f)$。该结果等价于"复制子 = Fisher 自然梯度"，已在信息几何—演化博弈文献中系统阐述。([arXiv][6])

---

## 附录 D：热力学长度与最小耗散协议

线性响应下，额外耗散功 $\langle W_{\rm ex}\rangle=\int_0^\tau \dot\lambda^\top\zeta(\lambda)\dot\lambda\,dt$。设 $\mathcal L=\int_0^\tau \sqrt{\dot\lambda^\top\zeta(\lambda)\dot\lambda}\,dt$，由 Cauchy–Schwarz 不等式得 $\langle W_{\rm ex}\rangle\ge \mathcal L^2/\tau$。等号当且仅当 $\sqrt{\zeta}\dot\lambda$ 为常模，即 $\lambda$ 沿测地恒速推进。该定理与"热力学度量—最优协议"完全一致。([物理评论链接管理器][4])

---

## 附录 E：功—信息不等式与 Landauer 界

带反馈的广义 Jarzynski 等式为 $\langle e^{-\beta W+\beta\Delta F-I}\rangle=1$。由 Jensen 不等式得 $\langle W\rangle\ge \Delta F-k_{\rm B}T\langle I\rangle$。对逻辑不可逆过程，最小散热满足 Landauer 界 $\Delta Q\ge k_{\rm B}T\ln 2$；有限时间擦除的最小功—散热由具体实现与协议决定，但存在严格的速率—代价权衡。([物理评论链接管理器][7])

---

## 附录 F：NPE 有限阶误差与停机判据

令窗化尾项熵通量 $\mathscr T_R=\int_{\mathbb R\setminus[-R,R]}W(E)\,|\rho_{\rm rel}(E)|\,dE$。若 $\int_{R_0}^\infty \mathscr T_R\,dR/R<\infty$ 且 $\lim_{R\to\infty}\mathscr T_R=0$，则在给定容差 $\epsilon$ 下存在 $R_\epsilon$ 使 $\mathscr T_{R_\epsilon}<\epsilon$。别名与 EM 余项分别由 Nyquist 条件与有限阶公式给出上界；综合得停机门槛与实验/仿真采样率选择准则。

---

## 附录 G：热力学不确定性关系与速度极限

稳态马尔可夫网络的 TUR 给出 $\mathrm{Var}(J_t)/\langle J_t\rangle^2 \ge 2/(t\,\Sigma)$ 的级数下界，或等价的 $\epsilon^{-2}$-型能量—精度成本；速度极限则给出任意给定熵产生下的最短转移时间下界，动力活度为关键尺度。二者共同构成生命—感知—行动的"精度—代价—时间"几何界。([物理评论链接管理器][8])

---

## 参考文献（选）

Seifert, U. *Stochastic thermodynamics, fluctuation theorems and molecular machines*. Rep. Prog. Phys. 75, 126001 (2012). ([Terpconnect][2])
Sagawa, T.; Ueda, M. *Generalized Jarzynski Equality under Nonequilibrium Feedback Control*. Phys. Rev. Lett. 104, 090602 (2010). ([物理评论链接管理器][7])
Sivak, D.A.; Crooks, G.E. *Thermodynamic Metrics and Optimal Paths*. Phys. Rev. Lett. 108, 190602 (2012). ([物理评论链接管理器][4])
Jordan, R.; Kinderlehrer, D.; Otto, F. *The variational formulation of the Fokker–Planck equation*. SIAM J. Math. Anal. 29, 1–17 (1998). ([SIAM E-Books][9])
Barato, A.C.; Seifert, U. *Thermodynamic Uncertainty Relation for Biomolecular Processes*. Phys. Rev. Lett. 114, 158101 (2015). ([物理评论链接管理器][8])
Shiraishi, N.; Funo, K.; Saito, K. *Speed Limit for Classical Stochastic Processes*. Phys. Rev. Lett. 121, 070601 (2018). ([物理评论链接管理器][10])
Bravetti, A. *Contact Hamiltonian Dynamics: The Concept and Its Use*. Entropy 19, 535 (2017)；*Contact geometry and thermodynamics*. IJGMMP 16 (2019). ([MDPI][1])
van der Schaft, A.; Maschke, B. *Geometry of Thermodynamic Processes*. Entropy 20, 925 (2018). ([PMC][11])
Amari, S.; Nagaoka, H. *Methods of Information Geometry*. AMS (2000)；Amari, S. *Natural gradient works efficiently in learning*. Neural Computation 10, 251–276 (1998). ([Vielbein][3])
Friston, K. *The free-energy principle: a unified brain theory?* Nat. Rev. Neurosci. 11, 127–138 (2010)；Parr, T.; Pezzulo, G.; Friston, K. *Active Inference*. MIT Press (2022). ([Nature][5])
Landauer, R. *Irreversibility and Heat Generation in the Computing Process*. IBM J. Res. Dev. 5, 183–191 (1961)；Giorgini, L.T. *Thermodynamic cost of erasing information in finite time*. Phys. Rev. Research 5, 023084 (2023). ([worrydream.com][12])
Harper, M. *Information Geometry and Evolutionary Game Theory*. arXiv:0911.1383 (2009). ([arXiv][6])

---

[1]: https://www.mdpi.com/1099-4300/19/10/535?utm_source=chatgpt.com "Contact Hamiltonian Dynamics: The Concept and Its Use"
[2]: https://terpconnect.umd.edu/~cjarzyns/CHEM-CHPH-PHYS_703_Spr_20/resources/Rep%20Prog%20Phys%202012%20Seifert.pdf?utm_source=chatgpt.com "Stochastic thermodynamics, fluctuation theorems and ..."
[3]: https://vielbein.it/pdf/Traduzioni/2000-Amer-Methods_of_Information_Geometry.pdf?utm_source=chatgpt.com "Methods of Information Geometry - Vielbein"
[4]: https://link.aps.org/doi/10.1103/PhysRevLett.108.190602?utm_source=chatgpt.com "Thermodynamic Metrics and Optimal Paths | Phys. Rev. Lett."
[5]: https://www.nature.com/articles/nrn2787?utm_source=chatgpt.com "The free-energy principle: a unified brain theory?"
[6]: https://arxiv.org/abs/0911.1383?utm_source=chatgpt.com "Information Geometry and Evolutionary Game Theory"
[7]: https://link.aps.org/doi/10.1103/PhysRevLett.104.090602?utm_source=chatgpt.com "Generalized Jarzynski Equality under Nonequilibrium ..."
[8]: https://link.aps.org/doi/10.1103/PhysRevLett.114.158101?utm_source=chatgpt.com "Thermodynamic Uncertainty Relation for Biomolecular ..."
[9]: https://epubs.siam.org/doi/10.1137/S0036141096303359?utm_source=chatgpt.com "The Variational Formulation of the Fokker--Planck Equation"
[10]: https://link.aps.org/doi/10.1103/PhysRevLett.121.070601?utm_source=chatgpt.com "Speed Limit for Classical Stochastic Processes | Phys. Rev. Lett."
[11]: https://pmc.ncbi.nlm.nih.gov/articles/PMC7512512/?utm_source=chatgpt.com "Geometry of Thermodynamic Processes - PMC"
[12]: https://worrydream.com/refs/Landauer_1961_-_Irreversibility_and_Heat_Generation_in_the_Computing_Process.pdf?utm_source=chatgpt.com "Irreversibility and Heat Generation in the Computing Process"
