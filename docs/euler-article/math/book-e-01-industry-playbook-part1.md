# 册 E｜行业卷（Playbook）

> 体例：每章给出**对象与变量**→**法则化目标函数**→**判据/定理（含证明要点）**→**执行规程（可复演步骤）**→**度量指标**。符号沿用册 A–C：窗读数 $\langle f\rangle_W$、相位—密度 $\varphi'(E)=\pi\rho(E)$、NPE 三分、KL/I-投影、谱隙 $\Delta$、采样阈 $\nu_r\ge 2B$。

---

## E-1｜家庭/团队：共识采样会（公开—镜断—三修—闭环）

### 对象与变量

* 议题状态信号 $y(t)$，有效带宽 $B$。
* 团队意见向量 $x_k\in\mathbb R^n$（第 $k$ 轮），共识迭代 $x_{k+1}=W x_k$，$W\mathbf 1=\mathbf 1$。
* 任务池 $\mathcal X=\{a_1,\dots,a_m\}$，每任务日损失 $l_t(a)$，权重 $w_t\in\Delta_m$。

### 法则化目标函数

* **会频—传播—跟踪折衷**：在会期间隔 $\Delta t=1/\nu_r$ 与迭代轮数 $K$ 下，最小化

$$
J_{\text{sync}}(\Delta t,K)=\underbrace{\lambda_2(W)^K|x_0-\bar y\,\mathbf 1|^2}_{\text{传播误差}}
+\underbrace{c\,|\dot y|_\infty^2\,\Delta t^2}_{\text{跟踪误差}},
$$

受 $\nu_r\ge 2B$（防混叠）的约束。
* **执行后悔**（5 分钟闭环）：$\displaystyle \mathcal R_T=\sum_{t=1}^T l_t(a_t)-\min_{a\in\mathcal X}\sum_{t=1}^T l_t(a)$。

### 判据/定理

**定理 1（Nyquist 化治理）** 若 $\nu_r<2B$ 则折叠能量 $E_{\text{alias}}>0$（见 C-5），会后共识将进入伪稳态；必要阈 $\nu_r^{\min}=2B$。
*证明要点*：采样频谱周期化叠加，$|\omega|>\pi\nu_r$ 处能量折回主带。

**命题 2（传播—跟踪界）** 若 $|\dot y|_\infty\le L$，则

$$
|x_K-\bar y\,\mathbf 1|\le \lambda_2(W)^K|x_0-\bar y\,\mathbf1|,\qquad
|y-\bar y|_\infty\le \tfrac{L}{2}\Delta t .
$$

*证明要点*：谱分解与均值值定理（零阶保持误差）。

**定理 3（闭环次线性后悔）** 用 Mirror Descent/指数权重（C-4）在 5 分钟粒度执行，则 $\mathcal R_T\le O(\sqrt{T})$。
*证明要点*：Bregman 三角恒等式与望远镜求和。

**命题 4（镜中复断的净效）** 设角色互换群 $G$，成本函数 $C$。若

$$
\Delta_{\mathrm{net}}:=\sup_{g\in G}\big|\mathbb E[C(x,D(x))]-\mathbb E[C(g\!\cdot\!x,D(g\!\cdot\!x))]\big|\le \eta,
$$

则"镜断"通过；对称化 $D^{\text{sym}}(x)=\mathbb E_{g}D(g\!\cdot\!x)$ 在凸损失下不劣。
*证明要点*：群平均 + Jensen。

### 执行规程

1. **会前公开窗秤**：发布数据窗 $W$（来源/时段）与刻度（单位/目标）。
2. **定频与轮次**：按近 4–8 周估得 $B$，设 $\nu_r=2B(1+\delta)$，选 $K$ 使 $\lambda_2(W)^K\le \varepsilon/(2|x_0-\bar y\,\mathbf1|)$。
3. **镜断评审**：对关键分配做角色互换评审，若 $p$-值显著或 $\Delta_{\mathrm{net}}>\eta$ 则返工。
4. **三修闭合**：为重要结论填 NPE 日志，使三项上界各 $\le \varepsilon/3$（C-2/C-8）。
5. **发布最小闭环**：每项生成 1 个 5 分钟动作，按指数权重更新 $w_{t+1}\propto w_t\exp(-\eta g_t)$。

### 度量指标

* **争议率**（会后 48h 内反对票比例）$\downarrow$。
* **按期率**（闭环按时完成率）$\uparrow$。
* **净增率** $G=\Delta S-\lambda\Delta C>0$ 的任务比例$\uparrow$。
* **折叠指示** $E_{\text{alias}}\to 0$。

---

## E-2｜教育：课程闭环与导师指针

### 对象与变量

* 概念图 $G=(V,E)$（先修拓扑），每节点 $v$ 难度 $d_v$、记忆时常 $\tau_v$。
* 学生状态 $p_{v,t}\in[0,1]$（即时回忆概率），进度窗 $W_T$（近 $T$ 日）。
* 导师子空间 $\mathcal S_{\text{mentor}}$，学生表征 $x_t$。

### 法则化目标函数

* **课程目标**：最小化外测损失 $L_{\text{test}}$ 并抑制遗忘成本 $\Phi$：

$$
\min_{\text{序列}}\ \underbrace{L_{\text{test}}}_{\text{泛化}}
+\lambda \underbrace{\sum_{v\in V}\int_0^T \big(1-p_{v,t}\big)_+\,dt}_{\text{累计遗忘}} .
$$

* **导师对齐**：最大化投影增长 $|P_{\mathcal S_{\text{mentor}}}x_t|$。

### 判据/定理

**命题 1（泛化界）** 若模型类 $\mathcal F$ 的 Rademacher 复杂度为 $\mathfrak R_n(\mathcal F)$，则

$$
L_{\text{test}}\le L_{\text{train}}+O\big(\sqrt{\mathfrak R_n(\mathcal F)}\big).
$$

*证明要点*：标准经验过程不等式。

**定理 2（间隔复现的最优阈）** 记忆模型 $p_{v}(t)=\exp(-\Delta t/\tau_v)$。若要求 $p_v(t)\ge p_0$ 恒成立，则复现间隔

$$
\Delta t_v^\star=\tau_v \ln(1/p_0).
$$

若复现使 $\tau_v$ 乘以 $1+\alpha$（巩固效应），则第 $k$ 次后最优间隔近似几何增长

$$
\Delta t_{v,k}^\star\approx \tau_v (1+\alpha)^{k-1}\ln(1/p_0).
$$

*证明要点*：把罚项写作 $\int (1-e^{-\Delta t/\tau})_+ dt$ 的分段常数最小化；巩固效应线性化逼近。

**命题 3（导师指针收敛）** 若谱隙 $\Delta_{\text{mentor}}>0$，学生在"模仿—纠偏"更新 $x_{t+1}=\Pi\big(x_t+\eta P_{\mathcal S_{\text{mentor}}}(z_t-x_t)\big)$ 下，

$$
|P_{\mathcal S_{\text{mentor}}}x_t|\ \nearrow,\quad
|x_t-P_{\mathcal S_{\text{mentor}}}x_t|\ \searrow\ \text{以 } e^{-\Delta_{\text{mentor}} t}.
$$

*证明要点*：非扩张投影 + 线性收敛由谱隙给界。

### 执行规程

1. **建图与定参**：构建 $G$，估 $\tau_v$、设 $p_0\in(0.7,0.9)$。
2. **排课**：按拓扑排序 + 难度递增；对每 $v$ 计划复现时点 $t_{v,k}=t_{v,1}+\sum_{j\le k}\Delta t_{v,j}^\star$。
3. **导师对齐**：每周测 $|P_{\mathcal S_{\text{mentor}}}x_t|$，若 $\downarrow$ 则加"模仿窗口"并用 KL-小步调整策略分布（选题权重）。
4. **评测**：预注册测验、校准曲线、外测 $L_{\text{test}}$。

### 度量指标

* 外测 $L_{\text{test}}\downarrow$ 且校准良好；
* 遗忘面积 $\sum_v\int (1-p_{v,t})_+dt \downarrow$；
* $|P_{\mathcal S_{\text{mentor}}}x_t|\uparrow$。

---

## E-3｜医疗：诊断—治疗—康复三段控制

### 对象与变量

* 病程状态 $x_t\in\mathbb R^d$（生理/行为指标），观测 $o_t$，治疗控制 $u_t$。
* 诊断概率 $p_t=\Pr(\theta=1|o_{\le t})$，校准窗 $W$。
* 成本 $c(x_t,u_t)$（毒副作用/资源），康复动作集 $\mathcal X$（5 分钟闭环）。

### 法则化目标函数

$$
\min_{u_{0:T-1}}\ \mathbb E\Big[\underbrace{\sum_{t=0}^{T-1} c(x_t,u_t)}_{\text{治疗成本}}
+\underbrace{\lambda\,\Phi(x_T)}_{\text{末端损失}}\Big]
\quad \text{s.t.}\quad x_{t+1}=F(x_t,u_t)+\xi_t .
$$

### 判据/定理

**命题 1（诊断校准）** 概率输出 $p$ 的 Brier 分数

$$
\mathrm{Brier}=\tfrac1n\sum_{i=1}^n (p_i-y_i)^2
$$

在重校准（等分箱拟合/等温回归）后下降，且校准曲线逼近对角线。
*证明要点*：校准是对 $p\mapsto \tilde p$ 的单调变换，优化经验平方损失。

**定理 2（线性二次情形的闭式治疗）** 若 $F(x,u)=Ax+Bu$，$c(x,u)=x^\top Qx+u^\top Ru$，则最优控制 $u_t=-K_tx_t$，$K_t$ 由离散 Riccati 递推给出。
*证明要点*：动态规划 Bellman 方程。

**命题 3（康复期次线性遗憾）** 以 Mirror Descent 在动作集 $\mathcal X$ 上做 5 分钟闭环（C-4），则康复阶段

$$
\mathcal R_T=O(\sqrt{T})\quad(\text{在 }L\text{-Lipschitz 损失下}).
$$

*证明要点*：同 C-4。

**命题 4（守恒清账）** 若治疗期存在资源失衡/依从性缺口，视为源项 $\sigma$ 破坏守恒：$\partial_t\rho+\nabla\!\cdot J=\sigma$。最小补偿流 $u^\star=-\nabla\phi$ 由 $-\Delta\phi=\sigma$ 解得，代价为 $|\nabla\phi|_2^2$。
*证明要点*：变分法与图拉普拉斯等价。

### 执行规程

1. **诊断**：训练—校准—外部验证；报告 $\mathrm{Brier}$、ROC、校准曲线。
2. **治疗**：若近线性，做 LQR；非线性用 MPC（滚动地平线）近似。
3. **清账**：识别 $\sigma$（依从性缺口/资源拖欠），解 $-\Delta\phi=\sigma$ 制定最小补偿。
4. **康复**：定义日动作集 $\mathcal X$（步行、呼吸操、冥想等），5 分钟闭环 + KL-小步更新配重；周检相位—密度一致

$$
\int \varphi'(E)W(E)\,dE\approx \pi\int \rho(E)W(E)\,dE .
$$

### 度量指标

* 诊断校准度（ECE/NLL/Brier）$\downarrow$。
* 总成本 $\sum c$ 与末端损失 $\Phi$ $\downarrow$。
* 复发率 $\downarrow$、功能评分 $\uparrow$。
* 清账残差 $|\sigma|_{\mathcal H^{-1}}\downarrow$。
