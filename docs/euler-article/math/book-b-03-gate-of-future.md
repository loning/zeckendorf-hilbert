## 第三门｜未之门（命纹章・问符法・地脉阵・奇迹门）

> 体例同前：每条含**法条**、**数学推理**、**可检步骤**，并统一使用册 A 的记号与公设。

---

### 9. 命纹章（"命"＝稳态，"运"＝瞬态漂移）

**法条**
"命"是长窗下的稳态分布 $\pi$；"运"是短窗内的瞬态漂移 $\delta_t$。改命不是改起点，而是**改核/改秤**使 $\pi$ 迁移。

**数学推理**
(1) 令日常行为马尔可夫核为 $P$，当 $P$ 遍历且非周期，则存在唯一稳态 $\pi$ 满足 $\pi^\top P=\pi^\top$。任意初值分布 $x^{(0)}$ 的演化 $x^{(t)}=x^{(0)}P^t$ 可分解为

$$
x^{(t)}=\pi+\delta_t,\qquad |\delta_t|_2\le C\,|\lambda_2(P)|^t\,|x^{(0)}-\pi|_2 ,
$$

其中 $|\lambda_2(P)|<1$ 为次特征值模长。瞬态项 $\delta_t$ 指"运"。
(2) **仅改起点不改命**：若保持 $P$ 不变，仅换初值 $x^{(0)}$，则 $t\to\infty$ 时 $x^{(t)}\to \pi$，稳态不变。
(3) **改命的充要条件**：要使 $\pi$ 迁移，必须改核 $P\mapsto \widetilde P$ 或改秤（代价/奖励）以致最优策略核改变。微扰一阶给

$$
\widetilde\pi^\top-\pi^\top \approx \pi^\top(\widetilde P-P)\,Z,\quad Z=\sum_{k=0}^\infty (P-\mathbf 1\pi^\top)^k ,
$$

表明稳态变动由核差与基本解 $Z$ 决定。
(4) **长窗读数**：以长窗 $W_T(t)=\tfrac1T \mathbf 1_{[0,T)}(t)$ 平均，$\langle x\rangle_{W_T}\to \pi$（遍历定理）。短窗平均保留 $\delta_t$ 的相当份额，即"当日之运"。
(5) 目标"方向—配重一致性"可照 $\varphi'(E)=\pi\,\rho(E)$ 校验：若方向（相位导数）与资源密度 $\rho$ 的窗化平均不匹配，则即便改核，也会被新稳态拉回一致的配重。

**可检步骤**
用 30 天日志估计 $\widehat P$ 与谱隙 $\widehat\Delta=1-|\widehat\lambda_2|$，计算 $\widehat\pi$。执行"末小时三件套"（换窗—校秤—记账）并引入政策改动 $\Delta P$（如改变触发阈、可见性、奖励），每 7 天估计 $\widehat\pi$ 的变动 $|\widehat\pi_{t+7}-\widehat\pi_t|_1$。若仅改起点而 $\widehat\pi$ 不动＝"只改运未改命"；若 $\widehat\pi$ 迁移且 $\widehat\Delta$ 未显著变差，则"改命"成立。

---

### 10. 问符法（占：公共之窗的小样本推断）

**法条**
占不是一次断命，而是**公共之窗**下的重复小实验；其效力来自一致与重复，非神秘本身。

**数学推理**
(1) **贝叶斯小样本**：事件成功率 $p$ 的先验 $\mathrm{Beta}(\alpha_0,\beta_0)$ 与观测 $s$ 成功、$f$ 失败更新为

$$
p\,|\,\text{data}\sim \mathrm{Beta}(\alpha_0+s,\ \beta_0+f),\quad
\mathbb E[p|\text{data}]=\frac{\alpha_0+s}{\alpha_0+\beta_0+s+f}.
$$

可信区间可用 Wilson/Clopper–Pearson。
(2) **顺序检验（SPRT）**：在 $H_0:p=p_0$ 与 $H_1:p=p_1$ 间，似然比 $\Lambda_n=\prod_{i=1}^n \frac{p_1^{X_i}(1-p_1)^{1-X_i}}{p_0^{X_i}(1-p_0)^{1-X_i}}$。设一类/二类错率 $(\alpha,\beta)$，阈值 $A=(1-\beta)/\alpha$，$B=\beta/(1-\alpha)$。当 $\Lambda_n\ge A$ 接受 $H_1$，当 $\Lambda_n\le B$ 接受 $H_0$，否则继续抽样。
(3) **评分与校准**：概率预测质量用 Brier 分数 $\mathrm{Brier}=\tfrac1n\sum_{i=1}^n (p_i-y_i)^2$。良好占式应在同窗同秤复验下让 Brier 下降，并通过校准曲线贴近对角线。
(4) **防气泡与多重**：多题占测需 FDR 控制，防止"显著性挑样"。同一问题必须保持窗一致（同来源/同时段/同解释规则），否则引入 $\mathrm{Alias}(W)$ 造成伪效应。

**可检步骤**
对同一抉择做 $n=20$ 次微试（同窗同秤），记录成功指示 $X_i$。以 $\mathrm{Beta}(1,1)$ 为先验更新后验并给出 95% 区间；并运行 SPRT 以 $(\alpha,\beta)=(0.05,0.2)$ 判定是否"可走此路"。事后给出 Brier 与校准图；若换窗后效应消失，则撤销结论。

---

### 11. 地脉阵（风水：空间权重的长期布置）

**法条**
风水的可操作解释：以空间权重 $W(x)$ 的长期布置，提高目标任务的**信噪比**与**平均效率**。

**数学推理**
(1) **平均路径代价**：设任务触发分布 $\mu(x)$，执行点在 $x_0$。布置权重 $W(x)$ 决定任务放置概率（或显著度）。平均代价

$$
J(W)=\int_{\Omega} c\big(d(x,x_0)\big)\,\mu(x)\,W(x)\,dx,\qquad \int W=1,\ W\ge 0 .
$$

当 $c(r)$ 单调增时，最优 $W^\star$ 将高重要度任务靠近 $x_0$，形成"愿望位"的数学像。
(2) **SNR 提升**：把目标信号 $s(x)$ 与噪声 $n(x)$ 看作能量密度，则

$$
\mathrm{SNR}(W)=\frac{\big(\int s(x)W(x)dx\big)^2}{\int n^2(x)W^2(x)dx}.
$$

Cauchy–Schwarz 给出最优形状 $W^\star(x)\propto s(x)/n^2(x)$（受非负与归一约束），即"朝向光、避开噪"的布置准则。
(3) **动线—关系保持**（图版本）：节点 $i$ 的位置 $x_i$ 与关联强度 $A_{ij}$，布局最优化

$$
\min_{x_1,\dots,x_m}\ \sum_{i<j} A_{ij}\,|x_i-x_j|^2\quad
\text{s.t. } x_i\in \text{可行域},
$$

等价于谱嵌入：将强关联任务置近，弱关联远置，降低切换成本。
(4) **环境势与降噪**：把光/噪建成势 $\Phi$ 与扩散项，$-\Delta \Phi=\text{源} - \text{汇}$。在高 $\Phi$ 区布置专注任务，在 $\nabla \Phi$ 变化剧烈区避免放置易扰任务。

**可检步骤**
测 7 天任务热力图 $\hat\mu(x)$ 与噪声图 $\hat n(x)$，按 $W^\star\propto s/n^2$ 生成布局方案，实施 14 天并对比：平均完成时长 $\downarrow$、错漏率 $\downarrow$、$\mathrm{SNR}\uparrow$。在团队/家中追加图谱法：依据 $A_{ij}$ 调整邻近度，复测切换成本是否显著下降。

---

### 12. 奇迹门（测度倾斜：把稀有变可见可达）

**法条**
"奇迹"不是破坏守恒，而是通过**测度倾斜**把低概率路径放到可见窗内；关键是**可复演且方差受控**。

**数学推理**
(1) **指数倾斜（Cramér tilt）**：令观测随机量 $X$ 的母函数 $\psi(\theta)=\log \mathbb E[e^{\theta X}]$ 有限。定义倾斜测度

$$
d\mathbb P_\theta=\exp\big(\theta X-\psi(\theta)\big)\,d\mathbb P .
$$

某事件 $A$ 在 $\mathbb P_\theta$ 下的概率

$$
\mathbb P_\theta(A)=\mathbb E\big[\mathbf 1_A\,e^{\theta X-\psi(\theta)}\big] .
$$

选择 $\theta$ 使 $X$ 的均值朝目标阈值移动，可把"稀有"显著抬升。
(2) **重要抽样方差**：权重 $w=e^{\theta X-\psi(\theta)}$ 的方差决定可复演性。要求 $\mathrm{CV}^2=\mathrm{Var}(w)/(\mathbb E w)^2$ 受控（如 $\le 1$）。过度倾斜导致方差爆炸＝"假奇迹"。
(3) **三因子微调的分量化**：把"出现地点/出现频次/可识别信号"分别建作 $X=\langle \theta, z\rangle$ 的线性因子（位置、频率、标识向量），$\theta$ 的小幅正向调整等价对这三因子做"低风险升重"。
(4) **与 KL 小步相容**：$\mathbb P_\theta$ 与 $\mathbb P$ 的 KL 距离 $\mathrm{KL}(\mathbb P_\theta|\mathbb P)=\theta\,\mathbb E_\theta[X]-\psi(\theta)$。小步倾斜（小 $|\theta|$）$\Rightarrow$ 低信息成本、低反弹。

**可检步骤**
确定目标事件指标 $Y$。连续 14 天按三因子微调（地点/频次/识别信号），估计 $\hat p_t=\Pr(Y=1)$ 与权重方差指标 $\widehat{\mathrm{CV}}^2$。若 $\hat p$ 持续显著上升且 $\widehat{\mathrm{CV}}^2\le 1$，且换窗后仍能复演，则"奇迹"成立；若 $\widehat{\mathrm{CV}}^2\gg 1$ 或换窗即失效，为"假奇迹"。

---

## 小结（未之门）

9. **命纹章**以稳态—瞬态分解与基本解 $Z$ 说明"改命须改核/改秤"；
10. **问符法**把"占"落实为贝叶斯小样本＋顺序检验＋校准评分；
11. **地脉阵**用路径代价、SNR 与谱嵌入给出"风水＝权重场"的最优形状；
12. **奇迹门**以测度倾斜与重要抽样方差界，说明"可复演的奇迹"如何在低信息成本下实现。
