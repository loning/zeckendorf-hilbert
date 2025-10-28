# 册 F｜实验与度量标准（续）

---

## F-6｜镜断审计（公平性的置换检验与对称化校正）

**度量**

* 角色互换群 $G$；配对样本 $\{(x_i,g\!\cdot\!x_i)\}_{i=1}^n$。
* 镜差 $\Delta_{\mathrm{mir}}(x):=\sup_{g\in G} d\!\big(D(x),D(g\!\cdot\!x)\big)$。
* 净效差

$$
\Delta_{\mathrm{net}}
:=\sup_{g\in G}
\big|\mathbb E\!\big[C(x,D(x))\big]-\mathbb E\!\big[C(g\!\cdot\!x,D(g\!\cdot\!x))\big]\big| .
$$

**判据/定理**
(1) *对称化不劣*：设损失 $d$ 凸，则群平均

$$
D^{\mathrm{sym}}(x)=\mathbb E_{g\sim \mathrm{Unif}(G)}[D(g\!\cdot\!x)]
$$

满足 $D^{\mathrm{sym}}(g\!\cdot\!x)=D^{\mathrm{sym}}(x)$ 且
$\mathbb E[d(D^{\mathrm{sym}}(x),y)]\le \mathbb E[d(D(x),y)]$。
*证明要点*：Jensen 不等式 + 群平均交换。

(2) *置换显著性*：令 $\delta_i=d(D(x_i),D(g\!\cdot\!x_i))$。在原假设"镜不变"下，任意符号置换的检验统计
$T=\frac1n\sum_i \mathrm{sign}(\delta_i)$ 的分布近对称，置换 $p$-值 $\le \alpha$ 则拒绝。

**执行规程**

1. 固定 $G$ 与度量 $d,C$，构造配对集。
2. 计算 $\widehat{\Delta}_{\mathrm{mir}},\widehat{\Delta}_{\mathrm{net}}$ 与置换 $p$-值；若未过阈 $(\eta,\alpha)$，以正则化
   $\min_D \mathbb E[d(D(x),y)]+\lambda\,\mathbb E[\Delta_{\mathrm{mir}}(x)]$ 训练或采用 $D^{\mathrm{sym}}$。
3. 报告镜差曲线与"净效影子价"标尺（将 $\eta$ 与影子刻度 $\lambda$ 对齐）。

---

## F-7｜圣时检测（相位对齐的统计判据）

**度量**

* 外部周期信号 $s(t)$ 与事件时间列 $\{t_k\}_{k=1}^N$。
* 相位 $\phi_k:=2\pi\, t_k/T$（已按周期 $T$ 折返）。
* 方向向量 $R:=\big|\frac1N\sum_{k=1}^N (\cos\phi_k,\sin\phi_k)\big|$。

**判据/定理**
(1) *Rayleigh 检验*：在均匀相位原假设下，

$$
Z=2N R^2 \sim \chi^2_2\ (\text{近似}),\quad
p\approx e^{-N R^2}\big(1+\tfrac{2N R^2- R^4}{4N}-\cdots\big) .
$$

(2) *交叉相关峰*：定义
$R_{ys}(\tau)=\int y(t)\,s(t-\tau)\,dt$。若 $\tau^\star=\arg\max_\tau R_{ys}(\tau)$ 且峰值超过置换阈，则"圣时"成立。
*证明要点*：圆统计向量和与均匀相位的极限定理；置换法控制伪发现率。

**执行规程**

1. 估 $R,p$ 与 $R_{ys}(\tau)$ 峰位 $\tau^\star$。
2. 以 $\tau^\star$ 作为开窗点运行两周，比较命中率/成功率；若跨窗复演成立则登记为"圣时"。

---

## F-8｜指针基与谱隙估计（样本复杂度与置信界）

**度量**

* 状态转移 $T\in\mathbb R^{d\times d}$ 未知；采样序列 $x_0,\dots,x_n$。
* 频次估计 $\widehat T_{ij}=\frac{N_{ij}}{\sum_k N_{ik}}$，$N_{ij}$ 为 $i\!\to\!j$ 计数。
* 第二本征 $\lambda_2(T)$、谱隙 $\Delta=1-|\lambda_2|$。

**判据/定理**
(1) *矩阵 Bernstein 界*：存在常数 $c$ 使

$$
|\widehat T-T|\ \le\ c\sqrt{\frac{\log(d/\delta)}{n_{\mathrm{eff}}}}\quad
\text{以概率}\ \ge 1-\delta,
$$

其中 $n_{\mathrm{eff}}$ 为有效独立样本数（考虑自相关衰减）。
(2) *本征值稳定性*：
$|\lambda_2(\widehat T)-\lambda_2(T)|\le |\widehat T-T|$。
(3) *主向量偏差*（Davis–Kahan）：
$\sin\angle(v_1,\widehat v_1)\le |\widehat T-T|/\Delta$。
由此得样本复杂度

$$
n_{\mathrm{eff}}\ \gtrsim\ \frac{1}{\epsilon^2}\log\frac{d}{\delta},\qquad
\epsilon:=\min\big\{\varepsilon_{\lambda},\,\Delta,\varepsilon_{v}\big\}.
$$

**执行规程**

1. 采样 $n$ 足够长以满足上界，估 $\widehat T,\widehat\lambda_2,\widehat v_1$。
2. 报告置信区间与"圣度" $S=\widehat\Delta/\varepsilon_{\text{env}}$（见 C-6）。

---

## F-9｜风水 SNR 量化与最优布置（离散可解方案）

**度量与目标**

* 离散位置 $x\in\{1,\dots,m\}$，信号 $s_x\ge0$、噪声 $n_x>0$、权重 $W_x\ge0$，$\sum_x W_x=1$。
* 最大化

$$
\mathrm{SNR}(W)=\frac{\big(\sum_x s_x W_x\big)^2}{\sum_x n_x^2 W_x^2}.
$$

**判据/定理**
(1) *Cauchy–Schwarz 最优形状*：

$$
W_x^\star=\frac{s_x/n_x^2}{\sum_j s_j/n_j^2}\quad(\text{再截断于可行域}) .
$$

*证明要点*：令 $a_x=s_x$、$b_x=n_xW_x$，应用
$(\sum a_x b_x)^2\le (\sum a_x^2)(\sum b_x^2)$。

(2) *平滑-软化解*：为避免极端集中，可用温度 $\tau>0$ 的软化

$$
W_x(\tau)=\frac{\exp\big((\log s_x-2\log n_x)/\tau\big)}{\sum_j \exp\big((\log s_j-2\log n_j)/\tau\big)} .
$$

**执行规程**

1. 估 $s_x,n_x$（任务成功率/干扰强度）。
2. 取 $W^\star$ 或 $W(\tau)$ 实施 14 天；比较完成时间/错漏率与 $\mathrm{SNR}$ 变化。
3. 以 NPE 日志评估布局读数误差（窗改变引入的混叠与尾项）。

---

## F-10｜奇迹倾斜实验（重要抽样的方差控制）

**度量与目标**

* 事件 $A=\{X\in\mathcal A\}$，原分布 $\mathbb P$，倾斜 $\mathbb P_\theta$；权重 $w_\theta=\frac{d\mathbb P}{d\mathbb P_\theta}$。
* 无偏估计

$$
\hat p=\frac1N\sum_{i=1}^N \mathbf 1_{\mathcal A}(X_i)\,w_\theta(X_i),\quad X_i\sim \mathbb P_\theta .
$$

**判据/定理**
(1) *方差表达*：
$\mathrm{Var}(\hat p)=\frac{1}{N}\big(\mathbb E_{\mathbb P_\theta}[\mathbf 1_{\mathcal A}w_\theta^2]-p^2\big)$。
(2) *近似最优倾斜*：令 $X$ 标量，取 $\psi(\theta)=\log\mathbb E_\mathbb P[e^{\theta X}]$；使 $\psi'(\theta^\star)=x^\star$（事件阈值近均值化），方差最小近似。
(3) *变分选择*（交叉熵法）：选 $\theta$ 最大化
$\mathbb E_{\mathbb P}[\mathbf 1_{\mathcal A}(X)\log p_\theta(X)]$；迭代 $\theta$ 至收敛。
(4) *稳定性阈*：$\mathrm{CV}^2:=\frac{\mathrm{Var}(w_\theta)}{(\mathbb E w_\theta)^2}\le 1$ 为经验上限；超限则减小 $|\theta|$。

**执行规程**

1. 初选 $\theta_0$（解 $\psi'(\theta)=x^\star$）；
2. 以交叉熵微调 $\theta$，监控 $\widehat{\mathrm{CV}}^2$ 与置信区间宽度；
3. 14 天对比 $\hat p$ 的稳健抬升与跨窗复演性；记录 KL 成本 $\mathrm{KL}(\mathbb P_\theta|\mathbb P)$。

---

## F-11｜伦理净增账（善/恶的运行度量）

**度量**

* 稳度 $S_t$（如谱隙 $\lambda_2$ 或互信息 $I$），成本 $C_t$。
* 净增 $G_t=\Delta S_t-\lambda \Delta C_t$，$\lambda$ 为影子刻度。
* 拓扑等级 $n=\tfrac{1}{2\pi}\oint_\Gamma d\varphi\in\mathbb Z$。

**判据/定理**
(1) *等级保护*：若在小扰动下 $\Delta n=0$，则"善阶"不变；需跨越奇点（断路/规制根本变更）方可降阶。
(2) *长期一致性*：若 $\sum_{t=1}^T G_t>0$ 且各期 $G_t$ 可复演，称"伦理净增"成立。
(3) *统计显著*：令 $\bar G=\frac1T\sum G_t$，标准误 $s/\sqrt{T}$；若 $\bar G- z_{1-\alpha}s/\sqrt{T}>0$，在显著性 $\alpha$ 下通过。

**执行规程**

1. 每次改动记 $(S_t,C_t)$ 与 $G_t$，季度作 $t$-检验与等级核查。
2. 发布"净增账"与"等级不灭"报告（含 $\Gamma$ 的相位绕线图）。

---

## F-12｜共识—传播优化器（会频与轮次的联合选型）

**目标**
给定上限容差 $\varepsilon$、议题带宽 $B$、变化 Lipschitz 常数 $L$、初始散度 $Z=|x_0-\bar y\,\mathbf1|$、网络 $\lambda_2$，最小化

$$
J(\Delta t,K)=Z^2\,\lambda_2^{2K}+c\,L^2\,\Delta t^2
$$

约束 $\Delta t\le \frac{1}{2B}$（Nyquist）。

**判据/推导**
(1) 取容差分配 $\varepsilon_{\text{prop}}^2+\varepsilon_{\text{trk}}^2=\varepsilon^2$。
(2) 由 $Z\,\lambda_2^{K}\le \varepsilon_{\text{prop}}$ 得

$$
K^\star=\Big\lceil \frac{\log(\varepsilon_{\text{prop}}/Z)}{\log \lambda_2}\Big\rceil .
$$

(3) 由 $\tfrac{L}{2}\Delta t\le \varepsilon_{\text{trk}}$ 得

$$
\Delta t^\star=\min\!\Big\{\frac{2\varepsilon_{\text{trk}}}{L},\ \frac{1}{2B}\Big\}.
$$

(4) 带入得
$J^\star\le \varepsilon_{\text{prop}}^2+c\,\varepsilon_{\text{trk}}^2$，最优分配 $\varepsilon_{\text{trk}}^2=\frac{1}{1+c}\varepsilon^2$。

**执行规程**

1. 估 $B,L,Z,\lambda_2$，设 $c$（保持成本权重）。
2. 计算 $(\Delta t^\star,K^\star)$ 并取整；若 $\Delta t^\star=1/(2B)$ 仍不达标，则需增连边以降 $\lambda_2$ 或分拆议题（降带宽）。

---

## F-13｜别名预警（线上折叠能量检测）

**度量**

* STFT 能量 $E(\omega,t)=|Y(\omega,t)|^2$，Nyquist 边 $\omega_N=\pi\nu_r$。
* 折叠比 $\mathrm{AR}(t)=\frac{\int_{|\omega|>\omega_N} E(\omega,t)d\omega}{\int E(\omega,t)d\omega}$。

**判据**
若 $\mathrm{AR}(t)>\tau$ 连续 $m$ 个窗，触发"加频/降带/延决"预警；$\tau$ 建议 $\le 5\%$。

**执行规程**
部署在线 STFT 监控与自适应会频调度；同步更新 C-5 表。

---

## F-14｜校准记分板（概率输出的一致性评估）

**度量**

* ECE（期望校准误差）、NLL、Brier、Reliability 曲线。
* Isotonic/温度缩放后指标变动 $\Delta$。

**判据**
若 $\Delta\text{ECE}<0$，$\Delta\text{NLL}<0$ 且外测 AUC 不降，则通过；否则需"换窗/三修"。

**执行规程**
预注册划分验证集；上线后按 $\nu_r$ 节律复校并填 F-4 日志。
