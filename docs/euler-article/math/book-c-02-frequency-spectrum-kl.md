## C-5｜频率阈值表（Nyquist 化治理）

**目的**：为"校窗校秤的仪式/会议/同步"给出**最低频率**与**跟踪误差**的可计算下界，避免混叠与伪稳态。

### 定义

* 议题状态信号 $y(t)$ 的有效带宽定义为满足

$$
\int_{|\omega|\le B}\! |Y(\omega)|^2\,d\omega \ge (1-\alpha)\int_{\mathbb R}\! |Y(\omega)|^2\,d\omega,\quad 0<\alpha\ll1,
$$

取 $B=B_{1-\alpha}$（如 $\alpha=0.05$）。
* 校准频率 $\nu_r=1/\Delta t$；一次校准视作"采样并保持"（sample-and-hold）：

$$
\hat y(t)=\sum_{n\in\mathbb Z} y(n\Delta t)\,\mathbf 1_{[n\Delta t,(n+1)\Delta t)}(t).
$$

### 定理 1（防混叠阈值）

若 $\nu_r\ge 2B$，则理想带通重建下无频谱折叠；若 $\nu_r<2B$，则折叠项能量下界

$$
E_{\text{alias}}\ \ge\ \int_{|\omega|> \pi \nu_r}\!\!\Big|\sum_{k\in\mathbb Z} Y(\omega-2\pi k\nu_r)\Big|^2 d\omega\ >0 .
$$

因此 $\nu_r^{\min}=2B$ 为防混叠必要阈值。

**证明要点**：Poisson 求和公式；带外分量经采样周期化叠加到主带。

### 命题 2（采样—保持跟踪误差）

设 $y$ 连续且 $\dot y$ 有界，$|\dot y|_\infty\le L$。则"零阶保持"在单间隔上的 $L^\infty$ 误差界

$$
|y-\hat y|_{\infty,[n\Delta t,(n+1)\Delta t)}\ \le\ L\,\Delta t/2 .
$$

若再以长度 $m$ 的移动平均窗 $W_m$ 平滑，均方误差

$$
\mathbb E|y-\hat y_W_m|_2^2\ \le\ C_1\,E_{\text{alias}} + C_2\,L^2\,\Delta t^2/m .
$$

**证明要点**：均值值定理给出分段误差；频域用窗频响衰减折叠能量。

### 命题 3（共识网络的传播—跟踪折衷）

群体共识迭代 $x_{k+1}=W x_k$，$W\mathbf 1=\mathbf1$。设每次会议迭代 $K$ 轮，第二特征值模长 $\lambda_2(W)$。对缓慢变化的 $y$，总跟踪误差

$$
\underbrace{|x_K-\bar y\,\mathbf1|}_{\text{传播误差}}\ \le\ \lambda_2(W)^{K}\,|x_0-\bar y\,\mathbf1|,\qquad
\underbrace{|\bar y-y|}_{\text{跟踪误差}}\ \lesssim\ L\,\Delta t/2 ,
$$

其中 $\bar y$ 为会期内均值。给定容差 $\varepsilon$，可取

$$
K\ \ge\ \frac{\log(\varepsilon_{\text{prop}}/|x_0-\bar y\,\mathbf1|)}{\log \lambda_2(W)},\qquad
\Delta t\ \le\ \frac{2\,\varepsilon_{\text{trk}}}{L},\quad
\varepsilon_{\text{prop}}+\varepsilon_{\text{trk}}=\varepsilon .
$$

### 操作规程（频率阈值表）

1. 估 $B_{1-\alpha}$（近 4–8 周数据做频谱能量分布），取 $\nu_r\ge 2B_{1-\alpha}$。
2. 估 $|\dot y|_\infty=L$，定 $\Delta t\le 2\varepsilon_{\text{trk}}/L$。
3. 计算 $\lambda_2(W)$，按上式选 $K$；必要时改网络连边以增谱隙 $1-\lambda_2(W)$。
4. 记录三项：$(\nu_r,\Delta t),(K,\lambda_2),(E_{\text{alias}})$，若 $E_{\text{alias}}>0$ 则提频或缩带（议题分拆）。

---

## C-6｜谱隙量表（权威/圣度）

**目的**：用谱隙 $\Delta$ 与扰动半径度量"流程/人物/制度"的稳定可托付程度（"圣度"）。

### 定义

* 归一正算子/马尔可夫核 $T$ 的主本征 $\lambda_1=1$，次本征模长 $|\lambda_2|<1$，谱隙 $\Delta=1-|\lambda_2|$。
* 环境扰动范数 $\varepsilon_{\text{env}}=\sup|T-\tilde T|$（数据/流程波动的经验上界）。
* 圣度指数 $S:=\Delta/\varepsilon_{\text{env}}$。

### 定理 1（混合时间与稳健度）

若 $T$ 可逆且满足详细平衡，则对任意初值

$$
|T^t x - \pi|_{\mathrm{TV}} \ \le\ c\, (1-\Delta)^t,
\quad t_{\text{mix}}(\epsilon)\ \le\ \frac{1}{\Delta}\,\log\frac{c}{\epsilon}.
$$

同时，若 $|T-\tilde T|\le \varepsilon$，则主向量偏移

$$
\sin\angle(v_1,\tilde v_1)\ \le\ \frac{\varepsilon}{\Delta}.
$$

**证明要点**：谱分解与 Cheeger–Poincaré；Davis–Kahan 夹角不等式。

### 命题 2（圣度阈值）

给定容许偏移 $\theta_{\max}$ 与目标混合上界 $t_{\max}$，若

$$
S=\Delta/\varepsilon_{\text{env}}\ \ge\ \frac{1}{\theta_{\max}},\qquad
\Delta\ \ge\ \frac{1}{t_{\max}}\log\frac{c}{\epsilon},
$$

则该对象可列入"圣规"。反之需"去圣化"（降权或重训）。

### 操作规程（谱隙量表）

1. 估计 $T$ 与 $|\lambda_2|$，得 $\Delta$。
2. 环境压力测评得 $\varepsilon_{\text{env}}$。
3. 计算 $S=\Delta/\varepsilon_{\text{env}}$，对比 $(\theta_{\max},t_{\max})$；
4. 归档：$S$ 连续 3 个评期不达标则降级；达标且 $S$ 持续上升则晋级"核心圣规"。

---

## C-7｜KL 小步流程（仁慈改错）

**目的**：给"改错不翻盘"的最优更正程序：在约束内做最小信息步，保证长期遗憾次线性且反弹低。

### 定义

* 可行域 $\mathcal C\subseteq \Delta_n$（概率单纯形的线性约束子集）。
* 损失 $l_t(w)$（如错案数、延误、成本），梯度估计 $g_t=\nabla l_t(w_t)$。
* Bregman 散度 $D_\phi(w|v)=\phi(w)-\phi(v)-\langle \nabla\phi(v),w-v\rangle$，取 $\phi(w)=\sum_i w_i\log w_i$（熵）。

### 算法（Mirror Descent with I-Projection）

$$
\tilde w_{t+1,i}\ \propto\ w_{t,i}\,\exp(-\eta_t g_{t,i}),\qquad
w_{t+1}\ =\ \arg\min_{w\in\mathcal C} \mathrm{KL}(w|\tilde w_{t+1}).
$$

第一步为"指数小步"，第二步为**I-投影**（最近点）回约束。

### 定理（遗憾界与最小代价）

若 $l_t$ 为 $L$-Lipschitz，$\eta_t=\eta/\sqrt{t}$，则

$$
\mathcal R_T=\sum_{t=1}^T l_t(w_t)-\min_{w\in\mathcal C}\sum_{t=1}^T l_t(w)\ \le\ O(L\sqrt{T}).
$$

并且对任意目标分布 $r\in\mathcal C$ 有 Bregman–Pythagoras：

$$
\mathrm{KL}(r|w_t)=\mathrm{KL}(r|w_{t+1})+\mathrm{KL}(w_{t+1}|w_t)-\langle g_t,w_{t+1}-w_t\rangle .
$$

故每步信息代价 $\mathrm{KL}(w_{t+1}|w_t)$ 最小且收益对齐。

**证明要点**：标准 Mirror Descent 分析；I-投影的 Pythagoras 恒等式。

### 与"清账符"的耦合

若存在源项 $\sigma$ 破坏守恒，先解 $-\Delta\phi=\sigma$ 给出最小控制 $u^\star$ 复账；随后在策略层执行上述 KL 小步，避免在未闭账时贸然更新导致的漂移放大。

### 操作规程

1. 明确 $\mathcal C$（红线约束、配额、预算）。
2. 设 $\eta_t\propto 1/\sqrt{t}$，每日计算 $g_t$，做指数小步＋I-投影。
3. 每 7 天汇总 $\mathcal R_T$ 估计与 $\sum_t \mathrm{KL}(w_{t+1}|w_t)$（信息开销）；
4. 若 $\mathcal R_T$ 不降，检查是否未先"清账"（源项未补）或学习率失配。

---

## C-8｜NPE 误差日志（结构误差台账）

**目的**：把一次测量/流程评估的**结构性误差**显式记账并闭合到目标容差 $\varepsilon$。

### 日志字段（必须项）

$$
\big(\nu_s,\ W,\ k,\ X,\ \widehat F,\ \widehat F^{(m)},\ \alpha,\ p,\ \varepsilon\big),
$$

其中 $\nu_s$ 采样率，$W$ 窗，$k$ EM 阶，$X$ 截断半径，$\widehat F$ 频谱估计，$\widehat F^{(m)}$ 用于 EM 的导数界，$\alpha,p$ 尾衰参数，$\varepsilon$ 目标总误差。

### 上界公式

* **混叠项**（频域卷积界）：

$$
\mathrm{Alias}\ \le\ \sum_{n\neq 0}\int_{\mathbb R}\!\big|\widehat F(\omega-2\pi n\nu_s)\big|\,\big|\widehat W(\omega)\big|\,d\omega .
$$

若 $|\widehat F(\omega)|\le C(1+|\omega|)^{-p}$，$p>1$，则 $\mathrm{Alias}=O(\nu_s^{-(p-1)})$。
* **伯努利层**（EM 至 $2k$ 阶）：

$$
\mathrm{Bernoulli}(k,W)\ \le\ \frac{2\zeta(2k)}{(2\pi)^{2k}}\ \sup |(fW)^{(2k)}|.
$$

* **尾项**（解析/指数衰减）：

$$
\mathrm{Tail}(k;X)\ \le\ C(\alpha)\,e^{-\alpha X}.
$$

### 闭合准则（$\varepsilon$-可行）

选择 $(\nu_s,k,X)$ 使

$$
\mathrm{Alias}(\nu_s)\le \varepsilon/3,\quad
\mathrm{Bernoulli}(k,W)\le \varepsilon/3,\quad
\mathrm{Tail}(k;X)\le \varepsilon/3.
$$

若任一项超标，触发相应调参：$\nu_s\uparrow$ 或换带宽；$k\uparrow$ 或提升平滑度；$X\uparrow$ 或改解析延拓策略。

### 触发器与降级策略

* **触发器**：$\max\{\mathrm{Alias},\mathrm{Bernoulli},\mathrm{Tail}\}>\varepsilon/3$ 任意两期连续成立。
* **降级**：把议题分带（降低 $B$）、缩小窗（减 $\widehat W$ 带外）、延后判决（增 $X$ 与样本量）。
* **升级**：$\mathrm{Err}_{\text{UB}}\le \varepsilon/5$ 且稳态三期，允许降成本（降 $\nu_s$ 或 $k$）但须保持 $\nu_r\ge 2B$。

### 操作规程

1. 填写初始日志，估 $\widehat F,\widehat F^{(m)}$ 与尾衰 $(\alpha,p)$。
2. 依闭合准则选 $(\nu_s,k,X)$，计算三项上界与裕度。
3. 运行期内每次记录实际误差与上界偏差；
4. 期末出具"误差闭合凭单"：三项曲线与最终 $\mathrm{Err}_{\text{UB}}\le \varepsilon$ 的证据。
