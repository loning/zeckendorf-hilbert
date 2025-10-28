# 册 C｜判据卷（数学与实验）

> 本册承接册 A 之记号：窗读数 $\langle f\rangle_W=\int fW$、相位—密度 $\varphi'=\pi\rho$、NPE 误差三分、KL/I-投影、谱隙 $\Delta$ 与采样阈 $\nu_r\ge 2B$。以下给出四张"标准卡"，含**定义—定理/命题—证明要点—操作规程**。

---

## C-1｜三窗卡（Window Triangulation）

**目的**：用三扇性质差异足够的窗 $W^{(1)},W^{(2)},W^{(3)}$ 对同一对象 $f$ 读数三角化，显式检测"不可辨域"（$\ker\mathcal A\neq\{0\}$）并定量化"窗差灵敏度"。

### 定义

* 测量算子 $\mathcal A: f\mapsto m=(m_1,m_2,m_3)$，$m_i=\langle f\rangle_{W^{(i)}}$。
* 窗 Gram 矩阵 $G\in\mathbb R^{3\times3}$：$G_{ij}=\int W^{(i)}(E)\,W^{(j)}(E)\,dE$。
* 条件数 $\kappa(G)=|G|\,|G^{-1}|$；"三窗可分性"指数 $\Theta=\min_{i\neq j}|W^{(i)}-W^{(j)}|_1$。

### 命题 1（窗差上界）

对有界 $f\in L^\infty$，任意两窗有

$$
|m_i-m_j|=\big|\langle f\rangle_{W^{(i)}-W^{(j)}}\big|
\le |f|_\infty\,|W^{(i)}-W^{(j)}|_1
\le |f|_\infty\,\Theta .
$$

**证明要点**：Hölder 不等式与 $|W|_1=1$。

### 命题 2（三窗可识别性）

若 $G$ 可逆且 $\kappa(G)$ 有界，则对任意 $f,g\in L^2$

$$
|f-g|_{W}:=\Big(\sum_{i=1}^3|\langle f-g\rangle_{W^{(i)}}|^2\Big)^{1/2}
\ge \sigma_{\min}(G)^{1/2}\,| \Pi_{\mathrm{span}\{W^{(i)}\}}(f-g)|_2 .
$$

特别地，$\kappa(G)$ 越小，"窗三角化"的稳定性越好。

**证明要点**：$|m|_2^2=\langle f-g,\,\sum_{i}m_i W^{(i)}\rangle$，以 Riesz 表示与最小奇异值界下推得不等式。

### 命题 3（不可辨域的见证）

三窗下不可辨域

$$
\mathcal N:=\{h\in L^2:\ \langle h\rangle_{W^{(i)}}=0,\ i=1,2,3\}
$$

非空且无界（在无限维情形）。其"最平滑见证"可由

$$
h^\star=\arg\min_{h\neq 0}\ |h|_{H^1}\ \ \text{s.t.}\ \ \langle h\rangle_{W^{(i)}}=0
$$

给出；$|h^\star|_{H^1}$ 越小，说明三窗对该频段/尺度的分辨力越弱。

**证明要点**：秩—核定理给 $\dim\mathcal N=\infty$；以 Hilbert 空间约束最小化求最小范数解。

### 操作规程

1. **设计三窗**：令 $W^{(i)}$ 具不同带宽/中心（如时间/频率/空间三域），最大化 $\det G$、最小化 $\kappa(G)$。
2. **三窗试验**：同对象 $f$ 得 $m_1,m_2,m_3$。若 $\max_{i\neq j}|m_i-m_j|>\tau$ 且噪声置信界不足以解释，则记为"窗不一致"→进入"三修卡"。
3. **见证构造**：数值解 $h^\star$（有限元/样条），标注其主频/主尺度，作为后续窗优化的定向证据。
4. **优化回路**：据 $h^\star$ 调整 $W^{(i)}$（加权、带宽、中心），直至 $\kappa(G)\downarrow$ 且 $|h^\star|_{H^1}\uparrow$。

---

## C-2｜三修卡（NPE 误差闭合）

**目的**：把一次读数的非渐近误差拆为"混叠 + 伯努利层 + 尾项"，给出可计算上界与参数选型（采样率/窗形/EM 阶数）。

### 定义（NPE 三分）

$$
\mathrm{Err}\le \underbrace{\mathrm{Alias}(W,\nu_s)}_{\text{混叠}}
+\underbrace{\mathrm{Bernoulli}(k,W)}_{\text{有限阶 EM 修正}}
+\underbrace{\mathrm{Tail}(k)}_{\text{截断尾项}}\quad (k\in\mathbb N).
$$

### 命题 1（混叠界）

$f$ 的频谱 $F(\omega)\in L^1$，采样率 $\nu_s$，窗频响 $\widehat W(\omega)$，则

$$
\mathrm{Alias}\ \le \sum_{n\neq 0}\int_{\mathbb R}\big|F(\omega-2\pi n \nu_s)\big|\,\big|\widehat W(\omega)\big|\,d\omega .
$$

若 $F$ 在 $|\omega|>\Omega$ 处以 $|F(\omega)|\le C(1+|\omega|)^{-p}$ 衰减（$p>1$），且 $\nu_s>\Omega/\pi$，则别名界 $O(\nu_s^{-(p-1)})$。

**证明要点**：Poisson 求和与卷积界。

### 命题 2（伯努利层）

对光滑 $f$ 的数值求和/积分误差，用 Euler–Maclaurin 到阶 $2k$：

$$
\sum_{n=a}^{b} f(n)=\int_a^b f(x)\,dx+\frac{f(a)+f(b)}{2}+\sum_{r=1}^{k}\frac{B_{2r}}{(2r)!}\big(f^{(2r-1)}(b)-f^{(2r-1)}(a)\big)+R_{2k},
$$

其余项

$$
|R_{2k}|\le \frac{2\zeta(2k)}{(2\pi)^{2k}}\ \sup_{x\in[a,b]}|f^{(2k)}(x)|.
$$

将 $f$ 换成窗加权 integrand，可得 $\mathrm{Bernoulli}(k,W)$ 的显式上界。

**证明要点**：经典 EM 余项的傅里叶—Bernoulli 界。

### 命题 3（尾项界）

若 $f$ 在复域带状区 $|\Im z|\le \sigma$ 全纯且 $|f(z)|\le M\,e^{-\alpha|z|}$，则按 Jordan 引理与最大模原理，截断到 $|x|\le X$ 的尾项

$$
\mathrm{Tail}(k;X)\le C(\sigma,\alpha)\,e^{-\alpha X}.
$$

**证明要点**：解析延拓 + 指数型衰减给出可调 $X$ 的指数界。

### 参数选型（$\varepsilon$-闭合）

给定目标误差 $\varepsilon$，求 $(\nu_s, k, X)$ 使

$$
\mathrm{Alias}(\nu_s)\le \varepsilon/3,\quad
\mathrm{Bernoulli}(k,W)\le \varepsilon/3,\quad
\mathrm{Tail}(k;X)\le \varepsilon/3 .
$$

一套可行策略：

* 先选 $\nu_s\ge \frac{\Omega_{0.95}}{\pi}\cdot \gamma$（$\Omega_{0.95}$ 为 95% 能量频宽，$\gamma\gtrsim 1.2$）抑制别名；
* 再选 $k$ 使 $\frac{2\zeta(2k)}{(2\pi)^{2k}}\sup |f^{(2k)}|\le \varepsilon/3$；
* 终选 $X$ 使 $C e^{-\alpha X}\le \varepsilon/3$。

### 操作规程

1. 估计 $F(\omega)$ 的能量分布与尾衰 $p$；定 $\nu_s$ 达别名阈。
2. 用 EM 到 $2k$ 阶补偿；验证余项界。
3. 设截断 $X$，以解析/数值证实尾项界。
4. 填写一页"误差日志"：$\langle \text{Err}\rangle$ 与三项上界及余裕系数。

---

## C-3｜镜断卡（Mirror Verdict）

**目的**：将"公平/公允"写成可检的不变性：**镜中互换仍给出同断**，并给出偏差统计与校正。

### 定义

* 角色互换群 $G$ 作用于数据 $x\mapsto g\cdot x$。
* 判决器 $D:\mathcal X\to\mathcal Y$。镜像偏差

$$
\Delta_{\mathrm{mir}}(x):=\sup_{g\in G} d\big(D(x),D(g\cdot x)\big)
$$

（取合适度量 $d$）。全体偏差 $\mathbb E[\Delta_{\mathrm{mir}}]$ 为系统镜差。

### 命题 1（对称化校正）

任意 $D$ 可"群平均"得对称判决器

$$
D^{\mathrm{sym}}(x):=\mathbb E_{g\sim \mathrm{Unif}(G)}[D(g\cdot x)],
$$

满足 $D^{\mathrm{sym}}(g\cdot x)=D^{\mathrm{sym}}(x)$，且

$$
\mathbb E[d(D^{\mathrm{sym}}(x),y)]\le \mathbb E[d(D(x),y)]
$$

当 $d$ 为凸型损失时。

**证明要点**：Jensen 不等式 + 群平均。

### 命题 2（镜差显著性检验）

给定配对样本 $\{(x_i,g\cdot x_i)\}_{i=1}^n$，令 $\delta_i=d(D(x_i),D(g\cdot x_i))$。
在原假设"镜不变"下，$\delta_i$ 的随机符号可近似对称；用符号检验或置换检验得 $p$-值，显著则拒绝。

### 命题 3（成本—收益对齐判据）

若判决带成本函数 $C$，镜中互换的**净效不变**要求

$$
\Delta_{\mathrm{net}}:=\sup_{g\in G}\ \big|\mathbb E[C(x,D(x))]-\mathbb E[C(g\cdot x,D(g\cdot x))]\big|\le \eta.
$$

若 $\eta$ 小于阈值（影子价尺度），则通过"镜断"。

**证明要点**：成本作为"秤"，用同秤对齐后的差异才有意义。

### 操作规程

1. 明确群 $G$（例如"甲/乙"角色互换、地理置换等），构造配对样本。
2. 估计 $\Delta_{\mathrm{mir}}$ 与置换 $p$-值；不通过则使用 $D^{\mathrm{sym}}$ 或在损失中加入对称正则 $\lambda\,\Delta_{\mathrm{mir}}$。
3. 以"影子价" $\lambda$ 设净效阈值 $\eta$，通过后方可发布判决。

---

## C-4｜闭环卡（5-分钟最小闭环）

**目的**：把宏愿落到**可复演的最小动作**，并保证序列性的"后悔次线性"。

### 定义（OCO 视角）

设可行域 $\mathcal X$ 与逐日凸损失 $l_t(x)$。最小闭环在时间 $t$ 选择 $x_t$，执行后得到反馈，目标是最小化遗憾

$$
\mathcal R_T:=\sum_{t=1}^{T} l_t(x_t)-\min_{x\in\mathcal X}\sum_{t=1}^{T} l_t(x).
$$

### 算法（Mirror Descent / 指数权重）

选 Bregman 散度 $D_\phi$，步长 $\eta_t\propto 1/\sqrt{t}$：

$$
x_{t+1}=\arg\min_{x\in\mathcal X}\Big\{\langle g_t,x\rangle+\frac{1}{\eta_t}D_\phi(x|x_t)\Big\},\quad g_t=\nabla l_t(x_t).
$$

若 $\mathcal X$ 为概率单纯形且 $\phi(x)=\sum_i x_i\log x_i$，得"指数权重法"：

$$
x_{t+1,i}\propto x_{t,i}\exp(-\eta_t g_{t,i}).
$$

### 定理（次线性遗憾与稳健性）

若 $l_t$ $L$-Lipschitz 且 $\mathrm{diam}_\phi(\mathcal X)\le D$，则

$$
\mathcal R_T\le O\!\big(LD\sqrt{T}\big).
$$

若反馈噪声为零均值次高斯，则以相同阶界成立（在适当常数下）。

**证明要点**：标准 Mirror Descent 分析：望远镜和 Bregman 三角等式。

### 5-分钟化（可操作化）

* 把"日目标"拆成 $\mathcal X$ 上的**离散动作**（3–5 个），损失为"负进展"。
* 设一轮时长 5 分钟；每轮更新权重 $x_{t}\to x_{t+1}$。
* 每日结束给出"闭环度"与 $\mathcal R_T$ 的上界估计（以经验 $L,D,\eta$ 代入）。

### 与相位—密度配重一致

对"方向词" $\varphi$ 与资源密度 $\rho$，闭环权重 $x_t$ 的窗化平均需满足

$$
\int \varphi'(E)\,W(E)\,dE\approx \pi\int \rho(E)\,W(E)\,dE ,
$$

否则调整动作池或时间分配直至一致。
