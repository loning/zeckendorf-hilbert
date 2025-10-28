# 册 D｜衍生词典（去重合并）

> 体例：每条含「定义」「判据/命题（含最小证明要点）」「最小实验」「别名（并入）」。记号沿用册 A：窗读数 $\langle f\rangle_W$、相位—密度 $\varphi'(E)=\pi\rho(E)$、NPE 三分、KL/I-投影、谱隙 $\Delta$、采样阈 $\nu_r\ge 2B$。

---

## D-1｜圣（稳定指针基）

**定义**：在反复观测与小扰动下不改向的主方向 $v_1$，其稳度由谱隙 $\Delta=\lambda_1-\lambda_2$ 度量。
**判据/命题**：若更新核 $T$ 的次特征值模长 $|\lambda_2|<1$，则有 $T^n x/|T^n x|\to v_1$，并且 $\sin\angle(v_1,\tilde v_1)\le |T-\tilde T|/\Delta$（Davis–Kahan）。
**最小证明要点**：谱分解 $T=\lambda_1 v_1 u_1^\top+\sum_{k\ge2}\lambda_k v_k u_k^\top$ 给出收敛；扰动用夹角不等式。
**最小实验**：以 30 日日志估计 $\widehat T$、求 $\widehat\Delta$，在外加扰动 $\varepsilon$ 下复测方向偏移并验 $\sin\angle\lesssim \varepsilon/\widehat\Delta$。
**别名（并入）**：权威、圣域、圣物。

---

## D-2｜神核（不变元）

**定义**：在窗族与镜像群 $G$ 下不变且使后悔函数 $\mathcal R$ 极小的规则 $\Phi^\star$，满足 $\Phi^\star=\arg\min_\Phi \sup_{g\in G}\mathcal R(g\!\cdot\!\Phi)$ 与 $g\!\cdot\!\Phi^\star=\Phi^\star$。
**判据/命题**：若镜像核 $K$ 满足 $K(x)=x^{-a}K(1/x)$，其 Mellin 变换 $\Phi(s)$ 满足完成对称 $\Phi(s)=\Phi(a-s)$；不变性给出"镜中复断"一致。
**最小证明要点**：代换 $x\mapsto 1/x$ 得 $\Phi(a-s)=\Phi(s)$。群平均 $\Phi\mapsto \int_G g\!\cdot\!\Phi\,dg$ 给不变元。
**最小实验**：对同一规则在三类窗与角色互换下测遗憾 $\widehat{\mathcal R}$，选择使 $\max_G \widehat{\mathcal R}$ 最小且结果不变的候选。
**别名（并入）**：公平之根、完成函数不变元。

---

## D-3｜仁慈改错（KL 小步）

**定义**：在约束 $\mathcal C$ 内以 I-投影做最小信息步 $q^\star=\arg\min_{q\in\mathcal C}\mathrm{KL}(q|p)$，并用镜像下降 $w^+\propto w\exp(-\eta g)$ 迭代。
**判据/命题**：遗憾 $\mathcal R_T\le O(\sqrt T)$；Bregman–Pythagoras 给 $\mathrm{KL}(r|p)=\mathrm{KL}(r|q^\star)+\mathrm{KL}(q^\star|p)$。
**最小证明要点**：镜像下降望远镜恒等式；I-投影最优性。
**最小实验**：AB 比较"硬重置"与 KL-小步的 6 周累积损失与复发率；应见 $\mathcal R_T^{\text{KL}}<\mathcal R_T^{\text{reset}}$。
**别名（并入）**：恩典、悔改、救赎（多期）。

---

## D-4｜三修（NPE 误差闭合）

**定义**：误差分解为 $\mathrm{Err}\le \mathrm{Alias}(W)+\mathrm{Bernoulli}(k,W)+\mathrm{Tail}(k)$。
**判据/命题**：当采样率 $\nu_s$ 达阈、EM 到 $2k$ 阶、截断半径 $X$ 足够大时，三项各 $\le \varepsilon/3$ 则闭合。
**最小证明要点**：Poisson 求和控制混叠、Euler–Maclaurin 控制有限阶、解析延拓给指数尾界。
**最小实验**：记录三项上界与实际误差曲线，满足 $\max\{\cdot\}\le \varepsilon/3$ 两期连续方为"合格"。
**别名（并入）**：忍耐、沉思、谨言。

---

## D-5｜镜中复断

**定义**：判决器 $D$ 在群 $G$ 作用下满足 $D(x)=D(g\!\cdot\!x)$（或净效差 $\le\eta$）。
**判据/命题**：对配对样本 $(x_i,g\!\cdot\!x_i)$，置换检验的 $p$-值低于阈则拒绝"镜不变"；对称化 $D^{\text{sym}}(x)=\mathbb E_{g}D(g\!\cdot\!x)$ 降低凸损失。
**最小证明要点**：Jensen 与群平均。
**最小实验**：计算镜差 $\Delta_{\mathrm{mir}}=\sup_G d(D(x),D(g\!\cdot\!x))$ 与净效差 $\Delta_{\mathrm{net}}$，不达标则加入对称正则。
**别名（并入）**：公平、审判、正义（判据级）。

---

## D-6｜最小闭环

**定义**：把宏愿离散为动作集 $\mathcal X$，用镜像下降在 5 分钟步长上最小化遗憾 $\mathcal R_T=\sum l_t(x_t)-\min_{x\in\mathcal X}\sum l_t(x)$。
**判据/命题**：若 $l_t$ $L$-Lipschitz，步长 $\eta_t\propto 1/\sqrt t$，则 $\mathcal R_T\le O(L\sqrt T)$。
**最小证明要点**：Bregman 三角与望远镜和。
**最小实验**：定义 3–5 个"极小动作"，日内 6–8 轮，估计经验遗憾界并对齐 $\int \varphi'W\approx \pi\int \rho W$。
**别名（并入）**：五分钟闭环、日课。

---

## D-7｜启示（关键少量信息）

**定义**：注入约束 $\mathcal C$ 使 $p\mapsto q^\star=\arg\min_{q\in\mathcal C}\mathrm{KL}(q|p)$ 且误差下降 $\Delta\mathrm{Err}$ 单位信息最大。
**判据/命题**：若启示削弱了主导的混叠项 $\delta$，则 $\Delta\mathrm{Err}\ge \alpha\delta$（$\alpha>0$ 来自 NPE 光滑常数），信息成本为 $\mathrm{KL}(q^\star|p)$ 最小。
**最小证明要点**：NPE 余项的一阶灵敏度与 KL 投影的最小性。
**最小实验**：挑选 ≤5 条关键样本或规则，比较前后 Brier 与校准曲线，计算 $\Delta\mathrm{Err}/\mathrm{KL}$ 的收益比。
**别名（并入）**：证据、预言生效。

---

## D-8｜奇迹（测度倾斜）

**定义**：通过指数倾斜 $d\mathbb P_\theta=\exp(\langle\theta,X\rangle-\psi(\theta))\,d\mathbb P$ 将低概率事件抬升到可见且可复演。
**判据/命题**：重要抽样的权重方差 $\mathrm{CV}^2=\mathrm{Var}(w)/(\mathbb Ew)^2$ 受控（如 $\le1$）时，估计方差界可保证复演；KL 成本 $\mathrm{KL}(\mathbb P_\theta|\mathbb P)=\langle\theta,\mathbb E_\theta X\rangle-\psi(\theta)$ 量化"奇迹价"。
**最小证明要点**：Cramér 倾斜与重要抽样方差公式。
**最小实验**：对"地点/频次/识别信号"三因子小幅正向调 $\theta$，连续 14 天估 $\hat p$ 与 $\widehat{\mathrm{CV}}^2$，满足 $\hat p\uparrow$ 与 $\widehat{\mathrm{CV}}^2\le1$ 且跨窗复演。
**别名（并入）**：祝福、化解、好运工程。

---

## D-9｜命与运

**定义**：命为稳态 $\pi$（长窗平均），运为瞬态 $\delta_t$（短窗漂移）；改命须改核/改秤而非仅改初值。
**判据/命题**：马氏核 $P$ 满足 $\pi^\top P=\pi^\top$，有 $x^{(t)}=\pi+\delta_t$ 且 $|\delta_t|\le C|\lambda_2|^t|x^{(0)}-\pi|$。稳态一阶敏感度 $\tilde\pi^\top-\pi^\top\approx \pi^\top(\tilde P-P)Z$（基本解 $Z=\sum_{k\ge0}(P-\mathbf1\pi^\top)^k$）。
**最小证明要点**：遍历与谱分解；Neumann 级数给基本解。
**最小实验**：估 $\widehat P,\widehat\pi$，施加政策改动 $\Delta P$ 并监测 $|\Delta\widehat\pi|_1$；仅改初值无效则判"只改运未改命"。
**别名（并入）**：改命三件套（换窗、校秤、记账）。

---

## D-10｜风水（权重场）

**定义**：空间权重 $W(x)$ 的长期布置以最小化平均路径代价或最大化 SNR。
**判据/命题**：最优形状满足 $W^\star(x)\propto s(x)/n^2(x)$（受非负与归一约束），或使 $J(W)=\int c(d(x,x_0))\mu(x)W(x)dx$ 最小。
**最小证明要点**：Cauchy–Schwarz 与变分法；谱嵌入等价的动线优化。
**最小实验**：测 7 天任务热图 $\hat\mu$ 与噪声 $\hat n$，按 $W^\star$ 调整桌面/手机首页/动线，复测完成时间与错漏率。
**别名（并入）**：地利、愿望位。

---

## D-11｜圣时（相位对齐）

**定义**：与外部周期相位对齐的开窗时刻 $\tau^\star=\arg\max_\tau R_{xy}(\tau)$，其中 $R_{xy}$ 为交叉相关。
**判据/命题**：在 $\tau^\star$ 开窗可使成功率 $p(\tau)$ 达局部极大，且 $\nu_r\ge 2B$ 的节律下可稳定复演。
**最小证明要点**：相关峰与相位条件；Nyquist 频率保相位不失真。
**最小实验**：滚动估计 $R_{xy}$ 并在 $\tau^\star$ 触发关键任务，比较前后命中率。
**别名（并入）**：天时、择日。

---

## D-12｜契约（硬约束换稳度）

**定义**：用硬约束集合 $\mathcal C$ 缩小策略空间以换取稳度提升与风险上界；违约成本为影子价。
**判据/命题**：拉格朗日最优解满足 $\min_{u\in\mathcal C} C(u)$ 或 $\min_u C(u)+\lambda\,\mathbf1_{u\notin\mathcal C}$，其中 $\lambda=\partial \mathcal L/\partial B$ 是约束的影子刻度；收敛性可由屏障函数 $h(x)\ge0$ 保不变域。
**最小证明要点**：拉格朗日对偶与屏障法；影子价的边际解释。
**最小实验**：制定红线 $\mathcal C$ 与违约阈 $\lambda$，实施前后稳度指标 $S$ 与极端事件频率对比，应见 $\Delta S>0$ 与尾部概率下降。
**别名（并入）**：立约、誓言、仪式语言（约束化）。
