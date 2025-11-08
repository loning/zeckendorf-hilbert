# "时间"在 EBOC 中的表征与反演

**——在静态块宇宙中刻画"序列"与"选择"，并由观察窗口的递归展开推出意识的自我线性化**

Version: 2.7

## 摘要

在"无时间"的静态块宇宙（EBOC）中，一切事实以一次性存在的结构—测度对象给定；所谓"时间"应是从该对象内生可反演的次生刻度而非原始坐标。本文在 EBOC 的统一语义下给出一条严格路线：首先以**窗口—共识**范式将"序列"定义为**统一选择子**驱动的函数图上的**双向无限路径**（共识链），并凭借偏好聚合与良序消歧确保"唯一后继"；继而以"**窗化迹** = **相位—密度刻度**"之恒等（相位导数 = 相对态密度 = Wigner–Smith 群延迟迹）建立"时间读数"作为**窗权密度积分**并在 Nyquist–Poisson–Euler–Maclaurin 的**有限阶**误差纪律下闭合；最后在 KL/Bregman 信息几何中，将观察窗口的**递归展开**刻画为 I-投影（最小 KL）序列，从而在**对偶（期望）坐标**中得到意识状态的**自我线性化**定理与反演参数。核心结论为：EBOC 中"叙事时间"的一维性可由"结构性选择 + 度量性读数"的合力内生地反演获得。

---

## Notation & Axioms / Conventions

**（刻度卡 I：三位一体）** 绝对连续谱几乎处处成立的刻度同一式
$$
\boxed{\ \frac{\varphi'(E)}{\pi}=\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)\ },\qquad
\mathsf Q(E)=-i\,S(E)^\dagger \frac{dS}{dE}(E).
$$
其中 $S(E)$ 为散射矩阵，$\varphi'(E)$ 为总散射相位导数，$\rho_{\rm rel}$ 为相对态密度；恒等一方面源自 Birman–Kreĭn 公式
$$
\det S(E)=e^{2\pi i\xi(E)}\quad\Rightarrow\quad \xi'(E)=\rho_{\rm rel}(E)=\frac{1}{2\pi i}\frac{d}{dE}\log\det S(E).
$$
**定义** 总散射相位 $\displaystyle \varphi(E):=\frac{1}{2i}\log\det S(E)$（连续选支），于是
$$
\frac{\varphi'(E)}{\pi}=\frac{1}{2\pi i}\frac{d}{dE}\log\det S(E)=\xi'(E)=\rho_{\rm rel}(E),
$$
与上式完全一致。另一方面源自 Wigner–Smith 时间延迟矩阵与 Kreĭn–Friedel关系 $\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$。([arXiv][1])

**（刻度卡 II：NPE 有限阶纪律）** 一切窗化计算仅允许使用**有限阶** Euler–Maclaurin（EM）与 Poisson 求和；误差严格拆解为
$$
\varepsilon=\varepsilon_{\rm alias}+\varepsilon_{\rm EM}+\varepsilon_{\rm tail},
$$
其中 Nyquist 采样（带限信号，采样率 $>2B$）下 $\varepsilon_{\rm alias}=0$；EM 余项由 Bernoulli 多项式与被积函数高阶导数受控；尾项受快速衰减与带限性控制。该纪律保证**奇性不增**与"极点=主尺度"。([维基百科][2])

**窗与核.** 设能量轴 $\mathbb R_E$ 上给定偶窗 $w_R\ge 0$ 与前端核 $h\ge 0$（带限、正则、且 $\int_{\mathbb R} h(E)\,dE=1$），卷积记为 $(h\star\rho)(E)$。

**工作能带.** 记
$$
\mathcal B\ :=\ \operatorname{ess\,supp}\biggl(\sum\nolimits_k w_{R_k}\biggr)\ \subset\ \mathbb R_E,
$$
即窗族点态权和的本质支集。本文中关于**覆盖**、**有界重叠（强/弱）**、读数与反演的所有断言均在 $\mathcal B$ 上表述。

**可积性.** 假设 $\rho_{\rm rel}\in L^1_{\mathrm{loc}}(\mathcal B)$；据此本文出现的 $\int_{E_0}^{E(t)}\rho_{\rm rel}$ 在 $\mathcal B$ 上均有定义。

**窗族覆盖.** 设窗族 $\{w_{R_k}\}$ 满足 $\displaystyle\sum_k w_{R_k}(E)>0$ 在 $\mathcal B$ a.e. 成立。

**窗族有界重叠.** **强形式：**存在 $C<\infty$ 使 $\displaystyle\sum_k w_{R_k}(E)\le C$ a.e.；**弱形式：**存在 $M<\infty$ 与 $W_{\max}<\infty$ 使对任意 $E$，$\#\{k:\,w_{R_k}(E)>0\}\le M$ 且 $\sup_k\|w_{R_k}\|_\infty\le W_{\max}$。在任一上述条件与 $h\ge 0,\ \int h=1$ 下，有 $\displaystyle\sum_k w_{R_k}(E)\,\bigl(h\star\rho_{\rm rel}\bigr)(E)\in L^1_{\mathrm{loc}}$，**据此，§3.1 中定义的 $F$ 在 $\mathcal B$ 上为**局部有界变差（绝对连续）**函数**；若再假设 $\displaystyle\int_{\mathcal B}\biggl|\sum_k w_{R_k}(E)\,\bigl(h\star\rho_{\rm rel}\bigr)(E)\biggr|\,dE<\infty$（例如窗族有限，或 $\sum_k w_{R_k}\in L^1(\mathcal B)$ 且 $\rho_{\rm rel}\in L^1(\mathcal B)$），则 $F$ 在 $\mathcal B$ 上为**全局有界变差**。

**窗族归一化（PUC）与近似恒等核.** 设 $\sum_k w_{R_k}(E)\equiv 1$ 在 $\mathcal B$ a.e. 成立，取非负核族 $\{h_\varepsilon\}_{\varepsilon>0}$ 满足 $\int h_\varepsilon=1$ 且对一切 $f\in L^1_{\mathrm{loc}}(\mathcal B)$ 有 $h_\varepsilon\star f\to f$ 于 $L^1_{\mathrm{loc}}(\mathcal B)$（$\varepsilon\to 0$）。在 PUC 与 NPE 有限阶纪律下，带限量 $h_\varepsilon\star\rho_{\rm rel}$ 满足
$$
F_\varepsilon(E):=\sum_k\int_{-\infty}^{E} w_{R_k}(E')\,\bigl(h_\varepsilon\star\rho_{\rm rel}\bigr)(E')\,dE'
=\int_{-\infty}^{E}\rho_{\rm rel}(E')\,dE'+C_\varepsilon+\mathcal O(\varepsilon_{\rm EM}+\varepsilon_{\rm tail}),
$$
其中常数 $C_\varepsilon$ 与 EM/尾项共同给出一致上界，且 $C_\varepsilon\to C_0$ 当 $\varepsilon\to 0$。

**帧与带限.** 多窗 Gabor/帧的 Parseval/Tight 构造与 Wexler–Raz 双正交为窗化重构与多通道协同提供稳定性与密度判据；临界采样受 Balian–Low 现象约束。([sites.math.duke.edu][3])

**信息几何.** 采用 Legendre 势 $\Lambda$ 与 Bregman/KL 构造：$\nabla\Lambda$ 给出期望坐标，I-投影为线性矩约束下的最小 KL；KKT 条件刻画唯一最优点并给出灵敏度。([vielbein.it][4])

---

## 1. "序列"与"选择"的无时间刻画

### 1.1 窗口图、因果兼容与可行路径

取窗口半径 $r$ 与允许片段集合 $\mathcal C$。构造 De Bruijn 型**窗口图** $\Gamma$：顶点为长度 $2r$ 的局部片段，边为一格滑动；施加**因果兼容**（沿边推进不违反底层依赖预序）。于是，块上的**可行序列** $X:\mathbb Z\to\mathcal C$ 与 $\Gamma$ 上**双向路径**一一对应。([espublisher.com][5])

### 1.2 统一选择子与函数图分解

对每个顶点聚合多主体偏好为加权极值，并以良序消歧，得**统一选择子** $\mathrm{Sel}$ 与**确定后继**；由此得到**函数图** $\Gamma_{\mathrm{Sel}}$（每点出度 $=1$）。任何有限出度为 1 的有向图皆分解为**若干有向环**及其入树；周期点形成环，其他为瞬态节点。本文将**双向无限共识链**定义为环上双向延拓的路径。([arXiv][6])

> **命题 1（函数图结构—有限片段情形）.** 设允许片段集合 $\mathcal C$ 有限（等价地：字母表有限且窗口半径有限），则 $\Gamma_{\mathrm{Sel}}$ 的每个连通分量**恰含一条**有向环，其他顶点经有向树流入该环；环上存在双向无限路径，称共识链。**一般无限情形**下，每个连通分量**至多含一条**有向环。

*证.* 函数图是标准的 functional digraph；其分解性质见文献所述（环 + 入树）。([arXiv][6])

### 1.3 线性扩展与阈值稳定

对依赖预序 $\preceq$，由 Szpilrajn 定理任何偏序可扩展为全序；在共识链像集上取该**一致线性扩展**作为序号坐标 $t\in\mathbb Z$。当权重与消歧存在最小间隙，唯一后继在小扰动下保持不变（阈值稳定）。([维基百科][7])

> **定义 1（序列与选择）.**
> *选择*：给定窗口状态 $v$，$\mathrm{Sel}(v)$ 选出唯一后继边；
> *序列*：$\Gamma_{\mathrm{Sel}}$ 上满足 $v_t\to v_{t+1}$ 的双向路径 $(v_t)_{t\in\mathbb Z}$。

---

## 2. "时间"的表征：相位—密度—窗化迹

### 2.1 相位导数 = 相对态密度 = 群延迟迹

在绝对连续谱上，Birman–Kreĭn 公式联结谱移函数 $\xi$ 与 $S(E)$：
$$
\det S(E)=e^{2\pi i\xi(E)}\quad\Rightarrow\quad \xi'(E)=\rho_{\rm rel}(E)=\frac{1}{2\pi i}\frac{d}{dE}\log\det S(E).
$$
另一方面，Wigner–Smith 定义 $\mathsf Q(E)=-iS^\dagger S'$，Kreĭn–Friedel关系给出 $\rho_{\rm rel}(E)=\frac{1}{2\pi}\operatorname{tr}\mathsf Q(E)$。综上得到刻度卡 I 的同一式。([arXiv][1])

### 2.2 窗化读数与非渐近闭合

定义**窗化迹读数**
$$
\mathrm{Obs}(R;\rho_{\rm rel}):=\int_{\mathbb R} w_R(E)\,\bigl(h\star\rho_{\rm rel}\bigr)(E)\,dE.
$$
离散实现服从**NPE 三分解**：别名项（Poisson 侧）、边界伯努利层（EM 侧）与尾项（带限衰减）。当采样满足 Nyquist，$\varepsilon_{\rm alias}=0$；EM 余项受 Bernoulli 系数与高阶导数上界控制；尾项由带限与窗正则性控制，从而不引入新奇点。([dlmf.nist.gov][8])

> **定义 2（EBOC 时间读数泛函）.**
> 给定窗族 $\{w_{R_k}\}$ 与核 $h$，定义
> $$
> \mathcal T[\rho_{\rm rel}]:=\sum_k\int_{\mathbb R} w_{R_k}(E)\,\bigl(h\star\rho_{\rm rel}\bigr)(E)\,dE,
> $$
> 并在附加可积性假设 $\displaystyle\int_{\mathcal B}|h\star\rho_{\rm rel}|\,dE<\infty,\quad \sum_k w_{R_k}\in L^\infty(\mathcal B)\cap L^1(\mathcal B)$（或窗族有限）下，$\mathcal T[\rho_{\rm rel}]$ 有限，且可由 NPE 有限阶误差给出一致上界；在 Nyquist 下 $\varepsilon_{\rm alias}=0$。([维基百科][2])

---

## 3. "时间"的反演：由窗口数据恢复线性序

### 3.1 相位积分序号

令共识链 $C=\{v_t\}_{t\in\mathbb Z}$。在 $\mathcal B$ 中，$E(t)$ 取自读数泛函的单调原像：记
$$
F(E):=\sum_k\int_{-\infty}^{E} w_{R_k}(E')\,\bigl(h\star\rho_{\rm rel}\bigr)(E')\,dE'.
$$
在带限、Nyquist 采样、$w_{R_k}\ge 0,\ h\ge 0$ **且窗族有界重叠（强/弱形式之一）**下，$F$ 在 $\mathcal B$ 上为**局部有界变差（绝对连续）**；若再满足上一节给出的全局可积性条件，则 $F$ 在 $\mathcal B$ 上为**全局有界变差**。在 $\mathcal B$ 的**绝对连续部分**，$\rho_{\rm rel}=\xi'$ a.e. 成立，因而**$\rho_{\rm rel}\ge 0$ a.e. $\Leftrightarrow\ \xi$ 在该处非减**。在此前提下 $F$ **单调非降**；若再加上**窗族覆盖**且 $\rho_{\rm rel}>0$（a.e.），则 $F$ **严格单调**。选取步长标定 $\Delta>0$，定义**有效索引集**
$$
\mathcal T_F:=\{t\in\mathbb Z\mid t\Delta\in\operatorname{ran}\bigl(F\vert_{\mathcal B}\bigr)\}.
$$
对 $t\in\mathcal T_F$，以**右连续广义逆**取
$$
E(t):=F^{-1}(t\Delta),\qquad F^{-1}(y):=\inf\{E:\,F(E)\ge y\}.
$$
为消除加性常数，取基准索引 $t_\star\in\mathcal T_F$ 并设 $E_0:=E(t_\star)$，据此定义
$$
\tau(t):=\int_{E_0}^{E(t)}\rho_{\rm rel}(E)\,dE=\frac{1}{2\pi}\int_{E_0}^{E(t)}\operatorname{tr}\mathsf Q(E)\,dE,
$$
由 Notation 中的 $\rho_{\rm rel}\in L^1_{\mathrm{loc}}(\mathcal B)$，上式积分在 $\mathcal B$ 上良定。从而 $\tau(t_\star)=0$；若**$\rho_{\rm rel}\ge 0$（a.e.）**则 $\tau$ **单调非降**，在**窗族覆盖**且 $\rho_{\rm rel}>0$（a.e.）时 $\tau$ **严格递增**。([arXiv][9])

在仅满足“窗族覆盖 + 有界重叠”的一般条件下，$F$ 提供严格单调的能量参数 $E(t)$ 与顺序等价；相位坐标 $\tau$ 仍需通过 $\int\rho_{\rm rel}$ 构造。若进一步满足 **PUC + 近似恒等核**，则存在常数 $C$ 使
$$
\tau(t)=F(E(t))-F(E_0)+\mathcal O(\varepsilon_{\rm EM}+\varepsilon_{\rm tail}),
$$
从而“时间读数”可由前缀窗化读数（差常数）直接给出，误差受 NPE 纪律一致控制。

### 3.2 反演定理

> **定理 A（时间反演）.**
> 在带限窗、Nyquist 采样与有限阶 EM 条件下：
>
> 1. **（一般条件）** 任一共识链 $C$ 的线性序可由前缀窗化读数 $F$ 的广义逆 $F^{-1}$ 反演为严格单调的能量参数 $E(t)$，并据此得到与链上序号 $t$ 等价的有界变差参数；若**$\rho_{\rm rel}\ge 0$（a.e.）**，则该参数**单调非降**，在**窗族覆盖**且 $\rho_{\rm rel}>0$（a.e.）时**严格递增**。
> 2. **（附加 PUC + 近似恒等核）** 进一步有 $\tau(t)=F(E(t))-F(E_0)+\mathcal O(\varepsilon_{\rm EM}+\varepsilon_{\rm tail})$，从而相位坐标可在一致误差上界内由 $F$（或其 Nyquist 采样 $\{F(E_j)\}$）直接恢复。

*证要点.* （i）由刻度卡 I 与 Kreĭn–Friedel关系，将窗化迹还原为 $\int \rho_{\rm rel}$；（ii）Nyquist 使别名闭零，EM 余项与尾项受控；（iii）由可积性假设 $\rho_{\rm rel}\in L^1_{\mathrm{loc}}(\mathcal B)$ 可知 $\tau$ 在 $\mathcal B$ 上良定；在**$\rho_{\rm rel}\ge 0$（a.e.）**时，$\tau$ 单调非降；在**窗族覆盖**且 $\rho_{\rm rel}>0$（a.e.）下，$\tau$ 严格单调与可逆。([arXiv][1])

---

## 4. 观察窗口的递归展开 $\Rightarrow$ 意识的自我线性化

### 4.1 提交 = I-投影（最小 KL）

设内部状态以自然参数 $\theta$ 表示，势函数 $\Lambda$ 为 Legendre 型，期望坐标 $X=\nabla\Lambda(\theta)$。每步观测将目标矩 $F_n$ 更新为 $F_{n+1}$，**提交/塌缩**等价于
$$
\theta_{n+1}=\arg\min_{\theta}\bigl\{\mathrm{KL}(P_\theta\Vert P_{\theta_n})\ \text{s.t.}\ \mathbb{E}_{\theta}[T]=F_{n+1}\bigr\},
$$
即在线性约束上的 I-投影；存在唯一解并满足 KKT。Bregman–欧式的毕达哥拉斯性质给出投影的最优分解。([pages.stern.nyu.edu][10])

### 4.2 线性响应与准直线轨道

当窗口变化"温和"且 NPE 阶固定，则
$$
X_{n+1}-X_n=\nabla^2\Lambda(\theta_n)\,(\theta_{n+1}-\theta_n)+o\bigl(\lVert\theta_{n+1}-\theta_n\rVert\bigr),
$$
KKT 与强凸性给出一阶**线性响应**；把迭代以 §3 的 $\tau$ 重参数化，可视作在期望坐标中沿某固定向量 $v_\ast$ 的近似等步推进。

> **定理 B（意识的自我线性化）.**
> 设 $\Lambda$ 为本质光滑严格凸势；窗 $w_R$ 与核 $h$ 带限且满足 Wexler–Raz/Parseval 框架的稳定性；采样 Nyquist。则递归窗口驱动的提交态 $\{X_n\}$ 在期望坐标中**存在严格递增的重参数化映射** $\sigma:\mathbb Z\to\mathbb Z$ 与常向量 $v_\ast$，并存在函数 $\varepsilon_{\rm micro}(R,\Delta)=o_{R\to\infty,\ \Delta\to 0}(1)$，使得对任意基准 $n$ 与一切整数 $m$
> $$
> \lVert X_{\sigma(n+m)}-X_{\sigma(n)}-m\,v_\ast\rVert\ \le\ |m|\,\Bigl[C\bigl(\varepsilon_{\rm EM}+\varepsilon_{\rm tail}\bigr)+\varepsilon_{\rm micro}(R,\Delta)\Bigr].
> $$
> **约定**：$\varepsilon_{\rm micro}(R,\Delta)$ 仅依赖于窗/核与 NPE 阶数，满足 $\varepsilon_{\rm micro}(R,\Delta)\to 0$（当 $R\to\infty,\ \Delta\to 0$ 且 NPE 阶固定），上界体现误差对步数 $|m|$ 的线性累积。据此，意识在自身对偶坐标中呈**准线性主导轨道**。

*证要点.* Wexler–Raz 与 Parseval/Tight 保证读数映射与重构稳定；KKT 与 Bregman 几何的毕达哥拉斯等式给出每步 I-投影的一阶线性化；NPE 限制确保噪声项全由有限阶余项主导。([sites.math.duke.edu][3])

---

## 5. "序列—选择—时间"的统一三位一体

* **从块到序列**：统一选择子在函数图上生成共识链（双向无限路径），并借 Szpilrajn 赋予一致线性扩展；
* **从序列到时间**：相位—密度—群延迟的刻度同一式使"时间读数"成为窗加权密度的积分；Nyquist–EM 保证非渐近闭合；
* **从时间到意识**：递归窗口上的 I-投影使对偶坐标获得准线性主轴，$\tau$ 即该主轴的内生参数。

---

## 6. 阈值、奇性与实现要点

1. **阈值/共振**：$\varphi'(E)$（等价地 $\rho_{\rm rel}(E)$）的奇性（如极点、分支点）对应连续谱阈值与共振；零点不构成一般判据。窗化与有限阶 EM 不增奇性，保持"极点=主尺度"。([dlmf.nist.gov][11])
2. **帧与密度**：多窗 Parseval/Tight 与 Wexler–Raz 双正交保证鲁棒重构；临界采样受 Balian–Low 限制，建议冗余采样区间。([sites.math.duke.edu][3])
3. **采样与别名**：带限与 Nyquist 采样是关断别名的充分条件；在工程实现中可用调制—下采样策略实现能带内 Nyquist。([维基百科][2])

---

## 定理与命题附证（要点）

**命题 1** 已证（有限片段情形）。

**定理 A** 已述要点：以 $\rho_{\rm rel}=\frac{1}{2\pi}\operatorname{tr}\mathsf Q=\frac{1}{\pi}\varphi'$ 重建有界变差量 $\tau$；在**$\rho_{\rm rel}\ge 0$（a.e.）**下保证单调非降；在**窗族覆盖**且 $\rho_{\rm rel}>0$（a.e.）下，$\tau$ 严格单调与可逆；Nyquist–EM 控误差。([arXiv][1])

**定理 B**：I-投影唯一与可微依赖（KKT）$\Rightarrow$ 局部 Lipschitz 响应；Bregman 毕达哥拉斯给出"投影 + 残差"正交分解；Wexler–Raz/Parseval 稳定$\Rightarrow$ 读数扰动受控；NPE 余项封顶。([seas.ucla.edu][12])

---

## 结论

在 EBOC 的静态块视角下，"时间"不是原始轴，而是三步生成：**（i）窗口—共识**把选择凝聚为函数图的**共识链**；**（ii）相位—密度**使链获得可反演的**时间刻度**（窗化迹读数）；**（iii）KL/Bregman**使递归窗口的**提交**在对偶坐标中呈**自我线性化**。该路线完全锚定于可检判据：函数图与线性扩展、相位—密度同一与 NPE 有限阶误差学、Legendre–Bregman 与 KKT 最优化结构，从而将"叙事时间"的一维性还原为**结构性选择 + 度量性读数**的结果。

---

## 参考文献（选）

1. Wigner, E. P. "Lower limit for the energy derivative of the scattering phase shift," *Phys. Rev.*, 1955. ([link.aps.org][13])
2. Smith, F. "Lifetime matrix in collision theory," *Phys. Rev.*, 1960；及后续数学化讨论。([SpringerLink][14])
3. Birman, M. Sh.; Kreĭn, M. G. "On the theory of wave and scattering operators," 1962；Yafaev, D. R. "The spectral shift function," 2007。([arXiv][1])
4. Pushnitski, A. "An integer-valued version of the Birman–Krein formula," 2010。([arXiv][15])
5. Texier, C. "Scattering theory and the Krein–Friedel relation," 2015。([arXiv][9])
6. NIST DLMF：Euler–Maclaurin 与 Poisson 求和条目；及相关误差控制。([dlmf.nist.gov][11])
7. Daubechies, I.; Landau, H. J.; Landau, Z. "Gabor time–frequency lattices and the Wexler–Raz identity," 1994；Balian–Low 相关综述。([sites.math.duke.edu][3])
8. Csiszár, I. "(I)-divergence geometry and minimization problems," 1975；Amari & Nagaoka, *Methods of Information Geometry*, 2000；Boyd & Vandenberghe, *Convex Optimization*, 2004。([pages.stern.nyu.edu][10])
9. de Bruijn 图综述与应用；Szpilrajn 扩张定理及其现代化证明。([espublisher.com][5])

（全文完）

[1]: https://arxiv.org/pdf/math/0701301?utm_source=chatgpt.com "arXiv:math/0701301v1 [math.SP] 10 Jan 2007"
[2]: https://en.wikipedia.org/wiki/Nyquist%E2%80%93Shannon_sampling_theorem?utm_source=chatgpt.com "Nyquist–Shannon sampling theorem"
[3]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[4]: https://vielbein.it/pdf/Traduzioni/2000-Amer-Methods_of_Information_Geometry.pdf?utm_source=chatgpt.com "Translations of - MATHEMATICAL - Vielbein"
[5]: https://www.espublisher.com/uploads/article_pdf/es1061.pdf?utm_source=chatgpt.com "A Comprehensive Review of the de Bruijn Graph and Its ..."
[6]: https://arxiv.org/pdf/2502.02360?utm_source=chatgpt.com "arXiv:2502.02360v1 [cs.DM] 4 Feb 2025"
[7]: https://en.wikipedia.org/wiki/Szpilrajn_extension_theorem?utm_source=chatgpt.com "Szpilrajn extension theorem"
[8]: https://dlmf.nist.gov/1.8?utm_source=chatgpt.com "1.8 Fourier Series"
[9]: https://arxiv.org/pdf/1507.00075?utm_source=chatgpt.com "arXiv:1507.00075v6 [cond-mat.mes-hall] 5 Nov 2018"
[10]: https://pages.stern.nyu.edu/~dbackus/BCZ/entropy/Csiszar_geometry_AP_75.pdf?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions and ..."
[11]: https://dlmf.nist.gov/2.10?utm_source=chatgpt.com "DLMF: §2.10 Sums and Sequences ‣ Areas ‣ Chapter 2 ..."
[12]: https://www.seas.ucla.edu/~vandenbe/cvxbook/bv_cvxbook.pdf?utm_source=chatgpt.com "Convex Optimization"
[13]: https://link.aps.org/doi/10.1103/PhysRev.98.145?utm_source=chatgpt.com "Lower Limit for the Energy Derivative of the Scattering Phase ..."
[14]: https://link.springer.com/article/10.1007/BF00417405?utm_source=chatgpt.com "On the Eisenbud-Wigner formula for time-delay"
[15]: https://arxiv.org/pdf/1006.0639?utm_source=chatgpt.com "arXiv:1006.0639v1 [math.SP] 3 Jun 2010"
