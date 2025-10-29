# RCA–CID–WSIG–EBOC 统一理论

**——可逆自动机 × 封闭自译码器 × 窗化散射/信息几何 × 永恒图因果网**

**（定义—定理—证明要点—可检判据—工程蓝图）**

**Version: 1.5**

**作者**：Auric（S-series / EBOC）

**关键词**：可逆元胞自动机（RCA）；封闭自译码器（CID）；追加式日志；记录熵；停机等价；Zeckendorf 规范形；Kraft–McMillan；I-投影/KL；Birman–Kreĭn；Wigner–Smith 延迟；Ihara–Hashimoto–Bass 图 ζ；Wexler–Raz/Gabor；Chebyshev 图滤波

---

## 摘要

立足"永恒图（EBOC-Graph）是**静态测度结构**，'时间'仅由观察者（译码器）对叶的滤过与提交产生"的立场，本文建立一个由**四层**构成、可证可检可工程化的统一理论：

**（I）动力学层（RCA）**：以可逆元胞自动机描述全系统的可逆演化，保证**联合信息守恒**与**无擦除实现**；可逆性以 Hedlund—Moore—Myhill 的伊甸园判据与 Toffoli–Margolus 的分块可逆构造为证据。([ibisc.univ-evry.fr][1])

**（II）记录/推断层（CID）**：封闭自译码器以**追加式日志**记录自身变更；在最小记录策略下其"记录熵"沿时间滤过**单调（通常严格）上升**，并与"**停机**/**I-投影定点**/**KL 不再下降**"互相等价（Csiszár 的 I-几何与毕达哥拉斯恒等式）。([pages.stern.nyu.edu][2])

**（III）测量层（WSIG）**：把一切读数统一为对**"相位导数 = Wigner–Smith 延迟迹 = −2π·谱移密度"**的**窗化积分**；并以 Nyquist–Poisson–Euler–Maclaurin 三分解给出**非渐近误差闭合**。([imo.universite-paris-saclay.fr][3])

**（IV）图谱层（EBOC-Graph）**：以图拉普拉斯谱为频域、用**Chebyshev 多项式**实现局部化滤波与指数型尾界，非回溯谱经 Ihara–Hashimoto–Bass 行列式与闭路计数同构，支撑"叶-读取/提交"的工程实现。([科学直通车][4])

本文的关键主张配有**可反驳判据**与**工程蓝图**：

1）在把 $R_t$ 建模为长度为 $t$ 的码字**序列**且以前缀码保证拼接可逆、更新为 $R_{t+1}=(R_t,C_t)$ 的前提下，有 $\,S_{t+1}-S_t=H(C_t\mid R_t)\ge0\,$；若按无边界比特串建模，则仅得 $\,S_{t+1}-S_t\le H(C_t\mid R_t)$。2）"无法熵增"$\Leftrightarrow$"停机"$\Leftrightarrow$"I-投影定点"；3）底层唯一规范形需满足"相邻尺度可重组 + 前缀可解"，其一类自然且充分的实现是 Zeckendorf 分解配合前缀码（Kraft），并非唯一可选方案；以此根除"同物多表"的指数级记录爆炸。([维基百科][5])

---

## 0. 设定与记号

* **静态块宇宙**：给定概率空间 $(\Omega,\mathscr F,\mathbb P)$，"时间"仅由译码器对叶的**滤过—提交**所诱导。
* **RCA**：在格 $\mathbb Z^d$ 上的全局映射 $F:\Sigma^{\mathbb Z^d}\!\to\!\Sigma^{\mathbb Z^d}$ **可逆**且 $F^{-1}$ 为 CA（存在有限半径逆局部规则）。([ibisc.univ-evry.fr][1])
* **CID**：内部记录 $R_t\in\mathcal C^\ast$ 以**追加式**更新 $R_{t+1}=R_t\circ C_t$；全态 $X_t=(Z_t,R_t)$ 在双射 $U$ 下可逆演化；编码器 $\mathrm{Enc}$ 为**前缀码**。([维基百科][6])
* **编码规范形**：规模负载 $n$ 用**Zeckendorf 唯一分解**（无相邻 1）；尾随"11"得斐波那契前缀码。([维基百科][5])
* **I-几何**：信念族为指数族，更新由**I-投影（最小 KL）**实现，满足 KL 的毕达哥拉斯分解。([pages.stern.nyu.edu][2])
* **WSIG**：散射矩阵 $S(\lambda)$ 的行列式相位给出**谱移** $\xi$，且 $\partial_\lambda\arg\det S(\lambda)=\operatorname{tr}Q_{\mathrm{WS}}(\lambda)=-2\pi\,\xi'(\lambda)$；本文采用 $\det S(\lambda)=e^{-2\pi i\,\xi(\lambda)}$ 的约定，其中 $Q_{\mathrm{WS}}=-iS^\dagger\partial_\lambda S$ 为 Wigner–Smith 延迟矩阵。并记
$$
\rho(\lambda):=\pi^{-1}\,\partial_\lambda\arg\det S(\lambda)=\pi^{-1}\operatorname{tr}Q_{\mathrm{WS}}(\lambda)=-2\,\xi'(\lambda),
$$
$\rho_0$ 为基准体系对应量。本文中出现的 $(\rho-\rho_0)$ 即指此定义。([imo.universite-paris-saclay.fr][3])
* **EBOC-Graph**：以图拉普拉斯 $L$ 的谱作频域，$\phi(L)$ 由 Chebyshev 级数近似（次数 $m$ 给出误差 $O(\varrho^{-m})$）。([科学直通车][4])

---

## 1. 可逆元胞自动机（RCA）：可逆性、信息守恒与构造

### 定义 1.1（可逆 CA）

若 $F$ 双射且 $F^{-1}$ 亦为 CA，则称 $F$ 为**可逆元胞自动机**。可逆性的结构与判据详见 Kari 综述与 Hedlund—Moore—Myhill 理论。([ibisc.univ-evry.fr][1])

### 定理 1.2（Moore–Myhill/Garden-of-Eden 判据）

在 $\mathbb Z^d$ 上，**满射**当且仅当**预单射**；因此"单射+满射"$\Leftrightarrow$**可逆**。

**证明要点**：基于移位动力系统的拓扑—组合论框架与图示覆盖论证。([ibisc.univ-evry.fr][1])

### 定理 1.3（联合熵守恒与无擦除实现）

可逆映射保持 Liouville/香农联合熵；Toffoli–Margolus **分块可逆**与 Durand-Lose 的"可逆块 CA 表示"确保用局部双射实现 $F$ 与 $F^{-1}$（不需擦除）；Bennett 逻辑可逆计算给出能耗与信息守恒的一致性。([MIT CSAIL][7])

---

## 2. 封闭自译码器（CID）：记录熵增律与"停机"等价

### 定义 2.1（CID）

$\mathrm{CID}=(\mathcal Z,U,R_t,\mathrm{Enc})$。$U$ 为双射；$R_{t+1}=R_t\circ C_t$（**追加式**）；$\mathrm{Enc}$ 为**前缀可解**（Kraft–McMillan）。([维基百科][6])

### 定理 2.2（记录熵单调与严格增条件）

定义"记录熵" $S_t:=H(R_t)$。在把 $R_t$ 建模为**码字序列**且 $\mathrm{Enc}$ 为**前缀码**（从而序列与拼接串一一对应）的前提下，
$$
S_{t+1}-S_t=H(C_t\mid R_t)\ge 0,
$$
若 $I(C_t;Z_t\mid R_t)>0$ 则 $S_{t+1}>S_t$。若仅将 $R_{t+1}$ 视作无边界普通串，则 $H(R_{t+1})\le H(R_t,C_t)$，因而 $S_{t+1}-S_t\le H(C_t\mid R_t)$，并不保证取等；本文采用前者建模以确保等式成立。

**证明要点**：链式法则与条件互信息非负性（数据处理不等式背景）。（I-几何版本见下一条）([pages.stern.nyu.edu][2])

### 定义 2.3（停机）

存在 $\tau$ 使 $\forall t\ge\tau$，$|C_t|=0$（不再追加码字）。

### 定理 2.4（"无熵增"$\Leftrightarrow$"停机"$\Leftrightarrow$"I-投影定点"，在最小记录+唯一规范形下）

在假设：① 采用**最小记录策略**（仅当新增码字带来净 MDL 改善且不可由现有模型重构时才追加）；② 记录以**前缀码**串行编码并采用**唯一规范形**（如 Zeckendorf）；③ $R_t$ 为码字序列随机变量；**③b** 取可检阈值 $\epsilon>0$；下，以下命题等价：

(a) $\exists \tau,\ S_{t+1}=S_t$；(b) $H(C_t\mid R_t)=0$；(c) $I(C_t;Z_t\mid R_t)=0$；

(d) $p(\rho_{t+1})=\arg\min_q\mathrm{KL}(q|p(\rho_t))\equiv p(\rho_t)$；(e) **停机**：存在 $\tau$ 使 $\forall t\ge\tau$，$|C_t|=0$，其触发准则为 $\Delta\mathrm{KL}\le\epsilon$ 且 $\widehat{I}(C_t;Z_t\mid R_t)\le\epsilon$。

**证明要点**：由定理 2.2 得 (a)$\Leftrightarrow$(b)；(b)$\Rightarrow$(c) 乃确定性后处理；(c)$\Rightarrow$(d) 表明无新约束$\Rightarrow$I-投影不动点（Csiszár）；(d)$\Rightarrow$(e) 在假设①–②下无冗余继续；(e)$\Rightarrow$(a) 反向平凡。

**说明**：若缺省①–②，则通常仅有 (a)$\Leftrightarrow$(b)$\Rightarrow$(c)$\Rightarrow$(d)，而 (d)$\Rightarrow$(e) 不再保证成立。([pages.stern.nyu.edu][2])

---

## 3. 防爆炸的底层唯一：**Zeckendorf + Kraft–McMillan**

### 定理 3.1（Zeckendorf 唯一分解与前缀化）

每个 $n\ge1$ 唯一表示为非相邻斐波那契数之和；尾随"11"得到**斐波那契前缀码**（自同步）。([维基百科][5])

### 命题 3.2（必要性：防"同物多表"指数爆炸）

若不施以"相邻尺度可重组"的**唯一规范形**，则等价表示的数目 $\#\mathrm{Rep}(n)$ 指数增长，最小区分代价 $\ge \log \#\mathrm{Rep}(n)$ 比特，导致**记录爆炸**；Zeckendorf 将其压至 1。其为 Ostrowski 计数系统在黄金分数情形的特例，故具**文法同构唯一性**。([projecteuclid.org][8])

### 定理 3.3（Kraft〔前缀码〕充要；McMillan〔唯一可译码〕必要）

对前缀码，若且唯若 $\sum_w 2^{-|w|}\le 1$，存在满足给定码长的前缀码（Kraft）。McMillan 证明：对任一唯一可译码，该不等式必成立（必要）；结合 Kraft，可知**对"存在某个唯一可译码以这些码长实现"同样是充要**（取其前缀实现即可）。本文在 CID 中显式采用前缀码，以保证**流式可解**与**拼接无歧义**。([维基百科][6])

---

## 4. RCA ⟷ CID：以**扩展可逆 CA**实现自译码

### 定理 4.1（嵌入定理）

对任意 RCA $F$ 与满足"前缀+唯一规范形"的编码器，存在扩展字母表 $\tilde\Sigma=\Sigma\times\mathcal A\times\mathcal H$（$\mathcal A$：**分布式日志轨**；$\mathcal H$：**写头/时钟轨**）与可逆分块 CA $F^\sharp$，使
$$
F^\sharp(Z,R,H)=\Big(F(Z),\ \Gamma\big([Z]_{r_C},[R]_{r_C},[H]_{r_H}\big),\ H'\Big),\qquad \pi\!\circ F^\sharp=F\!\circ\pi,
$$
其中 $\Gamma$ 为**局部可逆转导器**：每步在 $R$ 的局部缓冲区写入至多 $b$ 个码元，并由 $H$ 控制有限距离移位/提交；于是**逻辑上的**"$R_{t+1}=R_t\circ C_t$"由若干步的局部写入/移位实现（带宽受 $b$ 限制）。因此 $r^\sharp=\max\{r_F,r_C,r_H\}$ 仍有限，保持 CA 的局部性与可逆性。

此外，对任意 CA $F$ 可定义**二阶可逆化**
$$
\Phi(X,Y):=\big(F(X)\oplus Y,\ X\big)\quad\text{于}\ \tilde\Sigma=\Sigma\times\Sigma,
$$
其中 $\oplus$ 为按元的可逆阿贝尔群运算（如按位 XOR）。其逆为
$$
\Phi^{-1}(U,V)=\big(V,\ U\ominus F(V)\big),
$$
从而在不调用 $F^{-1}$ 的前提下给出可逆、有限半径的局部实现。**意义**：CID 作为 RCA 的一层，记录是动力学的可逆附载。([MIT CSAIL][7])

---

## 5. WSIG：相位—谱密度词典与**非渐近**误差闭合

### 定理 5.1（Birman–Kreĭn 与 Wigner–Smith）

散射对 $(H,H_0)$ 的 $S$-矩阵满足
$$
\det S(\lambda)=e^{-2\pi i\,\xi(\lambda)},
$$
且 $\partial_\lambda\arg\det S(\lambda)=\operatorname{tr}Q_{\mathrm{WS}}(\lambda)=-2\pi\,\xi'(\lambda)$，$Q_{\mathrm{WS}}=-i\,S^\dagger(\lambda)\,\partial_\lambda S(\lambda)$。从而**相位导数=延迟迹=负谱移密度**。([imo.universite-paris-saclay.fr][3])

### 命题 5.2（窗化读数与三项误差闭合）

任何现实读数可写为
$$
\mathrm{Obs}=\!\int w_R(E)\,h(E)\,(\rho-\rho_0)(E)\,dE\;+\;\varepsilon_{\text{alias}}+\varepsilon_{\text{EM}}+\varepsilon_{\text{tail}}.
$$
其中 $h(E)$ 指被测系统的目标符号/响应核（有界可测）；为与 §6 统一，亦可记作 $a(E)$。**别名/EM/尾项**三分分别由 Poisson 采样、Euler–Maclaurin 余项与截断引致；在严格带限且 Nyquist 取样时 $\varepsilon_{\text{alias}}=0$。([lup.lub.lu.se][9])

### 定理 5.3（最优窗 KKT 与相位等距采样）

在带限偶窗类上极小化泄漏/方差型泛函，极小元满足 KKT；以**相位测度** $d\mu_\varphi=\pi^{-1}\varphi'(E)\,dE$ 的等距节点 $\Delta\varphi=\pi$ 取样，可构造**稳定 tight/dual 帧**；Wexler–Raz 双正交与密度定理给出采样门槛与重建稳定性。([sites.math.duke.edu][10])

---

## 6. EBOC-Graph：静态块的图谱实现与 ζ-谱接口

### 定义 6.1（图谱滤波与叶-读取）

在无向图 $G$ 上以 $L$ 的谱为频域，构造滤波器 $\phi(L)$；当滤波器 $\phi$ 在某个 Bernstein 椭圆 $E_{\varrho}$（$\varrho>1$）内解析时，其 Chebyshev 级数截断误差满足 $O(\varrho^{-m})$ 的指数型界。为应用 Chebyshev 界，先将 $L$ 线性缩放至 $[-1,1]$：$\tilde L=\tfrac{2}{\lambda_{\max}(L)}L-I$，对 $\tilde L$ 作 Chebyshev 级数展开；误差界仍为 $O(\varrho^{-m})$（常数依赖于缩放）。叶-读取指对滤过信号的窗化采样与 I-投影提交。([科学直通车][4])

### 定理 6.2（非回溯谱与 Ihara–Bass 行列式）

设非回溯（Hashimoto）边邻接算子 $B$，则图 ζ 满足
$$
\zeta_G(u)^{-1}=\det(I-uB)=(1-u^2)^{\,|E|-|V|+c}\,\det\!\big(I-uA+u^2(D-I)\big),
$$
其中 $c$ 为图的连通分支数；对连通图 $c=1$。把闭路计数与谱联系为**行列式公式**，适配窗化读数。([sas.rochester.edu][11])

### 命题 6.3（CA 的图表示）

De Bruijn 图刻画一维 CA 的局部一致性与可逆性；可在 EBOC-Graph 上以非回溯谱监控规则可逆与通量守恒。([wpmedia.wolfram.com][12])

---

## 7. 两条熵单调机制（与 RCA 守恒配合）

### 定理 7.1（双随机自平均 $\Rightarrow$ 香农熵升）

若 $p^+=Kp$，$K$ **双随机**（置换矩阵凸包），则 $p^+\prec p$（迈约化），香农熵 $H$ 为 Schur-凹，故 $H(p^+)\ge H(p)$。若此外 $K$ 非置换矩阵且 $p$ 不是 $K$ 的不变分布（含非均匀），则严格不等式成立。

**要点**：HLP 迈约化定理与 Birkhoff–von Neumann 分解。([webpages.charlotte.edu][13])

### 定理 7.2（I-投影/KL 毕达哥拉斯）

在线性约束的指数族上，I-投影满足
$$
\mathrm{KL}(q|p)=\mathrm{KL}(q|p^\star)+\mathrm{KL}(p^\star|p),
$$
故沿 I-投影轨迹 KL **非增**，成为"完备性追求"的单调证书。([pages.stern.nyu.edu][2])

---

## 8. 三位一体（EBOC ↔ WSIG）的可检同构

### 定理 8.1（Born = I-投影；Pointer = 谱极小；Windows = 极大极小）

在"滤波—采样—提交"链中：
$$
\boxed{\ \text{Born}=\text{I-projection},\quad
\text{Pointer}=\text{Rayleigh–Ritz/Ky-Fan 极小},\quad
\text{Windows}=\text{极大极小最优（KKT/切比界）}\ }
$$
其中 Born 由 I-投影产出 $p^\star$，指针基由谱极小给出主方向，窗的极大极小由 KKT 与 Chebyshev 误差界支撑。([pages.stern.nyu.edu][2])

---

## 9. 资源-有界不完备（RBIT）与"能增/停机"的边界

把资源统一到逻辑与统计两端：逻辑（可加公理/证明长度）；统计（窗复杂度 $m$、采样点 $S$、样本量 $N$）。当所有可实现窗的条件互信息 $I(Y;Z\mid R)$ 低于阈值且 I-投影的 KL 下降 $\to0$ 时进入**停机区**；图谱侧阈值由 Chebyshev 近似误差 $O(\varrho^{-m})$ 与帧下界给出**预算-误差**曲线。([math.mit.edu][14])

---

## 10. 可反驳判据（面向实验/算例）

1. **记录熵曲线**：$S_t$ 必非降；当激活能区分新模式的窗/模型切换时呈**台阶式上升**；同时 $\Delta\mathrm{KL}\le0$（I-投影证书）。([pages.stern.nyu.edu][2])
2. **"无熵增"$\Leftrightarrow$"停机"**：在线检测 $H(C_t\mid R_t)\!\to\!0$、$\Delta\mathrm{KL}\!\to\!0$ 与基准窗的 $\widehat I(Y;Z\mid R)\!\to\!0$ 三合一即判停机。([pages.stern.nyu.edu][2])
3. **相位等距优于等距采样（有条件）**：在 $\varphi$ **单调**且目标谱**严格带限**、所用窗族满足 KKT 最优条件时，同预算下相位等距（$\Delta\varphi=\pi$）的重建误差不大于等距采样；若在这些前提下仍观察到显著更差误差，则可据此反驳"密度匹配"主张（Wexler–Raz/密度定理）。([sites.math.duke.edu][10])
4. **别名归零**：严格带限+Nyquist $\Rightarrow \varepsilon_{\text{alias}}=0$；若观测到显著 alias，说明带限或 Nyquist 假设被破坏。([lup.lub.lu.se][9])
5. **图谱 ζ 读数**：用 $\zeta_G(u)^{-1}=\det(I-uB)$ 重建非回溯谱密度；在 CA 的 De Bruijn 图上可复现实验。([sas.rochester.edu][11])

---

## 11. 工程蓝图（最短可用路径）

* **RCA 层**：采用 Toffoli–Margolus 分块/门阵列实现；必要时二阶可逆化；以 Moore–Myhill 判据验证可逆。([MIT CSAIL][7])
* **CID 记录**：底层 **Zeckendorf** 规范形与**斐波那契前缀码**；以 Kraft–McMillan 保障解码与拼接唯一；仅当"净码长下降"超过模型描述代价（MDL）才引入新模型（最小记录策略）。([维基百科][5])
* **WSIG 读数**：以 BK & WS 连接相位/谱密度；误差账本按"**别名 + EM 层 + 截断**"三分解给定上界（Poisson/EM/Nyquist）。([imo.universite-paris-saclay.fr][3])
* **采样与重建**：相位等距 + 多窗 tight/dual；用 **Wexler–Raz** 校核双正交与密度阈值。([sites.math.duke.edu][10])
* **EBOC-Graph**：Chebyshev 近似图滤波、帧下界最大化、I-投影提交；ζ-谱接口驱动非回溯谱的叶-读取。([科学直通车][4])

---

## 12. EBOC 与 RCA 的等价（窗-局部可逆完备）

### 定理 12.1（EBOC–RCA 半共轭/因子映射）

对任意半径 $r$ 的一维（或有限维） CA $F$ 与满足"前缀+唯一规范形"的编码器，存在扩展字母表 $\tilde{\Sigma}=\Sigma\times\mathcal A$、可逆分块 CA $F^\sharp$ 及满射因子映射 $\pi:\tilde{\Sigma}^{\mathbb Z^d}\!\to\!\Sigma^{\mathbb Z^d}$ 使
$$
\pi\circ F^\sharp = F\circ \pi .
$$
即便 $F$ 可逆，$\pi$ **一般也仅为满射的因子映射而非同胚**（因扩展轨 $\mathcal A$ 的信息被遗忘）；仅在采取**平凡扩展**（$\mathcal A$ 为单元集）时，$\pi$ 才与恒等同胚。若 $F$ 不可逆，则 $F^\sharp$ 是其可逆包络，仅有半共轭而非同构。

**证明要点**：De Bruijn 图把局部规则嵌入非回溯路径；Toffoli–Margolus 分区给出可逆块实现；Durand-Lose 证明可逆 CA 可由可逆块 CA 复合表达；因子映射 $\pi$ 的构造沿用 §4.1。([wpmedia.wolfram.com][12])

---

## 13. 讨论与延伸

* **量子版（QCA）**：分区可逆结构推广至量子情形（广义 Margolus 分区）；WSIG 的"相位—延迟—谱密度"在多通道散射与电磁/声学系统中已有统一表述。([arXiv][15])
* **图谱多分辨**：EBOC-Graph 下的多尺度核可用 Chebyshev/极小极大统一设计，指数级尾界 $O(\varrho^{-m})$ 直接给出"预算-误差"函数。([科学直通车][4])

---

## 结论

我们给出了从**可逆动力学（RCA）**到**自指记录（CID）**、再到**窗化测量（WSIG）**与**图谱实现（EBOC）**的**闭合链**：RCA 保障联合信息守恒；CID 的追加式日志使**记录熵单调（常严格）上升**，并与**停机/I-投影定点**等价；**Zeckendorf + Kraft–McMillan** 作为底层**唯一规范形/前缀**机制，根除"同物多表"爆炸并保持封闭可解；WSIG 把读数统一为**相位—谱密度**的窗化积分并给出**非渐近误差闭合**与**稳定采样/最优窗**；EBOC-Graph 将其落实为**叶-读取/提交**与**ζ-谱**接口的工程框架。核心环节均有公开判据/文献支撑，具备可检性与可实现性。

---

### 参考文献（选，按主题）

**CA 可逆性与结构**：Kari（综述，含 Garden-of-Eden）；Toffoli–Margolus（分块可逆）；Durand-Lose（可逆块 CA 表示）；Bennett（逻辑可逆计算）。([ibisc.univ-evry.fr][1])

**I-投影/KL**：Csiszár（I-几何与 Pythagoras）。([pages.stern.nyu.edu][2])

**BK/WS（相位—谱移—延迟）**：Guillarmou（Kreĭn 函数/行列式）；Wigner（1955）、Smith（1960）。([imo.universite-paris-saclay.fr][3])

**采样/帧（Wexler–Raz、Landau 密度）**：Daubechies–Landau–Landau；Heil（密度定理史）。([sites.math.duke.edu][10])

**编码唯一性**：Zeckendorf 定理与 Ostrowski 系统；Kraft–McMillan。([维基百科][5])

**图谱/ζ-函数**：Hammond–Vandergheynst–Gribonval（图小波/切比近似）；Defferrard–Bresson–Vandergheynst（ChebNet）；Ihara–Bass 行列式。([科学直通车][4])

**近似与误差界**：Chebyshev 近似的 $\varrho^{-m}$ 收敛（Demanet–Ying/Trefethen）。([math.mit.edu][14])

**De Bruijn 图与 CA**：Sutner 等。([wpmedia.wolfram.com][12])

---

**附：可直接用于实现的关键公式**（供查用）

* **记录熵增律**：$\;S_{t+1}-S_t=H(C_t\mid R_t)\ge0$。
* **I-投影毕达哥拉斯**：$\;\mathrm{KL}(q|p)=\mathrm{KL}(q|p^\star)+\mathrm{KL}(p^\star|p)$。
* **WSIG 统一式**：$\;\partial_\lambda\arg\det S=\operatorname{tr}Q_{\mathrm{WS}}=-2\pi\,\xi'$，其中 $Q_{\mathrm{WS}}=-i\,S^\dagger\partial_\lambda S$。
* **Ihara–Bass**：$\;\zeta_G(u)^{-1}=(1-u^2)^{\,|E|-|V|+c}\,\det\!\big(I-uA+u^2(D-I)\big)$，其中 $c$ 为连通分支数。
* **Chebyshev 误差（解析情形）**：若 $f$ 在 $E_{\varrho}$ 内解析，则 $\,\|f-p_m\|_\infty\le C\,\varrho^{-m}$。

---

[1]: https://ibisc.univ-evry.fr/~hutzler/Cours/IMBI_MPS/Kari05.pdf?utm_source=chatgpt.com "Theory of cellular automata: A survey"
[2]: https://pages.stern.nyu.edu/~dbackus/BCZ/entropy/Csiszar_geometry_AP_75.pdf?utm_source=chatgpt.com "$I$-Divergence Geometry of Probability Distributions and ..."
[3]: https://www.imo.universite-paris-saclay.fr/~colin.guillarmou/krein4.pdf?utm_source=chatgpt.com "Generalized Krein formula, determinants and Selberg zeta ..."
[4]: https://www.sciencedirect.com/science/article/pii/S1063520310000552?utm_source=chatgpt.com "Wavelets on graphs via spectral graph theory"
[5]: https://en.wikipedia.org/wiki/Zeckendorf%27s_theorem?utm_source=chatgpt.com "Zeckendorf's theorem"
[6]: https://en.wikipedia.org/wiki/Kraft%E2%80%93McMillan_inequality?utm_source=chatgpt.com "Kraft–McMillan inequality"
[7]: https://people.csail.mit.edu/nhm/ica.pdf?utm_source=chatgpt.com "ICA - People | MIT CSAIL"
[8]: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-59/issue-2/Ostrowski-Numeration-Systems-Addition-and-Finite-Automata/10.1215/00294527-2017-0027.pdf?utm_source=chatgpt.com "Ostrowski Numeration Systems, Addition, and Finite ..."
[9]: https://lup.lub.lu.se/student-papers/record/9111889/file/9111893.pdf?utm_source=chatgpt.com "SAMPLING AND INTERPOLATION IN PALEY-WIENER ..."
[10]: https://sites.math.duke.edu/~ingrid/publications/J_Four_Anala_Appl_1_p437.pdf?utm_source=chatgpt.com "Gabor Time-Frequency Lattices and the Wexler–Raz Identity"
[11]: https://www.sas.rochester.edu/mth/undergraduate/honorspaperspdfs/tongyuyang2021.pdf?utm_source=chatgpt.com "The Ihara Zeta function."
[12]: https://wpmedia.wolfram.com/sites/13/2018/02/05-1-3.pdf?utm_source=chatgpt.com "De Bruijn Graphs and Linear Cellular Automata - Wolfram"
[13]: https://webpages.charlotte.edu/~ghetyei/courses/old/F23.3116/Birkhoff.pdf?utm_source=chatgpt.com "Birkhoff's Theorem"
[14]: https://math.mit.edu/sites/icg-new/papers/cheb-interp.pdf?utm_source=chatgpt.com "On Chebyshev interpolation of analytic functions"
[15]: https://arxiv.org/abs/2003.06985?utm_source=chatgpt.com "Wigner-Smith Time Delay Matrix for Electromagnetics: Theory and Phenomenology"
