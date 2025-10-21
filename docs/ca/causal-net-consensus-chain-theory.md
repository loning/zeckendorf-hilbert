# 无端点因果网上一致规则递归的三层共识理论

**纯离散数学构造；含完整证明**

**作者**：Auric
**日期**：2025-10-20

---

## 摘要

在纯离散的语境中，本文系统构造并证明"因果网—共识—共识链"的三层统一理论。第一层以**无端点**、**局部度有限**、**连通**、**无限**的有向因果网为底座，建立有限子结构的**凝缩字母表**与其上的**依赖预序**。第二层在固定**窗口约束**下定义 De Bruijn 类**窗口图**，以统一、时齐的**加权极值选择**与良序消歧将多主体"自由意志"聚合成**确定自动机**，并以阈值刻画"被选择多"的**客观集合**。第三层通过唯一后继得到**函数图**，在其**环型或双向直线型**分量上存在**双向无限**的共识链，严格证明链在其像集上对依赖关系给出**一致线性扩展**；一般情形还可能出现**半直线型**分量，此时仅有单向轨道。进一步建立对权重与偏好**有限扰动**的**阈值稳定域**，并刻画"二元共识（共同自由意志）"在适当保序条件下与一元加权极值的**等价保序**。全文仅使用有限离散对象与有限比较，不引入连续与测度工具。

**关键词**：因果网；窗口约束；De Bruijn 图；确定自动机；函数图分解；一致线性扩展；阈值稳定；自由意志；共识链

---

## 目录

1. 引言
2. 底层因果网与凝缩字母表
3. 窗口约束、因果兼容与 De Bruijn 窗口图
4. 共识层：加权极值、统一选择子与客观集合
5. 函数图分解与双向共识链的存在与唯一
6. 依赖预序与像集上的一致线性扩展
7. 阈值稳定性：权重扰动与偏好扰动
8. 二元共识的外形保序与与一元极值的等价
9. 计算与复杂度（离散）
10. 结论

附录A：函数图的结构引理
附录B：符号与记号表

---

## 1 引言

本文给出一个完全离散、可证明的三层统一框架：以无端点因果网为底，构造以窗口约束驱动的确定自动机，将多主体选择收敛为唯一后继，从而在函数图的环型或双向直线型分量上得到双向无限的共识链（一般情形还可能出现半直线型分量）；链与底层依赖兼容，并在扰动下具备可验证的阈值稳定性。理论的每一层仅依赖有限对象、有限比较与组合论论证，适于算法化实现与复杂性分析。

---

## 2 底层因果网与凝缩字母表

### 2.1 有向因果网

记 $\mathcal{G}=(\mathcal{N},\mathcal{R})$ 为有向图，$u\to v\iff(u,v)\in\mathcal{R}$，$\to^\ast$ 为可达的传递闭包（含零步）。假设

* **(G1) 局部度有限（LFdeg）**：$\forall v\in\mathcal{N}$，$\deg^-(v),\deg^+(v)<\infty$。
* **(G2) 强无端点（NE）**：$\forall v\in\mathcal{N}$，$\exists u,w\in\mathcal{N}$ 使 $u\to v$ 且 $v\to w$。
* **(G3) 连通（SC）**：$\mathcal{G}$ 的基础无向图连通（或在一连通分量上工作）。
* **(G4) 无限（INF）**：$|\mathcal{N}|=\infty$。

是否存在有向环并不影响本文结论。

### 2.2 凝缩字母表与依赖预序

记 $\mathsf{Sub}_f(\mathcal{G})$ 为诱导边意义下的有限子网族。取等价关系 $\sim$（同构不变、可选向下闭保留、并合可提），定义**凝缩字母表**

$$
\mathcal{Q}:=\mathsf{Sub}_f(\mathcal{G})/\!\sim,\qquad [S]\in\mathcal{Q}.
$$

代表选择 $\sigma:\mathcal{Q}\to\mathsf{Sub}_f(\mathcal{G})$ 仅作记账；所有断言均以"存在式"表述，不依赖 $\sigma$。

定义**依赖预序**

$$
\downarrow[H]\ :=\ \bigcup_{T\in[H]}\downarrow T,\qquad
H_1\preceq^\star H_2\ \Longleftrightarrow\ [H_1]\subseteq \downarrow[H_2].
$$

其中 $\downarrow T:=\{U\in\mathsf{Sub}_f(\mathcal{G}):V(U)\subseteq\{x:\exists y\in V(T),\,x\to^\ast y\}\}$。

**引理 2.1（良定义与预序）**

$\preceq^\star$ 与代表无关，且自反、传递。

*证明.* 由定义 $\downarrow[H]$ 对代表替换不变，故与代表无关；自反性：任意 $S\in[H]$ 有 $S\in\downarrow S\subseteq\downarrow[H]$，从而 $[H]\subseteq\downarrow[H]$；传递性：若 $[H_1]\subseteq\downarrow[H_2]$ 且 $[H_2]\subseteq\downarrow[H_3]$，则利用下闭包幂等 $\downarrow(\downarrow[H_3])=\downarrow[H_3]$ 得 $[H_1]\subseteq\downarrow[H_3]$。∎

记 $H_1\equiv^\star H_2\iff(H_1\preceq^\star H_2\ \land\ H_2\preceq^\star H_1)$。商集 $\mathcal{Q}/{\equiv^\star}$ 上诱导**偏序** $\preceq^\star/{\equiv^\star}$。

---

## 3 窗口约束、因果兼容与 De Bruijn 窗口图

### 3.1 窗口可行性与有限分支

固定窗半径 $r\in\mathbb{N}$。给定允许片段集合 $\mathcal{C}\subseteq \mathcal{Q}^{\,2r+1}$。称 $X:\mathbb{Z}\to\mathcal{Q}$ **可行**，若

$$
\forall t\in\mathbb{Z},\quad (X_{t-r},\dots,X_{t+r})\in\mathcal{C}.
$$

对 $v=(q_{-r+1},\dots,q_r)\in\mathcal{Q}^{2r}$，置

$$
\mathsf{Succ}(v):=\{q_+:(q_{-r+1},\dots,q_r,q_+)\in\mathcal{C}\},
$$

$$
\mathsf{Pred}(v):=\{q_-:(q_-,q_{-r+1},\dots,q_{r-1})\in\mathcal{C}\}.
$$

**(C-LF) 窗口层有限分支**：$\forall v$，$\mathsf{Succ}(v),\mathsf{Pred}(v)$ 有限（可为空）。

**(W-NE) 两侧可延展**：若 $\mathsf{Succ}(v)\neq\varnothing$ 则 $\mathsf{Pred}(v)\neq\varnothing$，反之亦然。

### 3.2 因果兼容公理（关键）

为将时间顺序与依赖预序耦合，要求：

**(CC) 局部保序**：对任意允许边

$$
v=(q_{-r+1},\dots,q_r)\ \longrightarrow\ v'=(q_{-r+2},\dots,q_r,q_+)
$$

必有 $q_r\preceq^\star q_+$（在 $\mathcal{Q}/{\equiv^\star}$ 上等价为 $[q_r]\le [q_+]$）。

直观地说，窗口向前一步只会**推进**或**保持**依赖序，不会"逆行"。

### 3.3 De Bruijn 窗口图与可行路径

定义窗口图 $\Gamma=(V,E)$：

$$
V:=\{(q_{-r+1},\dots,q_r)\in\mathcal{Q}^{2r}:\ \mathsf{Succ}(v)\neq\varnothing\},
$$

$$
v\to v'\iff \exists q_+\in\mathsf{Succ}(v)\ \text{使}\ v'=(q_{-r+2},\dots,q_r,q_+).
$$

由 (C-LF) 得 $\Gamma$ 局部有限；(W-NE) 保证顶点入/出度同时非零。

**命题 3.1（可行序列 $\Leftrightarrow$ 双向路径）**

$X:\mathbb{Z}\to\mathcal{Q}$ 可行，当且仅当 $v_t:=(X_{t-r+1},\dots,X_t)$ 构成 $\Gamma$ 上的双向无限路径。

*证明.* 由定义互推。∎

**命题 3.2（沿边保序）**

若 $v_t\to v_{t+1}$，则 $X_t\preceq^\star X_{t+1}$。

*证明.* 由 (CC) 即得。∎

---

## 4 共识层：加权极值、统一选择子与客观集合

### 4.1 加权极值与统一选择子

设主体集合 $\Psi$ 与能力权重 $\alpha_\psi>0$。对边 $e\in E$ 赋离散偏好 $\phi_\psi(e)\in\{0,1,2,\dots\}$。定义

$$
\Phi(e):=\sum_{\psi\in\Psi}\alpha_\psi\,\phi_\psi(e)\in[0,+\infty].
$$

在每个顶点的出边上固定局部**良序** $\triangleleft$。定义**统一选择子**

$$
\mathsf{Sel}(v):=\mathrm{TB}\big(\arg\max\nolimits_{e:v\to v'}\Phi(e)\big),
$$

其中 $\mathrm{TB}$ 按 $\triangleleft$ 消歧。

**引理 4.1（极大元存在）**

每个 $v$ 的出边集有限，$\Phi$ 取扩展非负实值，故 $\arg\max$ 非空；$\mathsf{Sel}$ 良定义。∎

据此得到**确定自动机** $\Gamma_{\!\mathsf{Sel}}$：每顶点唯一后继。

为避免 $(+\infty-\infty)$ 与发散和，加入如下局部假设：

**(LF-Ψ) 局部可和/有界性** 对每个顶点 $v$，记

$$
\Psi_v:=\{\psi:\ \exists\,e\text{（自 }v\text{ 出发）使 }\phi_\psi(e)\ne 0\}.
$$

要求 $\Psi_v$ 有限；或更弱地，

$$
\sum_{\psi\in\Psi_v}\alpha_\psi<\infty,\qquad \sup_{\psi\in\Psi_v,\ e:v\to\cdot}|\phi_\psi(e)|<\infty.
$$

则对每个 $v$ 及其出边 $e$，$\Phi(e)<\infty$；若存在平手则 $\Delta^{\max}(v)=0$，若仅一条出边则 $\Delta^{\max}(v)=+\infty$，因而不发生 $(+\infty-\infty)$。

### 4.2 客观集合

给定阈值 $\vartheta>0$，定义

$$
\mathcal{O}:=\left\{q\in\mathcal{Q}:\ \exists e=v\to v'\ \text{且}\ v'=(q_{-r+2},\dots,q_r,q),\ \text{其中 } e=e^\ast(v)=\mathsf{Sel}(v) \text{ 为被选出边，且 } q=q_+ \text{ 为其后续字母，并且 } \Phi(e)\ge\vartheta\right\}.
$$

该集合只依赖 $\Phi$、$\mathsf{Sel}$ 与 $\mathcal{C}$，与代表选择无关。

---

## 5 函数图分解与双向共识链的存在与唯一

### 5.1 函数图与投影

记每顶点唯一后继边为 $e^\ast(v):v\to v'$。定义

$$
f:V\to V,\quad f(v):=v',\qquad (V,\{v\to f(v)\})\ \text{为函数图（出度=1）}.
$$

投影 $\pi:V\to\mathcal{Q}$，$\pi(q_{-r+1},\dots,q_r)=q_r$。置**共识字母链** $X_t:=\pi(v_t)$。

### 5.2 函数图分解（结构定理）

**定理 5.1（函数图分解）**

$\Gamma_{\!\mathsf{Sel}}$ 的任一连通分量恰为下述三类之一：

(a) **环型**：含唯一有向环，其余顶点沿边汇入该环（入向树丛）；

(b) **双向直线型**：与 $(\mathbb{Z},\,n\mapsto n+1)$ 同构（可在各点接入有限/可数入向树）；

(c) **半直线型**：与 $(\mathbb{N},\,n\mapsto n+1)$ 同构（可在各点接入有限/可数入向树）。

*证明.* 见附录A。∎

### 5.3 双向轨道的存在与（局部）唯一

**定理 5.2（双向轨道存在性）**

双向无限轨道 $(v_t)_{t\in\mathbb{Z}}$ 存在**当且仅当**分量为 (a) 或 (b) 型：

* 若为(a)型（环型），环本身给出周期性的双向轨道；
* 若为(b)型（双向直线），天然为 $\mathbb{Z}$ 轨道；
* 若为(c)型（半直线），**不存在**双向无限轨道，仅存在单向（前向）无限轨道。∎

**命题 5.3′（双向轨道的存在与（局部）唯一）**

在存在双向轨道的分量中：

1. **(b) 型**：沿主干双向直线本身的双向轨道唯一，至多相差一个全局平移；
2. **(a) 型**：仅限于环本身的双向轨道唯一，至多相差一个全局平移；若分量内存在一条从环上某点出发的**无限前驱链**（即存在 $(\cdots\to x_{-2}\to x_{-1}\to x_0\in C)$），则分量内还存在其它双向轨道（沿该链向过去、沿环向未来），因此不能主张“分量内（全体）双向轨道唯一”；
3. **(c) 型**：从任一点出发的前向轨道唯一，但不存在双向无限轨道。

*证明.* 函数图上前向像唯一；(b) 型的主干同构于 $(\mathbb{Z},n\mapsto n+1)$，双向轨道由主干确定，改变起点仅致平移；(a) 型的环本身为周期性双向轨道，改变起点亦仅致循环平移，但若存在从环上一点出发的无限前驱链，可将环点的前驱延伸至过去构造与环不同的双向轨道；(c) 型仅有单向前向轨道而无双向轨道。∎

---

## 6 依赖预序与像集上的一致线性扩展

**定理 6.1″（区间次序的线性扩展）**

设 $(v_t)_{t\in\mathbb{Z}}$ 为 (a)/(b) 型分量上的双向轨道，$[X_t]$ 为 $\equiv^\star$ 等价类。对像集中的任一等价类 $[q]$，定义其**支撑集**与**端点**

$$
S([q])\ :=\ \{t\in\mathbb{Z}:\ [X_t]=[q]\},\qquad
\ell([q])\ :=\ \inf S([q])\ \in\ \mathbb{Z}\cup\{-\infty\},\quad
r([q])\ :=\ \sup S([q])\ \in\ \mathbb{Z}\cup\{+\infty\}.
$$

则由 (CC) 的逐步保序与偏序反对称性可知：每个 $S([q])$ 为一个（可能无界的）**整数区间**，且不同等价类的区间两两**不相交**。据此定义严格与非严格次序：

$$
[p]\ <_X\ [q]\quad\Longleftrightarrow\quad r([p])\ <\ \ell([q])\ (\,[p]\ne[q] \,),
$$

并定义

$$
[p]\ \le_X\ [q]\quad\Longleftrightarrow\quad [p]=[q]\ \text{或}\ [p]<_X[q].
$$

（若像集单点，即常值环情形，则 $\le_X$ 为该单点上的平凡次序。）

**结论 A（线性扩展）** 以上定义给出 $\big(\operatorname{Im}([X]),\le_X\big)$ 的**全序**，且为 $\big(\operatorname{Im}([X]),\preceq^\star\big)$ 的**线性扩展**：若 $[p]\preceq^\star[q]$ 且 $[p]\ne[q]$，则 $[p]<_X[q]$，从而 $[p]\le_X[q]$；若 $[p]=[q]$ 则平凡成立。

**结论 B（索引单调）** 若 $[X_i]\ne[X_j]$ 且 $X_i\preceq^\star X_j$，则必有 $i<j$（因 $i\le r([X_i])<\ell([X_j])\le j$）。

*证明要点.*

1. **区间性与不相交**：若 $t_1<t_2$ 且 $[X_{t_1}]=[X_{t_2}]=[q]$，由逐步保序得 $[X_{t_1}]\preceq^\star\cdots\preceq^\star[X_{t_2}]$；更具体地，对任意 $k\in[t_1,t_2]$，有 $[X_{t_1}]\preceq^\star[X_k]\preceq^\star[X_{t_2}]=[X_{t_1}]$，由反对称性得 $[X_k]=[X_{t_1}]$，从而 $S([q])$ 为整数区间。若两类区间相交，则交点时刻给出等类相等，矛盾。
2. **线性与扩展**：区间在 $\mathbb{Z}$ 上全序排列，定义的 $\le_X$ 为其自然线性次序。若 $[p]\preceq^\star[q]$ 且出现 $r([p])>\ell([q])$，取 $t\in S([q])$、$s\in S([p])$ 使 $t<s$。由 (CC) 得 $[X_t]\preceq^\star[X_s]$，结合 $[p]\preceq^\star[q]$ 推出 $[p]\equiv^\star[q]$，与区间不相交矛盾；故 $r([p])\le \ell([q])$。结论 B 由不等式链直接得出。∎

---

## 7 阈值稳定性：权重扰动与偏好扰动

*约定.* 若顶点 $v$ 仅一条出边，则定义 $\Delta_{\phi}^{(\infty)}(v):=0$（此时按定义 $\Delta^{\max}(v)=+\infty$，§7 的阈值不等式自动成立）。

定义顶点 $v$ 的**局部极值间隙**

$$
\Delta^{\max}(v):=\min_{e\ne e^\ast(v),\,e:v\to\cdot}\big(\Phi(e^\ast(v))-\Phi(e)\big)\in[0,+\infty].
$$

若 $v$ 仅一条出边，则 $\Delta^{\max}(v)=+\infty$。

定义**局部偏好幅度**

$$
\Delta_{\phi}^{(\infty)}(v)\ :=\ \max_{e\ne e^\ast(v)}\ \sup_{\psi}\ |\phi_\psi(e^\ast(v))-\phi_\psi(e)|\ \in[0,\infty),
$$

（当采用 (LF-Ψ) 的强形式（$\Psi_v$ 有限）时，“$\sup$”可等价替换为“$\max$”。）

以及**局域参与者集合**

$$
\Psi_v:=\{\psi:\exists\,e\text{（自 }v\text{ 出发）使 }\phi_\psi(e)\ne 0\}.
$$

### 7.1 权重扰动

令 $\alpha,\alpha'$ 分别给出 $\Phi,\Phi'$。

**定理 7.1（局部保持—权重版）**

若

$$
\sum_{\psi\in\Psi_v}|\alpha'_\psi-\alpha_\psi|\cdot \Delta_{\phi}^{(\infty)}(v)\ <\ \tfrac{1}{2}\,\Delta^{\max}(v),
$$

则 $\mathsf{Sel}'(v)=\mathsf{Sel}(v)$。

*证明.* 对任意竞争边 $e\ne e^\ast(v)$，有

$$
\begin{aligned}
\Phi'(e^\ast)-\Phi'(e) &= \sum_{\psi}\alpha'_\psi[\phi_\psi(e^\ast)-\phi_\psi(e)]\\
&\ge (\Phi(e^\ast)-\Phi(e))-\sum_{\psi\in\Psi_v}|\alpha'_\psi-\alpha_\psi|\cdot|\phi_\psi(e^\ast)-\phi_\psi(e)|\\
&\ge \Delta^{\max}(v)-\sum_{\psi\in\Psi_v}|\alpha'_\psi-\alpha_\psi|\cdot \Delta_{\phi}^{(\infty)}(v)\\
&>\ \tfrac{1}{2}\Delta^{\max}(v)\ >0.
\end{aligned}
$$

故极大边不变，消歧一致，$\mathsf{Sel}'(v)=\mathsf{Sel}(v)$。∎

**定理 7.2（整链保持—权重版）**

设双向轨道 $(v_t)$ 上

$$
\delta:=\inf_t \Delta^{\max}(v_t)>0,\qquad \Delta_\phi^{(\infty)}:=\sup_t \Delta_{\phi}^{(\infty)}(v_t)<\infty.
$$

若

$$
\sup_t\sum_{\psi\in\Psi_{v_t}}|\alpha'_\psi-\alpha_\psi|\ <\ \tfrac{\delta}{2\,\Delta_\phi^{(\infty)}},
$$

则由 $\mathsf{Sel}$ 与 $\mathsf{Sel}'$ 生成的链在同一分量内一致（至多平移）。

*证明.* 由定理7.1，对全部 $v_t$ 选择边保持不变；函数图上前向像一致，故链一致。时间原点不同仅致平移。∎

### 7.2 偏好有限扰动（固定权重）

设权重不变，每个发生变化的参与者 $\psi$ 在 $v$ 处的**跨边改变量幅**

$$
\kappa_\psi(v):=\max_{e\ne e^\ast}\big|[\phi'_\psi(e^\ast)-\phi'_\psi(e)]-[\phi_\psi(e^\ast)-\phi_\psi(e)]\big|.
$$

**命题 7.3（局部保持—偏好版）**

若

$$
2\sum_{\psi\in\Psi_v}\alpha_\psi\,\kappa_\psi(v)\ <\ \Delta^{\max}(v),
$$

则 $\mathsf{Sel}'(v)=\mathsf{Sel}(v)$。

*证明.* 对任意竞争边 $e\ne e^\ast(v)$，

$$
\begin{aligned}
\Phi'(e^\ast)-\Phi'(e) &= \sum_{\psi}\alpha_\psi[\phi'_\psi(e^\ast)-\phi'_\psi(e)]\\
&\ge (\Phi(e^\ast)-\Phi(e))-\sum_{\psi\in\Psi_v}\alpha_\psi\,\kappa_\psi(v)\\
&\ge \Delta^{\max}(v)-\sum_{\psi\in\Psi_v}\alpha_\psi\,\kappa_\psi(v)\\
&>\ \tfrac{1}{2}\Delta^{\max}(v)\ >0.
\end{aligned}
$$

故极大边不变，消歧一致，$\mathsf{Sel}'(v)=\mathsf{Sel}(v)$。∎

---

## 8 二元共识的外形保序与一元极值的等价

为刻画"共同自由意志"，定义二元参与变量 $\chi_\psi(e):=\mathbf{1}_{\{\phi_\psi(e)>0\}}$ 与**参与权重和**

$$
B(e):=\sum_{\psi}\alpha_\psi\,\chi_\psi(e)\in[0,+\infty].
$$

取严格增函数 $g:[0,+\infty]\to[0,+\infty]$，定义外形增强得分

$$
\Lambda_{g,\mu}(e):=\Phi(e)+\mu\,g\!\big(B(e)\big),\qquad \mu\ge0.
$$

我们考虑两种充要到足以保序的局部条件（在每个顶点的出边集合内）：

* **(Bin)** 二元偏好：$\phi_\psi(e)\in\{0,1\}$（则 $B(e)=\Phi(e)$）。
* **(CoMon)** 共单调：对同一顶点的任意两边 $e_1,e_2$，若 $\Phi(e_1)\le\Phi(e_2)$ 则 $B(e_1)\le B(e_2)$。

**定理 8.1（外形保序）**

在(Bin)或(CoMon)成立时，任意 $\mu\ge0$、严格增 $g$ 下

$$
\arg\max_{e:v\to\cdot}\Lambda_{g,\mu}(e)\ =\ \arg\max_{e:v\to\cdot}\Phi(e),
$$

即"二元共识"外形增强不改变极大边，仅可能放大间隙。

*证明.*

* (Bin)下 $B=\Phi$，$\Lambda=\Phi+\mu g(\Phi)$ 对 $\Phi$ 严格增，保序即得。
* (CoMon)下，对同顶点两边 $e_1,e_2$，若 $\Phi(e_2)>\Phi(e_1)$ 则 $B(e_2)\ge B(e_1)$，故

$$
\Lambda(e_2)-\Lambda(e_1)\ \ge\ \Phi(e_2)-\Phi(e_1)\ >\ 0,
$$

极大边不变；平手由 $\triangleleft$ 消歧，结论成立。∎

**推论 8.2（稳定性传递）**

在(Bin)或(CoMon)下，§7的全部阈值不等式可用 $\Lambda_{g,\mu}$ 之差值下界替换，从而得到与外形增强自洽的稳定域（间隙仅增不减）。∎

**注记 8.3（二元偏好下的退化）**

当采用**二元偏好 (Bin)**（$\phi_\psi(e)\in\{0,1\}$）时：

* $\Delta_{\phi}^{(\infty)}(v)\le 1$，故定理7.1的条件退化为 $\sum_{\psi\in\Psi_v}|\alpha'_\psi-\alpha_\psi|<\tfrac{1}{2}\Delta^{\max}(v)$；
* $\kappa_\psi(v)\le 1$，故命题7.3的条件退化为 $2\sum_{\psi\in\Psi_v}\alpha_\psi<\Delta^{\max}(v)$。

这与原表述的阈值一致，确保§7与§8在(Bin)条件下的完全兼容性。

---

## 9 计算与复杂度（离散）

* **局部计算**：由 (C-LF) 与 $\triangleleft$，统一选择在每个顶点为有限次比较与一次消歧。
* **可行片段计数**：若 $\sup_v|\mathsf{Succ}(v)|\le B$，则长度 $L$ 的可行片段数 $\le B^L$。
* **环/直线/半直线识别**：函数图上可用线性时间与常量空间的迭代法识别(a)/(b)/(c) 型分量；环上的双向轨道由循环展开获得，双向直线分量天然同构于 $\mathbb{Z}$，半直线分量同构于 $\mathbb{N}$。
* **自由能式选择**：若另有结构代价 $\mathcal{J}(e)$，可在有限出边上最小化 $\mathcal{F}_\lambda(e):=\mathcal{J}(e)-\lambda\Phi(e)$；若 $\mathcal{J}$ 由次模结构诱导，则存在标准贪心近似界（局部有限集合上直接适用）。

---

## 10 结论

本文以完全离散的方法，完成因果层（无端点、局部度有限的有向网）、共识层（窗口图上的统一加权极值与阈值客观性）与链层（函数图分解与双向轨道）的统一构造与证明；在关键的因果兼容(CC)下，共识链在线性时间顺序上**一致地扩展**底层依赖偏序；在权重与偏好扰动下给出**可检阈值稳定域**；并在(Bin)/(CoMon)条件下证明"二元共识"外形增强对极大选择的**保序等价**。该框架不依赖连续与测度，便于落地为算法与复杂度分析，亦可拓展到多链耦合、层级凝缩与范畴化表达等方向。

---

## 附录A：函数图的结构引理

记 $F=(V,\to)$ 为出度=1的有向图（函数图），写 $f:V\to V$ 满足 $v\to f(v)$。

**引理 A.1（同分量至多一环）**

$F$ 的每个连通分量至多包含一个有向环。

*证明.* 反证：设同一无向连通分量内存在两条不相交有向环 $C_1,C_2$。令
$$
S:=\bigcup_{k\ge 0} f^{-k}(C_1),\qquad
T:=\bigcup_{k\ge 0} f^{-k}(C_2).
$$
则 $S\cap T=\varnothing$，且对任意 $x\in S$ 有 $f(x)\in S$（同理 $x\in T\Rightarrow f(x)\in T$），即二者对前向像封闭。若底层无向图中存在跨集边 $\{u,v\}$ 使 $u\in S,\ v\in T$，则要么 $u\to v$ 要么 $v\to u$：
并且 $S\neq\varnothing$ 且 $S\neq V$。由于底层无向图连通，必存在无向跨割边 $\{u,v\}$ 使 $u\in S,\ v\in V\setminus S$。若 $u\to v$，则 $v=f(u)\in S$，与 $v\in V\setminus S$ 矛盾；若 $v\to u$，则 $u=f(v)\in S$，从而存在 $m\ge 0$ 使得 $f^{m}(u)\in C_1$，于是 $f^{m+1}(v)=f^{m}(u)\in C_1$，故 $v\in S$，亦与 $v\in V\setminus S$ 矛盾。于是该连通分量不可能同时包含两条不相交有向环。∎

**引理 A.2（分量结构）**

在出度=1 的有向图 $F=(V,\to)$ 中，每个连通分量唯一地属于下列三类之一：

(a) **环型**：含唯一有向环 $C$，其余顶点位于入向树上并沿边汇入 $C$；

(b) **双向直线型**：与 $(\mathbb{Z},n\mapsto n+1)$ 同构（可在各点接入有限/可数入向树）；

(c) **半直线型**：与 $(\mathbb{N},n\mapsto n+1)$ 同构（可在各点接入有限/可数入向树）。

*证明.* 对任意 $v\in V$，考察前向轨道 $\mathcal{O}^+(v)=\{f^k(v):k\ge0\}$。若轨道有限，则存在最小 $k>0$ 使 $f^{k}(v)=f^{m}(v)$ 对某 $m<k$ 成立，得到有向环；引理A.1 说明该环对整个分量唯一，得(a)型。若轨道无限且无重复，则子图为单向无重复链 $\{v\to f(v)\to \cdots\}$。此时：若所有点入度均为1，则前向/后向均唯一，得(b)型（双向直线）；若存在入度为0的点，必为半直线起点，得(c)型。∎

由引理A.1–A.2 立即推出正文定理5.1与5.2。

---

## 附录B：符号与记号表

| 符号 | 含义 |
|------|------|
| $\mathcal{G}=(\mathcal{N},\mathcal{R})$ | 底层因果有向网 |
| (G1)(G2)(G3)(G4) | 局部度有限、无端点、连通、无限 |
| $\mathsf{Sub}_f(\mathcal{G})$ | 有限子网族 |
| $\sim$ | 凝缩等价 |
| $\mathcal{Q}$ | 凝缩字母表 |
| $\preceq^\star,\equiv^\star$ | 依赖预序与其等价 |
| $r\in\mathbb{N}$ | 窗半径 |
| $\mathcal{C}\subseteq\mathcal{Q}^{2r+1}$ | 允许片段 |
| (C-LF) | 窗口层有限分支 |
| (W-NE) | 两侧可延展 |
| (CC) | 窗口步进的局部保序 $q_r\preceq^\star q_+$ |
| $\Gamma=(V,E)$ | 窗口图 |
| $\mathsf{Succ},\mathsf{Pred}$ | 后继/前驱集合 |
| $\Psi,\alpha_\psi$ | 主体与权重 |
| $\phi_\psi(e)$ | 离散偏好 |
| $\Phi(e)$ | 加权得分 |
| $\triangleleft,\mathrm{TB}$ | 良序与消歧 |
| $\mathsf{Sel}$ | 统一选择子 |
| $\Gamma_{\!\mathsf{Sel}}$ | 确定自动机 |
| $f:V\to V$ | 函数图 |
| $\pi$ | 投影 |
| $X_t=\pi(v_t)$ | 共识字母链 |
| $\mathcal{O}$ | 阈值客观集合 |
| $\Delta^{\max}(v)$ | 局部极值间隙 |
| $\chi_\psi$, $B(e)$ | 二元参与与权重和 |
| $\Lambda_{g,\mu}$ | 外形增强得分 |
| $\mathcal{J},\mathcal{F}_\lambda$ | 结构代价与自由能式选择 |

---
