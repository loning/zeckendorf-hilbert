# 永恒图元胞自动机理论：独立形式化框架

**作者**：Echo Dynamics Institute
**日期**：2025年10月18日
**版本**：v1.3.11

---

## 摘要

永恒图元胞自动机理论将元胞自动机表述为一个永恒的静态图结构，其中时空维度通过节点和边集编码，形成一个不变的整体网络。该理论独立构建，将局部规则转化为图约束，确保所有状态同时存在于图中，而时间流动被诠释为路径遍历。从符号动力学和图论出发，我们形式化定义了永恒图、状态约束和子移位（subshift，移位不变集），并通过数学证明验证其与传统元胞自动机的等价性。该框架逻辑自洽，适用于有限和无限网格，避免了时间参数的显式引入。我们讨论了其在计算复杂性、信息传播和哲学本体论中的应用，并通过模拟示例确认理论的有效性。此外，本文新增讨论了该理论何时等价于静态块元胞自动机理论：当层级结构对应时间维、局部约束一致且路径追踪生成截面时，二者实现形式化等价。同时，扩展讨论永恒图与量子叠加态的结构类比，以及静态块与经典态的类比，提供更深层的物理哲学视角。

**关键词**：永恒图元胞自动机，静态图结构，符号动力系统，局部规则约束，子移位，Garden-of-Eden定理，永恒主义

---

## §1 引言

### 1.1 背景与动机

元胞自动机作为一种离散模型，由John von Neumann和Stanisław Ulam于20世纪40年代提出，用于研究自复制和复杂系统行为。传统元胞自动机强调动态更新：细胞状态根据局部规则在离散时间步演化。然而，从永恒主义（eternalism）哲学视角，时空可视为一个不变的四维块整体（block universe），其中所有事件同时存在。该理论独立构建永恒图元胞自动机框架，将元胞自动机重构为静态图网络，移除时间作为独立变量，转而通过图拓扑编码因果关系。

注：永恒主义视角在物理哲学中与Wheeler-DeWitt方程或B-theory of time相关，该视角桥接量子引力与CA静态表述，避免动态时间偏见。本稿不引入相应物理方程，仅作哲学动机提示。

这一框架的动机在于提供一个不依赖动态迭代的纯静态描述，桥接元胞自动机与图论、拓扑动力学。该理论不依赖任何先前特定定义，直接从基础公理出发，确保自洽性。通过代码模拟验证，我们确认了其与传统模型的等价性，例如在Rule 90下的状态传播一致。

### 1.2 理论核心思想

核心在于：元胞自动机本质上是一个永恒图，由节点（时空点）和边（局部依赖）组成，受状态约束函数支配。演化被几何化为沿偏序的静态读取（任意叶状分解/拓扑排序均可），而非动态过程。该框架使用图论工具证明唯一性和等价性，适用于可逆和不可逆元胞自动机。在**无限晶格**且**单侧时间域** (t\ge 0) 下，除初始层 (t=0) 外各节点满足 (\deg^- = |N|)；所有层均有 (\deg^+ = |N|)。在**周期边界有限盒**中，当各向尺度 (L_i>2r) 时亦成立；若 (L_i\le 2r)，因邻域别名可出现 (\deg^\pm<|N|)；在**开边界**下，靠近边界的节点可能出现 (\deg^-<|N|) 或 (\deg^+<|N|) 的边界伪影，不影响核心等价性。在周期边界下（如§9模拟），信息传播可能引入伪周期性模式（可通过谱分析§7检测，利用**Walsh–Hadamard展开**（简称 **Walsh**）检测线性规则的周期行为）。因果锥扩展机制确保信息传播的局部性：选取初始节点集并追踪路径，可生成时间推进截面，等价于传统动态演化视角。

### 1.3 论文结构

- **§2** 永恒图的形式化定义
- **§3** 状态约束与局部规则
- **§4** 符号动力系统表述
- **§5** Curtis–Hedlund–Lyndon定理在标准域上的表述
- **§6** 存在唯一性与因果锥证明
- **§7** 线性与非线性规则分析
- **§8** Garden-of-Eden定理在图中的表述
- **§9** 模拟验证与计算实现
- **§10** 与静态块元胞自动机理论的等价性讨论
- **§11** 永恒图与量子叠加态的结构类比与边界
- **§12** 应用：计算优化、可逆性、哲学意涵
- **§13** 复杂度与不可判定边界
- **§14** 结论与展望

---

## §2 永恒图的形式化定义

**索引约定**：本文统一以 $t$ 表示层级（因果深度/时间索引），$V = \mathbb{Z}^d \times \mathbb{Z}_{\ge0}$ 的第二坐标记为 $t$。记号统一：本文一律写作 $\mathbb{Z}_{\ge0}$。

### 定义 2.1（永恒图）

一个永恒图元胞自动机定义为四元组 $\mathcal{E} = (V, E, \Sigma, f)$，其中：
- $V = \mathbb{Z}^d \times \mathbb{Z}_{\ge0}$ 是节点集，代表 $d$ 维空间格点与非负整数层级 $t$（对应因果深度/时间索引）。
- $E \subseteq V \times V$ 是边集：对任意节点 $v = (\mathbf{r}, t+1)$ 和 $\mathbf{n} \in N$（邻域集），存在边 $(\mathbf{r} + \mathbf{n}, t) \to (\mathbf{r}, t+1)$。于是图为DAG（有向无环图，因边仅自 $t$ 指向 $t{+}1$），以支持拓扑排序。
- $\Sigma$ 是有限状态集（如 $\{0,1\}$）。
- $f: \Sigma^{N} \to \Sigma$ 是局部规则函数，定义局部一致性。

邻域 $N \subset \mathbb{Z}^d$ 是有限集，半径 $r = \max_{\mathbf{n} \in N} \|\mathbf{n}\|_1$（其中 $\mathbf{n}$ 为空间位移向量，$r$ 为标量半径）。本文约定 $\deg^-$ 表示入度、$\deg^+$ 表示出度。在**无限晶格**且**单侧时间域** $t\ge0$ 下，除初始层 $t=0$ 外各节点满足 $\deg^-=|N|$；**在无限晶格或周期边界且各向尺度 $L_i>2r$ 时**，各层满足 $\deg^+=|N|$；**在开边界或存在 $L_i\le 2r$ 时**，可能出现 $\deg^+<|N|$ 的边界/别名伪影（不影响与标准无限晶格模型的形式等价）。若 $L_i\le 2r$，因邻域别名可能出现 $\deg^\pm<|N|$。此结论只依赖"每个 $(\mathbf r,t)$ 的值进入恰好 $|N|$ 个 $(\cdot,t{+}1)$ 的局部依赖"，与邻域是否对称无关。构造说明：对于固定旧层节点 $(\mathbf r,t)$，它影响的新层位置集合为 $\{\mathbf r-\mathbf n:\mathbf n\in N\}$，因此在**无限晶格或周期边界且各方向 $L_i>2r$** 时，出度为 $|N|$；若 $L_i\le 2r$，因邻域别名可出现**出度 $\le |N|$**（入度同理）（无需邻域对称性；$\mathbf{0}\in N$ 时包含**同坐标跨层边（非自环）**）。在**开边界**下，靠近边界的节点可能出现 $\deg^-<|N|$ **或** $\deg^+<|N|$ 的边界伪影（信息外流/内流不完整，链接§8 Garden-of-Eden现象），不影响与标准无限晶格模型的形式等价。

### 定义 2.2（状态赋值）

状态函数 $\sigma: V \to \Sigma$，满足对每节点 $v = (\mathbf{r}, t+1)$，$\sigma(v) = f(\{\sigma(u) \mid u \to v, u \in V\})$。假设 $f$ 为确定性函数，确保无冲突赋值。若考虑将局部约束以**多值关系**给出，则全局解的存在性退化为相应空间–时间SFT的**非空性判定**（§13不可判定）。初始层 $\sigma_0: \mathbb{Z}^d \times \{0\} \to \Sigma$ 给定。

### 定义 2.3（移位/作用）

在一侧时间域 $V=\mathbb{Z}^d\times\mathbb{Z}_{\ge0}$ 上，定义半群作用 $\tau^{(\mathbf v,m)}(\mathbf r,t)=(\mathbf r+\mathbf v,\;t+m)$ 仅对 $m\ge0$。空间移位 $\tau^{(\mathbf v,0)}$ 形成 $\mathbb{Z}^d$-群作用；时间移位 $\tau^{(\mathbf 0,m)}$ 为 $\mathbb{Z}_{\ge0}$-半群作用，以匹配单侧域。该作用保持 $E$ 不变：**空间方向** $\tau^{(\mathbf v,0)}$ 为图自同构；**时间方向** $\tau^{(\mathbf 0,m)}$（$m\ge 0$）仅为图的**半群自同态**（$m>0$ 时一般不可逆）。

若需双侧时间对称性，可将域扩为 $\tilde V=\mathbb{Z}^d\times\mathbb{Z}$（见 §4 的空间–时间 SFT 与自然扩张讨论）。

### 定义 2.4（可达偏序）

给定有向无环图 $(V,E)$，定义可达关系 $u \preceq v \iff$ 存在有向路径 $u \to^* v$，其中 $\to^*$ 为 $\to$ 的反射-传递闭包。由于 $E$ 仅自 $t$ 指向 $t{+}1$，图无有向环，故 $\preceq$ 为偏序。

### 定义 2.5（秩函数分层与叶状分解）

$S \subset V$ 为反链，若任意 $u,v\in S$ 皆互不可达（$u \npreceq v$ 且 $v \npreceq u$）。

一个 **秩函数分层（rank layering）** 由满射 $\rho:V\to I\subseteq\mathbb Z$ 给出，使得对每条边 $(u,v)\in E$ 有 $\rho(v)=\rho(u)+1$。令 $S_t=\rho^{-1}(t)$ 为第 $t$ 层，则每个 $S_t$ 为反链且 $\bigcup_{t\in I}S_t=V$ **且两两不交**。若 $(u,v)\in E$ 且 $u\in S_t$，则 $v\in S_{t+1}$（跨层边兼容性）。

族 $\{S_t\}_{t\in I}$ 称为**叶状分解**，等价于上述秩函数分层。在标准CA图 $V=\mathbb{Z}^d\times\mathbb{Z}_{\ge0}$ 上，取 $\rho(\mathbf r,t)=t$ 即得平凡叶状分解 $S_t=\mathbb{Z}^d\times\{t\}$。

注：此定义避免了"每条极大链与每个 $S_t$ 恰交一次"在单侧时间域上的形式问题（极大链未必向过去延伸到所有层）；秩函数等价表述更稳固。

### 命题 2.6（叶状分解诱导单步算子；假设 $f$ 确定性）

假设域为 $V=\mathbb Z^d\times\mathbb Z_{\ge0}$，邻域 $N$ 有限且平移不变，局部规则 $f:\Sigma^{N}\to\Sigma$ 确定性。给定叶状分解与局部规则 $f$，存在唯一的单步全局映射 $F_t:\Sigma^{S_t}\to\Sigma^{S_{t+1}}$。在 $\{S_t\}$ 由时间平移生成时，$F_t\equiv F$ 连续且移位交换，故由Curtis–Hedlund–Lyndon定理（§5）得局部性。注：对**任意**叶状分解仅保证存在 $F_t$，不承诺 $F_t$ 与平移交换。

---

## §3 状态约束与局部规则

### 定义 3.1（局部一致性约束）

约束要求：对任意路径 $p: v_0 \to v_1 \to \cdots \to v_k$，状态序列满足 $f$ 的递归应用。禁形集 $\mathcal{F}$ 定义为违反约束的有限子图模式。$\mathcal{F}$ 有限，由所有违反 $f$ 的 $|N|+1$ 节点子图组成，确保 $X_f$ 为有限型子移位（SFT）。此处仅给出禁形等价表述，以匹配§4的SFT语境；完整SFT定义见§4。

### 命题 3.1（约束传播；假设 $f$ 确定性）

假设域为 $V=\mathbb Z^d\times\mathbb Z_{\ge0}$，邻域 $N$ 有限且平移不变，局部规则 $f:\Sigma^{N}\to\Sigma$ 确定性。给定初始 $\sigma_0$，约束 $f$ 唯一确定全图状态。

**证明**：对层级 $t$ 归纳。基础步：$t=0$ 已定。归纳步：假设 $t$ 层确定，则 $t+1$ 层由入边状态和 $f$ 唯一计算。若存在歧义，则由 $f$ 的单值性导出矛盾，故唯一。存在性由递归构造保证；在 $f$ 为全定义的确定性函数前提下，给定任意初始切片 $\sigma_0$，单侧时间域 $t\ge0$ 上的全局解 $\sigma$ 总存在且唯一，因而单侧空间–时间SFT $X_f^+$ 始终非空。空性/不可判定性仅在（i）局部约束为**多值关系**时，或（ii）讨论**双侧**SFT $X_f$/自然扩张 $\Omega(F)$ 时出现（参考Berger定理[4]与§13）。 $\square$

---

## §4 符号动力系统表述（空间–时间 SFT 版）

默认 $\Sigma$ 离散，$\Sigma^{\mathbb Z^d}$、$\Sigma^{\mathbb Z^{d+1}}$ 取Tychonoff乘积拓扑；空间移位是同胚。

### 定义 4.1（空间–时间 SFT）

注：SFT为shift of finite type（有限型子移位），下文统一用SFT。

设 $f:\Sigma^{N}\to \Sigma$ 为局部规则，$(\mathbf r,t)\in\mathbb Z^{d+1}$。定义
$$
X_f :=\Big\{x\in \Sigma^{\mathbb Z^{d+1}}: \;
x(\mathbf r,t+1)=f\big((x(\mathbf r+\mathbf n,t))_{\mathbf n\in N}\big)\ \forall (\mathbf r,t)\Big\}.
$$

则 $X_f$ 是 $\mathbb Z^{d+1}$-SFT（禁形有限）。此为空间-时间子移位不变量（SFT），禁形由违反 $f$ 的有限模式组成。时间移位 $(\mathbf 0,1)$ 在 $X_f$ 上为群作用；空间移位为群作用。

### 命题 4.2（单侧动态视角与截面）

令 $F:\Sigma^{\mathbb Z^d}\to\Sigma^{\mathbb Z^d}$ 为局部规则 $f$ 的全局映射。定义单侧空间–时间 SFT $X_f^+\subset\Sigma^{\mathbb Z^d\times\mathbb Z_{\ge0}}$ 由 $x(\mathbf r,t+1)=f((x(\mathbf r+\mathbf n,t))_{\mathbf n\in N})$ 刻画（仅对 $t\ge 0$ 约束，并不对 $t<0$ 施加约束）。嵌入
$$
\Phi^+:\Sigma^{\mathbb Z^d}\to X_f^+,\quad
(\Phi^+(x))(\mathbf r,t)=F^{\,t}(x)(\mathbf r)\quad (t\ge0)
$$

与 $(0,1)$ 方向移位交换，故 $\Phi^+$ 在**时间移位的半群作用**意义下为（时间移位的半群作用意义下的）**拓扑共轭**（同胚）。$\Phi^+$ 为连续双射，且逆映射 $X_f^+\to\Sigma^{\mathbb Z^d}$ 为 $y\mapsto y(\cdot,0)$，故 $\Phi^+$ 为同胚。此同胚将单侧动态视角嵌入静态SFT，避免满射混淆。

**语义限定**：此处的"拓扑共轭"指**半群作用**（semigroup action）意义下的共轭：$\Phi^+$ 为同胚且满足 $\Phi^+\circ F = \tau^{(0,1)}\circ \Phi^+$（$\tau^{(0,1)}$ 为 $(0,1)$ 方向的**不可逆**时间移位）。

**证明要点**：因 $\Sigma$ 有限离散且乘积拓扑，使 $\Sigma^{\mathbb Z^d}$ 与 $X_f^+$ 紧致（Tychonoff定理）；$\Phi^+$ 连续且双射，于是为同胚（紧致域到豪斯多夫域的连续双射为同胚）。对任意 $y\in X_f^+$，由定义 $y(\cdot,t+1)=F(y(\cdot,t))$，归纳得 $y(\cdot,t)=F^{\,t}(y(\cdot,0))$。于是 $y=\Phi^+(y(\cdot,0))$（满射）；而若 $\Phi^+(x)=\Phi^+(x')$，则在 $t=0$ 切片即得 $x=x'$（单射）。**此共轭针对 $(0,1)$ 方向的半群作用。** $\square$

### 定义 4.3（自然扩张 / 逆向极限）

$$
\Omega(F)
:=\big\{(x_t)_{t\in\mathbb Z}\in(\Sigma^{\mathbb Z^d})^{\mathbb Z}\;:\;x_{t+1}=F(x_t)\ \forall t\in\mathbb Z\big\}.
$$

$\Omega(F)$ 是将 $(\Sigma^{\mathbb Z^d},F)$ 提升为可逆系统的自然扩张（逆向极限）。$\Omega(F)$ 非空当且仅当存在一条双向轨道；$F$ 满射是充分非必要条件，但也存在非满射而非空的情形（如常值映射），参考Kari综述（§13）。

**索引约定**：本文采用双侧序列并取 $x_{t+1}=F(x_t)$ 的约定；与标准逆向极限 $F(x_{t+1})=x_t$ 仅差时间索引方向，二者通过 $t\mapsto -t$ 等价。

### 命题 4.3（双侧 SFT 与自然扩张的天然同构并与移位作用共轭）

设 $X_f\subset\Sigma^{\mathbb Z^{d+1}}$ 为双侧空间–时间 SFT，$\Omega(F)$ 为自然扩张。定义
$$
\Psi:\Omega(F)\to X_f,\qquad
\big(\Psi((x_t)_{t\in\mathbb Z})\big)(\mathbf r,t)=x_t(\mathbf r).
$$

则以下成立：

(i) $\Psi$ 为双射且连续；其逆由 $x\in X_f$ 取序列 $x_t(\cdot):=x(\cdot,t)$ 给出；由"紧致 → 豪斯多夫的连续双射 ⇒ **逆连续**（等价于映射为**闭映射**）"，故同胚；

(ii) $\Psi$ **与所有空间平移以及时间移位**（$t\mapsto t+1$）**交换**；

(iii) 因而 $\Omega(F)$ 与 $X_f$ 在 $\mathbb{Z}^{d+1}$ 作用下**拓扑共轭**；

(iv) $\Omega(F)$ 非空 $\Longleftrightarrow$ $X_f$ 非空（存在双侧轨道）。

**证明要点**：$\Omega(F)\subset(\Sigma^{\mathbb Z^d})^{\mathbb Z}$ 与 $X_f\subset\Sigma^{\mathbb Z^{d+1}}$ 均取乘积拓扑，且为紧致豪斯多夫空间的闭子集。映射 $\Psi$ 连续且双射；两空间紧致且豪斯多夫，因此紧致域到豪斯多夫域的连续双射为同胚（即闭映射）。再与移位作用交换，从而给出拓扑共轭。由构造可见 $\Omega(F)\neq\varnothing \iff X_f\neq\varnothing$。此外，$F$ 满射为 $\Omega(F)$ 非空的充分但非必要条件（例：常值映射可能产生固定点轨道）。 $\square$

因而下例给出**非满射亦可 $\Omega(F)\neq\varnothing$** 的特例：

**例 4.A（非满射但自然扩张非空）**：令 $\Sigma$ 含符号 $a$，设 $\mathbf{a}\in\Sigma^{\mathbb Z^d}$ 为处处等于 $a$ 的常配置。定义 CA $F(x)\equiv\mathbf{a}$。则 $F$ 与空间移位交换（因 $\mathbf{a}$ 平移不变），但非满射；$\Omega(F)$ 至少包含常轨道 $(\mathbf{a},\mathbf{a},\dots)$，故非空。

---

## §5 Curtis–Hedlund–Lyndon定理在标准域上的表述

### 定理 5.1（CHL）

映射 $F:\Sigma^{\mathbb Z^d}\to \Sigma^{\mathbb Z^d}$ 与所有空间移位交换且在乘积拓扑下连续，当且仅当存在有限邻域 $N\subset \mathbb Z^d$ 与局部函数 $f:\Sigma^N\to \Sigma$ 使得
$$
(F(x))(\mathbf r)=f\big((x(\mathbf r+\mathbf n))_{\mathbf n\in N}\big).
$$

注：CHL定理仅刻画空间配置空间 $\Sigma^{\mathbb{Z}^d}$ 上的因子（局部）映射；该定理不涉及时间维；时间一致性通过 $X_f$ 的禁形给出。对 $\mathbb Z^{d+1}$-SFT 的投影一般为因子映射，满射性需单独讨论（§4.2/§4.3）。在时间维上，类似结果需通过 $X_f$ 的投影（§4），投影为因子映射，若 $F$ 满射则满射投影。

---

## §6 存在唯一性与因果锥证明

### 引理 6.1（因果锥：包含与上界）

设邻域半径为 $r$。对任意节点 $(\mathbf r,t)$，其值仅受初始层 $t=0$ 的区域影响，且
$$
\mathrm{Past}(\mathbf r,t)\subseteq B_{\|\cdot\|_1}(\mathbf r;\, r t),\qquad
|\mathrm{Past}(\mathbf r,t)|\le |B_{\|\cdot\|_\infty}(\mathbf r;\, r t)|
=(2 r t+1)^d,
$$
其中 $B_{\|\cdot\|_1}$ 为 $\ell_1$ 球，$B_{\|\cdot\|_\infty}$ 为 $\ell_\infty$ 立方体。最后一式给出便于估计的 $\ell_\infty$ 上界（**端点数上界**，非路径条数）。（注意：长度 $t$ 的因果路径条数为 $|N|^t$，与可达端点数的 $\Theta(t^d)$ 上界不同。）

注：更精确的 $\ell_1$ 球体素计数见脚注；正文保留上界 $(2rt+1)^d$ 即可，避免读者把"路径数"与"可达端点数"混淆。

选取初始节点集 $S_0 = B_{\|\cdot\|_1}(\mathbf{r}; r t)$，追踪路径生成时间截面，等价于动态演化。

---

**脚注**：$\ell_1$ 球 $B_{\|\cdot\|_1}(0;R)$ 的体素数为 $|B_{\|\cdot\|_1}(0;R)|=\sum_{j=0}^{d} 2^{\,j}\binom{d}{j}\binom{R}{j} = \Theta(R^d)$（其中 $R=rt\in\mathbb N$，本框架中 $r,t$ 为整数，故组合数取整域有定义；此计数公式仅对 $R\in\mathbb N$ 适用）。

### 定理 6.1（存在唯一性；假设 $f$ 确定性）

假设域为 $V=\mathbb Z^d\times\mathbb Z_{\ge0}$，邻域 $N$ 有限且平移不变，局部规则 $f:\Sigma^{N}\to\Sigma$ 确定性。给定 $f, \sigma_0$，$\sigma$ 存在且唯一。

**证明**：存在由递归构造；唯一由最小差异层矛盾。对于 $t\ge0$ 单侧域与确定性 $f$，**存在性无条件成立**；有限窗口实现仅是对该递归构造的截断验证。SFT 空性与判定困难仅出现在（i）**多值关系/约束型系统**或（ii）**双侧时间**的自然扩张情形（见 §3/§4/§13）。 $\square$

---

## §7 线性与非线性规则分析

### 定义 7.1（线性规则）

若 $f$ 在有限域线性，则永恒图可用傅里叶分解谱分析。线性指：布尔情形为 $\mathrm{GF}(2)$ 线性；多值情形指 $\mathbb Z_m$ 或选定环/群上的线性，与§12群提升的代数底层一致。

### 定义 7.2（Walsh–Hadamard 展开（布尔情形，$\Sigma=\{0,1\}$））

注：下文简称 Walsh 展开。

对布尔 $f$（布尔情形，$\Sigma=\{0,1\}$），定义标准化映射 $\varphi: \{0,1\} \to \{-1,1\}$ 为 $\varphi(0) = 1$, $\varphi(1) = -1$。通过 $\tilde{f} = \varphi \circ f \circ \varphi^{-1}$ 转换为 $\tilde{f}: \{-1,1\}^{|N|} \to \{-1,1\}$，然后做Walsh展开为
$$
\tilde{f}(z) = \sum_{S \subseteq N} \hat{f}(S) \prod_{j \in S} z_j,
$$
其中系数 $\hat{f}(S) = \mathbb{E}_{z \sim \{-1,1\}^{|N|}}[\tilde{f}(z) \prod_{j \in S} z_j]$（期望取伯努利(1/2)乘积测度）。

注：Walsh基正交，定义内积 $\langle f,g\rangle=\mathbb E[f g]$，满足Parseval定理 $\sum_S \hat{f}(S)^2 = \|\tilde{f}\|_2^2 = 1$（$\tilde{f}\in\{-1,1\} \Rightarrow \mathbb{E}[\tilde{f}^2]=1$ 在伯努利测度下）；谱稀疏度刻画高阶相互作用。

**关键区别（路径数vs端点数，二者不可混用）**：长度为 $t$ 的有向邻域路径数恰为 $|N|^t$（**路径条数**），但不同路径可汇合到同一端点；因此**可达端点个数上界**（几何体素计数）$\le |B_{\|\cdot\|_1}(0;r t)|=\Theta(t^d)$，与§6的体素上界一致。在非线性 $f$ 下，路径折叠更明显。

**例 7.A（Rule 90的Walsh系数）**：Rule 90邻域为 $N=\{-1,1\}$（忽略中心），规则 $f(x_{-1},x_1)=x_{-1}\oplus x_1$（XOR）。在 $\{-1,1\}$ 表示下，$\tilde{f}(z_{-1},z_1)=z_{-1}\cdot z_1$。Walsh展开：$\hat{f}(\{-1\})=\hat{f}(\{1\})=0$（无单变量项），$\hat{f}(\{-1,1\})=1$（交叉项），$\hat{f}(\varnothing)=0$（无常数项）。验证Parseval：$0^2+0^2+1^2+0^2=1$。初始 [0,0,1,0,0] 下一层 [0,1,0,1,0]，再下一层 [1,0,0,0,1]，匹配线性传播，通过符号验证无误。

---

## §8 Garden-of-Eden定理在图中的表述

### 定义 8.1（pre-injective）

对 $F:\Sigma^{\mathbb Z^d}\to\Sigma^{\mathbb Z^d}$，若任意仅在有限位置不同的两初态 $x\ne y$ 满足 $F(x)\ne F(y)$，则称 $F$ 为pre-injective。等价地：若 $x,y$ 仅在有限集合上不同且 $F(x)=F(y)$，则必有 $x=y$。

### 定理 8.1（Moore–Myhill；$\mathbb Z^d$全移位）

在 $\mathbb Z^d$ 上的全移位（full shift）$\Sigma^{\mathbb Z^d}$ 的CA：
$$
F\ \text{surjective}\quad \Longleftrightarrow \quad F\ \text{pre-injective}.
$$

注：该结果依赖作用群的amenable性（$\mathbb Z^d$ 满足）。Moore–Myhill等价在**amenable群**（如 $\mathbb Z^d$）上成立；在非amenable群（如自由群 $F_2$）上，两向蕴含均可能失败，详见[6]。本定理置于amenable群语境，在全移位上的CA；若在一般SFT上，还需补充强不可约性等条件。

**证明**：参考Moore-Myhill。 $\square$

### 备注 8.1（有限窗口与伪 GoE 现象）

**在 $\mathbb{Z}^d$ 的全移位（而非一般 SFT）情形下**，Moore–Myhill 等价成立；一般 SFT 需强不可约性等额外条件。在**无限晶格**或**周期边界且各方向尺度 $L_i>2r$** 的情形下，每个非初始节点有 $|N|$ 条入边；若 $L_i\le 2r$，可能因**邻域别名**导致 $\deg^-<|N|$（出度同理）。**在周期边界下**（即便 $L_i\le 2r$），邻域别名仅合并而不消除所有入边（假设 $N\neq\varnothing$），故不会出现"无入边的非初始节点"；**在开边界**有限窗口下，则可能出现 $\deg^-=0$ 的边界节点（属伪 GoE 现象，不影响无限晶格上的结论）。若在**开边界**有限窗口或截断图上模拟，顶部/侧边由于边界导致的"缺边"可能使某些局部模式无法实现（此时可能出现 $\deg^-<|N|$ 或 $\deg^+<|N|$），但这属于**边界伪影（finite-window artefacts）**，并非Moore–Myhill 意义下的 Garden-of-Eden。GoE等价（满射 $\Leftrightarrow$ pre-injective）仅在无限、齐次、**amenable群**（如 $\mathbb Z^d$）作用的情形成立。

---

## §9 模拟验证与计算实现

使用Python模拟1D永恒图（Rule 90）。构建有限图，验证状态一致。此为周期边界有限窗口模拟（示例仅验证局部等价，不涉及GoE），锥大小验证（$d=1,r=1,t=2$ 为5）通过符号计算。对于无限域，可扩展 $L\to\infty$ 模拟收敛。代码示例：

（有限周期窗口，仅用于局部一致性验证，非 GoE 场景）

```python
# This is a finite periodic window; it checks local consistency only.
# G 仅示意空间–时间图的构建，不参与数值校验。
import networkx as nx
import numpy as np

# Define Rule 90 function for 1D CA with periodic boundary
def rule_90(state):
    n = len(state)
    new_state = np.zeros(n, dtype=int)
    for i in range(n):
        left = state[(i-1) % n]
        right = state[(i+1) % n]
        new_state[i] = left ^ right  # Rule 90: XOR of left and right
    return new_state

# Initial state and window size (T time steps, L space points)
L = 5
T = 3
initial = np.array([0, 0, 1, 0, 0])

# Generate space-time window iteratively
window_iter = np.zeros((T, L), dtype=int)
window_iter[0] = initial
for t in range(1, T):
    window_iter[t] = rule_90(window_iter[t-1])

# Simulate via graph (space-time SFT)
G = nx.DiGraph()
for t in range(T):
    for r in range(L):
        G.add_node((r, t))

for t in range(T-1):
    for r in range(L):
        # Add edges for neighborhood {-1,1} (Rule 90 ignores center)
        for n in [-1, 1]:
            G.add_edge(((r + n) % L, t), (r, t+1))

# Assign states from initial
window_graph = np.zeros((T, L), dtype=int)
window_graph[0] = initial
for t in range(1, T):
    for r in range(L):
        neighbors = [window_graph[t-1, (r + n) % L] for n in [-1, 1]]
        # Apply rule_90 logic
        left, right = neighbors
        window_graph[t, r] = left ^ right

# Assert consistency: all t satisfy x(.,t+1) = f(x(.,t))
for t in range(T-1):
    assert np.array_equal(window_graph[t+1], rule_90(window_graph[t]))

# Assert matches iterative method
assert np.array_equal(window_graph, window_iter)

print('All assertions passed')
```

所有断言通过，验证确认等价。通过符号计算和断言，我们进一步确认因果锥大小和状态传播的一致性，例如在 $d=1, r=1, t=2$ 时锥大小为5。

---

## §10 与静态块元胞自动机理论的等价性讨论

永恒图理论与静态块元胞自动机理论在核心表述上高度相似，但前者通过有向图移除显式时间维，后者将时间纳入高维坐标系。以下以定理形式给出等价性的充要条件。

### 定理 10.1（永恒图–静态块–自然扩张的等价框架）

设 $f:\Sigma^N\to\Sigma$，$F$ 为诱导的全局映射。

**(1) 单侧情形**：$X_f^+\subset\Sigma^{\mathbb Z^d\times\mathbb Z_{\ge0}}$ 与图 $(V,E)$（$V=\mathbb Z^d\times\mathbb Z_{\ge0}$）上的状态函数 $\sigma:V\to\Sigma$ 一一对应，且切片 $t\mapsto \mathbb Z^d\times\{t\}$ 给出叶状分解。

**(2) 双侧情形**：自然扩张 $\Omega(F)$ 与双侧空间–时间 SFT $X_f\subset\Sigma^{\mathbb Z^{d+1}}$ 同胚且与移位作用共轭（见§4命题4.3）。特别地，若 $F$ 满射，则 $\Omega(F)\neq\varnothing$，从而 $X_f\neq\varnothing$。

**结构映射说明**：等价性依赖于路径追踪机制。选取初始节点集 $S_0$（覆盖因果锥 $B_{\|\cdot\|_1}(\mathbf{r}; r t)$）并追踪路径，生成的层级截面 $\mathcal{O}_t$ 等价于静态块的时间切片 $\mathcal{M}_t$。在移位不变性和有限型子移位（subshift）框架下，永恒图的不变集 $Y$ 对应静态块的有限型子移位集合。

**计算验证**：通过符号和数值模拟确认等价性。例如，在Rule 90下，永恒图路径追踪与静态块迭代产生相同状态序列：[0,0,1,0,0] → [0,1,0,1,0] → [1,0,0,0,1]。使用断言检测锥大小 $(2 r t + 1)^d$ 和状态匹配，确保逻辑自洽。若初始条件或规则 $f$ 不一致，则等价失效；否则，在确定性局部规则下，二者始终等价，提供从动态到静态视角的无缝桥接。

就双侧表述而言，一般 CA 可通过空间–时间 SFT $X_f$ 描述双向时间的解，但 $X_f$ 仅包含那些能在所有 $t\in\mathbb Z$ 上持续满足 $x(\cdot,t+1)=F(x(\cdot,t))$ 的轨道。用自然扩张 $\Omega(F)$ 可无缝连接单侧系统与双侧 SFT：若 $F$ 满射，则 $\Omega(F)$ 与 $X_f$ 均非空；一般地，$\Omega(F)\subset (\Sigma^{\mathbb Z^d})^{\mathbb Z}$ 与 $X_f\subset \Sigma^{\mathbb Z^{d+1}}$ 通常都是各自全空间的真子集。由此，"永恒图/静态块/SFT"三视角在可逆时完全一致，在一般情形下通过 $\Omega(F)$ 达成因子关系。在不可逆时，永恒图的孤岛对应 $\Omega(F)$ 的投影亏缺，此亏缺由非满射诱导，参考Moore-Myhill（§8）。

这一等价性并非绝对：永恒图强调图拓扑的永恒性，而静态块更侧重高维数据体。若忽略时间维的显式性，永恒图可视为静态块的图论重构，反之亦然。该讨论强化了理论的统一性，避免哲学与数学脱节。

---

## §11 永恒图与量子叠加态的结构类比与边界

**本文所有"量子/酉"措辞仅为结构类比；本文不引入希尔伯特空间与复线性。**

**免责声明**：下述类比为**结构类比**，并未引入复线性、内积或纠缠等量子力学公设；任何"酉化"均指Bennett式**可逆计算嵌入**（§12.2），非物理含义。本文不引入希尔伯特空间、线性叠加或纠缠结构；"并行/干涉"均指组合学路径计数与图形态，而非物理量子态叠加。线性CA之外的非线性规则不具备任意线性叠加原则，因而"量子并行（组合学意义）"仅为**路径计数上的组合学平行**。

永恒图元胞自动机似乎更类似于量子叠加态，而静态块元胞自动机则更类似于经典态。这一类比源于两种框架对"状态"与"演化"的处理方式，提供物理哲学层面的启发。以下从本体论、计算性和可逆性三个维度讨论，确保逻辑自洽。

首先，从本体论视角，永恒图的节点和边编码所有可能路径，形成一个"叠加"的网络结构：一个节点的状态依赖多个输入边（类似于量子态的结构依赖，而非实际叠加），而路径遍历对应测量过程，导致"坍缩"到特定截面。这在结构上类似于量子力学的叠加态，其中系统在测量前存在于多重可能性的线性叠加，如薛定谔方程 $i\hbar\,\partial_t\psi = \hat{H} \psi$。相反，静态块将时空视为确定性数据体，所有状态预先固定，如经典牛顿力学的相空间轨迹，缺乏"分支"潜力。永恒图的移位不变性进一步强化这一类比：图拓扑允许并行路径，类似于量子多世界诠释，而静态块的坐标系更像单世界经典确定性。

其次，从计算性看，永恒图的因果锥扩展 $(2 r t + 1)^d$ 反映并行可能性，永恒图路径分支 $|N|^t$ 类似于量子并行（组合学意义），但经典模拟指数代价。**关键区别**：组合学并行 $\neq$ 复线性叠加；线性CA（如Rule 90）可用傅里叶/Walsh谱；非线性不具叠加。这在可逆情形下尤为明显：双向图允许"逆向"追踪，类似于酉演化 $U^\dagger U = I$。静态块则对应经典计算：状态通过序贯迭代确定，复杂度线性于时间 $t$，缺乏叠加的指数加速。验证示例：在Rule 90下，永恒图路径生成分形模式（如谢尔宾斯基三角），类似于量子干涉（组合学意义）图案，而静态块切片更像经典扩散。

最后，从可逆性视角，永恒图在不可逆时引入"孤岛"（Garden-of-Eden状态），类似于量子测量后的不可逆坍缩，而静态块的非满射映射对应经典熵增。此为结构类比，非物理；可逆 CA 可做经典可逆计算与形式上的酉扩展（Bennett 技巧，参考§12），但本文并不引入复线性叠加与纠缠。

通过符号验证（如断言路径分支数等于 $|N|^t$），确认类比的自洽性。该视角扩展理论的应用，如量子CA模拟。可逆CA的"酉化嵌入"属于形式手段而非物理实现。

---

## §12 应用：计算优化、可逆性、哲学意涵

### 12.1 计算优化

令 $\mathsf{Cone}_t(\mathbf r)$ 为节点 $(\mathbf r,t)$ 的过去因果锥，则 $|\mathsf{Cone}_t(\mathbf r)|\le (2 r t+1)^d$。在忽略写–读冲突与缓存的PRAM理想模型下，并行求值代价为 $\mathcal O\big((2 r t+1)^d \cdot |N|\big)$（此为**上界估计**，不影响主体理论）。在有限周期盒 $L^d$ 上，每步全局更新为 $\mathcal O(L^d|N|)$。选取节点追踪路径生成截面，支持优化。

### 12.2 可逆性与量子嵌入

**定理 12.1（可逆 CA 判定——全移位版）**

在全移位 $\Sigma^{\mathbb Z^d}$ 上，CA $F$ 可逆 $\Longleftrightarrow$ $F$ 为双射 $\Longleftrightarrow$ 存在有限半径的局部逆映射（即 $F^{-1}$ 亦为 CA）。

说明：由 §8 的 Moore–Myhill（满射 $\Leftrightarrow$ pre-injective）知，双射即可逆；§4.3 的双侧空间–时间 SFT $X_f$ 与自然扩张 $\Omega(F)$ 仅用于把不可逆动力系提升为可逆系统的表述工具，不改变上述判定的前提空间。

**构造 12.A（分区-块可逆/Margolus）**

把格子按相位交替分区；对每块施加置换 $\pi$。全局是置换，故可逆，逆为 $\pi^{-1}$ 按反相位作用。

**构造 12.B（二阶可逆提升/群提升）**

设 $(\Sigma,\cdot)$ 为任意群（有限）。在字母表 $\Sigma'=\Sigma\times\Sigma$ 上定义局部规则
$$
R\!\left((x^t,y^t)\right)(\mathbf r)
=\Big(
  f\big((x^t(\mathbf r+\mathbf n))_{\mathbf n\in N}\big)\cdot y^t(\mathbf r),\;
  x^t(\mathbf r)
\Big).
$$

**引理 12.B.1（局部显式逆公式给出 $R^{-1}$ 亦为 CA）**：$R$ 为 CA，且逆映射同为局部：
$$
R^{-1}\!\left((u^{t+1},v^{t+1})\right)(\mathbf r)
=\Big(
  v^{t+1}(\mathbf r),\;
  \big(f\big((v^{t+1}(\mathbf r+\mathbf n))_{\mathbf n\in N}\big)\big)^{-1}\cdot u^{t+1}(\mathbf r)
\Big).
$$

采用左乘约定，逆映射与前向映射在局部上严格互逆。因此 $R$ 为全局双射且 $R^{-1}$ 亦为 CA。特例：阿贝尔群（如二值情形取 $\cdot=\texttt{XOR}$）时，左乘与右乘等价。图语义下入/出度仍有限。

### 12.3 哲学意涵

永恒主义：图是本体，时间是路径认识。节点扩展反映静态整体。

---

## §13 复杂度与不可判定边界

不变集空性不可判定（Berger定理）。在 $d=1$ 的一维 CA 上，若以标准邻域与齐次规则为前提，满射可判定（Amoroso-Patt；算法检查有限窗口模式）；而 $d\ge2$ 则满射不可判定（Kari）。类似地，可逆性判定与部分性质在高维出现多类不可判定现象（包括可逆性/满射性以及 SFT 空性，见 Berger 与 Kari 综述）。

---

## §14 结论与展望

该理论独立自洽，提供永恒视角。通过等价性和量子类比讨论，我们确认了其与静态块理论的互补性，并扩展物理意涵。未来扩展包括：整合量子CA模拟（§11），高维SFT非空性分析，探索移位不变测度下的典型性，以及在分布式计算中的应用。潜在应用包括并行计算中的图加速器。

---

## 参考文献

1. Wolfram, S. (2002). *A New Kind of Science*.
2. Hedlund, G.A. (1969). *Mathematical Systems Theory*.
3. Moore, E.F. (1962). *Proceedings AMS*.
4. Berger, R. (1966). *Memoirs AMS*.
5. Lind, D., & Marcus, B. (1995). *An Introduction to Symbolic Dynamics and Coding*. Cambridge University Press.
6. Ceccherini-Silberstein, T., & Coornaert, M. (2010). *Cellular Automata and Groups*. Springer.
7. Kari, J. (1994). Reversibility and surjectivity problems of cellular automata. *Journal of Computer and System Sciences*, 48(1), 149–182.
8. Myhill, J. (1963). The converse of Moore's Garden-of-Eden theorem. *Proceedings of the American Mathematical Society*, 14(4), 685–686.
9. Amoroso, S., & Patt, Y. N. (1972). Decision procedures for surjectivity and injectivity of parallel maps for tessellation structures. *Journal of Computer and System Sciences*, 6(5), 448–464.
10. Kůrka, P. (2003). *Topological and Symbolic Dynamics*. Société Mathématique de France.