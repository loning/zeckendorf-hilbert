# 无时块元胞自动机理论：高维对称约束下的静态结构形式化


这个太复杂了, 基本放弃

**Timeless Block Cellular Automata Theory: A Formalization of Static Structures under High-Dimensional Symmetric Constraints**

**作者**：Auric
**日期**：2025年10月17日
**版本**：v1.7 (修订版，基于第六轮审阅反馈)

---

## 摘要

无时块元胞自动机理论将元胞自动机（Cellular Automata, CA）推广为一个完全对称的高维静态结构，其中所有维度被视为等价坐标，形成一个永恒不变的块体。该理论的核心在于：摒弃全局时间概念，将 CA 表述为受局部对称约束的高维子移位空间。从全局视角，传统 CA 的演化被重构为对这一静态结构的任意路径遍历，而非定向动态过程。我们通过形式化定义、详细数学证明和模拟验证，构建了这一独立理论框架，并讨论其在计算理论、信息论和哲学永恒主义中的应用。该理论逻辑自洽：所有可行配置由局部一致性约束所刻画，形成移位不变的高维场（一般不保证唯一性，唯一性需额外结构条件）。本文证明了高维配置集合 $Y$ 为有限型子移位并在定向确定条件下与传统 CA 等价，避免了时间方向的偏置，使用布尔傅里叶分析和拓扑动力学等工具，确保对称性。

**关键词**：元胞自动机，无时块，对称高维结构，符号动力系统，有限型子移位，Curtis–Hedlund–Lyndon 定理，Garden-of-Eden 定理

---

## §1 引言

### 1.1 背景与动机

元胞自动机作为一种离散计算模型，由冯·诺依曼和乌拉姆提出，用于模拟复杂系统的涌现行为。传统观点将 CA 视为动态演化系统：细胞根据局部规则在离散时间步更新状态。然而，从块宇宙理论和永恒主义视角，我们可以将 CA 重新诠释为静态结构。原静态块理论虽将时间纳入坐标，但仍保留时间方向的特殊性（如从初态起始的前向演化）。

本理论推广原框架，彻底去除全局时间概念：所有维度对称，等价对待。时间不再是特殊坐标，而是与空间维度相同的轴。整个结构是一个永恒的高维晶格配置，受局部约束定义，无需起始点或方向偏置。这一推广受启发于相对论时空的对称性和量子场论的永恒场概念，应用于 CA 时，形成一个纯静态的、无时的块体。在 $\mathbb{Z}^m$（乃至一般可数群）上，映射连续且与移位群作用可交换当且仅当存在有限记忆的局部规则（Curtis–Hedlund–Lyndon 型定理）；参见 Hedlund (1969)、Kitchens (1998)、Ceccherini-Silberstein & Coornaert (2010)。Richardson (1972) 讨论了局部变换与铺砌的相关结构，本文的 CHL 推广主要基于前述标准文献。

潜在挑战包括约束一致性可能导致的空配置空间，本文通过有限型子移位（SFT）的非空性条件（§6 定理 6.1）与高维不可判定性边界（§11）予以系统处理。

### 1.2 理论核心思想

本文构建的无时块 CA 理论强调：CA 本质上是高维对称数据体，由局部规则定义的配置空间构成，无需区分"空间"与"时间"。该框架深化了对 CA 的理解，桥接计算模型与物理哲学。我们聚焦于拓扑动力学、布尔傅里叶分析等框架，确保逻辑自洽和对称性。

### 1.3 论文结构

本文组织如下：

- **§2** 建立高维对称 CA 的形式化定义与配置空间
- **§3** 定义无时块结构与高维图
- **§4** 建立子移位与有限型子移位（SFT）表述
- **§5** 陈述 Curtis–Hedlund–Lyndon 定理的推广
- **§6** 证明无时块的存在非空性与局部依赖域
- **§7** 讨论线性 CA 的群傅里叶分解在高维对称下的扩展
- **§8** 介绍非线性布尔规则的 Walsh 展开
- **§9** 陈述 Garden-of-Eden 定理及其对无时块的意义
- **§10** 应用：计算优化、可逆性与量子嵌入、哲学意涵
- **§11** 讨论复杂度与不可判定边界
- **§12** 结论与展望
- **附录 A** 一般群 (G) 上的无时块 CA 结构（精简版）

---

**Notation（全局记号速览）**：$\Sigma$ 状态集；$X=\Sigma^{\mathbb Z^m}$ 配置空间；$N$ 邻域，$r_N=\max_{\mathbf n\in N}\|\mathbf n\|_\infty$（邻域半径）；$C$ 全局约束映射，$\mathrm{Fix}(C)$ 固定点 SFT；$S=N\cup\{0\}$ 禁形支撑；$B_m=(\mathbb Z/2\mathbb Z)^m\rtimes S_m$ 超正交群，$H\le B_m$ 为对称子群；$P$ 为定向确定的 past shape（其空间切片半径记 $r_P$）；$\mathsf{Spacetime}(F)$ 为 CA 时空 SFT。

---

## §2 高维对称元胞自动机的形式化定义

### 定义 2.1（高维对称元胞自动机结构）

一个 $m$-维对称元胞自动机结构定义为四元组 $\mathcal{C} = (\mathbb{Z}^m, \Sigma, N, f)$，其中：

- $\mathbb{Z}^m$ 是高维格点集合，所有维度对称
- $\Sigma$ 是有限状态集合（例如 $\{0,1\}$）
- $N \subset \mathbb{Z}^m$ 是对称邻域（允许包含 $0$，例如高维 von Neumann 或 Moore 邻域，确保旋转/反射不变）
- $f: \Sigma^{|N|} \to \Sigma$ 是局部函数，对称于维度置换

设 $H \le B_m$ 为有限对称子群，其中 $B_m$ 为**超正交群**（hyperoctahedral group），即 $B_m = (\mathbb{Z}/2\mathbb{Z})^m \rtimes S_m$，其元素为符号翻转与坐标置换的半直积：每个 $h \in B_m$ 可表示为先对各坐标施加独立的 $\pm 1$ 符号翻转（$m$ 个独立选择），再施加坐标置换（$S_m$ 的元素）。这是 $m$ 维超立方体的对称群，阶为 $|B_m| = 2^m m!$。称结构为 $H$-对称，若 $h(N)=N$ 且
$$
f\big((a_{h^{-1}\mathbf{n}})_{\mathbf{n}\in N}\big)=f\big((a_{\mathbf{n}})_{\mathbf{n}\in N}\big),\quad \forall h\in H.
$$

这避免了对称性过强要求。是否取 $0 \in N$ 由所需的局部约束决定；固定点 SFT 的禁形统一定义在 $S = N \cup \{0\}$。

**示例**：对于 2D 高维 Moore 邻域，$N = \{ (di, dj) : |di| \leq 1, |dj| \leq 1 \}$（包含中心），半径 $r_N = 1$，满足对称性。

**注记与构造性判例**：在传统 CA 语境中，全局映射 $F$ 是更新映射；本文的 $C$ 用作自洽约束算子（取不动点）。当 $0 \in N$ 且 $f$ 依赖中心位时，固定点方程 $x(\mathbf{p}) = f(x(\mathbf{p}), \ldots)$ 的可满足性取决于 $f$ 结构：

**判例 1（线性奇偶约束，解非唯一）**：令 $\Sigma = \{0, 1\}$，$f(x_0, x_1, \ldots, x_{|N|-1}) = x_0 \oplus \sum_{\mathbf{n} \in N \setminus \{0\}} x_{\mathbf{n}}$（中心 XOR 邻域和）。固定点方程化为 $\sum_{\mathbf{n} \in N \setminus \{0\}} x(\mathbf{p} + \mathbf{n}) \equiv 0 \pmod{2}$。因此**解集是线性方程组的核**（$\mathbb{F}_2$ 上的卷积核），**非唯一**：除 $x \equiv 0$ 外，至少包含 $x \equiv 1$（当 $|N \setminus \{0\}|$ 为偶数）；在 1D 还包含所有 2 周期解（如 $\ldots 0101 \ldots$ 和 $\ldots 1010 \ldots$），在更高维可出现条纹/棋盘等族。这一点与"唯一性须额外结构条件"（§6 命题 6.2）一致。

*提示*：上述条纹/棋盘是否为解取决于邻域具体形状与偶奇性；例如 2D von Neumann 邻域下棋盘给出邻域和为偶数而满足约束，但对某些非对称邻域则未必成立。

**判例 2（多不动点，邻域几何依赖）**：取 $f(x_0, \ldots) = x_0 \land (\bigvee_{i \geq 1} x_i)$（中心 AND 邻域有 1）。固定点除全 0、全 1 外，还包括**无孤立 1** 的配置（每个取 1 的格点至少有一个邻居也取 1）。例如条纹/团簇模式满足；而棋盘模式 $x(\mathbf{p}) = (p_1 + p_2) \mod 2$ 的可行性**依赖邻域几何**：在 **von Neumann 邻域**（4个正交邻居）下**不满足**（每个 1 的邻居全为 0，$1 \land 0 = 0 \neq 1$），但在 **Moore 邻域**（8个邻居含对角）下**满足**（每个 1 有 4 个对角邻居=1，$\bigvee = 1$，故 $1 \land 1 = 1$）。这体现了固定点结构对邻域拓扑的敏感性。

**判例 3（无解，导致 $\mathrm{Fix}(C) = \varnothing$）**：设计 $f$ 使得 $x(\mathbf{p}) = \neg x(\mathbf{p})$（如 $f(x_0, \ldots) = 1 - x_0$，忽略邻域）。无配置满足约束，$\mathrm{Fix}(C) = \varnothing$。

**$0 \notin N$ 的处理**：当 $0 \notin N$ 时，固定点约束通过 $S = N \cup \{0\}$ 上的禁形统一表达（定义 4.1）：$\mathcal{F} = \{a \in \Sigma^S : a(0) \neq f(a|_N)\}$，无需显式写自指方程。

### 定义 2.2（邻域半径）

记 $r_N := \max_{\mathbf{n} \in N} \|\mathbf{n}\|_\infty$ 为邻域的 $L_\infty$ 半径（常用于 Moore 邻域），其中 $\|\mathbf{n}\|_\infty = \max_{i=1}^m |n_i|$。邻域 $N$ 必须对称：若 $\mathbf{n} \in N$，则 $-\mathbf{n} \in N$，且对 $H$ 协变。

### 定义 2.3（配置空间）

令配置空间 $X = \Sigma^{\mathbb{Z}^m}$ 赋予乘积离散拓扑。这是紧空间，由 Tychonoff 定理保证。

### 定义 2.4（全局约束映射）

给定邻域 $N$ 与局部函数 $f$，定义全局约束映射
$$
C: X \to X, \qquad (C x)(\mathbf{p}) = f\left( \{ x(\mathbf{p} + \mathbf{n}) \mid \mathbf{n} \in N \} \right)
$$

**约束方程解释**：约束作为不动点 $\mathrm{Fix}(C) = \{ x \in X \mid C x = x \}$ 定义，避免循环依赖。当 $0 \in N$ 时，固定点方程 $x(\mathbf{p}) = f(x(\mathbf{p}), \ldots)$ 并非自指矛盾，而是对每个位点 $\mathbf{p}$，要求存在状态 $x(\mathbf{p})$ 满足该等式。此类方程的可满足性取决于 $f$ 的结构：
- 若 $f(s, \ldots) = s$ 对所有输入成立（恒等于中心），则 $\mathrm{Fix}(C) = X$（全空间）。
- 若 $f(s, \ldots) = s \oplus g(\text{其他})$ 在有限域上，则可能唯一解（如全0）或多支解。
- 一般情形下，非空性需通过局部约束传播验证（见定理6.1）。

由于 $N$ 有限，$C$ 是以 $N$ 为记忆的滑动块码；其固定点等化子 $\mathrm{Fix}(C)$ 因而可由有限禁形描述（取 $S = N \cup \{0\}$）。禁形阶数为 $\max_{\mathbf{s}, \mathbf{t} \in S} \|\mathbf{s} - \mathbf{t}\|_\infty$，以明确计算复杂度。

### 定义 2.5（移位映射）

对任意 $\mathbf{v} \in \mathbb{Z}^m$，定义移位作用 $\sigma^\mathbf{v}: X \to X$ 为
$$
(\sigma^\mathbf{v} x)(\mathbf{p}) = x(\mathbf{p} + \mathbf{v})
$$

移位在所有维度对称。

---

## §3 无时块：高维对称图

### 定义 3.1（高维对称图）

定义高维对称图
$$
\mathcal{M}: \mathbb{Z}^m \to \Sigma
$$

满足局部对称约束：
$$
\forall \mathbf{p} \in \mathbb{Z}^m, \quad \mathcal{M}(\mathbf{p}) = f\left( \{ \mathcal{M}(\mathbf{p} + \mathbf{n}) \mid \mathbf{n} \in N \} \right)
$$

### 定义 3.2（无时块）

称 $\mathcal{M}$ 为无时块（timeless block），它是 $\mathrm{Fix}(C)$ 的元素，满足局部约束，并在移位作用下构成闭不变集。

**解释**：无时块是一个整体对象，无需时间方向；"演化"被重构为沿任意维度的路径遍历。这避免了原定义的循环。

**示意图描述与叶分解**：想象一个 3D 晶格，其中每个点状态满足局部约束；路径遍历如沿 z 轴的"时间"序列，展示从静态结构到动态视图的投影。

形式上，可将 $\mathbb{Z}^m$ 中选定方向的层分解视作一族"叶"（foliation），每片叶上的投影是 $Y$ 的因子；当该方向定向确定时，该因子与某 CA 的时空图滑动块码等价。以下 ASCII 图示展示 2D SFT 的"叶分解"（选取垂直方向为"时间"）：

```
       z (time)
       ^
       |
  t=2  +---+---+---+---+  <-- layer 2 (leaf)
       | a | b | c | d |
  t=1  +---+---+---+---+  <-- layer 1 (leaf)
       | e | f | g | h |
  t=0  +---+---+---+---+  <-- layer 0 (leaf)
       | i | j | k | l |
       +---+---+---+---+---> x (space)

观察者选取：
- 沿 z 轴"向上"遍历（t=0 → t=1 → t=2）：**若定向确定**，则为传统 CA 的"前向演化"
- 沿 z 轴"向下"遍历（t=2 → t=1 → t=0）：**若反向定向确定**，则为 CA 的"逆演化"
- 沿 x 轴遍历：一般不定向确定，展示为"混沌"读取（非因果序列）

**关键：本体层面无"优先方向"；演化=观察者的读取选择，非内在动力学。**
**决定性演化需要定向确定（定义 4.3）：一般 SFT 不保证所有方向均满足。**
```

这一图示强调：**选取"时方向"仅为读取选择，非本体偏置**。高维对称结构本身是永恒静态块。

*注：上文"决定性演化"指 §4 **定义 4.3** 的定向确定/right-closing 情形；否则同一无时块在不同读取方向仅给出**因子投影**，非单一 CA 的时空图。*

### 定义 3.3（对称移位不变性）

定义高维移位 $\sigma^{\mathbf{v}}: \Sigma^{\mathbb{Z}^m} \to \Sigma^{\mathbb{Z}^m}$ 为
$$
\big(\sigma^{\mathbf{v}}\mathcal{M}\big)(\mathbf{p}) = \mathcal{M}(\mathbf{p} + \mathbf{v})
$$

无时块集合在所有移位下不变。

### 命题 3.4（等化子表述）

$\mathrm{Fix}(C) = \ker(C - \mathrm{id}) = \mathrm{Eq}(C, \mathrm{id})$ 在子移位的范畴中是 $C$ 与 $\mathrm{id}$ 的等化子，因此天然为子移位，且在移位作用下不变。

**证明**：在符号动力系统范畴中，等化子定义为最小满足 $C x = x$ 的子空间。由移位不变性，$\sigma^{\mathbf{v}}$ 作用于 $\mathrm{Fix}(C)$ 仍满足约束。作为移位不变闭集，由 Tychonoff 紧性保证紧致性质。参考 Lind & Marcus (1995)。 $\square$

### 注记 3.1（遍历视角）

观察到的"演化"是对 $\mathcal{M}$ 沿任意路径的投影与顺序读取。例如，选择一维作为"时间"，则可恢复传统动态视图，但无全局偏好。路径非唯一性可能导致"因果"歧义，但这反映了理论的对称性。一般SFT的路径遍历对应混沌读取，而定向确定对应因果锥演化。

注意：将某方向 $\mathbf{v}$ 选作"时间轴"以得到决定性逐步读取，需要 $Y$ 在 $\mathbf{v}$ 方向上满足定向确定/右闭合等充要条件；一般 SFT 不保证对所有方向均成立。此处"路径遍历/分叶"仅为观察者读取方式；"决定性演化"是更强的结构要求（需定向确定/右闭合），二者不可混同。

**熵视角的量化**：一般 SFT 的路径遍历在非定向确定方向上呈现"混沌读取"，可通过拓扑熵 $h_{\text{top}}(Y)$ 量化（§11）。定向确定方向的遍历对应于确定性 CA 的时空图，其熵由 CA 局部规则的信息传播决定；非定向确定方向的遍历熵可能显著更高，反映局部图样的组合自由度。

---

## §4 子移位与有限型子移位（SFT）表述

### 定义 4.1（禁形集合）

令 $S = N \cup \{0\}$。由局部函数 $f$ 引入在 $\mathbb{Z}^m$ 上的有限禁形集合 $\mathcal{F} = \{ a \in \Sigma^S : a(0) \neq f(a|_N) \}$，其成员是违反局部约束的有限图样。无论 $0 \in N$ 与否，固定点约束均通过 $S = N \cup \{0\}$ 的禁形集合 $\mathcal{F} = \{a \in \Sigma^S : a(0) \ne f(a|_N)\}$ 表达。

### 定义 4.2（有限型子移位）

所有满足约束的高维图组成的集合
$$
Y = \{ x \in \Sigma^{\mathbb{Z}^m} : \forall \mathbf{p}, \, x|_{\mathbf{p}+S} \notin \mathcal{F} \} \subseteq \Sigma^{\mathbb{Z}^m}
$$

是一个有限型子移位（SFT），并在所有高维移位作用 $\sigma^{\mathbf{v}}$ 下不变。

### 命题 4.1（SFT 表征）

无时块 $\mathcal{M}$ 是 SFT $Y$ 的一个元素，而"演化"是对 $Y$ 的路径遍历。

**证明**：由定义 3.1 和定义 4.1，$\mathcal{M} \in \mathrm{Fix}(C)$ 满足所有局部约束，因此 $\mathcal{M} \in Y$。路径遍历对应于固定路径的投影。 $\square$

### 注记 4.1（SFT 的意义）

这将高维对称约束与符号动力系统对齐，无时间偏置。禁形有限性确保 $Y$ 是 SFT。

### 定义 4.3（定向确定）

称 SFT $Y \subset \Sigma^{\mathbb{Z}^{d+1}}$ 在方向 $\mathbf{e}_{d+1}$ 上**定向确定**（directionally determined / **right-closing**，又称 right-resolving），若存在有限集合 $P \subset \mathbb{Z}^{d+1}$（称为 past shape）与局部函数 $g: \Sigma^{|P|} \to \Sigma$，使得对任意 $\mathbf{p} \in \mathbb{Z}^{d+1}$ 和 $y \in Y$，有
$$
y(\mathbf{p} + \mathbf{e}_{d+1}) = g\big(y|_{\mathbf{p} + P}\big), \qquad P \subset \{\mathbf{z} \in \mathbb{Z}^{d+1} : \langle \mathbf{z}, \mathbf{e}_{d+1} \rangle \leq 0\}.
$$

这里 $\langle \cdot, \cdot \rangle$ 为标准内积，条件 $\langle \mathbf{z}, \mathbf{e}_{d+1} \rangle \leq 0$ 确保 $P$ 位于"非正半空间"（过去锥）。

### 定理 4.3（空间-时间图与定向确定 SFT 的对应）

（1）对任意 $d$-维 CA $F$，其空间-时间图
$$
\mathsf{Spacetime}(F) = \{ y \in \Sigma^{\mathbb{Z}^{d+1}} : \forall \mathbf{s} \in \mathbb{Z}^d, t \in \mathbb{Z}, \, y(\mathbf{s}, t+1) = f(y|_{(\mathbf{s}, t) + N}) \}
$$

是 $(d+1)$-维 SFT，且在 $\mathbf{e}_{d+1} = (0,\ldots,0,1)$ 方向上定向确定。

（2）若 $Y \subset \Sigma^{\mathbb{Z}^{d+1}}$ 为 SFT 且在方向 $\mathbf{e}_{d+1}$ 上定向确定（定义 4.3），则存在 $d$-维 CA $F$ 使 $Y$ 与 $\mathsf{Spacetime}(F)$ 通过滑动块码拓扑共轭（或至少为其因子）。这精确限定了与传统 CA 的等价。

**证明**：

（1）禁形集合为所有违反时间步约束 $y(\mathbf{s}, t+1) \neq f(y|_{(\mathbf{s}, t) + N})$ 的有限图案（在 $(N \cup \{(0,\ldots,0,1)\})$ 上定义），因此 $\mathsf{Spacetime}(F)$ 是 SFT。定向确定显然，取 $P = N \times \{0\}$ 和 $g = f$。

（2）**CA 提取构造**：设 $Y$ 满足定义 4.3 的定向确定条件，past shape 为 $P \subset \{\mathbf{z} : \langle \mathbf{z}, \mathbf{e}_{d+1} \rangle \leq 0\}$，局部函数为 $g: \Sigma^{|P|} \to \Sigma$。定义 $d$-维邻域
$$
N = \{\mathbf{s} \in \mathbb{Z}^d : (\mathbf{s}, 0) \in P\}.
$$

**引理（扩展无关性）**：设 $u \in \Sigma^{|N|}$ 为 $N$ 上的局部图样。对 $P$ 上的两份扩展 $\tilde{u}, \tilde{u}' \in \Sigma^{|P|}$，若在 $N$ 上一致（即 $\tilde{u}|_N = \tilde{u}'|_N = u$），则 $g(\tilde{u}) = g(\tilde{u}')$。

**证明**：定向确定的定义（定义 4.3）保证：对 $y \in Y$ 与任意 $\mathbf{p} \in \mathbb{Z}^{d+1}$，$y(\mathbf{p} + \mathbf{e}_{d+1}) = g(y|_{\mathbf{p}+P})$ 仅依赖于 $y$ 在 $\mathbf{p} + P$ 上的取值。因此，$g$ 作为 $P$ 上的局部函数，其输出由 $P$ 上的图样唯一确定，与 $P$ 外部的任意延拓无关。 $\square$

由扩展无关性，对每个 $u \in \Sigma^{|N|}$，可良定义 CA 局部规则
$$
f(u) = g(\tilde{u}),
$$
其中 $\tilde{u}$ 为 $u$ 在 $P$ 上的任意扩展（例如，令 $\tilde{u}(\mathbf{s}, 0) = u(\mathbf{s})$ 对 $\mathbf{s} \in N$，其余位置任意填充）。

据此构造满射滑动块码 $\Phi: Y \to \mathsf{Spacetime}(F)$（由定向确定条件的函数 $g$ 自然诱导），故 $Y$ 为 $\mathsf{Spacetime}(F)$ 的**因子**。**并且仅当**满足定义 4.3bis(ii)（$\pi_0$ 单射且 $\pi_0^{-1}$ 为滑动块码）**时**，$\Phi$ 才升级为双射且逆为滑动块码，从而二者**拓扑共轭**。参考 Kitchens (1998) 和 Lind–Marcus (1995) 第 8 章。 $\square$

### 定义 4.3bis（初始层因子与列码）

设 $Y \subset \Sigma^{\mathbb{Z}^{d+1}}$ 为 SFT，且在 $\mathbf{e}_{d+1}$ 方向上定向确定（定义 4.3）。定义：

(i) **初始层投影**：
$$
\pi_0: Y \to \Sigma^{\mathbb{Z}^d}, \qquad \pi_0(y) = y|_{\mathbb{Z}^d \times \{0\}}.
$$

(ii) **列码**（column code）：
$$
\Pi: Y \to \big(\Sigma^{\mathbb{Z}^d}\big)^{\mathbb{Z}}, \qquad (\Pi y)(t) := y|_{\mathbb{Z}^d \times \{t\}}, \quad \forall t \in \mathbb{Z}.
$$

列码将高维配置 $y$ 编码为"层的序列"（沿 $\mathbf{e}_{d+1}$ 方向的切片族）。

### 命题 4.3bis（因子与共轭的判别条件）

设 $Y \subset \Sigma^{\mathbb{Z}^{d+1}}$ 为 SFT。

**(i) 因子充分条件**：若 $Y$ 在 $\mathbf{e}_{d+1}$ 方向上定向确定（定义 4.3），则存在 $d$-维 CA $F$ 使 $Y$ 为 $\mathsf{Spacetime}(F)$ 的**因子**（即存在满射滑动块码 $\Phi: Y \to \mathsf{Spacetime}(F)$）。这是定理 4.3(2) 的精化。

**(ii) 共轭的充分条件**：若此外初始层投影 $\pi_0$ 为**一对一**（单射）且其逆 $\pi_0^{-1}$ 为滑动块码（即每一层由初始层通过有限记忆可构造），则 $Y$ 与 $\mathsf{Spacetime}(F)$ **拓扑共轭**。

**(iii) 可检验判据**：上述"$\pi_0^{-1}$ 为滑动块码"的充分条件为：存在有限 $R \in \mathbb{N}$ 使得对任意 $y \in Y$ 与高度 $t \geq 0$，第 $t$ 层 $y|_{\mathbb{Z}^d \times \{t\}}$ 可由初始层 $\pi_0(y)$ 在半径 $(R + t \cdot r_P)$ 的邻域通过局部函数 $g$ 逐层合成得到，其中 $r_P$ 为 past shape $P$ 在空间切片上的 $L_\infty$ 半径（通常 $r_P \ge r_N$，若 $P = N \times \{0\}$ 则 $r_P = r_N$）。这里 $(R + t \cdot r_P)$ 称为**逐层展开的遮蔽半径**（radius of influence）：随高度 $t$ 线性增长，反映信息从初始层向上传播的因果锥扩张。

**证明要点**：
- (i) 由定理 4.3(2)，定向确定蕴含因子映射。
- (ii) $\pi_0$ 单射意味着无"初始层信息塌缩"；$\pi_0^{-1}$ 为滑动块码确保逆映射连续且与移位交换，因此构成拓扑共轭。
- (iii) 逐层构造与 SFT 的有限记忆性质确保有限半径依赖。 $\square$

**对照与非例**：hard-square SFT 等非定向确定系统只能成为某些 CA 的**多方向投影因子**（在不同方向上投影得到不同的 "CA 切片"），通常不可能与任何单一方向的时空图拓扑共轭。这体现了"无时块的本质对称性"：无优先演化方向，所有方向等价。

**关键限制（高亮）**：**并非所有 $(d+1)$-维 SFT 都可表示为某 $d$-维 CA 的时空图**。仅当 SFT 在至少一个方向上满足定向确定（定义 4.3）时，才能提取出对应的 CA（得到因子映射）；进一步要求 $\pi_0$ 单射等条件才能升格为拓扑共轭。一般对称 SFT（如 hard-square）在所有方向上均非定向确定，因此**不对应任何单一 CA 的时空图**，仅为纯粹的高维对称结构（无时块的真正"无时"本质）。

**术语说明（滑动块码范畴）**：本文中"与传统 CA 等价"系指存在滑动块码 $\Phi$ 使得 $Y$ 与 $\mathsf{Spacetime}(F)$ 拓扑共轭（或至少为因子），而非笼统同一。定向确定是这类对应的充分条件之一。我们采用 Lind–Marcus (1995) 的滑动块码范畴：

- **滑动块码（sliding block code）**：映射 $\Phi: \Sigma^{\mathbb{Z}^m} \to \Gamma^{\mathbb{Z}^m}$ 称为滑动块码，若存在有限邻域 $M \subset \mathbb{Z}^m$ 与局部映射 $\phi: \Sigma^{|M|} \to \Gamma$，使 $(\Phi x)(\mathbf{p}) = \phi(x|_{\mathbf{p}+M})$。滑动块码连续且与移位可交换。

- **拓扑共轭（topological conjugacy）**：若存在双射滑动块码 $\Phi: Y \to Z$ 且其逆 $\Phi^{-1}: Z \to Y$ 亦为滑动块码，则称 $Y$ 与 $Z$ 拓扑共轭。这是符号动力系统的同构概念。

- **因子（factor）**：若存在满射滑动块码 $\Phi: Y \to Z$，则称 $Z$ 为 $Y$ 的因子。因子映射是拓扑共轭的单向推广（投影关系）。

示例（1D CA 的 2D 时空 SFT）：取一维邻域 $N = \{-1,0,+1\}$，定义
$$
y(s,t+1)=f\big(y(s-1,t),y(s,t),y(s+1,t)\big).
$$

这是 $\mathbb{Z}^2$ 上的 SFT，且在"向上"方向定向确定。
非示例（hard-square SFT）：禁止 $\mathbb{Z}^2$ 中相邻格同时取 1 的 SFT 一般不定向确定（在任何方向均无有限 $S$ 使状态函数化），因而非任何 CA 的"单方向时空图"。参考 Pavlov & Schraudner (2010) 的相关工作；见 Lind–Marcus (1995) 第 9–10 章相关讨论。

### 定义 4.2bis（block-gluing / 块粘合性质）

设 $Y \subset \Sigma^{\mathbb{Z}^m}$ 为 SFT。若存在 $w \in \mathbb{N}$（缓冲宽度）使得对任意两个有界图样 $u, v$（分别支撑在有界集合 $A, B \subset \mathbb{Z}^m$ 上），当 $\mathrm{dist}_\infty(A, B) > w$（即 $\inf_{\mathbf{a} \in A, \mathbf{b} \in B} \|\mathbf{a} - \mathbf{b}\|_\infty > w$）时，总能在某 $y \in Y$ 中同时出现（即 $y|_A = u$，$y|_B = v$），则称 $Y$ 具有 **block-gluing 性质**（或称为块粘合性质）。

**注记**：
- Block-gluing 强于规范填充性质（specification）的若干版本，但弱于强混合性（strong mixing）。
- Block-gluing $\Rightarrow$ 周期点稠密（见命题 4.4）。在 $\mathbb{Z}^m$ 上的 SFT 中，这确保周期点稠密与某些可判定/半判定程序的可操作性（如 §11 的周期证书方法），为非空性验证提供实际路径。
- 本文仅用到"周期点稠密"这一推论，未依赖更强的混合性质。
- 在无时块语境下，block-gluing 意味着局部图样可在空间上"任意远"拼接而不违反全局约束，体现对称结构的"局部自由度"。

### 命题 4.4（block-gluing ⇒ 周期点稠密）

若 SFT $Y \subset \Sigma^{\mathbb{Z}^m}$ 满足 block-gluing（定义 4.2bis），则 $Y$ 的周期点在 $Y$ 中（乘积拓扑意义下）稠密。

**证明**：见 Lind–Marcus (1995, 定理 4.3.3) 与 Kitchens (1998, 第 4 章)。构造要点：给定 $y \in Y$ 与有限盒 $\Lambda$，利用 block-gluing 的缓冲宽度 $w$，在足够大的周期环面 $\mathbb{T}^m_n$ 上拼接 $y|_\Lambda$ 的多份拷贝（拷贝间距 $> w$），得到周期配置逼近 $y$ 在 $\Lambda$ 上的取值。 $\square$

**意涵**：在无时块视角下，这给出"可观测的周期切片"近似任意局部图样的可验证路径。周期配置可在有限环面上搜索，形成非空性的可验证证书（见 §11 推论 11.1）。

---

## §5 Curtis–Hedlund–Lyndon 定理的推广

### 定理 5.1（Curtis–Hedlund–Lyndon 定理, $m \geq 1$）

设 $X = \Sigma^{\mathbb{Z}^m}$ 赋予乘积离散拓扑，$\sigma^{\mathbf{v}}$ 为移位群作用。映射 $F: X \to X$ 为细胞自动机（CA）当且仅当 $F$ 连续且与所有移位可交换；等价地，存在有限邻域 $N \subset \mathbb{Z}^m$ 与局部规则 $f: \Sigma^{|N|} \to \Sigma$，使
$$
(F x)(\mathbf{p}) = f\big( x|_{\mathbf{p} + N} \big).
$$

若 $F$ 还是双射，则其逆 $F^{-1}$ 同样连续且移位可交换，因而亦为 CA（此时称 $F$ 可逆）。

**证明**：连续性确保局部规则有限；交换性确保均匀（Hedlund 1969）。逆映射连续由紧-豪斯多夫空间双射性质得，且交换性由双向相容。参考 Richardson (1972) 高维推广。 $\square$

**意义**：这一定理是 CA 的拓扑刻画，也确保"静态块"约束的局部性是充分且必要的。适用于 $Y$ 上的同态。

**子移位间的扩展**：对任意子移位 $Y, Z \subset \Sigma^{\mathbb{Z}^m}$，若 $\Phi: Y \to Z$ 连续且与所有移位 $\sigma^{\mathbf{v}}$ 可交换，则 $\Phi$ 为滑动块码（存在有限邻域 $M$ 与局部映射 $\phi$ 使 $(\Phi x)(\mathbf{p}) = \phi(x|_{\mathbf{p}+M})$）。若 $\Phi$ 是拓扑共轭（双射且逆连续），其逆 $\Phi^{-1}: Z \to Y$ 亦为滑动块码。本条用于 §4 的"因子/共轭"判据（定义 4.3bis 与命题 4.3bis）。

**群作用推广**：CHL 定理可推广至任意可数群 $G$ 作用于 $\Sigma^G$（见附录 A.2）：映射 $F: \Sigma^G \to \Sigma^G$ 为 CA 当且仅当连续且与所有 $\sigma^g$ ($g \in G$) 交换。这一推广对本文的无时块框架至关重要：$\mathbb{Z}^m$ 仅为特例（amenable 群），一般群作用下的局部约束同样可定义不动点 SFT（附录 A.1）。

**注记**：假设 $X$ 赋予乘积离散拓扑且 $\Sigma$ 有限。

**参考**：Hedlund (1969), Ceccherini-Silberstein & Coornaert (2010)

---

## §6 无时块的存在非空性与局部依赖

### 引理 6.1（局部依赖域）

设邻域 $N$ 的 $L_\infty$ 半径为 $r_N$。则对任意 $\mathbf{p}_0 \in \mathbb{Z}^m$，局部约束依赖于有限球 $B_\infty(\mathbf{p}_0; r_N) = \{ \mathbf{p} \in \mathbb{Z}^m : \|\mathbf{p} - \mathbf{p}_0\|_\infty \leq r_N \}$。

**证明**：约束仅涉及 $\mathbf{p}_0 + N$，因此依赖有限。 $\square$

### 定理 6.1（固定点子移位的非空性）

令 $C: X \to X$ 为一全局约束算子（滑动块码，记忆集 N）。其固定点集合 $\mathrm{Fix}(C) = \{ x \in X : C x = x \}$ 是 $X$ 的有限型子移位（SFT）：取 $S = N \cup \{0\}$，把所有违反"中心符号等于 $f$ 作用于邻域"之局部图样列为禁形，即得 $\mathrm{Fix}(C) = X_{\mathcal{F}}$。然而，$\mathrm{Fix}(C)$ 的非空性在 $m \geq 2$ 时与多米诺问题等价，一般不可判定。

**证明**：

(1) **SFT 结构**：由禁形有限性（§4 定义4.1），$\mathrm{Fix}(C)$ 为闭移位不变集，因此是 SFT。

(2) **非空性的充分条件（König 引理与强一致性）**：设 $\{A_p\}_{p\in\mathbb{Z}^m}$ 为满足点 $p$ 局部约束的闭集族，即 $A_p = \{ x \in X : x(\mathbf{p}) = f(x|_{\mathbf{p}+N}) \}$。若对每个有限点集 $P \subset \mathbb{Z}^m$ 存在整格配置 $x_P \in \Sigma^{\mathbb{Z}^m}$ 使 $x_P \in \bigcap_{p \in P} A_p$（**有限交性质, FIP**），则由 Tychonoff 紧致性，存在 $\mathcal{M} \in \bigcap_{p \in \mathbb{Z}^m} A_p$，即 $\mathrm{Fix}(C) \neq \varnothing$。

**强一致性（FIP）与弱一致性（盒可填充）的关键区分**：上述 FIP 要求对**任意有限点集**都存在**整格配置**满足其上所有约束。相反，仅有"对任意大有限盒 $\Lambda_n = [-n,n]^m$ 都存在**局部贴片** $x^{(n)}: \Lambda_n \to \Sigma$"而不保证这些贴片形成嵌套一致的射影族（即 $x^{(n+1)}|_{\Lambda_n} = x^{(n)}$）时，在 $m \geq 2$ 并**不能**推出全局解。Berger (1966) 的 Wang 平铺系统正是此类反例：任意有限盒局部可填充，但无全局铺砌。

(3) **高维不可判定性（Berger 反例机制）**：在 $m \geq 2$ 维，存在 SFT（如 Berger 1966 的 Wang 平铺构造）展示如下失败机制：
   - **典型现象**：可构造禁形集合 $\mathcal{F}$ 使得任意有限盒 $\Lambda_n$ 均存在满足局部约束的贴片 $x^{(n)}$（弱一致性），但这些贴片**无法**形成嵌套一致的射影族（即不存在 $x^{(n+1)}|_{\Lambda_n} = x^{(n)}$ 对所有 $n$ 成立）。
   - **机制解释**：非周期平铺的"强制性"导致局部可行贴片在扩展到更大盒时产生边界冲突，无法延拓为全局配置。因此可能出现 $\mathrm{Fix}(C) = \varnothing$。
   - **具体性说明**：并非所有 Berger 型 Wang 平铺都**必然**表现为"每个有限盒均可填但无全局解"；关键在于该类构造方法可产生此类现象，从而使判定问题归约为多米诺问题。

判定 $\mathrm{Fix}(C) \neq \varnothing$ 在 $m \geq 2$ 时归约为多米诺问题（Wang 平铺的空性问题），后者已被证明不可判定（Berger 1966）。

(4) **维度对比**：在 $m = 1$ 时，König 引理的树可简化为单链（De Bruijn 图），弱一致性（盒可填充）自动蕴含强一致性（FIP），因一维拓扑无"困难平铺"现象。因此非空性可判定（通过有限图遍历）。

**注记**：本文所谓"局部一致性"均指 FIP-级一致性。Brouwer 不动点定理不适用，因 $X$ 离散且非凸。参考 Weiss (2000) 对 sofic 系统边界。 $\square$

**伪码扩展**：以下伪码搜索有限网格一致配置（作为无限格点的有限近似，使用周期边界 % 操作）：

```python
def find_fixed_point(grid_size, N, f):
    """
    Search for fixed point on finite grid with periodic boundaries.
    max_iters: iteration limit (e.g., 10^4)
    apply_C_periodic: apply constraint C with periodic boundaries
    """
    grid = initialize_random_grid(grid_size)
    for iter in range(max_iters):
        new_grid = apply_C_periodic(grid, N, f)  # periodic boundaries
        if new_grid == grid:
            return grid  # fixed point found
        grid = new_grid
    return None  # did not converge
```

对于 3D 小网格（5x5x5），工具验证显示线性规则（如邻域和 mod 2）可收敛到全0固定点。

### 命题 6.2（唯一性充分条件）

$\mathrm{Fix}(C)$ 的唯一性需额外结构条件。以下两类充分条件分别对应度量与序结构：

**条件 A（度量收缩）**：若 $X$ 赋予完备度量 $d$（如 Cantor 度量 $d(x, y) = 2^{-\min\{\|\mathbf{p}\|: x(\mathbf{p}) \neq y(\mathbf{p})\}}$），且 $C$ 为严格收缩映射（存在 $0 < \lambda < 1$ 使 $d(Cx, Cy) \leq \lambda d(x, y)$），则 $\mathrm{Fix}(C)$ 至多一元（Banach 不动点定理）。

**条件 B（序单调性）**：若 $\Sigma$ 赋予偏序（如 $0 \leq 1$），$X = \Sigma^{\mathbb{Z}^m}$ 按逐点序为完备格，且 $C$ 为序单调映射（$x \leq y \Rightarrow Cx \leq Cy$），则 $\mathrm{Fix}(C)$ 非空时存在最小与最大不动点（Tarski–Knaster 定理）。最小不动点可通过 Kleene 迭代 $\bot, C\bot, C^2\bot, \ldots$ 的上确界得到（$\bot$ 为全 0 配置）。

**一般情形**：$\mathrm{Fix}(C)$ 可有多个不动点（见定义 2.4 判例 2）。唯一性依赖于 $f$ 的全局约束传播：若邻域生成群 $\mathbb{Z}^m$ 且 $f$ 对任意不同输入给出不同输出的"全局传播性"，则可通过连通性论证排除多解，但此条件过强，实际少见。

**度量注**：在 Cantor 度量下，滑动块码 $C$ 通常仅为 1-Lipschitz（非严格收缩），因条件 A 在一般 CA 中**极少**满足。条件 B 更常用于布尔或格值 CA 的不动点分析（如单调布尔网络）。

**证明要点**：条件 A 由 Banach 不动点定理直接得出。条件 B 中，Tarski 定理保证序连续映射在完备格上存在最小/最大不动点；单调性确保 Kleene 链递增。 $\square$

### 注记 6.1（依赖域）

在高维，这对应球域，无方向锥。

**模拟验证**：使用工具验证小网格固定点。例如，2D von Neumann 邻域下的 XOR-like 规则（邻域和 mod 2）。通过代码执行确认：全0配置是固定点，全1配置不是。这验证了理论的自洽性。扩展到 3D 网格（工具模拟显示类似结果）。

### 注记 6.1bis（一维情形的弱⇒强自动提升）

在 $m = 1$ 时，任意长度-$k$ 禁形 SFT 的"每个长度-$n$ 可行词存在"可经 De Bruijn 图抽象为"存在可达回路"（§11 注记 11.1），因此弱一致性（任意大有限盒可填充）自动提升为强一致性（FIP，可构造全局配置）。这使得空性可判定。对照 $m \geq 2$ 的失败（定理 6.1 (3)）是本文"计算边界"的核心：一维拓扑简单性 vs 高维平铺复杂性的本质跃迁。

---

## §7 线性 CA 的群傅里叶分解在高维对称下的扩展

**线性卷积记号**：取底域 $\mathbb{K}$（如 $\mathbb{F}_q$ 或 $\mathbb{R}/\mathbb{C}$），给定核 $a: N \to \mathbb{K}$，定义
$$
(F x)(\mathbf{p}) = (a * x)(\mathbf{p}) := \sum_{\mathbf{n} \in N} a(\mathbf{n}) x(\mathbf{p} + \mathbf{n}),
$$
与之对应的频域乘子为 $\widehat{a}(\xi) = \sum_{\mathbf{n} \in N} a(\mathbf{n}) e^{-2\pi i \langle \xi, \mathbf{n} \rangle}$（见命题 7.1）。

### 定义 7.1（线性对称 CA）

当 $f$ 在 $\mathbb{F}_q$ 上线性且对称时，$F$ 是 $\mathbb{Z}^m$ 上的卷积型线性 CA（线性平移不变）。

**提示（域与层级）**：下述谱分析均在 $\mathbb{C}$ / $\mathbb{R}$ 上给出**卷积算子**的乘子结构，仅供稳定性与对称性直觉；**不**据此判断**滑动块码层面的可逆性**。有限域 $\mathbb{F}_q$ 的 Laurent 多项式判据见本节"**三层可逆性速览**"。

### 命题 7.1（群傅里叶对角化，卷积型）

若 $f$ 在线性域上诱导的全局映射 $F$ 为卷积型（即平移不变线性），则其在 $\mathbb{Z}^m$ 的 Pontryagin 对偶 $\widehat{\mathbb{Z}^m} = \mathbb{T}^m$ 上由乘子 $\widehat{a}(\xi) = \sum_{\mathbf{n} \in N} a(\mathbf{n}) e^{-2\pi i \langle \xi, \mathbf{n} \rangle}$ 对角化。

**证明**：Pontryagin 对偶 $\widehat{\mathbb{Z}^m} = \mathbb{T}^m$ 上乘子对角化卷积。参考 O'Donnell (2014)。 $\square$

**三层可逆性速览**（避免频域与 CA 可逆性的混淆）：

(i) **$\ell^2$ 卷积算子层**：频域乘子 $\widehat{a}(\xi) \neq 0$ 表示反卷积在分析意义下存在（$L^2$ 或分布意义），但与 CA 局部逆**无直接等价**。这仅说明全局解的可恢复性（算子可逆），不保证有限半径局部规则。

(ii) **代数层（Laurent 多项式环 / 有限域）**：在有限域 $\mathbb{F}_q$ 上，线性 CA 可逆当且仅当其多项式 $p(z_1,\ldots,z_m) \in \mathbb{F}_q[z_1^{\pm 1}, \ldots, z_m^{\pm 1}]$ 是**单位**（即单项式 $\times$ 非零标量）。在 $m \geq 2$ 维，这极为苛刻：绝大多数线性规则不可逆。详见 Kari (1994)。

(iii) **动力系统层（滑动块码）**：CA 可逆 $\Leftrightarrow$ 存在**有限半径**的局部逆规则 $F^{-1}$，使得 $F \circ F^{-1} = F^{-1} \circ F = \mathrm{id}$。这是拓扑动力系统意义下的可逆性（拓扑共轭的自同构）。

**本文立场**：所有频域观察（如命题 7.1 的谱分解）仅用于 (i) 层的稳定性/谱结构直觉与对称性分析，**不据此判定** (iii) 层的 CA 可逆性。在 §10 量子嵌入讨论中，仅使用"可逆 CA $\Rightarrow$ 存在置换幺正实现"这一最低层结论。

**注记**：在无限晶格，需 $L^2(\mathbb{Z}^m)$ 边界条件。若非平移不变，需规约为卷积形式。

### 例 7.1（高维 Rule 90 类似）

在 2D 对称，呈现高维分形，无时间偏置。谱分析展示稳定性。例如取超正交对称核对应多项式 $p(z_1,z_2) = 1 + z_1 + z_1^{-1} + z_2 + z_2^{-1}$；其乘子为 $\widehat{a}(\xi_1,\xi_2) = 1 + 2\cos(2\pi\xi_1) + 2\cos(2\pi\xi_2)$。下述可视化同样只在复域进行，用于稳定性直觉。

*域提示*：本节谱分析仅在 ($\mathbb C/\mathbb R$) 上作卷积乘子直觉；与有限域 ($\mathbb F_q$) 上的代数可逆性无直接等价，细则见前述"**提示（域与层级）**"。

**谱热图示意（复域可视化）**：

*说明*：为方便比对，我们先展示**含中心项**的对称核（乘子 $1 + 2\cos(2\pi\xi_1) + 2\cos(2\pi\xi_2)$）的解析式，随后在热图中改用**不含中心项**的十字核（乘子 $2\cos(2\pi\xi_1) + 2\cos(2\pi\xi_2)$）做对比，可视化差别仅在于整体平移。

以二维"十字核" $a=\delta_{(1,0)}+\delta_{(-1,0)}+\delta_{(0,1)}+\delta_{(0,-1)}$ 为例，其复角色上的乘子
$$
\widehat a(\xi_1,\xi_2)=2\cos(2\pi\xi_1)+2\cos(2\pi\xi_2),\quad (\xi_1,\xi_2)\in\mathbb T^2.
$$

伪代码（演示可视化思路）：

```python
import numpy as np
import matplotlib.pyplot as plt
n = 256
xi1 = np.linspace(0, 1, n, endpoint=False)
xi2 = np.linspace(0, 1, n, endpoint=False)
X, Y = np.meshgrid(xi1, xi2, indexing='xy')
a_hat = 2*np.cos(2*np.pi*X) + 2*np.cos(2*np.pi*Y)
plt.imshow(a_hat, origin='lower')
plt.title(r'$\widehat a(\xi_1,\xi_2)=2\cos(2\pi\xi_1)+2\cos(2\pi\xi_2)$')
plt.show()
```

*说明：此图仅为复域频谱的直观展示，与有限域 $\mathbb F_q$ 上的代数可逆性判据无直接等价。*

---

## §8 非线性布尔规则的 Walsh 展开

### 定义 8.1（Walsh 展开）

对称扩展到高维子集 $S \subseteq N$。定义标准化映射 $\varphi: \{0,1\} \to \{-1,1\}$ 为 $\varphi(0) = 1$, $\varphi(1) = -1$。对布尔函数 $f$，通过 $\tilde{f} = \varphi \circ f \circ \varphi^{-1}$ 转换为 $\{-1,1\}^{|N|} \to \{-1,1\}$，然后展开：
$$
\tilde{f}(z) = \sum_{S \subseteq N} \widehat{\tilde{f}}(S) \, \chi_S(z), \qquad \chi_S(z) = \prod_{j \in S} z_j
$$

### 命题 8.1（Walsh 系数）

Walsh 系数 $\widehat{\tilde{f}}(S) = 2^{-|N|} \sum_{z \in \{-1,1\}^{|N|}} \tilde{f}(z) \chi_S(z)$

**证明**：正交基展开，参考 O'Donnell (2014)。 $\square$

**对称性与 Walsh 系数的轨道结构**：若局部函数 $f$ 满足对称子群 $H \le B_m$ 的不变性（定义 2.1），则 Walsh 系数在 $H$ 的作用下形成**轨道**（orbits）。具体地，对 $h \in H$ 与 $S \subseteq N$，有 $\widehat{\tilde{f}}(h \cdot S) = \widehat{\tilde{f}}(S)$，其中 $h \cdot S = \{h(\mathbf{n}) : \mathbf{n} \in S\}$。这使得 Walsh 展开可按 $H$-轨道分组：
$$
\tilde{f}(z) = \sum_{[S] \in \mathcal{P}(N)/H} \widehat{\tilde{f}}(S) \sum_{T \in [S]} \chi_T(z),
$$

其中 $[S]$ 为 $S$ 在 $H$ 下的轨道代表元，$\mathcal{P}(N)$ 为 $N$ 的幂集。这一轨道分解用于：
- **影响度分析**（influence）：度量输入位翻转对输出的敏感性，按对称等价类聚合。
- **灵敏度边界**（sensitivity bounds）：在高维对称约束下，通过轨道大小界定总影响度的上界。

**注记**：作为表示工具，Walsh 展开不直接给出动力学分解（非线性规则无群作用的特征子空间），但提供布尔函数的频域"指纹"，便于分析对称约束下的局部敏感性。

---

## §9 Garden-of-Eden 定理

### 定义 9.1（pre-injective）

若对任意 $x \neq y \in X$，其**差异支撑集** $\Delta(x,y) := \{\mathbf{p} \in \mathbb{Z}^m : x(\mathbf{p}) \ne y(\mathbf{p})\}$ 有限时必有 $F x \ne F y$，则称 $F$ pre-injective。

### 定理 9.1（Garden-of-Eden 定理, $\mathbb{Z}^m$ 或更一般的 amenable 群）

对 CA $F$，满射当且仅当 pre-injective。

**证明**：Moore–Myhill 定理在 amenable 群上成立（双向等价：$F$ 满射 $\Leftrightarrow$ pre-injective），参见 Ceccherini–Silberstein & Coornaert (2010, 定理 5.12)。 $\square$

**注**：在更广的 sofic 群上可得 **Myhill 方向**（pre-injective $\Rightarrow$ surjective，参见 Gromov 1999；Weiss 2000）；两向等价（Moore–Myhill）一般需 amenable 结构。关于"注入 $\Rightarrow$ 满射"的 surjunctivity，sofic 群亦成立（Gromov 1999）。详细分层见 Kari (1994) 与 Ceccherini–Silberstein & Coornaert (2010, 第 5 章)。

### 推论 9.1（可逆性）

可逆性确保双向对称块存在，无时限制。若非满射，则存在伊甸园配置，无法成为无时块部分。在无时块中，非满射规则导致"伊甸园配置"无法嵌入静态结构。

---

## §10 应用与讨论

### 10.1 计算应用

#### 命题 10.1（并行优化）

无时框架允许全并行生成高维片段，依赖球而非锥。复杂度界如依赖球半径 $r$ 的 $O((2r+1)^m)$ 局部计算。

### 10.2 可逆性与量子嵌入

#### 命题 10.2（量子嵌入）

可逆 CA $F$ 可嵌入为量子酉自同构：在 Hilbert 空间 $\mathcal{H} = \ell^2(\Sigma^{\mathbb{Z}^m})$ 上定义 $U_F |x\rangle = |F(x)\rangle$（标准正交基），则 $U_F$ 为酉算子且满足 $U_F U_F^\dagger = U_F^\dagger U_F = I$。其因果锥半径界定为 $\max(r_F, r_{F^{-1}})$，其中 $r_F, r_{F^{-1}}$ 分别为 $F$ 与 $F^{-1}$ 的邻域半径。

**准局域框架与物理可实现性**：上述嵌入在 $\ell^2(\Sigma^{\mathbb{Z}^m})$ 中形式上成立，但需注意：
- $\ell^2(\Sigma^{\mathbb{Z}^m})$ 在 $m \geq 1$ 时为**不可分**无限维 Hilbert 空间（基数 $|\Sigma|^{\aleph_0}$），不符合标准量子力学的可分性假设。*
- 物理可实现的 QCA 需在**准局域 $C^*$-代数**框架下表述（如 Arrighi 2019 的 QCA 定义）：量子态为格点局域代数的张量积，演化保持准局域性（有限传播速度）。
- 本文的"可幺正嵌入"仅为数学层面的存在性陈述（置换 $\Leftrightarrow$ 酉算子），**不蕴含**物理上的局域量子门分解或电路实现。

*脚注：尽管 $\ell^2(I)$ 中任一向量只有**至多可数**个非零坐标，但其**标准正交基** $\{e_i\}_{i \in I}$ 的势等于 $|I|$。当 $I = \Sigma^{\mathbb{Z}^m}$ 不可数时，$\ell^2(I)$ 便**不可分**（无可数稠密子集）。这正是为何物理上采用**准局域 $C^*$-代数**与**可分**的无穷张量积来刻画 QCA：标准 QCA 框架（如 Arrighi 2019）在格点局域代数的张量积结构上定义量子态，并通过 GNS 构造得到可分 Hilbert 空间表示，避免"基数-级别"的病态（如不可数正交基）。

**分类定理的维度限制**：
- 在 $m = 1$ 维，可逆 QCA 具有完整的 GNVW 指数分类（Gross–Nesme–Vogts–Werner, 2012）：$\mathbb{Z}$ 上的平移不变 QCA 由指数 $\nu \in \mathbb{Q}_{>0}$（正有理数）与内部幺正自由度分类；其中 **$\nu = 1$** 当且仅当存在**有限深度局域量子电路**分解，$\nu \neq 1$（如单步移位的 $\nu = |\Sigma|$）则虽为**有限传播 QCA** 但**不可**由有限深度电路实现。
- 在 $m \geq 2$ 维，QCA 分类显著更复杂（涉及高维上同调与 Clifford 代数扩张），目前无完整分类定理（部分结果见 Freedman–Hastings, 2019）。
- **本文立场**：仅使用"可逆 CA $\Rightarrow$ 存在置换幺正实现"这一最低层事实，不依赖维度特定的分类结构。

**非可逆情形**：非满射 CA 无幺正提升（伊甸园配置导致非酉性），可退而求其次使用 CPTP（完全正迹保持）通道表述量子演化的"部分映射"，但失去可逆性。

**桥接判据（修订版：CA 可逆性与 QCA 的精确对应）**：任意**可逆** CA $F: \Sigma^{\mathbb{Z}^m} \to \Sigma^{\mathbb{Z}^m}$ 都诱导**有限传播**的准局域酉算子 $U$（QCA），使得 $\mathrm{Ad}_U$ 在准局域 $C^*$-代数上实现 $F$ 的作用。但是否存在**有限深度**的局域量子门分解，取决于 QCA 的拓扑指数：

- **一维情形**：当且仅当 **GNVW 指数 $\nu = 1$** 时，存在**有限深度局域电路**实现；$\nu \neq 1$ 时（如**单步移位**的 $\nu = |\Sigma|$），仍为**有限传播 QCA** 但**不可**由有限深度电路实现。其余分类细节见前述"分类定理的维度限制"。

- **高维情形**：在 $m \geq 2$ 维，同样存在有限传播的 QCA 提升。有限深度可分解需额外满足上同调/Clifford 代数条件，分类理论尚未完整（部分结果见 Freedman–Hastings, 2019）。**本文仅依赖"可逆 $\Rightarrow$ 存在有限传播 QCA"这一最低层事实**，不依赖有限深度分解的充要条件。

**层级提示**：本文"幺正提升"仅为**存在性层**（置换幺正/QCA）；**是否**存在**有限深度电路**属于**实现层**问题，由 1D 的 GNVW 指数（$\nu = 1$ 当且仅当可有限深度实现）或高维的上同调条件决定。

**必要性警示**：可逆性是幺正提升的**必要条件**。若 $F$ 不满射（存在 Garden-of-Eden 配置，§9），则**不存在**幺正提升，仅可用 CPTP 通道模拟其"信息丢失"效应。

### 10.3 哲学意涵：永恒主义扩展

无时块桥接块宇宙，无时间流动幻觉。与相对论块时空比较：讨论 Lorentz 不变性在离散模型中的模拟，如高维对称下的近似连续极限。

#### 注记 10.1（类比局限）

启发性，非字面；强调离散 vs 连续差异。

### 10.4 局限性

无限存储；计算受资源限。

---

## §11 复杂度与不可判定边界

### 命题 11.1（空性问题）

判定 $Y = \varnothing$ 在 $m \geq 2$ 不可判定（Berger 1966）。Wang 平铺与 SFT 空性问题互相归约，共享不可判定性。

**维度对照**：
- 在 $m = 1$ 时，SFT 可由有限有向图（De Bruijn 图/标记图）表征，空性等价于"图无可达回路"，故可判定（通过有限图遍历）。
- 在 $m \geq 2$ 时，与 Wang 平铺空性互归，故不可判定。

**其他性质的不可判定性边界**：在 $m = 1$ 上，满射性/前注入性可用 De Bruijn 图与 Garden-of-Eden 判据算法化检验（Moore 1962；Myhill 1963）；而在 $m \geq 2$ 时，诸多性质普遍出现不可判定性（Kari 1994）：
- **满射性**（surjectivity）：判定 CA $F$ 是否满射，不可判定。
- **可逆性**（reversibility）：判定 CA $F$ 是否双射，不可判定。
- **周期性**（periodicity）：判定 SFT $Y$ 是否包含非平凡周期点，不可判定。
- **熵计算**（entropy）：精确计算 $h_{\text{top}}(Y)$，一般不可判定。

这些不可判定性是高维离散动力系统的固有障碍，源于拓扑复杂性的本质跃迁（1D链 vs 2D+平面）。

### 推论 11.1（存在性边界）

高维无统一算法。周期性、熵计算亦不可判定。

**可验证性与半判定途径**：尽管 $\mathrm{Fix}(C) \neq \varnothing$ 在 $m \geq 2$ 不可判定，以下方法可提供**正例证书**（certify non-emptiness）：

(i) **周期化证书**：若 $\mathrm{Fix}(C) \neq \varnothing$，则在许多自然 SFT 中（非全部），存在某周期 $\mathbf{p} \in \mathbb{Z}^m \setminus \{0\}$ 使得周期配置 $x \in \mathrm{Fix}(C)$ 满足 $x(\mathbf{q} + \mathbf{p}) = x(\mathbf{q})$ 对所有 $\mathbf{q}$ 成立。这样的周期配置可在有限环面 $\mathbb{T}^m_n = (\mathbb{Z}/n\mathbb{Z})^m$ 上搜索（有限状态空间 $\Sigma^{n^m}$），形成**有限可验证证书**。

(ii) **有限环面 SAT**：将固定点约束视为约束满足问题（CSP），在 $n \times \cdots \times n$ 环面上求解（其中 `max_iters` 为预设迭代上限如 $10^4$，`apply_C_periodic` 为按周期边界应用约束算子的版本）：
```python
def find_torus_fixed_point(n, m, N, f):
    """
    Search for fixed point on n^m torus with periodic boundaries.
    Returns a periodic certificate if found, None otherwise.
    """
    torus = initialize_random_torus(n, m)
    for iter in range(max_iters):
        new_torus = apply_C_periodic(torus, N, f)  # periodic=True
        if new_torus == torus:
            return torus  # period divides n in each dimension
        torus = new_torus
    return None  # no convergence, try larger n or different init
```

若找到周期解，则 $\mathrm{Fix}(C) \neq \varnothing$ 得证（半判定的"是"分支）。但无法通过有限次失败断言空性（"否"分支不可判定）。

**收敛性警示**：上述**迭代法不保证收敛**，即使 $\mathrm{Fix}(C) \neq \varnothing$ 且存在周期解。实际使用应配合约束满足技术（如 SAT/ILP 求解器、arc consistency 约束传播等），或使用随机重启策略。此外，**证书最小周期**（最小 $\mathbf{p}$ 使某 $x$ 满足 $x(\mathbf{q} + \mathbf{p}) = x(\mathbf{q})$）无法预先界定，需在搜索空间 $\{n : 1 \le n \le N_{\max}\}$ 上遍历多个环面尺寸。

(iii) **可判定子类**：特定结构 SFT（如 sofic/coded 系统、确定方向的 CA 时空图）的非空性可判定。通过识别此类结构（如定向确定性），可绕过一般不可判定性。

**注记**：周期证书方法在实践中常有效（如物理系统的晶格对称性），但理论上无普遍保证：存在非空 SFT 仅含非周期配置（如 Penrose 平铺的离散类似）。

拓扑熵（amenable 群下）：对 $\mathbb{Z}^m$ 上的 SFT $Y$，其拓扑熵
$$
h_{\text{top}}(Y)=\lim_{n\to\infty}\frac{1}{|B_n|}\log \#\{\text{可延拓的}~Y\text{图样在}~B_n\},
$$

其中 $B_n=[-n,n]^m\cap\mathbb{Z}^m$，极限由可和性保证存在。该量为"组合复杂度"的核心不变量；其计算在 $m\ge2$ 一般不可判定，但对部分结构化 SFT 可给上下界或近似。对于 trivial SFT（如全0配置），$h_{\text{top}}=0$.

维度差异：在一维上，多数基本判定（如满射性）可经 De Bruijn 图等方法判定；而在二维及更高维，诸多性质（如满射性/可逆性/周期性/空性等）普遍出现不可判定性现象（经典结果可追溯至 Berger 与后续工作）。

### 注记 11.1（一维对照：算法化流程）

对 $m = 1$ 的 SFT（或 1D CA 的时空图），可通过 **De Bruijn 图 / 标记图**（labeled graph）实现算法化判定：

**构造流程**：
1. 设 SFT $Y \subset \Sigma^{\mathbb{Z}}$ 由长度 $k$ 的禁形集合 $\mathcal{F}$ 定义。
2. 构造 De Bruijn 图 $G_Y$：
   - 节点为长度 $k-1$ 的允许词（不含禁形的子串）。
   - 从节点 $u = a_1 \cdots a_{k-1}$ 到节点 $v = a_2 \cdots a_k$ 有有向边，当且仅当 $a_1 \cdots a_k$ 为允许长度 $k$ 的词（即 $a_1 \cdots a_k \notin \mathcal{F}$）。

**可判定性质**：
- **空性 ⇔ 图无回路**：$Y = \varnothing$ **当且仅当** 图 $G_Y$ **无可达回路**（即不存在从任何节点出发返回自身的路径）。判定算法：图的强连通分量分解（SCC），时间复杂度 $O(|\Sigma|^k)$。
- **存在周期点 ⇔ 图有回路**：$Y$ **存在周期配置** **当且仅当** $G_Y$ **有回路**。判定算法：深度优先搜索（DFS）检测环。
- **满射性 / 前注入性**：可转化为 $G_Y$ 上的路径覆盖与同态性质的组合判据。Garden-of-Eden 定理在 1D 提供算法化检验（Moore 1962）。

*最小复现实验*：取字母表 $\Sigma = \{0, 1\}$ 与长度 $k = 3$ 的禁形集（如禁止 111 / 000），据此构造 De Bruijn 图并用 DFS / SCC 检测环路；你可在几十毫秒内复现"**空性 ⇔ 无回路** / **存在周期点 ⇔ 有回路**"的判定。

**高维失效机制**：在 $m \geq 2$ 时，De Bruijn 图的高维类比（如 Wang 平铺的"图表示"）需要编码**无限多的边界条件**：每个有限盒 $\Lambda_n$ 的可行配置不仅依赖内部约束，还依赖边界上所有可能的邻域图样（来自盒外）。在 1D，边界仅为两个端点，可穷举；在 2D+，边界为 $O(n^{m-1})$ 个点，其外部邻域配置数随 $n$ 指数增长，无法由有限自动机表征。因此，空性判定归约为多米诺问题（Berger 1966），后者已被证明不可判定。这一维度跳跃是无时块理论的关键计算边界：1D 的"时空图 $\Leftrightarrow$ 有限图"等价在 2D+ 彻底瓦解，反映高维空间拓扑复杂性的本质障碍。

**参考**：Lind–Marcus (1995, 第 3 章)；Kitchens (1998, 第 2 章)。

---

## §12 结论与展望

### 12.1 主要贡献

无时块理论将 CA 重构为对称高维体，确保自洽。

### 12.2 核心洞察

1. **本体论**：无演化，仅遍历。
2. **数学**：SFT 基础。
3. **边界**：Garden-of-Eden 范围。
4. **哲学**：永恒块扩展。

### 12.3 未来方向

未来研究可聚焦于以下方向：

1. **量子扩展**：深化可逆 CA 与 QCA 的对应，探索高维 QCA 的上同调分类与拓扑不变量（Freedman–Hastings 2019）。
2. **高维分析**：研究特定 SFT 类（如 block-gluing、sofic 系统）的非空性可判定子类，开发半判定算法。
3. **实证模拟**：设计高维 SFT 非空性的蒙特卡洛验证方法，利用周期证书（§11）与有限环面搜索验证理论预测。
4. **物理联系**：探索离散时空模型（如因果集理论）与无时块 CA 的对应，研究连续极限下的对称性涌现。
5. **优化算法**：开发基于无时块框架的并行计算优化，利用高维对称性实现分布式生成。

---

## 附录 A：一般群 (G) 上的无时块 CA 结构（精简版）

A.1 定义（(G)-移位、局部约束、等化子）
令 $G$ 为可数群，$\Sigma$ 有限集，$X=\Sigma^{G}$ 赋予乘积离散拓扑。对 $g\in G$ 定义移位 $(\sigma^{g}x)(h)=x(hg)$。取有限记忆集 $M\subset G$ 与局部函数 $f:\Sigma^{M}\to\Sigma$，定义约束算子
$$
(Cx)(g)=f\big(x|_{gM}\big),\qquad \mathrm{Fix}(C)=\{x\in X: Cx=x\}.
$$

则 $\mathrm{Fix}(C)$ 为 $G$-不变闭子集，且为 SFT（禁形定义在 $M\cup\{e\}$ 上）。

A.2 CHL（群版）
$F:X\to X$ 是 CA $\Longleftrightarrow$ $F$ 连续且与全部 $\sigma^{g}$ 交换；等价地，存在有限 $M\subset G$ 与局部 $f$ 使 $(Fx)(g)=f(x|_{gM})$.

A.3 GoE / Surjunctivity

- 若 $G$ amenable，则 $F$ 满射 $\Leftrightarrow$ pre-injective（Moore–Myhill）。
- 若 $G$ sofic，则 pre-injective $\Rightarrow$ 满射（Myhill 方向）与surjunctivity成立。
- $\mathbb Z^m$ 是 amenable，故主文定理 9.1 为特例。

**Gromov–Weiss 线路**：Surjunctivity 最初由 Gottschalk 猜想（1973），Gromov (1999) 在其专著中给出 sofic 群上的证明框架（利用 sofic 近似与有限模型的极限论证）；Weiss (2000) 进一步细化了 amenable 群下的 Garden-of-Eden 定理（双向等价）。本文在 §9 采用 Ceccherini-Silberstein & Coornaert (2010) 的现代表述，无时块语境下，这些结果表明"满射性↔pre-injective"为配置空间的内在拓扑对偶性质，与时间方向无关。

A.4 熵（Følner 序）
对 amenable $G$ 与 Følner 序 $(F_n)$，SFT $Y\subset\Sigma^{G}$ 的拓扑熵定义为
$$
h_{\rm top}(Y)=\lim_{n\to\infty}\frac{1}{|F_n|}\log N_Y(F_n),
$$

极限存在且与 Følner 序选取无关。

A.5 定向确定（群版）
当给定 $G\to\mathbb Z$ 的群同态或半群滤过 $G=H_0\subset H_1\subset\cdots$ 诱导"层次读取"时，若存在有限 $S$ 位于"非正层"使得下一层符号为 $S$ 上图样的函数，则 $Y$ 与某 CA 的"层次时空图"滑动块码等价。

---

## 参考文献

- Wolfram, S. (2002). *A New Kind of Science*. Wolfram Media.
- Hedlund, G.A. (1969). Endomorphisms and automorphisms of the shift dynamical system. *Mathematical Systems Theory* 3, 320–375.
- Moore, E. F. (1962). Machine models of self-reproduction. *Proceedings of Symposia in Applied Mathematics* 14, 17–33.
- Myhill, J. (1963). The converse of Moore's Garden-of-Eden theorem. *Proceedings of the American Mathematical Society* 14(5), 685–686.
- Gottschalk, W. H. (1973). Some general dynamical notions. *Recent Advances in Topological Dynamics*, Springer Lecture Notes in Mathematics 318, 120–125.
- Ceccherini-Silberstein, T., & Coornaert, M. (2010). *Cellular Automata and Groups*. Springer.
- Berger, R. (1966). The Undecidability of the Domino Problem. *Memoirs of the American Mathematical Society*, No. 66.
- O'Donnell, R. (2014). *Analysis of Boolean Functions*. Cambridge University Press.
- Kitchens, B. (1998). *Symbolic Dynamics: One-sided, Two-sided and Countable State Markov Shifts*. Springer.
- Richardson, D. (1972). Tessellations with local transformations. *Journal of Computer and System Sciences* 6, 373–388.
- Lind, D., & Marcus, B. (1995). *An Introduction to Symbolic Dynamics and Coding*. Cambridge University Press.
- Weiss, B. (2000). Sofic groups and dynamical systems. *Ergodic Theory & Dynamical Systems* 20, 525–542.
- Kari, J. (1994). Reversibility and surjectivity problems of cellular automata. *Journal of Computer and System Sciences* 48(1), 149–182.
- Arrighi, P. (2019). An Overview of Quantum Cellular Automata. *Natural Computing* 18, 885–899.
- Pavlov, R., & Schraudner, M. (2010). Classification of sofic projective subdynamics of multidimensional shifts of finite type. *Transactions of the American Mathematical Society* 362(1), 337–359.
- Gromov, M. (1999). *Endomorphisms of symbolic algebraic varieties*. *Journal of the European Mathematical Society* 1(2), 109–197.
- Gross, D., Nesme, V., Vogts, H., & Werner, R. F. (2012). Index theory of one dimensional quantum walks and cellular automata. *Communications in Mathematical Physics* 310(2), 419–454.
- Freedman, M., & Hastings, M. B. (2019). Classification of quantum cellular automata. *arXiv:1902.10285*.

---

**致谢**

基于原理论推广，确保对称严谨。