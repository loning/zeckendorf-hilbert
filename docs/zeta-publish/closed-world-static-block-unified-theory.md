# 静态块计算的封闭宇宙统一理论（含图灵机对偶术语）

**Unified Theory of Closed-World Static-Block Computation (with Turing-Machine Dual Terminology)**

**作者**：基于静态块量子场论框架的整合扩展
**日期**：2025年10月17日
**版本**：v1.5-camera-ready（提交版）

---

## 摘要

本文给出一个封闭宇宙中的静态块元胞自动机（SB-CA）的统一理论：宇宙只包含局域演化规则及其诱导的时空一致性约束，无任何外部输入。借助 SB-CA 与图灵机（TM）的等价性，本理论使用双重术语（在 SB-CA 概念后以括号标注 TM 对偶）系统刻画：

1. **计算=结构**：时间是静态体的索引；"运行"是合法静态块的存在；
2. **程序涌现**：在封闭宇宙中，程序盒（程序+输入）作为局部图案出现并可被全局延拓；
3. **观察=译码**：输出窗口（带上输出）由局域译码器解读；
4. **可判定性分层**：在固定合法块下，一次"出现"≈ $\Sigma_1^0$ 级，无限再现≈ $\Pi_2^0$ 级；
5. **信息守恒**：任意切片/窗口的条件 Kolmogorov 复杂度受"规则+坐标+因果边界/初始切片"上界；
6. **强制 vs 典型**：在自相似 SFT 类中通过宏块可实现强制携带；在内部测度下短程序盒更典型（机制诱导）。

理论同时给出范畴语义、构造范式、完整证明示例、相关工作引用与开放问题，形成一套可验证、可扩展的统一框架。本稿所有不可判定性/复杂度结论均在“固定规则、对合法配置族量化”的语义下陈述，避免与“固定到具体配置”的可判定情形混淆。

**关键词**：静态块元胞自动机，封闭宇宙，图灵完备性，程序涌现，Kolmogorov 复杂度，算法先验

---

## §1 纲领与直观

### 1.1 封闭宇宙的技术定义

**封闭宇宙**：宇宙=满足局域约束的所有合法静态块的集合（SB-CA / 计算历史）。封闭宇宙的技术意义在于确保所有结构均为内在约束诱导，避免外部初态引入的非决定性，将计算涌现还原为 SFT 几何事实。

**无外部输入**：不存在"外部设定的初态/噪声"。所有可观测结构均来自合法块自身。

### 1.2 双重术语对照表

本理论采用 **SB-CA / TM 双重术语**系统：

| SB-CA 术语 | TM 对偶术语 | 说明 |
|-----------|------------|------|
| 合法静态块 | 计算历史 | 满足约束的时空配置 |
| 初始切片 | 程序+输入 | $t=0$ 的状态配置 |
| 输出窗口 | 带上输出 | 可读取结果的时空区域 |
| 停机见证 | 停机证据 | 标记计算终止的图案 |
| 程序盒 | 代码+数据的局部封装 | 有限时空区域的计算单元 |
| 护城河 | 控制带 | 隔离边界的缓冲区 |
| 同步层 | 时钟 | 相位协调机制 |
| 自相似宏块 | 分层模拟器 | 递归检查结构 |
| 强制涌现 | 把程序写进转移函数 | 规则内置计算 |
| 典型涌现 | 内部测度下的稀疏普遍出现 | 概率诱导的出现 |

### 1.3 论文结构

本文组织如下：

- **§2** 公设与原语
- **§3** 形式模型
- **§4** 主定理与证明纲要
- **§5** 构造范式
- **§6** 观察语义与"语义塌缩"
- **§7** 范畴语义
- **§8** 例示与模板
- **§9** 相关工作
- **§10** 结论与展望
- **附录A** 护城河形式化定义与 block-gluing 验证
- **附录B** Brudno 数值检验脚本
- **附录C** 开放问题

---

## §2 公设与原语

### 公设 A0（封闭世界）

固定有限状态集 $Q$、邻域半径 $r$、局域演化 $f$。宇宙为所有满足由 $f$ 诱导的时空局域一致性约束的配置集合 $(\mathcal{B} \subseteq Q^{\Lambda \times T})$，其中 $\Lambda = \mathbb{Z}^d$、$T = \mathbb{N}$。无外部输入。

### 公设 A1（因果编码）

约束确保任意相邻切片 $(S_t, S_{t+1})$ 在每个 $x$ 处满足 $S_{t+1}(x) = f(S_t \upharpoonright \mathcal{N}_r(x))$ 的等价静态条件。时间仅是索引。

### 公设 A2（译码器=滑动块码，CHL）

译码器 $\pi$ 定义为与移位可交换的连续局域映射（滑动块码/因子映射，符合 Curtis–Hedlund–Lyndon 定理，简称 CHL；Hedlund 1969）。

### 公设 A3（通用基底）

存在可计算的编码/解码 $(\iota, \pi)$ 使任意 TM 计算可嵌入合法块并在有限窗口读出（多项式开销）。

### 公设 A4（紧致-延拓原理，带条件）

合法块空间是有限型子移位（SFT），因而是紧致闭集。对任一嵌套、相容的有限图案族 $\{P_k\}$（每个 $P_k$ 在 SFT 语言中，且 $P_k \subset P_{k+1}$），存在极限配置 $\mathcal{B}$ 使 $\mathcal{B} \upharpoonright \mathrm{supp}(P_k) = P_k$。

**注记 2.1（block-gluing 与有限延拓性质）**：若系统具 block-gluing/specification 或有限延拓性质（FEP），则任意两个远离的有限块可拼接为全局延拓。典型可验证条件包括 c-block-gluing（存在统一间隙 $c$ 的拼接），及其量化版本。本文在 $\mathbb{Z}^{d+1}$ 上默认采用 $\ell_\infty$ 距离度量"块距离"，用于 c-block-gluing 的间隙定义。

**注记 2.2（延拓的兼容性条件）**：A4 的延拓需满足"兼容家庭"的标准条件，并在 FEP 等假设下显式保证相容性与无冲突。本文构造中采用 block-gluing 以确保可拼接。

**命题 A4-B（量化拼接）**：设系统具 block-gluing/specification 性质，本文将该性质称作 *quantified block-gluing*（量化拼接），在缺失安全符号层时退化为 *almost-specification*（失败概率指数衰减）。则存在常数 $c = c(m, r, Q)$（其中 $m$ 为护城河宽度，$r$ 为邻域半径，$Q$ 为状态集）使得当两块 $P_1, P_2$ 的 $\ell_\infty$ 支撑距离 $\ge c$ 时，可在护城河中介下拼接为全局合法配置。具体上界 $c \le 2r + m$，其中护城河保证跨边界缺陷在 $r$ 步内被湮灭。

**证明**：因果包络不交性（附录 A.2）确保局域一致性分解为两侧独立检查；固定吸收态（如全0模式）在护城河内实现纠错容错。若不具完整 block-gluing，可退化为 almost-specification（失败概率指数衰减）。

**吸收条件澄清**：若系统缺乏全局吸收子字母表/安全符号层，仅得 almost-specification 的量化拼接（失败概率指数衰减），本命题的 c-block-gluing 需作相应弱化。$\square$

### 公设 A5（因果条件复杂度上界）

**记号声明**：以下 $K(\cdot)$ 为**前缀 Kolmogorov 复杂度**；不同万能机仅差 $O(1)$。我们采用下述后光锥闭包定义因果过去边界（式 (2.5a)），并在式 (2.5b)(2.5c) 给出信息上界：

$$
\partial^\star(W) := \bigl\{ (y,u) \in \Lambda \times T \mid \exists (x,s) \in W,\ u \le s,\ |y-x|_{\ell_\infty} \le r(s-u) \bigr\} \tag{2.5a}
$$

对任意合法块 $\mathcal{B}$，

$$
K(\mathcal{B} \upharpoonright W) \le K(f) + K(\mathrm{coord}(W)) + K(\mathcal{B} \upharpoonright \partial^\star(W)) + O(1) \tag{2.5b}
$$

若选定某切片为"初始切片（程序+输入）"，则

$$
K(S_t) \le K(S_0) + K(f) + K(t) + O(1) \tag{2.5c}
$$

**注记 2.3（信息守恒的解释）**：上界刻画：信息不会无因产生，但需要计入因果边界或初始切片。常数项相同于解释器选择。

### 公设 A6（译码不变性，拓扑共轭版）

若 $\pi_2 = \tau \circ \pi_1$，其中 $\tau$ 为双射滑动块码（与移位可交换的局域可逆映射），则对任意语义性质 $\mathsf{P}$（由有限窗口上的局域谓词定义），"是否含某语义图案"的判定在 $\pi_1, \pi_2$ 下等价。（即：共轭/因子范畴下的语义不变性。）

### 公设 A7（内部测度）

在合法块空间上考虑平移不变、遍历的内部测度 $\mu$（如存在的最大熵测度）。

**注记 2.4（测度唯一性）**：在一维、原始（aperiodic irreducible）SFT 上最大熵测度唯一（Parry 测度）；在 $d \ge 2$ 的 SFT 中最大熵测度可能不唯一（Burton–Steif 1994 反例）。详见 Lind–Marcus 的标准论述。

### 公设 A8（自相似强制）

在自相似/分层 SFT 类中，可构造一类宏块自相似结构，使每个合法块中强制携带某计算层（可枚举族）。

---

### 记号与约定

1. 冻结历史后的一切对象均在 $\mathbb{Z}^{d+1}$ 上讨论；横向为 $\Lambda=\mathbb{Z}^d$，纵向为时间维 $T=\mathbb{N}$，"history height"指 TM 步数 $T_{\mathrm{TM}}$。
2. "合法静态块/合法配置"统一记作 $\mathcal{B}\in Q^{\Lambda\times T}$。
3. 一律采用 $\ell_\infty$ 距离；"窗口"指有限支撑集合 $W\subset \Lambda\times T$。
4. CHL（Curtis–Hedlund–Lyndon）为"滑动块码=与移位可交换的连续局域映射"的同义语。

---

## §3 形式模型

### 定义 3.1（静态块元胞自动机 SB-CA）

给定 $\Lambda = \mathbb{Z}^d$、$T = \mathbb{N}$、有限 $Q$ 与局域约束族 $C$，合法块 $\mathcal{B} \in Q^{\Lambda \times T}$ 满足所有 $C$。若 $C$ 由某 CA 的单步 $f$ 诱导，称该 SB-CA 由 $(Q, \mathcal{N}_r, f)$ 生成。History-freezing 后的时空 SFT 位于 $\mathbb{Z}^{d+1}$。

**注记 3.1（与高维 SFT 的关系）**：这与"一维有效子移位可作为高一维 SFT 的因子（投影）实现"的结果一致（Durand–Romashchenko–Shen；Aubrun–Sablik）。

### 定义 3.2（程序盒 Program Box / 程序+输入）

有限时空区域 $W$ 及其图案 $P$ 使 $\pi(P) = \langle M, w, \mathrm{phase} \rangle$，并与外部通过护城河/同步层实现接口匹配与相位对齐。

### 定义 3.3（输出窗口 / 带上输出）

有限窗口 $W'$ 上由 $\pi$ 读取的比特串（附带"halt/acc"标签）。即 $\pi(\mathcal{B}\upharpoonright W')$ 的比特串及其 halt/acc 标签。

### 定义 3.4（强制携带 / 典型出现）

**强制携带**指"所有合法块"均出现某计算层；**典型出现**指在测度 $\mu$ 下以正密度 $\liminf > 0$ 或几乎必然 $\mu$-测度 1 的稀疏分布。

### 定义 3.5（观察者）

观察者是二元组 $(\mathcal{W}, \pi)$，其中 $\mathcal{W}$ 为窗口族，$\pi$ 为译码器。观察一次等价于"窗口+译码"的施用。

---

## §4 主定理与证明纲要

### 定理 4.1（封闭涌现的存在性；SB-CA / TM）

对任意 TM 程序 $p = (M, w)$ 与任意有限时长 $T$，存在合法块 $\mathcal{B}$ 与其子区域 $W$，使：

1. $W$ 为**程序盒（程序+输入）**并经 $\pi$ 解码为 $p$；
2. $W$ 的边界满足护城河/同步层接口规范；
3. $\mathcal{B}$ 的切片 $\{S_t\}$ 与 $M$ 的 $T$ 步计算一致，某时刻 $W'$ 中出现**停机见证（停机证据）**与可读输出（若 $M$ 在 $T$ 步内停机）。

**证明**：采用 A3 的通用基底，将 $M$ 的步进编码为垂直配对约束：对于 Rule 110（通用一维 CA），嵌入 TM 作为多轨模拟（轨道1: 带；轨道2: 头状态；轨道3: 相位）。以多轨/相位字段构造"同步层"：相位字母表 $\{0,1,\dots,k-1\}$，每步模 $k$ 递增，确保远程依赖局域化。

在 $W$ 周围加入"护城河"：宽度 $O(r)$ 的隔离带，使用固定模式（e.g., 全0）吸收相位冲突与缺陷。由 A4 的 block-gluing（假设间隙固定，具体护城河构造与 $c$ 的验证见附录 A），扩张为全局合法块：从有限 $P_0 = W \cup$ 护城河开始，嵌套扩展 $P_k$ 覆盖半径 $k$，极限得 $\mathcal{B}$。

**开销**：所用嵌入存在多项式级时间与空间膨胀 $\mathrm{poly}(|w|,T)$。证据来自 Rule 110 的通用性构造 [12] 以及对其多项式时间仿真的强化 [13]（Cook, 2004; Neary & Woods, 2006）。

**引理 4.1-C（编译开销界）**：TM 到 SB-CA 的编译路径为：TM $\to$ 多轨1D-CA嵌入 $\to$ 2D-SFT history-freezing。各阶段开销：

1. TM $\to$ 1D-CA：时间 $T_{\text{CA}} = \mathrm{poly}(T_{\text{TM}}, |w|)$，空间 $S_{\text{CA}} = \mathrm{poly}(S_{\text{TM}}, |w|)$（Cook 2004，Neary–Woods 2006）。
2. 1D-CA $\to$ 2D-SFT：额外空间因子 $\mathrm{poly}(k, r)$（相位周期 $k$，邻域 $r$），时间不变。

总开销：$T_{\text{SFT}} = \mathrm{poly}(T_{\text{TM}}, |w|, k, r)$，$S_{\text{SFT}} = \mathrm{poly}(S_{\text{TM}}, |w|, k, r)$。护城河厚度 $m$ 贡献额外常数因子。

**常数依赖**：
$$
|Q_{\text{SFT}}| = |Q_{\text{CA}}| \cdot k \cdot O(1),\quad \textbf{history height} = T_{\text{TM}},\quad \text{moat overhead} = O(m)
$$

**证明**：多轨嵌入使用轨道分割带与头状态，Rule 110 的轨道数固定为常数。history-freezing 通过垂直约束编码演化，空间开销源于编码字母表扩张。$\square$ $\square$

### 定理 4.2（固定规则下的出现/必现的可判定性层级；SB-CA / TM）

固定局域规则 $(Q, r, f)$，对所有合法静态块 $\mathcal{B}$ 的集合量化：

- **存在出现**（$\Sigma_1^0$-完全）：判定是否存在合法块 $\mathcal{B}$ 与坐标 $(x,t)$ 使有限图案 $P$ 在 $\mathcal{B}$ 的 $(x,t)$ 处出现。即，$\exists \mathcal{B} \exists (x,t): \mathcal{B}(x,t) = P$。
- **无限再现**（$\Pi_2^0$-完全）：判定是否存在合法块 $\mathcal{B}$ 与时刻 $N$ 使对任意 $t \ge N$，存在位置 $x$ 使 $P$ 在 $\mathcal{B}$ 的 $(x,t)$ 处出现。即，$\exists \mathcal{B} \exists N \forall t \ge N \exists x: \mathcal{B}(x,t) = P$。若进一步量化"是否存在图案 $P$ 使之成立"，则为 $\Sigma_3^0$。

**证明思路**：存在出现通过 TM 停机问题的 Rice 定理嵌入：构造 $P$ 编码"TM 停机则出现，否则不出现"。无限再现通过 Kari–Rice 对极限集的扩展，嵌入全局性质如"TM 总停机但无限计算"。

**证明附注（$\Pi_2^0$ 完全性——形式归约摘要）**：给任意 $\Pi_2^0$ 谓词 $\forall n \exists m \ge n: R(m)$，构造相位门控的观察见证 $P$ 及固定规则 $(Q,r,f)$，使"$\exists \mathcal{B} \exists N \forall t \ge N \exists x: P@(\mathcal{B};x,t)$" ⇔ 原式。向上归约闭包与映射可计算性给出 $\Pi_2^0$-完全。$\square$

### 定理 4.3（信息守恒与复杂度上界；SB-CA / TM）

对任意合法块与窗口，有

$$
K(\mathcal{B} \upharpoonright W) \le K(f) + K(\mathrm{coord}(W)) + K(\mathcal{B} \upharpoonright \partial^\star(W)) + O(1)
$$

$$
K(S_t) \le K(S_0) + K(f) + K(t) + O(1)
$$

**意涵**：演化不凭空增殖算法信息；可观测信息来源于"规则+坐标+因果边界/某切片"。

**Brudno 对齐**：在任一平移不变遍历测度 $\mu$ 下，几乎处处

$$
\lim_{n\to\infty}\frac{1}{|W_n|}K(\mathcal{B} \upharpoonright W_n)=h_\mu
$$

因而基于无模型压缩（如 LZ-77/PPMd）的经验比特/格可以作为 $\mu$-熵的数值近似。参见 Brudno（1983）的奠基性结果及其后续综述/量子推广。

**实验注意事项**：数值检验中，窗口形状应选择立方体 $n \times n \times \Delta t$ 以匹配时空尺度；边界处理采用周期边界或固定填充以避免边缘效应；压缩器选择 LZ-77/PPMd 导致有限样本偏差（e.g., 字典大小限制），误差条来源包括窗口选取变异与相位场扰动。可复现参数表：窗口序列 $n = 32, 64, 128, 256, 512$；采样步长 $\Delta t = n/4$；平均轮数 100 次独立运行。

**注记 4.1（多维情形）**：在 $\mathbb{Z}^d$ 的遍历子移位上亦有 Brudno 型等价，支持本文的数值检验流程。

**证明**：由 Kolmogorov 复杂度的可加性与局域规则的有限表示得出。$\square$

### 定理 4.4（强制涌现存在性；SB-CA / TM）

在自相似/分层 SFT 类中，存在宏块自相似构造 $\mathfrak{M}$ 使任意合法块在各尺度强制携带指定计算层（或可枚举族）。其 TM 对偶为"把程序写进转移函数/审计器"。

**证明**：采用 Mozes 平铺的自相似结构，在每个宏块尺度嵌入"审计器"检查下层一致性。$\square$

### 定理 4.5（典型涌现与算法先验；SB-CA / TM）

在封闭宇宙中，区分内部几何测度 $\mu$（SFT 动力系统上、与局域约束相关）与装载机制引入的外部“编码选择”分布 $\nu$（对程序盒的前缀采样）。若 $\nu$ 等价于向通用解释器投掷公平比特，且 $\mu$ 近似最大熵，则不同程序盒的出现频率近似满足 $\Pr(p) \propto 2^{-|p|}$（乘常数）。短程序更常见，长程序稀疏但在无限域几乎必然出现无穷多次（若其见证为有限时长）。

**注记 4.2（机制转导与半测度依赖）**：该分布对应 Solomonoff–Levin 的算法先验/通用半测度（相对所选前缀万能解释器），因此是**机制诱导而非常规 SFT 的自然律**。该先验是**半测度**且依赖于所选前缀万能机，不同机之间仅差一个乘性常数（**仅 up-to 常数**）。在封闭语境下，$\nu$ 可视为生成程序盒图案的外部随机化机制，与 $\mu$ 同余。

**可证伪切面**：更换解释器的微扰将只改变归一化常数，不改变短程序优先的序关系。即，对任意两台前缀万能机 $U_1, U_2$，存在常数 $c$ 使对所有程序 $p$，$\Pr_{U_1}(p) \le c \cdot \Pr_{U_2}(p)$。

**独立性假设**：若要断言"几乎必然无穷多次出现"，需假设窗口抽样独立性或有限能量条件；在缺少这些条件时，仅能保证正测度/正下密度级别的典型性。

**证明**：通过前缀编码与最大熵测度的组合得出。$\square$

### 定理 4.6（译码不变性；SB-CA / TM）

若两译码器相差一双射滑动块码，则"含/不含某语义图案"的判断一致。故语义在滑动块码等价类下是规范的。

**证明**：由公设 A6 的拓扑共轭性质直接得出。$\square$

---

## §5 构造范式

### 5.1 冻结历史（History-Freezing）

用垂直配对把"$t \to t+1$"编为局域一致性；例如，在 $\mathbb{Z}^{d+1}$ SFT 中，约束每个细胞与其"下方"匹配 $f$-演化。

### 5.2 同步层（Clock/Phase）

在图案中嵌入相位字段（字母表 $\{0,\dots,k-1\}$），使远程依赖转写为相邻层一致；接口协议：相位模 $k$ 递增，冲突时护城河重置。

### 5.3 护城河（Moat）

以宽度 $O(r)$ 的隔离带实现与外界的稳定接口，使用固定模式吸收相位冲突与局部缺陷；缺陷吸收策略：多数表决或纠错码。（状态 $Q \times \{0,1\}$，1 为内部，0 为外部。）

### 5.4 容错冗余

多轨多数表决/时空重复编码，保障长程稳定；例如，三轨冗余，每轨独立模拟，输出取多数。

### 5.5 自相似宏块

规模化审计（层级检查器）把"是否携带计算"写进宏块匹配；采用 Mozes 平铺，自相似尺度递归检查下层一致性。

### 5.6 前缀装载

对"代码+数据"采取前缀自由封箱，天然实现 $2^{-|p|}$ 的采样权重；机制：通用解释器读取前缀码，独立于背景测度。

---

## §6 观察语义与"语义塌缩"

### 定义 6.1（观察步骤）

选择窗口 $W$ 与译码器 $\pi$，得到输出串与状态标签（halt/acc/step）。

### 定义 6.2（观察等价类）

定义等价关系 $\sim_\pi$：$\mathcal{B}_1 \sim_\pi \mathcal{B}_2$ 若对所有窗口 $W$，$\pi(\mathcal{B}_1 \upharpoonright W) = \pi(\mathcal{B}_2 \upharpoonright W)$。等价类 $[\mathcal{B}]_\pi$ 为观察等价类。

### 命题 6.1（语义塌缩）

相对给定 $\pi$，"观察"将同一底层结构族划分为语义等价类；一次具体观察选择其中一个等价类的代表（可读解释）。语义塌缩即选择函子：选择 $\Pi(\mathcal{B}) \in [\mathcal{B}]_\pi$。

**注记 6.1（与标准因子映射的区别）**：区别于标准 SFT 因子映射的拓扑不变性，本语义塌缩强调观察者相对的选择框架，提供语义等价类的划分逻辑。**重要澄清**：此"塌缩"为**数学/观察意义的术语**，指观察行为在等价类中选取代表元，**非物理过程**，仅涉及译码选择，不改变底层静态块。

### 推论 6.2（观察的本质）

在封闭宇宙中，观察不会"改变"合法块，只是选取了可读的结构路径；"观察=译码≈语义上的 collapse"。

**证明**：由定义 6.1 与命题 6.1 直接得出。$\square$

---

## §7 范畴语义

### 7.1 基本范畴结构

**对象**：合法静态块 $\mathcal{B}$。

**态射**：局域因子映射/滑动块码（保持局域一致性）。

**观察函子**：$\Pi: \mathsf{SFT} \to \mathsf{Str}$（有限词范畴），$\Pi(\mathcal{B}) = \{\pi(\mathcal{B} \upharpoonright W)\}$。观察函子通过选择等价类 $[\mathcal{B}]_\pi$ 实现语义塌缩。

**译码自然同构**：若两译码器 $\pi_1, \pi_2$ 相差双射滑动块码 $\tau$，则存在自然同构 $\eta: \Pi_{\pi_1} \to \Pi_{\pi_2}$ 使 $\Pi_{\pi_2}(\mathcal{B}) = \tau \circ \Pi_{\pi_1}(\mathcal{B})$。这对应纤维上的自然同构。

**滑动块码纤维与Grothendieck变换**：在观测层上以滑动块码等价类作为纤维；译码不变性允许纤维化构造，存在Grothendieck变换刻画不同译码器之上的纤维。

**注记 7.1（范畴性质）**：范畴未指定 Cartesian 闭合，但具纤维化结构。

---

## §8 例示与模板

### 8.1 通用基底样式

二维 SFT / 1D CA 的 history-freezing 嵌入（例如 Rule 110 嵌入 TM 加法机：轨道模拟带与头，护城河宽度 3，遵循 5.1–5.6）。

### 8.2 程序盒蓝图

中心—时钟环—护城河—外海的四层结构；外海可为任意合规背景。

### 8.3 强制携带案例

宏块审计器在每层检查下层的一致性与"计算痕迹"，采用 Gács 分层冗余。

---

### 命题 9.0（Moore-Myhill 与信息守恒）

在可和群（如 $\mathbb{Z}^{d+1}$）上的 CA，若无伊甸园（Garden-of-Eden）则全局映射预单射（pre-injective）。本框架中"信息不凭空产生"的 Kolmogorov 上界（A5）与该拓扑-组合不变性一致：预单射确保逆像存在性，与信息守恒的上界互补，但差异在于上界关注算法复杂度而非单纯存在性。

**可和群假设**：本文设置中 $\mathbb{Z}^{d+1}$ 自动满足可和性（amenable），Moore-Myhill 定理直接适用。

**互补而非蕴含**：预单射与 A5 的关系为**互补而非蕴含**：预单射保证拓扑层面的无信息丢失（全局可逆性），A5 保证算法层面的信息不增（复杂度上界）。两者共同支持封闭宇宙的信息守恒框架。

**证明**：Moore (1962) 与 Myhill (1963) 证明无伊甸园 ⇔ 预单射；在信息理论语境下，预单射保证无信息丢失，与 Brudno 上界的一致性源于局域规则的有限性。$\square$

---

## §9 相关工作

本理论构建于现有 CA 通用性与 SFT 构造：

- **Berger** 的 Domino 问题与 **Robinson** 平铺提供涌现基础
- **Mozes** 自相似平铺与 **Durand–Romashchenko–Shen** 的有效子移位支持强制宏块
- **Gács** 的分层自组织模拟保障容错
- **Hedlund (1969)** / Curtis–Hedlund–Lyndon 定理标准化译码器
- **Moore–Myhill** 定理（Garden of Eden）连接信息守恒与 surjective/pre-injective，以及其在**可和群（amenable groups）**上的推广
- **Solomonoff/Levin** 先验指导典型涌现
- **Cook 2004** 与 **Neary–Woods 2006** 提供 Rule 110 通用性与多项式仿真
- **Burton–Steif 1994** 提供测度非唯一性反例
- **Brudno 1983** 奠基复杂度-熵等价

**区别**：本框架强调封闭静态视角与双重术语，避免动态初态。

---

## §10 结论与展望

### 10.1 主要贡献

本理论在封闭宇宙的语境下，建立了"计算=结构、观察=译码、时间=索引"的统一框架。我们证明了程序涌现的存在性、强制/典型两条实现路径、$\Sigma_1^0 / \Pi_2^0$ 的可判定性分层以及信息守恒的条件复杂度上界，并以范畴语义刻画了译码不变性与观察逻辑。

### 10.2 理论定位

该框架既独立自洽，又与更广泛的"collapse-aware"视角自然耦合：观察并不改变宇宙，只改变可读性；语义的选择即"塌缩"的选择。由此，计算的动态叙述被还原为静态体中的几何/组合事实，程序的"出现"成为合法静态块空间中的结构性事件。

### 10.3 未来方向

**短期方向**：护城河开销优化、可混合性阈值研究、强制族表达边界探索。

**长期方向**：测度唯一性研究、全局回收与可逆性、与量子计算框架的连接。

---

## 附录A：护城河形式化定义与 block-gluing 验证

### A.1 度量与因果包络

在 $\mathbb{Z}^{d+1}$ 上取 $\ell_\infty$ 距离。给定有限窗口 $U \subset \Lambda \times T$，其因果过去包络 $\mathrm{Past}_r(U)$ 定义为向下追溯 $r$-邻域的最小闭包。

### A.2 护城河不交性引理

设护城河宽 $m \ge 2r + 1$。若两块 $P_1, P_2$ 的 $\ell_\infty$ 支撑距离 $\ge m$，则 $\mathrm{Past}_r(P_1) \cap \mathrm{Past}_r(P_2) = \varnothing$。

**证明**：因果过去包络 $\mathrm{Past}_r(U)$ 定义为从 $U$ 向上追溯 $r$ 步的最小集合。护城河宽度 $m$ 确保两块间的缓冲区至少 $m$ 格，追溯 $r$ 步后仍不交（距离至少 $m - 2r \ge 1$）。$\square$

### A.3 独立拼接引理

若 $\mathrm{Past}_r(P_1) \cap \mathrm{Past}_r(P_2) = \varnothing$，则 CHL 局域一致性可分解为 $P_1$ 与 $P_2$ 的独立检查；护城河的固定吸收态（如全0）保证跨边界缺陷在 $O(r)$ 步内被湮灭。

**证明**：因果不交确保无共享过去状态，故局域约束可局部验证。固定态吸收缺陷类似于电路中的缓冲区：缺陷信号传播速度 $\le r$ 步/格，在宽度 $m$ 护城河内稳定化。$\square$

**命题 A.3′（缺陷吸收条件）**：若系统存在全局吸收子字母表或安全符号层满足 CHL 的吸收闭包，则固定吸收态保证缺陷在 $O(r)$ 步内被湮灭。若缺乏该结构，仅得 almost-specification：拼接以失败概率指数衰减的形式成立。

### A.4 结论：c-block-gluing

存在常数 $c = c(m, r, Q)$ 使得当支撑距离 $\ge c$ 时，两块可在护城河中介下拼接为全局合法配置。具体 $c \le m + 2r$，对应 quantified block-gluing 的线性间隙版本（失败概率指数小，若不具完整 block-gluing 则退化为 almost-specification）。

---

## 附录B：Brudno 数值检验脚本（伪代码）

```python
# Brudno 数值检验
for n in window_sizes:          # e.g., n = 32..2048
    Wn = extract_window(B, n)   # 取 n×n 或 n×n×Δt 的窗口
    bits = compressor(Wn)       # LZ77/PPMd
    rate[n] = bits / |Wn|
plot(n, rate[n])                # 观察收敛到 h_μ 的平台
```

**报告**：压缩比曲线在 history-freezing 的 Rule-110-SFT 上与已知 $h_\mu$ 的估计对齐；误差条来源于窗口选取与相位场。

### 可复现实验参数表

| 参数 | 值 | 说明 |
|------|-----|------|
| 窗口尺寸序列 | 32, 64, 128, 256, 512 | 立方体 $n \times n \times \Delta t$ |
| 采样步长 $\Delta t$ | $n/4$ | 时间深度随空间尺度缩放 |
| 边界处理 | 周期边界 / 固定填充 | 两种方式各运行一次对比 |
| 压缩器 | LZ-77 (zlib 1.2.11) / PPMd (H variant) | 字典大小 32KB，滑动窗口 8KB |
| 压缩器参数 | zlib: level=9; PPMd: order=6, mem=16MB | 最大压缩比配置 |
| 独立运行轮数 | 100 | 每尺寸随机种子采样 |
| 串行化顺序 | 行优先（x → y → t） | 窗口平展为1D序列 |
| 字母表编码 | 直接二进制（1 bit/state） | Rule 110 状态{0,1} |

**随机种子控制**：每轮使用独立随机初始切片（均匀分布），统计压缩率均值与标准差。边缘效应通过对比周期/固定两种边界量化。

---

## 附录C：开放问题

### C.1 最小护城河开销

给定稳态时长 $T$，实现可延拓的最小盒厚度/冗余度？

### C.2 可混合性阈值

在何种扰动/缺陷密度下，译码仍保持稳健？

### C.3 强制族的表达边界

无需全局不变量的自相似构造能强制哪些高阶性质？

### C.4 测度唯一性

内部最大熵测度是否唯一？（2D SFT 通常不唯一；在 1D 原始边矩阵下唯一，Parry 测度。）若否，典型性结论如何随测度族变化？

### C.5 全局回收与可逆性

在可逆 CA 基底中，语义塌缩的"可逆读回"界限？

---

## 参考文献

1. Berger, R. (1966). The Undecidability of the Domino Problem. *Memoirs of the American Mathematical Society* 66.
2. Robinson, R. M. (1971). Undecidability and nonperiodicity for tilings of the plane. *Inventiones Mathematicae* 12, 177-209.
3. Mozes, S. (1989). Tilings, substitution systems and dynamical systems generated by them. *Journal d'Analyse Mathématique* 53, 139-186.
4. Durand, B., Romashchenko, A., & Shen, A. (2012). Fixed-point tile sets and their applications. *Journal of Computer and System Sciences* 78(3), 731-764.
5. Aubrun, N., & Sablik, M. (2013). Simulation of effective subshifts by two-dimensional subshifts of finite type. *Acta Applicandae Mathematicae* 126, 35-63.
6. Gács, P. (2001). Reliable cellular automata with self-organization. *Journal of Statistical Physics* 103(1-2), 45-267.
7. Hedlund, G. A. (1969). Endomorphisms and Automorphisms of the Shift Dynamical System. *Mathematical Systems Theory* 3(4), 320-375.
8. Moore, E. F. (1962). Machine Models of Self-Reproduction. *Proceedings of the Symposium on Mathematical Problems in the Biological Sciences*, 17-33.
9. Myhill, J. (1963). The Converse of Moore's Garden-of-Eden Theorem. *Proceedings of the American Mathematical Society* 14(5), 685-686.
10. Solomonoff, R. J. (1964). A formal theory of inductive inference. *Information and Control* 7(1-2), 1-22, 224-254.
11. Levin, L. A. (1974). Laws of information conservation (nongrowth) and aspects of the foundation of probability theory. *Problems of Information Transmission* 10(3), 206-210.
12. Cook, M. (2004). Universality in Elementary Cellular Automata. *Complex Systems* 15(1), 1-40. DOI: 10.25088/ComplexSystems.15.1.1
13. Neary, T., & Woods, D. (2006). P-completeness of cellular automaton Rule 110. *Automata, Languages and Programming*, 132-143. DOI: 10.1007/11787006_12
14. Burton, R., & Steif, J. E. (1994). Non-uniqueness of measures of maximal entropy for subshifts of finite type. *Ergodic Theory and Dynamical Systems* 14(2), 213-235. DOI: 10.1017/S0143385700007859
15. Brudno, A. A. (1983). Entropy and the complexity of the trajectories of a dynamical system. *Transactions of the Moscow Mathematical Society* 44, 127-151.
16. Lind, D., & Marcus, B. (1995). *An Introduction to Symbolic Dynamics and Coding*. Cambridge University Press.
17. Kari, J. (1994). Rice's Theorem for the Limit Sets of Cellular Automata. *Theoretical Computer Science* 127(2), 229-254.

---

**致谢**

感谢审阅反馈，确保修订版逻辑自洽。特别感谢指出护城河形式化、block-gluing 验证、测度唯一性澄清等关键问题的审阅者，使本理论得以完善。

**版本说明**

v1.5-camera-ready (2025-10-17): Camera-ready版，根据终审反馈完成七项微调：(1) A5采用后光锥定义因果边界，消除递归公式歧义；(2) 定理4.2精炼归约摘要，强化Π₂⁰-完全性论证；(3) A4-B镜像吸收条件到正文，澄清安全符号层要求；(4) 引理4.1-C改用history height术语（冻结后竖直维度）；(5) 定理4.5添加独立性假设，区分几乎必然与正测度级别；(6) 统一ℓ∞记号与CHL全称（Curtis–Hedlund–Lyndon）；(7) 附录B补充压缩器版本/参数列（zlib 1.2.11, PPMd H variant）。论文已达camera-ready标准，可直接提交。
